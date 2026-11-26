module
/-
# Dealerless `(t, n)` Shamir/SPDZ Share-Level `Poseidon2` Threshold Engine

Share-level evaluation of every `Corduroy` primitive under a dealerless `(t, n)` Shamir/SPDZ
runner and the bit-identity of the threshold signer with the standalone signer
(`corduroy_threshold_matches_standalone`).
-/

public import Qsag.Protocol.Aggregation.CorduroyAndHemAirCompleteness.CorduroyHypertreeEufCma

public section

namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
set_option autoImplicit false
set_option maxErrors 1000
set_option Elab.async false
set_option exponentiation.threshold 2048
attribute [local irreducible] poseidon2Perm12

/-! ### Dealerless `(t, n)` Shamir/SPDZ Share-Level `Poseidon2` Threshold Engine (`corduroy_threshold_matches_standalone`) -/

/-- `(t, n)` Shamir secret-share bundle for `Corduroy`: each quorum party holds a 4-limb share of
    `skSeed` and a 4-limb share of `skPrf`, never reconstructing either secret in cleartext. -/
structure CorduroyKeyShares where
  skSeedShares : List Lane4
  skPrfShares  : List Lane4
  pkSeed       : Lane4
  deriving DecidableEq, Repr

/-- Validity of `CorduroyKeyShares` against Lagrange weights `lambdas` (`∑ λ_p = 1`). -/
def CorduroyKeyShares.MatchesSecret (lambdas : List Goldilocks)
    (sh : CorduroyKeyShares) (sk : CorduroySecretKey) : Prop :=
  ringListSum lambdas = Goldilocks.one ∧
  sh.skSeedShares.length = lambdas.length ∧
  sh.skPrfShares.length = lambdas.length ∧
  lagrangeCombineLane4 lambdas sh.skSeedShares = sk.skSeed ∧
  lagrangeCombineLane4 lambdas sh.skPrfShares = sk.skPrf ∧
  sh.pkSeed = sk.pkSeed

private theorem lagrangeCombineLane4_replicate_public
    (lambdas : List Goldilocks) (hSumOne : ringListSum lambdas = Goldilocks.one) (v : Lane4) :
    lagrangeCombineLane4 lambdas (List.replicate lambdas.length v) = v := by
  have hRepMap : ∀ (f : Lane4 → Goldilocks),
      (List.replicate lambdas.length v).map f = List.replicate lambdas.length (f v) := by
    intro f; simp [List.map_replicate]
  rw [lagrangeCombineLane4_proj, hRepMap (·.x0), hRepMap (·.x1), hRepMap (·.x2), hRepMap (·.x3)]
  have hCol : ∀ c : Goldilocks, lagrangeCombine lambdas (List.replicate lambdas.length c) = c := fun c => by
    unfold lagrangeCombine
    rw [ringDot_replicate_right, hSumOne]
    exact LawfulCommRing.one_mul c
  rw [hCol, hCol, hCol, hCol]

private def zipAddLane4Shares : List Lane4 → List Lane4 → List Lane4
  | a :: as, b :: bs => lane4Add a b :: zipAddLane4Shares as bs
  | _, _ => []

private theorem goldMul_add_distrib (l a b : Goldilocks) :
    Goldilocks.mul l (Goldilocks.add a b) = Goldilocks.add (Goldilocks.mul l a) (Goldilocks.mul l b) :=
  LawfulCommRing.left_distrib l a b

private theorem goldAdd_four_rearrange (a b c d : Goldilocks) :
    Goldilocks.add (Goldilocks.add a b) (Goldilocks.add c d) =
    Goldilocks.add (Goldilocks.add a c) (Goldilocks.add b d) :=
  LawfulCommRing.add_add_add_comm a b c d

private theorem lane4Scale_add_distrib (l : Goldilocks) (a b : Lane4) :
    lane4Scale l (lane4Add a b) = lane4Add (lane4Scale l a) (lane4Scale l b) := by
  rcases a with ⟨a0, a1, a2, a3⟩
  rcases b with ⟨b0, b1, b2, b3⟩
  simp only [lane4Scale_eq, lane4Add_eq]
  exact congrArg₄ Lane4.mk
    (goldMul_add_distrib l a0 b0)
    (goldMul_add_distrib l a1 b1)
    (goldMul_add_distrib l a2 b2)
    (goldMul_add_distrib l a3 b3)
where
  congrArg₄ {α β γ δ ε : Type} (f : α → β → γ → δ → ε)
      {a1 a2 : α} {b1 b2 : β} {c1 c2 : γ} {d1 d2 : δ}
      (ha : a1 = a2) (hb : b1 = b2) (hc : c1 = c2) (hd : d1 = d2) :
      f a1 b1 c1 d1 = f a2 b2 c2 d2 := by
    subst ha hb hc hd; rfl

private theorem lane4Add_four_rearrange (a b c d : Lane4) :
    lane4Add (lane4Add a b) (lane4Add c d) = lane4Add (lane4Add a c) (lane4Add b d) := by
  rcases a with ⟨a0, a1, a2, a3⟩
  rcases b with ⟨b0, b1, b2, b3⟩
  rcases c with ⟨c0, c1, c2, c3⟩
  rcases d with ⟨d0, d1, d2, d3⟩
  simp only [lane4Add_eq]
  have h0 := goldAdd_four_rearrange a0 b0 c0 d0
  have h1 := goldAdd_four_rearrange a1 b1 c1 d1
  have h2 := goldAdd_four_rearrange a2 b2 c2 d2
  have h3 := goldAdd_four_rearrange a3 b3 c3 d3
  rw [h0, h1, h2, h3]

private theorem zipAddLane4Shares_spec
    (ls : List Goldilocks) (as bs : List Lane4)
    (ha : as.length = ls.length) (hb : bs.length = ls.length) :
    (zipAddLane4Shares as bs).length = ls.length ∧
    lagrangeCombineLane4 ls (zipAddLane4Shares as bs) =
      lane4Add (lagrangeCombineLane4 ls as) (lagrangeCombineLane4 ls bs) := by
  induction ls generalizing as bs with
  | nil =>
    cases as with
    | nil =>
      cases bs with
      | nil => exact ⟨rfl, by simp only [lagrangeCombineLane4_nil, lane4Zero_eq, lane4Add_eq]; have hz : Goldilocks.add Goldilocks.zero Goldilocks.zero = Goldilocks.zero := LawfulCommRing.add_zero _; rw [hz]⟩
      | cons _ _ => exact absurd hb (by simp only [List.length_cons, List.length_nil]; omega)
    | cons _ _ => exact absurd ha (by simp only [List.length_cons, List.length_nil]; omega)
  | cons l ls ih =>
    cases as with
    | nil => exact absurd ha (by simp only [List.length_cons, List.length_nil]; omega)
    | cons a as =>
      cases bs with
      | nil => exact absurd hb (by simp only [List.length_cons, List.length_nil]; omega)
      | cons b bs =>
        obtain ⟨ihL, ihC⟩ := ih as bs (Nat.succ.inj ha) (Nat.succ.inj hb)
        refine ⟨by simp [zipAddLane4Shares, ihL], ?_⟩
        simp only [zipAddLane4Shares, lagrangeCombineLane4_cons]
        rw [ihC, lane4Scale_add_distrib, lane4Add_four_rearrange]

/-- Abstract online shared permutation handle preventing equation-generator WHNF expansion of
    30-round `runSharedPoseidon2PermOnline` inside recursive MPC hypertree definitions. -/
structure CorduroyMpcPermRunner where
  runPerm : List Goldilocks → List Poseidon2State12 → Poseidon2CallPrep → Option (List Poseidon2State12)

def corduroyMpcRunner : CorduroyMpcPermRunner where
  runPerm := fun lambdas ss prep =>
    runSharedPoseidon2PermOnline lambdas ss prep.extInit prep.inter prep.extTerm

private theorem corduroyMpcRunner_eq (lambdas : List Goldilocks) (ss : List Poseidon2State12)
    (prep : Poseidon2CallPrep) :
    corduroyMpcRunner.runPerm lambdas ss prep =
      runSharedPoseidon2PermOnline lambdas ss prep.extInit prep.inter prep.extTerm := by
  unfold corduroyMpcRunner; rfl

attribute [local irreducible] corduroyMpcRunner

/-- Share-level `Poseidon2` evaluation of `corduroyPrfMsg` (`skPrf` remains secret-shared throughout). -/
def mpcCorduroyPrfMsgWith (mr : CorduroyMpcPermRunner) (lambdas : List Goldilocks) (sh : CorduroyKeyShares)
    (optRand msg : Lane4) (prep0 prep1 : Poseidon2CallPrep) : Option Lane4 :=
  let n := lambdas.length
  let cap : Lane4 := ⟨corduroyTagHMsgStateless, Goldilocks.zero, Goldilocks.zero, corduroyPoseidon2Iv⟩
  let st0Sh := zipState12Shares sh.skPrfShares (List.replicate n optRand) (List.replicate n cap)
  match mr.runPerm lambdas st0Sh prep0 with
  | none => none
  | some out0Sh =>
    let b0MsgSh := zipAddLane4Shares (out0Sh.map (·.b0)) (List.replicate n msg)
    let st1Sh := zipState12Shares b0MsgSh (out0Sh.map (·.b1)) (out0Sh.map (·.b2))
    match mr.runPerm lambdas st1Sh prep1 with
    | none => none
    | some out1Sh => some (lagrangeCombineLane4 lambdas (out1Sh.map (·.b0)))

/-- Public part `2·pkSeed + 4·cap` of the weighted Jive feed-forward: both the second rate block and
    the tweak are public in a chain/leaf step, so parties add it as a public constant. -/
def corduroyJivePublicOffset (pkSeed cap : Lane4) : Lane4 :=
  lane4Add (lane4Scale (Goldilocks.ofNat 2) pkSeed) (lane4Scale (Goldilocks.ofNat 4) cap)

private theorem lane4Add_jive_assoc (p v k c : Lane4) :
    lane4Add (lane4Add p v) (lane4Add k c) = lane4Add p (lane4Add (lane4Add v k) c) := by
  rcases p with ⟨p0, p1, p2, p3⟩
  rcases v with ⟨v0, v1, v2, v3⟩
  rcases k with ⟨k0, k1, k2, k3⟩
  rcases c with ⟨c0, c1, c2, c3⟩
  have h : ∀ p v k c : Goldilocks,
      Goldilocks.add (Goldilocks.add p v) (Goldilocks.add k c) =
        Goldilocks.add p (Goldilocks.add (Goldilocks.add v k) c) := fun p v k c =>
    (LawfulCommRing.add_assoc p v (Goldilocks.add k c)).trans
      (congrArg (Goldilocks.add p) (LawfulCommRing.add_assoc v k c).symm)
  simp only [lane4Add_eq]
  rw [h p0 v0 k0 c0, h p1 v1 k1 c1, h p2 v2 k2 c2, h p3 v3 k3 c3]

/-- The share-level value `(perm.b0 + val) + (2·pkSeed + 4·cap)` is the weighted feed-forward output. -/
private theorem corduroyJive_offset_eq (p val pkSeed cap : Lane4) :
    lane4Add (lane4Add p val) (corduroyJivePublicOffset pkSeed cap) =
      lane4Add p (poseidon2WeightedFeedForward ⟨val, pkSeed, cap⟩) := by
  simp only [corduroyJivePublicOffset, poseidon2WeightedFeedForward_eq]
  exact lane4Add_jive_assoc p val _ _

/-- Share-level weighted Jive feed-forward step `[val] -> [F(pkSeed, adrs, val)]` keeping chain links
    secret-shared: shares of `perm.b0 + val` plus the public constant `2·pkSeed + 4·cap`
    (`eval_spdz_hem_compress12_ff_batch` in `poseidon2_mpc.rs`). -/
def mpcCorduroySharedJiveStepWith (mr : CorduroyMpcPermRunner) (lambdas : List Goldilocks)
    (pkSeed : Lane4) (adrs : CorduroyAdrs) (valSh : List Lane4) (prep : Poseidon2CallPrep) : Option (List Lane4) :=
  let n := lambdas.length
  let cap := corduroyEncodeAdrsCap adrs
  let stSh := zipState12Shares valSh (List.replicate n pkSeed) (List.replicate n cap)
  match mr.runPerm lambdas stSh prep with
  | none => none
  | some permSh =>
    some (zipAddLane4Shares (zipAddLane4Shares (permSh.map (·.b0)) valSh)
      (List.replicate n (corduroyJivePublicOffset pkSeed cap)))

def mpcCorduroySharedChainIterWith (mr : CorduroyMpcPermRunner) (lambdas : List Goldilocks) (pkSeed : Lane4)
    (layer treeIdx kpIdx chainIdx startStep steps : Nat)
    (valSh : List Lane4) (stepPrep : Nat → Poseidon2CallPrep) : Option (List Lane4) :=
  match steps with
  | 0 => some valSh
  | s + 1 =>
    match mpcCorduroySharedJiveStepWith mr lambdas pkSeed
            (wotsStepAdrs layer treeIdx kpIdx chainIdx startStep) valSh (stepPrep startStep) with
    | none => none
    | some nextSh =>
      mpcCorduroySharedChainIterWith mr lambdas pkSeed layer treeIdx kpIdx chainIdx (startStep + 1) s nextSh stepPrep
  termination_by structural steps

/-- Share-level WOTS+C chain evaluation: derives `[c_0]` from `[skSeed]`, advances `steps` links
    in MPC without opening intermediate chain values `< steps`, and opens ONLY `c_steps`! -/
def mpcCorduroyEvalWotsChainEndWith (mr : CorduroyMpcPermRunner) (lambdas : List Goldilocks) (sh : CorduroyKeyShares)
    (layer treeIdx kpIdx chainIdx steps : Nat) (callPrep : Nat → Poseidon2CallPrep) : Option Lane4 :=
  let n := lambdas.length
  let cap := corduroyEncodeAdrsCap (wotsPrfAdrs layer treeIdx kpIdx chainIdx)
  let initSh := zipState12Shares sh.skSeedShares (List.replicate n sh.pkSeed) (List.replicate n cap)
  match mr.runPerm lambdas initSh (callPrep 0) with
  | none => none
  | some basePermSh =>
    let baseSh := basePermSh.map (·.b0)
    match mpcCorduroySharedChainIterWith mr lambdas sh.pkSeed layer treeIdx kpIdx chainIdx 0 steps baseSh
            (fun s => callPrep (s + 1)) with
    | none => none
    | some endSh => some (lagrangeCombineLane4 lambdas endSh)

/-- Share-level FORS secret reveal (opened ONLY for the `k` message-selected FORS leaves). -/
def mpcCorduroyEvalForsSecretWith (mr : CorduroyMpcPermRunner) (lambdas : List Goldilocks) (sh : CorduroyKeyShares)
    (leafGlobalIdx treeJ leafIdx : Nat) (prep : Poseidon2CallPrep) : Option Lane4 :=
  let n := lambdas.length
  let cap := corduroyEncodeAdrsCap (forsPrfAdrs leafGlobalIdx treeJ leafIdx)
  let initSh := zipState12Shares sh.skSeedShares (List.replicate n sh.pkSeed) (List.replicate n cap)
  match mr.runPerm lambdas initSh prep with
  | none => none
  | some outSh => some (lagrangeCombineLane4 lambdas (outSh.map (·.b0)))

/-- Share-level unrevealed FORS leaf hash: derives `[sec]` in MPC, applies 1 shared Jive step in MPC,
    and opens ONLY the public leaf hash (`sec` is NEVER reconstructed in cleartext!). -/
def mpcCorduroyEvalForsLeafHashWith (mr : CorduroyMpcPermRunner) (lambdas : List Goldilocks) (sh : CorduroyKeyShares)
    (leafGlobalIdx treeJ leafIdx : Nat) (prep0 prep1 : Poseidon2CallPrep) : Option Lane4 :=
  let n := lambdas.length
  let cap := corduroyEncodeAdrsCap (forsPrfAdrs leafGlobalIdx treeJ leafIdx)
  let initSh := zipState12Shares sh.skSeedShares (List.replicate n sh.pkSeed) (List.replicate n cap)
  match mr.runPerm lambdas initSh prep0 with
  | none => none
  | some secPermSh =>
    match mpcCorduroySharedJiveStepWith mr lambdas sh.pkSeed (forsLeafAdrs leafGlobalIdx treeJ leafIdx)
            (secPermSh.map (·.b0)) prep1 with
    | none => none
    | some leafSh => some (lagrangeCombineLane4 lambdas leafSh)

private def mapMList {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | x :: xs =>
    match f x with
    | none => none
    | some y =>
      match mapMList f xs with
      | none => none
      | some ys => some (y :: ys)

private theorem mapMList_eq_some_map {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ (xs : List α), (∀ x ∈ xs, f x = some (g x)) → mapMList f xs = some (xs.map g)
  | [], _ => rfl
  | x :: xs, h => by
    dsimp only [mapMList, List.map]
    rw [h x (List.mem_cons_self ..),
        mapMList_eq_some_map f g xs (fun z hz => h z (List.mem_cons_of_mem _ hz))]

/-- Distributed WOTS+C public key computation via share-level `mpcCorduroyEvalWotsChainEndWith` at `steps = 3`. -/
def mpcCorduroyWotsPkWith (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner) (cfg : CorduroyParams)
    (lambdas : List Goldilocks) (sh : CorduroyKeyShares)
    (layer treeIdx kpIdx : Nat) (callPrep : Nat → Nat → Poseidon2CallPrep) : Option Lane4 :=
  match mapMList (fun c => mpcCorduroyEvalWotsChainEndWith mr lambdas sh layer treeIdx kpIdx c 3 (callPrep c))
          (List.range cfg.wotsChains) with
  | none => none
  | some peaks => some (corduroyWotsPkCompressWith eng sh.pkSeed layer treeIdx kpIdx peaks)

def mpcCorduroySubtreeRootWith (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner) (cfg : CorduroyParams)
    (lambdas : List Goldilocks) (sh : CorduroyKeyShares)
    (layer treeIdx : Nat) (callPrep : Nat → Nat → Nat → Poseidon2CallPrep) : Option Lane4 :=
  match mapMList (fun kp => mpcCorduroyWotsPkWith eng mr cfg lambdas sh layer treeIdx kp (callPrep kp))
          (List.range (2 ^ cfg.subtreeHeight)) with
  | none => none
  | some leaves =>
    some (computeCorduroyMerkleNodeWith eng sh.pkSeed (xmssMerkleAdrs layer treeIdx)
      (fun kp => leaves.getD kp lane4Zero) cfg.subtreeHeight 0)

def corduroyThresholdKeygenWith (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner)
    (cfg : CorduroyParams) (lambdas : List Goldilocks) (sh : CorduroyKeyShares)
    (callPrep : Nat → Nat → Nat → Poseidon2CallPrep) : Option CorduroyPublicKey :=
  match mpcCorduroySubtreeRootWith eng mr cfg lambdas sh (cfg.numLayers - 1) 0 callPrep with
  | none => none
  | some pkRoot => some { pkSeed := sh.pkSeed, pkRoot := pkRoot }

/-- **Dealerless `(t, n)` Shamir/SPDZ Distributed Key Generation (`corduroyThresholdKeygen`)**. -/
def corduroyThresholdKeygen (cfg : CorduroyParams) (lambdas : List Goldilocks) (sh : CorduroyKeyShares)
    (callPrep : Nat → Nat → Nat → Poseidon2CallPrep) : Option CorduroyPublicKey :=
  corduroyThresholdKeygenWith corduroyPoseidon2Engine corduroyMpcRunner cfg lambdas sh callPrep

def mpcCorduroyForsTreeLeavesWith (mr : CorduroyMpcPermRunner) (cfg : CorduroyParams)
    (lambdas : List Goldilocks) (sh : CorduroyKeyShares)
    (leafGlobalIdx treeJ : Nat) (callPrep : Nat → Nat → Poseidon2CallPrep) : Option (List Lane4) :=
  mapMList (fun u => mpcCorduroyEvalForsLeafHashWith mr lambdas sh leafGlobalIdx treeJ u (callPrep u 0) (callPrep u 1))
    (List.range (2 ^ cfg.forsHeight))

def mpcCorduroyForsPkWith (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner) (cfg : CorduroyParams)
    (lambdas : List Goldilocks) (sh : CorduroyKeyShares)
    (leafGlobalIdx : Nat) (callPrep : Nat → Nat → Nat → Poseidon2CallPrep) : Option Lane4 :=
  match mapMList (fun j =>
          match mpcCorduroyForsTreeLeavesWith mr cfg lambdas sh leafGlobalIdx j (callPrep j) with
          | none => none
          | some leaves =>
            some (computeCorduroyMerkleNodeWith eng sh.pkSeed (forsNodeAdrs leafGlobalIdx j)
              (fun u => leaves.getD u lane4Zero) cfg.forsHeight 0))
          (List.range cfg.forsTrees) with
  | none => none
  | some roots => some (corduroyForsRootsCompressWith eng sh.pkSeed leafGlobalIdx roots)

def mpcCorduroyBuildForsOpeningsWith (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner) (cfg : CorduroyParams)
    (lambdas : List Goldilocks) (sh : CorduroyKeyShares)
    (leafGlobalIdx : Nat) (callPrep : Nat → Nat → Nat → Poseidon2CallPrep)
    (j : Nat) (forsIndices : List Nat) : Option (List CorduroyForsOpening) :=
  match forsIndices with
  | [] => some []
  | idx :: idxs =>
    match mpcCorduroyEvalForsSecretWith mr lambdas sh leafGlobalIdx j idx (callPrep j idx 2),
          mpcCorduroyForsTreeLeavesWith mr cfg lambdas sh leafGlobalIdx j (callPrep j) with
    | some sec, some leaves =>
      let path := buildCorduroyMerklePathWith eng sh.pkSeed (forsNodeAdrs leafGlobalIdx j)
        (fun u => leaves.getD u lane4Zero) cfg.forsHeight 0 idx
      match mpcCorduroyBuildForsOpeningsWith eng mr cfg lambdas sh leafGlobalIdx callPrep (j + 1) idxs with
      | none => none
      | some rest => some ({ secretVal := sec, authPath := path } :: rest)
    | _, _ => none
  termination_by structural forsIndices

def mpcCorduroySignLayersAuxWith (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner) (cfg : CorduroyParams)
    (lambdas : List Goldilocks) (sh : CorduroyKeyShares)
    (pk : CorduroyPublicKey) (callPrep : Nat → Nat → Nat → Nat → Poseidon2CallPrep)
    (layer remIdx : Nat) (curRoot : Lane4) (ctrs : List Nat) : Option (List CorduroyLayerSig) :=
  match ctrs with
  | [] => some []
  | ctr :: restCtrs =>
    let subLeaves := 2 ^ cfg.subtreeHeight
    let kpIdx := remIdx % subLeaves
    let treeIdx := remIdx / subLeaves
    let hmsg := corduroyLayerHmsgWith eng pk layer treeIdx kpIdx ctr curRoot
    let digits := corduroyExtractDigits cfg.wotsChains hmsg
    match mapMList (fun c =>
            mpcCorduroyEvalWotsChainEndWith mr lambdas sh layer treeIdx kpIdx c (digits[c]!) (callPrep layer kpIdx c))
            (List.range cfg.wotsChains),
          mapMList (fun kp => mpcCorduroyWotsPkWith eng mr cfg lambdas sh layer treeIdx kp (callPrep layer kp))
            (List.range subLeaves) with
    | some chains, some leaves =>
      let leafFn := fun kp => leaves.getD kp lane4Zero
      let path := buildCorduroyMerklePathWith eng sh.pkSeed (xmssMerkleAdrs layer treeIdx) leafFn cfg.subtreeHeight 0 kpIdx
      let nextRoot := computeCorduroyMerkleNodeWith eng sh.pkSeed (xmssMerkleAdrs layer treeIdx) leafFn cfg.subtreeHeight 0
      match mpcCorduroySignLayersAuxWith eng mr cfg lambdas sh pk callPrep (layer + 1) treeIdx nextRoot restCtrs with
      | none => none
      | some restSigs => some ({ tswCtr := ctr, wotsChains := chains, authPath := path } :: restSigs)
    | _, _ => none
  termination_by structural ctrs

/-- Full preprocessing bundle for a dealerless `(t, n)` Shamir/SPDZ `Corduroy` threshold signing session. -/
structure CorduroyMpcPrep where
  keygenPrep : Nat → Nat → Nat → Poseidon2CallPrep
  prfPrep    : Nat → Poseidon2CallPrep
  forsPrep   : Nat → Nat → Nat → Poseidon2CallPrep
  layerPrep  : Nat → Nat → Nat → Nat → Poseidon2CallPrep

def CorduroyMpcPrep.validAt (lambdas : List Goldilocks) (p : CorduroyMpcPrep) : Prop :=
  (∀ kp c s, (p.keygenPrep kp c s).validAt lambdas) ∧
  (∀ b, (p.prfPrep b).validAt lambdas) ∧
  (∀ j u b, (p.forsPrep j u b).validAt lambdas) ∧
  (∀ l kp c s, (p.layerPrep l kp c s).validAt lambdas)

def corduroyThresholdSignWith (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner)
    (cfg : CorduroyParams) (lambdas : List Goldilocks)
    (sh : CorduroyKeyShares) (prep : CorduroyMpcPrep)
    (msg : Lane4) (r : CorduroySignRand) : Option CorduroySig :=
  match corduroyThresholdKeygenWith eng mr cfg lambdas sh prep.keygenPrep with
  | none => none
  | some pk =>
    match mpcCorduroyPrfMsgWith mr lambdas sh r.optRand msg (prep.prfPrep 0) (prep.prfPrep 1) with
    | none => none
    | some rRand =>
      let (leafGlobalIdx, forsIndices, _) := corduroyHashMsgWith eng cfg rRand pk msg
      match mpcCorduroyBuildForsOpeningsWith eng mr cfg lambdas sh leafGlobalIdx prep.forsPrep 0 forsIndices,
            mpcCorduroyForsPkWith eng mr cfg lambdas sh leafGlobalIdx prep.forsPrep with
      | some forsOps, some forsPk =>
        match mpcCorduroySignLayersAuxWith eng mr cfg lambdas sh pk prep.layerPrep 0 leafGlobalIdx forsPk r.layerCtrs with
        | none => none
        | some layerSigs =>
          some { rRand := rRand, forsOpenings := forsOps, layerSigs := layerSigs }
      | _, _ => none

/-- **Dealerless `(t, n)` Shamir/SPDZ Threshold `Corduroy` Signer (`corduroyThresholdSign`)**:
    Evaluates key derivation, `PRF_msg`, FORS openings/trees, and all `d` WOTS+C + Merkle layers
    directly over Shamir shares + SPDZ-MAC-checked `Poseidon2` gates with `0` secret reconstruction. -/
@[expose] def corduroyThresholdSign (cfg : CorduroyParams) (lambdas : List Goldilocks)
    (sh : CorduroyKeyShares) (prep : CorduroyMpcPrep)
    (msg : Lane4) (r : CorduroySignRand) : Option CorduroySig :=
  corduroyThresholdSignWith corduroyPoseidon2Engine corduroyMpcRunner cfg lambdas sh prep msg r

/-- Simulation contract relating a share-level `CorduroyMpcPermRunner` to `CorduroyPermEngine`. -/
