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
def CorduroyMpcSimulates (mr : CorduroyMpcPermRunner) (eng : CorduroyPermEngine)
    (lambdas : List Goldilocks) : Prop :=
  ∀ (stSh : List Poseidon2State12) (prep : Poseidon2CallPrep),
    ringListSum lambdas = Goldilocks.one →
    stSh.length = lambdas.length →
    prep.validAt lambdas →
    ∃ outSh : List Poseidon2State12,
      mr.runPerm lambdas stSh prep = some outSh ∧
      outSh.length = lambdas.length ∧
      lagrangeCombineState12 lambdas outSh = eng.perm (lagrangeCombineState12 lambdas stSh)

private theorem corduroyMpcRunner_simulates_engine (lambdas : List Goldilocks) :
    CorduroyMpcSimulates corduroyMpcRunner corduroyPoseidon2Engine lambdas := by
  intro stSh prep hSum hLen hValid
  obtain ⟨outSh, hRun, hOutLen, hComb⟩ :=
    evalSharedPoseidon2Perm_simulates lambdas stSh prep.extInit prep.inter prep.extTerm
      hSum hLen ((Poseidon2CallPrep.validAt_eq _ _).mp hValid).1 ((Poseidon2CallPrep.validAt_eq _ _).mp hValid).2.1 ((Poseidon2CallPrep.validAt_eq _ _).mp hValid).2.2
  refine ⟨outSh, ?_, hOutLen, ?_⟩
  · rw [corduroyMpcRunner_eq]; exact hRun
  · rw [corduroyPoseidon2Engine_perm]; exact hComb

-- Engine-parametric cut-boundary simulation lemmas (`eng` and `mr` remain free variables, so
-- kernel `isDefEq` never unfolds 30-round `poseidon2Perm12`).
private theorem mpcCorduroyPrfMsgWith_eq (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner)
    (lambdas : List Goldilocks) (hSim : CorduroyMpcSimulates mr eng lambdas)
    (sh : CorduroyKeyShares) (sk : CorduroySecretKey) (hMatch : sh.MatchesSecret lambdas sk)
    (optRand msg : Lane4) (prep0 prep1 : Poseidon2CallPrep)
    (hp0 : prep0.validAt lambdas) (hp1 : prep1.validAt lambdas) :
    mpcCorduroyPrfMsgWith mr lambdas sh optRand msg prep0 prep1 =
      some (corduroyPrfMsgWith eng sk optRand msg) := by
  rcases hMatch with ⟨hSumOne, _, hPrfLen, _, hPrfComb, _⟩
  let n := lambdas.length
  let cap : Lane4 := ⟨corduroyTagHMsgStateless, Goldilocks.zero, Goldilocks.zero, corduroyPoseidon2Iv⟩
  let st0Sh := zipState12Shares sh.skPrfShares (List.replicate n optRand) (List.replicate n cap)
  have hSt0Len : st0Sh.length = n :=
    zipState12Shares_length hPrfLen List.length_replicate List.length_replicate
  obtain ⟨out0Sh, hRun0, hLen0, hComb0⟩ := hSim st0Sh prep0 hSumOne hSt0Len hp0
  have hSt0Comb : lagrangeCombineState12 lambdas st0Sh = ⟨sk.skPrf, optRand, cap⟩ := by
    rw [lagrangeCombineState12_zip lambdas _ _ _ hPrfLen List.length_replicate List.length_replicate,
        hPrfComb, lagrangeCombineLane4_replicate_public lambdas hSumOne optRand,
        lagrangeCombineLane4_replicate_public lambdas hSumOne cap]
  rw [hSt0Comb] at hComb0
  obtain ⟨hB0MsgLen, hB0MsgComb⟩ := zipAddLane4Shares_spec lambdas (out0Sh.map (·.b0))
    (List.replicate n msg) (by simp [hLen0]) List.length_replicate
  let b0MsgSh := zipAddLane4Shares (out0Sh.map (·.b0)) (List.replicate n msg)
  let st1Sh := zipState12Shares b0MsgSh (out0Sh.map (·.b1)) (out0Sh.map (·.b2))
  have hSt1Len : st1Sh.length = n :=
    zipState12Shares_length hB0MsgLen (by simp [hLen0, n]) (by simp [hLen0, n])
  obtain ⟨out1Sh, hRun1, _, hComb1⟩ := hSim st1Sh prep1 hSumOne hSt1Len hp1
  have hProj0 := lagrangeCombineState12_proj lambdas out0Sh
  have hSt1Comb : lagrangeCombineState12 lambdas st1Sh =
      ⟨lane4Add (eng.perm ⟨sk.skPrf, optRand, cap⟩).b0 msg,
       (eng.perm ⟨sk.skPrf, optRand, cap⟩).b1,
       (eng.perm ⟨sk.skPrf, optRand, cap⟩).b2⟩ := by
    rw [lagrangeCombineState12_zip lambdas _ _ _ hB0MsgLen (by simp [hLen0]) (by simp [hLen0]),
        hB0MsgComb, lagrangeCombineLane4_replicate_public lambdas hSumOne msg]
    rw [hComb0] at hProj0
    have hb0 : lagrangeCombineLane4 lambdas (out0Sh.map (·.b0)) = (eng.perm ⟨sk.skPrf, optRand, cap⟩).b0 :=
      (congrArg Poseidon2State12.b0 hProj0).symm
    have hb1 : lagrangeCombineLane4 lambdas (out0Sh.map (·.b1)) = (eng.perm ⟨sk.skPrf, optRand, cap⟩).b1 :=
      (congrArg Poseidon2State12.b1 hProj0).symm
    have hb2 : lagrangeCombineLane4 lambdas (out0Sh.map (·.b2)) = (eng.perm ⟨sk.skPrf, optRand, cap⟩).b2 :=
      (congrArg Poseidon2State12.b2 hProj0).symm
    rw [hb0, hb1, hb2]
  rw [hSt1Comb] at hComb1
  have hProj1 := lagrangeCombineState12_proj lambdas out1Sh
  rw [hComb1] at hProj1
  unfold mpcCorduroyPrfMsgWith
  rw [corduroyPrfMsgWith.public_eq_1]
  dsimp only [n, cap, st0Sh]
  rw [hRun0]
  dsimp only [b0MsgSh, st1Sh]
  rw [hRun1]
  dsimp only
  exact congrArg some (congrArg Poseidon2State12.b0 hProj1).symm

private theorem mpcCorduroySharedJiveStepWith_eq (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner)
    (lambdas : List Goldilocks) (hSim : CorduroyMpcSimulates mr eng lambdas)
    (hSumOne : ringListSum lambdas = Goldilocks.one)
    (pkSeed : Lane4) (adrs : CorduroyAdrs)
    (valSh : List Lane4) (val : Lane4) (hValLen : valSh.length = lambdas.length)
    (hValComb : lagrangeCombineLane4 lambdas valSh = val)
    (prep : Poseidon2CallPrep) (hPrep : prep.validAt lambdas) :
    ∃ nextSh : List Lane4,
      mpcCorduroySharedJiveStepWith mr lambdas pkSeed adrs valSh prep = some nextSh ∧
      nextSh.length = lambdas.length ∧
      lagrangeCombineLane4 lambdas nextSh =
        lane4Add (eng.perm ⟨val, pkSeed, corduroyEncodeAdrsCap adrs⟩).b0
          (poseidon2WeightedFeedForward ⟨val, pkSeed, corduroyEncodeAdrsCap adrs⟩) := by
  let n := lambdas.length
  let cap := corduroyEncodeAdrsCap adrs
  let stSh := zipState12Shares valSh (List.replicate n pkSeed) (List.replicate n cap)
  have hStLen : stSh.length = n :=
    zipState12Shares_length hValLen List.length_replicate List.length_replicate
  obtain ⟨permSh, hRun, hPermLen, hPermComb⟩ := hSim stSh prep hSumOne hStLen hPrep
  have hStComb : lagrangeCombineState12 lambdas stSh = ⟨val, pkSeed, cap⟩ := by
    rw [lagrangeCombineState12_zip lambdas _ _ _ hValLen List.length_replicate List.length_replicate,
        hValComb, lagrangeCombineLane4_replicate_public lambdas hSumOne pkSeed,
        lagrangeCombineLane4_replicate_public lambdas hSumOne cap]
  rw [hStComb] at hPermComb
  obtain ⟨hSumLen, hSumComb⟩ := zipAddLane4Shares_spec lambdas (permSh.map (·.b0)) valSh
    (by simp [hPermLen]) hValLen
  obtain ⟨hNextLen, hNextComb⟩ := zipAddLane4Shares_spec lambdas
    (zipAddLane4Shares (permSh.map (·.b0)) valSh)
    (List.replicate n (corduroyJivePublicOffset pkSeed cap)) hSumLen List.length_replicate
  have hProj := lagrangeCombineState12_proj lambdas permSh
  rw [hPermComb] at hProj
  have hb0 : lagrangeCombineLane4 lambdas (permSh.map (·.b0)) =
      (eng.perm ⟨val, pkSeed, cap⟩).b0 := (congrArg Poseidon2State12.b0 hProj).symm
  refine ⟨zipAddLane4Shares (zipAddLane4Shares (permSh.map (·.b0)) valSh)
    (List.replicate n (corduroyJivePublicOffset pkSeed cap)), ?_, hNextLen, ?_⟩
  · unfold mpcCorduroySharedJiveStepWith
    dsimp only [n, cap, stSh]
    rw [hRun]
  · rw [hNextComb, hSumComb, hb0, hValComb,
      lagrangeCombineLane4_replicate_public lambdas hSumOne (corduroyJivePublicOffset pkSeed cap)]
    exact corduroyJive_offset_eq _ val pkSeed cap

private theorem mpcCorduroySharedChainIterWith_eq (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner)
    (lambdas : List Goldilocks) (hSim : CorduroyMpcSimulates mr eng lambdas)
    (hSumOne : ringListSum lambdas = Goldilocks.one)
    (pkSeed : Lane4) (layer treeIdx kpIdx chainIdx : Nat)
    (steps startStep : Nat) (valSh : List Lane4) (val : Lane4) (stepPrep : Nat → Poseidon2CallPrep)
    (hLen : valSh.length = lambdas.length)
    (hComb : lagrangeCombineLane4 lambdas valSh = val)
    (hPrep : ∀ s, (stepPrep s).validAt lambdas) :
    ∃ endSh : List Lane4,
      mpcCorduroySharedChainIterWith mr lambdas pkSeed layer treeIdx kpIdx chainIdx startStep steps valSh stepPrep = some endSh ∧
      endSh.length = lambdas.length ∧
      lagrangeCombineLane4 lambdas endSh =
        corduroyChainIterWith eng pkSeed layer treeIdx kpIdx chainIdx startStep steps val := by
  induction steps generalizing startStep valSh val with
  | zero => exact ⟨valSh, rfl, hLen, hComb⟩
  | succ steps ih =>
    obtain ⟨nextSh, hJive, hNextLen, hNextComb⟩ :=
      mpcCorduroySharedJiveStepWith_eq eng mr lambdas hSim hSumOne pkSeed
        (wotsStepAdrs layer treeIdx kpIdx chainIdx startStep) valSh val hLen hComb
        (stepPrep startStep) (hPrep startStep)
    have hStepEq : lane4Add (eng.perm ⟨val, pkSeed,
        corduroyEncodeAdrsCap (wotsStepAdrs layer treeIdx kpIdx chainIdx startStep)⟩).b0
        (poseidon2WeightedFeedForward ⟨val, pkSeed,
          corduroyEncodeAdrsCap (wotsStepAdrs layer treeIdx kpIdx chainIdx startStep)⟩) =
        corduroyWotsStepWith eng pkSeed layer treeIdx kpIdx chainIdx startStep val := by
      rw [corduroyWotsStepWith_eq, wotsStepAdrs.public_eq_1]
      exact (corduroySpongeEvalWith_jive_wots eng pkSeed layer treeIdx kpIdx chainIdx startStep val).symm
    rw [hStepEq] at hNextComb
    obtain ⟨endSh, hRest, hEndLen, hEndComb⟩ :=
      ih (startStep + 1) nextSh _ hNextLen hNextComb
    refine ⟨endSh, ?_, hEndLen, hEndComb.trans
      (corduroyChainIterWith_succ eng pkSeed layer treeIdx kpIdx chainIdx startStep steps val).symm⟩
    dsimp only [mpcCorduroySharedChainIterWith]
    rw [hJive]
    exact hRest

private theorem mpcCorduroyEvalWotsChainEndWith_eq (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner)
    (lambdas : List Goldilocks) (hSim : CorduroyMpcSimulates mr eng lambdas)
    (sh : CorduroyKeyShares) (sk : CorduroySecretKey) (hMatch : sh.MatchesSecret lambdas sk)
    (layer treeIdx kpIdx chainIdx steps : Nat) (callPrep : Nat → Poseidon2CallPrep)
    (hPrep : ∀ s, (callPrep s).validAt lambdas) :
    mpcCorduroyEvalWotsChainEndWith mr lambdas sh layer treeIdx kpIdx chainIdx steps callPrep =
      some (corduroyChainIterWith eng sk.pkSeed layer treeIdx kpIdx chainIdx 0 steps
              (corduroyWotsSecretWith eng sk layer treeIdx kpIdx chainIdx)) := by
  rcases hMatch with ⟨hSumOne, hSeedLen, _, hSeedComb, _, hPkSeedEq⟩
  let n := lambdas.length
  let cap := corduroyEncodeAdrsCap (wotsPrfAdrs layer treeIdx kpIdx chainIdx)
  let initSh := zipState12Shares sh.skSeedShares (List.replicate n sh.pkSeed) (List.replicate n cap)
  have hInitLen : initSh.length = n :=
    zipState12Shares_length hSeedLen List.length_replicate List.length_replicate
  obtain ⟨basePermSh, hRun0, hBaseLen, hBaseComb⟩ := hSim initSh (callPrep 0) hSumOne hInitLen (hPrep 0)
  have hInitComb : lagrangeCombineState12 lambdas initSh = ⟨sk.skSeed, sk.pkSeed, cap⟩ := by
    rw [lagrangeCombineState12_zip lambdas _ _ _ hSeedLen List.length_replicate List.length_replicate,
        hSeedComb, hPkSeedEq,
        lagrangeCombineLane4_replicate_public lambdas hSumOne sk.pkSeed,
        lagrangeCombineLane4_replicate_public lambdas hSumOne cap]
  rw [hInitComb] at hBaseComb
  have hProj := lagrangeCombineState12_proj lambdas basePermSh
  rw [hBaseComb] at hProj
  have hb0 : lagrangeCombineLane4 lambdas (basePermSh.map (·.b0)) =
      corduroyWotsSecretWith eng sk layer treeIdx kpIdx chainIdx :=
    (congrArg Poseidon2State12.b0 hProj).symm
  obtain ⟨endSh, hIter, _, hEndComb⟩ :=
    mpcCorduroySharedChainIterWith_eq eng mr lambdas hSim hSumOne sh.pkSeed layer treeIdx kpIdx chainIdx
      steps 0 (basePermSh.map (·.b0))
      (corduroyWotsSecretWith eng sk layer treeIdx kpIdx chainIdx)
      (fun s => callPrep (s + 1)) (by simp [hBaseLen]) hb0 (fun s => hPrep (s + 1))
  unfold mpcCorduroyEvalWotsChainEndWith
  dsimp only [n, cap, initSh]
  rw [hRun0]
  dsimp only
  rw [hIter]
  dsimp only
  rw [hEndComb, hPkSeedEq]

private theorem mpcCorduroyEvalForsSecretWith_eq (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner)
    (lambdas : List Goldilocks) (hSim : CorduroyMpcSimulates mr eng lambdas)
    (sh : CorduroyKeyShares) (sk : CorduroySecretKey) (hMatch : sh.MatchesSecret lambdas sk)
    (leafGlobalIdx treeJ leafIdx : Nat) (prep : Poseidon2CallPrep) (hPrep : prep.validAt lambdas) :
    mpcCorduroyEvalForsSecretWith mr lambdas sh leafGlobalIdx treeJ leafIdx prep =
      some (corduroyForsSecretWith eng sk leafGlobalIdx treeJ leafIdx) := by
  rcases hMatch with ⟨hSumOne, hSeedLen, _, hSeedComb, _, hPkSeedEq⟩
  let n := lambdas.length
  let cap := corduroyEncodeAdrsCap (forsPrfAdrs leafGlobalIdx treeJ leafIdx)
  let initSh := zipState12Shares sh.skSeedShares (List.replicate n sh.pkSeed) (List.replicate n cap)
  have hInitLen : initSh.length = n :=
    zipState12Shares_length hSeedLen List.length_replicate List.length_replicate
  obtain ⟨outSh, hRun, _, hComb⟩ := hSim initSh prep hSumOne hInitLen hPrep
  have hInitComb : lagrangeCombineState12 lambdas initSh = ⟨sk.skSeed, sk.pkSeed, cap⟩ := by
    rw [lagrangeCombineState12_zip lambdas _ _ _ hSeedLen List.length_replicate List.length_replicate,
        hSeedComb, hPkSeedEq,
        lagrangeCombineLane4_replicate_public lambdas hSumOne sk.pkSeed,
        lagrangeCombineLane4_replicate_public lambdas hSumOne cap]
  rw [hInitComb] at hComb
  have hProj := lagrangeCombineState12_proj lambdas outSh
  rw [hComb] at hProj
  unfold mpcCorduroyEvalForsSecretWith corduroyForsSecretWith
  dsimp only [n, cap, initSh]
  rw [hRun]
  exact congrArg some (congrArg Poseidon2State12.b0 hProj).symm

private theorem mpcCorduroyEvalForsLeafHashWith_eq (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner)
    (lambdas : List Goldilocks) (hSim : CorduroyMpcSimulates mr eng lambdas)
    (sh : CorduroyKeyShares) (sk : CorduroySecretKey) (hMatch : sh.MatchesSecret lambdas sk)
    (leafGlobalIdx treeJ leafIdx : Nat) (prep0 prep1 : Poseidon2CallPrep)
    (hp0 : prep0.validAt lambdas) (hp1 : prep1.validAt lambdas) :
    mpcCorduroyEvalForsLeafHashWith mr lambdas sh leafGlobalIdx treeJ leafIdx prep0 prep1 =
      some (corduroyHonestForsLeafWith eng sk leafGlobalIdx treeJ leafIdx) := by
  rcases hMatch with ⟨hSumOne, hSeedLen, _, hSeedComb, _, hPkSeedEq⟩
  let n := lambdas.length
  let cap := corduroyEncodeAdrsCap (forsPrfAdrs leafGlobalIdx treeJ leafIdx)
  let initSh := zipState12Shares sh.skSeedShares (List.replicate n sh.pkSeed) (List.replicate n cap)
  have hInitLen : initSh.length = n :=
    zipState12Shares_length hSeedLen List.length_replicate List.length_replicate
  obtain ⟨secPermSh, hRun0, hSecLen, hSecComb⟩ := hSim initSh prep0 hSumOne hInitLen hp0
  have hInitComb : lagrangeCombineState12 lambdas initSh = ⟨sk.skSeed, sk.pkSeed, cap⟩ := by
    rw [lagrangeCombineState12_zip lambdas _ _ _ hSeedLen List.length_replicate List.length_replicate,
        hSeedComb, hPkSeedEq,
        lagrangeCombineLane4_replicate_public lambdas hSumOne sk.pkSeed,
        lagrangeCombineLane4_replicate_public lambdas hSumOne cap]
  rw [hInitComb] at hSecComb
  have hProj := lagrangeCombineState12_proj lambdas secPermSh
  rw [hSecComb] at hProj
  have hb0 : lagrangeCombineLane4 lambdas (secPermSh.map (·.b0)) =
      corduroyForsSecretWith eng sk leafGlobalIdx treeJ leafIdx :=
    (congrArg Poseidon2State12.b0 hProj).symm
  obtain ⟨leafSh, hJive, _, hLeafComb⟩ :=
    mpcCorduroySharedJiveStepWith_eq eng mr lambdas hSim hSumOne sh.pkSeed
      (forsLeafAdrs leafGlobalIdx treeJ leafIdx) (secPermSh.map (·.b0))
      (corduroyForsSecretWith eng sk leafGlobalIdx treeJ leafIdx)
      (by simp [hSecLen]) hb0 prep1 hp1
  unfold mpcCorduroyEvalForsLeafHashWith
  dsimp only [n, cap, initSh]
  rw [hRun0]
  dsimp only
  rw [hJive]
  dsimp only
  rw [hLeafComb, hPkSeedEq]
  exact congrArg some (by
    simp only [corduroyHonestForsLeafWith.public_eqs, corduroyForsLeafHashWith.public_eqs, forsLeafAdrs.public_eqs]
    exact (corduroySpongeEvalWith_jive_fors eng sk.pkSeed leafGlobalIdx treeJ leafIdx
      (corduroyForsSecretWith eng sk leafGlobalIdx treeJ leafIdx)).symm)

private theorem computeCorduroyMerkleNodeWith_congr_in_range (eng : CorduroyPermEngine) (pkSeed : Lane4)
    (mkAdrs : Nat → Nat → CorduroyAdrs) (f g : Nat → Lane4) :
    ∀ (h idx : Nat),
      (∀ u, u < 2 ^ h * (idx + 1) → f u = g u) →
      computeCorduroyMerkleNodeWith eng pkSeed mkAdrs f h idx =
      computeCorduroyMerkleNodeWith eng pkSeed mkAdrs g h idx
  | 0, idx, hEq => hEq idx (by simp)
  | h + 1, idx, hEq => by
    dsimp only [computeCorduroyMerkleNodeWith]
    have hL : ∀ u, u < 2 ^ h * (2 * idx + 1) → u < 2 ^ (h + 1) * (idx + 1) := by
      intro u hu
      rw [Nat.pow_succ, Nat.mul_assoc]
      exact Nat.lt_of_lt_of_le hu (Nat.mul_le_mul_left (2 ^ h) (by omega))
    have hR : ∀ u, u < 2 ^ h * (2 * idx + 1 + 1) → u < 2 ^ (h + 1) * (idx + 1) := by
      intro u hu
      rw [Nat.pow_succ, Nat.mul_assoc]
      exact Nat.lt_of_lt_of_le hu (Nat.mul_le_mul_left (2 ^ h) (by omega))
    rw [computeCorduroyMerkleNodeWith_congr_in_range eng pkSeed mkAdrs f g h (2 * idx) (fun u hu => hEq u (hL u hu)),
        computeCorduroyMerkleNodeWith_congr_in_range eng pkSeed mkAdrs f g h (2 * idx + 1) (fun u hu => hEq u (hR u hu))]

private theorem buildCorduroyMerklePathWith_congr_in_range (eng : CorduroyPermEngine) (pkSeed : Lane4)
    (mkAdrs : Nat → Nat → CorduroyAdrs) (f g : Nat → Lane4) :
    ∀ (rem lvl idx : Nat),
      idx < 2 ^ rem →
      (∀ u, u < 2 ^ (lvl + rem) → f u = g u) →
      buildCorduroyMerklePathWith eng pkSeed mkAdrs f rem lvl idx =
      buildCorduroyMerklePathWith eng pkSeed mkAdrs g rem lvl idx
  | 0, _, _, _, _ => rfl
  | rem + 1, lvl, idx, hIdxLt, hEq => by
    dsimp only [buildCorduroyMerklePathWith]
    let sibIdx := if idx % 2 == 0 then idx + 1 else idx - 1
    have hSibBound : sibIdx + 1 ≤ 2 ^ (rem + 1) := by
      dsimp only [sibIdx]
      rcases Nat.mod_two_eq_zero_or_one idx with hE | hO
      · rw [Nat.pow_succ] at hIdxLt ⊢; simp [hE]; omega
      · have hNe : (idx % 2 == 0) = false := by rw [hO]; decide
        rw [Nat.pow_succ] at hIdxLt ⊢; simp [hNe]; omega
    have hNodeEq : computeCorduroyMerkleNodeWith eng pkSeed mkAdrs f lvl sibIdx =
        computeCorduroyMerkleNodeWith eng pkSeed mkAdrs g lvl sibIdx := by
      apply computeCorduroyMerkleNodeWith_congr_in_range
      intro u hu
      apply hEq
      have hMul : 2 ^ lvl * (sibIdx + 1) ≤ 2 ^ lvl * 2 ^ (rem + 1) := Nat.mul_le_mul_left _ hSibBound
      rw [← Nat.pow_add] at hMul
      omega
    have hDivLt : idx / 2 < 2 ^ rem := by rw [Nat.pow_succ] at hIdxLt; omega
    have hShift : (lvl + 1) + rem = lvl + (rem + 1) := by omega
    rw [hNodeEq, buildCorduroyMerklePathWith_congr_in_range eng pkSeed mkAdrs f g rem (lvl + 1) (idx / 2) hDivLt
          (by rw [hShift]; exact hEq)]

private theorem mpcCorduroyWotsPkWith_eq (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner)
    (cfg : CorduroyParams) (lambdas : List Goldilocks) (hSim : CorduroyMpcSimulates mr eng lambdas)
    (sh : CorduroyKeyShares) (sk : CorduroySecretKey) (hMatch : sh.MatchesSecret lambdas sk)
    (layer treeIdx kpIdx : Nat) (callPrep : Nat → Nat → Poseidon2CallPrep)
    (hPrep : ∀ c s, (callPrep c s).validAt lambdas) :
    mpcCorduroyWotsPkWith eng mr cfg lambdas sh layer treeIdx kpIdx callPrep =
      some (corduroyHonestWotsPkWith eng cfg sk layer treeIdx kpIdx) := by
  unfold mpcCorduroyWotsPkWith
  simp only [corduroyHonestWotsPkWith.public_eqs, corduroyHonestWotsPeaksWith.public_eqs]
  rw [mapMList_eq_some_map _ _ (List.range cfg.wotsChains)
        (fun c _ => mpcCorduroyEvalWotsChainEndWith_eq eng mr lambdas hSim sh sk hMatch layer treeIdx kpIdx c 3
          (callPrep c) (hPrep c))]
  dsimp only
  rw [hMatch.2.2.2.2.2]

private theorem mpcCorduroySubtreeRootWith_eq (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner)
    (cfg : CorduroyParams) (lambdas : List Goldilocks) (hSim : CorduroyMpcSimulates mr eng lambdas)
    (sh : CorduroyKeyShares) (sk : CorduroySecretKey) (hMatch : sh.MatchesSecret lambdas sk)
    (layer treeIdx : Nat) (callPrep : Nat → Nat → Nat → Poseidon2CallPrep)
    (hPrep : ∀ kp c s, (callPrep kp c s).validAt lambdas) :
    mpcCorduroySubtreeRootWith eng mr cfg lambdas sh layer treeIdx callPrep =
      some (corduroyHonestSubtreeRootWith eng cfg sk layer treeIdx) := by
  unfold mpcCorduroySubtreeRootWith
  simp only [corduroyHonestSubtreeRootWith.public_eqs]
  rw [mapMList_eq_some_map _ _ (List.range (2 ^ cfg.subtreeHeight))
        (fun kp _ => mpcCorduroyWotsPkWith_eq eng mr cfg lambdas hSim sh sk hMatch layer treeIdx kp (callPrep kp) (hPrep kp))]
  dsimp only
  rw [hMatch.2.2.2.2.2]
  congr 1
  apply computeCorduroyMerkleNodeWith_congr_in_range
  intro u hu
  simp only [Nat.zero_add, Nat.mul_one] at hu
  exact getD_map_range _ _ _ u hu

private theorem mpcCorduroyForsTreeLeavesWith_eq (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner)
    (cfg : CorduroyParams) (lambdas : List Goldilocks) (hSim : CorduroyMpcSimulates mr eng lambdas)
    (sh : CorduroyKeyShares) (sk : CorduroySecretKey) (hMatch : sh.MatchesSecret lambdas sk)
    (leafGlobalIdx treeJ : Nat) (callPrep : Nat → Nat → Poseidon2CallPrep)
    (hPrep : ∀ u b, (callPrep u b).validAt lambdas) :
    mpcCorduroyForsTreeLeavesWith mr cfg lambdas sh leafGlobalIdx treeJ callPrep =
      some ((List.range (2 ^ cfg.forsHeight)).map
        (corduroyHonestForsLeafWith eng sk leafGlobalIdx treeJ)) :=
  mapMList_eq_some_map _ _ (List.range (2 ^ cfg.forsHeight))
    (fun u _ => mpcCorduroyEvalForsLeafHashWith_eq eng mr lambdas hSim sh sk hMatch leafGlobalIdx treeJ u
      (callPrep u 0) (callPrep u 1) (hPrep u 0) (hPrep u 1))

private theorem mpcCorduroyForsPkWith_eq (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner)
    (cfg : CorduroyParams) (lambdas : List Goldilocks) (hSim : CorduroyMpcSimulates mr eng lambdas)
    (sh : CorduroyKeyShares) (sk : CorduroySecretKey) (hMatch : sh.MatchesSecret lambdas sk)
    (leafGlobalIdx : Nat) (callPrep : Nat → Nat → Nat → Poseidon2CallPrep)
    (hPrep : ∀ j u b, (callPrep j u b).validAt lambdas) :
    mpcCorduroyForsPkWith eng mr cfg lambdas sh leafGlobalIdx callPrep =
      some (corduroyHonestForsPkWith eng cfg sk leafGlobalIdx) := by
  unfold mpcCorduroyForsPkWith
  simp only [corduroyHonestForsPkWith.public_eqs]
  rw [mapMList_eq_some_map _ (corduroyHonestForsTreeRootWith eng cfg sk leafGlobalIdx)
        (List.range cfg.forsTrees) ?_]
  · dsimp only; rw [hMatch.2.2.2.2.2]
  · intro j _
    rw [mpcCorduroyForsTreeLeavesWith_eq eng mr cfg lambdas hSim sh sk hMatch leafGlobalIdx j (callPrep j) (hPrep j)]
    dsimp only
    rw [hMatch.2.2.2.2.2]
    congr 1
    simp only [corduroyHonestForsTreeRootWith.public_eqs]
    apply computeCorduroyMerkleNodeWith_congr_in_range
    intro u hu
    simp only [Nat.zero_add, Nat.mul_one] at hu
    exact getD_map_range _ _ _ u hu

private theorem mpcCorduroyBuildForsOpeningsWith_eq (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner)
    (cfg : CorduroyParams) (lambdas : List Goldilocks) (hSim : CorduroyMpcSimulates mr eng lambdas)
    (sh : CorduroyKeyShares) (sk : CorduroySecretKey) (hMatch : sh.MatchesSecret lambdas sk)
    (leafGlobalIdx : Nat) (callPrep : Nat → Nat → Nat → Poseidon2CallPrep)
    (hPrep : ∀ j u b, (callPrep j u b).validAt lambdas)
    (idxs : List Nat) (startJ : Nat)
    (hB : ∀ idx ∈ idxs, idx < 2 ^ cfg.forsHeight) :
    mpcCorduroyBuildForsOpeningsWith eng mr cfg lambdas sh leafGlobalIdx callPrep startJ idxs =
      some (corduroyBuildForsOpeningsWith eng cfg sk leafGlobalIdx startJ idxs) := by
  induction idxs generalizing startJ with
  | nil => rfl
  | cons idx idxs ih =>
    have hIdxLt : idx < 2 ^ cfg.forsHeight := hB idx (List.mem_cons_self ..)
    have hTailB : ∀ x ∈ idxs, x < 2 ^ cfg.forsHeight := fun x hx => hB x (List.mem_cons_of_mem _ hx)
    dsimp only [mpcCorduroyBuildForsOpeningsWith, corduroyBuildForsOpeningsWith]
    rw [mpcCorduroyEvalForsSecretWith_eq eng mr lambdas hSim sh sk hMatch leafGlobalIdx startJ idx _ (hPrep startJ idx 2),
        mpcCorduroyForsTreeLeavesWith_eq eng mr cfg lambdas hSim sh sk hMatch leafGlobalIdx startJ _ (hPrep startJ),
        ih (startJ + 1) hTailB]
    dsimp only
    rw [hMatch.2.2.2.2.2]
    congr 2
    congr 1
    apply buildCorduroyMerklePathWith_congr_in_range _ _ _ _ _ cfg.forsHeight 0 idx hIdxLt
    intro u hu
    rw [Nat.zero_add] at hu
    exact getD_map_range _ _ _ u hu

private theorem mpcCorduroySignLayersAuxWith_eq (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner)
    (cfg : CorduroyParams) (lambdas : List Goldilocks) (hSim : CorduroyMpcSimulates mr eng lambdas)
    (sh : CorduroyKeyShares) (sk : CorduroySecretKey) (hMatch : sh.MatchesSecret lambdas sk)
    (pk : CorduroyPublicKey) (callPrep : Nat → Nat → Nat → Nat → Poseidon2CallPrep)
    (hPrep : ∀ l kp c s, (callPrep l kp c s).validAt lambdas)
    (ctrs : List Nat) (layer remIdx : Nat) (curRoot : Lane4) :
    mpcCorduroySignLayersAuxWith eng mr cfg lambdas sh pk callPrep layer remIdx curRoot ctrs =
      some (corduroySignLayersAuxWith eng cfg sk pk layer remIdx curRoot ctrs) := by
  induction ctrs generalizing layer remIdx curRoot with
  | nil => rfl
  | cons ctr restCtrs ih =>
    dsimp only [mpcCorduroySignLayersAuxWith, corduroySignLayersAuxWith]
    let subLeaves := 2 ^ cfg.subtreeHeight
    let kpIdx := remIdx % subLeaves
    let treeIdx := remIdx / subLeaves
    have hKpLt : kpIdx < subLeaves := Nat.mod_lt _ (Nat.two_pow_pos _)
    let hmsg := corduroyLayerHmsgWith eng pk layer treeIdx kpIdx ctr curRoot
    let digits := corduroyExtractDigits cfg.wotsChains hmsg
    rw [mapMList_eq_some_map _
          (fun c => corduroyChainIterWith eng sk.pkSeed layer treeIdx kpIdx c 0 (digits[c]!)
            (corduroyWotsSecretWith eng sk layer treeIdx kpIdx c))
          (List.range cfg.wotsChains)
          (fun c _ => mpcCorduroyEvalWotsChainEndWith_eq eng mr lambdas hSim sh sk hMatch layer treeIdx kpIdx c
            (digits[c]!) (callPrep layer kpIdx c) (hPrep layer kpIdx c)),
        mapMList_eq_some_map _ (corduroyHonestWotsPkWith eng cfg sk layer treeIdx)
          (List.range subLeaves)
          (fun kp _ => mpcCorduroyWotsPkWith_eq eng mr cfg lambdas hSim sh sk hMatch layer treeIdx kp
            (callPrep layer kp) (hPrep layer kp))]
    dsimp only
    have hNextRootEq :
        computeCorduroyMerkleNodeWith eng sh.pkSeed (xmssMerkleAdrs layer treeIdx)
          (fun kp => ((List.range subLeaves).map
            (corduroyHonestWotsPkWith eng cfg sk layer treeIdx)).getD kp lane4Zero)
          cfg.subtreeHeight 0 =
        corduroyHonestSubtreeRootWith eng cfg sk layer treeIdx := by
      rw [hMatch.2.2.2.2.2]
      simp only [corduroyHonestSubtreeRootWith.public_eqs]
      apply computeCorduroyMerkleNodeWith_congr_in_range
      intro u hu
      simp only [Nat.zero_add, Nat.mul_one] at hu
      exact getD_map_range _ _ _ u hu
    have hPathEq :
        buildCorduroyMerklePathWith eng sh.pkSeed (xmssMerkleAdrs layer treeIdx)
          (fun kp => ((List.range subLeaves).map
            (corduroyHonestWotsPkWith eng cfg sk layer treeIdx)).getD kp lane4Zero)
          cfg.subtreeHeight 0 kpIdx =
        buildCorduroyMerklePathWith eng sk.pkSeed (xmssMerkleAdrs layer treeIdx)
          (corduroyHonestWotsPkWith eng cfg sk layer treeIdx) cfg.subtreeHeight 0 kpIdx := by
      rw [hMatch.2.2.2.2.2]
      apply buildCorduroyMerklePathWith_congr_in_range _ _ _ _ _ cfg.subtreeHeight 0 kpIdx hKpLt
      intro u hu
      rw [Nat.zero_add] at hu
      exact getD_map_range _ _ _ u hu
    rw [hNextRootEq, hPathEq,
        ih (layer + 1) treeIdx (corduroyHonestSubtreeRootWith eng cfg sk layer treeIdx)]

private theorem corduroy_threshold_matches_standalone_with
    (eng : CorduroyPermEngine) (mr : CorduroyMpcPermRunner)
    (cfg : CorduroyParams) (lambdas : List Goldilocks)
    (hSim : CorduroyMpcSimulates mr eng lambdas)
    (sh : CorduroyKeyShares) (sk : CorduroySecretKey)
    (prep : CorduroyMpcPrep) (msg : Lane4) (r : CorduroySignRand)
    (hMatch : sh.MatchesSecret lambdas sk)
    (hPrep : prep.validAt lambdas) :
    corduroyThresholdKeygenWith eng mr cfg lambdas sh prep.keygenPrep = some (corduroyDerivePkWith eng cfg sk) ∧
    corduroyThresholdSignWith eng mr cfg lambdas sh prep msg r = some (corduroySignWith eng cfg sk msg r) ∧
    (CorduroyValidGrindWith eng cfg sk msg r →
      corduroyVerifyWith eng cfg (corduroyDerivePkWith eng cfg sk) msg (corduroySignWith eng cfg sk msg r) = true) := by
  rcases hPrep with ⟨hKgPrep, hPrfPrep, hForsPrep, hLayPrep⟩
  have hKg : corduroyThresholdKeygenWith eng mr cfg lambdas sh prep.keygenPrep = some (corduroyDerivePkWith eng cfg sk) := by
    unfold corduroyThresholdKeygenWith
    simp only [corduroyDerivePkWith.public_eqs]
    rw [mpcCorduroySubtreeRootWith_eq eng mr cfg lambdas hSim sh sk hMatch (cfg.numLayers - 1) 0 prep.keygenPrep hKgPrep]
    dsimp only
    rw [hMatch.2.2.2.2.2]
  refine ⟨hKg, ?_, corduroyVerifyWith_corduroySignWith eng cfg sk msg r⟩
  unfold corduroyThresholdSignWith
  simp only [corduroySignWith.public_eqs]
  rw [hKg]
  dsimp only
  rw [mpcCorduroyPrfMsgWith_eq eng mr lambdas hSim sh sk hMatch r.optRand msg (prep.prfPrep 0) (prep.prfPrep 1)
        (hPrfPrep 0) (hPrfPrep 1)]
  dsimp only
  let pk := corduroyDerivePkWith eng cfg sk
  let rRand := corduroyPrfMsgWith eng sk r.optRand msg
  obtain ⟨_, _, hForsIdxBounds⟩ := corduroyHashMsgWith_bounds eng cfg rRand pk msg
  rw [mpcCorduroyBuildForsOpeningsWith_eq eng mr cfg lambdas hSim sh sk hMatch _ prep.forsPrep hForsPrep _ 0 hForsIdxBounds,
      mpcCorduroyForsPkWith_eq eng mr cfg lambdas hSim sh sk hMatch _ prep.forsPrep hForsPrep]
  dsimp only
  rw [mpcCorduroySignLayersAuxWith_eq eng mr cfg lambdas hSim sh sk hMatch pk prep.layerPrep hLayPrep]

/-- **Theorem 1: `Corduroy` Dealerless Threshold Matched-Input Bit-Identity & Completeness
    (`corduroy_threshold_matches_standalone`)**:
    For ANY `(t, n)` Shamir secret sharing `sh` of `sk = (skSeed, skPrf, pkSeed)` over `Goldilocks`
    and valid SPDZ-MAC-authenticated `Poseidon2` preprocessing `prep`:
    1. Distributed keygen `corduroyThresholdKeygen` outputs `some (corduroyDerivePk cfg sk)`;
    2. Distributed threshold signing `corduroyThresholdSign` outputs `some (corduroySign cfg sk msg r)`
       (**bit-for-bit identical** to standalone `corduroySign` under matched `(sk, msg, r)`, while
       never reconstructing `skSeed`, `skPrf`, unrevealed chain links, or unrevealed FORS leaves);
    3. Under any valid counter schedule `CorduroyValidGrind cfg sk msg r`, both standalone and
       threshold outputs satisfy `corduroyVerify = true`. -/
theorem corduroy_threshold_matches_standalone
    (cfg : CorduroyParams) (lambdas : List Goldilocks)
    (sh : CorduroyKeyShares) (sk : CorduroySecretKey)
    (prep : CorduroyMpcPrep) (msg : Lane4) (r : CorduroySignRand)
    (hMatch : sh.MatchesSecret lambdas sk)
    (hPrep : prep.validAt lambdas) :
    corduroyThresholdKeygen cfg lambdas sh prep.keygenPrep = some (corduroyDerivePk cfg sk) ∧
    corduroyThresholdSign cfg lambdas sh prep msg r = some (corduroySign cfg sk msg r) ∧
    (CorduroyValidGrind cfg sk msg r →
      corduroyVerify cfg (corduroyDerivePk cfg sk) msg (corduroySign cfg sk msg r) = true) :=
  corduroy_threshold_matches_standalone_with corduroyPoseidon2Engine corduroyMpcRunner
    cfg lambdas (corduroyMpcRunner_simulates_engine lambdas) sh sk prep msg r hMatch hPrep

end Qsag
end
