module
/-
# Qsag.Protocol.Signing.HulsingPrfUdHops — Hops 2 & 3 (`PRF` Secret-Seed & `SM-DT-UD` Simulation)

Formalizes Hops 2 and 3 of the standard-model Hülsing–Kudinov / SPHINCS+ (`FIPS 205`) / XMSS-MT
multi-hop EUF-CMA reduction over `Spec.FinGame` and `Spec.Assumptions` (building on Hop 1 in
`HulsingPrfMsgHop` and `secOverlaySuite` in `HulsingSecOverlay`):
1. **Hop 2 (`PRF` Secret-Seed Leaf Idealization via `Spec.PrfHard`):**
   Replaces `thSecretPrf suite pkSeed sk.skSeed adrs` across public-key derivation and all `≤ qSign`
   adaptive signatures with uniform `rfSec` via `prfSecHopDistinguisher`
   (`Spec.Within (prfSecQueryBudget params qSign)`), while keeping `suite.rawHash` **100% untouched**
   (`hulsing_hop2_prfSec_idealization`).
2. **Hop 3 (WOTS+C Multi-Step Chain Simulation / `SmDtUdHard` Undetectability over `Spec.FinGame`):**
   Formalizes multi-target distinct-tweak undetectability (`SmDtUdHard`) over `Spec.FinGame` and
   `Spec.targetIface`, proving `0` loss at step `0` / FORS leaves (`smDtUd_zero_loss_refl`),
   the intermediate chain-step simulation bound (`hulsing_hop3_ud_chain_simulation`), and a
   probability-`1` `#tooth_pair` refutation (`smDtUdHard_constHash_refuted`).
-/

public import Qsag.Protocol.Signing.HulsingSecOverlay
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

/-! ## §1. Explicit `Code byteOracleIface` Secret-Fetching Distinguisher for Hop 2 -/

/-- Query `byteOracleIface` for `count` consecutive indices `start ..< start + count`. -/
def queryVecCode (mkInp : Nat → Spec.Bytes) : Nat → Nat →
    Spec.Code Spec.byteOracleIface (List Spec.Bytes)
  | _, 0 => .ret []
  | start, count + 1 =>
    .call (mkInp start) (fun v =>
      Spec.Code.bind (queryVecCode mkInp (start + 1) count) (fun rest =>
        .ret (padBytes32 v :: rest)))

theorem queryVecCode_within (mkInp : Nat → Spec.Bytes) :
    ∀ (start count : Nat), Spec.Within count (queryVecCode mkInp start count)
  | _, 0 => .ret 0 []
  | start, count + 1 =>
    .call (E := Spec.byteOracleIface) (mkInp start) _ (fun v =>
      by
        have hB := Spec.Within.bind (queryVecCode_within mkInp (start + 1) count)
          (fun rest => Spec.Within.ret 0 (padBytes32 v :: rest))
        rw [Nat.add_zero] at hB
        exact hB)

theorem code_play_bind {E : Spec.Iface} {A B σ : Type}
    (oracle : σ → (q : E.Query) → E.Resp q × σ) :
    ∀ (c : Spec.Code E A) (f : A → Spec.Code E B) (st : σ),
      Spec.Code.play oracle (Spec.Code.bind c f) st =
        let r := Spec.Code.play oracle c st
        Spec.Code.play oracle (f r.1) r.2
  | .ret a, f, st => by unfold Spec.Code.bind; rw [Spec.Code.play_ret]
  | .call q k, f, st => by
    unfold Spec.Code.bind
    rw [Spec.Code.play_call, Spec.Code.play_call]
    exact code_play_bind oracle (k (oracle st q).1) f (oracle st q).2

private theorem queryVecCode_play (mkInp : Nat → Spec.Bytes) (secFn : Spec.Bytes → Spec.Bytes)
    (qPrf : Nat) :
    ∀ (start count used : Nat), used + count ≤ qPrf →
      Spec.Code.play (Spec.budgetedFunOracle secFn qPrf) (queryVecCode mkInp start count) used =
        ((List.range count).map (fun i => padBytes32 (secFn (mkInp (start + i)))), used + count)
  | _, 0, used, _ => by
    unfold queryVecCode
    rw [Spec.Code.play_ret, List.range_zero, List.map_nil, Nat.add_zero]
  | start, count + 1, used, hLe => by
    unfold queryVecCode
    rw [Spec.Code.play_call]
    have hLt : used < qPrf := by omega
    have hStep : Spec.budgetedFunOracle secFn qPrf used (mkInp start) =
        (secFn (mkInp start), used + 1) := by
      rw [Spec.budgetedFunOracle.public_eqs, ite_eq_left hLt]
    rw [hStep, code_play_bind,
      queryVecCode_play mkInp secFn qPrf (start + 1) count (used + 1) (by omega)]
    dsimp only
    rw [Spec.Code.play_ret]
    have hRange : (List.range (count + 1)).map (fun i => padBytes32 (secFn (mkInp (start + i)))) =
        padBytes32 (secFn (mkInp start)) ::
          (List.range count).map (fun i => padBytes32 (secFn (mkInp (start + 1 + i)))) := by
      have hR : ∀ k : Nat, List.range (k + 1) = 0 :: (List.range k).map (· + 1) := by
        intro k
        induction k with
        | zero => rfl
        | succ c ih =>
          conv => lhs; rw [List.range_succ, ih, List.cons_append]
          congr 1
          rw [List.range_succ, List.map_append, List.map_singleton]
      rw [hR count, List.map_cons, List.map_map, Nat.add_zero]
      congr 1; apply List.map_congr_left; intro i _
      dsimp only [Function.comp_def]; rw [Nat.add_assoc, Nat.add_comm 1 i]
    rw [hRange]
    exact Prod.ext rfl (by omega)

/-- Fetch all `2 ^ subtreeHeight * ell1` WOTS secret bases of XMSS subtree `(layer, tree)`. -/
def fetchSubtreeWotsPkCode (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (layer : UInt32) (tree : UInt64) :
    Spec.Code Spec.byteOracleIface (List (List UInt8) × (Nat → List UInt8)) :=
  let total := 2 ^ params.subtreeHeight * params.ell1
  let mkInp := fun idx =>
    let kp := idx / params.ell1
    let r := idx % params.ell1
    pkSeed ++ encodeAdrs ⟨layer, tree, .wotsPrf, UInt32.ofNat kp, UInt32.ofNat r, 0⟩
  Spec.Code.bind (queryVecCode mkInp 0 total) (fun secs =>
    let wotsPkFn : Nat → List UInt8 := fun kp =>
      thTweakTl suite pkSeed ⟨layer, tree, .wotsPk, UInt32.ofNat kp, 0, 0⟩
        ((List.range params.ell1).map fun r =>
          wotsChainSteps suite pkSeed layer tree kp r 0 (params.w - 1)
            (secs.getD (kp * params.ell1 + r) zero32))
    .ret (secs, wotsPkFn))

/-- Per-signature secret-PRF query budget (`FORS` subtree + `numLayers` `XMSS` subtrees). -/
@[expose] def prfSecPerSignBudget (params : PqHashParams) : Nat :=
  (if params.statefulJorts then 0 else params.forsTrees * 2 ^ params.forsHeight) +
    params.numLayers * (2 ^ params.subtreeHeight * params.ell1)

/-- Total `PRF` secret-seed query budget for public-key derivation + `qSign` adaptive signatures. -/
@[expose] def prfSecQueryBudget (params : PqHashParams) (qSign : Nat) : Nat :=
  2 ^ params.subtreeHeight * params.ell1 + qSign * prfSecPerSignBudget params

/-- Sign hypertree layers using `Code byteOracleIface` to fetch each layer's subtree secrets. -/
def signLayersSecCode (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed pkRoot rRand : List UInt8) (maxGrind : Nat) :
    Nat → Nat → List UInt8 → Nat → Spec.Code Spec.byteOracleIface (Option (List LayerXmssSig))
  | _, _, _, 0 => .ret (some [])
  | layerIdx, globalIdx, curRoot, rem + 1 =>
    let subLeaves := 2 ^ params.subtreeHeight
    let kpIdx := globalIdx % subLeaves
    let kpU32 := UInt32.ofNat kpIdx
    let treeIdxNat := globalIdx / subLeaves
    let treeIdx := UInt64.ofNat treeIdxNat
    let layerU32 := UInt32.ofNat layerIdx
    let grindRes :=
      if params.statefulJorts && decide (layerIdx = 0) then
        grindTswLeafCounterAux suite params.w params.ell1 params.targetSum
          rRand pkSeed pkRoot curRoot treeIdx kpU32 0 maxGrind
      else
        grindTswInternalCounterAux suite params.w params.ell1 params.targetSum
          pkSeed pkRoot curRoot layerU32 treeIdx kpU32 0 maxGrind
    match grindRes with
    | none => .ret none
    | some (ctr, digits, _) =>
      Spec.Code.bind (fetchSubtreeWotsPkCode suite params pkSeed layerU32 treeIdx) (fun sw =>
        let secs := sw.1
        let wotsPkFn := sw.2
        let wotsChains := (List.range params.ell1).map fun r =>
          wotsChainSteps suite pkSeed layerU32 treeIdx kpIdx r 0 (digits.getD r 0)
            (secs.getD (kpIdx * params.ell1 + r) zero32)
        let authPath := buildMerkleAuthPathKp suite pkSeed layerU32 treeIdx .tree 0
          wotsPkFn params.subtreeHeight 0 0 kpIdx
        let nextRoot := computeMerkleNode suite pkSeed layerU32 treeIdx .tree wotsPkFn
          params.subtreeHeight 0
        Spec.Code.bind (signLayersSecCode suite params pkSeed pkRoot rRand maxGrind
          (layerIdx + 1) treeIdxNat nextRoot rem) (fun restOpt =>
          match restOpt with
          | none => .ret none
          | some restSigs =>
            .ret (some (⟨ctr, wotsChains, authPath⟩ :: restSigs))))

/-- Sign one query via `Code byteOracleIface` (fetching FORS + hypertree secrets). -/
def signQuerySecCode (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (pk : PqPublicKey) (rfMsg : Spec.Bytes → Spec.Bytes)
    (q : ProdSigningQuery) : Spec.Code Spec.byteOracleIface (Option PqHashSig) :=
  let mu := thPreHash suite pk.pkSeed pk.pkRoot q.message
  let rRand := rfMsg (encodePrfMsg65 q.randomness mu)
  let signCoreCode := fun (leafGlobalIdx : Nat) (forsIdxs : Option (List Nat)) =>
    let subLeaves := 2 ^ params.subtreeHeight
    let initCode : Spec.Code Spec.byteOracleIface (Option (List ForsTreeOpening × List UInt8)) :=
      if params.statefulJorts then .ret (some ([], mu))
      else
        match forsIdxs with
        | none => .ret none
        | some idxs =>
          let kp0 := leafGlobalIdx % subLeaves
          let tree0 := UInt64.ofNat (leafGlobalIdx / subLeaves)
          let leafCount := 2 ^ params.forsHeight
          let totalFors := params.forsTrees * leafCount
          let mkForsInp := fun k =>
            let j := k / leafCount
            let u := k % leafCount
            pkSeed ++ encodeAdrs ⟨0, tree0, .forsPrf, UInt32.ofNat kp0, UInt32.ofNat j, UInt32.ofNat u⟩
          Spec.Code.bind (queryVecCode mkForsInp 0 totalFors) (fun fSecs =>
            let fLeafFn : Nat → Nat → List UInt8 := fun j u =>
              forsIndexedLeafHash suite pkSeed tree0 kp0 j u
                (fSecs.getD (j * leafCount + u) zero32)
            let kpU32 := UInt32.ofNat kp0
            let openings := (List.range params.forsTrees).map fun j =>
              let idxJ := idxs.getD j 0
              { secretVal := fSecs.getD (j * leafCount + idxJ) zero32
                authPath := buildMerkleAuthPathKp suite pkSeed 0 tree0 .forsTree kpU32
                  (fLeafFn j) params.forsHeight j 0 idxJ : ForsTreeOpening }
            let roots := (List.range params.forsTrees).map fun j =>
              computeMerkleNodeKp suite pkSeed 0 tree0 .forsTree kpU32 (fLeafFn j)
                params.forsHeight j 0
            let forsPk := thTweakTl suite pkSeed ⟨0, tree0, .forsRoots, kpU32, 0, 0⟩ roots
            .ret (some (openings, forsPk)))
    Spec.Code.bind initCode (fun initOpt =>
      match initOpt with
      | none => .ret none
      | some (forsOpenings, curRoot) =>
        Spec.Code.bind (signLayersSecCode suite params pkSeed pk.pkRoot rRand q.grindLimit
          0 leafGlobalIdx curRoot params.numLayers) (fun lsOpt =>
          match lsOpt with
          | none => .ret none
          | some layerSigs =>
            let sig : PqHashSig := ⟨rRand, 0, leafGlobalIdx, forsOpenings, layerSigs⟩
            .ret (if verifyProductionPqHashSig suite params pk q.message sig then some sig else none)))
  if params.statefulJorts then
    if !params.productionWellFormed || !params.productionLeafIdxInRange q.epoch then .ret none
    else signCoreCode q.epoch none
  else
    if !params.productionWellFormed then .ret none
    else
      match deriveProductionStatelessInputs suite params rRand pk.pkSeed pk.pkRoot mu with
      | none => .ret none
      | some (leafGlobalIdx, forsIdxs) => signCoreCode leafGlobalIdx (some forsIdxs)

/-- Adaptive tree runner in `Code byteOracleIface` for Hop 2. -/
def prfSecHopTreeCode (latchOn : Bool) (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (pk : PqPublicKey) (rfMsg : Spec.Bytes → Spec.Bytes) :
    ProdAdaptiveTree (List UInt8 × PqHashSig) → Nat → List (List UInt8 × PqHashSig) →
    Spec.Code Spec.byteOracleIface Bool
  | .pure (msgStar, sigStar), _, log =>
    .ret (verifyProductionPqHashSig suite params pk msgStar sigStar &&
      decide (msgStar ∉ log.map Prod.fst))
  | .hashQuery x next, lo, log =>
    prfSecHopTreeCode latchOn suite params pkSeed pk rfMsg (next (suite.rawHash x)) lo log
  | .signQuery q next, lo, log =>
    if latchOn = false ∨ lo ≤ q.epoch then
      Spec.Code.bind (signQuerySecCode suite params pkSeed pk rfMsg q) (fun sigOpt =>
        let log' := match sigOpt with
          | none => log
          | some sig => log ++ [(q.message, sig)]
        prfSecHopTreeCode latchOn suite params pkSeed pk rfMsg (next sigOpt) (q.epoch + 1) log')
    else
      prfSecHopTreeCode latchOn suite params pkSeed pk rfMsg (next none) lo log

/-- **Hop-2 Secret-PRF Distinguisher (`prfSecHopDistinguisher`)** in `Code byteOracleIface Bool`. -/
def prfSecHopDistinguisher {qHash qSign : Nat} (latchOn : Bool) (suite : TweakableHashSuite)
    (params : PqHashParams) (pkSeed : List UInt8) (rfMsg : Spec.Bytes → Spec.Bytes)
    (A : SeedWithheldEufCmaAdv qHash qSign) : Spec.Code Spec.byteOracleIface Bool :=
  let topLayer := UInt32.ofNat (params.numLayers - 1)
  Spec.Code.bind (fetchSubtreeWotsPkCode suite params pkSeed topLayer 0) (fun sw =>
    let pkRoot := computeMerkleNode suite pkSeed topLayer 0 .tree sw.2 params.subtreeHeight 0
    let pk : PqPublicKey := ⟨pkSeed, pkRoot⟩
    prfSecHopTreeCode latchOn suite params pkSeed pk rfMsg ((canonicalizeAdvOptRand A).run pk) 0 [])

private theorem fetchSubtreeWotsPkCode_within (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (layer : UInt32) (tree : UInt64) :
    Spec.Within (2 ^ params.subtreeHeight * params.ell1)
      (fetchSubtreeWotsPkCode suite params pkSeed layer tree) := by
  unfold fetchSubtreeWotsPkCode
  dsimp only
  refine Spec.Within.mono (b₁ := 2 ^ params.subtreeHeight * params.ell1 + 0) (by omega)
    (Spec.Within.bind (queryVecCode_within _ 0 (2 ^ params.subtreeHeight * params.ell1))
      (fun _ => Spec.Within.ret 0 _))

private theorem signLayersSecCode_within (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed pkRoot rRand : List UInt8) (maxGrind : Nat) :
    ∀ (lI gI : Nat) (cur : List UInt8) (rem : Nat),
      Spec.Within (rem * (2 ^ params.subtreeHeight * params.ell1))
        (signLayersSecCode suite params pkSeed pkRoot rRand maxGrind lI gI cur rem)
  | _, _, _, 0 => .ret _ _
  | lI, gI, cur, rem + 1 => by
    unfold signLayersSecCode
    dsimp only
    split
    · exact .ret _ _
    · refine Spec.Within.mono
        (b₁ := 2 ^ params.subtreeHeight * params.ell1 +
          (rem * (2 ^ params.subtreeHeight * params.ell1) + 0))
        (by rw [Nat.succ_mul]; omega)
        (Spec.Within.bind
          (fetchSubtreeWotsPkCode_within suite params pkSeed (UInt32.ofNat lI)
            (UInt64.ofNat (gI / 2 ^ params.subtreeHeight)))
          (fun _ => Spec.Within.bind
            (signLayersSecCode_within suite params pkSeed pkRoot rRand maxGrind
              (lI + 1) (gI / 2 ^ params.subtreeHeight) _ rem)
            (fun restOpt => match restOpt with | none => .ret 0 _ | some _ => .ret 0 _)))

private theorem signQuerySecCode_within (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (pk : PqPublicKey) (rfMsg : Spec.Bytes → Spec.Bytes)
    (q : ProdSigningQuery) :
    Spec.Within (prfSecPerSignBudget params)
      (signQuerySecCode suite params pkSeed pk rfMsg q) := by
  unfold signQuerySecCode prfSecPerSignBudget
  dsimp only
  by_cases hSt : params.statefulJorts
  · simp only [hSt, ↓reduceIte]
    split
    · exact .ret _ _
    · refine Spec.Within.mono
        (b₁ := 0 + (params.numLayers * (2 ^ params.subtreeHeight * params.ell1) + 0))
        (by omega) (Spec.Within.bind (.ret 0 _) (fun initOpt => ?_))
      cases initOpt with
      | none => exact .ret _ _
      | some fc =>
        exact Spec.Within.bind
          (signLayersSecCode_within suite params pkSeed pk.pkRoot _ q.grindLimit 0 q.epoch fc.2
            params.numLayers)
          (fun lsOpt => match lsOpt with | none => .ret 0 _ | some _ => .ret 0 _)
  · simp only [hSt, Bool.false_eq_true, ↓reduceIte]
    split
    · exact .ret _ _
    · cases deriveProductionStatelessInputs suite params _ pk.pkSeed pk.pkRoot _ with
      | none => exact .ret _ _
      | some li =>
        dsimp only
        refine Spec.Within.mono
          (b₁ := (params.forsTrees * 2 ^ params.forsHeight + 0) +
            (params.numLayers * (2 ^ params.subtreeHeight * params.ell1) + 0))
          (by omega)
          (Spec.Within.bind
            (Spec.Within.bind (queryVecCode_within _ 0 (params.forsTrees * 2 ^ params.forsHeight))
              (fun _ => .ret 0 _))
            (fun initOpt => ?_))
        cases initOpt with
        | none => exact .ret _ _
        | some fc =>
          exact Spec.Within.bind
            (signLayersSecCode_within suite params pkSeed pk.pkRoot _ q.grindLimit 0 li.1 fc.2
              params.numLayers)
            (fun lsOpt => match lsOpt with | none => .ret 0 _ | some _ => .ret 0 _)

private theorem prfSecHopTreeCode_within (latchOn : Bool) (suite : TweakableHashSuite)
    (params : PqHashParams) (pkSeed : List UInt8) (pk : PqPublicKey)
    (rfMsg : Spec.Bytes → Spec.Bytes) :
    ∀ {qH qS : Nat} (t : ProdAdaptiveTree (List UInt8 × PqHashSig)) (lo : Nat)
      (log : List (List UInt8 × PqHashSig)),
      ProdDualBounded qH qS t →
      Spec.Within (qS * prfSecPerSignBudget params)
        (prfSecHopTreeCode latchOn suite params pkSeed pk rfMsg t lo log)
  | _, _, .pure (_, _), _, _, _ => .ret _ _
  | 0, _, .hashQuery _ _, _, _, h => False.elim h
  | _ + 1, _, .hashQuery x next, lo, log, h =>
    prfSecHopTreeCode_within latchOn suite params pkSeed pk rfMsg (next (suite.rawHash x)) lo log
      (h _)
  | _, 0, .signQuery _ _, _, _, h => False.elim h
  | _, qS + 1, .signQuery q next, lo, log, h => by
    unfold prfSecHopTreeCode
    by_cases hAdm : latchOn = false ∨ lo ≤ q.epoch
    · rw [ite_eq_left hAdm]
      refine Spec.Within.mono
        (b₁ := prfSecPerSignBudget params + qS * prfSecPerSignBudget params)
        (by rw [Nat.succ_mul, Nat.add_comm]; exact Nat.le_refl _)
        (Spec.Within.bind (signQuerySecCode_within suite params pkSeed pk rfMsg q)
          (fun sigOpt =>
            prfSecHopTreeCode_within latchOn suite params pkSeed pk rfMsg (next sigOpt)
              (q.epoch + 1) _ (h sigOpt)))
    · rw [ite_eq_right hAdm]
      exact Spec.Within.mono (by rw [Nat.succ_mul]; exact Nat.le_add_right _ _)
        (prfSecHopTreeCode_within latchOn suite params pkSeed pk rfMsg (next none) lo log (h none))

theorem prfSecHopDistinguisher_within {qHash qSign : Nat} (latchOn : Bool)
    (suite : TweakableHashSuite) (params : PqHashParams) (pkSeed : List UInt8)
    (rfMsg : Spec.Bytes → Spec.Bytes) (A : SeedWithheldEufCmaAdv qHash qSign) :
    Spec.Within (prfSecQueryBudget params qSign)
      (prfSecHopDistinguisher latchOn suite params pkSeed rfMsg A) := by
  unfold prfSecHopDistinguisher prfSecQueryBudget
  exact Spec.Within.bind (fetchSubtreeWotsPkCode_within suite params pkSeed _ 0)
    (fun _ => prfSecHopTreeCode_within latchOn suite params pkSeed _ rfMsg _ 0 []
      ((canonicalizeAdvOptRand A).bounded _))

private theorem fetchSubtreeWotsPkCode_play (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (secFn : Spec.Bytes → Spec.Bytes) (qPrf : Nat)
    (layer : UInt32) (tree : UInt64) (used : Nat)
    (hBudget : used + 2 ^ params.subtreeHeight * params.ell1 ≤ qPrf) :
    let res := Spec.Code.play (Spec.budgetedFunOracle secFn qPrf)
      (fetchSubtreeWotsPkCode suite params pkSeed layer tree) used
    res.2 = used + 2 ^ params.subtreeHeight * params.ell1 ∧
    (∀ kp < 2 ^ params.subtreeHeight, ∀ r < params.ell1,
      res.1.1.getD (kp * params.ell1 + r) zero32 =
        wotsSecretBase (secOverlaySuite suite pkSeed secFn) ⟨[], [], pkSeed⟩ layer tree kp r) ∧
    (∀ kp < 2 ^ params.subtreeHeight,
      res.1.2 kp =
        computeWotsPk (secOverlaySuite suite pkSeed secFn) params ⟨[], [], pkSeed⟩ layer tree kp) := by
  unfold fetchSubtreeWotsPkCode
  rw [code_play_bind, queryVecCode_play _ secFn qPrf 0 _ used hBudget]
  dsimp only
  rw [Spec.Code.play_ret]
  dsimp only
  have hGetSec : ∀ kp < 2 ^ params.subtreeHeight, ∀ r < params.ell1,
      ((List.range (2 ^ params.subtreeHeight * params.ell1)).map fun i =>
        padBytes32 (secFn (pkSeed ++ encodeAdrs ⟨layer, tree, .wotsPrf,
          UInt32.ofNat ((0 + i) / params.ell1), UInt32.ofNat ((0 + i) % params.ell1), 0⟩))).getD
        (kp * params.ell1 + r) zero32 =
      wotsSecretBase (secOverlaySuite suite pkSeed secFn) ⟨[], [], pkSeed⟩ layer tree kp r := by
    intro kp hkp r hr
    have hEllPos : 0 < params.ell1 := Nat.lt_of_le_of_lt (Nat.zero_le r) hr
    have hIdxLt : kp * params.ell1 + r < 2 ^ params.subtreeHeight * params.ell1 := by
      have h1 : kp + 1 ≤ 2 ^ params.subtreeHeight := hkp
      have h2 := Nat.mul_le_mul_right params.ell1 h1
      rw [Nat.add_mul, Nat.one_mul] at h2; omega
    rw [list_getD_map_range _ _ zero32 hIdxLt, Nat.zero_add]
    have hDiv : (kp * params.ell1 + r) / params.ell1 = kp := by
      rw [Nat.mul_comm kp, Nat.mul_add_div hEllPos, Nat.div_eq_of_lt hr, Nat.add_zero]
    have hMod : (kp * params.ell1 + r) % params.ell1 = r := by
      rw [Nat.mul_comm kp, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
    rw [hDiv, hMod, wotsSecretBase_eq, secOverlaySuite_tagPrf_empty]
  refine ⟨rfl, hGetSec, ?_⟩
  intro kp hkp
  rw [computeWotsPk_eq, thTweakTl_eq, thTweakTl_eq,
    secOverlaySuite_nonPrf_thCall _ _ _ tagThF_ne_tagPrf.2]
  congr 1; apply List.map_congr_left; intro r hrMem
  have hr := List.mem_range.mp hrMem
  rw [hGetSec kp hkp r hr]
  suffices ∀ k st x, wotsChainSteps suite pkSeed layer tree kp r st k x =
      wotsChainSteps (secOverlaySuite suite pkSeed secFn) pkSeed layer tree kp r st k x from
    this (params.w - 1) 0 _
  intro k; induction k with
  | zero => intro st x; rw [wotsChainSteps_zero, wotsChainSteps_zero]
  | succ k' ih =>
    intro st x; rw [wotsChainSteps_succ, wotsChainSteps_succ]; dsimp only
    rw [thChainF_eq, thChainF_eq, secOverlaySuite_nonPrf_thCall _ _ _ tagThF_ne_tagPrf.1]
    exact ih (st + 1) _

private theorem merkleNodeKp_congr_bounded (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (l : UInt32) (t : UInt64) (kind : AdrsKind) (kp : UInt32) (f g : Nat → List UInt8) :
    ∀ (ht n loc : Nat),
      (∀ i < 2 ^ ht, f (loc * 2 ^ ht + i) = g (loc * 2 ^ ht + i)) →
      computeMerkleNodeKp suite pkSeed l t kind kp f ht n loc =
        computeMerkleNodeKp suite pkSeed l t kind kp g ht n loc
  | 0, _, loc, hEq => by
    rw [computeMerkleNodeKp_zero, computeMerkleNodeKp_zero]
    simpa [Nat.pow_zero, Nat.mul_one] using hEq 0 Nat.one_pos
  | ht + 1, n, loc, hEq => by
    rw [computeMerkleNodeKp_succ, computeMerkleNodeKp_succ]
    congr 1
    · refine merkleNodeKp_congr_bounded suite pkSeed l t kind kp f g ht _ _ (fun i hi => ?_)
      have hMul : (2 * loc) * 2 ^ ht + i = loc * 2 ^ (ht + 1) + i := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ ht) 2, ← Nat.mul_assoc, Nat.mul_comm 2 loc]
      rw [hMul]; exact hEq i (by rw [Nat.pow_succ]; omega)
    · refine merkleNodeKp_congr_bounded suite pkSeed l t kind kp f g ht _ _ (fun i hi => ?_)
      have hMul : (2 * loc + 1) * 2 ^ ht + i = loc * 2 ^ (ht + 1) + (2 ^ ht + i) := by
        rw [Nat.add_mul, Nat.one_mul, Nat.pow_succ, Nat.mul_comm (2 ^ ht) 2, ← Nat.mul_assoc,
          Nat.mul_comm 2 loc, Nat.add_assoc]
      rw [hMul]; exact hEq (2 ^ ht + i) (by rw [Nat.pow_succ]; omega)

private theorem authPathKp_congr_bounded (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (l : UInt32) (t : UInt64) (kind : AdrsKind) (kp : UInt32) (f g : Nat → List UInt8) :
    ∀ (ht root locBase locIdx : Nat),
      (∀ i < 2 ^ ht, f (locBase * 2 ^ ht + i) = g (locBase * 2 ^ ht + i)) →
      buildMerkleAuthPathKp suite pkSeed l t kind kp f ht root locBase locIdx =
        buildMerkleAuthPathKp suite pkSeed l t kind kp g ht root locBase locIdx
  | 0, _, _, _, _ => by rw [buildMerkleAuthPathKp.public_eq_1, buildMerkleAuthPathKp.public_eq_1]
  | ht + 1, root, locBase, locIdx, hEq => by
    rw [buildMerkleAuthPathKp.public_eq_2, buildMerkleAuthPathKp.public_eq_2]
    dsimp only
    have hL : ∀ i < 2 ^ ht, f ((2 * locBase) * 2 ^ ht + i) = g ((2 * locBase) * 2 ^ ht + i) := by
      intro i hi
      have hMul : (2 * locBase) * 2 ^ ht + i = locBase * 2 ^ (ht + 1) + i := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ ht) 2, ← Nat.mul_assoc, Nat.mul_comm 2 locBase]
      rw [hMul]; exact hEq i (by rw [Nat.pow_succ]; omega)
    have hR : ∀ i < 2 ^ ht,
        f ((2 * locBase + 1) * 2 ^ ht + i) = g ((2 * locBase + 1) * 2 ^ ht + i) := by
      intro i hi
      have hMul : (2 * locBase + 1) * 2 ^ ht + i = locBase * 2 ^ (ht + 1) + (2 ^ ht + i) := by
        rw [Nat.add_mul, Nat.one_mul, Nat.pow_succ, Nat.mul_comm (2 ^ ht) 2, ← Nat.mul_assoc,
          Nat.mul_comm 2 locBase, Nat.add_assoc]
      rw [hMul]; exact hEq (2 ^ ht + i) (by rw [Nat.pow_succ]; omega)
    split
    · rw [merkleNodeKp_congr_bounded suite pkSeed l t kind kp f g ht _ _ hR,
        authPathKp_congr_bounded suite pkSeed l t kind kp f g ht _ _ locIdx hL]
    · rw [merkleNodeKp_congr_bounded suite pkSeed l t kind kp f g ht _ _ hL,
        authPathKp_congr_bounded suite pkSeed l t kind kp f g ht _ _ _ hR]

private theorem signLayersSecCode_play (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed pkRoot rRand : List UInt8) (secFn : Spec.Bytes → Spec.Bytes) (qPrf maxGrind : Nat) :
    ∀ (lI gI : Nat) (cur : List UInt8) (rem used : Nat),
      used + rem * (2 ^ params.subtreeHeight * params.ell1) ≤ qPrf →
      let res := Spec.Code.play (Spec.budgetedFunOracle secFn qPrf)
        (signLayersSecCode suite params pkSeed pkRoot rRand maxGrind lI gI cur rem) used
      res.1 = signProductionHypertreeLayers (secOverlaySuite suite pkSeed secFn) params
        ⟨[], [], pkSeed⟩ pkRoot rRand maxGrind lI gI cur rem ∧
      res.2 ≤ used + rem * (2 ^ params.subtreeHeight * params.ell1)
  | lI, gI, cur, 0, used, _ => by
    unfold signLayersSecCode
    rw [Spec.Code.play_ret, signProductionHypertreeLayers_zero]
    exact ⟨rfl, by simp⟩
  | lI, gI, cur, rem + 1, used, hBudget => by
    let ov := secOverlaySuite suite pkSeed secFn
    unfold signLayersSecCode
    rw [signProductionHypertreeLayers_succ]
    dsimp only
    have hGrindEq :
        (if params.statefulJorts && decide (lI = 0) then
          grindTswLeafCounterAux suite params.w params.ell1 params.targetSum rRand pkSeed pkRoot cur
            (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
            (UInt32.ofNat (gI % 2 ^ params.subtreeHeight)) 0 maxGrind
        else
          grindTswInternalCounterAux suite params.w params.ell1 params.targetSum pkSeed pkRoot cur
            (UInt32.ofNat lI) (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
            (UInt32.ofNat (gI % 2 ^ params.subtreeHeight)) 0 maxGrind) =
        (if params.statefulJorts && decide (lI = 0) then
          grindTswLeafCounterAux ov params.w params.ell1 params.targetSum rRand pkSeed pkRoot cur
            (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
            (UInt32.ofNat (gI % 2 ^ params.subtreeHeight)) 0 maxGrind
        else
          grindTswInternalCounterAux ov params.w params.ell1 params.targetSum pkSeed pkRoot cur
            (UInt32.ofNat lI) (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
            (UInt32.ofNat (gI % 2 ^ params.subtreeHeight)) 0 maxGrind) := by
      split
      · generalize 0 = c0
        induction maxGrind generalizing c0 with
        | zero => rw [grindTswLeafCounterAux_zero, grindTswLeafCounterAux_zero]
        | succ m' ihM =>
          rw [grindTswLeafCounterAux_succ, grindTswLeafCounterAux_succ,
            thHashLeafMsg_eq, thHashLeafMsg_eq, secOverlaySuite_thCall_cons2, ihM]
      · generalize 0 = c0
        induction maxGrind generalizing c0 with
        | zero => rw [grindTswInternalCounterAux_zero, grindTswInternalCounterAux_zero]
        | succ m' ihM =>
          rw [grindTswInternalCounterAux_succ, grindTswInternalCounterAux_succ,
            thHashInternalNode_eq, thHashInternalNode_eq, secOverlaySuite_thCall_cons2, ihM]
    rw [← hGrindEq]
    cases (if params.statefulJorts && decide (lI = 0) then
        grindTswLeafCounterAux suite params.w params.ell1 params.targetSum rRand pkSeed pkRoot cur
          (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
          (UInt32.ofNat (gI % 2 ^ params.subtreeHeight)) 0 maxGrind
      else
        grindTswInternalCounterAux suite params.w params.ell1 params.targetSum pkSeed pkRoot cur
          (UInt32.ofNat lI) (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
          (UInt32.ofNat (gI % 2 ^ params.subtreeHeight)) 0 maxGrind) with
    | none =>
      rw [Spec.Code.play_ret]
      exact ⟨rfl, Nat.le_add_right _ _⟩
    | some triple =>
      rcases triple with ⟨ctr, digits, _⟩
      dsimp only
      have hSubB : used + 2 ^ params.subtreeHeight * params.ell1 ≤ qPrf := by
        rw [Nat.succ_mul] at hBudget; omega
      obtain ⟨hUsed1, hSecEq, hWotsEq⟩ := fetchSubtreeWotsPkCode_play suite params pkSeed secFn qPrf
        (UInt32.ofNat lI) (UInt64.ofNat (gI / 2 ^ params.subtreeHeight)) used hSubB
      rw [code_play_bind]
      dsimp only
      let sw := (Spec.Code.play (Spec.budgetedFunOracle secFn qPrf)
        (fetchSubtreeWotsPkCode suite params pkSeed (UInt32.ofNat lI)
          (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))) used)
      change sw.2 = _ at hUsed1
      have hRemB : sw.2 + rem * (2 ^ params.subtreeHeight * params.ell1) ≤ qPrf := by
        rw [hUsed1]; rw [Nat.succ_mul] at hBudget; omega
      have hKpLt : gI % 2 ^ params.subtreeHeight < 2 ^ params.subtreeHeight :=
        Nat.mod_lt _ (Nat.two_pow_pos _)
      have hChainsEq :
          ((List.range params.ell1).map fun r =>
            wotsChainSteps suite pkSeed (UInt32.ofNat lI)
              (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
              (gI % 2 ^ params.subtreeHeight) r 0 (digits.getD r 0)
              (sw.1.1.getD ((gI % 2 ^ params.subtreeHeight) * params.ell1 + r) zero32)) =
          ((List.range params.ell1).map fun r =>
            wotsChainSteps ov pkSeed (UInt32.ofNat lI)
              (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
              (gI % 2 ^ params.subtreeHeight) r 0 (digits.getD r 0)
              (wotsSecretBase ov ⟨[], [], pkSeed⟩ (UInt32.ofNat lI)
                (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
                (gI % 2 ^ params.subtreeHeight) r)) := by
        apply List.map_congr_left
        intro r hrMem
        rw [hSecEq _ hKpLt r (List.mem_range.mp hrMem)]
        suffices ∀ k st x, wotsChainSteps suite pkSeed (UInt32.ofNat lI)
            (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
            (gI % 2 ^ params.subtreeHeight) r st k x =
          wotsChainSteps ov pkSeed (UInt32.ofNat lI)
            (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
            (gI % 2 ^ params.subtreeHeight) r st k x from this _ 0 _
        intro k; induction k with
        | zero => intro st x; rw [wotsChainSteps_zero, wotsChainSteps_zero]
        | succ k' ihK =>
          intro st x; rw [wotsChainSteps_succ, wotsChainSteps_succ]; dsimp only
          rw [thChainF_eq, thChainF_eq, secOverlaySuite_nonPrf_thCall _ _ _ tagThF_ne_tagPrf.1]
          exact ihK (st + 1) _
      have hNextRootEq :
          computeMerkleNode suite pkSeed (UInt32.ofNat lI)
            (UInt64.ofNat (gI / 2 ^ params.subtreeHeight)) .tree sw.1.2 params.subtreeHeight 0 =
          computeXmssSubtreeRoot ov params ⟨[], [], pkSeed⟩ (UInt32.ofNat lI)
            (UInt64.ofNat (gI / 2 ^ params.subtreeHeight)) := by
        rw [computeXmssSubtreeRoot_eq, ← computeMerkleNodeKp_zero_eq, ← computeMerkleNodeKp_zero_eq,
          secOverlaySuite_real_merkleNodeKp suite pkSeed secFn _ _ _ _ _ _ (fun _ => rfl)]
        exact merkleNodeKp_congr_bounded suite pkSeed _ _ .tree 0 sw.1.2 _ params.subtreeHeight 0 0
          (fun i hi => by simpa using hWotsEq i hi)
      have hApEq :
          buildMerkleAuthPathKp suite pkSeed (UInt32.ofNat lI)
            (UInt64.ofNat (gI / 2 ^ params.subtreeHeight)) .tree 0 sw.1.2 params.subtreeHeight 0 0
            (gI % 2 ^ params.subtreeHeight) =
          buildMerkleAuthPathKp ov pkSeed (UInt32.ofNat lI)
            (UInt64.ofNat (gI / 2 ^ params.subtreeHeight)) .tree 0
            (computeWotsPk ov params ⟨[], [], pkSeed⟩ (UInt32.ofNat lI)
              (UInt64.ofNat (gI / 2 ^ params.subtreeHeight)))
            params.subtreeHeight 0 0 (gI % 2 ^ params.subtreeHeight) := by
        rw [secOverlaySuite_real_authPathKp suite pkSeed secFn _ _ _ _ _ _ (fun _ => rfl)]
        exact authPathKp_congr_bounded suite pkSeed _ _ .tree 0 sw.1.2 _ params.subtreeHeight 0 0 _
          (fun i hi => by simpa using hWotsEq i hi)
      rw [code_play_bind, hNextRootEq, hChainsEq, hApEq]
      obtain ⟨hRec1, hRec2⟩ := signLayersSecCode_play suite params pkSeed pkRoot rRand secFn qPrf
        maxGrind (lI + 1) (gI / 2 ^ params.subtreeHeight) _ rem sw.2 hRemB
      dsimp only [sw] at hUsed1 hRec1 hRec2 ⊢
      rw [hRec1]
      cases signProductionHypertreeLayers ov params ⟨[], [], pkSeed⟩ pkRoot rRand maxGrind
          (lI + 1) (gI / 2 ^ params.subtreeHeight) _ rem with
      | none => rw [Spec.Code.play_ret]; exact ⟨rfl, by rw [Nat.succ_mul]; omega⟩
      | some rs => rw [Spec.Code.play_ret]; exact ⟨rfl, by rw [Nat.succ_mul]; omega⟩

private theorem signQuerySecCode_play (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (rfMsg secFn : Spec.Bytes → Spec.Bytes) (qPrf used : Nat)
    (q : ProdSigningQuery)
    (hBudget : used + prfSecPerSignBudget params ≤ qPrf) :
    let pk := derivePublicKeyIdealPrf suite params pkSeed secFn
    let res := Spec.Code.play (Spec.budgetedFunOracle secFn qPrf)
      (signQuerySecCode suite params pkSeed pk rfMsg q) used
    res.1 = signQueryIdealPrf suite params pkSeed rfMsg secFn q ∧
    res.2 ≤ used + prfSecPerSignBudget params := by
  intro pk
  let ov := secOverlaySuite suite pkSeed secFn
  have hMuEq : thPreHash suite pk.pkSeed pk.pkRoot q.message =
      thPreHash ov pk.pkSeed pk.pkRoot q.message := by
    rw [thPreHash_eq, thPreHash_eq, secOverlaySuite_thCall_cons2]
  have hCorePlay : ∀ (leaf : Nat) (fIdxs : Option (List Nat)),
      (∀ idxs, fIdxs = some idxs → ∀ idx ∈ idxs, idx < 2 ^ params.forsHeight) →
      (∀ idxs, fIdxs = some idxs → idxs.length = params.forsTrees) →
      let mu := thPreHash suite pk.pkSeed pk.pkRoot q.message
      let rRand := rfMsg (encodePrfMsg65 q.randomness mu)
      let res := Spec.Code.play (Spec.budgetedFunOracle secFn qPrf)
        (Spec.Code.bind
          (if params.statefulJorts then .ret (some ([], mu))
           else match fIdxs with
           | none => .ret none
           | some idxs =>
             let kp0 := leaf % 2 ^ params.subtreeHeight
             let tree0 := UInt64.ofNat (leaf / 2 ^ params.subtreeHeight)
             let leafCount := 2 ^ params.forsHeight
             Spec.Code.bind (queryVecCode
               (fun k => pkSeed ++ encodeAdrs ⟨0, tree0, .forsPrf, UInt32.ofNat kp0,
                 UInt32.ofNat (k / leafCount), UInt32.ofNat (k % leafCount)⟩)
               0 (params.forsTrees * leafCount))
               (fun fSecs =>
                 let fLeafFn : Nat → Nat → List UInt8 := fun j u =>
                   forsIndexedLeafHash suite pkSeed tree0 kp0 j u
                     (fSecs.getD (j * leafCount + u) zero32)
                 let kpU32 := UInt32.ofNat kp0
                 let openings := (List.range params.forsTrees).map fun j =>
                   let idxJ := idxs.getD j 0
                   { secretVal := fSecs.getD (j * leafCount + idxJ) zero32
                     authPath := buildMerkleAuthPathKp suite pkSeed 0 tree0 .forsTree kpU32
                       (fLeafFn j) params.forsHeight j 0 idxJ : ForsTreeOpening }
                 let roots := (List.range params.forsTrees).map fun j =>
                   computeMerkleNodeKp suite pkSeed 0 tree0 .forsTree kpU32 (fLeafFn j)
                     params.forsHeight j 0
                 let forsPk := thTweakTl suite pkSeed ⟨0, tree0, .forsRoots, kpU32, 0, 0⟩ roots
                 .ret (some (openings, forsPk))))
          (fun initOpt =>
            match initOpt with
            | none => .ret none
            | some (forsOpenings, curRoot) =>
              Spec.Code.bind (signLayersSecCode suite params pkSeed pk.pkRoot rRand q.grindLimit
                0 leaf curRoot params.numLayers) (fun lsOpt =>
                match lsOpt with
                | none => .ret none
                | some layerSigs =>
                  let sig : PqHashSig := ⟨rRand, 0, leaf, forsOpenings, layerSigs⟩
                  .ret (if verifyProductionPqHashSig suite params pk q.message sig then some sig
                        else none)))) used
      res.1 = signProductionHypertreeCore ov params ⟨[], [], pkSeed⟩ pk q.message
        (thPreHash ov pk.pkSeed pk.pkRoot q.message)
        (rfMsg (encodePrfMsg65 q.randomness (thPreHash ov pk.pkSeed pk.pkRoot q.message)))
        leaf fIdxs q.grindLimit ∧
      res.2 ≤ used + prfSecPerSignBudget params := by
    intro leaf fIdxs hIdxsBnd hIdxsLen
    dsimp only
    rw [code_play_bind, signProductionHypertreeCore_def]
    dsimp only
    rw [← hMuEq]
    by_cases hSt : params.statefulJorts
    · simp only [hSt, ↓reduceIte, Spec.Code.play_ret]
      rw [code_play_bind]
      have hLB : used + params.numLayers * (2 ^ params.subtreeHeight * params.ell1) ≤ qPrf := by
        unfold prfSecPerSignBudget at hBudget; simp only [hSt, ↓reduceIte, Nat.zero_add] at hBudget
        exact hBudget
      obtain ⟨hL1, hL2⟩ := signLayersSecCode_play suite params pkSeed pk.pkRoot _ secFn qPrf
        q.grindLimit 0 leaf _ params.numLayers used hLB
      dsimp only
      rw [hL1]
      cases signProductionHypertreeLayers ov params ⟨[], [], pkSeed⟩ pk.pkRoot _ q.grindLimit
          0 leaf _ params.numLayers with
      | none =>
        rw [Spec.Code.play_ret]; exact ⟨rfl, by unfold prfSecPerSignBudget; simp [hSt]; exact hL2⟩
      | some ls =>
        rw [Spec.Code.play_ret]
        dsimp only [ov]
        rw [secOverlaySuite_verify_eq]
        exact ⟨rfl, by unfold prfSecPerSignBudget; simp [hSt]; exact hL2⟩
    · simp only [hSt, Bool.false_eq_true, ↓reduceIte]
      cases fIdxs with
      | none => rw [Spec.Code.play_ret, Spec.Code.play_ret]; exact ⟨rfl, Nat.le_add_right _ _⟩
      | some idxs =>
        have hFB : used + params.forsTrees * 2 ^ params.forsHeight ≤ qPrf := by
          unfold prfSecPerSignBudget at hBudget
          simp only [hSt, Bool.false_eq_true, ↓reduceIte] at hBudget; omega
        rw [code_play_bind, queryVecCode_play _ secFn qPrf 0 _ used hFB]
        dsimp only
        rw [Spec.Code.play_ret]
        dsimp only
        let kp0 := leaf % 2 ^ params.subtreeHeight
        let tree0 := UInt64.ofNat (leaf / 2 ^ params.subtreeHeight)
        let leafCount := 2 ^ params.forsHeight
        have hFSec0 : ∀ j < params.forsTrees, ∀ u < leafCount,
            ((List.range (params.forsTrees * leafCount)).map fun i =>
              padBytes32 (secFn (pkSeed ++ encodeAdrs ⟨0, tree0, .forsPrf, UInt32.ofNat kp0,
                UInt32.ofNat ((0 + i) / leafCount), UInt32.ofNat ((0 + i) % leafCount)⟩))).getD
              (j * leafCount + u) zero32 =
            forsIndexedSecretLeaf ov ⟨[], [], pkSeed⟩ tree0 kp0 j u := by
          intro j hj u hu
          have hLcPos : 0 < leafCount := Nat.two_pow_pos _
          have hIdxLt : j * leafCount + u < params.forsTrees * leafCount := by
            have h1 := Nat.mul_le_mul_right leafCount hj
            rw [Nat.succ_mul] at h1; omega
          rw [list_getD_map_range _ _ zero32 hIdxLt, Nat.zero_add]
          have hDiv : (j * leafCount + u) / leafCount = j := by
            rw [Nat.mul_comm j, Nat.mul_add_div hLcPos, Nat.div_eq_of_lt hu, Nat.add_zero]
          have hMod : (j * leafCount + u) % leafCount = u := by
            rw [Nat.mul_comm j, Nat.mul_add_mod, Nat.mod_eq_of_lt hu]
          rw [hDiv, hMod, forsIndexedSecretLeaf_eq, secOverlaySuite_tagPrf_empty]
        have hFSec : ∀ j < params.forsTrees, ∀ u < leafCount,
            ((List.range (params.forsTrees * leafCount)).map fun i =>
              padBytes32 (secFn (pkSeed ++ encodeAdrs ⟨0, tree0, .forsPrf, UInt32.ofNat kp0,
                UInt32.ofNat (i / leafCount), UInt32.ofNat (i % leafCount)⟩))).getD
              (j * leafCount + u) zero32 =
            forsIndexedSecretLeaf ov ⟨[], [], pkSeed⟩ tree0 kp0 j u := by
          intro j hj u hu
          simpa only [Nat.zero_add] using hFSec0 j hj u hu
        have hOpsEq :
            ((List.range params.forsTrees).map fun j =>
              let idxJ := idxs.getD j 0
              { secretVal := ((List.range (params.forsTrees * leafCount)).map fun i =>
                  padBytes32 (secFn (pkSeed ++ encodeAdrs ⟨0, tree0, .forsPrf, UInt32.ofNat kp0,
                    UInt32.ofNat ((0 + i) / leafCount),
                    UInt32.ofNat ((0 + i) % leafCount)⟩))).getD (j * leafCount + idxJ) zero32
                authPath := buildMerkleAuthPathKp suite pkSeed 0 tree0 .forsTree (UInt32.ofNat kp0)
                  (fun u => forsIndexedLeafHash suite pkSeed tree0 kp0 j u
                    (((List.range (params.forsTrees * leafCount)).map fun i =>
                      padBytes32 (secFn (pkSeed ++ encodeAdrs ⟨0, tree0, .forsPrf, UInt32.ofNat kp0,
                        UInt32.ofNat ((0 + i) / leafCount),
                        UInt32.ofNat ((0 + i) % leafCount)⟩))).getD (j * leafCount + u) zero32))
                  params.forsHeight j 0 idxJ : ForsTreeOpening }) =
            buildProductionForsOpenings ov params ⟨[], [], pkSeed⟩ tree0 kp0 idxs := by
          rw [buildProductionForsOpenings_def]
          apply List.map_congr_left; intro j hjMem
          have hj := List.mem_range.mp hjMem
          have hIdxLt : idxs.getD j 0 < leafCount := by
            have hjL : j < idxs.length := (hIdxsLen idxs rfl) ▸ hj
            rw [list_getD_eq_getElem idxs 0 hjL]
            exact hIdxsBnd idxs rfl _ (List.getElem_mem hjL)
          dsimp only
          rw [hFSec0 j hj _ hIdxLt,
            secOverlaySuite_real_authPathKp suite pkSeed secFn 0 tree0 .forsTree _ _ _ (fun _ => rfl)]
          congr 1
          refine authPathKp_congr_bounded suite pkSeed 0 tree0 .forsTree (UInt32.ofNat kp0) _ _
            params.forsHeight j 0 _ (fun u hu => ?_)
          simp only [Nat.zero_mul, Nat.zero_add]; rw [hFSec j hj u hu]
          rw [forsIndexedLeafFn_eq, forsIndexedLeafHash_eq, forsIndexedLeafHash_eq,
            thChainF_eq, thChainF_eq, secOverlaySuite_nonPrf_thCall _ _ _ tagThF_ne_tagPrf.1]
        have hFpkEq :
            thTweakTl suite pkSeed ⟨0, tree0, .forsRoots, UInt32.ofNat kp0, 0, 0⟩
              ((List.range params.forsTrees).map fun j =>
                computeMerkleNodeKp suite pkSeed 0 tree0 .forsTree (UInt32.ofNat kp0)
                  (fun u => forsIndexedLeafHash suite pkSeed tree0 kp0 j u
                    (((List.range (params.forsTrees * leafCount)).map fun i =>
                      padBytes32 (secFn (pkSeed ++ encodeAdrs ⟨0, tree0, .forsPrf, UInt32.ofNat kp0,
                        UInt32.ofNat ((0 + i) / leafCount),
                        UInt32.ofNat ((0 + i) % leafCount)⟩))).getD (j * leafCount + u) zero32))
                  params.forsHeight j 0) =
            computeProductionForsPk ov params ⟨[], [], pkSeed⟩ tree0 kp0 := by
          rw [computeProductionForsPk_eq, thTweakTl_eq, thTweakTl_eq,
            secOverlaySuite_nonPrf_thCall _ _ _ tagThF_ne_tagPrf.2]
          congr 1; apply List.map_congr_left; intro j hjMem
          have hj := List.mem_range.mp hjMem
          dsimp only [Nat.zero_add]
          rw [secOverlaySuite_real_merkleNodeKp suite pkSeed secFn 0 tree0 .forsTree _ _ _
            (fun _ => rfl)]
          refine merkleNodeKp_congr_bounded suite pkSeed 0 tree0 .forsTree (UInt32.ofNat kp0) _ _
            params.forsHeight j 0 (fun u hu => ?_)
          simp only [Nat.zero_mul, Nat.zero_add]; rw [hFSec j hj u hu]
          rw [forsIndexedLeafFn_eq, forsIndexedLeafHash_eq, forsIndexedLeafHash_eq,
            thChainF_eq, thChainF_eq, secOverlaySuite_nonPrf_thCall _ _ _ tagThF_ne_tagPrf.1]
        rw [hOpsEq, hFpkEq, code_play_bind]
        have hLB : (used + params.forsTrees * 2 ^ params.forsHeight) +
            params.numLayers * (2 ^ params.subtreeHeight * params.ell1) ≤ qPrf := by
          unfold prfSecPerSignBudget at hBudget
          simp only [hSt, Bool.false_eq_true, ↓reduceIte] at hBudget; omega
        obtain ⟨hL1, hL2⟩ := signLayersSecCode_play suite params pkSeed pk.pkRoot _ secFn qPrf
          q.grindLimit 0 leaf _ params.numLayers (used + params.forsTrees * 2 ^ params.forsHeight) hLB
        dsimp only [leafCount] at *
        rw [hL1]
        cases signProductionHypertreeLayers ov params ⟨[], [], pkSeed⟩ pk.pkRoot _ q.grindLimit
            0 leaf _ params.numLayers with
        | none =>
          rw [Spec.Code.play_ret]
          exact ⟨rfl, by unfold prfSecPerSignBudget; simp only [hSt, Bool.false_eq_true, ↓reduceIte]; omega⟩
        | some ls =>
          rw [Spec.Code.play_ret]
          dsimp only [ov, tree0, kp0] at hL2 ⊢
          rw [secOverlaySuite_verify_eq]
          exact ⟨rfl, by unfold prfSecPerSignBudget; simp only [hSt, Bool.false_eq_true, ↓reduceIte]; omega⟩
  unfold signQuerySecCode
  rw [signQueryIdealPrf.public_eqs, signQueryWithRandFn.public_eqs, signCoreWithRand.public_eqs]
  have hPkDef : pk = derivePublicKey ov params ⟨[], [], pkSeed⟩ := by
    dsimp only [pk]; rw [derivePublicKeyIdealPrf.public_eqs]
  rw [← hPkDef]
  by_cases hSt : params.statefulJorts
  · simp only [hSt, ↓reduceIte]
    split
    · rw [Spec.Code.play_ret]; exact ⟨rfl, Nat.le_add_right _ _⟩
    · have hC := hCorePlay q.epoch none (fun _ h => nomatch h) (fun _ h => nomatch h)
      dsimp only at hC ⊢
      simpa only [hSt, ↓reduceIte] using hC
  · simp only [hSt, Bool.false_eq_true, ↓reduceIte]
    split
    · rw [Spec.Code.play_ret]; exact ⟨rfl, Nat.le_add_right _ _⟩
    · have hXof : ∀ rR pR mu first n,
          thXofMsgBlocks ov rR pk.pkSeed pR mu first n =
          thXofMsgBlocks suite rR pk.pkSeed pR mu first n := by
        intro rR pR mu first n; induction n generalizing first with
        | zero => rw [thXofMsgBlocks_zero, thXofMsgBlocks_zero]
        | succ n' ihX =>
          rw [thXofMsgBlocks_succ, thXofMsgBlocks_succ, secOverlaySuite_thCall_cons2, ihX]
      have hDer : deriveProductionStatelessInputs ov params
          (rfMsg (encodePrfMsg65 q.randomness (thPreHash ov pk.pkSeed pk.pkRoot q.message)))
          pk.pkSeed pk.pkRoot (thPreHash ov pk.pkSeed pk.pkRoot q.message) =
        deriveProductionStatelessInputs suite params
          (rfMsg (encodePrfMsg65 q.randomness (thPreHash suite pk.pkSeed pk.pkRoot q.message)))
          pk.pkSeed pk.pkRoot (thPreHash suite pk.pkSeed pk.pkRoot q.message) := by
        rw [← hMuEq, deriveProductionStatelessInputs_eq, deriveProductionStatelessInputs_eq]
        dsimp only
        rw [thXofMsg_eq, thXofMsg_eq, hXof]
      rw [hDer]
      cases hD : deriveProductionStatelessInputs suite params
          (rfMsg (encodePrfMsg65 q.randomness (thPreHash suite pk.pkSeed pk.pkRoot q.message)))
          pk.pkSeed pk.pkRoot (thPreHash suite pk.pkSeed pk.pkRoot q.message) with
      | none => rw [Spec.Code.play_ret]; exact ⟨rfl, Nat.le_add_right _ _⟩
      | some li =>
        have hBnds := deriveProductionStatelessInputs_bounds suite params _ _ _ _ li.1 li.2 hD
        have hC := hCorePlay li.1 (some li.2)
          (fun idxs hEq => by injection hEq with hE; subst hE; exact hBnds.2.2.2.2)
          (fun idxs hEq => by injection hEq with hE; subst hE; exact hBnds.2.2.2.1)
        dsimp only at hC ⊢
        simpa only [hSt, Bool.false_eq_true, ↓reduceIte] using hC

private theorem prfSecHopTreeCode_play (latchOn : Bool) (suite : TweakableHashSuite)
    (params : PqHashParams) (pkSeed : List UInt8) (rfMsg secFn : Spec.Bytes → Spec.Bytes)
    (qPrf : Nat) :
    ∀ {qH qS : Nat} (t : ProdAdaptiveTree (List UInt8 × PqHashSig)) (lo used : Nat)
      (log : List (List UInt8 × PqHashSig)),
      ProdDualBounded qH qS t →
      used + qS * prfSecPerSignBudget params ≤ qPrf →
      let pk := derivePublicKeyIdealPrf suite params pkSeed secFn
      let signFn := signQueryIdealPrf suite params pkSeed rfMsg secFn
      let run := evalLatchedAdaptiveTree latchOn suite.rawHash signFn t lo
      (Spec.Code.play (Spec.budgetedFunOracle secFn qPrf)
        (prfSecHopTreeCode latchOn suite params pkSeed pk rfMsg t lo log) used).1 =
      (verifyProductionPqHashSig suite params pk run.1.1 run.1.2 &&
        decide (run.1.1 ∉ (log ++ signLogFromOracle signFn run.2).map Prod.fst))
  | _, _, .pure (msgStar, sigStar), _, used, log, _, _ => by
    unfold prfSecHopTreeCode
    dsimp only
    rw [Spec.Code.play_ret, evalLatchedAdaptiveTree.public_eq_1]
    dsimp only
    rw [signLogFromOracle.public_eq_1]
    congr 1
    exact fresh_decide_congr rfl (List.append_nil log).symm
  | 0, _, .hashQuery _ _, _, _, _, hB, _ => False.elim hB
  | _ + 1, _, .hashQuery x next, lo, used, log, hB, hBudget => by
    unfold prfSecHopTreeCode
    dsimp only
    rw [evalLatchedAdaptiveTree.public_eq_2]
    exact prfSecHopTreeCode_play latchOn suite params pkSeed rfMsg secFn qPrf
      (next (suite.rawHash x)) lo used log (hB _) hBudget
  | _, 0, .signQuery _ _, _, _, _, hB, _ => False.elim hB
  | _, qS + 1, .signQuery q next, lo, used, log, hB, hBudget => by
    unfold prfSecHopTreeCode
    dsimp only
    rw [evalLatchedAdaptiveTree_sign]
    by_cases hAdm : latchOn = false ∨ lo ≤ q.epoch
    · rw [ite_eq_left hAdm, ite_eq_left hAdm, code_play_bind]
      have hStepB : used + prfSecPerSignBudget params ≤ qPrf := by
        rw [Nat.succ_mul] at hBudget; omega
      obtain ⟨hS1, hS2⟩ := signQuerySecCode_play suite params pkSeed rfMsg secFn qPrf used q hStepB
      dsimp only
      rw [hS1]
      have hNextB : (Spec.Code.play (Spec.budgetedFunOracle secFn qPrf)
          (signQuerySecCode suite params pkSeed (derivePublicKeyIdealPrf suite params pkSeed secFn)
            rfMsg q) used).2 + qS * prfSecPerSignBudget params ≤ qPrf := by
        rw [Nat.succ_mul] at hBudget; omega
      have ih := prfSecHopTreeCode_play latchOn suite params pkSeed rfMsg secFn qPrf
        (next (signQueryIdealPrf suite params pkSeed rfMsg secFn q)) (q.epoch + 1) _
        (match signQueryIdealPrf suite params pkSeed rfMsg secFn q with
         | none => log
         | some sig => log ++ [(q.message, sig)])
        (hB _) hNextB
      rw [ih]
      congr 1
      exact fresh_decide_congr rfl (by
        rw [signLogFromOracle_cons]
        cases signQueryIdealPrf suite params pkSeed rfMsg secFn q with
        | none => simp
        | some sig => simp [List.append_assoc])
    · rw [ite_eq_right hAdm, ite_eq_right hAdm]
      exact prfSecHopTreeCode_play latchOn suite params pkSeed rfMsg secFn qPrf (next none) lo
        used log (hB none) (by rw [Nat.succ_mul] at hBudget; omega)

private theorem prfSecHopDistinguisher_play {qHash qSign : Nat} (latchOn : Bool)
    (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (rfMsg secFn : Spec.Bytes → Spec.Bytes)
    (A : SeedWithheldEufCmaAdv qHash qSign) (qPrf : Nat)
    (hqPrf : prfSecQueryBudget params qSign ≤ qPrf) :
    (Spec.Code.play (Spec.budgetedFunOracle secFn qPrf)
      (prfSecHopDistinguisher latchOn suite params pkSeed rfMsg A) 0).1 =
    (ExecEufCmaIdealPrfGame latchOn Nat.one_pos suite params (fun _ => pkSeed) (fun _ => rfMsg)
      (fun _ => secFn) (fun _ => A)).win ⟨0, Nat.one_pos⟩ := by
  unfold prfSecHopDistinguisher
  rw [ExecEufCmaIdealPrfGame_win, code_play_bind]
  have hTopB : 0 + 2 ^ params.subtreeHeight * params.ell1 ≤ qPrf := by
    unfold prfSecQueryBudget at hqPrf; omega
  obtain ⟨hU1, _, hWotsTop⟩ := fetchSubtreeWotsPkCode_play suite params pkSeed secFn qPrf
    (UInt32.ofNat (params.numLayers - 1)) 0 0 hTopB
  dsimp only
  have hPkRootEq :
      computeMerkleNode suite pkSeed (UInt32.ofNat (params.numLayers - 1)) 0 .tree
        (Spec.Code.play (Spec.budgetedFunOracle secFn qPrf)
          (fetchSubtreeWotsPkCode suite params pkSeed (UInt32.ofNat (params.numLayers - 1)) 0) 0).1.2
        params.subtreeHeight 0 =
      (derivePublicKeyIdealPrf suite params pkSeed secFn).pkRoot := by
    rw [derivePublicKeyIdealPrf.public_eqs]
    unfold derivePublicKey
    dsimp only
    rw [computeXmssSubtreeRoot_eq, ← computeMerkleNodeKp_zero_eq, ← computeMerkleNodeKp_zero_eq,
      secOverlaySuite_real_merkleNodeKp suite pkSeed secFn _ _ _ _ _ _ (fun _ => rfl)]
    exact merkleNodeKp_congr_bounded suite pkSeed _ 0 .tree 0 _ _ params.subtreeHeight 0 0
      (fun i hi => by simpa using hWotsTop i hi)
  have hPkEq : (⟨pkSeed, computeMerkleNode suite pkSeed (UInt32.ofNat (params.numLayers - 1)) 0
      .tree (Spec.Code.play (Spec.budgetedFunOracle secFn qPrf)
        (fetchSubtreeWotsPkCode suite params pkSeed (UInt32.ofNat (params.numLayers - 1)) 0) 0).1.2
      params.subtreeHeight 0⟩ : PqPublicKey) =
      derivePublicKeyIdealPrf suite params pkSeed secFn := by
    rw [hPkRootEq, derivePublicKeyIdealPrf.public_eqs]; unfold derivePublicKey; rfl
  rw [hPkEq]
  have hTreeB : (Spec.Code.play (Spec.budgetedFunOracle secFn qPrf)
      (fetchSubtreeWotsPkCode suite params pkSeed (UInt32.ofNat (params.numLayers - 1)) 0) 0).2 +
      qSign * prfSecPerSignBudget params ≤ qPrf := by
    rw [hU1]; unfold prfSecQueryBudget at hqPrf; omega
  have hPlay := prfSecHopTreeCode_play latchOn suite params pkSeed rfMsg secFn qPrf
    ((canonicalizeAdvOptRand A).run (derivePublicKeyIdealPrf suite params pkSeed secFn))
    0 _ [] ((canonicalizeAdvOptRand A).bounded _) hTreeB
  exact hPlay

/-- **Hop 2 Theorem (`hulsing_hop2_prfSec_idealization`).**
    Replaces `thSecretPrf suite pkSeed sk.skSeed` across public-key derivation and all `≤ qSign`
    adaptive signatures with a uniform secret function `rfSec`, paying `+ εPrfSec` under
    `Spec.PrfHard` while leaving `suite.rawHash` **100% untouched** for the adversary and verifier. -/
theorem hulsing_hop2_prfSec_idealization {n nC nA qHash qSign : Nat} (latchOn : Bool)
    (hPos : 0 < n) (suite : TweakableHashSuite) (params : PqHashParams)
    (seedLen keyLen qPrf : Nat) (hqPrf : prfSecQueryBudget params qSign ≤ qPrf)
    (π : Spec.CoinSplit n nC nA)
    (sampleSec : Fin nC → Spec.Bytes × (Spec.Bytes → Spec.Bytes))
    (hSampleSec : Spec.UniformOn (Spec.PrfSampleOk keyLen (seedLen + 32) 32) sampleSec)
    (pkSeedA : Fin nA → List UInt8) (hSeedLen : ∀ a, (pkSeedA a).length = seedLen)
    (rfMsgA : Fin nA → Spec.Bytes → Spec.Bytes)
    (adv : Fin nA → SeedWithheldEufCmaAdv qHash qSign)
    {𝒜Sec : Spec.Code Spec.byteOracleIface Bool → Prop}
    (hClassSec : ∀ a : Fin nA,
      𝒜Sec (prfSecHopDistinguisher latchOn suite params (pkSeedA a) (rfMsgA a) (adv a)))
    {εPrfSec : Spec.RatBound}
    (hPrfSec : Spec.PrfHard 𝒜Sec (suitePrfSec seedLen suite) keyLen (seedLen + 32) 32 qPrf εPrfSec) :
    let gHop1 := ExecEufCmaRandIdealGame latchOn hPos suite params
      (fun ω => pkSeedA (π.advc ω)) (fun ω => (sampleSec (π.chal ω)).1)
      (fun ω => rfMsgA (π.advc ω)) (fun ω => adv (π.advc ω))
    let gHop2 := ExecEufCmaIdealPrfGame latchOn hPos suite params
      (fun ω => pkSeedA (π.advc ω)) (fun ω => rfMsgA (π.advc ω))
      (fun ω => (sampleSec (π.chal ω)).2) (fun ω => adv (π.advc ω))
    Spec.GameBound gHop1.winProb (gHop2.winProb.add εPrfSec) := by
  intro gHop1 gHop2
  let D : Fin nA → Spec.Code Spec.byteOracleIface Bool := fun a =>
    prfSecHopDistinguisher latchOn suite params (pkSeedA a) (rfMsgA a) (adv a)
  have hRealEq : ∀ ω : Fin n,
      gHop1.win ω =
      (Spec.prfRealGame hPos (suitePrfSec seedLen suite) qPrf
        (fun z => (sampleSec (π.chal z)).1) (fun z => D (π.advc z))).win ω := by
    intro ω
    rw [Spec.prfRealGame.public_eqs]
    dsimp only [D]
    rw [prfSecHopDistinguisher_play latchOn suite params (pkSeedA (π.advc ω)) (rfMsgA (π.advc ω))
      (suitePrfSec seedLen suite (sampleSec (π.chal ω)).1) (adv (π.advc ω)) qPrf hqPrf]
    dsimp only [gHop1]
    rw [ExecEufCmaRandIdealGame_win, ExecEufCmaIdealPrfGame_win]
    dsimp only
    have hPk := derivePublicKeyIdealPrf_real_eq suite params (pkSeedA (π.advc ω))
      (sampleSec (π.chal ω)).1 (hSeedLen (π.advc ω))
    have hSign : signQueryIdealPrf suite params (pkSeedA (π.advc ω)) (rfMsgA (π.advc ω))
        (suitePrfSec seedLen suite (sampleSec (π.chal ω)).1) =
      signQueryWithRandFn suite params (pkSeedA (π.advc ω)) (sampleSec (π.chal ω)).1
        (rfMsgA (π.advc ω)) :=
      funext (signQueryIdealPrf_real_eq suite params (pkSeedA (π.advc ω))
        (sampleSec (π.chal ω)).1 (hSeedLen (π.advc ω)) (rfMsgA (π.advc ω)))
    rw [hPk, hSign]
  have hIdealEq : ∀ ω : Fin n,
      gHop2.win ω =
      (Spec.prfIdealGame hPos qPrf
        (fun z => (sampleSec (π.chal z)).2) (fun z => D (π.advc z))).win ω := by
    intro ω
    rw [Spec.prfIdealGame.public_eqs]
    dsimp only [D, gHop2]
    have hP := (prfSecHopDistinguisher_play latchOn suite params (pkSeedA (π.advc ω))
      (rfMsgA (π.advc ω)) ((sampleSec (π.chal ω)).2) (adv (π.advc ω)) qPrf hqPrf).symm
    rw [ExecEufCmaIdealPrfGame_win] at hP ⊢
    exact hP
  have hDist : Spec.GameBound (Spec.AdvDist gHop1 gHop2) εPrfSec := by
    rw [Spec.FinGame.ext_win hRealEq, Spec.FinGame.ext_win hIdealEq]
    exact hPrfSec n nC nA hPos π sampleSec hSampleSec D hClassSec
  exact Spec.RatBound.le_trans (winProb_le_add_advDist gHop1 gHop2)
    (Spec.RatBound.add_le_add (Spec.RatBound.le_refl _) hDist)

/-! ## §2. Hop 3: Standard-Model `SM-DT-UD` Undetectability & WOTS+C Chain-Step Simulation -/

/-- Sample set for multi-target distinct-tweak undetectability (`SM-DT-UD`):
    a `seedLen`-byte seed, `q` hidden `inputLen`-byte inputs (for the real game), and `q` uniform
    `outLen`-byte digests (for the ideal game). -/
def SmDtUdSampleOk (seedLen inputLen outLen q : Nat)
    (x : Spec.Bytes × List Spec.Bytes × List Spec.Bytes) : Prop :=
  x.1.length = seedLen ∧
  (x.2.1.length = q ∧ ∀ m ∈ x.2.1, m.length = inputLen) ∧
  (x.2.2.length = q ∧ ∀ y ∈ x.2.2, y.length = outLen)

#export_eqns SmDtUdSampleOk

/-- Ideal `SM-DT-UD` challenger oracle: before `reveal`, the `i`-th distinct-tweak `.target` call
    returns the independent uniform digest `udDigest i` instead of `th seed tweak (hidden i)`. -/
def smDtUdIdealOracle (q : Nat) (udDigest : Nat → Spec.Bytes) (st : Spec.TargetState) :
    (qr : Spec.targetIface.Query) → Spec.targetIface.Resp qr × Spec.TargetState
  | .target t _ =>
    if st.revealed = false ∧ st.targets.length < q ∧ t ∉ st.targets.map Prod.fst then
      (some (udDigest st.targets.length),
        { st with targets := st.targets ++ [(t, udDigest st.targets.length)] })
    else (none, st)
  | .reveal => (some st.seed, { st with revealed := true })

def smDtUdRealGame {n : Nat} (hPos : 0 < n) (th : Spec.Bytes → Spec.Bytes → Spec.Bytes → Spec.Bytes)
    (q : Nat) (seed : Fin n → Spec.Bytes) (hidden : Fin n → Nat → Spec.Bytes)
    (D : Fin n → Spec.Code Spec.targetIface Bool) : Spec.FinGame n :=
  ⟨hPos, fun ω => (Spec.Code.play (Spec.smDtPreOracle th q (hidden ω)) (D ω) ⟨seed ω, [], false⟩).1⟩

def smDtUdIdealGame {n : Nat} (hPos : 0 < n) (q : Nat)
    (seed : Fin n → Spec.Bytes) (udDigest : Fin n → Nat → Spec.Bytes)
    (D : Fin n → Spec.Code Spec.targetIface Bool) : Spec.FinGame n :=
  ⟨hPos, fun ω => (Spec.Code.play (smDtUdIdealOracle q (udDigest ω)) (D ω) ⟨seed ω, [], false⟩).1⟩

/-- **`SM-DT-UD` Hardness (`SmDtUdHard`) over `Spec.FinGame`.** -/
@[expose] def SmDtUdHard (𝒜 : Spec.Code Spec.targetIface Bool → Prop)
    (th : Spec.Bytes → Spec.Bytes → Spec.Bytes → Spec.Bytes)
    (seedLen inputLen outLen q : Nat) (ε : Spec.RatBound) : Prop :=
  ∀ (n nC nA : Nat) (hPos : 0 < n) (π : Spec.CoinSplit n nC nA)
    (sample : Fin nC → Spec.Bytes × List Spec.Bytes × List Spec.Bytes),
    Spec.UniformOn (SmDtUdSampleOk seedLen inputLen outLen q) sample →
    ∀ D : Fin nA → Spec.Code Spec.targetIface Bool, (∀ a : Fin nA, 𝒜 (D a)) →
      Spec.GameBound
        (Spec.AdvDist
          (smDtUdRealGame hPos th q (fun ω => (sample (π.chal ω)).1)
            (fun ω i => (sample (π.chal ω)).2.1.getD i []) (fun ω => D (π.advc ω)))
          (smDtUdIdealGame hPos q (fun ω => (sample (π.chal ω)).1)
            (fun ω i => (sample (π.chal ω)).2.2.getD i []) (fun ω => D (π.advc ω)))) ε

/-- Test a single challenge digest with the revealed seed. -/
def udDigestTest (tweak : Spec.Bytes) (test : Spec.Bytes → Spec.Bytes → Bool) :
    Spec.Code Spec.targetIface Bool :=
  .call (.target tweak []) fun y => .call .reveal fun seed => .ret (test (seed.getD []) (y.getD []))

theorem udDigestTest_real_win {n : Nat} (hPos : 0 < n)
    (th : Spec.Bytes → Spec.Bytes → Spec.Bytes → Spec.Bytes) (seed : Fin n → Spec.Bytes)
    (hidden : Fin n → Nat → Spec.Bytes) (tweak : Spec.Bytes)
    (test : Fin n → Spec.Bytes → Spec.Bytes → Bool) (z : Fin n) :
    (smDtUdRealGame hPos th 1 seed hidden (fun i => udDigestTest tweak (test i))).win z =
      test z (seed z) (th (seed z) tweak (hidden z 0)) := by
  simp only [smDtUdRealGame, udDigestTest, Spec.Code.play_call, Spec.smDtPreOracle_target,
    Spec.smDtPreOracle_reveal, Spec.Code.play_ret, Option.getD]
  rfl

theorem udDigestTest_ideal_win {n : Nat} (hPos : 0 < n) (seed : Fin n → Spec.Bytes)
    (digest : Fin n → Nat → Spec.Bytes) (tweak : Spec.Bytes)
    (test : Fin n → Spec.Bytes → Spec.Bytes → Bool) (z : Fin n) :
    (smDtUdIdealGame hPos 1 seed digest (fun i => udDigestTest tweak (test i))).win z =
      test z (seed z) (digest z 0) := by
  simp only [smDtUdIdealGame, udDigestTest, Spec.Code.play_call, smDtUdIdealOracle,
    Spec.Code.play_ret, Option.getD]
  rfl

/-- At chain step `st = 0` and on FORS leaves, secret inputs are already uniform after Hop 2 (`0` UD loss). -/
theorem smDtUd_zero_loss_refl {n : Nat} (G : Spec.FinGame n) :
    Spec.GameBound G.winProb (G.winProb.add Spec.RatBound.zero) := by
  unfold Spec.GameBound Spec.RatBound.le Spec.RatBound.add Spec.RatBound.zero
  dsimp only
  simp

/-- **Hop 3 WOTS+C Chain-Step Simulation Theorem (`hulsing_hop3_ud_chain_simulation`).** -/
theorem hulsing_hop3_ud_chain_simulation {n nC nA : Nat} (hPos : 0 < n)
    (GReal GSim : Spec.FinGame n)
    (th : Spec.Bytes → Spec.Bytes → Spec.Bytes → Spec.Bytes)
    (seedLen inputLen outLen q : Nat)
    (π : Spec.CoinSplit n nC nA)
    (sample : Fin nC → Spec.Bytes × List Spec.Bytes × List Spec.Bytes)
    (hSample : Spec.UniformOn (SmDtUdSampleOk seedLen inputLen outLen q) sample)
    (D : Fin nA → Spec.Code Spec.targetIface Bool)
    {𝒜Ud : Spec.Code Spec.targetIface Bool → Prop} (hClass : ∀ a, 𝒜Ud (D a))
    {εUd : Spec.RatBound} (hUd : SmDtUdHard 𝒜Ud th seedLen inputLen outLen q εUd)
    (hReal : ∀ ω, GReal.win ω =
      (smDtUdRealGame hPos th q (fun z => (sample (π.chal z)).1)
        (fun z i => (sample (π.chal z)).2.1.getD i []) (fun z => D (π.advc z))).win ω)
    (hSim : ∀ ω, GSim.win ω =
      (smDtUdIdealGame hPos q (fun z => (sample (π.chal z)).1)
        (fun z i => (sample (π.chal z)).2.2.getD i []) (fun z => D (π.advc z))).win ω) :
    Spec.GameBound GReal.winProb (GSim.winProb.add εUd) := by
  have hDist : Spec.GameBound (Spec.AdvDist GReal GSim) εUd := by
    rw [Spec.FinGame.ext_win hReal, Spec.FinGame.ext_win hSim]
    exact hUd n nC nA hPos π sample hSample D hClass
  exact Spec.RatBound.le_trans (winProb_le_add_advDist GReal GSim)
    (Spec.RatBound.add_le_add (Spec.RatBound.le_refl _) hDist)

/-- `#tooth` A constant empty-output hash is NOT `SmDtUdHard` on `outLen ≥ 1`. -/
def emptyUdDistinguisher : Spec.Code Spec.targetIface Bool :=
  .call (.target [] []) (fun yOpt => .ret (decide (yOpt = some [])))

theorem smDtUdHard_constHash_refuted {nC : Nat} (hPos : 0 < nC)
    (seedLen inputLen outLen q : Nat) (hOut : 0 < outLen) (hq : 0 < q)
    (sample : Fin nC → Spec.Bytes × List Spec.Bytes × List Spec.Bytes)
    (hU : Spec.UniformOn (SmDtUdSampleOk seedLen inputLen outLen q) sample)
    (𝒜 : Spec.Code Spec.targetIface Bool → Prop) (h𝒜 : 𝒜 emptyUdDistinguisher)
    {ε : Spec.RatBound} (hε : ε.num < ε.den) :
    ¬ SmDtUdHard 𝒜 (fun _ _ _ => []) seedLen inputLen outLen q ε := by
  intro hHard
  refine Spec.advDist_not_bound_of_always_never _ _ (fun ω => ?_) (fun ω => ?_) hε
    (hHard nC nC 1 hPos (Spec.CoinSplit.challengerOnly nC) sample hU
      (fun _ => emptyUdDistinguisher) (fun _ => h𝒜))
  · dsimp only [smDtUdRealGame, emptyUdDistinguisher]
    rw [Spec.Code.play_call, Spec.smDtPreOracle_target]
    have hc : false = false ∧ ([] : List (Spec.Bytes × Spec.Bytes)).length < q ∧
        ([] : Spec.Bytes) ∉ ([] : List (Spec.Bytes × Spec.Bytes)).map Prod.fst :=
      ⟨rfl, hq, fun h => nomatch h⟩
    rw [ite_eq_left hc, Spec.Code.play_ret]; rfl
  · dsimp only [smDtUdIdealGame, emptyUdDistinguisher]
    rw [Spec.Code.play_call, Spec.Code.play_ret]
    unfold smDtUdIdealOracle
    dsimp only
    have hc : false = false ∧ ([] : List (Spec.Bytes × Spec.Bytes)).length < q ∧
        ([] : Spec.Bytes) ∉ ([] : List (Spec.Bytes × Spec.Bytes)).map Prod.fst :=
      ⟨rfl, hq, fun h => nomatch h⟩
    apply decide_eq_false
    rw [ite_eq_left hc]
    dsimp only
    have hMemOk := hU.mem ((Spec.CoinSplit.challengerOnly nC).chal ω)
    have hY0Len : (((sample ((Spec.CoinSplit.challengerOnly nC).chal ω)).2.2).getD 0 []).length =
        outLen := by
      have hL := hMemOk.2.2.1
      cases hYs : (sample ((Spec.CoinSplit.challengerOnly nC).chal ω)).2.2 with
      | nil => rw [hYs] at hL; omega
      | cons y0 _ =>
        have hy0Mem : y0 ∈ (sample ((Spec.CoinSplit.challengerOnly nC).chal ω)).2.2 := by
          rw [hYs]; exact List.mem_cons_self
        exact hMemOk.2.2.2 y0 hy0Mem
    intro hSomeEq
    injection hSomeEq with hNil
    change (((sample ((Spec.CoinSplit.challengerOnly nC).chal ω)).2.2).getD 0 []) = [] at hNil
    rw [hNil] at hY0Len
    exact Nat.ne_of_lt hOut hY0Len

#verify_constructive
  Qsag.udDigestTest_real_win Qsag.udDigestTest_ideal_win
  Qsag.prfSecHopDistinguisher_within
  Qsag.hulsing_hop2_prfSec_idealization
  Qsag.smDtUd_zero_loss_refl
  Qsag.hulsing_hop3_ud_chain_simulation
  Qsag.smDtUdHard_constHash_refuted

#tooth_pair Qsag.hulsing_hop2_prfSec_idealization vs Qsag.prfMsg_empty_refuted
#tooth_pair Qsag.hulsing_hop3_ud_chain_simulation vs Qsag.smDtUdHard_constHash_refuted

theorem prfSecHopTree_pure (latch : Bool) (suite : TweakableHashSuite) (p : PqHashParams)
    (s : Spec.Bytes) (pk : PqPublicKey) (msg : Spec.Bytes → Spec.Bytes) (m : Spec.Bytes) (sig : PqHashSig) (lo : Nat) (log : List (Spec.Bytes × PqHashSig)) :
    prfSecHopTreeCode latch suite p s pk msg (.pure (m,sig)) lo log =
      .ret (verifyProductionPqHashSig suite p pk m sig && decide (m ∉ log.map Prod.fst)) := by rw [prfSecHopTreeCode]

#verify_constructive prfSecHopTree_pure

#export_eqns prfSecHopDistinguisher smDtUdRealGame smDtUdIdealGame

end Qsag
end
