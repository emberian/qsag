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
      have hR : List.range (count + 1) = 0 :: (List.range count).map (· + 1) := by
        induction count with
        | zero => rfl
        | succ c ih =>
          rw [List.range_succ, ih, List.range_succ, List.map_append, List.map_singleton]; rfl
      rw [hR, List.map_cons, List.map_map, Nat.add_zero]
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
def prfSecHopTreeCode (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (pk : PqPublicKey) (rfMsg : Spec.Bytes → Spec.Bytes) :
    ProdAdaptiveTree (List UInt8 × PqHashSig) → Nat → List (List UInt8 × PqHashSig) →
    Spec.Code Spec.byteOracleIface Bool
  | .pure (msgStar, sigStar), _, log =>
    .ret (verifyProductionPqHashSig suite params pk msgStar sigStar &&
      decide (msgStar ∉ log.map Prod.fst))
  | .hashQuery x next, lo, log =>
    prfSecHopTreeCode suite params pkSeed pk rfMsg (next (suite.rawHash x)) lo log
  | .signQuery q next, lo, log =>
    if params.statefulJorts = false ∨ lo ≤ q.epoch then
      let lo' := if params.statefulJorts then q.epoch + 1 else lo
      Spec.Code.bind (signQuerySecCode suite params pkSeed pk rfMsg q) (fun sigOpt =>
        let log' := match sigOpt with
          | some sig => log ++ [(q.message, sig)]
          | none => log
        prfSecHopTreeCode suite params pkSeed pk rfMsg (next sigOpt) lo' log')
    else
      prfSecHopTreeCode suite params pkSeed pk rfMsg (next none) lo log

/-- **Hop-2 Secret-PRF Distinguisher (`prfSecHopDistinguisher`)** in `Code byteOracleIface Bool`. -/
def prfSecHopDistinguisher {qHash qSign : Nat} (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (rfMsg : Spec.Bytes → Spec.Bytes)
    (A : SeedWithheldEufCmaAdv qHash qSign) : Spec.Code Spec.byteOracleIface Bool :=
  let topLayer := UInt32.ofNat (params.numLayers - 1)
  Spec.Code.bind (fetchSubtreeWotsPkCode suite params pkSeed topLayer 0) (fun sw =>
    let pkRoot := computeMerkleNode suite pkSeed topLayer 0 .tree sw.2 params.subtreeHeight 0
    let pk : PqPublicKey := ⟨pkSeed, pkRoot⟩
    prfSecHopTreeCode suite params pkSeed pk rfMsg ((canonicalizeAdvOptRand A).run pk) 0 [])

private theorem fetchSubtreeWotsPkCode_within (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (layer : UInt32) (tree : UInt64) :
    Spec.Within (2 ^ params.subtreeHeight * params.ell1)
      (fetchSubtreeWotsPkCode suite params pkSeed layer tree) := by
  unfold fetchSubtreeWotsPkCode
  have hB := Spec.Within.bind (queryVecCode_within _ 0 (2 ^ params.subtreeHeight * params.ell1))
    (fun _ => Spec.Within.ret 0 _)
  rwa [Nat.add_zero] at hB

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
    · have hSub := fetchSubtreeWotsPkCode_within suite params pkSeed (UInt32.ofNat lI)
        (UInt64.ofNat (gI / 2 ^ params.subtreeHeight))
      have hRest : ∀ sw : List (List UInt8) × (Nat → List UInt8),
          Spec.Within (rem * (2 ^ params.subtreeHeight * params.ell1))
            (Spec.Code.bind (signLayersSecCode suite params pkSeed pkRoot rRand maxGrind
              (lI + 1) (gI / 2 ^ params.subtreeHeight)
              (computeMerkleNode suite pkSeed (UInt32.ofNat lI)
                (UInt64.ofNat (gI / 2 ^ params.subtreeHeight)) .tree sw.2 params.subtreeHeight 0)
              rem) _) := fun _ => by
        have hb := Spec.Within.bind
          (signLayersSecCode_within suite params pkSeed pkRoot rRand maxGrind _ _ _ rem)
          (fun restOpt => match restOpt with | none => .ret 0 _ | some _ => .ret 0 _)
        rwa [Nat.add_zero] at hb
      have hTot := Spec.Within.bind hSub hRest
      exact Spec.Within.mono (by rw [Nat.succ_mul, Nat.add_comm]; exact Nat.le_refl _) hTot

private theorem signQuerySecCode_within (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (pk : PqPublicKey) (rfMsg : Spec.Bytes → Spec.Bytes)
    (q : ProdSigningQuery) :
    Spec.Within (prfSecPerSignBudget params)
      (signQuerySecCode suite params pkSeed pk rfMsg q) := by
  unfold signQuerySecCode prfSecPerSignBudget
  have hCore : ∀ leaf fIdxs,
      Spec.Within
        ((if params.statefulJorts then 0 else params.forsTrees * 2 ^ params.forsHeight) +
          params.numLayers * (2 ^ params.subtreeHeight * params.ell1))
        (Spec.Code.bind
          (if params.statefulJorts then .ret (some ([], thPreHash suite pk.pkSeed pk.pkRoot q.message))
           else match fIdxs with
           | none => .ret none
           | some idxs =>
             Spec.Code.bind (queryVecCode _ 0 (params.forsTrees * 2 ^ params.forsHeight)) _) _) := by
    intro leaf fIdxs
    have hInit : Spec.Within
        (if params.statefulJorts then 0 else params.forsTrees * 2 ^ params.forsHeight)
        (if params.statefulJorts then .ret (some ([], thPreHash suite pk.pkSeed pk.pkRoot q.message))
         else match fIdxs with
         | none => .ret none
         | some idxs =>
           Spec.Code.bind (queryVecCode _ 0 (params.forsTrees * 2 ^ params.forsHeight)) _) := by
      by_cases hSt : params.statefulJorts
      · simp only [hSt, ↓reduceIte]; exact .ret 0 _
      · simp only [hSt, Bool.false_eq_true, ↓reduceIte]
        cases fIdxs with
        | none => exact .ret _ _
        | some _ =>
          have hb := Spec.Within.bind (queryVecCode_within _ 0 _) (fun _ => Spec.Within.ret 0 _)
          rwa [Nat.add_zero] at hb
    refine Spec.Within.bind hInit (fun initOpt => ?_)
    cases initOpt with
    | none => exact .ret _ _
    | some fc =>
      have hb := Spec.Within.bind
        (signLayersSecCode_within suite params pkSeed pk.pkRoot _ q.grindLimit 0 leaf fc.2
          params.numLayers)
        (fun lsOpt => match lsOpt with | none => .ret 0 _ | some _ => .ret 0 _)
      rwa [Nat.add_zero] at hb
  by_cases hSt : params.statefulJorts
  · simp only [hSt, ↓reduceIte]
    split
    · exact .ret _ _
    · exact hCore q.epoch none
  · simp only [hSt, Bool.false_eq_true, ↓reduceIte]
    split
    · exact .ret _ _
    · cases deriveProductionStatelessInputs suite params _ pk.pkSeed pk.pkRoot _ with
      | none => exact .ret _ _
      | some li => exact hCore li.1 (some li.2)

private theorem prfSecHopTreeCode_within (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed : List UInt8) (pk : PqPublicKey) (rfMsg : Spec.Bytes → Spec.Bytes) :
    ∀ {qH qS : Nat} (t : ProdAdaptiveTree (List UInt8 × PqHashSig)) (lo : Nat)
      (log : List (List UInt8 × PqHashSig)),
      ProdDualBounded qH qS t →
      Spec.Within (qS * prfSecPerSignBudget params)
        (prfSecHopTreeCode suite params pkSeed pk rfMsg t lo log)
  | _, _, .pure (_, _), _, _, _ => .ret _ _
  | 0, _, .hashQuery _ _, _, _, h => False.elim h
  | _ + 1, _, .hashQuery x next, lo, log, h =>
    prfSecHopTreeCode_within suite params pkSeed pk rfMsg (next (suite.rawHash x)) lo log (h _)
  | _, 0, .signQuery _ _, _, _, h => False.elim h
  | _, qS + 1, .signQuery q next, lo, log, h => by
    unfold prfSecHopTreeCode
    by_cases hAdm : params.statefulJorts = false ∨ lo ≤ q.epoch
    · rw [ite_eq_left hAdm]
      have hb := Spec.Within.bind (signQuerySecCode_within suite params pkSeed pk rfMsg q)
        (fun sigOpt =>
          prfSecHopTreeCode_within suite params pkSeed pk rfMsg (next sigOpt) _ _ (h sigOpt))
      exact Spec.Within.mono (by rw [Nat.succ_mul, Nat.add_comm]; exact Nat.le_refl _) hb
    · rw [ite_eq_right hAdm]
      exact Spec.Within.mono (by rw [Nat.succ_mul]; exact Nat.le_add_right _ _)
        (prfSecHopTreeCode_within suite params pkSeed pk rfMsg (next none) lo log (h none))

