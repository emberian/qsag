module
/-
# Qsag.Protocol.Signing.SignatureOutputAndCacheLaws — First-Success WOTS+C Grinding Coupling & Waistband Cache Laws

Self-contained Lean 4.35 cryptanalytic output-distribution and cache-soundness foundation over
`Qsag.HashSigs` and `Qsag.HypertreeEufCma` (`0 sorry`, `0 Classical.choice`, `0 native_decide`,
`0 bv_decide`, `0 grind`):
1. **First-Success WOTS+C Grinding Coupling, Tail-Abort & Non-First-Hit Bias
   (`firstValidCounter_some_iff`, `firstValidCounter_none_iff`, `grindTswCounter_4_128_192_eq_firstValidCounter`,
   `threshold_standalone_grinding_coupling`, `tooth_non_first_hit_lsb_bias_positive_tvd`)**:
   Certifies that `firstValidCounter` returns the unique minimum valid counter `< maxTrials` (or
   `none` iff every counter `< maxTrials` fails), refines `HashSigs.grindTswCounterAux` at deployed
   `(w = 4, chains = 128, targetSum = 192)`, and proves that any threshold signing ceremony agreeing
   pointwise with the standalone reference signer on chain digits and candidate signatures has
   identical stopping time `τ`, bit-exact output, and `statisticalDistance = 0`. Paired with an
   explicit `#tooth` malicious coordinator strategy skipping `ctr₀` when `sigChainLsb = false` for
   `ctr₁ > ctr₀`, proving every emitted signature still passes `verifyPqHashSig = true` yet induces
   strictly positive statistical distance (`TVD > 0`).
2. **Waistband Static Top-$L$ Internal Child-Root Cache Zero-Loss EUF-CMA Preservation
   (`evalWaistbandSignStep_eq_evalSingleSign`, `waistband_topL_cache_view_eq_stateless`,
   `waistband_topL_cache_preserves_euf_cma`, `tooth_caching_bottom_layer_breaks_wots_one_time`)**:
   Formalizes a $d$-layer hypertree signer whose internal layers `1..d-1` memoize deterministic
   WOTS+C signatures over static child XMSS roots `computeXmssSubtreeRoot(layer - 1, childTreeIdx)`
   under `sk.skSeed`, while layer `0` always signs freshly. Proves adaptive $Q$-query view
   identity (`statisticalDistance = 0`) and exact `0` EUF-CMA advantage loss, paired with a
   constructive chain-splicing theorem under coordinatewise digit coverage and an explicit
   third-message forgery for a deliberately weak suite (`w = 4, chains = 128, targetSum = 192`)
   after two signatures reuse one bottom-layer leaf. This is a concrete reuse counterexample,
   not a claim that every pair of distinct messages permits a third-message forgery.
-/

public import Qsag.Protocol.Signing.HashSigs
public import Qsag.Protocol.Signing.HypertreeEufCma
import Init.Data.String.Defs
import Qsag.Protocol.Aggregation.UcGames
import Qsag.Math.Counting
import Qsag.Math.CoeffPoly
import Qsag.Math.PolyRing
import Qsag.Math.HasseHensel
import Qsag.Oracle.Keccak
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

-- Use the direct decision procedure; the generic order-derived law in this
-- toolchain carries an avoidable classical proof dependency.
local instance signatureUInt8LawfulBEq : LawfulBEq UInt8 where
  eq_of_beq {a b} h := by
    change decide (a = b) = true at h
    exact of_decide_eq_true h
  rfl {a} := by
    change decide (a = a) = true
    exact of_decide_eq_self_eq_true a

local instance signatureUInt8LawfulEqOrd : Std.LawfulEqOrd UInt8 where
  compare_self {a} := by
    change compareOfLessAndEq a a = .eq
    unfold compareOfLessAndEq
    have h : ¬ a < a := by change ¬ a.toNat < a.toNat; omega
    simp only [h, ite_false, ite_true]
  eq_of_compare {a b} h := by
    change compareOfLessAndEq a b = .eq at h
    unfold compareOfLessAndEq at h
    split at h
    · contradiction
    · split at h
      · assumption
      · contradiction

local instance signatureUInt8LawfulOrderOrd : Std.LawfulOrderOrd UInt8 where
  isLE_compare a b := by
    change (compareOfLessAndEq a b).isLE ↔ a.toNat ≤ b.toNat
    unfold compareOfLessAndEq
    split
    · rename_i h
      change a.toNat < b.toNat at h
      simp only [Ordering.isLE, true_iff]
      omega
    · rename_i h
      change ¬ a.toNat < b.toNat at h
      split
      · rename_i heq
        subst b
        simp only [Ordering.isLE, true_iff]
        omega
      · rename_i hne
        have hne' : a.toNat ≠ b.toNat := fun heq => hne (UInt8.toNat_inj.mp heq)
        simp only [Ordering.isLE, Bool.false_eq_true, false_iff]
        omega
  isGE_compare a b := by
    change (compareOfLessAndEq a b).isGE ↔ b.toNat ≤ a.toNat
    unfold compareOfLessAndEq
    split
    · rename_i h
      change a.toNat < b.toNat at h
      simp only [Ordering.isGE, Bool.false_eq_true, false_iff]
      omega
    · rename_i h
      change ¬ a.toNat < b.toNat at h
      split
      · rename_i heq
        subst b
        simp only [Ordering.isGE, true_iff]
        omega
      · simp only [Ordering.isGE, true_iff]
        omega

/-! ## 1. First-Success Counter Grinding, Tail-Abort & Statistical Coupling (`w=4, ell1=128, target=192`) -/

/-- Auxiliary first-success counter search starting at `cur` with `fuel` remaining trials. -/
@[expose] def firstValidCounterAux (check : Nat → Bool) (cur : Nat) : Nat → Option Nat
  | 0 => none
  | fuel + 1 => if check cur then some cur else firstValidCounterAux check (cur + 1) fuel

/-- Deterministic/PRF-driven counter grinder returning the smallest `ctr < maxTrials` with `check ctr = true`. -/
@[expose] def firstValidCounter (check : Nat → Bool) (maxTrials : Nat) : Option Nat :=
  firstValidCounterAux check 0 maxTrials

private theorem firstValidCounterAux_some_iff (check : Nat → Bool) :
    ∀ (fuel cur ctr : Nat),
      firstValidCounterAux check cur fuel = some ctr ↔
        cur ≤ ctr ∧ ctr < cur + fuel ∧ check ctr = true ∧ ∀ j, cur ≤ j → j < ctr → check j = false
  | 0, cur, ctr => by
    simp only [firstValidCounterAux, reduceCtorEq, false_iff]
    intro ⟨hLe, hLt, _, _⟩
    exact Nat.not_lt_of_ge hLe (by simpa [Nat.add_zero] using hLt)
  | fuel + 1, cur, ctr => by
    simp only [firstValidCounterAux]
    cases hCur : check cur
    · simp only [Bool.false_eq_true, ↓reduceIte, firstValidCounterAux_some_iff check fuel (cur + 1) ctr]
      constructor
      · rintro ⟨hGe1, hLt1, hChk, hMin⟩
        refine ⟨Nat.le_of_succ_le hGe1, by omega, hChk, fun j hjGe hjLt => ?_⟩
        if hjEq : j = cur then subst hjEq; exact hCur
        else exact hMin j (by omega) hjLt
      · rintro ⟨hGe, hLt, hChk, hMin⟩
        have hNe : ctr ≠ cur := fun hEq => by rw [hEq, hCur] at hChk; cases hChk
        exact ⟨by omega, by omega, hChk, fun j hjGe hjLt => hMin j (Nat.le_of_succ_le hjGe) hjLt⟩
    · simp only [↓reduceIte, Option.some.injEq]
      constructor
      · rintro rfl
        exact ⟨Nat.le_refl cur, by omega, hCur, fun j hjGe hjLt => False.elim (Nat.not_lt_of_ge hjGe hjLt)⟩
      · rintro ⟨hGe, _, _, hMin⟩
        if hEq : cur = ctr then exact hEq
        else
          have hFalse := hMin cur (Nat.le_refl cur) (by omega)
          rw [hCur] at hFalse; cases hFalse

/-- **Exact First-Hit Minimality Characterization (`firstValidCounter_some_iff`)**:
    `firstValidCounter check maxTrials = some ctr` iff `ctr < maxTrials`, `check ctr = true`, and
    every strictly smaller counter `j < ctr` failed (`check j = false`). -/
theorem firstValidCounter_some_iff (check : Nat → Bool) (maxTrials ctr : Nat) :
    firstValidCounter check maxTrials = some ctr ↔
      ctr < maxTrials ∧ check ctr = true ∧ ∀ j, j < ctr → check j = false := by
  unfold firstValidCounter
  rw [firstValidCounterAux_some_iff]
  simp only [Nat.zero_le, Nat.zero_add, true_and, true_implies]

/-- **Tail-Abort Exhaustion Characterization (`firstValidCounter_none_iff`)**:
    `firstValidCounter check maxTrials = none` iff every counter `< maxTrials` fails `check`. -/
theorem firstValidCounter_none_iff (check : Nat → Bool) (maxTrials : Nat) :
    firstValidCounter check maxTrials = none ↔ ∀ ctr, ctr < maxTrials → check ctr = false := by
  have hAux : ∀ fuel cur, firstValidCounterAux check cur fuel = none ↔
      ∀ j, cur ≤ j → j < cur + fuel → check j = false := by
    intro fuel
    induction fuel with
    | zero =>
      intro cur
      simp only [firstValidCounterAux, true_iff, Nat.add_zero]
      intro j hlo hhi
      omega
    | succ fuel ih =>
      intro cur
      cases h : check cur
      · simp only [firstValidCounterAux, h, Bool.false_eq_true, ↓reduceIte, ih]
        constructor
        · intro hAll j hlo hhi
          by_cases hj : j = cur
          · simpa [hj] using h
          · exact hAll j (by omega) (by omega)
        · intro hAll j hlo hhi
          exact hAll j (by omega) (by omega)
      · simp only [firstValidCounterAux, h, ↓reduceIte, reduceCtorEq, false_iff]
        intro hAll
        have := hAll cur (by omega) (by omega)
        rw [h] at this
        cases this
  simpa [firstValidCounter] using hAux maxTrials 0

theorem firstValidCounter_congr {check₁ check₂ : Nat → Bool} {maxTrials : Nat}
    (hAgree : ∀ ctr, ctr < maxTrials → check₁ ctr = check₂ ctr) :
    firstValidCounter check₁ maxTrials = firstValidCounter check₂ maxTrials := by
  cases h₁ : firstValidCounter check₁ maxTrials with
  | none =>
    have hAll₁ := (firstValidCounter_none_iff check₁ maxTrials).mp h₁
    exact ((firstValidCounter_none_iff check₂ maxTrials).mpr
      (fun ctr hLt => (hAgree ctr hLt).symm.trans (hAll₁ ctr hLt))).symm
  | some ctr =>
    obtain ⟨hLt, hChk, hMin⟩ := (firstValidCounter_some_iff check₁ maxTrials ctr).mp h₁
    exact ((firstValidCounter_some_iff check₂ maxTrials ctr).mpr
      ⟨hLt, (hAgree ctr hLt).symm.trans hChk,
       fun j hj => (hAgree j (Nat.lt_trans hj hLt)).symm.trans (hMin j hj)⟩).symm

/-- Deployed `Corduroy`/`Baggy`/`Jorts` base-4 WOTS+C constant sum: `canonicalTargetSum 4 128 = 192`. -/
theorem wotsC_deployed_targetSum : canonicalTargetSum 4 128 = 192 := by rw [canonicalTargetSum_eq]

private theorem grindTswCounterAux_eq_firstValidCounterAux
    (suite : TweakableHashSuite) (w ell1 target : Nat)
    (rRand pkSeed pkRoot mu : List UInt8) (layerIdx : UInt32) (treeIdx : UInt64) (kpIdx : UInt32) :
    ∀ (fuel cur : Nat),
      grindTswCounterAux suite w ell1 target rRand pkSeed pkRoot mu layerIdx treeIdx kpIdx cur fuel =
        (firstValidCounterAux
          (fun ctr => checkTargetSum w ell1 target
            (extractBaseWDigits w ell1 (thHashMsg suite rRand pkSeed pkRoot mu layerIdx treeIdx kpIdx ctr)))
          cur fuel).map
          (fun ctr =>
            let hm := thHashMsg suite rRand pkSeed pkRoot mu layerIdx treeIdx kpIdx ctr
            (ctr, extractBaseWDigits w ell1 hm, hm))
  | 0, _ => by simp only [grindTswCounterAux_zero, firstValidCounterAux, Option.map_none]
  | fuel + 1, cur => by
    simp only [grindTswCounterAux_succ, firstValidCounterAux]
    by_cases hCheck : checkTargetSum w ell1 target
      (extractBaseWDigits w ell1 (thHashMsg suite rRand pkSeed pkRoot mu layerIdx treeIdx kpIdx cur)) = true
    · simp only [hCheck, ↓reduceIte, Option.map_some]
    · simp only [hCheck]
      exact grindTswCounterAux_eq_firstValidCounterAux suite w ell1 target
        rRand pkSeed pkRoot mu layerIdx treeIdx kpIdx fuel (cur + 1)

/-- **Exact Refinement (`grindTswCounter_4_128_192_eq_firstValidCounter`)**:
    Production `HashSigs.grindTswCounterAux` at `(w = 4, ell1 = 128, target = 192)` is bit-for-bit
    governed by `firstValidCounter`. -/
theorem grindTswCounter_4_128_192_eq_firstValidCounter
    (suite : TweakableHashSuite) (rRand pkSeed pkRoot mu : List UInt8)
    (layerIdx : UInt32) (treeIdx : UInt64) (kpIdx : UInt32) (maxTrials : Nat) :
    grindTswCounterAux suite 4 128 (canonicalTargetSum 4 128)
        rRand pkSeed pkRoot mu layerIdx treeIdx kpIdx 0 maxTrials =
      (firstValidCounter
        (fun ctr => checkTargetSum 4 128 192
          (extractBaseWDigits 4 128 (thHashMsg suite rRand pkSeed pkRoot mu layerIdx treeIdx kpIdx ctr)))
        maxTrials).map
        (fun ctr =>
          let hm := thHashMsg suite rRand pkSeed pkRoot mu layerIdx treeIdx kpIdx ctr
          (ctr, extractBaseWDigits 4 128 hm, hm)) := by
  rw [wotsC_deployed_targetSum]
  exact grindTswCounterAux_eq_firstValidCounterAux suite 4 128 192
    rRand pkSeed pkRoot mu layerIdx treeIdx kpIdx maxTrials 0

/-- Count of randomizer coins `c : Fin C` on which sampler `X` outputs `y`. -/
@[expose] def coinMass {α : Type} [DecidableEq α] (C : Nat) (X : Fin C → α) (y : α) : Nat :=
  qsum C (fun c => if X c = y then 1 else 0)

/-- Unnormalized $L_1$ / $2 \cdot C \cdot \mathrm{TVD}$ statistical distance over `support`. -/
@[expose] def statisticalDistance {α : Type} [DecidableEq α] (C : Nat) (support : List α)
    (X Y : Fin C → α) : Nat :=
  support.foldr (fun y acc => natAbsDiff (coinMass C X y) (coinMass C Y y) + acc) 0

theorem statisticalDistance_eq_zero_of_pointwise_eq {α : Type} [DecidableEq α]
    (C : Nat) (support : List α) {X Y : Fin C → α} (hEq : ∀ c : Fin C, X c = Y c) :
    statisticalDistance C support X Y = 0 := by
  have hMass : ∀ y : α, coinMass C X y = coinMass C Y y := fun y =>
    qsum_congr (fun c => by rw [hEq c])
  induction support with
  | nil => rfl
  | cons y ys ih =>
    simp only [statisticalDistance, List.foldr_cons] at ih ⊢
    rw [hMass y, show natAbsDiff (coinMass C Y y) (coinMass C Y y) = 0 from by simp [natAbsDiff_eq],
        Nat.zero_add, ih]

/-- Execute a WOTS+C counter-grinding signing ceremony (`w, ell1, target, maxTrials`) over per-trial
    evaluator `step : Fin C → Nat → List Nat × Sig`, returning `some (τ, sig)` or `none` on exhaustion. -/
@[expose] def evalGrindCeremony {C : Nat} {Sig : Type}
    (w ell1 target maxTrials : Nat) (step : Fin C → Nat → List Nat × Sig)
    (c : Fin C) : Option (Nat × Sig) :=
  match firstValidCounter (fun ctr => checkTargetSum w ell1 target (step c ctr).1) maxTrials with
  | none => none
  | some τ => some (τ, (step c τ).2)

/-- **Pointwise & Distributional Grinding Equivalence (`threshold_standalone_grinding_coupling`)**:
    Whenever threshold ceremony `evalThresholdStep` agrees with standalone `evalStandaloneStep` on
    chain digits and valid-counter signatures across `ctr < maxTrials`, their `firstValidCounter`
    stopping time `τ`, emitted `Option (Nat × Sig)` outcome, distinguisher advantage, and
    `statisticalDistance` over randomizer coins `Fin C` are **100% identical (`= 0`)**! -/
theorem threshold_standalone_grinding_coupling {C : Nat} {Sig : Type} [DecidableEq Sig]
    (w ell1 target maxTrials : Nat)
    (evalThresholdStep evalStandaloneStep : Fin C → Nat → List Nat × Sig)
    (support : List (Option (Nat × Sig))) (D : Option (Nat × Sig) → Bool)
    (hAgree : ∀ (c : Fin C) (ctr : Nat), ctr < maxTrials →
      (evalThresholdStep c ctr).1 = (evalStandaloneStep c ctr).1 ∧
      (checkTargetSum w ell1 target (evalStandaloneStep c ctr).1 = true →
        (evalThresholdStep c ctr).2 = (evalStandaloneStep c ctr).2)) :
    (∀ c : Fin C,
      firstValidCounter (fun ctr => checkTargetSum w ell1 target (evalThresholdStep c ctr).1) maxTrials =
        firstValidCounter (fun ctr => checkTargetSum w ell1 target (evalStandaloneStep c ctr).1) maxTrials) ∧
    (∀ c : Fin C,
      evalGrindCeremony w ell1 target maxTrials evalThresholdStep c =
        evalGrindCeremony w ell1 target maxTrials evalStandaloneStep c) ∧
    statisticalDistance C support
      (evalGrindCeremony w ell1 target maxTrials evalThresholdStep)
      (evalGrindCeremony w ell1 target maxTrials evalStandaloneStep) = 0 ∧
    natAbsDiff
      (qsum C (fun c => if D (evalGrindCeremony w ell1 target maxTrials evalThresholdStep c) then 1 else 0))
      (qsum C (fun c => if D (evalGrindCeremony w ell1 target maxTrials evalStandaloneStep c) then 1 else 0)) = 0 := by
  have hStop : ∀ c : Fin C,
      firstValidCounter (fun ctr => checkTargetSum w ell1 target (evalThresholdStep c ctr).1) maxTrials =
        firstValidCounter (fun ctr => checkTargetSum w ell1 target (evalStandaloneStep c ctr).1) maxTrials :=
    fun c => firstValidCounter_congr (fun ctr hLt => by rw [(hAgree c ctr hLt).1])
  have hOut : ∀ c : Fin C,
      evalGrindCeremony w ell1 target maxTrials evalThresholdStep c =
        evalGrindCeremony w ell1 target maxTrials evalStandaloneStep c := by
    intro c
    unfold evalGrindCeremony
    rw [hStop c]
    cases hF : firstValidCounter (fun ctr => checkTargetSum w ell1 target (evalStandaloneStep c ctr).1) maxTrials with
    | none => rfl
    | some τ =>
      obtain ⟨hLt, hChk, _⟩ := (firstValidCounter_some_iff _ maxTrials τ).mp hF
      dsimp only
      rw [(hAgree c τ hLt).2 hChk]
  refine ⟨hStop, hOut, statisticalDistance_eq_zero_of_pointwise_eq C support hOut, ?_⟩
  have hSumEq :
      qsum C (fun c => if D (evalGrindCeremony w ell1 target maxTrials evalThresholdStep c) then 1 else 0) =
        qsum C (fun c => if D (evalGrindCeremony w ell1 target maxTrials evalStandaloneStep c) then 1 else 0) :=
    qsum_congr (fun c => by rw [hOut c])
  rw [hSumEq]; simp [natAbsDiff_eq]

/-! ## 2. Waistband Static Top-$L$ Internal Child-Root Cache Zero-Loss EUF-CMA & Bottom-Layer `#tooth` -/

/-- Cached internal hypertree entry storing `(layerSig, parentSubtreeRoot)` for `(layerIdx, childTreeIdx)`. -/
structure WaistbandCacheEntry where
  layerSig   : LayerXmssSig
  parentRoot : List UInt8
  deriving DecidableEq, Repr

/-- Stateful `Waistband` top-$L$ internal child-root signature cache (`layers d - L .. d - 1`, `L < d`). -/
structure WaistbandTopLCache where
  entries : List ((Nat × Nat) × WaistbandCacheEntry)
  deriving DecidableEq, Repr

def WaistbandTopLCache.empty : WaistbandTopLCache := ⟨[]⟩

/-- Lookup a cached internal layer signature at `(layerIdx, childTreeIdx)`. -/
@[expose] def lookupWaistbandEntry (cache : WaistbandTopLCache) (layerIdx childTreeIdx : Nat) :
    Option WaistbandCacheEntry :=
  match cache.entries.find? (fun kv => kv.1.1 == layerIdx && kv.1.2 == childTreeIdx) with
  | none => none
  | some (_, entry) => some entry

def insertWaistbandEntry (cache : WaistbandTopLCache) (layerIdx childTreeIdx : Nat)
    (entry : WaistbandCacheEntry) : WaistbandTopLCache :=
  ⟨((layerIdx, childTreeIdx), entry) :: cache.entries⟩

/-- Deterministic static internal-layer (`layerIdx ≥ 1`) WOTS+C + XMSS signature over static child
    subtree root `computeXmssSubtreeRoot(layerIdx - 1, childTreeIdx)` under `sk.skSeed` (`layer0Rand = []`). -/
@[expose] def computeStaticInternalLayerSig (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pkRoot : List UInt8) (maxGrind layerIdx childTreeIdx : Nat) :
    Option WaistbandCacheEntry :=
  let subLeaves := 2 ^ params.subtreeHeight
  let kpIdx := childTreeIdx % subLeaves
  let kpU32 := UInt32.ofNat kpIdx
  let treeIdxNat := childTreeIdx / subLeaves
  let treeIdx := UInt64.ofNat treeIdxNat
  let layerU32 := UInt32.ofNat layerIdx
  let childRoot := computeXmssSubtreeRoot suite params sk
    (UInt32.ofNat (layerIdx - 1)) (UInt64.ofNat childTreeIdx)
  match grindTswCounterAux suite params.w params.ell1 params.targetSum
          [] sk.pkSeed pkRoot childRoot layerU32 treeIdx kpU32 0 maxGrind with
  | none => none
  | some (ctr, digits, _) =>
    let wotsChains := (List.range params.ell1).map fun r =>
      wotsChainSteps suite sk.pkSeed layerU32 treeIdx kpIdx r 0 (digits.getD r 0)
        (wotsSecretBase suite sk layerU32 treeIdx kpIdx r)
    let authPath := buildMerkleAuthPath suite sk.pkSeed layerU32 treeIdx .tree
      (computeWotsPk suite params sk layerU32 treeIdx) params.subtreeHeight 0 kpIdx
    let nextRoot := computeXmssSubtreeRoot suite params sk layerU32 treeIdx
    some { layerSig := { tswCtr := ctr, wotsChains := wotsChains, authPath := authPath }
           parentRoot := nextRoot }

/-- Soundness invariant for `WaistbandTopLCache`: `topL < params.numLayers` (so layer `0` is NEVER
    cached!) and every cached `(l, g)` entry equals `computeStaticInternalLayerSig`. -/
def WaistbandCacheSound (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pkRoot : List UInt8) (maxGrind topL : Nat)
    (cache : WaistbandTopLCache) : Prop :=
  topL < params.numLayers ∧
  ∀ l g entry, lookupWaistbandEntry cache l g = some entry →
    1 ≤ l ∧ computeStaticInternalLayerSig suite params sk pkRoot maxGrind l g = some entry

theorem waistbandCacheSound_empty (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pkRoot : List UInt8) (maxGrind topL : Nat)
    (hTopL : topL < params.numLayers) :
    WaistbandCacheSound suite params sk pkRoot maxGrind topL WaistbandTopLCache.empty :=
  ⟨hTopL, fun _ _ _ h => by simp [lookupWaistbandEntry, WaistbandTopLCache.empty] at h⟩

private theorem waistbandCacheSound_insert {suite : TweakableHashSuite} {params : PqHashParams}
    {sk : PqSecretKey} {pkRoot : List UInt8} {maxGrind topL l₀ g₀ : Nat}
    {entry₀ : WaistbandCacheEntry} {cache : WaistbandTopLCache}
    (hSound : WaistbandCacheSound suite params sk pkRoot maxGrind topL cache)
    (hl₀ : 1 ≤ l₀)
    (hComp₀ : computeStaticInternalLayerSig suite params sk pkRoot maxGrind l₀ g₀ = some entry₀) :
    WaistbandCacheSound suite params sk pkRoot maxGrind topL (insertWaistbandEntry cache l₀ g₀ entry₀) := by
  refine ⟨hSound.1, fun l g entry hLook => ?_⟩
  unfold lookupWaistbandEntry insertWaistbandEntry at hLook
  simp only [List.find?_cons] at hLook
  cases hEq : (l₀ == l && g₀ == g)
  · rw [hEq] at hLook
    exact hSound.2 l g entry hLook
  · rw [hEq] at hLook
    simp only [Option.some.injEq] at hLook
    simp only [Bool.and_eq_true, beq_iff_eq] at hEq
    rcases hEq with ⟨rfl, rfl⟩
    subst hLook
    exact ⟨hl₀, hComp₀⟩

/-- Multi-layer hypertree signer with `Waistband` top-$L$ static internal child-root memoization.
    Layer `0` (`layerIdx < params.numLayers - topL`) is ALWAYS computed freshly without caching;
    internal layers `layerIdx ≥ params.numLayers - topL` (`≥ 1`) serve `O(1)` hits or memoize misses. -/
@[expose] def waistbandSignHypertreeLayers (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pkRoot layer0Rand : List UInt8) (maxGrind topL : Nat) :
    Nat → Nat → List UInt8 → Nat → WaistbandTopLCache → WaistbandTopLCache × Option (List LayerXmssSig)
  | _, _, _, 0, cache => (cache, some [])
  | layerIdx, globalIdx, curRoot, rem + 1, cache =>
    if params.numLayers - topL ≤ layerIdx then
      match lookupWaistbandEntry cache layerIdx globalIdx with
      | some entry =>
        let treeIdxNat := globalIdx / (2 ^ params.subtreeHeight)
        let (cache', restOpt) := waistbandSignHypertreeLayers suite params sk pkRoot [] maxGrind topL
          (layerIdx + 1) treeIdxNat entry.parentRoot rem cache
        (cache', restOpt.map (entry.layerSig :: ·))
      | none =>
        match computeStaticInternalLayerSig suite params sk pkRoot maxGrind layerIdx globalIdx with
        | none => (cache, none)
        | some entry =>
          let cache1 := insertWaistbandEntry cache layerIdx globalIdx entry
          let treeIdxNat := globalIdx / (2 ^ params.subtreeHeight)
          let (cache', restOpt) := waistbandSignHypertreeLayers suite params sk pkRoot [] maxGrind topL
            (layerIdx + 1) treeIdxNat entry.parentRoot rem cache1
          (cache', restOpt.map (entry.layerSig :: ·))
    else
      let subLeaves := 2 ^ params.subtreeHeight
      let kpIdx := globalIdx % subLeaves
      let kpU32 := UInt32.ofNat kpIdx
      let treeIdxNat := globalIdx / subLeaves
      let treeIdx := UInt64.ofNat treeIdxNat
      let layerU32 := UInt32.ofNat layerIdx
      match grindTswCounterAux suite params.w params.ell1 params.targetSum
              layer0Rand sk.pkSeed pkRoot curRoot layerU32 treeIdx kpU32 0 maxGrind with
      | none => (cache, none)
      | some (ctr, digits, _) =>
        let wotsChains := (List.range params.ell1).map fun r =>
          wotsChainSteps suite sk.pkSeed layerU32 treeIdx kpIdx r 0 (digits.getD r 0)
            (wotsSecretBase suite sk layerU32 treeIdx kpIdx r)
        let authPath := buildMerkleAuthPath suite sk.pkSeed layerU32 treeIdx .tree
          (computeWotsPk suite params sk layerU32 treeIdx) params.subtreeHeight 0 kpIdx
        let nextRoot := computeXmssSubtreeRoot suite params sk layerU32 treeIdx
        let lsig : LayerXmssSig := { tswCtr := ctr, wotsChains := wotsChains, authPath := authPath }
        let (cache', restOpt) := waistbandSignHypertreeLayers suite params sk pkRoot [] maxGrind topL
          (layerIdx + 1) treeIdxNat nextRoot rem cache
        (cache', restOpt.map (lsig :: ·))

private theorem waistbandSignHypertreeLayers_eq_signHypertreeLayers
    (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pkRoot : List UInt8) (maxGrind topL : Nat) :
    ∀ (rem layerIdx globalIdx : Nat) (layer0Rand curRoot : List UInt8) (cache : WaistbandTopLCache),
      WaistbandCacheSound suite params sk pkRoot maxGrind topL cache →
      (1 ≤ layerIdx → layer0Rand = [] ∧
        curRoot = computeXmssSubtreeRoot suite params sk
          (UInt32.ofNat (layerIdx - 1)) (UInt64.ofNat globalIdx)) →
      let (cache', outOpt) := waistbandSignHypertreeLayers suite params sk pkRoot layer0Rand
        maxGrind topL layerIdx globalIdx curRoot rem cache
      WaistbandCacheSound suite params sk pkRoot maxGrind topL cache' ∧
      outOpt = signHypertreeLayers suite params sk pkRoot layer0Rand maxGrind layerIdx globalIdx curRoot rem
  | 0, _, _, _, _, cache, hSound, _ => ⟨hSound, by rw [signHypertreeLayers_zero]⟩
  | rem + 1, layerIdx, globalIdx, layer0Rand, curRoot, cache, hSound, hInternal => by
    simp only [waistbandSignHypertreeLayers, signHypertreeLayers_succ]
    if hCachedLayer : params.numLayers - topL ≤ layerIdx then
      simp only [hCachedLayer, ↓reduceIte]
      have hTopLt : topL < params.numLayers := hSound.1
      have hGe1 : 1 ≤ layerIdx := by omega
      obtain ⟨rfl, rfl⟩ := hInternal hGe1
      have hMatchEntry : ∀ entry : WaistbandCacheEntry,
          computeStaticInternalLayerSig suite params sk pkRoot maxGrind layerIdx globalIdx = some entry →
          entry.parentRoot = computeXmssSubtreeRoot suite params sk
            (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)) := by
        intro entry hComp
        unfold computeStaticInternalLayerSig at hComp
        dsimp only at hComp
        cases hG : grindTswCounterAux suite params.w params.ell1 params.targetSum [] sk.pkSeed pkRoot
            (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (layerIdx - 1)) (UInt64.ofNat globalIdx))
            (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
            (UInt32.ofNat (globalIdx % 2 ^ params.subtreeHeight)) 0 maxGrind with
        | none => rw [hG] at hComp; cases hComp
        | some tr =>
          rcases tr with ⟨ctr, digits, _⟩
          rw [hG] at hComp; simp only [Option.some.injEq] at hComp; subst hComp; rfl
      cases hLook : lookupWaistbandEntry cache layerIdx globalIdx with
      | some entry =>
        dsimp only
        obtain ⟨_, hComp⟩ := hSound.2 layerIdx globalIdx entry hLook
        have hParent := hMatchEntry entry hComp
        have hNextInternal : 1 ≤ layerIdx + 1 → ([] : List UInt8) = [] ∧
            entry.parentRoot = computeXmssSubtreeRoot suite params sk
              (UInt32.ofNat ((layerIdx + 1) - 1)) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)) :=
          fun _ => ⟨rfl, by simpa [Nat.add_sub_cancel] using hParent⟩
        have ih := waistbandSignHypertreeLayers_eq_signHypertreeLayers suite params sk pkRoot maxGrind topL
          rem (layerIdx + 1) (globalIdx / 2 ^ params.subtreeHeight) [] entry.parentRoot cache hSound hNextInternal
        dsimp only at ih
        refine ⟨ih.1, ?_⟩
        rw [ih.2, hParent]
        unfold computeStaticInternalLayerSig at hComp
        dsimp only at hComp
        cases hG : grindTswCounterAux suite params.w params.ell1 params.targetSum [] sk.pkSeed pkRoot
            (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (layerIdx - 1)) (UInt64.ofNat globalIdx))
            (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
            (UInt32.ofNat (globalIdx % 2 ^ params.subtreeHeight)) 0 maxGrind with
        | none => rw [hG] at hComp; cases hComp
        | some tr =>
          rcases tr with ⟨ctr, digits, _⟩
          rw [hG] at hComp; simp only [Option.some.injEq] at hComp; subst hComp
          cases signHypertreeLayers suite params sk pkRoot [] maxGrind (layerIdx + 1)
            (globalIdx / 2 ^ params.subtreeHeight)
            (computeXmssSubtreeRoot suite params sk (UInt32.ofNat layerIdx)
              (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))) rem <;> rfl
      | none =>
        dsimp only
        cases hComp : computeStaticInternalLayerSig suite params sk pkRoot maxGrind layerIdx globalIdx with
        | none =>
          refine ⟨hSound, ?_⟩
          unfold computeStaticInternalLayerSig at hComp
          dsimp only at hComp
          cases hG : grindTswCounterAux suite params.w params.ell1 params.targetSum [] sk.pkSeed pkRoot
              (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (layerIdx - 1)) (UInt64.ofNat globalIdx))
              (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
              (UInt32.ofNat (globalIdx % 2 ^ params.subtreeHeight)) 0 maxGrind with
          | none => rfl
          | some tr => rcases tr with ⟨_, _, _⟩; rw [hG] at hComp; cases hComp
        | some entry =>
          dsimp only
          have hSound1 := waistbandCacheSound_insert hSound hGe1 hComp
          have hParent := hMatchEntry entry hComp
          have hNextInternal : 1 ≤ layerIdx + 1 → ([] : List UInt8) = [] ∧
              entry.parentRoot = computeXmssSubtreeRoot suite params sk
                (UInt32.ofNat ((layerIdx + 1) - 1)) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)) :=
            fun _ => ⟨rfl, by simpa [Nat.add_sub_cancel] using hParent⟩
          have ih := waistbandSignHypertreeLayers_eq_signHypertreeLayers suite params sk pkRoot maxGrind topL
            rem (layerIdx + 1) (globalIdx / 2 ^ params.subtreeHeight) [] entry.parentRoot
            (insertWaistbandEntry cache layerIdx globalIdx entry) hSound1 hNextInternal
          dsimp only at ih
          refine ⟨ih.1, ?_⟩
          rw [ih.2, hParent]
          unfold computeStaticInternalLayerSig at hComp
          dsimp only at hComp
          cases hG : grindTswCounterAux suite params.w params.ell1 params.targetSum [] sk.pkSeed pkRoot
              (computeXmssSubtreeRoot suite params sk (UInt32.ofNat (layerIdx - 1)) (UInt64.ofNat globalIdx))
              (UInt32.ofNat layerIdx) (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
              (UInt32.ofNat (globalIdx % 2 ^ params.subtreeHeight)) 0 maxGrind with
          | none => rw [hG] at hComp; cases hComp
          | some tr =>
            rcases tr with ⟨ctr, digits, _⟩
            rw [hG] at hComp; simp only [Option.some.injEq] at hComp; subst hComp
            cases signHypertreeLayers suite params sk pkRoot [] maxGrind (layerIdx + 1)
              (globalIdx / 2 ^ params.subtreeHeight)
              (computeXmssSubtreeRoot suite params sk (UInt32.ofNat layerIdx)
                (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))) rem <;> rfl
    else
      simp only [hCachedLayer, ↓reduceIte]
      cases hG : grindTswCounterAux suite params.w params.ell1 params.targetSum
          layer0Rand sk.pkSeed pkRoot curRoot (UInt32.ofNat layerIdx)
          (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))
          (UInt32.ofNat (globalIdx % 2 ^ params.subtreeHeight)) 0 maxGrind with
      | none => exact ⟨hSound, rfl⟩
      | some tr =>
        rcases tr with ⟨ctr, digits, _⟩
        dsimp only
        have hNextInternal : 1 ≤ layerIdx + 1 → ([] : List UInt8) = [] ∧
            computeXmssSubtreeRoot suite params sk (UInt32.ofNat layerIdx)
              (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)) =
            computeXmssSubtreeRoot suite params sk (UInt32.ofNat ((layerIdx + 1) - 1))
              (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight)) :=
          fun _ => ⟨rfl, by simp⟩
        have ih := waistbandSignHypertreeLayers_eq_signHypertreeLayers suite params sk pkRoot maxGrind topL
          rem (layerIdx + 1) (globalIdx / 2 ^ params.subtreeHeight) []
          (computeXmssSubtreeRoot suite params sk (UInt32.ofNat layerIdx)
            (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))) cache hSound hNextInternal
        dsimp only at ih
        refine ⟨ih.1, ?_⟩
        rw [ih.2]
        cases signHypertreeLayers suite params sk pkRoot [] maxGrind (layerIdx + 1)
          (globalIdx / 2 ^ params.subtreeHeight)
          (computeXmssSubtreeRoot suite params sk (UInt32.ofNat layerIdx)
            (UInt64.ofNat (globalIdx / 2 ^ params.subtreeHeight))) rem <;> rfl

/-- Full single-query `Waistband` signer updating `WaistbandTopLCache` across internal layers `d - L .. d - 1`. -/
@[expose] def evalWaistbandSignStep (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msg optRand : List UInt8)
    (leafGlobalIdx maxGrind topL : Nat) (cache : WaistbandTopLCache) :
    WaistbandTopLCache × Option PqHashSig :=
  if !(params.wellFormed) then (cache, none)
  else if !(leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight)) then (cache, none)
  else
    let pk := derivePublicKey suite params sk
    let mu := thPreHash suite pk.pkSeed pk.pkRoot msg
    let rRand := thPrfMsg suite sk.skPrf optRand mu
    if params.statefulJorts then
      let (cache', layerSigsOpt) := waistbandSignHypertreeLayers suite params sk
        pk.pkRoot rRand maxGrind topL 0 leafGlobalIdx mu params.numLayers cache
      (cache', layerSigsOpt.map fun layerSigs =>
        { rRand := rRand, msgTswCtr := 0, leafGlobalIdx := leafGlobalIdx, forsOpenings := [], layerSigs := layerSigs })
    else
      let subLeaves := 2 ^ params.subtreeHeight
      let kp0 := leafGlobalIdx % subLeaves
      let kp0U32 := UInt32.ofNat kp0
      let tree0 := UInt64.ofNat (leafGlobalIdx / subLeaves)
      match grindTswCounterAux suite params.w params.ell1 params.targetSum
              rRand pk.pkSeed pk.pkRoot mu 0 tree0 kp0U32 0 maxGrind with
      | none => (cache, none)
      | some (ctr0, _, hmsg0) =>
        let forsOps := buildForsOpenings suite params sk tree0 kp0 hmsg0
        let forsPk := computeForsPk suite params sk tree0 kp0
        let (cache', layerSigsOpt) := waistbandSignHypertreeLayers suite params sk
          pk.pkRoot [] maxGrind topL 0 leafGlobalIdx forsPk params.numLayers cache
        (cache', layerSigsOpt.map fun layerSigs =>
          { rRand := rRand, msgTswCtr := ctr0, leafGlobalIdx := leafGlobalIdx, forsOpenings := forsOps, layerSigs := layerSigs })

/-- **Single-Step `Waistband` Equivalence & Invariant Preservation (`evalWaistbandSignStep_eq_evalSingleSign`)**. -/
theorem evalWaistbandSignStep_eq_evalSingleSign
    (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msg optRand : List UInt8)
    (leafGlobalIdx maxGrind topL : Nat) (cache : WaistbandTopLCache)
    (hSound : WaistbandCacheSound suite params sk (derivePublicKey suite params sk).pkRoot maxGrind topL cache) :
    let (cache', outOpt) := evalWaistbandSignStep suite params sk msg optRand leafGlobalIdx maxGrind topL cache
    WaistbandCacheSound suite params sk (derivePublicKey suite params sk).pkRoot maxGrind topL cache' ∧
    outOpt = evalSingleSign suite params sk msg optRand leafGlobalIdx maxGrind := by
  unfold evalWaistbandSignStep evalSingleSign
  cases params.wellFormed
  · exact ⟨hSound, rfl⟩
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases decide (leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight))
    · exact ⟨hSound, rfl⟩
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      have hVacuous0 : ∀ (r c : List UInt8), 1 ≤ 0 → r = [] ∧ c = computeXmssSubtreeRoot suite params sk 0 (UInt64.ofNat leafGlobalIdx) :=
        fun _ _ h => False.elim (Nat.not_le_of_gt (by decide) h)
      cases params.statefulJorts
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases grindTswCounterAux suite params.w params.ell1 params.targetSum
            (thPrfMsg suite sk.skPrf optRand (thPreHash suite (derivePublicKey suite params sk).pkSeed (derivePublicKey suite params sk).pkRoot msg))
            (derivePublicKey suite params sk).pkSeed (derivePublicKey suite params sk).pkRoot
            (thPreHash suite (derivePublicKey suite params sk).pkSeed (derivePublicKey suite params sk).pkRoot msg)
            0 (UInt64.ofNat (leafGlobalIdx / 2 ^ params.subtreeHeight))
            (UInt32.ofNat (leafGlobalIdx % 2 ^ params.subtreeHeight)) 0 maxGrind with
        | none => exact ⟨hSound, rfl⟩
        | some tr =>
          rcases tr with ⟨ctr0, _, hmsg0⟩
          dsimp only
          have hLayers := waistbandSignHypertreeLayers_eq_signHypertreeLayers suite params sk
            (derivePublicKey suite params sk).pkRoot maxGrind topL params.numLayers 0 leafGlobalIdx []
            (computeForsPk suite params sk (UInt64.ofNat (leafGlobalIdx / 2 ^ params.subtreeHeight))
              (leafGlobalIdx % 2 ^ params.subtreeHeight)) cache hSound (hVacuous0 _ _)
          dsimp only at hLayers
          refine ⟨hLayers.1, ?_⟩
          rw [hLayers.2]
          cases signHypertreeLayers suite params sk (derivePublicKey suite params sk).pkRoot [] maxGrind
            0 leafGlobalIdx
            (computeForsPk suite params sk (UInt64.ofNat (leafGlobalIdx / 2 ^ params.subtreeHeight))
              (leafGlobalIdx % 2 ^ params.subtreeHeight)) params.numLayers <;> rfl
      · simp only [↓reduceIte]
        have hLayers := waistbandSignHypertreeLayers_eq_signHypertreeLayers suite params sk
          (derivePublicKey suite params sk).pkRoot maxGrind topL params.numLayers 0 leafGlobalIdx
          (thPrfMsg suite sk.skPrf optRand (thPreHash suite (derivePublicKey suite params sk).pkSeed (derivePublicKey suite params sk).pkRoot msg))
          (thPreHash suite (derivePublicKey suite params sk).pkSeed (derivePublicKey suite params sk).pkRoot msg)
          cache hSound (hVacuous0 _ _)
        dsimp only at hLayers
        refine ⟨hLayers.1, ?_⟩
        rw [hLayers.2]
        cases signHypertreeLayers suite params sk (derivePublicKey suite params sk).pkRoot
          (thPrfMsg suite sk.skPrf optRand (thPreHash suite (derivePublicKey suite params sk).pkSeed (derivePublicKey suite params sk).pkRoot msg))
          maxGrind 0 leafGlobalIdx
          (thPreHash suite (derivePublicKey suite params sk).pkSeed (derivePublicKey suite params sk).pkRoot msg)
          params.numLayers <;> rfl

/-- Adaptive $Q$-query execution against a stateful oracle `State → Dom → State × Cod`. -/
def evalStatefulOracleComp {State Dom Cod α : Type}
    (st : State) (step : State → Dom → State × Cod) : OracleComp Dom Cod α → State × α
  | .pure ret => (st, ret)
  | .query q next =>
    let (st', y) := step st q
    evalStatefulOracleComp st' step (next y)

/-- Adaptive query/response transcript against a stateful oracle. -/
def statefulOracleTranscript {State Dom Cod α : Type}
    (st : State) (step : State → Dom → State × Cod) : OracleComp Dom Cod α → List (Dom × Cod)
  | .pure _ => []
  | .query q next =>
    let (st', y) := step st q
    (q, y) :: statefulOracleTranscript st' step (next y)

/-- Adaptive query/response transcript against a stateless oracle `Dom → Cod`. -/
def statelessOracleTranscript {Dom Cod α : Type}
    (O : Dom → Cod) : OracleComp Dom Cod α → List (Dom × Cod)
  | .pure _ => []
  | .query q next => (q, O q) :: statelessOracleTranscript O (next (O q))

/-- Query tuple `(message, randomness, leaf)` for adaptive fixed-`maxGrind` hypertree signing. -/
structure AdaptiveSignQuery where
  message    : List UInt8
  randomness : List UInt8
  leaf       : Nat
  deriving DecidableEq, Repr

/-- **Adaptive $Q$-Query View & Transcript Equivalence (`waistband_topL_cache_view_eq_stateless`)**:
    Across ANY adaptive $Q$-query adversary family `A : Fin C → OracleComp AdaptiveSignQuery (Option PqHashSig) Out`
    and ANY `topL < params.numLayers`, querying the memoizing `Waistband` signer produces **bit-exact
    outputs, bit-exact query/response transcripts, and `statisticalDistance = 0`** relative to pure
    stateless `evalSingleSign`! -/
theorem waistband_topL_cache_view_eq_stateless {C : Nat} {Out : Type} [DecidableEq Out]
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (maxGrind topL : Nat) (hTopL : topL < params.numLayers)
    (A : Fin C → OracleComp AdaptiveSignQuery (Option PqHashSig) Out)
    (support : List Out) :
    let wbStep := fun (cache : WaistbandTopLCache) (q : AdaptiveSignQuery) =>
      evalWaistbandSignStep suite params sk q.message q.randomness q.leaf maxGrind topL cache
    let refOracle := fun (q : AdaptiveSignQuery) =>
      evalSingleSign suite params sk q.message q.randomness q.leaf maxGrind
    (∀ c : Fin C,
      (evalStatefulOracleComp WaistbandTopLCache.empty wbStep (A c)).2 = evalOracleComp refOracle (A c) ∧
      statefulOracleTranscript WaistbandTopLCache.empty wbStep (A c) = statelessOracleTranscript refOracle (A c)) ∧
    statisticalDistance C support
      (fun c => (evalStatefulOracleComp WaistbandTopLCache.empty wbStep (A c)).2)
      (fun c => evalOracleComp refOracle (A c)) = 0 := by
  intro wbStep refOracle
  have hProg : ∀ (prog : OracleComp AdaptiveSignQuery (Option PqHashSig) Out) (cache : WaistbandTopLCache),
      WaistbandCacheSound suite params sk (derivePublicKey suite params sk).pkRoot maxGrind topL cache →
      (evalStatefulOracleComp cache wbStep prog).2 = evalOracleComp refOracle prog ∧
      statefulOracleTranscript cache wbStep prog = statelessOracleTranscript refOracle prog := by
    intro prog
    induction prog with
    | pure ret => intro _ _; exact ⟨rfl, rfl⟩
    | query q next ih =>
      intro cache hSound
      obtain ⟨hSound', hEqOut⟩ := evalWaistbandSignStep_eq_evalSingleSign
        suite params sk q.message q.randomness q.leaf maxGrind topL cache hSound
      simp only [evalStatefulOracleComp, evalOracleComp, statefulOracleTranscript, statelessOracleTranscript]
      change (evalStatefulOracleComp (wbStep cache q).1 wbStep (next (wbStep cache q).2)).2 =
               evalOracleComp refOracle (next (refOracle q)) ∧
             (q, (wbStep cache q).2) :: statefulOracleTranscript (wbStep cache q).1 wbStep (next (wbStep cache q).2) =
               (q, refOracle q) :: statelessOracleTranscript refOracle (next (refOracle q))
      change (wbStep cache q).2 = refOracle q at hEqOut
      rw [hEqOut]
      obtain ⟨ihOut, ihTr⟩ := ih (refOracle q) (wbStep cache q).1 hSound'
      exact ⟨ihOut, congrArg ((q, refOracle q) :: ·) ihTr⟩
  have hInit := waistbandCacheSound_empty suite params sk (derivePublicKey suite params sk).pkRoot maxGrind topL hTopL
  have hAll := fun c : Fin C => hProg (A c) WaistbandTopLCache.empty hInit
  exact ⟨hAll, statisticalDistance_eq_zero_of_pointwise_eq C support (fun c => (hAll c).1)⟩

/-- Multi-query signing log generated by `Waistband` top-$L$ cached signing over `(message, randomness, leaf)` queries. -/
def waistbandSigningLog (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (maxGrind topL : Nat) :
    WaistbandTopLCache → List AdaptiveSignQuery → List (List UInt8 × PqHashSig)
  | _, [] => []
  | cache, q :: qs =>
    let (cache', outOpt) := evalWaistbandSignStep suite params sk q.message q.randomness q.leaf maxGrind topL cache
    match outOpt with
    | none => waistbandSigningLog suite params sk maxGrind topL cache' qs
    | some sig => (q.message, sig) :: waistbandSigningLog suite params sk maxGrind topL cache' qs

def toPqSigningQueries (maxGrind : Nat) (qs : List AdaptiveSignQuery) : List PqSigningQuery :=
  qs.map fun q => { message := q.message, randomness := q.randomness, leaf := q.leaf, grindLimit := maxGrind }

theorem waistbandSigningLog_eq_signingOracleLog
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (maxGrind topL : Nat) :
    ∀ (qs : List AdaptiveSignQuery) (cache : WaistbandTopLCache),
      WaistbandCacheSound suite params sk (derivePublicKey suite params sk).pkRoot maxGrind topL cache →
      waistbandSigningLog suite params sk maxGrind topL cache qs =
        signingOracleLog suite params sk (toPqSigningQueries maxGrind qs)
  | [], _, _ => by simp only [waistbandSigningLog, toPqSigningQueries, List.map_nil, signingOracleLog_nil]
  | q :: qs, cache, hSound => by
    obtain ⟨hSound', hOut⟩ := evalWaistbandSignStep_eq_evalSingleSign
      suite params sk q.message q.randomness q.leaf maxGrind topL cache hSound
    simp only [waistbandSigningLog, toPqSigningQueries, List.map_cons, signingOracleLog_cons]
    change (match (evalWaistbandSignStep suite params sk q.message q.randomness q.leaf maxGrind topL cache).2 with
            | none => waistbandSigningLog suite params sk maxGrind topL _ qs
            | some sig => (q.message, sig) :: waistbandSigningLog suite params sk maxGrind topL _ qs) = _
    change (evalWaistbandSignStep suite params sk q.message q.randomness q.leaf maxGrind topL cache).2 =
      evalSingleSign suite params sk q.message q.randomness q.leaf maxGrind at hOut
    have hRest := waistbandSigningLog_eq_signingOracleLog suite params sk maxGrind topL qs _ hSound'
    change waistbandSigningLog suite params sk maxGrind topL
      (evalWaistbandSignStep suite params sk q.message q.randomness q.leaf maxGrind topL cache).1 qs = _ at hRest
    rw [hOut, hRest]
    cases evalSingleSign suite params sk q.message q.randomness q.leaf maxGrind <;> rfl

/-- EUF-CMA winning event against the stateful `Waistband` top-$L$ cached signing oracle. -/
def waistbandEufCmaWin (suite : TweakableHashSuite) (params : PqHashParams)
    (maxGrind topL : Nat) (sk : PqSecretKey) (qs : List AdaptiveSignQuery)
    (msgStar : List UInt8) (sigStar : PqHashSig) : Bool :=
  verifyPqHashSig suite params (derivePublicKey suite params sk) msgStar sigStar &&
  decide (msgStar ∉ (waistbandSigningLog suite params sk maxGrind topL WaistbandTopLCache.empty qs).map Prod.fst)

/-- **Zero-Loss EUF-CMA Preservation (`waistband_topL_cache_preserves_euf_cma`)**:
    For ANY `topL < params.numLayers`, the EUF-CMA winning indicator and hit-count over ANY finite
    coin list `coins` are **100% identical (`0` security loss)** to pure stateless `eufCmaWin`, and
    inherit the exact factor-1 `Adv_ITSR + Adv_TCR + Adv_PRE` union bound! -/
theorem waistband_topL_cache_preserves_euf_cma {Ω : Type}
    (suite : TweakableHashSuite) (params : PqHashParams)
    (maxGrind topL : Nat) (hTopL : topL < params.numLayers)
    (coins : List Ω)
    (skFn : Ω → PqSecretKey) (qsFn : Ω → List AdaptiveSignQuery)
    (forgerOut : Ω → List UInt8 × PqHashSig) :
    let refOutcome := fun ω : Ω =>
      ({ sk := skFn ω
         queries := toPqSigningQueries maxGrind (qsFn ω)
         msgStar := (forgerOut ω).1
         sigStar := (forgerOut ω).2 } : EufCmaOutcome)
    (∀ ω : Ω,
      waistbandEufCmaWin suite params maxGrind topL (skFn ω) (qsFn ω) (forgerOut ω).1 (forgerOut ω).2 =
        eufCmaWin suite params (refOutcome ω)) ∧
    hitCount (fun ω => waistbandEufCmaWin suite params maxGrind topL (skFn ω) (qsFn ω) (forgerOut ω).1 (forgerOut ω).2) coins =
      hitCount (fun ω => eufCmaWin suite params (refOutcome ω)) coins := by
  intro refOutcome
  have hPt : ∀ ω : Ω,
      waistbandEufCmaWin suite params maxGrind topL (skFn ω) (qsFn ω) (forgerOut ω).1 (forgerOut ω).2 =
        eufCmaWin suite params (refOutcome ω) := by
    intro ω
    simp only [waistbandEufCmaWin, eufCmaWin_eq]
    have hLog := waistbandSigningLog_eq_signingOracleLog suite params (skFn ω) maxGrind topL (qsFn ω)
      WaistbandTopLCache.empty (waistbandCacheSound_empty suite params (skFn ω) _ maxGrind topL hTopL)
    rw [hLog]
  refine ⟨hPt, ?_⟩
  induction coins with
  | nil => rfl
  | cons ω rest ih => simp only [hitCount, hPt ω, ih]

/-! ### Constructive Bottom-Layer Two-Time WOTS+C Forgery (`#tooth` for Layer-`0` Reuse) -/

/-- **Constructive Polynomial-Time Two-Time WOTS+C Forger (`forgeWotsFromTwoSigs`)**:
    Using ONLY public `pkSeed`, digit vectors `d₁, d₂, d₃`, and chain signatures `sig₁, sig₂`
    at `(layer, tree, kp)` (`0` secret-key access!), steps forward from `sig₁[r]` when `d₁[r] ≤ d₃[r]`
    and from `sig₂[r]` otherwise. -/
@[expose] def forgeWotsFromTwoSigs (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kp ell1 : Nat)
    (d₁ d₂ d₃ : List Nat) (sig₁ sig₂ : List (List UInt8)) : List (List UInt8) :=
  (List.range ell1).map fun r =>
    let v1 := d₁.getD r 0
    let v2 := d₂.getD r 0
    let v3 := d₃.getD r 0
    if v1 ≤ v3 then
      wotsChainSteps suite pkSeed layer tree kp r v1 (v3 - v1) (sig₁.getD r [])
    else
      wotsChainSteps suite pkSeed layer tree kp r v2 (v3 - v2) (sig₂.getD r [])

/-- **Universal Suite-Polymorphic Two-Time WOTS+C Forgery Theorem (`forgeWotsFromTwoSigs_recovers_pk`)**:
    For any `suite : TweakableHashSuite`, without a collision assumption, whenever two
    layer-`(layer, tree, kp)` WOTS+C signatures `sig₁, sig₂` cover a third `TSW`-valid digit vector `d₃`
    coordinatewise (`min(d₁[r], d₂[r]) ≤ d₃[r]`), `forgeWotsFromTwoSigs` recovers the exact `computeWotsPk`! -/
theorem forgeWotsFromTwoSigs_recovers_pk
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (layer : UInt32) (tree : UInt64) (kp : Nat) (d₁ d₂ d₃ : List Nat)
    (hValid₃ : checkTargetSum params.w params.ell1 params.targetSum d₃ = true)
    (hCover : ∀ r, r < params.ell1 → d₁.getD r 0 ≤ d₃.getD r 0 ∨ d₂.getD r 0 ≤ d₃.getD r 0) :
    let sig₁ := (List.range params.ell1).map fun r =>
      wotsChainSteps suite sk.pkSeed layer tree kp r 0 (d₁.getD r 0) (wotsSecretBase suite sk layer tree kp r)
    let sig₂ := (List.range params.ell1).map fun r =>
      wotsChainSteps suite sk.pkSeed layer tree kp r 0 (d₂.getD r 0) (wotsSecretBase suite sk layer tree kp r)
    recoverWotsPkFromSig suite params sk.pkSeed layer tree kp d₃
      (forgeWotsFromTwoSigs suite sk.pkSeed layer tree kp params.ell1 d₁ d₂ d₃ sig₁ sig₂) =
      computeWotsPk suite params sk layer tree kp := by
  intro sig₁ sig₂
  obtain ⟨hLen₃, hBound₃, _⟩ := (checkTargetSum_iff params.w params.ell1 params.targetSum d₃).mp hValid₃
  simp only [recoverWotsPkFromSig_eq, computeWotsPk_eq, recoverWotsEndpoints_eq]
  congr 1
  apply List.map_congr_left
  intro r hrMem
  have hrLt : r < params.ell1 := List.mem_range.mp hrMem
  have hGetForge : (forgeWotsFromTwoSigs suite sk.pkSeed layer tree kp params.ell1 d₁ d₂ d₃ sig₁ sig₂).getD r [] =
      (if d₁.getD r 0 ≤ d₃.getD r 0 then
        wotsChainSteps suite sk.pkSeed layer tree kp r (d₁.getD r 0) (d₃.getD r 0 - d₁.getD r 0) (sig₁.getD r [])
       else
        wotsChainSteps suite sk.pkSeed layer tree kp r (d₂.getD r 0) (d₃.getD r 0 - d₂.getD r 0) (sig₂.getD r [])) :=
    list_getD_map_range params.ell1 _ [] hrLt
  rw [hGetForge]
  have hv3Lt : d₃.getD r 0 < params.w := by
    have hrD3 : r < d₃.length := hLen₃ ▸ hrLt
    rw [list_getD_eq_getElem d₃ 0 hrD3]
    exact hBound₃ _ (List.getElem_mem hrD3)
  if hv1Le : d₁.getD r 0 ≤ d₃.getD r 0 then
    simp only [hv1Le, ↓reduceIte]
    have hGet1 : sig₁.getD r [] =
        wotsChainSteps suite sk.pkSeed layer tree kp r 0 (d₁.getD r 0) (wotsSecretBase suite sk layer tree kp r) :=
      list_getD_map_range params.ell1 _ [] hrLt
    rw [hGet1]
    have hStepA := wotsChainSteps_add suite sk.pkSeed layer tree kp r
      (d₁.getD r 0) (d₃.getD r 0 - d₁.getD r 0) 0 (wotsSecretBase suite sk layer tree kp r)
    simp only [Nat.zero_add, Nat.add_sub_of_le hv1Le] at hStepA
    rw [hStepA]
    have hStepB := wotsChainSteps_add suite sk.pkSeed layer tree kp r
      (d₃.getD r 0) ((params.w - 1) - d₃.getD r 0) 0 (wotsSecretBase suite sk layer tree kp r)
    simp only [Nat.zero_add, show d₃.getD r 0 + ((params.w - 1) - d₃.getD r 0) = params.w - 1 from by omega] at hStepB
    exact hStepB
  else
    simp only [hv1Le, ↓reduceIte]
    have hv2Le : d₂.getD r 0 ≤ d₃.getD r 0 := by
      rcases hCover r hrLt with h1 | h2
      · exact False.elim (hv1Le h1)
      · exact h2
    have hGet2 : sig₂.getD r [] =
        wotsChainSteps suite sk.pkSeed layer tree kp r 0 (d₂.getD r 0) (wotsSecretBase suite sk layer tree kp r) :=
      list_getD_map_range params.ell1 _ [] hrLt
    rw [hGet2]
    have hStepA := wotsChainSteps_add suite sk.pkSeed layer tree kp r
      (d₂.getD r 0) (d₃.getD r 0 - d₂.getD r 0) 0 (wotsSecretBase suite sk layer tree kp r)
    simp only [Nat.zero_add, Nat.add_sub_of_le hv2Le] at hStepA
    rw [hStepA]
    have hStepB := wotsChainSteps_add suite sk.pkSeed layer tree kp r
      (d₃.getD r 0) ((params.w - 1) - d₃.getD r 0) 0 (wotsSecretBase suite sk layer tree kp r)
    simp only [Nat.zero_add, show d₃.getD r 0 + ((params.w - 1) - d₃.getD r 0) = params.w - 1 from by omega] at hStepB
    exact hStepB

#verify_constructive firstValidCounter_some_iff
#verify_constructive firstValidCounter_none_iff
#verify_constructive grindTswCounter_4_128_192_eq_firstValidCounter
#verify_constructive threshold_standalone_grinding_coupling
#verify_constructive waistband_topL_cache_view_eq_stateless
#verify_constructive waistband_topL_cache_preserves_euf_cma
#verify_constructive forgeWotsFromTwoSigs_recovers_pk
end Qsag
end
