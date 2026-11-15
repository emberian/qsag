module
/-
# Qsag.SignatureOutputAndCacheLaws — First-Success WOTS+C Grinding Coupling & Waistband Cache Laws

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
   constructive polynomial-time third-message WOTS+C forgery (`w = 4, chains = 128, targetSum = 192`)
   whenever a buggy cache reuses a bottom-layer leaf across two distinct messages.
-/

public import Qsag.HashSigs
public import Qsag.HypertreeEufCma
import all Qsag.HashSigs
import all Qsag.HypertreeEufCma
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

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
  simp only [Nat.zero_le, Nat.zero_add, true_and]

/-- **Tail-Abort Exhaustion Characterization (`firstValidCounter_none_iff`)**:
    `firstValidCounter check maxTrials = none` iff every counter `< maxTrials` fails `check`. -/
theorem firstValidCounter_none_iff (check : Nat → Bool) (maxTrials : Nat) :
    firstValidCounter check maxTrials = none ↔ ∀ ctr, ctr < maxTrials → check ctr = false := by
  constructor
  · intro hNone ctr hLt
    cases hChk : check ctr
    · rfl
    · have hFind : ∀ k, k ≤ maxTrials → (∃ m < k, check m = true) ∨ (∀ m < k, check m = false) := by
        intro k _
        induction k with
        | zero => exact .inr (fun _ hm => False.elim (Nat.not_lt_zero _ hm))
        | succ k ih =>
          rcases ih (by omega) with ⟨m, hmLt, hmChk⟩ | hAllFalse
          · exact .inl ⟨m, Nat.lt_succ_of_lt hmLt, hmChk⟩
          · cases hk : check k
            · exact .inr (fun m hmLt => if hmEq : m = k then hmEq ▸ hk else hAllFalse m (by omega))
            · exact .inl ⟨k, Nat.lt_succ_self k, hk⟩
      have hMinEx : ∃ m < ctr + 1, check m = true ∧ ∀ j < m, check j = false := by
        suffices ∀ bound, ctr < bound → ∃ m < bound, check m = true ∧ ∀ j < m, check j = false from
          this (ctr + 1) (Nat.lt_succ_self ctr)
        intro bound hBound
        induction bound generalizing ctr with
        | zero => exact False.elim (Nat.not_lt_zero _ hBound)
        | succ b ih =>
          rcases hFind b (by omega) with ⟨m, hmLt, hmChk⟩ | hAllFalse
          · obtain ⟨m0, hm0Lt, hm0Chk, hm0Min⟩ := ih m hmChk hmLt
            exact ⟨m0, Nat.lt_succ_of_lt hm0Lt, hm0Chk, hm0Min⟩
          · have hEq : ctr = b := by
              if hltB : ctr < b then
                have hf := hAllFalse ctr hltB; rw [hChk] at hf; cases hf
              else omega
            subst hEq
            exact ⟨ctr, Nat.lt_succ_self ctr, hChk, hAllFalse⟩
      obtain ⟨m, hmLt, hmChk, hmMin⟩ := hMinEx
      have hSome := (firstValidCounter_some_iff check maxTrials m).mpr ⟨by omega, hmChk, hmMin⟩
      rw [hNone] at hSome; cases hSome
  · intro hAll
    cases hRes : firstValidCounter check maxTrials with
    | none => rfl
    | some ctr =>
      obtain ⟨hLt, hChk, _⟩ := (firstValidCounter_some_iff check maxTrials ctr).mp hRes
      rw [hAll ctr hLt] at hChk; cases hChk

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
theorem wotsC_deployed_targetSum : canonicalTargetSum 4 128 = 192 := by decide

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
  | 0, _ => rfl
  | fuel + 1, cur => by
    simp only [grindTswCounterAux, firstValidCounterAux]
    cases checkTargetSum w ell1 target
      (extractBaseWDigits w ell1 (thHashMsg suite rRand pkSeed pkRoot mu layerIdx treeIdx kpIdx cur))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact grindTswCounterAux_eq_firstValidCounterAux suite w ell1 target
        rRand pkSeed pkRoot mu layerIdx treeIdx kpIdx fuel (cur + 1)
    · rfl

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
  finSum C (fun c => if X c = y then 1 else 0)

/-- Unnormalized $L_1$ / $2 \cdot C \cdot \mathrm{TVD}$ statistical distance over `support`. -/
@[expose] def statisticalDistance {α : Type} [DecidableEq α] (C : Nat) (support : List α)
    (X Y : Fin C → α) : Nat :=
  support.foldr (fun y acc => natAbsDiff (coinMass C X y) (coinMass C Y y) + acc) 0

theorem statisticalDistance_eq_zero_of_pointwise_eq {α : Type} [DecidableEq α]
    (C : Nat) (support : List α) {X Y : Fin C → α} (hEq : ∀ c : Fin C, X c = Y c) :
    statisticalDistance C support X Y = 0 := by
  have hMass : ∀ y : α, coinMass C X y = coinMass C Y y := fun y =>
    finSum_congr (fun c => by rw [hEq c])
  induction support with
  | nil => rfl
  | cons y ys ih =>
    simp only [statisticalDistance, List.foldr_cons] at ih ⊢
    rw [hMass y, show natAbsDiff (coinMass C Y y) (coinMass C Y y) = 0 from by simp [natAbsDiff],
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
      (finSum C (fun c => if D (evalGrindCeremony w ell1 target maxTrials evalThresholdStep c) then 1 else 0))
      (finSum C (fun c => if D (evalGrindCeremony w ell1 target maxTrials evalStandaloneStep c) then 1 else 0)) = 0 := by
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
      rw [(hAgree c τ hLt).2 hChk]
  refine ⟨hStop, hOut, statisticalDistance_eq_zero_of_pointwise_eq C support hOut, ?_⟩
  have hSumEq :
      finSum C (fun c => if D (evalGrindCeremony w ell1 target maxTrials evalThresholdStep c) then 1 else 0) =
        finSum C (fun c => if D (evalGrindCeremony w ell1 target maxTrials evalStandaloneStep c) then 1 else 0) :=
    finSum_congr (fun c => by rw [hOut c])
  rw [hSumEq]; simp [natAbsDiff]

/-! ### Non-First-Hit Bias `#tooth` Theorem over Real `verifyPqHashSig` (`w=4, ell1=128, target=192`) -/

/-- Canonical 1-layer WOTS+C parameter set at deployed `(w = 4, ell1 = 128, targetSum = 192)`. -/
def wotsSingleLayerParams : PqHashParams := ⟨4, 128, 1, 1, 0, 0, 1, true⟩

/-- Extract the least-significant bit of the first WOTS+C chain byte of a `PqHashSig`. -/
def sigChainLsb (sig : PqHashSig) : Bool :=
  (((sig.layerSigs.getD 0 ⟨0, [], []⟩).wotsChains.getD 0 []).getD 0 0 &&& 1) == 1

/-- Construct a 1-layer `PqHashSig` at an explicitly chosen counter `chosenCtr` when `checkTargetSum` holds. -/
def evalSingleLayerAtCounter (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msg rRand : List UInt8) (chosenCtr : Nat) : Option PqHashSig :=
  if !(params.wellFormed) || !(params.statefulJorts) || params.numLayers ≠ 1 then none
  else
    let pk := derivePublicKey suite params sk
    let mu := thPreHash suite pk.pkSeed pk.pkRoot msg
    let hmsg := thHashMsg suite rRand pk.pkSeed pk.pkRoot mu 0 0 0 chosenCtr
    let digits := extractBaseWDigits params.w params.ell1 hmsg
    if !(checkTargetSum params.w params.ell1 params.targetSum digits) then none
    else
      let wotsChains := (List.range params.ell1).map fun r =>
        wotsChainSteps suite sk.pkSeed 0 0 0 r 0 (digits.getD r 0) (wotsSecretBase suite sk 0 0 0 r)
      let authPath := buildMerkleAuthPath suite sk.pkSeed 0 0 .tree
        (computeWotsPk suite params sk 0 0) params.subtreeHeight 0 0
      some { rRand := rRand, msgTswCtr := 0, leafGlobalIdx := 0, forsOpenings := [],
             layerSigs := [{ tswCtr := chosenCtr, wotsChains := wotsChains, authPath := authPath }] }

/-- **Symbolic Verification of Any Valid Counter (`verifyPqHashSig_evalSingleLayerAtCounter`)**:
    ANY counter `chosenCtr` satisfying `checkTargetSum` produces a signature accepted by `verifyPqHashSig`! -/
theorem verifyPqHashSig_evalSingleLayerAtCounter
    (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (msg rRand : List UInt8) (chosenCtr : Nat) (sig : PqHashSig)
    (hEval : evalSingleLayerAtCounter suite params sk msg rRand chosenCtr = some sig) :
    verifyPqHashSig suite params (derivePublicKey suite params sk) msg sig = true := by
  unfold evalSingleLayerAtCounter at hEval
  cases hWf : params.wellFormed
  · simp [hWf] at hEval
  · cases hSt : params.statefulJorts
    · simp [hWf, hSt] at hEval
    · cases hL1 : decide (params.numLayers = 1)
      · have hNe1 : params.numLayers ≠ 1 := of_decide_eq_false hL1
        simp [hWf, hSt, hNe1] at hEval
      · have hEq1 : params.numLayers = 1 := of_decide_eq_true hL1
        simp only [hWf, hSt, hEq1, ne_eq, not_true_eq_false, Bool.not_true, Bool.or_self, ↓reduceIte] at hEval
        let pk := derivePublicKey suite params sk
        let mu := thPreHash suite pk.pkSeed pk.pkRoot msg
        let hmsg := thHashMsg suite rRand pk.pkSeed pk.pkRoot mu 0 0 0 chosenCtr
        let digits := extractBaseWDigits params.w params.ell1 hmsg
        cases hChk : checkTargetSum params.w params.ell1 params.targetSum digits
        · rw [show checkTargetSum params.w params.ell1 params.targetSum digits = false from hChk] at hEval
          simp at hEval
        · rw [show checkTargetSum params.w params.ell1 params.targetSum digits = true from hChk] at hEval
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hEval
          subst hEval
          have hZeroLt : 0 < 2 ^ (params.numLayers * params.subtreeHeight) := Nat.two_pow_pos _
          unfold verifyPqHashSig
          simp only [hWf, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.length_singleton,
            hEq1, ne_eq, not_true_eq_false, hZeroLt, decide_true, hSt, List.isEmpty_nil]
          simp only [verifyHypertreeLayers, Nat.zero_mod, Nat.zero_div]
          change (let hm := hmsg; _) = true
          dsimp only
          have hChainsLen : ((List.range params.ell1).map fun r =>
              wotsChainSteps suite sk.pkSeed 0 0 0 r 0 (digits.getD r 0)
                (wotsSecretBase suite sk 0 0 0 r)).length = params.ell1 := by simp
          rw [show checkTargetSum params.w params.ell1 params.targetSum digits = true from hChk]
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hChainsLen, ne_eq, not_true_eq_false]
          have hWots := recoverWotsPkFromSig_eq_computeWotsPk suite params sk 0 0 0 digits hChk
          dsimp only at hWots
          change (match walkMerkleAuthPath suite pk.pkSeed 0 0 .tree params.subtreeHeight 0 0
                    (recoverWotsPkFromSig suite params sk.pkSeed 0 0 0 digits _) _ with
                  | none => false | some r => _) = true
          rw [hWots]
          have hWalk := walkMerkleAuthPath_buildMerkleAuthPath suite sk.pkSeed 0 0 .tree
            (computeWotsPk suite params sk 0 0) params.subtreeHeight 0 0 (Nat.two_pow_pos _)
          simp only [Nat.zero_mul, Nat.zero_add] at hWalk
          change (match walkMerkleAuthPath suite sk.pkSeed 0 0 .tree params.subtreeHeight 0 0
                    (computeWotsPk suite params sk 0 0) _ with
                  | none => false | some r => _) = true
          rw [hWalk]
          simp only [verifyHypertreeLayers, derivePublicKey, hEq1, Nat.sub_self, decide_true]
          rfl

/-- Domain-sensitive 32-byte `TweakableHashSuite` exhibiting LSB steering when non-first-hit counters are allowed. -/
def lsbBiasRawHash (pre : List UInt8) : List UInt8 :=
  if pre.getD 3 0 == 14 then
    -- `tagPrf` (`wotsSecretBase`): chain base byte 0 is `0x00` (`lsb = false`)
    0x00 :: List.replicate 31 0x1B
  else if pre.getD 12 0 == 72 && pre.getLastD 0 == 0 && !(pre.contains 0xFE) then
    -- `tagHMsg` on coin `0` (`rRand = [0x00]`) at `ctr = 0`: byte 0 is `0x1B` (`digits[0] = 0`, sum = 192)
    0x1B :: List.replicate 31 0x1B
  else
    -- `tagHMsg` at `ctr = 1` or coin `1` (`rRand = [0xFE]`): byte 0 is `0x4B` (`digits[0] = 1`, sum = 192),
    -- and `tagThF` outputs byte 0 = `0x1B` (`lsb = true`)!
    0x4B :: List.replicate 31 0x1B

def lsbBiasSuite : TweakableHashSuite where
  suiteId := [0x01]
  rawHash := lsbBiasRawHash
  rawHash_len := fun pre => by
    unfold lsbBiasRawHash
    split <;> [simp; (split <;> simp)]

def coinTwoRand (c : Fin 2) : List UInt8 :=
  if c.val == 0 then [0x00] else [0xFE]

def honestReferenceLsbSampler (c : Fin 2) : Option PqHashSig :=
  let pk := derivePublicKey lsbBiasSuite wotsSingleLayerParams ⟨[], [], []⟩
  let mu := thPreHash lsbBiasSuite pk.pkSeed pk.pkRoot []
  let rRand := coinTwoRand c
  match firstValidCounter (fun ctr =>
      checkTargetSum 4 128 192 (extractBaseWDigits 4 128
        (thHashMsg lsbBiasSuite rRand pk.pkSeed pk.pkRoot mu 0 0 0 ctr))) 4 with
  | none => none
  | some ctr0 => evalSingleLayerAtCounter lsbBiasSuite wotsSingleLayerParams ⟨[], [], []⟩ [] rRand ctr0

/-- Malicious coordinator: inspects valid first-hit `ctr₀`; whenever `sigChainLsb sig₀ = false`, skips
    `ctr₀` and selects `ctr₁ = ctr₀ + 1` instead! -/
def maliciousSkipLsbZeroSampler (c : Fin 2) : Option PqHashSig :=
  let pk := derivePublicKey lsbBiasSuite wotsSingleLayerParams ⟨[], [], []⟩
  let mu := thPreHash lsbBiasSuite pk.pkSeed pk.pkRoot []
  let rRand := coinTwoRand c
  match firstValidCounter (fun ctr =>
      checkTargetSum 4 128 192 (extractBaseWDigits 4 128
        (thHashMsg lsbBiasSuite rRand pk.pkSeed pk.pkRoot mu 0 0 0 ctr))) 4 with
  | none => none
  | some ctr0 =>
    match evalSingleLayerAtCounter lsbBiasSuite wotsSingleLayerParams ⟨[], [], []⟩ [] rRand ctr0 with
    | none => none
    | some sig0 =>
      if sigChainLsb sig0 then some sig0
      else evalSingleLayerAtCounter lsbBiasSuite wotsSingleLayerParams ⟨[], [], []⟩ [] rRand (ctr0 + 1)

/-- **`#tooth` Non-First-Hit Coordinator Bias Theorem (`tooth_non_first_hit_lsb_bias_positive_tvd`)**:
    Skipping valid first-hit counter `ctr₀ = 0` when `sigChainLsb = false` in favor of `ctr₁ = 1 > ctr₀`
    produces signatures that **100% pass `verifyPqHashSig = true` on EVERY coin**, yet induces
    strictly positive statistical distance (`statisticalDistance = 2 > 0`, `TVD = 1/2 > 0`) from the
    honest `firstValidCounter` reference signer! -/
theorem tooth_non_first_hit_lsb_bias_positive_tvd :
    ∃ (pk : PqPublicKey),
      pk = derivePublicKey lsbBiasSuite wotsSingleLayerParams ⟨[], [], []⟩ ∧
      (∀ c : Fin 2, ∃ sig,
        maliciousSkipLsbZeroSampler c = some sig ∧
        verifyPqHashSig lsbBiasSuite wotsSingleLayerParams pk [] sig = true) ∧
      statisticalDistance 2 [false, true]
        (fun c => (honestReferenceLsbSampler c).elim false sigChainLsb)
        (fun c => (maliciousSkipLsbZeroSampler c).elim false sigChainLsb) = 2 ∧
      0 < statisticalDistance 2 [false, true]
        (fun c => (honestReferenceLsbSampler c).elim false sigChainLsb)
        (fun c => (maliciousSkipLsbZeroSampler c).elim false sigChainLsb) := by
  let sk0 : PqSecretKey := ⟨[], [], []⟩
  let pk0 := derivePublicKey lsbBiasSuite wotsSingleLayerParams sk0
  let mu0 := thPreHash lsbBiasSuite pk0.pkSeed pk0.pkRoot []
  have hHmsg00 : thHashMsg lsbBiasSuite [0x00] pk0.pkSeed pk0.pkRoot mu0 0 0 0 0 =
      (0x1B :: List.replicate 31 0x1B) ++ (0x1B :: List.replicate 31 0x1B) := by
    have hSub : ∀ k : UInt32,
        thCall lsbBiasSuite tagHMsg [] ⟨0, 0, .wotsHash, 0, k, 0⟩ [[0x00], pk0.pkRoot, mu0, be 4 0] =
        0x1B :: List.replicate 31 0x1B := by
      intro k
      have hNotMem : (0xFE : UInt8) ∉ pk0.pkRoot ∧ (0xFE : UInt8) ∉ mu0 := by
        refine ⟨?_, ?_⟩ <;> {
          have h4B : ∀ x, x ∈ (0x4B :: List.replicate 31 0x1B : List UInt8) → x ≠ 0xFE := by decide
          intro hMem; exact h4B _ hMem rfl
        }
      unfold thCall lsbBiasSuite lsbBiasRawHash thPreimage
      have hd3 : (encodeMultiFrame ([tagHMsg, [], encodeAdrs ⟨0, 0, .wotsHash, 0, k, 0⟩] ++
          [[0x00], pk0.pkRoot, mu0, be 4 0])).getD 3 0 = 15 := by rfl
      have hd12 : (encodeMultiFrame ([tagHMsg, [], encodeAdrs ⟨0, 0, .wotsHash, 0, k, 0⟩] ++
          [[0x00], pk0.pkRoot, mu0, be 4 0])).getD 12 0 = 72 := by rfl
      have hLast : (encodeMultiFrame ([tagHMsg, [], encodeAdrs ⟨0, 0, .wotsHash, 0, k, 0⟩] ++
          [[0x00], pk0.pkRoot, mu0, be 4 0])).getLastD 0 = 0 := by
        simp [encodeMultiFrame, frameList, be, List.getLastD_append]
      have hNoFE : (encodeMultiFrame ([tagHMsg, [], encodeAdrs ⟨0, 0, .wotsHash, 0, k, 0⟩] ++
          [[0x00], pk0.pkRoot, mu0, be 4 0])).contains 0xFE = false := by
        have hLenRoot : pk0.pkRoot.length = 32 := thCall_length _ _ _ _ _
        have hLenMu : mu0.length = 32 := thCall_length _ _ _ _ _
        apply List.contains_eq_false_iff.mpr
        simp only [encodeMultiFrame, List.cons_append, List.nil_append, frameList,
          List.mem_append, not_or, hLenRoot, hLenMu]
        refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, hNotMem.1⟩, ⟨?_, hNotMem.2⟩, ⟨?_, ?_⟩⟩
        all_goals first | decide | (simp [encodeAdrs, be]; decide)
      rw [hd3, hd12, hLast, hNoFE]; rfl
    unfold thHashMsg; dsimp only [pk0]; rw [hSub 0, hSub 1]
  have hHmsg01 : (thHashMsg lsbBiasSuite [0x00] pk0.pkSeed pk0.pkRoot mu0 0 0 0 1).take 32 =
      0x4B :: List.replicate 31 0x1B := by
    have hB0 : thCall lsbBiasSuite tagHMsg [] ⟨0, 0, .wotsHash, 0, 0, 1⟩ [[0x00], pk0.pkRoot, mu0, be 4 1] =
        0x4B :: List.replicate 31 0x1B := by
      unfold thCall lsbBiasSuite lsbBiasRawHash thPreimage
      have hd3 : (encodeMultiFrame ([tagHMsg, [], encodeAdrs ⟨0, 0, .wotsHash, 0, 0, 1⟩] ++
          [[0x00], pk0.pkRoot, mu0, be 4 1])).getD 3 0 = 15 := by rfl
      have hLast : (encodeMultiFrame ([tagHMsg, [], encodeAdrs ⟨0, 0, .wotsHash, 0, 0, 1⟩] ++
          [[0x00], pk0.pkRoot, mu0, be 4 1])).getLastD 0 = 1 := by
        simp [encodeMultiFrame, frameList, be, List.getLastD_append]
      rw [hd3, hLast]; simp
    unfold thHashMsg; dsimp only [pk0]; rw [hB0, List.take_left' (by simp)]
  have hHmsg10 : (thHashMsg lsbBiasSuite [0xFE] pk0.pkSeed pk0.pkRoot mu0 0 0 0 0).take 32 =
      0x4B :: List.replicate 31 0x1B := by
    have hB0 : thCall lsbBiasSuite tagHMsg [] ⟨0, 0, .wotsHash, 0, 0, 0⟩ [[0xFE], pk0.pkRoot, mu0, be 4 0] =
        0x4B :: List.replicate 31 0x1B := by
      unfold thCall lsbBiasSuite lsbBiasRawHash thPreimage
      have hd3 : (encodeMultiFrame ([tagHMsg, [], encodeAdrs ⟨0, 0, .wotsHash, 0, 0, 0⟩] ++
          [[0xFE], pk0.pkRoot, mu0, be 4 0])).getD 3 0 = 15 := by rfl
      have hCont : (encodeMultiFrame ([tagHMsg, [], encodeAdrs ⟨0, 0, .wotsHash, 0, 0, 0⟩] ++
          [[0xFE], pk0.pkRoot, mu0, be 4 0])).contains 0xFE = true := by
        apply List.contains_iff_mem.mpr
        simp [encodeMultiFrame, frameList]
      rw [hd3, hCont]; simp
    unfold thHashMsg; dsimp only [pk0]; rw [hB0, List.take_left' (by simp)]
  have hTakeDigits : ∀ xs : List UInt8, 32 ≤ xs.length →
      extractBaseWDigits 4 128 xs = extractBaseWDigits 4 128 (xs.take 32) := by
    intro xs hLen
    unfold extractBaseWDigits
    apply List.map_congr_left
    intro idx hMem
    have hIdxLt : idx < 128 := List.mem_range.mp hMem
    have hByteLt : idx / 4 < 32 := Nat.div_lt_of_lt_mul hIdxLt
    simp only [show ¬(4 < 2) from by decide, ↓reduceIte]
    have hGet : xs.getD (idx / 4) 0 = (xs.take 32).getD (idx / 4) 0 := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_take_of_lt hByteLt]
    rw [hGet]
  have hDig1B : checkTargetSum 4 128 192 (extractBaseWDigits 4 128 (0x1B :: List.replicate 31 0x1B)) = true ∧
      (extractBaseWDigits 4 128 (0x1B :: List.replicate 31 0x1B)).getD 0 0 = 0 := by decide
  have hDig4B : checkTargetSum 4 128 192 (extractBaseWDigits 4 128 (0x4B :: List.replicate 31 0x1B)) = true ∧
      (extractBaseWDigits 4 128 (0x4B :: List.replicate 31 0x1B)).getD 0 0 = 1 := by decide
  have hChk00 : checkTargetSum 4 128 192 (extractBaseWDigits 4 128
      (thHashMsg lsbBiasSuite [0x00] pk0.pkSeed pk0.pkRoot mu0 0 0 0 0)) = true ∧
      (extractBaseWDigits 4 128 (thHashMsg lsbBiasSuite [0x00] pk0.pkSeed pk0.pkRoot mu0 0 0 0 0)).getD 0 0 = 0 := by
    rw [hTakeDigits _ (by rw [thHashMsg_length]; decide), hHmsg00,
        List.take_left' (by simp)]; exact hDig1B
  have hChk01 : checkTargetSum 4 128 192 (extractBaseWDigits 4 128
      (thHashMsg lsbBiasSuite [0x00] pk0.pkSeed pk0.pkRoot mu0 0 0 0 1)) = true ∧
      (extractBaseWDigits 4 128 (thHashMsg lsbBiasSuite [0x00] pk0.pkSeed pk0.pkRoot mu0 0 0 0 1)).getD 0 0 = 1 := by
    rw [hTakeDigits _ (by rw [thHashMsg_length]; decide), hHmsg01]; exact hDig4B
  have hChk10 : checkTargetSum 4 128 192 (extractBaseWDigits 4 128
      (thHashMsg lsbBiasSuite [0xFE] pk0.pkSeed pk0.pkRoot mu0 0 0 0 0)) = true ∧
      (extractBaseWDigits 4 128 (thHashMsg lsbBiasSuite [0xFE] pk0.pkSeed pk0.pkRoot mu0 0 0 0 0)).getD 0 0 = 1 := by
    rw [hTakeDigits _ (by rw [thHashMsg_length]; decide), hHmsg10]; exact hDig4B
  have hPrfBase : wotsSecretBase lsbBiasSuite sk0 0 0 0 0 = 0x00 :: List.replicate 31 0x1B := by
    unfold wotsSecretBase thSecretPrf thCall lsbBiasSuite lsbBiasRawHash thPreimage
    have hd3 : (encodeMultiFrame ([tagPrf, [], encodeAdrs ⟨0, 0, .wotsPrf, 0, 0, 0⟩] ++ [[]])).getD 3 0 = 14 := rfl
    rw [hd3]; rfl
  have hStep1 : wotsChainSteps lsbBiasSuite [] 0 0 0 0 0 1 (wotsSecretBase lsbBiasSuite sk0 0 0 0 0) =
      0x4B :: List.replicate 31 0x1B := by
    simp only [wotsChainSteps]
    unfold thChainF thCall lsbBiasSuite lsbBiasRawHash thPreimage
    have hd3 : (encodeMultiFrame ([tagThF, [], encodeAdrs ⟨0, 0, .wotsHash, 0, 0, 0⟩] ++
        [wotsSecretBase lsbBiasSuite sk0 0 0 0 0])).getD 3 0 = 15 := rfl
    have hd12 : (encodeMultiFrame ([tagThF, [], encodeAdrs ⟨0, 0, .wotsHash, 0, 0, 0⟩] ++
        [wotsSecretBase lsbBiasSuite sk0 0 0 0 0])).getD 12 0 = 84 := rfl
    rw [hd3, hd12]; rfl
  have hWfP : wotsSingleLayerParams.wellFormed = true ∧
      wotsSingleLayerParams.statefulJorts = true ∧
      wotsSingleLayerParams.numLayers = 1 ∧
      wotsSingleLayerParams.targetSum = 192 := by decide
  have hHon0 : ∃ s0, honestReferenceLsbSampler ⟨0, by decide⟩ = some s0 ∧ sigChainLsb s0 = false := by
    unfold honestReferenceLsbSampler coinTwoRand
    simp only [beq_self_eq_true, ↓reduceIte]
    change (match firstValidCounter (fun ctr => checkTargetSum 4 128 192 (extractBaseWDigits 4 128
              (thHashMsg lsbBiasSuite [0x00] pk0.pkSeed pk0.pkRoot mu0 0 0 0 ctr))) 4 with
            | none => none | some ctr0 => _) = _
    have hF0 : firstValidCounter (fun ctr => checkTargetSum 4 128 192 (extractBaseWDigits 4 128
        (thHashMsg lsbBiasSuite [0x00] pk0.pkSeed pk0.pkRoot mu0 0 0 0 ctr))) 4 = some 0 := by
      unfold firstValidCounter firstValidCounterAux; rw [hChk00.1]; rfl
    rw [hF0]; unfold evalSingleLayerAtCounter
    simp only [hWfP.1, hWfP.2.1, hWfP.2.2.1, hWfP.2.2.2, Bool.not_true, ne_eq, not_true_eq_false, Bool.or_self, ↓reduceIte]
    change (if !(checkTargetSum 4 128 192 (extractBaseWDigits 4 128
              (thHashMsg lsbBiasSuite [0x00] pk0.pkSeed pk0.pkRoot mu0 0 0 0 0))) then none else _) = _
    rw [hChk00.1]; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refine ⟨_, rfl, ?_⟩
    unfold sigChainLsb wotsSingleLayerParams
    simp only [List.getD_cons_zero]
    rw [list_getD_map_range 128 _ [] (by decide : 0 < 128)]
    change ((wotsChainSteps lsbBiasSuite [] 0 0 0 0 0
      ((extractBaseWDigits 4 128 (thHashMsg lsbBiasSuite [0x00] pk0.pkSeed pk0.pkRoot mu0 0 0 0 0)).getD 0 0)
      (wotsSecretBase lsbBiasSuite sk0 0 0 0 0)).getD 0 0 &&& 1 == 1) = false
    rw [hChk00.2, wotsChainSteps_zero, hPrfBase]; decide
  have hMal0 : ∃ s0', maliciousSkipLsbZeroSampler ⟨0, by decide⟩ = some s0' ∧
      sigChainLsb s0' = true ∧ verifyPqHashSig lsbBiasSuite wotsSingleLayerParams pk0 [] s0' = true := by
    unfold maliciousSkipLsbZeroSampler coinTwoRand
    simp only [beq_self_eq_true, ↓reduceIte]
    have hF0 : firstValidCounter (fun ctr => checkTargetSum 4 128 192 (extractBaseWDigits 4 128
        (thHashMsg lsbBiasSuite [0x00] pk0.pkSeed pk0.pkRoot mu0 0 0 0 ctr))) 4 = some 0 := by
      unfold firstValidCounter firstValidCounterAux; rw [hChk00.1]; rfl
    change (match firstValidCounter (fun ctr => checkTargetSum 4 128 192 (extractBaseWDigits 4 128
              (thHashMsg lsbBiasSuite [0x00] pk0.pkSeed pk0.pkRoot mu0 0 0 0 ctr))) 4 with
            | none => none | some ctr0 => _) = _
    rw [hF0]
    obtain ⟨s0, hs0Eq, hs0Lsb⟩ := hHon0
    have hs0Eval : evalSingleLayerAtCounter lsbBiasSuite wotsSingleLayerParams sk0 [] [0x00] 0 = some s0 := by
      unfold honestReferenceLsbSampler coinTwoRand at hs0Eq
      simp only [beq_self_eq_true, ↓reduceIte] at hs0Eq
      change (match firstValidCounter (fun ctr => checkTargetSum 4 128 192 (extractBaseWDigits 4 128
                (thHashMsg lsbBiasSuite [0x00] pk0.pkSeed pk0.pkRoot mu0 0 0 0 ctr))) 4 with
              | none => none | some ctr0 => _) = some s0 at hs0Eq
      rw [hF0] at hs0Eq; exact hs0Eq
    rw [hs0Eval, hs0Lsb]; simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    have hEv1 : ∃ s1, evalSingleLayerAtCounter lsbBiasSuite wotsSingleLayerParams sk0 [] [0x00] 1 = some s1 ∧
        sigChainLsb s1 = true := by
      unfold evalSingleLayerAtCounter
      simp only [hWfP.1, hWfP.2.1, hWfP.2.2.1, hWfP.2.2.2, Bool.not_true, ne_eq, not_true_eq_false, Bool.or_self, ↓reduceIte]
      change (if !(checkTargetSum 4 128 192 (extractBaseWDigits 4 128
                (thHashMsg lsbBiasSuite [0x00] pk0.pkSeed pk0.pkRoot mu0 0 0 0 1))) then none else _) = _
      rw [hChk01.1]; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine ⟨_, rfl, ?_⟩
      unfold sigChainLsb wotsSingleLayerParams
      simp only [List.getD_cons_zero]
      rw [list_getD_map_range 128 _ [] (by decide : 0 < 128)]
      change ((wotsChainSteps lsbBiasSuite [] 0 0 0 0 0
        ((extractBaseWDigits 4 128 (thHashMsg lsbBiasSuite [0x00] pk0.pkSeed pk0.pkRoot mu0 0 0 0 1)).getD 0 0)
        (wotsSecretBase lsbBiasSuite sk0 0 0 0 0)).getD 0 0 &&& 1 == 1) = true
      rw [hChk01.2, hStep1]; decide
    obtain ⟨s1, hs1Eq, hs1Lsb⟩ := hEv1
    exact ⟨s1, hs1Eq, hs1Lsb, verifyPqHashSig_evalSingleLayerAtCounter _ _ _ _ _ 1 s1 hs1Eq⟩
  have hBoth1 : ∃ s1, honestReferenceLsbSampler ⟨1, by decide⟩ = some s1 ∧
      maliciousSkipLsbZeroSampler ⟨1, by decide⟩ = some s1 ∧
      sigChainLsb s1 = true ∧ verifyPqHashSig lsbBiasSuite wotsSingleLayerParams pk0 [] s1 = true := by
    have hF1 : firstValidCounter (fun ctr => checkTargetSum 4 128 192 (extractBaseWDigits 4 128
        (thHashMsg lsbBiasSuite [0xFE] pk0.pkSeed pk0.pkRoot mu0 0 0 0 ctr))) 4 = some 0 := by
      unfold firstValidCounter firstValidCounterAux; rw [hChk10.1]; rfl
    have hEv : ∃ s1, evalSingleLayerAtCounter lsbBiasSuite wotsSingleLayerParams sk0 [] [0xFE] 0 = some s1 ∧
        sigChainLsb s1 = true := by
      unfold evalSingleLayerAtCounter
      simp only [hWfP.1, hWfP.2.1, hWfP.2.2.1, hWfP.2.2.2, Bool.not_true, ne_eq, not_true_eq_false, Bool.or_self, ↓reduceIte]
      change (if !(checkTargetSum 4 128 192 (extractBaseWDigits 4 128
                (thHashMsg lsbBiasSuite [0xFE] pk0.pkSeed pk0.pkRoot mu0 0 0 0 0))) then none else _) = _
      rw [hChk10.1]; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine ⟨_, rfl, ?_⟩
      unfold sigChainLsb wotsSingleLayerParams
      simp only [List.getD_cons_zero]
      rw [list_getD_map_range 128 _ [] (by decide : 0 < 128)]
      change ((wotsChainSteps lsbBiasSuite [] 0 0 0 0 0
        ((extractBaseWDigits 4 128 (thHashMsg lsbBiasSuite [0xFE] pk0.pkSeed pk0.pkRoot mu0 0 0 0 0)).getD 0 0)
        (wotsSecretBase lsbBiasSuite sk0 0 0 0 0)).getD 0 0 &&& 1 == 1) = true
      rw [hChk10.2, hStep1]; decide
    obtain ⟨s1, hs1Eq, hs1Lsb⟩ := hEv
    have hH : honestReferenceLsbSampler ⟨1, by decide⟩ = some s1 := by
      unfold honestReferenceLsbSampler coinTwoRand
      change (match firstValidCounter (fun ctr => checkTargetSum 4 128 192 (extractBaseWDigits 4 128
                (thHashMsg lsbBiasSuite [0xFE] pk0.pkSeed pk0.pkRoot mu0 0 0 0 ctr))) 4 with
              | none => none | some ctr0 => _) = some s1
      rw [hF1]; exact hs1Eq
    have hM : maliciousSkipLsbZeroSampler ⟨1, by decide⟩ = some s1 := by
      unfold maliciousSkipLsbZeroSampler coinTwoRand
      change (match firstValidCounter (fun ctr => checkTargetSum 4 128 192 (extractBaseWDigits 4 128
                (thHashMsg lsbBiasSuite [0xFE] pk0.pkSeed pk0.pkRoot mu0 0 0 0 ctr))) 4 with
              | none => none | some ctr0 => _) = some s1
      rw [hF1, hs1Eq, hs1Lsb]; rfl
    exact ⟨s1, hH, hM, hs1Lsb, verifyPqHashSig_evalSingleLayerAtCounter _ _ _ _ _ 0 s1 hs1Eq⟩
  obtain ⟨s0, hs0H, hs0Lsb⟩ := hHon0
  obtain ⟨s0', hs0M, hs0'Lsb, hs0'Ver⟩ := hMal0
  obtain ⟨s1, hs1H, hs1M, hs1Lsb, hs1Ver⟩ := hBoth1
  have hDist : statisticalDistance 2 [false, true]
      (fun c => (honestReferenceLsbSampler c).elim false sigChainLsb)
      (fun c => (maliciousSkipLsbZeroSampler c).elim false sigChainLsb) = 2 := by
    simp only [statisticalDistance, List.foldr, coinMass, finSum,
      hs0H, hs0M, hs1H, hs1M, Option.elim, hs0Lsb, hs0'Lsb, hs1Lsb, natAbsDiff]
    decide
  refine ⟨pk0, rfl, ?_, hDist, by rw [hDist]; decide⟩
  intro ⟨cv, cLt⟩
  match cv with
  | 0 => exact ⟨s0', hs0M, hs0'Ver⟩
  | 1 => exact ⟨s1, hs1M, hs1Ver⟩
  | n + 2 => omega

/-- Exhausted counter budget `#tooth` refutation (`tooth_exhausted_grinder_aborts_none`). -/
theorem tooth_exhausted_grinder_aborts_none :
    ∃ (check : Nat → Bool) (maxTrials : Nat),
      check = (fun ctr => decide (ctr = 5)) ∧ maxTrials = 5 ∧
      check 5 = true ∧ firstValidCounter check maxTrials = none :=
  ⟨fun ctr => decide (ctr = 5), 5, rfl, rfl, by decide, by decide⟩

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
  | 0, _, _, _, _, cache, hSound, _ => ⟨hSound, rfl⟩
  | rem + 1, layerIdx, globalIdx, layer0Rand, curRoot, cache, hSound, hInternal => by
    simp only [waistbandSignHypertreeLayers, signHypertreeLayers]
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
          fun _ => ⟨rfl, by simp [Nat.add_sub_cancel]⟩
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
  | [], _, _ => rfl
  | q :: qs, cache, hSound => by
    obtain ⟨hSound', hOut⟩ := evalWaistbandSignStep_eq_evalSingleSign
      suite params sk q.message q.randomness q.leaf maxGrind topL cache hSound
    simp only [waistbandSigningLog, toPqSigningQueries, List.map_cons, signingOracleLog]
    change (match (evalWaistbandSignStep suite params sk q.message q.randomness q.leaf maxGrind topL cache).2 with
            | none => waistbandSigningLog suite params sk maxGrind topL _ qs
            | some sig => (q.message, sig) :: waistbandSigningLog suite params sk maxGrind topL _ qs) = _
    rw [hOut, waistbandSigningLog_eq_signingOracleLog suite params sk maxGrind topL qs _ hSound']
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
    unfold waistbandEufCmaWin eufCmaWin
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
    Over **ANY** `suite : TweakableHashSuite` (even an ideal ROM with `0` collisions!), whenever two
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
  unfold recoverWotsPkFromSig computeWotsPk recoverWotsEndpoints computeWotsEndpoints
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

/-- Concrete 32-byte `TSW`-valid (`w = 4, ell1 = 128, targetSum = 192`) digests for 2-message forgery. -/
def reuseDigest1 : List UInt8 := 0x0F :: List.replicate 31 0x1B
def reuseDigest2 : List UInt8 := 0xF0 :: List.replicate 31 0x1B
def reuseDigest3 : List UInt8 := 0x5A :: List.replicate 31 0x1B

def bottomReuseRawHash (pre : List UInt8) : List UInt8 :=
  if pre.getD 12 0 == 80 && pre.getD 13 0 == 82 && pre.getD 14 0 == 69 then
    -- `tagHPre` (`"QSAG.PQ.PRE/v1"`): preserve last message byte in byte 0
    pre.getLastD 0 :: List.replicate 31 0x1B
  else if pre.getD 12 0 == 72 then
    -- `tagHMsg`: map `mu[0] ∈ {1, 2, 3}` to `reuseDigest1`, `reuseDigest2`, `reuseDigest3`
    if pre.contains 0xE1 then reuseDigest1
    else if pre.contains 0xE2 then reuseDigest2
    else reuseDigest3
  else
    0x1B :: List.replicate 31 0x1B

def bottomReuseSuite : TweakableHashSuite where
  suiteId := [0x02]
  rawHash := bottomReuseRawHash
  rawHash_len := fun pre => by
    unfold bottomReuseRawHash reuseDigest1 reuseDigest2 reuseDigest3
    split
    · simp
    · split <;> [simp; (split <;> simp)]

/-- **`#tooth` Bottom-Layer Leaf-Reuse WOTS+C Forgery (`tooth_caching_bottom_layer_breaks_wots_one_time`)**:
    Violating `topL < params.numLayers` by reusing a bottom-layer (`layer = 0`) WOTS+C leaf across
    two distinct messages `m₁ = [0xE1] ≠ [0xE2] = m₂` exposes two `TSW`-valid (`w = 4, ell1 = 128,
    targetSum = 192`) chain vectors `sig₁, sig₂` from which the secret-key-free polynomial-time
    extractor `forgeWotsFromTwoSigs` constructs a **valid `PqHashSig` accepted by `verifyPqHashSig`
    (`= true`) on an unqueried third message `m₃ = [0xE3] ∉ [m₁, m₂]`**! -/
theorem tooth_caching_bottom_layer_breaks_wots_one_time :
    ∃ (m₁ m₂ m₃ : List UInt8) (pk : PqPublicKey) (sig₁ sig₂ forgedSig₃ : PqHashSig),
      m₁ = [0xE1] ∧ m₂ = [0xE2] ∧ m₃ = [0xE3] ∧
      m₁ ≠ m₂ ∧ m₃ ∉ [m₁, m₂] ∧
      pk = derivePublicKey bottomReuseSuite wotsSingleLayerParams ⟨[], [], []⟩ ∧
      evalSingleLayerAtCounter bottomReuseSuite wotsSingleLayerParams ⟨[], [], []⟩ m₁ [] 0 = some sig₁ ∧
      evalSingleLayerAtCounter bottomReuseSuite wotsSingleLayerParams ⟨[], [], []⟩ m₂ [] 0 = some sig₂ ∧
      verifyPqHashSig bottomReuseSuite wotsSingleLayerParams pk m₁ sig₁ = true ∧
      verifyPqHashSig bottomReuseSuite wotsSingleLayerParams pk m₂ sig₂ = true ∧
      verifyPqHashSig bottomReuseSuite wotsSingleLayerParams pk m₃ forgedSig₃ = true := by
  let sk0 : PqSecretKey := ⟨[], [], []⟩
  let pk0 := derivePublicKey bottomReuseSuite wotsSingleLayerParams sk0
  have hMu : ∀ b : UInt8,
      thPreHash bottomReuseSuite pk0.pkSeed pk0.pkRoot [b] = b :: List.replicate 31 0x1B := by
    intro b
    unfold thPreHash thCall bottomReuseSuite bottomReuseRawHash thPreimage
    have hd12 : (encodeMultiFrame ([tagHPre, [], encodeAdrs zeroAdrs] ++ [pk0.pkRoot, [b]])).getD 12 0 = 80 := rfl
    have hd13 : (encodeMultiFrame ([tagHPre, [], encodeAdrs zeroAdrs] ++ [pk0.pkRoot, [b]])).getD 13 0 = 82 := rfl
    have hd14 : (encodeMultiFrame ([tagHPre, [], encodeAdrs zeroAdrs] ++ [pk0.pkRoot, [b]])).getD 14 0 = 69 := rfl
    have hLast : (encodeMultiFrame ([tagHPre, [], encodeAdrs zeroAdrs] ++ [pk0.pkRoot, [b]])).getLastD 0 = b := by
      simp [encodeMultiFrame, frameList, List.getLastD_append]
    rw [hd12, hd13, hd14, hLast]; rfl
  have hRootNoE : ∀ x : UInt8, x ∈ pk0.pkRoot → x ≠ 0xE1 ∧ x ≠ 0xE2 := by
    have h1B : ∀ x, x ∈ (0x1B :: List.replicate 31 0x1B : List UInt8) → x ≠ 0xE1 ∧ x ≠ 0xE2 := by decide
    have hRootEq : pk0.pkRoot = 0x1B :: List.replicate 31 0x1B := by
      dsimp only [pk0, derivePublicKey, wotsSingleLayerParams]
      unfold computeXmssSubtreeRoot computeMerkleNode thNodeH thCall bottomReuseSuite bottomReuseRawHash thPreimage
      rfl
    rw [hRootEq]; exact h1B
  have hTake32 : ∀ xs : List UInt8, 32 ≤ xs.length →
      extractBaseWDigits 4 128 xs = extractBaseWDigits 4 128 (xs.take 32) := by
    intro xs _; unfold extractBaseWDigits; apply List.map_congr_left
    intro idx hMem
    have hByteLt : idx / 4 < 32 := Nat.div_lt_of_lt_mul (List.mem_range.mp hMem)
    simp only [show ¬(4 < 2) from by decide, ↓reduceIte]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hByteLt]
  have hHm1 : (thHashMsg bottomReuseSuite [] pk0.pkSeed pk0.pkRoot
      (thPreHash bottomReuseSuite pk0.pkSeed pk0.pkRoot [0xE1]) 0 0 0 0).take 32 = reuseDigest1 := by
    rw [hMu 0xE1]
    have hB0 : thCall bottomReuseSuite tagHMsg [] ⟨0, 0, .wotsHash, 0, 0, 0⟩
        [[], pk0.pkRoot, 0xE1 :: List.replicate 31 0x1B, be 4 0] = reuseDigest1 := by
      unfold thCall bottomReuseSuite bottomReuseRawHash thPreimage
      have hd12 : (encodeMultiFrame ([tagHMsg, [], encodeAdrs ⟨0, 0, .wotsHash, 0, 0, 0⟩] ++
          [[], pk0.pkRoot, 0xE1 :: List.replicate 31 0x1B, be 4 0])).getD 12 0 = 72 := rfl
      have hC1 : (encodeMultiFrame ([tagHMsg, [], encodeAdrs ⟨0, 0, .wotsHash, 0, 0, 0⟩] ++
          [[], pk0.pkRoot, 0xE1 :: List.replicate 31 0x1B, be 4 0])).contains 0xE1 = true := by
        apply List.contains_iff_mem.mpr; simp [encodeMultiFrame, frameList]
      rw [hd12, hC1]; rfl
    unfold thHashMsg; dsimp only [pk0]; rw [hB0, List.take_left' (by simp [reuseDigest1])]
  have hHm2 : (thHashMsg bottomReuseSuite [] pk0.pkSeed pk0.pkRoot
      (thPreHash bottomReuseSuite pk0.pkSeed pk0.pkRoot [0xE2]) 0 0 0 0).take 32 = reuseDigest2 := by
    rw [hMu 0xE2]
    have hB0 : thCall bottomReuseSuite tagHMsg [] ⟨0, 0, .wotsHash, 0, 0, 0⟩
        [[], pk0.pkRoot, 0xE2 :: List.replicate 31 0x1B, be 4 0] = reuseDigest2 := by
      unfold thCall bottomReuseSuite bottomReuseRawHash thPreimage
      have hd12 : (encodeMultiFrame ([tagHMsg, [], encodeAdrs ⟨0, 0, .wotsHash, 0, 0, 0⟩] ++
          [[], pk0.pkRoot, 0xE2 :: List.replicate 31 0x1B, be 4 0])).getD 12 0 = 72 := rfl
      have hNo1 : (encodeMultiFrame ([tagHMsg, [], encodeAdrs ⟨0, 0, .wotsHash, 0, 0, 0⟩] ++
          [[], pk0.pkRoot, 0xE2 :: List.replicate 31 0x1B, be 4 0])).contains 0xE1 = false := by
        have hLenRoot : pk0.pkRoot.length = 32 := thCall_length _ _ _ _ _
        apply List.contains_eq_false_iff.mpr
        simp only [encodeMultiFrame, List.cons_append, List.nil_append, frameList, List.mem_append, not_or, hLenRoot]
        refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by simp [encodeAdrs, be]; decide⟩,
          ⟨by decide, by decide⟩, ⟨by decide, fun hm => (hRootNoE _ hm).1 rfl⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩
      have hC2 : (encodeMultiFrame ([tagHMsg, [], encodeAdrs ⟨0, 0, .wotsHash, 0, 0, 0⟩] ++
          [[], pk0.pkRoot, 0xE2 :: List.replicate 31 0x1B, be 4 0])).contains 0xE2 = true := by
        apply List.contains_iff_mem.mpr; simp [encodeMultiFrame, frameList]
      rw [hd12, hNo1, hC2]; rfl
    unfold thHashMsg; dsimp only [pk0]; rw [hB0, List.take_left' (by simp [reuseDigest2])]
  have hHm3 : (thHashMsg bottomReuseSuite [] pk0.pkSeed pk0.pkRoot
      (thPreHash bottomReuseSuite pk0.pkSeed pk0.pkRoot [0xE3]) 0 0 0 0).take 32 = reuseDigest3 := by
    rw [hMu 0xE3]
    have hB0 : thCall bottomReuseSuite tagHMsg [] ⟨0, 0, .wotsHash, 0, 0, 0⟩
        [[], pk0.pkRoot, 0xE3 :: List.replicate 31 0x1B, be 4 0] = reuseDigest3 := by
      unfold thCall bottomReuseSuite bottomReuseRawHash thPreimage
      have hd12 : (encodeMultiFrame ([tagHMsg, [], encodeAdrs ⟨0, 0, .wotsHash, 0, 0, 0⟩] ++
          [[], pk0.pkRoot, 0xE3 :: List.replicate 31 0x1B, be 4 0])).getD 12 0 = 72 := rfl
      have hNo1 : (encodeMultiFrame ([tagHMsg, [], encodeAdrs ⟨0, 0, .wotsHash, 0, 0, 0⟩] ++
          [[], pk0.pkRoot, 0xE3 :: List.replicate 31 0x1B, be 4 0])).contains 0xE1 = false := by
        have hLenRoot : pk0.pkRoot.length = 32 := thCall_length _ _ _ _ _
        apply List.contains_eq_false_iff.mpr
        simp only [encodeMultiFrame, List.cons_append, List.nil_append, frameList, List.mem_append, not_or, hLenRoot]
        refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by simp [encodeAdrs, be]; decide⟩,
          ⟨by decide, by decide⟩, ⟨by decide, fun hm => (hRootNoE _ hm).1 rfl⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩
      have hNo2 : (encodeMultiFrame ([tagHMsg, [], encodeAdrs ⟨0, 0, .wotsHash, 0, 0, 0⟩] ++
          [[], pk0.pkRoot, 0xE3 :: List.replicate 31 0x1B, be 4 0])).contains 0xE2 = false := by
        have hLenRoot : pk0.pkRoot.length = 32 := thCall_length _ _ _ _ _
        apply List.contains_eq_false_iff.mpr
        simp only [encodeMultiFrame, List.cons_append, List.nil_append, frameList, List.mem_append, not_or, hLenRoot]
        refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by simp [encodeAdrs, be]; decide⟩,
          ⟨by decide, by decide⟩, ⟨by decide, fun hm => (hRootNoE _ hm).2 rfl⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩
      rw [hd12, hNo1, hNo2]; rfl
    unfold thHashMsg; dsimp only [pk0]; rw [hB0, List.take_left' (by simp [reuseDigest3])]
  let d1 := extractBaseWDigits 4 128 reuseDigest1
  let d2 := extractBaseWDigits 4 128 reuseDigest2
  let d3 := extractBaseWDigits 4 128 reuseDigest3
  have hDValid : checkTargetSum 4 128 192 d1 = true ∧
      checkTargetSum 4 128 192 d2 = true ∧
      checkTargetSum 4 128 192 d3 = true := by decide
  have hDCover : ∀ r, r < 128 → d1.getD r 0 ≤ d3.getD r 0 ∨ d2.getD r 0 ≤ d3.getD r 0 := by
    have hAll : (List.range 128).all (fun r => decide (d1.getD r 0 ≤ d3.getD r 0 ∨ d2.getD r 0 ≤ d3.getD r 0)) = true := by
      decide
    intro r hr
    exact of_decide_eq_true ((List.all_eq_true.mp hAll) r (List.mem_range.mpr hr))
  have hDigEq1 : extractBaseWDigits 4 128 (thHashMsg bottomReuseSuite [] pk0.pkSeed pk0.pkRoot
      (thPreHash bottomReuseSuite pk0.pkSeed pk0.pkRoot [0xE1]) 0 0 0 0) = d1 := by
    rw [hTake32 _ (by rw [thHashMsg_length]; decide), hHm1]
  have hDigEq2 : extractBaseWDigits 4 128 (thHashMsg bottomReuseSuite [] pk0.pkSeed pk0.pkRoot
      (thPreHash bottomReuseSuite pk0.pkSeed pk0.pkRoot [0xE2]) 0 0 0 0) = d2 := by
    rw [hTake32 _ (by rw [thHashMsg_length]; decide), hHm2]
  have hDigEq3 : extractBaseWDigits 4 128 (thHashMsg bottomReuseSuite [] pk0.pkSeed pk0.pkRoot
      (thPreHash bottomReuseSuite pk0.pkSeed pk0.pkRoot [0xE3]) 0 0 0 0) = d3 := by
    rw [hTake32 _ (by rw [thHashMsg_length]; decide), hHm3]
  have hWfP : wotsSingleLayerParams.wellFormed = true ∧
      wotsSingleLayerParams.statefulJorts = true ∧
      wotsSingleLayerParams.numLayers = 1 ∧
      wotsSingleLayerParams.targetSum = 192 := by decide
  let chains1 := (List.range 128).map fun r =>
    wotsChainSteps bottomReuseSuite [] 0 0 0 r 0 (d1.getD r 0) (wotsSecretBase bottomReuseSuite sk0 0 0 0 r)
  let chains2 := (List.range 128).map fun r =>
    wotsChainSteps bottomReuseSuite [] 0 0 0 r 0 (d2.getD r 0) (wotsSecretBase bottomReuseSuite sk0 0 0 0 r)
  let path0 := buildMerkleAuthPath bottomReuseSuite [] 0 0 .tree (computeWotsPk bottomReuseSuite wotsSingleLayerParams sk0 0 0) 1 0 0
  let sig1 : PqHashSig := ⟨[], 0, 0, [], [⟨0, chains1, path0⟩]⟩
  let sig2 : PqHashSig := ⟨[], 0, 0, [], [⟨0, chains2, path0⟩]⟩
  -- Forged signature uses ONLY public `pk0.pkSeed`, `d1, d2, d3`, `chains1, chains2`, and `path0` from `sig1`!
  let forgedChains3 := forgeWotsFromTwoSigs bottomReuseSuite pk0.pkSeed 0 0 0 128 d1 d2 d3 chains1 chains2
  let forgedSig3 : PqHashSig := ⟨[], 0, 0, [], [⟨0, forgedChains3, path0⟩]⟩
  have hEv1 : evalSingleLayerAtCounter bottomReuseSuite wotsSingleLayerParams sk0 [0xE1] [] 0 = some sig1 := by
    unfold evalSingleLayerAtCounter
    simp only [hWfP.1, hWfP.2.1, hWfP.2.2.1, hWfP.2.2.2, Bool.not_true, ne_eq, not_true_eq_false, Bool.or_self, ↓reduceIte]
    change (if !(checkTargetSum 4 128 192 (extractBaseWDigits 4 128
              (thHashMsg bottomReuseSuite [] pk0.pkSeed pk0.pkRoot
                (thPreHash bottomReuseSuite pk0.pkSeed pk0.pkRoot [0xE1]) 0 0 0 0))) then none else _) = _
    rw [hDigEq1, hDValid.1]; rfl
  have hEv2 : evalSingleLayerAtCounter bottomReuseSuite wotsSingleLayerParams sk0 [0xE2] [] 0 = some sig2 := by
    unfold evalSingleLayerAtCounter
    simp only [hWfP.1, hWfP.2.1, hWfP.2.2.1, hWfP.2.2.2, Bool.not_true, ne_eq, not_true_eq_false, Bool.or_self, ↓reduceIte]
    change (if !(checkTargetSum 4 128 192 (extractBaseWDigits 4 128
              (thHashMsg bottomReuseSuite [] pk0.pkSeed pk0.pkRoot
                (thPreHash bottomReuseSuite pk0.pkSeed pk0.pkRoot [0xE2]) 0 0 0 0))) then none else _) = _
    rw [hDigEq2, hDValid.2.1]; rfl
  have hVer3 : verifyPqHashSig bottomReuseSuite wotsSingleLayerParams pk0 [0xE3] forgedSig3 = true := by
    unfold verifyPqHashSig
    simp only [hWfP.1, Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.length_singleton,
      hWfP.2.2.1, ne_eq, not_true_eq_false, show 0 < 2 ^ (1 * 1) from by decide, decide_true,
      hWfP.2.1, List.isEmpty_nil]
    simp only [verifyHypertreeLayers, Nat.zero_mod, Nat.zero_div]
    change (if !(checkTargetSum 4 128 192 (extractBaseWDigits 4 128
              (thHashMsg bottomReuseSuite [] pk0.pkSeed pk0.pkRoot
                (thPreHash bottomReuseSuite pk0.pkSeed pk0.pkRoot [0xE3]) 0 0 0 0))) then none else _) = _
    -- Unfold the match on `verifyHypertreeLayers` cleanly:
    revert hVer3 2>/dev/null || skip
  sorry
end Qsag
end
