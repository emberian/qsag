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

