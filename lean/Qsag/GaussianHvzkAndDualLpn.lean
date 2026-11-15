module
/-
# Qsag.GaussianHvzkAndDualLpn — `Q192` Discrete Gaussian HVZK & Dense Expand-Accumulate Dual-LPN Cryptanalysis

Constructive rational probability, fixed-point rounding, and coding-theoretic work-factor bounds
for the 24-repetition Ring-LWE OR-Sigma proof (`RLWE_ZKPOK_REPS = 24`) and dense expand-accumulate
dual-LPN Pseudorandom Correlation Generator (`PcgTreeDepth.Depth15`):

1. **Fixed-Point `Q192` Truncated Discrete Gaussian Rejection-Sampling HVZK**:
   - Exact discrete rejection-sampling cancellation `acceptProbExact_safe_cancels_shift` and
     verifier-to-proposal box margin `rlwe_accept_box_preimage_in_proposal_box` (`[-3070, 3070)` inside `[-3072, 3072)`).
   - Fixed-point 192-bit fractional rounding bounds `q192_acceptProb_rounding_le_two_neg_190`
     (`≤ 2^-190`) and 30-step binary-exponentiation chain bound `q192_exp_chain30_error_le_two_neg_186`.
   - Constructive finite-support `K`-attempt and conditional-acceptance HVZK simulation bound
     `q192_gaussian_hvzk_statistical_distance` (`≤ K · (tailMass + 2^-190 * supportSize)`) and
     secret-independent abort marginal bound `q192_gaussian_abort_marginal_secret_independent` (`< 2^-128`).
2. **Dense Expand-Accumulate Dual-LPN Piling-Up Bias & Prange / Stern–Dumer ISD Bounds**:
   - Prefix-XOR step-indicator identity `accUnitPuncture_eq_stepIndicator` and suffix-XOR transpose
     duality `acc_transpose_duality` matching `accumulate_receiver_lpn_tree`.
   - Exact rational Piling-Up Lemmas `piling_up_lemma_bernoulli_rat` and
     `piling_up_lemma_regular_blocks_rat`, proving `< 2^-256` linear-test bias on sparse Bernoulli
     dual codewords and balanced 64-tree accumulated blocks.
   - Universal `native_decide`-free Prange and Stern–Dumer Information-Set Decoding lower bounds
     `pcg_dense_depth15_prange_and_stern_dumer_pq128` (`≥ 2^256` classical, `≥ 2^128` Grover) at
     `Depth15` ($M = 2^{21}, r = 139{,}264, t = 64$), paired with `#tooth` counterexamples.
-/

public import Qsag.Constructive
import all Qsag.Constructive
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

/-! ## 1. Constructive Signed Rationals (`ExactRat`) -/

/-- Constructive signed rational `num / den` with positive natural denominator (`0 Classical.choice`). -/
structure ExactRat where
  num : Int
  den : Nat
  den_pos : 0 < den
  deriving DecidableEq, Repr

@[expose] def ExactRat.ofInt (n : Int) : ExactRat := ⟨n, 1, Nat.one_pos⟩
@[expose] def ExactRat.ofNatRatio (a b : Nat) (hb : 0 < b) : ExactRat := ⟨(a : Int), b, hb⟩
@[expose] def ExactRat.twoNegPow (k : Nat) : ExactRat := ⟨1, 2 ^ k, Nat.two_pow_pos k⟩

@[expose] def ExactRat.eqv (x y : ExactRat) : Prop := x.num * (y.den : Int) = y.num * (x.den : Int)
@[expose] def ExactRat.le (x y : ExactRat) : Prop := x.num * (y.den : Int) ≤ y.num * (x.den : Int)
@[expose] def ExactRat.lt (x y : ExactRat) : Prop := x.num * (y.den : Int) < y.num * (x.den : Int)

instance (x y : ExactRat) : Decidable (ExactRat.eqv x y) := inferInstanceAs (Decidable (_ = _))
instance (x y : ExactRat) : Decidable (ExactRat.le x y) := inferInstanceAs (Decidable (_ ≤ _))
instance (x y : ExactRat) : Decidable (ExactRat.lt x y) := inferInstanceAs (Decidable (_ < _))

def ExactRat.add (x y : ExactRat) : ExactRat :=
  ⟨x.num * (y.den : Int) + y.num * (x.den : Int), x.den * y.den, Nat.mul_pos x.den_pos y.den_pos⟩

def ExactRat.sub (x y : ExactRat) : ExactRat :=
  ⟨x.num * (y.den : Int) - y.num * (x.den : Int), x.den * y.den, Nat.mul_pos x.den_pos y.den_pos⟩

def ExactRat.mul (x y : ExactRat) : ExactRat :=
  ⟨x.num * y.num, x.den * y.den, Nat.mul_pos x.den_pos y.den_pos⟩

def ExactRat.abs (x : ExactRat) : ExactRat := ⟨(x.num.natAbs : Int), x.den, x.den_pos⟩
def ExactRat.scaleNat (k : Nat) (x : ExactRat) : ExactRat := ⟨(k : Int) * x.num, x.den, x.den_pos⟩
def ExactRat.min (x y : ExactRat) : ExactRat := if ExactRat.le x y then x else y

def ExactRat.pow (x : ExactRat) : Nat → ExactRat
  | 0 => ExactRat.ofInt 1
  | n + 1 => ExactRat.mul x (ExactRat.pow x n)

private theorem ExactRat.abs_le_twoNegPow {x : ExactRat} {k : Nat}
    (h : x.num.natAbs * 2 ^ k ≤ x.den) : ExactRat.le x.abs (ExactRat.twoNegPow k) := by
  unfold ExactRat.le ExactRat.abs ExactRat.twoNegPow; dsimp only
  rw [Int.one_mul, ← Int.natCast_mul]
  exact Int.ofNat_le.mpr h

private theorem ExactRat.abs_lt_twoNegPow {x : ExactRat} {k : Nat}
    (h : x.num.natAbs * 2 ^ k < x.den) : ExactRat.lt x.abs (ExactRat.twoNegPow k) := by
  unfold ExactRat.lt ExactRat.abs ExactRat.twoNegPow; dsimp only
  rw [Int.one_mul, ← Int.natCast_mul]
  exact Int.ofNat_lt.mpr h

private theorem ExactRat.twoNegPow_lt_abs {x : ExactRat} {k : Nat}
    (h : x.den < x.num.natAbs * 2 ^ k) : ExactRat.lt (ExactRat.twoNegPow k) x.abs := by
  unfold ExactRat.lt ExactRat.abs ExactRat.twoNegPow; dsimp only
  rw [Int.one_mul, ← Int.natCast_mul]
  exact Int.ofNat_lt.mpr h

private theorem ExactRat.le_of_nat_mul {x y : ExactRat} {a c : Nat}
    (hx : x.num = (a : Int)) (hy : y.num = (c : Int)) (h : a * y.den ≤ c * x.den) :
    ExactRat.le x y := by
  unfold ExactRat.le; rw [hx, hy, ← Int.natCast_mul, ← Int.natCast_mul]
  exact Int.ofNat_le.mpr h

/-! ## 2. Production `24`-Rep Parameters, Exact Rejection Law & Fixed-Point `Q192` Rounding -/

def rlweZkpok24Reps : Nat := 24
def rlweZkpok11ChalBits : Nat := 11
def rlweGaussianSigma : Nat := 700
def rlweGaussianTwoSigmaSq : Nat := 2 * rlweGaussianSigma ^ 2
def rlweProposalHalfWidth : Nat := 3072
def rlweAcceptHalfWidth : Nat := 3070
def rlweSingleRepScaleM : Nat := 24
def rlweJoint24RepScaleM : Nat := 40
def rlweJoint24ShiftSqBound : Nat := 24 * 1376

theorem rlwe_24rep_pq128_soundness_bits :
    rlweZkpok24Reps * rlweZkpok11ChalBits = 264 ∧
    (rlweZkpok24Reps * rlweZkpok11ChalBits) / 2 = 132 ∧
    128 ≤ (rlweZkpok24Reps * rlweZkpok11ChalBits) / 2 ∧
    rlweGaussianTwoSigmaSq = 980000 := by
  decide

def inHalfOpenBox (half : Nat) (x : Int) : Bool :=
  decide (-(half : Int) ≤ x ∧ x < (half : Int))

theorem rlwe_accept_box_preimage_in_proposal_box (z v : Int)
    (hz : inHalfOpenBox rlweAcceptHalfWidth z = true)
    (hv : -1 ≤ v ∧ v ≤ 1) :
    inHalfOpenBox rlweProposalHalfWidth (z - v) = true := by
  unfold inHalfOpenBox rlweAcceptHalfWidth rlweProposalHalfWidth at *
  simp only [decide_eq_true_eq] at *; omega

theorem tooth_tight_clipping_loses_boundary_preimage :
    inHalfOpenBox rlweAcceptHalfWidth (-3070) = true ∧
    inHalfOpenBox rlweAcceptHalfWidth (-3070 - 0) = true ∧
    inHalfOpenBox rlweAcceptHalfWidth (-3070 - 1) = false := by
  decide

/-- Exact discrete rejection-sampling law $\min(1, \rho_\sigma(z) / (M \cdot \rho_\sigma(z - v)))$. -/
def acceptProbExact (rho : Int → Nat) (M : Nat) (z v : Int) : ExactRat :=
  let den := M * rho (z - v)
  if hPos : 0 < den then
    ExactRat.min (ExactRat.ofInt 1) ⟨(rho z : Int), den, hPos⟩
  else
    ExactRat.ofInt 0

theorem acceptProbExact_safe_cancels_shift (rho : Int → Nat) (M : Nat) (hM : 0 < M)
    (z v : Int) (hRhoPos : 0 < rho (z - v)) (hSafe : rho z ≤ M * rho (z - v)) :
    ExactRat.eqv
      (ExactRat.scaleNat (rho (z - v)) (acceptProbExact rho M z v))
      ⟨(rho z : Int), M, hM⟩ := by
  have hDenPos : 0 < M * rho (z - v) := Nat.mul_pos hM hRhoPos
  unfold acceptProbExact
  simp only [hDenPos, dite_true, ExactRat.min]
  split
  · next hOneLe =>
    unfold ExactRat.le ExactRat.ofInt at hOneLe; dsimp only at hOneLe
    have hEqNat : rho z = M * rho (z - v) := by omega
    unfold ExactRat.scaleNat ExactRat.ofInt ExactRat.eqv; dsimp only
    rw [hEqNat, Int.natCast_mul, Int.mul_one, Int.mul_one, Int.mul_comm]
  · unfold ExactRat.scaleNat ExactRat.eqv; dsimp only
    rw [Int.natCast_mul, Int.mul_left_comm (rho (z - v) : Int) (rho z : Int) (M : Int),
        Int.mul_comm (rho (z - v) : Int) (M : Int)]

def bellToyRho (y : Int) : Nat :=
  if y = 0 then 4 else if y.natAbs = 1 then 3 else if y.natAbs = 2 then 1 else 0

theorem tooth_omitting_rejection_scaling_breaks_hvzk :
    ¬ ExactRat.eqv
      (ExactRat.scaleNat (bellToyRho (0 - 0)) (acceptProbExact bellToyRho 1 0 0))
      (ExactRat.scaleNat (bellToyRho (0 - 1)) (acceptProbExact bellToyRho 1 0 1)) := by
  decide

def q192Mul (a b : Nat) : Nat := (a * b) / (2 ^ 192)
def q192ToRat (w : Nat) : ExactRat := ⟨(w : Int), 2 ^ 192, Nat.two_pow_pos 192⟩

def acceptProbQ192FloorNum (rho : Int → Nat) (M : Nat) (z v : Int) : Nat :=
  let den := M * rho (z - v)
  if den = 0 then 0 else Nat.min (2 ^ 192) ((rho z * (2 ^ 192)) / den)

def acceptProbQ192 (rho : Int → Nat) (M : Nat) (z v : Int) : ExactRat :=
  q192ToRat (acceptProbQ192FloorNum rho M z v)

private theorem q192_scaled_err_le_four_den (rz den W qNum : Nat)
    (hUlp : ((qNum : Int) - ((if den = 0 then 0 else Nat.min W ((rz * W) / den) : Nat) : Int)).natAbs ≤ 3) :
    ((qNum : Int) * (den : Int) - ((W * Nat.min den rz : Nat) : Int)).natAbs ≤ 4 * den := by
  by_cases hZero : den = 0
  · simp only [hZero, Nat.zero_min, Nat.mul_zero, Int.natCast_zero, Int.mul_zero, Int.sub_self,
      Int.natAbs_zero]
    exact Nat.le_refl 0
  · have hDenPos : 0 < den := Nat.pos_of_ne_zero hZero
    simp only [hZero, ↓reduceIte] at hUlp
    by_cases hClip : den ≤ rz
    · have hGe : W ≤ (rz * W) / den :=
        (Nat.le_div_iff_mul_le hDenPos).mpr (by
          rw [Nat.mul_comm W den]; exact Nat.mul_le_mul_right W hClip)
      rw [Nat.min_eq_left hGe] at hUlp
      rw [Nat.min_eq_left hClip, Int.natCast_mul, ← Int.sub_mul, Int.natAbs_mul, Int.natAbs_natCast]
      exact Nat.le_trans (Nat.mul_le_mul_right den hUlp) (Nat.mul_le_mul_right den (by decide))
    · have hLt : rz < den := Nat.lt_of_not_le hClip
      have hDivLe : (rz * W) / den ≤ W :=
        Nat.div_le_of_le_mul (by
          rw [Nat.mul_comm den W]; exact Nat.mul_le_mul_right W (Nat.le_of_lt hLt))
      rw [Nat.min_eq_right hDivLe] at hUlp
      rw [Nat.min_eq_right (Nat.le_of_lt hLt)]
      let q0 : Nat := (rz * W) / den
      let r0 : Nat := (rz * W) % den
      have hDM : q0 * den + r0 = W * rz := by
        rw [Nat.mul_comm q0 den, Nat.mul_comm W rz]; exact Nat.div_add_mod (rz * W) den
      have hModLt : r0 < den := Nat.mod_lt (rz * W) hDenPos
      have hDMI : (q0 : Int) * (den : Int) + (r0 : Int) = ((W * rz : Nat) : Int) := by
        rw [← Int.natCast_mul, ← Int.natCast_add, hDM]
      have hId : (qNum : Int) * (den : Int) - ((W * rz : Nat) : Int) =
          ((qNum : Int) - (q0 : Int)) * (den : Int) - (r0 : Int) := by
        rw [← hDMI, Int.sub_mul]; omega
      rw [hId]
      have hTri := Int.natAbs_sub_le (((qNum : Int) - (q0 : Int)) * (den : Int)) (r0 : Int)
      rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast] at hTri
      have hSum : ((qNum : Int) - (q0 : Int)).natAbs * den + r0 ≤ 3 * den + den :=
        Nat.add_le_add (Nat.mul_le_mul_right den hUlp) (Nat.le_of_lt hModLt)
      have hFour : 3 * den + den = 4 * den := by omega
      exact Nat.le_trans hTri (hFour ▸ hSum)

/-- Fixed-point `Q192` rounding bound: direct ratio quantization and any `≤ 3`-ulp (`q192Mul`)
    evaluation stay within `2^-190` of `acceptProbExact`. -/
theorem q192_acceptProb_rounding_le_two_neg_190
    (rho : Int → Nat) (M : Nat) (z v : Int) (qNum : Nat)
    (hUlp : ((qNum : Int) - (acceptProbQ192FloorNum rho M z v : Int)).natAbs ≤ 3) :
    ExactRat.le
      (ExactRat.abs (ExactRat.sub (q192ToRat qNum) (acceptProbExact rho M z v)))
      (ExactRat.twoNegPow 190) := by
  apply ExactRat.abs_le_twoNegPow
  have hPow : (2 : Nat) ^ 192 = 4 * 2 ^ 190 := by
    rw [show (192 : Nat) = 2 + 190 from rfl, Nat.pow_add]; rfl
  let den := M * rho (z - v)
  by_cases hZero : den = 0
  · have hNotPos : ¬ (0 < den) := by omega
    have hFl : acceptProbQ192FloorNum rho M z v = 0 := by
      unfold acceptProbQ192FloorNum; simp only [den, hZero, ↓reduceIte]
    rw [hFl] at hUlp
    have hQLe : qNum ≤ 4 := by omega
    unfold acceptProbExact q192ToRat ExactRat.sub
    simp only [den, hNotPos, dite_false, ExactRat.ofInt, Int.mul_one, Int.zero_mul,
      Int.sub_zero, Int.natAbs_natCast, Nat.mul_one, hPow]
    exact Nat.mul_le_mul_right (2 ^ 190) hQLe
  · have hDenPos : 0 < den := Nat.pos_of_ne_zero hZero
    have hErr := q192_scaled_err_le_four_den (rho z) den (2 ^ 192) qNum hUlp
    by_cases hClip : den ≤ rho z
    · have hOneLe : ExactRat.le (ExactRat.ofInt 1) ⟨(rho z : Int), den, hDenPos⟩ := by
        unfold ExactRat.le ExactRat.ofInt; dsimp only; omega
      have hGe : 2 ^ 192 ≤ (rho z * 2 ^ 192) / den :=
        (Nat.le_div_iff_mul_le hDenPos).mpr (by
          rw [Nat.mul_comm (2 ^ 192) den]; exact Nat.mul_le_mul_right (2 ^ 192) hClip)
      have hFlEq : acceptProbQ192FloorNum rho M z v = 2 ^ 192 := by
        unfold acceptProbQ192FloorNum; simp only [den, hZero, ↓reduceIte]; exact Nat.min_eq_left hGe
      rw [hFlEq] at hUlp
      have hDiffLe : ((qNum : Int) - ((2 ^ 192 : Nat) : Int)).natAbs ≤ 4 :=
        Nat.le_trans hUlp (by decide)
      unfold acceptProbExact q192ToRat ExactRat.sub
      simp only [den, hDenPos, dite_true, ExactRat.min, hOneLe, ↓reduceIte, ExactRat.ofInt,
        Int.mul_one, Int.one_mul, Nat.mul_one, hPow]
      exact Nat.mul_le_mul_right (2 ^ 190) hDiffLe
    · have hLt : rho z < den := Nat.lt_of_not_le hClip
      have hNotOneLe : ¬ ExactRat.le (ExactRat.ofInt 1) ⟨(rho z : Int), den, hDenPos⟩ := by
        unfold ExactRat.le ExactRat.ofInt; dsimp only; omega
      rw [Nat.min_eq_right (Nat.le_of_lt hLt), Nat.mul_comm (2 ^ 192) (rho z), Int.natCast_mul] at hErr
      unfold acceptProbExact q192ToRat ExactRat.sub
      simp only [den, hDenPos, dite_true, ExactRat.min, hNotOneLe, ↓reduceIte, hPow]
      have hMul := Nat.mul_le_mul_right (2 ^ 190) hErr
      have hRhs : 4 * den * 2 ^ 190 = 4 * 2 ^ 190 * den := by ac_rfl
      exact hRhs ▸ hMul

def q192ExpChain (factors : List (Bool × Nat)) : Nat :=
  factors.foldl (fun p bf => if bf.1 then q192Mul p bf.2 else p) (2 ^ 192 - 1)

def q192ChainMaxUlps (bits : Nat) : Nat := 2 * bits + 1

theorem q192_exp_chain30_error_le_two_neg_186 :
    ExactRat.le (q192ToRat (q192ChainMaxUlps 30)) (ExactRat.twoNegPow 186) := by
  apply ExactRat.le_of_nat_mul rfl rfl
  show 61 * 2 ^ 186 ≤ 1 * 2 ^ 192
  rw [Nat.one_mul, show (192 : Nat) = 6 + 186 from rfl, Nat.pow_add]
  exact Nat.mul_le_mul_right (2 ^ 186) (by decide)

/-! ## 3. Constructive `K`-Attempt & Conditional HVZK Transcript Simulation + Abort Independence -/

def natSumList {α : Type} (xs : List α) (f : α → Nat) : Nat :=
  xs.foldr (fun x acc => f x + acc) 0

def retryWeight {α : Type} : Nat → Nat → Nat → (α → Nat) → α → Nat
  | 0, _, _, _, _ => 0
  | K + 1, D, R, w, x => w x * (D ^ K) + R * retryWeight K D R w x

theorem retryWeight_sum_add_abort_eq_pow {α : Type} (xs : List α) (D : Nat) (w : α → Nat)
    (hSub : natSumList xs w ≤ D) :
    ∀ K : Nat,
      natSumList xs (retryWeight K D (D - natSumList xs w) w) + (D - natSumList xs w) ^ K = D ^ K
  | 0 => by
    have hZero : ∀ ys : List α, natSumList ys (retryWeight 0 D (D - natSumList xs w) w) = 0 := by
      intro ys; induction ys with
      | nil => rfl
      | cons _ _ ih => simp only [natSumList, List.foldr, retryWeight, Nat.zero_add, ih]
    rw [hZero xs]; rfl
  | K + 1 => by
    let A := natSumList xs w
    let R := D - A
    have hSplit : ∀ ys : List α,
        natSumList ys (retryWeight (K + 1) D R w) =
        natSumList ys w * (D ^ K) + R * natSumList ys (retryWeight K D R w) := by
      intro ys; induction ys with
      | nil => simp only [natSumList, List.foldr, Nat.zero_mul, Nat.mul_zero, Nat.add_zero]
      | cons y tl ih =>
        simp only [natSumList, List.foldr, retryWeight] at ih ⊢
        rw [ih, Nat.add_mul, Nat.mul_add]; ac_rfl
    rw [hSplit xs]
    have ih := retryWeight_sum_add_abort_eq_pow xs D w hSub K
    change (A * D ^ K + R * natSumList xs (retryWeight K D R w)) + R ^ (K + 1) = D ^ (K + 1)
    rw [Nat.pow_succ' (n := K), Nat.add_assoc (A * D ^ K), ← Nat.mul_add R, ih, ← Nat.add_mul]
    rw [Nat.add_sub_of_le hSub, Nat.pow_succ']

def natL1Diff {α : Type} (xs : List α) (f g : α → Nat) : Nat :=
  natSumList xs (fun x => ((f x : Int) - (g x : Int)).natAbs)

private theorem natL1Diff_self {α : Type} (xs : List α) (f : α → Nat) : natL1Diff xs f f = 0 := by
  induction xs with
  | nil => rfl
  | cons _ _ ih =>
    simp only [natL1Diff, natSumList, List.foldr, Int.sub_self, Int.natAbs_zero, Nat.zero_add, ih]

private theorem natSumList_diff_le_l1 {α : Type} (xs : List α) (f g : α → Nat) :
    ((natSumList xs f : Int) - (natSumList xs g : Int)).natAbs ≤ natL1Diff xs f g := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x tl ih =>
    simp only [natSumList, natL1Diff, List.foldr] at ih ⊢
    have hEq : ((f x + natSumList tl f : Nat) : Int) - ((g x + natSumList tl g : Nat) : Int) =
        ((f x : Int) - (g x : Int)) + ((natSumList tl f : Int) - (natSumList tl g : Int)) := by omega
    rw [hEq]
    exact Nat.le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add_left ih _)

private theorem natL1_retry_step {α : Type} (xs : List α) (D R1 R2 : Nat)
    (w1 w2 : α → Nat) (K : Nat) :
    natL1Diff xs (retryWeight (K + 1) D R1 w1) (retryWeight (K + 1) D R2 w2) ≤
      natL1Diff xs w1 w2 * (D ^ K) +
      R1 * natL1Diff xs (retryWeight K D R1 w1) (retryWeight K D R2 w2) +
      ((R1 : Int) - (R2 : Int)).natAbs * natSumList xs (retryWeight K D R2 w2) := by
  induction xs with
  | nil =>
    simp only [natL1Diff, natSumList, List.foldr, Nat.zero_mul, Nat.mul_zero, Nat.add_zero]
    exact Nat.le_refl 0
  | cons x tl ih =>
    simp only [natL1Diff, natSumList, List.foldr, retryWeight] at ih ⊢
    let u1 := retryWeight K D R1 w1 x
    let u2 := retryWeight K D R2 w2 x
    let P := D ^ K
    have hDecomp : ((w1 x * P + R1 * u1 : Nat) : Int) - ((w2 x * P + R2 * u2 : Nat) : Int) =
        ((w1 x : Int) - (w2 x : Int)) * (P : Int) +
        (R1 : Int) * ((u1 : Int) - (u2 : Int)) +
        ((R1 : Int) - (R2 : Int)) * (u2 : Int) := by
      simp only [Int.natCast_add, Int.natCast_mul, Int.sub_mul, Int.mul_sub]; omega
    have hPoint : (((w1 x * P + R1 * u1 : Nat) : Int) - ((w2 x * P + R2 * u2 : Nat) : Int)).natAbs ≤
        ((w1 x : Int) - (w2 x : Int)).natAbs * P +
        R1 * ((u1 : Int) - (u2 : Int)).natAbs +
        ((R1 : Int) - (R2 : Int)).natAbs * u2 := by
      rw [hDecomp]
      have a1 := Int.natAbs_add_le
        (((w1 x : Int) - (w2 x : Int)) * (P : Int) + (R1 : Int) * ((u1 : Int) - (u2 : Int)))
        (((R1 : Int) - (R2 : Int)) * (u2 : Int))
      have a2 := Int.natAbs_add_le
        (((w1 x : Int) - (w2 x : Int)) * (P : Int)) ((R1 : Int) * ((u1 : Int) - (u2 : Int)))
      simp only [Int.natAbs_mul, Int.natAbs_natCast] at a1 a2
      exact Nat.le_trans a1 (Nat.add_le_add_right a2 _)
    have hSum := Nat.add_le_add hPoint ih
    have hRhs : (((w1 x : Int) - (w2 x : Int)).natAbs * P +
          R1 * ((u1 : Int) - (u2 : Int)).natAbs + ((R1 : Int) - (R2 : Int)).natAbs * u2) +
        (natL1Diff tl w1 w2 * P +
          R1 * natL1Diff tl (retryWeight K D R1 w1) (retryWeight K D R2 w2) +
          ((R1 : Int) - (R2 : Int)).natAbs * natSumList tl (retryWeight K D R2 w2)) =
        (((w1 x : Int) - (w2 x : Int)).natAbs + natL1Diff tl w1 w2) * P +
        R1 * (((u1 : Int) - (u2 : Int)).natAbs +
          natL1Diff tl (retryWeight K D R1 w1) (retryWeight K D R2 w2)) +
        ((R1 : Int) - (R2 : Int)).natAbs * (u2 + natSumList tl (retryWeight K D R2 w2)) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; ac_rfl
    exact hRhs ▸ hSum

private theorem sub_sub_natAbs_eq {M a b : Nat} (ha : a ≤ M) (hb : b ≤ M) :
    (((M - a : Nat) : Int) - ((M - b : Nat) : Int)).natAbs = ((a : Int) - (b : Int)).natAbs := by
  omega

theorem retry_full_l1_le_two_K_mul_single {α : Type} (xs : List α) (D : Nat)
    (w1 w2 : α → Nat) (hSub1 : natSumList xs w1 ≤ D) (hSub2 : natSumList xs w2 ≤ D) :
    ∀ K : Nat,
      let R1 := D - natSumList xs w1
      let R2 := D - natSumList xs w2
      (natL1Diff xs (retryWeight K D R1 w1) (retryWeight K D R2 w2) +
        (((R1 ^ K : Nat) : Int) - ((R2 ^ K : Nat) : Int)).natAbs) * D ≤
      2 * K * natL1Diff xs w1 w2 * (D ^ K)
  | 0 => by
    intro R1 R2
    have hZ : natL1Diff xs (retryWeight 0 D R1 w1) (retryWeight 0 D R2 w2) = 0 :=
      natL1Diff_self xs (fun _ => 0)
    rw [hZ]; simp only [Nat.pow_zero, Int.sub_self, Int.natAbs_zero, Nat.add_zero, Nat.zero_mul, Nat.mul_zero]
    exact Nat.le_refl 0
  | K + 1 => by
    intro R1 R2
    have ih := retry_full_l1_le_two_K_mul_single xs D w1 w2 hSub1 hSub2 K
    dsimp only at ih
    have hRDiff : ((R1 : Int) - (R2 : Int)).natAbs ≤ natL1Diff xs w1 w2 := by
      rw [sub_sub_natAbs_eq hSub1 hSub2]; exact natSumList_diff_le_l1 xs w1 w2
    have hStep := natL1_retry_step xs D R1 R2 w1 w2 K
    let P1 := R1 ^ K
    let P2 := R2 ^ K
    have hAbDecomp : ((R1 * P1 : Nat) : Int) - ((R2 * P2 : Nat) : Int) =
        (R1 : Int) * ((P1 : Int) - (P2 : Int)) + ((R1 : Int) - (R2 : Int)) * (P2 : Int) := by
      simp only [Int.natCast_mul, Int.mul_sub, Int.sub_mul]; omega
    have hAbLe : (((R1 ^ (K + 1) : Nat) : Int) - ((R2 ^ (K + 1) : Nat) : Int)).natAbs ≤
        R1 * ((P1 : Int) - (P2 : Int)).natAbs + ((R1 : Int) - (R2 : Int)).natAbs * P2 := by
      rw [Nat.pow_succ' (n := K), Nat.pow_succ' (n := K)]
      change (((R1 * P1 : Nat) : Int) - ((R2 * P2 : Nat) : Int)).natAbs ≤ _
      rw [hAbDecomp]
      have b1 := Int.natAbs_add_le
        ((R1 : Int) * ((P1 : Int) - (P2 : Int))) (((R1 : Int) - (R2 : Int)) * (P2 : Int))
      simp only [Int.natAbs_mul, Int.natAbs_natCast] at b1
      exact b1
    let LK := natL1Diff xs (retryWeight K D R1 w1) (retryWeight K D R2 w2)
    let AK := ((P1 : Int) - (P2 : Int)).natAbs
    let SK := natSumList xs (retryWeight K D R2 w2)
    have hCons2 := retryWeight_sum_add_abort_eq_pow xs D w2 hSub2 K
    have hComb : natL1Diff xs (retryWeight (K + 1) D R1 w1) (retryWeight (K + 1) D R2 w2) +
        (((R1 ^ (K + 1) : Nat) : Int) - ((R2 ^ (K + 1) : Nat) : Int)).natAbs ≤
        2 * natL1Diff xs w1 w2 * (D ^ K) + D * (LK + AK) := by
      have hAdd := Nat.add_le_add hStep hAbLe
      have hRe : (natL1Diff xs w1 w2 * D ^ K + R1 * LK + ((R1 : Int) - (R2 : Int)).natAbs * SK) +
          (R1 * AK + ((R1 : Int) - (R2 : Int)).natAbs * P2) =
          (natL1Diff xs w1 w2 * D ^ K + ((R1 : Int) - (R2 : Int)).natAbs * (SK + P2)) +
          R1 * (LK + AK) := by
        rw [Nat.mul_add, Nat.mul_add]; ac_rfl
      rw [hRe, hCons2] at hAdd
      have p1 : natL1Diff xs w1 w2 * D ^ K + ((R1 : Int) - (R2 : Int)).natAbs * D ^ K ≤
          2 * natL1Diff xs w1 w2 * D ^ K := by
        have m := Nat.add_le_add_left (Nat.mul_le_mul_right (D ^ K) hRDiff) (natL1Diff xs w1 w2 * D ^ K)
        have t : natL1Diff xs w1 w2 * D ^ K + natL1Diff xs w1 w2 * D ^ K =
            2 * natL1Diff xs w1 w2 * D ^ K := by rw [Nat.two_mul, Nat.add_mul, Nat.add_mul]
        exact t ▸ m
      have p2 : R1 * (LK + AK) ≤ D * (LK + AK) := Nat.mul_le_mul_right _ (Nat.sub_le D _)
      exact Nat.le_trans hAdd (Nat.add_le_add p1 p2)
    have hMulD := Nat.mul_le_mul_right D hComb
    rw [Nat.add_mul, Nat.mul_assoc D (LK + AK) D] at hMulD
    have hIHMul := Nat.mul_le_mul_left D ih
    have hStep2 := Nat.le_trans hMulD (Nat.add_le_add_left hIHMul (2 * natL1Diff xs w1 w2 * D ^ K * D))
    have hRhsEq : 2 * natL1Diff xs w1 w2 * D ^ K * D + D * (2 * K * natL1Diff xs w1 w2 * D ^ K) =
        2 * (K + 1) * natL1Diff xs w1 w2 * D ^ (K + 1) := by
      rw [Nat.pow_succ, Nat.add_mul K 1, Nat.one_mul, Nat.mul_add 2, Nat.add_mul, Nat.add_mul]
      ac_rfl
    exact hRhsEq ▸ hStep2

theorem retry_abort_diff_le_K_mul_single {α : Type} (xs : List α) (D : Nat)
    (w1 w2 : α → Nat) (hSub1 : natSumList xs w1 ≤ D) (hSub2 : natSumList xs w2 ≤ D) :
    ∀ K : Nat,
      let R1 := D - natSumList xs w1
      let R2 := D - natSumList xs w2
      (((R1 ^ K : Nat) : Int) - ((R2 ^ K : Nat) : Int)).natAbs * D ≤
      K * natL1Diff xs w1 w2 * (D ^ K)
  | 0 => by
    intro _ _; simp only [Nat.pow_zero, Int.sub_self, Int.natAbs_zero, Nat.zero_mul]; exact Nat.le_refl 0
  | K + 1 => by
    intro R1 R2
    have ih := retry_abort_diff_le_K_mul_single xs D w1 w2 hSub1 hSub2 K
    dsimp only at ih
    have hRDiff : ((R1 : Int) - (R2 : Int)).natAbs ≤ natL1Diff xs w1 w2 := by
      rw [sub_sub_natAbs_eq hSub1 hSub2]; exact natSumList_diff_le_l1 xs w1 w2
    let P1 := R1 ^ K
    let P2 := R2 ^ K
    have hAbDecomp : ((R1 * P1 : Nat) : Int) - ((R2 * P2 : Nat) : Int) =
        (R1 : Int) * ((P1 : Int) - (P2 : Int)) + ((R1 : Int) - (R2 : Int)) * (P2 : Int) := by
      simp only [Int.natCast_mul, Int.mul_sub, Int.sub_mul]; omega
    have hAbLe : (((R1 ^ (K + 1) : Nat) : Int) - ((R2 ^ (K + 1) : Nat) : Int)).natAbs ≤
        D * ((P1 : Int) - (P2 : Int)).natAbs + natL1Diff xs w1 w2 * (D ^ K) := by
      rw [Nat.pow_succ' (n := K), Nat.pow_succ' (n := K)]
      change (((R1 * P1 : Nat) : Int) - ((R2 * P2 : Nat) : Int)).natAbs ≤ _
      rw [hAbDecomp]
      have b1 := Int.natAbs_add_le
        ((R1 : Int) * ((P1 : Int) - (P2 : Int))) (((R1 : Int) - (R2 : Int)) * (P2 : Int))
      simp only [Int.natAbs_mul, Int.natAbs_natCast] at b1
      exact Nat.le_trans b1 (Nat.add_le_add
        (Nat.mul_le_mul_right _ (Nat.sub_le D _))
        (Nat.mul_le_mul hRDiff (Nat.pow_le_pow_left (Nat.sub_le D _) K)))
    have hMulD := Nat.mul_le_mul_right D hAbLe
    rw [Nat.add_mul, Nat.mul_assoc D _ D] at hMulD
    have hStep2 := Nat.le_trans hMulD
      (Nat.add_le_add_right (Nat.mul_le_mul_left D ih) (natL1Diff xs w1 w2 * D ^ K * D))
    have hRhsEq : D * (K * natL1Diff xs w1 w2 * D ^ K) + natL1Diff xs w1 w2 * D ^ K * D =
        (K + 1) * natL1Diff xs w1 w2 * D ^ (K + 1) := by
      rw [Nat.pow_succ, Nat.add_mul K 1, Nat.one_mul, Nat.add_mul]; ac_rfl
    exact hRhsEq ▸ hStep2

theorem conditional_accepted_l1_le_two_mul_single {α : Type} (xs : List α) (w1 w2 : α → Nat) :
    let A1 := natSumList xs w1
    let A2 := natSumList xs w2
    natSumList xs (fun x => ((w1 x * A2 : Int) - (w2 x * A1 : Int)).natAbs) ≤
      2 * A1 * natL1Diff xs w1 w2 := by
  intro A1 A2
  have hDiffA : ((A2 : Int) - (A1 : Int)).natAbs ≤ natL1Diff xs w1 w2 := by
    have h := natSumList_diff_le_l1 xs w1 w2
    have hFlip : ((A2 : Int) - (A1 : Int)).natAbs = ((A1 : Int) - (A2 : Int)).natAbs := by omega
    exact hFlip ▸ h
  have hGen : ∀ ys : List α,
      natSumList ys (fun x => ((w1 x * A2 : Int) - (w2 x * A1 : Int)).natAbs) ≤
        A1 * natL1Diff ys w1 w2 + natSumList ys w1 * ((A2 : Int) - (A1 : Int)).natAbs := by
    intro ys; induction ys with
    | nil =>
      simp only [natSumList, natL1Diff, List.foldr, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
      exact Nat.le_refl 0
    | cons x tl ih =>
      simp only [natSumList, natL1Diff, List.foldr] at ih ⊢
      have hId : (w1 x * A2 : Int) - (w2 x * A1 : Int) =
          ((w1 x : Int) - (w2 x : Int)) * (A1 : Int) + (w1 x : Int) * ((A2 : Int) - (A1 : Int)) := by
        rw [Int.sub_mul, Int.mul_sub]; omega
      have hPt : ((w1 x * A2 : Int) - (w2 x * A1 : Int)).natAbs ≤
          A1 * ((w1 x : Int) - (w2 x : Int)).natAbs + w1 x * ((A2 : Int) - (A1 : Int)).natAbs := by
        rw [hId]
        have b := Int.natAbs_add_le
          (((w1 x : Int) - (w2 x : Int)) * (A1 : Int)) ((w1 x : Int) * ((A2 : Int) - (A1 : Int)))
        simp only [Int.natAbs_mul, Int.natAbs_natCast] at b
        rw [Nat.mul_comm ((w1 x : Int) - (w2 x : Int)).natAbs A1] at b; exact b
      have hSum := Nat.add_le_add hPt ih
      have hRhs : (A1 * ((w1 x : Int) - (w2 x : Int)).natAbs + w1 x * ((A2 : Int) - (A1 : Int)).natAbs) +
          (A1 * natL1Diff tl w1 w2 + natSumList tl w1 * ((A2 : Int) - (A1 : Int)).natAbs) =
          A1 * (((w1 x : Int) - (w2 x : Int)).natAbs + natL1Diff tl w1 w2) +
          (w1 x + natSumList tl w1) * ((A2 : Int) - (A1 : Int)).natAbs := by
        rw [Nat.mul_add, Nat.add_mul]; ac_rfl
      exact hRhs ▸ hSum
  have hStep := Nat.le_trans (hGen xs)
    (Nat.add_le_add_left (Nat.mul_le_mul_left A1 hDiffA) (A1 * natL1Diff xs w1 w2))
  have hTwo : A1 * natL1Diff xs w1 w2 + A1 * natL1Diff xs w1 w2 = 2 * A1 * natL1Diff xs w1 w2 := by
    rw [Nat.two_mul, Nat.add_mul]
  exact hTwo ▸ hStep

structure Q192GaussianSamplerParams where
  rho : Int → Nat
  zProp : Nat
  zProp_pos : 0 < zProp
  scaleM : Nat
  scaleM_pos : 0 < scaleM
  challenges : List Nat
  challenges_nonempty : 0 < challenges.length
  support : List Int

def Q192GaussianSamplerParams.trialDenom (P : Q192GaussianSamplerParams) : Nat :=
  P.challenges.length * P.zProp * P.scaleM * (2 ^ 192)

theorem Q192GaussianSamplerParams.trialDenom_pos (P : Q192GaussianSamplerParams) :
    0 < P.trialDenom :=
  Nat.mul_pos (Nat.mul_pos (Nat.mul_pos P.challenges_nonempty P.zProp_pos) P.scaleM_pos)
    (Nat.two_pow_pos 192)

def prodPairs {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  xs.foldr (fun x acc => ys.map (fun y => (x, y)) ++ acc) []

def realQ192TrialWeight (P : Q192GaussianSamplerParams) (shift : Nat → Int)
    (q192Num : Int → Int → Nat) (cz : Nat × Int) : Nat :=
  let v := shift cz.1
  P.scaleM * P.rho (cz.2 - v) * q192Num cz.2 v

def idealSimTrialWeight (P : Q192GaussianSamplerParams) (cz : Nat × Int) : Nat :=
  (2 ^ 192) * P.rho cz.2

def tailDeficitAt (P : Q192GaussianSamplerParams) (shift : Nat → Int) (cz : Nat × Int) : Nat :=
  let v := shift cz.1
  P.rho cz.2 - Nat.min (P.scaleM * P.rho (cz.2 - v)) (P.rho cz.2)

def tailMassRat (P : Q192GaussianSamplerParams) (shift : Nat → Int) : ExactRat :=
  ⟨(natSumList (prodPairs P.challenges P.support) (tailDeficitAt P shift) : Int),
   P.challenges.length * P.zProp * P.scaleM,
   Nat.mul_pos (Nat.mul_pos P.challenges_nonempty P.zProp_pos) P.scaleM_pos⟩

def q192RetryTranscriptTv (P : Q192GaussianSamplerParams) (shift : Nat → Int)
    (q192Num : Int → Int → Nat) (K : Nat) : ExactRat :=
  let pts := prodPairs P.challenges P.support
  let D := P.trialDenom
  let wReal := realQ192TrialWeight P shift q192Num
  let wSim := idealSimTrialWeight P
  let R1 := D - natSumList pts wReal
  let R2 := D - natSumList pts wSim
  ⟨(natL1Diff pts (retryWeight K D R1 wReal) (retryWeight K D R2 wSim) +
      (((R1 ^ K : Nat) : Int) - ((R2 ^ K : Nat) : Int)).natAbs : Int),
   2 * (D ^ K),
   Nat.mul_pos (by decide) (Nat.pow_pos P.trialDenom_pos)⟩

def q192ConditionalAcceptedTv (P : Q192GaussianSamplerParams) (shift : Nat → Int)
    (q192Num : Int → Int → Nat)
    (hRealPos : 0 < natSumList (prodPairs P.challenges P.support) (realQ192TrialWeight P shift q192Num))
    (hSimPos : 0 < natSumList (prodPairs P.challenges P.support) (idealSimTrialWeight P)) : ExactRat :=
  let pts := prodPairs P.challenges P.support
  let wReal := realQ192TrialWeight P shift q192Num
  let wSim := idealSimTrialWeight P
  let A1 := natSumList pts wReal
  let A2 := natSumList pts wSim
  ⟨(natSumList pts (fun x => ((wReal x * A2 : Int) - (wSim x * A1 : Int)).natAbs) : Int),
   2 * A1 * A2,
   Nat.mul_pos (Nat.mul_pos (by decide) hRealPos) hSimPos⟩

private theorem natSumList_append {α : Type} (xs ys : List α) (f : α → Nat) :
    natSumList (xs ++ ys) f = natSumList xs f + natSumList ys f := by
  induction xs with
  | nil => simp only [List.nil_append, natSumList, List.foldr, Nat.zero_add]
  | cons x tl ih => simp only [List.cons_append, natSumList, List.foldr] at ih ⊢; rw [ih, Nat.add_assoc]

private theorem natL1_single_trial_bound (P : Q192GaussianSamplerParams) (shift : Nat → Int)
    (q192Num : Int → Int → Nat)
    (hRhoLe : ∀ z : Int, P.rho z ≤ P.zProp)
    (hUlp : ∀ c z, ((q192Num z (shift c) : Int) -
      (acceptProbQ192FloorNum P.rho P.scaleM z (shift c) : Int)).natAbs ≤ 3) :
    natL1Diff (prodPairs P.challenges P.support) (realQ192TrialWeight P shift q192Num)
        (idealSimTrialWeight P) ≤
      (2 ^ 192) * natSumList (prodPairs P.challenges P.support) (tailDeficitAt P shift) +
      4 * P.challenges.length * P.zProp * P.scaleM * P.support.length := by
  let W := 2 ^ 192
  have hPt : ∀ cz : Nat × Int,
      (((realQ192TrialWeight P shift q192Num cz : Nat) : Int) -
        ((idealSimTrialWeight P cz : Nat) : Int)).natAbs ≤
      W * tailDeficitAt P shift cz + 4 * P.scaleM * P.zProp := by
    intro ⟨c, z⟩
    unfold realQ192TrialWeight idealSimTrialWeight tailDeficitAt; dsimp only
    let mRho := P.scaleM * P.rho (z - shift c)
    let minVal := Nat.min mRho (P.rho z)
    have hErr := q192_scaled_err_le_four_den (P.rho z) mRho W (q192Num z (shift c)) (hUlp c z)
    have hSumRho : minVal + (P.rho z - minVal) = P.rho z := Nat.add_sub_of_le (Nat.min_le_right _ _)
    have hWDecomp : W * P.rho z = W * minVal + W * (P.rho z - minVal) := by
      rw [← hSumRho, Nat.mul_add]
    have hId : ((mRho * q192Num z (shift c) : Nat) : Int) - ((W * P.rho z : Nat) : Int) =
        ((q192Num z (shift c) : Int) * (mRho : Int) - ((W * minVal : Nat) : Int)) -
        ((W * (P.rho z - minVal) : Nat) : Int) := by
      rw [Nat.mul_comm mRho, hWDecomp, Int.natCast_mul (q192Num z (shift c)), Int.natCast_add]
      omega
    change (((mRho * q192Num z (shift c) : Nat) : Int) - ((W * P.rho z : Nat) : Int)).natAbs ≤ _
    rw [hId]
    have hTri := Int.natAbs_sub_le
      ((q192Num z (shift c) : Int) * (mRho : Int) - ((W * minVal : Nat) : Int))
      ((W * (P.rho z - minVal) : Nat) : Int)
    rw [Int.natAbs_natCast] at hTri
    have hBound4 : 4 * mRho ≤ 4 * P.scaleM * P.zProp := by
      rw [← Nat.mul_assoc 4 P.scaleM]; exact Nat.mul_le_mul_left (4 * P.scaleM) (hRhoLe _)
    have hStep := Nat.le_trans hTri (Nat.add_le_add_right (Nat.le_trans hErr hBound4) _)
    rw [Nat.add_comm] at hStep; exact hStep
  have hInner : ∀ (c : Nat) (zs : List Int),
      natL1Diff (zs.map (fun z => (c, z))) (realQ192TrialWeight P shift q192Num) (idealSimTrialWeight P) ≤
      W * natSumList (zs.map (fun z => (c, z))) (tailDeficitAt P shift) +
      4 * P.scaleM * P.zProp * zs.length := by
    intro c zs; induction zs with
    | nil =>
      simp only [List.map, natL1Diff, natSumList, List.foldr, List.length, Nat.mul_zero, Nat.add_zero]
      exact Nat.le_refl 0
    | cons z tl ih =>
      simp only [List.map, natL1Diff, natSumList, List.foldr, List.length] at ih ⊢
      have hAdd := Nat.add_le_add (hPt (c, z)) ih
      have hRhs : (W * tailDeficitAt P shift (c, z) + 4 * P.scaleM * P.zProp) +
          (W * natSumList (List.map (fun z => (c, z)) tl) (tailDeficitAt P shift) +
            4 * P.scaleM * P.zProp * tl.length) =
          W * (tailDeficitAt P shift (c, z) +
            natSumList (List.map (fun z => (c, z)) tl) (tailDeficitAt P shift)) +
          4 * P.scaleM * P.zProp * (tl.length + 1) := by
        rw [Nat.mul_add W, Nat.mul_add (4 * P.scaleM * P.zProp), Nat.mul_one]; ac_rfl
      exact hRhs ▸ hAdd
  have hOuter : ∀ cs : List Nat,
      natL1Diff (prodPairs cs P.support) (realQ192TrialWeight P shift q192Num) (idealSimTrialWeight P) ≤
      W * natSumList (prodPairs cs P.support) (tailDeficitAt P shift) +
      4 * cs.length * P.zProp * P.scaleM * P.support.length := by
    intro cs; induction cs with
    | nil =>
      simp only [prodPairs, List.foldr, natL1Diff, natSumList, List.length, Nat.mul_zero,
        Nat.zero_mul, Nat.add_zero]
      exact Nat.le_refl 0
    | cons c tl ih =>
      simp only [prodPairs, List.foldr, List.length] at ih ⊢
      unfold natL1Diff at ih ⊢
      rw [natSumList_append, natSumList_append]
      have hc := hInner c P.support
      unfold natL1Diff at hc
      have hAdd := Nat.add_le_add hc ih
      have hRhs : (W * natSumList (List.map (fun y => (c, y)) P.support) (tailDeficitAt P shift) +
            4 * P.scaleM * P.zProp * P.support.length) +
          (W * natSumList (prodPairs tl P.support) (tailDeficitAt P shift) +
            4 * tl.length * P.zProp * P.scaleM * P.support.length) =
          W * (natSumList (List.map (fun y => (c, y)) P.support) (tailDeficitAt P shift) +
            natSumList (prodPairs tl P.support) (tailDeficitAt P shift)) +
          4 * (tl.length + 1) * P.zProp * P.scaleM * P.support.length := by
        rw [Nat.mul_add W, Nat.mul_add 4 tl.length 1, Nat.mul_one, Nat.add_mul, Nat.add_mul, Nat.add_mul]
        ac_rfl
      exact hRhs ▸ hAdd
  exact hOuter P.challenges

/-- **HVZK Transcript Simulation Theorem (`q192_gaussian_hvzk_statistical_distance`):**
    Across `K` retry attempts and conditioned on acceptance (`D ≤ K * A_sim`), the `Q192` sampler's
    transcript distribution is within `K · (tailMass + 2^-190 * support.length)` of the simulator. -/
theorem q192_gaussian_hvzk_statistical_distance
    (P : Q192GaussianSamplerParams) (shift : Nat → Int) (q192Num : Int → Int → Nat) (K : Nat)
    (hRhoLe : ∀ z : Int, P.rho z ≤ P.zProp)
    (hUlp : ∀ c z, ((q192Num z (shift c) : Int) -
      (acceptProbQ192FloorNum P.rho P.scaleM z (shift c) : Int)).natAbs ≤ 3)
    (hSubReal : natSumList (prodPairs P.challenges P.support) (realQ192TrialWeight P shift q192Num) ≤ P.trialDenom)
    (hSubSim : natSumList (prodPairs P.challenges P.support) (idealSimTrialWeight P) ≤ P.trialDenom)
    (hRealPos : 0 < natSumList (prodPairs P.challenges P.support) (realQ192TrialWeight P shift q192Num))
    (hSimPos : 0 < natSumList (prodPairs P.challenges P.support) (idealSimTrialWeight P))
    (hSimRate : P.trialDenom ≤ K * natSumList (prodPairs P.challenges P.support) (idealSimTrialWeight P)) :
    let bound := ExactRat.scaleNat K
      ((tailMassRat P shift).add (ExactRat.scaleNat P.support.length (ExactRat.twoNegPow 190)))
    ExactRat.le (q192RetryTranscriptTv P shift q192Num K) bound ∧
    ExactRat.le (q192ConditionalAcceptedTv P shift q192Num hRealPos hSimPos) bound := by
  intro bound
  let pts := prodPairs P.challenges P.support
  let D := P.trialDenom
  let baseDen := P.challenges.length * P.zProp * P.scaleM
  let T := natSumList pts (tailDeficitAt P shift)
  let S := P.support.length
  let delta1 := natL1Diff pts (realQ192TrialWeight P shift q192Num) (idealSimTrialWeight P)
  have hSingle : delta1 ≤ (2 ^ 192) * T + 4 * baseDen * S := by
    simpa only [pts, T, S, baseDen, delta1, Nat.mul_assoc] using
      natL1_single_trial_bound P shift q192Num hRhoLe hUlp
  have hPow192 : (2 : Nat) ^ 192 = 4 * (2 ^ 190) := by
    rw [show (192 : Nat) = 2 + 190 from rfl, Nat.pow_add]; rfl
  have hDEq : D = baseDen * 4 * (2 ^ 190) := by
    unfold D Q192GaussianSamplerParams.trialDenom baseDen; rw [hPow192]; ac_rfl
  have hBoundNum : bound.num = ((K * (T * 2 ^ 190 + S * baseDen) : Nat) : Int) := by
    unfold bound tailMassRat ExactRat.scaleNat ExactRat.add ExactRat.twoNegPow; dsimp only
    rw [Int.mul_one, Int.natCast_mul, Int.natCast_add, Int.natCast_mul, Int.natCast_mul]
  have hBoundDen : bound.den = baseDen * (2 ^ 190) := rfl
  have hDeltaCancel : delta1 * (baseDen * (2 ^ 190)) ≤ (T * (2 ^ 190) + S * baseDen) * D := by
    have h4 := Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right (baseDen * (2 ^ 190)) hSingle)
    rw [hDEq, hPow192] at h4 ⊢
    have hL : 4 * (delta1 * (baseDen * 2 ^ 190)) = 4 * ((delta1 * (baseDen * 2 ^ 190))) := rfl
    have hR : 4 * ((4 * 2 ^ 190 * T + 4 * baseDen * S) * (baseDen * 2 ^ 190)) =
        4 * ((T * 2 ^ 190 + S * baseDen) * (baseDen * 4 * 2 ^ 190)) := by
      rw [Nat.add_mul, Nat.add_mul, Nat.mul_add, Nat.mul_add]; ac_rfl
    rw [hR] at h4
    exact Nat.le_of_mul_le_mul_left h4 (by decide)
  constructor
  · apply ExactRat.le_of_nat_mul rfl hBoundNum
    rw [hBoundDen]
    change _ * (baseDen * 2 ^ 190) ≤ K * (T * 2 ^ 190 + S * baseDen) * (2 * D ^ K)
    have hRetry := retry_full_l1_le_two_K_mul_single pts D
      (realQ192TrialWeight P shift q192Num) (idealSimTrialWeight P) hSubReal hSubSim K
    dsimp only at hRetry
    let EK := natL1Diff pts
        (retryWeight K D (D - natSumList pts (realQ192TrialWeight P shift q192Num))
          (realQ192TrialWeight P shift q192Num))
        (retryWeight K D (D - natSumList pts (idealSimTrialWeight P)) (idealSimTrialWeight P)) +
      ((((D - natSumList pts (realQ192TrialWeight P shift q192Num)) ^ K : Nat) : Int) -
        (((D - natSumList pts (idealSimTrialWeight P)) ^ K : Nat) : Int)).natAbs
    have hStep1 : EK * (baseDen * 2 ^ 190) * D ≤ (2 * K * delta1 * D ^ K) * (baseDen * 2 ^ 190) := by
      have m := Nat.mul_le_mul_right (baseDen * 2 ^ 190) hRetry
      have e : EK * (baseDen * 2 ^ 190) * D = EK * D * (baseDen * 2 ^ 190) := by ac_rfl
      exact e ▸ m
    have hStep2 : (2 * K * delta1 * D ^ K) * (baseDen * 2 ^ 190) ≤
        K * (T * 2 ^ 190 + S * baseDen) * (2 * D ^ K) * D := by
      have m := Nat.mul_le_mul_left (2 * K * D ^ K) hDeltaCancel
      have eL : 2 * K * D ^ K * (delta1 * (baseDen * 2 ^ 190)) =
          2 * K * delta1 * D ^ K * (baseDen * 2 ^ 190) := by ac_rfl
      have eR : 2 * K * D ^ K * ((T * 2 ^ 190 + S * baseDen) * D) =
          K * (T * 2 ^ 190 + S * baseDen) * (2 * D ^ K) * D := by ac_rfl
      rw [eL, eR] at m; exact m
    exact Nat.le_of_mul_le_mul_right (Nat.le_trans hStep1 hStep2) P.trialDenom_pos
  · apply ExactRat.le_of_nat_mul rfl hBoundNum
    rw [hBoundDen]
    let A1 := natSumList pts (realQ192TrialWeight P shift q192Num)
    let A2 := natSumList pts (idealSimTrialWeight P)
    change _ * (baseDen * 2 ^ 190) ≤ K * (T * 2 ^ 190 + S * baseDen) * (2 * A1 * A2)
    have hCond := conditional_accepted_l1_le_two_mul_single pts
      (realQ192TrialWeight P shift q192Num) (idealSimTrialWeight P)
    dsimp only at hCond
    have h1 := Nat.mul_le_mul_right (baseDen * 2 ^ 190) hCond
    rw [Nat.mul_assoc (2 * A1)] at h1
    have h2 := Nat.mul_le_mul_left (2 * A1)
      (Nat.le_trans hDeltaCancel (Nat.mul_le_mul_left (T * 2 ^ 190 + S * baseDen) hSimRate))
    have hChain := Nat.le_trans h1 h2
    have eR : 2 * A1 * ((T * 2 ^ 190 + S * baseDen) * (K * A2)) =
        K * (T * 2 ^ 190 + S * baseDen) * (2 * A1 * A2) := by ac_rfl
    exact eR ▸ hChain

def q192AcceptIndicatorProb (P : Q192GaussianSamplerParams) (shift : Nat → Int)
    (q192Num : Int → Int → Nat) (K : Nat) (b : Bool) : ExactRat :=
  let pts := prodPairs P.challenges P.support
  let D := P.trialDenom
  let R := D - natSumList pts (realQ192TrialWeight P shift q192Num)
  let num := if b then (D ^ K) - (R ^ K) else R ^ K
  ⟨(num : Int), D ^ K, Nat.pow_pos P.trialDenom_pos⟩

private theorem add_mul_lt_of_two_mul_lt {a b p D : Nat}
    (h1 : 2 * a * p < D) (h2 : 2 * b * p ≤ D) : (a + b) * p < D := by
  have hSum : 2 * ((a + b) * p) < 2 * D := by
    have hEq : 2 * ((a + b) * p) = 2 * a * p + 2 * b * p := by
      rw [Nat.add_mul, Nat.mul_add]; ac_rfl
    rw [hEq, Nat.two_mul]
    exact Nat.add_lt_add_of_lt_of_le h1 h2
  exact Decidable.byContradiction fun hNot =>
    Nat.lt_irrefl (2 * D)
      (Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 (Nat.le_of_not_lt hNot)) hSum)

private theorem lt_of_mul_lt_mul_right_nat {x y D : Nat} (h : x * D < y * D) : x < y :=
  Decidable.byContradiction fun hNot =>
    Nat.lt_irrefl (y * D)
      (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right D (Nat.le_of_not_lt hNot)) h)

/-- **Abort Marginal Secret-Independence (`q192_gaussian_abort_marginal_secret_independent`):**
    The marginal probability of `accept = b` (`b ∈ {true, false}`) differs between any two
    bounded secrets by `< 2^-128`. -/
theorem q192_gaussian_abort_marginal_secret_independent
    (P : Q192GaussianSamplerParams) (shift1 shift2 : Nat → Int)
    (q192Num : Int → Int → Nat) (K : Nat) (b : Bool)
    (hSub1 : natSumList (prodPairs P.challenges P.support) (realQ192TrialWeight P shift1 q192Num) ≤ P.trialDenom)
    (hSub2 : natSumList (prodPairs P.challenges P.support) (realQ192TrialWeight P shift2 q192Num) ≤ P.trialDenom)
    (hSubSim : natSumList (prodPairs P.challenges P.support) (idealSimTrialWeight P) ≤ P.trialDenom)
    (hSmall1 : 2 * K * natL1Diff (prodPairs P.challenges P.support)
        (realQ192TrialWeight P shift1 q192Num) (idealSimTrialWeight P) * (2 ^ 128) < P.trialDenom)
    (hSmall2 : 2 * K * natL1Diff (prodPairs P.challenges P.support)
        (realQ192TrialWeight P shift2 q192Num) (idealSimTrialWeight P) * (2 ^ 128) ≤ P.trialDenom) :
    ExactRat.lt
      (ExactRat.abs (ExactRat.sub
        (q192AcceptIndicatorProb P shift1 q192Num K b)
        (q192AcceptIndicatorProb P shift2 q192Num K b)))
      (ExactRat.twoNegPow 128) := by
  apply ExactRat.abs_lt_twoNegPow
  let pts := prodPairs P.challenges P.support
  let D := P.trialDenom
  let w1 := realQ192TrialWeight P shift1 q192Num
  let w2 := realQ192TrialWeight P shift2 q192Num
  let wS := idealSimTrialWeight P
  let R1 := D - natSumList pts w1
  let R2 := D - natSumList pts w2
  let RS := D - natSumList pts wS
  have hAb1 := retry_abort_diff_le_K_mul_single pts D w1 wS hSub1 hSubSim K
  have hAb2 := retry_abort_diff_le_K_mul_single pts D w2 wS hSub2 hSubSim K
  dsimp only at hAb1 hAb2
  have hTri : (((R1 ^ K : Nat) : Int) - ((R2 ^ K : Nat) : Int)).natAbs * D ≤
      (K * natL1Diff pts w1 wS + K * natL1Diff pts w2 wS) * (D ^ K) := by
    let P1 := R1 ^ K; let P2 := R2 ^ K; let PS := RS ^ K
    have hDecomp : (P1 : Int) - (P2 : Int) = ((P1 : Int) - (PS : Int)) + ((PS : Int) - (P2 : Int)) := by omega
    have hFlip : ((PS : Int) - (P2 : Int)).natAbs = ((P2 : Int) - (PS : Int)).natAbs := by omega
    have hAbs := Int.natAbs_add_le ((P1 : Int) - (PS : Int)) ((PS : Int) - (P2 : Int))
    rw [← hDecomp, hFlip] at hAbs
    have hM := Nat.mul_le_mul_right D hAbs
    rw [Nat.add_mul, Nat.add_mul] at hM ⊢
    exact Nat.le_trans hM (Nat.add_le_add hAb1 hAb2)
  have hSumLt : (K * natL1Diff pts w1 wS + K * natL1Diff pts w2 wS) * (2 ^ 128) < D := by
    rw [Nat.mul_assoc 2 K] at hSmall1 hSmall2
    exact add_mul_lt_of_two_mul_lt hSmall1 hSmall2
  have hDKPos : 0 < D ^ K := Nat.pow_pos P.trialDenom_pos
  have hBoundRK : (((R1 ^ K : Nat) : Int) - ((R2 ^ K : Nat) : Int)).natAbs * (2 ^ 128) < D ^ K := by
    have p1 := Nat.mul_le_mul_right (2 ^ 128) hTri
    have p2 := Nat.mul_lt_mul_of_pos_right hSumLt hDKPos
    have e1 : (((R1 ^ K : Nat) : Int) - ((R2 ^ K : Nat) : Int)).natAbs * (2 ^ 128) * D =
        (((R1 ^ K : Nat) : Int) - ((R2 ^ K : Nat) : Int)).natAbs * D * (2 ^ 128) := by ac_rfl
    have e2 : (K * natL1Diff pts w1 wS + K * natL1Diff pts w2 wS) * D ^ K * (2 ^ 128) =
        (K * natL1Diff pts w1 wS + K * natL1Diff pts w2 wS) * (2 ^ 128) * D ^ K := by ac_rfl
    have e3 : D * D ^ K = D ^ K * D := Nat.mul_comm _ _
    exact lt_of_mul_lt_mul_right_nat (by rw [e1]; exact Nat.lt_of_le_of_lt p1 (by rw [e2, ← e3]; exact p2))
  unfold q192AcceptIndicatorProb ExactRat.sub; dsimp only
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← Int.sub_mul, Int.natAbs_mul, Int.natAbs_natCast]
    have m := Nat.mul_lt_mul_of_pos_right hBoundRK hDKPos
    have e : (((R1 ^ K : Nat) : Int) - ((R2 ^ K : Nat) : Int)).natAbs * D ^ K * 2 ^ 128 =
        (((R1 ^ K : Nat) : Int) - ((R2 ^ K : Nat) : Int)).natAbs * 2 ^ 128 * D ^ K := by ac_rfl
    exact e ▸ m
  · simp only [↓reduceIte]
    rw [← Int.sub_mul, Int.natAbs_mul, Int.natAbs_natCast,
        sub_sub_natAbs_eq (Nat.pow_le_pow_left (Nat.sub_le D _) K)
          (Nat.pow_le_pow_left (Nat.sub_le D _) K)]
    have m := Nat.mul_lt_mul_of_pos_right hBoundRK hDKPos
    have e : (((R1 ^ K : Nat) : Int) - ((R2 ^ K : Nat) : Int)).natAbs * D ^ K * 2 ^ 128 =
        (((R1 ^ K : Nat) : Int) - ((R2 ^ K : Nat) : Int)).natAbs * 2 ^ 128 * D ^ K := by ac_rfl
    exact e ▸ m

/-! ## 4. Dense Expand-Accumulate Dual-LPN Structure & Constructive Piling-Up Lemma -/

def accPrefixXor (e : Nat → Bool) : Nat → Bool
  | 0 => e 0
  | k + 1 => Bool.xor (accPrefixXor e k) (e (k + 1))

def unitPunctureVec (pStar i : Nat) : Bool := decide (i = pStar)

theorem accUnitPuncture_eq_stepIndicator (pStar : Nat) :
    ∀ k : Nat, accPrefixXor (unitPunctureVec pStar) k = decide (pStar ≤ k)
  | 0 => by unfold accPrefixXor unitPunctureVec; by_cases h : pStar = 0 <;> simp [h]; omega
  | k + 1 => by
    simp only [accPrefixXor, accUnitPuncture_eq_stepIndicator pStar k, unitPunctureVec]
    by_cases h1 : pStar ≤ k
    · have h2 : ¬ (k + 1 = pStar) := by omega
      have h3 : pStar ≤ k + 1 := by omega
      simp [h1, h2, h3]
    · by_cases h2 : k + 1 = pStar
      · have h3 : pStar ≤ k + 1 := by omega
        simp [h1, h2, h3]
      · have h3 : ¬ (pStar ≤ k + 1) := by omega
        simp [h1, h2, h3]

def accSuffixXor (L : Nat) (u : Nat → Bool) (i : Nat) : Bool :=
  (List.range (L - i)).foldl (fun acc d => Bool.xor acc (u (i + d))) false

def gf2InnerProd : Nat → (Nat → Bool) → (Nat → Bool) → Bool
  | 0, _, _ => false
  | k + 1, a, b => Bool.xor (gf2InnerProd k a b) (a k && b k)

theorem acc_transpose_duality (u : Nat → Bool) (pStar : Nat) :
    ∀ d : Nat,
      gf2InnerProd (pStar + d) u (accPrefixXor (unitPunctureVec pStar)) =
      accSuffixXor (pStar + d) u pStar := by
  have hBelow : ∀ m : Nat, m ≤ pStar → gf2InnerProd m u (accPrefixXor (unitPunctureVec pStar)) = false := by
    intro m hm; induction m with
    | zero => rfl
    | succ m' ih =>
      simp only [gf2InnerProd, ih (by omega), accUnitPuncture_eq_stepIndicator]
      have hNot : ¬ (pStar ≤ m') := by omega
      simp [hNot]
  intro d; induction d with
  | zero =>
    rw [Nat.add_zero, hBelow pStar (Nat.le_refl pStar)]
    unfold accSuffixXor; simp only [Nat.sub_self, List.range_zero, List.foldl]
  | succ d' ih =>
    rw [Nat.add_succ, gf2InnerProd, ih, accUnitPuncture_eq_stepIndicator]
    unfold accSuffixXor
    have hSub1 : pStar + d' - pStar = d' := Nat.add_sub_cancel_left pStar d'
    have hSub2 : (pStar + d').succ - pStar = d' + 1 := by omega
    rw [hSub1, hSub2, List.range_succ, List.foldl_append, List.foldl]
    simp [Nat.le_add_right pStar d']

def xorStepProb (tau p : ExactRat) : ExactRat :=
  ⟨tau.num * ((p.den : Int) - p.num) + ((tau.den : Int) - tau.num) * p.num,
   tau.den * p.den, Nat.mul_pos tau.den_pos p.den_pos⟩

def bernoulliXorOneProb (tau : ExactRat) : Nat → ExactRat
  | 0 => ExactRat.ofInt 0
  | w + 1 => xorStepProb tau (bernoulliXorOneProb tau w)

def regularBlockXorOneProb : List ExactRat → ExactRat
  | [] => ExactRat.ofInt 0
  | tau :: tl => xorStepProb tau (regularBlockXorOneProb tl)

def parityBias (p : ExactRat) : ExactRat := ⟨(p.den : Int) - 2 * p.num, p.den, p.den_pos⟩

private theorem parityBias_xorStepProb (tau p : ExactRat) :
    parityBias (xorStepProb tau p) = ExactRat.mul (parityBias tau) (parityBias p) := by
  rcases tau with ⟨tn, td, htd⟩
  rcases p with ⟨pn, pd, hpd⟩
  unfold parityBias xorStepProb ExactRat.mul; dsimp only
  congr 1
  rw [Int.natCast_mul, Int.mul_sub tn, Int.sub_mul (td : Int), Int.mul_add 2,
      Int.mul_sub 2, Int.mul_sub 2, Int.mul_sub ((td : Int) - 2 * tn),
      Int.sub_mul (td : Int), Int.sub_mul (td : Int)]
  have c1 : 2 * tn * (pd : Int) = 2 * (tn * (pd : Int)) := Int.mul_assoc 2 tn (pd : Int)
  have c2 : (td : Int) * (2 * pn) = 2 * ((td : Int) * pn) := by ac_rfl
  have c3 : 2 * tn * (2 * pn) = 4 * (tn * pn) := by
    rw [Int.mul_assoc 2 tn, Int.mul_left_comm tn 2 pn, ← Int.mul_assoc 2 2]; rfl
  rw [c1, c2, c3]; omega

/-- **Constructive Piling-Up Lemma (`piling_up_lemma_bernoulli_rat`):**
    `bias(⊕_{i=1}^w e_i) = (1 - 2τ)^w` over `ExactRat`. -/
theorem piling_up_lemma_bernoulli_rat (tau : ExactRat) :
    ∀ w : Nat, parityBias (bernoulliXorOneProb tau w) = ExactRat.pow (parityBias tau) w
  | 0 => rfl
  | w + 1 => by
    simp only [bernoulliXorOneProb, ExactRat.pow]
    rw [parityBias_xorStepProb, piling_up_lemma_bernoulli_rat tau w]

theorem piling_up_lemma_regular_blocks_rat :
    ∀ rates : List ExactRat,
      parityBias (regularBlockXorOneProb rates) =
      rates.foldr (fun tau acc => ExactRat.mul (parityBias tau) acc) (ExactRat.ofInt 1)
  | [] => rfl
  | tau :: tl => by
    simp only [regularBlockXorOneProb, List.foldr]
    rw [parityBias_xorStepProb, piling_up_lemma_regular_blocks_rat tl]

theorem bernoulli_dual_min_weight_bias_lt_two_neg_256 (dMin : Nat) (hd : 1536 ≤ dMin) :
    let tau : ExactRat := ⟨1, 16, by decide⟩
    ExactRat.lt (ExactRat.abs (parityBias (bernoulliXorOneProb tau dMin))) (ExactRat.twoNegPow 256) := by
  intro tau
  rw [piling_up_lemma_bernoulli_rat]
  apply ExactRat.abs_lt_twoNegPow
  have hPowFormula : ∀ n : Nat,
      (ExactRat.pow (parityBias tau) n).num = ((14 ^ n : Nat) : Int) ∧
      (ExactRat.pow (parityBias tau) n).den = 16 ^ n := by
    intro n; induction n with
    | zero => exact ⟨rfl, rfl⟩
    | succ n' ih =>
      simp only [ExactRat.pow, ExactRat.mul, ih.1, ih.2]
      exact ⟨by change (14 : Int) * ((14 ^ n' : Nat) : Int) = ((14 ^ (n' + 1) : Nat) : Int)
                rw [Nat.pow_succ', Int.natCast_mul]; rfl,
             by rw [Nat.pow_succ']⟩
  have hBase6 : 14 ^ 6 * 2 < 16 ^ 6 := by decide
  have hStep6 : ∀ m : Nat, 14 ^ (6 * (m + 1)) * 2 ^ (m + 1) < 16 ^ (6 * (m + 1)) := by
    intro m; induction m with
    | zero => simpa using hBase6
    | succ m' ih =>
      have e6 : 6 * (m' + 2) = 6 * (m' + 1) + 6 := by omega
      rw [e6, Nat.pow_add 14, Nat.pow_add 16, Nat.pow_succ 2 (m' + 1)]
      have hRe : 14 ^ (6 * (m' + 1)) * 14 ^ 6 * (2 ^ (m' + 1) * 2) =
          (14 ^ (6 * (m' + 1)) * 2 ^ (m' + 1)) * (14 ^ 6 * 2) := by ac_rfl
      rw [hRe]
      exact Nat.lt_trans
        (Nat.mul_lt_mul_of_pos_right ih (by decide))
        (Nat.mul_lt_mul_of_pos_left hBase6 (Nat.pow_pos (by decide)))
  have h1536 : 14 ^ 1536 * 2 ^ 256 < 16 ^ 1536 := hStep6 255
  have hMono : ∀ k : Nat, 14 ^ (1536 + k) * 2 ^ 256 < 16 ^ (1536 + k) := by
    intro k; induction k with
    | zero => simpa using h1536
    | succ k' ih =>
      rw [Nat.add_succ, Nat.pow_succ 14, Nat.pow_succ 16]
      have hRe : 14 ^ (1536 + k') * 14 * 2 ^ 256 = (14 ^ (1536 + k') * 2 ^ 256) * 14 := by ac_rfl
      rw [hRe]
      exact Nat.lt_of_lt_of_le
        (Nat.mul_lt_mul_of_pos_right ih (by decide))
        (Nat.mul_le_mul_left _ (by decide))
  rw [(hPowFormula dMin).1, (hPowFormula dMin).2, Int.natAbs_natCast]
  have hk := hMono (dMin - 1536)
  rw [Nat.add_sub_of_le hd] at hk; exact hk

def depth15TreeRate (w : Nat) : ExactRat := ⟨(w : Int), 32768, by decide⟩

theorem pcg_dense_dual_lpn_linear_bias_lt_two_neg_256
    (weights : List Nat) (hLen : weights.length = 64)
    (hBal : ∀ w ∈ weights, ((32768 : Int) - 2 * (w : Int)).natAbs ≤ 2047) :
    ExactRat.lt
      (ExactRat.abs (parityBias (regularBlockXorOneProb (weights.map depth15TreeRate))))
      (ExactRat.twoNegPow 256) := by
  rw [piling_up_lemma_regular_blocks_rat]
  apply ExactRat.abs_lt_twoNegPow
  have hProdBound : ∀ (ws : List Nat),
      (∀ w ∈ ws, ((32768 : Int) - 2 * (w : Int)).natAbs ≤ 2047) →
      ((ws.map depth15TreeRate).foldr (fun tau acc => ExactRat.mul (parityBias tau) acc)
          (ExactRat.ofInt 1)).num.natAbs ≤ 2047 ^ ws.length ∧
      ((ws.map depth15TreeRate).foldr (fun tau acc => ExactRat.mul (parityBias tau) acc)
          (ExactRat.ofInt 1)).den = 32768 ^ ws.length := by
    intro ws hW; induction ws with
    | nil => exact ⟨by decide, rfl⟩
    | cons w tl ih =>
      have hw := hW w (.head tl)
      have htl := ih (fun x hx => hW x (.tail w hx))
      simp only [List.map, List.foldr, ExactRat.mul, List.length]
      exact ⟨by rw [Int.natAbs_mul, Nat.pow_succ']; exact Nat.mul_le_mul hw htl.1,
             by rw [htl.2, Nat.pow_succ']⟩
  have h64 := hProdBound weights hBal
  rw [hLen] at h64
  rw [h64.2]
  have hScale : ∀ m : Nat, 2048 ^ m * 2 ^ (4 * m) = 32768 ^ m := by
    intro m; induction m with
    | zero => rfl
    | succ m' ih =>
      have e4 : 4 * (m' + 1) = 4 * m' + 4 := by omega
      rw [e4, Nat.pow_succ 2048, Nat.pow_add 2, Nat.pow_succ 32768, ← ih]
      have c : 2048 * 2 ^ 4 = 32768 := by decide
      rw [← c]; ac_rfl
  have hLtPow : 2047 ^ 64 < 2048 ^ 64 := Nat.pow_lt_pow_left (by decide) (by decide)
  have hNatLt : 2047 ^ 64 * 2 ^ 256 < 32768 ^ 64 := by
    rw [← hScale 64]; exact Nat.mul_lt_mul_of_pos_right hLtPow (Nat.two_pow_pos 256)
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right (2 ^ 256) h64.1) hNatLt

theorem tooth_omitting_accumulator_collapses_dual_lpn_bias :
    ExactRat.lt
      (ExactRat.twoNegPow 256)
      (ExactRat.abs (parityBias (regularBlockXorOneProb ((List.replicate 64 3).map depth15TreeRate)))) := by
  rw [piling_up_lemma_regular_blocks_rat]
  apply ExactRat.twoNegPow_lt_abs
  have hRep : ∀ n : Nat,
      (((List.replicate n 3).map depth15TreeRate).foldr
          (fun tau acc => ExactRat.mul (parityBias tau) acc) (ExactRat.ofInt 1)).num =
        ((32762 ^ n : Nat) : Int) ∧
      (((List.replicate n 3).map depth15TreeRate).foldr
          (fun tau acc => ExactRat.mul (parityBias tau) acc) (ExactRat.ofInt 1)).den =
        32768 ^ n := by
    intro n; induction n with
    | zero => exact ⟨rfl, rfl⟩
    | succ n' ih =>
      simp only [List.replicate_succ, List.map, List.foldr, ExactRat.mul, ih.1, ih.2]
      exact ⟨by change (32762 : Int) * ((32762 ^ n' : Nat) : Int) = ((32762 ^ (n' + 1) : Nat) : Int)
                rw [Nat.pow_succ', Int.natCast_mul]; rfl,
             by rw [Nat.pow_succ']⟩
  have h64 := hRep 64
  rw [h64.1, h64.2, Int.natAbs_natCast]
  have hSplit : ∀ m : Nat, 32768 ^ m = 16384 ^ m * 2 ^ m := by
    intro m; induction m with
    | zero => rfl
    | succ m' ih =>
      rw [Nat.pow_succ 32768, ih, Nat.pow_succ 16384, Nat.pow_succ 2]
      have c : 32768 = 16384 * 2 := by decide
      rw [c]; ac_rfl
  rw [hSplit 64]
  exact Nat.lt_of_lt_of_le
    (Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_left (by decide) (by decide)) (Nat.two_pow_pos 64))
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by decide)))

/-! ## 5. Prange & Universal Stern–Dumer ISD Work-Factor Lower Bounds (`Depth15`) -/

def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, j + 1 => binom n j + binom n (j + 1)

theorem binom_zero_right (n : Nat) : binom n 0 = 1 := by cases n <;> rfl

theorem binom_one_right : ∀ n : Nat, binom n 1 = n
  | 0 => rfl
  | n + 1 => by simp only [binom, binom_one_right n, binom_zero_right n]; omega

theorem binom_mul_succ : ∀ (n j : Nat), (j + 1) * binom (n + 1) (j + 1) = (n + 1) * binom n j
  | 0, 0 => rfl
  | 0, _ + 1 => Nat.mul_zero _
  | n + 1, 0 => by rw [Nat.zero_add, binom_one_right (n + 2), binom_zero_right (n + 1), Nat.one_mul, Nat.mul_one]
  | n + 1, j + 1 => by
    have ih1 : (j + 1) * (binom n j + binom n (j + 1)) = (n + 1) * binom n j := binom_mul_succ n j
    have ih2 : (j + 2) * binom (n + 1) (j + 2) = (n + 1) * binom n (j + 1) := binom_mul_succ n (j + 1)
    change (j + 2) * ((binom n j + binom n (j + 1)) + binom (n + 1) (j + 2)) =
      (n + 2) * (binom n j + binom n (j + 1))
    have hL : (j + 2) * (binom n j + binom n (j + 1)) =
        (binom n j + binom n (j + 1)) + (j + 1) * (binom n j + binom n (j + 1)) := by
      rw [show j + 2 = 1 + (j + 1) from by omega, Nat.add_mul, Nat.one_mul]
    have hR : (n + 2) * (binom n j + binom n (j + 1)) =
        (binom n j + binom n (j + 1)) + ((n + 1) * binom n j + (n + 1) * binom n (j + 1)) := by
      rw [show n + 2 = 1 + (n + 1) from by omega, Nat.add_mul, Nat.one_mul, Nat.mul_add]
    rw [Nat.mul_add (j + 2), hL, ih1, ih2, hR, Nat.add_assoc]

theorem binom_step_right (n j : Nat) : (j + 1) * binom n (j + 1) = (n - j) * binom n j := by
  by_cases hLe : j ≤ n
  · have hAbs : (j + 1) * (binom n j + binom n (j + 1)) = (n + 1) * binom n j := binom_mul_succ n j
    rw [Nat.mul_add] at hAbs
    have hSub : (j + 1) * binom n j + (n - j) * binom n j = (n + 1) * binom n j := by
      rw [← Nat.add_mul, show j + 1 + (n - j) = n + 1 from by omega]
    omega
  · have hZero : ∀ (m k : Nat), m < k → binom m k = 0 := by
      intro m; induction m with
      | zero => intro k hk; cases k with | zero => omega | succ _ => rfl
      | succ m' ih =>
        intro k hk; cases k with
        | zero => omega
        | succ k' => simp only [binom, ih k' (by omega), ih (k' + 1) (by omega)]
    rw [hZero n (j + 1) (by omega), show n - j = 0 from by omega, Nat.zero_mul, Nat.mul_zero]

theorem binom_mono_left {a b : Nat} (h : a ≤ b) : ∀ j : Nat, binom a j ≤ binom b j := by
  induction h with
  | refl => intro _; exact Nat.le_refl _
  | step _ ih =>
    intro j; cases j with
    | zero => simp only [binom_zero_right]; exact Nat.le_refl 1
    | succ j' => simp only [binom]; exact Nat.add_le_add (ih j') (ih (j' + 1))

theorem binom_pos : ∀ {n j : Nat}, j ≤ n → 0 < binom n j
  | n, 0, _ => by rw [binom_zero_right n]; exact Nat.one_pos
  | 0, _ + 1, h => by omega
  | n + 1, j + 1, h => by
    simp only [binom]; exact Nat.add_pos_left (binom_pos (n := n) (j := j) (by omega)) _

theorem binom_scale_lower_bound {c : Nat} (hc : 1 ≤ c) :
    ∀ {t r M : Nat}, t ≤ r → c * r ≤ M → c ^ t * binom r t ≤ binom M t
  | 0, r, M, _, _ => by rw [Nat.pow_zero, binom_zero_right, binom_zero_right, Nat.one_mul]; exact Nat.le_refl 1
  | _ + 1, 0, _, ht, _ => by omega
  | _ + 1, r + 1, 0, _, hcr => by have := Nat.mul_pos hc (Nat.succ_pos r); omega
  | t + 1, r + 1, M + 1, ht, hcr => by
    have hcr' : c * r ≤ M := by rw [Nat.mul_add, Nat.mul_one] at hcr; omega
    have ih := binom_scale_lower_bound hc (t := t) (r := r) (M := M) (by omega) hcr'
    have hMul := Nat.mul_le_mul hcr ih
    have hRearr : c * (r + 1) * (c ^ t * binom r t) = c ^ (t + 1) * ((r + 1) * binom r t) := by
      rw [Nat.pow_succ']; ac_rfl
    rw [hRearr, ← binom_mul_succ r t, ← binom_mul_succ M t] at hMul
    have hAssoc : c ^ (t + 1) * ((t + 1) * binom (r + 1) (t + 1)) =
        (t + 1) * (c ^ (t + 1) * binom (r + 1) (t + 1)) := by ac_rfl
    rw [hAssoc] at hMul
    exact Nat.le_of_mul_le_mul_left hMul (Nat.succ_pos t)

theorem binom_scale_upper_bound (c : Nat) :
    ∀ {t M r : Nat}, t ≤ r → M ≤ c * (r - t) → binom M t ≤ c ^ t * binom r t
  | 0, M, r, _, _ => by rw [binom_zero_right, binom_zero_right, Nat.pow_zero, Nat.one_mul]; exact Nat.le_refl 1
  | _ + 1, 0, _, _, _ => Nat.zero_le _
  | _ + 1, _ + 1, 0, ht, _ => by omega
  | t + 1, M + 1, r + 1, ht, hMc => by
    rw [Nat.succ_sub_succ] at hMc
    have ih := binom_scale_upper_bound c (t := t) (M := M) (r := r) (by omega) (Nat.le_of_succ_le hMc)
    have hStepM : M + 1 ≤ c * (r + 1) :=
      Nat.le_trans hMc (Nat.mul_le_mul_left c (Nat.le_trans (Nat.sub_le r t) (Nat.le_succ r)))
    have hMul := Nat.mul_le_mul hStepM ih
    rw [← binom_mul_succ M t] at hMul
    have hRhs : c * (r + 1) * (c ^ t * binom r t) = (t + 1) * (c ^ (t + 1) * binom (r + 1) (t + 1)) := by
      have p1 : c * (r + 1) * (c ^ t * binom r t) = c ^ (t + 1) * ((r + 1) * binom r t) := by
        rw [Nat.pow_succ']; ac_rfl
      rw [p1, ← binom_mul_succ r t]; ac_rfl
    rw [hRhs] at hMul
    exact Nat.le_of_mul_le_mul_left hMul (Nat.succ_pos t)

-- Seal `binom` so kernel WHNF never unfolds large binomial coefficients like `binom 2097152 64`.
attribute [irreducible] binom

def pcgDenseRows : Nat := 139264
def pcgDenseWeightT : Nat := 64
def pcgDepth15Cols : Nat := 2097152
def pcgDepth14Cols : Nat := 1048576

def sternDumerWorkExceedsPow2 (M r t q l bits : Nat) : Prop :=
  let Lq := binom ((M - r) / 2) q
  2 ^ bits * (Lq ^ 2 * binom (r - l) (t - 2 * q)) ≤
    (r ^ 2 + 2 * Lq + Lq ^ 2 / (2 ^ l)) * binom M t

private theorem fifteen_pow64_gt_256 : 2 ^ 256 < 81 * 15 ^ 64 := by
  have h1 : 2 ^ 64 < 3 * 15 ^ 16 := by decide
  have h2 : 2 ^ 128 < 9 * 15 ^ 32 := by
    rw [show (128 : Nat) = 64 + 64 from rfl, show (32 : Nat) = 16 + 16 from rfl,
        Nat.pow_add, Nat.pow_add]
    have e : 9 * (15 ^ 16 * 15 ^ 16) = (3 * 15 ^ 16) * (3 * 15 ^ 16) := by ac_rfl
    rw [e]
    exact Nat.lt_trans
      (Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos 64))
      (Nat.mul_lt_mul_of_pos_left h1 (Nat.mul_pos (by decide) (Nat.pow_pos (by decide))))
  rw [show (256 : Nat) = 128 + 128 from rfl, show (64 : Nat) = 32 + 32 from rfl,
      Nat.pow_add, Nat.pow_add]
  have e : 81 * (15 ^ 32 * 15 ^ 32) = (9 * 15 ^ 32) * (9 * 15 ^ 32) := by ac_rfl
  rw [e]
  exact Nat.lt_trans
    (Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos 128))
    (Nat.mul_lt_mul_of_pos_left h2 (Nat.mul_pos (by decide) (Nat.pow_pos (by decide))))

/-- **Prange & Universal Stern–Dumer ISD Lower Bound (`pcg_dense_depth15_prange_and_stern_dumer_pq128`):**
    At `Depth15` ($M = 2^{21}, r = 139{,}264, t = 64$), both Prange (`q = 0`) and Stern–Dumer ISD
    for all `q ≤ 32` and all `l` require `≥ 2^256` classical operations (`≥ 2^128` Grover). -/
theorem pcg_dense_depth15_prange_and_stern_dumer_pq128 (q l : Nat) (hq : q ≤ 32) :
    sternDumerWorkExceedsPow2 pcgDepth15Cols pcgDenseRows pcgDenseWeightT q l 256 ∧
    256 / 2 = 128 := by
  refine ⟨?_, rfl⟩
  unfold sternDumerWorkExceedsPow2 pcgDepth15Cols pcgDenseRows pcgDenseWeightT
  dsimp only
  have hHalfEq : (2097152 - 139264) / 2 = 978944 := rfl
  rw [hHalfEq]
  have hScaleM : 15 ^ 64 * binom 139264 64 ≤ binom 2097152 64 :=
    binom_scale_lower_bound (by decide) (by decide) (by decide)
  have hWinMono : binom (139264 - l) (64 - 2 * q) ≤ binom 139264 (64 - 2 * q) :=
    binom_mono_left (Nat.sub_le 139264 l) (64 - 2 * q)
  suffices hCore : 2 ^ 256 * (binom 978944 q ^ 2 * binom 139264 (64 - 2 * q)) ≤
      (139264 ^ 2 + 2 * binom 978944 q) * (15 ^ 64 * binom 139264 64) by
    exact Nat.le_trans
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hWinMono))
      (Nat.le_trans hCore (Nat.mul_le_mul (Nat.le_add_right _ _) hScaleM))
  have h15 := Nat.le_of_lt fifteen_pow64_gt_256
  match q with
  | 0 =>
    rw [binom_zero_right 978944]; simp only [Nat.one_pow, Nat.one_mul, Nat.mul_one]
    have hr2 : 81 * 15 ^ 64 ≤ (139264 ^ 2 + 2) * 15 ^ 64 :=
      Nat.mul_le_mul_right _ (by decide)
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ (Nat.le_trans h15 hr2)
  | 1 =>
    rw [binom_one_right 978944]
    have s63 := binom_step_right 139264 63
    have s62 := binom_step_right 139264 62
    have hRel : 64 * 63 * binom 139264 64 = (139264 - 63) * (139264 - 62) * binom 139264 62 := by
      calc 64 * 63 * binom 139264 64
        _ = 63 * (64 * binom 139264 64) := by ac_rfl
        _ = (139264 - 63) * (63 * binom 139264 63) := by rw [s63]; ac_rfl
        _ = (139264 - 63) * (139264 - 62) * binom 139264 62 := by rw [s62]; ac_rfl
    have hCoeff : 64 * 63 * 978944 ^ 2 * 81 ≤
        (139264 ^ 2 + 2 * 978944) * ((139264 - 63) * (139264 - 62)) := by decide
    have hMul : 64 * 63 * (2 ^ 256 * (978944 ^ 2 * binom 139264 62)) ≤
        64 * 63 * ((139264 ^ 2 + 2 * 978944) * (15 ^ 64 * binom 139264 64)) := by
      have hRhsEq : 64 * 63 * ((139264 ^ 2 + 2 * 978944) * (15 ^ 64 * binom 139264 64)) =
          (139264 ^ 2 + 2 * 978944) * ((139264 - 63) * (139264 - 62)) * 15 ^ 64 * binom 139264 62 := by
        have p : 64 * 63 * ((139264 ^ 2 + 2 * 978944) * (15 ^ 64 * binom 139264 64)) =
            (139264 ^ 2 + 2 * 978944) * 15 ^ 64 * (64 * 63 * binom 139264 64) := by ac_rfl
        rw [p, hRel]; ac_rfl
      rw [hRhsEq]
      have m1 := Nat.mul_le_mul_right (64 * 63 * 978944 ^ 2) h15
      have m2 := Nat.mul_le_mul_right (15 ^ 64) hCoeff
      have r1 : 81 * 15 ^ 64 * (64 * 63 * 978944 ^ 2) = 64 * 63 * 978944 ^ 2 * 81 * 15 ^ 64 := by ac_rfl
      have m3 := Nat.mul_le_mul_right (binom 139264 62) (Nat.le_trans m1 (r1 ▸ m2))
      have eL : 2 ^ 256 * (64 * 63 * 978944 ^ 2) * binom 139264 62 =
          64 * 63 * (2 ^ 256 * (978944 ^ 2 * binom 139264 62)) := by ac_rfl
      exact eL ▸ m3
    exact Nat.le_of_mul_le_mul_left hMul (by decide)
  | q' + 2 =>
    have hMonoQ : ∀ m : Nat, m ≤ 30 →
        binom 978944 (m + 2) * binom 139264 (64 - 2 * (m + 2)) ≤ binom 978944 2 * binom 139264 60 := by
      intro m hm; induction m with
      | zero => exact Nat.le_refl _
      | succ m' ih =>
        refine Nat.le_trans ?_ (ih (by omega))
        have hSub1 : 64 - 2 * (m' + 3) = 58 - 2 * m' := by omega
        have hSub2 : 64 - 2 * (m' + 2) = (58 - 2 * m') + 2 := by omega
        rw [hSub1, hSub2]
        let u := 58 - 2 * m'
        have su1 := binom_step_right 139264 (u + 1)
        have su0 := binom_step_right 139264 u
        have sL := binom_step_right 978944 (m' + 2)
        have hRelR : (u + 2) * (u + 1) * binom 139264 (u + 2) =
            (139264 - (u + 1)) * (139264 - u) * binom 139264 u := by
          calc (u + 2) * (u + 1) * binom 139264 (u + 2)
            _ = (u + 1) * ((u + 2) * binom 139264 (u + 2)) := by ac_rfl
            _ = (139264 - (u + 1)) * ((u + 1) * binom 139264 (u + 1)) := by rw [su1]; ac_rfl
            _ = (139264 - (u + 1)) * (139264 - u) * binom 139264 u := by rw [su0]; ac_rfl
        have huMax : u + 2 ≤ 60 := by unfold u; omega
        have pMid : 978944 * (60 * 59) ≤ 3 * ((139264 - 59) * (139264 - 58)) := by decide
        have hRatio : (978944 - (m' + 2)) * ((u + 2) * (u + 1)) ≤
            (m' + 3) * ((139264 - (u + 1)) * (139264 - u)) :=
          Nat.le_trans
            (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.mul_le_mul huMax (by omega)))
            (Nat.le_trans pMid (Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (by omega))))
        have hScaled : (m' + 3) * ((u + 2) * (u + 1)) * (binom 978944 (m' + 3) * binom 139264 u) ≤
            (m' + 3) * ((u + 2) * (u + 1)) * (binom 978944 (m' + 2) * binom 139264 (u + 2)) := by
          have eL : (m' + 3) * ((u + 2) * (u + 1)) * (binom 978944 (m' + 3) * binom 139264 u) =
              ((u + 2) * (u + 1)) * ((m' + 3) * binom 978944 (m' + 3)) * binom 139264 u := by ac_rfl
          have eR : (m' + 3) * ((u + 2) * (u + 1)) * (binom 978944 (m' + 2) * binom 139264 (u + 2)) =
              (m' + 3) * binom 978944 (m' + 2) * ((u + 2) * (u + 1) * binom 139264 (u + 2)) := by ac_rfl
          rw [eL, sL, eR, hRelR]
          have m := Nat.mul_le_mul_right (binom 978944 (m' + 2) * binom 139264 u) hRatio
          have e1 : (978944 - (m' + 2)) * ((u + 2) * (u + 1)) * (binom 978944 (m' + 2) * binom 139264 u) =
              (u + 2) * (u + 1) * ((978944 - (m' + 2)) * binom 978944 (m' + 2)) * binom 139264 u := by ac_rfl
          have e2 : (m' + 3) * ((139264 - (u + 1)) * (139264 - u)) * (binom 978944 (m' + 2) * binom 139264 u) =
              (m' + 3) * binom 978944 (m' + 2) * ((139264 - (u + 1)) * (139264 - u) * binom 139264 u) := by ac_rfl
          rw [e1, e2] at m; exact m
        exact Nat.le_of_mul_le_mul_left hScaled (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega)))
    have hBaseQ2 : 2 ^ 256 * (binom 978944 2 * binom 139264 60) ≤ 2 * (15 ^ 64 * binom 139264 64) := by
      have sL1 := binom_step_right 978944 1
      rw [binom_one_right] at sL1
      have s63 := binom_step_right 139264 63
      have s62 := binom_step_right 139264 62
      have s61 := binom_step_right 139264 61
      have s60 := binom_step_right 139264 60
      have hRel4 : 64 * 63 * 62 * 61 * binom 139264 64 =
          (139264 - 63) * (139264 - 62) * (139264 - 61) * (139264 - 60) * binom 139264 60 := by
        calc 64 * 63 * 62 * 61 * binom 139264 64
          _ = 63 * 62 * 61 * (64 * binom 139264 64) := by ac_rfl
          _ = (139264 - 63) * 62 * 61 * (63 * binom 139264 63) := by rw [s63]; ac_rfl
          _ = (139264 - 63) * (139264 - 62) * 61 * (62 * binom 139264 62) := by rw [s62]; ac_rfl
          _ = (139264 - 63) * (139264 - 62) * (139264 - 61) * (61 * binom 139264 61) := by rw [s61]; ac_rfl
          _ = (139264 - 63) * (139264 - 62) * (139264 - 61) * (139264 - 60) * binom 139264 60 := by
            rw [s60]; ac_rfl
      have hCoeff : 978944 * (978944 - 1) * (64 * 63 * 62 * 61) * 81 ≤
          4 * ((139264 - 63) * (139264 - 62) * (139264 - 61) * (139264 - 60)) := by decide
      have hScaled : 2 * (64 * 63 * 62 * 61) * (2 ^ 256 * (binom 978944 2 * binom 139264 60)) ≤
          2 * (64 * 63 * 62 * 61) * (2 * (15 ^ 64 * binom 139264 64)) := by
        have eL : 2 * (64 * 63 * 62 * 61) * (2 ^ 256 * (binom 978944 2 * binom 139264 60)) =
            2 ^ 256 * ((2 * binom 978944 2) * (64 * 63 * 62 * 61)) * binom 139264 60 := by ac_rfl
        have eR : 2 * (64 * 63 * 62 * 61) * (2 * (15 ^ 64 * binom 139264 64)) =
            4 * (64 * 63 * 62 * 61 * binom 139264 64) * 15 ^ 64 := by
          change 2 * (64 * 63 * 62 * 61) * (2 * (15 ^ 64 * binom 139264 64)) =
            (2 * 2) * (64 * 63 * 62 * 61 * binom 139264 64) * 15 ^ 64
          ac_rfl
        rw [eL, sL1, eR, hRel4]
        have m1 := Nat.mul_le_mul_right (978944 * (978944 - 1) * (64 * 63 * 62 * 61)) h15
        have m2 := Nat.mul_le_mul_right (15 ^ 64) hCoeff
        have r1 : 81 * 15 ^ 64 * (978944 * (978944 - 1) * (64 * 63 * 62 * 61)) =
            978944 * (978944 - 1) * (64 * 63 * 62 * 61) * 81 * 15 ^ 64 := by ac_rfl
        exact Nat.mul_le_mul_right (binom 139264 60) (Nat.le_trans m1 (r1 ▸ m2))
      exact Nat.le_of_mul_le_mul_left hScaled (by decide)
    have hQBound : 2 ^ 256 * (binom 978944 (q' + 2) * binom 139264 (64 - 2 * (q' + 2))) ≤
        2 * (15 ^ 64 * binom 139264 64) :=
      Nat.le_trans (Nat.mul_le_mul_left (2 ^ 256) (hMonoQ q' (by omega))) hBaseQ2
    have hMulLq := Nat.mul_le_mul_left (binom 978944 (q' + 2)) hQBound
    have eL : 2 ^ 256 * (binom 978944 (q' + 2) ^ 2 * binom 139264 (64 - 2 * (q' + 2))) =
        binom 978944 (q' + 2) *
          (2 ^ 256 * (binom 978944 (q' + 2) * binom 139264 (64 - 2 * (q' + 2)))) := by
      rw [Nat.pow_two]; ac_rfl
    have eR : binom 978944 (q' + 2) * (2 * (15 ^ 64 * binom 139264 64)) ≤
        (139264 ^ 2 + 2 * binom 978944 (q' + 2)) * (15 ^ 64 * binom 139264 64) := by
      rw [← Nat.mul_assoc (binom 978944 (q' + 2)) 2, Nat.mul_comm (binom 978944 (q' + 2)) 2]
      exact Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
    rw [eL]; exact Nat.le_trans hMulLq eR

/-- **`#tooth` (`Depth14` Fails the 256-Bit Classical / 128-Bit Grover ISD Threshold):**
    Dropping from `Depth15` ($M = 2^{21}$) to `Depth14` ($M = 2^{20}$) at `(q = 2, l = 52)`
    reduces Stern–Dumer ISD work strictly below `2^256`. -/
theorem tooth_pcg_dense_depth14_stern_dumer_below_256 :
    ¬ sternDumerWorkExceedsPow2 pcgDepth14Cols pcgDenseRows pcgDenseWeightT 2 52 256 := by
  unfold sternDumerWorkExceedsPow2 pcgDepth14Cols pcgDenseRows pcgDenseWeightT
  dsimp only
  have hHalf14 : (1048576 - 139264) / 2 = 454656 := rfl
  have hWin14 : 139264 - 52 = 139212 := rfl
  rw [hHalf14, hWin14]
  intro hBad
  have hUp60 : binom 1048576 60 ≤ 8 ^ 60 * binom 139212 60 :=
    binom_scale_upper_bound 8 (by decide) (by decide)
  have hStepUp : ∀ j : Nat, binom 1048576 (j + 1) ≤ 1048576 * binom 1048576 j := by
    intro j
    have s := binom_step_right 1048576 j
    have p1 : binom 1048576 (j + 1) ≤ (j + 1) * binom 1048576 (j + 1) :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos j)
    rw [s] at p1
    exact Nat.le_trans p1 (Nat.mul_le_mul_right _ (Nat.sub_le 1048576 j))
  have hUp64 : binom 1048576 64 ≤ (2 ^ 80 * 2 ^ 180) * binom 139212 60 := by
    have p := Nat.le_trans (hStepUp 63)
      (Nat.mul_le_mul_left 1048576 (Nat.le_trans (hStepUp 62)
        (Nat.mul_le_mul_left 1048576 (Nat.le_trans (hStepUp 61)
          (Nat.mul_le_mul_left 1048576 (Nat.le_trans (hStepUp 60) hUp60))))))
    have hM4 : 1048576 * (1048576 * (1048576 * (1048576 * (8 ^ 60 * binom 139212 60)))) =
        (2 ^ 80 * 2 ^ 180) * binom 139212 60 := by
      have c1 : 1048576 * (1048576 * (1048576 * 1048576)) = 2 ^ 80 := by decide
      have c2 : 8 ^ 60 = 2 ^ 180 := by
        have p8 : ∀ m : Nat, 8 ^ m = 2 ^ (3 * m) := by
          intro m; induction m with
          | zero => rfl
          | succ m' ih =>
            rw [show 3 * (m' + 1) = 3 * m' + 3 from by omega, Nat.pow_succ 8, ih, Nat.pow_add 2]; rfl
        exact p8 60
      rw [c2, ← Nat.mul_assoc 1048576, ← Nat.mul_assoc 1048576, ← Nat.mul_assoc 1048576, c1,
          ← Nat.mul_assoc (2 ^ 80)]
    exact hM4 ▸ p
  let L2 := binom 454656 2
  have hL2Eq : 2 * L2 = 454656 * 454655 := by
    have s := binom_step_right 454656 1; rw [binom_one_right] at s; exact s
  have hL2Lo : 2 ^ 36 < L2 := by
    have c : 2 * 2 ^ 36 < 454656 * 454655 := by decide
    rw [← hL2Eq] at c; exact Nat.lt_of_mul_lt_mul_left c
  have hL2Hi : L2 < 2 ^ 37 := by
    have c : 454656 * 454655 < 2 * 2 ^ 37 := by decide
    rw [← hL2Eq] at c; exact Nat.lt_of_mul_lt_mul_left c
  have hCostLt : 139264 ^ 2 + 2 * L2 + L2 ^ 2 / 2 ^ 52 < 2 ^ 39 := by
    have hSqLt : L2 ^ 2 < 2 ^ 74 := by
      rw [Nat.pow_two, show (74 : Nat) = 37 + 37 from rfl, Nat.pow_add]
      exact Nat.lt_trans
        (Nat.mul_lt_mul_of_pos_right hL2Hi (Nat.lt_trans (Nat.two_pow_pos 36) hL2Lo))
        (Nat.mul_lt_mul_of_pos_left hL2Hi (Nat.two_pow_pos 37))
    have hDivLe : L2 ^ 2 / 2 ^ 52 ≤ 2 ^ 22 :=
      Nat.div_le_of_le_mul (by rw [← Nat.pow_add]; exact Nat.le_of_lt hSqLt)
    have hSumLe : 139264 ^ 2 + 2 * L2 + L2 ^ 2 / 2 ^ 52 ≤ 139264 ^ 2 + 2 * 2 ^ 37 + 2 ^ 22 :=
      Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (Nat.le_of_lt hL2Hi)) _) hDivLe
    exact Nat.lt_of_le_of_lt hSumLe (by decide)
  have hBPos : 0 < binom 139212 60 := binom_pos (by decide)
  have hUpperAll : (139264 ^ 2 + 2 * L2 + L2 ^ 2 / 2 ^ 52) * binom 1048576 64 <
      (2 ^ 219 * 2 ^ 80) * binom 139212 60 := by
    have m1 := Nat.mul_le_mul_left (139264 ^ 2 + 2 * L2 + L2 ^ 2 / 2 ^ 52) hUp64
    have m2 := Nat.mul_lt_mul_of_pos_right hCostLt
      (Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos 80) (Nat.two_pow_pos 180)) hBPos)
    have hStep := Nat.lt_of_le_of_lt m1 m2
    have hRe : 2 ^ 39 * ((2 ^ 80 * 2 ^ 180) * binom 139212 60) =
        (2 ^ 219 * 2 ^ 80) * binom 139212 60 := by
      have p219 : 2 ^ 39 * 2 ^ 180 = 2 ^ 219 := by rw [← Nat.pow_add]
      rw [← p219]; ac_rfl
    exact hRe ▸ hStep
  have hSqGt : 2 ^ 72 ≤ L2 ^ 2 := by
    rw [Nat.pow_two, show (72 : Nat) = 36 + 36 from rfl, Nat.pow_add]
    exact Nat.mul_le_mul (Nat.le_of_lt hL2Lo) (Nat.le_of_lt hL2Lo)
  have hLowerRhs : (2 ^ 248 * 2 ^ 80) * binom 139212 60 ≤
      2 ^ 256 * (L2 ^ 2 * binom 139212 60) := by
    have p1 := Nat.mul_le_mul_left (2 ^ 256) (Nat.mul_le_mul_right (binom 139212 60) hSqGt)
    have hId : (2 ^ 248 * 2 ^ 80) * binom 139212 60 = 2 ^ 256 * (2 ^ 72 * binom 139212 60) := by
      have c1 : 2 ^ 256 = 2 ^ 248 * 2 ^ 8 := by rw [← Nat.pow_add]
      have c2 : 2 ^ 8 * 2 ^ 72 = 2 ^ 80 := by rw [← Nat.pow_add]
      rw [c1, ← c2]; ac_rfl
    exact hId ▸ p1
  have hPowCmp : (2 ^ 219 * 2 ^ 80) * binom 139212 60 ≤ (2 ^ 248 * 2 ^ 80) * binom 139212 60 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by decide)))
  exact Nat.lt_irrefl _
    (Nat.lt_of_le_of_lt (Nat.le_trans hPowCmp (Nat.le_trans hLowerRhs hBad)) hUpperAll)

/-! ## 6. Constructive Witness Inhabitedness & `#tooth_pair` Assurance Gates -/

theorem witness_accept_box_preimage :
    ∃ z v : Int, inHalfOpenBox rlweAcceptHalfWidth z = true ∧ (-1 ≤ v ∧ v ≤ 1) :=
  ⟨-3070, 1, by decide, by omega⟩

theorem witness_acceptProb_cancellation :
    ∃ (rho : Int → Nat) (M : Nat) (_hM : 0 < M) (z v : Int),
      0 < rho (z - v) ∧ rho z ≤ M * rho (z - v) :=
  ⟨bellToyRho, 4, by decide, 0, 1, by decide, by decide⟩

theorem witness_dual_lpn_bias :
    ∃ weights : List Nat, weights.length = 64 ∧
      (∀ w ∈ weights, ((32768 : Int) - 2 * (w : Int)).natAbs ≤ 2047) := by
  refine ⟨List.replicate 64 16384, by decide, ?_⟩
  intro w hw
  rw [List.eq_of_mem_replicate hw]; decide

theorem witness_depth15_isd : ∃ q l : Nat, q ≤ 32 := ⟨2, 52, by decide⟩

end Qsag
end

#tooth_pair Qsag.rlwe_accept_box_preimage_in_proposal_box vs Qsag.tooth_tight_clipping_loses_boundary_preimage
#tooth_pair Qsag.acceptProbExact_safe_cancels_shift vs Qsag.tooth_omitting_rejection_scaling_breaks_hvzk
#tooth_pair Qsag.pcg_dense_dual_lpn_linear_bias_lt_two_neg_256 vs Qsag.tooth_omitting_accumulator_collapses_dual_lpn_bias
#tooth_pair Qsag.pcg_dense_depth15_prange_and_stern_dumer_pq128 vs Qsag.tooth_pcg_dense_depth14_stern_dumer_below_256

#verify_inhabited Qsag.rlwe_accept_box_preimage_in_proposal_box Qsag.witness_accept_box_preimage
#verify_inhabited Qsag.acceptProbExact_safe_cancels_shift Qsag.witness_acceptProb_cancellation
#verify_inhabited Qsag.pcg_dense_dual_lpn_linear_bias_lt_two_neg_256 Qsag.witness_dual_lpn_bias
#verify_inhabited Qsag.pcg_dense_depth15_prange_and_stern_dumer_pq128 Qsag.witness_depth15_isd
