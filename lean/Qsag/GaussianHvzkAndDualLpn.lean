module
/-
# Qsag.GaussianHvzkAndDualLpn — `Q192` Discrete Gaussian HVZK & Dense Expand-Accumulate Dual-LPN Cryptanalysis

Constructive rational probability, fixed-point rounding, and coding-theoretic work-factor bounds
for the 24-repetition Ring-LWE OR-Sigma proof (`RLWE_ZKPOK_REPS = 24`) and dense expand-accumulate
dual-LPN Pseudorandom Correlation Generator (`PcgTreeDepth.Depth15`):
The probability lemmas below are conditional finite-weight identities. No production
`Q192GaussianSamplerParams` instance, vector sampler refinement, `hUlp` certificate, or
Gaussian tail/normalization bound is supplied here. The abort theorem assumes the two
small single-trial L1 bounds. The linear-test result applies only to the supplied balanced
block weights. Generated rows do not satisfy that premise: `Qsag.DensePcgProductionTaps`
evaluates the tap generator and finds one-row biases near `2^-117` and `2^-89`, and
`Qsag.DensePcgTapLinearTests` replaces the premise by an exact per-row formula and a
second-moment bound over uniform taps. ISD bounds concern the stated Prange/Stern–Dumer
cost formulas, not all decoding algorithms.
1. Fixed-point `Q192` discrete Gaussian rejection-sampling law (`acceptProbExact_safe_cancels_shift`),
   `≤ 2^-190` rounding perturbation (`q192_acceptProb_rounding_le_two_neg_190`), `K`-attempt +
   conditional HVZK simulation (`q192_gaussian_hvzk_statistical_distance`), and `< 2^-128` abort
   indicator marginal secret-independence (`q192_gaussian_abort_marginal_secret_independent`).
2. Expand-accumulate transpose duality (`acc_transpose_duality`), rational Piling-Up Lemmas
   (`piling_up_lemma_bernoulli_rat`, `piling_up_lemma_regular_blocks_rat`), `< 2^-256` dual-LPN
   linear-test bias bounds, and universal Prange / Stern–Dumer ISD `≥ 2^256` (`≥ 2^128` Grover)
   bounds (`pcg_dense_depth15_prange_and_stern_dumer_pq128`).
-/

public import Qsag.Constructive
import all Qsag.Constructive
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag
set_option autoImplicit false

/-! ## 1. Constructive Signed Rationals (`ExactRat`) -/

structure ExactRat where
  num : Int
  den : Nat
  den_pos : 0 < den
  deriving DecidableEq, Repr

@[expose] def ExactRat.ofInt (n : Int) : ExactRat := ⟨n, 1, Nat.one_pos⟩
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
def ExactRat.mul (x y : ExactRat) : ExactRat := ⟨x.num * y.num, x.den * y.den, Nat.mul_pos x.den_pos y.den_pos⟩
def ExactRat.abs (x : ExactRat) : ExactRat := ⟨(x.num.natAbs : Int), x.den, x.den_pos⟩
def ExactRat.scaleNat (k : Nat) (x : ExactRat) : ExactRat := ⟨(k : Int) * x.num, x.den, x.den_pos⟩
def ExactRat.min (x y : ExactRat) : ExactRat := if ExactRat.le x y then x else y
def ExactRat.pow (x : ExactRat) : Nat → ExactRat
  | 0 => ExactRat.ofInt 1
  | n + 1 => ExactRat.mul x (ExactRat.pow x n)

private theorem ExactRat.mul_num (a b : ExactRat) : (a.mul b).num = a.num * b.num := rfl
private theorem ExactRat.mul_den (a b : ExactRat) : (a.mul b).den = a.den * b.den := rfl
private theorem ExactRat.abs_le_twoNegPow {x : ExactRat} {k : Nat} (h : x.num.natAbs * 2 ^ k ≤ x.den) :
    ExactRat.le x.abs (ExactRat.twoNegPow k) := by
  unfold ExactRat.le ExactRat.abs ExactRat.twoNegPow; dsimp only; rw [Int.one_mul, ← Int.natCast_mul]; exact Int.ofNat_le.mpr h
private theorem ExactRat.abs_lt_twoNegPow {x : ExactRat} {k : Nat} (h : x.num.natAbs * 2 ^ k < x.den) :
    ExactRat.lt x.abs (ExactRat.twoNegPow k) := by
  unfold ExactRat.lt ExactRat.abs ExactRat.twoNegPow; dsimp only; rw [Int.one_mul, ← Int.natCast_mul]; exact Int.ofNat_lt.mpr h
private theorem ExactRat.not_lt_twoNegPow_of_gt {x : ExactRat} {k : Nat} (h : x.den < x.num.natAbs * 2 ^ k) :
    ¬ ExactRat.lt x.abs (ExactRat.twoNegPow k) := by
  unfold ExactRat.lt ExactRat.abs ExactRat.twoNegPow; dsimp only; rw [Int.one_mul, ← Int.natCast_mul]
  intro hLt; exact Nat.lt_asymm h (Int.ofNat_lt.mp hLt)
private theorem ExactRat.le_of_nat_mul {x y : ExactRat} {a c : Nat}
    (hx : x.num = (a : Int)) (hy : y.num = (c : Int)) (h : a * y.den ≤ c * x.den) : ExactRat.le x y := by
  unfold ExactRat.le; rw [hx, hy, ← Int.natCast_mul, ← Int.natCast_mul]; exact Int.ofNat_le.mpr h
private theorem nat_mul4_swap (a b c d : Nat) : (a * b) * (c * d) = (a * c) * (b * d) := by ac_rfl
private theorem nat_mul_right_comm (a b c : Nat) : a * b * c = a * c * b := by ac_rfl
private theorem nat_lt_of_mul_lt_left {a b c : Nat} (h : a * b < a * c) : b < c :=
  Decidable.byContradiction fun hN => Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.mul_le_mul_left a (Nat.le_of_not_lt hN)) h)
private theorem nat_lt_of_mul_lt_right {a b c : Nat} (h : b * a < c * a) : b < c :=
  Decidable.byContradiction fun hN => Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right a (Nat.le_of_not_lt hN)) h)

/-! ## 2. Production `24`-Rep Parameters, Exact Rejection Law & Fixed-Point `Q192` Rounding -/

def rlweZkpok24Reps : Nat := 24
def rlweZkpok11ChalBits : Nat := 11
def rlweGaussianSigma : Nat := 700
def rlweGaussianTwoSigmaSq : Nat := 2 * rlweGaussianSigma ^ 2
def rlweProposalHalfWidth : Nat := 3072
def rlweAcceptHalfWidth : Nat := 3070
def rlweSingleRepScaleM : Nat := 24
def rlweJoint24RepScaleM : Nat := 40

theorem rlwe_24rep_pq128_soundness_bits :
    rlweZkpok24Reps * rlweZkpok11ChalBits = 264 ∧ (rlweZkpok24Reps * rlweZkpok11ChalBits) / 2 = 132 ∧
    128 ≤ (rlweZkpok24Reps * rlweZkpok11ChalBits) / 2 ∧ rlweGaussianTwoSigmaSq = 980000 := by decide

def inHalfOpenBox (half : Nat) (x : Int) : Bool := decide (-(half : Int) ≤ x ∧ x < (half : Int))

theorem rlwe_accept_box_preimage_in_proposal_box (z v : Int)
    (hz : inHalfOpenBox rlweAcceptHalfWidth z = true) (hvLo : -1 ≤ v) (hvHi : v ≤ 1) :
    inHalfOpenBox rlweProposalHalfWidth (z - v) = true := by
  have ⟨hzLo, hzHi⟩ := of_decide_eq_true hz; apply decide_eq_true
  unfold rlweAcceptHalfWidth rlweProposalHalfWidth at *; constructor <;> omega

theorem tooth_tight_clipping_loses_boundary_preimage :
    ∃ z v : Int, inHalfOpenBox rlweAcceptHalfWidth z = true ∧ (-1 ≤ v) ∧ (v ≤ 1) ∧
      inHalfOpenBox rlweAcceptHalfWidth (z - v) = false :=
  ⟨-3070, 1, by decide, by decide, by decide, by decide⟩

def acceptProbExact (rho : Int → Nat) (M : Nat) (z v : Int) : ExactRat :=
  let den := M * rho (z - v)
  if hPos : 0 < den then ExactRat.min (ExactRat.ofInt 1) ⟨(rho z : Int), den, hPos⟩ else ExactRat.ofInt 0

theorem acceptProbExact_safe_cancels_shift (rho : Int → Nat) (M : Nat) (hM : 0 < M)
    (z v : Int) (hRhoPos : 0 < rho (z - v)) (hSafe : rho z ≤ M * rho (z - v)) :
    ExactRat.eqv (ExactRat.scaleNat (rho (z - v)) (acceptProbExact rho M z v)) ⟨(rho z : Int), M, hM⟩ := by
  have hDenPos : 0 < M * rho (z - v) := Nat.mul_pos hM hRhoPos
  unfold acceptProbExact; simp only [hDenPos, dite_true, ExactRat.min]; split
  · next hOneLe =>
    unfold ExactRat.le ExactRat.ofInt at hOneLe; dsimp only at hOneLe
    have hEqNat : rho z = M * rho (z - v) := by omega
    unfold ExactRat.scaleNat ExactRat.ofInt ExactRat.eqv; dsimp only; rw [hEqNat, Int.natCast_mul]; ac_rfl
  · unfold ExactRat.scaleNat ExactRat.eqv; dsimp only; rw [Int.natCast_mul]; ac_rfl

def bellToyRho (y : Int) : Nat := if y = 0 then 4 else if y.natAbs = 1 then 3 else if y.natAbs = 2 then 1 else 0

theorem tooth_omitting_rejection_scaling_breaks_hvzk :
    ¬ ExactRat.eqv (ExactRat.scaleNat (bellToyRho (0 - 0)) (acceptProbExact bellToyRho 1 0 0))
      (ExactRat.scaleNat (bellToyRho (0 - 1)) (acceptProbExact bellToyRho 1 0 1)) := by decide

def q192ToRat (w : Nat) : ExactRat := ⟨(w : Int), 2 ^ 192, Nat.two_pow_pos 192⟩
def acceptProbQ192FloorNum (rho : Int → Nat) (M : Nat) (z v : Int) : Nat :=
  let den := M * rho (z - v)
  if den = 0 then 0 else min (2 ^ 192) ((rho z * (2 ^ 192)) / den)
def acceptProbQ192 (rho : Int → Nat) (M : Nat) (z v : Int) : ExactRat := q192ToRat (acceptProbQ192FloorNum rho M z v)

private theorem q192_scaled_err_le_four_den (rz den W qNum : Nat)
    (hUlp : ((qNum : Int) - ((if den = 0 then 0 else min W ((rz * W) / den) : Nat) : Int)).natAbs ≤ 3) :
    ((qNum : Int) * (den : Int) - ((W * min den rz : Nat) : Int)).natAbs ≤ 4 * den := by
  by_cases hZero : den = 0
  · simp only [hZero, Nat.zero_min, Nat.mul_zero, Int.natCast_zero, Int.mul_zero, Int.sub_self, Int.natAbs_zero]
    exact Nat.le_refl 0
  · have hDenPos : 0 < den := Nat.pos_of_ne_zero hZero
    simp only [hZero, ↓reduceIte] at hUlp
    by_cases hClip : den ≤ rz
    · have hGe : W ≤ (rz * W) / den := (Nat.le_div_iff_mul_le hDenPos).mpr
        (by rw [Nat.mul_comm W den]; exact Nat.mul_le_mul_right W hClip)
      rw [Nat.min_eq_left hGe] at hUlp
      rw [Nat.min_eq_left hClip, Int.natCast_mul, ← Int.sub_mul, Int.natAbs_mul, Int.natAbs_natCast]
      exact Nat.le_trans (Nat.mul_le_mul_right den hUlp) (Nat.mul_le_mul_right den (by decide))
    · have hLt : rz < den := Nat.lt_of_not_le hClip
      have hDivLe : (rz * W) / den ≤ W := Nat.div_le_of_le_mul (Nat.mul_le_mul_right W (Nat.le_of_lt hLt))
      rw [Nat.min_eq_right hDivLe] at hUlp; rw [Nat.min_eq_right (Nat.le_of_lt hLt)]
      let q0 := (rz * W) / den; let r0 := (rz * W) % den
      have hDMI : (q0 : Int) * (den : Int) + (r0 : Int) = ((W * rz : Nat) : Int) := by
        rw [← Int.natCast_mul, ← Int.natCast_add, Nat.mul_comm q0 den, Nat.mul_comm W rz, Nat.div_add_mod]
      rw [show (qNum : Int) * (den : Int) - ((W * rz : Nat) : Int) =
          ((qNum : Int) - (q0 : Int)) * (den : Int) - (r0 : Int) from by rw [← hDMI, Int.sub_mul]; omega]
      have hTri := Int.natAbs_sub_le (((qNum : Int) - (q0 : Int)) * (den : Int)) (r0 : Int)
      rw [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast] at hTri
      have hMod : r0 ≤ den := Nat.le_of_lt (Nat.mod_lt (rz * W) hDenPos)
      have hSum := Nat.add_le_add (Nat.mul_le_mul_right den hUlp) hMod
      exact Nat.le_trans hTri ((by omega : 3 * den + den = 4 * den) ▸ hSum)

private theorem q192_rounding_core (rz den U qNum : Nat) (hUPos : 0 < U)
    (hUlp : ((qNum : Int) - ((if den = 0 then 0 else min (4 * U) ((rz * (4 * U)) / den) : Nat) : Int)).natAbs ≤ 3) :
    let ex : ExactRat := if hPos : 0 < den then ExactRat.min (ExactRat.ofInt 1) ⟨(rz : Int), den, hPos⟩ else ExactRat.ofInt 0
    let qRat : ExactRat := ⟨(qNum : Int), 4 * U, Nat.mul_pos (by decide) hUPos⟩
    (qRat.sub ex).num.natAbs * U ≤ (qRat.sub ex).den := by
  intro ex qRat
  by_cases hZero : den = 0
  · have hNotPos : ¬ (0 < den) := by omega
    simp only [hZero, ↓reduceIte] at hUlp; unfold ex qRat ExactRat.sub ExactRat.ofInt; simp only [hNotPos, dite_false]
    rw [show ((qNum : Int) * (1 : Nat) - 0 * ((4 * U : Nat) : Int)).natAbs = qNum from by omega, Nat.mul_one]
    exact Nat.mul_le_mul_right U (by omega)
  · have hDenPos : 0 < den := Nat.pos_of_ne_zero hZero
    have hErr := q192_scaled_err_le_four_den rz den (4 * U) qNum hUlp
    unfold ex qRat ExactRat.sub ExactRat.min; simp only [hDenPos, dite_true]; split
    · next hOneLe =>
      unfold ExactRat.le ExactRat.ofInt at hOneLe; dsimp only at hOneLe
      have hGe : 4 * U ≤ (rz * (4 * U)) / den := (Nat.le_div_iff_mul_le hDenPos).mpr
        (by rw [Nat.mul_comm (4 * U) den]; exact Nat.mul_le_mul_right (4 * U) (by omega))
      simp only [hZero, ↓reduceIte, Nat.min_eq_left hGe] at hUlp
      unfold ExactRat.ofInt; dsimp only; rw [Nat.mul_one]; exact Nat.mul_le_mul_right U (by omega)
    · next hNotOneLe =>
      unfold ExactRat.le ExactRat.ofInt at hNotOneLe; dsimp only at hNotOneLe
      rw [Nat.min_eq_right (by omega : rz ≤ den), Nat.mul_comm (4 * U) rz, Int.natCast_mul] at hErr; dsimp only
      have hMul := Nat.mul_le_mul_right U hErr; rw [nat_mul_right_comm 4 den U] at hMul; exact hMul

theorem q192_acceptProb_rounding_le_two_neg_190 (rho : Int → Nat) (M : Nat) (z v : Int) (qNum : Nat)
    (hUlp : ((qNum : Int) - (acceptProbQ192FloorNum rho M z v : Int)).natAbs ≤ 3) :
    ExactRat.le (ExactRat.abs (ExactRat.sub (q192ToRat qNum) (acceptProbExact rho M z v))) (ExactRat.twoNegPow 190) := by
  apply ExactRat.abs_le_twoNegPow
  have hPow : (2 : Nat) ^ 192 = 4 * 2 ^ 190 := by rw [show (192 : Nat) = 2 + 190 from rfl, Nat.pow_add]
  unfold acceptProbQ192FloorNum at hUlp; unfold q192ToRat acceptProbExact; simp only [hPow] at hUlp ⊢
  exact q192_rounding_core (rho z) (M * rho (z - v)) (2 ^ 190) qNum (Nat.two_pow_pos 190) hUlp

/-! ## 3. Constructive `K`-Attempt & Conditional HVZK Transcript Simulation + Abort Independence -/

def natSumList {α : Type} : List α → (α → Nat) → Nat
  | [], _ => 0
  | x :: tl, f => f x + natSumList tl f

private theorem natSumList_zero {α : Type} : ∀ xs : List α, natSumList xs (fun _ => 0) = 0
  | [] => rfl
  | _ :: tl => by simp only [natSumList, Nat.zero_add, natSumList_zero tl]

def retryWeight {α : Type} : Nat → Nat → Nat → (α → Nat) → α → Nat
  | 0, _, _, _, _ => 0
  | K + 1, D, R, w, x => w x * (D ^ K) + R * retryWeight K D R w x

theorem retryWeight_sum_add_abort_eq_pow {α : Type} (xs : List α) (D : Nat) (w : α → Nat) (hSub : natSumList xs w ≤ D) :
    ∀ K : Nat, natSumList xs (retryWeight K D (D - natSumList xs w) w) + (D - natSumList xs w) ^ K = D ^ K
  | 0 => by have hZ : retryWeight 0 D (D - natSumList xs w) w = (fun _ => 0) := rfl; rw [hZ, natSumList_zero]; rfl
  | K + 1 => by
    let R := D - natSumList xs w
    have hSplit : ∀ ys : List α, natSumList ys (retryWeight (K + 1) D R w) =
        natSumList ys w * (D ^ K) + R * natSumList ys (retryWeight K D R w) := by
      intro ys; induction ys with
      | nil => simp only [natSumList, Nat.zero_mul, Nat.mul_zero, Nat.add_zero]
      | cons _ _ ih => simp only [natSumList, retryWeight] at ih ⊢; rw [ih, Nat.add_mul, Nat.mul_add]; ac_rfl
    rw [hSplit xs, Nat.pow_succ' (n := K), Nat.add_assoc, ← Nat.mul_add R,
        retryWeight_sum_add_abort_eq_pow xs D w hSub K, ← Nat.add_mul, Nat.add_sub_of_le hSub, Nat.pow_succ']

def natL1Diff {α : Type} (xs : List α) (f g : α → Nat) : Nat := natSumList xs (fun x => ((f x : Int) - (g x : Int)).natAbs)

private theorem natL1Diff_self {α : Type} : ∀ (xs : List α) (f : α → Nat), natL1Diff xs f f = 0
  | [], _ => rfl
  | _ :: tl, f => by unfold natL1Diff; dsimp only [natSumList]; rw [Int.sub_self, Int.natAbs_zero, Nat.zero_add]; exact natL1Diff_self tl f

private theorem natSumList_diff_le_l1 {α : Type} (xs : List α) (f g : α → Nat) :
    ((natSumList xs f : Int) - (natSumList xs g : Int)).natAbs ≤ natL1Diff xs f g := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x tl ih =>
    unfold natL1Diff at ih ⊢; simp only [natSumList]
    rw [show ((f x + natSumList tl f : Nat) : Int) - ((g x + natSumList tl g : Nat) : Int) =
        ((f x : Int) - (g x : Int)) + ((natSumList tl f : Int) - (natSumList tl g : Int)) from by omega]
    exact Nat.le_trans (Int.natAbs_add_le _ _) (Nat.add_le_add_left ih _)

private theorem natL1_retry_step {α : Type} (xs : List α) (D R1 R2 : Nat) (w1 w2 : α → Nat) (K : Nat) :
    natL1Diff xs (retryWeight (K + 1) D R1 w1) (retryWeight (K + 1) D R2 w2) ≤
      natL1Diff xs w1 w2 * (D ^ K) + R1 * natL1Diff xs (retryWeight K D R1 w1) (retryWeight K D R2 w2) +
      ((R1 : Int) - (R2 : Int)).natAbs * natSumList xs (retryWeight K D R2 w2) := by
  induction xs with
  | nil => simp only [natL1Diff, natSumList, Nat.zero_mul, Nat.mul_zero, Nat.add_zero]; exact Nat.le_refl 0
  | cons x tl ih =>
    unfold natL1Diff at ih ⊢; simp only [natSumList, retryWeight]
    let u1 := retryWeight K D R1 w1 x; let u2 := retryWeight K D R2 w2 x; let P := D ^ K
    have hPt : (((w1 x * P + R1 * u1 : Nat) : Int) - ((w2 x * P + R2 * u2 : Nat) : Int)).natAbs ≤
        ((w1 x : Int) - (w2 x : Int)).natAbs * P + R1 * ((u1 : Int) - (u2 : Int)).natAbs +
        ((R1 : Int) - (R2 : Int)).natAbs * u2 := by
      rw [show ((w1 x * P + R1 * u1 : Nat) : Int) - ((w2 x * P + R2 * u2 : Nat) : Int) =
          ((w1 x : Int) - (w2 x : Int)) * (P : Int) + (R1 : Int) * ((u1 : Int) - (u2 : Int)) +
          ((R1 : Int) - (R2 : Int)) * (u2 : Int) from by simp only [Int.natCast_add, Int.natCast_mul, Int.sub_mul, Int.mul_sub]; omega]
      have a1 := Int.natAbs_add_le (((w1 x : Int) - (w2 x : Int)) * (P : Int) + (R1 : Int) * ((u1 : Int) - (u2 : Int)))
        (((R1 : Int) - (R2 : Int)) * (u2 : Int))
      have a2 := Int.natAbs_add_le (((w1 x : Int) - (w2 x : Int)) * (P : Int)) ((R1 : Int) * ((u1 : Int) - (u2 : Int)))
      simp only [Int.natAbs_mul, Int.natAbs_natCast] at a1 a2; exact Nat.le_trans a1 (Nat.add_le_add_right a2 _)
    have hSum := Nat.add_le_add hPt ih
    have hRhs : ∀ a1 a2 b1 b2 c1 c2 : Nat,
        (a1 * P + R1 * b1 + ((R1 : Int) - (R2 : Int)).natAbs * c1) + (a2 * P + R1 * b2 + ((R1 : Int) - (R2 : Int)).natAbs * c2) =
        (a1 + a2) * P + R1 * (b1 + b2) + ((R1 : Int) - (R2 : Int)).natAbs * (c1 + c2) :=
      fun _ _ _ _ _ _ => by rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; ac_rfl
    rw [hRhs] at hSum; exact hSum

private theorem sub_sub_natAbs_eq {M a b : Nat} (ha : a ≤ M) (hb : b ≤ M) :
    (((M - a : Nat) : Int) - ((M - b : Nat) : Int)).natAbs = ((a : Int) - (b : Int)).natAbs := by omega

private theorem abort_pow_step_le (R1 R2 P1 P2 : Nat) :
    (((R1 * P1 : Nat) : Int) - ((R2 * P2 : Nat) : Int)).natAbs ≤
      R1 * ((P1 : Int) - (P2 : Int)).natAbs + ((R1 : Int) - (R2 : Int)).natAbs * P2 := by
  rw [show ((R1 * P1 : Nat) : Int) - ((R2 * P2 : Nat) : Int) =
      (R1 : Int) * ((P1 : Int) - (P2 : Int)) + ((R1 : Int) - (R2 : Int)) * (P2 : Int) from by
    simp only [Int.natCast_mul, Int.mul_sub, Int.sub_mul]; omega]
  simpa only [Int.natAbs_mul, Int.natAbs_natCast] using
    Int.natAbs_add_le ((R1 : Int) * ((P1 : Int) - (P2 : Int))) (((R1 : Int) - (R2 : Int)) * (P2 : Int))

theorem retry_full_l1_le_two_K_mul_single {α : Type} (xs : List α) (D : Nat)
    (w1 w2 : α → Nat) (hSub1 : natSumList xs w1 ≤ D) (hSub2 : natSumList xs w2 ≤ D) :
    ∀ K : Nat, let R1 := D - natSumList xs w1; let R2 := D - natSumList xs w2
      (natL1Diff xs (retryWeight K D R1 w1) (retryWeight K D R2 w2) +
        (((R1 ^ K : Nat) : Int) - ((R2 ^ K : Nat) : Int)).natAbs) * D ≤ 2 * K * natL1Diff xs w1 w2 * (D ^ K)
  | 0 => by
    intro R1 R2; have hZ1 : retryWeight 0 D R1 w1 = (fun _ => 0) := rfl; have hZ2 : retryWeight 0 D R2 w2 = (fun _ => 0) := rfl
    rw [hZ1, hZ2, natL1Diff_self xs (fun _ => 0)]
    simp only [Nat.pow_zero, Int.sub_self, Int.natAbs_zero, Nat.add_zero, Nat.zero_mul]; exact Nat.zero_le _
  | K + 1 => by
    intro R1 R2; have ih := retry_full_l1_le_two_K_mul_single xs D w1 w2 hSub1 hSub2 K; dsimp only at ih
    have hRDiff : ((R1 : Int) - (R2 : Int)).natAbs ≤ natL1Diff xs w1 w2 := by
      rw [sub_sub_natAbs_eq hSub1 hSub2]; exact natSumList_diff_le_l1 xs w1 w2
    have hAbLe : (((R1 ^ (K + 1) : Nat) : Int) - ((R2 ^ (K + 1) : Nat) : Int)).natAbs ≤
        R1 * (((R1 ^ K : Nat) : Int) - ((R2 ^ K : Nat) : Int)).natAbs + ((R1 : Int) - (R2 : Int)).natAbs * R2 ^ K := by
      rw [Nat.pow_succ' (n := K), Nat.pow_succ' (n := K)]; exact abort_pow_step_le R1 R2 (R1 ^ K) (R2 ^ K)
    let LK := natL1Diff xs (retryWeight K D R1 w1) (retryWeight K D R2 w2)
    let AK := (((R1 ^ K : Nat) : Int) - ((R2 ^ K : Nat) : Int)).natAbs
    have hAdd := Nat.add_le_add (natL1_retry_step xs D R1 R2 w1 w2 K) hAbLe
    have hRe : ∀ d1 P dR SK : Nat, (d1 * P + R1 * LK + dR * SK) + (R1 * AK + dR * R2 ^ K) =
        (d1 * P + dR * (SK + R2 ^ K)) + R1 * (LK + AK) := fun _ _ _ _ => by rw [Nat.mul_add, Nat.mul_add]; ac_rfl
    rw [hRe, retryWeight_sum_add_abort_eq_pow xs D w2 hSub2 K] at hAdd
    have p1 : natL1Diff xs w1 w2 * D ^ K + ((R1 : Int) - (R2 : Int)).natAbs * D ^ K ≤ 2 * natL1Diff xs w1 w2 * D ^ K := by
      have m := Nat.add_le_add_left (Nat.mul_le_mul_right (D ^ K) hRDiff) (natL1Diff xs w1 w2 * D ^ K)
      rw [← Nat.two_mul, ← Nat.mul_assoc] at m; exact m
    have hMulD := Nat.mul_le_mul_right D (Nat.le_trans hAdd (Nat.add_le_add p1 (Nat.mul_le_mul_right (LK + AK) (Nat.sub_le D _))))
    have hRhs1 : ∀ X Y : Nat, (X + D * Y) * D = X * D + D * (Y * D) := fun _ _ => by rw [Nat.add_mul, Nat.mul_assoc]
    rw [hRhs1] at hMulD
    have hStep2 := Nat.le_trans hMulD (Nat.add_le_add_left (Nat.mul_le_mul_left D ih) _)
    have hRhs2 : ∀ d P : Nat, 2 * d * P * D + D * (2 * K * d * P) = 2 * (K + 1) * d * (P * D) :=
      fun _ _ => by rw [Nat.mul_add 2 K 1, Nat.mul_one, Nat.add_mul, Nat.add_mul]; ac_rfl
    rw [Nat.pow_succ]; exact hRhs2 _ _ ▸ hStep2

theorem retry_abort_diff_le_K_mul_single {α : Type} (xs : List α) (D : Nat)
    (w1 w2 : α → Nat) (hSub1 : natSumList xs w1 ≤ D) (hSub2 : natSumList xs w2 ≤ D) :
    ∀ K : Nat, let R1 := D - natSumList xs w1; let R2 := D - natSumList xs w2
      (((R1 ^ K : Nat) : Int) - ((R2 ^ K : Nat) : Int)).natAbs * D ≤ K * natL1Diff xs w1 w2 * (D ^ K)
  | 0 => by intro _ _; simp only [Nat.pow_zero, Int.sub_self, Int.natAbs_zero, Nat.zero_mul]; exact Nat.zero_le _
  | K + 1 => by
    intro R1 R2; have ih := retry_abort_diff_le_K_mul_single xs D w1 w2 hSub1 hSub2 K; dsimp only at ih
    have hRDiff : ((R1 : Int) - (R2 : Int)).natAbs ≤ natL1Diff xs w1 w2 := by
      rw [sub_sub_natAbs_eq hSub1 hSub2]; exact natSumList_diff_le_l1 xs w1 w2
    have hAb := abort_pow_step_le R1 R2 (R1 ^ K) (R2 ^ K)
    rw [← Nat.pow_succ' (n := K), ← Nat.pow_succ' (n := K)] at hAb
    have hMulD := Nat.mul_le_mul_right D (Nat.le_trans hAb (Nat.add_le_add
      (Nat.mul_le_mul_right _ (Nat.sub_le D _)) (Nat.mul_le_mul hRDiff (Nat.pow_le_pow_left (Nat.sub_le D _) K))))
    rw [Nat.add_mul, Nat.mul_assoc D _ D] at hMulD
    have hStep2 := Nat.le_trans hMulD (Nat.add_le_add_right (Nat.mul_le_mul_left D ih) _)
    have hRhs : ∀ d P : Nat, D * (K * d * P) + d * P * D = (K + 1) * d * (P * D) :=
      fun _ _ => by rw [Nat.add_mul K 1, Nat.one_mul, Nat.add_mul]; ac_rfl
    rw [Nat.pow_succ]; exact hRhs _ _ ▸ hStep2

theorem conditional_accepted_l1_le_two_mul_single {α : Type} (xs : List α) (w1 w2 : α → Nat) :
    let A1 := natSumList xs w1; let A2 := natSumList xs w2
    natSumList xs (fun x => ((w1 x * A2 : Int) - (w2 x * A1 : Int)).natAbs) ≤ 2 * A1 * natL1Diff xs w1 w2 := by
  intro A1 A2
  have hDiffA : ((A2 : Int) - (A1 : Int)).natAbs ≤ natL1Diff xs w1 w2 :=
    (by omega : ((A2 : Int) - (A1 : Int)).natAbs = ((A1 : Int) - (A2 : Int)).natAbs) ▸ natSumList_diff_le_l1 xs w1 w2
  have hGen : ∀ ys : List α, natSumList ys (fun x => ((w1 x * A2 : Int) - (w2 x * A1 : Int)).natAbs) ≤
      A1 * natL1Diff ys w1 w2 + natSumList ys w1 * ((A2 : Int) - (A1 : Int)).natAbs := by
    intro ys; induction ys with
    | nil => simp only [natSumList, natL1Diff, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]; exact Nat.le_refl 0
    | cons x tl ih =>
      unfold natL1Diff at ih ⊢; simp only [natSumList]
      have hPt : ((w1 x * A2 : Int) - (w2 x * A1 : Int)).natAbs ≤
          A1 * ((w1 x : Int) - (w2 x : Int)).natAbs + w1 x * ((A2 : Int) - (A1 : Int)).natAbs := by
        rw [show (w1 x * A2 : Int) - (w2 x * A1 : Int) =
            ((w1 x : Int) - (w2 x : Int)) * (A1 : Int) + (w1 x : Int) * ((A2 : Int) - (A1 : Int)) from by rw [Int.sub_mul, Int.mul_sub]; omega]
        have b := Int.natAbs_add_le (((w1 x : Int) - (w2 x : Int)) * (A1 : Int)) ((w1 x : Int) * ((A2 : Int) - (A1 : Int)))
        simp only [Int.natAbs_mul, Int.natAbs_natCast] at b; rw [Nat.mul_comm _ A1] at b; exact b
      have hSum := Nat.add_le_add hPt ih
      have hRhs : ∀ d1 d2 s1 dA : Nat, (A1 * d1 + w1 x * dA) + (A1 * d2 + s1 * dA) = A1 * (d1 + d2) + (w1 x + s1) * dA :=
        fun _ _ _ _ => by rw [Nat.mul_add, Nat.add_mul]; ac_rfl
      rw [hRhs] at hSum; exact hSum
  have hStep := Nat.le_trans (hGen xs) (Nat.add_le_add_left (Nat.mul_le_mul_left A1 hDiffA) _)
  rw [← Nat.two_mul, ← Nat.mul_assoc] at hStep; exact hStep

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
theorem Q192GaussianSamplerParams.trialDenom_pos (P : Q192GaussianSamplerParams) : 0 < P.trialDenom :=
  Nat.mul_pos (Nat.mul_pos (Nat.mul_pos P.challenges_nonempty P.zProp_pos) P.scaleM_pos) (Nat.two_pow_pos 192)
def prodPairs {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  xs.foldr (fun x acc => ys.map (fun y => (x, y)) ++ acc) []
def realQ192TrialWeight (P : Q192GaussianSamplerParams) (shift : Nat → Int) (q192Num : Int → Int → Nat) (cz : Nat × Int) : Nat :=
  P.scaleM * P.rho (cz.2 - shift cz.1) * q192Num cz.2 (shift cz.1)
def idealSimTrialWeight (P : Q192GaussianSamplerParams) (cz : Nat × Int) : Nat := (2 ^ 192) * P.rho cz.2
def tailDeficitAt (P : Q192GaussianSamplerParams) (shift : Nat → Int) (cz : Nat × Int) : Nat :=
  P.rho cz.2 - min (P.scaleM * P.rho (cz.2 - shift cz.1)) (P.rho cz.2)
def tailMassRat (P : Q192GaussianSamplerParams) (shift : Nat → Int) : ExactRat :=
  ⟨(natSumList (prodPairs P.challenges P.support) (tailDeficitAt P shift) : Int),
   P.challenges.length * P.zProp * P.scaleM, Nat.mul_pos (Nat.mul_pos P.challenges_nonempty P.zProp_pos) P.scaleM_pos⟩

def q192RetryTranscriptTv (P : Q192GaussianSamplerParams) (shift : Nat → Int) (q192Num : Int → Int → Nat) (K : Nat) : ExactRat :=
  let pts := prodPairs P.challenges P.support; let D := P.trialDenom
  let wReal := realQ192TrialWeight P shift q192Num; let wSim := idealSimTrialWeight P
  let R1 := D - natSumList pts wReal; let R2 := D - natSumList pts wSim
  ⟨(natL1Diff pts (retryWeight K D R1 wReal) (retryWeight K D R2 wSim) + (((R1 ^ K : Nat) : Int) - ((R2 ^ K : Nat) : Int)).natAbs : Int),
   2 * (D ^ K), Nat.mul_pos (by decide) (Nat.pow_pos P.trialDenom_pos)⟩

def q192ConditionalAcceptedTv (P : Q192GaussianSamplerParams) (shift : Nat → Int) (q192Num : Int → Int → Nat)
    (hRealPos : 0 < natSumList (prodPairs P.challenges P.support) (realQ192TrialWeight P shift q192Num))
    (hSimPos : 0 < natSumList (prodPairs P.challenges P.support) (idealSimTrialWeight P)) : ExactRat :=
  let pts := prodPairs P.challenges P.support
  let wReal := realQ192TrialWeight P shift q192Num; let wSim := idealSimTrialWeight P
  let A1 := natSumList pts wReal; let A2 := natSumList pts wSim
  ⟨(natSumList pts (fun x => ((wReal x * A2 : Int) - (wSim x * A1 : Int)).natAbs) : Int),
   2 * A1 * A2, Nat.mul_pos (Nat.mul_pos (by decide) hRealPos) hSimPos⟩

private theorem natSumList_append {α : Type} (xs ys : List α) (f : α → Nat) :
    natSumList (xs ++ ys) f = natSumList xs f + natSumList ys f := by
  induction xs with
  | nil => simp only [List.nil_append, natSumList, Nat.zero_add]
  | cons _ _ ih => simp only [List.cons_append, natSumList, ih, Nat.add_assoc]

private theorem natL1_single_trial_gen (P : Q192GaussianSamplerParams) (shift : Nat → Int)
    (q192Num : Int → Int → Nat) (W : Nat) (hRhoLe : ∀ z : Int, P.rho z ≤ P.zProp)
    (hUlp : ∀ c z, ((q192Num z (shift c) : Int) -
      ((if P.scaleM * P.rho (z - shift c) = 0 then 0 else min W ((P.rho z * W) / (P.scaleM * P.rho (z - shift c))) : Nat) : Int)).natAbs ≤ 3) :
    natL1Diff (prodPairs P.challenges P.support) (realQ192TrialWeight P shift q192Num) (fun cz => W * P.rho cz.2) ≤
      W * natSumList (prodPairs P.challenges P.support) (tailDeficitAt P shift) +
      4 * P.challenges.length * P.zProp * P.scaleM * P.support.length := by
  have hPt : ∀ cz : Nat × Int, (((realQ192TrialWeight P shift q192Num cz : Nat) : Int) -
      ((W * P.rho cz.2 : Nat) : Int)).natAbs ≤ W * tailDeficitAt P shift cz + 4 * P.scaleM * P.zProp := by
    intro ⟨c, z⟩; unfold realQ192TrialWeight tailDeficitAt; dsimp only
    let mRho := P.scaleM * P.rho (z - shift c); let minVal := min mRho (P.rho z)
    have hErr := q192_scaled_err_le_four_den (P.rho z) mRho W (q192Num z (shift c)) (hUlp c z)
    have hWDecomp : W * P.rho z = W * minVal + W * (P.rho z - minVal) := by
      rw [← Nat.mul_add, Nat.add_sub_of_le (Nat.min_le_right _ _)]
    change (((mRho * q192Num z (shift c) : Nat) : Int) - ((W * P.rho z : Nat) : Int)).natAbs ≤ _
    rw [show ((mRho * q192Num z (shift c) : Nat) : Int) - ((W * P.rho z : Nat) : Int) =
        ((q192Num z (shift c) : Int) * (mRho : Int) - ((W * minVal : Nat) : Int)) - ((W * (P.rho z - minVal) : Nat) : Int) from by
      rw [Nat.mul_comm mRho, hWDecomp, Int.natCast_mul (q192Num z (shift c)), Int.natCast_add]; omega]
    have hTri := Int.natAbs_sub_le ((q192Num z (shift c) : Int) * (mRho : Int) - ((W * minVal : Nat) : Int))
      ((W * (P.rho z - minVal) : Nat) : Int)
    rw [Int.natAbs_natCast] at hTri
    have hB4 : 4 * mRho ≤ 4 * P.scaleM * P.zProp := by rw [← Nat.mul_assoc 4 P.scaleM]; exact Nat.mul_le_mul_left _ (hRhoLe _)
    have hStep := Nat.le_trans hTri (Nat.add_le_add_right (Nat.le_trans hErr hB4) _)
    rw [Nat.add_comm] at hStep; exact hStep
  have hInner : ∀ (c : Nat) (zs : List Int),
      natL1Diff (zs.map (fun z => (c, z))) (realQ192TrialWeight P shift q192Num) (fun cz => W * P.rho cz.2) ≤
      W * natSumList (zs.map (fun z => (c, z))) (tailDeficitAt P shift) + 4 * P.scaleM * P.zProp * zs.length := by
    intro c zs; induction zs with
    | nil => simp only [List.map, natL1Diff, natSumList, List.length, Nat.mul_zero, Nat.add_zero]; exact Nat.le_refl 0
    | cons z tl ih =>
      unfold natL1Diff at ih ⊢; simp only [List.map, natSumList, List.length]
      have hAdd := Nat.add_le_add (hPt (c, z)) ih
      have hR : ∀ t1 t2 n : Nat, (W * t1 + 4 * P.scaleM * P.zProp) + (W * t2 + 4 * P.scaleM * P.zProp * n) =
          W * (t1 + t2) + 4 * P.scaleM * P.zProp * (n + 1) :=
        fun _ _ _ => by rw [Nat.mul_add W, Nat.mul_add (4 * P.scaleM * P.zProp), Nat.mul_one]; ac_rfl
      rw [hR] at hAdd; exact hAdd
  have hOuter : ∀ cs : List Nat,
      natL1Diff (prodPairs cs P.support) (realQ192TrialWeight P shift q192Num) (fun cz => W * P.rho cz.2) ≤
      W * natSumList (prodPairs cs P.support) (tailDeficitAt P shift) + 4 * cs.length * P.zProp * P.scaleM * P.support.length := by
    intro cs; induction cs with
    | nil => simp only [prodPairs, List.foldr, natL1Diff, natSumList, List.length, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]; exact Nat.le_refl 0
    | cons c tl ih =>
      simp only [prodPairs, List.foldr, List.length] at ih ⊢; unfold natL1Diff at ih ⊢
      rw [natSumList_append, natSumList_append]
      have hAdd := Nat.add_le_add (hInner c P.support) ih
      have hR : ∀ t1 t2 n : Nat, (W * t1 + 4 * P.scaleM * P.zProp * P.support.length) +
          (W * t2 + 4 * n * P.zProp * P.scaleM * P.support.length) =
          W * (t1 + t2) + 4 * (n + 1) * P.zProp * P.scaleM * P.support.length :=
        fun _ _ _ => by rw [Nat.mul_add W, Nat.mul_add 4 _ 1, Nat.mul_one, Nat.add_mul, Nat.add_mul, Nat.add_mul]; ac_rfl
      unfold natL1Diff at hAdd; rw [hR] at hAdd; exact hAdd
  exact hOuter P.challenges

private theorem hvzk_nat_algebra (baseDen U T S K EK CNum A1 A2 delta1 : Nat)
    (hDPos : 0 < baseDen * (4 * U)) (hSingle : delta1 ≤ 4 * U * T + 4 * baseDen * S)
    (hRetry : EK * (baseDen * (4 * U)) ≤ 2 * K * delta1 * (baseDen * (4 * U)) ^ K)
    (hCond : CNum ≤ 2 * A1 * delta1) (hSimRate : baseDen * (4 * U) ≤ K * A2) :
    EK * (baseDen * U) ≤ K * (T * U + S * baseDen) * (2 * (baseDen * (4 * U)) ^ K) ∧
    CNum * (baseDen * U) ≤ K * (T * U + S * baseDen) * (2 * A1 * A2) := by
  let D := baseDen * (4 * U)
  have hCancel : delta1 * (baseDen * U) ≤ (T * U + S * baseDen) * D := by
    have h4 := Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right (baseDen * U) hSingle)
    have hR : 4 * ((4 * U * T + 4 * baseDen * S) * (baseDen * U)) = 4 * ((T * U + S * baseDen) * (baseDen * (4 * U))) := by
      rw [Nat.add_mul, Nat.add_mul, Nat.mul_add, Nat.mul_add]; ac_rfl
    rw [hR] at h4; exact Nat.le_of_mul_le_mul_left h4 (by decide)
  constructor
  · have m := Nat.mul_le_mul_right (baseDen * U) hRetry
    have eL : EK * (baseDen * U) * D = EK * D * (baseDen * U) := by ac_rfl
    have eR : 2 * K * delta1 * D ^ K * (baseDen * U) = 2 * K * D ^ K * (delta1 * (baseDen * U)) := by ac_rfl
    have s1 : EK * (baseDen * U) * D ≤ (2 * K * D ^ K) * (delta1 * (baseDen * U)) := by rw [eL, ← eR]; exact m
    have s2 := Nat.mul_le_mul_left (2 * K * D ^ K) hCancel
    have eR2 : 2 * K * D ^ K * ((T * U + S * baseDen) * D) = K * (T * U + S * baseDen) * (2 * D ^ K) * D := by ac_rfl
    rw [eR2] at s2; exact Nat.le_of_mul_le_mul_right (Nat.le_trans s1 s2) hDPos
  · have h1 := Nat.mul_le_mul_right (baseDen * U) hCond; rw [Nat.mul_assoc (2 * A1)] at h1
    have hChain := Nat.le_trans h1 (Nat.mul_le_mul_left (2 * A1)
      (Nat.le_trans hCancel (Nat.mul_le_mul_left (T * U + S * baseDen) hSimRate)))
    have eR : 2 * A1 * ((T * U + S * baseDen) * (K * A2)) = K * (T * U + S * baseDen) * (2 * A1 * A2) := by ac_rfl
    exact eR ▸ hChain

theorem q192_gaussian_hvzk_statistical_distance
    (P : Q192GaussianSamplerParams) (shift : Nat → Int) (q192Num : Int → Int → Nat) (K : Nat)
    (hRhoLe : ∀ z : Int, P.rho z ≤ P.zProp)
    (hUlp : ∀ c z, ((q192Num z (shift c) : Int) - (acceptProbQ192FloorNum P.rho P.scaleM z (shift c) : Int)).natAbs ≤ 3)
    (hSubReal : natSumList (prodPairs P.challenges P.support) (realQ192TrialWeight P shift q192Num) ≤ P.trialDenom)
    (hSubSim : natSumList (prodPairs P.challenges P.support) (idealSimTrialWeight P) ≤ P.trialDenom)
    (hRealPos : 0 < natSumList (prodPairs P.challenges P.support) (realQ192TrialWeight P shift q192Num))
    (hSimPos : 0 < natSumList (prodPairs P.challenges P.support) (idealSimTrialWeight P))
    (hSimRate : P.trialDenom ≤ K * natSumList (prodPairs P.challenges P.support) (idealSimTrialWeight P)) :
    let bound := ExactRat.scaleNat K ((tailMassRat P shift).add (ExactRat.scaleNat P.support.length (ExactRat.twoNegPow 190)))
    ExactRat.le (q192RetryTranscriptTv P shift q192Num K) bound ∧
    ExactRat.le (q192ConditionalAcceptedTv P shift q192Num hRealPos hSimPos) bound := by
  intro bound; let pts := prodPairs P.challenges P.support; let baseDen := P.challenges.length * P.zProp * P.scaleM
  have hPow : (2 : Nat) ^ 192 = 4 * 2 ^ 190 := by rw [show (192 : Nat) = 2 + 190 from rfl, Nat.pow_add]
  have hSingle := natL1_single_trial_gen P shift q192Num (2 ^ 192) hRhoLe hUlp
  change natL1Diff pts (realQ192TrialWeight P shift q192Num) (idealSimTrialWeight P) ≤ _ at hSingle
  have hRetry := retry_full_l1_le_two_K_mul_single pts P.trialDenom
    (realQ192TrialWeight P shift q192Num) (idealSimTrialWeight P) hSubReal hSubSim K
  have hCond := conditional_accepted_l1_le_two_mul_single pts (realQ192TrialWeight P shift q192Num) (idealSimTrialWeight P)
  dsimp only at hRetry hCond
  have hDDef : P.trialDenom = baseDen * (4 * 2 ^ 190) := by unfold Q192GaussianSamplerParams.trialDenom baseDen; rw [hPow]
  have hSingle' : natL1Diff pts (realQ192TrialWeight P shift q192Num) (idealSimTrialWeight P) ≤
      4 * 2 ^ 190 * natSumList pts (tailDeficitAt P shift) + 4 * baseDen * P.support.length := by
    rw [hPow] at hSingle; simpa only [baseDen, Nat.mul_assoc] using hSingle
  have hAlg := hvzk_nat_algebra baseDen (2 ^ 190) (natSumList pts (tailDeficitAt P shift))
    P.support.length K _ _ _ _ _ (hDDef ▸ P.trialDenom_pos) hSingle' (hDDef ▸ hRetry) hCond (hDDef ▸ hSimRate)
  have hBNum : bound.num = ((K * (natSumList pts (tailDeficitAt P shift) * 2 ^ 190 + P.support.length * baseDen) : Nat) : Int) := by
    unfold bound tailMassRat ExactRat.scaleNat ExactRat.add ExactRat.twoNegPow; dsimp only
    simp only [Int.natCast_mul, Int.natCast_add, Int.mul_one, pts, baseDen]
  refine ⟨ExactRat.le_of_nat_mul rfl hBNum ?_, ExactRat.le_of_nat_mul rfl hBNum hAlg.2⟩
  change _ ≤ _ * (2 * P.trialDenom ^ K); exact hDDef.symm ▸ hAlg.1

def q192AcceptIndicatorProb (P : Q192GaussianSamplerParams) (shift : Nat → Int)
    (q192Num : Int → Int → Nat) (K : Nat) (b : Bool) : ExactRat :=
  let pts := prodPairs P.challenges P.support; let D := P.trialDenom
  let R := D - natSumList pts (realQ192TrialWeight P shift q192Num)
  ⟨((if b then D ^ K - R ^ K else R ^ K : Nat) : Int), D ^ K, Nat.pow_pos P.trialDenom_pos⟩

private theorem abort_marginal_core (D K d1 d2 R1K R2K RSK p : Nat) (b : Bool)
    (hDPos : 0 < D) (hR1Le : R1K ≤ D ^ K) (hR2Le : R2K ≤ D ^ K)
    (hAb1 : ((R1K : Int) - (RSK : Int)).natAbs * D ≤ K * d1 * D ^ K)
    (hAb2 : ((R2K : Int) - (RSK : Int)).natAbs * D ≤ K * d2 * D ^ K)
    (hS1 : 2 * K * d1 * p < D) (hS2 : 2 * K * d2 * p ≤ D) :
    (((if b then D ^ K - R1K else R1K : Nat) : Int) * ((D ^ K : Nat) : Int) -
      ((if b then D ^ K - R2K else R2K : Nat) : Int) * ((D ^ K : Nat) : Int)).natAbs * p < D ^ K * D ^ K := by
  have hDKPos : 0 < D ^ K := Nat.pow_pos hDPos
  have hTri : ((R1K : Int) - (R2K : Int)).natAbs * D ≤ (K * d1 + K * d2) * D ^ K := by
    have hAbs := Int.natAbs_add_le ((R1K : Int) - (RSK : Int)) ((RSK : Int) - (R2K : Int))
    rw [show (R1K : Int) - (RSK : Int) + ((RSK : Int) - (R2K : Int)) = (R1K : Int) - (R2K : Int) from by omega,
        show ((RSK : Int) - (R2K : Int)).natAbs = ((R2K : Int) - (RSK : Int)).natAbs from by omega] at hAbs
    have hM := Nat.mul_le_mul_right D hAbs; rw [Nat.add_mul] at hM; rw [Nat.add_mul]; exact Nat.le_trans hM (Nat.add_le_add hAb1 hAb2)
  have hSumLt : (K * d1 + K * d2) * p < D := by
    have h2 : 2 * ((K * d1 + K * d2) * p) < 2 * D := by
      have e : 2 * ((K * d1 + K * d2) * p) = 2 * K * d1 * p + 2 * K * d2 * p := by rw [Nat.add_mul, Nat.mul_add]; ac_rfl
      rw [e, Nat.two_mul D]; exact Nat.add_lt_add_of_lt_of_le hS1 hS2
    exact nat_lt_of_mul_lt_left h2
  have hRK : ((R1K : Int) - (R2K : Int)).natAbs * p < D ^ K := by
    have p1 := Nat.mul_le_mul_right p hTri; have p2 := Nat.mul_lt_mul_of_pos_right hSumLt hDKPos
    have e1 : ((R1K : Int) - (R2K : Int)).natAbs * p * D = ((R1K : Int) - (R2K : Int)).natAbs * D * p := by ac_rfl
    have e2 : (K * d1 + K * d2) * D ^ K * p = (K * d1 + K * d2) * p * D ^ K := by ac_rfl
    have hLtD : ((R1K : Int) - (R2K : Int)).natAbs * p * D < D ^ K * D := by
      rw [e1, Nat.mul_comm (D ^ K) D]; exact Nat.lt_of_le_of_lt p1 (e2.symm ▸ p2)
    exact nat_lt_of_mul_lt_right hLtD
  rw [← Int.sub_mul, Int.natAbs_mul, Int.natAbs_natCast]
  have hB : (((if b then D ^ K - R1K else R1K : Nat) : Int) - ((if b then D ^ K - R2K else R2K : Nat) : Int)).natAbs =
      ((R1K : Int) - (R2K : Int)).natAbs := by
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]; exact sub_sub_natAbs_eq hR1Le hR2Le
  rw [hB, nat_mul_right_comm _ (D ^ K) p]; exact Nat.mul_lt_mul_of_pos_right hRK hDKPos

theorem q192_gaussian_abort_marginal_secret_independent
    (P : Q192GaussianSamplerParams) (shift1 shift2 : Nat → Int) (q192Num : Int → Int → Nat) (K : Nat) (b : Bool)
    (hSub1 : natSumList (prodPairs P.challenges P.support) (realQ192TrialWeight P shift1 q192Num) ≤ P.trialDenom)
    (hSub2 : natSumList (prodPairs P.challenges P.support) (realQ192TrialWeight P shift2 q192Num) ≤ P.trialDenom)
    (hSubSim : natSumList (prodPairs P.challenges P.support) (idealSimTrialWeight P) ≤ P.trialDenom)
    (hSmall1 : 2 * K * natL1Diff (prodPairs P.challenges P.support) (realQ192TrialWeight P shift1 q192Num) (idealSimTrialWeight P) * (2 ^ 128) < P.trialDenom)
    (hSmall2 : 2 * K * natL1Diff (prodPairs P.challenges P.support) (realQ192TrialWeight P shift2 q192Num) (idealSimTrialWeight P) * (2 ^ 128) ≤ P.trialDenom) :
    ExactRat.lt (ExactRat.abs (ExactRat.sub (q192AcceptIndicatorProb P shift1 q192Num K b) (q192AcceptIndicatorProb P shift2 q192Num K b)))
      (ExactRat.twoNegPow 128) := by
  apply ExactRat.abs_lt_twoNegPow; let pts := prodPairs P.challenges P.support; let D := P.trialDenom
  exact abort_marginal_core D K _ _ _ _ _ (2 ^ 128) b P.trialDenom_pos
    (Nat.pow_le_pow_left (Nat.sub_le D _) K) (Nat.pow_le_pow_left (Nat.sub_le D _) K)
    (retry_abort_diff_le_K_mul_single pts D _ _ hSub1 hSubSim K)
    (retry_abort_diff_le_K_mul_single pts D _ _ hSub2 hSubSim K) hSmall1 hSmall2

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
      · simp [h1, h2]
      · have h3 : ¬ (pStar ≤ k + 1) := by omega
        simp [h1, h2, h3]

def accSuffixXor (L : Nat) (u : Nat → Bool) (i : Nat) : Bool :=
  (List.range (L - i)).foldl (fun acc d => Bool.xor acc (u (i + d))) false
def gf2InnerProd : Nat → (Nat → Bool) → (Nat → Bool) → Bool
  | 0, _, _ => false
  | k + 1, a, b => Bool.xor (gf2InnerProd k a b) (a k && b k)

theorem acc_transpose_duality (u : Nat → Bool) (pStar : Nat) :
    ∀ d : Nat, gf2InnerProd (pStar + d) u (accPrefixXor (unitPunctureVec pStar)) = accSuffixXor (pStar + d) u pStar := by
  have hBelow : ∀ m : Nat, m ≤ pStar → gf2InnerProd m u (accPrefixXor (unitPunctureVec pStar)) = false := by
    intro m hm; induction m with
    | zero => rfl
    | succ m' ih =>
      simp only [gf2InnerProd, ih (by omega), accUnitPuncture_eq_stepIndicator]
      have hN : ¬ (pStar ≤ m') := by omega
      simp [hN]
  intro d; induction d with
  | zero => rw [Nat.add_zero, hBelow pStar (Nat.le_refl pStar)]; unfold accSuffixXor; simp [Nat.sub_self]
  | succ d' ih =>
    rw [Nat.add_succ, gf2InnerProd, ih, accUnitPuncture_eq_stepIndicator]; unfold accSuffixXor
    rw [Nat.add_sub_cancel_left, show (pStar + d').succ - pStar = d' + 1 from by omega,
        List.range_succ, List.foldl_append, List.foldl]; simp [Nat.le_add_right pStar d']

def xorStepProb (tau p : ExactRat) : ExactRat :=
  ⟨tau.num * ((p.den : Int) - p.num) + ((tau.den : Int) - tau.num) * p.num, tau.den * p.den, Nat.mul_pos tau.den_pos p.den_pos⟩
def bernoulliXorOneProb (tau : ExactRat) : Nat → ExactRat
  | 0 => ExactRat.ofInt 0
  | w + 1 => xorStepProb tau (bernoulliXorOneProb tau w)
def regularBlockXorOneProb : List ExactRat → ExactRat
  | [] => ExactRat.ofInt 0
  | tau :: tl => xorStepProb tau (regularBlockXorOneProb tl)
def parityBias (p : ExactRat) : ExactRat := ⟨(p.den : Int) - 2 * p.num, p.den, p.den_pos⟩

private theorem parityBias_xorStepProb (tau p : ExactRat) :
    parityBias (xorStepProb tau p) = ExactRat.mul (parityBias tau) (parityBias p) := by
  rcases tau with ⟨tn, td, htd⟩; rcases p with ⟨pn, pd, hpd⟩
  unfold parityBias xorStepProb ExactRat.mul; dsimp only; congr 1
  rw [Int.natCast_mul, Int.mul_sub tn, Int.sub_mul (td : Int), Int.mul_add 2, Int.mul_sub 2, Int.mul_sub 2,
      Int.mul_sub ((td : Int) - 2 * tn), Int.sub_mul (td : Int), Int.sub_mul (td : Int)]
  have c1 : 2 * tn * (pd : Int) = 2 * (tn * (pd : Int)) := Int.mul_assoc 2 tn (pd : Int)
  have c2 : (td : Int) * (2 * pn) = 2 * ((td : Int) * pn) := by ac_rfl
  have c3 : 2 * tn * (2 * pn) = 4 * (tn * pn) := by rw [Int.mul_assoc 2 tn, Int.mul_left_comm tn 2 pn, ← Int.mul_assoc 2 2]; rfl
  rw [c1, c2, c3]; omega

theorem piling_up_lemma_bernoulli_rat (tau : ExactRat) :
    ∀ w : Nat, parityBias (bernoulliXorOneProb tau w) = ExactRat.pow (parityBias tau) w
  | 0 => rfl
  | w + 1 => by simp only [bernoulliXorOneProb, ExactRat.pow, parityBias_xorStepProb, piling_up_lemma_bernoulli_rat tau w]

theorem piling_up_lemma_regular_blocks_rat :
    ∀ rates : List ExactRat, parityBias (regularBlockXorOneProb rates) =
      rates.foldr (fun tau acc => ExactRat.mul (parityBias tau) acc) (ExactRat.ofInt 1)
  | [] => rfl
  | tau :: tl => by simp only [regularBlockXorOneProb, List.foldr, parityBias_xorStepProb, piling_up_lemma_regular_blocks_rat tl]

theorem bernoulli_dual_min_weight_bias_lt_two_neg_256 (dMin : Nat) (hd : 1536 ≤ dMin) :
    let tau : ExactRat := ⟨1, 16, by decide⟩
    ExactRat.lt (ExactRat.abs (parityBias (bernoulliXorOneProb tau dMin))) (ExactRat.twoNegPow 256) := by
  intro tau; rw [piling_up_lemma_bernoulli_rat]; apply ExactRat.abs_lt_twoNegPow
  have hPowF : ∀ n : Nat, (ExactRat.pow (parityBias tau) n).num = ((14 ^ n : Nat) : Int) ∧
      (ExactRat.pow (parityBias tau) n).den = 16 ^ n := by
    intro n; induction n with
    | zero => exact ⟨rfl, rfl⟩
    | succ n' ih =>
      rw [ExactRat.pow, ExactRat.mul_num, ExactRat.mul_den, ih.1, ih.2]
      exact ⟨by change (14 : Int) * ((14 ^ n' : Nat) : Int) = _; rw [Nat.pow_succ', Int.natCast_mul]; rfl,
             by change 16 * 16 ^ n' = 16 ^ (n' + 1); rw [Nat.pow_succ']⟩
  have hBase6 : 14 ^ 6 * 2 < 16 ^ 6 := by decide
  have hStep6 : ∀ m : Nat, 14 ^ (6 * (m + 1)) * 2 ^ (m + 1) < 16 ^ (6 * (m + 1)) := by
    intro m; induction m with
    | zero => exact hBase6
    | succ m' ih =>
      rw [show 6 * (m' + 2) = 6 * (m' + 1) + 6 from by omega, Nat.pow_add 14, Nat.pow_add 16, Nat.pow_succ 2 (m' + 1), nat_mul4_swap]
      exact Nat.lt_trans (Nat.mul_lt_mul_of_pos_right ih (by decide)) (Nat.mul_lt_mul_of_pos_left hBase6 (Nat.pow_pos (by decide)))
  have hMono : ∀ k : Nat, 14 ^ (6 * (255 + 1) + k) * 2 ^ (255 + 1) < 16 ^ (6 * (255 + 1) + k) := by
    intro k; induction k with
    | zero => rw [Nat.add_zero]; exact hStep6 255
    | succ k' ih =>
      rw [Nat.add_succ, Nat.pow_succ 14, Nat.pow_succ 16, nat_mul_right_comm _ 14]
      exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right ih (by decide)) (Nat.mul_le_mul_left _ (by decide))
  rw [(hPowF dMin).1, (hPowF dMin).2, Int.natAbs_natCast]
  have hk := hMono (dMin - 1536)
  rw [show 6 * (255 + 1) + (dMin - 1536) = dMin from by omega] at hk; exact hk

def depth15TreeRate (w : Nat) : ExactRat := ⟨(w : Int), 32768, by decide⟩

theorem pcg_dense_dual_lpn_linear_bias_lt_two_neg_256
    (weights : List Nat) (hLen : weights.length = 64)
    (hBal : ∀ w ∈ weights, ((32768 : Int) - 2 * (w : Int)).natAbs ≤ 2047) :
    ExactRat.lt (ExactRat.abs (parityBias (regularBlockXorOneProb (weights.map depth15TreeRate)))) (ExactRat.twoNegPow 256) := by
  rw [piling_up_lemma_regular_blocks_rat]; apply ExactRat.abs_lt_twoNegPow
  have hProd : ∀ ws : List Nat, (∀ w ∈ ws, ((32768 : Int) - 2 * (w : Int)).natAbs ≤ 2047) →
      ((ws.map depth15TreeRate).foldr (fun tau acc => ExactRat.mul (parityBias tau) acc) (ExactRat.ofInt 1)).num.natAbs ≤ 2047 ^ ws.length ∧
      ((ws.map depth15TreeRate).foldr (fun tau acc => ExactRat.mul (parityBias tau) acc) (ExactRat.ofInt 1)).den = 32768 ^ ws.length := by
    intro ws hW; induction ws with
    | nil => exact ⟨by decide, rfl⟩
    | cons w tl ih =>
      have htl := ih (fun x hx => hW x (.tail w hx))
      rw [List.map_cons, List.foldr_cons, ExactRat.mul_num, ExactRat.mul_den, List.length_cons]
      exact ⟨by rw [Int.natAbs_mul, Nat.pow_succ']; exact Nat.mul_le_mul (hW w (.head tl)) htl.1, by rw [htl.2, Nat.pow_succ']; rfl⟩
  have h64 := hProd weights hBal; rw [hLen] at h64; rw [h64.2]
  have hScale : ∀ m : Nat, 2048 ^ m * 2 ^ (4 * m) = 32768 ^ m := by
    intro m; induction m with
    | zero => rfl
    | succ m' ih =>
      rw [show 4 * (m' + 1) = 4 * m' + 4 from by omega, Nat.pow_succ 2048, Nat.pow_add 2, Nat.pow_succ 32768,
          ← ih, nat_mul4_swap, show 2048 * 2 ^ 4 = 32768 from by decide]
  rw [← hScale 64]
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right (2 ^ 256) h64.1)
    (Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_left (by decide) (by decide)) (Nat.two_pow_pos 256))

theorem tooth_omitting_accumulator_collapses_dual_lpn_bias :
    ¬ ExactRat.lt (ExactRat.abs (parityBias (regularBlockXorOneProb ((List.replicate 64 3).map depth15TreeRate))))
      (ExactRat.twoNegPow 256) := by
  rw [piling_up_lemma_regular_blocks_rat]; apply ExactRat.not_lt_twoNegPow_of_gt
  have hRep : ∀ n : Nat, (((List.replicate n 3).map depth15TreeRate).foldr
        (fun tau acc => ExactRat.mul (parityBias tau) acc) (ExactRat.ofInt 1)).num = ((32762 ^ n : Nat) : Int) ∧
      (((List.replicate n 3).map depth15TreeRate).foldr
        (fun tau acc => ExactRat.mul (parityBias tau) acc) (ExactRat.ofInt 1)).den = 32768 ^ n := by
    intro n; induction n with
    | zero => exact ⟨rfl, rfl⟩
    | succ n' ih =>
      rw [List.replicate_succ, List.map_cons, List.foldr_cons, ExactRat.mul_num, ExactRat.mul_den, ih.1, ih.2]
      exact ⟨by change (32762 : Int) * ((32762 ^ n' : Nat) : Int) = _; rw [Nat.pow_succ', Int.natCast_mul]; rfl,
             by change 32768 * 32768 ^ n' = 32768 ^ (n' + 1); rw [Nat.pow_succ']⟩
  rw [(hRep 64).1, (hRep 64).2, Int.natAbs_natCast]
  have hSplit : ∀ m : Nat, 32768 ^ m = 16384 ^ m * 2 ^ m := by
    intro m; induction m with
    | zero => rfl
    | succ m' ih => rw [Nat.pow_succ 32768, ih, Nat.pow_succ 16384, Nat.pow_succ 2, nat_mul4_swap, show 16384 * 2 = 32768 from by decide]
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
    change (j + 2) * ((binom n j + binom n (j + 1)) + binom (n + 1) (j + 2)) = (n + 2) * (binom n j + binom n (j + 1))
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
  · have hZ : ∀ m k : Nat, m < k → binom m k = 0 := by
      intro m; induction m with
      | zero => intro k hk; cases k with | zero => omega | succ _ => rfl
      | succ _ ih => intro k hk; cases k with | zero => omega | succ k' => simp only [binom, ih k' (by omega), ih (k' + 1) (by omega)]
    rw [hZ n (j + 1) (by omega), show n - j = 0 from by omega, Nat.zero_mul, Nat.mul_zero]

theorem binom_mono_left {a b : Nat} (h : a ≤ b) : ∀ j : Nat, binom a j ≤ binom b j := by
  induction h with
  | refl => intro _; exact Nat.le_refl _
  | step _ ih => intro j; cases j with
    | zero => simp only [binom_zero_right]; exact Nat.le_refl 1
    | succ j' => simp only [binom]; exact Nat.le_trans (ih (j' + 1)) (Nat.le_add_left _ _)

theorem binom_pos : ∀ {n j : Nat}, j ≤ n → 0 < binom n j
  | n, 0, _ => by rw [binom_zero_right n]; exact Nat.one_pos
  | 0, _ + 1, h => by omega
  | n + 1, j + 1, h => by simp only [binom]; exact Nat.add_pos_left (binom_pos (n := n) (j := j) (by omega)) _

theorem binom_scale_lower_bound {c : Nat} (hc : 1 ≤ c) :
    ∀ {t r M : Nat}, t ≤ r → c * r ≤ M → c ^ t * binom r t ≤ binom M t
  | 0, _, _, _, _ => by rw [Nat.pow_zero, binom_zero_right, binom_zero_right, Nat.one_mul]; exact Nat.le_refl 1
  | _ + 1, 0, _, ht, _ => by omega
  | _ + 1, r + 1, 0, _, hcr => False.elim (Nat.ne_of_gt (Nat.mul_pos hc (Nat.succ_pos r)) (Nat.eq_zero_of_le_zero hcr))
  | t + 1, r + 1, M + 1, ht, hcr => by
    have hcr' : c * r ≤ M := by rw [Nat.mul_add, Nat.mul_one] at hcr; omega
    have hMul := Nat.mul_le_mul hcr (binom_scale_lower_bound hc (t := t) (r := r) (M := M) (by omega) hcr')
    have hRe : c * (r + 1) * (c ^ t * binom r t) = (t + 1) * (c ^ (t + 1) * binom (r + 1) (t + 1)) := by
      have p : c * (r + 1) * (c ^ t * binom r t) = c ^ (t + 1) * ((r + 1) * binom r t) := by rw [Nat.pow_succ']; ac_rfl
      rw [p, ← binom_mul_succ r t]; ac_rfl
    rw [hRe, ← binom_mul_succ M t] at hMul; exact Nat.le_of_mul_le_mul_left hMul (Nat.succ_pos t)

theorem binom_scale_upper_bound (c : Nat) :
    ∀ {t M r : Nat}, t ≤ r → M ≤ c * (r - t) → binom M t ≤ c ^ t * binom r t
  | 0, _, _, _, _ => by rw [binom_zero_right, binom_zero_right, Nat.pow_zero, Nat.one_mul]; exact Nat.le_refl 1
  | _ + 1, 0, _, _, _ => Nat.zero_le _
  | _ + 1, _ + 1, 0, ht, _ => by omega
  | t + 1, M + 1, r + 1, ht, hMc => by
    rw [Nat.succ_sub_succ] at hMc
    have ih := binom_scale_upper_bound c (t := t) (M := M) (r := r) (by omega) (Nat.le_of_succ_le hMc)
    have hMul := Nat.mul_le_mul (Nat.le_trans hMc (Nat.mul_le_mul_left c (Nat.le_trans (Nat.sub_le r t) (Nat.le_succ r)))) ih
    have hRhs : c * (r + 1) * (c ^ t * binom r t) = (t + 1) * (c ^ (t + 1) * binom (r + 1) (t + 1)) := by
      have p : c * (r + 1) * (c ^ t * binom r t) = c ^ (t + 1) * ((r + 1) * binom r t) := by rw [Nat.pow_succ']; ac_rfl
      rw [p, ← binom_mul_succ r t]; ac_rfl
    rw [← binom_mul_succ M t, hRhs] at hMul; exact Nat.le_of_mul_le_mul_left hMul (Nat.succ_pos t)

attribute [irreducible] binom

private theorem binom_step2 (n u : Nat) : (u + 2) * (u + 1) * binom n (u + 2) = (n - (u + 1)) * (n - u) * binom n u := by
  have s1 := binom_step_right n (u + 1); have s0 := binom_step_right n u
  calc (u + 2) * (u + 1) * binom n (u + 2) = (u + 1) * ((u + 2) * binom n (u + 2)) := by ac_rfl
    _ = (n - (u + 1)) * ((u + 1) * binom n (u + 1)) := by rw [s1]; ac_rfl
    _ = (n - (u + 1)) * (n - u) * binom n u := by rw [s0]; ac_rfl

private theorem chain_rel2 (k1 k2 d1 d2 b4 b2 b0 : Nat) (h1 : k1 * b4 = d1 * b2) (h2 : k2 * b2 = d2 * b0) :
    (k1 * k2) * b4 = (d1 * d2) * b0 := by
  calc (k1 * k2) * b4 = k2 * (k1 * b4) := by ac_rfl
    _ = d1 * (k2 * b2) := by rw [h1]; ac_rfl
    _ = (d1 * d2) * b0 := by rw [h2]; ac_rfl

private theorem step_ratio_le (m3 subL u21 subR bL3 bL2 bRu bRu2 : Nat)
    (hPos : 0 < m3 * u21) (hRatio : subL * u21 ≤ m3 * subR) (h1 : m3 * bL3 = subL * bL2) (h2 : u21 * bRu2 = subR * bRu) :
    bL3 * bRu ≤ bL2 * bRu2 := by
  have m := Nat.mul_le_mul_right (bL2 * bRu) hRatio
  have e1 : subL * u21 * (bL2 * bRu) = m3 * u21 * (bL3 * bRu) := by
    calc subL * u21 * (bL2 * bRu) = u21 * (subL * bL2) * bRu := by ac_rfl
      _ = m3 * u21 * (bL3 * bRu) := by rw [← h1]; ac_rfl
  have e2 : m3 * subR * (bL2 * bRu) = m3 * u21 * (bL2 * bRu2) := by
    calc m3 * subR * (bL2 * bRu) = m3 * bL2 * (subR * bRu) := by ac_rfl
      _ = m3 * u21 * (bL2 * bRu2) := by rw [← h2]; ac_rfl
  rw [e1, e2] at m; exact Nat.le_of_mul_le_mul_left m hPos

private theorem scale_binom_bound (P256 P15 K A R D bHi bLo : Nat)
    (hK : 0 < K) (hP : P256 ≤ 81 * P15) (hRel : K * bHi = D * bLo) (hNum : K * A * 81 ≤ R * D) :
    P256 * (A * bLo) ≤ R * (P15 * bHi) := by
  have m1 := Nat.mul_le_mul_left (K * A) hP; have m2 := Nat.mul_le_mul_right P15 hNum
  have r1 : K * A * (81 * P15) = K * A * 81 * P15 := by ac_rfl
  have m3 := Nat.mul_le_mul_right bLo (Nat.le_trans m1 (r1 ▸ m2))
  have eL : K * A * P256 * bLo = K * (P256 * (A * bLo)) := by ac_rfl
  have eR : R * D * P15 * bLo = K * (R * (P15 * bHi)) := by
    calc R * D * P15 * bLo = R * P15 * (D * bLo) := by ac_rfl
      _ = K * (R * (P15 * bHi)) := by rw [← hRel]; ac_rfl
  rw [eL, eR] at m3; exact Nat.le_of_mul_le_mul_left m3 hK

private theorem finish_q2_bound (P256 P15 L2 Lq R0 b64 b60 bq : Nat)
    (hMono : Lq * bq ≤ L2 * b60) (hBase2 : P256 * ((2 * L2) * b60) ≤ 4 * (P15 * b64)) :
    P256 * (Lq ^ 2 * bq) ≤ (R0 + 2 * Lq) * (P15 * b64) := by
  have e2 : P256 * ((2 * L2) * b60) = 2 * (P256 * (L2 * b60)) := by ac_rfl
  have e4 : 4 * (P15 * b64) = 2 * (2 * (P15 * b64)) := by rw [show (4 : Nat) = 2 * 2 from rfl, Nat.mul_assoc]
  rw [e2, e4] at hBase2; have hBase := Nat.le_of_mul_le_mul_left hBase2 (by decide)
  have hMulLq := Nat.mul_le_mul_left Lq (Nat.le_trans (Nat.mul_le_mul_left P256 hMono) hBase)
  have fL : Lq * (P256 * (Lq * bq)) = P256 * (Lq ^ 2 * bq) := by rw [Nat.pow_two]; ac_rfl
  have fR : Lq * (2 * (P15 * b64)) ≤ (R0 + 2 * Lq) * (P15 * b64) := by
    have c : Lq * (2 * (P15 * b64)) = (2 * Lq) * (P15 * b64) := by ac_rfl
    rw [c]; exact Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
  rw [fL] at hMulLq; exact Nat.le_trans hMulLq fR

def pcgDenseRows : Nat := 136 * 1024
def pcgDenseWeightT : Nat := 64
def pcgDepth15Cols : Nat := 2048 * 1024
def pcgDepth14Cols : Nat := 1024 * 1024

def sternDumerWorkExceedsPow2 (M r t q l bits : Nat) : Prop :=
  let Lq := binom ((M - r) / 2) q
  2 ^ bits * (Lq ^ 2 * binom (r - l) (t - 2 * q)) ≤ (r ^ 2 + 2 * Lq + Lq ^ 2 / (2 ^ l)) * binom M t

private theorem add_sub_ge_gen (A B d : Nat) (hd : d ≤ B) : A ≤ (A + B) - d := by omega

private theorem rows_sub_ge (d : Nat) (hd : d ≤ 1024) : 135 * 1024 ≤ pcgDenseRows - d := by
  have h : pcgDenseRows = 135 * 1024 + 1024 := by unfold pcgDenseRows; rw [show (136 : Nat) = 135 + 1 from rfl, Nat.add_mul, Nat.one_mul]
  rw [h]; exact add_sub_ge_gen (135 * 1024) 1024 d hd

private theorem half_diff_depth15 : (pcgDepth15Cols - pcgDenseRows) / 2 = 956 * 1024 := by
  unfold pcgDepth15Cols pcgDenseRows
  rw [← Nat.sub_mul, show 2048 - 136 = 2 * 956 from by decide, Nat.mul_assoc 2 956 1024, Nat.mul_div_right _ (by decide : 0 < 2)]

private theorem half_diff_depth14 : (pcgDepth14Cols - pcgDenseRows) / 2 = 888 * 512 := by
  unfold pcgDepth14Cols pcgDenseRows
  have h1024 : 888 * 1024 = 2 * (888 * 512) := by decide
  rw [← Nat.sub_mul, show 1024 - 136 = 888 from by decide, h1024, Nat.mul_div_right _ (by decide : 0 < 2)]

private theorem fifteen_pow64_gt_256 : 2 ^ 256 < 81 * 15 ^ 64 := by
  have sq : ∀ a b c : Nat, 0 < a → 0 < b → 0 < c → a < c * b → a * a < (c * c) * (b * b) := by
    intro a b c ha hb hc h; rw [nat_mul4_swap c c b b]
    exact Nat.lt_trans (Nat.mul_lt_mul_of_pos_right h ha) (Nat.mul_lt_mul_of_pos_left h (Nat.mul_pos hc hb))
  have h2 := sq (2 ^ 64) (15 ^ 16) 3 (Nat.two_pow_pos 64) (Nat.pow_pos (by decide)) (by decide) (by decide)
  rw [← Nat.pow_add, ← Nat.pow_add] at h2
  have h3 := sq (2 ^ 128) (15 ^ 32) 9 (Nat.two_pow_pos 128) (Nat.pow_pos (by decide)) (by decide) h2
  rw [← Nat.pow_add, ← Nat.pow_add] at h3; exact h3

private theorem sq956_bound (K : Nat) (hK : 32 * 32 = K) : (956 * K) * (956 * K) ≤ (15 * 64) * K * K * K := by
  have m := Nat.mul_le_mul (by decide : 956 ≤ 30 * 32) (by decide : 956 ≤ 30 * 32)
  rw [nat_mul4_swap 30 32 30 32, hK] at m
  have m2 := Nat.le_trans m (Nat.mul_le_mul_right K (by decide : 30 * 30 ≤ 15 * 64))
  have eL : (956 * K) * (956 * K) = (956 * 956) * (K * K) := nat_mul4_swap 956 K 956 K
  have eR : ((15 * 64) * K) * (K * K) = (15 * 64) * K * K * K := by ac_rfl
  rw [eL, ← eR]; exact Nat.mul_le_mul_right (K * K) m2

private theorem q1_num_bound (K R0 R63 R62 : Nat) (hK : 32 * 32 = K) (hK1024 : 5 * 1024 ≤ 5 * K)
    (hR1 : 32 * K ≤ R0) (hR2 : 32 * K ≤ R63) (hR3 : 32 * K ≤ R62) :
    (64 * 63) * ((956 * K) ^ 2) * 81 ≤ (R0 ^ 2 + 2 * (956 * K)) * (R63 * R62) := by
  have h63 : (64 * 63) * 81 ≤ 5 * 64 * K := by
    have p := Nat.mul_le_mul_left 64 (Nat.le_trans (by decide : 63 * 81 ≤ 5 * 1024) hK1024)
    have e : 64 * (5 * K) = 5 * 64 * K := by ac_rfl
    rw [e] at p; exact p
  have hSq : (956 * K) ^ 2 ≤ (15 * 64) * K * K * K := by rw [Nat.pow_two]; exact sq956_bound K hK
  have hL1 := Nat.mul_le_mul h63 hSq
  have eL1 : (64 * 63) * 81 * (956 * K) ^ 2 = (64 * 63) * (956 * K) ^ 2 * 81 := by ac_rfl
  have eL2 : (5 * 64 * K) * ((15 * 64) * K * K * K) = (5 * 64 * (15 * 64)) * (K * K * K * K) := by ac_rfl
  rw [eL1, eL2] at hL1
  have hCoeff : 5 * 64 * (15 * 64) ≤ 32 * 32 * 32 * 32 := by
    have e : 5 * (2 * 32) * (15 * (2 * 32)) = (5 * 2 * 15 * 2) * 32 * 32 := by ac_rfl
    rw [show (64 : Nat) = 2 * 32 from rfl, e]
    exact Nat.mul_le_mul_right 32 (Nat.mul_le_mul_right 32 (by decide : 5 * 2 * 15 * 2 ≤ 32 * 32))
  have hR1Sq : 32 * K * (32 * K) ≤ R0 ^ 2 + 2 * (956 * K) := by
    rw [Nat.pow_two]; exact Nat.le_trans (Nat.mul_le_mul hR1 hR1) (Nat.le_add_right _ _)
  have hRProd := Nat.mul_le_mul hR1Sq (Nat.mul_le_mul hR2 hR3)
  have eR : (32 * K * (32 * K)) * (32 * K * (32 * K)) = (32 * 32 * 32 * 32) * (K * K * K * K) := by ac_rfl
  rw [eR] at hRProd
  exact Nat.le_trans hL1 (Nat.le_trans (Nat.mul_le_mul_right _ hCoeff) hRProd)

private theorem q2_num_bound (K H R63 R62 R61 R60 : Nat)
    (hK : 32 * 32 = K) (hK64 : 64 * 16 = K) (hH : 2 * H = K) (hK5 : 63 * 81 ≤ 5 * K)
    (h63 : 135 * K ≤ R63) (h62 : 135 * K ≤ R62) (h61 : 135 * K ≤ R61) (h60 : 135 * K ≤ R60) :
    ((64 * 63) * (62 * 61)) * ((956 * K - 1) * (956 * K)) * 81 ≤ 4 * ((R63 * R62) * (R61 * R60)) := by
  have hA : ((64 * 63) * (62 * 61)) * 81 ≤ (75 * 16) * (K * K) := by
    have p2 : 64 * (62 * 61) ≤ 240 * K := by
      have c := Nat.mul_le_mul_left 64 (by decide : 62 * 61 ≤ 240 * 16)
      have e : 64 * (240 * 16) = 240 * (64 * 16) := by ac_rfl
      rw [e, hK64] at c; exact c
    have m := Nat.mul_le_mul hK5 p2
    have eL : (63 * 81) * (64 * (62 * 61)) = ((64 * 63) * (62 * 61)) * 81 := by ac_rfl
    have eR : (5 * K) * (240 * K) = (5 * 240) * (K * K) := by ac_rfl
    rw [eL, eR, show 5 * 240 = 75 * 16 from by decide] at m; exact m
  have hB : (956 * K - 1) * (956 * K) ≤ (15 * 64) * K * K * K :=
    Nat.le_trans (Nat.mul_le_mul_right _ (Nat.sub_le _ 1)) (sq956_bound K hK)
  have hAB := Nat.mul_le_mul hA hB
  have eAB1 : ((64 * 63) * (62 * 61)) * 81 * ((956 * K - 1) * (956 * K)) =
      ((64 * 63) * (62 * 61)) * ((956 * K - 1) * (956 * K)) * 81 := by ac_rfl
  have eAB2 : ((75 * 16) * (K * K)) * ((15 * 64) * K * K * K) = (75 * 15) * (64 * 16) * (K * K * K * K * K) := by ac_rfl
  rw [eAB1, eAB2, hK64] at hAB
  have h135 : 35 * H ≤ 135 * 135 := by
    have h2 : 2 * (16 * 32) = 2 * H := by rw [hH, ← hK]
    have hH16 : 16 * 32 = H := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h2
    have m := Nat.mul_le_mul (by decide : 5 * 16 ≤ 9 * 9) (by decide : 7 * 32 ≤ 15 * 15)
    rw [nat_mul4_swap 5 16 7 32, nat_mul4_swap 9 9 15 15, hH16, show 9 * 15 = 135 from by decide] at m; exact m
  have h135_4 : (35 * 35) * (K * K) ≤ 4 * ((135 * 135) * (135 * 135)) := by
    have m := Nat.mul_le_mul_left 4 (Nat.mul_le_mul h135 h135)
    have e : 4 * ((35 * H) * (35 * H)) = (35 * 35) * ((2 * H) * (2 * H)) := by rw [show (4 : Nat) = 2 * 2 from rfl]; ac_rfl
    rw [e, hH] at m; exact m
  have hR4 := Nat.mul_le_mul_left 4 (Nat.mul_le_mul (Nat.mul_le_mul h63 h62) (Nat.mul_le_mul h61 h60))
  have eR4 : 4 * (((135 * K) * (135 * K)) * ((135 * K) * (135 * K))) = (4 * ((135 * 135) * (135 * 135))) * (K * K * K * K) := by ac_rfl
  rw [eR4] at hR4
  have c2 := Nat.mul_le_mul_right (K * K * K * K) (Nat.le_trans (Nat.mul_le_mul_right (K * K) (by decide : 75 * 15 ≤ 35 * 35)) h135_4)
  have ec : (75 * 15) * (K * K) * (K * K * K * K) = (75 * 15) * K * (K * K * K * K * K) := by ac_rfl
  rw [ec] at c2
  exact Nat.le_trans hAB (Nat.le_trans c2 hR4)

private theorem mono_q_ratio (K subL u21 m3 R1 R2 : Nat)
    (hSubL : subL ≤ K * K) (hU : u21 ≤ 4 * K) (hm : 3 ≤ m3) (hR1 : 64 * K ≤ R1) (hR2 : 64 * K ≤ R2)
    (h64 : 4 * K ≤ 3 * (64 * 64)) : subL * u21 ≤ m3 * (R1 * R2) := by
  have hL := Nat.mul_le_mul hSubL hU
  have eL : (K * K) * (4 * K) = (4 * K) * (K * K) := by ac_rfl
  rw [eL] at hL
  have hR := Nat.mul_le_mul hm (Nat.mul_le_mul hR1 hR2)
  have eR : 3 * ((64 * K) * (64 * K)) = (3 * (64 * 64)) * (K * K) := by ac_rfl
  rw [eR] at hR
  exact Nat.le_trans hL (Nat.le_trans (Nat.mul_le_mul_right (K * K) h64) hR)

private theorem stern_dumer_depth15_gen (B : Nat → Nat → Nat)
    (bZero : ∀ n, B n 0 = 1) (bOne : ∀ n, B n 1 = n)
    (bStep : ∀ n j, (j + 1) * B n (j + 1) = (n - j) * B n j)
    (bStep2 : ∀ n u, (u + 2) * (u + 1) * B n (u + 2) = (n - (u + 1)) * (n - u) * B n u)
    (bMono : ∀ {a b}, a ≤ b → ∀ j, B a j ≤ B b j)
    (hScaleM : 15 ^ 64 * B pcgDenseRows 64 ≤ B pcgDepth15Cols 64)
    (q l : Nat) (hq : q ≤ 32) :
    let Lq := B ((pcgDepth15Cols - pcgDenseRows) / 2) q
    2 ^ 256 * (Lq ^ 2 * B (pcgDenseRows - l) (pcgDenseWeightT - 2 * q)) ≤
      (pcgDenseRows ^ 2 + 2 * Lq + Lq ^ 2 / (2 ^ l)) * B pcgDepth15Cols pcgDenseWeightT := by
  dsimp only; rw [half_diff_depth15]; unfold pcgDenseWeightT
  have hWin := bMono (Nat.sub_le pcgDenseRows l) (64 - 2 * q)
  suffices hCore : 2 ^ 256 * (B (956 * 1024) q ^ 2 * B pcgDenseRows (64 - 2 * q)) ≤
      (pcgDenseRows ^ 2 + 2 * B (956 * 1024) q) * (15 ^ 64 * B pcgDenseRows 64) by
    exact Nat.le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hWin))
      (Nat.le_trans hCore (Nat.mul_le_mul (Nat.le_add_right _ _) hScaleM))
  have h15 := Nat.le_of_lt fifteen_pow64_gt_256
  match q with
  | 0 =>
    rw [bZero]; simp only [Nat.one_pow, Nat.one_mul, Nat.mul_one, ← Nat.mul_assoc]
    have h9 : 9 ≤ pcgDenseRows := Nat.le_trans (by decide : 9 ≤ 1024) (Nat.le_mul_of_pos_left 1024 (by decide : 0 < 136))
    have h81 : 81 ≤ pcgDenseRows ^ 2 + 2 := Nat.le_trans (by rw [Nat.pow_two]; exact Nat.mul_le_mul h9 h9) (Nat.le_add_right _ 2)
    exact Nat.mul_le_mul_right _ (Nat.le_trans h15 (Nat.mul_le_mul_right _ h81))
  | 1 =>
    rw [bOne]
    exact scale_binom_bound (2 ^ 256) (15 ^ 64) (64 * 63) ((956 * 1024) ^ 2)
      (pcgDenseRows ^ 2 + 2 * (956 * 1024)) ((pcgDenseRows - 63) * (pcgDenseRows - 62))
      _ _ (by decide) h15 (bStep2 pcgDenseRows 62)
      (q1_num_bound 1024 pcgDenseRows _ _ (by decide) (Nat.le_refl _)
        (by unfold pcgDenseRows; exact Nat.mul_le_mul_right 1024 (by decide))
        (Nat.le_trans (Nat.mul_le_mul_right 1024 (by decide)) (rows_sub_ge 63 (by decide)))
        (Nat.le_trans (Nat.mul_le_mul_right 1024 (by decide)) (rows_sub_ge 62 (by decide))))
  | q' + 2 =>
    have hMonoQ : ∀ m : Nat, m ≤ 30 →
        B (956 * 1024) (m + 2) * B pcgDenseRows (64 - 2 * (m + 2)) ≤ B (956 * 1024) 2 * B pcgDenseRows 60 := by
      intro m hm; induction m with
      | zero => exact Nat.le_refl _
      | succ m' ih =>
        refine Nat.le_trans ?_ (ih (by omega))
        rw [show 64 - 2 * (m' + 3) = 58 - 2 * m' from by omega, show 64 - 2 * (m' + 2) = (58 - 2 * m') + 2 from by omega]
        let u := 58 - 2 * m'
        have huMax : u + 2 ≤ 60 := by unfold u; omega
        have hRatio := mono_q_ratio 1024 (956 * 1024 - (m' + 2)) ((u + 2) * (u + 1)) (m' + 3)
          (pcgDenseRows - (u + 1)) (pcgDenseRows - u)
          (Nat.le_trans (Nat.sub_le _ _) (Nat.mul_le_mul_right 1024 (by decide)))
          (Nat.le_trans (Nat.mul_le_mul huMax (by omega : u + 1 ≤ 60)) (by decide)) (by omega)
          (Nat.le_trans (Nat.mul_le_mul_right 1024 (by decide : 64 ≤ 135)) (rows_sub_ge (u + 1) (by omega)))
          (Nat.le_trans (Nat.mul_le_mul_right 1024 (by decide : 64 ≤ 135)) (rows_sub_ge u (by omega)))
          (by decide)
        exact step_ratio_le (m' + 3) (956 * 1024 - (m' + 2)) ((u + 2) * (u + 1))
          ((pcgDenseRows - (u + 1)) * (pcgDenseRows - u)) _ _ _ _
          (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))) hRatio
          (bStep (956 * 1024) (m' + 2)) (bStep2 pcgDenseRows u)
    have sL1 := bStep (956 * 1024) 1; rw [bOne] at sL1
    change 2 * B (956 * 1024) 2 = (956 * 1024 - 1) * (956 * 1024) at sL1
    have hRel4 := chain_rel2 _ _ _ _ _ _ _ (bStep2 pcgDenseRows 62) (bStep2 pcgDenseRows 60)
    have hBase2 := scale_binom_bound (2 ^ 256) (15 ^ 64) ((64 * 63) * (62 * 61))
      (2 * B (956 * 1024) 2) 4 (((pcgDenseRows - 63) * (pcgDenseRows - 62)) * ((pcgDenseRows - 61) * (pcgDenseRows - 60)))
      _ _ (by decide) h15 hRel4
      (by rw [sL1]; exact q2_num_bound 1024 512 _ _ _ _ (by decide) (by decide) (by decide) (by decide)
            (rows_sub_ge 63 (by decide)) (rows_sub_ge 62 (by decide)) (rows_sub_ge 61 (by decide)) (rows_sub_ge 60 (by decide)))
    exact finish_q2_bound (2 ^ 256) (15 ^ 64) _ _ (pcgDenseRows ^ 2) _ _ _ (hMonoQ q' (by omega)) hBase2

theorem pcg_dense_depth15_prange_and_stern_dumer_pq128 (q l : Nat) (hq : q ≤ 32) :
    sternDumerWorkExceedsPow2 pcgDepth15Cols pcgDenseRows pcgDenseWeightT q l 256 ∧ 256 / 2 = 128 :=
  ⟨stern_dumer_depth15_gen binom binom_zero_right binom_one_right binom_step_right binom_step2
    (fun h => binom_mono_left h)
    (binom_scale_lower_bound (by decide)
      (Nat.le_trans (by decide : 64 ≤ 1024) (Nat.le_mul_of_pos_left 1024 (by decide : 0 < 136)))
      (by unfold pcgDenseRows pcgDepth15Cols; rw [← Nat.mul_assoc 15 136 1024]; exact Nat.mul_le_mul_right 1024 (by decide)))
    q l hq, rfl⟩

private theorem contra_isd_bound (C L2 bM bW P39 P80 P180 P256 P70 : Nat)
    (hbW : 0 < bW) (hP : 0 < P80 * P180) (hBM : bM ≤ P80 * P180 * bW) (hCost : C < P39)
    (hSq : P70 ≤ L2 ^ 2) (hPow : P39 * P80 * P180 ≤ P256 * P70) (hIn : P256 * (L2 ^ 2 * bW) ≤ C * bM) : False := by
  have hUp : C * bM < P39 * P80 * P180 * bW := by
    have t := Nat.lt_of_le_of_lt (Nat.mul_le_mul_left C hBM)
      (Nat.mul_lt_mul_of_pos_right hCost (Nat.mul_pos hP hbW))
    have e : P39 * ((P80 * P180) * bW) = P39 * P80 * P180 * bW := by ac_rfl
    rw [e] at t; exact t
  have hDn : P39 * P80 * P180 * bW ≤ C * bM := by
    have s1 := Nat.mul_le_mul_right bW hPow; rw [Nat.mul_assoc P256 P70 bW] at s1
    exact Nat.le_trans s1 (Nat.le_trans (Nat.mul_le_mul_left P256 (Nat.mul_le_mul_right bW hSq)) hIn)
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hUp hDn)

private theorem l2_cost_and_sq (L2 R0 P35 P36 P37 P22 P52 P70 P74 P39 : Nat)
    (hP35 : 0 < P35) (hP37 : 0 < P37) (hR0 : R0 ^ 2 < P36) (hLo : P35 ≤ L2) (hHi : L2 < P37)
    (hSq70 : P35 * P35 = P70) (hSq74 : P37 * P37 = P74) (hDiv74 : P74 = P22 * P52) (h22 : P22 ≤ P36)
    (hSum : P36 + 2 * P37 + P36 ≤ P39) : R0 ^ 2 + 2 * L2 + L2 ^ 2 / P52 < P39 ∧ P70 ≤ L2 ^ 2 := by
  have hSqLt : L2 ^ 2 < P74 := by
    rw [Nat.pow_two, ← hSq74]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right L2 (Nat.le_of_lt hHi)) (Nat.mul_lt_mul_of_pos_left hHi hP37)
  have _ := hP35
  have hDivLe : L2 ^ 2 / P52 ≤ P36 := Nat.le_trans
    (Nat.div_le_of_le_mul (by rw [Nat.mul_comm P52 P22, ← hDiv74]; exact Nat.le_of_lt hSqLt)) h22
  refine ⟨Nat.lt_of_lt_of_le (Nat.add_lt_add_of_lt_of_le
      (Nat.add_lt_add_of_lt_of_le hR0 (Nat.mul_le_mul_left 2 (Nat.le_of_lt hHi))) hDivLe) hSum, ?_⟩
  rw [Nat.pow_two, ← hSq70]; exact Nat.mul_le_mul hLo hLo

private theorem stern_dumer_depth14_contra_gen (B : Nat → Nat → Nat)
    (bOne : ∀ n, B n 1 = n) (bStep : ∀ n j, (j + 1) * B n (j + 1) = (n - j) * B n j)
    (hUp60 : B pcgDepth14Cols 60 ≤ 8 ^ 60 * B (pcgDenseRows - 52) 60)
    (hPos60 : 0 < B (pcgDenseRows - 52) 60)
    (hBad : let Lq := B ((pcgDepth14Cols - pcgDenseRows) / 2) 2
      2 ^ 256 * (Lq ^ 2 * B (pcgDenseRows - 52) (pcgDenseWeightT - 2 * 2)) ≤
        (pcgDenseRows ^ 2 + 2 * Lq + Lq ^ 2 / (2 ^ 52)) * B pcgDepth14Cols pcgDenseWeightT) : False := by
  dsimp only at hBad; rw [half_diff_depth14] at hBad; unfold pcgDenseWeightT at hBad
  have hM14 : pcgDepth14Cols = 2 ^ 20 := by
    unfold pcgDepth14Cols; rw [show (1024 : Nat) = 2 ^ 10 from by decide, ← Nat.pow_add]
  have hStepUp : ∀ j : Nat, B pcgDepth14Cols (j + 1) ≤ 2 ^ 20 * B pcgDepth14Cols j := by
    intro j; have s := bStep pcgDepth14Cols j
    have p1 : B pcgDepth14Cols (j + 1) ≤ (j + 1) * B pcgDepth14Cols (j + 1) := Nat.le_mul_of_pos_left _ (Nat.succ_pos j)
    rw [s] at p1; exact Nat.le_trans p1 (Nat.mul_le_mul_right _ (hM14 ▸ Nat.sub_le pcgDepth14Cols j))
  have p8 : ∀ m : Nat, 8 ^ m = 2 ^ (3 * m) := by
    intro m; induction m with
    | zero => rfl
    | succ m' ih => rw [show 3 * (m' + 1) = 3 * m' + 3 from by omega, Nat.pow_succ 8, ih, Nat.pow_add 2]
  have hUp64 : B pcgDepth14Cols 64 ≤ 2 ^ 80 * 2 ^ 180 * B (pcgDenseRows - 52) 60 := by
    have p := Nat.le_trans (hStepUp 63) (Nat.mul_le_mul_left (2 ^ 20) (Nat.le_trans (hStepUp 62)
      (Nat.mul_le_mul_left (2 ^ 20) (Nat.le_trans (hStepUp 61)
        (Nat.mul_le_mul_left (2 ^ 20) (Nat.le_trans (hStepUp 60) (Nat.mul_le_mul_left (2 ^ 20) hUp60)))))))
    rw [p8 60, ← Nat.mul_assoc (2 ^ 20), ← Nat.pow_add 2 20 20, ← Nat.mul_assoc (2 ^ 40),
        ← Nat.pow_add 2 40 20, ← Nat.mul_assoc (2 ^ 60), ← Nat.pow_add 2 60 20, ← Nat.mul_assoc (2 ^ 80)] at p
    exact p
  have sL2 := bStep (888 * 512) 1; rw [bOne] at sL2
  change 2 * B (888 * 512) 2 = (888 * 512 - 1) * (888 * 512) at sL2
  have hLo : 2 ^ 35 ≤ B (888 * 512) 2 := by
    have a : 2 ^ 18 ≤ 888 * 512 - 1 := by
      have h888 : 888 * 512 = 887 * 512 + 512 := by rw [show (888 : Nat) = 887 + 1 from rfl, Nat.add_mul, Nat.one_mul]
      have sub1 : 887 * 512 ≤ 888 * 512 - 1 := by rw [h888]; exact add_sub_ge_gen (887 * 512) 512 1 (by decide)
      have m := Nat.mul_le_mul (by decide : 2 ^ 9 ≤ 887) (by decide : 2 ^ 9 ≤ 512)
      rw [← Nat.pow_add] at m; exact Nat.le_trans m sub1
    have b : 2 * 2 ^ 17 ≤ 888 * 512 := by
      have m := Nat.mul_le_mul (by decide : 2 * 2 ^ 8 ≤ 888) (by decide : 2 ^ 9 ≤ 512)
      rw [Nat.mul_assoc 2, ← Nat.pow_add] at m; exact m
    have prod := Nat.mul_le_mul a b
    have e : 2 ^ 18 * (2 * 2 ^ 17) = 2 * 2 ^ 35 := by rw [Nat.mul_left_comm (2 ^ 18) 2 (2 ^ 17), ← Nat.pow_add]
    rw [e, ← sL2] at prod; exact Nat.le_of_mul_le_mul_left prod (by decide)
  have hHi : B (888 * 512) 2 < 2 ^ 37 := by
    have a : 888 * 512 - 1 < 2 ^ 19 := Nat.lt_of_le_of_lt (Nat.sub_le _ 1)
      (by rw [show (2 : Nat) ^ 19 = 2 ^ 10 * 2 ^ 9 from by rw [← Nat.pow_add], show 2 ^ 9 = 512 from by decide]
          exact Nat.mul_lt_mul_of_pos_right (by decide : 888 < 2 ^ 10) (by decide))
    have b : 888 * 512 ≤ 2 * 2 ^ 18 := by
      have m := Nat.mul_le_mul (by decide : 888 ≤ 2 * 2 ^ 9) (by decide : 512 ≤ 2 ^ 9)
      rw [Nat.mul_assoc 2, ← Nat.pow_add] at m; exact m
    have prod := Nat.mul_lt_mul_of_lt_of_le a b (by decide)
    have e : 2 ^ 19 * (2 * 2 ^ 18) = 2 * 2 ^ 37 := by rw [Nat.mul_left_comm (2 ^ 19) 2 (2 ^ 18), ← Nat.pow_add]
    rw [e, ← sL2] at prod; exact nat_lt_of_mul_lt_left prod
  have hR0 : pcgDenseRows ^ 2 < 2 ^ 36 := by
    have r : pcgDenseRows < 2 ^ 18 := by
      unfold pcgDenseRows; rw [show (2 : Nat) ^ 18 = 2 ^ 8 * 2 ^ 10 from by rw [← Nat.pow_add], show 2 ^ 10 = 1024 from by decide]
      exact Nat.mul_lt_mul_of_pos_right (by decide : 136 < 2 ^ 8) (by decide)
    rw [Nat.pow_two, show (2 : Nat) ^ 36 = 2 ^ 18 * 2 ^ 18 from by rw [← Nat.pow_add]]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_of_lt r)) (Nat.mul_lt_mul_of_pos_left r (Nat.two_pow_pos 18))
  have hSum39 : 2 ^ 36 + 2 * 2 ^ 37 + 2 ^ 36 ≤ 2 ^ 39 := by
    have h8 : ∀ u : Nat, u + 2 * (2 * u) + u ≤ 8 * u := fun _ => by omega
    rw [show (2 : Nat) ^ 37 = 2 * 2 ^ 36 from by rw [Nat.pow_succ'], show (2 : Nat) ^ 39 = 8 * 2 ^ 36 from by rw [show (8 : Nat) = 2 ^ 3 from rfl, ← Nat.pow_add]]
    exact h8 (2 ^ 36)
  have hBounds := l2_cost_and_sq (B (888 * 512) 2) pcgDenseRows (2 ^ 35) (2 ^ 36) (2 ^ 37)
    (2 ^ 22) (2 ^ 52) (2 ^ 70) (2 ^ 74) (2 ^ 39) (Nat.two_pow_pos 35) (Nat.two_pow_pos 37)
    hR0 hLo hHi (by rw [← Nat.pow_add]) (by rw [← Nat.pow_add]) (by rw [← Nat.pow_add])
    (Nat.pow_le_pow_right (by decide) (by decide)) hSum39
  have hPow : 2 ^ 39 * 2 ^ 80 * 2 ^ 180 ≤ 2 ^ 256 * 2 ^ 70 := by
    rw [← Nat.pow_add 2 39 80, show (180 : Nat) = 110 + 70 from rfl, Nat.pow_add 2 110 70,
        ← Nat.mul_assoc (2 ^ 119) (2 ^ 110) (2 ^ 70), ← Nat.pow_add 2 119 110]
    exact Nat.mul_le_mul_right (2 ^ 70) (Nat.pow_le_pow_right (by decide) (by decide))
  exact contra_isd_bound _ (B (888 * 512) 2) (B pcgDepth14Cols 64) (B (pcgDenseRows - 52) 60)
    (2 ^ 39) (2 ^ 80) (2 ^ 180) (2 ^ 256) (2 ^ 70) hPos60
    (Nat.mul_pos (Nat.two_pow_pos 80) (Nat.two_pow_pos 180)) hUp64 hBounds.1 hBounds.2 hPow hBad

theorem tooth_pcg_dense_depth14_stern_dumer_below_256 :
    ¬ sternDumerWorkExceedsPow2 pcgDepth14Cols pcgDenseRows pcgDenseWeightT 2 52 256 := by
  intro hBad
  have h60Le : 60 ≤ pcgDenseRows - 52 := Nat.le_trans
    (Nat.le_trans (by decide : 60 ≤ 1024) (Nat.le_mul_of_pos_left 1024 (by decide : 0 < 135))) (rows_sub_ge 52 (by decide))
  have hUp60 : binom pcgDepth14Cols 60 ≤ 8 ^ 60 * binom (pcgDenseRows - 52) 60 := by
    apply binom_scale_upper_bound 8 h60Le
    rw [Nat.sub_sub]
    have hR := Nat.mul_le_mul_left 8 (rows_sub_ge (52 + 60) (by decide))
    rw [← Nat.mul_assoc 8 135 1024] at hR
    exact Nat.le_trans (by unfold pcgDepth14Cols; exact Nat.mul_le_mul_right 1024 (by decide : 1024 ≤ 8 * 135)) hR
  exact stern_dumer_depth14_contra_gen binom binom_one_right binom_step_right hUp60 (binom_pos h60Le) hBad

/-! ## 6. Constructive Witness Inhabitedness & `#tooth_pair` Assurance Gates -/

theorem witness_accept_box_preimage :
    ∃ z v : Int, inHalfOpenBox rlweAcceptHalfWidth z = true ∧ (-1 ≤ v) ∧ (v ≤ 1) :=
  ⟨-3070, 1, by decide, by decide, by decide⟩

theorem witness_acceptProb_cancellation :
    ∃ (rho : Int → Nat) (M : Nat) (hM : 0 < M) (z v : Int),
      0 < rho (z - v) ∧ rho z ≤ M * rho (z - v) ∧
      ExactRat.eqv (ExactRat.scaleNat (rho (z - v)) (acceptProbExact rho M z v)) ⟨(rho z : Int), M, hM⟩ :=
  ⟨bellToyRho, 4, by decide, 0, 1, by decide, by decide, by decide⟩

theorem witness_dual_lpn_bias :
    ∃ weights : List Nat, weights.length = 64 ∧
      (∀ w ∈ weights, ((32768 : Int) - 2 * (w : Int)).natAbs ≤ 2047) ∧
      ExactRat.lt (ExactRat.abs (parityBias (regularBlockXorOneProb (weights.map depth15TreeRate)))) (ExactRat.twoNegPow 256) :=
  ⟨List.replicate 64 16384, by decide, fun _ hw => by rw [List.eq_of_mem_replicate hw]; decide,
   pcg_dense_dual_lpn_linear_bias_lt_two_neg_256 (List.replicate 64 16384) (by decide)
     (fun _ hw => by rw [List.eq_of_mem_replicate hw]; decide)⟩

theorem witness_depth15_isd :
    ∃ q l : Nat, q ≤ 32 ∧ sternDumerWorkExceedsPow2 pcgDepth15Cols pcgDenseRows pcgDenseWeightT q l 256 :=
  ⟨2, 52, by decide, (pcg_dense_depth15_prange_and_stern_dumer_pq128 2 52 (by decide)).1⟩

end Qsag
end

#verify_constructive Qsag.q192_acceptProb_rounding_le_two_neg_190 Qsag.q192_gaussian_hvzk_statistical_distance Qsag.q192_gaussian_abort_marginal_secret_independent Qsag.acc_transpose_duality Qsag.piling_up_lemma_bernoulli_rat Qsag.piling_up_lemma_regular_blocks_rat Qsag.bernoulli_dual_min_weight_bias_lt_two_neg_256

#tooth_pair Qsag.rlwe_accept_box_preimage_in_proposal_box vs Qsag.tooth_tight_clipping_loses_boundary_preimage
#tooth_pair Qsag.acceptProbExact_safe_cancels_shift vs Qsag.tooth_omitting_rejection_scaling_breaks_hvzk
#tooth_pair Qsag.pcg_dense_dual_lpn_linear_bias_lt_two_neg_256 vs Qsag.tooth_omitting_accumulator_collapses_dual_lpn_bias
#tooth_pair Qsag.pcg_dense_depth15_prange_and_stern_dumer_pq128 vs Qsag.tooth_pcg_dense_depth14_stern_dumer_below_256

#verify_inhabited Qsag.rlwe_accept_box_preimage_in_proposal_box Qsag.witness_accept_box_preimage
#verify_inhabited Qsag.acceptProbExact_safe_cancels_shift Qsag.witness_acceptProb_cancellation
#verify_inhabited Qsag.pcg_dense_dual_lpn_linear_bias_lt_two_neg_256 Qsag.witness_dual_lpn_bias
#verify_inhabited Qsag.pcg_dense_depth15_prange_and_stern_dumer_pq128 Qsag.witness_depth15_isd
