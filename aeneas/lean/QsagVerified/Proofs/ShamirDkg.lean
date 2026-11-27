module
import all QsagVerified.Funs

public import QsagVerified.Proofs.Common
public import QsagVerified.Proofs.Gf256

public section

namespace qsag_verified.proofs

open Aeneas Aeneas.Std Result ControlFlow Error
open qsag_verified

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

attribute [-simp] BitVec.getLsbD_eq_getElem
attribute [local simp] UScalar.val UScalarTy.numBits

/-! ## Arbitrary-length binary-field Horner evaluation -/

/-- Horner recurrence on the first `n` coefficients, consuming highest degree first. -/
@[expose]
def pureHornerGf256Prefix (coeffs : List tower.Gf256) (x : tower.Gf256) :
    Nat → tower.Gf256 → tower.Gf256
  | 0, acc => acc
  | n + 1, acc => pureHornerGf256Prefix coeffs x n
      (pureGf256Mul acc x ^^^ coeffs.getD n 0#u8)

@[expose]
def pureHornerGf256 (coeffs : List tower.Gf256) (x : tower.Gf256) : tower.Gf256 :=
  pureHornerGf256Prefix coeffs x coeffs.length 0#u8

private theorem horner_gf256_fuel (coeffs : Slice tower.Gf256) (x : tower.Gf256)
    (n : Nat) (rem : Std.Usize) (acc : tower.Gf256)
    (hr : rem.val = n) (hn : n ≤ coeffs.val.length) :
    loopFuel (n + 1)
      (fun (a, r) => threshold.shamir_eval_poly_gf256_loop.body coeffs x a r)
      (acc, rem) = .ok (pureHornerGf256Prefix coeffs.val x n acc) := by
  induction n generalizing rem acc with
  | zero =>
    have hz : rem = 0#usize := UScalar.eq_of_val_eq hr
    subst rem
    simp [loopFuel, threshold.shamir_eval_poly_gf256_loop.body,
      pureHornerGf256Prefix]
  | succ n ih =>
    have hp : rem > 0#usize := BitVec.lt_def.mpr (by change 0 < rem.val; rw [hr]; exact Nat.zero_lt_succ _)
    have hle : (1#usize).val ≤ rem.val := by change 1 ≤ rem.val; rw [hr]; exact Nat.succ_le_succ (Nat.zero_le _)
    let r : Std.Usize := ⟨rem.bv - (1#usize).bv⟩
    have hs : (rem - 1#usize : Result Std.Usize) = .ok r := by
      simp only [hSub_uscalar_eq, hle, ite_true]; rfl
    have hr' : r.val = n := by
      change (rem.bv - (1#usize).bv).toNat = n
      rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle)]
      change rem.val - 1 = n
      rw [hr]; exact Nat.succ_sub_one n
    have hi : r.val < coeffs.val.length := by rw [hr']; exact Nat.lt_of_succ_le hn
    have hget : Slice.index_usize coeffs r = .ok (coeffs.val.getD n 0#u8) := by
      simp only [Slice.index_usize, dite_eq_left_of_eq_true (eq_true hi)]
      rw [List.getElem_eq_getD 0#u8, hr']
    have step : threshold.shamir_eval_poly_gf256_loop.body coeffs x acc rem =
        .ok (.cont (pureGf256Mul acc x ^^^ coeffs.val.getD n 0#u8, r)) := by
      simp only [threshold.shamir_eval_poly_gf256_loop.body, hp, ite_eq_left_of_eq_true,
        hs, bind_eq_result_bind, result_bind_ok, gf256_mul_eq_pure, hget,
        tower.gf256_add, lift_eq_ok]
    rw [loopFuel_succ]
    change (threshold.shamir_eval_poly_gf256_loop.body coeffs x acc rem >>= _) = _
    rw [step]
    exact ih r _ hr' (Nat.le_trans (Nat.le_succ n) hn)

theorem shamir_eval_poly_gf256_spec (coeffs : Slice tower.Gf256) (x : tower.Gf256) :
    threshold.shamir_eval_poly_gf256 coeffs x = .ok (pureHornerGf256 coeffs.val x) := by
  unfold threshold.shamir_eval_poly_gf256 threshold.shamir_eval_poly_gf256_loop
  apply loop_ok_of_loopFuel (fuel := coeffs.val.length + 1)
  · simpa only [Slice.len_val] using usize_lt_loopMaxFuel (Slice.len coeffs)
  · exact horner_gf256_fuel coeffs x coeffs.val.length (Slice.len coeffs)
      0#u8 (Slice.len_val coeffs) (Nat.le_refl _)

theorem shamir_validate_points_gf256_rejects_empty (points : Slice tower.Gf256)
    (h : points.val = []) : threshold.shamir_validate_points_gf256 points = .ok false := by
  have hn : Slice.len points = 0#usize := UScalar.eq_of_val_eq (by simp [h])
  simp [threshold.shamir_validate_points_gf256, hn]

theorem shamir_validate_points_gf256_3_spec (x0 x1 x2 : tower.Gf256) :
    threshold.shamir_validate_points_gf256
      (Array.to_slice (Array.make 3#usize [x0, x1, x2])) =
      .ok (decide (x0 ≠ 0#u8 ∧ x1 ≠ 0#u8 ∧ x2 ≠ 0#u8 ∧
        x0 ≠ x1 ∧ x0 ≠ x2 ∧ x1 ≠ x2)) := by
  have step01 : (0#usize + 1#usize : Result Std.Usize) = .ok 1#usize := rfl
  have step12 : (1#usize + 1#usize : Result Std.Usize) = .ok 2#usize := rfl
  have step23 : (2#usize + 1#usize : Result Std.Usize) = .ok 3#usize := rfl
  let p := Array.to_slice (Array.make 3#usize [x0, x1, x2])
  have p_idx0 : Slice.index_usize p 0#usize = .ok x0 := by rfl
  have p_idx1 : Slice.index_usize p 1#usize = .ok x1 := by rfl
  have p_idx2 : Slice.index_usize p 2#usize = .ok x2 := by rfl
  have p_len : Slice.len p = 3#usize := by rfl
  have h2 (ok1 : Bool) :
      threshold.shamir_validate_points_gf256_loop0_loop0 p 3#usize ok1 2#usize 3#usize =
        .ok ok1 := by
    unfold threshold.shamir_validate_points_gf256_loop0_loop0
    apply loop_ok_of_loopFuel (fuel := 1) (by decide)
    rfl
  have h1 (ok1 : Bool) :
      threshold.shamir_validate_points_gf256_loop0_loop0 p 3#usize ok1 1#usize 2#usize =
        .ok (if x1 = x2 then false else ok1) := by
    unfold threshold.shamir_validate_points_gf256_loop0_loop0
    apply loop_ok_of_loopFuel (fuel := 2) (by decide)
    by_cases h : x1 = x2 <;>
      simp [step23, bind_eq_result_bind, result_bind_ok, loopFuel, threshold.shamir_validate_points_gf256_loop0_loop0.body,
        p_idx1, p_idx2, h]
  have h0 (ok1 : Bool) :
      threshold.shamir_validate_points_gf256_loop0_loop0 p 3#usize ok1 0#usize 1#usize =
        .ok (if x0 = x2 then false else if x0 = x1 then false else ok1) := by
    unfold threshold.shamir_validate_points_gf256_loop0_loop0
    apply loop_ok_of_loopFuel (fuel := 3) (by decide)
    by_cases ha : x0 = x1 <;> by_cases hb : x0 = x2 <;>
      simp [step12, bind_eq_result_bind, result_bind_ok, loopFuel, threshold.shamir_validate_points_gf256_loop0_loop0.body,
        p_idx0, p_idx1, p_idx2, ha, hb] <;> simp_all
  change threshold.shamir_validate_points_gf256 p = _
  unfold threshold.shamir_validate_points_gf256
  rw [p_len]
  change threshold.shamir_validate_points_gf256_loop0 p 3#usize true 0#usize = _
  unfold threshold.shamir_validate_points_gf256_loop0
  apply loop_ok_of_loopFuel (fuel := 4) (by decide)
  by_cases hz0 : x0 = 0#u8
  · simp [step01, bind_eq_result_bind, result_bind_ok, loopFuel, threshold.shamir_validate_points_gf256_loop0.body,
      h0, h1, h2, p_idx0, p_idx1, p_idx2, hz0]
  by_cases hz1 : x1 = 0#u8
  · simp [step01, bind_eq_result_bind, result_bind_ok, loopFuel, threshold.shamir_validate_points_gf256_loop0.body,
      h0, h1, h2, p_idx0, p_idx1, p_idx2, hz0, hz1]
  by_cases hz2 : x2 = 0#u8
  · simp [step01, bind_eq_result_bind, result_bind_ok, loopFuel, threshold.shamir_validate_points_gf256_loop0.body,
      h0, h1, h2, p_idx0, p_idx1, p_idx2, hz0, hz1, hz2]
  by_cases he01 : x0 = x1
  · simp [step01, bind_eq_result_bind, result_bind_ok, loopFuel, threshold.shamir_validate_points_gf256_loop0.body,
      h0, h1, h2, p_idx0, p_idx1, p_idx2, hz1, hz2, he01]
  by_cases he02 : x0 = x2
  · simp [step01, bind_eq_result_bind, result_bind_ok, loopFuel, threshold.shamir_validate_points_gf256_loop0.body,
      h0, h1, h2, p_idx0, p_idx1, p_idx2, hz1, hz2, he02]
  by_cases he12 : x1 = x2
  · simp [step01, bind_eq_result_bind, result_bind_ok, loopFuel, threshold.shamir_validate_points_gf256_loop0.body,
      h0, h1, h2, p_idx0, p_idx1, p_idx2, hz0, hz2, he02, he12]
  simp [step01, bind_eq_result_bind, result_bind_ok, loopFuel, threshold.shamir_validate_points_gf256_loop0.body,
      h0, h1, h2, p_idx0, p_idx1, p_idx2, hz0, hz1, hz2, he01, he02, he12]

theorem shamir_lagrange_at_zero_gf256_rejects_invalid
    (points shares : Slice tower.Gf256)
    (h : points.val = [] ∨ shares.val.length ≠ points.val.length) :
    threshold.shamir_lagrange_at_zero_gf256 points shares = .ok none := by
  rcases h with h | h
  · have hn : Slice.len points = 0#usize := UScalar.eq_of_val_eq (by simp [h])
    simp [threshold.shamir_lagrange_at_zero_gf256, hn]
  · have hn : Slice.len shares ≠ Slice.len points := by
      intro he; apply h
      simpa only [Slice.len_val] using congrArg UScalar.val he
    unfold threshold.shamir_lagrange_at_zero_gf256
    dsimp only
    by_cases h0 : Slice.len points = 0#usize <;> simp [h0, hn]

/-! ## Algebraic Shamir reconstruction over the generated loops -/


private theorem u8_xor_left_comm (a b c : Std.U8) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← u8_xor_assoc, u8_xor_comm a b, u8_xor_assoc]

private theorem u8_xor_eq_zero (a b : Std.U8) : a ^^^ b = 0#u8 ↔ a = b := by
  constructor
  · intro h
    have he := congrArg (fun x => x ^^^ b) h
    rw [u8_xor_assoc, u8_xor_self, u8_xor_zero, u8_zero_xor] at he
    exact he
  · rintro rfl; exact u8_xor_self _

private theorem pureGf256Mul_one_left (a : Std.U8) : pureGf256Mul 1#u8 a = a := by
  rw [pureGf256Mul_comm, pureGf256Mul_one]

private theorem pureGf256Mul_left_comm (a b c : Std.U8) :
    pureGf256Mul a (pureGf256Mul b c) = pureGf256Mul b (pureGf256Mul a c) := by
  rw [← pureGf256Mul_assoc, pureGf256Mul_comm a b, pureGf256Mul_assoc]

private theorem gf256_inv_pure_nonzero (a : Std.U8) (ha : a ≠ 0#u8) :
    tower.gf256_inv a = .ok (some (pureGf256Inv a)) := by
  have hn : pureGf256Inv a ≠ 0#u8 := by
    intro h
    have hi := pureGf256Mul_inv a ha
    rw [h, pureGf256Mul_zero] at hi
    exact (by decide : (0#u8 : Std.U8) ≠ 1#u8) hi
  simp only [tower.gf256_inv, gf256_inv_or_zero_eq_pure, bind_eq_result_bind,
    result_bind_ok, hn, ite_false]

abbrev gfSlice2 (a b : Std.U8) : Slice Std.U8 :=
  Std.Array.to_slice (Std.Array.make 2#usize [a, b])

abbrev gfSlice3 (a b c : Std.U8) : Slice Std.U8 :=
  Std.Array.to_slice (Std.Array.make 3#usize [a, b, c])

private theorem gf256_product_ne_zero (a b : Std.U8) (ha : a ≠ 0#u8) (hb : b ≠ 0#u8) :
    pureGf256Mul a b ≠ 0#u8 := by
  intro h
  rcases (pureGf256Mul_eq_zero_iff a b).mp h with h | h
  · exact ha h
  · exact hb h

private theorem lagrange_weight_2_0 (x0 x1 : Std.U8)
    (hz0 : x0 ≠ 0#u8) (_hz1 : x1 ≠ 0#u8)
    (hne01 : x0 ≠ x1) :
    threshold.shamir_lagrange_weight_zero_gf256 (gfSlice2 x0 x1) 0#usize =
      .ok (some (pureGf256Mul (x1) (pureGf256Inv (x0 ^^^ x1)))) := by
  have hd01 : x0 ^^^ x1 ≠ 0#u8 := fun h => hne01 ((u8_xor_eq_zero _ _).mp h)
  have hd10 : x1 ^^^ x0 ≠ 0#u8 := fun h => hne01.symm ((u8_xor_eq_zero _ _).mp h)
  have hden : (x0 ^^^ x1) ≠ 0#u8 := hd01
  have hl : threshold.shamir_lagrange_weight_zero_gf256_loop (gfSlice2 x0 x1)
      0#usize 2#usize x0 1#u8 1#u8 true 0#usize = .ok (x1, x0 ^^^ x1, true) := by
    unfold threshold.shamir_lagrange_weight_zero_gf256_loop
    apply loop_ok_of_loopFuel (fuel := 3) (by decide)
    simp [loopFuel, threshold.shamir_lagrange_weight_zero_gf256_loop.body,
      gfSlice2, Std.Array.to_slice, Std.Array.make, Slice.index_usize,
      tower.gf256_add, gf256_mul_eq_pure,
      hd01]
    constructor <;> rw [pureGf256Mul_one_left]
  have hinv := gf256_inv_pure_nonzero (x0 ^^^ x1) hden
  unfold threshold.shamir_lagrange_weight_zero_gf256
  have hlen : Slice.len (gfSlice2 x0 x1) = 2#usize := rfl
  have hidx : Slice.index_usize (gfSlice2 x0 x1) 0#usize = .ok x0 := rfl
  simp only [hlen, show ¬ (0#usize : Std.Usize) >= 2#usize from by decide,
    ite_false, hidx, bind_eq_result_bind, result_bind_ok, hz0, hl,
    ite_true, hinv, gf256_mul_eq_pure]

private theorem lagrange_weight_2_1 (x0 x1 : Std.U8)
    (_hz0 : x0 ≠ 0#u8) (hz1 : x1 ≠ 0#u8)
    (hne01 : x0 ≠ x1) :
    threshold.shamir_lagrange_weight_zero_gf256 (gfSlice2 x0 x1) 1#usize =
      .ok (some (pureGf256Mul (x0) (pureGf256Inv (x1 ^^^ x0)))) := by
  have hd01 : x0 ^^^ x1 ≠ 0#u8 := fun h => hne01 ((u8_xor_eq_zero _ _).mp h)
  have hd10 : x1 ^^^ x0 ≠ 0#u8 := fun h => hne01.symm ((u8_xor_eq_zero _ _).mp h)
  have hden : (x1 ^^^ x0) ≠ 0#u8 := hd10
  have hl : threshold.shamir_lagrange_weight_zero_gf256_loop (gfSlice2 x0 x1)
      1#usize 2#usize x1 1#u8 1#u8 true 0#usize = .ok (x0, x1 ^^^ x0, true) := by
    unfold threshold.shamir_lagrange_weight_zero_gf256_loop
    apply loop_ok_of_loopFuel (fuel := 3) (by decide)
    simp [loopFuel, threshold.shamir_lagrange_weight_zero_gf256_loop.body,
      gfSlice2, Std.Array.to_slice, Std.Array.make, Slice.index_usize,
      tower.gf256_add, gf256_mul_eq_pure,
      hd10]
    constructor <;> rw [pureGf256Mul_one_left]
  have hinv := gf256_inv_pure_nonzero (x1 ^^^ x0) hden
  unfold threshold.shamir_lagrange_weight_zero_gf256
  have hlen : Slice.len (gfSlice2 x0 x1) = 2#usize := rfl
  have hidx : Slice.index_usize (gfSlice2 x0 x1) 1#usize = .ok x1 := rfl
  simp only [hlen, show ¬ (1#usize : Std.Usize) >= 2#usize from by decide,
    ite_false, hidx, bind_eq_result_bind, result_bind_ok, hz1, hl,
    ite_true, hinv, gf256_mul_eq_pure]

private theorem lagrange_weight_3_0 (x0 x1 x2 : Std.U8)
    (hz0 : x0 ≠ 0#u8) (_hz1 : x1 ≠ 0#u8) (_hz2 : x2 ≠ 0#u8)
    (hne01 : x0 ≠ x1) (hne02 : x0 ≠ x2) (hne12 : x1 ≠ x2) :
    threshold.shamir_lagrange_weight_zero_gf256 (gfSlice3 x0 x1 x2) 0#usize =
      .ok (some (pureGf256Mul (pureGf256Mul x1 x2) (pureGf256Inv (pureGf256Mul (x0 ^^^ x1) (x0 ^^^ x2))))) := by
  have hd01 : x0 ^^^ x1 ≠ 0#u8 := fun h => hne01 ((u8_xor_eq_zero _ _).mp h)
  have hd02 : x0 ^^^ x2 ≠ 0#u8 := fun h => hne02 ((u8_xor_eq_zero _ _).mp h)
  have hd10 : x1 ^^^ x0 ≠ 0#u8 := fun h => hne01.symm ((u8_xor_eq_zero _ _).mp h)
  have hd12 : x1 ^^^ x2 ≠ 0#u8 := fun h => hne12 ((u8_xor_eq_zero _ _).mp h)
  have hd20 : x2 ^^^ x0 ≠ 0#u8 := fun h => hne02.symm ((u8_xor_eq_zero _ _).mp h)
  have hd21 : x2 ^^^ x1 ≠ 0#u8 := fun h => hne12.symm ((u8_xor_eq_zero _ _).mp h)
  have hden : (pureGf256Mul (x0 ^^^ x1) (x0 ^^^ x2)) ≠ 0#u8 := gf256_product_ne_zero _ _ hd01 hd02
  have hl : threshold.shamir_lagrange_weight_zero_gf256_loop (gfSlice3 x0 x1 x2)
      0#usize 3#usize x0 1#u8 1#u8 true 0#usize = .ok (pureGf256Mul x1 x2, pureGf256Mul (x0 ^^^ x1) (x0 ^^^ x2), true) := by
    unfold threshold.shamir_lagrange_weight_zero_gf256_loop
    apply loop_ok_of_loopFuel (fuel := 4) (by decide)
    simp [loopFuel, threshold.shamir_lagrange_weight_zero_gf256_loop.body,
      gfSlice3, Std.Array.to_slice, Std.Array.make, Slice.index_usize,
      tower.gf256_add, gf256_mul_eq_pure,
      hd01, hd02]
    constructor <;> rw [pureGf256Mul_one_left]
  have hinv := gf256_inv_pure_nonzero (pureGf256Mul (x0 ^^^ x1) (x0 ^^^ x2)) hden
  unfold threshold.shamir_lagrange_weight_zero_gf256
  have hlen : Slice.len (gfSlice3 x0 x1 x2) = 3#usize := rfl
  have hidx : Slice.index_usize (gfSlice3 x0 x1 x2) 0#usize = .ok x0 := rfl
  simp only [hlen, show ¬ (0#usize : Std.Usize) >= 3#usize from by decide,
    ite_false, hidx, bind_eq_result_bind, result_bind_ok, hz0, hl,
    ite_true, hinv, gf256_mul_eq_pure]

private theorem lagrange_weight_3_1 (x0 x1 x2 : Std.U8)
    (_hz0 : x0 ≠ 0#u8) (hz1 : x1 ≠ 0#u8) (_hz2 : x2 ≠ 0#u8)
    (hne01 : x0 ≠ x1) (hne02 : x0 ≠ x2) (hne12 : x1 ≠ x2) :
    threshold.shamir_lagrange_weight_zero_gf256 (gfSlice3 x0 x1 x2) 1#usize =
      .ok (some (pureGf256Mul (pureGf256Mul x0 x2) (pureGf256Inv (pureGf256Mul (x1 ^^^ x0) (x1 ^^^ x2))))) := by
  have hd01 : x0 ^^^ x1 ≠ 0#u8 := fun h => hne01 ((u8_xor_eq_zero _ _).mp h)
  have hd02 : x0 ^^^ x2 ≠ 0#u8 := fun h => hne02 ((u8_xor_eq_zero _ _).mp h)
  have hd10 : x1 ^^^ x0 ≠ 0#u8 := fun h => hne01.symm ((u8_xor_eq_zero _ _).mp h)
  have hd12 : x1 ^^^ x2 ≠ 0#u8 := fun h => hne12 ((u8_xor_eq_zero _ _).mp h)
  have hd20 : x2 ^^^ x0 ≠ 0#u8 := fun h => hne02.symm ((u8_xor_eq_zero _ _).mp h)
  have hd21 : x2 ^^^ x1 ≠ 0#u8 := fun h => hne12.symm ((u8_xor_eq_zero _ _).mp h)
  have hden : (pureGf256Mul (x1 ^^^ x0) (x1 ^^^ x2)) ≠ 0#u8 := gf256_product_ne_zero _ _ hd10 hd12
  have hl : threshold.shamir_lagrange_weight_zero_gf256_loop (gfSlice3 x0 x1 x2)
      1#usize 3#usize x1 1#u8 1#u8 true 0#usize = .ok (pureGf256Mul x0 x2, pureGf256Mul (x1 ^^^ x0) (x1 ^^^ x2), true) := by
    unfold threshold.shamir_lagrange_weight_zero_gf256_loop
    apply loop_ok_of_loopFuel (fuel := 4) (by decide)
    simp [loopFuel, threshold.shamir_lagrange_weight_zero_gf256_loop.body,
      gfSlice3, Std.Array.to_slice, Std.Array.make, Slice.index_usize,
      tower.gf256_add, gf256_mul_eq_pure,
      hd10, hd12]
    constructor <;> rw [pureGf256Mul_one_left]
  have hinv := gf256_inv_pure_nonzero (pureGf256Mul (x1 ^^^ x0) (x1 ^^^ x2)) hden
  unfold threshold.shamir_lagrange_weight_zero_gf256
  have hlen : Slice.len (gfSlice3 x0 x1 x2) = 3#usize := rfl
  have hidx : Slice.index_usize (gfSlice3 x0 x1 x2) 1#usize = .ok x1 := rfl
  simp only [hlen, show ¬ (1#usize : Std.Usize) >= 3#usize from by decide,
    ite_false, hidx, bind_eq_result_bind, result_bind_ok, hz1, hl,
    ite_true, hinv, gf256_mul_eq_pure]

private theorem lagrange_weight_3_2 (x0 x1 x2 : Std.U8)
    (_hz0 : x0 ≠ 0#u8) (_hz1 : x1 ≠ 0#u8) (hz2 : x2 ≠ 0#u8)
    (hne01 : x0 ≠ x1) (hne02 : x0 ≠ x2) (hne12 : x1 ≠ x2) :
    threshold.shamir_lagrange_weight_zero_gf256 (gfSlice3 x0 x1 x2) 2#usize =
      .ok (some (pureGf256Mul (pureGf256Mul x0 x1) (pureGf256Inv (pureGf256Mul (x2 ^^^ x0) (x2 ^^^ x1))))) := by
  have hd01 : x0 ^^^ x1 ≠ 0#u8 := fun h => hne01 ((u8_xor_eq_zero _ _).mp h)
  have hd02 : x0 ^^^ x2 ≠ 0#u8 := fun h => hne02 ((u8_xor_eq_zero _ _).mp h)
  have hd10 : x1 ^^^ x0 ≠ 0#u8 := fun h => hne01.symm ((u8_xor_eq_zero _ _).mp h)
  have hd12 : x1 ^^^ x2 ≠ 0#u8 := fun h => hne12 ((u8_xor_eq_zero _ _).mp h)
  have hd20 : x2 ^^^ x0 ≠ 0#u8 := fun h => hne02.symm ((u8_xor_eq_zero _ _).mp h)
  have hd21 : x2 ^^^ x1 ≠ 0#u8 := fun h => hne12.symm ((u8_xor_eq_zero _ _).mp h)
  have hden : (pureGf256Mul (x2 ^^^ x0) (x2 ^^^ x1)) ≠ 0#u8 := gf256_product_ne_zero _ _ hd20 hd21
  have hl : threshold.shamir_lagrange_weight_zero_gf256_loop (gfSlice3 x0 x1 x2)
      2#usize 3#usize x2 1#u8 1#u8 true 0#usize = .ok (pureGf256Mul x0 x1, pureGf256Mul (x2 ^^^ x0) (x2 ^^^ x1), true) := by
    unfold threshold.shamir_lagrange_weight_zero_gf256_loop
    apply loop_ok_of_loopFuel (fuel := 4) (by decide)
    simp [loopFuel, threshold.shamir_lagrange_weight_zero_gf256_loop.body,
      gfSlice3, Std.Array.to_slice, Std.Array.make, Slice.index_usize,
      tower.gf256_add, gf256_mul_eq_pure,
      hd20, hd21]
    constructor <;> rw [pureGf256Mul_one_left]
  have hinv := gf256_inv_pure_nonzero (pureGf256Mul (x2 ^^^ x0) (x2 ^^^ x1)) hden
  unfold threshold.shamir_lagrange_weight_zero_gf256
  have hlen : Slice.len (gfSlice3 x0 x1 x2) = 3#usize := rfl
  have hidx : Slice.index_usize (gfSlice3 x0 x1 x2) 2#usize = .ok x2 := rfl
  simp only [hlen, show ¬ (2#usize : Std.Usize) >= 3#usize from by decide,
    ite_false, hidx, bind_eq_result_bind, result_bind_ok, hz2, hl,
    ite_true, hinv, gf256_mul_eq_pure]

private theorem lagrange_sum_2 (x0 x1 y0 y1 : Std.U8)
    (hz0 : x0 ≠ 0#u8) (hz1 : x1 ≠ 0#u8)
    (hne01 : x0 ≠ x1) :
    threshold.shamir_lagrange_at_zero_gf256 (gfSlice2 x0 x1) (gfSlice2 y0 y1) =
      .ok (some (pureGf256Mul y0 (pureGf256Mul (x1) (pureGf256Inv (x0 ^^^ x1))) ^^^ pureGf256Mul y1 (pureGf256Mul (x0) (pureGf256Inv (x1 ^^^ x0))))) := by
  have hw0 := lagrange_weight_2_0 x0 x1 hz0 hz1 hne01
  have hw1 := lagrange_weight_2_1 x0 x1 hz0 hz1 hne01
  have step0 (acc : Std.U8) (v : Bool) :
      threshold.shamir_lagrange_at_zero_gf256_loop.body (gfSlice2 x0 x1) (gfSlice2 y0 y1)
        2#usize acc v 0#usize = .ok (.cont (acc ^^^ pureGf256Mul y0 (pureGf256Mul (x1) (pureGf256Inv (x0 ^^^ x1))), v, 1#usize)) := by
    unfold threshold.shamir_lagrange_at_zero_gf256_loop.body
    rw [ite_eq_left (by decide), hw0]
    have hget : Slice.index_usize (gfSlice2 y0 y1) 0#usize = .ok y0 := rfl
    simp only [bind_eq_result_bind, result_bind_ok, hget, gf256_mul_eq_pure, tower.gf256_add]
    rfl
  have step1 (acc : Std.U8) (v : Bool) :
      threshold.shamir_lagrange_at_zero_gf256_loop.body (gfSlice2 x0 x1) (gfSlice2 y0 y1)
        2#usize acc v 1#usize = .ok (.cont (acc ^^^ pureGf256Mul y1 (pureGf256Mul (x0) (pureGf256Inv (x1 ^^^ x0))), v, 2#usize)) := by
    unfold threshold.shamir_lagrange_at_zero_gf256_loop.body
    rw [ite_eq_left (by decide), hw1]
    have hget : Slice.index_usize (gfSlice2 y0 y1) 1#usize = .ok y1 := rfl
    simp only [bind_eq_result_bind, result_bind_ok, hget, gf256_mul_eq_pure, tower.gf256_add]
    rfl
  have stop (acc : Std.U8) (v : Bool) :
      threshold.shamir_lagrange_at_zero_gf256_loop.body (gfSlice2 x0 x1) (gfSlice2 y0 y1)
        2#usize acc v 2#usize = .ok (.done (acc, v)) := by
    unfold threshold.shamir_lagrange_at_zero_gf256_loop.body
    rw [ite_eq_right (by decide)]
  have hl : threshold.shamir_lagrange_at_zero_gf256_loop (gfSlice2 x0 x1) (gfSlice2 y0 y1)
      2#usize 0#u8 true 0#usize = .ok (pureGf256Mul y0 (pureGf256Mul (x1) (pureGf256Inv (x0 ^^^ x1))) ^^^ pureGf256Mul y1 (pureGf256Mul (x0) (pureGf256Inv (x1 ^^^ x0))), true) := by
    unfold threshold.shamir_lagrange_at_zero_gf256_loop
    apply loop_ok_of_loopFuel (fuel := 3) (by decide)
    rw [loopFuel_succ]
    dsimp only
    rw [step0, result_bind_ok]
    dsimp only
    rw [loopFuel_succ]
    dsimp only
    rw [step1, result_bind_ok]
    dsimp only
    rw [loopFuel_succ]
    dsimp only
    rw [stop, result_bind_ok, u8_zero_xor]

  unfold threshold.shamir_lagrange_at_zero_gf256
  have hlen : Slice.len (gfSlice2 x0 x1) = 2#usize := rfl
  have hslen : Slice.len (gfSlice2 y0 y1) = 2#usize := rfl
  simp only [hlen, hslen, show (2#usize : Std.Usize) ≠ 0#usize from by decide,
    ite_false, bne_self_eq_false, Bool.false_eq_true, hl, bind_eq_result_bind,
    result_bind_ok, ite_true]

private theorem lagrange_sum_3 (x0 x1 x2 y0 y1 y2 : Std.U8)
    (hz0 : x0 ≠ 0#u8) (hz1 : x1 ≠ 0#u8) (hz2 : x2 ≠ 0#u8)
    (hne01 : x0 ≠ x1) (hne02 : x0 ≠ x2) (hne12 : x1 ≠ x2) :
    threshold.shamir_lagrange_at_zero_gf256 (gfSlice3 x0 x1 x2) (gfSlice3 y0 y1 y2) =
      .ok (some (pureGf256Mul y0 (pureGf256Mul (pureGf256Mul x1 x2) (pureGf256Inv (pureGf256Mul (x0 ^^^ x1) (x0 ^^^ x2)))) ^^^ pureGf256Mul y1 (pureGf256Mul (pureGf256Mul x0 x2) (pureGf256Inv (pureGf256Mul (x1 ^^^ x0) (x1 ^^^ x2)))) ^^^ pureGf256Mul y2 (pureGf256Mul (pureGf256Mul x0 x1) (pureGf256Inv (pureGf256Mul (x2 ^^^ x0) (x2 ^^^ x1)))))) := by
  have hw0 := lagrange_weight_3_0 x0 x1 x2 hz0 hz1 hz2 hne01 hne02 hne12
  have hw1 := lagrange_weight_3_1 x0 x1 x2 hz0 hz1 hz2 hne01 hne02 hne12
  have hw2 := lagrange_weight_3_2 x0 x1 x2 hz0 hz1 hz2 hne01 hne02 hne12
  have step0 (acc : Std.U8) (v : Bool) :
      threshold.shamir_lagrange_at_zero_gf256_loop.body (gfSlice3 x0 x1 x2) (gfSlice3 y0 y1 y2)
        3#usize acc v 0#usize = .ok (.cont (acc ^^^ pureGf256Mul y0 (pureGf256Mul (pureGf256Mul x1 x2) (pureGf256Inv (pureGf256Mul (x0 ^^^ x1) (x0 ^^^ x2)))), v, 1#usize)) := by
    unfold threshold.shamir_lagrange_at_zero_gf256_loop.body
    rw [ite_eq_left (by decide), hw0]
    have hget : Slice.index_usize (gfSlice3 y0 y1 y2) 0#usize = .ok y0 := rfl
    simp only [bind_eq_result_bind, result_bind_ok, hget, gf256_mul_eq_pure, tower.gf256_add]
    rfl
  have step1 (acc : Std.U8) (v : Bool) :
      threshold.shamir_lagrange_at_zero_gf256_loop.body (gfSlice3 x0 x1 x2) (gfSlice3 y0 y1 y2)
        3#usize acc v 1#usize = .ok (.cont (acc ^^^ pureGf256Mul y1 (pureGf256Mul (pureGf256Mul x0 x2) (pureGf256Inv (pureGf256Mul (x1 ^^^ x0) (x1 ^^^ x2)))), v, 2#usize)) := by
    unfold threshold.shamir_lagrange_at_zero_gf256_loop.body
    rw [ite_eq_left (by decide), hw1]
    have hget : Slice.index_usize (gfSlice3 y0 y1 y2) 1#usize = .ok y1 := rfl
    simp only [bind_eq_result_bind, result_bind_ok, hget, gf256_mul_eq_pure, tower.gf256_add]
    rfl
  have step2 (acc : Std.U8) (v : Bool) :
      threshold.shamir_lagrange_at_zero_gf256_loop.body (gfSlice3 x0 x1 x2) (gfSlice3 y0 y1 y2)
        3#usize acc v 2#usize = .ok (.cont (acc ^^^ pureGf256Mul y2 (pureGf256Mul (pureGf256Mul x0 x1) (pureGf256Inv (pureGf256Mul (x2 ^^^ x0) (x2 ^^^ x1)))), v, 3#usize)) := by
    unfold threshold.shamir_lagrange_at_zero_gf256_loop.body
    rw [ite_eq_left (by decide), hw2]
    have hget : Slice.index_usize (gfSlice3 y0 y1 y2) 2#usize = .ok y2 := rfl
    simp only [bind_eq_result_bind, result_bind_ok, hget, gf256_mul_eq_pure, tower.gf256_add]
    rfl
  have stop (acc : Std.U8) (v : Bool) :
      threshold.shamir_lagrange_at_zero_gf256_loop.body (gfSlice3 x0 x1 x2) (gfSlice3 y0 y1 y2)
        3#usize acc v 3#usize = .ok (.done (acc, v)) := by
    unfold threshold.shamir_lagrange_at_zero_gf256_loop.body
    rw [ite_eq_right (by decide)]
  have hl : threshold.shamir_lagrange_at_zero_gf256_loop (gfSlice3 x0 x1 x2) (gfSlice3 y0 y1 y2)
      3#usize 0#u8 true 0#usize = .ok (pureGf256Mul y0 (pureGf256Mul (pureGf256Mul x1 x2) (pureGf256Inv (pureGf256Mul (x0 ^^^ x1) (x0 ^^^ x2)))) ^^^ pureGf256Mul y1 (pureGf256Mul (pureGf256Mul x0 x2) (pureGf256Inv (pureGf256Mul (x1 ^^^ x0) (x1 ^^^ x2)))) ^^^ pureGf256Mul y2 (pureGf256Mul (pureGf256Mul x0 x1) (pureGf256Inv (pureGf256Mul (x2 ^^^ x0) (x2 ^^^ x1)))), true) := by
    unfold threshold.shamir_lagrange_at_zero_gf256_loop
    apply loop_ok_of_loopFuel (fuel := 4) (by decide)
    rw [loopFuel_succ]
    dsimp only
    rw [step0, result_bind_ok]
    dsimp only
    rw [loopFuel_succ]
    dsimp only
    rw [step1, result_bind_ok]
    dsimp only
    rw [loopFuel_succ]
    dsimp only
    rw [step2, result_bind_ok]
    dsimp only
    rw [loopFuel_succ]
    dsimp only
    rw [stop, result_bind_ok, u8_zero_xor]

  unfold threshold.shamir_lagrange_at_zero_gf256
  have hlen : Slice.len (gfSlice3 x0 x1 x2) = 3#usize := rfl
  have hslen : Slice.len (gfSlice3 y0 y1 y2) = 3#usize := rfl
  simp only [hlen, hslen, show (3#usize : Std.Usize) ≠ 0#usize from by decide,
    ite_false, bne_self_eq_false, Bool.false_eq_true, hl, bind_eq_result_bind,
    result_bind_ok, ite_true]

private theorem u8_xor_cancel (a b : Std.U8) : a ^^^ (a ^^^ b) = b := by
  rw [← u8_xor_assoc, u8_xor_self, u8_zero_xor]

private theorem lagrange_linear_identity (c0 c1 x0 x1 : Std.U8) (hne : x0 ≠ x1) :
    pureGf256Mul (c0 ^^^ pureGf256Mul c1 x0)
        (pureGf256Mul x1 (pureGf256Inv (x0 ^^^ x1))) ^^^
      pureGf256Mul (c0 ^^^ pureGf256Mul c1 x1)
        (pureGf256Mul x0 (pureGf256Inv (x1 ^^^ x0))) = c0 := by
  have hd : x0 ^^^ x1 ≠ 0#u8 := fun h => hne ((u8_xor_eq_zero _ _).mp h)
  rw [u8_xor_comm x1 x0]
  have hpoly :
      pureGf256Mul (c0 ^^^ pureGf256Mul c1 x0) x1 ^^^
        pureGf256Mul (c0 ^^^ pureGf256Mul c1 x1) x0 = pureGf256Mul c0 (x0 ^^^ x1) := by
    simp only [pureGf256Mul_xor_right,
      pureGf256Mul_left_comm, pureGf256Mul_comm,
      u8_xor_left_comm, u8_xor_comm, u8_xor_self]
    rw [u8_xor_zero]
  rw [← pureGf256Mul_assoc, ← pureGf256Mul_assoc, ← pureGf256Mul_xor_left, hpoly,
    pureGf256Mul_assoc, pureGf256Mul_inv _ hd, pureGf256Mul_one]

private theorem linear_horner (c0 c1 x : Std.U8) :
    threshold.shamir_eval_poly_gf256 (gfSlice2 c0 c1) x = .ok (c0 ^^^ pureGf256Mul c1 x) := by
  rw [shamir_eval_poly_gf256_spec]
  dsimp only [pureHornerGf256, pureHornerGf256Prefix, gfSlice2, gfSlice3, Std.Array.to_slice,
    Std.Array.make, List.length_cons, List.length_nil, List.getD_cons_zero, List.getD_cons_succ]
  rw [pureGf256Mul_zero_left, u8_zero_xor]
  simp only [List.getD_cons_zero, List.getD_cons_succ, u8_xor_comm]

private theorem quadratic_horner (c0 c1 c2 x : Std.U8) :
    threshold.shamir_eval_poly_gf256 (gfSlice3 c0 c1 c2) x =
      .ok (c0 ^^^ pureGf256Mul c1 x ^^^ pureGf256Mul c2 (pureGf256Mul x x)) := by
  rw [shamir_eval_poly_gf256_spec]
  dsimp only [pureHornerGf256, pureHornerGf256Prefix, gfSlice2, gfSlice3, Std.Array.to_slice,
    Std.Array.make, List.length_cons, List.length_nil, List.getD_cons_zero, List.getD_cons_succ]
  rw [pureGf256Mul_zero_left, u8_zero_xor]
  simp only [List.getD_cons_zero, List.getD_cons_succ, pureGf256Mul_xor_left, pureGf256Mul_assoc, u8_xor_assoc, u8_xor_comm]

theorem shamir_lagrange_at_zero_gf256_2of2_spec (c0 c1 x0 x1 : tower.Gf256)
    (hx0 : x0 ≠ 0#u8) (hx1 : x1 ≠ 0#u8) (hne : x0 ≠ x1) :
    (∀ x, threshold.shamir_eval_poly_gf256 (gfSlice2 c0 c1) x =
      .ok (c0 ^^^ pureGf256Mul c1 x)) ∧
    threshold.shamir_lagrange_at_zero_gf256 (gfSlice2 x0 x1)
      (gfSlice2 (c0 ^^^ pureGf256Mul c1 x0) (c0 ^^^ pureGf256Mul c1 x1)) = .ok (some c0) := by
  refine ⟨linear_horner c0 c1, ?_⟩
  rw [lagrange_sum_2 _ _ _ _ hx0 hx1 hne, lagrange_linear_identity _ _ _ _ hne]

private theorem gf256_cancel_right (a b d : Std.U8) (hd : d ≠ 0#u8)
    (h : pureGf256Mul a d = pureGf256Mul b d) : a = b := by
  have he := congrArg (fun v => pureGf256Mul v (pureGf256Inv d)) h
  rw [pureGf256Mul_assoc, pureGf256Mul_assoc, pureGf256Mul_inv d hd, pureGf256Mul_one, pureGf256Mul_one] at he
  exact he

private theorem gf256_weight_clear (y n d e : Std.U8) (hd : d ≠ 0#u8) :
    pureGf256Mul (pureGf256Mul y (pureGf256Mul n (pureGf256Inv d))) (pureGf256Mul d e) =
      pureGf256Mul y (pureGf256Mul n e) := by
  rw [pureGf256Mul_assoc, pureGf256Mul_assoc,
    ← pureGf256Mul_assoc (pureGf256Inv d) d e, pureGf256Mul_comm (pureGf256Inv d) d,
    pureGf256Mul_inv d hd, pureGf256Mul_one_left]

private theorem quadratic_numerator_identity {α : Type} (add mul : α → α → α) (z : α)
    (dist : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c))
    (mlc : ∀ a b c, mul a (mul b c) = mul b (mul a c))
    (mc : ∀ a b, mul a b = mul b a)
    (aa : ∀ a b c, add (add a b) c = add a (add b c))
    (alc : ∀ a b c, add a (add b c) = add b (add a c))
    (ac : ∀ a b, add a b = add b a)
    (az : ∀ a, add a a = z)
    (cancel : ∀ a b, add a (add a b) = b)
    (c0 c1 c2 x0 x1 x2 : α) :
    let y := fun x => add (add c0 (mul c1 x)) (mul c2 (mul x x))
    add (add (mul (y x0) (mul (mul x1 x2) (add x1 x2)))
      (mul (y x1) (mul (mul x0 x2) (add x0 x2))))
      (mul (y x2) (mul (mul x0 x1) (add x0 x1))) =
      mul c0 (mul (mul (add x0 x1) (add x0 x2)) (add x1 x2)) := by
  dsimp only
  simp only [dist, mlc, mc, aa, alc, ac, az, cancel]

private theorem lagrange_quadratic_identity (c0 c1 c2 x0 x1 x2 : Std.U8)
    (hne01 : x0 ≠ x1) (hne02 : x0 ≠ x2) (hne12 : x1 ≠ x2) :
    let y := fun x => c0 ^^^ pureGf256Mul c1 x ^^^ pureGf256Mul c2 (pureGf256Mul x x)
    pureGf256Mul (y x0) (pureGf256Mul (pureGf256Mul x1 x2)
        (pureGf256Inv (pureGf256Mul (x0 ^^^ x1) (x0 ^^^ x2)))) ^^^
      pureGf256Mul (y x1) (pureGf256Mul (pureGf256Mul x0 x2)
        (pureGf256Inv (pureGf256Mul (x1 ^^^ x0) (x1 ^^^ x2)))) ^^^
      pureGf256Mul (y x2) (pureGf256Mul (pureGf256Mul x0 x1)
        (pureGf256Inv (pureGf256Mul (x2 ^^^ x0) (x2 ^^^ x1)))) = c0 := by
  dsimp only
  rw [u8_xor_comm x1 x0, u8_xor_comm x2 x0, u8_xor_comm x2 x1]
  let a := x0 ^^^ x1
  let b := x0 ^^^ x2
  let c := x1 ^^^ x2
  have ha : a ≠ 0#u8 := fun h => hne01 ((u8_xor_eq_zero _ _).mp h)
  have hb : b ≠ 0#u8 := fun h => hne02 ((u8_xor_eq_zero _ _).mp h)
  have hc : c ≠ 0#u8 := fun h => hne12 ((u8_xor_eq_zero _ _).mp h)
  have hab : pureGf256Mul a b ≠ 0#u8 := gf256_product_ne_zero _ _ ha hb
  have hac : pureGf256Mul a c ≠ 0#u8 := gf256_product_ne_zero _ _ ha hc
  have hbc : pureGf256Mul b c ≠ 0#u8 := gf256_product_ne_zero _ _ hb hc
  have hd : pureGf256Mul (pureGf256Mul a b) c ≠ 0#u8 := gf256_product_ne_zero _ _ hab hc
  apply gf256_cancel_right _ _ _ hd
  rw [pureGf256Mul_xor_left, pureGf256Mul_xor_left, gf256_weight_clear _ _ _ c hab]
  have hD1 : pureGf256Mul (pureGf256Mul a b) c = pureGf256Mul (pureGf256Mul a c) b := by
    simp only [pureGf256Mul_left_comm, pureGf256Mul_comm]
  have hD2 : pureGf256Mul (pureGf256Mul a b) c = pureGf256Mul (pureGf256Mul b c) a := by
    simp only [pureGf256Mul_left_comm, pureGf256Mul_comm]
  conv => lhs; arg 1; arg 2; rw [hD1, gf256_weight_clear _ _ _ b hac]
  conv => lhs; arg 2; rw [hD2, gf256_weight_clear _ _ _ a hbc]
  exact quadratic_numerator_identity (fun x y : Std.U8 => x ^^^ y) pureGf256Mul 0#u8
    pureGf256Mul_xor_right pureGf256Mul_left_comm pureGf256Mul_comm
    u8_xor_assoc u8_xor_left_comm u8_xor_comm u8_xor_self u8_xor_cancel
    c0 c1 c2 x0 x1 x2

theorem shamir_lagrange_at_zero_gf256_3of3_spec (c0 c1 c2 x0 x1 x2 : tower.Gf256)
    (hx0 : x0 ≠ 0#u8) (hx1 : x1 ≠ 0#u8) (hx2 : x2 ≠ 0#u8)
    (hne01 : x0 ≠ x1) (hne02 : x0 ≠ x2) (hne12 : x1 ≠ x2) :
    (∀ x, threshold.shamir_eval_poly_gf256 (gfSlice3 c0 c1 c2) x =
      .ok (c0 ^^^ pureGf256Mul c1 x ^^^ pureGf256Mul c2 (pureGf256Mul x x))) ∧
    threshold.shamir_lagrange_at_zero_gf256 (gfSlice3 x0 x1 x2)
      (gfSlice3
        (c0 ^^^ pureGf256Mul c1 x0 ^^^ pureGf256Mul c2 (pureGf256Mul x0 x0))
        (c0 ^^^ pureGf256Mul c1 x1 ^^^ pureGf256Mul c2 (pureGf256Mul x1 x1))
        (c0 ^^^ pureGf256Mul c1 x2 ^^^ pureGf256Mul c2 (pureGf256Mul x2 x2))) = .ok (some c0) := by
  refine ⟨quadratic_horner c0 c1 c2, ?_⟩
  rw [lagrange_sum_3 _ _ _ _ _ _ hx0 hx1 hx2 hne01 hne02 hne12,
    lagrange_quadratic_identity _ _ _ _ _ _ hne01 hne02 hne12]

private theorem u8_xor_mix6 (a b c d e f : Std.U8) :
    ((a ^^^ b) ^^^ (c ^^^ d)) ^^^ (e ^^^ f) = (a ^^^ c ^^^ e) ^^^ (b ^^^ d ^^^ f) := by
  simp only [u8_xor_left_comm, u8_xor_comm]

set_option maxHeartbeats 200000 in
theorem shamir_degree_reduce_2of3_gf256_spec (c0 c1 c2 x0 x1 x2 m0 m1 m2 : tower.Gf256)
    (hx0 : x0 ≠ 0#u8) (hx1 : x1 ≠ 0#u8) (hx2 : x2 ≠ 0#u8)
    (hne01 : x0 ≠ x1) (hne02 : x0 ≠ x2) (hne12 : x1 ≠ x2) :
    let p := fun x => c0 ^^^ pureGf256Mul c1 x ^^^ pureGf256Mul c2 (pureGf256Mul x x)
    ∃ r0 r1,
      threshold.shamir_degree_reduce_2of3_gf256 (Std.Array.make 3#usize [x0, x1, x2])
        (Std.Array.make 3#usize [p x0, p x1, p x2]) (Std.Array.make 3#usize [m0, m1, m2]) x0 = .ok (some r0) ∧
      threshold.shamir_degree_reduce_2of3_gf256 (Std.Array.make 3#usize [x0, x1, x2])
        (Std.Array.make 3#usize [p x0, p x1, p x2]) (Std.Array.make 3#usize [m0, m1, m2]) x1 = .ok (some r1) ∧
      threshold.shamir_lagrange_at_zero_gf256 (gfSlice2 x0 x1) (gfSlice2 r0 r1) = .ok (some c0) := by
  dsimp only
  let slope := m0 ^^^ m1 ^^^ m2
  have hd01 : x0 ^^^ x1 ≠ 0#u8 := fun h => hne01 ((u8_xor_eq_zero _ _).mp h)
  have hd02 : x0 ^^^ x2 ≠ 0#u8 := fun h => hne02 ((u8_xor_eq_zero _ _).mp h)
  have hd12 : x1 ^^^ x2 ≠ 0#u8 := fun h => hne12 ((u8_xor_eq_zero _ _).mp h)
  have hi0 := gf256_inv_pure_nonzero _ (gf256_product_ne_zero _ _ hd01 hd02)
  have hi1 := gf256_inv_pure_nonzero _ (gf256_product_ne_zero _ _ hd01 hd12)
  have hi2 := gf256_inv_pure_nonzero _ (gf256_product_ne_zero _ _ hd02 hd12)
  have hp := lagrange_quadratic_identity c0 c1 c2 x0 x1 x2 hne01 hne02 hne12
  dsimp only at hp
  rw [u8_xor_comm x1 x0, u8_xor_comm x2 x0, u8_xor_comm x2 x1] at hp
  have run (x : Std.U8) :
      threshold.shamir_degree_reduce_2of3_gf256 (Std.Array.make 3#usize [x0, x1, x2])
        (Std.Array.make 3#usize
          [c0 ^^^ pureGf256Mul c1 x0 ^^^ pureGf256Mul c2 (pureGf256Mul x0 x0),
           c0 ^^^ pureGf256Mul c1 x1 ^^^ pureGf256Mul c2 (pureGf256Mul x1 x1),
           c0 ^^^ pureGf256Mul c1 x2 ^^^ pureGf256Mul c2 (pureGf256Mul x2 x2)])
        (Std.Array.make 3#usize [m0, m1, m2]) x = .ok (some (c0 ^^^ pureGf256Mul slope x)) := by
    unfold threshold.shamir_degree_reduce_2of3_gf256
    simp [Std.Array.index_usize, Std.Array.make, hx0, hx1, hx2,
      tower.gf256_add, gf256_mul_eq_pure]
    rw [hi0, result_bind_ok]
    dsimp only
    rw [hi1, result_bind_ok]
    dsimp only
    rw [hi2, result_bind_ok]
    dsimp only
    apply congrArg (fun z => Result.ok (some z))
    rw [u8_xor_mix6, hp, ← pureGf256Mul_xor_left, ← pureGf256Mul_xor_left]
  exact ⟨_, _, run x0, run x1,
    (shamir_lagrange_at_zero_gf256_2of2_spec c0 slope x0 x1 hx0 hx1 hne01).2⟩

private theorem gf256_frobenius_linear_share (s m x : Std.U8) :
    tower.gf256_frobenius_residual (s ^^^ pureGf256Mul m x) =
      .ok ((pureGf256Mul s s ^^^ s) ^^^ pureGf256Mul m x ^^^
        pureGf256Mul (pureGf256Mul m m) (pureGf256Mul x x)) := by
  simp only [tower.gf256_frobenius_residual, gf256_mul_eq_pure,
    bind_eq_result_bind, result_bind_ok, tower.gf256_add, lift_eq_ok]
  congr 1
  simp only [pureGf256Mul_xor_right,
    pureGf256Mul_left_comm, pureGf256Mul_comm,
    u8_xor_assoc, u8_xor_left_comm, u8_xor_comm, u8_xor_cancel]

set_option maxHeartbeats 200000 in
theorem dkg_linear_key_bit_gf256_spec (s m x0 x1 x2 : tower.Gf256)
    (hx0 : x0 ≠ 0#u8) (hx1 : x1 ≠ 0#u8) (hx2 : x2 ≠ 0#u8)
    (hne01 : x0 ≠ x1) (hne02 : x0 ≠ x2) (hne12 : x1 ≠ x2) :
    threshold.dkg_verify_shamir_2of3_key_bit_gf256 (Std.Array.make 3#usize [x0, x1, x2])
      (Std.Array.make 3#usize [s ^^^ pureGf256Mul m x0, s ^^^ pureGf256Mul m x1, s ^^^ pureGf256Mul m x2]) =
      .ok (decide (s = 0#u8 ∨ s = 1#u8)) := by
  have hv := shamir_validate_points_gf256_3_spec x0 x1 x2
  have hl0 := (shamir_lagrange_at_zero_gf256_2of2_spec s m x0 x1 hx0 hx1 hne01).2
  have hl1 := (shamir_lagrange_at_zero_gf256_2of2_spec s m x1 x2 hx1 hx2 hne12).2
  have hl2 := (shamir_lagrange_at_zero_gf256_3of3_spec
    (pureGf256Mul s s ^^^ s) m (pureGf256Mul m m) x0 x1 x2 hx0 hx1 hx2 hne01 hne02 hne12).2
  have hv' : threshold.shamir_validate_points_gf256 (gfSlice3 x0 x1 x2) = .ok true := by
    have h : (x0 ≠ 0#u8 ∧ x1 ≠ 0#u8 ∧ x2 ≠ 0#u8 ∧ x0 ≠ x1 ∧ x0 ≠ x2 ∧ x1 ≠ x2) :=
      ⟨hx0, hx1, hx2, hne01, hne02, hne12⟩
    rw [decide_eq_true h] at hv
    exact hv
  have hr0 := gf256_frobenius_linear_share s m x0
  have hr1 := gf256_frobenius_linear_share s m x1
  have hr2 := gf256_frobenius_linear_share s m x2
  generalize hy0 : s ^^^ pureGf256Mul m x0 = y0 at hl0 hr0 ⊢
  generalize hy1 : s ^^^ pureGf256Mul m x1 = y1 at hl0 hl1 hr1 ⊢
  generalize hy2 : s ^^^ pureGf256Mul m x2 = y2 at hl1 hr2 ⊢
  generalize hz0 : (pureGf256Mul s s ^^^ s) ^^^ pureGf256Mul m x0 ^^^ pureGf256Mul (pureGf256Mul m m) (pureGf256Mul x0 x0) = z0 at hl2 hr0
  generalize hz1 : (pureGf256Mul s s ^^^ s) ^^^ pureGf256Mul m x1 ^^^ pureGf256Mul (pureGf256Mul m m) (pureGf256Mul x1 x1) = z1 at hl2 hr1
  generalize hz2 : (pureGf256Mul s s ^^^ s) ^^^ pureGf256Mul m x2 ^^^ pureGf256Mul (pureGf256Mul m m) (pureGf256Mul x2 x2) = z2 at hl2 hr2
  unfold threshold.dkg_verify_shamir_2of3_key_bit_gf256
  simp only [bind_eq_result_bind, lift_eq_ok, result_bind_ok]
  rw [hv', result_bind_ok]
  conv => lhs; simp [Std.Array.index_usize, Std.Array.make]
  dsimp only [gfSlice2, gfSlice3, Std.Array.to_slice, Std.Array.make] at hl0 hl1 hl2 ⊢
  rw [hl0, result_bind_ok]
  dsimp only
  rw [hl1, result_bind_ok]
  dsimp only
  simp only [ite_true, hr0, hr1, hr2,
    result_bind_ok]
  rw [hl2, result_bind_ok]
  dsimp only
  have hf := tower_gf256_boolean_iff_frobenius s
  have he : pureGf256Mul s s ^^^ s = 0#u8 ↔ s = 0#u8 ∨ s = 1#u8 := by
    simpa only [tower.gf256_frobenius_residual, gf256_mul_eq_pure, tower.gf256_add,
      bind_eq_result_bind, result_bind_ok, lift_eq_ok, Result.ok.injEq] using hf.1
  by_cases hz : pureGf256Mul s s ^^^ s = 0#u8
  · rw [ite_eq_left hz, hf.2]
  · rw [ite_eq_right hz]
    have hs : ¬ (s = 0#u8 ∨ s = 1#u8) := fun hs => hz (he.mpr hs)
    rw [decide_eq_false hs]



theorem dkg_inconsistent_reconstructions_rejected
    (x0 x1 x2 y0 y1 y2 : Std.U8)
    (hx0 : x0 ≠ 0#u8) (hx1 : x1 ≠ 0#u8) (hx2 : x2 ≠ 0#u8)
    (hne01 : x0 ≠ x1) (hne02 : x0 ≠ x2) (hne12 : x1 ≠ x2)
    (hne :
      pureGf256Mul y0 (pureGf256Mul x1 (pureGf256Inv (x0 ^^^ x1))) ^^^
        pureGf256Mul y1 (pureGf256Mul x0 (pureGf256Inv (x1 ^^^ x0))) ≠
      pureGf256Mul y1 (pureGf256Mul x2 (pureGf256Inv (x1 ^^^ x2))) ^^^
        pureGf256Mul y2 (pureGf256Mul x1 (pureGf256Inv (x2 ^^^ x1)))) :
    threshold.dkg_verify_shamir_2of3_key_bit_gf256
      (Std.Array.make 3#usize [x0, x1, x2]) (Std.Array.make 3#usize [y0, y1, y2]) = .ok false := by
  have hv := shamir_validate_points_gf256_3_spec x0 x1 x2
  rw [decide_eq_true (show x0 ≠ 0#u8 ∧ x1 ≠ 0#u8 ∧ x2 ≠ 0#u8 ∧
    x0 ≠ x1 ∧ x0 ≠ x2 ∧ x1 ≠ x2 from ⟨hx0, hx1, hx2, hne01, hne02, hne12⟩)] at hv
  have h01 := lagrange_sum_2 x0 x1 y0 y1 hx0 hx1 hne01
  have h12 := lagrange_sum_2 x1 x2 y1 y2 hx1 hx2 hne12
  unfold threshold.dkg_verify_shamir_2of3_key_bit_gf256
  simp only [bind_eq_result_bind, lift_eq_ok, result_bind_ok]
  rw [hv, result_bind_ok]
  conv => lhs; simp [Std.Array.index_usize, Std.Array.make]
  dsimp only [gfSlice2, Std.Array.to_slice, Std.Array.make] at h01 h12 ⊢
  rw [h01, result_bind_ok]
  dsimp only
  rw [h12, result_bind_ok]
  simp only [hne, ite_false]

theorem tooth_dkg_inconsistent_shares_rejected :
    threshold.dkg_verify_shamir_2of3_key_bit_gf256
      (Std.Array.make 3#usize [1#u8, 2#u8, 3#u8])
      (Std.Array.make 3#usize [0#u8, 1#u8, 1#u8]) = .ok false := by
  apply dkg_inconsistent_reconstructions_rejected <;> decide

@[expose]
def ValidPoints3 (pts : Std.Array tower.Gf256 3#usize) : Prop :=
  let x0 := pts.val.getD 0 0#u8
  let x1 := pts.val.getD 1 0#u8
  let x2 := pts.val.getD 2 0#u8
  x0 ≠ 0#u8 ∧ x1 ≠ 0#u8 ∧ x2 ≠ 0#u8 ∧ x0 ≠ x1 ∧ x0 ≠ x2 ∧ x1 ≠ x2

private theorem array3_decompose (a : Std.Array tower.Gf256 3#usize) :
    ∃ x0 x1 x2, a = Std.Array.make 3#usize [x0, x1, x2] := by
  rcases a with ⟨xs, h⟩
  change xs.length = 3 at h
  cases xs with
  | nil => cases h
  | cons x0 xs =>
    cases xs with
    | nil => cases h
    | cons x1 xs =>
      cases xs with
      | nil => cases h
      | cons x2 xs =>
        have ht : xs.length = 0 := Nat.succ.inj (Nat.succ.inj (Nat.succ.inj h))
        have hz := List.eq_nil_of_length_eq_zero ht
        subst xs
        exact ⟨x0, x1, x2, rfl⟩

private theorem inverse_nonzero (x : Std.U8) (hx : x ≠ 0#u8) : pureGf256Inv x ≠ 0#u8 := by
  intro hz
  have h := pureGf256Mul_inv x hx
  rw [hz, pureGf256Mul_zero] at h
  exact (by decide : (0#u8 : Std.U8) ≠ 1#u8) h

private theorem linear_second_of_reconstruction (s m x0 x1 y0 y1 : Std.U8)
    (hx0 : x0 ≠ 0#u8) (hne : x0 ≠ x1)
    (hy0 : y0 = s ^^^ pureGf256Mul m x0)
    (hr : pureGf256Mul y0 (pureGf256Mul x1 (pureGf256Inv (x0 ^^^ x1))) ^^^
      pureGf256Mul y1 (pureGf256Mul x0 (pureGf256Inv (x1 ^^^ x0))) = s) :
    y1 = s ^^^ pureGf256Mul m x1 := by
  have hd : x1 ^^^ x0 ≠ 0#u8 := fun h => hne.symm ((u8_xor_eq_zero _ _).mp h)
  have hw := gf256_product_ne_zero x0 (pureGf256Inv (x1 ^^^ x0)) hx0 (inverse_nonzero _ hd)
  have hp := lagrange_linear_identity s m x0 x1 hne
  rw [← hy0] at hp
  have he := hr.trans hp.symm
  have hc := congrArg (fun t => pureGf256Mul y0
    (pureGf256Mul x1 (pureGf256Inv (x0 ^^^ x1))) ^^^ t) he
  simp only [u8_xor_cancel] at hc
  exact gf256_cancel_right _ _ _ hw hc

private theorem consistent_shares_linear (x0 x1 x2 y0 y1 y2 : Std.U8)
    (hx0 : x0 ≠ 0#u8) (hx1 : x1 ≠ 0#u8) (hne01 : x0 ≠ x1) (hne12 : x1 ≠ x2)
    (hc : pureGf256Mul y0 (pureGf256Mul x1 (pureGf256Inv (x0 ^^^ x1))) ^^^
        pureGf256Mul y1 (pureGf256Mul x0 (pureGf256Inv (x1 ^^^ x0))) =
      pureGf256Mul y1 (pureGf256Mul x2 (pureGf256Inv (x1 ^^^ x2))) ^^^
        pureGf256Mul y2 (pureGf256Mul x1 (pureGf256Inv (x2 ^^^ x1)))) :
    ∃ s m, y0 = s ^^^ pureGf256Mul m x0 ∧ y1 = s ^^^ pureGf256Mul m x1 ∧
      y2 = s ^^^ pureGf256Mul m x2 := by
  let s := pureGf256Mul y0 (pureGf256Mul x1 (pureGf256Inv (x0 ^^^ x1))) ^^^
    pureGf256Mul y1 (pureGf256Mul x0 (pureGf256Inv (x1 ^^^ x0)))
  let m := pureGf256Mul (y0 ^^^ s) (pureGf256Inv x0)
  have h0 : y0 = s ^^^ pureGf256Mul m x0 := by
    dsimp only [m]
    rw [pureGf256Mul_assoc, pureGf256Mul_comm (pureGf256Inv x0),
      pureGf256Mul_inv _ hx0, pureGf256Mul_one, u8_xor_comm y0 s, u8_xor_cancel]
  have h1 := linear_second_of_reconstruction s m x0 x1 y0 y1 hx0 hne01 h0 rfl
  have h2 := linear_second_of_reconstruction s m x1 x2 y1 y2 hx1 hne12 h1 hc.symm
  exact ⟨s, m, h0, h1, h2⟩

theorem dkg_verify_shamir_2of3_key_bit_gf256_spec
    (pts shares : Std.Array tower.Gf256 3#usize) :
    (∃ ok, threshold.dkg_verify_shamir_2of3_key_bit_gf256 pts shares = .ok ok) ∧
    (threshold.dkg_verify_shamir_2of3_key_bit_gf256 pts shares = .ok true ↔
      ValidPoints3 pts ∧ ∃ s m : tower.Gf256, (s = 0#u8 ∨ s = 1#u8) ∧
        shares = Std.Array.make 3#usize
          [s ^^^ pureGf256Mul m (pts.val.getD 0 0#u8),
           s ^^^ pureGf256Mul m (pts.val.getD 1 0#u8),
           s ^^^ pureGf256Mul m (pts.val.getD 2 0#u8)]) := by
  obtain ⟨x0, x1, x2, rfl⟩ := array3_decompose pts
  obtain ⟨y0, y1, y2, rfl⟩ := array3_decompose shares
  change (∃ ok, threshold.dkg_verify_shamir_2of3_key_bit_gf256 _ _ = .ok ok) ∧
    (threshold.dkg_verify_shamir_2of3_key_bit_gf256 _ _ = .ok true ↔
      (x0 ≠ 0#u8 ∧ x1 ≠ 0#u8 ∧ x2 ≠ 0#u8 ∧ x0 ≠ x1 ∧ x0 ≠ x2 ∧ x1 ≠ x2) ∧
      ∃ s m : Std.U8, (s = 0#u8 ∨ s = 1#u8) ∧
        Std.Array.make 3#usize [y0, y1, y2] =
          Std.Array.make 3#usize [s ^^^ pureGf256Mul m x0, s ^^^ pureGf256Mul m x1, s ^^^ pureGf256Mul m x2])
  by_cases hv : x0 ≠ 0#u8 ∧ x1 ≠ 0#u8 ∧ x2 ≠ 0#u8 ∧ x0 ≠ x1 ∧ x0 ≠ x2 ∧ x1 ≠ x2
  · obtain ⟨hx0, hx1, hx2, h01, h02, h12⟩ := hv
    have complete (s m : Std.U8) (hs : s = 0#u8 ∨ s = 1#u8) :=
      dkg_linear_key_bit_gf256_spec s m x0 x1 x2 hx0 hx1 hx2 h01 h02 h12
    by_cases hc : pureGf256Mul y0 (pureGf256Mul x1 (pureGf256Inv (x0 ^^^ x1))) ^^^
        pureGf256Mul y1 (pureGf256Mul x0 (pureGf256Inv (x1 ^^^ x0))) =
      pureGf256Mul y1 (pureGf256Mul x2 (pureGf256Inv (x1 ^^^ x2))) ^^^
        pureGf256Mul y2 (pureGf256Mul x1 (pureGf256Inv (x2 ^^^ x1)))
    · obtain ⟨s, m, rfl, rfl, rfl⟩ := consistent_shares_linear _ _ _ _ _ _ hx0 hx1 h01 h12 hc
      have run := dkg_linear_key_bit_gf256_spec s m x0 x1 x2 hx0 hx1 hx2 h01 h02 h12
      refine ⟨⟨_, run⟩, ?_⟩
      constructor
      · intro h
        have hb : s = 0#u8 ∨ s = 1#u8 := of_decide_eq_true (Result.ok.inj (run.symm.trans h))
        exact ⟨⟨hx0, hx1, hx2, h01, h02, h12⟩, s, m, hb, rfl⟩
      · rintro ⟨_, t, n, ht, he⟩
        rw [he, complete t n ht, decide_eq_true ht]
    · have run := dkg_inconsistent_reconstructions_rejected _ _ _ _ _ _ hx0 hx1 hx2 h01 h02 h12 hc
      refine ⟨⟨false, run⟩, ?_⟩
      constructor
      · intro h; have hf := Result.ok.inj (run.symm.trans h); cases hf
      · rintro ⟨_, s, m, hs, he⟩
        rw [he, complete s m hs, decide_eq_true hs]
  · have hval := shamir_validate_points_gf256_3_spec x0 x1 x2
    rw [decide_eq_false hv] at hval
    have run : threshold.dkg_verify_shamir_2of3_key_bit_gf256
        (Std.Array.make 3#usize [x0, x1, x2]) (Std.Array.make 3#usize [y0, y1, y2]) = .ok false := by
      unfold threshold.dkg_verify_shamir_2of3_key_bit_gf256
      simp only [bind_eq_result_bind, lift_eq_ok, result_bind_ok, hval, Bool.false_eq_true, ite_false]
    refine ⟨⟨false, run⟩, ?_⟩
    rw [run]
    simp only [Result.ok.injEq, Bool.false_eq_true, false_iff, not_and]
    exact fun h => False.elim (hv h)

end qsag_verified.proofs
