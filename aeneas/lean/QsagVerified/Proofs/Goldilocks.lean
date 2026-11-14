module

public import QsagVerified.Proofs.Common

public section

namespace qsag_verified.proofs

open Aeneas Aeneas.Std Result ControlFlow Error
open qsag_verified

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

attribute [-simp] BitVec.getLsbD_eq_getElem
attribute [local simp] UScalar.val UScalarTy.numBits

/-- Canonical Goldilocks prime $p = 2^{64} - 2^{32} + 1$. -/
@[expose]
def GoldilocksP : Nat := 18446744069414584321

private theorem goldilocks_prime_eq :
    goldilocks.GOLDILOCKS_PRIME = 18446744069414584321#u64 := by
  unfold goldilocks.GOLDILOCKS_PRIME
  rfl

private theorem goldilocks_epsilon_eq :
    goldilocks.GOLDILOCKS_EPSILON = 4294967295#u64 := by
  unfold goldilocks.GOLDILOCKS_EPSILON
  rfl

/-! ## Section 2: Pillar A — Branchless Goldilocks Field Refinement () -/

private theorem mod_sub_normalize (p x c : Nat) (hc : c ≤ p) :
    (p + x % p - c) % p = (p + x - c) % p := by
  have hd : x = p * (x / p) + x % p := (Nat.div_add_mod _ _).symm
  have he : p + x - c = p * (x / p) + (p + x % p - c) := by
    calc
      _ = (p * (x / p) + (p + x % p)) - c :=
        congrArg (fun z => z - c) ((congrArg (p + ·) hd).trans (Nat.add_left_comm _ _ _))
      _ = _ := Nat.add_sub_assoc (Nat.le_trans hc (Nat.le_add_right _ _)) _
  rw [he, Nat.mul_add_mod_self_left]

private theorem mod_sub_add_cancel (p a b : Nat) (hp : 0 < p) :
    (p + (a + b) % p - a % p) % p = b % p := by
  rw [← Nat.mod_add_mod a p b]
  rw [mod_sub_normalize p (a % p + b) (a % p) (Nat.le_of_lt (Nat.mod_lt _ hp))]
  rw [Nat.add_left_comm p (a % p) b, Nat.add_sub_cancel_left, Nat.add_mod_left]

private theorem goldilocks_fold_mod (m p x : Nat) (hpm : p ≤ m) (hx : x < 2 * p) :
    (m + x - p + p *
      (1 - (m + x - p) / m % 2)) %
      m = x % p := by
  have hp : p ≤ m + x := Nat.le_trans hpm (Nat.le_add_right m x)
  by_cases h : x < p
  · have hd : m + x - p < m :=
      (sub_lt_iff_lt_add_of_le hp).mpr (Nat.add_lt_add_left h m)
    rw [Nat.div_eq_of_lt hd]
    simp only [Nat.zero_mod, Nat.sub_zero, Nat.mul_one]
    rw [Nat.sub_add_cancel hp, Nat.add_mod_left,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h hpm), Nat.mod_eq_of_lt h]
  · have hpx : p ≤ x := Nat.le_of_not_gt h
    have he : m + x - p = m + (x - p) := Nat.add_sub_assoc hpx m
    have hxp : x - p < p :=
      (sub_lt_iff_lt_add_of_le hpx).mpr (by simpa only [Nat.two_mul] using hx)
    have hxm : x - p < m := Nat.lt_of_lt_of_le hxp hpm
    have hq : (m + x - p) / m = 1 := by
      rw [he]
      apply Nat.div_eq_of_lt_le
      · simpa only [Nat.one_mul] using Nat.le_add_right m (x - p)
      · simpa only [Nat.one_add, Nat.two_mul] using Nat.add_lt_add_left hxm m
    rw [hq]
    change (m + x - p) % m = x % p
    calc
      (m + x - p) % m = (x - p) % m := by rw [he, Nat.add_mod_left]
      _ = x - p := Nat.mod_eq_of_lt hxm
      _ = (x - p) % p := (Nat.mod_eq_of_lt hxp).symm
      _ = x % p := (Nat.mod_eq_sub_mod hpx).symm

private theorem goldilocks_borrow_mod (m p a b : Nat) (hpm : p ≤ m)
    (ha : a < p) (hb : b < p) :
    (m + a - b + p * (1 - (m + a - b) / m % 2)) % m = (p + a - b) % p := by
  have hbp : b ≤ p + a := Nat.le_trans (Nat.le_of_lt hb) (Nat.le_add_right _ _)
  have hbm : b ≤ m + a := Nat.le_trans (Nat.le_trans (Nat.le_of_lt hb) hpm) (Nat.le_add_right _ _)
  by_cases hba : b ≤ a
  · have hd : a - b < p := Nat.lt_of_le_of_lt (Nat.sub_le _ _) ha
    have hdm : a - b < m := Nat.lt_of_lt_of_le hd hpm
    rw [Nat.add_sub_assoc hba m, Nat.add_sub_assoc hba p]
    have hq : (m + (a - b)) / m = 1 :=
      Nat.div_eq_of_lt_le (by simp)
        (by simpa only [Nat.one_add, Nat.two_mul] using Nat.add_lt_add_left hdm m)
    rw [hq]
    simp only [Nat.reduceMod, Nat.reduceSub, Nat.mul_zero, Nat.add_zero,
      Nat.add_mod_left, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hdm]
  · have hab : a < b := Nat.lt_of_not_ge hba
    have hd : m + a - b < m :=
      (sub_lt_iff_lt_add_of_le hbm).mpr (Nat.add_lt_add_left hab m)
    have ht : p + a - b < p :=
      (sub_lt_iff_lt_add_of_le hbp).mpr (Nat.add_lt_add_left hab p)
    have he : (m + a - b) + p = m + (p + a - b) := by
      rw [Nat.add_comm (m + a - b) p, ← Nat.add_sub_assoc hbm p, ← Nat.add_sub_assoc hbp m]
      congr 1
      ac_rfl
    rw [Nat.div_eq_of_lt hd]
    simp only [Nat.zero_mod, Nat.sub_zero, Nat.mul_one]
    rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le ht hpm), Nat.mod_eq_of_lt ht]

private theorem goldilocks_intermediate_bound (x y z : Nat) (hx : x < 2 * GoldilocksP) :
    (2 ^ 64 + x - y) + GoldilocksP * (1 - z) < 2 ^ 128 := by
  apply Nat.lt_of_le_of_lt
    (Nat.add_le_add (Nat.sub_le _ _) (Nat.mul_le_mul_left _ (Nat.sub_le 1 z)))
  exact Nat.lt_trans (Nat.add_lt_add_right (Nat.add_lt_add_left hx _) _) (by decide)

/-- Branchless `goldilocks_canon` never panics/overflows and reduces every `u64` modulo
    $p = 2^{64} - 2^{32} + 1$ into `[0, p)`. -/
theorem goldilocks_canon_spec (x : Std.U64) :
    ∃ y : goldilocks.Goldilocks,
      goldilocks.goldilocks_canon x = .ok y ∧
      y.val = x.val % GoldilocksP ∧
      y.val < GoldilocksP := by
  unfold goldilocks.goldilocks_canon
  rw [goldilocks_prime_eq]
  have hx : x.val < 2 ^ 64 := x.bv.isLt
  have hsh : (1#u128 <<< 64#i32 : Result Std.U128) = .ok 18446744073709551616#u128 := rfl
  rw [hsh]
  dsimp only [Bind.bind, Result.bind, lift]
  have hi_val : (18446744073709551616#u128).val = 2 ^ 64 := rfl
  have hi1_val : (UScalar.cast .U128 x).val = x.val := u64_cast_u128_val x
  have hp_val : (UScalar.cast .U128 18446744069414584321#u64).val = GoldilocksP := rfl
  obtain ⟨hadd1, hi2_val⟩ := u128_add_ok (a := 18446744073709551616#u128) (b := UScalar.cast .U128 x)
    (by rw [hi_val, hi1_val]; exact Nat.lt_trans (Nat.add_lt_add_left hx _) (by decide))
  rw [hadd1]; dsimp only [Result.bind]
  obtain ⟨hsub1, hd_val⟩ := u128_sub_ok
    (a := ⟨(18446744073709551616#u128).bv + (UScalar.cast .U128 x).bv⟩)
    (b := UScalar.cast .U128 18446744069414584321#u64)
    (by rw [hi2_val, hi_val, hi1_val, hp_val]; exact Nat.le_trans (by decide) (Nat.le_add_right _ _))
  rw [hsub1]; dsimp only [Result.bind]
  let d : Std.U128 :=
    ⟨(⟨(18446744073709551616#u128).bv + (UScalar.cast .U128 x).bv⟩ : Std.U128).bv -
      (UScalar.cast .U128 18446744069414584321#u64).bv⟩
  rw [u128_shr64_eq d]; dsimp only [Result.bind]
  let ge : Std.U128 := ⟨d.bv >>> 64⟩ &&& 1#u128
  have hge_val : ge.val = (d.val / (2 ^ 64)) % 2 := by
    rw [u128_and_one_val, u128_shr64_val]
  have hd_eq : d.val = 2 ^ 64 + x.val - GoldilocksP := by
    rw [hd_val, hi2_val, hi_val, hi1_val, hp_val]
  have hge_le : ge.val ≤ (1#u128).val := by
    change ge.val ≤ 1
    rw [hge_val]
    exact Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
  obtain ⟨hsub2, hi6_val⟩ := u128_sub_ok (a := 1#u128) (b := ge) hge_le
  rw [hsub2]; dsimp only [Result.bind]
  let i6 : Std.U128 := ⟨(1#u128).bv - ge.bv⟩
  have hi6_eq : i6.val = 1 - ge.val := by
    exact hi6_val
  obtain ⟨hmul, hadj_val⟩ := u128_mul_ok
    (a := UScalar.cast .U128 18446744069414584321#u64) (b := i6)
    (by rw [hp_val, hi6_eq]; exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.sub_le 1 _)) (by decide))
  rw [hmul]; dsimp only [Result.bind]
  let adj : Std.U128 := ⟨(UScalar.cast .U128 18446744069414584321#u64).bv * i6.bv⟩
  obtain ⟨hadd2, hi7_val⟩ := u128_add_ok (a := d) (b := adj)
    (by rw [hd_eq, hadj_val, hp_val, hi6_eq]; exact goldilocks_intermediate_bound _ _ _ (Nat.lt_trans hx (by decide)))
  rw [hadd2]; dsimp only [Result.bind]
  let i7 : Std.U128 := ⟨d.bv + adj.bv⟩
  change i7.val = d.val + adj.val at hi7_val
  have hp1 : (1#u128).val = 1 := rfl
  let i8 : Std.U128 := i7 &&& 18446744073709551615#u128
  have hi8_val : i8.val = i7.val % (2 ^ 64) := u128_and_mask64_val i7
  have hi8_lt : i8.val < 2 ^ 64 := by rw [hi8_val]; exact Nat.mod_lt _ (by decide)
  refine ⟨UScalar.cast .U64 i8, rfl, ?_, ?_⟩
  · rw [u128_cast_u64_val_of_lt i8 hi8_lt, hi8_val, hi7_val, hadj_val, hp_val, hi6_eq,
        hge_val, hd_eq]
    unfold GoldilocksP
    rw [goldilocks_fold_mod _ _ _ (by decide) (Nat.lt_trans hx (by decide))]
  · rw [u128_cast_u64_val_of_lt i8 hi8_lt, hi8_val, hi7_val, hadj_val, hp_val, hi6_eq,
        hge_val, hd_eq]
    unfold GoldilocksP
    rw [goldilocks_fold_mod _ _ _ (by decide) (Nat.lt_trans hx (by decide))]
    exact Nat.mod_lt _ (by decide)

/-- Branchless `goldilocks_add` is total (`.ok`) and computes exact canonical modular addition
    `(a mod p + b mod p) mod p < p`. -/
theorem goldilocks_add_spec (a b : goldilocks.Goldilocks) :
    ∃ y : goldilocks.Goldilocks,
      goldilocks.goldilocks_add a b = .ok y ∧
      y.val = (a.val % GoldilocksP + b.val % GoldilocksP) % GoldilocksP ∧
      y.val < GoldilocksP := by
  unfold goldilocks.goldilocks_add
  rw [goldilocks_prime_eq]
  obtain ⟨ga, hga, hga_eq, hga_lt⟩ := goldilocks_canon_spec a
  obtain ⟨gb, hgb, hgb_eq, hgb_lt⟩ := goldilocks_canon_spec b
  rw [hga]; dsimp only [Bind.bind, Result.bind]
  rw [hgb]; dsimp only [Result.bind, lift]
  have hia : (UScalar.cast .U128 ga).val = ga.val := u64_cast_u128_val ga
  have hib : (UScalar.cast .U128 gb).val = gb.val := u64_cast_u128_val gb
  have hp_val : (UScalar.cast .U128 18446744069414584321#u64).val = GoldilocksP := rfl
  obtain ⟨hsum, hsum_val⟩ := u128_add_ok (a := UScalar.cast .U128 ga) (b := UScalar.cast .U128 gb)
    (by rw [hia, hib]; exact Nat.lt_trans (Nat.add_lt_add hga_lt hgb_lt) (by decide))
  rw [hsum]; dsimp only [Result.bind]
  let sum : Std.U128 := ⟨(UScalar.cast .U128 ga).bv + (UScalar.cast .U128 gb).bv⟩
  have hsh : (1#u128 <<< 64#i32 : Result Std.U128) = .ok 18446744073709551616#u128 := rfl
  rw [hsh]; dsimp only [Result.bind]
  have hi2_val : (18446744073709551616#u128).val = 2 ^ 64 := rfl
  obtain ⟨hi3, hi3_val⟩ := u128_add_ok (a := 18446744073709551616#u128) (b := sum)
    (by rw [hi2_val, hsum_val, hia, hib]; exact Nat.lt_trans (Nat.add_lt_add_left (Nat.add_lt_add hga_lt hgb_lt) _) (by decide))
  rw [hi3]; dsimp only [Result.bind]
  let i3 : Std.U128 := ⟨(18446744073709551616#u128).bv + sum.bv⟩
  obtain ⟨hd, hd_val⟩ := u128_sub_ok (a := i3) (b := UScalar.cast .U128 18446744069414584321#u64)
    (by rw [hi3_val, hi2_val, hsum_val, hia, hib, hp_val]; exact Nat.le_trans (by decide) (Nat.le_add_right _ _))
  rw [hd]; dsimp only [Result.bind]
  let d : Std.U128 := ⟨i3.bv - (UScalar.cast .U128 18446744069414584321#u64).bv⟩
  rw [u128_shr64_eq d]; dsimp only [Result.bind]
  let ge : Std.U128 := ⟨d.bv >>> 64⟩ &&& 1#u128
  have hge_val : ge.val = (d.val / (2 ^ 64)) % 2 := by
    rw [u128_and_one_val, u128_shr64_val]
  have hd_eq : d.val = 2 ^ 64 + (ga.val + gb.val) - GoldilocksP := by
    rw [hd_val, hi3_val, hi2_val, hsum_val, hia, hib, hp_val]
  have hge_le : ge.val ≤ (1#u128).val := by
    change ge.val ≤ 1
    rw [hge_val]
    exact Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
  obtain ⟨hi7, hi7_val⟩ := u128_sub_ok (a := 1#u128) (b := ge) hge_le
  rw [hi7]; dsimp only [Result.bind]
  let i7 : Std.U128 := ⟨(1#u128).bv - ge.bv⟩
  have hi7_eq : i7.val = 1 - ge.val := by
    exact hi7_val
  obtain ⟨hadj, hadj_val⟩ := u128_mul_ok
    (a := UScalar.cast .U128 18446744069414584321#u64) (b := i7)
    (by rw [hp_val, hi7_eq]; exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.sub_le 1 _)) (by decide))
  rw [hadj]; dsimp only [Result.bind]
  let adj : Std.U128 := ⟨(UScalar.cast .U128 18446744069414584321#u64).bv * i7.bv⟩
  obtain ⟨hi8, hi8_val⟩ := u128_add_ok (a := d) (b := adj)
    (by rw [hd_eq, hadj_val, hp_val, hi7_eq]; apply goldilocks_intermediate_bound; simpa only [Nat.two_mul] using Nat.add_lt_add hga_lt hgb_lt)
  rw [hi8]; dsimp only [Result.bind]
  let i8 : Std.U128 := ⟨d.bv + adj.bv⟩
  change i8.val = d.val + adj.val at hi8_val
  let i9 : Std.U128 := i8 &&& 18446744073709551615#u128
  have hi9_val : i9.val = i8.val % (2 ^ 64) := u128_and_mask64_val i8
  have hi9_lt : i9.val < 2 ^ 64 := by rw [hi9_val]; exact Nat.mod_lt _ (by decide)
  refine ⟨UScalar.cast .U64 i9, rfl, ?_, ?_⟩
  · rw [u128_cast_u64_val_of_lt i9 hi9_lt, hi9_val, hi8_val, hadj_val, hp_val, hi7_eq,
        hge_val, hd_eq, ← hga_eq, ← hgb_eq]
    unfold GoldilocksP at hga_lt hgb_lt ⊢
    rw [goldilocks_fold_mod _ _ _ (by decide) (by simpa only [Nat.two_mul] using Nat.add_lt_add hga_lt hgb_lt)]
  · rw [u128_cast_u64_val_of_lt i9 hi9_lt, hi9_val, hi8_val, hadj_val, hp_val, hi7_eq,
        hge_val, hd_eq]
    unfold GoldilocksP at hga_lt hgb_lt ⊢
    rw [goldilocks_fold_mod _ _ _ (by decide) (by simpa only [Nat.two_mul] using Nat.add_lt_add hga_lt hgb_lt)]
    exact Nat.mod_lt _ (by decide)

/-- Branchless `goldilocks_sub` is total (`.ok`) and computes exact canonical modular subtraction
    `(p + a mod p - b mod p) mod p < p`. -/
theorem goldilocks_sub_spec (a b : goldilocks.Goldilocks) :
    ∃ y : goldilocks.Goldilocks,
      goldilocks.goldilocks_sub a b = .ok y ∧
      y.val = (GoldilocksP + a.val % GoldilocksP - b.val % GoldilocksP) % GoldilocksP ∧
      y.val < GoldilocksP := by
  unfold goldilocks.goldilocks_sub
  rw [goldilocks_prime_eq]
  obtain ⟨ga, hga, hga_eq, hga_lt⟩ := goldilocks_canon_spec a
  obtain ⟨gb, hgb, hgb_eq, hgb_lt⟩ := goldilocks_canon_spec b
  rw [hga]; dsimp only [Bind.bind, Result.bind]
  rw [hgb]; dsimp only [Result.bind, lift]
  have hsh : (1#u128 <<< 64#i32 : Result Std.U128) = .ok 18446744073709551616#u128 := rfl
  rw [hsh]; dsimp only [Result.bind]
  have hi_val : (18446744073709551616#u128).val = 2 ^ 64 := rfl
  have hia : (UScalar.cast .U128 ga).val = ga.val := u64_cast_u128_val ga
  have hib : (UScalar.cast .U128 gb).val = gb.val := u64_cast_u128_val gb
  have hp_val : (UScalar.cast .U128 18446744069414584321#u64).val = GoldilocksP := rfl
  obtain ⟨hi2, hi2_val⟩ := u128_add_ok (a := 18446744073709551616#u128) (b := UScalar.cast .U128 ga)
    (by rw [hi_val, hia]; exact Nat.lt_trans (Nat.add_lt_add_left hga_lt _) (by decide))
  rw [hi2]; dsimp only [Result.bind]
  let i2 : Std.U128 := ⟨(18446744073709551616#u128).bv + (UScalar.cast .U128 ga).bv⟩
  obtain ⟨hd, hd_val⟩ := u128_sub_ok (a := i2) (b := UScalar.cast .U128 gb)
    (by rw [hi2_val, hi_val, hia, hib]; exact Nat.le_trans (Nat.le_trans (Nat.le_of_lt hgb_lt) (by decide)) (Nat.le_add_right _ _))
  rw [hd]; dsimp only [Result.bind]
  let d : Std.U128 := ⟨i2.bv - (UScalar.cast .U128 gb).bv⟩
  rw [u128_shr64_eq d]; dsimp only [Result.bind]
  let ge : Std.U128 := ⟨d.bv >>> 64⟩ &&& 1#u128
  have hge_val : ge.val = (d.val / (2 ^ 64)) % 2 := by
    rw [u128_and_one_val, u128_shr64_val]
  have hd_eq : d.val = 2 ^ 64 + ga.val - gb.val := by
    rw [hd_val, hi2_val, hi_val, hia, hib]
  have hge_le : ge.val ≤ (1#u128).val := by
    change ge.val ≤ 1
    rw [hge_val]
    exact Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
  obtain ⟨hi6, hi6_val⟩ := u128_sub_ok (a := 1#u128) (b := ge) hge_le
  rw [hi6]; dsimp only [Result.bind]
  let i6 : Std.U128 := ⟨(1#u128).bv - ge.bv⟩
  have hi6_eq : i6.val = 1 - ge.val := by
    exact hi6_val
  obtain ⟨hadj, hadj_val⟩ := u128_mul_ok
    (a := UScalar.cast .U128 18446744069414584321#u64) (b := i6)
    (by rw [hp_val, hi6_eq]; exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.sub_le 1 _)) (by decide))
  rw [hadj]; dsimp only [Result.bind]
  let adj : Std.U128 := ⟨(UScalar.cast .U128 18446744069414584321#u64).bv * i6.bv⟩
  obtain ⟨hi7, hi7_val⟩ := u128_add_ok (a := d) (b := adj)
    (by rw [hd_eq, hadj_val, hp_val, hi6_eq]; exact goldilocks_intermediate_bound _ _ _ (Nat.lt_trans hga_lt (by decide)))
  rw [hi7]; dsimp only [Result.bind]
  let i7 : Std.U128 := ⟨d.bv + adj.bv⟩
  change i7.val = d.val + adj.val at hi7_val
  have hp1 : (1#u128).val = 1 := rfl
  let i8 : Std.U128 := i7 &&& 18446744073709551615#u128
  have hi8_val : i8.val = i7.val % (2 ^ 64) := u128_and_mask64_val i7
  have hi8_lt : i8.val < 2 ^ 64 := by rw [hi8_val]; exact Nat.mod_lt _ (by decide)
  refine ⟨UScalar.cast .U64 i8, rfl, ?_, ?_⟩
  · rw [u128_cast_u64_val_of_lt i8 hi8_lt, hi8_val, hi7_val, hadj_val, hp_val, hi6_eq,
        hge_val, hd_eq, ← hga_eq, ← hgb_eq]
    exact goldilocks_borrow_mod _ _ _ _ (by decide) hga_lt hgb_lt
  · rw [u128_cast_u64_val_of_lt i8 hi8_lt, hi8_val, hi7_val, hadj_val, hp_val, hi6_eq,
        hge_val, hd_eq, goldilocks_borrow_mod _ _ _ _ (by decide) hga_lt hgb_lt]
    exact Nat.mod_lt _ (by decide)

set_option maxHeartbeats 200000 in
/-- Branchless 128-bit Goldilocks folding `goldilocks_reduce128` ($2^{64} \equiv 2^{32}-1$,
    $2^{96} \equiv -1 \pmod p$) is total and reduces any `u128` modulo $p$. -/
theorem goldilocks_reduce128_spec (x : Std.U128) :
    ∃ y : goldilocks.Goldilocks,
      goldilocks.goldilocks_reduce128 x = .ok y ∧
      y.val = x.val % GoldilocksP ∧
      y.val < GoldilocksP := by
  unfold goldilocks.goldilocks_reduce128
  rw [goldilocks_epsilon_eq]
  simp only [Bind.bind, Result.bind, lift]
  let i0 : Std.U128 := x &&& 18446744073709551615#u128
  have hi0_val : i0.val = x.val % (2 ^ 64) := u128_and_mask64_val x
  have hi0_lt : i0.val < 2 ^ 64 := by rw [hi0_val]; exact Nat.mod_lt _ (by decide)
  let lo : Std.U64 := UScalar.cast .U64 i0
  have hlo_val : lo.val = x.val % (2 ^ 64) := by
    rw [u128_cast_u64_val_of_lt i0 hi0_lt, hi0_val]
  rw [u128_shr64_eq x]; dsimp only [Result.bind]
  let i1 : Std.U128 := ⟨x.bv >>> 64⟩
  have hx_lt : x.val < 2 ^ 128 := x.bv.isLt
  have hi1_val : i1.val = x.val / (2 ^ 64) := u128_shr64_val x
  have hi1_lt : i1.val < 2 ^ 64 := by rw [hi1_val]; exact (Nat.div_lt_iff_lt_mul (by decide)).mpr hx_lt
  let hi : Std.U64 := UScalar.cast .U64 i1
  have hhi_val : hi.val = x.val / (2 ^ 64) := by
    rw [u128_cast_u64_val_of_lt i1 hi1_lt, hi1_val]
  let hi_lo : Std.U64 := hi &&& 4294967295#u64
  have hhi_lo_val : hi_lo.val = hi.val % (2 ^ 32) := u64_and_mask32_val hi
  have hhi_lo_lt : hi_lo.val < 2 ^ 32 := by rw [hhi_lo_val]; exact Nat.mod_lt _ (by decide)
  rw [u64_shr32_eq hi]; dsimp only [Result.bind]
  let hi_hi : Std.U64 := ⟨hi.bv >>> 32⟩
  have hhi_hi_val : hi_hi.val = hi.val / (2 ^ 32) := u64_shr32_val hi
  have hhi_hi_lt : hi_hi.val < 2 ^ 32 := by rw [hhi_hi_val]; exact (Nat.div_lt_iff_lt_mul (by decide)).mpr hi.bv.isLt
  rw [u64_shl32_eq hi_lo]; dsimp only [Result.bind]
  let i2 : Std.U64 := ⟨hi_lo.bv <<< 32⟩
  have hi2_val : i2.val = hi_lo.val * (2 ^ 32) := u64_shl32_val_of_lt hi_lo hhi_lo_lt
  obtain ⟨hmid, hmid_val⟩ := u64_sub_ok (a := i2) (b := hi_lo) (by rw [hi2_val]; exact Nat.le_mul_of_pos_right _ (by decide))
  rw [hmid]; dsimp only [Result.bind]
  let mid : Std.U64 := ⟨i2.bv - hi_lo.bv⟩
  have hmid_lt : mid.val < GoldilocksP := by
    rw [hmid_val, hi2_val]
    have he : hi_lo.val * 2 ^ 32 - hi_lo.val = hi_lo.val * (2 ^ 32 - 1) := by
      simpa only [Nat.mul_one] using (Nat.mul_sub_left_distrib hi_lo.val (2 ^ 32) 1).symm
    rw [he]
    exact Nat.lt_trans (Nat.mul_lt_mul_of_pos_right hhi_lo_lt (by decide)) (by decide)
  obtain ⟨sum, hsum, hsum_eq, hsum_lt⟩ := goldilocks_add_spec lo mid
  rw [hsum]; dsimp only [Result.bind]
  obtain ⟨res, hres, hres_eq, hres_lt⟩ := goldilocks_sub_spec sum hi_hi
  rw [hres]
  refine ⟨res, rfl, ?_, hres_lt⟩
  have hhi_hi_lt_p : hi_hi.val < GoldilocksP := by exact Nat.lt_trans hhi_hi_lt (by decide)
  have hmid_mod : mid.val % GoldilocksP = mid.val := Nat.mod_eq_of_lt hmid_lt
  have hsum_mod : sum.val % GoldilocksP = sum.val := Nat.mod_eq_of_lt hsum_lt
  have hhi_hi_mod : hi_hi.val % GoldilocksP = hi_hi.val := Nat.mod_eq_of_lt hhi_hi_lt_p
  rw [hres_eq, hsum_mod, hhi_hi_mod, hsum_eq, hmid_mod]
  -- Algebraic congruence: x = lo + hi_lo * 2^64 + hi_hi * 2^96
  -- Since 2^64 = p + (2^32 - 1) and 2^96 = p * (2^32 + 1) - 1:
  -- x + p = (lo + mid + p - hi_hi) + p * (hi_lo + hi_hi * (2^32 + 1))
  have hx_decomp : x.val = lo.val + hi_lo.val * (2 ^ 64) + hi_hi.val * (2 ^ 96) := by
    have hx := (Nat.mod_add_div x.val (2 ^ 64)).symm
    have hh := (Nat.mod_add_div hi.val (2 ^ 32)).symm
    rw [← hlo_val, ← hhi_val] at hx
    rw [← hhi_lo_val, ← hhi_hi_val] at hh
    rw [hx, hh, Nat.mul_add]
    simp only [Nat.reducePow]
    ac_rfl
  have hmid_eq : mid.val = hi_lo.val * (2 ^ 32 - 1) := by
    rw [hmid_val, hi2_val]
    simpa only [Nat.mul_one] using (Nat.mul_sub_left_distrib hi_lo.val (2 ^ 32) 1).symm
  -- Prove congruence modulo GoldilocksP by relating (lo.val % p + mid.val) % p + p - hi_hi.val
  -- to (x.val + p * K) % p:
  have hstep1 :
      (GoldilocksP + (lo.val % GoldilocksP + mid.val) % GoldilocksP - hi_hi.val) % GoldilocksP =
      (GoldilocksP + (lo.val + mid.val) - hi_hi.val) % GoldilocksP := by
    rw [Nat.mod_add_mod]
    exact mod_sub_normalize _ _ _ (Nat.le_of_lt hhi_hi_lt_p)
  rw [hstep1]
  have hstep2 :
      x.val + GoldilocksP =
      (GoldilocksP + (lo.val + mid.val) - hi_hi.val) +
        GoldilocksP * (hi_lo.val + hi_hi.val * (2 ^ 32 + 1)) := by
    have hbnd : hi_hi.val ≤ GoldilocksP + (lo.val + mid.val) :=
      Nat.le_trans (Nat.le_of_lt hhi_hi_lt_p) (Nat.le_add_right _ _)
    have he : (x.val + GoldilocksP) + hi_hi.val =
        GoldilocksP + (lo.val + mid.val) +
          GoldilocksP * (hi_lo.val + hi_hi.val * (2 ^ 32 + 1)) := by
      rw [hx_decomp, hmid_eq]
      calc
        _ = GoldilocksP + lo.val + hi_lo.val * 2 ^ 64 + hi_hi.val * (2 ^ 96 + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
          ac_rfl
        _ = GoldilocksP + lo.val + hi_lo.val * (GoldilocksP + (2 ^ 32 - 1)) +
            hi_hi.val * (GoldilocksP * (2 ^ 32 + 1)) := by
          rw [show 2 ^ 64 = GoldilocksP + (2 ^ 32 - 1) from by decide,
            show 2 ^ 96 + 1 = GoldilocksP * (2 ^ 32 + 1) from by decide]
        _ = _ := by
          simp only [Nat.mul_add]
          ac_rfl
    have hr : ((GoldilocksP + (lo.val + mid.val) - hi_hi.val) +
        GoldilocksP * (hi_lo.val + hi_hi.val * (2 ^ 32 + 1))) + hi_hi.val =
        GoldilocksP + (lo.val + mid.val) +
          GoldilocksP * (hi_lo.val + hi_hi.val * (2 ^ 32 + 1)) := by
      calc
        _ = ((GoldilocksP + (lo.val + mid.val) - hi_hi.val) + hi_hi.val) +
          GoldilocksP * (hi_lo.val + hi_hi.val * (2 ^ 32 + 1)) := Nat.add_right_comm _ _ _
        _ = _ := by rw [Nat.sub_add_cancel hbnd]
    exact Nat.add_right_cancel (he.trans hr.symm)
  have hmod_x : (x.val + GoldilocksP) % GoldilocksP = x.val % GoldilocksP := by
    exact Nat.add_mul_mod_self_left x.val GoldilocksP 1
  rw [← hmod_x, hstep2, Nat.add_mul_mod_self_left]

/-- Branchless `goldilocks_mul` is total (`.ok`) and computes exact canonical modular multiplication
    `((a mod p) * (b mod p)) mod p < p`. -/
theorem goldilocks_mul_spec (a b : goldilocks.Goldilocks) :
    ∃ y : goldilocks.Goldilocks,
      goldilocks.goldilocks_mul a b = .ok y ∧
      y.val = ((a.val % GoldilocksP) * (b.val % GoldilocksP)) % GoldilocksP ∧
      y.val < GoldilocksP := by
  unfold goldilocks.goldilocks_mul
  obtain ⟨ga, hga, hga_eq, hga_lt⟩ := goldilocks_canon_spec a
  obtain ⟨gb, hgb, hgb_eq, hgb_lt⟩ := goldilocks_canon_spec b
  rw [hga]; simp only [Bind.bind, Result.bind]
  rw [hgb]; dsimp only [Result.bind, lift]
  have hia : (UScalar.cast .U128 ga).val = ga.val := u64_cast_u128_val ga
  have hib : (UScalar.cast .U128 gb).val = gb.val := u64_cast_u128_val gb
  have hprod_lt : (UScalar.cast .U128 ga).val * (UScalar.cast .U128 gb).val < 2 ^ 128 := by
    rw [hia, hib]
    have hh := Nat.mul_lt_mul'' (show ga.val < 2 ^ 64 from ga.bv.isLt) (show gb.val < 2 ^ 64 from gb.bv.isLt)
    exact hh
  obtain ⟨hprod, hprod_val⟩ := u128_mul_ok (a := UScalar.cast .U128 ga) (b := UScalar.cast .U128 gb) hprod_lt
  rw [hprod]; dsimp only [Result.bind]
  obtain ⟨y, hy, hy_eq, hy_lt⟩ := goldilocks_reduce128_spec
    ⟨(UScalar.cast .U128 ga).bv * (UScalar.cast .U128 gb).bv⟩
  refine ⟨y, hy, ?_, hy_lt⟩
  rw [hy_eq, hprod_val, hia, hib, hga_eq, hgb_eq]

/-- `goldilocks_pow7` (Poseidon2 S-box $x \mapsto x^7 \bmod p$) is total and exact. -/
theorem goldilocks_pow7_spec (x : goldilocks.Goldilocks) :
    ∃ y : goldilocks.Goldilocks,
      goldilocks.goldilocks_pow7 x = .ok y ∧
      y.val = ((x.val % GoldilocksP) ^ 7) % GoldilocksP ∧
      y.val < GoldilocksP := by
  unfold goldilocks.goldilocks_pow7
  obtain ⟨x2, hx2, hx2_eq, hx2_lt⟩ := goldilocks_mul_spec x x
  rw [hx2]; simp only [Bind.bind, Result.bind]
  obtain ⟨x3, hx3, hx3_eq, hx3_lt⟩ := goldilocks_mul_spec x2 x
  rw [hx3]; dsimp only [Result.bind]
  obtain ⟨x4, hx4, hx4_eq, hx4_lt⟩ := goldilocks_mul_spec x2 x2
  rw [hx4]; dsimp only [Result.bind]
  obtain ⟨y, hy, hy_eq, hy_lt⟩ := goldilocks_mul_spec x3 x4
  refine ⟨y, hy, ?_, hy_lt⟩
  rw [hy_eq, Nat.mod_eq_of_lt hx3_lt, Nat.mod_eq_of_lt hx4_lt, hx3_eq, hx4_eq,
      Nat.mod_eq_of_lt hx2_lt, hx2_eq]
  let r := x.val % GoldilocksP
  rw [Nat.mul_mod_mod, Nat.mod_mul_mod]
  have h7 : r * r % GoldilocksP * r * (r * r % GoldilocksP * (r * r % GoldilocksP)) % GoldilocksP =
      (r ^ 7) % GoldilocksP := by
    calc
      r * r % GoldilocksP * r * (r * r % GoldilocksP * (r * r % GoldilocksP)) % GoldilocksP
          = ((r * r % GoldilocksP * r) % GoldilocksP *
              ((r * r % GoldilocksP * (r * r % GoldilocksP)) % GoldilocksP)) % GoldilocksP := by
            rw [Nat.mul_mod]
      _ = (((r * r * r) % GoldilocksP) * ((r * r * (r * r)) % GoldilocksP)) % GoldilocksP := by
            have h3 : (r * r % GoldilocksP * r) % GoldilocksP =
                (r * r * r) % GoldilocksP := Nat.mod_mul_mod (r * r) r GoldilocksP
            have h4 : (r * r % GoldilocksP * (r * r % GoldilocksP)) % GoldilocksP =
                (r * r * (r * r)) % GoldilocksP := by
              rw [Nat.mul_mod_mod, Nat.mod_mul_mod]
            rw [h3, h4]
      _ = (r * r * r * (r * r * (r * r))) % GoldilocksP := by
            rw [← Nat.mul_mod]
      _ = (r ^ 7) % GoldilocksP := by
            have hp7 : r * r * r * (r * r * (r * r)) = r ^ 7 := by
              simp [Nat.pow_succ, Nat.mul_assoc]
            rw [hp7]
  exact h7

/-- Branchless Fermat inversion `goldilocks_inv_or_zero` ($a^{p-2} \bmod p$) never panics or overflows. -/
theorem goldilocks_inv_or_zero_total (a : goldilocks.Goldilocks) :
    ∃ y : goldilocks.Goldilocks,
      goldilocks.goldilocks_inv_or_zero a = .ok y ∧ y.val < GoldilocksP := by
  have hsq : ∀ u, ∃ v, goldilocks.goldilocks_square u = .ok v ∧ v.val < GoldilocksP := by
    intro u; unfold goldilocks.goldilocks_square
    obtain ⟨v, hv, _, hlt⟩ := goldilocks_mul_spec u u; exact ⟨v, hv, hlt⟩
  have hsq3 : ∀ u, ∃ v, goldilocks.goldilocks_sq3 u = .ok v ∧ v.val < GoldilocksP := by
    intro u; unfold goldilocks.goldilocks_sq3
    obtain ⟨v1, hv1, _⟩ := hsq u; rw [hv1]; simp only [Bind.bind, Result.bind]
    obtain ⟨v2, hv2, _⟩ := hsq v1; rw [hv2]; dsimp only [Result.bind]
    exact hsq v2
  have hsq6 : ∀ u, ∃ v, goldilocks.goldilocks_sq6 u = .ok v ∧ v.val < GoldilocksP := by
    intro u; unfold goldilocks.goldilocks_sq6
    obtain ⟨v1, hv1, _⟩ := hsq3 u; rw [hv1]; simp only [Bind.bind, Result.bind]
    exact hsq3 v1
  have hsq12 : ∀ u, ∃ v, goldilocks.goldilocks_sq12 u = .ok v ∧ v.val < GoldilocksP := by
    intro u; unfold goldilocks.goldilocks_sq12
    obtain ⟨v1, hv1, _⟩ := hsq6 u; rw [hv1]; simp only [Bind.bind, Result.bind]
    exact hsq6 v1
  have hsq33 : ∀ u, ∃ v, goldilocks.goldilocks_sq33 u = .ok v ∧ v.val < GoldilocksP := by
    intro u; unfold goldilocks.goldilocks_sq33
    obtain ⟨v1, hv1, _⟩ := hsq12 u; rw [hv1]; simp only [Bind.bind, Result.bind]
    obtain ⟨v2, hv2, _⟩ := hsq12 v1; rw [hv2]; dsimp only [Result.bind]
    obtain ⟨v3, hv3, _⟩ := hsq6 v2; rw [hv3]; dsimp only [Result.bind]
    exact hsq3 v3
  unfold goldilocks.goldilocks_inv_or_zero
  obtain ⟨c, hc, _, _⟩ := goldilocks_canon_spec a; rw [hc]; simp only [Bind.bind, Result.bind]
  obtain ⟨g, hg, _⟩ := hsq c; rw [hg]; dsimp only [Result.bind]
  obtain ⟨t2, ht2, _, _⟩ := goldilocks_mul_spec g c; rw [ht2]; dsimp only [Result.bind]
  obtain ⟨g1, hg1, _⟩ := hsq t2; rw [hg1]; dsimp only [Result.bind]
  obtain ⟨t3, ht3, _, _⟩ := goldilocks_mul_spec g1 c; rw [ht3]; dsimp only [Result.bind]
  obtain ⟨g2, hg2, _⟩ := hsq3 t3; rw [hg2]; dsimp only [Result.bind]
  obtain ⟨t6, ht6, _, _⟩ := goldilocks_mul_spec g2 t3; rw [ht6]; dsimp only [Result.bind]
  obtain ⟨g3, hg3, _⟩ := hsq6 t6; rw [hg3]; dsimp only [Result.bind]
  obtain ⟨t12, ht12, _, _⟩ := goldilocks_mul_spec g3 t6; rw [ht12]; dsimp only [Result.bind]
  obtain ⟨g4, hg4, _⟩ := hsq12 t12; rw [hg4]; dsimp only [Result.bind]
  obtain ⟨t24, ht24, _, _⟩ := goldilocks_mul_spec g4 t12; rw [ht24]; dsimp only [Result.bind]
  obtain ⟨g5, hg5, _⟩ := hsq6 t24; rw [hg5]; dsimp only [Result.bind]
  obtain ⟨t30, ht30, _, _⟩ := goldilocks_mul_spec g5 t6; rw [ht30]; dsimp only [Result.bind]
  obtain ⟨g6, hg6, _⟩ := hsq t30; rw [hg6]; dsimp only [Result.bind]
  obtain ⟨t31, ht31, _, _⟩ := goldilocks_mul_spec g6 c; rw [ht31]; dsimp only [Result.bind]
  obtain ⟨g7, hg7, _⟩ := hsq t31; rw [hg7]; dsimp only [Result.bind]
  obtain ⟨t32, ht32, _, _⟩ := goldilocks_mul_spec g7 c; rw [ht32]; dsimp only [Result.bind]
  obtain ⟨hi, hhi, _⟩ := hsq33 t31; rw [hhi]; dsimp only [Result.bind]
  obtain ⟨res, hres, _, hlt⟩ := goldilocks_mul_spec hi t32
  exact ⟨res, hres, hlt⟩

/-! ## Canonical inputs and extension addition -/

theorem goldilocks_from_canonical_spec (raw : Std.U64) :
    (goldilocks.goldilocks_from_canonical raw = .ok (.Ok raw) ↔
      raw.val < GoldilocksP) ∧
    (GoldilocksP ≤ raw.val → goldilocks.goldilocks_from_canonical raw =
      .ok (.Err { raw_value := raw })) := by
  have hc : (raw < goldilocks.GOLDILOCKS_PRIME) ↔ raw.val < GoldilocksP := by
    rw [goldilocks_prime_eq]
    exact BitVec.lt_def
  simp only [goldilocks.goldilocks_from_canonical, hc]
  by_cases h : raw.val < GoldilocksP
  · constructor
    · simp [h]
    · intro hn; exact False.elim (Nat.not_lt_of_ge hn h)
  · constructor
    · simp [h]
    · intro _; simp [h]

theorem goldilocks_neg_spec (a : goldilocks.Goldilocks) :
    ∃ y, goldilocks.goldilocks_neg a = .ok y ∧
      y.val = (GoldilocksP - a.val % GoldilocksP) % GoldilocksP ∧
      y.val < GoldilocksP := by
  obtain ⟨y, hy, veq, vlt⟩ := goldilocks_sub_spec 0#u64 a
  refine ⟨y, hy, ?_, vlt⟩
  simpa using veq

theorem goldilocks_ext2_add_spec (a b : goldilocks.GoldilocksExt2) :
    ∃ y, goldilocks.goldilocks_ext2_add a b = .ok y ∧
      y.c0.val < GoldilocksP ∧ y.c1.val < GoldilocksP ∧
      y.c0.val = (a.c0.val % GoldilocksP + b.c0.val % GoldilocksP) % GoldilocksP ∧
      y.c1.val = (a.c1.val % GoldilocksP + b.c1.val % GoldilocksP) % GoldilocksP := by
  obtain ⟨c0, h0, e0, b0⟩ := goldilocks_add_spec a.c0 b.c0
  obtain ⟨c1, h1, e1, b1⟩ := goldilocks_add_spec a.c1 b.c1
  refine ⟨⟨c0, c1⟩, ?_, b0, b1, e0, e1⟩
  simp [goldilocks.goldilocks_ext2_add, h0, h1]

theorem goldilocks_ext2_mul_spec (a b : goldilocks.GoldilocksExt2) :
    ∃ y, goldilocks.goldilocks_ext2_mul a b = .ok y ∧
      y.c0.val < GoldilocksP ∧ y.c1.val < GoldilocksP ∧
      y.c0.val = ((a.c0.val % GoldilocksP) * (b.c0.val % GoldilocksP) +
        7 * ((a.c1.val % GoldilocksP) * (b.c1.val % GoldilocksP))) % GoldilocksP ∧
      y.c1.val = ((a.c0.val % GoldilocksP) * (b.c1.val % GoldilocksP) +
        (a.c1.val % GoldilocksP) * (b.c0.val % GoldilocksP)) % GoldilocksP := by
  obtain ⟨p, hp, vp, bp⟩ := goldilocks_mul_spec a.c0 b.c0
  obtain ⟨q, hq, vq, bq⟩ := goldilocks_mul_spec a.c1 b.c1
  obtain ⟨sa, hsa, vsa, bsa⟩ := goldilocks_add_spec a.c0 a.c1
  obtain ⟨sb, hsb, vsb, bsb⟩ := goldilocks_add_spec b.c0 b.c1
  obtain ⟨prod, hprod, vprod, bprod⟩ := goldilocks_mul_spec sa sb
  obtain ⟨g, hg, vg, bg⟩ := goldilocks_sub_spec prod p
  obtain ⟨c1, hc1, vc1, bc1⟩ := goldilocks_sub_spec g q
  obtain ⟨seven, hseven, vseven, bseven⟩ :=
    goldilocks_mul_spec goldilocks.GOLDILOCKS_NON_RESIDUE q
  obtain ⟨c0, hc0, vc0, bc0⟩ := goldilocks_add_spec p seven
  refine ⟨⟨c0, c1⟩, ?_, bc0, bc1, ?_, ?_⟩
  · unfold goldilocks.goldilocks_ext2_mul
    simp only [hp, hq, hsa, hsb, hprod, hg, hc1, hseven, hc0,
      bind_eq_result_bind, result_bind_ok]
  · have hn : goldilocks.GOLDILOCKS_NON_RESIDUE.val % GoldilocksP = 7 := by
      unfold goldilocks.GOLDILOCKS_NON_RESIDUE GoldilocksP
      rfl
    rw [vc0, vseven, hn, vp, vq]
    simp only [Nat.mod_mod, Nat.mul_mod, Nat.add_mod]
  · let a0 := a.c0.val % GoldilocksP
    let a1 := a.c1.val % GoldilocksP
    let b0 := b.c0.val % GoldilocksP
    let b1 := b.c1.val % GoldilocksP
    have hexpand : (a0 + a1) * (b0 + b1) =
        a0 * b0 + a1 * b1 + (a0 * b1 + a1 * b0) := by
      simp only [Nat.add_mul, Nat.mul_add]
      ac_rfl
    have hprod_val : prod.val =
        (a0 * b0 + a1 * b1 + (a0 * b1 + a1 * b0)) % GoldilocksP := by
      rw [vprod, vsa, vsb]
      simp only [Nat.mod_mod, Nat.mod_mul_mod, Nat.mul_mod_mod]
      change ((a0 + a1) * (b0 + b1)) % GoldilocksP = _
      rw [hexpand]
    rw [vc1, Nat.mod_eq_of_lt bg, Nat.mod_eq_of_lt bq,
      vg, Nat.mod_eq_of_lt bprod, Nat.mod_eq_of_lt bp, hprod_val, vp, vq]
    change (GoldilocksP + (GoldilocksP +
      (a0 * b0 + a1 * b1 + (a0 * b1 + a1 * b0)) % GoldilocksP -
      (a0 * b0) % GoldilocksP) % GoldilocksP -
      (a1 * b1) % GoldilocksP) % GoldilocksP =
      (a0 * b1 + a1 * b0) % GoldilocksP
    rw [Nat.add_assoc, mod_sub_add_cancel _ _ _ (by decide), mod_sub_add_cancel _ _ _ (by decide)]

@[expose]
def pureHornerGoldilocksPrefix (coeffs : List goldilocks.Goldilocks) (x : Nat) :
    Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => pureHornerGoldilocksPrefix coeffs x n
      ((acc % GoldilocksP * (x % GoldilocksP) +
        (coeffs.getD n 0#u64).val % GoldilocksP) % GoldilocksP)

@[expose]
def pureHornerGoldilocks (coeffs : List goldilocks.Goldilocks) (x : Nat) : Nat :=
  pureHornerGoldilocksPrefix coeffs x coeffs.length 0

private theorem horner_goldilocks_fuel (coeffs : Slice goldilocks.Goldilocks)
    (x : goldilocks.Goldilocks) (n : Nat) (rem : Std.Usize)
    (acc : goldilocks.Goldilocks) (hr : rem.val = n) (hn : n ≤ coeffs.val.length) :
    ∃ y, loopFuel (n + 1)
      (fun (a, r) => threshold.shamir_eval_poly_goldilocks_loop.body coeffs x a r)
      (acc, rem) = .ok y ∧
      y.val = pureHornerGoldilocksPrefix coeffs.val (x.val % GoldilocksP) n acc.val := by
  induction n generalizing rem acc with
  | zero =>
    have hz : rem = 0#usize := UScalar.eq_of_val_eq hr
    subst rem
    refine ⟨acc, ?_, rfl⟩
    simp [loopFuel, threshold.shamir_eval_poly_goldilocks_loop.body]
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
    have hget : Slice.index_usize coeffs r = .ok (coeffs.val.getD n 0#u64) := by
      simp only [Slice.index_usize, dite_eq_left_of_eq_true (eq_true hi)]
      rw [List.getElem_eq_getD 0#u64, hr']
    obtain ⟨prod, hprod, vprod, _⟩ := goldilocks_mul_spec acc x
    obtain ⟨sum, hsum, vsum, _⟩ := goldilocks_add_spec prod (coeffs.val.getD n 0#u64)
    obtain ⟨y, hy, vy⟩ := ih r sum hr' (Nat.le_trans (Nat.le_succ n) hn)
    refine ⟨y, ?_, ?_⟩
    · rw [loopFuel_succ]
      simp only [threshold.shamir_eval_poly_goldilocks_loop.body, hp, ite_eq_left_of_eq_true,
        hs, bind_eq_result_bind, result_bind_ok, hprod, hget, hsum]
      exact hy
    · rw [vy, vsum, vprod]
      simp only [pureHornerGoldilocksPrefix, Nat.mod_mod, Nat.mod_add_mod]

theorem shamir_eval_poly_goldilocks_spec (coeffs : Slice goldilocks.Goldilocks)
    (x : goldilocks.Goldilocks) :
    ∃ y, threshold.shamir_eval_poly_goldilocks coeffs x = .ok y ∧
      y.val = pureHornerGoldilocks coeffs.val (x.val % GoldilocksP) := by
  obtain ⟨y, hy, vy⟩ := horner_goldilocks_fuel coeffs x coeffs.val.length
    (Slice.len coeffs) 0#u64 (Slice.len_val coeffs) (Nat.le_refl _)
  refine ⟨y, ?_, vy⟩
  unfold threshold.shamir_eval_poly_goldilocks threshold.shamir_eval_poly_goldilocks_loop
  apply loop_ok_of_loopFuel (fuel := coeffs.val.length + 1) _ hy
  simpa only [Slice.len_val] using usize_lt_loopMaxFuel (Slice.len coeffs)


private theorem goldilocks_mul_powers (base i j : Nat) (a b : Std.U64)
    (ha : a.val = base ^ i % GoldilocksP) (hb : b.val = base ^ j % GoldilocksP) :
    ∃ y, goldilocks.goldilocks_mul a b = .ok y ∧
      y.val = base ^ (i + j) % GoldilocksP ∧ y.val < GoldilocksP := by
  obtain ⟨y, hy, vy, hlt⟩ := goldilocks_mul_spec a b
  refine ⟨y, hy, ?_, hlt⟩
  rw [vy, ha, hb, Nat.mod_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.pow_add]

private theorem goldilocks_square_power (base n : Nat) (a : Std.U64)
    (ha : a.val = base ^ n % GoldilocksP) :
    ∃ y, goldilocks.goldilocks_square a = .ok y ∧
      y.val = base ^ (n * 2) % GoldilocksP ∧ y.val < GoldilocksP := by
  simpa only [goldilocks.goldilocks_square, Nat.mul_two] using
    goldilocks_mul_powers base n n a a ha ha

private theorem goldilocks_sq3_power (base n : Nat) (a : Std.U64)
    (ha : a.val = base ^ n % GoldilocksP) :
    ∃ y, goldilocks.goldilocks_sq3 a = .ok y ∧
      y.val = base ^ (n * 8) % GoldilocksP ∧ y.val < GoldilocksP := by
  unfold goldilocks.goldilocks_sq3
  obtain ⟨v0, h0, value0, bound0⟩ := goldilocks_square_power base (n) a ha
  rw [h0]; try dsimp only [Bind.bind, Result.bind]
  obtain ⟨v1, h1, value1, bound1⟩ := goldilocks_square_power base ((n * 2)) v0 value0
  rw [h1]; try dsimp only [Bind.bind, Result.bind]
  obtain ⟨v2, h2, value2, bound2⟩ := goldilocks_square_power base (((n * 2) * 2)) v1 value1
  rw [h2]; try dsimp only [Bind.bind, Result.bind]
  exact ⟨v2, rfl, by simpa only [Nat.mul_assoc, Nat.reduceMul] using value2, bound2⟩

private theorem goldilocks_sq6_power (base n : Nat) (a : Std.U64)
    (ha : a.val = base ^ n % GoldilocksP) :
    ∃ y, goldilocks.goldilocks_sq6 a = .ok y ∧
      y.val = base ^ (n * 64) % GoldilocksP ∧ y.val < GoldilocksP := by
  unfold goldilocks.goldilocks_sq6
  obtain ⟨v0, h0, value0, bound0⟩ := goldilocks_sq3_power base (n) a ha
  rw [h0]; try dsimp only [Bind.bind, Result.bind]
  obtain ⟨v1, h1, value1, bound1⟩ := goldilocks_sq3_power base ((n * 8)) v0 value0
  rw [h1]; try dsimp only [Bind.bind, Result.bind]
  exact ⟨v1, rfl, by simpa only [Nat.mul_assoc, Nat.reduceMul] using value1, bound1⟩

private theorem goldilocks_sq12_power (base n : Nat) (a : Std.U64)
    (ha : a.val = base ^ n % GoldilocksP) :
    ∃ y, goldilocks.goldilocks_sq12 a = .ok y ∧
      y.val = base ^ (n * 4096) % GoldilocksP ∧ y.val < GoldilocksP := by
  unfold goldilocks.goldilocks_sq12
  obtain ⟨v0, h0, value0, bound0⟩ := goldilocks_sq6_power base (n) a ha
  rw [h0]; try dsimp only [Bind.bind, Result.bind]
  obtain ⟨v1, h1, value1, bound1⟩ := goldilocks_sq6_power base ((n * 64)) v0 value0
  rw [h1]; try dsimp only [Bind.bind, Result.bind]
  exact ⟨v1, rfl, by simpa only [Nat.mul_assoc, Nat.reduceMul] using value1, bound1⟩

private theorem goldilocks_sq33_power (base n : Nat) (a : Std.U64)
    (ha : a.val = base ^ n % GoldilocksP) :
    ∃ y, goldilocks.goldilocks_sq33 a = .ok y ∧
      y.val = base ^ (n * 8589934592) % GoldilocksP ∧ y.val < GoldilocksP := by
  unfold goldilocks.goldilocks_sq33
  obtain ⟨v0, h0, value0, bound0⟩ := goldilocks_sq12_power base (n) a ha
  rw [h0]; try dsimp only [Bind.bind, Result.bind]
  obtain ⟨v1, h1, value1, bound1⟩ := goldilocks_sq12_power base ((n * 4096)) v0 value0
  rw [h1]; try dsimp only [Bind.bind, Result.bind]
  obtain ⟨v2, h2, value2, bound2⟩ := goldilocks_sq6_power base (((n * 4096) * 4096)) v1 value1
  rw [h2]; try dsimp only [Bind.bind, Result.bind]
  obtain ⟨v3, h3, value3, bound3⟩ := goldilocks_sq3_power base ((((n * 4096) * 4096) * 64)) v2 value2
  rw [h3]; try dsimp only [Bind.bind, Result.bind]
  exact ⟨v3, rfl, by simpa only [Nat.mul_assoc, Nat.reduceMul] using value3, bound3⟩

theorem goldilocks_inv_or_zero_spec (a : goldilocks.Goldilocks) :
    ∃ y, goldilocks.goldilocks_inv_or_zero a = .ok y ∧
      y.val = (a.val % GoldilocksP) ^ (GoldilocksP - 2) % GoldilocksP ∧
      y.val < GoldilocksP ∧ (a.val % GoldilocksP = 0 → y = 0#u64) := by
  generalize hbase : a.val % GoldilocksP = base
  unfold goldilocks.goldilocks_inv_or_zero
  obtain ⟨c, hc, vc, _⟩ := goldilocks_canon_spec a
  have pc : c.val = base ^ 1 % GoldilocksP := by rw [Nat.pow_one, ← hbase, Nat.mod_mod]; exact vc
  rw [hc]; try dsimp only [Bind.bind, Result.bind]
  obtain ⟨g, hg, pg, bg⟩ := goldilocks_square_power base 1 c pc
  simp only [Nat.reduceMul] at pg
  rw [hg]; try dsimp only [Result.bind]
  obtain ⟨t2, ht2, pt2, bt2⟩ := goldilocks_mul_powers base 2 1 g c pg pc
  simp only [Nat.reduceAdd] at pt2
  rw [ht2]; try dsimp only [Result.bind]
  obtain ⟨g1, hg1, pg1, bg1⟩ := goldilocks_square_power base 3 t2 pt2
  simp only [Nat.reduceMul] at pg1
  rw [hg1]; try dsimp only [Result.bind]
  obtain ⟨t3, ht3, pt3, bt3⟩ := goldilocks_mul_powers base 6 1 g1 c pg1 pc
  simp only [Nat.reduceAdd] at pt3
  rw [ht3]; try dsimp only [Result.bind]
  obtain ⟨g2, hg2, pg2, bg2⟩ := goldilocks_sq3_power base 7 t3 pt3
  simp only [Nat.reduceMul] at pg2
  rw [hg2]; try dsimp only [Result.bind]
  obtain ⟨t6, ht6, pt6, bt6⟩ := goldilocks_mul_powers base 56 7 g2 t3 pg2 pt3
  simp only [Nat.reduceAdd] at pt6
  rw [ht6]; try dsimp only [Result.bind]
  obtain ⟨g3, hg3, pg3, bg3⟩ := goldilocks_sq6_power base 63 t6 pt6
  simp only [Nat.reduceMul] at pg3
  rw [hg3]; try dsimp only [Result.bind]
  obtain ⟨t12, ht12, pt12, bt12⟩ := goldilocks_mul_powers base 4032 63 g3 t6 pg3 pt6
  simp only [Nat.reduceAdd] at pt12
  rw [ht12]; try dsimp only [Result.bind]
  obtain ⟨g4, hg4, pg4, bg4⟩ := goldilocks_sq12_power base 4095 t12 pt12
  simp only [Nat.reduceMul] at pg4
  rw [hg4]; try dsimp only [Result.bind]
  obtain ⟨t24, ht24, pt24, bt24⟩ := goldilocks_mul_powers base 16773120 4095 g4 t12 pg4 pt12
  simp only [Nat.reduceAdd] at pt24
  rw [ht24]; try dsimp only [Result.bind]
  obtain ⟨g5, hg5, pg5, bg5⟩ := goldilocks_sq6_power base 16777215 t24 pt24
  simp only [Nat.reduceMul] at pg5
  rw [hg5]; try dsimp only [Result.bind]
  obtain ⟨t30, ht30, pt30, bt30⟩ := goldilocks_mul_powers base 1073741760 63 g5 t6 pg5 pt6
  simp only [Nat.reduceAdd] at pt30
  rw [ht30]; try dsimp only [Result.bind]
  obtain ⟨g6, hg6, pg6, bg6⟩ := goldilocks_square_power base 1073741823 t30 pt30
  simp only [Nat.reduceMul] at pg6
  rw [hg6]; try dsimp only [Result.bind]
  obtain ⟨t31, ht31, pt31, bt31⟩ := goldilocks_mul_powers base 2147483646 1 g6 c pg6 pc
  simp only [Nat.reduceAdd] at pt31
  rw [ht31]; try dsimp only [Result.bind]
  obtain ⟨g7, hg7, pg7, bg7⟩ := goldilocks_square_power base 2147483647 t31 pt31
  simp only [Nat.reduceMul] at pg7
  rw [hg7]; try dsimp only [Result.bind]
  obtain ⟨t32, ht32, pt32, bt32⟩ := goldilocks_mul_powers base 4294967294 1 g7 c pg7 pc
  simp only [Nat.reduceAdd] at pt32
  rw [ht32]; try dsimp only [Result.bind]
  obtain ⟨hi, hhi, phi, bhi⟩ := goldilocks_sq33_power base 2147483647 t31 pt31
  simp only [Nat.reduceMul] at phi
  rw [hhi]; try dsimp only [Result.bind]
  obtain ⟨y, hy, py, bound_y⟩ := goldilocks_mul_powers base 18446744065119617024 4294967295 hi t32 phi pt32
  simp only [Nat.reduceAdd] at py
  rw [hy]; try dsimp only [Result.bind]
  have pexp : GoldilocksP - 2 = 18446744069414584319 := rfl
  refine ⟨y, rfl, ?_, bound_y, ?_⟩
  · rw [pexp]; exact py
  intro hz
  apply UScalar.eq_of_val_eq
  rw [py]
  change base ^ (GoldilocksP - 2) % GoldilocksP = 0
  rw [show base = 0 from hz, Nat.zero_pow (by decide : 0 < GoldilocksP - 2)]
  rfl

theorem tooth_goldilocks_inv_seven :
    (goldilocks.goldilocks_inv_or_zero 7#u64 >>= fun inv =>
      goldilocks.goldilocks_mul inv 7#u64) = .ok 1#u64 := by decide +kernel

theorem goldilocks_inv_spec (a : goldilocks.Goldilocks) :
    ∃ inv, goldilocks.goldilocks_inv_or_zero a = .ok inv ∧
      (goldilocks.goldilocks_inv a = .ok none ↔ a.val % GoldilocksP = 0 ∨ inv = 0#u64) ∧
      (inv ≠ 0#u64 → goldilocks.goldilocks_inv a = .ok (some inv)) := by
  obtain ⟨inv, hi, _, _, hz⟩ := goldilocks_inv_or_zero_spec a
  refine ⟨inv, hi, ?_, ?_⟩
  · simp only [goldilocks.goldilocks_inv, hi, bind_eq_result_bind, result_bind_ok]
    by_cases h : inv = 0#u64
    · simp [h]
    · simp only [h, ite_false, Result.ok.injEq, Option.some_ne_none, false_iff, not_or]
      exact ⟨fun ha => h (hz ha), id⟩
  · intro hn
    simp [goldilocks.goldilocks_inv, hi, hn]

end qsag_verified.proofs
