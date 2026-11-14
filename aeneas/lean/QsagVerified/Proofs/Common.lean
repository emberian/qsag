module

public import Aeneas
public import QsagVerified.Types
public import QsagVerified.Funs

public section

namespace qsag_verified.proofs

open Aeneas Aeneas.Std Result ControlFlow Error
open qsag_verified

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

attribute [-simp] BitVec.getLsbD_eq_getElem
attribute [local simp] UScalar.val UScalarTy.numBits

private theorem mask_testBit (n i : Nat) :
    Nat.testBit (2 ^ n - 1) i = decide (i < n) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    have he : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 := by
      have hs : (2 ^ (n + 1) - 1) + 1 = (2 * (2 ^ n - 1) + 1) + 1 := by
        rw [Nat.sub_add_cancel (Nat.two_pow_pos _)]
        have hp := Nat.sub_add_cancel (Nat.two_pow_pos n)
        calc
          2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
          _ = 2 * ((2 ^ n - 1) + 1) := by rw [hp]
          _ = _ := by simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
      exact Nat.add_right_cancel hs
    cases i with
    | zero => simp [he, Nat.testBit_zero, Nat.add_mod]
    | succ i =>
      rw [he, Nat.testBit_succ]
      have hd : (2 * (2 ^ n - 1) + 1) / 2 = 2 ^ n - 1 := by
        rw [Nat.add_comm, Nat.add_mul_div_left 1 _ (by decide)]
        exact Nat.zero_add _
      rw [hd, ih]
      rfl

theorem and_mask_eq_mod (x n : Nat) : x &&& (2 ^ n - 1) = x % 2 ^ n := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_mod_two_pow, mask_testBit]
  exact Bool.and_comm _ _

theorem sub_lt_iff_lt_add_of_le {a b c : Nat} (hb : b ≤ a) :
    a - b < c ↔ a < c + b := by
  constructor
  · intro h
    have hh := Nat.add_lt_add_right h b
    simpa only [Nat.sub_add_cancel hb] using hh
  · intro h
    exact Nat.lt_of_add_lt_add_right (show (a - b) + b < c + b from
      by simpa only [Nat.sub_add_cancel hb] using h)

theorem u64_cast_u128_val (x : Std.U64) :
    (UScalar.cast .U128 x).val = x.val := by
  have hx : x.val < 2 ^ 64 := x.bv.isLt
  have hx128 : x.val < 2 ^ 128 := Nat.lt_of_lt_of_le hx (by decide)
  change (x.bv.setWidth 128).toNat = x.bv.toNat
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx128]

theorem u128_cast_u64_val_of_lt (x : Std.U128) (h : x.val < 2 ^ 64) :
    (UScalar.cast .U64 x).val = x.val := by
  change (x.bv.setWidth 64).toNat = x.bv.toNat
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt h]

theorem u128_and_mask64_val (x : Std.U128) :
    (x &&& 18446744073709551615#u128).val = x.val % (2 ^ 64) := by
  change (x.bv &&& (18446744073709551615#u128).bv).toNat = x.bv.toNat % (2 ^ 64)
  rw [BitVec.toNat_and]
  have hm : (18446744073709551615#u128).bv.toNat = 2 ^ 64 - 1 := by rfl
  rw [hm, and_mask_eq_mod]

theorem u128_and_one_val (x : Std.U128) :
    (x &&& 1#u128).val = x.val % 2 := by
  change (x.bv &&& (1#u128).bv).toNat = x.bv.toNat % 2
  rw [BitVec.toNat_and]
  have hm : (1#u128).bv.toNat = 2 ^ 1 - 1 := by rfl
  rw [hm, and_mask_eq_mod]

theorem u64_and_mask32_val (x : Std.U64) :
    (x &&& 4294967295#u64).val = x.val % (2 ^ 32) := by
  change (x.bv &&& (4294967295#u64).bv).toNat = x.bv.toNat % (2 ^ 32)
  rw [BitVec.toNat_and]
  have hm : (4294967295#u64).bv.toNat = 2 ^ 32 - 1 := by rfl
  rw [hm, and_mask_eq_mod]

theorem u128_shr64_eq (x : Std.U128) :
    (x >>> 64#i32 : Result Std.U128) = .ok ⟨x.bv >>> 64⟩ := rfl

theorem u128_shr64_val (x : Std.U128) :
    (⟨x.bv >>> 64⟩ : Std.U128).val = x.val / (2 ^ 64) := by
  change (x.bv >>> 64).toNat = x.bv.toNat / (2 ^ 64)
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem u64_shr32_eq (x : Std.U64) :
    (x >>> 32#i32 : Result Std.U64) = .ok ⟨x.bv >>> 32⟩ := rfl

theorem u64_shr32_val (x : Std.U64) :
    (⟨x.bv >>> 32⟩ : Std.U64).val = x.val / (2 ^ 32) := by
  change (x.bv >>> 32).toNat = x.bv.toNat / (2 ^ 32)
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem u64_shl32_eq (x : Std.U64) :
    (x <<< 32#i32 : Result Std.U64) = .ok ⟨x.bv <<< 32⟩ := rfl

theorem u64_shl32_val_of_lt (x : Std.U64) (hx : x.val < 2 ^ 32) :
    (⟨x.bv <<< 32⟩ : Std.U64).val = x.val * (2 ^ 32) := by
  change (x.bv <<< 32).toNat = x.bv.toNat * (2 ^ 32)
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  simp only [UScalarTy.numBits]
  apply Nat.mod_eq_of_lt
  have hx' : x.bv.toNat < 2 ^ 32 := hx
  exact Nat.mul_lt_mul_of_pos_right hx' (by decide)

theorem u128_add_ok {a b : Std.U128} (h : a.val + b.val < 2 ^ 128) :
    (a + b : Result Std.U128) = .ok ⟨a.bv + b.bv⟩ ∧
      (⟨a.bv + b.bv⟩ : Std.U128).val = a.val + b.val := by
  have h1 : (a + b : Result Std.U128) = .ok ⟨a.bv + b.bv⟩ := by
    simp [hAdd_uscalar_eq, h]
  refine ⟨h1, ?_⟩
  change (a.bv + b.bv).toNat = a.bv.toNat + b.bv.toNat
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

theorem u128_sub_ok {a b : Std.U128} (h : b.val ≤ a.val) :
    (a - b : Result Std.U128) = .ok ⟨a.bv - b.bv⟩ ∧
      (⟨a.bv - b.bv⟩ : Std.U128).val = a.val - b.val := by
  have h1 : (a - b : Result Std.U128) = .ok ⟨a.bv - b.bv⟩ := by
    simp [hSub_uscalar_eq, h]
  refine ⟨h1, ?_⟩
  change (a.bv - b.bv).toNat = a.bv.toNat - b.bv.toNat
  have ha : a.bv.toNat < 2 ^ 128 := a.bv.isLt
  exact BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)

theorem u128_mul_ok {a b : Std.U128} (h : a.val * b.val < 2 ^ 128) :
    (a * b : Result Std.U128) = .ok ⟨a.bv * b.bv⟩ ∧
      (⟨a.bv * b.bv⟩ : Std.U128).val = a.val * b.val := by
  have h1 : (a * b : Result Std.U128) = .ok ⟨a.bv * b.bv⟩ := by
    simp [hMul_uscalar_eq, h]
  refine ⟨h1, ?_⟩
  change (a.bv * b.bv).toNat = a.bv.toNat * b.bv.toNat
  rw [BitVec.toNat_mul, Nat.mod_eq_of_lt h]

theorem u64_sub_ok {a b : Std.U64} (h : b.val ≤ a.val) :
    (a - b : Result Std.U64) = .ok ⟨a.bv - b.bv⟩ ∧
      (⟨a.bv - b.bv⟩ : Std.U64).val = a.val - b.val := by
  have h1 : (a - b : Result Std.U64) = .ok ⟨a.bv - b.bv⟩ := by
    simp [hSub_uscalar_eq, h]
  refine ⟨h1, ?_⟩
  change (a.bv - b.bv).toNat = a.bv.toNat - b.bv.toNat
  exact BitVec.toNat_sub_of_le (BitVec.le_def.mpr h)

theorem result_bind_total {α β : Type} (r : Result α) (f : α → Result β)
    (hr : ∃ x, r = .ok x) (hf : ∀ x, ∃ y, f x = .ok y) :
    ∃ y, (r >>= f) = .ok y := by
  obtain ⟨x, hx⟩ := hr
  obtain ⟨y, hy⟩ := hf x
  exact ⟨y, by simp [hx, hy]⟩


theorem u8_xor_comm (a b : Std.U8) : a ^^^ b = b ^^^ a :=
  UScalar.ext (BitVec.xor_comm a.bv b.bv)

theorem u8_xor_assoc (a b c : Std.U8) : (a ^^^ b) ^^^ c = a ^^^ (b ^^^ c) :=
  UScalar.ext (BitVec.xor_assoc a.bv b.bv c.bv)

theorem u8_xor_self (a : Std.U8) : a ^^^ a = 0#u8 :=
  UScalar.ext BitVec.xor_self

theorem u8_xor_zero (a : Std.U8) : a ^^^ 0#u8 = a :=
  UScalar.ext BitVec.xor_zero

theorem u8_zero_xor (a : Std.U8) : 0#u8 ^^^ a = a :=
  UScalar.ext BitVec.zero_xor

theorem array_index_total {α : Type} {n : Std.Usize}
    (a : Array α n) (i : Std.Usize) (hi : i.val < n.val) :
    ∃ x, Std.Array.index_usize a i = .ok x := by
  have h : i.val < a.val.length := by rw [a.property]; exact hi
  exact ⟨a.val[i.val]'h, dite_eq_left_of_eq_true (eq_true h)⟩

theorem array_update_total {α : Type} {n : Std.Usize}
    (a : Array α n) (i : Std.Usize) (v : α) (hi : i.val < n.val) :
    ∃ b, Std.Array.update a i v = .ok b := by
  have h : i.val < a.val.length := by rw [a.property]; exact hi
  exact ⟨_, dite_eq_left_of_eq_true (eq_true h)⟩

/-! ## Fixed-size byte equality -/

private theorem u8_or_zero_iff (a b : Std.U8) :
    a ||| b = 0#u8 ↔ a = 0#u8 ∧ b = 0#u8 := by
  constructor
  · intro h
    obtain ⟨ha, hb⟩ := BitVec.or_eq_zero_iff.mp (congrArg UScalar.bv h)
    exact ⟨UScalar.ext ha, UScalar.ext hb⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem u8_xor_zero_iff (a b : Std.U8) : a ^^^ b = 0#u8 ↔ a = b := by
  constructor
  · intro h
    exact UScalar.ext (BitVec.xor_eq_zero_iff.mp (congrArg UScalar.bv h))
  · rintro rfl; exact u8_xor_self _

private def byteDifference (a b : Array Std.U8 32#usize) (i : Nat) : Std.U8 :=
  a.val.getD i 0#u8 ^^^ b.val.getD i 0#u8

private def diffBytes8 (a b : Array Std.U8 32#usize) (i : Nat) : Std.U8 :=
  (((byteDifference a b i ||| byteDifference a b (i + 1)) |||
    (byteDifference a b (i + 2) ||| byteDifference a b (i + 3))) |||
    (byteDifference a b (i + 4) ||| byteDifference a b (i + 5))) |||
    (byteDifference a b (i + 6) ||| byteDifference a b (i + 7))

theorem array_index_getD {α : Type} {n : Std.Usize}
    (a : Array α n) (i : Std.Usize) (d : α) (h : i.val < n.val) :
    Std.Array.index_usize a i = .ok (a.val.getD i.val d) := by
  have hi : i.val < a.val.length := by rw [a.property]; exact h
  simp only [Std.Array.index_usize, dite_eq_left_of_eq_true (eq_true hi), List.getElem_eq_getD d]

private theorem diff_bytes8_spec (a b : Array Std.U8 32#usize) (base : Std.Usize)
    (hbase : base.val + 7 < 32) :
    tower.diff_bytes8 a b base = .ok (diffBytes8 a b base.val) := by
  have hsmall (k : Nat) (hk : k ≤ 7) : base.val + k < 32 :=
    Nat.lt_of_le_of_lt (Nat.add_le_add_left hk _) hbase
  have hbase0 : base.val < 32 := hsmall 0 (by decide)
  let j1 : Std.Usize := ⟨base.bv + (1#usize).bv⟩
  have hb1 : base.val + 1 < 2 ^ 64 := Nat.lt_of_lt_of_le (hsmall 1 (by decide)) (by decide)
  have hs1 : (base + 1#usize : Result Std.Usize) = .ok j1 := by
    simp [hAdd_uscalar_eq, hb1, j1]
  have hv1 : j1.val = base.val + 1 := by
    change (base.bv + (1#usize).bv).toNat = base.val + 1
    rw [BitVec.toNat_add]
    change (_ + _) % (2 ^ 64) = _
    exact Nat.mod_eq_of_lt hb1
  let j2 : Std.Usize := ⟨base.bv + (2#usize).bv⟩
  have hb2 : base.val + 2 < 2 ^ 64 := Nat.lt_of_lt_of_le (hsmall 2 (by decide)) (by decide)
  have hs2 : (base + 2#usize : Result Std.Usize) = .ok j2 := by
    simp [hAdd_uscalar_eq, hb2, j2]
  have hv2 : j2.val = base.val + 2 := by
    change (base.bv + (2#usize).bv).toNat = base.val + 2
    rw [BitVec.toNat_add]
    change (_ + _) % (2 ^ 64) = _
    exact Nat.mod_eq_of_lt hb2
  let j3 : Std.Usize := ⟨base.bv + (3#usize).bv⟩
  have hb3 : base.val + 3 < 2 ^ 64 := Nat.lt_of_lt_of_le (hsmall 3 (by decide)) (by decide)
  have hs3 : (base + 3#usize : Result Std.Usize) = .ok j3 := by
    simp [hAdd_uscalar_eq, hb3, j3]
  have hv3 : j3.val = base.val + 3 := by
    change (base.bv + (3#usize).bv).toNat = base.val + 3
    rw [BitVec.toNat_add]
    change (_ + _) % (2 ^ 64) = _
    exact Nat.mod_eq_of_lt hb3
  let j4 : Std.Usize := ⟨base.bv + (4#usize).bv⟩
  have hb4 : base.val + 4 < 2 ^ 64 := Nat.lt_of_lt_of_le (hsmall 4 (by decide)) (by decide)
  have hs4 : (base + 4#usize : Result Std.Usize) = .ok j4 := by
    simp [hAdd_uscalar_eq, hb4, j4]
  have hv4 : j4.val = base.val + 4 := by
    change (base.bv + (4#usize).bv).toNat = base.val + 4
    rw [BitVec.toNat_add]
    change (_ + _) % (2 ^ 64) = _
    exact Nat.mod_eq_of_lt hb4
  let j5 : Std.Usize := ⟨base.bv + (5#usize).bv⟩
  have hb5 : base.val + 5 < 2 ^ 64 := Nat.lt_of_lt_of_le (hsmall 5 (by decide)) (by decide)
  have hs5 : (base + 5#usize : Result Std.Usize) = .ok j5 := by
    simp [hAdd_uscalar_eq, hb5, j5]
  have hv5 : j5.val = base.val + 5 := by
    change (base.bv + (5#usize).bv).toNat = base.val + 5
    rw [BitVec.toNat_add]
    change (_ + _) % (2 ^ 64) = _
    exact Nat.mod_eq_of_lt hb5
  let j6 : Std.Usize := ⟨base.bv + (6#usize).bv⟩
  have hb6 : base.val + 6 < 2 ^ 64 := Nat.lt_of_lt_of_le (hsmall 6 (by decide)) (by decide)
  have hs6 : (base + 6#usize : Result Std.Usize) = .ok j6 := by
    simp [hAdd_uscalar_eq, hb6, j6]
  have hv6 : j6.val = base.val + 6 := by
    change (base.bv + (6#usize).bv).toNat = base.val + 6
    rw [BitVec.toNat_add]
    change (_ + _) % (2 ^ 64) = _
    exact Nat.mod_eq_of_lt hb6
  let j7 : Std.Usize := ⟨base.bv + (7#usize).bv⟩
  have hb7 : base.val + 7 < 2 ^ 64 := Nat.lt_of_lt_of_le (hsmall 7 (by decide)) (by decide)
  have hs7 : (base + 7#usize : Result Std.Usize) = .ok j7 := by
    simp [hAdd_uscalar_eq, hb7, j7]
  have hv7 : j7.val = base.val + 7 := by
    change (base.bv + (7#usize).bv).toNat = base.val + 7
    rw [BitVec.toNat_add]
    change (_ + _) % (2 ^ 64) = _
    exact Nat.mod_eq_of_lt hb7
  have hj1 : j1.val < 32 := by rw [hv1]; exact hsmall 1 (by decide)
  have hj2 : j2.val < 32 := by rw [hv2]; exact hsmall 2 (by decide)
  have hj3 : j3.val < 32 := by rw [hv3]; exact hsmall 3 (by decide)
  have hj4 : j4.val < 32 := by rw [hv4]; exact hsmall 4 (by decide)
  have hj5 : j5.val < 32 := by rw [hv5]; exact hsmall 5 (by decide)
  have hj6 : j6.val < 32 := by rw [hv6]; exact hsmall 6 (by decide)
  have hj7 : j7.val < 32 := by rw [hv7]; exact hsmall 7 (by decide)
  have index (xs : Array Std.U8 32#usize) (i : Std.Usize) (h : i.val < 32) :
      Std.Array.index_usize xs i = .ok (xs.val.getD i.val 0#u8) :=
    array_index_getD xs i 0#u8 h
  simp (disch := assumption) only [tower.diff_bytes8, diffBytes8, byteDifference,
    hs1, hv1, hs2, hv2, hs3, hv3, hs4, hv4, hs5, hv5, hs6, hv6, hs7, hv7,
    index, bind_eq_result_bind, result_bind_ok, lift_eq_ok]

theorem ct_eq_bytes32_spec (a b : Array Std.U8 32#usize) :
    tower.ct_eq_bytes32 a b = .ok (decide (a = b)) := by
  rw [tower.ct_eq_bytes32, diff_bytes8_spec a b 0#usize (by decide)]
  simp only [bind_eq_result_bind, result_bind_ok]
  rw [diff_bytes8_spec a b 8#usize (by decide)]
  simp only [result_bind_ok, lift_eq_ok]
  rw [diff_bytes8_spec a b 16#usize (by decide)]
  simp only [result_bind_ok]
  rw [diff_bytes8_spec a b 24#usize (by decide)]
  simp only [result_bind_ok]
  apply congrArg Result.ok
  apply decide_eq_decide.mpr
  dsimp only [diffBytes8, byteDifference]
  repeat rw [u8_or_zero_iff]
  repeat rw [u8_xor_zero_iff]
  constructor
  · intro h
    apply Std.Array.ext
    apply List.ext_getElem (by rw [a.property, b.property])
    intro i ha hb
    rw [List.getElem_eq_getD 0#u8, List.getElem_eq_getD 0#u8]
    have hi : i < 32 := by rw [a.property] at ha; exact ha
    rcases h with ⟨⟨⟨⟨⟨⟨h0, h1⟩, ⟨h2, h3⟩⟩, ⟨h4, h5⟩⟩, ⟨h6, h7⟩⟩, ⟨⟨⟨⟨h8, h9⟩, ⟨h10, h11⟩⟩, ⟨h12, h13⟩⟩, ⟨h14, h15⟩⟩⟩, ⟨⟨⟨⟨⟨h16, h17⟩, ⟨h18, h19⟩⟩, ⟨h20, h21⟩⟩, ⟨h22, h23⟩⟩, ⟨⟨⟨⟨h24, h25⟩, ⟨h26, h27⟩⟩, ⟨h28, h29⟩⟩, ⟨h30, h31⟩⟩⟩⟩
    match i, hi with
    | 0, _ => exact h0
    | 1, _ => exact h1
    | 2, _ => exact h2
    | 3, _ => exact h3
    | 4, _ => exact h4
    | 5, _ => exact h5
    | 6, _ => exact h6
    | 7, _ => exact h7
    | 8, _ => exact h8
    | 9, _ => exact h9
    | 10, _ => exact h10
    | 11, _ => exact h11
    | 12, _ => exact h12
    | 13, _ => exact h13
    | 14, _ => exact h14
    | 15, _ => exact h15
    | 16, _ => exact h16
    | 17, _ => exact h17
    | 18, _ => exact h18
    | 19, _ => exact h19
    | 20, _ => exact h20
    | 21, _ => exact h21
    | 22, _ => exact h22
    | 23, _ => exact h23
    | 24, _ => exact h24
    | 25, _ => exact h25
    | 26, _ => exact h26
    | 27, _ => exact h27
    | 28, _ => exact h28
    | 29, _ => exact h29
    | 30, _ => exact h30
    | 31, _ => exact h31
    | i + 32, hi => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 32 i) hi)
  · rintro rfl
    simp []

theorem checked_add_val {ty : UScalarTy} (a b : UScalar ty)
    (h : a.val + b.val < 2 ^ ty.numBits) :
    ∃ c, (a + b : Result (UScalar ty)) = .ok c ∧ c.val = a.val + b.val := by
  refine ⟨⟨a.bv + b.bv⟩, ?_, ?_⟩
  · simp only [hAdd_uscalar_eq, h, ite_true]
  · exact (BitVec.toNat_add _ _).trans (Nat.mod_eq_of_lt h)

theorem checked_mul_val {ty : UScalarTy} (a b : UScalar ty)
    (h : a.val * b.val < 2 ^ ty.numBits) :
    ∃ c, (a * b : Result (UScalar ty)) = .ok c ∧ c.val = a.val * b.val := by
  refine ⟨⟨a.bv * b.bv⟩, ?_, ?_⟩
  · simp only [hMul_uscalar_eq, h, ite_true]
  · exact (BitVec.toNat_mul _ _).trans (Nat.mod_eq_of_lt h)

theorem slice_index_total {α : Type} (a : Slice α) (i : Std.Usize)
    (h : i.val < a.val.length) : ∃ v, Slice.index_usize a i = .ok v :=
  ⟨_, dite_eq_left_of_eq_true (eq_true h)⟩

theorem slice_update_total (a : Slice Std.U8) (i : Std.Usize) (v : Std.U8)
    (h : i.val < a.val.length) :
    ∃ b, Slice.update a i v = .ok b ∧ b.val.length = a.val.length := by
  unfold Slice.update
  rw [dite_eq_left h]
  exact ⟨_, rfl, List.length_set⟩

theorem loopFuel_total_rank {α β : Type} (body : α → Result (ControlFlow α β))
    (P : Nat → α → Prop) (Q : β → Prop)
    (hzero : ∀ x, P 0 x → ∃ y, body x = .ok (.done y) ∧ Q y)
    (hstep : ∀ n x, P (n + 1) x → ∃ x', body x = .ok (.cont x') ∧ P n x')
    (n : Nat) (x : α) (hx : P n x) :
    ∃ y, loopFuel (n + 1) body x = .ok y ∧ Q y := by
  induction n generalizing x with
  | zero =>
    obtain ⟨y, hy, hq⟩ := hzero x hx
    exact ⟨y, by rw [loopFuel_succ, hy, result_bind_ok], hq⟩
  | succ n ih =>
    obtain ⟨x', hbody, hp⟩ := hstep n x hx
    obtain ⟨y, hy, hq⟩ := ih x' hp
    exact ⟨y, by rw [loopFuel_succ, hbody, result_bind_ok]; exact hy, hq⟩


end qsag_verified.proofs
