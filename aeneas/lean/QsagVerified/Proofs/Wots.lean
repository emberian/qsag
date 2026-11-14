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

set_option maxHeartbeats 200000

/-! ## WOTS base-16 arithmetic -/

@[expose]
def natPrefixSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => natPrefixSum f n + f n

@[expose]
def wotsChecksumNat (digits : Std.Array Std.U8 32#usize) : Nat :=
  natPrefixSum (fun k => 15 - (digits.val.getD k 0#u8).val % 16) 32

private theorem u8_low_nibble_val (a : Std.U8) : (a &&& 15#u8).val = a.val % 16 := by
  change (a.bv &&& (15#u8).bv).toNat = a.bv.toNat % 16
  rw [BitVec.toNat_and]
  exact and_mask_eq_mod _ 4

private theorem u16_add_val (a b : Std.U16) (h : a.val + b.val < 65536) :
    ∃ c, (a + b : Result Std.U16) = .ok c ∧ c.val = a.val + b.val := by
  refine ⟨⟨a.bv + b.bv⟩, ?_, ?_⟩
  · simp [hAdd_uscalar_eq, h]
  · change (a.bv + b.bv).toNat = _
    rw [BitVec.toNat_add]
    exact Nat.mod_eq_of_lt h

private theorem wots_csum_term_spec (d : Std.U8) :
    ∃ c, fips205.wots_csum_term d = .ok c ∧ c.val = 15 - d.val % 16 ∧ c.val ≤ 15 := by
  let nib := UScalar.cast .U16 (d &&& 15#u8)
  have hv : nib.val = d.val % 16 := by
    change ((d &&& 15#u8).bv.setWidth 16).toNat = _
    rw [BitVec.toNat_setWidth]
    change (d &&& 15#u8).val % 65536 = _
    rw [u8_low_nibble_val, Nat.mod_eq_of_lt (by exact Nat.lt_trans (Nat.mod_lt d.val (by decide : 0 < 16)) (by decide))]
  have hb : nib.val ≤ (15#u16).val := by
    change nib.val ≤ 15
    rw [hv]
    exact Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
  let c : Std.U16 := ⟨(15#u16).bv - nib.bv⟩
  refine ⟨c, ?_, ?_, ?_⟩
  · unfold fips205.wots_csum_term
    simp only [bind_eq_result_bind, lift_eq_ok, result_bind_ok]
    change (15#u16 - nib : Result Std.U16) = .ok c
    simp only [hSub_uscalar_eq, hb, ite_true]
    rfl
  · change ((15#u16).bv - nib.bv).toNat = _
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hb)]
    change 15 - nib.val = _
    rw [hv]
  · change ((15#u16).bv - nib.bv).toNat ≤ 15
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hb)]
    exact Nat.sub_le _ _

private theorem wots_csum_oct_spec (d0 d1 d2 d3 d4 d5 d6 d7 : Std.U8) :
    ∃ c, fips205.wots_csum_oct d0 d1 d2 d3 d4 d5 d6 d7 = .ok c ∧
      c.val = (15 - d0.val % 16) + (15 - d1.val % 16) + (15 - d2.val % 16) + (15 - d3.val % 16) + (15 - d4.val % 16) + (15 - d5.val % 16) + (15 - d6.val % 16) + (15 - d7.val % 16) ∧ c.val ≤ 120 := by
  obtain ⟨c0, h0, v0, b0⟩ := wots_csum_term_spec d0
  obtain ⟨c1, h1, v1, b1⟩ := wots_csum_term_spec d1
  obtain ⟨c2, h2, v2, b2⟩ := wots_csum_term_spec d2
  obtain ⟨c3, h3, v3, b3⟩ := wots_csum_term_spec d3
  obtain ⟨c4, h4, v4, b4⟩ := wots_csum_term_spec d4
  obtain ⟨c5, h5, v5, b5⟩ := wots_csum_term_spec d5
  obtain ⟨c6, h6, v6, b6⟩ := wots_csum_term_spec d6
  obtain ⟨c7, h7, v7, b7⟩ := wots_csum_term_spec d7
  obtain ⟨s01, hs01, vs01⟩ := u16_add_val c0 c1 (Nat.lt_of_le_of_lt (Nat.add_le_add b0 b1) (by decide))
  have bound_s01 : s01.val ≤ 30 := by rw [vs01]; exact Nat.add_le_add b0 b1
  obtain ⟨s23, hs23, vs23⟩ := u16_add_val c2 c3 (Nat.lt_of_le_of_lt (Nat.add_le_add b2 b3) (by decide))
  have bound_s23 : s23.val ≤ 30 := by rw [vs23]; exact Nat.add_le_add b2 b3
  obtain ⟨s03, hs03, vs03⟩ := u16_add_val s01 s23 (Nat.lt_of_le_of_lt (Nat.add_le_add bound_s01 bound_s23) (by decide))
  have bound_s03 : s03.val ≤ 60 := by rw [vs03]; exact Nat.add_le_add bound_s01 bound_s23
  obtain ⟨s45, hs45, vs45⟩ := u16_add_val c4 c5 (Nat.lt_of_le_of_lt (Nat.add_le_add b4 b5) (by decide))
  have bound_s45 : s45.val ≤ 30 := by rw [vs45]; exact Nat.add_le_add b4 b5
  obtain ⟨s67, hs67, vs67⟩ := u16_add_val c6 c7 (Nat.lt_of_le_of_lt (Nat.add_le_add b6 b7) (by decide))
  have bound_s67 : s67.val ≤ 30 := by rw [vs67]; exact Nat.add_le_add b6 b7
  obtain ⟨s47, hs47, vs47⟩ := u16_add_val s45 s67 (Nat.lt_of_le_of_lt (Nat.add_le_add bound_s45 bound_s67) (by decide))
  have bound_s47 : s47.val ≤ 60 := by rw [vs47]; exact Nat.add_le_add bound_s45 bound_s67
  obtain ⟨total, htotal, vtotal⟩ := u16_add_val s03 s47 (Nat.lt_of_le_of_lt (Nat.add_le_add bound_s03 bound_s47) (by decide))
  have bound_total : total.val ≤ 120 := by rw [vtotal]; exact Nat.add_le_add bound_s03 bound_s47
  refine ⟨total, ?_, ?_, ?_⟩
  · simp only [fips205.wots_csum_oct, h0, h1, h2, h3, h4, h5, h6, h7, hs01, hs23, hs03, hs45, hs67, hs47, htotal, bind_eq_result_bind, result_bind_ok]
  · simp only [vtotal, vs03, vs01, vs23, vs47, vs45, vs67, v0, v1, v2, v3, v4, v5, v6, v7, Nat.add_assoc]
  · exact bound_total

theorem wots_checksum_base16_spec (digits : Std.Array Std.U8 32#usize) :
    ∃ csum, fips205.wots_checksum_base16 digits = .ok csum ∧
      csum.val = wotsChecksumNat digits ∧ csum.val ≤ 480 := by
  obtain ⟨s0, h0, v0, b0⟩ := wots_csum_oct_spec (digits.val.getD 0 0#u8) (digits.val.getD 1 0#u8) (digits.val.getD 2 0#u8) (digits.val.getD 3 0#u8) (digits.val.getD 4 0#u8) (digits.val.getD 5 0#u8) (digits.val.getD 6 0#u8) (digits.val.getD 7 0#u8)
  obtain ⟨s1, h1, v1, b1⟩ := wots_csum_oct_spec (digits.val.getD 8 0#u8) (digits.val.getD 9 0#u8) (digits.val.getD 10 0#u8) (digits.val.getD 11 0#u8) (digits.val.getD 12 0#u8) (digits.val.getD 13 0#u8) (digits.val.getD 14 0#u8) (digits.val.getD 15 0#u8)
  obtain ⟨s2, h2, v2, b2⟩ := wots_csum_oct_spec (digits.val.getD 16 0#u8) (digits.val.getD 17 0#u8) (digits.val.getD 18 0#u8) (digits.val.getD 19 0#u8) (digits.val.getD 20 0#u8) (digits.val.getD 21 0#u8) (digits.val.getD 22 0#u8) (digits.val.getD 23 0#u8)
  obtain ⟨s3, h3, v3, b3⟩ := wots_csum_oct_spec (digits.val.getD 24 0#u8) (digits.val.getD 25 0#u8) (digits.val.getD 26 0#u8) (digits.val.getD 27 0#u8) (digits.val.getD 28 0#u8) (digits.val.getD 29 0#u8) (digits.val.getD 30 0#u8) (digits.val.getD 31 0#u8)
  obtain ⟨s01, hs01, vs01⟩ := u16_add_val s0 s1 (Nat.lt_of_le_of_lt (Nat.add_le_add b0 b1) (by decide))
  have bound_s01 : s01.val ≤ 240 := by rw [vs01]; exact Nat.add_le_add b0 b1
  obtain ⟨s23, hs23, vs23⟩ := u16_add_val s2 s3 (Nat.lt_of_le_of_lt (Nat.add_le_add b2 b3) (by decide))
  have bound_s23 : s23.val ≤ 240 := by rw [vs23]; exact Nat.add_le_add b2 b3
  obtain ⟨total, htotal, vtotal⟩ := u16_add_val s01 s23 (Nat.lt_of_le_of_lt (Nat.add_le_add bound_s01 bound_s23) (by decide))
  have bound_total : total.val ≤ 480 := by rw [vtotal]; exact Nat.add_le_add bound_s01 bound_s23
  refine ⟨total, ?_, ?_, bound_total⟩
  · unfold fips205.wots_checksum_base16
    have hi0 : Std.Array.index_usize digits 0#usize = .ok (digits.val.getD 0 0#u8) :=
      array_index_getD digits 0#usize 0#u8 (by decide)
    have hi1 : Std.Array.index_usize digits 1#usize = .ok (digits.val.getD 1 0#u8) :=
      array_index_getD digits 1#usize 0#u8 (by decide)
    have hi2 : Std.Array.index_usize digits 2#usize = .ok (digits.val.getD 2 0#u8) :=
      array_index_getD digits 2#usize 0#u8 (by decide)
    have hi3 : Std.Array.index_usize digits 3#usize = .ok (digits.val.getD 3 0#u8) :=
      array_index_getD digits 3#usize 0#u8 (by decide)
    have hi4 : Std.Array.index_usize digits 4#usize = .ok (digits.val.getD 4 0#u8) :=
      array_index_getD digits 4#usize 0#u8 (by decide)
    have hi5 : Std.Array.index_usize digits 5#usize = .ok (digits.val.getD 5 0#u8) :=
      array_index_getD digits 5#usize 0#u8 (by decide)
    have hi6 : Std.Array.index_usize digits 6#usize = .ok (digits.val.getD 6 0#u8) :=
      array_index_getD digits 6#usize 0#u8 (by decide)
    have hi7 : Std.Array.index_usize digits 7#usize = .ok (digits.val.getD 7 0#u8) :=
      array_index_getD digits 7#usize 0#u8 (by decide)
    have hi8 : Std.Array.index_usize digits 8#usize = .ok (digits.val.getD 8 0#u8) :=
      array_index_getD digits 8#usize 0#u8 (by decide)
    have hi9 : Std.Array.index_usize digits 9#usize = .ok (digits.val.getD 9 0#u8) :=
      array_index_getD digits 9#usize 0#u8 (by decide)
    have hi10 : Std.Array.index_usize digits 10#usize = .ok (digits.val.getD 10 0#u8) :=
      array_index_getD digits 10#usize 0#u8 (by decide)
    have hi11 : Std.Array.index_usize digits 11#usize = .ok (digits.val.getD 11 0#u8) :=
      array_index_getD digits 11#usize 0#u8 (by decide)
    have hi12 : Std.Array.index_usize digits 12#usize = .ok (digits.val.getD 12 0#u8) :=
      array_index_getD digits 12#usize 0#u8 (by decide)
    have hi13 : Std.Array.index_usize digits 13#usize = .ok (digits.val.getD 13 0#u8) :=
      array_index_getD digits 13#usize 0#u8 (by decide)
    have hi14 : Std.Array.index_usize digits 14#usize = .ok (digits.val.getD 14 0#u8) :=
      array_index_getD digits 14#usize 0#u8 (by decide)
    have hi15 : Std.Array.index_usize digits 15#usize = .ok (digits.val.getD 15 0#u8) :=
      array_index_getD digits 15#usize 0#u8 (by decide)
    have hi16 : Std.Array.index_usize digits 16#usize = .ok (digits.val.getD 16 0#u8) :=
      array_index_getD digits 16#usize 0#u8 (by decide)
    have hi17 : Std.Array.index_usize digits 17#usize = .ok (digits.val.getD 17 0#u8) :=
      array_index_getD digits 17#usize 0#u8 (by decide)
    have hi18 : Std.Array.index_usize digits 18#usize = .ok (digits.val.getD 18 0#u8) :=
      array_index_getD digits 18#usize 0#u8 (by decide)
    have hi19 : Std.Array.index_usize digits 19#usize = .ok (digits.val.getD 19 0#u8) :=
      array_index_getD digits 19#usize 0#u8 (by decide)
    have hi20 : Std.Array.index_usize digits 20#usize = .ok (digits.val.getD 20 0#u8) :=
      array_index_getD digits 20#usize 0#u8 (by decide)
    have hi21 : Std.Array.index_usize digits 21#usize = .ok (digits.val.getD 21 0#u8) :=
      array_index_getD digits 21#usize 0#u8 (by decide)
    have hi22 : Std.Array.index_usize digits 22#usize = .ok (digits.val.getD 22 0#u8) :=
      array_index_getD digits 22#usize 0#u8 (by decide)
    have hi23 : Std.Array.index_usize digits 23#usize = .ok (digits.val.getD 23 0#u8) :=
      array_index_getD digits 23#usize 0#u8 (by decide)
    have hi24 : Std.Array.index_usize digits 24#usize = .ok (digits.val.getD 24 0#u8) :=
      array_index_getD digits 24#usize 0#u8 (by decide)
    have hi25 : Std.Array.index_usize digits 25#usize = .ok (digits.val.getD 25 0#u8) :=
      array_index_getD digits 25#usize 0#u8 (by decide)
    have hi26 : Std.Array.index_usize digits 26#usize = .ok (digits.val.getD 26 0#u8) :=
      array_index_getD digits 26#usize 0#u8 (by decide)
    have hi27 : Std.Array.index_usize digits 27#usize = .ok (digits.val.getD 27 0#u8) :=
      array_index_getD digits 27#usize 0#u8 (by decide)
    have hi28 : Std.Array.index_usize digits 28#usize = .ok (digits.val.getD 28 0#u8) :=
      array_index_getD digits 28#usize 0#u8 (by decide)
    have hi29 : Std.Array.index_usize digits 29#usize = .ok (digits.val.getD 29 0#u8) :=
      array_index_getD digits 29#usize 0#u8 (by decide)
    have hi30 : Std.Array.index_usize digits 30#usize = .ok (digits.val.getD 30 0#u8) :=
      array_index_getD digits 30#usize 0#u8 (by decide)
    have hi31 : Std.Array.index_usize digits 31#usize = .ok (digits.val.getD 31 0#u8) :=
      array_index_getD digits 31#usize 0#u8 (by decide)
    simp only [hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11, hi12, hi13, hi14, hi15, hi16, hi17, hi18, hi19, hi20, hi21, hi22, hi23, hi24, hi25, hi26, hi27, hi28, hi29, hi30, hi31, h0, h1, h2, h3, hs01, hs23, htotal, bind_eq_result_bind, result_bind_ok]
  · simp only [wotsChecksumNat, natPrefixSum]
    simp only [vtotal, vs01, vs23, v0, v1, v2, v3, Nat.zero_add, Nat.add_assoc]

private theorem natPrefixSum_mono (f g : Nat → Nat) (n : Nat)
    (h : ∀ k < n, f k ≤ g k) : natPrefixSum f n ≤ natPrefixSum g n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have hn := h n (Nat.lt_succ_self n)
    have hp := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
    simp only [natPrefixSum]
    exact Nat.add_le_add hp hn

private theorem natPrefixSum_strict (f g : Nat → Nat) (n : Nat)
    (h : ∀ k < n, f k ≤ g k) (hj : ∃ j < n, f j < g j) :
    natPrefixSum f n < natPrefixSum g n := by
  induction n with
  | zero => obtain ⟨j, hj, _⟩ := hj; exact False.elim (Nat.not_lt_zero j hj)
  | succ n ih =>
    have hn := h n (Nat.lt_succ_self n)
    have hp := natPrefixSum_mono f g n (fun k hk => h k (Nat.lt_succ_of_lt hk))
    obtain ⟨j, hj, hs⟩ := hj
    simp only [natPrefixSum]
    by_cases he : j = n
    · subst j; exact Nat.add_lt_add_of_le_of_lt hp hs
    · have hprev := ih (fun k hk => h k (Nat.lt_succ_of_lt hk)) ⟨j, Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) he, hs⟩
      exact Nat.add_lt_add_of_lt_of_le hprev hn

theorem wots_checksum_strict_antitone (d1 d2 : Std.Array Std.U8 32#usize)
    (h1 : ∀ k < 32, (d1.val.getD k 0#u8).val < 16)
    (h2 : ∀ k < 32, (d2.val.getD k 0#u8).val < 16)
    (hle : ∀ k < 32, (d2.val.getD k 0#u8).val ≤ (d1.val.getD k 0#u8).val)
    (hlt : ∃ j < 32, (d2.val.getD j 0#u8).val < (d1.val.getD j 0#u8).val) :
    ∃ c1 c2, fips205.wots_checksum_base16 d1 = .ok c1 ∧
      fips205.wots_checksum_base16 d2 = .ok c2 ∧ c1.val < c2.val := by
  obtain ⟨c1, hc1, hv1, _⟩ := wots_checksum_base16_spec d1
  obtain ⟨c2, hc2, hv2, _⟩ := wots_checksum_base16_spec d2
  refine ⟨c1, c2, hc1, hc2, ?_⟩
  rw [hv1, hv2]
  apply natPrefixSum_strict
  · intro k hk
    rw [Nat.mod_eq_of_lt (h1 k hk), Nat.mod_eq_of_lt (h2 k hk)]
    exact Nat.sub_le_sub_left (hle k hk) 15
  · obtain ⟨j, hj, hs⟩ := hlt
    refine ⟨j, hj, ?_⟩
    rw [Nat.mod_eq_of_lt (h1 j hj), Nat.mod_eq_of_lt (h2 j hj)]
    exact Nat.sub_lt_sub_left (Nat.lt_of_lt_of_le hs (Nat.le_of_lt_succ (h1 j hj))) hs

@[expose]
def highNibble (d : Std.U8) : Std.U8 := ⟨d.bv >>> 4⟩

private theorem highNibble_val (d : Std.U8) : (highNibble d).val = d.val / 16 := by
  change (d.bv >>> 4).toNat = _
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem nibble_bounds (d : Std.U8) :
    (highNibble d).val < 16 ∧ (d &&& 15#u8).val < 16 := by
  rw [highNibble_val, u8_low_nibble_val]
  have hd : d.val < 256 := d.bv.isLt
  constructor
  · exact (Nat.div_lt_iff_lt_mul (by decide)).mpr hd
  · exact Nat.mod_lt _ (by decide)

@[expose]
def wotsBase16Digits (msg16 : Std.Array Std.U8 16#usize) : Std.Array Std.U8 32#usize :=
  Std.Array.make 32#usize [
    highNibble (msg16.val.getD 0 0#u8), msg16.val.getD 0 0#u8 &&& 15#u8,
    highNibble (msg16.val.getD 1 0#u8), msg16.val.getD 1 0#u8 &&& 15#u8,
    highNibble (msg16.val.getD 2 0#u8), msg16.val.getD 2 0#u8 &&& 15#u8,
    highNibble (msg16.val.getD 3 0#u8), msg16.val.getD 3 0#u8 &&& 15#u8,
    highNibble (msg16.val.getD 4 0#u8), msg16.val.getD 4 0#u8 &&& 15#u8,
    highNibble (msg16.val.getD 5 0#u8), msg16.val.getD 5 0#u8 &&& 15#u8,
    highNibble (msg16.val.getD 6 0#u8), msg16.val.getD 6 0#u8 &&& 15#u8,
    highNibble (msg16.val.getD 7 0#u8), msg16.val.getD 7 0#u8 &&& 15#u8,
    highNibble (msg16.val.getD 8 0#u8), msg16.val.getD 8 0#u8 &&& 15#u8,
    highNibble (msg16.val.getD 9 0#u8), msg16.val.getD 9 0#u8 &&& 15#u8,
    highNibble (msg16.val.getD 10 0#u8), msg16.val.getD 10 0#u8 &&& 15#u8,
    highNibble (msg16.val.getD 11 0#u8), msg16.val.getD 11 0#u8 &&& 15#u8,
    highNibble (msg16.val.getD 12 0#u8), msg16.val.getD 12 0#u8 &&& 15#u8,
    highNibble (msg16.val.getD 13 0#u8), msg16.val.getD 13 0#u8 &&& 15#u8,
    highNibble (msg16.val.getD 14 0#u8), msg16.val.getD 14 0#u8 &&& 15#u8,
    highNibble (msg16.val.getD 15 0#u8), msg16.val.getD 15 0#u8 &&& 15#u8]

private theorem u8_shift4 (d : Std.U8) : (d >>> 4#i32 : Result Std.U8) = .ok (highNibble d) := rfl

private theorem u16_shift4 (d : Std.U16) : (d >>> 4#i32 : Result Std.U16) = .ok ⟨d.bv >>> 4⟩ := rfl

private theorem u16_shift8 (d : Std.U16) : (d >>> 8#i32 : Result Std.U16) = .ok ⟨d.bv >>> 8⟩ := rfl


private theorem wots_extract_values (msg16 : Std.Array Std.U8 16#usize) (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Std.U8)
    (h0 : Std.Array.index_usize msg16 0#usize = .ok b0)
    (h1 : Std.Array.index_usize msg16 1#usize = .ok b1)
    (h2 : Std.Array.index_usize msg16 2#usize = .ok b2)
    (h3 : Std.Array.index_usize msg16 3#usize = .ok b3)
    (h4 : Std.Array.index_usize msg16 4#usize = .ok b4)
    (h5 : Std.Array.index_usize msg16 5#usize = .ok b5)
    (h6 : Std.Array.index_usize msg16 6#usize = .ok b6)
    (h7 : Std.Array.index_usize msg16 7#usize = .ok b7)
    (h8 : Std.Array.index_usize msg16 8#usize = .ok b8)
    (h9 : Std.Array.index_usize msg16 9#usize = .ok b9)
    (h10 : Std.Array.index_usize msg16 10#usize = .ok b10)
    (h11 : Std.Array.index_usize msg16 11#usize = .ok b11)
    (h12 : Std.Array.index_usize msg16 12#usize = .ok b12)
    (h13 : Std.Array.index_usize msg16 13#usize = .ok b13)
    (h14 : Std.Array.index_usize msg16 14#usize = .ok b14)
    (h15 : Std.Array.index_usize msg16 15#usize = .ok b15)
    : fips205.wots_extract_base16_digits msg16 = .ok (Std.Array.make 32#usize [highNibble b0, b0 &&& 15#u8, highNibble b1, b1 &&& 15#u8, highNibble b2, b2 &&& 15#u8, highNibble b3, b3 &&& 15#u8, highNibble b4, b4 &&& 15#u8, highNibble b5, b5 &&& 15#u8, highNibble b6, b6 &&& 15#u8, highNibble b7, b7 &&& 15#u8, highNibble b8, b8 &&& 15#u8, highNibble b9, b9 &&& 15#u8, highNibble b10, b10 &&& 15#u8, highNibble b11, b11 &&& 15#u8, highNibble b12, b12 &&& 15#u8, highNibble b13, b13 &&& 15#u8, highNibble b14, b14 &&& 15#u8, highNibble b15, b15 &&& 15#u8]) := by
  unfold fips205.wots_extract_base16_digits
  apply bind_ok_step h0
  apply bind_ok_step (u8_shift4 b0)
  apply bind_ok_step (show lift (b0 &&& 15#u8) = .ok (b0 &&& 15#u8) from rfl)
  apply bind_ok_step h1
  apply bind_ok_step (u8_shift4 b1)
  apply bind_ok_step (show lift (b1 &&& 15#u8) = .ok (b1 &&& 15#u8) from rfl)
  apply bind_ok_step h2
  apply bind_ok_step (u8_shift4 b2)
  apply bind_ok_step (show lift (b2 &&& 15#u8) = .ok (b2 &&& 15#u8) from rfl)
  apply bind_ok_step h3
  apply bind_ok_step (u8_shift4 b3)
  apply bind_ok_step (show lift (b3 &&& 15#u8) = .ok (b3 &&& 15#u8) from rfl)
  apply bind_ok_step h4
  apply bind_ok_step (u8_shift4 b4)
  apply bind_ok_step (show lift (b4 &&& 15#u8) = .ok (b4 &&& 15#u8) from rfl)
  apply bind_ok_step h5
  apply bind_ok_step (u8_shift4 b5)
  apply bind_ok_step (show lift (b5 &&& 15#u8) = .ok (b5 &&& 15#u8) from rfl)
  apply bind_ok_step h6
  apply bind_ok_step (u8_shift4 b6)
  apply bind_ok_step (show lift (b6 &&& 15#u8) = .ok (b6 &&& 15#u8) from rfl)
  apply bind_ok_step h7
  apply bind_ok_step (u8_shift4 b7)
  apply bind_ok_step (show lift (b7 &&& 15#u8) = .ok (b7 &&& 15#u8) from rfl)
  apply bind_ok_step h8
  apply bind_ok_step (u8_shift4 b8)
  apply bind_ok_step (show lift (b8 &&& 15#u8) = .ok (b8 &&& 15#u8) from rfl)
  apply bind_ok_step h9
  apply bind_ok_step (u8_shift4 b9)
  apply bind_ok_step (show lift (b9 &&& 15#u8) = .ok (b9 &&& 15#u8) from rfl)
  apply bind_ok_step h10
  apply bind_ok_step (u8_shift4 b10)
  apply bind_ok_step (show lift (b10 &&& 15#u8) = .ok (b10 &&& 15#u8) from rfl)
  apply bind_ok_step h11
  apply bind_ok_step (u8_shift4 b11)
  apply bind_ok_step (show lift (b11 &&& 15#u8) = .ok (b11 &&& 15#u8) from rfl)
  apply bind_ok_step h12
  apply bind_ok_step (u8_shift4 b12)
  apply bind_ok_step (show lift (b12 &&& 15#u8) = .ok (b12 &&& 15#u8) from rfl)
  apply bind_ok_step h13
  apply bind_ok_step (u8_shift4 b13)
  apply bind_ok_step (show lift (b13 &&& 15#u8) = .ok (b13 &&& 15#u8) from rfl)
  apply bind_ok_step h14
  apply bind_ok_step (u8_shift4 b14)
  apply bind_ok_step (show lift (b14 &&& 15#u8) = .ok (b14 &&& 15#u8) from rfl)
  apply bind_ok_step h15
  apply bind_ok_step (u8_shift4 b15)
  apply bind_ok_step (show lift (b15 &&& 15#u8) = .ok (b15 &&& 15#u8) from rfl)
  rfl

private theorem wots_extract_eq (msg16 : Std.Array Std.U8 16#usize) :
    fips205.wots_extract_base16_digits msg16 = .ok (wotsBase16Digits msg16) := by
  exact wots_extract_values msg16 (msg16.val.getD 0 0#u8) (msg16.val.getD 1 0#u8) (msg16.val.getD 2 0#u8) (msg16.val.getD 3 0#u8) (msg16.val.getD 4 0#u8) (msg16.val.getD 5 0#u8) (msg16.val.getD 6 0#u8) (msg16.val.getD 7 0#u8) (msg16.val.getD 8 0#u8) (msg16.val.getD 9 0#u8) (msg16.val.getD 10 0#u8) (msg16.val.getD 11 0#u8) (msg16.val.getD 12 0#u8) (msg16.val.getD 13 0#u8) (msg16.val.getD 14 0#u8) (msg16.val.getD 15 0#u8)
    (array_index_getD msg16 0#usize 0#u8 (by decide))
    (array_index_getD msg16 1#usize 0#u8 (by decide))
    (array_index_getD msg16 2#usize 0#u8 (by decide))
    (array_index_getD msg16 3#usize 0#u8 (by decide))
    (array_index_getD msg16 4#usize 0#u8 (by decide))
    (array_index_getD msg16 5#usize 0#u8 (by decide))
    (array_index_getD msg16 6#usize 0#u8 (by decide))
    (array_index_getD msg16 7#usize 0#u8 (by decide))
    (array_index_getD msg16 8#usize 0#u8 (by decide))
    (array_index_getD msg16 9#usize 0#u8 (by decide))
    (array_index_getD msg16 10#usize 0#u8 (by decide))
    (array_index_getD msg16 11#usize 0#u8 (by decide))
    (array_index_getD msg16 12#usize 0#u8 (by decide))
    (array_index_getD msg16 13#usize 0#u8 (by decide))
    (array_index_getD msg16 14#usize 0#u8 (by decide))
    (array_index_getD msg16 15#usize 0#u8 (by decide))

theorem wots_extract_base16_digits_spec (msg16 : Std.Array Std.U8 16#usize) :
    ∃ digits, fips205.wots_extract_base16_digits msg16 = .ok digits ∧
      (∀ k < 16, (digits.val.getD (2 * k) 0#u8).val = (msg16.val.getD k 0#u8).val / 16 ∧
        (digits.val.getD (2 * k + 1) 0#u8).val = (msg16.val.getD k 0#u8).val % 16) ∧
      (∀ k < 32, (digits.val.getD k 0#u8).val < 16) := by
  refine ⟨wotsBase16Digits msg16, wots_extract_eq msg16, ?_, ?_⟩
  · intro k hk
    match k, hk with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ =>
      change (highNibble _).val = _ ∧ (_ &&& 15#u8).val = _
      exact ⟨highNibble_val _, u8_low_nibble_val _⟩
    | n + 16, hk => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 16 n) hk)
  · intro k hk
    match k, hk with
    | 0, _ => exact (nibble_bounds (msg16.val.getD 0 0#u8)).1
    | 1, _ => exact (nibble_bounds (msg16.val.getD 0 0#u8)).2
    | 2, _ => exact (nibble_bounds (msg16.val.getD 1 0#u8)).1
    | 3, _ => exact (nibble_bounds (msg16.val.getD 1 0#u8)).2
    | 4, _ => exact (nibble_bounds (msg16.val.getD 2 0#u8)).1
    | 5, _ => exact (nibble_bounds (msg16.val.getD 2 0#u8)).2
    | 6, _ => exact (nibble_bounds (msg16.val.getD 3 0#u8)).1
    | 7, _ => exact (nibble_bounds (msg16.val.getD 3 0#u8)).2
    | 8, _ => exact (nibble_bounds (msg16.val.getD 4 0#u8)).1
    | 9, _ => exact (nibble_bounds (msg16.val.getD 4 0#u8)).2
    | 10, _ => exact (nibble_bounds (msg16.val.getD 5 0#u8)).1
    | 11, _ => exact (nibble_bounds (msg16.val.getD 5 0#u8)).2
    | 12, _ => exact (nibble_bounds (msg16.val.getD 6 0#u8)).1
    | 13, _ => exact (nibble_bounds (msg16.val.getD 6 0#u8)).2
    | 14, _ => exact (nibble_bounds (msg16.val.getD 7 0#u8)).1
    | 15, _ => exact (nibble_bounds (msg16.val.getD 7 0#u8)).2
    | 16, _ => exact (nibble_bounds (msg16.val.getD 8 0#u8)).1
    | 17, _ => exact (nibble_bounds (msg16.val.getD 8 0#u8)).2
    | 18, _ => exact (nibble_bounds (msg16.val.getD 9 0#u8)).1
    | 19, _ => exact (nibble_bounds (msg16.val.getD 9 0#u8)).2
    | 20, _ => exact (nibble_bounds (msg16.val.getD 10 0#u8)).1
    | 21, _ => exact (nibble_bounds (msg16.val.getD 10 0#u8)).2
    | 22, _ => exact (nibble_bounds (msg16.val.getD 11 0#u8)).1
    | 23, _ => exact (nibble_bounds (msg16.val.getD 11 0#u8)).2
    | 24, _ => exact (nibble_bounds (msg16.val.getD 12 0#u8)).1
    | 25, _ => exact (nibble_bounds (msg16.val.getD 12 0#u8)).2
    | 26, _ => exact (nibble_bounds (msg16.val.getD 13 0#u8)).1
    | 27, _ => exact (nibble_bounds (msg16.val.getD 13 0#u8)).2
    | 28, _ => exact (nibble_bounds (msg16.val.getD 14 0#u8)).1
    | 29, _ => exact (nibble_bounds (msg16.val.getD 14 0#u8)).2
    | 30, _ => exact (nibble_bounds (msg16.val.getD 15 0#u8)).1
    | 31, _ => exact (nibble_bounds (msg16.val.getD 15 0#u8)).2
    | n + 32, hk => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 32 n) hk)

private def checksumNibble (csum : Std.U16) (shift : Nat) : Std.U8 :=
  UScalar.cast .U8 ((⟨csum.bv >>> shift⟩ : Std.U16) &&& 15#u16)

private theorem checksumNibble_val (csum : Std.U16) (shift : Nat) :
    (checksumNibble csum shift).val = (csum.val / 2 ^ shift) % 16 := by
  change (((csum.bv >>> shift) &&& (15#u16).bv).setWidth 8).toNat = _
  rw [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ushiftRight]
  change (((csum.bv.toNat >>> shift) &&& (2 ^ 4 - 1)) % 256) = _
  rw [and_mask_eq_mod, Nat.shiftRight_eq_div_pow]
  exact Nat.mod_eq_of_lt (by exact Nat.lt_trans (Nat.mod_lt _ (by decide : 0 < 16)) (by decide))

private def checksumDigits (md : Std.Array Std.U8 32#usize) (csum : Std.U16) : Std.Array Std.U8 35#usize :=
  Std.Array.make 35#usize [
    md.val.getD 0 0#u8, md.val.getD 1 0#u8, md.val.getD 2 0#u8, md.val.getD 3 0#u8, md.val.getD 4 0#u8, md.val.getD 5 0#u8, md.val.getD 6 0#u8, md.val.getD 7 0#u8, md.val.getD 8 0#u8, md.val.getD 9 0#u8, md.val.getD 10 0#u8, md.val.getD 11 0#u8, md.val.getD 12 0#u8, md.val.getD 13 0#u8, md.val.getD 14 0#u8, md.val.getD 15 0#u8, md.val.getD 16 0#u8, md.val.getD 17 0#u8, md.val.getD 18 0#u8, md.val.getD 19 0#u8, md.val.getD 20 0#u8, md.val.getD 21 0#u8, md.val.getD 22 0#u8, md.val.getD 23 0#u8, md.val.getD 24 0#u8, md.val.getD 25 0#u8, md.val.getD 26 0#u8, md.val.getD 27 0#u8, md.val.getD 28 0#u8, md.val.getD 29 0#u8, md.val.getD 30 0#u8, md.val.getD 31 0#u8,
    checksumNibble csum 8, checksumNibble csum 4, checksumNibble csum 0]

private theorem fips205_checksum_values (msg16 : Std.Array Std.U8 16#usize)
    (md : Std.Array Std.U8 32#usize) (csum : Std.U16) (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : Std.U8)
    (hd : fips205.wots_extract_base16_digits msg16 = .ok md)
    (hc : fips205.wots_checksum_base16 md = .ok csum)
    (h0 : Std.Array.index_usize md 0#usize = .ok b0)
    (h1 : Std.Array.index_usize md 1#usize = .ok b1)
    (h2 : Std.Array.index_usize md 2#usize = .ok b2)
    (h3 : Std.Array.index_usize md 3#usize = .ok b3)
    (h4 : Std.Array.index_usize md 4#usize = .ok b4)
    (h5 : Std.Array.index_usize md 5#usize = .ok b5)
    (h6 : Std.Array.index_usize md 6#usize = .ok b6)
    (h7 : Std.Array.index_usize md 7#usize = .ok b7)
    (h8 : Std.Array.index_usize md 8#usize = .ok b8)
    (h9 : Std.Array.index_usize md 9#usize = .ok b9)
    (h10 : Std.Array.index_usize md 10#usize = .ok b10)
    (h11 : Std.Array.index_usize md 11#usize = .ok b11)
    (h12 : Std.Array.index_usize md 12#usize = .ok b12)
    (h13 : Std.Array.index_usize md 13#usize = .ok b13)
    (h14 : Std.Array.index_usize md 14#usize = .ok b14)
    (h15 : Std.Array.index_usize md 15#usize = .ok b15)
    (h16 : Std.Array.index_usize md 16#usize = .ok b16)
    (h17 : Std.Array.index_usize md 17#usize = .ok b17)
    (h18 : Std.Array.index_usize md 18#usize = .ok b18)
    (h19 : Std.Array.index_usize md 19#usize = .ok b19)
    (h20 : Std.Array.index_usize md 20#usize = .ok b20)
    (h21 : Std.Array.index_usize md 21#usize = .ok b21)
    (h22 : Std.Array.index_usize md 22#usize = .ok b22)
    (h23 : Std.Array.index_usize md 23#usize = .ok b23)
    (h24 : Std.Array.index_usize md 24#usize = .ok b24)
    (h25 : Std.Array.index_usize md 25#usize = .ok b25)
    (h26 : Std.Array.index_usize md 26#usize = .ok b26)
    (h27 : Std.Array.index_usize md 27#usize = .ok b27)
    (h28 : Std.Array.index_usize md 28#usize = .ok b28)
    (h29 : Std.Array.index_usize md 29#usize = .ok b29)
    (h30 : Std.Array.index_usize md 30#usize = .ok b30)
    (h31 : Std.Array.index_usize md 31#usize = .ok b31)
    : fips205.fips205_wots_checksum msg16 = .ok (Std.Array.make 35#usize [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31, checksumNibble csum 8, checksumNibble csum 4, checksumNibble csum 0]) := by
  unfold fips205.fips205_wots_checksum
  apply bind_ok_step hd
  apply bind_ok_step hc
  apply bind_ok_step (u16_shift8 csum)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (u16_shift4 csum)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step h0
  apply bind_ok_step h1
  apply bind_ok_step h2
  apply bind_ok_step h3
  apply bind_ok_step h4
  apply bind_ok_step h5
  apply bind_ok_step h6
  apply bind_ok_step h7
  apply bind_ok_step h8
  apply bind_ok_step h9
  apply bind_ok_step h10
  apply bind_ok_step h11
  apply bind_ok_step h12
  apply bind_ok_step h13
  apply bind_ok_step h14
  apply bind_ok_step h15
  apply bind_ok_step h16
  apply bind_ok_step h17
  apply bind_ok_step h18
  apply bind_ok_step h19
  apply bind_ok_step h20
  apply bind_ok_step h21
  apply bind_ok_step h22
  apply bind_ok_step h23
  apply bind_ok_step h24
  apply bind_ok_step h25
  apply bind_ok_step h26
  apply bind_ok_step h27
  apply bind_ok_step h28
  apply bind_ok_step h29
  apply bind_ok_step h30
  apply bind_ok_step h31
  rfl

private theorem fips205_checksum_eq (msg16 : Std.Array Std.U8 16#usize)
    (md : Std.Array Std.U8 32#usize) (csum : Std.U16)
    (hd : fips205.wots_extract_base16_digits msg16 = .ok md)
    (hc : fips205.wots_checksum_base16 md = .ok csum) :
    fips205.fips205_wots_checksum msg16 = .ok (checksumDigits md csum) := by
  exact fips205_checksum_values msg16 md csum (md.val.getD 0 0#u8) (md.val.getD 1 0#u8) (md.val.getD 2 0#u8) (md.val.getD 3 0#u8) (md.val.getD 4 0#u8) (md.val.getD 5 0#u8) (md.val.getD 6 0#u8) (md.val.getD 7 0#u8) (md.val.getD 8 0#u8) (md.val.getD 9 0#u8) (md.val.getD 10 0#u8) (md.val.getD 11 0#u8) (md.val.getD 12 0#u8) (md.val.getD 13 0#u8) (md.val.getD 14 0#u8) (md.val.getD 15 0#u8) (md.val.getD 16 0#u8) (md.val.getD 17 0#u8) (md.val.getD 18 0#u8) (md.val.getD 19 0#u8) (md.val.getD 20 0#u8) (md.val.getD 21 0#u8) (md.val.getD 22 0#u8) (md.val.getD 23 0#u8) (md.val.getD 24 0#u8) (md.val.getD 25 0#u8) (md.val.getD 26 0#u8) (md.val.getD 27 0#u8) (md.val.getD 28 0#u8) (md.val.getD 29 0#u8) (md.val.getD 30 0#u8) (md.val.getD 31 0#u8) hd hc
    (array_index_getD md 0#usize 0#u8 (by decide))
    (array_index_getD md 1#usize 0#u8 (by decide))
    (array_index_getD md 2#usize 0#u8 (by decide))
    (array_index_getD md 3#usize 0#u8 (by decide))
    (array_index_getD md 4#usize 0#u8 (by decide))
    (array_index_getD md 5#usize 0#u8 (by decide))
    (array_index_getD md 6#usize 0#u8 (by decide))
    (array_index_getD md 7#usize 0#u8 (by decide))
    (array_index_getD md 8#usize 0#u8 (by decide))
    (array_index_getD md 9#usize 0#u8 (by decide))
    (array_index_getD md 10#usize 0#u8 (by decide))
    (array_index_getD md 11#usize 0#u8 (by decide))
    (array_index_getD md 12#usize 0#u8 (by decide))
    (array_index_getD md 13#usize 0#u8 (by decide))
    (array_index_getD md 14#usize 0#u8 (by decide))
    (array_index_getD md 15#usize 0#u8 (by decide))
    (array_index_getD md 16#usize 0#u8 (by decide))
    (array_index_getD md 17#usize 0#u8 (by decide))
    (array_index_getD md 18#usize 0#u8 (by decide))
    (array_index_getD md 19#usize 0#u8 (by decide))
    (array_index_getD md 20#usize 0#u8 (by decide))
    (array_index_getD md 21#usize 0#u8 (by decide))
    (array_index_getD md 22#usize 0#u8 (by decide))
    (array_index_getD md 23#usize 0#u8 (by decide))
    (array_index_getD md 24#usize 0#u8 (by decide))
    (array_index_getD md 25#usize 0#u8 (by decide))
    (array_index_getD md 26#usize 0#u8 (by decide))
    (array_index_getD md 27#usize 0#u8 (by decide))
    (array_index_getD md 28#usize 0#u8 (by decide))
    (array_index_getD md 29#usize 0#u8 (by decide))
    (array_index_getD md 30#usize 0#u8 (by decide))
    (array_index_getD md 31#usize 0#u8 (by decide))

theorem fips205_wots_checksum_spec (msg16 : Std.Array Std.U8 16#usize) :
    ∃ digits csum out,
      fips205.wots_extract_base16_digits msg16 = .ok digits ∧
      fips205.wots_checksum_base16 digits = .ok csum ∧
      fips205.fips205_wots_checksum msg16 = .ok out ∧
      csum.val = wotsChecksumNat digits ∧ csum.val ≤ 480 ∧
      (∀ k < 32, out.val.getD k 0#u8 = digits.val.getD k 0#u8) ∧
      (∀ k < 35, (out.val.getD k 0#u8).val < 16) ∧
      csum.val = 256 * (out.val.getD 32 0#u8).val +
        16 * (out.val.getD 33 0#u8).val + (out.val.getD 34 0#u8).val := by
  obtain ⟨digits, hd, _, hbound⟩ := wots_extract_base16_digits_spec msg16
  obtain ⟨csum, hc, hv, hb⟩ := wots_checksum_base16_spec digits
  have hprefix (k : Nat) (hk : k < 32) :
      (checksumDigits digits csum).val.getD k 0#u8 = digits.val.getD k 0#u8 := by
    match k, hk with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ | 25, _ | 26, _ | 27, _ | 28, _ | 29, _ | 30, _ | 31, _ => rfl
    | n + 32, hk => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 32 n) hk)
  refine ⟨digits, csum, checksumDigits digits csum, hd, hc,
    fips205_checksum_eq msg16 digits csum hd hc, hv, hb, hprefix, ?_, ?_⟩
  · intro k hk
    by_cases hlt : k < 32
    · rw [hprefix k hlt]; exact hbound k hlt
    · have hn : k = 32 ∨ k = 33 ∨ k = 34 := by
        have h32 : 32 ≤ k := Nat.le_of_not_gt hlt
        rcases Nat.eq_or_lt_of_le h32 with he | he
        · exact Or.inl he.symm
        rcases Nat.eq_or_lt_of_le he with he | he
        · exact Or.inr (Or.inl he.symm)
        exact Or.inr (Or.inr (Nat.le_antisymm (Nat.le_of_lt_succ hk) he))
      rcases hn with rfl | rfl | rfl
      all_goals change (checksumNibble csum _).val < 16
      all_goals rw [checksumNibble_val]; exact Nat.mod_lt _ (by decide)
  · change csum.val = 256 * (checksumNibble csum 8).val +
        16 * (checksumNibble csum 4).val + (checksumNibble csum 0).val
    rw [checksumNibble_val, checksumNibble_val, checksumNibble_val]
    simp only [Nat.reducePow, Nat.div_one]
    have hdiv : csum.val / 256 < 16 :=
      (Nat.div_lt_iff_lt_mul (by decide)).mpr (Nat.lt_of_le_of_lt hb (by decide))
    rw [Nat.mod_eq_of_lt hdiv]
    have he := Nat.mod_add_div csum.val 16
    have hq := Nat.mod_add_div (csum.val / 16) 16
    rw [← hq, Nat.mul_add, ← Nat.mul_assoc, Nat.div_div_eq_div_mul] at he
    simp only [Nat.reduceMul] at he
    exact he.symm.trans (by ac_rfl)


end qsag_verified.proofs
