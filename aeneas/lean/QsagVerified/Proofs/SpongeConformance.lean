module
public import QsagVerified.Proofs.RealSpecKeccakWeld

public section
namespace qsag_verified.proofs
open Aeneas Aeneas.Std Result ControlFlow qsag_verified
set_option maxRecDepth 4096

/-- Little-endian byte selection from the 17 rate lanes. -/
@[expose] def spongeRateByte (a : Array Std.U64 25#usize) (offset : Nat) : Std.U8 :=
  UScalar.cast .U8 ((⟨(a.val.getD (offset / 8) 0#u64).bv >>> (8 * (offset % 8))⟩ : Std.U64) &&& 255#u64)

/-- Every non-boundary squeeze step writes the specified byte, preserving all
other buffer bytes and sponge fields, and advances both offsets exactly once. -/
theorem sponge_squeeze_byte (s : keccak.Shake256Sponge) (dst : Slice Std.U8)
    (i : Std.Usize) (hi : i.val < dst.val.length) (ho : s.squeeze_offset.val < 136) :
    ∃ dst' i' off',
      keccak.Shake256Sponge.squeeze_loop.body s dst i =
        .ok (.cont ({s with squeeze_offset := off'}, dst', i')) ∧
      dst'.val = dst.val.set i.val (spongeRateByte s.state s.squeeze_offset.val) ∧
      i'.val = i.val + 1 ∧ off'.val = s.squeeze_offset.val + 1 := by
  have hlt : i < Slice.len dst := by change i.val < (Slice.len dst).val; rw [Slice.len_val]; exact hi
  have hno : ¬ s.squeeze_offset >= keccak.SHAKE256_RATE_BYTES := by
    unfold keccak.SHAKE256_RATE_BYTES; change ¬ 136 ≤ s.squeeze_offset.val
    exact Nat.not_le_of_gt ho
  let lane : Std.Usize := ⟨s.squeeze_offset.bv / (8#usize).bv⟩
  let rem : Std.Usize := ⟨s.squeeze_offset.bv % (8#usize).bv⟩
  have hdiv : (s.squeeze_offset / 8#usize : Result Std.Usize) = .ok lane := rfl
  have hmod : (s.squeeze_offset % 8#usize : Result Std.Usize) = .ok rem := rfl
  have vlane : lane.val = s.squeeze_offset.val / 8 := BitVec.toNat_udiv
  have vrem : rem.val = s.squeeze_offset.val % 8 := BitVec.toNat_umod
  have hrem : rem.val < 8 := by rw [vrem]; exact Nat.mod_lt _ (by decide)
  let byte := UScalar.cast .U32 rem
  have vbyte : byte.val = rem.val := by
    change (rem.bv.setWidth 32).toNat = rem.bv.toNat
    rw [BitVec.toNat_setWidth]
    exact Nat.mod_eq_of_lt (Nat.lt_trans hrem (by decide))
  obtain ⟨shift, hshift, vshift⟩ := checked_mul_val 8#u32 byte
    (by change 8 * byte.val < 2 ^ 32; rw [vbyte]; exact Nat.lt_trans (Nat.mul_lt_mul_of_pos_left hrem (by decide : 0 < 8)) (by decide))
  change shift.val = 8 * byte.val at vshift
  have hv := array_index_getD s.state lane 0#u64
    (by change lane.val < 25; rw [vlane]; exact (Nat.div_lt_iff_lt_mul (by decide)).mpr (Nat.lt_trans ho (by decide)))
  let v := s.state.val.getD lane.val 0#u64
  let shifted : Std.U64 := ⟨v.bv >>> shift.val⟩
  have hshifted : (v >>> shift : Result Std.U64) = .ok shifted := by
    change (if shift.val < 64 then Result.ok shifted else Result.fail .integerOverflow) = Result.ok shifted
    exact ite_eq_left (by rw [vshift, vbyte]; exact Nat.mul_lt_mul_of_pos_left hrem (by decide))
  have hbyte : UScalar.cast .U8 (shifted &&& 255#u64) = spongeRateByte s.state s.squeeze_offset.val := by
    simp only [shifted, v, vlane, vshift, vbyte, vrem, spongeRateByte]
  let dst' : Slice Std.U8 := ⟨dst.val.set i.val (spongeRateByte s.state s.squeeze_offset.val), by rw [List.length_set]; exact dst.property⟩
  have hdst : Slice.update dst i (UScalar.cast .U8 (shifted &&& 255#u64)) = .ok dst' := by
    rw [hbyte]; exact dite_eq_left hi
  obtain ⟨i', hi', vi'⟩ := checked_add_val i 1#usize (by
    change i.val + 1 < 2 ^ 64
    have hd : (Slice.len dst).val < 2 ^ 64 := (Slice.len dst).bv.isLt
    rw [Slice.len_val] at hd
    exact Nat.lt_of_le_of_lt hi hd)
  obtain ⟨off', hoff', voff'⟩ := checked_add_val s.squeeze_offset 1#usize
    (by change s.squeeze_offset.val + 1 < 2 ^ 64; exact Nat.lt_of_le_of_lt ho (by decide))
  refine ⟨dst', i', off', ?_, rfl, vi', voff'⟩
  simp only [keccak.Shake256Sponge.squeeze_loop.body, hlt, ite_true, hno, ite_false,
    hdiv, hmod, hv, hi', hoff', bind_eq_result_bind, result_bind_ok, lift_eq_ok]
  rw [hshift, result_bind_ok, hshifted, result_bind_ok, hdst, result_bind_ok]

/-- At every rate boundary the next byte is read from the canonical permutation
of the previous state, with the offset reset to zero. Applies equally to SHAKE
and cSHAKE states; suffix framing and finalization are separate obligations. -/
theorem sponge_squeeze_rollover (s : keccak.Shake256Sponge) (dst : Slice Std.U8)
    (i : Std.Usize) (hi : i.val < dst.val.length) (ho : 136 ≤ s.squeeze_offset.val) :
    keccak.Shake256Sponge.squeeze_loop.body s dst i =
      keccak.Shake256Sponge.squeeze_loop.body
        {s with state := keccakArrayOfState (Qsag.keccakF1600 (keccakStateOfArray s.state)), squeeze_offset := 0#usize} dst i := by
  have hlt : i < Slice.len dst := by change i.val < (Slice.len dst).val; rw [Slice.len_val]; exact hi
  have hge : s.squeeze_offset >= keccak.SHAKE256_RATE_BYTES := by unfold keccak.SHAKE256_RATE_BYTES; exact ho
  have hz : ¬ (0#usize >= keccak.SHAKE256_RATE_BYTES) := by
    unfold keccak.SHAKE256_RATE_BYTES; decide
  simp only [keccak.Shake256Sponge.squeeze_loop.body, hlt, hge, hz, ite_true, ite_false,
    keccak_f1600_array_refines_qsag, bind_eq_result_bind, result_bind_ok]

end qsag_verified.proofs
