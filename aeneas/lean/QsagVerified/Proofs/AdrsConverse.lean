module
import all QsagVerified.Funs

public import QsagVerified.Proofs.Adrs

public section

namespace qsag_verified.proofs
open Aeneas Aeneas.Std Result ControlFlow Error qsag_verified
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
attribute [-simp] BitVec.getLsbD_eq_getElem BitVec.setWidth_ofNat_of_le
attribute [local simp] UScalar.val UScalarTy.numBits

private def read32 (b0 b1 b2 b3 : Std.U8) : Std.U32 := ⟨((UScalar.cast .U32 b0).bv <<< 24) ||| ((UScalar.cast .U32 b1).bv <<< 16) ||| ((UScalar.cast .U32 b2).bv <<< 8) ||| (UScalar.cast .U32 b3).bv⟩

private theorem read32_eq (b0 b1 b2 b3 : Std.U8) :
    fips205.be_u32 b0 b1 b2 b3 = .ok (read32 b0 b1 b2 b3) := rfl

private theorem read32_byte0 (b0 b1 b2 b3 : Std.U8) :
    adrsByte32 (read32 b0 b1 b2 b3) 24 = b0 := by
  apply UScalar.ext
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change j < 8 at hj
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [adrsByte32, read32, UScalar.cast, UScalar.bv_and,
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  | j + 8, hj => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 j) hj)

private theorem read32_byte1 (b0 b1 b2 b3 : Std.U8) :
    adrsByte32 (read32 b0 b1 b2 b3) 16 = b1 := by
  apply UScalar.ext
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change j < 8 at hj
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [adrsByte32, read32, UScalar.cast, UScalar.bv_and,
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  | j + 8, hj => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 j) hj)

private theorem read32_byte2 (b0 b1 b2 b3 : Std.U8) :
    adrsByte32 (read32 b0 b1 b2 b3) 8 = b2 := by
  apply UScalar.ext
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change j < 8 at hj
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [adrsByte32, read32, UScalar.cast, UScalar.bv_and,
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  | j + 8, hj => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 j) hj)

private theorem read32_byte3 (b0 b1 b2 b3 : Std.U8) :
    adrsByte32 (read32 b0 b1 b2 b3) 0 = b3 := by
  apply UScalar.ext
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change j < 8 at hj
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [adrsByte32, read32, UScalar.cast, UScalar.bv_and,
      BitVec.getLsbD_and]
  | j + 8, hj => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 j) hj)

private def read64 (b0 b1 b2 b3 b4 b5 b6 b7 : Std.U8) : Std.U64 := ⟨((UScalar.cast .U64 b0).bv <<< 56) ||| ((UScalar.cast .U64 b1).bv <<< 48) ||| ((UScalar.cast .U64 b2).bv <<< 40) ||| ((UScalar.cast .U64 b3).bv <<< 32) ||| ((UScalar.cast .U64 b4).bv <<< 24) ||| ((UScalar.cast .U64 b5).bv <<< 16) ||| ((UScalar.cast .U64 b6).bv <<< 8) ||| (UScalar.cast .U64 b7).bv⟩

private theorem read64_eq (b0 b1 b2 b3 b4 b5 b6 b7 : Std.U8) :
    fips205.be_u64 b0 b1 b2 b3 b4 b5 b6 b7 = .ok (read64 b0 b1 b2 b3 b4 b5 b6 b7) := rfl

private theorem read64_byte0 (b0 b1 b2 b3 b4 b5 b6 b7 : Std.U8) :
    adrsByte64 (read64 b0 b1 b2 b3 b4 b5 b6 b7) 56 = b0 := by
  apply UScalar.ext
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change j < 8 at hj
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [adrsByte64, read64, UScalar.cast, UScalar.bv_and,
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  | j + 8, hj => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 j) hj)

private theorem read64_byte1 (b0 b1 b2 b3 b4 b5 b6 b7 : Std.U8) :
    adrsByte64 (read64 b0 b1 b2 b3 b4 b5 b6 b7) 48 = b1 := by
  apply UScalar.ext
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change j < 8 at hj
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [adrsByte64, read64, UScalar.cast, UScalar.bv_and,
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  | j + 8, hj => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 j) hj)

private theorem read64_byte2 (b0 b1 b2 b3 b4 b5 b6 b7 : Std.U8) :
    adrsByte64 (read64 b0 b1 b2 b3 b4 b5 b6 b7) 40 = b2 := by
  apply UScalar.ext
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change j < 8 at hj
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [adrsByte64, read64, UScalar.cast, UScalar.bv_and,
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  | j + 8, hj => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 j) hj)

private theorem read64_byte3 (b0 b1 b2 b3 b4 b5 b6 b7 : Std.U8) :
    adrsByte64 (read64 b0 b1 b2 b3 b4 b5 b6 b7) 32 = b3 := by
  apply UScalar.ext
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change j < 8 at hj
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [adrsByte64, read64, UScalar.cast, UScalar.bv_and,
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  | j + 8, hj => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 j) hj)

private theorem read64_byte4 (b0 b1 b2 b3 b4 b5 b6 b7 : Std.U8) :
    adrsByte64 (read64 b0 b1 b2 b3 b4 b5 b6 b7) 24 = b4 := by
  apply UScalar.ext
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change j < 8 at hj
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [adrsByte64, read64, UScalar.cast, UScalar.bv_and,
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  | j + 8, hj => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 j) hj)

private theorem read64_byte5 (b0 b1 b2 b3 b4 b5 b6 b7 : Std.U8) :
    adrsByte64 (read64 b0 b1 b2 b3 b4 b5 b6 b7) 16 = b5 := by
  apply UScalar.ext
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change j < 8 at hj
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [adrsByte64, read64, UScalar.cast, UScalar.bv_and,
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  | j + 8, hj => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 j) hj)

private theorem read64_byte6 (b0 b1 b2 b3 b4 b5 b6 b7 : Std.U8) :
    adrsByte64 (read64 b0 b1 b2 b3 b4 b5 b6 b7) 8 = b6 := by
  apply UScalar.ext
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change j < 8 at hj
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [adrsByte64, read64, UScalar.cast, UScalar.bv_and,
      BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  | j + 8, hj => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 j) hj)

private theorem read64_byte7 (b0 b1 b2 b3 b4 b5 b6 b7 : Std.U8) :
    adrsByte64 (read64 b0 b1 b2 b3 b4 b5 b6 b7) 0 = b7 := by
  apply UScalar.ext
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change j < 8 at hj
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [adrsByte64, read64, UScalar.cast, UScalar.bv_and,
      BitVec.getLsbD_and]
  | j + 8, hj => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 j) hj)

private theorem adrs_type_converse (tag : Std.U32) (ty : fips205.Fips205AdrsType)
    (h : fips205.Fips205AdrsType.from_u32 tag = .ok (some ty)) : adrsTypeWord ty = tag := by
  unfold fips205.Fips205AdrsType.from_u32 at h
  split at h <;> cases h <;> rfl

theorem fips205_adrs_decode_encode_spec (bytes : Std.Array Std.U8 32#usize)
    (adrs : fips205.Fips205Adrs)
    (h : fips205.decode_fips205_adrs bytes = .ok (some adrs)) :
    fips205.encode_fips205_adrs adrs = .ok bytes := by
  have index (i : Std.Usize) (hi : i.val < 32) :
      Std.Array.index_usize bytes i = .ok (bytes.val.getD i.val 0#u8) :=
    array_index_getD bytes i 0#u8 hi
  unfold fips205.decode_fips205_adrs at h
  simp (disch := decide) only [index, bind_eq_result_bind, result_bind_ok, read32_eq, read64_eq] at h
  simp only [UScalar.val, UScalarTy.numBits, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at h
  let tag := read32 (bytes.val.getD 16 0#u8) (bytes.val.getD 17 0#u8)
    (bytes.val.getD 18 0#u8) (bytes.val.getD 19 0#u8)
  cases ht : fips205.Fips205AdrsType.from_u32 tag with
  | fail e => rw [ht] at h; cases h
  | div => rw [ht] at h; cases h
  | ok o =>
    rw [ht] at h
    cases o with
    | none => simp only [Result.bind, Result.ok.injEq] at h; cases h
    | some ty =>
      simp only [Result.bind, Result.ok.injEq, Option.some.injEq] at h
      subst adrs
      rw [adrs_encode_eq]
      apply congrArg Result.ok
      have hty := adrs_type_converse tag ty ht
      apply Std.Array.ext
      apply List.ext_getElem (by simp only [adrsBytes, Std.Array.make, List.length_cons, List.length_nil]; exact bytes.property.symm)
      intro i hi hj
      rw [List.getElem_eq_getD 0#u8, List.getElem_eq_getD 0#u8]
      have bound : i < 32 := by rw [bytes.property] at hj; exact hj
      simp only [adrsBytes, hty]
      dsimp only [tag]
      match i, bound with
      | 0, _ => exact read32_byte0 _ _ _ _
      | 1, _ => exact read32_byte1 _ _ _ _
      | 2, _ => exact read32_byte2 _ _ _ _
      | 3, _ => exact read32_byte3 _ _ _ _
      | 4, _ => exact read32_byte0 _ _ _ _
      | 5, _ => exact read32_byte1 _ _ _ _
      | 6, _ => exact read32_byte2 _ _ _ _
      | 7, _ => exact read32_byte3 _ _ _ _
      | 8, _ => exact read64_byte0 _ _ _ _ _ _ _ _
      | 9, _ => exact read64_byte1 _ _ _ _ _ _ _ _
      | 10, _ => exact read64_byte2 _ _ _ _ _ _ _ _
      | 11, _ => exact read64_byte3 _ _ _ _ _ _ _ _
      | 12, _ => exact read64_byte4 _ _ _ _ _ _ _ _
      | 13, _ => exact read64_byte5 _ _ _ _ _ _ _ _
      | 14, _ => exact read64_byte6 _ _ _ _ _ _ _ _
      | 15, _ => exact read64_byte7 _ _ _ _ _ _ _ _
      | 16, _ => exact read32_byte0 _ _ _ _
      | 17, _ => exact read32_byte1 _ _ _ _
      | 18, _ => exact read32_byte2 _ _ _ _
      | 19, _ => exact read32_byte3 _ _ _ _
      | 20, _ => exact read32_byte0 _ _ _ _
      | 21, _ => exact read32_byte1 _ _ _ _
      | 22, _ => exact read32_byte2 _ _ _ _
      | 23, _ => exact read32_byte3 _ _ _ _
      | 24, _ => exact read32_byte0 _ _ _ _
      | 25, _ => exact read32_byte1 _ _ _ _
      | 26, _ => exact read32_byte2 _ _ _ _
      | 27, _ => exact read32_byte3 _ _ _ _
      | 28, _ => exact read32_byte0 _ _ _ _
      | 29, _ => exact read32_byte1 _ _ _ _
      | 30, _ => exact read32_byte2 _ _ _ _
      | 31, _ => exact read32_byte3 _ _ _ _
      | i + 32, hi => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 32 i) hi)

end qsag_verified.proofs
