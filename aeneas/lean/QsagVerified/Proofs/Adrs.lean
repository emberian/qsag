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

/-! ## FIPS 205 address serialization -/

private theorem byte_and_allOnes (x : BitVec 8) : x &&& BitVec.allOnes 8 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and]
  have hm : (BitVec.allOnes 8).getLsbD i = true := by
    match i, hi with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl
    | n + 8, hi => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 8 n) hi)
  rw [hm, Bool.and_true]

@[expose]
def adrsByte32 (v : Std.U32) (shift : Nat) : Std.U8 :=
  UScalar.cast .U8 ((⟨v.bv >>> shift⟩ : Std.U32) &&& 255#u32)

private theorem be_u32_roundtrip (v : Std.U32) :
    fips205.be_u32 (adrsByte32 v 24) (adrsByte32 v 16) (adrsByte32 v 8) (adrsByte32 v 0) = .ok v := by
  change Result.ok (⟨((UScalar.cast .U32 (adrsByte32 v 24)).bv <<< 24) ||| ((UScalar.cast .U32 (adrsByte32 v 16)).bv <<< 16) ||| ((UScalar.cast .U32 (adrsByte32 v 8)).bv <<< 8) ||| (UScalar.cast .U32 (adrsByte32 v 0)).bv⟩ : Std.U32) = .ok v
  apply congrArg Result.ok
  apply UScalar.ext
  simp only [adrsByte32, UScalar.cast, UScalar.bv_and, BitVec.setWidth_and]
  change (((v.bv >>> 24).setWidth 8 &&& BitVec.allOnes 8).setWidth 32 <<< 24) ||| (((v.bv >>> 16).setWidth 8 &&& BitVec.allOnes 8).setWidth 32 <<< 16) ||| (((v.bv >>> 8).setWidth 8 &&& BitVec.allOnes 8).setWidth 32 <<< 8) ||| (((v.bv >>> 0).setWidth 8 &&& BitVec.allOnes 8).setWidth 32) = v.bv
  simp only [byte_and_allOnes]
  have hcat : (v.bv >>> 24).setWidth 8 ++ (v.bv >>> 16).setWidth 8 ++ (v.bv >>> 8).setWidth 8 ++ (v.bv >>> 0).setWidth 8 = v.bv := by
    simp only [BitVec.setWidth_ushiftRight_eq_extractLsb]
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
    simp
  calc
    _ = ((v.bv >>> 24).setWidth 8 ++ (v.bv >>> 16).setWidth 8 ++ (v.bv >>> 8).setWidth 8 ++ (v.bv >>> 0).setWidth 8).setWidth 32 := by
      rw [BitVec.setWidth_append_eq_shiftLeft_setWidth_or (b := (v.bv >>> 24).setWidth 8 ++ (v.bv >>> 16).setWidth 8 ++ (v.bv >>> 8).setWidth 8) (b' := (v.bv >>> 0).setWidth 8)]
      rw [BitVec.setWidth_append_eq_shiftLeft_setWidth_or (b := (v.bv >>> 24).setWidth 8 ++ (v.bv >>> 16).setWidth 8) (b' := (v.bv >>> 8).setWidth 8)]
      rw [BitVec.setWidth_append_eq_shiftLeft_setWidth_or (b := (v.bv >>> 24).setWidth 8) (b' := (v.bv >>> 16).setWidth 8)]
      simp only [BitVec.shiftLeft_or_distrib, ← BitVec.shiftLeft_add, Nat.reduceAdd]
    _ = v.bv := by rw [hcat]; rfl

@[expose]
def adrsByte64 (v : Std.U64) (shift : Nat) : Std.U8 :=
  UScalar.cast .U8 ((⟨v.bv >>> shift⟩ : Std.U64) &&& 255#u64)

set_option maxHeartbeats 200000 in
private theorem be_u64_roundtrip (v : Std.U64) :
    fips205.be_u64 (adrsByte64 v 56) (adrsByte64 v 48) (adrsByte64 v 40) (adrsByte64 v 32) (adrsByte64 v 24) (adrsByte64 v 16) (adrsByte64 v 8) (adrsByte64 v 0) = .ok v := by
  change Result.ok (⟨((UScalar.cast .U64 (adrsByte64 v 56)).bv <<< 56) ||| ((UScalar.cast .U64 (adrsByte64 v 48)).bv <<< 48) ||| ((UScalar.cast .U64 (adrsByte64 v 40)).bv <<< 40) ||| ((UScalar.cast .U64 (adrsByte64 v 32)).bv <<< 32) ||| ((UScalar.cast .U64 (adrsByte64 v 24)).bv <<< 24) ||| ((UScalar.cast .U64 (adrsByte64 v 16)).bv <<< 16) ||| ((UScalar.cast .U64 (adrsByte64 v 8)).bv <<< 8) ||| (UScalar.cast .U64 (adrsByte64 v 0)).bv⟩ : Std.U64) = .ok v
  apply congrArg Result.ok
  apply UScalar.ext
  simp only [adrsByte64, UScalar.cast, UScalar.bv_and, BitVec.setWidth_and]
  change (((v.bv >>> 56).setWidth 8 &&& BitVec.allOnes 8).setWidth 64 <<< 56) ||| (((v.bv >>> 48).setWidth 8 &&& BitVec.allOnes 8).setWidth 64 <<< 48) ||| (((v.bv >>> 40).setWidth 8 &&& BitVec.allOnes 8).setWidth 64 <<< 40) ||| (((v.bv >>> 32).setWidth 8 &&& BitVec.allOnes 8).setWidth 64 <<< 32) ||| (((v.bv >>> 24).setWidth 8 &&& BitVec.allOnes 8).setWidth 64 <<< 24) ||| (((v.bv >>> 16).setWidth 8 &&& BitVec.allOnes 8).setWidth 64 <<< 16) ||| (((v.bv >>> 8).setWidth 8 &&& BitVec.allOnes 8).setWidth 64 <<< 8) ||| (((v.bv >>> 0).setWidth 8 &&& BitVec.allOnes 8).setWidth 64) = v.bv
  simp only [byte_and_allOnes]
  have hcat : (v.bv >>> 56).setWidth 8 ++ (v.bv >>> 48).setWidth 8 ++ (v.bv >>> 40).setWidth 8 ++ (v.bv >>> 32).setWidth 8 ++ (v.bv >>> 24).setWidth 8 ++ (v.bv >>> 16).setWidth 8 ++ (v.bv >>> 8).setWidth 8 ++ (v.bv >>> 0).setWidth 8 = v.bv := by
    simp only [BitVec.setWidth_ushiftRight_eq_extractLsb]
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
    simp
  calc
    _ = ((v.bv >>> 56).setWidth 8 ++ (v.bv >>> 48).setWidth 8 ++ (v.bv >>> 40).setWidth 8 ++ (v.bv >>> 32).setWidth 8 ++ (v.bv >>> 24).setWidth 8 ++ (v.bv >>> 16).setWidth 8 ++ (v.bv >>> 8).setWidth 8 ++ (v.bv >>> 0).setWidth 8).setWidth 64 := by
      rw [BitVec.setWidth_append_eq_shiftLeft_setWidth_or (b := (v.bv >>> 56).setWidth 8 ++ (v.bv >>> 48).setWidth 8 ++ (v.bv >>> 40).setWidth 8 ++ (v.bv >>> 32).setWidth 8 ++ (v.bv >>> 24).setWidth 8 ++ (v.bv >>> 16).setWidth 8 ++ (v.bv >>> 8).setWidth 8) (b' := (v.bv >>> 0).setWidth 8)]
      rw [BitVec.setWidth_append_eq_shiftLeft_setWidth_or (b := (v.bv >>> 56).setWidth 8 ++ (v.bv >>> 48).setWidth 8 ++ (v.bv >>> 40).setWidth 8 ++ (v.bv >>> 32).setWidth 8 ++ (v.bv >>> 24).setWidth 8 ++ (v.bv >>> 16).setWidth 8) (b' := (v.bv >>> 8).setWidth 8)]
      rw [BitVec.setWidth_append_eq_shiftLeft_setWidth_or (b := (v.bv >>> 56).setWidth 8 ++ (v.bv >>> 48).setWidth 8 ++ (v.bv >>> 40).setWidth 8 ++ (v.bv >>> 32).setWidth 8 ++ (v.bv >>> 24).setWidth 8) (b' := (v.bv >>> 16).setWidth 8)]
      rw [BitVec.setWidth_append_eq_shiftLeft_setWidth_or (b := (v.bv >>> 56).setWidth 8 ++ (v.bv >>> 48).setWidth 8 ++ (v.bv >>> 40).setWidth 8 ++ (v.bv >>> 32).setWidth 8) (b' := (v.bv >>> 24).setWidth 8)]
      rw [BitVec.setWidth_append_eq_shiftLeft_setWidth_or (b := (v.bv >>> 56).setWidth 8 ++ (v.bv >>> 48).setWidth 8 ++ (v.bv >>> 40).setWidth 8) (b' := (v.bv >>> 32).setWidth 8)]
      rw [BitVec.setWidth_append_eq_shiftLeft_setWidth_or (b := (v.bv >>> 56).setWidth 8 ++ (v.bv >>> 48).setWidth 8) (b' := (v.bv >>> 40).setWidth 8)]
      rw [BitVec.setWidth_append_eq_shiftLeft_setWidth_or (b := (v.bv >>> 56).setWidth 8) (b' := (v.bv >>> 48).setWidth 8)]
      simp only [BitVec.shiftLeft_or_distrib, ← BitVec.shiftLeft_add, Nat.reduceAdd]
    _ = v.bv := by rw [hcat]; rfl

@[expose]
def adrsTypeWord : fips205.Fips205AdrsType → Std.U32
  | .WotsHash => 0#u32
  | .WotsPk => 1#u32
  | .Tree => 2#u32
  | .ForsTree => 3#u32
  | .ForsRoots => 4#u32
  | .WotsPrf => 5#u32
  | .ForsPrf => 6#u32

private theorem adrs_type_encode (ty : fips205.Fips205AdrsType) :
    fips205.Fips205AdrsType.to_u32 ty = .ok (adrsTypeWord ty) := by cases ty <;> rfl

private theorem adrs_type_decode (ty : fips205.Fips205AdrsType) :
    fips205.Fips205AdrsType.from_u32 (adrsTypeWord ty) = .ok (some ty) := by cases ty <;> rfl

@[expose]
def adrsBytes (a : fips205.Fips205Adrs) : Std.Array Std.U8 32#usize :=
  Std.Array.make 32#usize [
    adrsByte32 a.layer 24, adrsByte32 a.layer 16, adrsByte32 a.layer 8, adrsByte32 a.layer 0,
    adrsByte32 a.tree_hi 24, adrsByte32 a.tree_hi 16, adrsByte32 a.tree_hi 8, adrsByte32 a.tree_hi 0,
    adrsByte64 a.tree_lo 56, adrsByte64 a.tree_lo 48, adrsByte64 a.tree_lo 40, adrsByte64 a.tree_lo 32, adrsByte64 a.tree_lo 24, adrsByte64 a.tree_lo 16, adrsByte64 a.tree_lo 8, adrsByte64 a.tree_lo 0,
    adrsByte32 (adrsTypeWord a.adrs_type) 24, adrsByte32 (adrsTypeWord a.adrs_type) 16, adrsByte32 (adrsTypeWord a.adrs_type) 8, adrsByte32 (adrsTypeWord a.adrs_type) 0,
    adrsByte32 a.kp 24, adrsByte32 a.kp 16, adrsByte32 a.kp 8, adrsByte32 a.kp 0,
    adrsByte32 a.chain 24, adrsByte32 a.chain 16, adrsByte32 a.chain 8, adrsByte32 a.chain 0,
    adrsByte32 a.hash 24, adrsByte32 a.hash 16, adrsByte32 a.hash 8, adrsByte32 a.hash 0]

theorem adrs_encode_eq (a : fips205.Fips205Adrs) :
    fips205.encode_fips205_adrs a = .ok (adrsBytes a) := by
  unfold fips205.encode_fips205_adrs
  rw [adrs_type_encode]
  rfl

theorem fips205_adrs_roundtrip_spec (adrs : fips205.Fips205Adrs) :
    ∃ bytes, fips205.encode_fips205_adrs adrs = .ok bytes ∧
      fips205.decode_fips205_adrs bytes = .ok (some adrs) := by
  refine ⟨adrsBytes adrs, adrs_encode_eq adrs, ?_⟩
  unfold fips205.decode_fips205_adrs
  simp [adrsBytes, Std.Array.make, Std.Array.index_usize,
    be_u32_roundtrip, be_u64_roundtrip, adrs_type_decode]

/-- Big-endian address type word at byte positions 16 through 19. -/
@[expose]
def fips205AdrsTypeTag (bytes : Std.Array Std.U8 32#usize) : Std.U32 :=
  ⟨((UScalar.cast .U32 (bytes.val.getD 16 0#u8)).bv <<< 24) |||
    ((UScalar.cast .U32 (bytes.val.getD 17 0#u8)).bv <<< 16) |||
    ((UScalar.cast .U32 (bytes.val.getD 18 0#u8)).bv <<< 8) |||
    (UScalar.cast .U32 (bytes.val.getD 19 0#u8)).bv⟩

private theorem adrs_type_invalid (tag : Std.U32) (h : 6 < tag.val) :
    fips205.Fips205AdrsType.from_u32 tag = .ok none := by
  unfold fips205.Fips205AdrsType.from_u32
  split <;> first | rfl | (simp_all [UScalar.val])

private theorem be_u32_total (a b c d : Std.U8) : ∃ out, fips205.be_u32 a b c d = .ok out := ⟨_, rfl⟩
private theorem be_u64_total (a b c d e f g h : Std.U8) : ∃ out, fips205.be_u64 a b c d e f g h = .ok out := ⟨_, rfl⟩

theorem fips205_adrs_decode_invalid_type_none (bytes : Std.Array Std.U8 32#usize)
    (h : 6 < (fips205AdrsTypeTag bytes).val) :
    fips205.decode_fips205_adrs bytes = .ok none := by
  have hi0 : Std.Array.index_usize bytes 0#usize = .ok (bytes.val.getD 0 0#u8) :=
    array_index_getD bytes 0#usize 0#u8 (by decide)
  have hi1 : Std.Array.index_usize bytes 1#usize = .ok (bytes.val.getD 1 0#u8) :=
    array_index_getD bytes 1#usize 0#u8 (by decide)
  have hi2 : Std.Array.index_usize bytes 2#usize = .ok (bytes.val.getD 2 0#u8) :=
    array_index_getD bytes 2#usize 0#u8 (by decide)
  have hi3 : Std.Array.index_usize bytes 3#usize = .ok (bytes.val.getD 3 0#u8) :=
    array_index_getD bytes 3#usize 0#u8 (by decide)
  have hi4 : Std.Array.index_usize bytes 4#usize = .ok (bytes.val.getD 4 0#u8) :=
    array_index_getD bytes 4#usize 0#u8 (by decide)
  have hi5 : Std.Array.index_usize bytes 5#usize = .ok (bytes.val.getD 5 0#u8) :=
    array_index_getD bytes 5#usize 0#u8 (by decide)
  have hi6 : Std.Array.index_usize bytes 6#usize = .ok (bytes.val.getD 6 0#u8) :=
    array_index_getD bytes 6#usize 0#u8 (by decide)
  have hi7 : Std.Array.index_usize bytes 7#usize = .ok (bytes.val.getD 7 0#u8) :=
    array_index_getD bytes 7#usize 0#u8 (by decide)
  have hi8 : Std.Array.index_usize bytes 8#usize = .ok (bytes.val.getD 8 0#u8) :=
    array_index_getD bytes 8#usize 0#u8 (by decide)
  have hi9 : Std.Array.index_usize bytes 9#usize = .ok (bytes.val.getD 9 0#u8) :=
    array_index_getD bytes 9#usize 0#u8 (by decide)
  have hi10 : Std.Array.index_usize bytes 10#usize = .ok (bytes.val.getD 10 0#u8) :=
    array_index_getD bytes 10#usize 0#u8 (by decide)
  have hi11 : Std.Array.index_usize bytes 11#usize = .ok (bytes.val.getD 11 0#u8) :=
    array_index_getD bytes 11#usize 0#u8 (by decide)
  have hi12 : Std.Array.index_usize bytes 12#usize = .ok (bytes.val.getD 12 0#u8) :=
    array_index_getD bytes 12#usize 0#u8 (by decide)
  have hi13 : Std.Array.index_usize bytes 13#usize = .ok (bytes.val.getD 13 0#u8) :=
    array_index_getD bytes 13#usize 0#u8 (by decide)
  have hi14 : Std.Array.index_usize bytes 14#usize = .ok (bytes.val.getD 14 0#u8) :=
    array_index_getD bytes 14#usize 0#u8 (by decide)
  have hi15 : Std.Array.index_usize bytes 15#usize = .ok (bytes.val.getD 15 0#u8) :=
    array_index_getD bytes 15#usize 0#u8 (by decide)
  have hi16 : Std.Array.index_usize bytes 16#usize = .ok (bytes.val.getD 16 0#u8) :=
    array_index_getD bytes 16#usize 0#u8 (by decide)
  have hi17 : Std.Array.index_usize bytes 17#usize = .ok (bytes.val.getD 17 0#u8) :=
    array_index_getD bytes 17#usize 0#u8 (by decide)
  have hi18 : Std.Array.index_usize bytes 18#usize = .ok (bytes.val.getD 18 0#u8) :=
    array_index_getD bytes 18#usize 0#u8 (by decide)
  have hi19 : Std.Array.index_usize bytes 19#usize = .ok (bytes.val.getD 19 0#u8) :=
    array_index_getD bytes 19#usize 0#u8 (by decide)
  have htag : fips205.be_u32 (bytes.val.getD 16 0#u8) (bytes.val.getD 17 0#u8)
      (bytes.val.getD 18 0#u8) (bytes.val.getD 19 0#u8) = .ok (fips205AdrsTypeTag bytes) := rfl
  have hnone := adrs_type_invalid _ h
  obtain ⟨layer, hlayer⟩ := be_u32_total (bytes.val.getD 0 0#u8) (bytes.val.getD 1 0#u8) (bytes.val.getD 2 0#u8) (bytes.val.getD 3 0#u8)
  obtain ⟨tree, htree⟩ := be_u32_total (bytes.val.getD 4 0#u8) (bytes.val.getD 5 0#u8) (bytes.val.getD 6 0#u8) (bytes.val.getD 7 0#u8)
  obtain ⟨treeLo, htreeLo⟩ := be_u64_total (bytes.val.getD 8 0#u8) (bytes.val.getD 9 0#u8) (bytes.val.getD 10 0#u8) (bytes.val.getD 11 0#u8) (bytes.val.getD 12 0#u8) (bytes.val.getD 13 0#u8) (bytes.val.getD 14 0#u8) (bytes.val.getD 15 0#u8)
  unfold fips205.decode_fips205_adrs
  simp only [bind_eq_result_bind]
  rw [hi0, result_bind_ok]
  rw [hi1, result_bind_ok]
  rw [hi2, result_bind_ok]
  rw [hi3, result_bind_ok]
  rw [hlayer, result_bind_ok]
  rw [hi4, result_bind_ok]
  rw [hi5, result_bind_ok]
  rw [hi6, result_bind_ok]
  rw [hi7, result_bind_ok]
  rw [htree, result_bind_ok]
  rw [hi8, result_bind_ok]
  rw [hi9, result_bind_ok]
  rw [hi10, result_bind_ok]
  rw [hi11, result_bind_ok]
  rw [hi12, result_bind_ok]
  rw [hi13, result_bind_ok]
  rw [hi14, result_bind_ok]
  rw [hi15, result_bind_ok]
  rw [htreeLo, result_bind_ok]
  rw [hi16, result_bind_ok]
  rw [hi17, result_bind_ok]
  rw [hi18, result_bind_ok]
  rw [hi19, result_bind_ok]
  rw [htag, result_bind_ok, hnone, result_bind_ok]


end qsag_verified.proofs
