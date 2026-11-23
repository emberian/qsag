module
public import QsagWhirVerified.Types
public import QsagWhirVerified.Funs
public import QsagWhirVerified.Arithmetic
public import Aeneas
public import Aeneas.Std.Types
public import Aeneas.Std.Containers
public section
open Aeneas Aeneas.Std
namespace qsag_whir_verified.proofs
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096

@[simp] private theorem u64_zero_val : (0#u64).val = 0 := rfl

/-! ## 1. Little-Endian 40-Byte & 56-Byte Word Loaders and Canonical Wire Decoders -/

private theorem shl8 (d : U64) : (d <<< 8#i32 : Result U64) = .ok ⟨d.bv <<< 8⟩ := rfl
private theorem shl16 (d : U64) : (d <<< 16#i32 : Result U64) = .ok ⟨d.bv <<< 16⟩ := rfl
private theorem shl24 (d : U64) : (d <<< 24#i32 : Result U64) = .ok ⟨d.bv <<< 24⟩ := rfl
private theorem shl32 (d : U64) : (d <<< 32#i32 : Result U64) = .ok ⟨d.bv <<< 32⟩ := rfl
private theorem shl40 (d : U64) : (d <<< 40#i32 : Result U64) = .ok ⟨d.bv <<< 40⟩ := rfl
private theorem shl48 (d : U64) : (d <<< 48#i32 : Result U64) = .ok ⟨d.bv <<< 48⟩ := rfl
private theorem shl56 (d : U64) : (d <<< 56#i32 : Result U64) = .ok ⟨d.bv <<< 56⟩ := rfl

private theorem array_index_getD_u8 {n : Usize} (arr : Array U8 n) (idx : Usize)
    (hlt : idx.val < n.val) :
    Array.index_usize arr idx = .ok (arr.val.getD idx.val 0#u8) := by
  have hlen : idx.val < arr.val.length := by rw [arr.property]; exact hlt
  simp only [Array.index_usize, dite_eq_left hlen, Result.ok.injEq]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some]

private theorem add_index_getD_u8 {n : Usize} (arr : Array U8 n) (off c : Usize) (k : Nat)
    (hc : c.val = k) (hlt : off.val + k < n.val) (hn64 : n.val < 2 ^ 64) :
    ∃ j : Usize, (off + c : Result Usize) = .ok j ∧
      Array.index_usize arr j = .ok (arr.val.getD (off.val + k) 0#u8) := by
  have hsum_lt : off.val + c.val < 2 ^ 64 := by rw [hc]; omega
  let j : Usize := ⟨off.bv + c.bv⟩
  have hj : (off + c : Result Usize) = .ok j := by
    simp only [hAdd_uscalar_eq, UScalarTy.numBits_usize, hsum_lt, ↓reduceIte]
    rfl
  have hjval : j.val = off.val + k := by
    change (off.bv + c.bv).toNat = off.val + k
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hsum_lt, hc]
  refine ⟨j, hj, ?_⟩
  have hidx := array_index_getD_u8 arr j (by rw [hjval]; exact hlt)
  rwa [hjval] at hidx

theorem load_le_u64_40_spec (bytes : Array U8 40#usize) (off : Usize) :
    load_le_u64_40 bytes off =
      .ok (if 32 < off.val then 0#u64 else lePackU64At bytes.val off.val) := by
  simp only [load_le_u64_40.public_eqs]
  have h32 : (32#usize).val = 32 := rfl
  have h40 : (40#usize).val = 40 := rfl
  by_cases hgt : off > 32#usize
  · have hgt' : 32 < off.val := by simpa only [GT.gt, UScalar.lt_iff_val, h32] using hgt
    simp [hgt, hgt']
  · have hle : off.val ≤ 32 := by
      simp only [GT.gt, UScalar.lt_iff_val, h32] at hgt; omega
    have hng : ¬ (32 < off.val) := by omega
    have hv0 := array_index_getD_u8 bytes off (by rw [h40]; omega)
    obtain ⟨j1, hj1, hv1⟩ := add_index_getD_u8 bytes off 1#usize 1 rfl (by rw [h40]; omega) (by decide)
    obtain ⟨j2, hj2, hv2⟩ := add_index_getD_u8 bytes off 2#usize 2 rfl (by rw [h40]; omega) (by decide)
    obtain ⟨j3, hj3, hv3⟩ := add_index_getD_u8 bytes off 3#usize 3 rfl (by rw [h40]; omega) (by decide)
    obtain ⟨j4, hj4, hv4⟩ := add_index_getD_u8 bytes off 4#usize 4 rfl (by rw [h40]; omega) (by decide)
    obtain ⟨j5, hj5, hv5⟩ := add_index_getD_u8 bytes off 5#usize 5 rfl (by rw [h40]; omega) (by decide)
    obtain ⟨j6, hj6, hv6⟩ := add_index_getD_u8 bytes off 6#usize 6 rfl (by rw [h40]; omega) (by decide)
    obtain ⟨j7, hj7, hv7⟩ := add_index_getD_u8 bytes off 7#usize 7 rfl (by rw [h40]; omega) (by decide)
    simp only [hgt, hng, ↓reduceIte, hv0, hj1, hv1, hj2, hv2, hj3, hv3, hj4, hv4,
      hj5, hv5, hj6, hv6, hj7, hv7, shl8, shl16, shl24, shl32, shl40, shl48, shl56,
      lift_eq_ok, bind_eq_result_bind, result_bind_ok, lePackU64At]
    rfl

theorem load_le_u64_56_spec (bytes : Array U8 56#usize) (off : Usize) :
    load_le_u64_56 bytes off =
      .ok (if 48 < off.val then 0#u64 else lePackU64At bytes.val off.val) := by
  simp only [load_le_u64_56.public_eqs]
  have h48 : (48#usize).val = 48 := rfl
  have h56 : (56#usize).val = 56 := rfl
  by_cases hgt : off > 48#usize
  · have hgt' : 48 < off.val := by simpa only [GT.gt, UScalar.lt_iff_val, h48] using hgt
    simp [hgt, hgt']
  · have hle : off.val ≤ 48 := by
      simp only [GT.gt, UScalar.lt_iff_val, h48] at hgt; omega
    have hng : ¬ (48 < off.val) := by omega
    have hv0 := array_index_getD_u8 bytes off (by rw [h56]; omega)
    obtain ⟨j1, hj1, hv1⟩ := add_index_getD_u8 bytes off 1#usize 1 rfl (by rw [h56]; omega) (by decide)
    obtain ⟨j2, hj2, hv2⟩ := add_index_getD_u8 bytes off 2#usize 2 rfl (by rw [h56]; omega) (by decide)
    obtain ⟨j3, hj3, hv3⟩ := add_index_getD_u8 bytes off 3#usize 3 rfl (by rw [h56]; omega) (by decide)
    obtain ⟨j4, hj4, hv4⟩ := add_index_getD_u8 bytes off 4#usize 4 rfl (by rw [h56]; omega) (by decide)
    obtain ⟨j5, hj5, hv5⟩ := add_index_getD_u8 bytes off 5#usize 5 rfl (by rw [h56]; omega) (by decide)
    obtain ⟨j6, hj6, hv6⟩ := add_index_getD_u8 bytes off 6#usize 6 rfl (by rw [h56]; omega) (by decide)
    obtain ⟨j7, hj7, hv7⟩ := add_index_getD_u8 bytes off 7#usize 7 rfl (by rw [h56]; omega) (by decide)
    simp only [hgt, hng, ↓reduceIte, hv0, hj1, hv1, hj2, hv2, hj3, hv3, hj4, hv4,
      hj5, hv5, hj6, hv6, hj7, hv7, shl8, shl16, shl24, shl32, shl40, shl48, shl56,
      lift_eq_ok, bind_eq_result_bind, result_bind_ok, lePackU64At]
    rfl

theorem decode_canonical_u64_spec (x : U64) :
    decode_canonical_u64 x = .ok (if x.val < goldilocksMod then some x else none) := by
  simp only [decode_canonical_u64.public_eqs]
  by_cases h : x < GOLDILOCKS_P
  · have hv : x.val < goldilocksMod := by
      simpa only [UScalar.lt_iff_val, goldilocks_p_val] using h
    simp [h, hv]
  · have hv : ¬ x.val < goldilocksMod := by
      simpa only [UScalar.lt_iff_val, goldilocks_p_val] using h
    simp [h, hv]

theorem decode_canonical_u64_some_iff (x y : U64) :
    decode_canonical_u64 x = .ok (some y) ↔ IsCanonical x ∧ y = x := by
  rw [decode_canonical_u64_spec]
  by_cases h : x.val < goldilocksMod
  · simp [IsCanonical, h, eq_comm]
  · simp [IsCanonical, h]

theorem decode_canonical_u64_none_iff (x : U64) :
    decode_canonical_u64 x = .ok none ↔ goldilocksMod ≤ x.val := by
  rw [decode_canonical_u64_spec]
  by_cases h : x.val < goldilocksMod
  · simp [h, Nat.not_le.mpr h]
  · simp [h, Nat.not_lt.mp h]

theorem decode_canonical_u64_rejects_noncanonical (x : U64)
    (h : GOLDILOCKS_P.val ≤ x.val) : decode_canonical_u64 x = .ok none := by
  rw [decode_canonical_u64_none_iff]
  simpa only [goldilocks_p_val] using h

private theorem lt_goldilocks_iff_isCanonical (u : U64) :
    (u < GOLDILOCKS_P) ↔ IsCanonical u := by
  rw [UScalar.lt_iff_val, goldilocks_p_val]

theorem decode_canonical_fp5_limbs_spec (c0 c1 c2 c3 c4 : U64) :
    decode_canonical_fp5_limbs c0 c1 c2 c3 c4 =
      .ok (if IsCanonical c0 ∧ IsCanonical c1 ∧ IsCanonical c2 ∧ IsCanonical c3 ∧ IsCanonical c4
           then some ⟨c0, c1, c2, c3, c4⟩ else none) := by
  simp only [decode_canonical_fp5_limbs.public_eqs]
  by_cases h0 : c0 < GOLDILOCKS_P <;> simp only [h0, (lt_goldilocks_iff_isCanonical c0).mp,
    ↓reduceIte]
  · have hc0 := (lt_goldilocks_iff_isCanonical c0).mp h0
    by_cases h1 : c1 < GOLDILOCKS_P
    · have hc1 := (lt_goldilocks_iff_isCanonical c1).mp h1
      by_cases h2 : c2 < GOLDILOCKS_P
      · have hc2 := (lt_goldilocks_iff_isCanonical c2).mp h2
        by_cases h3 : c3 < GOLDILOCKS_P
        · have hc3 := (lt_goldilocks_iff_isCanonical c3).mp h3
          by_cases h4 : c4 < GOLDILOCKS_P
          · have hc4 := (lt_goldilocks_iff_isCanonical c4).mp h4
            simp [h1, h2, h3, h4, hc0, hc1, hc2, hc3, hc4]
          · have hc4 : ¬ IsCanonical c4 := fun k => h4 ((lt_goldilocks_iff_isCanonical c4).mpr k)
            simp [h1, h2, h3, h4, hc0, hc1, hc2, hc3, hc4]
        · have hc3 : ¬ IsCanonical c3 := fun k => h3 ((lt_goldilocks_iff_isCanonical c3).mpr k)
          simp [h1, h2, h3, hc0, hc1, hc2, hc3]
      · have hc2 : ¬ IsCanonical c2 := fun k => h2 ((lt_goldilocks_iff_isCanonical c2).mpr k)
        simp [h1, h2, hc0, hc1, hc2]
    · have hc1 : ¬ IsCanonical c1 := fun k => h1 ((lt_goldilocks_iff_isCanonical c1).mpr k)
      simp [h1, hc0, hc1]
  · have hc0 : ¬ IsCanonical c0 := fun k => h0 ((lt_goldilocks_iff_isCanonical c0).mpr k)
    simp [hc0]

theorem decode_canonical_fp5_limbs_some_iff (c0 c1 c2 c3 c4 : U64) (out : Fp5) :
    decode_canonical_fp5_limbs c0 c1 c2 c3 c4 = .ok (some out) ↔
      IsCanonical c0 ∧ IsCanonical c1 ∧ IsCanonical c2 ∧ IsCanonical c3 ∧ IsCanonical c4 ∧
      out = ⟨c0, c1, c2, c3, c4⟩ := by
  rw [decode_canonical_fp5_limbs_spec]
  by_cases h : IsCanonical c0 ∧ IsCanonical c1 ∧ IsCanonical c2 ∧ IsCanonical c3 ∧ IsCanonical c4
  · rcases h with ⟨h0, h1, h2, h3, h4⟩
    simp [h0, h1, h2, h3, h4, eq_comm]
  · simp [h]
    intro h0 h1 h2 h3 h4 _
    exact h ⟨h0, h1, h2, h3, h4⟩

theorem decode_canonical_fp5_limbs_none_iff (c0 c1 c2 c3 c4 : U64) :
    decode_canonical_fp5_limbs c0 c1 c2 c3 c4 = .ok none ↔
      ¬ (IsCanonical c0 ∧ IsCanonical c1 ∧ IsCanonical c2 ∧ IsCanonical c3 ∧ IsCanonical c4) := by
  rw [decode_canonical_fp5_limbs_spec]
  by_cases h : IsCanonical c0 ∧ IsCanonical c1 ∧ IsCanonical c2 ∧ IsCanonical c3 ∧ IsCanonical c4 <;>
    simp [h]

theorem decode_canonical_fp5_spec (bytes : Array U8 40#usize) :
    decode_canonical_fp5 bytes =
      decode_canonical_fp5_limbs
        (lePackU64At bytes.val 0) (lePackU64At bytes.val 8) (lePackU64At bytes.val 16)
        (lePackU64At bytes.val 24) (lePackU64At bytes.val 32) := by
  simp only [decode_canonical_fp5.public_eqs, load_le_u64_40_spec, bind_eq_result_bind,
    result_bind_ok]
  rfl

theorem decode_canonical_fp5_some_iff (bytes : Array U8 40#usize) (out : Fp5) :
    decode_canonical_fp5 bytes = .ok (some out) ↔
      IsCanonicalFp5 out ∧
      out = ⟨lePackU64At bytes.val 0, lePackU64At bytes.val 8, lePackU64At bytes.val 16,
             lePackU64At bytes.val 24, lePackU64At bytes.val 32⟩ := by
  rw [decode_canonical_fp5_spec, decode_canonical_fp5_limbs_some_iff]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, rfl⟩
    exact ⟨⟨h0, h1, h2, h3, h4⟩, rfl⟩
  · rintro ⟨⟨h0, h1, h2, h3, h4⟩, rfl⟩
    exact ⟨h0, h1, h2, h3, h4, rfl⟩

theorem decode_canonical_fp5_none_iff (bytes : Array U8 40#usize) :
    decode_canonical_fp5 bytes = .ok none ↔
      ¬ IsCanonicalFp5
        ⟨lePackU64At bytes.val 0, lePackU64At bytes.val 8, lePackU64At bytes.val 16,
         lePackU64At bytes.val 24, lePackU64At bytes.val 32⟩ := by
  rw [decode_canonical_fp5_spec, decode_canonical_fp5_limbs_none_iff]

theorem decode_canonical_gl24_limbs_spec (l0 l1 l2 l3 l4 l5 l6 : U64) :
    decode_canonical_gl24_limbs l0 l1 l2 l3 l4 l5 l6 =
      .ok (if IsCanonicalGl24 ⟨l0, l1, l2, l3, l4, l5, l6⟩
           then some ⟨l0, l1, l2, l3, l4, l5, l6⟩ else none) := by
  simp only [decode_canonical_gl24_limbs.public_eqs, IsCanonicalGl24]
  by_cases h0 : l0 < GOLDILOCKS_P
  · have hc0 := (lt_goldilocks_iff_isCanonical l0).mp h0
    by_cases h1 : l1 < GOLDILOCKS_P
    · have hc1 := (lt_goldilocks_iff_isCanonical l1).mp h1
      by_cases h2 : l2 < GOLDILOCKS_P
      · have hc2 := (lt_goldilocks_iff_isCanonical l2).mp h2
        by_cases h3 : l3 < GOLDILOCKS_P
        · have hc3 := (lt_goldilocks_iff_isCanonical l3).mp h3
          by_cases h4 : l4 < GOLDILOCKS_P
          · have hc4 := (lt_goldilocks_iff_isCanonical l4).mp h4
            by_cases h5 : l5 < GOLDILOCKS_P
            · have hc5 := (lt_goldilocks_iff_isCanonical l5).mp h5
              by_cases h6 : l6 < GOLDILOCKS_P
              · have hc6 := (lt_goldilocks_iff_isCanonical l6).mp h6
                simp [h0, h1, h2, h3, h4, h5, h6, hc0, hc1, hc2, hc3, hc4, hc5, hc6]
              · have hc6 : ¬ IsCanonical l6 := fun k => h6 ((lt_goldilocks_iff_isCanonical l6).mpr k)
                simp [h0, h1, h2, h3, h4, h5, h6, hc0, hc1, hc2, hc3, hc4, hc5, hc6]
            · have hc5 : ¬ IsCanonical l5 := fun k => h5 ((lt_goldilocks_iff_isCanonical l5).mpr k)
              simp [h0, h1, h2, h3, h4, h5, hc0, hc1, hc2, hc3, hc4, hc5]
          · have hc4 : ¬ IsCanonical l4 := fun k => h4 ((lt_goldilocks_iff_isCanonical l4).mpr k)
            simp [h0, h1, h2, h3, h4, hc0, hc1, hc2, hc3, hc4]
        · have hc3 : ¬ IsCanonical l3 := fun k => h3 ((lt_goldilocks_iff_isCanonical l3).mpr k)
          simp [h0, h1, h2, h3, hc0, hc1, hc2, hc3]
      · have hc2 : ¬ IsCanonical l2 := fun k => h2 ((lt_goldilocks_iff_isCanonical l2).mpr k)
        simp [h0, h1, h2, hc0, hc1, hc2]
    · have hc1 : ¬ IsCanonical l1 := fun k => h1 ((lt_goldilocks_iff_isCanonical l1).mpr k)
      simp [h0, h1, hc0, hc1]
  · have hc0 : ¬ IsCanonical l0 := fun k => h0 ((lt_goldilocks_iff_isCanonical l0).mpr k)
    simp [h0, hc0]

theorem decode_canonical_gl24_limbs_some_iff (l0 l1 l2 l3 l4 l5 l6 : U64) (out : Gl24Digest) :
    decode_canonical_gl24_limbs l0 l1 l2 l3 l4 l5 l6 = .ok (some out) ↔
      IsCanonicalGl24 ⟨l0, l1, l2, l3, l4, l5, l6⟩ ∧ out = ⟨l0, l1, l2, l3, l4, l5, l6⟩ := by
  rw [decode_canonical_gl24_limbs_spec]
  by_cases h : IsCanonicalGl24 ⟨l0, l1, l2, l3, l4, l5, l6⟩
  · simp [h, eq_comm]
  · simp [h]

theorem decode_canonical_gl24_limbs_none_iff (l0 l1 l2 l3 l4 l5 l6 : U64) :
    decode_canonical_gl24_limbs l0 l1 l2 l3 l4 l5 l6 = .ok none ↔
      ¬ IsCanonicalGl24 ⟨l0, l1, l2, l3, l4, l5, l6⟩ := by
  rw [decode_canonical_gl24_limbs_spec]
  by_cases h : IsCanonicalGl24 ⟨l0, l1, l2, l3, l4, l5, l6⟩ <;> simp [h]

theorem decode_canonical_gl24_digest_spec (bytes : Array U8 56#usize) :
    decode_canonical_gl24_digest bytes =
      decode_canonical_gl24_limbs
        (lePackU64At bytes.val 0) (lePackU64At bytes.val 8) (lePackU64At bytes.val 16)
        (lePackU64At bytes.val 24) (lePackU64At bytes.val 32) (lePackU64At bytes.val 40)
        (lePackU64At bytes.val 48) := by
  simp only [decode_canonical_gl24_digest.public_eqs, load_le_u64_56_spec, bind_eq_result_bind,
    result_bind_ok]
  rfl

theorem decode_canonical_gl24_digest_some_iff (bytes : Array U8 56#usize) (out : Gl24Digest) :
    decode_canonical_gl24_digest bytes = .ok (some out) ↔
      IsCanonicalGl24 out ∧
      out = ⟨lePackU64At bytes.val 0, lePackU64At bytes.val 8, lePackU64At bytes.val 16,
             lePackU64At bytes.val 24, lePackU64At bytes.val 32, lePackU64At bytes.val 40,
             lePackU64At bytes.val 48⟩ := by
  rw [decode_canonical_gl24_digest_spec, decode_canonical_gl24_limbs_some_iff]
  constructor
  · rintro ⟨hc, rfl⟩; exact ⟨hc, rfl⟩
  · rintro ⟨hc, rfl⟩; exact ⟨hc, rfl⟩

theorem decode_canonical_gl24_digest_none_iff (bytes : Array U8 56#usize) :
    decode_canonical_gl24_digest bytes = .ok none ↔
      ¬ IsCanonicalGl24
        ⟨lePackU64At bytes.val 0, lePackU64At bytes.val 8, lePackU64At bytes.val 16,
         lePackU64At bytes.val 24, lePackU64At bytes.val 32, lePackU64At bytes.val 40,
         lePackU64At bytes.val 48⟩ := by
  rw [decode_canonical_gl24_digest_spec, decode_canonical_gl24_limbs_none_iff]

/-! ## 2. `Fp5` Equality, OOD Pin Equality, Duet Folding, CWYZ Folding, & Dual Bridge Soundness -/

theorem fp5_eq_spec (x y : Fp5) : fp5_eq x y = .ok (decide (x = y)) := by
  cases x; cases y
  simp only [fp5_eq.public_eqs]
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

theorem fp5_eq_sound (x y : Fp5) : fp5_eq x y = .ok true ↔ x = y := by
  rw [fp5_eq_spec]
  simp

theorem verify_ood_pin_eq_fp5_spec (expected supplied : Fp5) :
    verify_ood_pin_eq_fp5 expected supplied = .ok (decide (expected = supplied)) := by
  simp only [verify_ood_pin_eq_fp5.public_eqs, fp5_eq_spec]

theorem verify_ood_pin_eq_fp5_sound (expected supplied : Fp5) :
    verify_ood_pin_eq_fp5 expected supplied = .ok true ↔ expected = supplied := by
  rw [verify_ood_pin_eq_fp5_spec]; simp

theorem verify_ood_pin_eq_fp5_false_iff (expected supplied : Fp5) :
    verify_ood_pin_eq_fp5 expected supplied = .ok false ↔ expected ≠ supplied := by
  rw [verify_ood_pin_eq_fp5_spec]; simp

theorem verify_affine_duet_fold_step_fp5_spec (v0 v1 : Fp5) (iy it : U64)
    (alpha claimed : Fp5) :
    verify_affine_duet_fold_step_fp5 v0 v1 iy it alpha claimed =
      .ok (decide (duetFp5Value v0 v1 iy it alpha = claimed)) := by
  simp only [verify_affine_duet_fold_step_fp5.public_eqs]
  rw [duet_fold_fp5_refines]
  simp [Result.bind, fp5_eq_spec]

theorem verify_affine_duet_fold_step_fp5_sound (v0 v1 : Fp5) (iy it : U64)
    (alpha claimed : Fp5) :
    verify_affine_duet_fold_step_fp5 v0 v1 iy it alpha claimed = .ok true ↔
      claimed = duetFp5Value v0 v1 iy it alpha := by
  rw [verify_affine_duet_fold_step_fp5_spec]
  simp [eq_comm]

theorem verify_affine_duet_fold_step_fp5_coset_sound
    {even odd : Fp5} {y0 iy it : U64} (alpha claimed : Fp5)
    (he : IsCanonicalFp5 even) (ho : IsCanonicalFp5 odd)
    (hit : fieldMul 2#u64 it = 1#u64)
    (hiy : fieldMul (fieldMul 2#u64 y0) iy = 1#u64) :
    verify_affine_duet_fold_step_fp5
        (fp5Add even (fp5Scale odd y0)) (fp5Sub even (fp5Scale odd y0))
        iy it alpha claimed = .ok true ↔
      claimed = fp5Add odd (fp5Mul alpha even) := by
  rw [verify_affine_duet_fold_step_fp5_sound, duet_fold_fp5_algebraic_sound alpha he ho hit hiy]

theorem duet_fold_fp5_coset_sound
    {even odd : Fp5} {y0 iy it : U64} (alpha : Fp5)
    (he : IsCanonicalFp5 even) (ho : IsCanonicalFp5 odd)
    (hit : fieldMul 2#u64 it = 1#u64)
    (hiy : fieldMul (fieldMul 2#u64 y0) iy = 1#u64) :
    duet_fold_fp5 (fp5Add even (fp5Scale odd y0)) (fp5Sub even (fp5Scale odd y0)) iy it alpha =
      .ok (fp5Add odd (fp5Mul alpha even)) := by
  rw [duet_fold_fp5_refines, duet_fold_fp5_algebraic_sound alpha he ho hit hiy]

theorem cwyz_duet_fold_fp5_coset_sound
    {even odd : Fp5} {y0 iy it : U64} (theta alpha beta : Fp5)
    (he : IsCanonicalFp5 even) (ho : IsCanonicalFp5 odd)
    (hit : fieldMul 2#u64 it = 1#u64)
    (hiy : fieldMul (fieldMul 2#u64 y0) iy = 1#u64) :
    cwyz_duet_fold_fp5 (fp5Add even (fp5Scale odd y0)) (fp5Sub even (fp5Scale odd y0))
        iy it (fieldMul y0 y0) theta alpha beta =
      .ok (fp5Add odd (fp5Mul (fp5Add alpha (fp5Scale beta (fieldMul y0 y0)))
        (fp5Add even (fp5Mul theta odd)))) := by
  rw [cwyz_duet_fold_fp5_refines, cwyz_duet_fold_fp5_algebraic_sound theta alpha beta he ho hit hiy]

theorem verify_cwyz_duet_fold_step_fp5_spec
    (v0 v1 : Fp5) (iy it yy : U64) (theta alpha beta claimed : Fp5) :
    verify_cwyz_duet_fold_step_fp5 v0 v1 iy it yy theta alpha beta claimed =
      .ok (decide (cwyzFp5Value v0 v1 iy it yy theta alpha beta = claimed)) := by
  simp only [verify_cwyz_duet_fold_step_fp5.public_eqs]
  rw [cwyz_duet_fold_fp5_refines]
  simp [Result.bind, fp5_eq_spec]

theorem verify_cwyz_duet_fold_step_fp5_sound
    (v0 v1 : Fp5) (iy it yy : U64) (theta alpha beta claimed : Fp5) :
    verify_cwyz_duet_fold_step_fp5 v0 v1 iy it yy theta alpha beta claimed = .ok true ↔
      claimed = cwyzFp5Value v0 v1 iy it yy theta alpha beta := by
  rw [verify_cwyz_duet_fold_step_fp5_spec]
  simp [eq_comm]

theorem verify_cwyz_duet_fold_step_fp5_coset_sound
    {even odd : Fp5} {y0 iy it : U64} (theta alpha beta claimed : Fp5)
    (he : IsCanonicalFp5 even) (ho : IsCanonicalFp5 odd)
    (hit : fieldMul 2#u64 it = 1#u64)
    (hiy : fieldMul (fieldMul 2#u64 y0) iy = 1#u64) :
    verify_cwyz_duet_fold_step_fp5
        (fp5Add even (fp5Scale odd y0)) (fp5Sub even (fp5Scale odd y0))
        iy it (fieldMul y0 y0) theta alpha beta claimed = .ok true ↔
      claimed = fp5Add odd (fp5Mul (fp5Add alpha (fp5Scale beta (fieldMul y0 y0)))
                  (fp5Add even (fp5Mul theta odd))) := by
  rw [verify_cwyz_duet_fold_step_fp5_sound, cwyz_duet_fold_fp5_algebraic_sound theta alpha beta he ho hit hiy]

theorem verify_cwyz_bridge_claim_step_fp5_spec
    (w0 w1 w2 w3 w4 claim phi theta alpha beta claimed_next : Fp5) :
    verify_cwyz_bridge_claim_step_fp5 w0 w1 w2 w3 w4 claim phi theta alpha beta claimed_next =
      .ok (decide (cwyzBridgeFp5Value w0 w1 w2 w3 w4 claim phi theta alpha beta = claimed_next)) := by
  simp only [verify_cwyz_bridge_claim_step_fp5.public_eqs]
  rw [cwyz_bridge_claim_step_fp5_refines]
  simp [Result.bind, fp5_eq_spec]

theorem verify_cwyz_bridge_claim_step_fp5_sound
    (w0 w1 w2 w3 w4 claim phi theta alpha beta claimed_next : Fp5) :
    verify_cwyz_bridge_claim_step_fp5 w0 w1 w2 w3 w4 claim phi theta alpha beta claimed_next = .ok true ↔
      claimed_next = cwyzBridgeFp5Value w0 w1 w2 w3 w4 claim phi theta alpha beta := by
  rw [verify_cwyz_bridge_claim_step_fp5_spec]
  simp [eq_comm]

theorem verify_cwyz_bridge_claim_step_fp5_dual_sound
    (a0 a1 b0 b1 kn phi theta alpha beta claimed_next : Fp5) :
    verify_cwyz_bridge_claim_step_fp5
        (fp5Mul a0 b0) (fp5Mul a0 b1) (fp5Mul a1 b0) (fp5Mul a0 kn) (fp5Mul a1 kn)
        (fp5Add (fp5Mul a0 b0) (fp5Mul a1 b1)) phi theta alpha beta claimed_next = .ok true ↔
      claimed_next = fp5Add
        (fp5Mul (fp5Add a1 (fp5Mul alpha (fp5Add a0 (fp5Mul theta a1)))) (fp5Add b0 (fp5Mul phi b1)))
        (fp5Mul (fp5Mul beta (fp5Add a0 (fp5Mul theta a1))) kn) := by
  rw [verify_cwyz_bridge_claim_step_fp5_sound, cwyz_bridge_claim_step_fp5_dual_sound]

theorem cwyz_bridge_claim_step_fp5_dual_spec
    (a0 a1 b0 b1 kn phi theta alpha beta : Fp5) :
    cwyz_bridge_claim_step_fp5
        (fp5Mul a0 b0) (fp5Mul a0 b1) (fp5Mul a1 b0) (fp5Mul a0 kn) (fp5Mul a1 kn)
        (fp5Add (fp5Mul a0 b0) (fp5Mul a1 b1)) phi theta alpha beta =
      .ok (fp5Add
        (fp5Mul (fp5Add a1 (fp5Mul alpha (fp5Add a0 (fp5Mul theta a1)))) (fp5Add b0 (fp5Mul phi b1)))
        (fp5Mul (fp5Mul beta (fp5Add a0 (fp5Mul theta a1))) kn)) := by
  rw [cwyz_bridge_claim_step_fp5_refines, cwyz_bridge_claim_step_fp5_dual_sound]

theorem eval_quadratic_sumcheck_wire_fp5_hypercube_spec
    (c0 c2 sum_claim : Fp5) (hs : IsCanonicalFp5 sum_claim) :
    ∃ y0 y1,
      eval_quadratic_sumcheck_wire_fp5 c0 c2 sum_claim fp5Zero = .ok y0 ∧
      eval_quadratic_sumcheck_wire_fp5 c0 c2 sum_claim fp5One = .ok y1 ∧
      fp5Add y0 y1 = sum_claim :=
  ⟨quadraticWireFp5Value c0 c2 sum_claim fp5Zero,
   quadraticWireFp5Value c0 c2 sum_claim fp5One,
   eval_quadratic_sumcheck_wire_fp5_refines c0 c2 sum_claim fp5Zero,
   eval_quadratic_sumcheck_wire_fp5_refines c0 c2 sum_claim fp5One,
   eval_quadratic_sumcheck_wire_fp5_hypercube_sum c0 c2 sum_claim hs⟩

/-! ## 3. Arbitrary-Slice Horner Evaluation & Polynomial Pin Verification over `Fp5` -/

private theorem list_take_succ_eq {α : Type} (xs : List α) (k : Nat) (hk : k < xs.length) :
    xs.take (k + 1) = xs.take k ++ [xs[k]'hk] := by
  induction xs generalizing k with
  | nil => cases hk
  | cons x rest ih =>
    cases k with
    | zero => rfl
    | succ k' =>
      have hk' : k' < rest.length := Nat.lt_of_succ_lt_succ hk
      show x :: rest.take (k' + 1) = x :: rest.take k' ++ [rest[k']'hk']
      rw [ih k' hk', List.cons_append]

private theorem eval_fp5_univariate_loop_fuel
    (coeffs : Slice Fp5) (z : U64) (k : Nat)
    (hk : k ≤ coeffs.val.length) (acc : Fp5) (rem : Usize) (hrem : rem.val = k) :
    loopFuel (k + 1)
      (fun (acc1, rem1) => eval_fp5_univariate_at_base_loop.body coeffs z acc1 rem1)
      (acc, rem) = .ok (hornerSpec (coeffs.val.take k) z acc) := by
  induction k generalizing acc rem with
  | zero =>
    have hgt : ¬ (rem > 0#usize) := by
      simp [GT.gt, UScalar.lt_iff_val, hrem]
    have hbody : eval_fp5_univariate_at_base_loop.body coeffs z acc rem = .ok (.done acc) := by
      simp only [eval_fp5_univariate_at_base_loop.body.public_eqs]
      simp only [hgt, ↓reduceIte, pure_eq_ok]
    rw [loopFuel_succ]
    dsimp only
    rw [hbody]
    rfl
  | succ k' ih =>
    have hk' : k' < coeffs.val.length := hk
    have hgt : rem > 0#usize := by
      change 0 < rem.val
      omega
    have hsub_le : (1#usize).val ≤ rem.val := by
      have h1 : (1#usize).val = 1 := rfl
      omega
    let rem1 : Usize := ⟨rem.bv - (1#usize).bv⟩
    have hsub : (rem - 1#usize : Result Usize) = .ok rem1 := by
      simp only [hSub_uscalar_eq, hsub_le, ↓reduceIte]
      rfl
    have hrem1 : rem1.val = k' := by
      have hv : rem1.val = rem.val - 1 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr hsub_le)
      have h1 : (1#usize).val = 1 := rfl
      omega
    have hidx : Slice.index_usize coeffs rem1 = .ok (coeffs.val[k']'hk') := by
      simp only [Slice.index_usize, hrem1, dite_eq_left hk']
    have hbody : eval_fp5_univariate_at_base_loop.body coeffs z acc rem =
        .ok (.cont (fp5Add (fp5Scale acc z) (coeffs.val[k']'hk'), rem1)) := by
      simp only [eval_fp5_univariate_at_base_loop.body.public_eqs]
      simp only [hgt, ↓reduceIte, hsub, bind_eq_result_bind, result_bind_ok,
        hidx, fp5_scale_refines, copy_fp5_spec, fp5_add_refines, pure_eq_ok]
    rw [loopFuel_succ]
    dsimp only
    rw [hbody, result_bind_ok]
    dsimp only
    rw [ih (Nat.le_of_lt hk') (fp5Add (fp5Scale acc z) (coeffs.val[k']'hk')) rem1 hrem1]
    congr 1
    unfold hornerSpec
    rw [list_take_succ_eq coeffs.val k' hk', List.foldr_append]
    rfl

theorem eval_fp5_univariate_at_base_spec (coeffs : Slice Fp5) (z : U64) :
    eval_fp5_univariate_at_base coeffs z = .ok (hornerSpec coeffs.val z fp5Zero) := by
  simp only [eval_fp5_univariate_at_base.public_eqs, fp5_zero_refines,
    eval_fp5_univariate_at_base_loop.public_eqs, bind_eq_result_bind, result_bind_ok]
  have hfuel : coeffs.val.length + 1 ≤ loopMaxFuel := by
    have hlen : (Slice.len coeffs).val = coeffs.val.length := Slice.len_val coeffs
    rw [← hlen]
    exact usize_lt_loopMaxFuel (Slice.len coeffs)
  have hloop := eval_fp5_univariate_loop_fuel coeffs z coeffs.val.length (Nat.le_refl _)
    fp5Zero (Slice.len coeffs) (Slice.len_val coeffs)
  rw [List.take_length] at hloop
  exact loop_ok_of_loopFuel hfuel hloop

theorem eval_fp5_univariate_at_base_ascending_sound (coeffs : Slice Fp5) (z : U64)
    (hcan : ∀ c ∈ coeffs.val, IsCanonicalFp5 c) :
    eval_fp5_univariate_at_base coeffs z = .ok (evalPolyAscending coeffs.val z) := by
  rw [eval_fp5_univariate_at_base_spec, hornerSpec_eq_evalPolyAscending coeffs.val z hcan]

theorem verify_fp5_univariate_at_base_pin_spec
    (coeffs : Slice Fp5) (z : U64) (expected : Fp5) :
    verify_fp5_univariate_at_base_pin coeffs z expected =
      .ok (decide (hornerSpec coeffs.val z fp5Zero = expected)) := by
  simp only [verify_fp5_univariate_at_base_pin.public_eqs]
  rw [eval_fp5_univariate_at_base_spec]
  simp [Result.bind, fp5_eq_spec]

theorem verify_fp5_univariate_at_base_pin_sound
    (coeffs : Slice Fp5) (z : U64) (expected : Fp5) :
    verify_fp5_univariate_at_base_pin coeffs z expected = .ok true ↔
      expected = hornerSpec coeffs.val z fp5Zero := by
  rw [verify_fp5_univariate_at_base_pin_spec]
  simp [eq_comm]

theorem verify_fp5_univariate_at_base_pin_ascending_sound
    (coeffs : Slice Fp5) (z : U64) (expected : Fp5)
    (hcan : ∀ c ∈ coeffs.val, IsCanonicalFp5 c) :
    verify_fp5_univariate_at_base_pin coeffs z expected = .ok true ↔
      expected = evalPolyAscending coeffs.val z := by
  rw [verify_fp5_univariate_at_base_pin_sound, hornerSpec_eq_evalPolyAscending coeffs.val z hcan]

/-! ## 4. Canonical Query Group Reduction & Canopy Merkle Ordering (`400`-bit & `Gl24`) -/

private theorem testBit_low_mask (n i : Nat) :
    Nat.testBit (2 ^ n - 1) i = decide (i < n) := by
  induction n generalizing i with
  | zero =>
    change Nat.testBit 0 i = false
    exact Nat.zero_testBit i
  | succ n ih =>
    have hp := Nat.two_pow_pos n
    have hshape : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 := by
      rw [Nat.pow_succ]; omega
    cases i with
    | zero =>
      rw [hshape, Nat.testBit_zero]
      have hm : (2 * (2 ^ n - 1) + 1) % 2 = 1 := by omega
      simp only [hm, Nat.zero_lt_succ, decide_true]
    | succ i =>
      rw [hshape, Nat.testBit_succ]
      have hd : (2 * (2 ^ n - 1) + 1) / 2 = 2 ^ n - 1 := by omega
      rw [hd, ih]
      simp only [Nat.succ_lt_succ_iff]

private theorem and_low_mask_eq_mod (x n : Nat) :
    x &&& (2 ^ n - 1) = x % 2 ^ n := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, testBit_low_mask, Nat.testBit_mod_two_pow]
  exact Bool.and_comm _ _

theorem canonical_query_group_idx_spec (raw groups : U64) :
    canonical_query_group_idx raw groups =
      .ok (if groups.val = 0 then none else some (UScalar.ofNat .U64 (raw.val % groups.val))) := by
  simp only [canonical_query_group_idx.public_eqs]
  by_cases hg : groups = 0#u64
  · subst hg; rfl
  · have hnz : groups.val ≠ 0 := fun hz =>
      hg (UScalar.eq_of_val_eq (by change _ = 0; exact hz))
    have hmod : (raw % groups : Result U64) = .ok (UScalar.ofNat .U64 (raw.val % groups.val)) := by
      simp only [hMod_uscalar_eq, hnz, ↓reduceIte, Result.ok.injEq]
      apply UScalar.eq_of_val_eq
      have hlt : raw.val % groups.val < 2 ^ 64 :=
        Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero hnz)) groups.bv.isLt
      change (raw.bv % groups.bv).toNat = (BitVec.ofNat 64 (raw.val % groups.val)).toNat
      rw [BitVec.toNat_umod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    simp [hg, hnz, hmod, Result.bind]

theorem canonical_query_group_idx_some_iff (raw groups idx : U64) :
    canonical_query_group_idx raw groups = .ok (some idx) ↔
      0 < groups.val ∧ idx.val = raw.val % groups.val := by
  rw [canonical_query_group_idx_spec]
  by_cases hz : groups.val = 0
  · simp [hz]
  · have hpos : 0 < groups.val := Nat.pos_of_ne_zero hz
    have hlt : raw.val % groups.val < 2 ^ 64 := Nat.lt_trans (Nat.mod_lt _ hpos) groups.bv.isLt
    simp only [hz, ↓reduceIte, Result.ok.injEq, Option.some.injEq, hpos, true_and]
    constructor
    · intro h; rw [← h, UScalar.val_ofNat]; exact Nat.mod_eq_of_lt hlt
    · intro h; apply UScalar.eq_of_val_eq; rw [UScalar.val_ofNat, Nat.mod_eq_of_lt hlt]; exact h.symm

theorem canonical_query_group_idx_none_iff (raw groups : U64) :
    canonical_query_group_idx raw groups = .ok none ↔ groups = 0#u64 := by
  rw [canonical_query_group_idx_spec]
  by_cases hz : groups.val = 0
  · refine ⟨fun _ => UScalar.eq_of_val_eq (by change _ = 0; exact hz), fun _ => by simp [hz]⟩
  · simp [hz]; intro h; subst h; exact hz rfl

theorem canonical_query_group_idx_lt_groups (raw groups idx : U64)
    (h : canonical_query_group_idx raw groups = .ok (some idx)) : idx.val < groups.val := by
  obtain ⟨hpos, hv⟩ := (canonical_query_group_idx_some_iff raw groups idx).mp h
  rw [hv]
  exact Nat.mod_lt _ hpos

theorem step_merkle_pair_order_400_spec
    (idx : U64) (level : U32) (node sibling : Array U8 50#usize) :
    step_merkle_pair_order_400 idx level node sibling =
      .ok (if 64 ≤ level.val then none
           else if (idx.val >>> level.val) % 2 = 0
                then some { left := node, right := sibling }
                else some { left := sibling, right := node }) := by
  simp only [step_merkle_pair_order_400.public_eqs]
  have h64 : (64#u32).val = 64 := rfl
  by_cases hge : level >= 64#u32
  · have hge' : 64 ≤ level.val := by simpa only [ge_iff_le, UScalar.le_iff_val, h64] using hge
    simp [hge, hge']
  · have hlt : level.val < 64 := by
      simp only [ge_iff_le, UScalar.le_iff_val, h64] at hge; omega
    have hge' : ¬ (64 ≤ level.val) := by omega
    let shifted : U64 := ⟨idx.bv >>> level.val⟩
    have hshr : (idx >>> level : Result U64) = .ok shifted := by
      simp only [hShrU_uscalar_eq, UScalarTy.numBits_u64, hlt, ↓reduceIte]; rfl
    have hbit_val : (shifted &&& 1#u64).val = (idx.val >>> level.val) % 2 := by
      change ((idx.bv >>> level.val) &&& (1#u64).bv).toNat = (idx.val >>> level.val) % 2
      rw [BitVec.toNat_and, BitVec.toNat_ushiftRight]
      change (idx.val >>> level.val) &&& (2 ^ 1 - 1) = (idx.val >>> level.val) % 2
      exact and_low_mask_eq_mod (idx.val >>> level.val) 1
    simp only [hge, ↓reduceIte, hshr, bind_eq_result_bind, result_bind_ok, lift_eq_ok, hge']
    by_cases hb : (shifted &&& 1#u64) = 0#u64
    · have hm0 : (idx.val >>> level.val) % 2 = 0 := by rw [← hbit_val, hb]; rfl
      simp [hb, hm0]
    · have hmnz : (idx.val >>> level.val) % 2 ≠ 0 := by
        intro hz; apply hb; apply UScalar.eq_of_val_eq
        change (shifted &&& 1#u64).val = 0
        exact hbit_val.trans hz
      simp [hb, hmnz]

theorem step_merkle_pair_order_400_some_iff
    (idx : U64) (level : U32) (node sibling : Array U8 50#usize) (pair : MerklePair400) :
    step_merkle_pair_order_400 idx level node sibling = .ok (some pair) ↔
      level.val < 64 ∧
      (if (idx.val >>> level.val) % 2 = 0
       then pair.left = node ∧ pair.right = sibling
       else pair.left = sibling ∧ pair.right = node) := by
  rw [step_merkle_pair_order_400_spec]
  by_cases hge : 64 ≤ level.val
  · simp [hge]; omega
  · have hlt : level.val < 64 := by omega
    by_cases hb : (idx.val >>> level.val) % 2 = 0 <;>
      simp only [hge, ↓reduceIte, hb, Result.ok.injEq, Option.some.injEq, hlt, true_and]
    · exact ⟨fun h => by subst h; exact ⟨rfl, rfl⟩, fun ⟨hl, hr⟩ => (MerklePair400.ext hl hr).symm⟩
    · exact ⟨fun h => by subst h; exact ⟨rfl, rfl⟩, fun ⟨hl, hr⟩ => (MerklePair400.ext hl hr).symm⟩

theorem step_merkle_pair_order_400_none_iff
    (idx : U64) (level : U32) (node sibling : Array U8 50#usize) :
    step_merkle_pair_order_400 idx level node sibling = .ok none ↔ 64 ≤ level.val := by
  rw [step_merkle_pair_order_400_spec]
  by_cases hge : 64 ≤ level.val
  · simp [hge]
  · by_cases hb : (idx.val >>> level.val) % 2 = 0 <;> simp [hge, hb]

theorem step_merkle_pair_order_gl24_spec
    (idx : U64) (level : U32) (node sibling : Gl24Digest) :
    step_merkle_pair_order_gl24 idx level node sibling =
      .ok (if 64 ≤ level.val then none
           else if IsCanonicalGl24 node ∧ IsCanonicalGl24 sibling then
             if (idx.val >>> level.val) % 2 = 0
             then some { left := node, right := sibling }
             else some { left := sibling, right := node }
           else none) := by
  simp only [step_merkle_pair_order_gl24.public_eqs]
  have h64 : (64#u32).val = 64 := rfl
  by_cases hge : level >= 64#u32
  · have hge' : 64 ≤ level.val := by simpa only [ge_iff_le, UScalar.le_iff_val, h64] using hge
    simp [hge, hge']
  · have hlt : level.val < 64 := by
      simp only [ge_iff_le, UScalar.le_iff_val, h64] at hge; omega
    have hge' : ¬ (64 ≤ level.val) := by omega
    cases node with | mk n0 n1 n2 n3 n4 n5 n6 =>
    cases sibling with | mk s0 s1 s2 s3 s4 s5 s6 =>
    simp only [hge, hge', ↓reduceIte, decode_canonical_gl24_limbs_spec,
      bind_eq_result_bind, result_bind_ok]
    by_cases hn : IsCanonicalGl24 ⟨n0, n1, n2, n3, n4, n5, n6⟩
    · by_cases hs : IsCanonicalGl24 ⟨s0, s1, s2, s3, s4, s5, s6⟩
      · let shifted : U64 := ⟨idx.bv >>> level.val⟩
        have hshr : (idx >>> level : Result U64) = .ok shifted := by
          simp only [hShrU_uscalar_eq, UScalarTy.numBits_u64, hlt, ↓reduceIte]; rfl
        have hbit_val : (shifted &&& 1#u64).val = (idx.val >>> level.val) % 2 := by
          change ((idx.bv >>> level.val) &&& (1#u64).bv).toNat = (idx.val >>> level.val) % 2
          rw [BitVec.toNat_and, BitVec.toNat_ushiftRight]
          change (idx.val >>> level.val) &&& (2 ^ 1 - 1) = (idx.val >>> level.val) % 2
          exact and_low_mask_eq_mod (idx.val >>> level.val) 1
        rw [ite_eq_left hn]; dsimp only
        rw [ite_eq_left hs]; dsimp only
        rw [ite_eq_left ⟨hn, hs⟩]
        simp only [hshr, result_bind_ok, lift_eq_ok]
        by_cases hb : (shifted &&& 1#u64) = 0#u64
        · have hm0 : (idx.val >>> level.val) % 2 = 0 := by rw [← hbit_val, hb]; rfl
          simp [hb, hm0]
        · have hmnz : (idx.val >>> level.val) % 2 ≠ 0 := by
            intro hz; apply hb; apply UScalar.eq_of_val_eq
            change (shifted &&& 1#u64).val = 0
            exact hbit_val.trans hz
          simp [hb, hmnz]
      · rw [ite_eq_left hn]; dsimp only
        rw [ite_eq_right hs]; dsimp only
        rw [ite_eq_right (fun h => hs h.2)]
    · rw [ite_eq_right hn]; dsimp only
      rw [ite_eq_right (fun h => hn h.1)]

theorem step_merkle_pair_order_gl24_some_iff
    (idx : U64) (level : U32) (node sibling : Gl24Digest) (pair : MerklePairGl24) :
    step_merkle_pair_order_gl24 idx level node sibling = .ok (some pair) ↔
      level.val < 64 ∧ IsCanonicalGl24 node ∧ IsCanonicalGl24 sibling ∧
      (if (idx.val >>> level.val) % 2 = 0
       then pair.left = node ∧ pair.right = sibling
       else pair.left = sibling ∧ pair.right = node) := by
  rw [step_merkle_pair_order_gl24_spec]
  by_cases hge : 64 ≤ level.val
  · simp [hge]; omega
  · have hlt : level.val < 64 := by omega
    rw [ite_eq_right hge]
    by_cases hc : IsCanonicalGl24 node ∧ IsCanonicalGl24 sibling
    · rw [ite_eq_left hc]
      rcases hc with ⟨hn, hs⟩
      cases pair with | mk pl pr =>
      by_cases hb : (idx.val >>> level.val) % 2 = 0 <;> simp only [hb, ↓reduceIte, Result.ok.injEq, Option.some.injEq]
      · exact ⟨fun h => ⟨hlt, hn, hs, (congrArg MerklePairGl24.left h).symm, (congrArg MerklePairGl24.right h).symm⟩,
               fun ⟨_, _, _, hl, hr⟩ => by cases hl; cases hr; rfl⟩
      · exact ⟨fun h => ⟨hlt, hn, hs, (congrArg MerklePairGl24.left h).symm, (congrArg MerklePairGl24.right h).symm⟩,
               fun ⟨_, _, _, hl, hr⟩ => by cases hl; cases hr; rfl⟩
    · rw [ite_eq_right hc]
      simp only [Result.ok.injEq, reduceCtorEq, false_iff]
      rintro ⟨_, hn, hs, _⟩
      exact hc ⟨hn, hs⟩

theorem step_merkle_pair_order_gl24_none_iff
    (idx : U64) (level : U32) (node sibling : Gl24Digest) :
    step_merkle_pair_order_gl24 idx level node sibling = .ok none ↔
      64 ≤ level.val ∨ ¬ (IsCanonicalGl24 node ∧ IsCanonicalGl24 sibling) := by
  rw [step_merkle_pair_order_gl24_spec]
  by_cases hge : 64 ≤ level.val
  · simp [hge]
  · by_cases hc : IsCanonicalGl24 node ∧ IsCanonicalGl24 sibling
    · by_cases hb : (idx.val >>> level.val) % 2 = 0 <;> simp [hge, hc, hb]
    · simp [hge, hc]

/-! ## 5. Overflow-Free Quorum Weight Summation (`checked_quorum_sum`) -/

@[expose] def natSumU64 (xs : List U64) : Nat :=
  xs.foldl (fun acc x => acc + x.val) 0

@[expose] def QuorumSumSpec
    (counts minimums : List U64) (minimum_global : U64) (sum : Nat) : Prop :=
  counts ≠ [] ∧
  counts.length = minimums.length ∧
  0 < minimum_global.val ∧
  (∀ j (hc : j < counts.length) (hm : j < minimums.length),
    0 < (minimums[j]'hm).val ∧ (minimums[j]'hm).val ≤ (counts[j]'hc).val) ∧
  sum = natSumU64 counts ∧
  sum ≤ 18446744073709551615 ∧
  minimum_global.val ≤ sum

private theorem list_drop_eq_cons {α : Type} (xs : List α) (k : Nat) (hk : k < xs.length) :
    xs.drop k = (xs[k]'hk) :: xs.drop (k + 1) := by
  induction xs generalizing k with
  | nil => cases hk
  | cons x rest ih =>
    cases k with
    | zero => rfl
    | succ k' => exact ih k' (Nat.lt_of_succ_lt_succ hk)

private def quorumSuffixPure
    (cs ms : List U64) (minG : U64) (total minTotal : Nat) : Option U64 :=
  match cs, ms with
  | [], [] =>
    if total < minG.val then none else some (UScalar.ofNat .U64 total)
  | c :: cs', m :: ms' =>
    if m.val = 0 then none
    else if c.val < m.val then none
    else if total + c.val > 18446744073709551615 then none
    else if minTotal + m.val > 18446744073709551615 then none
    else quorumSuffixPure cs' ms' minG (total + c.val) (minTotal + m.val)
  | _, _ => none
termination_by structural cs

private theorem checked_quorum_sum_loop_fuel
    (counts minimums : Slice U64) (minG : U64)
    (hlen : counts.val.length = minimums.val.length)
    (rem : Nat) (total min_total : U64) (i : Usize)
    (hi : i.val + rem = counts.val.length) :
    loopFuel (rem + 1)
      (fun (t1, mt1, i1) => checked_quorum_sum_loop.body counts minimums minG t1 mt1 i1)
      (total, min_total, i) =
      .ok (quorumSuffixPure (counts.val.drop i.val) (minimums.val.drop i.val)
            minG total.val min_total.val) := by
  induction rem generalizing total min_total i with
  | zero =>
    have hi_eq : i.val = counts.val.length := by omega
    have hlt : ¬ (i < Slice.len counts) := by
      simp [UScalar.lt_iff_val, Slice.len_val, hi_eq]
    have hdc : counts.val.drop i.val = [] := by rw [hi_eq, List.drop_length]
    have hdm : minimums.val.drop i.val = [] := by rw [hi_eq, hlen, List.drop_length]
    rw [loopFuel_succ, hdc, hdm]
    dsimp only [quorumSuffixPure]
    by_cases hmin : total < minG
    · have hmin' : total.val < minG.val := by simpa only [UScalar.lt_iff_val] using hmin
      have hbody : checked_quorum_sum_loop.body counts minimums minG total min_total i =
          .ok (.done none) := by
        simp only [checked_quorum_sum_loop.body.public_eqs]
        simp only [hlt, ↓reduceIte, hmin]
      rw [hbody, result_bind_ok]
      simp [hmin']
    · have hmin' : ¬ (total.val < minG.val) := by simpa only [UScalar.lt_iff_val] using hmin
      have htot : UScalar.ofNat .U64 total.val = total := by
        apply UScalar.eq_of_val_eq
        rw [UScalar.val_ofNat, UScalarTy.numBits_u64, Nat.mod_eq_of_lt total.bv.isLt]
      have hbody : checked_quorum_sum_loop.body counts minimums minG total min_total i =
          .ok (.done (some total)) := by
        simp only [checked_quorum_sum_loop.body.public_eqs]
        simp only [hlt, ↓reduceIte, hmin]
      rw [hbody, result_bind_ok]
      simp [hmin', htot]
  | succ rem' ih =>
    have hilt_c : i.val < counts.val.length := by omega
    have hilt_m : i.val < minimums.val.length := by omega
    have hlt_u : i < Slice.len counts := by
      simp [UScalar.lt_iff_val, Slice.len_val, hilt_c]
    let c := counts.val[i.val]'hilt_c
    let m := minimums.val[i.val]'hilt_m
    have hidx_c : Slice.index_usize counts i = .ok c := by
      simp only [Slice.index_usize, dite_eq_left hilt_c, c]
    have hidx_m : Slice.index_usize minimums i = .ok m := by
      simp only [Slice.index_usize, dite_eq_left hilt_m, m]
    have hdc : counts.val.drop i.val = c :: counts.val.drop (i.val + 1) :=
      list_drop_eq_cons counts.val i.val hilt_c
    have hdm : minimums.val.drop i.val = m :: minimums.val.drop (i.val + 1) :=
      list_drop_eq_cons minimums.val i.val hilt_m
    rw [loopFuel_succ, hdc, hdm]
    dsimp only [quorumSuffixPure]
    by_cases hm0 : m = 0#u64
    · have hm0' : m.val = 0 := by rw [hm0]; rfl
      have hbody : checked_quorum_sum_loop.body counts minimums minG total min_total i =
          .ok (.done none) := by
        simp only [checked_quorum_sum_loop.body.public_eqs]
        simp only [hlt_u, ↓reduceIte, hidx_c, hidx_m, bind_eq_result_bind, result_bind_ok, hm0]
      rw [hbody, result_bind_ok]
      simp [hm0']
    · have hm0' : m.val ≠ 0 := fun hz => hm0 (UScalar.eq_of_val_eq (by change _ = 0; exact hz))
      by_cases hcm : c < m
      · have hcm' : c.val < m.val := by simpa only [UScalar.lt_iff_val] using hcm
        have hbody : checked_quorum_sum_loop.body counts minimums minG total min_total i =
             .ok (.done none) := by
          simp only [checked_quorum_sum_loop.body.public_eqs]
          simp only [hlt_u, ↓reduceIte, hidx_c, hidx_m, bind_eq_result_bind, result_bind_ok,
            hm0, hcm]
        rw [hbody, result_bind_ok]
        simp [hm0', hcm']
      · have hcm' : ¬ (c.val < m.val) := by simpa only [UScalar.lt_iff_val] using hcm
        have hc_le_max : c.val ≤ MAX_U64_WORD.val := by
          rw [max_u64_word_val]; have hc64 : c.val < 2 ^ 64 := c.bv.isLt; omega
        obtain ⟨cap_c, hcap_c⟩ : ∃ cap_c : U64, cap_c.bv = MAX_U64_WORD.bv - c.bv :=
          ⟨⟨MAX_U64_WORD.bv - c.bv⟩, rfl⟩
        have hsub_c : (MAX_U64_WORD - c : Result U64) = .ok cap_c := by
          simp only [hSub_uscalar_eq, hc_le_max, ↓reduceIte]
          exact congrArg Result.ok (UScalar.ext hcap_c.symm)
        have hcap_c_val : cap_c.val = 18446744073709551615 - c.val := by
          calc
            cap_c.val = MAX_U64_WORD.val - c.val :=
              (congrArg BitVec.toNat hcap_c).trans
                (BitVec.toNat_sub_of_le (BitVec.le_def.mpr hc_le_max))
            _ = 18446744073709551615 - c.val := by rw [max_u64_word_val]
        have hc64 : c.val < 2 ^ 64 := c.bv.isLt
        have htot64 : total.val < 2 ^ 64 := total.bv.isLt
        by_cases htc : total > cap_c
        · have htc' : total.val + c.val > 18446744073709551615 := by
            have hv : cap_c.val < total.val := by simpa only [GT.gt, UScalar.lt_iff_val] using htc
            omega
          have hbody : checked_quorum_sum_loop.body counts minimums minG total min_total i =
              .ok (.done none) := by
            simp only [checked_quorum_sum_loop.body.public_eqs]
            simp only [hlt_u, ↓reduceIte, hidx_c, hidx_m, bind_eq_result_bind, result_bind_ok,
              hm0, Bool.false_eq_true, hcm, hsub_c, htc]
          rw [hbody, result_bind_ok]
          simp [hm0', hcm', htc']
        · have htc' : ¬ (total.val + c.val > 18446744073709551615) := by
            have hv : ¬ (cap_c.val < total.val) := by simpa only [GT.gt, UScalar.lt_iff_val] using htc
            omega
          have htc_lt : total.val + c.val < 2 ^ 64 := by omega
          let total1 : U64 := ⟨total.bv + c.bv⟩
          have hadd_t : (total + c : Result U64) = .ok total1 := by
            simp only [hAdd_uscalar_eq, UScalarTy.numBits_u64, htc_lt, ↓reduceIte]; rfl
          have htot1_val : total1.val = total.val + c.val := by
            change (total.bv + c.bv).toNat = total.val + c.val
            rw [BitVec.toNat_add, Nat.mod_eq_of_lt htc_lt]
          have hm64 : m.val < 2 ^ 64 := m.bv.isLt
          have hmt64 : min_total.val < 2 ^ 64 := min_total.bv.isLt
          have hm_le_max : m.val ≤ MAX_U64_WORD.val := by
            rw [max_u64_word_val]; omega
          obtain ⟨cap_m, hcap_m⟩ : ∃ cap_m : U64, cap_m.bv = MAX_U64_WORD.bv - m.bv :=
            ⟨⟨MAX_U64_WORD.bv - m.bv⟩, rfl⟩
          have hsub_m : (MAX_U64_WORD - m : Result U64) = .ok cap_m := by
            simp only [hSub_uscalar_eq, hm_le_max, ↓reduceIte]
            exact congrArg Result.ok (UScalar.ext hcap_m.symm)
          have hcap_m_val : cap_m.val = 18446744073709551615 - m.val := by
            calc
              cap_m.val = MAX_U64_WORD.val - m.val :=
                (congrArg BitVec.toNat hcap_m).trans
                  (BitVec.toNat_sub_of_le (BitVec.le_def.mpr hm_le_max))
              _ = 18446744073709551615 - m.val := by rw [max_u64_word_val]
          by_cases htm : min_total > cap_m
          · have htm' : min_total.val + m.val > 18446744073709551615 := by
              have hv : cap_m.val < min_total.val := by simpa only [GT.gt, UScalar.lt_iff_val] using htm
              omega
            have hbody : checked_quorum_sum_loop.body counts minimums minG total min_total i =
                .ok (.done none) := by
              simp only [checked_quorum_sum_loop.body.public_eqs]
              simp only [hlt_u, ↓reduceIte, hidx_c, hidx_m, bind_eq_result_bind, result_bind_ok,
                hm0, Bool.false_eq_true, hcm, hsub_c, htc, hadd_t, hsub_m, htm]
            rw [hbody, result_bind_ok]
            simp [hm0', hcm', htc', htm']
          · have htm' : ¬ (min_total.val + m.val > 18446744073709551615) := by
              have hv : ¬ (cap_m.val < min_total.val) := by simpa only [GT.gt, UScalar.lt_iff_val] using htm
              omega
            have htm_lt : min_total.val + m.val < 2 ^ 64 := by omega
            let min_total1 : U64 := ⟨min_total.bv + m.bv⟩
            have hadd_m : (min_total + m : Result U64) = .ok min_total1 := by
              simp only [hAdd_uscalar_eq, UScalarTy.numBits_u64, htm_lt, ↓reduceIte]; rfl
            have hmt1_val : min_total1.val = min_total.val + m.val := by
              change (min_total.bv + m.bv).toNat = min_total.val + m.val
              rw [BitVec.toNat_add, Nat.mod_eq_of_lt htm_lt]
            have hi_lt : i.val + (1#usize).val < 2 ^ 64 := by
              have hm_c := counts.property
              have h1 : (1#usize).val = 1 := rfl
              unfold Usize.max at hm_c; omega
            let i1 : Usize := ⟨i.bv + (1#usize).bv⟩
            have hadd_i : (i + 1#usize : Result Usize) = .ok i1 := by
              simp only [hAdd_uscalar_eq, UScalarTy.numBits_usize, hi_lt, ↓reduceIte]; rfl
            have hi1_val : i1.val = i.val + 1 := by
              change (i.bv + (1#usize).bv).toNat = i.val + 1
              rw [BitVec.toNat_add, Nat.mod_eq_of_lt hi_lt]; rfl
            have hbody : checked_quorum_sum_loop.body counts minimums minG total min_total i =
                .ok (.cont (total1, min_total1, i1)) := by
              simp only [checked_quorum_sum_loop.body.public_eqs]
              simp only [hlt_u, ↓reduceIte, hidx_c, hidx_m, bind_eq_result_bind, result_bind_ok,
                hm0, Bool.false_eq_true, hcm, hsub_c, htc, hadd_t, hsub_m, htm, hadd_m, hadd_i]
            rw [hbody, result_bind_ok]
            dsimp only
            simp only [hm0', hcm', htc', htm', ↓reduceIte]
            rw [ih total1 min_total1 i1 (by omega), hi1_val, htot1_val, hmt1_val]

private theorem foldl_u64_shift (xs : List U64) (acc : Nat) :
    xs.foldl (fun a x => a + x.val) acc = acc + natSumU64 xs := by
  induction xs generalizing acc with
  | nil => simp [natSumU64]
  | cons x rest ih =>
    unfold natSumU64
    simp only [List.foldl, Nat.zero_add]
    rw [ih (acc + x.val), ih x.val]
    omega

private theorem quorumSuffixPure_some_iff
    (cs ms : List U64) (minG : U64) (total minTotal : Nat) (out : U64)
    (hlen : cs.length = ms.length)
    (hle : minTotal ≤ total)
    (htot_max : total ≤ 18446744073709551615) :
    quorumSuffixPure cs ms minG total minTotal = some out ↔
      (∀ j (hc : j < cs.length) (hm : j < ms.length),
        0 < (ms[j]'hm).val ∧ (ms[j]'hm).val ≤ (cs[j]'hc).val) ∧
      out.val = total + natSumU64 cs ∧
      total + natSumU64 cs ≤ 18446744073709551615 ∧
      minG.val ≤ total + natSumU64 cs := by
  induction cs generalizing ms total minTotal with
  | nil =>
    cases ms with
    | cons _ _ => cases hlen
    | nil =>
      simp only [quorumSuffixPure, natSumU64, List.foldl, Nat.add_zero]
      constructor
      · intro h
        by_cases hlt : total < minG.val
        · simp [hlt] at h
        · simp [hlt] at h
          have hout : out.val = total := by
            rw [← h, UScalar.val_ofNat, UScalarTy.numBits_u64, Nat.mod_eq_of_lt (by omega)]
          exact ⟨fun j hc => False.elim (Nat.not_lt_zero j hc), hout, htot_max, by omega⟩
      · rintro ⟨_, hout, _, hmin⟩
        have hlt : ¬ (total < minG.val) := by omega
        simp only [hlt, ↓reduceIte, Option.some.injEq]
        apply UScalar.eq_of_val_eq
        rw [UScalar.val_ofNat, UScalarTy.numBits_u64, Nat.mod_eq_of_lt (by omega), hout]
  | cons c cs' ih =>
    cases ms with
    | nil => cases hlen
    | cons m ms' =>
      have hlen' : cs'.length = ms'.length := Nat.succ.inj hlen
      have hc_sum : natSumU64 (c :: cs') = c.val + natSumU64 cs' := by
        unfold natSumU64; simp only [List.foldl, Nat.zero_add]; exact foldl_u64_shift cs' c.val
      have hsum_cons : total + natSumU64 (c :: cs') = (total + c.val) + natSumU64 cs' := by
        rw [hc_sum]; omega
      simp only [quorumSuffixPure]
      constructor
      · intro h
        by_cases hm0 : m.val = 0
        · simp [hm0] at h
        · by_cases hcm : c.val < m.val
          · simp [hm0, hcm] at h
          · by_cases htc : total + c.val > 18446744073709551615
            · simp [hm0, hcm, htc] at h
            · by_cases htm : minTotal + m.val > 18446744073709551615
              · simp [hm0, hcm, htc, htm] at h
              · simp only [hm0, hcm, htc, htm, ↓reduceIte] at h
                obtain ⟨hrec_all, hout, hmax, hmin⟩ :=
                  ih ms' (total + c.val) (minTotal + m.val) hlen' (by omega) (by omega) |>.mp h
                refine ⟨?_, ?_, ?_, ?_⟩
                · intro j hc hm
                  cases j with
                  | zero =>
                    simp only [List.getElem_cons_zero]
                    exact ⟨Nat.pos_of_ne_zero hm0, by omega⟩
                  | succ j' =>
                    simpa only [List.getElem_cons_succ] using
                      hrec_all j' (Nat.lt_of_succ_lt_succ hc) (Nat.lt_of_succ_lt_succ hm)
                · rw [hsum_cons]; exact hout
                · rw [hsum_cons]; exact hmax
                · rw [hsum_cons]; exact hmin
      · rintro ⟨hall, hout, hmax, hmin⟩
        have h0 : 0 < m.val ∧ m.val ≤ c.val := by
          simpa only [List.getElem_cons_zero] using hall 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
        have hm0 : m.val ≠ 0 := by omega
        have hcm : ¬ (c.val < m.val) := by omega
        have htc_le : total + c.val ≤ 18446744073709551615 := by omega
        have htc : ¬ (total + c.val > 18446744073709551615) := by omega
        have htm : ¬ (minTotal + m.val > 18446744073709551615) := by omega
        simp only [hm0, hcm, htc, htm, ↓reduceIte]
        apply (ih ms' (total + c.val) (minTotal + m.val) hlen' (by omega) htc_le).mpr
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro j' hc' hm'
          simpa only [List.getElem_cons_succ] using
            hall (j' + 1) (Nat.succ_lt_succ hc') (Nat.succ_lt_succ hm')
        · rw [← hsum_cons]; exact hout
        · rw [← hsum_cons]; exact hmax
        · rw [← hsum_cons]; exact hmin

theorem checked_quorum_sum_total
    (counts minimums : Slice U64) (minimum_global : U64) :
    ∃ out : Option U64, checked_quorum_sum counts minimums minimum_global = .ok out := by
  simp only [checked_quorum_sum.public_eqs, core.slice.Slice.is_empty_eq,
    bind_eq_result_bind, result_bind_ok]
  by_cases hemp : counts.val.isEmpty
  · exact ⟨none, by simp [hemp]⟩
  · simp only [hemp, Bool.false_eq_true, ↓reduceIte]
    by_cases hne : Slice.len counts != Slice.len minimums
    · exact ⟨none, by simp [hne]⟩
    · have hlen : counts.val.length = minimums.val.length := by
        by_cases he : Slice.len counts = Slice.len minimums
        · simpa [Slice.len_val] using congrArg UScalar.val he
        · exact False.elim (hne (bne_iff_ne.mpr he))
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      by_cases hg0 : minimum_global = 0#u64
      · exact ⟨none, by simp [hg0]⟩
      · simp only [hg0, ↓reduceIte, checked_quorum_sum_loop.public_eqs]
        have hfuel : counts.val.length + 1 ≤ loopMaxFuel := by
          rw [← Slice.len_val counts]; exact usize_lt_loopMaxFuel (Slice.len counts)
        have h0u : (0#usize).val = 0 := rfl
        have hloop := checked_quorum_sum_loop_fuel counts minimums minimum_global hlen
          counts.val.length 0#u64 0#u64 0#usize (by omega)
        exact ⟨_, loop_ok_of_loopFuel hfuel hloop⟩

theorem checked_quorum_sum_sound
    (counts minimums : Slice U64) (minimum_global total : U64) :
    checked_quorum_sum counts minimums minimum_global = .ok (some total) ↔
      QuorumSumSpec counts.val minimums.val minimum_global total.val := by
  simp only [checked_quorum_sum.public_eqs, core.slice.Slice.is_empty_eq,
    bind_eq_result_bind, result_bind_ok]
  by_cases hemp : counts.val.isEmpty
  · have hnil : counts.val = [] := List.isEmpty_iff.mp hemp
    simp [hemp, hnil, QuorumSumSpec]
  · have hne_nil : counts.val ≠ [] := fun h => hemp (List.isEmpty_iff.mpr h)
    simp only [hemp, Bool.false_eq_true, ↓reduceIte]
    by_cases hne : Slice.len counts != Slice.len minimums
    · have hlen_ne : counts.val.length ≠ minimums.val.length := by
        intro heq
        have hu : Slice.len counts = Slice.len minimums :=
          UScalar.eq_of_val_eq (by simp [Slice.len_val, heq])
        exact (bne_iff_ne.mp hne) hu
      simp [hne, QuorumSumSpec, hlen_ne]
    · have hlen : counts.val.length = minimums.val.length := by
        by_cases he : Slice.len counts = Slice.len minimums
        · simpa [Slice.len_val] using congrArg UScalar.val he
        · exact False.elim (hne (bne_iff_ne.mpr he))
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      by_cases hg0 : minimum_global = 0#u64
      · simp only [hg0, ↓reduceIte, Result.ok.injEq, reduceCtorEq, false_iff]
        intro hs; exact Nat.not_lt_zero _ hs.2.2.1
      · have hg_pos : 0 < minimum_global.val :=
          Nat.pos_of_ne_zero (fun hz => hg0 (UScalar.eq_of_val_eq (by change _ = 0; exact hz)))
        simp only [hg0, ↓reduceIte, checked_quorum_sum_loop.public_eqs]
        have hfuel : counts.val.length + 1 ≤ loopMaxFuel := by
          rw [← Slice.len_val counts]; exact usize_lt_loopMaxFuel (Slice.len counts)
        have h0u : (0#usize).val = 0 := rfl
        have h064 : (0#u64).val = 0 := rfl
        have hloop := checked_quorum_sum_loop_fuel counts minimums minimum_global hlen
          counts.val.length 0#u64 0#u64 0#usize (by omega)
        have hrun := loop_ok_of_loopFuel hfuel hloop
        simp only [h0u, h064, List.drop_zero] at hrun
        rw [hrun]
        simp only [Result.ok.injEq]
        rw [quorumSuffixPure_some_iff counts.val minimums.val minimum_global 0 0 total
          hlen (Nat.le_refl 0) (by decide)]
        simp only [Nat.zero_add, QuorumSumSpec, hne_nil, hlen, hg_pos, true_and]
        exact ⟨fun ⟨hp, hs, hm, hg⟩ => ⟨hne_nil, hp, hs, hs.symm ▸ hm, hs.symm ▸ hg⟩,
               fun ⟨_, hp, hs, hm, hg⟩ => ⟨hp, hs, hs ▸ hm, hs ▸ hg⟩⟩

theorem checked_quorum_sum_none_iff
    (counts minimums : Slice U64) (minimum_global : U64) :
    checked_quorum_sum counts minimums minimum_global = .ok none ↔
      ¬ ∃ s : Nat, QuorumSumSpec counts.val minimums.val minimum_global s := by
  obtain ⟨out, hout⟩ := checked_quorum_sum_total counts minimums minimum_global
  cases out with
  | none =>
    simp only [hout, true_iff]
    rintro ⟨s, hs⟩
    have hlt64 : s < 2 ^ 64 := by have hm := hs.2.2.2.2.2.1; omega
    let u : U64 := UScalar.ofNat .U64 s
    have hu : u.val = s := by rw [UScalar.val_ofNat, UScalarTy.numBits_u64, Nat.mod_eq_of_lt hlt64]
    have hspec : QuorumSumSpec counts.val minimums.val minimum_global u.val := by simpa only [hu] using hs
    have hsome := (checked_quorum_sum_sound counts minimums minimum_global u).mpr hspec
    rw [hout] at hsome; cases hsome
  | some v =>
    simp only [hout, Result.ok.injEq, reduceCtorEq, false_iff]
    have hv := (checked_quorum_sum_sound counts minimums minimum_global v).mp hout
    exact fun hnot => hnot ⟨v.val, hv⟩

theorem checked_quorum_sum_le_max_u64_word
    (counts minimums : Slice U64) (minimum_global total : U64)
    (h : checked_quorum_sum counts minimums minimum_global = .ok (some total)) :
    natSumU64 counts.val ≤ MAX_U64_WORD.val := by
  obtain ⟨_, _, _, _, hsum, hle, _⟩ :=
    (checked_quorum_sum_sound counts minimums minimum_global total).mp h
  rw [max_u64_word_val, ← hsum]
  exact hle

/-! ## 6. `QSAGHQM2` Wire Envelope & Quintic Schedule Envelope Gates -/

abbrev Qsaghqm2HeaderSpec
    (magic : List U8) (profile_tag : U8)
    (active_signers num_validators declared_payload_len actual_payload_len : U64) : Prop :=
  magic = [81#u8, 83#u8, 65#u8, 71#u8, 72#u8, 81#u8, 77#u8, 50#u8] ∧
  (profile_tag = QSAGHQM2_PROFILE_TURBO400 ∨ profile_tag = QSAGHQM2_PROFILE_GL24) ∧
  0 < active_signers.val ∧
  active_signers.val ≤ num_validators.val ∧
  0 < declared_payload_len.val ∧
  declared_payload_len = actual_payload_len

abbrev QuinticScheduleEnvelopeSpec
    (log_cells early_stop_vars folded_vars_sum num_stages : U32) : Prop :=
  MIN_QUINTIC_LOG_CELLS.val ≤ log_cells.val ∧
  log_cells.val ≤ MAX_QUINTIC_LOG_CELLS.val ∧
  num_stages.val = (if log_cells.val ≤ 22 then 3 else 4) ∧
  1 ≤ early_stop_vars.val ∧
  early_stop_vars.val ≤ 8 ∧
  early_stop_vars.val + folded_vars_sum.val = log_cells.val

theorem verify_qsaghqm2_header_spec
    (magic : Array U8 8#usize) (profile_tag : U8)
    (active_signers num_validators declared_payload_len actual_payload_len : U64) :
    verify_qsaghqm2_header magic profile_tag active_signers num_validators
      declared_payload_len actual_payload_len =
      .ok (if Qsaghqm2HeaderSpec magic.val profile_tag active_signers num_validators
                declared_payload_len actual_payload_len
           then some { profile_tag, active_signers, payload_len := declared_payload_len }
           else none) := by
  rcases magic with ⟨ms, hms⟩
  have hlen8 : ms.length = 8 := hms
  rcases ms with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals try (exfalso; simp only [List.length_cons, List.length_nil] at hlen8; omega)
  have hi0 : Array.index_usize ⟨[b0, b1, b2, b3, b4, b5, b6, b7], hms⟩ 0#usize = .ok b0 := rfl
  have hi1 : Array.index_usize ⟨[b0, b1, b2, b3, b4, b5, b6, b7], hms⟩ 1#usize = .ok b1 := rfl
  have hi2 : Array.index_usize ⟨[b0, b1, b2, b3, b4, b5, b6, b7], hms⟩ 2#usize = .ok b2 := rfl
  have hi3 : Array.index_usize ⟨[b0, b1, b2, b3, b4, b5, b6, b7], hms⟩ 3#usize = .ok b3 := rfl
  have hi4 : Array.index_usize ⟨[b0, b1, b2, b3, b4, b5, b6, b7], hms⟩ 4#usize = .ok b4 := rfl
  have hi5 : Array.index_usize ⟨[b0, b1, b2, b3, b4, b5, b6, b7], hms⟩ 5#usize = .ok b5 := rfl
  have hi6 : Array.index_usize ⟨[b0, b1, b2, b3, b4, b5, b6, b7], hms⟩ 6#usize = .ok b6 := rfl
  have hi7 : Array.index_usize ⟨[b0, b1, b2, b3, b4, b5, b6, b7], hms⟩ 7#usize = .ok b7 := rfl
  simp only [verify_qsaghqm2_header.public_eqs, hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7,
    bind_eq_result_bind, result_bind_ok, Qsaghqm2HeaderSpec]
  have checkTail :
      (profile_tag = QSAGHQM2_PROFILE_TURBO400 ∨ profile_tag = QSAGHQM2_PROFILE_GL24) →
      (if active_signers = 0#u64 then (Result.ok none : Result (Option Qsaghqm2Header))
       else if active_signers > num_validators then Result.ok none
       else if declared_payload_len = 0#u64 then Result.ok none
       else if declared_payload_len != actual_payload_len then Result.ok none
       else Result.ok (some ({ profile_tag, active_signers, payload_len := declared_payload_len } : Qsaghqm2Header))) =
      Result.ok (if 0 < active_signers.val ∧ active_signers.val ≤ num_validators.val ∧
                    0 < declared_payload_len.val ∧ declared_payload_len = actual_payload_len
                 then some ({ profile_tag, active_signers, payload_len := declared_payload_len } : Qsaghqm2Header)
                 else none) := by
    intro _
    have h064 : (0#u64).val = 0 := rfl
    by_cases ha0 : active_signers = 0#u64
    · subst ha0; simp [h064]
    · have ha_pos : 0 < active_signers.val :=
        Nat.pos_of_ne_zero (fun hz => ha0 (UScalar.eq_of_val_eq hz))
      by_cases hgt : active_signers > num_validators
      · have hgt' : ¬ (active_signers.val ≤ num_validators.val) := by
          have hv : num_validators.val < active_signers.val := by
            simpa only [GT.gt, UScalar.lt_iff_val] using hgt
          omega
        simp [ha0, hgt, ha_pos, hgt']
      · have hle : active_signers.val ≤ num_validators.val := by
          simp only [GT.gt, UScalar.lt_iff_val] at hgt; omega
        by_cases hd0 : declared_payload_len = 0#u64
        · subst hd0; simp [ha0, hgt, ha_pos, hle, h064]
        · have hd_pos : 0 < declared_payload_len.val :=
            Nat.pos_of_ne_zero (fun hz => hd0 (UScalar.eq_of_val_eq hz))
          by_cases hne : declared_payload_len != actual_payload_len
          · have hne' : declared_payload_len ≠ actual_payload_len := bne_iff_ne.mp hne
            simp [ha0, hgt, hd0, hne, ha_pos, hle, hd_pos, hne']
          · have heq : declared_payload_len = actual_payload_len := by
              by_cases he : declared_payload_len = actual_payload_len
              · exact he
              · exact False.elim (hne (bne_iff_ne.mpr he))
            subst heq
            simp [ha0, hgt, hd0, bne_self_eq_false, ha_pos, hle, hd_pos]
  have bne_false_iff : ∀ (u v : U8), (u != v) = false ↔ u = v := by
    intro u v; constructor
    · intro h; by_cases he : u = v; exact he; exact False.elim (by rw [bne_iff_ne.mpr he] at h; cases h)
    · rintro rfl; exact bne_self_eq_false u
  cases hb0 : (b0 != 81#u8)
  · rw [bne_false_iff] at hb0; subst hb0
    cases hb1 : (b1 != 83#u8)
    · rw [bne_false_iff] at hb1; subst hb1
      cases hb2 : (b2 != 65#u8)
      · rw [bne_false_iff] at hb2; subst hb2
        cases hb3 : (b3 != 71#u8)
        · rw [bne_false_iff] at hb3; subst hb3
          cases hb4 : (b4 != 72#u8)
          · rw [bne_false_iff] at hb4; subst hb4
            cases hb5 : (b5 != 81#u8)
            · rw [bne_false_iff] at hb5; subst hb5
              cases hb6 : (b6 != 77#u8)
              · rw [bne_false_iff] at hb6; subst hb6
                cases hb7 : (b7 != 50#u8)
                · rw [bne_false_iff] at hb7; subst hb7
                  simp only [Bool.false_eq_true, ↓reduceIte, true_and]
                  cases hpt1 : (profile_tag != QSAGHQM2_PROFILE_TURBO400)
                  · have hp1 := (bne_false_iff _ _).mp hpt1
                    subst hp1
                    simp only [Bool.false_eq_true, ↓reduceIte, true_or, true_and]
                    exact checkTail (Or.inl rfl)
                  · have hp1 : profile_tag ≠ QSAGHQM2_PROFILE_TURBO400 := bne_iff_ne.mp hpt1
                    simp only [↓reduceIte, hp1, false_or]
                    cases hpt2 : (profile_tag != QSAGHQM2_PROFILE_GL24)
                    · have hp2 := (bne_false_iff _ _).mp hpt2
                      subst hp2
                      simp only [Bool.false_eq_true, ↓reduceIte, true_and]
                      exact checkTail (Or.inr rfl)
                    · have hp2 : profile_tag ≠ QSAGHQM2_PROFILE_GL24 := bne_iff_ne.mp hpt2
                      simp [hp2]
                · simp [bne_iff_ne.mp hb7]
              · simp [bne_iff_ne.mp hb6]
            · simp [bne_iff_ne.mp hb5]
          · simp [bne_iff_ne.mp hb4]
        · simp [bne_iff_ne.mp hb3]
      · simp [bne_iff_ne.mp hb2]
    · simp [bne_iff_ne.mp hb1]
  · simp [bne_iff_ne.mp hb0]

theorem verify_qsaghqm2_header_some_iff
    (magic : Array U8 8#usize) (profile_tag : U8)
    (active_signers num_validators declared_payload_len actual_payload_len : U64)
    (hdr : Qsaghqm2Header) :
    verify_qsaghqm2_header magic profile_tag active_signers num_validators
      declared_payload_len actual_payload_len = .ok (some hdr) ↔
      Qsaghqm2HeaderSpec magic.val profile_tag active_signers num_validators
        declared_payload_len actual_payload_len ∧
      hdr = { profile_tag, active_signers, payload_len := declared_payload_len } := by
  rw [verify_qsaghqm2_header_spec]
  by_cases hs : Qsaghqm2HeaderSpec magic.val profile_tag active_signers num_validators
      declared_payload_len actual_payload_len
  · simp [hs, eq_comm]
  · simp [hs]

theorem verify_qsaghqm2_header_none_iff
    (magic : Array U8 8#usize) (profile_tag : U8)
    (active_signers num_validators declared_payload_len actual_payload_len : U64) :
    verify_qsaghqm2_header magic profile_tag active_signers num_validators
      declared_payload_len actual_payload_len = .ok none ↔
      ¬ Qsaghqm2HeaderSpec magic.val profile_tag active_signers num_validators
          declared_payload_len actual_payload_len := by
  rw [verify_qsaghqm2_header_spec]
  by_cases hs : Qsaghqm2HeaderSpec magic.val profile_tag active_signers num_validators
      declared_payload_len actual_payload_len <;> simp [hs]

theorem verify_quintic_schedule_envelope_spec
    (log_cells early_stop_vars folded_vars_sum num_stages : U32) :
    verify_quintic_schedule_envelope log_cells early_stop_vars folded_vars_sum num_stages =
      .ok (decide (QuinticScheduleEnvelopeSpec log_cells early_stop_vars folded_vars_sum num_stages)) := by
  simp only [verify_quintic_schedule_envelope.public_eqs, QuinticScheduleEnvelopeSpec]
  have hmin16 : MIN_QUINTIC_LOG_CELLS.val = 16 := by rw [min_quintic_log_cells_val]; rfl
  have hmax28 : MAX_QUINTIC_LOG_CELLS.val = 28 := by rw [max_quintic_log_cells_val]; rfl
  by_cases hlo : log_cells < MIN_QUINTIC_LOG_CELLS
  · have hlo' : ¬ (MIN_QUINTIC_LOG_CELLS.val ≤ log_cells.val) := by
      have hv : log_cells.val < MIN_QUINTIC_LOG_CELLS.val := UScalar.lt_iff_val _ _ |>.mp hlo
      omega
    simp [hlo, hlo']
  · have hlo' : MIN_QUINTIC_LOG_CELLS.val ≤ log_cells.val := by
      rw [UScalar.lt_iff_val] at hlo; omega
    by_cases hhi : log_cells > MAX_QUINTIC_LOG_CELLS
    · have hhi' : ¬ (log_cells.val ≤ MAX_QUINTIC_LOG_CELLS.val) := by
        have hv : MAX_QUINTIC_LOG_CELLS.val < log_cells.val := by
          simpa only [GT.gt, UScalar.lt_iff_val] using hhi
        omega
      simp [hlo, hlo', hhi, hhi']
    · have hhi' : log_cells.val ≤ MAX_QUINTIC_LOG_CELLS.val := by
        simp only [GT.gt, UScalar.lt_iff_val] at hhi; omega
      have h22v : (22#u32).val = 22 := rfl
      have h8v : (8#u32).val = 8 := rfl
      have h3v : (3#u32).val = 3 := rfl
      have h4v : (4#u32).val = 4 := rfl
      have checkEarly :
          (if early_stop_vars = 0#u32 then Result.ok false
           else if (8#u32).val < early_stop_vars.val then Result.ok false
           else if log_cells.val < folded_vars_sum.val then Result.ok false
           else (early_stop_vars + folded_vars_sum).bind fun i => Result.ok (decide (i = log_cells))) =
          Result.ok (decide (1 ≤ early_stop_vars.val ∧ early_stop_vars.val ≤ 8 ∧
            early_stop_vars.val + folded_vars_sum.val = log_cells.val)) := by
        by_cases he0 : early_stop_vars = 0#u32
        · subst he0
          have h032 : (0#u32).val = 0 := rfl
          simp [h032]
        · have he_ge1 : 1 ≤ early_stop_vars.val := by
            have hnz : early_stop_vars.val ≠ 0 := fun hz => he0 (UScalar.eq_of_val_eq hz)
            omega
          by_cases he8 : 8 < early_stop_vars.val
          · have he8' : ¬ (early_stop_vars.val ≤ 8) := by omega
            simp [he0, h8v, he8, he_ge1, he8']
          · have he8' : early_stop_vars.val ≤ 8 := by omega
            by_cases hfv : log_cells.val < folded_vars_sum.val
            · have hfv' : ¬ (early_stop_vars.val + folded_vars_sum.val = log_cells.val) := by omega
              simp [he0, h8v, he8, hfv, he_ge1, he8', hfv']
            · have hfv_le : folded_vars_sum.val ≤ log_cells.val := by omega
              have hsum_lt : early_stop_vars.val + folded_vars_sum.val < 2 ^ 32 := by omega
              let s : U32 := ⟨early_stop_vars.bv + folded_vars_sum.bv⟩
              have hadd : (early_stop_vars + folded_vars_sum : Result U32) = .ok s := by
                simp only [hAdd_uscalar_eq, UScalarTy.numBits_u32, hsum_lt, ↓reduceIte]; rfl
              have hs_val : s.val = early_stop_vars.val + folded_vars_sum.val := by
                change (early_stop_vars.bv + folded_vars_sum.bv).toNat = _
                rw [BitVec.toNat_add, Nat.mod_eq_of_lt hsum_lt]
              simp only [he0, h8v, he8, hfv, ↓reduceIte, hadd, Result.bind, Result.ok.injEq,
                he_ge1, he8', true_and]
              exact decide_eq_decide.mpr ⟨fun h => by rw [← hs_val, h], fun h => UScalar.eq_of_val_eq (hs_val.trans h)⟩
      simp only [hlo, hhi, hlo', hhi', true_and, ↓reduceIte, UScalar.le_iff_val, GT.gt, UScalar.lt_iff_val,
        bind_eq_result_bind, result_bind_ok, bne_iff_ne]
      by_cases hle22 : log_cells.val ≤ 22
      · simp only [h22v, hle22, ↓reduceIte]
        by_cases hns : num_stages = 3#u32
        · subst hns; simp only [↓reduceIte, h3v, true_and]; exact checkEarly
        · have hns' : num_stages.val ≠ 3 := fun hv => hns (UScalar.eq_of_val_eq hv)
          simp [hns, hns']
      · simp only [h22v, hle22, ↓reduceIte]
        by_cases hns : num_stages = 4#u32
        · subst hns; simp only [↓reduceIte, h4v, true_and]; exact checkEarly
        · have hns' : num_stages.val ≠ 4 := fun hv => hns (UScalar.eq_of_val_eq hv)
          simp [hns, hns']

theorem verify_quintic_schedule_envelope_sound
    (log_cells early_stop_vars folded_vars_sum num_stages : U32) :
    verify_quintic_schedule_envelope log_cells early_stop_vars folded_vars_sum num_stages = .ok true ↔
      QuinticScheduleEnvelopeSpec log_cells early_stop_vars folded_vars_sum num_stages := by
  rw [verify_quintic_schedule_envelope_spec]; simp

theorem verify_quintic_schedule_envelope_le_max_canopy
    (log_cells early_stop_vars folded_vars_sum num_stages : U32)
    (h : verify_quintic_schedule_envelope log_cells early_stop_vars folded_vars_sum num_stages = .ok true) :
    folded_vars_sum.val < MAX_CANOPY_LOG_LEAVES.val := by
  obtain ⟨_, hhi, _, he1, _, hsum⟩ := (verify_quintic_schedule_envelope_sound _ _ _ _).mp h
  rw [max_quintic_log_cells_val] at hhi
  rw [max_canopy_log_leaves_val]
  change log_cells.val ≤ 28 at hhi
  change folded_vars_sum.val < 28
  omega

/-! ## 7. `#tooth` Mutation-Sensitivity & Premise-Inhabitedness Witnesses -/

/-- `#tooth`: Unchecked `% p` aliases `0` and `p`, whereas `decode_canonical_u64` rejects `p`. -/
theorem tooth_unchecked_mod_p_accepts_aliased_field_limb :
    (0#u64) ≠ GOLDILOCKS_P ∧
    (0#u64 % GOLDILOCKS_P : Result U64) = .ok 0#u64 ∧
    (GOLDILOCKS_P % GOLDILOCKS_P : Result U64) = .ok 0#u64 ∧
    decode_canonical_u64 GOLDILOCKS_P = .ok none := by
  simp only [decode_canonical_u64.public_eqs, GOLDILOCKS_P.public_eqs]
  decide

private theorem u8_cast_u64_bv (b : U8) :
    (UScalar.cast .U64 b).bv = BitVec.ofNat 64 b.val := by
  apply BitVec.eq_of_toNat_eq
  change (UScalar.cast .U64 b).val = (BitVec.ofNat 64 b.val).toNat
  rw [UScalar.cast_val, BitVec.toNat_ofNat]

/-- `#tooth`: `decode_canonical_fp5_limbs` and `decode_canonical_fp5` reject a non-canonical 5th limb (`= p`)
    while accepting canonical 5-limb quintic elements. -/
theorem tooth_decode_canonical_fp5_rejects_fifth_limb_alias :
    decode_canonical_fp5_limbs 1#u64 2#u64 3#u64 4#u64 GOLDILOCKS_P = .ok none ∧
    decode_canonical_fp5_limbs 1#u64 2#u64 3#u64 4#u64 5#u64 =
      .ok (some ⟨1#u64, 2#u64, 3#u64, 4#u64, 5#u64⟩) ∧
    decode_canonical_fp5 (Array.repeat 40#usize 0xFF#u8) = .ok none ∧
    decode_canonical_fp5 (Array.repeat 40#usize 0#u8) = .ok (some fp5Zero) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [decode_canonical_fp5_limbs_none_iff, IsCanonical, goldilocks_p_val]; decide
  · simp only [decode_canonical_fp5_limbs_some_iff, IsCanonical]; decide
  · rw [decode_canonical_fp5_none_iff]
    simp only [lePackU64At, Array.repeat, u8_cast_u64_bv, IsCanonicalFp5, IsCanonical]
    decide
  · rw [decode_canonical_fp5_some_iff]
    simp only [lePackU64At, Array.repeat, u8_cast_u64_bv, IsCanonicalFp5, IsCanonical, fp5Zero]
    decide

/-- `#tooth`: `decode_canonical_gl24_limbs` and `decode_canonical_gl24_digest` reject a non-canonical
    7th limb (`= p`) and all-`0xFF` bytes while accepting canonical 7-limb digests. -/
theorem tooth_decode_canonical_gl24_rejects_seventh_limb_alias :
    decode_canonical_gl24_limbs 1#u64 2#u64 3#u64 4#u64 5#u64 6#u64 GOLDILOCKS_P = .ok none ∧
    decode_canonical_gl24_limbs 1#u64 2#u64 3#u64 4#u64 5#u64 6#u64 7#u64 =
      .ok (some ⟨1#u64, 2#u64, 3#u64, 4#u64, 5#u64, 6#u64, 7#u64⟩) ∧
    decode_canonical_gl24_digest (Array.repeat 56#usize 0xFF#u8) = .ok none := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [decode_canonical_gl24_limbs_none_iff, IsCanonicalGl24, IsCanonical, goldilocks_p_val]; decide
  · simp only [decode_canonical_gl24_limbs_some_iff, IsCanonicalGl24, IsCanonical]; decide
  · rw [decode_canonical_gl24_digest_none_iff]
    simp only [lePackU64At, Array.repeat, u8_cast_u64_bv, IsCanonicalGl24, IsCanonical]
    decide

/-- `#tooth`: Both `step_merkle_pair_order_400` and `step_merkle_pair_order_gl24` swap `(node, sibling)`
    on the direction bit, reject `level = 64`, and `step_merkle_pair_order_gl24` rejects non-canonical limbs. -/
theorem tooth_merkle_400_and_gl24_swap_and_reject :
    let z := Array.repeat 50#usize 0x11#u8
    let w := Array.repeat 50#usize 0x22#u8
    let g0 : Gl24Digest := ⟨1#u64, 2#u64, 3#u64, 4#u64, 5#u64, 6#u64, 7#u64⟩
    let g1 : Gl24Digest := ⟨8#u64, 9#u64, 10#u64, 11#u64, 12#u64, 13#u64, 14#u64⟩
    let gBad : Gl24Digest := ⟨1#u64, 2#u64, 3#u64, 4#u64, 5#u64, 6#u64, GOLDILOCKS_P⟩
    step_merkle_pair_order_400 0#u64 0#u32 z w = .ok (some ⟨z, w⟩) ∧
    step_merkle_pair_order_400 1#u64 0#u32 z w = .ok (some ⟨w, z⟩) ∧
    step_merkle_pair_order_400 0#u64 64#u32 z w = .ok none ∧
    step_merkle_pair_order_gl24 0#u64 0#u32 g0 g1 = .ok (some ⟨g0, g1⟩) ∧
    step_merkle_pair_order_gl24 1#u64 0#u32 g0 g1 = .ok (some ⟨g1, g0⟩) ∧
    step_merkle_pair_order_gl24 0#u64 0#u32 g0 gBad = .ok none := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [step_merkle_pair_order_400_spec]; rfl
  · rw [step_merkle_pair_order_400_spec]; rfl
  · rw [step_merkle_pair_order_400_spec]; rfl
  · rw [step_merkle_pair_order_gl24_spec]; decide
  · rw [step_merkle_pair_order_gl24_spec]; decide
  · rw [step_merkle_pair_order_gl24_none_iff]; right; simp [IsCanonicalGl24, IsCanonical, goldilocks_p_val]

/-- `#tooth`: `checked_quorum_sum` rejects `u64` wraparound forgery (`u64::MAX + 5`) while accepting
    valid multi-shard quorum sums. -/
theorem tooth_checked_quorum_sum_rejects_u64_wraparound_forgery :
    let overflow_counts : Slice U64 := Array.to_slice (Array.make 2#usize [MAX_U64_WORD, 5#u64])
    let overflow_mins : Slice U64 := Array.to_slice (Array.make 2#usize [1#u64, 1#u64])
    let honest_counts : Slice U64 := Array.to_slice (Array.make 2#usize [10#u64, 15#u64])
    let honest_mins : Slice U64 := Array.to_slice (Array.make 2#usize [8#u64, 12#u64])
    checked_quorum_sum overflow_counts overflow_mins 4#u64 = .ok none ∧
    checked_quorum_sum honest_counts honest_mins 20#u64 = .ok (some 25#u64) := by
  dsimp only [Array.to_slice, Array.make]
  constructor
  · rw [checked_quorum_sum_none_iff]
    rintro ⟨s, _, _, _, _, hsum, hmax, _⟩
    simp only [natSumU64, List.foldl, Nat.zero_add, max_u64_word_val] at hsum
    change s = 18446744073709551620 at hsum
    omega
  · rw [checked_quorum_sum_sound]
    refine ⟨by decide, rfl, by decide, ?_, by rfl, by decide, by decide⟩
    intro j hc _
    match j with
    | 0 => change 0 < 8 ∧ 8 ≤ 10; decide
    | 1 => change 0 < 12 ∧ 12 ≤ 15; decide
    | n + 2 => change n + 2 < 2 at hc; omega

/-- `#tooth`: `verify_ood_pin_eq_fp5` rejects single-limb perturbations in any of the 5 limbs while
    accepting exact matches. -/
theorem tooth_ood_pin_fp5_rejects_perturbation :
    let p1 : Fp5 := ⟨1#u64, 2#u64, 3#u64, 4#u64, 5#u64⟩
    let p2 : Fp5 := ⟨1#u64, 2#u64, 3#u64, 4#u64, 6#u64⟩
    verify_ood_pin_eq_fp5 p1 p2 = .ok false ∧
    verify_ood_pin_eq_fp5 p1 p1 = .ok true := by
  dsimp only
  simp only [verify_ood_pin_eq_fp5_spec]
  decide

private theorem eval_fieldMul (a b c : U64)
    (h : (a.val * b.val) % 18446744069414584321 = c.val) : fieldMul a b = c :=
  UScalar.eq_of_val_eq ((fieldMul_val a b).trans h)

private theorem eval_fp5_concrete (lhs rhs : Fp5)
    (h0 : lhs.c0.val = rhs.c0.val) (h1 : lhs.c1.val = rhs.c1.val)
    (h2 : lhs.c2.val = rhs.c2.val) (h3 : lhs.c3.val = rhs.c3.val)
    (h4 : lhs.c4.val = rhs.c4.val) : lhs = rhs :=
  Fp5.ext (UScalar.eq_of_val_eq h0) (UScalar.eq_of_val_eq h1) (UScalar.eq_of_val_eq h2)
    (UScalar.eq_of_val_eq h3) (UScalar.eq_of_val_eq h4)

/-- `#tooth` & premise-inhabitedness witness: exhibits concrete Goldilocks inverses `it` and `iy`,
    verifies exact coset recovery for `duet_fold_fp5` and `cwyz_duet_fold_fp5`, and proves
    `verify_affine_duet_fold_step_fp5` and `verify_cwyz_duet_fold_step_fp5` accept honest claims
    while rejecting single-limb perturbations. -/
theorem tooth_coset_inverse_premises_inhabited_and_fp5_fold_rejects_perturbation :
    let it := 9223372034707292161#u64
    let y0 := 2#u64
    let iy := 13835058052060938241#u64
    let yy := 4#u64
    let even : Fp5 := ⟨3#u64, 5#u64, 7#u64, 9#u64, 11#u64⟩
    let odd : Fp5 := ⟨13#u64, 17#u64, 19#u64, 24#u64, 29#u64⟩
    let v0 : Fp5 := ⟨29#u64, 39#u64, 45#u64, 57#u64, 69#u64⟩
    let v1 : Fp5 := ⟨18446744069414584298#u64, 18446744069414584292#u64,
                      18446744069414584290#u64, 18446744069414584282#u64,
                      18446744069414584274#u64⟩
    let theta : Fp5 := ⟨2#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩
    let alpha : Fp5 := ⟨5#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩
    let beta : Fp5 := ⟨7#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩
    let duet_honest : Fp5 := ⟨28#u64, 42#u64, 54#u64, 69#u64, 84#u64⟩
    let duet_forged : Fp5 := ⟨28#u64, 42#u64, 54#u64, 69#u64, 85#u64⟩
    let cwyz_honest : Fp5 := ⟨970#u64, 1304#u64, 1504#u64, 1905#u64, 2306#u64⟩
    let cwyz_forged : Fp5 := ⟨970#u64, 1304#u64, 1504#u64, 1905#u64, 2307#u64⟩
    v0 = fp5Add even (fp5Scale odd y0) ∧
    v1 = fp5Sub even (fp5Scale odd y0) ∧
    fieldMul 2#u64 it = 1#u64 ∧
    fieldMul (fieldMul 2#u64 y0) iy = 1#u64 ∧
    duet_fold_fp5 v0 v1 iy it alpha = .ok duet_honest ∧
    cwyz_duet_fold_fp5 v0 v1 iy it yy theta alpha beta = .ok cwyz_honest ∧
    verify_affine_duet_fold_step_fp5 v0 v1 iy it alpha duet_honest = .ok true ∧
    verify_affine_duet_fold_step_fp5 v0 v1 iy it alpha duet_forged = .ok false ∧
    verify_cwyz_duet_fold_step_fp5 v0 v1 iy it yy theta alpha beta cwyz_honest = .ok true ∧
    verify_cwyz_duet_fold_step_fp5 v0 v1 iy it yy theta alpha beta cwyz_forged = .ok false := by
  dsimp only
  have hv0 : (⟨29#u64, 39#u64, 45#u64, 57#u64, 69#u64⟩ : Fp5) =
      fp5Add ⟨3#u64, 5#u64, 7#u64, 9#u64, 11#u64⟩
        (fp5Scale ⟨13#u64, 17#u64, 19#u64, 24#u64, 29#u64⟩ 2#u64) := by
    unfold fp5Add fp5Scale
    apply eval_fp5_concrete <;> simp only [fieldAdd_val, fieldMul_val] <;> decide
  have hv1 : (⟨18446744069414584298#u64, 18446744069414584292#u64,
               18446744069414584290#u64, 18446744069414584282#u64,
               18446744069414584274#u64⟩ : Fp5) =
      fp5Sub ⟨3#u64, 5#u64, 7#u64, 9#u64, 11#u64⟩
        (fp5Scale ⟨13#u64, 17#u64, 19#u64, 24#u64, 29#u64⟩ 2#u64) := by
    unfold fp5Sub fp5Scale
    apply eval_fp5_concrete <;> simp only [fieldSub_val, fieldMul_val] <;> decide
  have hit : fieldMul 2#u64 9223372034707292161#u64 = 1#u64 := eval_fieldMul _ _ _ (by decide)
  have hiy : fieldMul (fieldMul 2#u64 2#u64) 13835058052060938241#u64 = 1#u64 := by
    rw [eval_fieldMul 2#u64 2#u64 4#u64 (by decide)]
    exact eval_fieldMul _ _ _ (by decide)
  have hduet : duetFp5Value ⟨29#u64, 39#u64, 45#u64, 57#u64, 69#u64⟩
      ⟨18446744069414584298#u64, 18446744069414584292#u64, 18446744069414584290#u64,
       18446744069414584282#u64, 18446744069414584274#u64⟩
      13835058052060938241#u64 9223372034707292161#u64
      ⟨5#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩ =
      ⟨28#u64, 42#u64, 54#u64, 69#u64, 84#u64⟩ := by
    simp only [duetFp5Value.public_eqs]
    unfold fp5Add fp5Sub fp5Scale fp5Mul
    apply eval_fp5_concrete <;> simp only [fieldAdd_val, fieldSub_val, fieldMul_val] <;> decide
  have hcwyz : cwyzFp5Value ⟨29#u64, 39#u64, 45#u64, 57#u64, 69#u64⟩
      ⟨18446744069414584298#u64, 18446744069414584292#u64, 18446744069414584290#u64,
       18446744069414584282#u64, 18446744069414584274#u64⟩
      13835058052060938241#u64 9223372034707292161#u64 4#u64
      ⟨2#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩ ⟨5#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩
      ⟨7#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩ =
      ⟨970#u64, 1304#u64, 1504#u64, 1905#u64, 2306#u64⟩ := by
    simp only [cwyzFp5Value.public_eqs]
    unfold fp5Add fp5Sub fp5Scale fp5Mul
    apply eval_fp5_concrete <;> simp only [fieldAdd_val, fieldSub_val, fieldMul_val] <;> decide
  refine ⟨hv0, hv1, hit, hiy, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [duet_fold_fp5_refines, hduet]
  · rw [cwyz_duet_fold_fp5_refines, hcwyz]
  · rw [verify_affine_duet_fold_step_fp5_spec, hduet]; decide
  · rw [verify_affine_duet_fold_step_fp5_spec, hduet]; decide
  · rw [verify_cwyz_duet_fold_step_fp5_spec, hcwyz]; decide
  · rw [verify_cwyz_duet_fold_step_fp5_spec, hcwyz]; decide

/-- `#tooth`: `cwyz_bridge_claim_step_fp5` and `verify_cwyz_bridge_claim_step_fp5` accept honest
    dual cross-term claims and reject single-limb perturbations. -/
theorem tooth_cwyz_bridge_fp5_accepts_dual_and_rejects_perturbation :
    let w0 : Fp5 := ⟨10#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩
    let w1 : Fp5 := ⟨14#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩
    let w2 : Fp5 := ⟨0#u64, 15#u64, 0#u64, 0#u64, 0#u64⟩
    let w3 : Fp5 := ⟨22#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩
    let w4 : Fp5 := ⟨0#u64, 33#u64, 0#u64, 0#u64, 0#u64⟩
    let claim : Fp5 := ⟨10#u64, 21#u64, 0#u64, 0#u64, 0#u64⟩
    let phi : Fp5 := ⟨2#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩
    let theta : Fp5 := ⟨2#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩
    let alpha : Fp5 := ⟨5#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩
    let beta : Fp5 := ⟨7#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩
    let honest : Fp5 := ⟨344#u64, 1089#u64, 0#u64, 0#u64, 0#u64⟩
    let forged : Fp5 := ⟨344#u64, 1090#u64, 0#u64, 0#u64, 0#u64⟩
    cwyz_bridge_claim_step_fp5 w0 w1 w2 w3 w4 claim phi theta alpha beta = .ok honest ∧
    verify_cwyz_bridge_claim_step_fp5 w0 w1 w2 w3 w4 claim phi theta alpha beta honest = .ok true ∧
    verify_cwyz_bridge_claim_step_fp5 w0 w1 w2 w3 w4 claim phi theta alpha beta forged = .ok false := by
  dsimp only
  have hval : cwyzBridgeFp5Value
      ⟨10#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩ ⟨14#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩
      ⟨0#u64, 15#u64, 0#u64, 0#u64, 0#u64⟩ ⟨22#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩
      ⟨0#u64, 33#u64, 0#u64, 0#u64, 0#u64⟩ ⟨10#u64, 21#u64, 0#u64, 0#u64, 0#u64⟩
      ⟨2#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩ ⟨2#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩
      ⟨5#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩ ⟨7#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩ =
      ⟨344#u64, 1089#u64, 0#u64, 0#u64, 0#u64⟩ := by
    simp only [cwyzBridgeFp5Value.public_eqs]
    unfold fp5Add fp5Sub fp5Mul
    apply eval_fp5_concrete <;> simp only [fieldAdd_val, fieldSub_val, fieldMul_val] <;> decide
  refine ⟨?_, ?_, ?_⟩
  · rw [cwyz_bridge_claim_step_fp5_refines, hval]
  · rw [verify_cwyz_bridge_claim_step_fp5_spec, hval]; decide
  · rw [verify_cwyz_bridge_claim_step_fp5_spec, hval]; decide

/-- `#tooth`: `eval_fp5_univariate_at_base`, `verify_fp5_univariate_at_base_pin`, and
    `eval_quadratic_sumcheck_wire_fp5` accept ascending-degree polynomials and hypercube sums
    while rejecting perturbed evaluation pins. -/
theorem tooth_horner_fp5_accepts_ascending_and_rejects_perturbation :
    let coeffs : Slice Fp5 :=
      Array.to_slice (Array.make 3#usize
        [⟨1#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩,
         ⟨2#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩,
         ⟨3#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩])
    let honest : Fp5 := ⟨17#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩
    let forged : Fp5 := ⟨18#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩
    eval_fp5_univariate_at_base coeffs 2#u64 = .ok honest ∧
    verify_fp5_univariate_at_base_pin coeffs 2#u64 honest = .ok true ∧
    verify_fp5_univariate_at_base_pin coeffs 2#u64 forged = .ok false ∧
    eval_quadratic_sumcheck_wire_fp5
      ⟨3#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩ ⟨5#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩
      ⟨20#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩ ⟨2#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩ =
      .ok ⟨41#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩ := by
  dsimp only
  have hval : hornerSpec
      [⟨1#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩,
       ⟨2#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩,
       ⟨3#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩] 2#u64 fp5Zero =
      ⟨17#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩ := by
    simp only [hornerSpec_cons, hornerSpec_nil]
    unfold fp5Add fp5Scale fp5Zero
    apply eval_fp5_concrete <;> simp only [fieldAdd_val, fieldMul_val] <;> decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eval_fp5_univariate_at_base_spec]; dsimp only [Array.to_slice, Array.make]; rw [hval]
  · simp only [verify_fp5_univariate_at_base_pin_spec, Array.to_slice, Array.make, hval]; decide
  · simp only [verify_fp5_univariate_at_base_pin_spec, Array.to_slice, Array.make, hval]; decide
  · rw [eval_quadratic_sumcheck_wire_fp5_refines]
    congr 1
    simp only [quadraticWireFp5Value.public_eqs]
    unfold fp5Add fp5Sub fp5Mul
    apply eval_fp5_concrete <;> simp only [fieldAdd_val, fieldSub_val, fieldMul_val] <;> decide

/-- `#tooth`: `verify_qsaghqm2_header` and `verify_quintic_schedule_envelope` accept valid
    `QSAGHQM2` envelopes and deployed `[16, 28]` schedules while rejecting bad magic, unknown
    profile tags, signer overcounts, length mismatches, and out-of-envelope stage counts. -/
theorem tooth_qsaghqm2_header_and_schedule_reject_tamper :
    let magicOk := Array.make 8#usize [81#u8, 83#u8, 65#u8, 71#u8, 72#u8, 81#u8, 77#u8, 50#u8]
    let magicBad := Array.make 8#usize [81#u8, 83#u8, 65#u8, 71#u8, 72#u8, 81#u8, 77#u8, 49#u8]
    verify_qsaghqm2_header magicOk QSAGHQM2_PROFILE_TURBO400 10#u64 16#u64 1280#u64 1280#u64 =
      .ok (some { profile_tag := 1#u8, active_signers := 10#u64, payload_len := 1280#u64 }) ∧
    verify_qsaghqm2_header magicOk QSAGHQM2_PROFILE_GL24 16#u64 16#u64 960#u64 960#u64 =
      .ok (some { profile_tag := 2#u8, active_signers := 16#u64, payload_len := 960#u64 }) ∧
    verify_qsaghqm2_header magicBad QSAGHQM2_PROFILE_TURBO400 10#u64 16#u64 1280#u64 1280#u64 = .ok none ∧
    verify_qsaghqm2_header magicOk 3#u8 10#u64 16#u64 1280#u64 1280#u64 = .ok none ∧
    verify_qsaghqm2_header magicOk QSAGHQM2_PROFILE_TURBO400 17#u64 16#u64 1280#u64 1280#u64 = .ok none ∧
    verify_qsaghqm2_header magicOk QSAGHQM2_PROFILE_TURBO400 10#u64 16#u64 1280#u64 1281#u64 = .ok none ∧
    verify_quintic_schedule_envelope 20#u32 8#u32 12#u32 3#u32 = .ok true ∧
    verify_quintic_schedule_envelope 24#u32 8#u32 16#u32 4#u32 = .ok true ∧
    verify_quintic_schedule_envelope 20#u32 8#u32 12#u32 4#u32 = .ok false ∧
    verify_quintic_schedule_envelope 15#u32 5#u32 10#u32 3#u32 = .ok false := by
  dsimp only [Array.make]
  simp only [verify_qsaghqm2_header_spec, verify_quintic_schedule_envelope_spec,
    qsaghqm2_profile_turbo400_val, qsaghqm2_profile_gl24_val,
    min_quintic_log_cells_val, max_quintic_log_cells_val,
    Qsaghqm2HeaderSpec, QuinticScheduleEnvelopeSpec]
  decide

end qsag_whir_verified.proofs
