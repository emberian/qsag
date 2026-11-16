module
public import Qsag.Math.GoldilocksBase
public import Qsag.Math.Counting
public import Qsag.Oracle.FiatShamir
public import Qsag.Math.Goldilocks
public import Qsag.Oracle.Keccak
public import Qsag.Oracle.Poseidon2
public import Qsag.Oracle.Sponge
public import Qsag.Tactic.Prelude
public import Qsag.Oracle.Spn
public import Qsag.Math.Gf2Pow128
public import Qsag.Spec.Bounds
public import Qsag.Spec.Encoding
public import Qsag.Oracle.Qrom
public section
set_option exponentiation.threshold 8192
namespace Qsag
set_option autoImplicit false
/-! ## 6. Official NIST FIPS 202 `SHAKE256` Build-Time Conformance Vectors -/

-- NIST FIPS 202 SHAKE256("", 256) = 46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762f
example : shake256Xof 32 [] =
    [0x46, 0xb9, 0xdd, 0x2b, 0x0b, 0xa8, 0x8d, 0x13,
     0x23, 0x3b, 0x3f, 0xeb, 0x74, 0x3e, 0xeb, 0x24,
     0x3f, 0xcd, 0x52, 0xea, 0x62, 0xb8, 0x1b, 0x82,
     0xb5, 0x0c, 0x27, 0x64, 0x6e, 0xd5, 0x76, 0x2f] := shake256_empty_kat

-- NIST FIPS 202 SHAKE256("abc", 256) = 483366601360a8771c6863080cc4114d8db44530f8f1e1ee4f94ea37e78b5739
example : shake256Xof 32 [0x61, 0x62, 0x63] =
    [0x48, 0x33, 0x66, 0x60, 0x13, 0x60, 0xa8, 0x77,
     0x1c, 0x68, 0x63, 0x08, 0x0c, 0xc4, 0x11, 0x4d,
     0x8d, 0xb4, 0x45, 0x30, 0xf8, 0xf1, 0xe1, 0xee,
     0x4f, 0x94, 0xea, 0x37, 0xe7, 0x8b, 0x57, 0x39] := shake256_abc_kat


/-! ## 5. Build-Time Conformance Vectors Matching `poseidon2.rs` -/

example : (poseidon2Perm12 ⟨⟨Goldilocks.ofNat 0, Goldilocks.ofNat 0, Goldilocks.ofNat 0, Goldilocks.ofNat 0⟩, ⟨Goldilocks.ofNat 0, Goldilocks.ofNat 0, Goldilocks.ofNat 0, Goldilocks.ofNat 0⟩, ⟨Goldilocks.ofNat 0, Goldilocks.ofNat 0, Goldilocks.ofNat 0, Goldilocks.ofNat 0⟩⟩).toList.map (·.val) =
    [17528629447354354351, 5014055130248055117, 10679077121839038553, 431078547345611051, 7807009921345120310, 2413869689279715014, 11875300792986830377, 1872634884137602556, 15069512080271275672, 14253608580209913153, 14550618143248480092, 107036164978639472] := poseidon2Perm12_zero_kat

example : (poseidon2Perm12 ⟨⟨Goldilocks.ofNat 0, Goldilocks.ofNat 1, Goldilocks.ofNat 2, Goldilocks.ofNat 3⟩, ⟨Goldilocks.ofNat 4, Goldilocks.ofNat 5, Goldilocks.ofNat 6, Goldilocks.ofNat 7⟩, ⟨Goldilocks.ofNat 8, Goldilocks.ofNat 9, Goldilocks.ofNat 10, Goldilocks.ofNat 11⟩⟩).toList.map (·.val) =
    [13782584570844608145, 13136387643152332171, 7171133015474200819, 7643370872200861694, 14144755201299840503, 16470027036684692562, 1748465969625202405, 1718729118078964347, 6141020819996733037, 16322330185628708898, 11650380702735067362, 2734959974607798415] := poseidon2Perm12_iota_kat

example : poseidon2Hash32 [] =
    [182, 168, 65, 106, 0, 54, 23, 124, 22, 116, 119, 199, 75, 253, 202, 145, 123, 13, 115, 200, 186, 143, 207, 66, 162, 161, 198, 9, 220, 37, 176, 162] := poseidon2Hash32_empty_kat

example : poseidon2Hash32 [0] =
    [116, 79, 15, 95, 17, 248, 202, 240, 45, 126, 192, 181, 89, 193, 185, 161, 98, 167, 199, 38, 214, 141, 4, 22, 97, 34, 223, 133, 16, 3, 170, 104] := poseidon2Hash32_zero_byte_kat

example : poseidon2Hash32 [1, 2, 3] =
    [149, 79, 171, 160, 0, 49, 166, 60, 204, 121, 241, 71, 102, 130, 24, 17, 35, 162, 114, 249, 194, 254, 120, 46, 18, 111, 254, 27, 106, 81, 178, 227] := poseidon2Hash32_123_kat

example : poseidon2Hash32 [113, 115, 97, 103, 45, 112, 111, 115, 101, 105, 100, 111, 110, 50, 45, 107, 97, 116] =
    [228, 156, 140, 147, 124, 10, 100, 197, 103, 106, 168, 7, 254, 196, 250, 183, 212, 130, 17, 26, 2, 139, 235, 15, 219, 46, 193, 238, 148, 50, 236, 229] := poseidon2Hash32_ascii_kat

example : (let out := poseidon2CompressWeighted ⟨⟨Goldilocks.ofNat 0, Goldilocks.ofNat 1, Goldilocks.ofNat 2, Goldilocks.ofNat 3⟩, ⟨Goldilocks.ofNat 4, Goldilocks.ofNat 5, Goldilocks.ofNat 6, Goldilocks.ofNat 7⟩, ⟨Goldilocks.ofNat 8, Goldilocks.ofNat 9, Goldilocks.ofNat 10, Goldilocks.ofNat 11⟩⟩;
    [out.x0.val, out.x1.val, out.x2.val, out.x3.val]) =
    [13782584570844608185, 13136387643152332218, 7171133015474200873, 7643370872200861755] :=
  poseidon2CompressWeighted_iota_kat


/-! ## 4. `#tooth` Cryptanalytic Refutations & Assurance Gates -/

/-- **`#tooth` Unframed Concatenation Collision (`tooth_unframed_concat_collides`)**:
    Without SP 800-185 `encodeString` length-framing, naive `S ++ m` collides immediately on
    `("AB", "C")` vs `("A", "BC")`, whereas `cshakePrefix` separates them! -/
theorem tooth_unframed_concat_collides :
    ∃ (S₁ m₁ S₂ m₂ : List UInt8),
      S₁ = [0x41, 0x42] ∧ m₁ = [0x43] ∧ S₂ = [0x41] ∧ m₂ = [0x42, 0x43] ∧
      S₁ ≠ S₂ ∧ S₁ ++ m₁ = S₂ ++ m₂ ∧
      cshakePrefix [] S₁ ++ m₁ ≠ cshakePrefix [] S₂ ++ m₂ := by
  refine ⟨[0x41, 0x42], [0x43], [0x41], [0x42, 0x43], rfl, rfl, rfl, rfl, by decide, rfl, ?_⟩
  intro hEq
  have hS := (cshakePrefix_prefix_free
    (bitlen_lt_sp800_bound (by decide)) (bitlen_lt_sp800_bound (by decide))
    (bitlen_lt_sp800_bound (by decide)) (bitlen_lt_sp800_bound (by decide)) hEq).2.1
  exact absurd hS (by decide)

/-- **`#tooth` Zero Domain-Byte Padding Collision (`tooth_zero_domByte_pad10star1_collides`)**:
    Omitting `ValidDomByte` (`domByte = 0x00`) causes `[]` and `[0x00]` to collide identically! -/
theorem tooth_zero_domByte_pad10star1_collides :
    ∃ (m₁ m₂ : List UInt8), ¬ ValidDomByte 0x00 ∧ m₁ ≠ m₂ ∧
      absorbPayload 136 0x00 m₁ = absorbPayload 136 0x00 m₂ := by
  refine ⟨[], [0x00], by decide, by decide, ?_⟩
  have hPad : pad10star1 136 0x00 [] = pad10star1 136 0x00 [0x00] := by
    unfold pad10star1
    change ([] ++ [0] ++ List.replicate 134 0 ++ [0x80] : List UInt8) = ([0] ++ [0] ++ List.replicate 133 0 ++ [0x80] : List UInt8)
    have hRep : (List.replicate 134 0 : List UInt8) = 0 :: List.replicate 133 0 := rfl
    rw [hRep]; rfl
  unfold absorbPayload; rw [hPad]

/-- **`#tooth` Multi-Block Customization Overflow (`tooth_oversized_tag_midstate_single_block_fails`)**:
    When `(encodeString [] ++ encodeString S).length > 134` (`|S| = 131` bytes), `cshakePrefix [] S`
    spans 2 blocks (`272 ≠ 136` bytes), refuting single-block midstate truncation! -/
theorem tooth_oversized_tag_midstate_single_block_fails :
    ∃ S : List UInt8,
      S = List.replicate 131 0x41 ∧
      ¬ ((encodeString [] ++ encodeString S).length ≤ 134) ∧
      (cshakePrefix [] S).length = 272 ∧ (cshakePrefix [] S).length ≠ 136 := by
  have hB0 : natBytesBE 0 = [0] := natBytesBE_small_kats.1
  have hB136 : natBytesBE 136 = [136] := natBytesBE_small_kats.2.1
  have hB1048 : natBytesBE 1048 = [4, 24] := natBytesBE_small_kats.2.2
  have hEncLen : (encodeString [] ++ encodeString (List.replicate 131 0x41)).length = 136 := by
    simp only [encodeString_eq, leftEncode_eq, List.length_append, List.length_replicate,
      List.length_nil, Nat.mul_zero, hB0, hB1048, List.length_cons]
  have hPfxLen : (cshakePrefix [] (List.replicate 131 0x41)).length = 272 := by
    unfold cshakePrefix
    rw [bytepad_eq]
    simp only [show (136 : Nat) ≠ 0 from by decide, ↓reduceIte, List.length_append,
      List.length_replicate, hEncLen, leftEncode_eq, hB136, List.length_cons, List.length_nil]
  exact ⟨List.replicate 131 0x41, rfl, by rw [hEncLen]; decide, hPfxLen, by rw [hPfxLen]; decide⟩

theorem witness_pad10star1_valid_domain :
    ∃ (r : Nat) (d : UInt8) (m₁ m₂ : List UInt8),
      0 < r ∧ ValidDomByte d ∧ absorbPayload r d m₁ = absorbPayload r d m₂ :=
  ⟨136, domShake256, [0x61, 0x62], [0x61, 0x62], by decide,
    by rw [domShake256_eq]; decide, rfl⟩

theorem witness_cross_domain_pair :
    ∃ (r : Nat) (d₁ d₂ : UInt8) (m₁ m₂ : List UInt8),
      m₁ = [0x01] ∧ m₂ = [0x02] ∧
      0 < r ∧ ValidDomByte d₁ ∧ ValidDomByte d₂ ∧ d₁ ≠ d₂ :=
  ⟨136, domShake256, domCshake256, [0x01], [0x02], rfl, rfl,
   by decide, by rw [domShake256_eq]; decide, by rw [domCshake256_eq]; decide,
   by rw [domShake256_eq, domCshake256_eq]; decide⟩

/-- `cshakePrefix_prefix_free` applied at the Canopy leaf tag: its hypotheses are jointly
dischargeable. The equation forces repeated components, which the positional
`#verify_inhabited` matcher cannot assign, so the application itself is the witness. -/
theorem witness_cshakePrefix_canopy :
    ([] : List UInt8) = [] ∧ qsagTagCanopyLeaf = qsagTagCanopyLeaf ∧ ([0x01] : List UInt8) = [0x01] :=
  cshakePrefix_prefix_free (N₁ := []) (S₁ := qsagTagCanopyLeaf) (N₂ := []) (S₂ := qsagTagCanopyLeaf)
    (m₁ := [0x01]) (m₂ := [0x01])
    (bitlen_lt_sp800_bound (by decide))
    (bitlen_lt_sp800_bound (by rw [qsagTagCanopyLeaf_eq]; decide))
    (bitlen_lt_sp800_bound (by decide))
    (bitlen_lt_sp800_bound (by rw [qsagTagCanopyLeaf_eq]; decide)) rfl

theorem witness_keccak_midstate_canopy :
    ∃ (S msg : List UInt8) (outLen : Nat),
      S ≠ [] ∧ (encodeString [] ++ encodeString S).length ≤ 134 ∧
      (cshake256Xof outLen S msg).length = 32 :=
  ⟨qsagTagCanopyLeaf, [0xde, 0xad, 0xbe, 0xef], 32,
    by rw [qsagTagCanopyLeaf_eq]; decide,
    by
      rw [List.length_append, encodeString_length_short (by decide),
        encodeString_length_short (by rw [qsagTagCanopyLeaf_eq]; decide), qsagTagCanopyLeaf_eq]
      decide,
    by simp⟩

#verify_constructive Qsag.pad10star1_joint_injective Qsag.pad10star1_injective
  Qsag.absorbPayload_cross_domain_encodings_ne Qsag.evalSponge_keccak_eq_shake256Xof
  Qsag.leftEncode_prefix_inj Qsag.encodeString_prefix_inj Qsag.cshakePrefix_prefix_free
  Qsag.cshakePrefix_injective Qsag.cshake256_encodings_ne
  Qsag.cshake_precomputed_midstate_eq Qsag.keccak_cshake256_precomputed_midstate_eq

#verify_inhabited Qsag.pad10star1_injective Qsag.witness_pad10star1_valid_domain
#verify_inhabited Qsag.absorbPayload_cross_domain_encodings_ne Qsag.witness_cross_domain_pair
#verify_constructive Qsag.witness_cshakePrefix_canopy
#verify_inhabited Qsag.keccak_cshake256_precomputed_midstate_eq Qsag.witness_keccak_midstate_canopy

#tooth_pair Qsag.pad10star1_injective vs Qsag.tooth_zero_domByte_pad10star1_collides
#tooth_pair Qsag.cshakePrefix_prefix_free vs Qsag.tooth_unframed_concat_collides
#tooth_pair Qsag.cshakePrefix_single_block_length vs Qsag.tooth_oversized_tag_midstate_single_block_fails



open MigrationExecution
set_option exponentiation.threshold 2048
theorem tooth_degenerate_mds_ab_eq_one_collapses_branch_number :
    ∃ st : Tower128 × Tower128,
      st ≠ (towerZero 7, towerZero 7) ∧
      spnLinearMix 7 (towerOne 7) (towerOne 7) st = (towerZero 7, towerZero 7) ∧
      laneActiveWeight 7 st + laneActiveWeight 7 (spnLinearMix 7 (towerOne 7) (towerOne 7) st) = 2 := by
  refine ⟨(towerOne 7, towerOne 7), fun h => towerOne128_ne_zero (congrArg Prod.fst h), ?_, ?_⟩
  · unfold spnLinearMix
    simp only [towerOne_mul, towerAdd_self_zero]
  · unfold spnLinearMix laneActiveWeight
    simp only [towerOne_mul, towerAdd_self_zero, towerOne128_ne_zero, ↓reduceIte]

theorem tooth_frobenius_sbox_x2_differential_probability_one :
    ∃ badBound : RatBound,
      binaryPopcount 2 = 1 ∧
      (∀ x delta : Tower128,
        towerAdd 7 (towerMul 7 (towerAdd 7 x delta) (towerAdd 7 x delta)) (towerMul 7 x x) =
          towerMul 7 delta delta) ∧
      RatBound.lt sbox7MaxDiffProb128 badBound ∧
      ¬ strictlyMoreThanBits 125 badBound := by
  refine ⟨RatBound.one, binaryPopcount_two, fun x delta => ?_,
    by rw [RatBound.one_eq]; decide, by rw [RatBound.one_eq]; decide⟩
  rw [towerSq_add, towerAdd_comm 7 (towerMul 7 x x), towerAdd_assoc, towerAdd_self_zero, towerAdd_zero]

theorem tooth_zero_round_constants_preserve_zero_subspace (mdsA mdsB : Tower128) :
    ∃ rc : Tower128 × Tower128,
      spnRound128 mdsA mdsB rc (towerZero 7, towerZero 7) = (towerZero 7, towerZero 7) ∧
      spnIterRounds128 mdsA mdsB (fun _ => rc) spnRounds
        (towerZero 7, towerZero 7) = (towerZero 7, towerZero 7) := by
  have hStep : spnRound128 mdsA mdsB (towerZero 7, towerZero 7) (towerZero 7, towerZero 7) =
      (towerZero 7, towerZero 7) := by unfold spnRound128 spnLinearMix towerSbox7; simp
  refine ⟨(towerZero 7, towerZero 7), hStep, ?_⟩
  suffices hAll : ∀ r : Nat, spnIterRounds128 mdsA mdsB (fun _ => (towerZero 7, towerZero 7)) r
      (towerZero 7, towerZero 7) = (towerZero 7, towerZero 7) from hAll spnRounds
  intro r
  induction r with
  | zero => exact spnIterRounds128_zero _ _ _ _
  | succ r ih => rw [spnIterRounds128_succ, ih, hStep]

#tooth_pair Qsag.spnLinearMix_branch_number_three vs Qsag.tooth_degenerate_mds_ab_eq_one_collapses_branch_number
#tooth_pair Qsag.sbox7MaxDiffProb128_eq_three_div_two_pow_127 vs Qsag.tooth_frobenius_sbox_x2_differential_probability_one
#tooth_pair Qsag.spnRound128_nonzero_rc_breaks_zero_fixpoint vs Qsag.tooth_zero_round_constants_preserve_zero_subspace

theorem inhabited_parallel_seeded_spn_security :
    ∃ (mds : ValidSpnMdsPair 7) (rc : Tower128 × Tower128) (s s' : Tower128 × Tower128),
      rc ≠ (towerZero 7, towerZero 7) ∧ s ≠ s' ∧
      72 ≤ spnTrailActiveSboxes mds.mdsA mds.mdsB (fun _ => rc) spnRounds s s' := by
  have hRcNe : ((towerOne 7, towerZero 7) : Tower128 × Tower128) ≠ (towerZero 7, towerZero 7) :=
    fun h => towerOne128_ne_zero (congrArg Prod.fst h)
  have hSNe : ((towerZero 7, towerZero 7) : Tower128 × Tower128) ≠ (towerOne 7, towerZero 7) :=
    fun h => towerOne128_ne_zero (congrArg Prod.fst h).symm
  exact ⟨parallelSeededMdsPair, (towerOne 7, towerZero 7), (towerZero 7, towerZero 7),
    (towerOne 7, towerZero 7), hRcNe, hSNe,
    (spn48_active_sboxes_ge_72 parallelSeededMdsPair (fun _ => (towerOne 7, towerZero 7))
      (towerZero 7, towerZero 7) (towerOne 7, towerZero 7) hSNe).1⟩

#verify_inhabited Qsag.spn48_active_sboxes_ge_72 Qsag.inhabited_parallel_seeded_spn_security


/-! ## 7. Controls -/

set_option maxRecDepth 4096 in
/-- Positive controls: values of the Rust model, cross-checked against an independent
    transcription of `gf2_128_mul` / `pow7_plain` / the round body outside Lean. -/
theorem rust_spn_poly_basis_kats :
    rustPow7 2#128 = 0x80#128 ∧
    rustPow7 3#128 = 0xff#128 ∧
    rustSpnRound (7#128, 11#128) (3#128, 5#128) =
      (0x7e449a0c3042bf1c84c9783f54d336e9#128, 0x11db4739396e6534126ec4cc445b09a2#128) ∧
    rustSpnRound (0#128, 0#128) (1#128, 0#128) = (1#128, gf128MdsBPolyBits) :=
  rust_spn_poly_basis_kat

/-- Positive control for the framing: the little-endian bytes of `GF128_MDS_A`; byte 0 bit 0
    is the constant coefficient and byte 15 bit 7 is `x^127`. -/
theorem rust_le_lane_framing_kats :
    rustU128FromLeBytes [0x35, 0xc8, 0xed, 0x5c, 0x60, 0xc0, 0x9c, 0xf3,
      0x15, 0x7c, 0x4a, 0x7f, 0xb9, 0x79, 0x37, 0x9e] = gf128MdsAPolyBits ∧
    rustU128FromLeBytes [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = 1#128 ∧
    rustU128FromLeBytes [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x80] =
      BitVec.twoPow 128 127 ∧
    rustU128ToLeBytes 2#128 = [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [rustU128FromLeBytes_eq, rustU128FromLeBytes_eq, rustU128FromLeBytes_eq,
    rustU128ToLeBytes_eq, gf128MdsAPolyBits_eq]
  decide +kernel

/-- Negative control: reading the same sixteen bytes big-endian gives a different field
    element. -/
theorem tooth_big_endian_lane_framing_differs :
    BitVec.ofNat 128 (ofBE [0x35, 0xc8, 0xed, 0x5c, 0x60, 0xc0, 0x9c, 0xf3,
      0x15, 0x7c, 0x4a, 0x7f, 0xb9, 0x79, 0x37, 0x9e]) ≠ gf128MdsAPolyBits := by
  rw [gf128MdsAPolyBits_eq]
  decide +kernel

set_option maxRecDepth 4096 in
/-- Negative control: exchanging `GF128_MDS_A` and `GF128_MDS_B` changes the round. -/
theorem tooth_swapped_mds_constants_change_round :
    ∃ st : BitVec 128 × BitVec 128,
      rustSpnRound (0#128, 0#128) st ≠
        (let x7 := rustPow7 st.1
         let y7 := rustPow7 st.2
         (x7 ^^^ rustGf128Mul y7 gf128MdsBPolyBits, y7 ^^^ rustGf128Mul x7 gf128MdsAPolyBits)) :=
  ⟨(1#128, 0#128), rustSpnRound_swapped_mds_ne⟩

set_option maxRecDepth 4096 in
/-- Negative control: with tower constants read as raw `packTower` words instead of their
    images, the Rust round disagrees with the image of the tower round. -/
theorem tooth_untranslated_tower_constant_breaks_round :
    psiTower128Pair (spnRound128 gf128MdsATower gf128MdsBTower
        (towerZero 7, towerZero 7) (towerZero 7, towerOne 7)) ≠
      (rustGf128Mul 1#128 gf128MdsATowerBits, 1#128) ∧
    psiTower128Pair (spnRound128 gf128MdsATower gf128MdsBTower
        (towerZero 7, towerZero 7) (towerZero 7, towerOne 7)) =
      (gf128MdsAPolyBits, 1#128) := by
  have hEq : psiTower128Pair (spnRound128 gf128MdsATower gf128MdsBTower
        (towerZero 7, towerZero 7) (towerZero 7, towerOne 7)) = (gf128MdsAPolyBits, 1#128) := by
    rw [psiTower128Pair_spnRound128, psiTower128Pair_eq, psiTower128Pair_eq]
    show rustSpnRound (psiTower128ToPoly (towerZero 7), psiTower128ToPoly (towerZero 7))
      (psiTower128ToPoly (towerZero 7), psiTower128ToPoly (towerOne 7)) = _
    rw [psiTower128ToPoly_zero, psiTower128ToPoly_one]
    exact rustSpnRound_zero_one_kat.1
  refine ⟨?_, hEq⟩
  rw [hEq]
  exact rustSpnRound_zero_one_kat.2


/-- **Invertibility is not collision or preimage resistance.** Xor with a constant is a
    bijection of the 256-bit state, and its Davies–Meyer feed-forward is the constant map:
    every pair collides and every input is a preimage of `c`. Any collision or preimage claim
    for `spnDaviesMeyer48` must therefore use more than `pow7_tower128_bijective`. -/
theorem tooth_xor_constant_permutation_davies_meyer_collapses (c : Tower128 × Tower128) :
    IsBijective (fun x => pairXor x c) ∧ ∀ x, pairXor (pairXor x c) x = c := by
  have hInv : ∀ x, pairXor (pairXor x c) c = x := fun x => by
    rw [pairXor_eq, pairXor_eq]
    apply Prod.ext <;> simp only [towerAdd_assoc, towerAdd_self_zero, towerAdd_zero]
  refine ⟨⟨fun a b h => ?_, fun b => ⟨pairXor b c, hInv b⟩⟩, fun x => ?_⟩
  · have h2 := congrArg (fun z => pairXor z c) h
    simpa only [hInv] using h2
  · rw [pairXor_eq, pairXor_eq]
    apply Prod.ext
    · show towerAdd 7 (towerAdd 7 x.1 c.1) x.1 = c.1
      rw [towerAdd_comm 7 x.1 c.1, towerAdd_assoc, towerAdd_comm 7 x.1 x.1, towerAdd_self_zero,
        towerAdd_zero]
    · show towerAdd 7 (towerAdd 7 x.2 c.2) x.2 = c.2
      rw [towerAdd_comm 7 x.2 c.2, towerAdd_assoc, towerAdd_self_zero, towerAdd_zero]


/-! ## §5. One trail is not the hull -/

/-- `Bool` with `&&` as pairing and `^^` as addition. -/
def boolWalsh : WalshSpace Bool where
  elems := [false, true]
  dot := fun a b => a && b
  add := fun a b => a ^^ b
  nodup := by decide
  complete := fun x => by cases x <;> decide
  dot_symm := fun a b => by cases a <;> cases b <;> rfl
  dot_add := fun u a b => by cases u <;> cases a <;> cases b <;> rfl
  orth := fun y y' => by
    cases y <;> cases y' <;> simp only [isum_cons, isum_nil, wsgn_eq] <;> decide

/-- Two rounds over `Bool`: the identity, then the constant map. With output and input mask
    `true`, the trail through the intermediate mask `false` contributes `2 · 2 = 4`, the trail
    through `true` contributes `-2 · 2 = -4`, and the hull (their sum) is `0`. A single
    trail's size says nothing about the hull, in either direction. -/
theorem tooth_walsh_single_trail_is_not_the_hull :
    walsh boolWalsh (fun _ => true) true false * walsh boolWalsh (fun x => x) false true = 0 ∧
    walsh boolWalsh (fun _ => true) true true * walsh boolWalsh (fun x => x) true true = 0 ∧
    walsh boolWalsh (fun x => !x) true true * walsh boolWalsh (fun x => x) true true = -4 ∧
    walsh boolWalsh (fun x => x) true true * walsh boolWalsh (fun x => x) true true = 4 ∧
    walshTrailSum boolWalsh [fun x => x, fun _ => true] true true = 0 := by
  simp only [walshTrailSum_cons, walshTrailSum_nil, walsh_eq, boolWalsh, isum_cons, isum_nil,
    wsgn_eq]
  decide

#verify_constructive tooth_big_endian_lane_framing_differs
#verify_constructive tooth_swapped_mds_constants_change_round
#verify_constructive tooth_untranslated_tower_constant_breaks_round
#verify_constructive tooth_xor_constant_permutation_davies_meyer_collapses
#verify_constructive tooth_walsh_single_trail_is_not_the_hull

end Qsag

section
namespace Qsag
open MigrationExecution

set_option autoImplicit false

/-- Frame body of `cshake256_framed_xof` (`keccak.rs:281-284`). -/
def spnFramesU64LeBody : List (List UInt8) → List UInt8
  | [] => []
  | f :: fs => (encodeNatLeBytes 8 f.length ++ f) ++ spnFramesU64LeBody fs

/-- `cshake256_framed_xof` (`qsag-accel/src/keccak.rs`) over the `Qsag.Keccak` cSHAKE256 model. -/
def spnCshake256FramedXof (customization : List UInt8) (frames : List (List UInt8))
    (outLen : Nat) : List UInt8 :=
  cshake256Xof outLen customization
    (encodeNatLeBytes 8 frames.length ++ spnFramesU64LeBody frames)

/-- Rounds `m, …, m+n-1` of the Rust loop. -/
def rustSpnIterFrom (rcs : Nat → BitVec 128 × BitVec 128) (m : Nat) :
    Nat → BitVec 128 × BitVec 128 → BitVec 128 × BitVec 128
  | 0, st => st
  | n + 1, st => rustSpnRound (rcs (m + n)) (rustSpnIterFrom rcs m n st)

theorem rustSpnIter_add (rcs : Nat → BitVec 128 × BitVec 128) (m : Nat) :
    ∀ (n : Nat) (st : BitVec 128 × BitVec 128),
      rustSpnIter rcs (m + n) st = rustSpnIterFrom rcs m n (rustSpnIter rcs m st)
  | 0, _ => rfl
  | n + 1, st => by
    show rustSpnIter rcs (m + n + 1) st =
      rustSpnRound (rcs (m + n)) (rustSpnIterFrom rcs m n (rustSpnIter rcs m st))
    rw [rustSpnIter_succ, rustSpnIter_add rcs m n st]

/-- A segment of the loop is the loop over the shifted round-constant schedule. -/
theorem rustSpnIterFrom_eq_shift (rcs : Nat → BitVec 128 × BitVec 128) (m : Nat) :
    ∀ (n : Nat) (st : BitVec 128 × BitVec 128),
      rustSpnIterFrom rcs m n st = rustSpnIter (fun r => rcs (m + r)) n st
  | 0, st => (rustSpnIter_zero _ st).symm
  | n + 1, st => by
    show rustSpnRound (rcs (m + n)) (rustSpnIterFrom rcs m n st) = _
    rw [rustSpnIter_succ, rustSpnIterFrom_eq_shift rcs m n st]

/-- `pk_seed = 00 01 … 1f`. -/
def chainStepKatPkSeed : List UInt8 :=
  [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b,
   0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
   0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f]

/-- `cur = a0 a1 … bf`. -/
def chainStepKatCur : List UInt8 :=
  [0xa0, 0xa1, 0xa2, 0xa3, 0xa4, 0xa5, 0xa6, 0xa7, 0xa8, 0xa9, 0xaa, 0xab,
   0xac, 0xad, 0xae, 0xaf, 0xb0, 0xb1, 0xb2, 0xb3, 0xb4, 0xb5, 0xb6, 0xb7,
   0xb8, 0xb9, 0xba, 0xbb, 0xbc, 0xbd, 0xbe, 0xbf]

/-- Output printed by the compiled Rust `qsag_fts::parallel_mpc::parallel_chain_step` (label
    `POW7_ROUNDS.V5`) for `(pk_seed, epoch 7, chain_idx 3, step 2, cur)`. -/
def chainStepKatRustOutput : List UInt8 :=
  [0xad, 0xbf, 0xab, 0x95, 0x2b, 0x29, 0xd9, 0xe8, 0x89, 0x4d, 0xa4, 0x69,
   0xa7, 0xb1, 0xce, 0x40, 0xe3, 0x56, 0xec, 0xff, 0x1d, 0x50, 0x76, 0xac,
   0x46, 0xd7, 0x33, 0x34, 0x65, 0x7d, 0xc4, 0x61]

/-- The `48 * 32` bytes written by the compiled Rust `cshake256_framed_xof` for the frames of
    `round_constants(chainStepKatTweak)`. -/
def chainStepKatRustStream : List UInt8 :=
  [0x42, 0xcd, 0x4c, 0x60, 0x1c, 0x0c, 0x8d, 0x58, 0x98, 0x65, 0xfa, 0x2b,
   0xd7, 0x4e, 0x3a, 0x8a, 0xfd, 0x04, 0x9d, 0x0a, 0x7c, 0x73, 0x4f, 0x61,
   0x47, 0x00, 0xf6, 0x3c, 0xdb, 0x1a, 0x89, 0x7d, 0x61, 0xc0, 0x7c, 0xc6,
   0x37, 0xa6, 0x2f, 0xf0, 0x9b, 0x97, 0xe7, 0x1b, 0x12, 0x8c, 0x7e, 0x87,
   0x3b, 0x5e, 0x3d, 0x2e, 0xd8, 0x1b, 0xb2, 0x7f, 0xfc, 0x2c, 0xe6, 0x5f,
   0xc3, 0x26, 0xa6, 0x31, 0xf9, 0x79, 0x04, 0xa6, 0x04, 0x8e, 0x42, 0xdb,
   0x45, 0xd2, 0xea, 0x9c, 0xa0, 0x7e, 0x82, 0x9d, 0x3c, 0x7d, 0x01, 0xa9,
   0xd2, 0x2d, 0x1e, 0x25, 0x6a, 0xc2, 0x6d, 0xbe, 0x56, 0xfc, 0x5b, 0x52,
   0x67, 0x49, 0x60, 0xb1, 0xc1, 0x05, 0x37, 0x4c, 0xda, 0xb7, 0x04, 0x27,
   0x54, 0x7a, 0x98, 0xa2, 0xf9, 0xbf, 0xbd, 0x81, 0xd8, 0x8a, 0x57, 0x58,
   0xd7, 0x9c, 0x94, 0x4f, 0x24, 0xd0, 0xae, 0x85, 0xc7, 0xb1, 0x99, 0xca,
   0x24, 0x5a, 0x03, 0x56, 0x23, 0x81, 0x16, 0xb3, 0xb5, 0xcd, 0x4f, 0xa3,
   0x04, 0xe0, 0x81, 0x10, 0xeb, 0xff, 0x59, 0x01, 0x0b, 0x31, 0x87, 0xc7,
   0x66, 0x79, 0x2b, 0xd5, 0xa6, 0xd6, 0xd7, 0x6d, 0xb0, 0xc2, 0x57, 0xa7,
   0x31, 0x7a, 0xa1, 0x87, 0x65, 0xb0, 0x25, 0xb8, 0x34, 0x26, 0x38, 0xfb,
   0x5c, 0xcb, 0x96, 0x32, 0x89, 0xdc, 0x5f, 0x33, 0x7b, 0xed, 0x6a, 0x9b,
   0xec, 0x23, 0xd9, 0x69, 0xbb, 0x00, 0x01, 0x5b, 0x2c, 0x5f, 0x7a, 0x52,
   0xbd, 0xfa, 0x4a, 0x3c, 0x9b, 0x3c, 0x84, 0x0b, 0x98, 0xde, 0x34, 0xe1,
   0x02, 0x80, 0xdf, 0xc2, 0x41, 0x62, 0x36, 0xcd, 0x09, 0x06, 0x10, 0xea,
   0x2d, 0xbe, 0xb3, 0x7d, 0x76, 0x6f, 0x45, 0x56, 0x8b, 0xa3, 0x4d, 0x39,
   0xf3, 0xb3, 0xe0, 0xdc, 0x4b, 0x04, 0x40, 0xdf, 0xcf, 0x2a, 0x92, 0xad,
   0x39, 0xd0, 0x14, 0x64, 0xd1, 0x80, 0xbf, 0xed, 0x80, 0xdc, 0xb9, 0x54,
   0x1a, 0xd6, 0x4b, 0xf0, 0x84, 0xef, 0xcc, 0x49, 0x5f, 0x67, 0xbb, 0xaa,
   0x38, 0xab, 0xa4, 0xff, 0xc3, 0x0a, 0x68, 0x8c, 0x0a, 0x8e, 0x07, 0x10,
   0xf0, 0x87, 0xd4, 0x02, 0x27, 0xc7, 0x61, 0x1d, 0x31, 0xce, 0x7f, 0x0b,
   0x1e, 0x17, 0x08, 0x85, 0xe7, 0xc5, 0x26, 0x63, 0x02, 0x94, 0x31, 0x9e,
   0x39, 0xb0, 0xec, 0xf9, 0x07, 0x75, 0x89, 0xde, 0xca, 0xf2, 0xf4, 0x4b,
   0xff, 0x24, 0xbc, 0xb9, 0x36, 0x29, 0xb3, 0xff, 0x60, 0x6c, 0x64, 0x3d,
   0x03, 0x34, 0x96, 0x3e, 0x46, 0x2e, 0x76, 0x5c, 0xe4, 0x1c, 0xed, 0x71,
   0x20, 0x78, 0xcd, 0x33, 0x11, 0x2f, 0xcd, 0xab, 0x8a, 0xd8, 0xca, 0x75,
   0x11, 0xcc, 0xcd, 0xa1, 0x60, 0x8f, 0xf1, 0xea, 0xf3, 0x74, 0x1f, 0x38,
   0x58, 0x24, 0x3e, 0xbf, 0x8c, 0x39, 0xe3, 0x09, 0xd5, 0x36, 0x66, 0xbc,
   0x9b, 0x18, 0x38, 0xe0, 0x41, 0xa3, 0xf9, 0x41, 0xe9, 0xc3, 0xbe, 0xf7,
   0x1c, 0x2f, 0x4c, 0x2b, 0x1c, 0xaa, 0x92, 0x6b, 0x75, 0xf0, 0x6c, 0xd9,
   0x43, 0x4a, 0x8b, 0xca, 0xe7, 0xbc, 0x26, 0x73, 0xe2, 0xcf, 0xb8, 0x0a,
   0x75, 0x22, 0x52, 0x78, 0x18, 0x06, 0x69, 0x3c, 0xce, 0xb6, 0xa1, 0xc9,
   0x74, 0xdd, 0xcb, 0x42, 0xe2, 0x76, 0x1d, 0xb6, 0xd6, 0xf7, 0x8a, 0xf6,
   0xce, 0x6b, 0x9f, 0x86, 0xfd, 0x1a, 0x31, 0x9d, 0xa5, 0xa3, 0x30, 0x82,
   0x58, 0xcb, 0x4f, 0x52, 0x94, 0xea, 0x82, 0x35, 0x4c, 0x32, 0x09, 0xe8,
   0xdd, 0x43, 0x38, 0x75, 0xd6, 0x53, 0x25, 0x86, 0xd7, 0xba, 0x9b, 0xd2,
   0x59, 0xfc, 0x0c, 0xd5, 0xca, 0x36, 0x0a, 0xdc, 0x01, 0xc7, 0xe6, 0xc2,
   0x2e, 0xe8, 0x7e, 0x2b, 0x28, 0x89, 0x54, 0x19, 0xab, 0xeb, 0x1d, 0xa5,
   0x39, 0x9a, 0x81, 0xdb, 0x19, 0xfd, 0xd6, 0x34, 0x46, 0xba, 0xb3, 0xe4,
   0xec, 0xe1, 0x39, 0x61, 0xde, 0xe7, 0x22, 0x80, 0xbe, 0x24, 0x5b, 0x3b,
   0xc2, 0xf5, 0x8f, 0xbf, 0x70, 0xe2, 0x22, 0x5d, 0xa8, 0x02, 0xec, 0x23,
   0x96, 0xa5, 0x28, 0xe6, 0x42, 0xa5, 0xdf, 0xf5, 0xea, 0x5e, 0x6d, 0x59,
   0x66, 0x1a, 0x21, 0x25, 0xa3, 0xcf, 0x23, 0x22, 0x43, 0x6f, 0x17, 0x22,
   0x0f, 0xb3, 0xb2, 0x4c, 0x04, 0xfa, 0xe5, 0x64, 0xb2, 0x75, 0x72, 0x01,
   0x68, 0x30, 0x68, 0x2c, 0x53, 0xa6, 0x52, 0xf3, 0x85, 0x04, 0xe0, 0xd1,
   0x55, 0xb2, 0xfc, 0x80, 0x21, 0xf8, 0xcb, 0xa8, 0x70, 0x2f, 0x11, 0x37,
   0x5b, 0x66, 0xa1, 0x39, 0xee, 0x41, 0xc1, 0xde, 0xfe, 0xc1, 0x69, 0x45,
   0x9b, 0xbf, 0x8c, 0x3c, 0x23, 0xfa, 0xa8, 0x00, 0x49, 0xd9, 0x88, 0x4c,
   0xee, 0x80, 0xd2, 0x9f, 0x9c, 0x6d, 0xdc, 0x89, 0x1c, 0x25, 0xd6, 0x32,
   0x9c, 0xe4, 0x78, 0x0a, 0xc3, 0xf5, 0xee, 0xac, 0xfa, 0x30, 0x2d, 0xb2,
   0x77, 0x05, 0x86, 0x1e, 0x4d, 0xba, 0x91, 0xe4, 0xb4, 0x9e, 0x2c, 0x0d,
   0xb0, 0x4d, 0x74, 0xc5, 0xf2, 0xdb, 0x95, 0xa2, 0xe2, 0x5e, 0xba, 0xba,
   0xba, 0x36, 0x83, 0xb2, 0x99, 0xe2, 0x69, 0x41, 0x37, 0x93, 0x7e, 0x7e,
   0xd8, 0x13, 0x4a, 0xa1, 0xa7, 0x32, 0x07, 0x7b, 0xb2, 0x2d, 0x9f, 0xb4,
   0x43, 0x93, 0x14, 0x9e, 0xb0, 0x2f, 0xf5, 0x17, 0xcf, 0xb4, 0xff, 0x1e,
   0x1a, 0x9e, 0xfd, 0x38, 0xa7, 0x81, 0x72, 0x38, 0x72, 0xfa, 0x41, 0xac,
   0x5a, 0x83, 0x91, 0x88, 0xa2, 0x6e, 0xb7, 0x1f, 0x36, 0xfa, 0x43, 0xcb,
   0x80, 0x80, 0xd3, 0x4b, 0x7c, 0xaa, 0x98, 0xac, 0xc8, 0xb9, 0x77, 0x56,
   0x8e, 0xbe, 0xd5, 0xfe, 0xf2, 0xe8, 0xd3, 0x7e, 0x74, 0xdc, 0x0c, 0x43,
   0x1d, 0x8c, 0xd8, 0x29, 0x60, 0x76, 0x5a, 0xa0, 0xc4, 0x50, 0x09, 0x5f,
   0xb6, 0x76, 0xe7, 0xd4, 0xa5, 0x50, 0x0d, 0x2e, 0xb9, 0xa0, 0x91, 0xc4,
   0xea, 0x58, 0xa2, 0x74, 0xfc, 0x99, 0xd9, 0x44, 0x49, 0x99, 0x1a, 0xd4,
   0xb7, 0xdc, 0x53, 0x34, 0x06, 0xed, 0x9f, 0x79, 0x01, 0xf5, 0xbd, 0x44,
   0x57, 0x86, 0x78, 0x5d, 0xa2, 0xf0, 0x38, 0x6b, 0xc4, 0x7d, 0x14, 0x0a,
   0xe3, 0x65, 0xda, 0xd6, 0x09, 0xdd, 0xf0, 0xeb, 0x59, 0x7a, 0x46, 0xe3,
   0xf9, 0x7b, 0x44, 0xb8, 0xdf, 0xf4, 0xef, 0x43, 0x69, 0xfa, 0xdd, 0xb5,
   0x78, 0x66, 0xd0, 0xb0, 0xdb, 0x34, 0x05, 0x34, 0x9e, 0x98, 0x65, 0x4c,
   0xbe, 0x3b, 0x44, 0x7f, 0x14, 0xc5, 0x01, 0x99, 0xc3, 0xbc, 0x34, 0x6b,
   0xf8, 0x20, 0xd7, 0x29, 0xc1, 0x45, 0x12, 0x47, 0x87, 0x9e, 0x04, 0x5d,
   0xac, 0xef, 0xca, 0x61, 0xe4, 0xfc, 0x45, 0x05, 0x6e, 0xbe, 0xfe, 0x57,
   0xf0, 0x0c, 0x24, 0x52, 0x1c, 0x58, 0xb5, 0xa9, 0x08, 0x14, 0x7e, 0x53,
   0xab, 0xbd, 0x4b, 0xc9, 0x41, 0xe9, 0x71, 0x43, 0x53, 0x12, 0xda, 0x9f,
   0x3a, 0x6a, 0x07, 0x7e, 0xc5, 0xc4, 0x62, 0x0f, 0xd5, 0x2f, 0x3d, 0x22,
   0x94, 0x83, 0xe6, 0xe3, 0x02, 0xa0, 0x81, 0x4e, 0xc8, 0x2e, 0xcb, 0xb5,
   0xa3, 0x79, 0x23, 0x12, 0xcd, 0x20, 0x9e, 0x33, 0x0b, 0x7b, 0xc9, 0xfb,
   0x21, 0x73, 0xf6, 0x5c, 0x89, 0xb0, 0x68, 0xa1, 0x61, 0x58, 0x91, 0x51,
   0x0e, 0x65, 0x18, 0x67, 0xc6, 0x5c, 0x18, 0x87, 0x3b, 0x7a, 0x25, 0xea,
   0xbe, 0x0e, 0xd1, 0x9b, 0x5e, 0x5c, 0x26, 0x2d, 0xae, 0xce, 0xb0, 0xfb,
   0xce, 0x4c, 0x63, 0x8d, 0xbb, 0x38, 0x99, 0xb7, 0xf8, 0xa0, 0x1c, 0x2d,
   0x66, 0xcb, 0xf5, 0x4f, 0x2f, 0x31, 0x72, 0xea, 0x39, 0x72, 0x0e, 0x41,
   0x5d, 0x1c, 0x58, 0xa8, 0x12, 0x12, 0xd8, 0xaa, 0x73, 0x36, 0x35, 0x98,
   0x11, 0xa1, 0xba, 0x2e, 0x79, 0xe1, 0x5b, 0x45, 0xe6, 0xc3, 0xa1, 0xb9,
   0x59, 0x35, 0x56, 0x21, 0x5c, 0xb0, 0x30, 0xaa, 0x42, 0xe0, 0x97, 0x2d,
   0xde, 0xb9, 0x36, 0x01, 0x27, 0x53, 0xff, 0x96, 0xf8, 0x58, 0x33, 0xa0,
   0x85, 0x4c, 0x8e, 0x80, 0x3b, 0x64, 0x20, 0x32, 0x9c, 0xaa, 0xff, 0x69,
   0x10, 0xc1, 0x18, 0x03, 0x96, 0x8d, 0xf6, 0x2c, 0x43, 0xf3, 0xfb, 0x95,
   0xc7, 0x81, 0x14, 0xf2, 0x99, 0x56, 0xba, 0xc5, 0xbe, 0x9b, 0xc3, 0x4a,
   0xee, 0xca, 0x72, 0x0d, 0xb0, 0xe0, 0x16, 0xc7, 0x32, 0x95, 0x98, 0x56,
   0x62, 0x1b, 0xf6, 0xa0, 0xa4, 0x20, 0xb1, 0x7b, 0xff, 0x11, 0x67, 0xe7,
   0x1c, 0x31, 0x4d, 0xf2, 0xb0, 0x0b, 0x94, 0x81, 0x44, 0x18, 0x70, 0x7c,
   0xde, 0xd2, 0x22, 0xa6, 0x03, 0x99, 0xc0, 0xe6, 0xb0, 0x4a, 0xf9, 0x5d,
   0x70, 0xf7, 0xab, 0x2c, 0xfd, 0x48, 0x9d, 0x0f, 0x1b, 0xf5, 0xdd, 0xc7,
   0x7b, 0x86, 0xaa, 0x8c, 0xa6, 0xfc, 0x80, 0x1f, 0xbe, 0x77, 0xaf, 0x4d,
   0x40, 0xf1, 0xc9, 0x18, 0xf7, 0x05, 0xd6, 0xd9, 0x8f, 0x6c, 0x73, 0x70,
   0x66, 0x8b, 0x5e, 0x90, 0xf8, 0x91, 0xc8, 0x66, 0x3f, 0x3a, 0xe2, 0xea,
   0x5e, 0xb5, 0xb4, 0xdd, 0x47, 0xa8, 0x46, 0x9c, 0x65, 0xe1, 0x77, 0xd2,
   0x8f, 0x4d, 0x3d, 0x4b, 0x26, 0x2b, 0x34, 0xed, 0x79, 0x71, 0xfa, 0x2d,
   0x01, 0x47, 0x77, 0xc7, 0xa7, 0xe7, 0x5c, 0xf3, 0xfa, 0x51, 0x0a, 0x74,
   0x59, 0x27, 0xcf, 0xea, 0x4f, 0xc1, 0x7c, 0x0b, 0x46, 0x88, 0xbc, 0x6f,
   0xd6, 0xe2, 0xde, 0xd1, 0xaa, 0xea, 0x35, 0xc8, 0xd2, 0x1a, 0x4d, 0x52,
   0xd3, 0xf3, 0xbe, 0xe8, 0xe3, 0x45, 0x77, 0x23, 0x03, 0xf9, 0x55, 0x61,
   0xe8, 0x6b, 0x11, 0x2c, 0xcd, 0x6d, 0x7d, 0x21, 0x7a, 0x30, 0x41, 0xc7,
   0xc0, 0xa2, 0x96, 0xb1, 0x8c, 0x68, 0xdd, 0x41, 0x84, 0xf1, 0xc7, 0x08,
   0x3b, 0xbb, 0xce, 0x73, 0xc5, 0x7e, 0x3f, 0xec, 0xa3, 0xa7, 0x4b, 0xf7,
   0x65, 0xbc, 0xb6, 0xc5, 0x63, 0x66, 0x0c, 0x3a, 0x0e, 0x7e, 0xcd, 0x56,
   0x36, 0x50, 0x48, 0xf5, 0x0b, 0x9d, 0x71, 0x9a, 0xb2, 0x58, 0x65, 0xca,
   0x65, 0xa8, 0x0c, 0x90, 0x84, 0x65, 0x4e, 0x12, 0xef, 0xd8, 0x2b, 0x67,
   0x3e, 0x4e, 0xfe, 0x6c, 0xfc, 0x9d, 0x57, 0x38, 0xc0, 0xee, 0xf8, 0x05,
   0xfc, 0xc8, 0x3f, 0x68, 0x2c, 0x2e, 0xa8, 0x9e, 0xe8, 0x20, 0x83, 0x37,
   0xce, 0xa9, 0x0f, 0xd9, 0xbe, 0x32, 0x17, 0x6b, 0x78, 0x06, 0x38, 0xc8,
   0xaa, 0xa3, 0xe1, 0x8f, 0xc2, 0xb2, 0xa1, 0xce, 0x5f, 0xa6, 0xc8, 0x2e,
   0xc9, 0x52, 0x15, 0xc8, 0xc2, 0xc8, 0x8e, 0x08, 0xf2, 0xb0, 0x96, 0x7f,
   0x5a, 0x09, 0xd8, 0x4b, 0x93, 0xfa, 0xab, 0xd3, 0x7d, 0xe8, 0x37, 0x5d,
   0xa9, 0x28, 0x2c, 0x91, 0xaf, 0xa5, 0x4b, 0x79, 0x92, 0x6c, 0xbf, 0xbd,
   0xee, 0x04, 0x34, 0xa4, 0xf8, 0x7d, 0x54, 0x36, 0xfd, 0x20, 0x5d, 0x29,
   0x72, 0x4c, 0x98, 0xa7, 0xd4, 0xd0, 0x26, 0x2f, 0x75, 0x31, 0xc5, 0xf7,
   0xcc, 0xaf, 0x76, 0x7f, 0x83, 0x3a, 0xe8, 0x82, 0x34, 0x83, 0xd3, 0x1d,
   0x1f, 0x90, 0x8a, 0xa7, 0x0c, 0x7a, 0x67, 0x51, 0x4c, 0x6c, 0x10, 0x7b,
   0x51, 0xc2, 0x57, 0xa1, 0x4e, 0x90, 0x98, 0x14, 0x24, 0xbc, 0x34, 0x32,
   0xd0, 0xb1, 0x3b, 0x29, 0xc0, 0xc4, 0x59, 0x3e, 0x95, 0x4c, 0xaf, 0xbd,
   0xe9, 0x84, 0x13, 0x06, 0xed, 0x57, 0xaf, 0xe5, 0xcf, 0x74, 0x8d, 0x87,
   0x7b, 0x72, 0xf5, 0x7c, 0x27, 0x05, 0xbc, 0x1b, 0x22, 0xcb, 0x67, 0xe1,
   0x1a, 0x1e, 0xa6, 0xaa, 0x8e, 0x99, 0xc8, 0xa2, 0xda, 0xe6, 0x04, 0x5d,
   0xd6, 0xe2, 0x31, 0x7a, 0x52, 0x81, 0x36, 0x8b, 0xea, 0x21, 0x44, 0x48]

def chainStepKatTweak : BitVec 128 × BitVec 128 :=
  (0x4668a6864f7bee9787e94643de34423c#128, 0x2f7744435eb81c943103f437706a0e10#128)

/-- State after `8k` rounds, `k ≤ 6`. -/
def chainStepKatState : Nat → BitVec 128 × BitVec 128
  | 0 => (0xafaeadacabaaa9a8a7a6a5a4a3a2a1a0#128, 0xbfbebdbcbbbab9b8b7b6b5b4b3b2b1b0#128)
  | 1 => (0xcfe875a4c42ae20e39e3c0d879d92e23#128, 0x12aeeead5a863c075f0e3f5781c8fc65#128)
  | 2 => (0xaacba03cdc94eed5475d40f589cf70fb#128, 0xb27b201c28f45aa3898908dee0c22324#128)
  | 3 => (0x1b9c5eddf208544c6359ba10c764c7ac#128, 0x81b4b555b012a19261fa327c17c19872#128)
  | 4 => (0x33f373b7052ea3949bede8944c3727b0#128, 0xaf021355ca2d3f1bb60e2305d46ec3a2#128)
  | 5 => (0x4b7e30eded2d6a0e4cef9f0814972739#128, 0x66fa18039a7600e5ea17dea95196c3a1#128)
  | 6 => (0xef601c0bc20ee4214f7f8c8f36091e0d#128, 0xde7ac0d98f896efe1bc0e5a94c5ee753#128)
  | _ => (0#128, 0#128)

set_option maxRecDepth 8192 in
theorem chainStepKat_tweak :
    rustDeriveChainTweak spnCshake256FramedXof chainStepKatPkSeed 7 3 2 = chainStepKatTweak := by
  rw [rustDeriveChainTweak_eq, spnChainTweakCustomization_eq]
  rw [show spnCshake256FramedXof _ [chainStepKatPkSeed, be 4 7, be 2 3, [2]] 32 = _ from
    cshake256_chain_tweak_kat, rustBytes32ToLanes_eq]
  decide +kernel

theorem chainStepKat_lanes : rustBytes32ToLanes chainStepKatCur = chainStepKatState 0 := by
  rw [rustBytes32ToLanes_eq]
  decide +kernel

set_option maxRecDepth 65536 in
/-- The Lean cSHAKE256 model reproduces the whole Rust round-constant stream. -/
theorem chainStepKat_stream :
    rustSpnRoundConstantStream spnCshake256FramedXof chainStepKatTweak = chainStepKatRustStream := by
  rw [rustSpnRoundConstantStream_eq, rustU128ToLeBytes_eq, rustU128ToLeBytes_eq,
    spnPow7RoundsCustomization_eq]
  exact cshake256_pow7_round_stream_kat

/-- Round constants read from the Rust stream. -/
def chainStepKatRcs (round : Nat) : BitVec 128 × BitVec 128 :=
  rustBytes32ToLanes ((chainStepKatRustStream.drop (32 * round)).take 32)

theorem chainStepKat_rcs :
    rustSpnRoundConstants spnCshake256FramedXof chainStepKatTweak = chainStepKatRcs := by
  funext round
  unfold chainStepKatRcs
  rw [rustSpnRoundConstants_eq_stream, chainStepKat_stream]

/-- The six eight-round segments, from the kernel-evaluated field arithmetic of
    `rustSpnIter_chain_kat`; the hypothesis discharged here is that the 48 chunks of the Rust
    stream decode to its round-constant lanes. -/
theorem chainStepKat_segments :
    rustSpnIter (fun r => chainStepKatRcs (0 + r)) 8 (chainStepKatState 0) = chainStepKatState 1 ∧
    rustSpnIter (fun r => chainStepKatRcs (8 + r)) 8 (chainStepKatState 1) = chainStepKatState 2 ∧
    rustSpnIter (fun r => chainStepKatRcs (16 + r)) 8 (chainStepKatState 2) = chainStepKatState 3 ∧
    rustSpnIter (fun r => chainStepKatRcs (24 + r)) 8 (chainStepKatState 3) = chainStepKatState 4 ∧
    rustSpnIter (fun r => chainStepKatRcs (32 + r)) 8 (chainStepKatState 4) = chainStepKatState 5 ∧
    rustSpnIter (fun r => chainStepKatRcs (40 + r)) 8 (chainStepKatState 5) = chainStepKatState 6 :=
  rustSpnIter_chain_kat _ rfl chainStepKatRustStream (by
    intro r hr
    rw [rustBytes32ToLanes_eq]
    revert r
    decide +kernel)

set_option maxRecDepth 8192 in
theorem chainStepKat_rounds_0_8 :
    rustSpnIterFrom chainStepKatRcs 0 8
      (chainStepKatState 0) = chainStepKatState 1 := by
  rw [rustSpnIterFrom_eq_shift]
  exact chainStepKat_segments.1

set_option maxRecDepth 8192 in
theorem chainStepKat_rounds_8_16 :
    rustSpnIterFrom chainStepKatRcs 8 8
      (chainStepKatState 1) = chainStepKatState 2 := by
  rw [rustSpnIterFrom_eq_shift]
  exact chainStepKat_segments.2.1

set_option maxRecDepth 8192 in
theorem chainStepKat_rounds_16_24 :
    rustSpnIterFrom chainStepKatRcs 16 8
      (chainStepKatState 2) = chainStepKatState 3 := by
  rw [rustSpnIterFrom_eq_shift]
  exact chainStepKat_segments.2.2.1

set_option maxRecDepth 8192 in
theorem chainStepKat_rounds_24_32 :
    rustSpnIterFrom chainStepKatRcs 24 8
      (chainStepKatState 3) = chainStepKatState 4 := by
  rw [rustSpnIterFrom_eq_shift]
  exact chainStepKat_segments.2.2.2.1

set_option maxRecDepth 8192 in
theorem chainStepKat_rounds_32_40 :
    rustSpnIterFrom chainStepKatRcs 32 8
      (chainStepKatState 4) = chainStepKatState 5 := by
  rw [rustSpnIterFrom_eq_shift]
  exact chainStepKat_segments.2.2.2.2.1

set_option maxRecDepth 8192 in
theorem chainStepKat_rounds_40_48 :
    rustSpnIterFrom chainStepKatRcs 40 8
      (chainStepKatState 5) = chainStepKatState 6 := by
  rw [rustSpnIterFrom_eq_shift]
  exact chainStepKat_segments.2.2.2.2.2

theorem chainStepKat_rounds_0_48 :
    rustSpnIter chainStepKatRcs spnRounds
      (chainStepKatState 0) = chainStepKatState 6 := by
  let rcs := chainStepKatRcs
  have step : ∀ (m k : Nat), rustSpnIter rcs m (chainStepKatState 0) = chainStepKatState k →
      rustSpnIterFrom rcs m 8 (chainStepKatState k) = chainStepKatState (k + 1) →
      rustSpnIter rcs (m + 8) (chainStepKatState 0) = chainStepKatState (k + 1) :=
    fun m k hPrev hChunk =>
      (rustSpnIter_add rcs m 8 _).trans ((congrArg (rustSpnIterFrom rcs m 8) hPrev).trans hChunk)
  have h8 := step 0 0 (rustSpnIter_zero _ _) chainStepKat_rounds_0_8
  have h16 := step 8 1 h8 chainStepKat_rounds_8_16
  have h24 := step 16 2 h16 chainStepKat_rounds_16_24
  have h32 := step 24 3 h24 chainStepKat_rounds_24_32
  have h40 := step 32 4 h32 chainStepKat_rounds_32_40
  exact step 40 5 h40 chainStepKat_rounds_40_48

/-- **Executed-Rust agreement.** The Lean transcription of `parallel_chain_step`, evaluated by
    the kernel over the Lean cSHAKE256 model, returns the 32 bytes the compiled Rust function
    printed for the same arguments. -/
theorem rust_parallel_chain_step_executed_kat :
    rustParallelChainStep spnCshake256FramedXof chainStepKatPkSeed 7 3 2 chainStepKatCur =
      chainStepKatRustOutput := by
  have hStep : rustAlgebraicStep chainStepKatRcs (chainStepKatState 0) =
      ((chainStepKatState 6).1 ^^^ (chainStepKatState 0).1,
       (chainStepKatState 6).2 ^^^ (chainStepKatState 0).2) := by
    rw [rustAlgebraicStep_eq, chainStepKat_rounds_0_48]
  rw [rustParallelChainStep_eq, chainStepKat_tweak, chainStepKat_rcs, chainStepKat_lanes, hStep,
    rustLanesToBytes32_eq]
  decide +kernel


def buildFullTableReader (cardB : Nat) : (rem : Nat) → rem ≤ cardB →
    OracleComp (Fin cardB × Unit) Bool Bool
  | 0, _ => .pure false
  | m + 1, hm =>
    .query (⟨cardB - (m + 1), by omega⟩, ()) (fun b =>
      if b then .pure true else buildFullTableReader cardB m (by omega))

def oneQueryGuesser (cardB : Nat) (hPos : 0 < cardB) : OracleComp (Fin cardB × Unit) Bool Bool :=
  .query (⟨0, hPos⟩, ()) (fun b => .pure b)

def zeroQueryHardcoder (cardB : Nat) (c : Bool) : OracleComp (Fin cardB × Unit) Bool Bool :=
  .pure c

theorem lazyRo_query_regime_characterization (cardB : Nat) (hPos : 0 < cardB) (c : Bool) :
    natAbsDiff (keyedPrfRealAccept cardB (fun _ => false) (fun _ => true) (zeroQueryHardcoder cardB c))
               (keyedPrfIdealAccept cardB (fun _ => false) (zeroQueryHardcoder cardB c)) = 0 ∧
    (0 < natAbsDiff (keyedPrfRealAccept cardB (fun _ => false) (fun _ => true) (oneQueryGuesser cardB hPos))
                    (keyedPrfIdealAccept cardB (fun _ => false) (oneQueryGuesser cardB hPos)) ∧
     QueryBounded 1 (oneQueryGuesser cardB hPos)) ∧
    2 * 1 < natAbsDiff (keyedPrfRealAccept 8 (fun _ => false) (fun _ => true) (buildFullTableReader 8 8 (Nat.le_refl 8)))
                       (keyedPrfIdealAccept 8 (fun _ => false) (buildFullTableReader 8 8 (Nat.le_refl 8))) := by
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · rw [keyedPrfRealAccept_def, keyedPrfIdealAccept_def]
    unfold zeroQueryHardcoder evalOracleComp
    simp [natAbsDiff_eq]
  rotate_left
  · unfold oneQueryGuesser
    rw [QueryBounded_succ_query]
    intro y
    rw [QueryBounded_pure]
    exact True.intro
  · rw [keyedPrfRealAccept_def, keyedPrfIdealAccept_def, natAbsDiff_eq]
    decide
  · rw [keyedPrfRealAccept_def, keyedPrfIdealAccept_def]
    unfold oneQueryGuesser evalOracleComp
    have hIdeal0 : qsum cardB (fun _ => (0 : Nat)) = 0 := by rw [qsum_const]; omega
    have hReal1 :
        qsum cardB (fun kStar : Fin cardB =>
          if (if (⟨0, hPos⟩ : Fin cardB) = kStar then true else false) = true then 1 else 0) = 1 := by
      have hCongr :
          qsum cardB (fun kStar : Fin cardB =>
            if (if (⟨0, hPos⟩ : Fin cardB) = kStar then true else false) = true then 1 else 0) =
          qsum cardB (fun kStar : Fin cardB => if kStar = ⟨0, hPos⟩ then 1 else 0) := by
        apply qsum_congr
        intro kStar
        by_cases hk : kStar = ⟨0, hPos⟩
        · subst hk; simp
        · have hne : (⟨0, hPos⟩ : Fin cardB) ≠ kStar := fun h => hk h.symm
          simp [hk, hne]
      rw [hCongr, qsum_eq_indicator]
    change 0 < natAbsDiff
      (qsum cardB (fun kStar : Fin cardB =>
        if (if (⟨0, hPos⟩ : Fin cardB) = kStar then true else false) = true then 1 else 0))
      (qsum cardB (fun _ => 0))
    rw [hReal1, hIdeal0, natAbsDiff_eq]
    decide

/-- **`#tooth` BHT 256-Bit Unrestricted Collision Ceiling (`~85.3` Quantum Bits)**:
    A 256-bit untargeted hash does NOT provide 128-bit generic quantum collision resistance:
    at `qHash = 2 ^ 86` (`< 2 ^ 128`), `quantumBhtPureCubicBound 256 (2 ^ 86) = 2 ^ 258 / 2 ^ 256 > 1`
    (`exceedsBitBudget 0`), whereas a 384-bit output achieves `atLeastBits 128` up to `qHash < 2 ^ 84`
    even under `quantumBhtCollisionBound 384`! -/
theorem tooth_bht_256bit_unrestricted_collision_ceiling_85bits :
    exceedsBitBudget 0 (quantumBhtPureCubicBound 256 (2 ^ 86)) ∧
    exceedsBitBudget 128 (quantumBhtPureCubicBound 256 (2 ^ 43)) ∧
    (∀ qHash : Nat, qHash + 1 ≤ 2 ^ 84 →
      atLeastBits 129 (quantumBhtCollisionBound 384 qHash)) := by
  refine ⟨by unfold exceedsBitBudget; rw [quantumBhtPureCubicBound_eq]; decide,
          by unfold exceedsBitBudget; rw [quantumBhtPureCubicBound_eq]; decide, ?_⟩
  intro qHash hq
  unfold atLeastBits
  rw [quantumBhtCollisionBound_def]
  dsimp only
  have hCube : (qHash + 1) ^ 3 ≤ (2 ^ 84) ^ 3 := Nat.pow_le_pow_left hq 3
  have hPow : 8 * (2 ^ 84) ^ 3 * 2 ^ 129 ≤ 2 ^ 384 := by decide
  have h1 := Nat.mul_le_mul_left 8 hCube
  have h2 := Nat.mul_le_mul_right (2 ^ 129) h1
  exact Nat.le_trans h2 hPow


/-- `#tooth`: a compression function that forgets its right child is not binding, and the
    theorem's collision branch is the one that fires. -/
theorem tooth_merkle_right_blind_compression_collides :
    merkleRootFromPath (fun _ _ (a : Nat) _ => a) 0 0 7 [1] =
      merkleRootFromPath (fun _ _ (a : Nat) _ => a) 0 0 7 [2] ∧
    MerkleTweakCollision (fun _ _ (a : Nat) _ => a) := by
  have hRoot : ∀ s : Nat, merkleRootFromPath (fun _ _ (a : Nat) _ => a) 0 0 7 [s] = 7 := fun s =>
    (merkleRootFromPath_cons _ _ _ _ _ _).trans (merkleRootFromPath_nil _ _ _ _)
  refine ⟨(hRoot 1).trans (hRoot 2).symm, ?_⟩
  exact (MerkleTweakCollision_iff _).mpr ⟨0, 0, 7, 1, 7, 2, .inr (by decide), rfl⟩

#verify_constructive tooth_bht_256bit_unrestricted_collision_ceiling_85bits
#verify_constructive tooth_merkle_right_blind_compression_collides

end Qsag
end

namespace Qsag
/-! ### Concrete instance: `logLeaves = 3`, opened leaves `{1, 2, 6}` -/

/-- Cantor pairing on `Nat`, used as a toy digest combiner. -/
def canopyToyPair (a b : Nat) : Nat := (a + b) * (a + b + 1) / 2 + b

/-- Toy `hash_merkle_internal`: pairs the node index with the pair of children. -/
def canopyToyNodeHash (i l r : Nat) : Nat := canopyToyPair i (canopyToyPair l r)

/-- Toy `hash_tree_root`: pairs `logLeaves` with the top node. -/
def canopyToyRootHash (logLeaves top : Nat) : Nat := canopyToyPair logLeaves top

/-- Toy leaf digest of leaf `i`. -/
def canopyToyLeaf (i : Nat) : Nat := 100 + i

/-- Commitment of the full 8-leaf toy tree, computed node by node (not through the verifier). -/
def canopyToyCommitment : Nat :=
  canopyToyRootHash 3
    (canopyToyNodeHash 1
      (canopyToyNodeHash 2
        (canopyToyNodeHash 4 (canopyToyLeaf 0) (canopyToyLeaf 1))
        (canopyToyNodeHash 5 (canopyToyLeaf 2) (canopyToyLeaf 3)))
      (canopyToyNodeHash 3
        (canopyToyNodeHash 6 (canopyToyLeaf 4) (canopyToyLeaf 5))
        (canopyToyNodeHash 7 (canopyToyLeaf 6) (canopyToyLeaf 7))))

/-- Opened leaves `{1, 2, 6}` with their digests. -/
def canopyToyLeaves : List (Nat × Nat) :=
  [(1, canopyToyLeaf 1), (2, canopyToyLeaf 2), (6, canopyToyLeaf 6)]

/-- Steiner multiproof for `{1, 2, 6}`: leaves `0`, `3`, `7` at the bottom level and internal
    node `6` one level up; nodes `4, 5` and `2, 3` merge without consuming a digest. -/
def canopyToyProof : List Nat :=
  [canopyToyLeaf 0, canopyToyLeaf 3, canopyToyLeaf 7,
   canopyToyNodeHash 6 (canopyToyLeaf 4) (canopyToyLeaf 5)]

theorem canopyToy_honest_accepted :
    verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
      canopyToyLeaves canopyToyProof = true :=
  (canopy_toy_kats canopyToyNodeHash canopyToyRootHash rfl rfl canopyToyLeaf rfl
    canopyToyCommitment rfl canopyToyLeaves rfl canopyToyProof rfl).1

theorem canopyToy_sibling_count :
    steinerSiblingCount 3 [1, 2, 6] = 4 :=
  (canopy_toy_kats canopyToyNodeHash canopyToyRootHash rfl rfl canopyToyLeaf rfl
    canopyToyCommitment rfl canopyToyLeaves rfl canopyToyProof rfl).2.1

/-- A flipped sibling digest (leaf `7` replaced) is rejected. -/
theorem canopyToy_flipped_sibling_rejected :
    verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
      canopyToyLeaves
      [canopyToyLeaf 0, canopyToyLeaf 3, canopyToyLeaf 7 + 1,
       canopyToyNodeHash 6 (canopyToyLeaf 4) (canopyToyLeaf 5)] = false :=
  (canopy_toy_kats canopyToyNodeHash canopyToyRootHash rfl rfl canopyToyLeaf rfl
    canopyToyCommitment rfl canopyToyLeaves rfl canopyToyProof rfl).2.2.1

/-- `#tooth`: a proof differing from the honest one in a single sibling digest is rejected. -/
theorem tooth_canopy_sibling_mutation :
    ∃ proof : List Nat, proof ≠ canopyToyProof ∧
      verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
        canopyToyLeaves proof = false :=
  ⟨[canopyToyLeaf 0, canopyToyLeaf 3, canopyToyLeaf 7 + 1,
    canopyToyNodeHash 6 (canopyToyLeaf 4) (canopyToyLeaf 5)],
    by decide, canopyToy_flipped_sibling_rejected⟩

#tooth_pair canopyToy_honest_accepted vs tooth_canopy_sibling_mutation

/-- The exact-sibling-count premise is inhabited by the honest three-leaf opening. -/
theorem inhabited_canopy_nonempty_opening :
    ∃ (leaves : List (Nat × Nat)) (proof : List Nat),
      leaves = canopyToyLeaves ∧ proof = canopyToyProof ∧
      verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
        leaves proof = true :=
  ⟨canopyToyLeaves, canopyToyProof, rfl, rfl, canopyToy_honest_accepted⟩

#verify_inhabited verifyCanopyMultiproof_exact_sibling_count inhabited_canopy_nonempty_opening
#verify_constructive tooth_canopy_sibling_mutation inhabited_canopy_nonempty_opening

/-- A flipped leaf digest (leaf `2`) is rejected. -/
theorem canopyToy_flipped_leaf_rejected :
    verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
      [(1, canopyToyLeaf 1), (2, canopyToyLeaf 2 + 1), (6, canopyToyLeaf 6)]
      canopyToyProof = false :=
  (canopy_toy_kats canopyToyNodeHash canopyToyRootHash rfl rfl canopyToyLeaf rfl
    canopyToyCommitment rfl canopyToyLeaves rfl canopyToyProof rfl).2.2.2.1

/-- The proof with its last sibling removed is rejected. -/
theorem canopyToy_missing_sibling_rejected :
    verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
      canopyToyLeaves canopyToyProof.dropLast = false :=
  (canopy_toy_kats canopyToyNodeHash canopyToyRootHash rfl rfl canopyToyLeaf rfl
    canopyToyCommitment rfl canopyToyLeaves rfl canopyToyProof rfl).2.2.2.2.1

/-- The proof with one trailing digest appended is rejected. -/
theorem canopyToy_extra_sibling_rejected :
    verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
      canopyToyLeaves (canopyToyProof ++ [999]) = false :=
  (canopy_toy_kats canopyToyNodeHash canopyToyRootHash rfl rfl canopyToyLeaf rfl
    canopyToyCommitment rfl canopyToyLeaves rfl canopyToyProof rfl).2.2.2.2.2.1

/-- A duplicated index is rejected. -/
theorem canopyToy_duplicate_index_rejected :
    verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
      [(1, canopyToyLeaf 1), (1, canopyToyLeaf 1), (2, canopyToyLeaf 2), (6, canopyToyLeaf 6)]
      canopyToyProof = false :=
  (canopy_toy_kats canopyToyNodeHash canopyToyRootHash rfl rfl canopyToyLeaf rfl
    canopyToyCommitment rfl canopyToyLeaves rfl canopyToyProof rfl).2.2.2.2.2.2.1

/-- An unsorted index list is rejected. -/
theorem canopyToy_unsorted_index_rejected :
    verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
      [(2, canopyToyLeaf 2), (1, canopyToyLeaf 1), (6, canopyToyLeaf 6)]
      canopyToyProof = false :=
  (canopy_toy_kats canopyToyNodeHash canopyToyRootHash rfl rfl canopyToyLeaf rfl
    canopyToyCommitment rfl canopyToyLeaves rfl canopyToyProof rfl).2.2.2.2.2.2.2.1

/-- An index `≥ 2^logLeaves` is rejected. -/
theorem canopyToy_out_of_range_index_rejected :
    verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
      [(1, canopyToyLeaf 1), (2, canopyToyLeaf 2), (8, canopyToyLeaf 6)]
      canopyToyProof = false :=
  (canopy_toy_kats canopyToyNodeHash canopyToyRootHash rfl rfl canopyToyLeaf rfl
    canopyToyCommitment rfl canopyToyLeaves rfl canopyToyProof rfl).2.2.2.2.2.2.2.2.1

/-- **The exact-consumption check is load-bearing.** The relaxed verifier, which differs from
    `verifyCanopyMultiproof` only by ignoring unconsumed digests, accepts the honest proof with a
    trailing digest appended, while `verifyCanopyMultiproof` rejects the same input. -/
theorem canopyToy_relaxed_accepts_extra_sibling :
    verifyCanopyMultiproofRelaxed canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
      canopyToyLeaves (canopyToyProof ++ [999]) = true ∧
    verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
      canopyToyLeaves (canopyToyProof ++ [999]) = false :=
  ⟨(canopy_toy_kats canopyToyNodeHash canopyToyRootHash rfl rfl canopyToyLeaf rfl
    canopyToyCommitment rfl canopyToyLeaves rfl canopyToyProof rfl).2.2.2.2.2.2.2.2.2,
   (canopy_toy_kats canopyToyNodeHash canopyToyRootHash rfl rfl canopyToyLeaf rfl
    canopyToyCommitment rfl canopyToyLeaves rfl canopyToyProof rfl).2.2.2.2.2.1⟩

/-- Non-vacuity witness for §3: the honest toy opening is accepted, carries exactly
    `steinerSiblingCount` siblings, and every other opening of the same indices against the same
    commitment is rejected or exhibits a collision of the toy hashes. -/
theorem inhabited_canopy_multiproof_binding :
    verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
      canopyToyLeaves canopyToyProof = true ∧
    canopyToyProof.length = steinerSiblingCount 3 (canopyToyLeaves.map Prod.fst) ∧
    (∀ (leaves' : List (Nat × Nat)) (proof' : List Nat),
      leaves'.map Prod.fst = canopyToyLeaves.map Prod.fst →
      (leaves', proof') ≠ (canopyToyLeaves, canopyToyProof) →
      verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
        leaves' proof' = false ∨
      (∃ top₁ top₂ : Nat, top₁ ≠ top₂ ∧ canopyToyRootHash 3 top₁ = canopyToyRootHash 3 top₂) ∨
      (∃ (i l r l' r' : Nat), (l, r) ≠ (l', r') ∧
        canopyToyNodeHash i l r = canopyToyNodeHash i l' r')) :=
  ⟨canopyToy_honest_accepted,
   verifyCanopyMultiproof_exact_sibling_count canopyToyNodeHash canopyToyRootHash 3
     canopyToyCommitment canopyToyLeaves canopyToyProof canopyToy_honest_accepted,
   fun leaves' proof' hIdx hNe =>
     verifyCanopyMultiproof_tamper_rejected_or_collision canopyToyNodeHash canopyToyRootHash 3
       canopyToyCommitment canopyToyLeaves leaves' canopyToyProof proof'
       canopyToy_honest_accepted hIdx hNe⟩


/-- `#tooth` witness: with an empty pre-challenge query table (`queries = []`), a depth-1 opening
    cannot be online-extracted (`extractOnlineMerkleOpening = none`). -/
theorem tooth_onlineMerkle_empty_queries_unqueried_root :
    ¬ ∃ lp : Nat × List Nat,
      extractOnlineMerkleOpening 10 ([] : List (RecordedMerkleQuery Nat)) 0 1 0 = some lp := by
  rintro ⟨_, h⟩
  unfold extractOnlineMerkleOpening at h
  simp only [findFirst_nil] at h
  cases h




private def witnessInitVec : QVec 2 2 1 :=
  fun x y _ => if x.1 = 0 ∧ y.1 = 0 then ⟨1, 0⟩ else GaussInt.zero

private theorem witnessInitVec_pos : 0 < QVec.stateNormSq witnessInitVec :=
  qrom_witness_init_kat witnessInitVec rfl

private def witnessQuantumAdv : QuantumAdv 2 2 1 0 :=
  { init := witnessInitVec, h_init_pos := witnessInitVec_pos, steps := fun t => Fin.elim0 t }

private def witnessFailExtract (H : Fin 2 → BitVec 2) (x : Fin 2) : Bool :=
  decide ((H x).toNat = 0)

private def witnessProj (_ : Fin (2 * 1)) (x : Fin 2) : Fin 2 := x

private def witnessTargetSet (_ : Fin (2 * 1)) (_ : Fin 2 → BitVec 2) (_ : Fin 2) :
    List (BitVec 2) := [0#2]

private theorem witnessCoverProof (H : Fin 2 → BitVec 2) :
    QVec.queryMassOn (witnessFailExtract H) (runQuantumAdv witnessQuantumAdv H) ≤
      qsum (2 * 1) (fun r =>
        qromOrdinaryFlipMass witnessQuantumAdv H (witnessProj r) (fun _ _ => true)
          (fun O x => listHasElem (O x) (witnessTargetSet r O x))) := by
  have hPt : ∀ (ψ : QVec 2 2 1) (x : Fin 2),
      QVec.queryWeight ψ x ≤ QVec.queryMassOn (fun z => decide (x = z)) ψ := by
    intro ψ ⟨i, hi⟩
    match i, hi with
    | 0, _ =>
      rw [QVec.queryMassOn_def]; unfold qsum; dsimp only
      simp only [decide_true, ↓reduceIte]
      exact Nat.le_add_right _ _
    | 1, _ =>
      rw [QVec.queryMassOn_def]
      simp only [qsum, Fin.ext_iff, Nat.one_ne_zero, Nat.zero_add, decide_false, decide_true,
        Bool.false_eq_true, ↓reduceIte]
      omega
  have hLe : QVec.queryMassOn (witnessFailExtract H) (runQuantumAdv witnessQuantumAdv H) ≤
      qromOrdinaryFlipMass witnessQuantumAdv H (witnessProj ⟨0, by omega⟩) (fun _ _ => true)
        (fun O x => listHasElem (O x) (witnessTargetSet ⟨0, by omega⟩ O x)) := by
    rw [QVec.queryMassOn_def, qromOrdinaryFlipMass_def]
    unfold witnessFailExtract witnessProj witnessTargetSet
    apply qsum_le_qsum; intro x
    by_cases h0 : (H x).toNat = 0
    · have hBv : H x = 0#2 := BitVec.eq_of_toNat_eq h0
      have hElem : listHasElem (H x) [0#2] = true := by
        rw [hBv]; exact (listHasElem_eq_true_iff _ _).mpr List.mem_cons_self
      simp only [h0, decide_true, Bool.true_and, hElem, ↓reduceIte]
      exact hPt (runQuantumAdv witnessQuantumAdv H) x
    · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact Nat.zero_le _
  exact Nat.le_trans hLe (Nat.le_add_right _ _)

/-- Inhabitedness of the conditional target-hit premises: zero queries, two-bit answers,
    and constant singleton targets. This is not an inhabited Merkle extraction execution. -/
theorem inhabited_qrom_unitary_merkle_extract :
    ∃ (cardX w cardAnc Q numRoots : Nat)
      (A : QuantumAdv cardX w cardAnc Q)
      (failExtract : (Fin cardX → BitVec w) → Fin cardX → Bool)
      (proj : Fin (2 * numRoots) → Fin cardX → Fin cardX)
      (targetSet : Fin (2 * numRoots) → (Fin cardX → BitVec w) → Fin cardX → List (BitVec w)),
      (∀ r O x ch, targetSet r (reprogramOracle O x ch) x = targetSet r O x) ∧
      (∀ r O x, (targetSet r O x).length ≤ (if r.1 % 2 = 0 then 1 else 2 * Q + 1)) ∧
      (∀ H, QVec.queryMassOn (failExtract H) (runQuantumAdv A H) ≤
        qsum (2 * numRoots) (fun r =>
          qromOrdinaryFlipMass A H (proj r) (fun _ _ => true)
            (fun O x => listHasElem (O x) (targetSet r O x)))) :=
  ⟨2, 2, 1, 0, 1, witnessQuantumAdv, witnessFailExtract, witnessProj, witnessTargetSet,
    (fun _ _ _ _ => rfl),
    (fun _ _ _ => by unfold witnessTargetSet; simp),
    witnessCoverProof⟩




/-- A singleton adaptive target can contain the answer being tested. -/
def qromSelfTarget (H : Fin 1 → BitVec 1) (x : Fin 1) : List (BitVec 1) := [H x]

/-- Small target cardinality is insufficient: this event always succeeds, but changing its
    tested oracle coordinate changes its target list and violates `hLocal`. -/
theorem tooth_qrom_self_target_not_local :
    (∀ (H : Fin 1 → BitVec 1) (x : Fin 1),
      (qromSelfTarget H x).length = 1 ∧ listHasElem (H x) (qromSelfTarget H x) = true) ∧
    ¬ (∀ (H : Fin 1 → BitVec 1) (x : Fin 1) (ch : BitVec 1),
      qromSelfTarget (reprogramOracle H x ch) x = qromSelfTarget H x) := by
  constructor
  · intro H x
    simp [qromSelfTarget, listHasElem_eq_true_iff]
  · intro h
    have h01 := h (fun _ => 0#1) 0 1#1
    have hne : qromSelfTarget (reprogramOracle (fun _ : Fin 1 => 0#1) 0 1#1) 0 ≠
        qromSelfTarget (fun _ : Fin 1 => 0#1) 0 := by
      rw [reprogramOracle_def]
      decide
    exact hne h01

/-- Uniform query register, phase-kickback response, and a blank record register. -/
def qromParityInit : QVec 2 1 2 := fun _ y a =>
  if a.val = 0 then (if y.val = 0 then ⟨1, 0⟩ else ⟨-1, 0⟩) else GaussInt.zero

/-- The two input addresses have different oracle answers. -/
def qromParityOracle (x : Fin 2) : BitVec 1 := BitVec.ofFin x

/-- One coherent oracle call followed by a query-register Hadamard. -/
def qromParityAdv : QuantumAdv 2 1 2 1 where
  init := qromParityInit
  h_init_pos := (qrom_parity_kats qromParityInit _ rfl rfl).1
  steps := fun _ => hadamardQuery2 1 2

/-- The same initial state after copying the query address to an orthogonal record.
    This is the controlled-X copy on a blank ancilla, before the oracle call. -/
def qromRecordedParityInit : QVec 2 1 2 := fun x y a =>
  if a = x then (if y.val = 0 then ⟨1, 0⟩ else ⟨-1, 0⟩) else GaussInt.zero

def qromRecordedParityAdv : QuantumAdv 2 1 2 1 where
  init := qromRecordedParityInit
  h_init_pos := (qrom_parity_kats _ qromRecordedParityInit rfl rfl).2.1
  steps := fun _ => hadamardQuery2 1 2

/-- A classical record of the queried address destroys interference even for one query.
    Both final states have squared norm eight. The coherent circuit outputs one with
    probability one; retaining the address record changes that probability to one half.
    An online extractor therefore needs a proved disturbance/simulation bound, not just a
    consistent classical query list handed to `classifyOnlineMerkleOpening`. -/
theorem tooth_qrom_query_record_changes_born_probability :
    QVec.stateNormSq (runQuantumAdv qromParityAdv qromParityOracle) = 8 ∧
    QVec.stateNormSq (runQuantumAdv qromRecordedParityAdv qromParityOracle) = 8 ∧
    QVec.queryMassOn (fun x : Fin 2 => decide (x.val = 1))
      (runQuantumAdv qromParityAdv qromParityOracle) = 8 ∧
    QVec.queryMassOn (fun x : Fin 2 => decide (x.val = 1))
      (runQuantumAdv qromRecordedParityAdv qromParityOracle) = 4 :=
  ((qrom_parity_kats qromParityInit qromRecordedParityInit rfl rfl).2.2
    qromParityAdv qromRecordedParityAdv rfl rfl rfl rfl qromParityOracle rfl).1


/-! ## Executed example: the experiment is not the coherent run -/

/-- On the one-query parity circuit of `QromExtractionBoundary`, the coherent run puts mass
    8 of 8 on output one, while the measured experiment puts 4 of 8 there (two branches of
    mass 4 each). The bounds in this module are statements about the second number. -/
theorem measured_parity_execution :
    QVec.queryMassOn (fun x : Fin 2 => decide (x.val = 1))
      (runQuantumAdv qromParityAdv qromParityOracle) = 8 ∧
    sumLogs 2 1 (fun xs => QVec.queryMassOn (fun x : Fin 2 => decide (x.val = 1))
      (measuredStateAt qromParityAdv qromParityOracle 1 (Nat.le_refl 1) xs)) = 4 ∧
    sumLogs 2 1 (fun xs => QVec.stateNormSq
      (measuredStateAt qromParityAdv qromParityOracle 1 (Nat.le_refl 1) xs)) = 8 :=
  ((qrom_parity_kats qromParityInit qromRecordedParityInit rfl rfl).2.2
    qromParityAdv qromRecordedParityAdv rfl rfl rfl rfl qromParityOracle rfl).2



#verify_constructive inhabited_canopy_multiproof_binding
#verify_constructive tooth_onlineMerkle_empty_queries_unqueried_root
#tooth_pair Qsag.onlineMerkle_preChallenge_unique vs Qsag.tooth_onlineMerkle_empty_queries_unqueried_root
#verify_constructive witnessInitVec_pos
#verify_constructive witnessCoverProof
#verify_constructive inhabited_qrom_unitary_merkle_extract
#verify_inhabited Qsag.qrom_unitary_multiRoot_merkle_extract_bound Qsag.inhabited_qrom_unitary_merkle_extract
#verify_constructive tooth_qrom_self_target_not_local
#verify_constructive tooth_qrom_query_record_changes_born_probability

end Qsag

namespace Qsag
set_option maxRecDepth 10000 in
/-- Nonvacuity control in the QUANTUM game: the identity primitive makes the mode
constant, so every online adversary wins for every challenge. This does not describe
the actual SPN; it rules out deriving mode hardness from permutation laws alone. -/
theorem identityPublicPermutation_quantum_preimage_mass {anc q : Nat}
    (adversary : PublicSpnPreimageAdversary anc q) (challenge : PublicSpnState) :
    publicSpnPreimageMass identityPublicPermutation adversary challenge =
      QVec.stateNormSq (publicSpnPreimageFinalState identityPublicPermutation adversary challenge) := by
  rw [publicSpnPreimageMass_def]
  unfold QVec.stateNormSq
  simp only [QVec.queryWeight_def, publicSpnFeedForward_eq, identityPublicPermutation_forward,
    BitVec.xor_self, ↓reduceIte]


end Qsag

public section
set_option exponentiation.threshold 8192
namespace Qsag
open RoundPoly
/-- `x ↦ x ^ 3` identifies `ω₃ ≠ 1` with `1`, because `3 ∣ p - 1`. -/
theorem tooth_d3_not_permutation_on_goldilocks :
    goldilocksOmega3 ≠ Goldilocks.one ∧ goldilocksOmega3 ≠ Goldilocks.zero ∧
    goldilocksPow goldilocksOmega3 3 = goldilocksPow Goldilocks.one 3 ∧
    3 ∣ goldilocksPrime - 1 :=
  goldilocksOmega3_cube_collision


/-- `x ↦ x ^ 5` identifies `ω₅ ≠ 1` with `1`, because `5 ∣ p - 1`. -/
theorem tooth_d5_not_permutation_on_goldilocks :
    goldilocksOmega5 ≠ Goldilocks.one ∧ goldilocksOmega5 ≠ Goldilocks.zero ∧
    goldilocksPow goldilocksOmega5 5 = goldilocksPow Goldilocks.one 5 ∧
    5 ∣ goldilocksPrime - 1 :=
  goldilocksOmega5_fifth_power_collision


/-- The univariate degree alone stays below `2 ^ 85`: `7 ^ 30 > 2 ^ 128` is false, and `46`
    rounds would be the least count with `7 ^ r ≥ 2 ^ 128`. What exceeds `2 ^ 128` at `30` rounds
    is the square `(7 ^ 30) ^ 2`. -/
theorem tooth_univariate_degree_alone_below_two_pow_128 :
    7 ^ (8 + 22) < 2 ^ 85 ∧ 7 ^ 45 < 2 ^ 128 ∧ 2 ^ 128 ≤ 7 ^ 46 ∧
    2 ^ 128 < (7 ^ (8 + 22)) ^ 2 := by decide


theorem tooth_poseidon2_margin_fails_at_rp17 : ¬ Poseidon2InterpolationMargin 16 8 17 :=
  fun h => by
    have := poseidon2_interpolation_margin_needs_26 16 8 17 (by decide) h
    omega




private theorem gold_add_cring_here (a b : Goldilocks) :
    Goldilocks.add a b = CommRingOps.add a b := by rfl
private theorem gold_sub_cring_here (a b : Goldilocks) :
    Goldilocks.sub a b = CommRingOps.sub a b := by rfl
private theorem gold_mul_cring_here (a b : Goldilocks) :
    Goldilocks.mul a b = CommRingOps.mul a b := by rfl
private theorem gold_neg_cring_here (a : Goldilocks) :
    Goldilocks.neg a = CommRingOps.neg a := by rfl
private theorem gold_zero_cring_here : Goldilocks.zero = (CommRingOps.zero : Goldilocks) := by rfl
private theorem gold_one_cring_here : Goldilocks.one = (CommRingOps.one : Goldilocks) := by rfl
private theorem gold_2_cring_here : Goldilocks.ofNat 2 = CRing.natCast 2 := by decide +kernel
private theorem gold_3_cring_here : Goldilocks.ofNat 3 = CRing.natCast 3 := by decide +kernel
private theorem gold_4_cring_here : Goldilocks.ofNat 4 = CRing.natCast 4 := by decide +kernel

/-- `gold_cring` of `Qsag.Oracle.Poseidon2`, over bridge lemmas visible in this module: the
    library macro cites lemmas private to its module, so outside it the bridge step is skipped. -/
local macro "gold_cring_here" : tactic => `(tactic| (
  try dsimp only
  try simp only [gold_add_cring_here, gold_sub_cring_here, gold_mul_cring_here,
    gold_neg_cring_here, gold_zero_cring_here, gold_one_cring_here, gold_2_cring_here,
    gold_3_cring_here, gold_4_cring_here]
  try (open scoped Qsag.CRing in constructive_ring)))

/-- `#tooth` **Merz–Rodríguez García (`2026/306`) `(X, -X, 0)` Subspace & Partial Feed-Forward Vulnerability**:
    1. On the block-circulant factor `applyMEStd = P_3 ⊗ M_4 = circ(2 M_4, M_4, M_4)` (the external layer before the `M_4 ⊗ P_3` lane transposition was deployed), the entire 4-dimensional subspace
       `⟨X, -X, 0⟩` maps to `⟨M_4 X, -M_4 X, 0⟩`, leaving the sponge capacity block `b2 = 0` untouched!
    2. Across a full round `sboxState12 (state12Add (applyMEStd ⟨U0 + X, -X, U2⟩) C)` under the two linear
       antisymmetry conditions `(applyMEStd ⟨U0, 0, U2⟩).b0 + C.b0 = -((applyMEStd ⟨U0, 0, U2⟩).b1 + C.b1)`,
       oddness of `sbox7` preserves `(X^(1), -X^(1))` in blocks `0, 1` while keeping block `b2` independent of `X`!
    3. Partial feed-forward `(perm st).b0 + st.b0` (`poseidon2_compress12_ff` in `sponge.rs`) and naive
       uniform sum `st.b0 + st.b1 + st.b2` leave `(0, X, -X)` canceled in the feed-forward term. -/
theorem tooth_poseidon2_me_std_admits_x_neg_x_subspace_skip (X U0 U2 : Lane4)
    (C : Poseidon2State12)
    (hAnti : lane4Add (applyMEStd ⟨U0, lane4Zero, U2⟩).b0 C.b0 =
             lane4Neg (lane4Add (applyMEStd ⟨U0, lane4Zero, U2⟩).b1 C.b1)) :
    applyMEStd ⟨X, lane4Neg X, lane4Zero⟩ = ⟨applyM4 X, lane4Neg (applyM4 X), lane4Zero⟩ ∧
    let afterSbox := sboxState12 (state12Add (applyMEStd ⟨lane4Add U0 X, lane4Neg X, U2⟩) C)
    afterSbox.b1 = lane4Neg afterSbox.b0 ∧
    afterSbox.b2 = sboxLane4 (lane4Add (applyMEStd ⟨U0, lane4Zero, U2⟩).b2 C.b2) ∧
    (⟨U0, X, lane4Neg X⟩ : Poseidon2State12).b0 = U0 ∧
    lane4Add (lane4Add U0 X) (lane4Neg X) = U0 := by
  have hLinSub : applyMEStd ⟨X, lane4Neg X, lane4Zero⟩ =
      ⟨applyM4 X, lane4Neg (applyM4 X), lane4Zero⟩ := by
    unfold applyMEStd
    simp only [lane4Neg_eq, applyM4_eq, lane4Add_eq, lane4Sub_eq, lane4Sum_eq, lane4Zero_eq]
    apply Poseidon2State12.ext <;> apply Lane4.ext <;> gold_cring_here
  have hDecomp : ⟨lane4Add U0 X, lane4Neg X, U2⟩ =
      state12Add ⟨U0, lane4Zero, U2⟩ ⟨X, lane4Neg X, lane4Zero⟩ := by
    simp only [state12Add_eq, lane4Add_eq, lane4Neg_eq, lane4Sub_eq, lane4Zero_eq]
    apply Poseidon2State12.ext <;> apply Lane4.ext <;> gold_cring_here
  refine ⟨hLinSub, ?_, ?_, rfl, ?_⟩
  · rw [hDecomp, applyMEStd_add, hLinSub]
    simp only [state12Add_eq, sboxState12_eq]
    have hHelper : ∀ (M0 M1 A C0 C1 : Lane4),
        lane4Add M0 C0 = lane4Neg (lane4Add M1 C1) →
        lane4Add (lane4Add M1 (lane4Neg A)) C1 = lane4Neg (lane4Add (lane4Add M0 A) C0) := by
      intro M0 M1 A C0 C1 hEq
      have h0 := congrArg Lane4.x0 hEq
      have h1 := congrArg Lane4.x1 hEq
      have h2 := congrArg Lane4.x2 hEq
      have h3 := congrArg Lane4.x3 hEq
      simp only [lane4Add_eq, lane4Neg_eq, lane4Sub_eq, lane4Zero_eq] at h0 h1 h2 h3 ⊢
      have hInv : ∀ a : Goldilocks, Goldilocks.sub Goldilocks.zero (Goldilocks.sub Goldilocks.zero a) = a :=
        fun _ => by gold_cring_here
      apply Lane4.ext
      · have hL : Goldilocks.add (Goldilocks.add M1.x0 (Goldilocks.sub Goldilocks.zero A.x0)) C1.x0 =
            Goldilocks.sub (Goldilocks.add M1.x0 C1.x0) A.x0 := by gold_cring_here
        have rhsEq : Goldilocks.sub Goldilocks.zero (Goldilocks.add (Goldilocks.add M0.x0 A.x0) C0.x0) =
            Goldilocks.sub (Goldilocks.sub Goldilocks.zero (Goldilocks.add M0.x0 C0.x0)) A.x0 := by gold_cring_here
        have hFlip : Goldilocks.add M1.x0 C1.x0 = Goldilocks.sub Goldilocks.zero (Goldilocks.add M0.x0 C0.x0) := by
          have := congrArg (Goldilocks.sub Goldilocks.zero) h0
          rw [hInv] at this
          exact this.symm
        rw [hL, rhsEq, hFlip]
      · have hL : Goldilocks.add (Goldilocks.add M1.x1 (Goldilocks.sub Goldilocks.zero A.x1)) C1.x1 =
            Goldilocks.sub (Goldilocks.add M1.x1 C1.x1) A.x1 := by gold_cring_here
        have rhsEq : Goldilocks.sub Goldilocks.zero (Goldilocks.add (Goldilocks.add M0.x1 A.x1) C0.x1) =
            Goldilocks.sub (Goldilocks.sub Goldilocks.zero (Goldilocks.add M0.x1 C0.x1)) A.x1 := by gold_cring_here
        have hFlip : Goldilocks.add M1.x1 C1.x1 = Goldilocks.sub Goldilocks.zero (Goldilocks.add M0.x1 C0.x1) := by
          have := congrArg (Goldilocks.sub Goldilocks.zero) h1
          rw [hInv] at this
          exact this.symm
        rw [hL, rhsEq, hFlip]
      · have hL : Goldilocks.add (Goldilocks.add M1.x2 (Goldilocks.sub Goldilocks.zero A.x2)) C1.x2 =
            Goldilocks.sub (Goldilocks.add M1.x2 C1.x2) A.x2 := by gold_cring_here
        have rhsEq : Goldilocks.sub Goldilocks.zero (Goldilocks.add (Goldilocks.add M0.x2 A.x2) C0.x2) =
            Goldilocks.sub (Goldilocks.sub Goldilocks.zero (Goldilocks.add M0.x2 C0.x2)) A.x2 := by gold_cring_here
        have hFlip : Goldilocks.add M1.x2 C1.x2 = Goldilocks.sub Goldilocks.zero (Goldilocks.add M0.x2 C0.x2) := by
          have := congrArg (Goldilocks.sub Goldilocks.zero) h2
          rw [hInv] at this
          exact this.symm
        rw [hL, rhsEq, hFlip]
      · have hL : Goldilocks.add (Goldilocks.add M1.x3 (Goldilocks.sub Goldilocks.zero A.x3)) C1.x3 =
            Goldilocks.sub (Goldilocks.add M1.x3 C1.x3) A.x3 := by gold_cring_here
        have rhsEq : Goldilocks.sub Goldilocks.zero (Goldilocks.add (Goldilocks.add M0.x3 A.x3) C0.x3) =
            Goldilocks.sub (Goldilocks.sub Goldilocks.zero (Goldilocks.add M0.x3 C0.x3)) A.x3 := by gold_cring_here
        have hFlip : Goldilocks.add M1.x3 C1.x3 = Goldilocks.sub Goldilocks.zero (Goldilocks.add M0.x3 C0.x3) := by
          have := congrArg (Goldilocks.sub Goldilocks.zero) h3
          rw [hInv] at this
          exact this.symm
        rw [hL, rhsEq, hFlip]
    have hSumAnti := hHelper (applyMEStd ⟨U0, lane4Zero, U2⟩).b0 (applyMEStd ⟨U0, lane4Zero, U2⟩).b1
      (applyM4 X) C.b0 C.b1 hAnti
    rw [hSumAnti]
    simp only [lane4Neg_eq, lane4Sub_eq, lane4Zero_eq]
    exact Lane4.ext (sbox7_odd _) (sbox7_odd _) (sbox7_odd _) (sbox7_odd _)
  · rw [hDecomp, applyMEStd_add, hLinSub]
    simp only [state12Add_eq, sboxState12_eq, sboxLane4_eq]
    have hAddZ : ∀ a : Lane4, lane4Add a lane4Zero = a := fun a => by
      rw [lane4Add_eq, lane4Zero_eq]; apply Lane4.ext <;> exact LawfulCommRing.add_zero _
    rw [hAddZ]
  · simp only [lane4Add_eq, lane4Neg_eq, lane4Sub_eq, lane4Zero_eq]
    apply Lane4.ext <;> gold_cring_here


/-- Superseded internal diffusion matrix `diag(-2, 1, 2, 4, ..., 1024) + 1·1ᵀ` (first diagonal entry
    `-2`; the deployed `applyMI` uses `-64`). Kept only as the object of the tooth below. -/
def applyMIFirstEntryNegTwo (st : Poseidon2State12) : Poseidon2State12 :=
  let s := state12Sum st
  ⟨⟨Goldilocks.add (Goldilocks.mul (goldOfInt (-2)) st.b0.x0) s,
    Goldilocks.add st.b0.x1 s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 2) st.b0.x2) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 4) st.b0.x3) s⟩,
   ⟨Goldilocks.add (Goldilocks.mul (goldOfInt 8) st.b1.x0) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 16) st.b1.x1) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 32) st.b1.x2) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 64) st.b1.x3) s⟩,
   ⟨Goldilocks.add (Goldilocks.mul (goldOfInt 128) st.b2.x0) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 256) st.b2.x1) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 512) st.b2.x2) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 1024) st.b2.x3) s⟩⟩

/-- Explicit 12-lane Goldilocks eigenvector of `applyMIFirstEntryNegTwo` for eigenvalue
    `λ₀ = 8914261387277420341`. -/
def miRationalEigvec0 : Poseidon2State12 :=
  ⟨⟨Goldilocks.ofNat 8415733694666260766, Goldilocks.ofNat 10081604446170657914,
    Goldilocks.ofNat 13429757962329074280, Goldilocks.ofNat 7212905167159261059⟩,
   ⟨Goldilocks.ofNat 7177536167446655380, Goldilocks.ofNat 16173559831921257667,
    Goldilocks.ofNat 11410676009809774369, Goldilocks.ofNat 263994636750658321⟩,
   ⟨Goldilocks.ofNat 11338638786567724180, Goldilocks.ofNat 17416777037312523837,
    Goldilocks.ofNat 8867871345638664998, Goldilocks.ofNat 17338153400129577477⟩⟩

/-- `#tooth` **The superseded `V[0] = -2` internal matrix has a rational eigenvector over Goldilocks**:
    `applyMIFirstEntryNegTwo miRationalEigvec0 = λ₀ · miRationalEigvec0` with `miRationalEigvec0 ≠ 0`, so
    `diag(-2, 1, 2, ..., 1024) + 1·1ᵀ` has a reducible characteristic polynomial over `𝔽_p`. The same
    vector is not an eigenvector of the deployed `applyMI` for `λ₀`. -/
theorem tooth_current_mi_has_rational_eigenvector :
    miRationalEigvec0 ≠ state12Zero ∧
    applyMIFirstEntryNegTwo miRationalEigvec0 =
      state12Scale (Goldilocks.ofNat 8914261387277420341) miRationalEigvec0 ∧
    ¬ (applyMI miRationalEigvec0 =
      state12Scale (Goldilocks.ofNat 8914261387277420341) miRationalEigvec0) :=
  superseded_mi_rational_eigenvector_kat applyMIFirstEntryNegTwo rfl miRationalEigvec0 rfl


/-- `#tooth` **Reduced-Round `(R_F = 4, R_P = 10)` & Single-Initial-Round GSR Failure (`tooth_reduced_poseidon2_fails_cico_and_gsr`)**:
    1. At `(R_F = 4, R_P = 10)` (`14` rounds), univariate degree `7^14 < goldilocksPrime` and half-full +
       partial Bézout degree `7^(12 * (4 / 2) + 10) = 7^34 < 2^128` both fail!
    2. If initial full rounds were reduced from `R_F0 = 4` to `R_F0 = 1` (`2026/1692` GSR premise),
       univariate CICO-1 degree drops to `7^(22 + 4 - 12 + 2) = 7^16 < goldilocksPrime`! -/
theorem tooth_reduced_poseidon2_fails_cico_and_gsr :
    7 ^ (4 + 10) < goldilocksPrime ∧
    7 ^ (12 * (4 / 2) + 10) < 2 ^ 128 ∧
    7 ^ (22 + 4 - 12 + 2) < goldilocksPrime := by decide


theorem witness_poseidon2_margin : ∃ t rF rP, Poseidon2InterpolationMargin t rF rP :=
  ⟨12, 8, 22, poseidon2_interpolation_margin_width12⟩


#verify_constructive tooth_d3_not_permutation_on_goldilocks
#verify_constructive tooth_d5_not_permutation_on_goldilocks
#verify_constructive tooth_univariate_degree_alone_below_two_pow_128
#verify_constructive tooth_poseidon2_margin_fails_at_rp17
#tooth_pair Qsag.poseidon2_interpolation_margin_needs_26 vs Qsag.tooth_poseidon2_margin_fails_at_rp17
#verify_constructive tooth_poseidon2_me_std_admits_x_neg_x_subspace_skip
#verify_constructive tooth_current_mi_has_rational_eigenvector
#verify_constructive tooth_reduced_poseidon2_fails_cico_and_gsr
#verify_constructive witness_poseidon2_margin
#verify_inhabited Qsag.poseidon2_interpolation_margin_needs_26 Qsag.witness_poseidon2_margin

end Qsag
end

public section
set_option exponentiation.threshold 8192
namespace Qsag

set_option autoImplicit false

def toyMerkleEncode (u v : BitVec 1) : Fin 4 :=
  ⟨2 * u.toFin.val + v.toFin.val, by have := u.toFin.isLt; have := v.toFin.isLt; omega⟩

def toyMerkleDecode (x : Fin 4) : Nat × Nat × BitVec 1 × BitVec 1 :=
  (0, 0, BitVec.ofNat 1 (x.val / 2), BitVec.ofNat 1 (x.val % 2))

def toyMerkleLayout : MerkleAddressLayout 4 1 where
  encode := fun _ _ u v => toyMerkleEncode u v
  decode := fun x => some (toyMerkleDecode x)
  levels := 1
  nodes := 1
  decode_sound := by
    intro x l n u v h
    have h' := Option.some.inj h
    have hu : BitVec.ofNat 1 (x.val / 2) = u := congrArg (fun τ => τ.2.2.1) h'
    have hv : BitVec.ofNat 1 (x.val % 2) = v := congrArg (fun τ => τ.2.2.2) h'
    rw [← hu, ← hv]
    clear h h' hu hv
    revert x
    decide
  decode_encode := by
    intro l n u v hl hn
    have hl0 : l = 0 := by omega
    have hn0 : n = 0 := by omega
    subst hl0 hn0
    cases u with | ofFin fu =>
    cases v with | ofFin fv =>
    revert fu fv
    decide

/-- Basis state at query address `x₀`, zero response register. -/
def toyBasisInit (x₀ : Fin 4) : QVec 4 1 1 := fun x y _ =>
  if x = x₀ ∧ y.val = 0 then ⟨1, 0⟩ else GaussInt.zero

def toyQueryAdv (x₀ : Fin 4) (h : 0 < QVec.stateNormSq (toyBasisInit x₀)) : QuantumAdv 4 1 1 1 where
  init := toyBasisInit x₀
  h_init_pos := h
  steps := fun _ => ScaledUnitary.id 4 1 1

theorem toyBasisInit_pos (x₀ : Fin 4) : 0 < QVec.stateNormSq (toyBasisInit x₀) :=
  (qrom_toy_merkle_kats toyBasisInit rfl).1 x₀

/-- Every output claims: root `0`, index `0`, leaf `0`, sibling `1`. The verifier therefore
    evaluates the oracle at address `2 * 0 + 1 = 1`. -/
def toyOpening (_ : Fin 4) : MerkleOpeningReadout 1 := ⟨0#1, 0, 0#1, [1#1]⟩

/-- Acceptance without the extraction comparison. -/
def toyAccepted (H : Fin 4 → BitVec 1) (o : Fin 4) : Bool :=
  decide (merkleRootFromPath (toyMerkleLayout.hash H) 0 (toyOpening o).idx (toyOpening o).leaf
    (toyOpening o).path = (toyOpening o).rt)

theorem toy_measured_merkle_execution :
    let honest := toyQueryAdv ⟨1, by decide⟩ (toyBasisInit_pos _)
    let guesser := toyQueryAdv ⟨0, by decide⟩ (toyBasisInit_pos _)
    -- both are accepted on 8 of the 16 oracles
    uniformOracleSum 1 4 (fun H => sumLogs 4 1 (fun xs =>
      QVec.queryMassOn (toyAccepted H) (measuredStateAt honest H 1 (Nat.le_refl 1) xs))) = 8 ∧
    uniformOracleSum 1 4 (fun H => sumLogs 4 1 (fun xs =>
      QVec.queryMassOn (toyAccepted H) (measuredStateAt guesser H 1 (Nat.le_refl 1) xs))) = 8 ∧
    -- the honest log always yields the opening; the other log never does
    uniformOracleSum 1 4 (fun H => sumLogs 4 1 (fun xs =>
      QVec.queryMassOn (measuredMerkleFailure toyMerkleLayout 0 1 toyOpening H xs)
        (measuredStateAt honest H 1 (Nat.le_refl 1) xs))) = 0 ∧
    uniformOracleSum 1 4 (fun H => sumLogs 4 1 (fun xs =>
      QVec.queryMassOn (measuredMerkleFailure toyMerkleLayout 0 1 toyOpening H xs)
        (measuredStateAt guesser H 1 (Nat.le_refl 1) xs))) = 8 ∧
    (2 ^ 1) ^ 4 * (prefixScale guesser 1 (Nat.le_refl 1) * QVec.stateNormSq guesser.init) = 16 :=
  ((qrom_toy_merkle_kats toyBasisInit rfl).2 toyMerkleLayout rfl rfl rfl rfl
    (toyQueryAdv ⟨1, by decide⟩ (toyBasisInit_pos _))
    (toyQueryAdv ⟨0, by decide⟩ (toyBasisInit_pos _)) rfl rfl rfl rfl toyOpening rfl toyAccepted rfl).1

/-- The toy adversaries are classical-address adversaries, so `ClassicalQueryAddresses` is
    satisfiable and the transfer theorem applies to them. -/
theorem toyQueryAdv_classical (x₀ : Fin 4) (h : 0 < QVec.stateNormSq (toyBasisInit x₀)) :
    ClassicalQueryAddresses (toyQueryAdv x₀ h) (fun _ _ => x₀) := by
  refine (ClassicalQueryAddresses_iff _ _).mpr ?_
  intro H t ht x y a hx
  have ht0 : t = 0 := by omega
  subst ht0
  rw [advStateAt_zero]
  show (if x = x₀ ∧ y.val = 0 then (⟨1, 0⟩ : GaussInt) else GaussInt.zero) = GaussInt.zero
  exact ite_eq_right (fun hh => hx hh.1)

/-- The coherent run of the non-querying-the-right-address adversary, with its own address
    log `[0]`, has failure mass 8 of 16: the value the measured experiment gave, as the
    transfer theorem states, and within the general bound `(1 * 4 + 0) / 2`. -/
theorem toy_classical_run_execution :
    let guesser := toyQueryAdv ⟨0, by decide⟩ (toyBasisInit_pos _)
    uniformOracleSum 1 4 (fun H =>
      QVec.queryMassOn (measuredMerkleFailure toyMerkleLayout 0 1 toyOpening H
          (classicalQueryLog (fun _ _ => (⟨0, by decide⟩ : Fin 4)) H 1))
        (runQuantumAdv guesser H)) = 8 ∧
    2 ^ 1 * 8 ≤ (1 * (3 * 1 + 1) + triangleSum 1) *
      ((2 ^ 1) ^ 4 * (prefixScale guesser 1 (Nat.le_refl 1) * QVec.stateNormSq guesser.init)) :=
  ((qrom_toy_merkle_kats toyBasisInit rfl).2 toyMerkleLayout rfl rfl rfl rfl
    (toyQueryAdv ⟨1, by decide⟩ (toyBasisInit_pos _))
    (toyQueryAdv ⟨0, by decide⟩ (toyBasisInit_pos _)) rfl rfl rfl rfl toyOpening rfl toyAccepted rfl).2

#verify_constructive
  Qsag.toy_measured_merkle_execution
  Qsag.toyQueryAdv_classical
  Qsag.toy_classical_run_execution

end Qsag
end

public section
set_option exponentiation.threshold 8192
namespace Qsag.CrossProtocol
open CommRingOps LawfulCommRing
/-- Explicit permutation: raw inversion succeeds, adding the recovered input fails. -/
theorem raw_vs_feedforward_tooth :
    ∃ p : SimpleEquiv (State Goldilocks) (State Goldilocks),
      rawTrunc p (p.invFun (one, zero, zero)) = one ∧
      jiveCompress (fun _ => zero) p (p.invFun (one, zero, zero)) ≠ one := by
  refine ⟨SimpleEquiv.refl _, raw_inverse _ _ _ _, ?_⟩
  rw [jiveCompress_eq]
  decide


/-- Feed-forward does not guarantee security for every fixed permutation. -/
theorem identity_collision_tooth :
    ∃ x y : State Goldilocks, x ≠ y ∧
      jiveCompress (fun _ => zero) (SimpleEquiv.refl _) x =
      jiveCompress (fun _ => zero) (SimpleEquiv.refl _) y := by
  exact ⟨(zero, zero, zero), (zero, one, zero), by decide,
    by rw [jiveCompress_eq, jiveCompress_eq]; rfl⟩


/-- A zero-query guess can succeed; verification must extend the charged transcript. -/
theorem unchecked_preimage_tooth : ∃ x : State Goldilocks,
    jiveCompress (fun _ => zero) (SimpleEquiv.refl _) x = zero ∧
    ¬ ∃ y, (x, y) ∈ ([] : List (State Goldilocks × State Goldilocks)) := by
  exact ⟨(zero, zero, zero), by rw [jiveCompress_eq]; decide, by intro ⟨_, h⟩; cases h⟩


#verify_constructive raw_vs_feedforward_tooth
#tooth_pair inverse_feedforward_relation vs raw_vs_feedforward_tooth
#verify_constructive identity_collision_tooth
#verify_constructive unchecked_preimage_tooth

end Qsag.CrossProtocol
end

public section
set_option exponentiation.threshold 8192
namespace Qsag.PreprocessingGame
/-- Two advice bits choose one of three pairs; no online oracle call is made. -/
def storedCollisionAdvice (H : Fin 3 → BitVec 1) : BitVec 2 :=
  if H 0 = H 1 then 0 else if H 0 = H 2 then 1 else 2

def storedCollisionPair (advice : BitVec 2) : Fin 3 × Fin 3 :=
  if advice = 0 then (0, 1) else if advice = 1 then (0, 2) else (1, 2)

def storedCollision : ClassicalAdvice 3 1 1 2 0 (Fin 3 × Fin 3) where
  preprocess := storedCollisionAdvice
  online := fun advice _ => .done (storedCollisionPair advice)

/-- A real zero-online-query strategy wins on EVERY oracle in this finite family.
This is an inhabited counterexample to unsalted collision hardness with free preprocessing. -/
theorem storedCollision_wins (H : Fin 3 → BitVec 1) :
    collisionWin H (storedCollision.run H 0).1 = true := by
  have hpigeon : ∀ a b c : BitVec 1, a = b ∨ a = c ∨ b = c := by decide
  have hp := hpigeon (H 0) (H 1) (H 2)
  by_cases h01 : H 0 = H 1
  · simp [ClassicalAdvice.run_def, storedCollision, storedCollisionAdvice,
      Program.run_done, storedCollisionPair, collisionWin_def, h01]
  · by_cases h02 : H 0 = H 2
    · have h21 : H 2 ≠ H 1 := by intro he; exact h01 (h02.trans he)
      simp [ClassicalAdvice.run_def, storedCollision, storedCollisionAdvice,
      Program.run_done, storedCollisionPair, collisionWin_def, h02, h21]
    · have h12 : H 1 = H 2 := hp.resolve_left h01 |>.resolve_left h02
      simp [ClassicalAdvice.run_def, storedCollision, storedCollisionAdvice,
      Program.run_done, storedCollisionPair, collisionWin_def, h02, h12]

theorem storedCollision_count :
    adviceWinCount storedCollision (fun H _ pair => collisionWin H pair) = 8 := by
  have hEach : ∀ H : Fin 3 → BitVec 1, qsum 1 (fun salt =>
      if collisionWin H (storedCollision.run H salt).1 then 1 else 0) = 1 := by
    intro H
    have hTerms : ∀ salt : Fin 1,
        (if collisionWin H (storedCollision.run H salt).1 then 1 else 0) = 1 := by
      intro salt
      have hs : salt = (0 : Fin 1) := Fin.ext (by omega)
      rw [hs, storedCollision_wins]
      rfl
    rw [qsum_congr hTerms, qsum_const]
  rw [adviceWinCount_def, uniformOracleSum_congr 1 3 _ _ hEach, uniformOracleSum_const]


end Qsag.PreprocessingGame
end

public section
set_option exponentiation.threshold 8192
namespace Qsag.PreprocessingGame
set_option autoImplicit false

/-- With advice fixed independently of H, each chosen pair collides on 4 of 8 oracles. -/
theorem fixedAdvice_collision_count (a : BitVec 2) :
    fixedAdviceWinCount storedCollision.online (fun H _ pair => collisionWin H pair) a = 4 := by
  exact (stored_collision_kats storedCollisionAdvice rfl storedCollisionPair rfl).1 a

/-- A witness that the oracle-dependent preprocessing really changes the experiment:
8 successes with two bits of advice versus 4 for every fixed advice, and zero online calls. -/
theorem storedCollision_execution :
    adviceWinCount storedCollision (fun H _ pair => collisionWin H pair) = 8 ∧
    fixedAdviceWinCount storedCollision.online (fun H _ pair => collisionWin H pair) 0 = 4 ∧
    ∀ H : Fin 3 → BitVec 1, (storedCollision.run H 0).2 = 0 := by
  refine ⟨storedCollision_count, fixedAdvice_collision_count 0, ?_⟩
  intro H
  rw [ClassicalAdvice.run_def]
  exact congrArg Prod.snd (Program.run_done H _)

/-- Two disjoint three-address slices of the same six-address oracle. -/
def saltSlice (H : Fin 6 → BitVec 1) (s : Fin 2) : Fin 3 → BitVec 1 :=
  fun x => H ⟨s.val * 3 + x.val, by have := s.isLt; have := x.isLt; omega⟩

/-- A single stored entry for salt zero, created without knowing the challenge salt. -/
def oneSaltTable (H : Fin 6 → BitVec 1) : List (Fin 2 × (Fin 3 × Fin 3)) :=
  [(0, storedCollisionPair (storedCollisionAdvice (saltSlice H 0)))]

/-- The same one-entry capacity used after learning the challenge: intentionally NOT
an instance of the chronology in ClassicalAdvice, because preprocessing receives s. -/
def challengeAwareTable (H : Fin 6 → BitVec 1) (s : Fin 2) :
    List (Fin 2 × (Fin 3 × Fin 3)) :=
  [(s, storedCollisionPair (storedCollisionAdvice (saltSlice H s)))]

/-- Fresh uniform salt: exactly 64 successful oracle/salt pairs out of 64*2.
The entry-count bound is attained. Challenge-dependent preprocessing: 128/128 despite
still storing just one entry. Thus moving salt disclosure before preprocessing invalidates
applying the fixed-table entries/K bound to the whole two-stage experiment. -/
theorem freshSalt_chronology_execution :
    uniformOracleSum 1 6 (fun H => qsum 2
      (tableWin (fun s pair => collisionWin (saltSlice H s) pair) (oneSaltTable H))) = 64 ∧
    uniformOracleSum 1 6 (fun H => qsum 2 (fun s =>
      tableWin (fun t pair => collisionWin (saltSlice H t) pair) (challengeAwareTable H s) s)) = 128 ∧
    (2 ^ 1) ^ 6 * 2 = 128 :=
  ⟨((stored_collision_kats storedCollisionAdvice rfl storedCollisionPair rfl).2 saltSlice rfl).1,
   ((stored_collision_kats storedCollisionAdvice rfl storedCollisionPair rfl).2 saltSlice rfl).2,
   by decide⟩

/-- Reuses the general proved theorem, not only an executed enumeration. -/
theorem oneSaltTable_bound :
    uniformOracleSum 1 6 (fun H => qsum 2
      (tableWin (fun s pair => collisionWin (saltSlice H s) pair) (oneSaltTable H))) ≤ 64 := by
  exact freshSalt_preprocessed_table_bound oneSaltTable
    (fun H s pair => collisionWin (saltSlice H s) pair) 1 (fun _ => Nat.le_refl 1)

/-- Actual adaptive online queries are charged, even when an address is repeated. -/
def twiceQuery (x : Fin 3) : Program (Fin 3) (BitVec 1) (BitVec 1) 2 :=
  .query x fun _ => .query x fun y => .done y

theorem twiceQuery_execution (H : Fin 3 → BitVec 1) (x : Fin 3) :
    (twiceQuery x).run H = (H x, 2) := by
  unfold twiceQuery
  rw [Program.run_query, Program.run_query, Program.run_done]

#verify_constructive
  Qsag.PreprocessingGame.fixedAdvice_collision_count
  Qsag.PreprocessingGame.storedCollision_execution
  Qsag.PreprocessingGame.freshSalt_chronology_execution
  Qsag.PreprocessingGame.oneSaltTable_bound
  Qsag.PreprocessingGame.twiceQuery_execution
end Qsag.PreprocessingGame
end

public section
set_option exponentiation.threshold 8192
namespace Qsag
def paritySuccess (H : Fin 2 → BitVec 1) (x : Fin 2) : Bool :=
  decide (x.val = (H 0 ^^^ H 1).toNat)

/-- A genuine superposition query: both addresses have positive initial mass. All four
    oracles are included. The coherent runtime preserves perfect parity success and has
    Fourier support exactly on one-entry labels after one call. -/
theorem coherent_parity_runtime_execution :
    QVec.queryWeight qromParityAdv.init 0 = 2 ∧ QVec.queryWeight qromParityAdv.init 1 = 2 ∧
    uniformOracleSum 1 2 (fun H => QVec.queryMassOn (paritySuccess H) (runQuantumAdv qromParityAdv H)) = 32 ∧
    coherentTableEventMass paritySuccess
      (fourierOracleState (fourierAdvStateAt qromParityAdv 1 (Nat.le_refl 1))) = 8192 ∧
    oracleTableSum 2 (fun d => if tableWeight 2 d = 1 then
      QVec.stateNormSq (fourierAdvStateAt qromParityAdv 1 (Nat.le_refl 1) d) else 0) = 2048 ∧
    oracleTableSum 2 (fun d => if 1 < tableWeight 2 d then
      QVec.stateNormSq (fourierAdvStateAt qromParityAdv 1 (Nat.le_refl 1) d) else 0) = 0 :=
  (qrom_parity_fourier_kats qromParityAdv rfl rfl paritySuccess rfl).1

/-- Measuring the Fourier label before decoding changes oracle/output correlations. The
    coherent success mass 8192 falls to 4096 while total mass stays 8192. This refutes treating
    the Q-entry support invariant as a nondisturbing classical answer-table extractor. -/
theorem tooth_fourier_database_measurement_disturbs :
    oracleTableSum 2 (fun d => coherentTableEventMass paritySuccess
      (fourierOracleState (projectFourierLabel d (fourierAdvStateAt qromParityAdv 1 (Nat.le_refl 1))))) = 4096 ∧
    oracleTableSum 2 (fun d => coherentTableEventMass (fun _ _ => true)
      (fourierOracleState (projectFourierLabel d (fourierAdvStateAt qromParityAdv 1 (Nat.le_refl 1))))) = 8192 ∧
    uniformOracleSum 1 2 (fun H => sumLogs 2 1 (fun xs =>
      QVec.queryMassOn (paritySuccess H) (measuredStateAt qromParityAdv H 1 (Nat.le_refl 1) xs))) = 16 :=
  (qrom_parity_fourier_kats qromParityAdv rfl rfl paritySuccess rfl).2


#verify_constructive tooth_fourier_database_measurement_disturbs

end Qsag
end

public section
namespace Qsag
open MigrationExecution
theorem towerToRust_differs_from_psi_on_mds_constant :
    towerToRust 7 gf128MdsATower ≠ gf128MdsAPolyBits ∧
    psiTower128ToPoly gf128MdsATower = gf128MdsAPolyBits := by
  exact ⟨towerToRust_gf128MdsATower_ne, gf128_mds_constants_certified.1⟩

end Qsag
end
