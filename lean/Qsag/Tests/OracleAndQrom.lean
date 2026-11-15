module
import all Qsag.Math.Algebra
import all Qsag.Oracle.FiatShamir
import all Qsag.Math.Goldilocks
import all Qsag.Oracle.Keccak
import all Qsag.Oracle.Poseidon2
import all Qsag.Oracle.Sponge
public import Qsag.Tactic.Prelude
public import Qsag.Oracle.Keccak
public import Qsag.Oracle.Poseidon2
public import Qsag.Oracle.Sponge
public import Qsag.Oracle.Spn
import all Qsag.Oracle.Spn
import all Qsag.Math.Gf2Pow128
import all Qsag.Spec.Bounds
import all Qsag.Spec.Encoding
public import Qsag.Oracle.Qrom
import all Qsag.Oracle.Qrom
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
     0xb5, 0x0c, 0x27, 0x64, 0x6e, 0xd5, 0x76, 0x2f] := by decide +kernel

-- NIST FIPS 202 SHAKE256("abc", 256) = 483366601360a8771c6863080cc4114d8db44530f8f1e1ee4f94ea37e78b5739
example : shake256Xof 32 [0x61, 0x62, 0x63] =
    [0x48, 0x33, 0x66, 0x60, 0x13, 0x60, 0xa8, 0x77,
     0x1c, 0x68, 0x63, 0x08, 0x0c, 0xc4, 0x11, 0x4d,
     0x8d, 0xb4, 0x45, 0x30, 0xf8, 0xf1, 0xe1, 0xee,
     0x4f, 0x94, 0xea, 0x37, 0xe7, 0x8b, 0x57, 0x39] := by decide +kernel


/-! ## 5. Build-Time Conformance Vectors Matching `poseidon2.rs` -/

example : (poseidon2Perm12 ⟨⟨Goldilocks.ofNat 0, Goldilocks.ofNat 0, Goldilocks.ofNat 0, Goldilocks.ofNat 0⟩, ⟨Goldilocks.ofNat 0, Goldilocks.ofNat 0, Goldilocks.ofNat 0, Goldilocks.ofNat 0⟩, ⟨Goldilocks.ofNat 0, Goldilocks.ofNat 0, Goldilocks.ofNat 0, Goldilocks.ofNat 0⟩⟩).toList.map (·.val) =
    [17528629447354354351, 5014055130248055117, 10679077121839038553, 431078547345611051, 7807009921345120310, 2413869689279715014, 11875300792986830377, 1872634884137602556, 15069512080271275672, 14253608580209913153, 14550618143248480092, 107036164978639472] := by decide +kernel

example : (poseidon2Perm12 ⟨⟨Goldilocks.ofNat 0, Goldilocks.ofNat 1, Goldilocks.ofNat 2, Goldilocks.ofNat 3⟩, ⟨Goldilocks.ofNat 4, Goldilocks.ofNat 5, Goldilocks.ofNat 6, Goldilocks.ofNat 7⟩, ⟨Goldilocks.ofNat 8, Goldilocks.ofNat 9, Goldilocks.ofNat 10, Goldilocks.ofNat 11⟩⟩).toList.map (·.val) =
    [13782584570844608145, 13136387643152332171, 7171133015474200819, 7643370872200861694, 14144755201299840503, 16470027036684692562, 1748465969625202405, 1718729118078964347, 6141020819996733037, 16322330185628708898, 11650380702735067362, 2734959974607798415] := by decide +kernel

example : poseidon2Hash32 [] =
    [182, 168, 65, 106, 0, 54, 23, 124, 22, 116, 119, 199, 75, 253, 202, 145, 123, 13, 115, 200, 186, 143, 207, 66, 162, 161, 198, 9, 220, 37, 176, 162] := by decide +kernel

example : poseidon2Hash32 [0] =
    [116, 79, 15, 95, 17, 248, 202, 240, 45, 126, 192, 181, 89, 193, 185, 161, 98, 167, 199, 38, 214, 141, 4, 22, 97, 34, 223, 133, 16, 3, 170, 104] := by decide +kernel

example : poseidon2Hash32 [1, 2, 3] =
    [149, 79, 171, 160, 0, 49, 166, 60, 204, 121, 241, 71, 102, 130, 24, 17, 35, 162, 114, 249, 194, 254, 120, 46, 18, 111, 254, 27, 106, 81, 178, 227] := by decide +kernel

example : poseidon2Hash32 [113, 115, 97, 103, 45, 112, 111, 115, 101, 105, 100, 111, 110, 50, 45, 107, 97, 116] =
    [228, 156, 140, 147, 124, 10, 100, 197, 103, 106, 168, 7, 254, 196, 250, 183, 212, 130, 17, 26, 2, 139, 235, 15, 219, 46, 193, 238, 148, 50, 236, 229] := by decide +kernel

example : (let out := poseidon2CompressWeighted ⟨⟨Goldilocks.ofNat 0, Goldilocks.ofNat 1, Goldilocks.ofNat 2, Goldilocks.ofNat 3⟩, ⟨Goldilocks.ofNat 4, Goldilocks.ofNat 5, Goldilocks.ofNat 6, Goldilocks.ofNat 7⟩, ⟨Goldilocks.ofNat 8, Goldilocks.ofNat 9, Goldilocks.ofNat 10, Goldilocks.ofNat 11⟩⟩;
    [out.x0.val, out.x1.val, out.x2.val, out.x3.val]) =
    [13782584570844608185, 13136387643152332218, 7171133015474200873, 7643370872200861755] := by decide +kernel


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
  have hB0 : natBytesBE 0 = [0] := by decide
  have hB136 : natBytesBE 136 = [136] := by decide
  have hB1048 : natBytesBE 1048 = [4, 24] := by decide
  have hEncLen : (encodeString [] ++ encodeString (List.replicate 131 0x41)).length = 136 := by
    simp only [encodeString, leftEncode, List.length_append, List.length_replicate,
      List.length_nil, Nat.mul_zero, hB0, hB1048, List.length_cons]
  have hPfxLen : (cshakePrefix [] (List.replicate 131 0x41)).length = 272 := by
    unfold cshakePrefix bytepad
    simp only [show (136 : Nat) ≠ 0 from by decide, ↓reduceIte, List.length_append,
      List.length_replicate, hEncLen, leftEncode, hB136, List.length_cons, List.length_nil]
  exact ⟨List.replicate 131 0x41, rfl, by rw [hEncLen]; decide, hPfxLen, by rw [hPfxLen]; decide⟩

theorem witness_pad10star1_valid_domain :
    ∃ (r : Nat) (d : UInt8) (m₁ m₂ : List UInt8),
      0 < r ∧ ValidDomByte d ∧ absorbPayload r d m₁ = absorbPayload r d m₂ :=
  ⟨136, domShake256, [0x61, 0x62], [0x61, 0x62], by decide, ⟨by decide, by decide⟩, rfl⟩

theorem witness_cross_domain_pair :
    ∃ (r : Nat) (d₁ d₂ : UInt8) (m₁ m₂ : List UInt8),
      m₁ = [0x01] ∧ m₂ = [0x02] ∧
      0 < r ∧ ValidDomByte d₁ ∧ ValidDomByte d₂ ∧ d₁ ≠ d₂ :=
  ⟨136, domShake256, domCshake256, [0x01], [0x02], rfl, rfl,
   by decide, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, by decide⟩

/-- `cshakePrefix_prefix_free` applied at the Canopy leaf tag: its hypotheses are jointly
dischargeable. The equation forces repeated components, which the positional
`#verify_inhabited` matcher cannot assign, so the application itself is the witness. -/
theorem witness_cshakePrefix_canopy :
    ([] : List UInt8) = [] ∧ qsagTagCanopyLeaf = qsagTagCanopyLeaf ∧ ([0x01] : List UInt8) = [0x01] :=
  cshakePrefix_prefix_free (N₁ := []) (S₁ := qsagTagCanopyLeaf) (N₂ := []) (S₂ := qsagTagCanopyLeaf)
    (m₁ := [0x01]) (m₂ := [0x01])
    (bitlen_lt_sp800_bound (by decide)) (bitlen_lt_sp800_bound (by decide))
    (bitlen_lt_sp800_bound (by decide)) (bitlen_lt_sp800_bound (by decide)) rfl

theorem witness_keccak_midstate_canopy :
    ∃ (S msg : List UInt8) (outLen : Nat),
      S ≠ [] ∧ (encodeString [] ++ encodeString S).length ≤ 134 ∧
      (cshake256Xof outLen S msg).length = 32 :=
  ⟨qsagTagCanopyLeaf, [0xde, 0xad, 0xbe, 0xef], 32, by decide, by decide, by simp⟩

#verify_constructive Qsag.pad10star1_joint_injective Qsag.pad10star1_injective
  Qsag.absorbPayload_cross_domain_disjoint Qsag.evalSponge_keccak_eq_shake256Xof
  Qsag.leftEncode_prefix_inj Qsag.encodeString_prefix_inj Qsag.cshakePrefix_prefix_free
  Qsag.cshakePrefix_injective Qsag.cshake256_domains_disjoint
  Qsag.cshake_precomputed_midstate_eq Qsag.keccak_cshake256_precomputed_midstate_eq

#verify_inhabited Qsag.pad10star1_injective Qsag.witness_pad10star1_valid_domain
#verify_inhabited Qsag.absorbPayload_cross_domain_disjoint Qsag.witness_cross_domain_pair
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
  refine ⟨RatBound.one, by decide, fun x delta => ?_, by decide, by decide⟩
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
  | zero => rfl
  | succ r ih => simp only [spnIterRounds128, ih, hStep]

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
    rustSpnRound (0#128, 0#128) (1#128, 0#128) = (1#128, gf128MdsBPolyBits) := by
  decide +kernel

/-- Positive control for the framing: the little-endian bytes of `GF128_MDS_A`; byte 0 bit 0
    is the constant coefficient and byte 15 bit 7 is `x^127`. -/
theorem rust_le_lane_framing_kats :
    rustU128FromLeBytes [0x35, 0xc8, 0xed, 0x5c, 0x60, 0xc0, 0x9c, 0xf3,
      0x15, 0x7c, 0x4a, 0x7f, 0xb9, 0x79, 0x37, 0x9e] = gf128MdsAPolyBits ∧
    rustU128FromLeBytes [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = 1#128 ∧
    rustU128FromLeBytes [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x80] =
      BitVec.twoPow 128 127 ∧
    rustU128ToLeBytes 2#128 = [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

/-- Negative control: reading the same sixteen bytes big-endian gives a different field
    element. -/
theorem tooth_big_endian_lane_framing_differs :
    BitVec.ofNat 128 (ofBE [0x35, 0xc8, 0xed, 0x5c, 0x60, 0xc0, 0x9c, 0xf3,
      0x15, 0x7c, 0x4a, 0x7f, 0xb9, 0x79, 0x37, 0x9e]) ≠ gf128MdsAPolyBits := by
  decide +kernel

set_option maxRecDepth 4096 in
/-- Negative control: exchanging `GF128_MDS_A` and `GF128_MDS_B` changes the round. -/
theorem tooth_swapped_mds_constants_change_round :
    ∃ st : BitVec 128 × BitVec 128,
      rustSpnRound (0#128, 0#128) st ≠
        (let x7 := rustPow7 st.1
         let y7 := rustPow7 st.2
         (x7 ^^^ rustGf128Mul y7 gf128MdsBPolyBits, y7 ^^^ rustGf128Mul x7 gf128MdsAPolyBits)) :=
  ⟨(1#128, 0#128), by decide +kernel⟩

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
    rw [psiTower128Pair_spnRound128]
    show rustSpnRound (psiTower128ToPoly (towerZero 7), psiTower128ToPoly (towerZero 7))
      (psiTower128ToPoly (towerZero 7), psiTower128ToPoly (towerOne 7)) = _
    rw [psiTower128ToPoly_zero, psiTower128ToPoly_one]
    decide +kernel
  refine ⟨?_, hEq⟩
  rw [hEq]
  decide +kernel


/-- **Invertibility is not collision or preimage resistance.** Xor with a constant is a
    bijection of the 256-bit state, and its Davies–Meyer feed-forward is the constant map:
    every pair collides and every input is a preimage of `c`. Any collision or preimage claim
    for `spnDaviesMeyer48` must therefore use more than `pow7_tower128_bijective`. -/
theorem tooth_xor_constant_permutation_davies_meyer_collapses (c : Tower128 × Tower128) :
    IsBijective (fun x => pairXor x c) ∧ ∀ x, pairXor (pairXor x c) x = c := by
  have hInv : ∀ x, pairXor (pairXor x c) c = x := fun x => by
    unfold pairXor
    apply Prod.ext <;> simp only [towerAdd_assoc, towerAdd_self_zero, towerAdd_zero]
  refine ⟨⟨fun a b h => ?_, fun b => ⟨pairXor b c, hInv b⟩⟩, fun x => ?_⟩
  · have h2 := congrArg (fun z => pairXor z c) h
    simpa only [hInv] using h2
  · unfold pairXor
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
  orth := fun y y' => by cases y <;> cases y' <;> rfl

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
  decide

end Qsag

section
namespace Qsag
open MigrationExecution

set_option autoImplicit false

/-- Frame body of `cshake256_framed_xof` (`keccak.rs:281-284`). -/
def spnFramesU64LeBody : List (List UInt8) → List UInt8
  | [] => []
  | f :: fs => (encodeNatLeBytes 8 f.length ++ f) ++ spnFramesU64LeBody fs

/-- `cshake256_framed_32` (`keccak.rs:277-295`) over the `Qsag.Keccak` cSHAKE256 model. -/
def spnCshake256Framed32 (customization : List UInt8) (frames : List (List UInt8)) :
    List UInt8 :=
  cshake256Bytes customization (encodeNatLeBytes 8 frames.length ++ spnFramesU64LeBody frames)

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
    show rustSpnRound (rcs (m + n)) (rustSpnIter rcs (m + n) st) =
      rustSpnRound (rcs (m + n)) (rustSpnIterFrom rcs m n (rustSpnIter rcs m st))
    rw [rustSpnIter_add rcs m n st]

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

/-- Output printed by the Rust harness for `(pk_seed, epoch 7, chain_idx 3, step 2, cur)`. -/
def chainStepKatRustOutput : List UInt8 :=
  [0x24, 0xc1, 0x9a, 0x2d, 0x42, 0x51, 0xdf, 0x83, 0x40, 0xd1, 0x7d, 0xf8,
   0xde, 0xc6, 0x6b, 0x9c, 0xd4, 0x60, 0x46, 0xb7, 0xb2, 0x34, 0x72, 0xb1,
   0x4b, 0xb6, 0x8f, 0x62, 0x11, 0x22, 0x91, 0x4b]

def chainStepKatTweak : BitVec 128 × BitVec 128 :=
  (0x4668a6864f7bee9787e94643de34423c#128, 0x2f7744435eb81c943103f437706a0e10#128)

/-- State after `8k` rounds, `k ≤ 6`. -/
def chainStepKatState : Nat → BitVec 128 × BitVec 128
  | 0 => (0xafaeadacabaaa9a8a7a6a5a4a3a2a1a0#128, 0xbfbebdbcbbbab9b8b7b6b5b4b3b2b1b0#128)
  | 1 => (0x2bd5eef093126656772fb98cf70d43c1#128, 0x58b1a4a862530ca569b93c0c9f839923#128)
  | 2 => (0x6cdc2dacdcb33e5347e44c9e8d276445#128, 0xba352c8a0c0bd7639d484ab60c75f57d#128)
  | 3 => (0x7b5d995999b5e650e78f4b0ca3b6fd89#128, 0xbe4268d7c4890e6f38438a0aa7b69114#128)
  | 4 => (0x6f7b16116ee2bf063beea2ad89749e8e#128, 0xedfb215302775491fab2c19cca81af56#128)
  | 5 => (0xef989eea2f03174c916b4ff381b3b153#128, 0xabd713ce96b31b4227d0d661999e014f#128)
  | 6 => (0x33c56b7253d778e82479f4e68e386084#128, 0xf42f9fadd9350ff306c4810604f4d164#128)
  | _ => (0#128, 0#128)

set_option maxRecDepth 8192 in
theorem chainStepKat_tweak :
    rustDeriveChainTweak spnCshake256Framed32 chainStepKatPkSeed 7 3 2 = chainStepKatTweak := by
  decide +kernel

theorem chainStepKat_lanes : rustBytes32ToLanes chainStepKatCur = chainStepKatState 0 := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem chainStepKat_rounds_0_8 :
    rustSpnIterFrom (rustSpnRoundConstants spnCshake256Framed32 chainStepKatTweak) 0 8
      (chainStepKatState 0) = chainStepKatState 1 := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem chainStepKat_rounds_8_16 :
    rustSpnIterFrom (rustSpnRoundConstants spnCshake256Framed32 chainStepKatTweak) 8 8
      (chainStepKatState 1) = chainStepKatState 2 := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem chainStepKat_rounds_16_24 :
    rustSpnIterFrom (rustSpnRoundConstants spnCshake256Framed32 chainStepKatTweak) 16 8
      (chainStepKatState 2) = chainStepKatState 3 := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem chainStepKat_rounds_24_32 :
    rustSpnIterFrom (rustSpnRoundConstants spnCshake256Framed32 chainStepKatTweak) 24 8
      (chainStepKatState 3) = chainStepKatState 4 := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem chainStepKat_rounds_32_40 :
    rustSpnIterFrom (rustSpnRoundConstants spnCshake256Framed32 chainStepKatTweak) 32 8
      (chainStepKatState 4) = chainStepKatState 5 := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem chainStepKat_rounds_40_48 :
    rustSpnIterFrom (rustSpnRoundConstants spnCshake256Framed32 chainStepKatTweak) 40 8
      (chainStepKatState 5) = chainStepKatState 6 := by
  decide +kernel

theorem chainStepKat_rounds_0_48 :
    rustSpnIter (rustSpnRoundConstants spnCshake256Framed32 chainStepKatTweak) spnRounds
      (chainStepKatState 0) = chainStepKatState 6 := by
  let rcs := rustSpnRoundConstants spnCshake256Framed32 chainStepKatTweak
  have step : ∀ (m k : Nat), rustSpnIter rcs m (chainStepKatState 0) = chainStepKatState k →
      rustSpnIterFrom rcs m 8 (chainStepKatState k) = chainStepKatState (k + 1) →
      rustSpnIter rcs (m + 8) (chainStepKatState 0) = chainStepKatState (k + 1) :=
    fun m k hPrev hChunk =>
      (rustSpnIter_add rcs m 8 _).trans ((congrArg (rustSpnIterFrom rcs m 8) hPrev).trans hChunk)
  have h8 := step 0 0 rfl chainStepKat_rounds_0_8
  have h16 := step 8 1 h8 chainStepKat_rounds_8_16
  have h24 := step 16 2 h16 chainStepKat_rounds_16_24
  have h32 := step 24 3 h24 chainStepKat_rounds_24_32
  have h40 := step 32 4 h32 chainStepKat_rounds_32_40
  exact step 40 5 h40 chainStepKat_rounds_40_48

/-- **Executed-Rust agreement.** The Lean transcription of `parallel_chain_step`, evaluated by
    the kernel over the Lean cSHAKE256 model, returns the 32 bytes the compiled Rust function
    printed for the same arguments. -/
theorem rust_parallel_chain_step_executed_kat :
    rustParallelChainStep spnCshake256Framed32 chainStepKatPkSeed 7 3 2 chainStepKatCur =
      chainStepKatRustOutput := by
  have hStep : rustAlgebraicStep
      (rustSpnRoundConstants spnCshake256Framed32 chainStepKatTweak) (chainStepKatState 0) =
      ((chainStepKatState 6).1 ^^^ (chainStepKatState 0).1,
       (chainStepKatState 6).2 ^^^ (chainStepKatState 0).2) := by
    show ((rustSpnIter (rustSpnRoundConstants spnCshake256Framed32 chainStepKatTweak) spnRounds
          (chainStepKatState 0)).1 ^^^ (chainStepKatState 0).1,
        (rustSpnIter (rustSpnRoundConstants spnCshake256Framed32 chainStepKatTweak) spnRounds
          (chainStepKatState 0)).2 ^^^ (chainStepKatState 0).2) = _
    rw [chainStepKat_rounds_0_48]
  unfold rustParallelChainStep
  rw [chainStepKat_tweak, chainStepKat_lanes, hStep]
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
  refine ⟨?_, ⟨?_, fun _ => trivial⟩, by decide⟩
  · unfold keyedPrfRealAccept keyedPrfIdealAccept zeroQueryHardcoder evalOracleComp
    simp [natAbsDiff]
  · unfold keyedPrfRealAccept keyedPrfIdealAccept oneQueryGuesser evalOracleComp
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
    rw [hReal1, hIdeal0]
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
  refine ⟨by unfold exceedsBitBudget quantumBhtPureCubicBound; decide,
          by unfold exceedsBitBudget quantumBhtPureCubicBound; decide, ?_⟩
  intro qHash hq
  unfold atLeastBits quantumBhtCollisionBound
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
  refine ⟨rfl, ?_⟩
  unfold MerkleTweakCollision
  exact ⟨0, 0, 7, 1, 7, 2, .inr (by decide), rfl⟩

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
      canopyToyLeaves canopyToyProof = true := by decide

theorem canopyToy_sibling_count :
    steinerSiblingCount 3 [1, 2, 6] = 4 := by decide

/-- A flipped sibling digest (leaf `7` replaced) is rejected. -/
theorem canopyToy_flipped_sibling_rejected :
    verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
      canopyToyLeaves
      [canopyToyLeaf 0, canopyToyLeaf 3, canopyToyLeaf 7 + 1,
       canopyToyNodeHash 6 (canopyToyLeaf 4) (canopyToyLeaf 5)] = false := by decide

/-- A flipped leaf digest (leaf `2`) is rejected. -/
theorem canopyToy_flipped_leaf_rejected :
    verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
      [(1, canopyToyLeaf 1), (2, canopyToyLeaf 2 + 1), (6, canopyToyLeaf 6)]
      canopyToyProof = false := by decide

/-- The proof with its last sibling removed is rejected. -/
theorem canopyToy_missing_sibling_rejected :
    verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
      canopyToyLeaves canopyToyProof.dropLast = false := by decide

/-- The proof with one trailing digest appended is rejected. -/
theorem canopyToy_extra_sibling_rejected :
    verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
      canopyToyLeaves (canopyToyProof ++ [999]) = false := by decide

/-- A duplicated index is rejected. -/
theorem canopyToy_duplicate_index_rejected :
    verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
      [(1, canopyToyLeaf 1), (1, canopyToyLeaf 1), (2, canopyToyLeaf 2), (6, canopyToyLeaf 6)]
      canopyToyProof = false := by decide

/-- An unsorted index list is rejected. -/
theorem canopyToy_unsorted_index_rejected :
    verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
      [(2, canopyToyLeaf 2), (1, canopyToyLeaf 1), (6, canopyToyLeaf 6)]
      canopyToyProof = false := by decide

/-- An index `≥ 2^logLeaves` is rejected. -/
theorem canopyToy_out_of_range_index_rejected :
    verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
      [(1, canopyToyLeaf 1), (2, canopyToyLeaf 2), (8, canopyToyLeaf 6)]
      canopyToyProof = false := by decide

/-- **The exact-consumption check is load-bearing.** The relaxed verifier, which differs from
    `verifyCanopyMultiproof` only by ignoring unconsumed digests, accepts the honest proof with a
    trailing digest appended, while `verifyCanopyMultiproof` rejects the same input. -/
theorem canopyToy_relaxed_accepts_extra_sibling :
    verifyCanopyMultiproofRelaxed canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
      canopyToyLeaves (canopyToyProof ++ [999]) = true ∧
    verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
      canopyToyLeaves (canopyToyProof ++ [999]) = false := by decide

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
  unfold extractOnlineMerkleOpening findFirst at h
  cases h




private def witnessInitVec : QVec 2 2 1 :=
  fun x y _ => if x.1 = 0 ∧ y.1 = 0 then ⟨1, 0⟩ else GaussInt.zero

private theorem witnessInitVec_pos : 0 < QVec.stateNormSq witnessInitVec := by decide

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
      unfold QVec.queryMassOn qsum; dsimp only
      simp only [decide_true, ↓reduceIte]
      exact Nat.le_add_right _ _
    | 1, _ =>
      unfold QVec.queryMassOn
      simp only [qsum, Fin.ext_iff, Nat.one_ne_zero, Nat.zero_add, decide_false, decide_true,
        Bool.false_eq_true, ↓reduceIte]
      omega
  have hLe : QVec.queryMassOn (witnessFailExtract H) (runQuantumAdv witnessQuantumAdv H) ≤
      qromOrdinaryFlipMass witnessQuantumAdv H (witnessProj ⟨0, by omega⟩) (fun _ _ => true)
        (fun O x => listHasElem (O x) (witnessTargetSet ⟨0, by omega⟩ O x)) := by
    unfold QVec.queryMassOn qromOrdinaryFlipMass witnessFailExtract witnessProj witnessTargetSet
    apply qsum_le_qsum; intro x
    by_cases h0 : (H x).toNat = 0
    · have hBv : H x = 0#2 := BitVec.eq_of_toNat_eq h0
      have hElem : listHasElem (H x) [0#2] = true := by rw [hBv]; rfl
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
    simp [qromSelfTarget, listHasElem]
  · intro h
    have h01 := h (fun _ => 0#1) 0 1#1
    have hne : qromSelfTarget (reprogramOracle (fun _ : Fin 1 => 0#1) 0 1#1) 0 ≠
        qromSelfTarget (fun _ : Fin 1 => 0#1) 0 := by decide
    exact hne h01

/-- Uniform query register, phase-kickback response, and a blank record register. -/
def qromParityInit : QVec 2 1 2 := fun _ y a =>
  if a.val = 0 then (if y.val = 0 then ⟨1, 0⟩ else ⟨-1, 0⟩) else GaussInt.zero

/-- The two input addresses have different oracle answers. -/
def qromParityOracle (x : Fin 2) : BitVec 1 := BitVec.ofFin x

/-- One coherent oracle call followed by a query-register Hadamard. -/
def qromParityAdv : QuantumAdv 2 1 2 1 where
  init := qromParityInit
  h_init_pos := by decide
  steps := fun _ => hadamardQuery2 1 2

/-- The same initial state after copying the query address to an orthogonal record.
    This is the controlled-X copy on a blank ancilla, before the oracle call. -/
def qromRecordedParityInit : QVec 2 1 2 := fun x y a =>
  if a = x then (if y.val = 0 then ⟨1, 0⟩ else ⟨-1, 0⟩) else GaussInt.zero

def qromRecordedParityAdv : QuantumAdv 2 1 2 1 where
  init := qromRecordedParityInit
  h_init_pos := by decide
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
      (runQuantumAdv qromRecordedParityAdv qromParityOracle) = 4 := by
  decide


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
      (measuredStateAt qromParityAdv qromParityOracle 1 (Nat.le_refl 1) xs)) = 8 := by
  decide



end Qsag

namespace Qsag
/-- Nonvacuity control in the QUANTUM game: the identity primitive makes the mode
constant, so every online adversary wins for every challenge. This does not describe
the actual SPN; it rules out deriving mode hardness from permutation laws alone. -/
theorem identityPublicPermutation_quantum_preimage_mass {anc q : Nat}
    (adversary : PublicSpnPreimageAdversary anc q) (challenge : PublicSpnState) :
    publicSpnPreimageMass identityPublicPermutation adversary challenge =
      QVec.stateNormSq (publicSpnPreimageFinalState identityPublicPermutation adversary challenge) := by
  unfold publicSpnPreimageMass QVec.stateNormSq QVec.queryWeight
  simp only [publicSpnFeedForward, identityPublicPermutation, id_eq, BitVec.xor_self, ↓reduceIte]


end Qsag

public section
set_option exponentiation.threshold 8192
namespace Qsag
open RoundPoly
/-- `x ↦ x ^ 3` identifies `ω₃ ≠ 1` with `1`, because `3 ∣ p - 1`. -/
theorem tooth_d3_not_permutation_on_goldilocks :
    goldilocksOmega3 ≠ Goldilocks.one ∧ goldilocksOmega3 ≠ Goldilocks.zero ∧
    goldilocksPow goldilocksOmega3 3 = goldilocksPow Goldilocks.one 3 ∧
    3 ∣ goldilocksPrime - 1 := by
  refine ⟨gold_ne_of_val_ne (by decide), gold_ne_of_val_ne (by decide), ?_,
    ⟨6148914689804861440, by decide⟩⟩
  apply Goldilocks.ext
  rw [goldilocksPow_val, goldilocksPow_val]
  decide


/-- `x ↦ x ^ 5` identifies `ω₅ ≠ 1` with `1`, because `5 ∣ p - 1`. -/
theorem tooth_d5_not_permutation_on_goldilocks :
    goldilocksOmega5 ≠ Goldilocks.one ∧ goldilocksOmega5 ≠ Goldilocks.zero ∧
    goldilocksPow goldilocksOmega5 5 = goldilocksPow Goldilocks.one 5 ∧
    5 ∣ goldilocksPrime - 1 := by
  refine ⟨gold_ne_of_val_ne (by decide), gold_ne_of_val_ne (by decide), ?_,
    ⟨3689348813882916864, by decide⟩⟩
  apply Goldilocks.ext
  rw [goldilocksPow_val, goldilocksPow_val]
  decide


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
    unfold applyMEStd lane4Neg applyM4 lane4Add lane4Sub lane4Sum lane4Zero
    apply Poseidon2State12.ext <;> apply Lane4.ext <;> gold_cring
  have hDecomp : ⟨lane4Add U0 X, lane4Neg X, U2⟩ =
      state12Add ⟨U0, lane4Zero, U2⟩ ⟨X, lane4Neg X, lane4Zero⟩ := by
    unfold state12Add lane4Add lane4Neg lane4Sub lane4Zero
    apply Poseidon2State12.ext <;> apply Lane4.ext <;> gold_cring
  refine ⟨hLinSub, ?_, ?_, rfl, ?_⟩
  · rw [hDecomp, applyMEStd_add, hLinSub]
    unfold state12Add sboxState12 sboxLane4
    dsimp only
    have hHelper : ∀ (M0 M1 A C0 C1 : Lane4),
        lane4Add M0 C0 = lane4Neg (lane4Add M1 C1) →
        lane4Add (lane4Add M1 (lane4Neg A)) C1 = lane4Neg (lane4Add (lane4Add M0 A) C0) := by
      intro M0 M1 A C0 C1 hEq
      have h0 := congrArg Lane4.x0 hEq
      have h1 := congrArg Lane4.x1 hEq
      have h2 := congrArg Lane4.x2 hEq
      have h3 := congrArg Lane4.x3 hEq
      unfold lane4Add lane4Neg lane4Sub lane4Zero at h0 h1 h2 h3 ⊢
      dsimp only at h0 h1 h2 h3 ⊢
      have hInv : ∀ a : Goldilocks, Goldilocks.sub Goldilocks.zero (Goldilocks.sub Goldilocks.zero a) = a :=
        fun _ => by gold_cring
      apply Lane4.ext
      · have hL : Goldilocks.add (Goldilocks.add M1.x0 (Goldilocks.sub Goldilocks.zero A.x0)) C1.x0 =
            Goldilocks.sub (Goldilocks.add M1.x0 C1.x0) A.x0 := by gold_cring
        have rhsEq : Goldilocks.sub Goldilocks.zero (Goldilocks.add (Goldilocks.add M0.x0 A.x0) C0.x0) =
            Goldilocks.sub (Goldilocks.sub Goldilocks.zero (Goldilocks.add M0.x0 C0.x0)) A.x0 := by gold_cring
        have hFlip : Goldilocks.add M1.x0 C1.x0 = Goldilocks.sub Goldilocks.zero (Goldilocks.add M0.x0 C0.x0) := by
          have := congrArg (Goldilocks.sub Goldilocks.zero) h0
          rw [hInv] at this
          exact this.symm
        rw [hL, rhsEq, hFlip]
      · have hL : Goldilocks.add (Goldilocks.add M1.x1 (Goldilocks.sub Goldilocks.zero A.x1)) C1.x1 =
            Goldilocks.sub (Goldilocks.add M1.x1 C1.x1) A.x1 := by gold_cring
        have rhsEq : Goldilocks.sub Goldilocks.zero (Goldilocks.add (Goldilocks.add M0.x1 A.x1) C0.x1) =
            Goldilocks.sub (Goldilocks.sub Goldilocks.zero (Goldilocks.add M0.x1 C0.x1)) A.x1 := by gold_cring
        have hFlip : Goldilocks.add M1.x1 C1.x1 = Goldilocks.sub Goldilocks.zero (Goldilocks.add M0.x1 C0.x1) := by
          have := congrArg (Goldilocks.sub Goldilocks.zero) h1
          rw [hInv] at this
          exact this.symm
        rw [hL, rhsEq, hFlip]
      · have hL : Goldilocks.add (Goldilocks.add M1.x2 (Goldilocks.sub Goldilocks.zero A.x2)) C1.x2 =
            Goldilocks.sub (Goldilocks.add M1.x2 C1.x2) A.x2 := by gold_cring
        have rhsEq : Goldilocks.sub Goldilocks.zero (Goldilocks.add (Goldilocks.add M0.x2 A.x2) C0.x2) =
            Goldilocks.sub (Goldilocks.sub Goldilocks.zero (Goldilocks.add M0.x2 C0.x2)) A.x2 := by gold_cring
        have hFlip : Goldilocks.add M1.x2 C1.x2 = Goldilocks.sub Goldilocks.zero (Goldilocks.add M0.x2 C0.x2) := by
          have := congrArg (Goldilocks.sub Goldilocks.zero) h2
          rw [hInv] at this
          exact this.symm
        rw [hL, rhsEq, hFlip]
      · have hL : Goldilocks.add (Goldilocks.add M1.x3 (Goldilocks.sub Goldilocks.zero A.x3)) C1.x3 =
            Goldilocks.sub (Goldilocks.add M1.x3 C1.x3) A.x3 := by gold_cring
        have rhsEq : Goldilocks.sub Goldilocks.zero (Goldilocks.add (Goldilocks.add M0.x3 A.x3) C0.x3) =
            Goldilocks.sub (Goldilocks.sub Goldilocks.zero (Goldilocks.add M0.x3 C0.x3)) A.x3 := by gold_cring
        have hFlip : Goldilocks.add M1.x3 C1.x3 = Goldilocks.sub Goldilocks.zero (Goldilocks.add M0.x3 C0.x3) := by
          have := congrArg (Goldilocks.sub Goldilocks.zero) h3
          rw [hInv] at this
          exact this.symm
        rw [hL, rhsEq, hFlip]
    have hSumAnti := hHelper (applyMEStd ⟨U0, lane4Zero, U2⟩).b0 (applyMEStd ⟨U0, lane4Zero, U2⟩).b1
      (applyM4 X) C.b0 C.b1 hAnti
    rw [hSumAnti]
    unfold lane4Neg lane4Sub lane4Zero
    dsimp only
    exact Lane4.ext (sbox7_odd _) (sbox7_odd _) (sbox7_odd _) (sbox7_odd _)
  · rw [hDecomp, applyMEStd_add, hLinSub]
    unfold state12Add sboxState12
    dsimp only
    have hAddZ : ∀ a : Lane4, lane4Add a lane4Zero = a := fun a => by
      unfold lane4Add lane4Zero; apply Lane4.ext <;> exact LawfulCommRing.add_zero _
    rw [hAddZ]
  · unfold lane4Add lane4Neg lane4Sub lane4Zero
    apply Lane4.ext <;> gold_cring


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
      state12Scale (Goldilocks.ofNat 8914261387277420341) miRationalEigvec0) := by decide


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

/-- Every output claims: root `0`, index `0`, leaf `0`, sibling `1`. The verifier therefore
    evaluates the oracle at address `2 * 0 + 1 = 1`. -/
def toyOpening (_ : Fin 4) : MerkleOpeningReadout 1 := ⟨0#1, 0, 0#1, [1#1]⟩

/-- Acceptance without the extraction comparison. -/
def toyAccepted (H : Fin 4 → BitVec 1) (o : Fin 4) : Bool :=
  decide (merkleRootFromPath (toyMerkleLayout.hash H) 0 (toyOpening o).idx (toyOpening o).leaf
    (toyOpening o).path = (toyOpening o).rt)

theorem toy_measured_merkle_execution :
    let honest := toyQueryAdv ⟨1, by decide⟩ (by decide)
    let guesser := toyQueryAdv ⟨0, by decide⟩ (by decide)
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
    (2 ^ 1) ^ 4 * (prefixScale guesser 1 (Nat.le_refl 1) * QVec.stateNormSq guesser.init) = 16 := by
  decide +kernel

/-- The toy adversaries are classical-address adversaries, so `ClassicalQueryAddresses` is
    satisfiable and the transfer theorem applies to them. -/
theorem toyQueryAdv_classical (x₀ : Fin 4) (h : 0 < QVec.stateNormSq (toyBasisInit x₀)) :
    ClassicalQueryAddresses (toyQueryAdv x₀ h) (fun _ _ => x₀) := by
  intro H t ht x y a hx
  have ht0 : t = 0 := by omega
  subst ht0
  show (if x = x₀ ∧ y.val = 0 then (⟨1, 0⟩ : GaussInt) else GaussInt.zero) = GaussInt.zero
  exact ite_eq_right (fun hh => hx hh.1)

/-- The coherent run of the non-querying-the-right-address adversary, with its own address
    log `[0]`, has failure mass 8 of 16: the value the measured experiment gave, as the
    transfer theorem states, and within the general bound `(1 * 4 + 0) / 2`. -/
theorem toy_classical_run_execution :
    let guesser := toyQueryAdv ⟨0, by decide⟩ (by decide)
    uniformOracleSum 1 4 (fun H =>
      QVec.queryMassOn (measuredMerkleFailure toyMerkleLayout 0 1 toyOpening H
          (classicalQueryLog (fun _ _ => (⟨0, by decide⟩ : Fin 4)) H 1))
        (runQuantumAdv guesser H)) = 8 ∧
    2 ^ 1 * 8 ≤ (1 * (3 * 1 + 1) + triangleSum 1) *
      ((2 ^ 1) ^ 4 * (prefixScale guesser 1 (Nat.le_refl 1) * QVec.stateNormSq guesser.init)) := by
  decide +kernel

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
  refine ⟨SimpleEquiv.refl _, rfl, ?_⟩
  decide


/-- Feed-forward does not guarantee security for every fixed permutation. -/
theorem identity_collision_tooth :
    ∃ x y : State Goldilocks, x ≠ y ∧
      jiveCompress (fun _ => zero) (SimpleEquiv.refl _) x =
      jiveCompress (fun _ => zero) (SimpleEquiv.refl _) y := by
  exact ⟨(zero, zero, zero), (zero, one, zero), by decide, rfl⟩


/-- A zero-query guess can succeed; verification must extend the charged transcript. -/
theorem unchecked_preimage_tooth : ∃ x : State Goldilocks,
    jiveCompress (fun _ => zero) (SimpleEquiv.refl _) x = zero ∧
    ¬ ∃ y, (x, y) ∈ ([] : List (State Goldilocks × State Goldilocks)) := by
  exact ⟨(zero, zero, zero), by decide, by intro ⟨_, h⟩; cases h⟩


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
  · simp [ClassicalAdvice.run, storedCollision, storedCollisionAdvice,
      Program.run, storedCollisionPair, collisionWin, h01]
  · by_cases h02 : H 0 = H 2
    · have h21 : H 2 ≠ H 1 := by intro he; exact h01 (h02.trans he)
      simp [ClassicalAdvice.run, storedCollision, storedCollisionAdvice,
        Program.run, storedCollisionPair, collisionWin, h02, h21]
    · have h12 : H 1 = H 2 := hp.resolve_left h01 |>.resolve_left h02
      simp [ClassicalAdvice.run, storedCollision, storedCollisionAdvice,
        Program.run, storedCollisionPair, collisionWin, h02, h12]

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
  unfold adviceWinCount
  rw [uniformOracleSum_congr 1 3 _ _ hEach, uniformOracleSum_const]


end Qsag.PreprocessingGame
end

public section
set_option exponentiation.threshold 8192
namespace Qsag.PreprocessingGame
set_option autoImplicit false

/-- With advice fixed independently of H, each chosen pair collides on 4 of 8 oracles. -/
theorem fixedAdvice_collision_count (a : BitVec 2) :
    fixedAdviceWinCount storedCollision.online (fun H _ pair => collisionWin H pair) a = 4 := by
  cases a with | ofFin a =>
  revert a
  decide +kernel

/-- A witness that the oracle-dependent preprocessing really changes the experiment:
8 successes with two bits of advice versus 4 for every fixed advice, and zero online calls. -/
theorem storedCollision_execution :
    adviceWinCount storedCollision (fun H _ pair => collisionWin H pair) = 8 ∧
    fixedAdviceWinCount storedCollision.online (fun H _ pair => collisionWin H pair) 0 = 4 ∧
    ∀ H : Fin 3 → BitVec 1, (storedCollision.run H 0).2 = 0 := by
  refine ⟨storedCollision_count, fixedAdvice_collision_count 0, ?_⟩
  intro H
  rfl

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
    (2 ^ 1) ^ 6 * 2 = 128 := by
  decide +kernel

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
  unfold twiceQuery Program.run
  rfl

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
      QVec.stateNormSq (fourierAdvStateAt qromParityAdv 1 (Nat.le_refl 1) d) else 0) = 0 := by
  decide +kernel

/-- Measuring the Fourier label before decoding changes oracle/output correlations. The
    coherent success mass 8192 falls to 4096 while total mass stays 8192. This refutes treating
    the Q-entry support invariant as a nondisturbing classical answer-table extractor. -/
theorem tooth_fourier_database_measurement_disturbs :
    oracleTableSum 2 (fun d => coherentTableEventMass paritySuccess
      (fourierOracleState (projectFourierLabel d (fourierAdvStateAt qromParityAdv 1 (Nat.le_refl 1))))) = 4096 ∧
    oracleTableSum 2 (fun d => coherentTableEventMass (fun _ _ => true)
      (fourierOracleState (projectFourierLabel d (fourierAdvStateAt qromParityAdv 1 (Nat.le_refl 1))))) = 8192 ∧
    uniformOracleSum 1 2 (fun H => sumLogs 2 1 (fun xs =>
      QVec.queryMassOn (paritySuccess H) (measuredStateAt qromParityAdv H 1 (Nat.le_refl 1) xs))) = 16 := by
  decide +kernel


end Qsag
end

public section
namespace Qsag
open MigrationExecution
theorem towerToRust_differs_from_psi_on_mds_constant :
    towerToRust 7 gf128MdsATower ≠ gf128MdsAPolyBits ∧
    psiTower128ToPoly gf128MdsATower = gf128MdsAPolyBits := by
  refine ⟨?_, gf128_mds_constants_certified.1⟩
  decide +kernel

end Qsag
end
