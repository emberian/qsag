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

example : (poseidon2Perm12 ⟨lane4Zero, lane4Zero, lane4Zero⟩).toList.map (·.val) =
    [444626622888223479, 10486189390627733761, 5399253379101132897, 5052010181030417489, 6267397916963039069,
     9245911245446346418, 9661705423445490201, 787089484585814203, 14953692268052641311, 11458212182116269477,
     16934754160153525625, 6948793053817514326] := by decide +kernel
example : poseidon2Hash32 [] =
    [138, 190, 114, 201, 171, 117, 245, 165, 115, 111, 42, 219, 119, 171, 10, 76, 186, 173, 182, 128, 209, 69, 108,
     220, 169, 239, 117, 130, 81, 43, 90, 65] := by decide +kernel
example : poseidon2Hash32 [0x00] =
    [233, 139, 182, 115, 89, 72, 21, 126, 245, 149, 62, 120, 26, 254, 106, 209, 111, 96, 153, 251, 141, 207, 186,
     100, 74, 174, 87, 99, 85, 43, 117, 48] := by decide +kernel
example : poseidon2Hash32 [0x01, 0x02, 0x03] =
    [196, 180, 177, 170, 216, 21, 133, 248, 62, 149, 42, 39, 133, 17, 81, 112, 144, 59, 209, 93, 95, 26, 110, 112,
     237, 219, 50, 120, 128, 103, 142, 202] := by decide +kernel


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
