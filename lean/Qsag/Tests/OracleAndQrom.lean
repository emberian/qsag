module
public import Qsag.Math.GoldilocksBase
public import Qsag.Math.Counting
public import Qsag.Oracle.FiatShamir
public import Qsag.Math.Goldilocks
public import Qsag.Oracle.Keccak
public import Qsag.Oracle.Poseidon2
public import Qsag.Oracle.Sponge
public import Qsag.Tactic.Prelude
public import Qsag.Oracle.PublicPermutation
public import Qsag.Math.Gf2Pow128
public import Qsag.Spec.Bounds
public import Qsag.Spec.Encoding
public import Qsag.Oracle.Qrom
public section
set_option exponentiation.threshold 8192
namespace Qsag
set_option autoImplicit false
/-! ## 6. Official NIST FIPS 202 `SHAKE256` Build-Time Conformance Vectors

The two executed `shake256Xof` vectors are checked in `Oracle/Keccak` (same section title), where the
permutation body is visible. -/


/-! ## 5. Build-Time Conformance Vectors Matching `poseidon2.rs`

The executed `poseidon2Perm12` / `poseidon2Hash32` / `poseidon2CompressWeighted` vectors are checked in
`Oracle/Poseidon2` (section "5. Build-Time Conformance Vectors"), where the permutation body is visible. -/


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
  have hEncLen : (encodeString [] ++ encodeString (List.replicate 131 0x41)).length = 136 :=
    encodeString_empty_append_replicate131_length
  have hPfxLen : (cshakePrefix [] (List.replicate 131 0x41)).length = 272 := by
    unfold cshakePrefix
    rw [bytepad_eq]
    simp only [show (136 : Nat) ≠ 0 from by decide, ↓reduceIte, List.length_append,
      List.length_replicate, hEncLen, leftEncode_length_short (show 136 < 256 by decide)]
  exact ⟨List.replicate 131 0x41, rfl, by rw [hEncLen]; decide, hPfxLen, by rw [hPfxLen]; decide⟩

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


end Qsag

section
namespace Qsag
open MigrationExecution

set_option autoImplicit false

-- The executed controls of this section (`lazyRo_query_regime_characterization`, the BHT and Merkle teeth,
-- the canopy toy instance, the online-extraction and query-record teeth, `measured_parity_execution`)
-- are proved in `Oracle/Qrom`, whose definitions they evaluate; they are audited and paired below.
#verify_constructive tooth_bht_256bit_unrestricted_collision_ceiling_85bits
#verify_constructive tooth_merkle_right_blind_compression_collides

end Qsag
end

namespace Qsag
#tooth_pair canopyToy_honest_accepted vs tooth_canopy_sibling_mutation


#verify_inhabited verifyCanopyMultiproof_exact_sibling_count inhabited_canopy_nonempty_opening
#verify_constructive tooth_canopy_sibling_mutation inhabited_canopy_nonempty_opening


#verify_constructive inhabited_canopy_multiproof_binding
#verify_constructive tooth_onlineMerkle_empty_queries_unqueried_root
#tooth_pair Qsag.onlineMerkle_preChallenge_unique vs Qsag.tooth_onlineMerkle_empty_queries_unqueried_root
-- `witnessInitVec_pos` and `witnessCoverProof` are private to `Oracle/Qrom` and audited there.
#verify_constructive inhabited_qrom_unitary_merkle_extract
#verify_inhabited Qsag.qrom_unitary_multiRoot_merkle_extract_bound Qsag.inhabited_qrom_unitary_merkle_extract
#verify_constructive tooth_qrom_self_target_not_local
#verify_constructive tooth_qrom_query_record_changes_born_probability

end Qsag

public section
set_option exponentiation.threshold 8192
namespace Qsag
open RoundPoly


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

-- The toy Merkle layout and its executed runs (`toy_measured_merkle_execution`, `toyQueryAdv_classical`,
-- `toy_classical_run_execution`) are proved in `Oracle/Qrom`.

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
-- `raw_vs_feedforward_tooth`, `identity_collision_tooth` and `unchecked_preimage_tooth` are proved in
-- `Oracle/Poseidon2`, namespace `Qsag.CrossProtocol` (they evaluate `rawTrunc` / `jiveCompress`).


#verify_constructive raw_vs_feedforward_tooth
#tooth_pair inverse_feedforward_relation vs raw_vs_feedforward_tooth
#verify_constructive identity_collision_tooth
#verify_constructive unchecked_preimage_tooth

end Qsag.CrossProtocol
end

public section
set_option exponentiation.threshold 8192
namespace Qsag.PreprocessingGame
-- The preprocessing-game controls (`storedCollision*`, `fixedAdvice_collision_count`,
-- `freshSalt_chronology_execution`, `oneSaltTable_bound`, `twiceQuery_execution`) are proved in
-- `Oracle/Qrom`, namespace `Qsag.PreprocessingGame`: they execute `Program.run`, `adviceWinCount`,
-- `collisionWin` and `tableWin`.


end Qsag.PreprocessingGame
end

public section
set_option exponentiation.threshold 8192
namespace Qsag.PreprocessingGame
set_option autoImplicit false


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
-- `paritySuccess`, `coherent_parity_runtime_execution` and `tooth_fourier_database_measurement_disturbs`
-- are proved in `Oracle/Qrom` (they execute its coherent / Fourier runtime).


#verify_constructive tooth_fourier_database_measurement_disturbs

end Qsag
end

public section
namespace Qsag
open MigrationExecution
#verify_constructive lazyRo_query_regime_characterization
  measured_parity_execution coherent_parity_runtime_execution
end Qsag
end
