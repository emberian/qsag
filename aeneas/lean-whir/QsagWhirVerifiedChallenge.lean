module
public import Aeneas
public import QsagWhirVerified.Types
public import QsagWhirVerified.Funs
public import QsagWhirVerifiedChallengeDefs

public section

/-!
# Independent statement file for the WHIR Rust MIR refinement theorems

This module pins the exact theorem statements for the generated `qsag-whir-verified`
Rust MIR model (`QsagWhirVerified.Types` and `QsagWhirVerified.Funs`) without importing
any proof module (`Arithmetic` or `Proofs`). `lake comparator --paranoid` checks that
`QsagWhirVerified` proves every theorem listed in `comparator.json` over identical
definitions, using only `propext` and `Quot.sound`, and replays the proofs across all
six external kernels.

Every theorem body below is `sorry`, following the comparator challenge convention.
-/

open Aeneas Aeneas.Std
namespace qsag_whir_verified.proofs
set_option maxRecDepth 4096

/-! ## 1. Goldilocks & Quartic Extension Arithmetic Refinements -/

theorem goldilocks_p_val : GOLDILOCKS_P.val = 18446744069414584321 := sorry

theorem max_u64_word_val : MAX_U64_WORD.val = 18446744073709551615 := sorry

theorem tag_canopy_merkle_internal_eq : TAG_CANOPY_MERKLE_INTERNAL = 0#u8 := sorry

theorem add_refines (a b : U64) : add a b = .ok (fieldAdd a b) := sorry

theorem sub_refines (a b : U64) : sub a b = .ok (fieldSub a b) := sorry

theorem mul_refines (a b : U64) : mul a b = .ok (fieldMul a b) := sorry

theorem ext_add_refines (x y : Ext4) : ext_add x y = .ok (extAdd x y) := sorry

theorem ext_sub_refines (x y : Ext4) : ext_sub x y = .ok (extSub x y) := sorry

theorem ext_scale_refines (x : Ext4) (y : U64) : ext_scale x y = .ok (extScale x y) := sorry

theorem ext_mul_refines (x y : Ext4) : ext_mul x y = .ok (extMul x y) := sorry

theorem affine_combine_refines (even odd alpha : Ext4) :
    affine_combine even odd alpha = .ok (extAdd odd (extMul alpha even)) := sorry

/-! ## 2. Canonical Goldilocks & `Ext4` Wire Decoding -/

theorem decode_canonical_u64_spec (x : U64) :
    decode_canonical_u64 x = .ok (if x.val < goldilocksMod then some x else none) := sorry

theorem decode_canonical_u64_some_iff (x y : U64) :
    decode_canonical_u64 x = .ok (some y) ↔ IsCanonical x ∧ y = x := sorry

theorem decode_canonical_u64_none_iff (x : U64) :
    decode_canonical_u64 x = .ok none ↔ goldilocksMod ≤ x.val := sorry

theorem decode_canonical_u64_rejects_noncanonical (x : U64)
    (h : GOLDILOCKS_P.val ≤ x.val) : decode_canonical_u64 x = .ok none := sorry

theorem decode_canonical_ext4_some_iff (a b c d : U64) (out : Ext4) :
    decode_canonical_ext4 a b c d = .ok (some out) ↔
      IsCanonical a ∧ IsCanonical b ∧ IsCanonical c ∧ IsCanonical d ∧ out = ⟨a, b, c, d⟩ := sorry

theorem decode_canonical_ext4_none_iff (a b c d : U64) :
    decode_canonical_ext4 a b c d = .ok none ↔
      ¬ (IsCanonical a ∧ IsCanonical b ∧ IsCanonical c ∧ IsCanonical d) := sorry

/-! ## 3. Duet Folding, CWYZ Folding, Dual Bridge, Sumcheck Wire, & Cascade -/

theorem ext_eq_sound (x y : Ext4) : ext_eq x y = .ok true ↔ x = y := sorry

theorem duet_fold_coset_sound
    {even odd : Ext4} {y0 iy it : U64} (alpha : Ext4)
    (he : IsCanonicalExt4 even) (ho : IsCanonicalExt4 odd)
    (hit : fieldMul 2#u64 it = 1#u64)
    (hiy : fieldMul (fieldMul 2#u64 y0) iy = 1#u64) :
    duet_fold (extAdd even (extScale odd y0)) (extSub even (extScale odd y0)) iy it alpha =
      .ok (extAdd odd (extMul alpha even)) := sorry

theorem verify_affine_duet_fold_step_coset_sound
    {even odd : Ext4} {y0 iy it : U64} (alpha claimed : Ext4)
    (he : IsCanonicalExt4 even) (ho : IsCanonicalExt4 odd)
    (hit : fieldMul 2#u64 it = 1#u64)
    (hiy : fieldMul (fieldMul 2#u64 y0) iy = 1#u64) :
    verify_affine_duet_fold_step
        (extAdd even (extScale odd y0)) (extSub even (extScale odd y0))
        iy it alpha claimed = .ok true ↔
      claimed = extAdd odd (extMul alpha even) := sorry

theorem cwyz_duet_fold_coset_sound
    {even odd : Ext4} {y0 iy it : U64} (theta alpha beta : Ext4)
    (he : IsCanonicalExt4 even) (ho : IsCanonicalExt4 odd)
    (hit : fieldMul 2#u64 it = 1#u64)
    (hiy : fieldMul (fieldMul 2#u64 y0) iy = 1#u64) :
    cwyz_duet_fold (extAdd even (extScale odd y0)) (extSub even (extScale odd y0))
        iy it (fieldMul y0 y0) theta alpha beta =
      .ok (extAdd odd (extMul (extAdd alpha (extScale beta (fieldMul y0 y0)))
        (extAdd even (extMul theta odd)))) := sorry

theorem fold_duet_affine_ext4_coset_sound
    {even odd : Ext4} {y0 iy it : U64} (theta alpha beta : Ext4)
    (he : IsCanonicalExt4 even) (ho : IsCanonicalExt4 odd)
    (hit : fieldMul 2#u64 it = 1#u64)
    (hiy : fieldMul (fieldMul 2#u64 y0) iy = 1#u64) :
    fold_duet_affine_ext4 (extAdd even (extScale odd y0)) (extSub even (extScale odd y0))
        iy it (fieldMul y0 y0) theta alpha beta =
      .ok (extAdd odd (extMul (extAdd alpha (extScale beta (fieldMul y0 y0)))
        (extAdd even (extMul theta odd)))) := sorry

theorem verify_cwyz_duet_fold_step_coset_sound
    {even odd : Ext4} {y0 iy it : U64} (theta alpha beta claimed : Ext4)
    (he : IsCanonicalExt4 even) (ho : IsCanonicalExt4 odd)
    (hit : fieldMul 2#u64 it = 1#u64)
    (hiy : fieldMul (fieldMul 2#u64 y0) iy = 1#u64) :
    verify_cwyz_duet_fold_step
        (extAdd even (extScale odd y0)) (extSub even (extScale odd y0))
        iy it (fieldMul y0 y0) theta alpha beta claimed = .ok true ↔
      claimed = extAdd odd (extMul (extAdd alpha (extScale beta (fieldMul y0 y0)))
                  (extAdd even (extMul theta odd))) := sorry

theorem cwyz_bridge_claim_step_dual_spec
    (a0 a1 b0 b1 kn phi theta alpha beta : Ext4) :
    cwyz_bridge_claim_step
        (extMul a0 b0) (extMul a0 b1) (extMul a1 b0) (extMul a0 kn) (extMul a1 kn)
        (extAdd (extMul a0 b0) (extMul a1 b1)) phi theta alpha beta =
      .ok (extAdd
        (extMul (extAdd a1 (extMul alpha (extAdd a0 (extMul theta a1)))) (extAdd b0 (extMul phi b1)))
        (extMul (extMul beta (extAdd a0 (extMul theta a1))) kn)) := sorry

theorem verify_cwyz_bridge_claim_step_dual_sound
    (a0 a1 b0 b1 kn phi theta alpha beta claimed_next : Ext4) :
    verify_cwyz_bridge_claim_step
        (extMul a0 b0) (extMul a0 b1) (extMul a1 b0) (extMul a0 kn) (extMul a1 kn)
        (extAdd (extMul a0 b0) (extMul a1 b1)) phi theta alpha beta claimed_next = .ok true ↔
      claimed_next = extAdd
        (extMul (extAdd a1 (extMul alpha (extAdd a0 (extMul theta a1)))) (extAdd b0 (extMul phi b1)))
        (extMul (extMul beta (extAdd a0 (extMul theta a1))) kn) := sorry

theorem eval_quadratic_sumcheck_wire_hypercube_spec
    (c0 c2 sum_claim : Ext4) (hs : IsCanonicalExt4 sum_claim) :
    ∃ y0 y1,
      eval_quadratic_sumcheck_wire c0 c2 sum_claim extZero = .ok y0 ∧
      eval_quadratic_sumcheck_wire c0 c2 sum_claim extOne = .ok y1 ∧
      extAdd y0 y1 = sum_claim := sorry

theorem affine_cascade_claim_step_spec
    (acc w0 w1 eval_at_point shifted_eval : Ext4) :
    affine_cascade_claim_step acc w0 w1 eval_at_point shifted_eval =
      .ok (extAdd (extAdd acc (extMul w0 eval_at_point)) (extMul w1 shifted_eval)) := sorry

/-! ## 4. Arbitrary-Slice Horner Evaluation & Polynomial Pin Verification -/

theorem eval_ext4_univariate_at_base_spec (coeffs : Slice Ext4) (z : U64) :
    eval_ext4_univariate_at_base coeffs z = .ok (hornerSpec coeffs.val z extZero) := sorry

theorem eval_ext4_univariate_at_base_ascending_sound (coeffs : Slice Ext4) (z : U64)
    (hcan : ∀ c ∈ coeffs.val, IsCanonicalExt4 c) :
    eval_ext4_univariate_at_base coeffs z = .ok (evalPolyAscending coeffs.val z) := sorry

theorem eval_univariate_ext4_at_base_spec (coeffs : Slice Ext4) (z : U64) :
    eval_univariate_ext4_at_base coeffs z = .ok (hornerSpec coeffs.val z extZero) := sorry

theorem eval_univariate_ext4_at_base_ascending_sound (coeffs : Slice Ext4) (z : U64)
    (hcan : ∀ c ∈ coeffs.val, IsCanonicalExt4 c) :
    eval_univariate_ext4_at_base coeffs z = .ok (evalPolyAscending coeffs.val z) := sorry

theorem verify_ext4_univariate_at_base_pin_sound
    (coeffs : Slice Ext4) (z : U64) (expected : Ext4) :
    verify_ext4_univariate_at_base_pin coeffs z expected = .ok true ↔
      expected = hornerSpec coeffs.val z extZero := sorry

theorem verify_ext4_univariate_at_base_pin_ascending_sound
    (coeffs : Slice Ext4) (z : U64) (expected : Ext4)
    (hcan : ∀ c ∈ coeffs.val, IsCanonicalExt4 c) :
    verify_ext4_univariate_at_base_pin coeffs z expected = .ok true ↔
      expected = evalPolyAscending coeffs.val z := sorry

/-! ## 5. Stage PoW Mask, OOD Equality, Query Reduction, Merkle Ordering, & Quorum Sum -/

theorem verify_stage_pow_mask_sound (word : U64) (bits : U32) :
    verify_stage_pow_mask word bits = .ok true ↔
      bits.val ≤ 32 ∧ word.bv &&& BitVec.ofNat 64 (2 ^ bits.val - 1) = 0 := sorry

theorem verify_stage_pow_mask_mod_sound (word : U64) (bits : U32) :
    verify_stage_pow_mask word bits = .ok true ↔
      bits.val ≤ 32 ∧ word.val % (2 ^ bits.val) = 0 := sorry

theorem verify_ood_pin_eq_sound (expected supplied : Slice U64) :
    verify_ood_pin_eq expected supplied = .ok true ↔ expected.val = supplied.val := sorry

theorem verify_ood_pin_eq_false_iff (expected supplied : Slice U64) :
    verify_ood_pin_eq expected supplied = .ok false ↔ expected.val ≠ supplied.val := sorry

theorem canonical_query_group_idx_some_iff (raw groups idx : U64) :
    canonical_query_group_idx raw groups = .ok (some idx) ↔
      0 < groups.val ∧ idx.val = raw.val % groups.val := sorry

theorem canonical_query_group_idx_none_iff (raw groups : U64) :
    canonical_query_group_idx raw groups = .ok none ↔ groups = 0#u64 := sorry

theorem canonical_query_group_idx_lt_groups (raw groups idx : U64)
    (h : canonical_query_group_idx raw groups = .ok (some idx)) : idx.val < groups.val := sorry

theorem step_merkle_pair_order_some_iff
    (idx : U64) (level : U32) (node sibling : Array U8 32#usize) (pair : MerklePair) :
    step_merkle_pair_order idx level node sibling = .ok (some pair) ↔
      level.val < 64 ∧ pair.tag = 0#u8 ∧
      (if (idx.val >>> level.val) % 2 = 0
       then pair.left = node ∧ pair.right = sibling
       else pair.left = sibling ∧ pair.right = node) := sorry

theorem step_merkle_pair_order_none_iff
    (idx : U64) (level : U32) (node sibling : Array U8 32#usize) :
    step_merkle_pair_order idx level node sibling = .ok none ↔ 64 ≤ level.val := sorry

theorem step_merkle_pair_order_tag_eq
    (idx : U64) (level : U32) (node sibling : Array U8 32#usize) (pair : MerklePair)
    (h : step_merkle_pair_order idx level node sibling = .ok (some pair)) :
    pair.tag = TAG_CANOPY_MERKLE_INTERNAL := sorry

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

theorem checked_quorum_sum_total
    (counts minimums : Slice U64) (minimum_global : U64) :
    ∃ out : Option U64, checked_quorum_sum counts minimums minimum_global = .ok out := sorry

theorem checked_quorum_sum_sound
    (counts minimums : Slice U64) (minimum_global total : U64) :
    checked_quorum_sum counts minimums minimum_global = .ok (some total) ↔
      QuorumSumSpec counts.val minimums.val minimum_global total.val := sorry

theorem checked_quorum_sum_none_iff
    (counts minimums : Slice U64) (minimum_global : U64) :
    checked_quorum_sum counts minimums minimum_global = .ok none ↔
      ¬ ∃ s : Nat, QuorumSumSpec counts.val minimums.val minimum_global s := sorry

theorem checked_quorum_sum_le_max_u64_word
    (counts minimums : Slice U64) (minimum_global total : U64)
    (h : checked_quorum_sum counts minimums minimum_global = .ok (some total)) :
    natSumU64 counts.val ≤ MAX_U64_WORD.val := sorry

/-! ## 6. Concrete `#tooth` Mutation-Sensitivity & Non-Vacuity Controls -/

theorem tooth_unchecked_mod_p_accepts_aliased_field_limb :
    (0#u64) ≠ GOLDILOCKS_P ∧
    (0#u64 % GOLDILOCKS_P : Result U64) = .ok 0#u64 ∧
    (GOLDILOCKS_P % GOLDILOCKS_P : Result U64) = .ok 0#u64 ∧
    decode_canonical_u64 GOLDILOCKS_P = .ok none := sorry

theorem tooth_decode_canonical_ext4_rejects_fourth_limb_alias :
    decode_canonical_ext4 1#u64 2#u64 3#u64 GOLDILOCKS_P = .ok none ∧
    decode_canonical_ext4 1#u64 2#u64 3#u64 4#u64 = .ok (some ⟨1#u64, 2#u64, 3#u64, 4#u64⟩) := sorry

theorem tooth_pow_rejects_excessive_bits_and_nonzero_low_bits :
    verify_stage_pow_mask 0#u64 33#u32 = .ok false ∧
    verify_stage_pow_mask 8#u64 4#u32 = .ok false ∧
    verify_stage_pow_mask 16#u64 4#u32 = .ok true := sorry

theorem tooth_merkle_pair_swaps_on_direction_bit_and_rejects_shift64 :
    let z := Array.repeat 32#usize 0x11#u8
    let w := Array.repeat 32#usize 0x22#u8
    z ≠ w ∧
    step_merkle_pair_order 0#u64 0#u32 z w = .ok (some ⟨0#u8, z, w⟩) ∧
    step_merkle_pair_order 1#u64 0#u32 z w = .ok (some ⟨0#u8, w, z⟩) ∧
    step_merkle_pair_order 0#u64 64#u32 z w = .ok none := sorry

theorem tooth_checked_quorum_sum_rejects_u64_wraparound_forgery :
    let overflow_counts : Slice U64 := Array.to_slice (Array.make 2#usize [MAX_U64_WORD, 5#u64])
    let overflow_mins : Slice U64 := Array.to_slice (Array.make 2#usize [1#u64, 1#u64])
    let honest_counts : Slice U64 := Array.to_slice (Array.make 2#usize [10#u64, 15#u64])
    let honest_mins : Slice U64 := Array.to_slice (Array.make 2#usize [8#u64, 12#u64])
    checked_quorum_sum overflow_counts overflow_mins 4#u64 = .ok none ∧
    checked_quorum_sum honest_counts honest_mins 20#u64 = .ok (some 25#u64) := sorry

theorem tooth_ood_pin_rejects_perturbation_and_length_mismatch :
    let s1 : Slice U64 := Array.to_slice (Array.make 4#usize [1#u64, 2#u64, 3#u64, 4#u64])
    let s2 : Slice U64 := Array.to_slice (Array.make 4#usize [1#u64, 2#u64, 3#u64, 5#u64])
    let s3 : Slice U64 := Array.to_slice (Array.make 3#usize [1#u64, 2#u64, 3#u64])
    verify_ood_pin_eq s1 s2 = .ok false ∧
    verify_ood_pin_eq s1 s3 = .ok false ∧
    verify_ood_pin_eq s1 s1 = .ok true := sorry

theorem tooth_coset_inverse_premises_inhabited_and_fold_rejects_perturbation :
    let it := 9223372034707292161#u64
    let y0 := 2#u64
    let iy := 13835058052060938241#u64
    let yy := 4#u64
    let v0 : Ext4 := ⟨29#u64, 39#u64, 45#u64, 57#u64⟩
    let v1 : Ext4 := ⟨18446744069414584298#u64, 18446744069414584292#u64,
                      18446744069414584290#u64, 18446744069414584286#u64⟩
    let theta : Ext4 := ⟨2#u64, 0#u64, 0#u64, 0#u64⟩
    let alpha : Ext4 := ⟨5#u64, 0#u64, 0#u64, 0#u64⟩
    let beta : Ext4 := ⟨7#u64, 0#u64, 0#u64, 0#u64⟩
    let duet_honest : Ext4 := ⟨28#u64, 42#u64, 54#u64, 78#u64⟩
    let duet_forged : Ext4 := ⟨28#u64, 42#u64, 54#u64, 79#u64⟩
    let cwyz_honest : Ext4 := ⟨970#u64, 1304#u64, 1504#u64, 1904#u64⟩
    let cwyz_forged : Ext4 := ⟨970#u64, 1304#u64, 1504#u64, 1905#u64⟩
    fieldMul 2#u64 it = 1#u64 ∧
    fieldMul (fieldMul 2#u64 y0) iy = 1#u64 ∧
    fold_duet_affine_ext4 v0 v1 iy it yy theta alpha beta = .ok cwyz_honest ∧
    cwyz_duet_fold v0 v1 iy it yy theta alpha beta = .ok cwyz_honest ∧
    verify_affine_duet_fold_step v0 v1 iy it alpha duet_honest = .ok true ∧
    verify_affine_duet_fold_step v0 v1 iy it alpha duet_forged = .ok false ∧
    verify_cwyz_duet_fold_step v0 v1 iy it yy theta alpha beta cwyz_honest = .ok true ∧
    verify_cwyz_duet_fold_step v0 v1 iy it yy theta alpha beta cwyz_forged = .ok false := sorry

theorem tooth_cwyz_bridge_accepts_dual_and_rejects_perturbation :
    let w0 : Ext4 := ⟨10#u64, 0#u64, 0#u64, 0#u64⟩
    let w1 : Ext4 := ⟨14#u64, 0#u64, 0#u64, 0#u64⟩
    let w2 : Ext4 := ⟨0#u64, 15#u64, 0#u64, 0#u64⟩
    let w3 : Ext4 := ⟨22#u64, 0#u64, 0#u64, 0#u64⟩
    let w4 : Ext4 := ⟨0#u64, 33#u64, 0#u64, 0#u64⟩
    let claim : Ext4 := ⟨10#u64, 21#u64, 0#u64, 0#u64⟩
    let phi : Ext4 := ⟨2#u64, 0#u64, 0#u64, 0#u64⟩
    let theta : Ext4 := ⟨2#u64, 0#u64, 0#u64, 0#u64⟩
    let alpha : Ext4 := ⟨5#u64, 0#u64, 0#u64, 0#u64⟩
    let beta : Ext4 := ⟨7#u64, 0#u64, 0#u64, 0#u64⟩
    let honest : Ext4 := ⟨344#u64, 1089#u64, 0#u64, 0#u64⟩
    let forged : Ext4 := ⟨344#u64, 1090#u64, 0#u64, 0#u64⟩
    cwyz_bridge_claim_step w0 w1 w2 w3 w4 claim phi theta alpha beta = .ok honest ∧
    verify_cwyz_bridge_claim_step w0 w1 w2 w3 w4 claim phi theta alpha beta honest = .ok true ∧
    verify_cwyz_bridge_claim_step w0 w1 w2 w3 w4 claim phi theta alpha beta forged = .ok false := sorry

theorem tooth_horner_and_pin_accepts_ascending_and_rejects_perturbation :
    let coeffs : Slice Ext4 :=
      Array.to_slice (Array.make 3#usize
        [⟨1#u64, 0#u64, 0#u64, 0#u64⟩,
         ⟨2#u64, 0#u64, 0#u64, 0#u64⟩,
         ⟨3#u64, 0#u64, 0#u64, 0#u64⟩])
    let honest : Ext4 := ⟨17#u64, 0#u64, 0#u64, 0#u64⟩
    let forged : Ext4 := ⟨18#u64, 0#u64, 0#u64, 0#u64⟩
    eval_ext4_univariate_at_base coeffs 2#u64 = .ok honest ∧
    eval_univariate_ext4_at_base coeffs 2#u64 = .ok honest ∧
    verify_ext4_univariate_at_base_pin coeffs 2#u64 honest = .ok true ∧
    verify_ext4_univariate_at_base_pin coeffs 2#u64 forged = .ok false := sorry

theorem tooth_quadratic_sumcheck_wire_nontrivial_eval :
    let c0 : Ext4 := ⟨3#u64, 0#u64, 0#u64, 0#u64⟩
    let c2 : Ext4 := ⟨5#u64, 0#u64, 0#u64, 0#u64⟩
    let sum_claim : Ext4 := ⟨20#u64, 0#u64, 0#u64, 0#u64⟩
    eval_quadratic_sumcheck_wire c0 c2 sum_claim extZero = .ok ⟨3#u64, 0#u64, 0#u64, 0#u64⟩ ∧
    eval_quadratic_sumcheck_wire c0 c2 sum_claim extOne = .ok ⟨17#u64, 0#u64, 0#u64, 0#u64⟩ ∧
    eval_quadratic_sumcheck_wire c0 c2 sum_claim ⟨2#u64, 0#u64, 0#u64, 0#u64⟩ =
      .ok ⟨41#u64, 0#u64, 0#u64, 0#u64⟩ := sorry

end qsag_whir_verified.proofs

public section
namespace qsag_whir_verified.proofs

theorem fieldAbs_add (x y : U64) :
    fieldAbs (fieldAdd x y) = Qsag.Goldilocks.add (fieldAbs x) (fieldAbs y) := by sorry

theorem fieldAbs_mul (x y : U64) :
    fieldAbs (fieldMul x y) = Qsag.Goldilocks.mul (fieldAbs x) (fieldAbs y) := by sorry

theorem fieldAbs_sub (x y : U64) :
    fieldAbs (fieldSub x y) = Qsag.Goldilocks.sub (fieldAbs x) (fieldAbs y) := by sorry

theorem ext4Abs_add (x y : Ext4) :
    ext4Abs (extAdd x y) = Qsag.Aggregation.GoldilocksExt4.add (ext4Abs x) (ext4Abs y) := by sorry

theorem ext4Abs_sub (x y : Ext4) :
    ext4Abs (extSub x y) = Qsag.Aggregation.GoldilocksExt4.sub (ext4Abs x) (ext4Abs y) := by sorry

theorem ext4Abs_mul (x y : Ext4) :
    ext4Abs (extMul x y) = Qsag.Aggregation.GoldilocksExt4.mul (ext4Abs x) (ext4Abs y) := by sorry

theorem ext_mul_refines_exec (x y : Ext4) :
    (ext4Abs <$> ext_mul x y) =
      .ok (Qsag.Aggregation.GoldilocksExt4.mul (ext4Abs x) (ext4Abs y)) := by sorry

theorem cwyz_bridge_refines_exec
    (e0 e1 e2 e3 e4 claim phi theta alpha beta : Ext4) :
    (ext4Abs <$> cwyz_bridge_claim_step e0 e1 e2 e3 e4 claim phi theta alpha beta) =
      .ok (Qsag.Exec.hemBridgeClaimStep
        (ext4Abs e0) (ext4Abs e1) (ext4Abs e2) (ext4Abs e3) (ext4Abs e4)
        (ext4Abs claim) (ext4Abs phi) (ext4Abs theta) (ext4Abs alpha) (ext4Abs beta)) := by sorry

theorem ext4Abs_scale (x : Ext4) (s : U64) :
    ext4Abs (extScale x s) = Qsag.Aggregation.GoldilocksExt4.mul (ext4Abs x)
      (Qsag.Aggregation.GoldilocksExt4.embedBase (fieldAbs s)) := by sorry

theorem fieldAbs_zero : fieldAbs 0#u64 = Qsag.Goldilocks.zero := by sorry

theorem fieldAbs_one : fieldAbs 1#u64 = Qsag.Goldilocks.one := by sorry

theorem ext4Abs_zero : ext4Abs extZero = Qsag.Aggregation.GoldilocksExt4.zero := by sorry

theorem ext4Abs_one : ext4Abs extOne = Qsag.Aggregation.GoldilocksExt4.one := by sorry

theorem duet_fold_refines_exec (v0 v1 : Ext4) (iy it : U64) (alpha : Ext4) :
    (ext4Abs <$> duet_fold v0 v1 iy it alpha) =
      .ok (Qsag.Exec.hemDuetFold (ext4Abs v0) (ext4Abs v1)
        (fieldAbs iy) (fieldAbs it) (ext4Abs alpha)) := by sorry

theorem hornerSpec_refines_exec (coeffs : List Ext4) (z : U64) (init : Ext4) :
    ext4Abs (hornerSpec coeffs z init) =
      Qsag.Exec.hemHorner (coeffs.map ext4Abs) (fieldAbs z) (ext4Abs init) := by sorry

theorem eval_ext4_univariate_refines_exec (coeffs : Slice Ext4) (z : U64) :
    (ext4Abs <$> eval_ext4_univariate_at_base coeffs z) =
      .ok (Qsag.Exec.hemHorner (coeffs.val.map ext4Abs) (fieldAbs z)) := by sorry

theorem fold_duet_affine_ext4_refines_exec
    (v0 v1 : Ext4) (iy it yy : U64) (theta alpha beta : Ext4) (x : Qsag.Goldilocks)
    (hit : fieldAbs it = Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2))
    (hiy : fieldAbs iy = Qsag.Goldilocks.mul (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2))
      (Qsag.Goldilocks.inv x))
    (hyy : fieldAbs yy = Qsag.Goldilocks.mul x x) :
    (ext4Abs <$> fold_duet_affine_ext4 v0 v1 iy it yy theta alpha beta) =
      .ok (Qsag.Exec.hemAffineDuetFold (ext4Abs v0) (ext4Abs v1) x
        (ext4Abs theta) (ext4Abs alpha) (ext4Abs beta)) := by sorry

theorem canonicalFieldWord_val (x : Qsag.Goldilocks) :
    (canonicalFieldWord x).val = x.val := by sorry

theorem isCanonical_canonicalFieldWord (x : Qsag.Goldilocks) :
    IsCanonical (canonicalFieldWord x) := by sorry

theorem fieldAbs_canonicalFieldWord (x : Qsag.Goldilocks) :
    fieldAbs (canonicalFieldWord x) = x := by sorry

theorem canonicalFieldWord_fieldAbs {x : U64} (hx : IsCanonical x) :
    canonicalFieldWord (fieldAbs x) = x := by sorry

theorem fieldAbs_inj {x y : U64} (hx : IsCanonical x) (hy : IsCanonical y) :
    fieldAbs x = fieldAbs y ↔ x = y := by sorry

theorem isCanonicalExt4_canonicalExt4 (z : Qsag.Aggregation.GoldilocksExt4) :
    IsCanonicalExt4 (canonicalExt4 z) := by sorry

theorem ext4Abs_canonicalExt4 (z : Qsag.Aggregation.GoldilocksExt4) :
    ext4Abs (canonicalExt4 z) = z := by sorry

theorem canonicalExt4_ext4Abs {x : Ext4} (hx : IsCanonicalExt4 x) :
    canonicalExt4 (ext4Abs x) = x := by sorry

theorem ext4Abs_inj {x y : Ext4} (hx : IsCanonicalExt4 x) (hy : IsCanonicalExt4 y) :
    ext4Abs x = ext4Abs y ↔ x = y := by sorry

theorem isCanonicalExt4_extInv (x : Ext4) : IsCanonicalExt4 (extInv x) := by sorry

theorem ext4Abs_inv (x : Ext4) :
    ext4Abs (extInv x) = Qsag.Aggregation.GoldilocksExt4.inv (ext4Abs x) := by sorry

theorem ext_mul_extInv_ok_one {x : Ext4}
    (hz : ext4Abs x ≠ Qsag.Aggregation.GoldilocksExt4.zero) :
    ext_mul x (extInv x) = .ok extOne := by sorry

theorem canonicalFieldWord_two_inv :
    fieldMul 2#u64 (canonicalFieldWord (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2))) = 1#u64 := by sorry

theorem canonicalFieldWord_two_x_inv {x : Qsag.Goldilocks} (hx : x ≠ Qsag.Goldilocks.zero) :
    fieldMul (fieldMul 2#u64 (canonicalFieldWord x))
      (canonicalFieldWord (Qsag.Goldilocks.mul
        (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)) (Qsag.Goldilocks.inv x))) = 1#u64 := by sorry

theorem fold_duet_affine_ext4_canonical_twiddles
    (v0 v1 : Ext4) (x : Qsag.Goldilocks) (theta alpha beta : Ext4) :
    (ext4Abs <$> fold_duet_affine_ext4 v0 v1
      (canonicalFieldWord (Qsag.Goldilocks.mul
        (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)) (Qsag.Goldilocks.inv x)))
      (canonicalFieldWord (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)))
      (canonicalFieldWord (Qsag.Goldilocks.mul x x)) theta alpha beta) =
      .ok (Qsag.Exec.hemAffineDuetFold (ext4Abs v0) (ext4Abs v1) x
        (ext4Abs theta) (ext4Abs alpha) (ext4Abs beta)) := by sorry

theorem decode_canonical_u64_refines_qsag (x : U64) :
    (Option.map fieldAbs <$> decode_canonical_u64 x) =
      .ok (if x.val < Qsag.goldilocksPrime then some (Qsag.Goldilocks.ofNat x.val) else none) := by sorry

theorem decode_canonical_ext4_refines_qsag (a b c d : U64) :
    (Option.map ext4Abs <$> decode_canonical_ext4 a b c d) =
      .ok (if a.val < Qsag.goldilocksPrime ∧ b.val < Qsag.goldilocksPrime ∧
              c.val < Qsag.goldilocksPrime ∧ d.val < Qsag.goldilocksPrime
           then some (Qsag.Math.aggOfPolynomial ⟨fieldAbs a, fieldAbs b, fieldAbs c, fieldAbs d⟩)
           else none) := by sorry

theorem decode_canonical_ext4_canonicalExt4 (z : Qsag.Aggregation.GoldilocksExt4) :
    decode_canonical_ext4
      (canonicalFieldWord z.c0.c0) (canonicalFieldWord z.c1.c0)
      (canonicalFieldWord z.c0.c1) (canonicalFieldWord z.c1.c1) =
      .ok (some (canonicalExt4 z)) := by sorry

theorem embedBase_inv (a : Qsag.Goldilocks) :
    Qsag.Aggregation.GoldilocksExt4.embedBase (Qsag.Goldilocks.inv a) =
      Qsag.LawfulField.inv (Qsag.Aggregation.GoldilocksExt4.embedBase a) := by sorry

theorem hemAffineDuetFold_eq_hemVirtualFoldOracle
    (v0 v1 theta alpha beta : Qsag.Aggregation.GoldilocksExt4)
    (x : Qsag.Goldilocks)
    (curDom foldDom : List Qsag.Aggregation.GoldilocksExt4)
    (curOracle : Nat → Qsag.Aggregation.GoldilocksExt4) (idx : Nat)
    (hx : curDom.getD (2 * idx) Qsag.CommRingOps.one =
      Qsag.Aggregation.GoldilocksExt4.embedBase x)
    (hy : foldDom.getD idx Qsag.CommRingOps.zero =
      Qsag.Aggregation.GoldilocksExt4.embedBase (Qsag.Goldilocks.mul x x))
    (ha : curOracle (2 * idx) = v0)
    (hb : curOracle (2 * idx + 1) = v1) :
    Qsag.Exec.hemAffineDuetFold v0 v1 x theta alpha beta =
      Qsag.hemVirtualFoldOracle theta alpha beta curDom foldDom curOracle idx := by sorry

theorem fold_duet_affine_ext4_refines_hemVirtualFoldOracle
    (v0 v1 : Ext4) (x : Qsag.Goldilocks) (theta alpha beta : Ext4)
    (curDom foldDom : List Qsag.Aggregation.GoldilocksExt4)
    (curOracle : Nat → Qsag.Aggregation.GoldilocksExt4) (idx : Nat)
    (hx : curDom.getD (2 * idx) Qsag.CommRingOps.one =
      Qsag.Aggregation.GoldilocksExt4.embedBase x)
    (hy : foldDom.getD idx Qsag.CommRingOps.zero =
      Qsag.Aggregation.GoldilocksExt4.embedBase (Qsag.Goldilocks.mul x x))
    (ha : curOracle (2 * idx) = ext4Abs v0)
    (hb : curOracle (2 * idx + 1) = ext4Abs v1) :
    (ext4Abs <$> fold_duet_affine_ext4 v0 v1
      (canonicalFieldWord (Qsag.Goldilocks.mul
        (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)) (Qsag.Goldilocks.inv x)))
      (canonicalFieldWord (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)))
      (canonicalFieldWord (Qsag.Goldilocks.mul x x)) theta alpha beta) =
      .ok (Qsag.hemVirtualFoldOracle
        (ext4Abs theta) (ext4Abs alpha) (ext4Abs beta) curDom foldDom curOracle idx) := by sorry

theorem verify_cwyz_duet_fold_step_sound_qsag
    (v0 v1 : Ext4) (x : Qsag.Goldilocks) (theta alpha beta claimed : Ext4)
    (curDom foldDom : List Qsag.Aggregation.GoldilocksExt4)
    (curOracle : Nat → Qsag.Aggregation.GoldilocksExt4) (idx : Nat)
    (hx : curDom.getD (2 * idx) Qsag.CommRingOps.one =
      Qsag.Aggregation.GoldilocksExt4.embedBase x)
    (hy : foldDom.getD idx Qsag.CommRingOps.zero =
      Qsag.Aggregation.GoldilocksExt4.embedBase (Qsag.Goldilocks.mul x x))
    (ha : curOracle (2 * idx) = ext4Abs v0)
    (hb : curOracle (2 * idx + 1) = ext4Abs v1) :
    verify_cwyz_duet_fold_step v0 v1
      (canonicalFieldWord (Qsag.Goldilocks.mul
        (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)) (Qsag.Goldilocks.inv x)))
      (canonicalFieldWord (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)))
      (canonicalFieldWord (Qsag.Goldilocks.mul x x))
      theta alpha beta claimed = .ok true ↔
      (IsCanonicalExt4 claimed ∧
       ext4Abs claimed = Qsag.hemVirtualFoldOracle
         (ext4Abs theta) (ext4Abs alpha) (ext4Abs beta) curDom foldDom curOracle idx) := by sorry

theorem verify_affine_duet_fold_step_sound_qsag
    (v0 v1 : Ext4) (iy it : U64) (alpha claimed : Ext4) :
    verify_affine_duet_fold_step v0 v1 iy it alpha claimed = .ok true ↔
      (IsCanonicalExt4 claimed ∧
       ext4Abs claimed = Qsag.Exec.hemDuetFold
         (ext4Abs v0) (ext4Abs v1) (fieldAbs iy) (fieldAbs it) (ext4Abs alpha)) := by sorry

theorem verify_affine_duet_fold_step_roots_le_one
    (v0 v1 claimed : Ext4) (iy it : U64)
    (S : List Qsag.Aggregation.GoldilocksExt4) (hS : S.Nodup)
    (hne : ∃ r : Qsag.Aggregation.GoldilocksExt4,
      Qsag.Exec.hemDuetFold (ext4Abs v0) (ext4Abs v1) (fieldAbs iy) (fieldAbs it) r ≠
        ext4Abs claimed) :
    (S.filter (fun r => decide
      (verify_affine_duet_fold_step v0 v1 iy it (canonicalExt4 r) claimed = .ok true))).length ≤ 1 := by sorry

theorem hemBridgeClaimStep_eq_hemBridgeFoldClaim
    (e0 e1 e2 e3 e4 claim phi theta alpha beta : Qsag.Aggregation.GoldilocksExt4) :
    Qsag.Exec.hemBridgeClaimStep e0 e1 e2 e3 e4 claim phi theta alpha beta =
      Qsag.hemBridgeFoldClaim claim e0 e1 e2 e3 e4 phi theta alpha beta := by sorry

theorem verify_cwyz_bridge_claim_step_sound_qsag
    (w0 w1 w2 w3 w4 claim phi theta alpha beta claimed_next : Ext4) :
    verify_cwyz_bridge_claim_step w0 w1 w2 w3 w4 claim phi theta alpha beta claimed_next = .ok true ↔
      (IsCanonicalExt4 claimed_next ∧
       ext4Abs claimed_next = Qsag.hemBridgeFoldClaim
         (ext4Abs claim) (ext4Abs w0) (ext4Abs w1) (ext4Abs w2) (ext4Abs w3) (ext4Abs w4)
         (ext4Abs phi) (ext4Abs theta) (ext4Abs alpha) (ext4Abs beta)) := by sorry

theorem affine_cascade_claim_step_refines_evalCascadeClaim
    (w0 w1 eval_at_point shifted_eval : Ext4)
    (es ss : List Qsag.Aggregation.GoldilocksExt4)
    (abs : List (Qsag.Aggregation.GoldilocksExt4 × Qsag.Aggregation.GoldilocksExt4)) :
    (ext4Abs <$> affine_cascade_claim_step
      (canonicalExt4 (Qsag.evalCascadeClaim es ss abs)) w0 w1 eval_at_point shifted_eval) =
      .ok (Qsag.evalCascadeClaim
        (ext4Abs eval_at_point :: es)
        (ext4Abs shifted_eval :: ss)
        ((ext4Abs w0, ext4Abs w1) :: abs)) := by sorry

theorem eval_quadratic_sumcheck_wire_refines_qsag
    (c0 c2 sum_claim r : Ext4) :
    (ext4Abs <$> eval_quadratic_sumcheck_wire c0 c2 sum_claim r) =
      .ok (Qsag.RoundPoly.evalCoeffs
        (canonicalQuadraticWirePoly (ext4Abs c0) (ext4Abs c2) (ext4Abs sum_claim))
        (ext4Abs r)) := by sorry

theorem eval_quadratic_sumcheck_wire_bad_challenges_le_two
    (G S : List Qsag.Aggregation.GoldilocksExt4) (c0 c2 sum_claim : Ext4)
    (hS : S.Nodup) (hG : G.length ≤ 3)
    (hFalse : ext4Abs sum_claim ≠ Qsag.CommRingOps.add
      (Qsag.RoundPoly.evalCoeffs G Qsag.CommRingOps.zero)
      (Qsag.RoundPoly.evalCoeffs G Qsag.CommRingOps.one)) :
    (S.filter (fun r => decide
      ((ext4Abs <$> eval_quadratic_sumcheck_wire c0 c2 sum_claim (canonicalExt4 r)) =
        .ok (Qsag.RoundPoly.evalCoeffs G r)))).length ≤ 2 := by sorry

theorem hemHorner_zero_eq_evalCoeffs
    (cs : List Qsag.Aggregation.GoldilocksExt4) (z : Qsag.Goldilocks) :
    Qsag.Exec.hemHorner cs z Qsag.Aggregation.GoldilocksExt4.zero =
      Qsag.RoundPoly.evalCoeffs cs (Qsag.Aggregation.GoldilocksExt4.embedBase z) := by sorry

theorem eval_ext4_univariate_at_base_refines_evalCoeffs (coeffs : Slice Ext4) (z : U64) :
    (ext4Abs <$> eval_ext4_univariate_at_base coeffs z) =
      .ok (Qsag.RoundPoly.evalCoeffs (coeffs.val.map ext4Abs)
        (Qsag.Aggregation.GoldilocksExt4.embedBase (fieldAbs z))) := by sorry

theorem verify_ext4_univariate_at_base_pin_sound_qsag
    (coeffs : Slice Ext4) (z : U64) (expected : Ext4) :
    verify_ext4_univariate_at_base_pin coeffs z expected = .ok true ↔
      (IsCanonicalExt4 expected ∧
       ext4Abs expected = Qsag.RoundPoly.evalCoeffs (coeffs.val.map ext4Abs)
         (Qsag.Aggregation.GoldilocksExt4.embedBase (fieldAbs z))) := by sorry

theorem verify_ext4_univariate_at_base_pin_roots_le_degree
    (d : Nat) (candA candB : Slice Ext4) (S : List Qsag.Goldilocks)
    (hNodup : S.Nodup)
    (hLenA : candA.val.length ≤ d + 1) (hLenB : candB.val.length ≤ d + 1)
    (hDiff : ∃ z₀ : Qsag.Aggregation.GoldilocksExt4,
      Qsag.RoundPoly.evalCoeffs (candA.val.map ext4Abs) z₀ ≠
        Qsag.RoundPoly.evalCoeffs (candB.val.map ext4Abs) z₀) :
    (S.filter (fun z =>
      let pinA := canonicalExt4 (Qsag.RoundPoly.evalCoeffs (candA.val.map ext4Abs)
        (Qsag.Aggregation.GoldilocksExt4.embedBase z))
      decide (verify_ext4_univariate_at_base_pin candB (canonicalFieldWord z) pinA = .ok true))).length ≤
      d := by sorry

theorem ext4SliceWords_injective :
    ∀ {xs ys : List Qsag.Aggregation.GoldilocksExt4},
      ext4SliceWords xs = ext4SliceWords ys → xs = ys := by sorry

theorem verify_ood_pin_eq_canonical_ext4_iff
    (expected supplied : Slice U64)
    (expPins supPins : List Qsag.Aggregation.GoldilocksExt4)
    (he : expected.val = ext4SliceWords expPins)
    (hs : supplied.val = ext4SliceWords supPins) :
    verify_ood_pin_eq expected supplied = .ok true ↔ expPins = supPins := by sorry

theorem verify_stage_pow_mask_refines_canonical (word : U64) (bits : U32) :
    verify_stage_pow_mask word bits =
      .ok (Qsag.Aggregation.whirStagePowMask word.val bits.val) := by sorry

theorem verify_stage_pow_mask_16_iff_verifyWhirStagePow
    (chal : List UInt8) (powNonce word : U64)
    (hLen : chal.length = 32)
    (hLow16 : word.val % 65536 =
      let dig := Qsag.cshake256Bytes Qsag.Aggregation.whirPowCustomization
        (chal ++ Qsag.Aggregation.leBytes 8 powNonce.val)
      (dig.getD 0 0).toNat + 256 * (dig.getD 1 0).toNat) :
    verify_stage_pow_mask word 16#u32 = .ok true ↔
      Qsag.Aggregation.verifyWhirStagePow chal powNonce.val 16 = true := by sorry

theorem step_merkle_pair_order_canonical_parity
    (idx : U64) (level : U32) (node sibling : Array U8 32#usize) (pair : MerklePair)
    (h : step_merkle_pair_order idx level node sibling = .ok (some pair)) :
    level.val < 64 ∧
    pair.tag = 0#u8 ∧
    Qsag.encodeMultiFrame [pair.left.val.map (fun b => UInt8.ofNat b.val),
                           pair.right.val.map (fun b => UInt8.ofNat b.val)] =
      Qsag.encodeMultiFrame
        (if (idx.val / 2 ^ level.val) % 2 = 0
         then [node.val.map (fun b => UInt8.ofNat b.val),
               sibling.val.map (fun b => UInt8.ofNat b.val)]
         else [sibling.val.map (fun b => UInt8.ofNat b.val),
               node.val.map (fun b => UInt8.ofNat b.val)]) := by sorry

theorem checked_quorum_sum_sound_qsag
    (counts minimums : Slice U64) (minimum_global total : U64) :
    checked_quorum_sum counts minimums minimum_global = .ok (some total) ↔
      (counts.val ≠ [] ∧
       counts.val.length = minimums.val.length ∧
       0 < minimum_global.val ∧
       (∀ i (hi : i < counts.val.length) (hmi : i < minimums.val.length),
         0 < (minimums.val[i]'hmi).val ∧ (minimums.val[i]'hmi).val ≤ (counts.val[i]'hi).val) ∧
       total.val = (counts.val.map UScalar.val).sum ∧
       minimum_global.val ≤ total.val ∧
       (counts.val.map UScalar.val).sum < 2 ^ 64) := by sorry

theorem tooth_canonical_cwyz_fold_rejects_wrong_twiddle_and_forged_claim :
    let x := Qsag.Goldilocks.ofNat 3
    let v0 := canonicalExt4 Qsag.Aggregation.GoldilocksExt4.one
    let v1 := canonicalExt4 Qsag.Aggregation.GoldilocksExt4.zero
    let honest := Qsag.Exec.hemAffineDuetFold
      Qsag.Aggregation.GoldilocksExt4.one Qsag.Aggregation.GoldilocksExt4.zero
      x Qsag.Aggregation.GoldilocksExt4.zero
      Qsag.Aggregation.GoldilocksExt4.zero Qsag.Aggregation.GoldilocksExt4.zero
    let forged := Qsag.Aggregation.GoldilocksExt4.add honest Qsag.Aggregation.GoldilocksExt4.one
    let iyGood := canonicalFieldWord (Qsag.Goldilocks.mul
      (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)) (Qsag.Goldilocks.inv x))
    let iyBad := canonicalFieldWord (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2))
    let it := canonicalFieldWord (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2))
    let yy := canonicalFieldWord (Qsag.Goldilocks.mul x x)
    verify_cwyz_duet_fold_step v0 v1 iyGood it yy extZero extZero extZero
      (canonicalExt4 honest) = .ok true ∧
    verify_cwyz_duet_fold_step v0 v1 iyGood it yy extZero extZero extZero
      (canonicalExt4 forged) = .ok false ∧
    verify_cwyz_duet_fold_step v0 v1 iyBad it yy extZero extZero extZero
      (canonicalExt4 honest) = .ok false := by sorry
end qsag_whir_verified.proofs
end
