module
public import Aeneas
public import QsagWhirVerified.Types
public import QsagWhirVerified.Funs
public import QsagWhirVerifiedChallengeDefs

public section

/-!
# Independent Challenge Statement Module for Quintic `Fp5` WHIR Rust MIR Refinement Theorems

Pins the exact theorem statements for the generated `qsag-whir-verified` Rust MIR model
(`QsagWhirVerified.Types` and `QsagWhirVerified.Funs`, 54 definitions) without importing any
proof module (`Arithmetic`, `Proofs`, `Canonical`, or `ProtocolWeld`). `lake comparator --paranoid`
replays `QsagWhirVerified` against these independent obligations across all six external kernels.

Every theorem body below is `sorry`, following the comparator challenge convention.
-/

open Aeneas Aeneas.Std
namespace qsag_whir_verified.proofs
set_option maxRecDepth 4096

/-! ## 1. Constants, Base Goldilocks & Quintic `Fp5` Ring/Frobenius Refinements -/

theorem goldilocks_p_val : GOLDILOCKS_P.val = 18446744069414584321 := sorry

theorem max_u64_word_val : MAX_U64_WORD.val = 18446744073709551615 := sorry

theorem fp5_nonresidue_w_val : FP5_NONRESIDUE_W = 3#u64 := sorry

theorem frobenius_zeta5_1_val : FROBENIUS_ZETA5_1 = 1041288259238279555#u64 := sorry

theorem frobenius_zeta5_2_val : FROBENIUS_ZETA5_2 = 15820824984080659046#u64 := sorry

theorem frobenius_zeta5_3_val : FROBENIUS_ZETA5_3 = 211587555138949697#u64 := sorry

theorem frobenius_zeta5_4_val : FROBENIUS_ZETA5_4 = 1373043270956696022#u64 := sorry

theorem qsaghqm2_profile_turbo400_val : QSAGHQM2_PROFILE_TURBO400 = 1#u8 := sorry

theorem qsaghqm2_profile_gl24_val : QSAGHQM2_PROFILE_GL24 = 2#u8 := sorry

theorem min_quintic_log_cells_val : MIN_QUINTIC_LOG_CELLS = 16#u32 := sorry

theorem max_quintic_log_cells_val : MAX_QUINTIC_LOG_CELLS = 28#u32 := sorry

theorem max_canopy_log_leaves_val : MAX_CANOPY_LOG_LEAVES = 28#u32 := sorry

theorem copy_fp5_spec (x : Fp5) : copy_fp5 x = .ok x := sorry

theorem zeta5_powers_spec :
    fieldMul FROBENIUS_ZETA5_1 FROBENIUS_ZETA5_1 = FROBENIUS_ZETA5_2 ∧
    fieldMul FROBENIUS_ZETA5_2 FROBENIUS_ZETA5_1 = FROBENIUS_ZETA5_3 ∧
    fieldMul FROBENIUS_ZETA5_3 FROBENIUS_ZETA5_1 = FROBENIUS_ZETA5_4 ∧
    fieldMul FROBENIUS_ZETA5_4 FROBENIUS_ZETA5_1 = 1#u64 := sorry

theorem add_refines (a b : U64) : add a b = .ok (fieldAdd a b) := sorry

theorem sub_refines (a b : U64) : sub a b = .ok (fieldSub a b) := sorry

theorem mul_refines (a b : U64) : mul a b = .ok (fieldMul a b) := sorry

theorem fp5_zero_refines : fp5_zero = .ok fp5Zero := sorry

theorem fp5_one_refines : fp5_one = .ok fp5One := sorry

theorem fp5_from_base_refines (x : U64) : fp5_from_base x = .ok (fp5FromBase x) := sorry

theorem fp5_add_refines (x y : Fp5) : fp5_add x y = .ok (fp5Add x y) := sorry

theorem fp5_sub_refines (x y : Fp5) : fp5_sub x y = .ok (fp5Sub x y) := sorry

theorem fp5_neg_refines (x : Fp5) : fp5_neg x = .ok (fp5Neg x) := sorry

theorem fp5_scale_refines (x : Fp5) (s : U64) : fp5_scale x s = .ok (fp5Scale x s) := sorry

theorem fp5_mul_refines (x y : Fp5) : fp5_mul x y = .ok (fp5Mul x y) := sorry

theorem fp5_frobenius_refines (x : Fp5) : fp5_frobenius x = .ok (fp5Frob x) := sorry

theorem fp5Frob_pow5_id {x : Fp5} (hx : IsCanonicalFp5 x) :
    fp5Frob (fp5Frob (fp5Frob (fp5Frob (fp5Frob x)))) = x := sorry

theorem affine_combine_fp5_refines (even odd alpha : Fp5) :
    affine_combine_fp5 even odd alpha = .ok (fp5Add odd (fp5Mul alpha even)) := sorry

/-! ## 2. Little-Endian Loaders & Canonical Wire Decoders (`Fp5` & `Gl24Digest`) -/

theorem load_le_u64_40_spec (bytes : Array U8 40#usize) (off : Usize) :
    load_le_u64_40 bytes off =
      .ok (if 32 < off.val then 0#u64 else lePackU64At bytes.val off.val) := sorry

theorem load_le_u64_56_spec (bytes : Array U8 56#usize) (off : Usize) :
    load_le_u64_56 bytes off =
      .ok (if 48 < off.val then 0#u64 else lePackU64At bytes.val off.val) := sorry

theorem decode_canonical_u64_spec (x : U64) :
    decode_canonical_u64 x = .ok (if x.val < goldilocksMod then some x else none) := sorry

theorem decode_canonical_u64_some_iff (x y : U64) :
    decode_canonical_u64 x = .ok (some y) ↔ IsCanonical x ∧ y = x := sorry

theorem decode_canonical_u64_none_iff (x : U64) :
    decode_canonical_u64 x = .ok none ↔ goldilocksMod ≤ x.val := sorry

theorem decode_canonical_u64_rejects_noncanonical (x : U64)
    (h : GOLDILOCKS_P.val ≤ x.val) : decode_canonical_u64 x = .ok none := sorry

theorem decode_canonical_fp5_limbs_some_iff (c0 c1 c2 c3 c4 : U64) (out : Fp5) :
    decode_canonical_fp5_limbs c0 c1 c2 c3 c4 = .ok (some out) ↔
      IsCanonical c0 ∧ IsCanonical c1 ∧ IsCanonical c2 ∧ IsCanonical c3 ∧ IsCanonical c4 ∧
      out = ⟨c0, c1, c2, c3, c4⟩ := sorry

theorem decode_canonical_fp5_limbs_none_iff (c0 c1 c2 c3 c4 : U64) :
    decode_canonical_fp5_limbs c0 c1 c2 c3 c4 = .ok none ↔
      ¬ (IsCanonical c0 ∧ IsCanonical c1 ∧ IsCanonical c2 ∧ IsCanonical c3 ∧ IsCanonical c4) := sorry

theorem decode_canonical_fp5_some_iff (bytes : Array U8 40#usize) (out : Fp5) :
    decode_canonical_fp5 bytes = .ok (some out) ↔
      IsCanonicalFp5 out ∧
      out = ⟨lePackU64At bytes.val 0, lePackU64At bytes.val 8, lePackU64At bytes.val 16,
             lePackU64At bytes.val 24, lePackU64At bytes.val 32⟩ := sorry

theorem decode_canonical_fp5_none_iff (bytes : Array U8 40#usize) :
    decode_canonical_fp5 bytes = .ok none ↔
      ¬ IsCanonicalFp5
        ⟨lePackU64At bytes.val 0, lePackU64At bytes.val 8, lePackU64At bytes.val 16,
         lePackU64At bytes.val 24, lePackU64At bytes.val 32⟩ := sorry

theorem decode_canonical_gl24_limbs_some_iff (l0 l1 l2 l3 l4 l5 l6 : U64) (out : Gl24Digest) :
    decode_canonical_gl24_limbs l0 l1 l2 l3 l4 l5 l6 = .ok (some out) ↔
      IsCanonicalGl24 ⟨l0, l1, l2, l3, l4, l5, l6⟩ ∧ out = ⟨l0, l1, l2, l3, l4, l5, l6⟩ := sorry

theorem decode_canonical_gl24_limbs_none_iff (l0 l1 l2 l3 l4 l5 l6 : U64) :
    decode_canonical_gl24_limbs l0 l1 l2 l3 l4 l5 l6 = .ok none ↔
      ¬ IsCanonicalGl24 ⟨l0, l1, l2, l3, l4, l5, l6⟩ := sorry

theorem decode_canonical_gl24_digest_some_iff (bytes : Array U8 56#usize) (out : Gl24Digest) :
    decode_canonical_gl24_digest bytes = .ok (some out) ↔
      IsCanonicalGl24 out ∧
      out = ⟨lePackU64At bytes.val 0, lePackU64At bytes.val 8, lePackU64At bytes.val 16,
             lePackU64At bytes.val 24, lePackU64At bytes.val 32, lePackU64At bytes.val 40,
             lePackU64At bytes.val 48⟩ := sorry

theorem decode_canonical_gl24_digest_none_iff (bytes : Array U8 56#usize) :
    decode_canonical_gl24_digest bytes = .ok none ↔
      ¬ IsCanonicalGl24
        ⟨lePackU64At bytes.val 0, lePackU64At bytes.val 8, lePackU64At bytes.val 16,
         lePackU64At bytes.val 24, lePackU64At bytes.val 32, lePackU64At bytes.val 40,
         lePackU64At bytes.val 48⟩ := sorry

/-! ## 3. Quintic Duet Folding, CWYZ Folding, Dual Bridge, Sumcheck Wire & Horner -/

theorem fp5_eq_sound (x y : Fp5) : fp5_eq x y = .ok true ↔ x = y := sorry

theorem verify_ood_pin_eq_fp5_sound (expected supplied : Fp5) :
    verify_ood_pin_eq_fp5 expected supplied = .ok true ↔ expected = supplied := sorry

theorem verify_ood_pin_eq_fp5_false_iff (expected supplied : Fp5) :
    verify_ood_pin_eq_fp5 expected supplied = .ok false ↔ expected ≠ supplied := sorry

theorem duet_fold_fp5_coset_sound
    {even odd : Fp5} {y0 iy it : U64} (alpha : Fp5)
    (he : IsCanonicalFp5 even) (ho : IsCanonicalFp5 odd)
    (hit : fieldMul 2#u64 it = 1#u64)
    (hiy : fieldMul (fieldMul 2#u64 y0) iy = 1#u64) :
    duet_fold_fp5 (fp5Add even (fp5Scale odd y0)) (fp5Sub even (fp5Scale odd y0)) iy it alpha =
      .ok (fp5Add odd (fp5Mul alpha even)) := sorry

theorem verify_affine_duet_fold_step_fp5_coset_sound
    {even odd : Fp5} {y0 iy it : U64} (alpha claimed : Fp5)
    (he : IsCanonicalFp5 even) (ho : IsCanonicalFp5 odd)
    (hit : fieldMul 2#u64 it = 1#u64)
    (hiy : fieldMul (fieldMul 2#u64 y0) iy = 1#u64) :
    verify_affine_duet_fold_step_fp5
        (fp5Add even (fp5Scale odd y0)) (fp5Sub even (fp5Scale odd y0))
        iy it alpha claimed = .ok true ↔
      claimed = fp5Add odd (fp5Mul alpha even) := sorry

theorem cwyz_duet_fold_fp5_coset_sound
    {even odd : Fp5} {y0 iy it : U64} (theta alpha beta : Fp5)
    (he : IsCanonicalFp5 even) (ho : IsCanonicalFp5 odd)
    (hit : fieldMul 2#u64 it = 1#u64)
    (hiy : fieldMul (fieldMul 2#u64 y0) iy = 1#u64) :
    cwyz_duet_fold_fp5 (fp5Add even (fp5Scale odd y0)) (fp5Sub even (fp5Scale odd y0))
        iy it (fieldMul y0 y0) theta alpha beta =
      .ok (fp5Add odd (fp5Mul (fp5Add alpha (fp5Scale beta (fieldMul y0 y0)))
        (fp5Add even (fp5Mul theta odd)))) := sorry

theorem verify_cwyz_duet_fold_step_fp5_coset_sound
    {even odd : Fp5} {y0 iy it : U64} (theta alpha beta claimed : Fp5)
    (he : IsCanonicalFp5 even) (ho : IsCanonicalFp5 odd)
    (hit : fieldMul 2#u64 it = 1#u64)
    (hiy : fieldMul (fieldMul 2#u64 y0) iy = 1#u64) :
    verify_cwyz_duet_fold_step_fp5
        (fp5Add even (fp5Scale odd y0)) (fp5Sub even (fp5Scale odd y0))
        iy it (fieldMul y0 y0) theta alpha beta claimed = .ok true ↔
      claimed = fp5Add odd (fp5Mul (fp5Add alpha (fp5Scale beta (fieldMul y0 y0)))
                  (fp5Add even (fp5Mul theta odd))) := sorry

theorem cwyz_bridge_claim_step_fp5_dual_spec
    (a0 a1 b0 b1 kn phi theta alpha beta : Fp5) :
    cwyz_bridge_claim_step_fp5
        (fp5Mul a0 b0) (fp5Mul a0 b1) (fp5Mul a1 b0) (fp5Mul a0 kn) (fp5Mul a1 kn)
        (fp5Add (fp5Mul a0 b0) (fp5Mul a1 b1)) phi theta alpha beta =
      .ok (fp5Add
        (fp5Mul (fp5Add a1 (fp5Mul alpha (fp5Add a0 (fp5Mul theta a1)))) (fp5Add b0 (fp5Mul phi b1)))
        (fp5Mul (fp5Mul beta (fp5Add a0 (fp5Mul theta a1))) kn)) := sorry

theorem verify_cwyz_bridge_claim_step_fp5_dual_sound
    (a0 a1 b0 b1 kn phi theta alpha beta claimed_next : Fp5) :
    verify_cwyz_bridge_claim_step_fp5
        (fp5Mul a0 b0) (fp5Mul a0 b1) (fp5Mul a1 b0) (fp5Mul a0 kn) (fp5Mul a1 kn)
        (fp5Add (fp5Mul a0 b0) (fp5Mul a1 b1)) phi theta alpha beta claimed_next = .ok true ↔
      claimed_next = fp5Add
        (fp5Mul (fp5Add a1 (fp5Mul alpha (fp5Add a0 (fp5Mul theta a1)))) (fp5Add b0 (fp5Mul phi b1)))
        (fp5Mul (fp5Mul beta (fp5Add a0 (fp5Mul theta a1))) kn) := sorry

theorem eval_quadratic_sumcheck_wire_fp5_hypercube_spec
    (c0 c2 sum_claim : Fp5) (hs : IsCanonicalFp5 sum_claim) :
    ∃ y0 y1,
      eval_quadratic_sumcheck_wire_fp5 c0 c2 sum_claim fp5Zero = .ok y0 ∧
      eval_quadratic_sumcheck_wire_fp5 c0 c2 sum_claim fp5One = .ok y1 ∧
      fp5Add y0 y1 = sum_claim := sorry

theorem eval_fp5_univariate_at_base_spec (coeffs : Slice Fp5) (z : U64) :
    eval_fp5_univariate_at_base coeffs z = .ok (hornerSpec coeffs.val z fp5Zero) := sorry

theorem eval_fp5_univariate_at_base_ascending_sound (coeffs : Slice Fp5) (z : U64)
    (hcan : ∀ c ∈ coeffs.val, IsCanonicalFp5 c) :
    eval_fp5_univariate_at_base coeffs z = .ok (evalPolyAscending coeffs.val z) := sorry

theorem verify_fp5_univariate_at_base_pin_sound
    (coeffs : Slice Fp5) (z : U64) (expected : Fp5) :
    verify_fp5_univariate_at_base_pin coeffs z expected = .ok true ↔
      expected = hornerSpec coeffs.val z fp5Zero := sorry

theorem verify_fp5_univariate_at_base_pin_ascending_sound
    (coeffs : Slice Fp5) (z : U64) (expected : Fp5)
    (hcan : ∀ c ∈ coeffs.val, IsCanonicalFp5 c) :
    verify_fp5_univariate_at_base_pin coeffs z expected = .ok true ↔
      expected = evalPolyAscending coeffs.val z := sorry

/-! ## 4. Query Reduction, Canopy Merkle (`400`-bit & `Gl24`), Quorum Sum & Envelope Gates -/

theorem canonical_query_group_idx_some_iff (raw groups idx : U64) :
    canonical_query_group_idx raw groups = .ok (some idx) ↔
      0 < groups.val ∧ idx.val = raw.val % groups.val := sorry

theorem canonical_query_group_idx_none_iff (raw groups : U64) :
    canonical_query_group_idx raw groups = .ok none ↔ groups = 0#u64 := sorry

theorem canonical_query_group_idx_lt_groups (raw groups idx : U64)
    (h : canonical_query_group_idx raw groups = .ok (some idx)) : idx.val < groups.val := sorry

theorem step_merkle_pair_order_400_some_iff
    (idx : U64) (level : U32) (node sibling : Array U8 50#usize) (pair : MerklePair400) :
    step_merkle_pair_order_400 idx level node sibling = .ok (some pair) ↔
      level.val < 64 ∧
      (if (idx.val >>> level.val) % 2 = 0
       then pair.left = node ∧ pair.right = sibling
       else pair.left = sibling ∧ pair.right = node) := sorry

theorem step_merkle_pair_order_400_none_iff
    (idx : U64) (level : U32) (node sibling : Array U8 50#usize) :
    step_merkle_pair_order_400 idx level node sibling = .ok none ↔ 64 ≤ level.val := sorry

theorem step_merkle_pair_order_gl24_some_iff
    (idx : U64) (level : U32) (node sibling : Gl24Digest) (pair : MerklePairGl24) :
    step_merkle_pair_order_gl24 idx level node sibling = .ok (some pair) ↔
      level.val < 64 ∧ IsCanonicalGl24 node ∧ IsCanonicalGl24 sibling ∧
      (if (idx.val >>> level.val) % 2 = 0
       then pair.left = node ∧ pair.right = sibling
       else pair.left = sibling ∧ pair.right = node) := sorry

theorem step_merkle_pair_order_gl24_none_iff
    (idx : U64) (level : U32) (node sibling : Gl24Digest) :
    step_merkle_pair_order_gl24 idx level node sibling = .ok none ↔
      64 ≤ level.val ∨ ¬ (IsCanonicalGl24 node ∧ IsCanonicalGl24 sibling) := sorry

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

theorem verify_qsaghqm2_header_some_iff
    (magic : Array U8 8#usize) (profile_tag : U8)
    (active_signers num_validators declared_payload_len actual_payload_len : U64)
    (hdr : Qsaghqm2Header) :
    verify_qsaghqm2_header magic profile_tag active_signers num_validators
      declared_payload_len actual_payload_len = .ok (some hdr) ↔
      Qsaghqm2HeaderSpec magic.val profile_tag active_signers num_validators
        declared_payload_len actual_payload_len ∧
      hdr = { profile_tag, active_signers, payload_len := declared_payload_len } := sorry

theorem verify_qsaghqm2_header_none_iff
    (magic : Array U8 8#usize) (profile_tag : U8)
    (active_signers num_validators declared_payload_len actual_payload_len : U64) :
    verify_qsaghqm2_header magic profile_tag active_signers num_validators
      declared_payload_len actual_payload_len = .ok none ↔
      ¬ Qsaghqm2HeaderSpec magic.val profile_tag active_signers num_validators
          declared_payload_len actual_payload_len := sorry

theorem verify_quintic_schedule_envelope_sound
    (log_cells early_stop_vars folded_vars_sum num_stages : U32) :
    verify_quintic_schedule_envelope log_cells early_stop_vars folded_vars_sum num_stages = .ok true ↔
      QuinticScheduleEnvelopeSpec log_cells early_stop_vars folded_vars_sum num_stages := sorry

theorem verify_quintic_schedule_envelope_le_max_canopy
    (log_cells early_stop_vars folded_vars_sum num_stages : U32)
    (h : verify_quintic_schedule_envelope log_cells early_stop_vars folded_vars_sum num_stages = .ok true) :
    folded_vars_sum.val < MAX_CANOPY_LOG_LEAVES.val := sorry

/-! ## 5. Canonical `Qsag` Welds & `#tooth` Mutation-Sensitivity Witnesses -/

@[expose] def fieldAbs (x : U64) : Qsag.Goldilocks := Qsag.Goldilocks.ofNat x.val

@[expose] def fp5Abs (x : Fp5) : Qsag.QuinticGoldilocks :=
  ⟨fieldAbs x.c0, fieldAbs x.c1, fieldAbs x.c2, fieldAbs x.c3, fieldAbs x.c4⟩

@[expose] def gl24Abs (d : Gl24Digest) : Qsag.Poseidon2Gl24.Digest7 :=
  ⟨fieldAbs d.l0, fieldAbs d.l1, fieldAbs d.l2, fieldAbs d.l3,
   fieldAbs d.l4, fieldAbs d.l5, fieldAbs d.l6⟩

@[expose] def canonicalFieldWord (x : Qsag.Goldilocks) : U64 := ⟨BitVec.ofNat 64 x.val⟩

@[expose] def canonicalFp5 (z : Qsag.QuinticGoldilocks) : Fp5 :=
  ⟨canonicalFieldWord z.c0, canonicalFieldWord z.c1, canonicalFieldWord z.c2,
   canonicalFieldWord z.c3, canonicalFieldWord z.c4⟩

@[expose] def canonicalGl24 (d : Qsag.Poseidon2Gl24.Digest7) : Gl24Digest :=
  ⟨canonicalFieldWord d.d0, canonicalFieldWord d.d1, canonicalFieldWord d.d2,
   canonicalFieldWord d.d3, canonicalFieldWord d.d4, canonicalFieldWord d.d5,
   canonicalFieldWord d.d6⟩

@[expose] def fp5Inv (x : Fp5) : Fp5 :=
  canonicalFp5 (Qsag.LawfulField.inv (fp5Abs x))

@[expose] def hemDuetFoldFp5 (v0 v1 : Qsag.QuinticGoldilocks) (iy it : Qsag.Goldilocks)
    (alpha : Qsag.QuinticGoldilocks) : Qsag.QuinticGoldilocks :=
  let even := Qsag.QuinticGoldilocks.mul (Qsag.QuinticGoldilocks.add v0 v1)
    (Qsag.QuinticGoldilocks.ofBase it)
  let odd := Qsag.QuinticGoldilocks.mul (Qsag.QuinticGoldilocks.sub v0 v1)
    (Qsag.QuinticGoldilocks.ofBase iy)
  Qsag.QuinticGoldilocks.add odd (Qsag.QuinticGoldilocks.mul alpha even)

@[expose] def canonicalQuadraticWireFp5Poly (c0 c2 claim : Qsag.QuinticGoldilocks) :
    List Qsag.QuinticGoldilocks :=
  [c0, Qsag.QuinticGoldilocks.sub
         (Qsag.QuinticGoldilocks.sub claim (Qsag.QuinticGoldilocks.add c0 c0))
         c2, c2]

@[expose] def decodePublicHemProfileTag (tag : U8) : Option Qsag.Aggregation.PublicHemQuintic128 :=
  if tag = QSAGHQM2_PROFILE_TURBO400 then some .turboShake400
  else if tag = QSAGHQM2_PROFILE_GL24 then some .poseidon2Gl24
  else none

theorem fieldAbs_add (x y : U64) :
    fieldAbs (fieldAdd x y) = Qsag.Goldilocks.add (fieldAbs x) (fieldAbs y) := sorry

theorem fieldAbs_mul (x y : U64) :
    fieldAbs (fieldMul x y) = Qsag.Goldilocks.mul (fieldAbs x) (fieldAbs y) := sorry

theorem fieldAbs_sub (x y : U64) :
    fieldAbs (fieldSub x y) = Qsag.Goldilocks.sub (fieldAbs x) (fieldAbs y) := sorry

theorem fp5Abs_add (x y : Fp5) :
    fp5Abs (fp5Add x y) = Qsag.QuinticGoldilocks.add (fp5Abs x) (fp5Abs y) := sorry

theorem fp5Abs_sub (x y : Fp5) :
    fp5Abs (fp5Sub x y) = Qsag.QuinticGoldilocks.sub (fp5Abs x) (fp5Abs y) := sorry

theorem fp5Abs_mul (x y : Fp5) :
    fp5Abs (fp5Mul x y) = Qsag.QuinticGoldilocks.mul (fp5Abs x) (fp5Abs y) := sorry

theorem fp5Abs_frob (x : Fp5) :
    fp5Abs (fp5Frob x) = Qsag.QuinticGoldilocks.frob (fp5Abs x) := sorry

theorem fp5Abs_canonicalFp5 (z : Qsag.QuinticGoldilocks) :
    fp5Abs (canonicalFp5 z) = z := sorry

theorem gl24Abs_canonicalGl24 (d : Qsag.Poseidon2Gl24.Digest7) :
    gl24Abs (canonicalGl24 d) = d := sorry

theorem fp5_mul_fp5Inv_ok_one {x : Fp5}
    (hz : fp5Abs x ≠ Qsag.QuinticGoldilocks.zero) :
    fp5_mul x (fp5Inv x) = .ok fp5One := sorry

theorem cwyz_duet_fold_fp5_refines_hemVirtualFoldOracle
    (v0 v1 : Fp5) (x : Qsag.Goldilocks) (theta alpha beta : Fp5)
    (curDom foldDom : List Qsag.QuinticGoldilocks)
    (curOracle : Nat → Qsag.QuinticGoldilocks) (idx : Nat)
    (hx : curDom.getD (2 * idx) Qsag.CommRingOps.one = Qsag.QuinticGoldilocks.ofBase x)
    (hy : foldDom.getD idx Qsag.CommRingOps.zero =
      Qsag.QuinticGoldilocks.ofBase (Qsag.Goldilocks.mul x x))
    (ha : curOracle (2 * idx) = fp5Abs v0)
    (hb : curOracle (2 * idx + 1) = fp5Abs v1) :
    (fp5Abs <$> cwyz_duet_fold_fp5 v0 v1
      (canonicalFieldWord (Qsag.Goldilocks.mul
        (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)) (Qsag.Goldilocks.inv x)))
      (canonicalFieldWord (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)))
      (canonicalFieldWord (Qsag.Goldilocks.mul x x)) theta alpha beta) =
      .ok (Qsag.hemVirtualFoldOracle
        (fp5Abs theta) (fp5Abs alpha) (fp5Abs beta) curDom foldDom curOracle idx) := sorry

theorem verify_cwyz_duet_fold_step_fp5_sound_qsag
    (v0 v1 : Fp5) (x : Qsag.Goldilocks) (theta alpha beta claimed : Fp5)
    (curDom foldDom : List Qsag.QuinticGoldilocks)
    (curOracle : Nat → Qsag.QuinticGoldilocks) (idx : Nat)
    (hx : curDom.getD (2 * idx) Qsag.CommRingOps.one = Qsag.QuinticGoldilocks.ofBase x)
    (hy : foldDom.getD idx Qsag.CommRingOps.zero =
      Qsag.QuinticGoldilocks.ofBase (Qsag.Goldilocks.mul x x))
    (ha : curOracle (2 * idx) = fp5Abs v0)
    (hb : curOracle (2 * idx + 1) = fp5Abs v1) :
    verify_cwyz_duet_fold_step_fp5 v0 v1
      (canonicalFieldWord (Qsag.Goldilocks.mul
        (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)) (Qsag.Goldilocks.inv x)))
      (canonicalFieldWord (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)))
      (canonicalFieldWord (Qsag.Goldilocks.mul x x))
      theta alpha beta claimed = .ok true ↔
      (IsCanonicalFp5 claimed ∧
       fp5Abs claimed = Qsag.hemVirtualFoldOracle
         (fp5Abs theta) (fp5Abs alpha) (fp5Abs beta) curDom foldDom curOracle idx) := sorry

theorem verify_affine_duet_fold_step_fp5_roots_le_one
    (v0 v1 claimed : Fp5) (iy it : U64)
    (S : List Qsag.QuinticGoldilocks) (hS : S.Nodup)
    (hne : ∃ r : Qsag.QuinticGoldilocks,
      hemDuetFoldFp5 (fp5Abs v0) (fp5Abs v1) (fieldAbs iy) (fieldAbs it) r ≠ fp5Abs claimed) :
    (S.filter (fun r => decide
      (verify_affine_duet_fold_step_fp5 v0 v1 iy it (canonicalFp5 r) claimed = .ok true))).length ≤ 1 := sorry

theorem verify_cwyz_bridge_claim_step_fp5_sound_qsag
    (w0 w1 w2 w3 w4 claim phi theta alpha beta claimed_next : Fp5) :
    verify_cwyz_bridge_claim_step_fp5 w0 w1 w2 w3 w4 claim phi theta alpha beta claimed_next = .ok true ↔
      (IsCanonicalFp5 claimed_next ∧
       fp5Abs claimed_next = Qsag.hemBridgeFoldClaim
         (fp5Abs claim) (fp5Abs w0) (fp5Abs w1) (fp5Abs w2) (fp5Abs w3) (fp5Abs w4)
         (fp5Abs phi) (fp5Abs theta) (fp5Abs alpha) (fp5Abs beta)) := sorry

theorem eval_quadratic_sumcheck_wire_fp5_bad_challenges_le_two
    (G S : List Qsag.QuinticGoldilocks) (c0 c2 sum_claim : Fp5)
    (hS : S.Nodup) (hG : G.length ≤ 3)
    (hFalse : fp5Abs sum_claim ≠ Qsag.CommRingOps.add
      (Qsag.RoundPoly.evalCoeffs G Qsag.CommRingOps.zero)
      (Qsag.RoundPoly.evalCoeffs G Qsag.CommRingOps.one)) :
    (S.filter (fun r => decide
      ((fp5Abs <$> eval_quadratic_sumcheck_wire_fp5 c0 c2 sum_claim (canonicalFp5 r)) =
        .ok (Qsag.RoundPoly.evalCoeffs G r)))).length ≤ 2 := sorry

theorem eval_fp5_univariate_at_base_refines_evalCoeffs (coeffs : Slice Fp5) (z : U64) :
    (fp5Abs <$> eval_fp5_univariate_at_base coeffs z) =
      .ok (Qsag.RoundPoly.evalCoeffs (coeffs.val.map fp5Abs)
        (Qsag.QuinticGoldilocks.ofBase (fieldAbs z))) := sorry

theorem verify_fp5_univariate_at_base_pin_roots_le_degree
    (d : Nat) (candA candB : Slice Fp5) (S : List Qsag.Goldilocks)
    (hNodup : S.Nodup)
    (hLenA : candA.val.length ≤ d + 1) (hLenB : candB.val.length ≤ d + 1)
    (hDiff : ∃ z₀ : Qsag.QuinticGoldilocks,
      Qsag.RoundPoly.evalCoeffs (candA.val.map fp5Abs) z₀ ≠
        Qsag.RoundPoly.evalCoeffs (candB.val.map fp5Abs) z₀) :
    (S.filter (fun z =>
      let pinA := canonicalFp5 (Qsag.RoundPoly.evalCoeffs (candA.val.map fp5Abs)
        (Qsag.QuinticGoldilocks.ofBase z))
      decide (verify_fp5_univariate_at_base_pin candB (canonicalFieldWord z) pinA = .ok true))).length ≤ d := sorry

theorem step_merkle_pair_order_400_canonical_parity
    (idx : U64) (level : U32) (node sibling : Array U8 50#usize) (pair : MerklePair400)
    (h : step_merkle_pair_order_400 idx level node sibling = .ok (some pair)) :
    level.val < 64 ∧
    0 < Qsag.Aggregation.publicHemDigestCard .turboShake400 ∧
    8 * node.val.length = 400 ∧
    Qsag.encodeMultiFrame [pair.left.val.map (fun b => UInt8.ofNat b.val),
                           pair.right.val.map (fun b => UInt8.ofNat b.val)] =
      Qsag.Aggregation.merkleNodeFrame (idx.val / 2 ^ level.val)
        (node.val.map (fun b => UInt8.ofNat b.val))
        (sibling.val.map (fun b => UInt8.ofNat b.val)) := sorry

theorem step_merkle_pair_order_gl24_refines_poseidon2Gl24
    (idx : U64) (level : U32) (node sibling : Gl24Digest) (pair : MerklePairGl24)
    (tweak0 tweak1 : Qsag.Goldilocks)
    (h : step_merkle_pair_order_gl24 idx level node sibling = .ok (some pair)) :
    level.val < 64 ∧ IsCanonicalGl24 node ∧ IsCanonicalGl24 sibling ∧
    Qsag.Poseidon2Gl24.poseidon2Gl24CompressMerkle (gl24Abs pair.left) (gl24Abs pair.right)
      tweak0 tweak1 =
      (if (idx.val / 2 ^ level.val) % 2 = 0
       then Qsag.Poseidon2Gl24.poseidon2Gl24CompressMerkle (gl24Abs node) (gl24Abs sibling) tweak0 tweak1
       else Qsag.Poseidon2Gl24.poseidon2Gl24CompressMerkle (gl24Abs sibling) (gl24Abs node) tweak0 tweak1) := sorry

theorem verify_qsaghqm2_header_refines_qsag
    (magic : Array U8 8#usize) (profile_tag : U8)
    (active_signers num_validators declared_payload_len actual_payload_len : U64)
    (hdr : Qsaghqm2Header) :
    verify_qsaghqm2_header magic profile_tag active_signers num_validators
      declared_payload_len actual_payload_len = .ok (some hdr) →
      ∃ prof : Qsag.Aggregation.PublicHemQuintic128,
        decodePublicHemProfileTag hdr.profile_tag = some prof ∧
        0 < Qsag.Aggregation.publicHemDigestCard prof ∧
        (prof = .turboShake400 ↔ hdr.profile_tag = QSAGHQM2_PROFILE_TURBO400) ∧
        (prof = .poseidon2Gl24 ↔ hdr.profile_tag = QSAGHQM2_PROFILE_GL24) ∧
        0 < hdr.active_signers.val ∧ hdr.active_signers.val ≤ num_validators.val ∧
        0 < hdr.payload_len.val ∧ hdr.payload_len = actual_payload_len := sorry

theorem verify_quintic_schedule_envelope_accepts_zkHemV2ProdStages
    (n : Nat) (hLo : MIN_QUINTIC_LOG_CELLS.val ≤ n) (hHi : n ≤ MAX_QUINTIC_LOG_CELLS.val) :
    let stages := Qsag.ZkHemV2Cert.zkHemV2ProdStages n
    let folded := (stages.map Qsag.ClosedWhir.WhirStage.foldK).sum
    folded < MAX_CANOPY_LOG_LEAVES.val ∧
    verify_quintic_schedule_envelope
      (UScalar.ofNat .U32 n)
      (UScalar.ofNat .U32 (n - folded))
      (UScalar.ofNat .U32 folded)
      (UScalar.ofNat .U32 stages.length) = .ok true := sorry

theorem tooth_unchecked_mod_p_accepts_aliased_field_limb :
    (0#u64) ≠ GOLDILOCKS_P ∧
    (0#u64 % GOLDILOCKS_P : Result U64) = .ok 0#u64 ∧
    (GOLDILOCKS_P % GOLDILOCKS_P : Result U64) = .ok 0#u64 ∧
    decode_canonical_u64 GOLDILOCKS_P = .ok none := sorry

theorem tooth_decode_canonical_fp5_rejects_fifth_limb_alias :
    decode_canonical_fp5_limbs 1#u64 2#u64 3#u64 4#u64 GOLDILOCKS_P = .ok none ∧
    decode_canonical_fp5_limbs 1#u64 2#u64 3#u64 4#u64 5#u64 =
      .ok (some ⟨1#u64, 2#u64, 3#u64, 4#u64, 5#u64⟩) ∧
    decode_canonical_fp5 (Array.repeat 40#usize 0xFF#u8) = .ok none ∧
    decode_canonical_fp5 (Array.repeat 40#usize 0#u8) = .ok (some fp5Zero) := sorry

theorem tooth_decode_canonical_gl24_rejects_seventh_limb_alias :
    decode_canonical_gl24_limbs 1#u64 2#u64 3#u64 4#u64 5#u64 6#u64 GOLDILOCKS_P = .ok none ∧
    decode_canonical_gl24_limbs 1#u64 2#u64 3#u64 4#u64 5#u64 6#u64 7#u64 =
      .ok (some ⟨1#u64, 2#u64, 3#u64, 4#u64, 5#u64, 6#u64, 7#u64⟩) ∧
    decode_canonical_gl24_digest (Array.repeat 56#usize 0xFF#u8) = .ok none := sorry

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
    step_merkle_pair_order_gl24 0#u64 0#u32 g0 gBad = .ok none := sorry

theorem tooth_checked_quorum_sum_rejects_u64_wraparound_forgery :
    let overflow_counts : Slice U64 := Array.to_slice (Array.make 2#usize [MAX_U64_WORD, 5#u64])
    let overflow_mins : Slice U64 := Array.to_slice (Array.make 2#usize [1#u64, 1#u64])
    let honest_counts : Slice U64 := Array.to_slice (Array.make 2#usize [10#u64, 15#u64])
    let honest_mins : Slice U64 := Array.to_slice (Array.make 2#usize [8#u64, 12#u64])
    checked_quorum_sum overflow_counts overflow_mins 4#u64 = .ok none ∧
    checked_quorum_sum honest_counts honest_mins 20#u64 = .ok (some 25#u64) := sorry

theorem tooth_ood_pin_fp5_rejects_perturbation :
    let p1 : Fp5 := ⟨1#u64, 2#u64, 3#u64, 4#u64, 5#u64⟩
    let p2 : Fp5 := ⟨1#u64, 2#u64, 3#u64, 4#u64, 6#u64⟩
    verify_ood_pin_eq_fp5 p1 p2 = .ok false ∧
    verify_ood_pin_eq_fp5 p1 p1 = .ok true := sorry

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
    verify_cwyz_duet_fold_step_fp5 v0 v1 iy it yy theta alpha beta cwyz_forged = .ok false := sorry

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
    verify_cwyz_bridge_claim_step_fp5 w0 w1 w2 w3 w4 claim phi theta alpha beta forged = .ok false := sorry

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
      .ok ⟨41#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩ := sorry

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
    verify_quintic_schedule_envelope 15#u32 5#u32 10#u32 3#u32 = .ok false := sorry

theorem tooth_canonical_cwyz_fp5_fold_rejects_wrong_twiddle_and_forged_claim :
    let x := Qsag.Goldilocks.ofNat 3
    let v0 := canonicalFp5 Qsag.QuinticGoldilocks.one
    let v1 := canonicalFp5 Qsag.QuinticGoldilocks.zero
    let curDom := [Qsag.QuinticGoldilocks.ofBase x]
    let foldDom := [Qsag.QuinticGoldilocks.ofBase (Qsag.Goldilocks.mul x x)]
    let curO : Nat → Qsag.QuinticGoldilocks :=
      fun i => if i = 0 then Qsag.QuinticGoldilocks.one else Qsag.QuinticGoldilocks.zero
    let honest := Qsag.hemVirtualFoldOracle
      Qsag.QuinticGoldilocks.zero Qsag.QuinticGoldilocks.zero Qsag.QuinticGoldilocks.zero
      curDom foldDom curO 0
    let forged := Qsag.QuinticGoldilocks.add honest Qsag.QuinticGoldilocks.one
    let iyGood := canonicalFieldWord (Qsag.Goldilocks.mul
      (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)) (Qsag.Goldilocks.inv x))
    let iyBad := canonicalFieldWord (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2))
    let it := canonicalFieldWord (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2))
    let yy := canonicalFieldWord (Qsag.Goldilocks.mul x x)
    verify_cwyz_duet_fold_step_fp5 v0 v1 iyGood it yy fp5Zero fp5Zero fp5Zero
      (canonicalFp5 honest) = .ok true ∧
    verify_cwyz_duet_fold_step_fp5 v0 v1 iyGood it yy fp5Zero fp5Zero fp5Zero
      (canonicalFp5 forged) = .ok false ∧
    verify_cwyz_duet_fold_step_fp5 v0 v1 iyBad it yy fp5Zero fp5Zero fp5Zero
      (canonicalFp5 honest) = .ok false := sorry

end qsag_whir_verified.proofs
end
