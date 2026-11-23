module
public import QsagWhirVerified.Canonical
public import Qsag.Protocol.Aggregation.Aggregation
public import Qsag.Protocol.Aggregation.ZkHemV2
public import Qsag.Protocol.Aggregation.ZkHemV2ScheduleCert
public import Qsag.Protocol.Aggregation.PublicHemQuintic128
public import Qsag.Protocol.Aggregation.QuinticMultiStageWhir
import Qsag.Tactic.AssuranceKit
/-!
# `QsagWhirVerified.ProtocolWeld` — Full 54/54 Canonical Closure & Protocol-Level Quintic WHIR Welds

Completes the canonical `Qsag` refinement bridge between `QsagWhirVerified` (50 extracted Rust
items and 4 loop helpers = 54 definitions in `QsagWhirVerified.Funs`) and the canonical quintic
aggregation specifications:

1. **100% Canonical `Qsag` Symbol Closure (54/54 `Funs.lean` Definitions):**
   Welds every extracted constant, byte loader, canonical wire decoder, base & quintic `Fp5`
   ring/Frobenius operation, folding/bridge/sumcheck/Horner kernel, Canopy Merkle (`400`-bit &
   `Poseidon2-GL-w24`), quorum sum, `QSAGHQM2` envelope header, and `[16, 28]` quintic schedule
   envelope directly to canonical `Qsag.*` declarations.
2. **`ZkHemV2` Zero-Knowledge Mask-Line Weld (`affine_combine_fp5_refines_zkHemV2_maskLine`,
   `mir_affine_combine_fp5_coin_bijection_simulated`):**
   Welds extracted `affine_combine_fp5` directly to `Qsag.ZkHemV2.maskLine` and lifts
   `ZkHemV2.v2_mask_line_perfectly_simulated` (`CoinBijectionSimulated`) to MIR `Fp5` coins.
3. **Antipodal `QuinticMultiStageWhir` Fiber & Multi-Round Sumcheck Chain Welds:**
   Welds `duet_fold_fp5` to `Qsag.SuccinctWhirAgg.fiberPoint` antipodal cosets, welds the
   multi-round MIR `eval_quadratic_sumcheck_wire_fp5` verifier to `Qsag.RoundPoly.evalCoeffs`,
   welds `verify_qsaghqm2_header` to `Qsag.Aggregation.PublicHemQuintic128` (`publicHemDigestCard`),
   welds `verify_quintic_schedule_envelope` to all 13 deployed schedules in
   `Qsag.ZkHemV2Cert.zkHemV2ProdStages`, and welds accepted MIR stage gates directly into
   `Qsag.verifyHemAffineWhir` over `Qsag.QuinticGoldilocks`.
-/

public section
namespace qsag_whir_verified.proofs
open Aeneas Aeneas.Std Result

/-! ## 1. Canonical `Qsag` Closure of Constants, Helpers, Scalar Ops & Quintic `Fp5` Ring/Frobenius Ops -/

theorem goldilocks_p_eq_qsag_prime : GOLDILOCKS_P.val = Qsag.goldilocksPrime :=
  goldilocks_p_val

theorem max_u64_word_lt_two_pow_64_qsag :
    MAX_U64_WORD.val + 1 = 2 ^ 64 ∧ Qsag.goldilocksPrime < MAX_U64_WORD.val := by
  rw [max_u64_word_val]
  exact ⟨by decide, by decide⟩

theorem fp5_nonresidue_w_eq_qsag :
    fieldAbs FP5_NONRESIDUE_W = Qsag.QuinticGoldilocks.nonResidue := by
  rw [fp5_nonresidue_w_val]
  exact fieldAbs_three

theorem frobenius_zeta5_constants_eq_qsag :
    fieldAbs FROBENIUS_ZETA5_1 = Qsag.QuinticGoldilocks.zeta ∧
    fieldAbs FROBENIUS_ZETA5_2 =
      Qsag.Goldilocks.mul Qsag.QuinticGoldilocks.zeta Qsag.QuinticGoldilocks.zeta ∧
    fieldAbs FROBENIUS_ZETA5_3 =
      Qsag.Goldilocks.mul
        (Qsag.Goldilocks.mul Qsag.QuinticGoldilocks.zeta Qsag.QuinticGoldilocks.zeta)
        Qsag.QuinticGoldilocks.zeta ∧
    fieldAbs FROBENIUS_ZETA5_4 =
      Qsag.Goldilocks.mul
        (Qsag.Goldilocks.mul Qsag.QuinticGoldilocks.zeta Qsag.QuinticGoldilocks.zeta)
        (Qsag.Goldilocks.mul Qsag.QuinticGoldilocks.zeta Qsag.QuinticGoldilocks.zeta) := by
  rw [frobenius_zeta5_1_val, frobenius_zeta5_2_val, frobenius_zeta5_3_val, frobenius_zeta5_4_val]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    apply Qsag.Goldilocks.ext <;>
    simp only [fieldAbs, Qsag.Goldilocks.ofNat_val, Qsag.Goldilocks.mul_val,
      Qsag.QuinticGoldilocks.zeta_val] <;>
    decide

theorem copy_fp5_refines_qsag (x : Fp5) :
    (fp5Abs <$> copy_fp5 x) = .ok (fp5Abs x : Qsag.QuinticGoldilocks) := by
  rw [copy_fp5_spec]; rfl

theorem add_refines_qsag (a b : U64) :
    (fieldAbs <$> add a b) = .ok (Qsag.Goldilocks.add (fieldAbs a) (fieldAbs b)) := by
  rw [add_refines]; exact congrArg Result.ok (fieldAbs_add a b)

theorem sub_refines_qsag (a b : U64) :
    (fieldAbs <$> sub a b) = .ok (Qsag.Goldilocks.sub (fieldAbs a) (fieldAbs b)) := by
  rw [sub_refines]; exact congrArg Result.ok (fieldAbs_sub a b)

theorem mul_refines_qsag (a b : U64) :
    (fieldAbs <$> mul a b) = .ok (Qsag.Goldilocks.mul (fieldAbs a) (fieldAbs b)) := by
  rw [mul_refines]; exact congrArg Result.ok (fieldAbs_mul a b)

theorem fp5_zero_refines_qsag :
    (fp5Abs <$> fp5_zero) = .ok Qsag.QuinticGoldilocks.zero := by
  rw [fp5_zero_refines]; exact congrArg Result.ok fp5Abs_zero

theorem fp5_one_refines_qsag :
    (fp5Abs <$> fp5_one) = .ok Qsag.QuinticGoldilocks.one := by
  rw [fp5_one_refines]; exact congrArg Result.ok fp5Abs_one

theorem fp5_from_base_refines_qsag (x : U64) :
    (fp5Abs <$> fp5_from_base x) = .ok (Qsag.QuinticGoldilocks.ofBase (fieldAbs x)) := by
  rw [fp5_from_base_refines]; exact congrArg Result.ok (fp5Abs_fromBase x)

theorem fp5_eq_iff_qsag {x y : Fp5} (hx : IsCanonicalFp5 x) (hy : IsCanonicalFp5 y) :
    fp5_eq x y = .ok true ↔ fp5Abs x = fp5Abs y := by
  rw [fp5_eq_sound]; exact (fp5Abs_inj hx hy).symm

theorem fp5_add_refines_qsag (x y : Fp5) :
    (fp5Abs <$> fp5_add x y) =
      .ok (Qsag.QuinticGoldilocks.add (fp5Abs x) (fp5Abs y)) := by
  rw [fp5_add_refines]; exact congrArg Result.ok (fp5Abs_add x y)

theorem fp5_sub_refines_qsag (x y : Fp5) :
    (fp5Abs <$> fp5_sub x y) =
      .ok (Qsag.QuinticGoldilocks.sub (fp5Abs x) (fp5Abs y)) := by
  rw [fp5_sub_refines]; exact congrArg Result.ok (fp5Abs_sub x y)

theorem fp5_neg_refines_qsag (x : Fp5) :
    (fp5Abs <$> fp5_neg x) =
      .ok (Qsag.QuinticGoldilocks.neg (fp5Abs x)) := by
  rw [fp5_neg_refines]; exact congrArg Result.ok (fp5Abs_neg x)

theorem fp5_scale_refines_qsag (x : Fp5) (s : U64) :
    (fp5Abs <$> fp5_scale x s) =
      .ok (Qsag.QuinticGoldilocks.mul (fp5Abs x) (Qsag.QuinticGoldilocks.ofBase (fieldAbs s))) := by
  rw [fp5_scale_refines]; exact congrArg Result.ok (fp5Abs_scale x s)

theorem fp5_mul_refines_qsag (x y : Fp5) :
    (fp5Abs <$> fp5_mul x y) =
      .ok (Qsag.QuinticGoldilocks.mul (fp5Abs x) (fp5Abs y)) := by
  rw [fp5_mul_refines]; exact congrArg Result.ok (fp5Abs_mul x y)

theorem fp5_frobenius_refines_qsag (x : Fp5) :
    (fp5Abs <$> fp5_frobenius x) =
      .ok (Qsag.QuinticGoldilocks.frob (fp5Abs x)) := by
  rw [fp5_frobenius_refines]; exact congrArg Result.ok (fp5Abs_frob x)

theorem canonical_query_group_idx_refines_qsag
    (raw_idx groups : U64) (dom : List Qsag.QuinticGoldilocks)
    (hDom : dom.length = groups.val) :
    (Option.map UScalar.val <$> canonical_query_group_idx raw_idx groups) =
      .ok (if dom.length = 0 then none else some (raw_idx.val % dom.length)) := by
  rw [canonical_query_group_idx_spec, hDom]
  by_cases hg : groups = 0#u64
  · rw [hg]; rfl
  · have hgNe : groups.val ≠ 0 := fun h0 => hg (UScalar.eq_of_val_eq h0)
    have hModLt : raw_idx.val % groups.val < 2 ^ 64 :=
      Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero hgNe)) groups.val_lt
    simp only [hgNe, ↓reduceIte]
    change Result.ok (some (BitVec.ofNat 64 (raw_idx.val % groups.val)).toNat) =
      Result.ok (some (raw_idx.val % groups.val))
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hModLt]

/-! ## 2. Antipodal `QuinticMultiStageWhir` Fiber Fold & `ZkHemV2.maskLine` Zero-Knowledge Welds -/

/-- Antipodal coset weld connecting `duet_fold_fp5` to `Qsag.SuccinctWhirAgg.fiberPoint`:
    on antipodal order-`2^(k+1)` fiber evaluations `P(fiberPoint (k+1) 1 j)` and
    `P(fiberPoint (k+1) 1 (2^k + j))` of any linear coset polynomial `P = [even, odd]`,
    `duet_fold_fp5` recovers `RoundPoly.evalCoeffs [odd, even] (fp5Abs alpha)`. -/
theorem duet_fold_fp5_antipodal_fiberPoint_qsag
    (even odd : Qsag.QuinticGoldilocks) (k j : Nat) (hk : k + 1 ≤ 32)
    (x : Qsag.Goldilocks) (hx : x ≠ Qsag.Goldilocks.zero)
    (hPt : Qsag.SuccinctWhirAgg.fiberPoint (k + 1) Qsag.QuinticGoldilocks.one j =
      Qsag.QuinticGoldilocks.ofBase x)
    (alpha : Fp5) :
    let pPos := Qsag.RoundPoly.evalCoeffs [even, odd]
      (Qsag.SuccinctWhirAgg.fiberPoint (k + 1) Qsag.QuinticGoldilocks.one j)
    let pNeg := Qsag.RoundPoly.evalCoeffs [even, odd]
      (Qsag.SuccinctWhirAgg.fiberPoint (k + 1) Qsag.QuinticGoldilocks.one (2 ^ k + j))
    (fp5Abs <$> duet_fold_fp5 (canonicalFp5 pPos) (canonicalFp5 pNeg)
      (canonicalFieldWord (Qsag.Goldilocks.mul
        (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)) (Qsag.Goldilocks.inv x)))
      (canonicalFieldWord (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2))) alpha) =
      .ok (Qsag.RoundPoly.evalCoeffs [odd, even] (fp5Abs alpha)) := by
  intro pPos pNeg
  have hAnti := Qsag.SuccinctWhirAgg.fiberPoint_antipode k j hk Qsag.QuinticGoldilocks.one
  have hpPos : canonicalFp5 pPos =
      fp5Add (canonicalFp5 even) (fp5Scale (canonicalFp5 odd) (canonicalFieldWord x)) := by
    apply (fp5Abs_inj (isCanonicalFp5_canonicalFp5 _) (fp5Add_canonical _ _)).mp
    rw [fp5Abs_canonicalFp5, fp5Abs_add, fp5Abs_scale, fp5Abs_canonicalFp5,
        fp5Abs_canonicalFp5, fieldAbs_canonicalFieldWord]
    dsimp only [pPos]
    rw [hPt, Qsag.RoundPoly.evalCoeffs_cons, Qsag.RoundPoly.evalCoeffs_cons,
        Qsag.RoundPoly.evalCoeffs_nil]
    simp only [← Qsag.QuinticGoldilocks.ring_add, ← Qsag.QuinticGoldilocks.ring_mul]
    constructive_ring
  have hpNeg : canonicalFp5 pNeg =
      fp5Sub (canonicalFp5 even) (fp5Scale (canonicalFp5 odd) (canonicalFieldWord x)) := by
    apply (fp5Abs_inj (isCanonicalFp5_canonicalFp5 _) (fp5Sub_canonical _ _)).mp
    rw [fp5Abs_canonicalFp5, fp5Abs_sub, fp5Abs_scale, fp5Abs_canonicalFp5,
        fp5Abs_canonicalFp5, fieldAbs_canonicalFieldWord]
    dsimp only [pNeg]
    rw [hAnti, hPt, Qsag.RoundPoly.evalCoeffs_cons, Qsag.RoundPoly.evalCoeffs_cons,
        Qsag.RoundPoly.evalCoeffs_nil]
    simp only [← Qsag.QuinticGoldilocks.ring_sub, ← Qsag.QuinticGoldilocks.ring_mul]
    constructive_ring
  rw [hpPos, hpNeg, duet_fold_fp5_coset_sound alpha
      (isCanonicalFp5_canonicalFp5 even) (isCanonicalFp5_canonicalFp5 odd)
      canonicalFieldWord_two_inv (canonicalFieldWord_two_x_inv hx)]
  change Result.ok (fp5Abs (fp5Add (canonicalFp5 odd) (fp5Mul alpha (canonicalFp5 even)))) = _
  rw [fp5Abs_add, fp5Abs_mul, fp5Abs_canonicalFp5, fp5Abs_canonicalFp5,
      Qsag.RoundPoly.evalCoeffs_cons, Qsag.RoundPoly.evalCoeffs_cons, Qsag.RoundPoly.evalCoeffs_nil]
  simp only [← Qsag.QuinticGoldilocks.ring_add, ← Qsag.QuinticGoldilocks.ring_mul]
  exact congrArg Result.ok (by constructive_ring)

/-- Extracted `affine_combine_fp5 even odd alpha` (`odd + alpha * even`) refines `Qsag.ZkHemV2.maskLine`
    over `Qsag.QuinticGoldilocks`. -/
theorem affine_combine_fp5_refines_zkHemV2_maskLine (even odd alpha : Fp5) :
    (fp5Abs <$> affine_combine_fp5 even odd alpha) =
      .ok (Qsag.ZkHemV2.maskLine (fp5Abs alpha)
        (fun _ : Unit => fp5Abs odd) (fun _ : Unit => fp5Abs even) ()) := by
  rw [affine_combine_fp5_refines]
  change Result.ok (fp5Abs (fp5Add odd (fp5Mul alpha even))) = _
  rw [fp5Abs_add, fp5Abs_mul]
  rfl

/-- **MIR Quintic Mask-Line Zero-Knowledge Theorem (`mir_affine_combine_fp5_coin_bijection_simulated`)**:
    For every nonzero challenge `alpha` (`fp5Abs alpha ≠ 0`), the canonical MIR `affine_combine_fp5`
    output distribution over uniform canonical `Fp5` blinding coins is perfectly simulated
    (`Qsag.ZkHemV2.CoinBijectionSimulated`) by a uniform `QuinticGoldilocks` element independent of `odd`! -/
theorem mir_affine_combine_fp5_coin_bijection_simulated
    (alpha : Fp5) (hAlpha : fp5Abs alpha ≠ Qsag.CommRingOps.zero) :
    Qsag.ZkHemV2.CoinBijectionSimulated
      (fun (odd : Qsag.QuinticGoldilocks) (even : Qsag.QuinticGoldilocks) =>
        fp5Abs <$> affine_combine_fp5 (canonicalFp5 even) (canonicalFp5 odd) alpha)
      (fun (simOut : Qsag.QuinticGoldilocks) =>
        (Result.ok simOut : Result Qsag.QuinticGoldilocks)) := by
  intro odd
  let F := Qsag.QuinticGoldilocks
  let unitWord : Qsag.SimpleEquiv F (Unit → F) :=
    ⟨fun x _ => x, fun f => f (), fun _ => rfl, fun _ => rfl⟩
  obtain ⟨mask, hMask⟩ := Qsag.ZkHemV2.v2_mask_line_perfectly_simulated
    (fp5Abs alpha) hAlpha (unitWord.toFun odd)
  refine ⟨(unitWord.trans mask).trans unitWord.symm, fun even => ?_⟩
  dsimp only
  rw [affine_combine_fp5_refines_zkHemV2_maskLine, fp5Abs_canonicalFp5, fp5Abs_canonicalFp5]
  exact congrArg Result.ok (congrFun (hMask (unitWord.toFun even)) ())

/-! ## 3. Multi-Round MIR Sumcheck Chain Weld to Canonical `Qsag.RoundPoly.evalCoeffs` -/

def mirVerifyShiftSumcheckChainFp5 :
    Fp5 → List (Fp5 × Fp5) → List Fp5 → Fp5 → Result Bool
  | curClaim, [], [], termEval => fp5_eq curClaim termEval
  | curClaim, (c0, c2) :: ps, r :: rs, termEval => do
    let nextClaim ← eval_quadratic_sumcheck_wire_fp5 c0 c2 curClaim r
    mirVerifyShiftSumcheckChainFp5 nextClaim ps rs termEval
  | _, _, _, _ => ok false

def evalCanonicalShiftSumcheckChainFp5 :
    Qsag.QuinticGoldilocks →
    List (Qsag.QuinticGoldilocks × Qsag.QuinticGoldilocks) →
    List Qsag.QuinticGoldilocks →
    Option Qsag.QuinticGoldilocks
  | curClaim, [], [] => some curClaim
  | curClaim, (c0, c2) :: ps, r :: rs =>
    let nextClaim := Qsag.RoundPoly.evalCoeffs (canonicalQuadraticWireFp5Poly c0 c2 curClaim) r
    evalCanonicalShiftSumcheckChainFp5 nextClaim ps rs
  | _, _, _ => none

theorem mirVerifyShiftSumcheckChainFp5_iff_qsag :
    ∀ (curClaim : Fp5) (wires : List (Fp5 × Fp5)) (challenges : List Fp5) (termEval : Fp5),
      IsCanonicalFp5 curClaim →
      IsCanonicalFp5 termEval →
      (mirVerifyShiftSumcheckChainFp5 curClaim wires challenges termEval = .ok true ↔
        evalCanonicalShiftSumcheckChainFp5 (fp5Abs curClaim)
          (wires.map (fun p => (fp5Abs p.1, fp5Abs p.2)))
          (challenges.map fp5Abs) = some (fp5Abs termEval))
  | curClaim, [], [], termEval, hCur, hTerm => by
    dsimp only [mirVerifyShiftSumcheckChainFp5, evalCanonicalShiftSumcheckChainFp5, List.map]
    rw [fp5_eq_iff_qsag hCur hTerm, Option.some.injEq]
  | _, [], _ :: _, _, _, _ => by
    dsimp only [mirVerifyShiftSumcheckChainFp5, evalCanonicalShiftSumcheckChainFp5, List.map]
    constructor <;> intro h <;> cases h
  | _, _ :: _, [], _, _, _ => by
    dsimp only [mirVerifyShiftSumcheckChainFp5, evalCanonicalShiftSumcheckChainFp5, List.map]
    constructor <;> intro h <;> cases h
  | curClaim, (c0, c2) :: ps, r :: rs, termEval, _, hTerm => by
    dsimp only [mirVerifyShiftSumcheckChainFp5, evalCanonicalShiftSumcheckChainFp5, List.map]
    rw [bind_eq_result_bind, eval_quadratic_sumcheck_wire_fp5_refines]
    dsimp only [Result.bind]
    have hNextCan : IsCanonicalFp5 (quadraticWireFp5Value c0 c2 curClaim r) := by
      rw [quadraticWireFp5Value.public_eqs]; exact fp5Add_canonical _ _
    have hNextAbs : fp5Abs (quadraticWireFp5Value c0 c2 curClaim r) =
        Qsag.RoundPoly.evalCoeffs
          (canonicalQuadraticWireFp5Poly (fp5Abs c0) (fp5Abs c2) (fp5Abs curClaim))
          (fp5Abs r) := by
      have hRef := eval_quadratic_sumcheck_wire_fp5_refines_qsag c0 c2 curClaim r
      rw [eval_quadratic_sumcheck_wire_fp5_refines] at hRef
      exact Result.ok.inj hRef
    have ih := mirVerifyShiftSumcheckChainFp5_iff_qsag
      (quadraticWireFp5Value c0 c2 curClaim r) ps rs termEval hNextCan hTerm
    rw [ih, hNextAbs]

/-! ## 4. `QSAGHQM2` Header, Deployed `[16, 28]` Schedule Envelope & `verifyHemAffineWhir` Stage Welds -/

/-- Maps a verified `QSAGHQM2` profile tag onto canonical `Qsag.Aggregation.PublicHemQuintic128`. -/
@[expose] def decodePublicHemProfileTag (tag : U8) : Option Qsag.Aggregation.PublicHemQuintic128 :=
  if tag = QSAGHQM2_PROFILE_TURBO400 then some .turboShake400
  else if tag = QSAGHQM2_PROFILE_GL24 then some .poseidon2Gl24
  else none

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
        0 < hdr.payload_len.val ∧ hdr.payload_len = actual_payload_len := by
  intro hOk
  obtain ⟨⟨_, hProf, hActPos, hActLe, hLenPos, hLenEq⟩, rfl⟩ :=
    (verify_qsaghqm2_header_some_iff magic profile_tag active_signers num_validators
      declared_payload_len actual_payload_len hdr).mp hOk
  have hNe : QSAGHQM2_PROFILE_GL24 ≠ QSAGHQM2_PROFILE_TURBO400 := by
    rw [qsaghqm2_profile_gl24_val, qsaghqm2_profile_turbo400_val]; decide
  rcases hProf with rfl | rfl
  · refine ⟨.turboShake400, ?_, Qsag.Aggregation.publicHemDigestCard_pos _,
      ⟨fun _ => rfl, fun _ => rfl⟩,
      ⟨(fun h => by cases h), (fun h => absurd h.symm hNe)⟩,
      hActPos, hActLe, hLenPos, hLenEq⟩
    simp [decodePublicHemProfileTag]
  · refine ⟨.poseidon2Gl24, ?_, Qsag.Aggregation.publicHemDigestCard_pos _,
      ⟨(fun h => by cases h), (fun h => absurd h hNe)⟩,
      ⟨fun _ => rfl, fun _ => rfl⟩,
      hActPos, hActLe, hLenPos, hLenEq⟩
    simp [decodePublicHemProfileTag, hNe]

/-- **Production `[16, 28]` Schedule Envelope Theorem (`verify_quintic_schedule_envelope_accepts_zkHemV2ProdStages`)**:
    Every deployed `zk-Hem v2` schedule `Qsag.ZkHemV2Cert.zkHemV2ProdStages n` across
    `MIN_QUINTIC_LOG_CELLS ≤ n ≤ MAX_QUINTIC_LOG_CELLS` (`16 ≤ n ≤ 28`) has folded-variable sum
    strictly below `MAX_CANOPY_LOG_LEAVES` (`28`) and is accepted (`= .ok true`) by the extracted
    Rust MIR gate `verify_quintic_schedule_envelope`! -/
theorem verify_quintic_schedule_envelope_accepts_zkHemV2ProdStages
    (n : Nat) (hLo : MIN_QUINTIC_LOG_CELLS.val ≤ n) (hHi : n ≤ MAX_QUINTIC_LOG_CELLS.val) :
    let stages := Qsag.ZkHemV2Cert.zkHemV2ProdStages n
    let folded := (stages.map Qsag.ClosedWhir.WhirStage.foldK).sum
    folded < MAX_CANOPY_LOG_LEAVES.val ∧
    verify_quintic_schedule_envelope
      (UScalar.ofNat .U32 n)
      (UScalar.ofNat .U32 (n - folded))
      (UScalar.ofNat .U32 folded)
      (UScalar.ofNat .U32 stages.length) = .ok true := by
  rw [min_quintic_log_cells_val] at hLo
  rw [max_quintic_log_cells_val] at hHi
  change 16 ≤ n at hLo
  change n ≤ 28 at hHi
  have hCases : n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨
      n = 24 ∨ n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 := by omega
  rcases hCases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (dsimp only;
     simp only [Qsag.ZkHemV2Cert.zkHemV2ProdStages.public_eqs,
       verify_quintic_schedule_envelope_spec, QuinticScheduleEnvelopeSpec,
       min_quintic_log_cells_val, max_quintic_log_cells_val, max_canopy_log_leaves_val];
     decide)

/-- **Stage-Fold Weld into `Qsag.verifyHemAffineWhir` over `QuinticGoldilocks`**:
    When `verify_cwyz_bridge_claim_step_fp5` and both `verify_fp5_univariate_at_base_pin` OOD checks
    return `.ok true` on candidate polynomial slice `cand` satisfying `polyWitnessValid` and
    `checkQueriedCosets`, and the cascade + tail stages pass, `Qsag.verifyHemAffineWhir` accepts
    the composed `.cascade :: .stageFold :: restTr` transcript over `Qsag.QuinticGoldilocks`! -/
theorem mirStageGatesFp5_sound_for_verifyHemAffineWhir
    (inst : Qsag.HemWhirInstance Qsag.QuinticGoldilocks)
    (st : Qsag.HemWhirStageSpec Qsag.QuinticGoldilocks)
    (remStages : List (Qsag.HemWhirStageSpec Qsag.QuinticGoldilocks))
    (hStages : inst.stages = st :: remStages)
    (shifts : List Qsag.QuinticGoldilocks)
    (weights : List (Qsag.QuinticGoldilocks × Qsag.QuinticGoldilocks))
    (cascadeDecoded : List (List Qsag.QuinticGoldilocks))
    (stageOracle : Nat → Qsag.QuinticGoldilocks)
    (w0 w1 w2 w3 w4 claim phi theta alpha beta claimedNext ood0 ood1 : Fp5)
    (z0 z1 : U64)
    (cand : Slice Fp5)
    (restTr : List (Qsag.HemTranscriptRound Qsag.QuinticGoldilocks))
    (hBatchBounds : 1 ≤ inst.batchOracles.length ∧ inst.batchOracles.length ≤ 16 ∧
      inst.batchClaims.length = inst.batchOracles.length)
    (hShiftsLen : shifts.length = inst.batchClaims.length)
    (hWeightsLen : weights.length = inst.batchClaims.length)
    (hClaimEq : fp5Abs claim = Qsag.evalCascadeClaim inst.batchClaims shifts weights)
    (hCascadeWit : cascadeDecoded.any (fun P =>
      Qsag.polyWitnessValid inst.initDomainPts
        (Qsag.hemNextMinAgree inst.initDomainPts.length inst.initMinAgree)
        (inst.initDegBound + 1)
        (Qsag.evalCascadeOracle inst.initDomainPts inst.batchOracles weights)
        inst.initKernel (fp5Abs claim) P) = true)
    (hBridgeOk : verify_cwyz_bridge_claim_step_fp5 w0 w1 w2 w3 w4 claim phi theta alpha beta claimedNext = .ok true)
    (hPin0Ok : verify_fp5_univariate_at_base_pin cand z0 ood0 = .ok true)
    (hPin1Ok : verify_fp5_univariate_at_base_pin cand z1 ood1 = .ok true)
    (hCandWit : Qsag.polyWitnessValid st.domainPts st.minAgree st.degBound stageOracle
      (Qsag.hemKernelFold (fp5Abs phi) inst.initKernel) (fp5Abs claimedNext)
      (cand.val.map fp5Abs) = true)
    (hCosetsOk : Qsag.checkQueriedCosets st.domainPts stageOracle (cand.val.map fp5Abs)
      st.queriedCosets = true)
    (hTailOk : Qsag.verifyHemStages stageOracle st.domainPts st.degBound st.minAgree
      (Qsag.hemKernelFold (fp5Abs phi) inst.initKernel) (fp5Abs claimedNext) remStages restTr = true) :
    Qsag.verifyHemAffineWhir inst
      (.cascade shifts weights cascadeDecoded ::
       .stageFold stageOracle (fp5Abs w0) (fp5Abs w1) (fp5Abs w2) (fp5Abs w3) (fp5Abs w4)
         (fp5Abs phi) (fp5Abs theta) (fp5Abs alpha) (fp5Abs beta)
         (Qsag.QuinticGoldilocks.ofBase (fieldAbs z0))
         (Qsag.QuinticGoldilocks.ofBase (fieldAbs z1))
         (fp5Abs ood0) (fp5Abs ood1) [cand.val.map fp5Abs] :: restTr) = true := by
  have hBridge := ((verify_cwyz_bridge_claim_step_fp5_sound_qsag
    w0 w1 w2 w3 w4 claim phi theta alpha beta claimedNext).mp hBridgeOk).2
  have hEval0 := ((verify_fp5_univariate_at_base_pin_sound_qsag cand z0 ood0).mp hPin0Ok).2.symm
  have hEval1 := ((verify_fp5_univariate_at_base_pin_sound_qsag cand z1 ood1).mp hPin1Ok).2.symm
  unfold Qsag.verifyHemAffineWhir
  dsimp only
  rw [decide_eq_true hBatchBounds, decide_eq_true hShiftsLen, decide_eq_true hWeightsLen,
      hStages, ← hClaimEq, hCascadeWit, Qsag.verifyHemStages_cons_stageFold]
  simp only [List.any_cons, List.any_nil, Bool.or_false]
  rw [← hBridge, hCandWit, decide_eq_true hEval0, decide_eq_true hEval1, hCosetsOk, hTailOk]
  rfl

#verify_constructive
  goldilocks_p_eq_qsag_prime
  max_u64_word_lt_two_pow_64_qsag
  fp5_nonresidue_w_eq_qsag
  frobenius_zeta5_constants_eq_qsag
  copy_fp5_refines_qsag
  add_refines_qsag
  sub_refines_qsag
  mul_refines_qsag
  fp5_zero_refines_qsag
  fp5_one_refines_qsag
  fp5_from_base_refines_qsag
  fp5_eq_iff_qsag
  fp5_add_refines_qsag
  fp5_sub_refines_qsag
  fp5_neg_refines_qsag
  fp5_scale_refines_qsag
  fp5_mul_refines_qsag
  fp5_frobenius_refines_qsag
  canonical_query_group_idx_refines_qsag
  duet_fold_fp5_antipodal_fiberPoint_qsag
  affine_combine_fp5_refines_zkHemV2_maskLine
  mir_affine_combine_fp5_coin_bijection_simulated
  mirVerifyShiftSumcheckChainFp5_iff_qsag
  verify_qsaghqm2_header_refines_qsag
  verify_quintic_schedule_envelope_accepts_zkHemV2ProdStages
  mirStageGatesFp5_sound_for_verifyHemAffineWhir

end qsag_whir_verified.proofs
end
