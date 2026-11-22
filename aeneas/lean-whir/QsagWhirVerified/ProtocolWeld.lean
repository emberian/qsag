module
public import QsagWhirVerified.Canonical
public import Qsag.Protocol.Aggregation.Aggregation
public import Qsag.Protocol.Aggregation.ZkHemV2
import Qsag.Tactic.AssuranceKit
/-!
# `QsagWhirVerified.ProtocolWeld` — Full 37/37 Canonical Closure & Protocol-Level WHIR Verifier Welds

Completes the canonical `Qsag` refinement bridge between `QsagWhirVerified` (31 extracted
functions/constants and six loop helpers in `QsagWhirVerified.Funs`) and the aggregation specs.

1. **100% Canonical `Qsag` Symbol Closure (`add`, `sub`, `mul`, `ext_eq`, `ext_add`, `ext_sub`,
   `ext_scale`, `affine_combine`, `cwyz_duet_fold`, `eval_univariate_ext4_at_base`,
   `canonical_query_group_idx`, plus the 3 module constants)**:
   Closes every remaining extracted symbol in `QsagWhirVerified.Funs` directly against canonical
   `Qsag.Goldilocks`, `Qsag.Aggregation.GoldilocksExt4`, `Qsag.Aggregation.foldDuetExt4`, and
   `Qsag.RoundPoly.evalCoeffs`.
2. **`ZkHemV2` Zero-Knowledge Mask-Line Weld (`affine_combine_refines_zkHemV2_maskLine`,
   `mir_affine_combine_coin_bijection_simulated`)**:
   Welds extracted `affine_combine even odd alpha` directly to `Qsag.ZkHemV2.maskLine` and lifts
   `ZkHemV2.v2_mask_line_perfectly_simulated` (`CoinBijectionSimulated`) to MIR `Ext4` coins.
3. **Multi-Round Sumcheck Chain Weld (`mirVerifyShiftSumcheckChain_iff_qsag`)**:
   Characterizes acceptance of the quadratic wire chain by iterating `Qsag.RoundPoly.evalCoeffs`
   on the reconstructed coefficients and comparing the terminal claim.
4. **Cascade & Stage-Fold Weld to `Qsag.verifyHemAffineWhir` (`mirEvalCascadeBatch_refines_evalCascadeClaim`,
   `mirStageGates_sound_for_verifyHemAffineWhir`)**:
   Welds the multi-polynomial MIR `affine_cascade_claim_step` accumulator loop to `Qsag.evalCascadeClaim`
   and connects accepted MIR bridge (`cwyz_bridge_claim_step`) + dual OOD (`verify_ext4_univariate_at_base_pin`)
   checks directly into `Qsag.verifyHemStages` / `Qsag.verifyHemAffineWhir`.
-/

public section
namespace qsag_whir_verified.proofs
open Aeneas Aeneas.Std Result

/-! ## 1. Canonical `Qsag` Closure of Constants, Scalar Ops, `Ext4` Ops & `canonical_query_group_idx` -/

theorem goldilocks_p_eq_qsag_prime : GOLDILOCKS_P.val = Qsag.goldilocksPrime :=
  goldilocks_p_val

theorem max_u64_word_lt_two_pow_64_qsag :
    MAX_U64_WORD.val + 1 = 2 ^ 64 ∧ Qsag.goldilocksPrime < MAX_U64_WORD.val := by
  rw [max_u64_word_val]
  exact ⟨by decide, by decide⟩

theorem tag_canopy_merkle_internal_qsag
    (idx : U64) (level : U32) (node sibling : Array U8 32#usize) (pair : MerklePair)
    (h : step_merkle_pair_order idx level node sibling = .ok (some pair)) :
    pair.tag = TAG_CANOPY_MERKLE_INTERNAL ∧
    Qsag.encodeMultiFrame [pair.left.val.map (fun b => UInt8.ofNat b.val),
                           pair.right.val.map (fun b => UInt8.ofNat b.val)] =
      Qsag.Aggregation.merkleNodeFrame (idx.val / 2 ^ level.val)
        (node.val.map (fun b => UInt8.ofNat b.val))
        (sibling.val.map (fun b => UInt8.ofNat b.val)) := by
  obtain ⟨_, hTag, hFrame⟩ := step_merkle_pair_order_canonical_parity idx level node sibling pair h
  rw [tag_canopy_merkle_internal_eq]
  exact ⟨hTag, hFrame⟩

theorem add_refines_qsag (a b : U64) :
    (fieldAbs <$> add a b) = .ok (Qsag.Goldilocks.add (fieldAbs a) (fieldAbs b)) := by
  rw [add_refines]
  exact congrArg Result.ok (fieldAbs_add a b)

theorem sub_refines_qsag (a b : U64) :
    (fieldAbs <$> sub a b) = .ok (Qsag.Goldilocks.sub (fieldAbs a) (fieldAbs b)) := by
  rw [sub_refines]
  exact congrArg Result.ok (fieldAbs_sub a b)

theorem mul_refines_qsag (a b : U64) :
    (fieldAbs <$> mul a b) = .ok (Qsag.Goldilocks.mul (fieldAbs a) (fieldAbs b)) := by
  rw [mul_refines]
  exact congrArg Result.ok (fieldAbs_mul a b)

theorem ext_eq_iff_qsag {x y : Ext4} (hx : IsCanonicalExt4 x) (hy : IsCanonicalExt4 y) :
    ext_eq x y = .ok true ↔ ext4Abs x = ext4Abs y := by
  rw [ext_eq_sound]
  exact (ext4Abs_inj hx hy).symm

theorem ext_add_refines_qsag (x y : Ext4) :
    (ext4Abs <$> ext_add x y) =
      .ok (Qsag.Aggregation.GoldilocksExt4.add (ext4Abs x) (ext4Abs y)) := by
  rw [ext_add_refines]
  exact congrArg Result.ok (ext4Abs_add x y)

theorem ext_sub_refines_qsag (x y : Ext4) :
    (ext4Abs <$> ext_sub x y) =
      .ok (Qsag.Aggregation.GoldilocksExt4.sub (ext4Abs x) (ext4Abs y)) := by
  rw [ext_sub_refines]
  exact congrArg Result.ok (ext4Abs_sub x y)

theorem ext_scale_refines_qsag (x : Ext4) (s : U64) :
    (ext4Abs <$> ext_scale x s) =
      .ok (Qsag.Aggregation.GoldilocksExt4.mul (ext4Abs x)
        (Qsag.Aggregation.GoldilocksExt4.embedBase (fieldAbs s))) := by
  rw [ext_scale_refines]
  exact congrArg Result.ok (ext4Abs_scale x s)

/-- Direct weld of `cwyz_duet_fold` to `Qsag.Exec.hemAffineDuetFold` (`Qsag.Aggregation.foldDuetExt4`)
    under canonical coset twiddles. -/
theorem cwyz_duet_fold_refines_foldDuetExt4
    (v0 v1 : Ext4) (x : Qsag.Goldilocks) (theta alpha beta : Ext4) :
    (ext4Abs <$> cwyz_duet_fold v0 v1
      (canonicalFieldWord (Qsag.Goldilocks.mul
        (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)) (Qsag.Goldilocks.inv x)))
      (canonicalFieldWord (Qsag.Goldilocks.inv (Qsag.Goldilocks.ofNat 2)))
      (canonicalFieldWord (Qsag.Goldilocks.mul x x)) theta alpha beta) =
      .ok (Qsag.Exec.hemAffineDuetFold (ext4Abs v0) (ext4Abs v1) x
        (ext4Abs theta) (ext4Abs alpha) (ext4Abs beta)) := by
  have h := fold_duet_affine_ext4_canonical_twiddles v0 v1 x theta alpha beta
  rw [fold_duet_affine_ext4.public_eq_1] at h
  exact h

/-- Direct weld of `eval_univariate_ext4_at_base` to `Qsag.RoundPoly.evalCoeffs`. -/
theorem eval_univariate_ext4_at_base_refines_evalCoeffs (coeffs : Slice Ext4) (z : U64) :
    (ext4Abs <$> eval_univariate_ext4_at_base coeffs z) =
      .ok (Qsag.RoundPoly.evalCoeffs (coeffs.val.map ext4Abs)
        (Qsag.Aggregation.GoldilocksExt4.embedBase (fieldAbs z))) := by
  rw [eval_univariate_ext4_at_base.public_eq_1]
  exact eval_ext4_univariate_at_base_refines_evalCoeffs coeffs z

/-- Canonical fiber/coset group-index weld for `canonical_query_group_idx`:
    rejects `groups = 0` (`none`) and otherwise maps `raw_idx` onto `Fin groups.val` (`< groups.val`),
    matching WHIR coset index projection into a domain of `groups.val` cosets. -/
theorem canonical_query_group_idx_refines_qsag
    (raw_idx groups : U64) (dom : List Qsag.Aggregation.GoldilocksExt4)
    (hDom : dom.length = groups.val) :
    (Option.map UScalar.val <$> canonical_query_group_idx raw_idx groups) =
      .ok (if dom.length = 0 then none else some (raw_idx.val % dom.length)) := by
  rw [canonical_query_group_idx_spec, hDom]
  by_cases hg : groups = 0#u64
  · rw [hg]
    rfl
  · have hgNe : groups.val ≠ 0 := fun h0 => hg (UScalar.eq_of_val_eq h0)
    have hModLt : raw_idx.val % groups.val < 2 ^ 64 :=
      Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero hgNe)) groups.val_lt
    simp only [hgNe, ↓reduceIte]
    change Result.ok (some (BitVec.ofNat 64 (raw_idx.val % groups.val)).toNat) =
      Result.ok (some (raw_idx.val % groups.val))
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hModLt]

/-! ## 2. `ZkHemV2.maskLine` & `CoinBijectionSimulated` Zero-Knowledge Weld for `affine_combine` -/

/-- Extracted `affine_combine even odd alpha` (`odd + alpha * even`) refines `Qsag.ZkHemV2.maskLine`
    at challenge `ext4Abs alpha`, witness `ext4Abs odd`, and blinding coin `ext4Abs even`. -/
theorem affine_combine_refines_zkHemV2_maskLine (even odd alpha : Ext4) :
    (ext4Abs <$> affine_combine even odd alpha) =
      .ok (Qsag.ZkHemV2.maskLine (ext4Abs alpha)
        (fun _ : Unit => ext4Abs odd) (fun _ : Unit => ext4Abs even) ()) := by
  rw [affine_combine_refines]
  change Result.ok (ext4Abs (extAdd odd (extMul alpha even))) = _
  rw [ext4Abs_add, ext4Abs_mul]
  rfl

/-- **MIR Mask-Line Zero-Knowledge Theorem (`mir_affine_combine_coin_bijection_simulated`)**:
    For every nonzero challenge `alpha` (`ext4Abs alpha ≠ 0`), the canonical MIR `affine_combine`
    output distribution over uniform canonical `Ext4` blinding coins is perfectly simulated
    (`Qsag.ZkHemV2.CoinBijectionSimulated`) by a uniform `GoldilocksExt4` element independent of `odd`! -/
theorem mir_affine_combine_coin_bijection_simulated
    (alpha : Ext4) (hAlpha : ext4Abs alpha ≠ Qsag.CommRingOps.zero) :
    Qsag.ZkHemV2.CoinBijectionSimulated
      (fun (odd : Qsag.Aggregation.GoldilocksExt4) (even : Qsag.Aggregation.GoldilocksExt4) =>
        ext4Abs <$> affine_combine (canonicalExt4 even) (canonicalExt4 odd) alpha)
      (fun (simOut : Qsag.Aggregation.GoldilocksExt4) =>
        (Result.ok simOut : Result Qsag.Aggregation.GoldilocksExt4)) := by
  intro odd
  let F := Qsag.Aggregation.GoldilocksExt4
  let unitWord : Qsag.SimpleEquiv F (Unit → F) :=
    ⟨fun x _ => x, fun f => f (), fun _ => rfl, fun _ => rfl⟩
  obtain ⟨mask, hMask⟩ := Qsag.ZkHemV2.v2_mask_line_perfectly_simulated
    (ext4Abs alpha) hAlpha (unitWord.toFun odd)
  refine ⟨(unitWord.trans mask).trans unitWord.symm, fun even => ?_⟩
  dsimp only
  rw [affine_combine_refines_zkHemV2_maskLine, ext4Abs_canonicalExt4, ext4Abs_canonicalExt4]
  exact congrArg Result.ok (congrFun (hMask (unitWord.toFun even)) ())

/-! ## 3. Multi-Round MIR Sumcheck Chain Weld to Canonical `Qsag.RoundPoly.evalCoeffs` -/

/-- Multi-round MIR quadratic shift-sumcheck verifier executing `eval_quadratic_sumcheck_wire`
    step-by-step and checking final equality via `ext_eq`. -/
def mirVerifyShiftSumcheckChain :
    Ext4 → List (Ext4 × Ext4) → List Ext4 → Ext4 → Result Bool
  | curClaim, [], [], termEval => ext_eq curClaim termEval
  | curClaim, (c0, c2) :: ps, r :: rs, termEval => do
    let nextClaim ← eval_quadratic_sumcheck_wire c0 c2 curClaim r
    mirVerifyShiftSumcheckChain nextClaim ps rs termEval
  | _, _, _, _ => ok false

/-- Multi-round canonical `Qsag.RoundPoly.evalCoeffs` evaluator stepping along quadratic wire
    round polynomials `canonicalQuadraticWirePoly c0 c2 curClaim`. -/
def evalCanonicalShiftSumcheckChain :
    Qsag.Aggregation.GoldilocksExt4 →
    List (Qsag.Aggregation.GoldilocksExt4 × Qsag.Aggregation.GoldilocksExt4) →
    List Qsag.Aggregation.GoldilocksExt4 →
    Option Qsag.Aggregation.GoldilocksExt4
  | curClaim, [], [] => some curClaim
  | curClaim, (c0, c2) :: ps, r :: rs =>
    let nextClaim := Qsag.RoundPoly.evalCoeffs (canonicalQuadraticWirePoly c0 c2 curClaim) r
    evalCanonicalShiftSumcheckChain nextClaim ps rs
  | _, _, _ => none

/-- **Bidirectional Multi-Round Sumcheck Weld (`mirVerifyShiftSumcheckChain_iff_qsag`)**:
    Over limb-canonical `Ext4` endpoints (`IsCanonicalExt4`), the monadic MIR loop
    `mirVerifyShiftSumcheckChain` returns `.ok true` **if and only if** the canonical `Qsag`
    polynomial chain `evalCanonicalShiftSumcheckChain` (`Qsag.RoundPoly.evalCoeffs`) evaluates
    to `some (ext4Abs termEval)`! -/
theorem mirVerifyShiftSumcheckChain_iff_qsag :
    ∀ (curClaim : Ext4) (wires : List (Ext4 × Ext4)) (challenges : List Ext4) (termEval : Ext4),
      IsCanonicalExt4 curClaim →
      IsCanonicalExt4 termEval →
      (mirVerifyShiftSumcheckChain curClaim wires challenges termEval = .ok true ↔
        evalCanonicalShiftSumcheckChain (ext4Abs curClaim)
          (wires.map (fun p => (ext4Abs p.1, ext4Abs p.2)))
          (challenges.map ext4Abs) = some (ext4Abs termEval))
  | curClaim, [], [], termEval, hCur, hTerm => by
    dsimp only [mirVerifyShiftSumcheckChain, evalCanonicalShiftSumcheckChain, List.map]
    rw [ext_eq_iff_qsag hCur hTerm, Option.some.injEq]
  | _, [], _ :: _, _, _, _ => by
    dsimp only [mirVerifyShiftSumcheckChain, evalCanonicalShiftSumcheckChain, List.map]
    constructor <;> intro h <;> cases h
  | _, _ :: _, [], _, _, _ => by
    dsimp only [mirVerifyShiftSumcheckChain, evalCanonicalShiftSumcheckChain, List.map]
    constructor <;> intro h <;> cases h
  | curClaim, (c0, c2) :: ps, r :: rs, termEval, _, hTerm => by
    dsimp only [mirVerifyShiftSumcheckChain, evalCanonicalShiftSumcheckChain, List.map]
    rw [bind_eq_result_bind, eval_quadratic_sumcheck_wire_refines]
    dsimp only [Result.bind]
    have hNextCan : IsCanonicalExt4 (quadraticWireValue c0 c2 curClaim r) := by
      rw [quadraticWireValue.public_eqs]
      exact extAdd_canonical _ _
    have hNextAbs : ext4Abs (quadraticWireValue c0 c2 curClaim r) =
        Qsag.RoundPoly.evalCoeffs
          (canonicalQuadraticWirePoly (ext4Abs c0) (ext4Abs c2) (ext4Abs curClaim))
          (ext4Abs r) := by
      have hRef := eval_quadratic_sumcheck_wire_refines_qsag c0 c2 curClaim r
      rw [eval_quadratic_sumcheck_wire_refines] at hRef
      exact Result.ok.inj hRef
    have ih := mirVerifyShiftSumcheckChain_iff_qsag
      (quadraticWireValue c0 c2 curClaim r) ps rs termEval hNextCan hTerm
    rw [ih, hNextAbs]

/-! ## 4. Multi-Polynomial Cascade Loop & `Qsag.verifyHemAffineWhir` Stage Weld -/

/-- Multi-polynomial MIR cascade claim accumulator folding `affine_cascade_claim_step` across
    `(w0, w1, eval_at_point, shifted_eval)` tuples. -/
def mirEvalCascadeBatch : List (Ext4 × Ext4 × Ext4 × Ext4) → Result Ext4
  | [] => ok extZero
  | (w0, w1, ev, sh) :: rest => do
    let tailAcc ← mirEvalCascadeBatch rest
    affine_cascade_claim_step tailAcc w0 w1 ev sh

/-- **Multi-Polynomial Cascade Weld (`mirEvalCascadeBatch_refines_evalCascadeClaim`)**:
    `mirEvalCascadeBatch` evaluates `Qsag.evalCascadeClaim` across any batch of `S_poly` polynomials,
    connecting directly into Round 0 (`.cascade`) of `Qsag.verifyHemAffineWhir`! -/
theorem mirEvalCascadeBatch_refines_evalCascadeClaim :
    ∀ (batch : List (Ext4 × Ext4 × Ext4 × Ext4)),
      (ext4Abs <$> mirEvalCascadeBatch batch) =
        .ok (Qsag.evalCascadeClaim
          (batch.map (fun t => ext4Abs t.2.2.1))
          (batch.map (fun t => ext4Abs t.2.2.2))
          (batch.map (fun t => (ext4Abs t.1, ext4Abs t.2.1))))
  | [] => by
    dsimp only [mirEvalCascadeBatch, List.map]
    change Result.ok (ext4Abs extZero) = Result.ok (Qsag.evalCascadeClaim [] [] [])
    rw [Qsag.evalCascadeClaim_nil, ext4Abs_zero]
    exact congrArg Result.ok Qsag.GoldilocksField.GoldilocksExt4.zero_eq_ringZero
  | (w0, w1, ev, sh) :: rest => by
    have ih := mirEvalCascadeBatch_refines_evalCascadeClaim rest
    dsimp only [mirEvalCascadeBatch, List.map]
    cases hRec : mirEvalCascadeBatch rest with
    | fail e => rw [hRec] at ih; cases ih
    | div => rw [hRec] at ih; cases ih
    | ok tailAcc =>
      rw [hRec] at ih
      have hTailAbs : ext4Abs tailAcc = Qsag.evalCascadeClaim
          (rest.map (fun t => ext4Abs t.2.2.1))
          (rest.map (fun t => ext4Abs t.2.2.2))
          (rest.map (fun t => (ext4Abs t.1, ext4Abs t.2.1))) := Result.ok.inj ih
      simp only [bind_eq_result_bind, Result.bind, affine_cascade_claim_step_spec]
      change Result.ok (ext4Abs (extAdd (extAdd tailAcc (extMul w0 ev)) (extMul w1 sh))) = _
      rw [ext4Abs_add, ext4Abs_add, ext4Abs_mul, ext4Abs_mul, hTailAbs, Qsag.evalCascadeClaim_cons]
      apply congrArg Result.ok
      simp only [Qsag.Aggregation.GoldilocksExt4.add, Qsag.Aggregation.GoldilocksExt4.mul,
        ← Qsag.QuarticGoldilocks.ring_add, ← Qsag.QuarticGoldilocks.ring_mul]
      constructive_ring

/-- **Stage-Fold Weld into `Qsag.verifyHemAffineWhir` (`mirStageGates_sound_for_verifyHemAffineWhir`)**:
    When the MIR dual-bridge check (`verify_cwyz_bridge_claim_step`) and both MIR OOD univariate
    pins (`verify_ext4_univariate_at_base_pin` at `z₀, z₁`) return `.ok true` on candidate polynomial
    slice `cand` satisfying `polyWitnessValid` and `checkQueriedCosets`, and the cascade + tail
    stages pass, `Qsag.verifyHemAffineWhir` accepts the composed `.cascade :: .stageFold :: restTr`
    transcript! -/
theorem mirStageGates_sound_for_verifyHemAffineWhir
    (inst : Qsag.HemWhirInstance Qsag.QuarticGoldilocks)
    (st : Qsag.HemWhirStageSpec Qsag.QuarticGoldilocks)
    (remStages : List (Qsag.HemWhirStageSpec Qsag.QuarticGoldilocks))
    (hStages : inst.stages = st :: remStages)
    (shifts : List Qsag.QuarticGoldilocks)
    (weights : List (Qsag.QuarticGoldilocks × Qsag.QuarticGoldilocks))
    (cascadeDecoded : List (List Qsag.QuarticGoldilocks))
    (stageOracle : Nat → Qsag.QuarticGoldilocks)
    (w0 w1 w2 w3 w4 claim phi theta alpha beta claimedNext ood0 ood1 : Ext4)
    (z0 z1 : U64)
    (cand : Slice Ext4)
    (restTr : List (Qsag.HemTranscriptRound Qsag.QuarticGoldilocks))
    (hBatchBounds : 1 ≤ inst.batchOracles.length ∧ inst.batchOracles.length ≤ 16 ∧
      inst.batchClaims.length = inst.batchOracles.length)
    (hShiftsLen : shifts.length = inst.batchClaims.length)
    (hWeightsLen : weights.length = inst.batchClaims.length)
    (hClaimEq : ext4Abs claim = Qsag.evalCascadeClaim inst.batchClaims shifts weights)
    (hCascadeWit : cascadeDecoded.any (fun P =>
      Qsag.polyWitnessValid inst.initDomainPts
        (Qsag.hemNextMinAgree inst.initDomainPts.length inst.initMinAgree)
        (inst.initDegBound + 1)
        (Qsag.evalCascadeOracle inst.initDomainPts inst.batchOracles weights)
        inst.initKernel (ext4Abs claim) P) = true)
    (hBridgeOk : verify_cwyz_bridge_claim_step w0 w1 w2 w3 w4 claim phi theta alpha beta claimedNext = .ok true)
    (hPin0Ok : verify_ext4_univariate_at_base_pin cand z0 ood0 = .ok true)
    (hPin1Ok : verify_ext4_univariate_at_base_pin cand z1 ood1 = .ok true)
    (hCandWit : Qsag.polyWitnessValid st.domainPts st.minAgree st.degBound stageOracle
      (Qsag.hemKernelFold (ext4Abs phi) inst.initKernel) (ext4Abs claimedNext)
      (cand.val.map ext4Abs) = true)
    (hCosetsOk : Qsag.checkQueriedCosets st.domainPts stageOracle (cand.val.map ext4Abs)
      st.queriedCosets = true)
    (hTailOk : Qsag.verifyHemStages stageOracle st.domainPts st.degBound st.minAgree
      (Qsag.hemKernelFold (ext4Abs phi) inst.initKernel) (ext4Abs claimedNext) remStages restTr = true) :
    Qsag.verifyHemAffineWhir inst
      (.cascade shifts weights cascadeDecoded ::
       .stageFold stageOracle (ext4Abs w0) (ext4Abs w1) (ext4Abs w2) (ext4Abs w3) (ext4Abs w4)
         (ext4Abs phi) (ext4Abs theta) (ext4Abs alpha) (ext4Abs beta)
         (Qsag.Aggregation.GoldilocksExt4.embedBase (fieldAbs z0))
         (Qsag.Aggregation.GoldilocksExt4.embedBase (fieldAbs z1))
         (ext4Abs ood0) (ext4Abs ood1) [cand.val.map ext4Abs] :: restTr) = true := by
  have hBridge := ((verify_cwyz_bridge_claim_step_sound_qsag
    w0 w1 w2 w3 w4 claim phi theta alpha beta claimedNext).mp hBridgeOk).2
  have hEval0 := ((verify_ext4_univariate_at_base_pin_sound_qsag cand z0 ood0).mp hPin0Ok).2.symm
  have hEval1 := ((verify_ext4_univariate_at_base_pin_sound_qsag cand z1 ood1).mp hPin1Ok).2.symm
  unfold Qsag.verifyHemAffineWhir
  dsimp only
  rw [decide_eq_true hBatchBounds, decide_eq_true hShiftsLen, decide_eq_true hWeightsLen,
      hStages, ← hClaimEq, hCascadeWit]
  dsimp only [Qsag.verifyHemStages]
  simp only [List.any_cons, List.any_nil, Bool.or_false]
  rw [← hBridge, hCandWit, decide_eq_true hEval0, decide_eq_true hEval1, hCosetsOk, hTailOk]
  rfl

#verify_constructive
  goldilocks_p_eq_qsag_prime
  max_u64_word_lt_two_pow_64_qsag
  tag_canopy_merkle_internal_qsag
  add_refines_qsag
  sub_refines_qsag
  mul_refines_qsag
  ext_eq_iff_qsag
  ext_add_refines_qsag
  ext_sub_refines_qsag
  ext_scale_refines_qsag
  cwyz_duet_fold_refines_foldDuetExt4
  eval_univariate_ext4_at_base_refines_evalCoeffs
  canonical_query_group_idx_refines_qsag
  affine_combine_refines_zkHemV2_maskLine
  mir_affine_combine_coin_bijection_simulated
  mirVerifyShiftSumcheckChain_iff_qsag
  mirEvalCascadeBatch_refines_evalCascadeClaim
  mirStageGates_sound_for_verifyHemAffineWhir

end qsag_whir_verified.proofs
end
