module
public import Qsag.Protocol.Aggregation.Aggregation
public import Qsag.Protocol.Aggregation.ZkHem
public import Qsag.Protocol.Aggregation.SuccinctAggregationIop
public import Qsag.Oracle.Qrom
public import Qsag.Math.GoldilocksBase
public import Qsag.Oracle.Keccak
/-
Witnesses and teeth for the aggregation parity statements.

A. Canonical GF(p^4) (`Math/QuarticExt4`, `Protocol/Aggregation/FieldTransport`): the
   tower-to-polynomial-basis isomorphism on concrete elements, and the limb order it needs
   (`tooth_identity_limb_order_not_multiplicative`: reading the tower limbs in storage order as
   polynomial coefficients is not multiplicative; `tooth_identity_limb_order_wrong_wire`).
B. Squeezed challenges (`Aggregation` §10b): zero has sixteen word-quadruple preimages, a
   generic element has one, and the factor 16 cannot be dropped from
   `Aggregation.squeezed_event_count_le` (`tooth_squeezed_zero_event_exceeds_uniform_bound`).
C. WHIR regimes: the eight wire tags, the per-regime targets, and that the five bounded-query
   profiles and the classical regime do not reach the 128-bit Grover floor or the 256-bit query
   target (`tooth_cdhz25_misses_johnson_qrom_target`, `tooth_no_uniform_grover_floor`).
D. The 28-variable cap in `Composed.checkTree`.
E. The regenerated label inventory of `CrossProtocolAndDualOracleComposition`.
-/
public import Qsag.Protocol.Aggregation.FieldTransport
public import Qsag.Protocol.Aggregation.ComposedQsAgAndMergeSecurity
public import Qsag.Protocol.Aggregation.CrossProtocolAndDualOracleComposition
public import Qsag.Math.Goldilocks
public import Qsag.Math.QuarticExt4
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.AggregationParityTeeth
set_option autoImplicit false
attribute [-instance] Fin.instLinearOrderPackage UInt8.instLawfulEqOrd

open Qsag.GoldilocksField.GoldilocksExt4 (Ext4Poly towerToPoly polyToTower)

/-! ## A. Canonical GF(p^4): tower and polynomial basis -/

/-- `2 + 3u + (5 + 7u) v`. -/
def sampleX : QuarticGoldilocks :=
  ⟨⟨Goldilocks.ofNat 2, Goldilocks.ofNat 3⟩, ⟨Goldilocks.ofNat 5, Goldilocks.ofNat 7⟩⟩

/-- `11 + 13u + (17 + 19u) v`. -/
def sampleY : QuarticGoldilocks :=
  ⟨⟨Goldilocks.ofNat 11, Goldilocks.ofNat 13⟩, ⟨Goldilocks.ofNat 17, Goldilocks.ofNat 19⟩⟩

/-- The isomorphism on concrete elements: `2 + 5v + 3v^2 + 7v^3`, product, inverse and wire
    bytes all agree across the two bases. -/
theorem inhabited_isoQuarticToPoly :
    Math.isoQuarticToPoly.toFun sampleX =
      ⟨Goldilocks.ofNat 2, Goldilocks.ofNat 5, Goldilocks.ofNat 3, Goldilocks.ofNat 7⟩ ∧
    Math.isoQuarticToPoly.toFun (CommRingOps.mul sampleX sampleY) =
      CommRingOps.mul (Math.isoQuarticToPoly.toFun sampleX) (Math.isoQuarticToPoly.toFun sampleY) ∧
    Math.isoQuarticToPoly.toFun (LawfulField.inv sampleX) =
      LawfulField.inv (Math.isoQuarticToPoly.toFun sampleX) ∧
    encodeExt4PolyBytes32 (Math.isoQuarticToPoly.toFun sampleX) = encodeExt4Bytes32 sampleX ∧
    decodeExt4PolyBytes32 (encodeExt4Bytes32 sampleX) =
      some (Math.isoQuarticToPoly.toFun sampleX) :=
  ⟨by rw [Math.isoQuarticToPoly_toFun]; rfl, Math.isoQuarticToPoly.map_mul _ _, Math.isoQuarticToPoly.map_inv _,
    Math.isoQuarticToPoly_encode _, by
      rw [Math.isoQuarticToPoly_decode, decodeExt4Bytes32_encode]; rfl⟩

/-- The product of the two samples is not their limbwise product: the multiplication transported
    by the isomorphism is the `v^4 = 7` convolution. -/
theorem inhabited_ext4Poly_mul_value :
    towerToPoly (CommRingOps.mul sampleX sampleY) =
      ⟨Goldilocks.ofNat 1793, Goldilocks.ofNat 1125, Goldilocks.ofNat 1075,
        Goldilocks.ofNat 231⟩ := by
  rfl

/-- Reading the tower limbs `[c0.c0, c0.c1, c1.c0, c1.c1]` in storage order as the coefficients of
    `1, v, v^2, v^3`. -/
def identityLimbOrder (z : QuarticGoldilocks) : Ext4Poly := ⟨z.c0.c0, z.c0.c1, z.c1.c0, z.c1.c1⟩

/-- `#tooth`: the storage-order reading is not multiplicative (`v` would be read as `v^2`, and
    `v * v = u` as `v`), so the `[0, 2, 1, 3]` limb permutation of `towerToPoly` is needed. -/
theorem tooth_identity_limb_order_not_multiplicative :
    ¬ (identityLimbOrder (CommRingOps.mul QuarticGoldilocks.vBasis QuarticGoldilocks.vBasis) =
      CommRingOps.mul (identityLimbOrder QuarticGoldilocks.vBasis)
        (identityLimbOrder QuarticGoldilocks.vBasis)) := by
  intro h
  have hc := congrArg Ext4Poly.a1 h
  change Goldilocks.ofNat 1 = Goldilocks.ofNat 0 at hc
  exact (by decide : Goldilocks.ofNat 1 ≠ Goldilocks.ofNat 0) hc

/-- `#tooth`: the storage-order reading also disagrees with the wire: its polynomial-basis bytes
    are not the bytes `field.rs:to_le_bytes` writes. -/
theorem tooth_identity_limb_order_wrong_wire :
    ¬ (encodeExt4PolyBytes32 (identityLimbOrder sampleX) = encodeExt4Bytes32 sampleX) := by
  intro h
  have hd := congrArg decodeExt4PolyBytes32 h
  rw [decodeExt4PolyBytes32_encode, ← Math.isoQuarticToPoly_encode,
    decodeExt4PolyBytes32_encode] at hd
  have hc := congrArg (fun p => p.a1) (Option.some.inj hd)
  rw [Math.isoQuarticToPoly_toFun] at hc
  change Goldilocks.ofNat 3 = Goldilocks.ofNat 5 at hc
  exact (by decide : Goldilocks.ofNat 3 ≠ Goldilocks.ofNat 5) hc

/-! ## B. Squeezed challenges -/

/-- Zero has two 64-bit preimages per limb: `0` and `p`. -/
theorem inhabited_zero_word_preimages :
    Goldilocks.ofNat 0 = Goldilocks.zero ∧ Goldilocks.ofNat goldilocksPrime = Goldilocks.zero ∧
      goldilocksPrime < 2 ^ 64 ∧ Goldilocks.wordMultiplicity Goldilocks.zero = 2 := by
  rw [Goldilocks.wordMultiplicity.public_eqs]
  decide

/-- A residue `≥ 2^32 - 1` has one preimage, so the multiplicity is not constant. -/
theorem inhabited_word_multiplicity_one :
    Goldilocks.wordMultiplicity (Goldilocks.ofNat (2 ^ 32 - 1)) = 1 ∧
      ext4WordMultiplicity
        ⟨⟨Goldilocks.ofNat (2 ^ 32), Goldilocks.ofNat (2 ^ 32)⟩,
          ⟨Goldilocks.ofNat (2 ^ 32), Goldilocks.ofNat (2 ^ 32)⟩⟩ = 1 := by
  simp only [ext4WordMultiplicity.public_eqs, Goldilocks.wordMultiplicity.public_eqs]
  decide

/-- Exactly sixteen of the `2^256` word quadruples reduce to zero. -/
theorem inhabited_zero_quad_preimages :
    (wordQuadPool.filter
      (fun q => decide (ofWordQuad q = (CommRingOps.zero : QuarticGoldilocks)))).length = 16 := by
  rw [wordQuadPool_fiber_length, ext4WordMultiplicity_zero]

/-- The event "the challenge is zero" is hit by at most one element of any duplicate-free list
    of field elements: the hypothesis of `Aggregation.squeezed_event_count_le` at `d = 1`. -/
theorem inhabited_zero_event_uniform_bound (T : List Aggregation.GoldilocksExt4) (hT : T.Nodup) :
    (T.filter (fun z => decide (z = (CommRingOps.zero : QuarticGoldilocks)))).length ≤ 1 :=
  filter_eq_max_one_of_nodup _ hT

/-- The squeezed bound at `d = 1` is `16`, and it is attained. -/
theorem inhabited_squeezed_event_count :
    (wordQuadPool.filter
      (fun q => decide (ofWordQuad q = (CommRingOps.zero : QuarticGoldilocks)))).length ≤
        16 * 1 :=
  Aggregation.squeezed_event_count_le
    (fun z => decide (z = (CommRingOps.zero : QuarticGoldilocks))) 1
    inhabited_zero_event_uniform_bound

/-- `#tooth`: the uniform-field count `d = 1` is false for squeezed challenges; the factor 16 in
    `Aggregation.squeezed_event_count_le` cannot be dropped. -/
theorem tooth_squeezed_zero_event_exceeds_uniform_bound :
    ¬ ((wordQuadPool.filter
      (fun q => decide (ofWordQuad q = (CommRingOps.zero : QuarticGoldilocks)))).length ≤ 1) := by
  rw [inhabited_zero_quad_preimages]
  decide

/-! ## C. WHIR regimes -/

/-- All eight Rust `repr(u8)` tags decode; the next unused tag `11` is rejected. -/
theorem inhabited_eight_regime_tags :
    ([2, 4, 5, 6, 7, 8, 9, 10] : List UInt8).map Aggregation.WhirSecurityRegime.decodeTag? =
      Aggregation.WhirSecurityRegime.all.map some ∧
    Aggregation.WhirSecurityRegime.decodeTag? 11 = none := by
  exact ⟨rfl, rfl⟩

/-- `#tooth`: the Role-1 TurboSHAKE tag is live, so rejecting tag `9` is not wire parity. -/
theorem tooth_turboshake_tag_not_retired :
    Aggregation.WhirSecurityRegime.decodeTag? 9 ≠ none := by
  decide

/-- Representatives of the CDHZ25 tables at the 28-variable cap. -/
theorem inhabited_cdhz25_schedule_28 :
    (WhirSecurityRegime.schedule .cdhz25JohnsonQrom128 28).stages =
      [⟨4, 6, 202⟩, ⟨16, 6, 102⟩, ⟨64, 4, 70⟩, ⟨256, 4, 52⟩] ∧
    (WhirSecurityRegime.schedule .poseidon2Cdhz25ZeroPowQrom128 28).stages =
      [⟨4, 6, 216⟩, ⟨16, 6, 109⟩, ⟨64, 4, 74⟩, ⟨256, 4, 56⟩] := by
  exact ⟨rfl, rfl⟩

/-- `#tooth`: the CDHZ25 PoW table does not reach the `2^-256` query target of the default
    Johnson regime (its first stage has `(√B)^q = 2^202`). -/
theorem tooth_cdhz25_misses_johnson_qrom_target :
    ¬ (∀ s ∈ Aggregation.whirSchedule4Stage .cdhz25JohnsonQrom128,
      2 ^ 256 < s.johnsonSqrtBlowup ^ s.numQueries) := by
  decide

/-- `#tooth`: there is no 128-bit nominal Grover floor over all eight regimes: six of the eight
    are below it. -/
theorem tooth_no_uniform_grover_floor :
    ¬ (∀ r ∈ Aggregation.WhirSecurityRegime.all, 128 ≤ r.qromGroverRoundBits) := by
  decide

/-- `#tooth`: the bounded-query accounting fails at an unbounded query budget: at `Q = 2^64` the
    tag-5 profile leaves fewer than 128 bits. -/
theorem tooth_cdhz25_search_accounting_fails_at_two_pow_64 :
    ¬ (4 * (2 ^ 64) ^ 2 * 2 ^ 128 ≤
      2 ^ Aggregation.WhirSecurityRegime.cdhz25JohnsonQrom128.classicalFsRoundBits) := by
  decide

/-! ## D. The 28-variable cap in `Composed.checkTree` -/

open Qsag.Composed in
/-- A leaf at the cap `numVars = 28` with the canonical schedule is accepted. -/
theorem inhabited_checkTree_28_vars :
    checkTree exampleHeader exampleVerifier 16
      (.leaf { exampleShard 1#2 with
        numVars := 28, schedule := WhirSecurityRegime.schedule .bciksJohnsonQrom128 28 }) =
      true := by
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, rfl⟩
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, by decide +kernel⟩
  apply Bool.and_eq_true_iff.mpr
  exact ⟨decide_eq_true rfl, decide_eq_true ⟨by decide, by decide, rfl⟩⟩

open Qsag.Composed in
/-- `#tooth`: a leaf claiming 29 variables is rejected even with the schedule function's own
    output for 29. -/
theorem tooth_checkTree_29_vars_rejected :
    ¬ (checkTree exampleHeader exampleVerifier 16
      (.leaf { exampleShard 1#2 with
        numVars := 29, schedule := WhirSecurityRegime.schedule .bciksJohnsonQrom128 29 }) =
      true) := by
  intro h
  have h1 := (Bool.and_eq_true_iff.mp h).1
  have h2 := (Bool.and_eq_true_iff.mp h1).1
  have hg := of_decide_eq_true (Bool.and_eq_true_iff.mp h2).2
  exact (by decide : ¬ (29 ≤ 28)) hg.2.1

/-! ## E. Label inventory -/

/-- The Rust `round_constants` label and the current HD/policy/VC labels are inventoried. -/
theorem inhabited_current_labels :
    (CrossProtocol.auditedLabelsOf "qsag-fts").contains "QSAG.PSFTS.POW7_ROUNDS.V5" = true ∧
    (CrossProtocol.auditedLabelsOf "qsag-hd").contains "QSAG.HD.QUERY_BUDGET.V4" = true ∧
    (CrossProtocol.auditedLabelsOf "qsag-policy").contains "QSAG.POLICY.DURABLE_LEDGER.V6" = true ∧
    (CrossProtocol.auditedLabelsOf "qsag-cred").contains "QSAG.VC.SD_STMT_DIGEST.V2" = true := by
  decide +kernel

/-- `#tooth`: the superseded labels are no longer inventoried. -/
theorem tooth_stale_labels_absent :
    ¬ ((CrossProtocol.auditedLabelsOf "qsag-fts").contains "QSAG.PSFTS.POW7_ROUND.V4" = true) ∧
    ¬ ((CrossProtocol.auditedLabelsOf "qsag-hd").contains "QSAG.HD.QUERY_BUDGET.V2" = true) ∧
    ¬ ((CrossProtocol.auditedLabelsOf "qsag-hd").contains "QSAG.HD.QUERY_BUDGET.V3" = true) ∧
    ¬ ((CrossProtocol.auditedLabelsOf "qsag-policy").contains "QSAG.POLICY.DURABLE_LEDGER.V5" = true) ∧
    ¬ ((CrossProtocol.auditedLabelsOf "qsag-cred").contains "QSAG.VC.SD_STMT_DIGEST.V1" = true) := by
  decide +kernel

#verify_constructive inhabited_isoQuarticToPoly inhabited_ext4Poly_mul_value
  tooth_identity_limb_order_not_multiplicative tooth_identity_limb_order_wrong_wire
  inhabited_zero_word_preimages inhabited_word_multiplicity_one inhabited_zero_quad_preimages
  inhabited_zero_event_uniform_bound inhabited_squeezed_event_count
  tooth_squeezed_zero_event_exceeds_uniform_bound inhabited_eight_regime_tags
  tooth_turboshake_tag_not_retired
  inhabited_cdhz25_schedule_28 tooth_cdhz25_misses_johnson_qrom_target
  tooth_no_uniform_grover_floor tooth_cdhz25_search_accounting_fails_at_two_pow_64
  inhabited_checkTree_28_vars tooth_checkTree_29_vars_rejected inhabited_current_labels
  tooth_stale_labels_absent

#tooth_pair Qsag.GoldilocksField.GoldilocksExt4.towerToPoly_mul_hom vs
  tooth_identity_limb_order_not_multiplicative
#tooth_pair Qsag.Math.isoQuarticToPoly_encode vs tooth_identity_limb_order_wrong_wire
#tooth_pair Qsag.Aggregation.squeezed_event_count_le vs
  tooth_squeezed_zero_event_exceeds_uniform_bound
#tooth_pair Qsag.wordQuadPool_fiber_length vs tooth_squeezed_zero_event_exceeds_uniform_bound
#tooth_pair Qsag.Aggregation.whirRegime_positive_slack vs tooth_cdhz25_misses_johnson_qrom_target
#tooth_pair Qsag.Aggregation.whirRegime_bounded_query_profiles vs tooth_no_uniform_grover_floor
#tooth_pair Qsag.Aggregation.whirRegime_bounded_query_search_accounting vs
  tooth_cdhz25_search_accounting_fails_at_two_pow_64
#tooth_pair Qsag.Composed.binary_merge_sound vs tooth_checkTree_29_vars_rejected

end Qsag.AggregationParityTeeth
end

public section
namespace Qsag.Aggregation
/-- Concrete inhabitedness witness: a genuine 16-bit `cSHAKE256` Proof-of-Work (`powBits = 16`,
    nonce `70035`) on the digest of `powWitnessSeed` (`"WHIR_STAGE_POW"` under
    `"QSAG.AGG.FS_TRANSCRIPT/v1"`), checked by the Lean kernel. -/
theorem inhabited_whir_stage_pow_16 :
    verifyWhirStagePow (stagePowDigest powWitnessSeed) 70035 16 = true := stage_pow_fixture_accepts

/-- `#tooth` Invalid PoW Nonce Rejection (`powNonce = 0` fails 16-bit PoW on the witness digest). -/
theorem tooth_whir_pow16_nonce0_rejected :
    verifyWhirStagePow (stagePowDigest powWitnessSeed) 0 16 = false := stage_pow_fixture_rejects_zero

theorem tooth_whir_pow_nonce_mutation :
    ∃ nonce : Nat, nonce ≠ 70035 ∧
      verifyWhirStagePow (stagePowDigest powWitnessSeed) nonce 16 = false :=
  ⟨0, by decide, tooth_whir_pow16_nonce0_rejected⟩

#tooth_pair verifyWhirStagePow_16_iff vs tooth_whir_pow_nonce_mutation
theorem inhabited_whir_pow_inputs :
    ∃ (chal : List UInt8) (nonce : Nat),
      chal = stagePowDigest powWitnessSeed ∧ nonce = 70035 ∧
      chal.length = 32 ∧ nonce < 2 ^ 64 ∧ verifyWhirStagePow chal nonce 16 = true :=
  ⟨stagePowDigest powWitnessSeed, 70035, rfl, rfl, stagePowDigest_length _,
    by decide, inhabited_whir_stage_pow_16⟩

#verify_inhabited verifyWhirStagePow_16_iff inhabited_whir_pow_inputs

/-- Dual-OOD (`whirOodSamples = 2`) challenge derivation produces two well-defined challenges,
    and mutating `oodChallenges.2` triggers `verifyOneWhirStage = false`. -/
theorem tooth_whir_dual_ood_samples_enforced :
    whirOodSamples = 2 ∧
    let oods := deriveStageOodChallenges powWitnessSeed (stagePowDigest powWitnessSeed)
    let spBad : WhirStageProof :=
      { stageRoot := stagePowDigest powWitnessSeed
        oodChallenges := (oods.1, CommRingOps.add oods.2 GoldilocksExt4.one)
        oodEvals := (GoldilocksExt4.zero, GoldilocksExt4.zero)
        shiftClaim := GoldilocksExt4.zero
        shiftPolys := []
        layerRoots := []
        shiftChallenges := []
        foldChallenges := []
        shiftTerminalEval := GoldilocksExt4.zero
        powNonce := 0
        queries := [] }
    let sdom0 : WhirStageDomain :=
      { stageIdx := 0, blowup := 4, groups0 := 4, foldLayers := 1, numQueries := 1,
        powBits := 0, invTwo := Goldilocks.one, invTwoY0 := fun _ _ => Goldilocks.one,
        sampleFuel := 1 }
    spBad.oodChallenge = deriveStageOodChallenge powWitnessSeed spBad.stageRoot ∧
    verifyOneWhirStage [] [] powWitnessSeed sdom0 spBad none = false := by
  refine ⟨by rw [whirOodSamples.public_eqs], ?_, ?_⟩
  · simp only [WhirStageProof.oodChallenge.public_eqs, deriveStageOodChallenge.public_eqs]
  apply tooth_whir_wrong_second_ood_challenge_rejected
  intro hEq
  simp only [WhirStageProof.oodChallenge2.public_eqs] at hEq
  have hSub : CommRingOps.sub
      (CommRingOps.add (deriveStageOodChallenges powWitnessSeed (stagePowDigest powWitnessSeed)).2
        GoldilocksExt4.one)
      (deriveStageOodChallenges powWitnessSeed (stagePowDigest powWitnessSeed)).2 =
      GoldilocksExt4.zero := by
    rw [hEq, LawfulCommRing.sub_self]
    exact GoldilocksExt4.zero_eq_ringZero.symm
  have hOne : CommRingOps.sub
      (CommRingOps.add (deriveStageOodChallenges powWitnessSeed (stagePowDigest powWitnessSeed)).2
        GoldilocksExt4.one)
      (deriveStageOodChallenges powWitnessSeed (stagePowDigest powWitnessSeed)).2 =
      GoldilocksExt4.one := by
    rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_comm _ GoldilocksExt4.one,
      LawfulCommRing.add_assoc, LawfulCommRing.add_right_neg, LawfulCommRing.add_zero]
  exact LawfulField.one_ne_zero (F := QuarticGoldilocks) (hOne.symm.trans hSub)

end Qsag.Aggregation
end

public section
namespace Qsag
/-- A concrete `ByteArray → ByteArray` digest with 32-byte output: the first 32 bytes of the
    input, zero-padded. It is not collision resistant (it ignores every byte past the 32nd),
    which is what makes the hypotheses of the extractor satisfiable. -/
def canopyPrefixHash (x : ByteArray) : ByteArray :=
  ⟨⟨(x.data.toList ++ List.replicate 32 (0 : UInt8)).take 32⟩⟩

theorem canopyPrefixHash_length (x : ByteArray) :
    (canopyPrefixHash x).data.toList.length = 32 := by
  show ((x.data.toList ++ List.replicate 32 (0 : UInt8)).take 32).length = 32
  rw [List.length_take, List.length_append, List.length_replicate]
  omega

/-- The 32-byte digest whose bytes all equal `b`. -/
def canopyConstDigest (b : UInt8) : CanopyDigest32 :=
  ⟨⟨⟨List.replicate 32 b⟩⟩, List.length_replicate⟩

/-- Commitment of the two-leaf tree with leaf `0` equal to `canopyConstDigest 5` under
    `canopyPrefixHash`; the node frame keeps only 27 bytes of the left child, so the commitment
    does not depend on the right child. -/
def canopyAuditCommitment : CanopyDigest32 :=
  canopyRootHashOf canopyPrefixHash canopyPrefixHash_length 1
    (canopyNodeHashOf canopyPrefixHash canopyPrefixHash_length 1
      (canopyConstDigest 5) (canopyConstDigest 7))

private theorem canopyAudit_accepts (b : UInt8) :
    verifyCanopyMultiproof (canopyNodeHashOf canopyPrefixHash canopyPrefixHash_length)
      (canopyRootHashOf canopyPrefixHash canopyPrefixHash_length) 1 canopyAuditCommitment
      [(0, canopyConstDigest 5)] [canopyConstDigest b] = true := by
  rw [verifyCanopyMultiproof_one, decide_eq_true_eq]
  apply Subtype.ext
  simp only [canopyAuditCommitment, canopyRootHashOf_val, canopyNodeHashOf_val,
    canopyNodeFrame.public_eqs, canopyRootFrame.public_eqs, canopyPrefixHash, canopyConstDigest]
  rfl

/-- Inhabitedness witness for the transcript extractor over a `ByteArray → ByteArray` 32-byte
    digest: under `canopyPrefixHash`, two `CanopyMultiProof` openings of leaf `0` with different
    siblings are both accepted against `canopyAuditCommitment`, so the hypotheses of
    `extractHashCollisionFromCanopyTranscripts` are jointly satisfiable, and the extractor
    returns an explicit pair of distinct byte strings with equal digests. -/
theorem inhabited_canopy_collision_extractor :
    verifyCanopyMultiproof (canopyNodeHashOf canopyPrefixHash canopyPrefixHash_length)
        (canopyRootHashOf canopyPrefixHash canopyPrefixHash_length) 1 canopyAuditCommitment
        [(0, canopyConstDigest 5)] [canopyConstDigest 7] = true ∧
    verifyCanopyMultiproof (canopyNodeHashOf canopyPrefixHash canopyPrefixHash_length)
        (canopyRootHashOf canopyPrefixHash canopyPrefixHash_length) 1 canopyAuditCommitment
        [(0, canopyConstDigest 5)] [canopyConstDigest 8] = true ∧
    Nonempty (ExtractedHashCollision canopyPrefixHash) :=
  ⟨canopyAudit_accepts 7, canopyAudit_accepts 8,
    ⟨extractHashCollisionFromCanopyTranscripts canopyPrefixHash canopyPrefixHash_length 1
      canopyAuditCommitment [(0, canopyConstDigest 5)] [(0, canopyConstDigest 5)]
      [canopyConstDigest 7] [canopyConstDigest 8] rfl
        (canopyAudit_accepts 7) (canopyAudit_accepts 8) (by
          intro h
          have hs := congrArg Prod.snd h
          have hc := congrArg (fun d : CanopyDigest32 => d.val.data.toList) (List.cons.inj hs).1
          exact (by decide : List.replicate 32 (7 : UInt8) ≠ List.replicate 32 8) hc)⟩⟩

end Qsag
end

public section
namespace Qsag.ZkHem
open CommRingOps
/-- One terminal operand `w ∈ F_{p^4}` padded with four base-field cells at a challenge
    outside `F_{p^2}`, with a zero-round sumcheck: an instance of `ZkHemModel`. -/
def padModel (z : Fp4) (hz : z.c1 ≠ zero) : @ZkHemModel Fp4 fp4Field :=
  letI := fp4Field
  { Wit := Fp4
    Coin := Pad
    Obs := Fp4
    Idx := Unit
    n := 0
    d := 0
    c := fun _ => zero
    pubH := zero
    enc := fun w κ _ => add w (padMap z κ)
    ell := LinForm.evalAt ()
    obs := fun w κ => add w (padMap z κ)
    obsInv := fun w o => padInv z (sub o w)
    obs_left := fun w κ => by
      have e : sub (add w (padMap z κ)) w = padMap z κ := by constructive_ring
      rw [e, padInv_padMap z hz]
    obs_right := fun w o => by
      rw [padMap_padInv z hz]
      constructive_ring
    evalOf := fun o => o
    eval_obs := fun _ _ => rfl
    term := fun _ => zero
    rounds := fun _ _ => ⟨zero, fun _ => zero, fun _ _ => zero⟩
    rounds_honest := fun _ _ i hi => absurd hi (Nat.not_lt_zero i)
    rounds_claim := fun _ _ => rfl
    rounds_term := fun _ _ => rfl }

/-- Perfect HVZK of the padded opening for every challenge outside `F_{p^2}`. -/
theorem zkHem_padded_opening_perfect_hvzk (z : Fp4) (hz : z.c1 ≠ zero) (ρ γ : Fp4)
    (hρ : ρ ≠ zero) (hγ : γ ≠ zero) :
    PerfectlySimulated (@ZkHemModel.real Fp4 fp4Field (padModel z hz) ρ γ)
      (@ZkHemModel.sim Fp4 fp4Field (padModel z hz) ρ γ) :=
  @zkHem_perfect_hvzk_simulation Fp4 fp4Field _ (padModel z hz) fp4_two_ne_zero ρ γ hρ hγ


#verify_constructive Qsag.ZkHem.zkHem_padded_opening_perfect_hvzk
end Qsag.ZkHem
end
