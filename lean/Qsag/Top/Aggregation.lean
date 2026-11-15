module
/-
# Qsag.Top.Aggregation — End-to-End Composed Succinct Aggregation Soundness and Extraction

Top-level composition module (zero `import all`) connecting the coding-theoretic proximity-gap
proofs (`Coding/Cwyz26JohnsonCertificate`, `Coding/Cwyz26DeployedStages`), the
round-by-round `HEM`/`WHIR` verifier and point-reduction bridges (`HemVerifierAcceptance`,
`HemPointReductionSoundness`, `HemFoldDecompositionBridge`, `HemSlicedFoldBudget`), the classical
and coherent Fourier QROM Merkle-opening extractors (`QromBatchMerkleExtraction`,
`HemExtractedOpeningBridge`, `QromCoherentMerkleBridge`, `QromFourierSupport`), the hierarchical
shard merge-tree and quorum reduction (`ComposedQsAgAndMergeSecurity`, `Spec/IdealAggregate`),
the quartic-extension field isomorphism (`Math/QuarticExt4`), and SIMT GPU constant-time kernel
execution (`SpirvSimtGpuEquiv`).

Section 6 connects the ideal knowledge-soundness contract `Spec.AggregateExtractorSound` to the
quorum layer: for the native aggregate-signature verifier `verifyAggNativeSig` and an enrolled
custody roster, an accepted aggregate outside the soundness-error event gives, for every active
validator, a validated collision of the commitment hash (`Spec.ValidBreak`), a signature that
verifies without quorum participation, or quorum participation. The contract itself is a
hypothesis of that theorem: no instance for the deployed `HEM`/`WHIR` verifier is constructed
in this module.
-/

public import Qsag.Spec.Primitives
public import Qsag.Spec.Parameters
public import Qsag.Spec.Assumptions
public import Qsag.Spec.IdealAggregate
public import Qsag.Math.QuarticExt4
public import Qsag.Protocol.Aggregation.Cwyz26JohnsonCertificate
public import Qsag.Coding.Cwyz26
public import Qsag.Protocol.Aggregation.Cwyz26EqualDegreeAndMultiFold
public import Qsag.Protocol.Aggregation.CorduroyAndHemAirCompleteness
public import Qsag.Protocol.Aggregation.Poseidon2AlgebraicAndRecursiveHem
public import Qsag.Protocol.Aggregation.CrossProtocolAndDualOracleComposition
public import Qsag.Protocol.Aggregation.HemVerifierAcceptance
public import Qsag.Protocol.Aggregation.HemPointReductionSoundness
public import Qsag.Protocol.Aggregation.HemExtractedOpeningBridge
public import Qsag.Oracle.Qrom
public import Qsag.Protocol.Aggregation.QromCoherentMerkleBridge
public import Qsag.Protocol.Aggregation.QromSaltedMerkleStateRestoration
public import Qsag.Protocol.Aggregation.ComposedQsAgAndMergeSecurity
public import Qsag.Protocol.Aggregation.CompositionInstances
public import Qsag.Protocol.Aggregation.HemSlicedFoldBudget
public import Qsag.Machine.SpirvSimtGpuEquiv
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Top

set_option autoImplicit false

/-! ## 1. `[CWYZ26]` Fold Decomposition, Point Reduction, and Verifier Soundness on `Aggregation.GoldilocksExt4` -/

/-- **End-to-End `Aggregation.GoldilocksExt4` IOP Soundness Chain (`aggExt4_cwyz26_fold_and_point_reduction`)**:
    Instantiates and composes four IOP soundness components directly over the concrete
    32-byte-encoded `Qsag.Aggregation.GoldilocksExt4` field (enabled by `Math.QuarticExt4`):
    1. `[CWYZ26]` Johnson-regime sliced bivariate fold decomposition bound (`nonExcludedDecompBound_sliced`),
    2. Formal `UPoly` affine explanation ↔ correlated-pair decomposition (`hasPolynomialExplanation_iff_decomposes`),
    3. Degree-2 sumcheck point-reduction bad-challenge bound `≤ 2` (`hemPointReductionWire_bad_challenges_le_two`),
    4. `verifyHemAffineWhir` zero-oracle false-claim acceptance bound `≤ |S|` (`verifyHemZeroOracle_accepted_pairs_le`). -/
theorem aggExt4_cwyz26_fold_and_point_reduction
    (D S : List Qsag.Aggregation.GoldilocksExt4)
    (d A B m Wx Dy agree : Nat)
    (G : List Qsag.Aggregation.GoldilocksExt4)
    (c0 c2 claim shiftPt α β : Qsag.Aggregation.GoldilocksExt4)
    (pairOracles : (Qsag.Aggregation.GoldilocksExt4 → Qsag.Aggregation.GoldilocksExt4) ×
                   (Qsag.Aggregation.GoldilocksExt4 → Qsag.Aggregation.GoldilocksExt4))
    (candPoly : List Qsag.Aggregation.GoldilocksExt4)
    (stages : List (Qsag.HemWhirStageSpec Qsag.Aggregation.GoldilocksExt4))
    (decoded : Qsag.Aggregation.GoldilocksExt4 × Qsag.Aggregation.GoldilocksExt4 →
      List (List Qsag.Aggregation.GoldilocksExt4))
    (rest : Qsag.Aggregation.GoldilocksExt4 × Qsag.Aggregation.GoldilocksExt4 →
      List (Qsag.HemTranscriptRound Qsag.Aggregation.GoldilocksExt4))
    (hD : D.Nodup) (hS : S.Nodup)
    (hCount : D.length * Qsag.Poly3.triCount 1 m Dy m < Qsag.Poly3.triCount d Wx Dy (Dy + 1))
    (hd : 1 ≤ d) (hDy : 1 ≤ Dy) (hB : d + 1 ≤ B) (hDen : D.length * (d + 1) < B * B)
    (hAB : B < A)
    (hChar : ∀ k, 1 ≤ k → k ≤ Dy →
      (Qsag.CRing.natCast k : Qsag.Aggregation.GoldilocksExt4) ≠ CommRingOps.zero)
    (hGLen : G.length ≤ 3)
    (hFalseSum : claim ≠ CommRingOps.add
      (Qsag.RoundPoly.evalCoeffs G CommRingOps.zero)
      (Qsag.RoundPoly.evalCoeffs G CommRingOps.one))
    (hEnough : d + 2 ≤ agree) :
    Qsag.NonExcludedDecompBound D S d A m Wx Dy
      (((D.length * (B - (d + 1))) / (B * B - D.length * (d + 1))) *
          Nat.max S.length (D.length * (D.length - 1) / 2) +
        S.length * ((Nat.min Dy ((Wx + Dy - 1) / d)) *
          (Dy * (D.length * ((Nat.min Dy ((Wx + Dy - 1) / d)) * (2 * d * Dy)) / (A - B) + 1)))) ∧
    (Qsag.HasPolynomialExplanation pairOracles D d B α β (Qsag.UPoly.ofList candPoly) ↔
      Qsag.DecomposesViaCorrelatedPair d B pairOracles.1 pairOracles.2 D α β candPoly) ∧
    (S.filter (fun r => decide
      (Qsag.RoundPoly.evalCoeffs (Qsag.hemPointReductionWirePoly c0 c2 claim) r =
        Qsag.RoundPoly.evalCoeffs G r))).length ≤ 2 ∧
    ((Qsag.prodPool S).filter (fun p =>
      Qsag.verifyHemAffineWhir (Qsag.hemZeroOracleClaimInstance D d agree stages)
        (.cascade [shiftPt] [p] (decoded p) :: rest p))).length ≤ S.length :=
  ⟨Qsag.nonExcludedDecompBound_sliced D S d A B m Wx Dy hD hS hCount hd hDy hB hDen hAB hChar,
   Qsag.hasPolynomialExplanation_iff_decomposes pairOracles D d B α β candPoly,
   Qsag.hemPointReductionWire_bad_challenges_le_two G S c0 c2 claim hS hGLen hFalseSum,
   Qsag.verifyHemZeroOracle_accepted_pairs_le D S d agree stages shiftPt decoded rest hD hS hEnough⟩

/-! ## 2. Deployed Stage Geometries (`2 ≤ nv ≤ 24`) Projected Into Canonical `Spec.RatBound` -/

/-- **Deployed `HEM` Stage RBR & QROM Budget Composition (`deployed_hem_stage_budget_and_aggExt4_transport`)**:
    Chains `Cwyz26DeployedStages` + `HemSlicedFoldBudget.sliced_stage_supported_budget` with
    `Math.isoQuarticToAgg` and `Spec.RatBound`:
    1. Transports `D_agg, S_agg : List Aggregation.GoldilocksExt4` into `AffineFoldDecompBound`
       via `isoQuarticToAgg.symm` (`RingIso.map_nodup`),
    2. Certifies `Spec.RatBound.atLeastBits 184` for the stage RBR soundness error, and
    3. Certifies `Spec.RatBound.atLeastBits 128` after Don–Fehr–Majenz (`dfmRoundScale`) QROM
       scaling for all quantum query budgets `Q + 1 ≤ 2 ^ 27`! -/
theorem deployed_hem_stage_budget_and_aggExt4_transport
    (nv : Nat) (h2 : 2 ≤ nv) (h24 : nv ≤ 24)
    (g : Qsag.HemStageGeom) (hg : g ∈ Qsag.hemStageGeoms nv)
    (hne : Qsag.hemJohnsonQromStageExhaustive g = false)
    (Q : Nat) (hQ : Q + 1 ≤ 2 ^ 27) :
    ∃ (r : Nat × Nat × Nat × Nat × Nat) (w : Nat × Nat × Nat × Nat),
      Qsag.hemJohnsonQromTableRow nv g.stageIdx = some r ∧
      Qsag.slicedStageRow nv g.stageIdx = some w ∧
      (∀ (D_agg S_agg : List Qsag.Aggregation.GoldilocksExt4),
        D_agg.Nodup → S_agg.Nodup → D_agg.length = g.n →
        Qsag.AffineFoldDecompBound
          (D_agg.map Qsag.Math.isoQuarticToAgg.symm.toFun)
          (S_agg.map Qsag.Math.isoQuarticToAgg.symm.toFun)
          g.d r.2.2.1 (Qsag.slicedStageCount S_agg.length g r w)) ∧
      (Qsag.Spec.RatBound.ofBudget (Qsag.slicedBinaryStageBound g r w)).atLeastBits 184 ∧
      (Qsag.Spec.RatBound.ofBudget
        (Qsag.dfmRoundScale Q (Qsag.slicedBinaryStageBound g r w))).atLeastBits 128 := by
  obtain ⟨r, w, hTab, hRow, hDecomp, h184, hQrom⟩ :=
    Qsag.sliced_stage_supported_budget nv h2 h24 g hg hne
  refine ⟨r, w, hTab, hRow, ?_, ?_, ?_⟩
  · intro D_agg S_agg hDAgg hSAgg hLen
    have hDQuart := Qsag.Math.isoQuarticToAgg.symm.toRingIso.map_nodup hDAgg
    have hSQuart := Qsag.Math.isoQuarticToAgg.symm.toRingIso.map_nodup hSAgg
    have hDLen : (D_agg.map Qsag.Math.isoQuarticToAgg.symm.toFun).length = g.n := by
      rw [List.length_map, hLen]
    have hSLen : (S_agg.map Qsag.Math.isoQuarticToAgg.symm.toFun).length = S_agg.length :=
      List.length_map _
    rw [← hSLen]
    exact hDecomp _ _ hDQuart hSQuart hDLen
  · exact (Qsag.Spec.RatBound.ofBudget_atLeastBits_iff 184 _).mpr h184
  · exact (Qsag.Spec.RatBound.ofBudget_atLeastBits_iff 128 _).mpr (hQrom Q hQ)

/-! ## 3. Measured & Coherent Fourier QROM Opening Extraction Connected to `verifyHemAffineWhir` -/

/-- **End-to-End Classical-Log & Coherent Fourier QROM Opening Extraction Chain
    (`qrom_hem_opening_and_invalid_coordinate_chain`)**:
    Composes `QromBatchMerkleExtraction` (`measured_batch_merkle_extraction_failure_bound`),
    `HemExtractedOpeningBridge` (`measured_hem_acceptance_from_extracted`, `hem_extracted_invalid_coordinate`),
    and the Zhandry compressed Fourier-register QROM model (`QromCoherentMerkleBridge.coherent_hem_authenticated_event_eq`,
    `QromFourierSupport.fourier_database_overflow_mass_zero`):
    1. Bounds `2^w · measuredEventMass(verifyHemOpeningBatch)` by the extracted-transcript `verifyHemAffineWhir`
       mass plus `batchMerkleCost Q slots · quantumExperimentTotal A`,
    2. Certifies zero Fourier-database support above Hamming weight `Q` (`fourier_database_overflow_mass_zero`)
       and exact Plancherel equivalence of coherent `verifyHemOpeningBatch` mass (`coherent_hem_authenticated_event_eq`), and
    3. On any invalid `HemWhirInstance` (`¬ HemStatementValid inst`) whose extracted opening decodes
       to an accepted cascade transcript, pinpoints an invalid batch coordinate `i < batchOracles.length`! -/
theorem qrom_hem_opening_and_invalid_coordinate_chain
    {cardX w cardAnc Q : Nat}
    (A : Qsag.QuantumAdv cardX w cardAnc Q)
    (ABit : Qsag.QuantumAdv cardX 1 cardAnc Q)
    (L : Qsag.MerkleAddressLayout cardX w)
    (LBit : Qsag.MerkleAddressLayout cardX 1)
    (slots : List (Qsag.MerkleOpeningSlot cardX w))
    (slotsBit : List (Qsag.MerkleOpeningSlot cardX 1))
    (hLevels : ∀ s ∈ slots, s.level + s.depth ≤ L.levels)
    (inst : Qsag.HemWhirInstance Qsag.QuarticGoldilocks)
    (decode : Fin cardX → List (Option (Qsag.MerkleOpeningValue w)) →
      List (Qsag.HemTranscriptRound Qsag.QuarticGoldilocks))
    (decodeBit : Fin cardX → List (Option (Qsag.MerkleOpeningValue 1)) →
      List (Qsag.HemTranscriptRound Qsag.QuarticGoldilocks))
    (H : Fin cardX → BitVec w) (xs : List (Fin cardX)) (x : Fin cardX)
    (shifts : List Qsag.QuarticGoldilocks)
    (weights : List (Qsag.QuarticGoldilocks × Qsag.QuarticGoldilocks))
    (decoded : List (List Qsag.QuarticGoldilocks))
    (rest : List (Qsag.HemTranscriptRound Qsag.QuarticGoldilocks))
    (hDom : inst.initDomainPts.Nodup)
    (hEnough : inst.initDegBound + 1 ≤ inst.initMinAgree)
    (hInvalid : ¬ Qsag.HemStatementValid inst)
    (hDec : decode x (Qsag.extractedOpeningValues L slots H xs x) =
      .cascade shifts weights decoded :: rest)
    (hBatchOk : Qsag.verifyHemOpeningBatch L slots inst decode H x = true)
    (hNoFail : Qsag.batchMerkleFailure L slots H xs x = false) :
    (2 ^ w * Qsag.measuredEventMass A (fun H' _ x' =>
        Qsag.verifyHemOpeningBatch L slots inst decode H' x') ≤
      2 ^ w * Qsag.measuredEventMass A (fun H' xs' x' =>
        Qsag.verifyHemAffineWhir inst (decode x' (Qsag.extractedOpeningValues L slots H' xs' x'))) +
      Qsag.batchMerkleCost Q slots * Qsag.quantumExperimentTotal A) ∧
    (Qsag.oracleTableSum cardX (fun d => if Q < Qsag.tableWeight cardX d then
      Qsag.QVec.stateNormSq (Qsag.fourierAdvStateAt ABit Q (Nat.le_refl Q) d) else 0) = 0) ∧
    (Qsag.coherentTableEventMass (Qsag.verifyHemOpeningBatch LBit slotsBit inst decodeBit)
      (Qsag.fourierOracleState (Qsag.fourierAdvStateAt ABit Q (Nat.le_refl Q))) =
      4 ^ (cardX * Q + cardX) * Qsag.uniformOracleSum 1 cardX (fun H' =>
        Qsag.QVec.queryMassOn (Qsag.verifyHemOpeningBatch LBit slotsBit inst decodeBit H')
          (Qsag.runQuantumAdv ABit H'))) ∧
    (∃ i, i < inst.batchOracles.length ∧
      (∀ G : List Qsag.QuarticGoldilocks,
        Qsag.polyWitnessValid inst.initDomainPts inst.initMinAgree inst.initDegBound
          (inst.batchOracles.getD i (fun _ => CommRingOps.zero)) inst.initKernel
          (inst.batchClaims.getD i CommRingOps.zero) G = false)) := by
  have hMass := Qsag.measured_hem_acceptance_from_extracted A L slots hLevels inst decode
  have hFourier := Qsag.fourier_database_overflow_mass_zero ABit
  have hCoherent := Qsag.coherent_hem_authenticated_event_eq ABit LBit slotsBit inst decodeBit
  obtain ⟨i, hiLt, hNoWit, _⟩ := Qsag.hem_extracted_invalid_coordinate
    L slots inst decode H xs x shifts weights decoded rest
    hDom hEnough hInvalid hBatchOk hNoFail hDec
  exact ⟨hMass, hFourier, hCoherent, i, hiLt, hNoWit⟩

/-! ## 4. Hierarchical Merge-Tree Quorum Soundness & SIMT GPU Non-Interference -/

/-- **Aggregate Merge-Tree & Quorum Reduction Paired With SIMT GPU Constant-Time Verification
    (`aggregate_merge_and_simt_gpu_noninterference`)**:
    Composes `Spec.IdealAggregate.mergeWitnessMaps_valid`, `Composed.binary_merge_sound`,
    and `SpirvSimtGpuEquiv.decoded_spirv_words_simt_ct_noninterference`. -/
theorem aggregate_merge_and_simt_gpu_noninterference
    {PK Sig : Type} {numValidators : Nat}
    (verifySingle : PK → Qsag.Spec.Bytes → Sig → Bool)
    (roster : Fin numValidators → PK) (msg : Qsag.Spec.Bytes)
    (bmL bmR : BitVec numValidators)
    (wL wR : Fin numValidators → Option Sig)
    (hWitL : Qsag.Spec.ValidAggregateWitness verifySingle ⟨roster, bmL, msg⟩ wL)
    (hWitR : Qsag.Spec.ValidAggregateWitness verifySingle ⟨roster, bmR, msg⟩ wR)
    (rootHdr : Qsag.Composed.Header) (verifyShard : Qsag.Composed.Shard numValidators → Bool)
    (tree : Qsag.Composed.MergeTree numValidators) (depth : Nat)
    (hTreeOk : Qsag.Composed.checkTree rootHdr verifyShard depth tree = true)
    {words : List UInt32} {pol : Qsag.SimtCtPolicy} {prog : List Qsag.SpirvInst}
    (hCt : Qsag.checkDecodedWordsSimtCt words pol prog = true)
    (cfg : Qsag.WorkgroupConfig) (subvecIdx fuel : Nat)
    {m₁ m₂ : Qsag.GpuMemState} (hMem : Qsag.MemLowEq pol m₁ m₂) :
    Qsag.Spec.ValidAggregateWitness verifySingle ⟨roster, bmL ||| bmR, msg⟩
      (Qsag.Spec.mergeWitnessMaps bmL wL wR) ∧
    Qsag.Composed.weight tree.bitmap = (tree.leaves.map fun s => Qsag.Composed.weight s.bitmap).sum ∧
    tree.leaves.length ≤ 2 ^ depth ∧
    Qsag.runDecodedWordsWaveWithObs words cfg subvecIdx prog fuel m₁ =
      Qsag.runDecodedWordsWaveWithObs words cfg subvecIdx prog fuel m₂ := by
  obtain ⟨hWt, _, _, hLeaves⟩ := Qsag.Composed.binary_merge_sound rootHdr verifyShard tree depth hTreeOk
  exact ⟨Qsag.Spec.mergeWitnessMaps_valid verifySingle roster msg bmL bmR wL wR hWitL hWitR,
         hWt, hLeaves,
         Qsag.decoded_spirv_words_simt_ct_noninterference hCt cfg subvecIdx fuel hMem⟩

/-! ## 5. Multifold `[CWYZ26]` + Salted-Merkle DFMS QROM State Restoration + Committee Boundary -/

/-- **Multifold `HEM` `nv = 24` Salted-Merkle QROM State-Restoration & Deployed Committee Quorum Reduction
    (`multifold_salted_qrom_and_committee_boundary_chain`)**:
    Composes `HemSlicedFoldBudget.dfm184_budget_at_2pow27`, `Cwyz26EqualDegreeAndMultiFold.sliced_multifold_stage_supported_budget`,
    `QromSaltedMerkleStateRestoration` (`hemNv24_unitaryPow16_sound_up_to_2pow40`, `dfms_database_overflow_mass_zero`),
    and `CompositionInstances.boundary_of_hem_opening_batch` + `Composed.merged_quorum_reduction`
    parameterized over deployed `xmssPoseidon2Geom` / `corduroyPoseidon2Geom` (`wotsChains = 128`) and
    any non-vacuous QROM/IOP opening-batch failure predicate `bad : Shard nVal → Prop`! -/
theorem multifold_salted_qrom_and_committee_boundary_chain
    {n cardAnc nVal cardX w : Nat}
    (Q_pow : Nat) (hQPow : Q_pow + 1 ≤ 2 ^ 40)
    (Q_dfm : Nat) (hQDfm : Q_dfm + 1 ≤ 2 ^ 27)
    (nvMf : Nat) (h2Mf : 2 ≤ nvMf) (h24Mf : nvMf ≤ 24)
    (gMf : Qsag.HemStageGeom) (hgMf : gMf ∈ Qsag.hemStageGeoms nvMf)
    (hneMf : Qsag.hemJohnsonQromStageExhaustive gMf = false)
    (bStage : Qsag.RatBound) (hb184 : Qsag.atLeastBits 184 bStage)
    (ADfms : Qsag.QuantumAdv n 256 cardAnc Q_pow)
    (geom : Qsag.AggSigGeometry)
    (hDeployedGeom : geom = Qsag.xmssPoseidon2Geom ∨ geom = Qsag.corduroyPoseidon2Geom)
    (custody : Fin nVal → Qsag.Composed.Custody)
    (bad : Qsag.Composed.Shard nVal → Prop)
    (L : Qsag.MerkleAddressLayout cardX w)
    (slots : List (Qsag.MerkleOpeningSlot cardX w))
    (hemInst : Qsag.Composed.Shard nVal → Qsag.HemWhirInstance Qsag.QuarticGoldilocks)
    (decode : Qsag.Composed.Shard nVal → Fin cardX → List (Option (Qsag.MerkleOpeningValue w)) →
      List (Qsag.HemTranscriptRound Qsag.QuarticGoldilocks))
    (oracleOf : Qsag.Composed.Shard nVal → Fin cardX → BitVec w)
    (outOf : Qsag.Composed.Shard nVal → Fin cardX)
    (modeOk : Qsag.Composed.Shard nVal → Bool)
    (stmt : Qsag.Composed.Shard nVal → Qsag.AggArithPublicStmt)
    (slot : Fin nVal → Nat)
    (hHemSound : ∀ s,
      Qsag.verifyHemOpeningBatch L slots (hemInst s) (decode s) (oracleOf s) (outOf s) = true →
      modeOk s = true →
      bad s ∨ Qsag.HemStatementValid (hemInst s))
    (hHemToTrace : ∀ s, Qsag.HemStatementValid (hemInst s) → modeOk s = true →
      ∃ tr, Qsag.traceSatisfiesAllConstraints (stmt s) tr = true)
    (hBinds : ∀ s, modeOk s = true → (stmt s).geom = geom ∧
      ∀ v : Fin nVal, s.bitmap.getLsbD v.val = true →
        (stmt s).committeePks[slot v]? = some (custody v).state.pk ∧
        (stmt s).msg = s.header.mode.message v.val) :
    let hemVerifyShard := fun s =>
      Qsag.verifyHemOpeningBatch L slots (hemInst s) (decode s) (oracleOf s) (outOf s) && modeOk s
    geom.wellFormed = true ∧
    (Qsag.Spec.RatBound.ofBudget
      (Qsag.powScaledFsQromCompilerBound Q_pow 5 256 16
        Qsag.hemV6FiveRoundRbrBounds
        (Qsag.hemOptimizedQueryBounds .unitaryPow16 24))).atLeastBits 128 ∧
    (∃ (r : Nat × Nat × Nat × Nat × Nat) (wRow : Nat × Nat × Nat × Nat),
      Qsag.hemJohnsonQromTableRow nvMf gMf.stageIdx = some r ∧
      Qsag.slicedStageRow nvMf gMf.stageIdx = some wRow ∧
      (Qsag.Spec.RatBound.ofBudget (Qsag.slicedMultiFoldStageBound gMf r wRow)).atLeastBits 175) ∧
    (Qsag.Spec.RatBound.ofBudget (Qsag.dfmRoundScale Q_dfm bStage)).atLeastBits 128 ∧
    Qsag.dfmsTableSum 128 n (fun D => if Q_pow < Qsag.dfmsRecordedCount n D then
      Qsag.QVec.stateNormSq (Qsag.dfmsAdvStateAt 128 ADfms Q_pow (Nat.le_refl Q_pow) D) else 0) = 0 ∧
    Qsag.Composed.ExtractionBoundary geom custody hemVerifyShard bad ∧
    (∀ (rootHdr : Qsag.Composed.Header) (tree : Qsag.Composed.MergeTree nVal) (v : Fin nVal),
      Qsag.Composed.checkTree rootHdr hemVerifyShard 16 tree = true →
      tree.bitmap.getLsbD v.val = true →
      (∃ s ∈ tree.leaves, bad s) ∨
      Qsag.Composed.QuorumForgery geom (custody v) (rootHdr.mode.message v.val) ∨
      Qsag.Composed.quorumParticipated (custody v) (rootHdr.mode.message v.val) = true) := by
  intro hemVerifyShard
  have hGeomWf : geom.wellFormed = true := by
    rcases hDeployedGeom with rfl | rfl
    · exact Qsag.deployedAggGeometries_wellFormed.1
    · exact Qsag.deployedAggGeometries_wellFormed.2.1
  obtain ⟨_, hPow128⟩ := Qsag.hemNv24_unitaryPow16_sound_up_to_2pow40 Q_pow hQPow
  obtain ⟨rMf, wMf, hrMf, hwMf, _, _, _, hb175, _, _⟩ :=
    Qsag.sliced_multifold_stage_supported_budget nvMf h2Mf h24Mf gMf hgMf hneMf
  have hDfm128 := Qsag.dfm184_budget_at_2pow27 bStage hb184 Q_dfm hQDfm
  have hBnd : Qsag.Composed.ExtractionBoundary geom custody hemVerifyShard bad :=
    Qsag.CompositionInstances.boundary_of_hem_opening_batch geom custody bad L slots
      hemInst decode oracleOf outOf modeOk stmt slot hHemSound hHemToTrace hBinds
  exact ⟨hGeomWf,
         (Qsag.Spec.RatBound.ofBudget_atLeastBits_iff 128 _).mpr hPow128,
         ⟨rMf, wMf, hrMf, hwMf, (Qsag.Spec.RatBound.ofBudget_atLeastBits_iff 175 _).mpr hb175⟩,
         (Qsag.Spec.RatBound.ofBudget_atLeastBits_iff 128 _).mpr hDfm128,
         Qsag.dfms_database_overflow_mass_zero 128 ADfms,
         hBnd,
         fun rootHdr tree v hTree hAct =>
           Qsag.Composed.merged_quorum_reduction geom custody hemVerifyShard bad hBnd
             rootHdr tree hTree v hAct⟩

/-! ## 6. `Spec.AggregateExtractorSound` for the Native Verifier and the Quorum Layer -/

/-- The base prime of the production aggregation profile is the Goldilocks prime of
    `Qsag.Math.Primality`. -/
theorem hemGoldilocksExt4Profile_basePrime_eq_goldilocksPrime :
    Qsag.Spec.hemGoldilocksExt4Profile.basePrime = Qsag.goldilocksPrime := by
  rfl

/-- **Accepted aggregate ⟹ validated break, quorum forgery, or quorum participation.**
    Let `C` be a knowledge-soundness contract (`Spec.AggregateExtractorSound`) for an aggregate
    verifier `verifyAgg` over individual signatures checked by `verifyAggNativeSig geom`, with
    commitment hash `H`. On a coin `ω` whose statement lists the enrolled custody keys, where
    `verifyAgg` accepts and the soundness-error event of `C` does not occur, every active
    validator `v` satisfies one of:
    1. the break finder of `C` returned a collision of `H` (`Spec.ValidBreak`),
    2. some native signature verifies under `v`'s key on the statement's message although the
       quorum of `v` did not participate (the content of `Composed.QuorumForgery`),
    3. the quorum of `v` participated.

    Open obligation: `C` for the deployed verifier. Its fields are the extractor, the break
    finder, the soundness-error event and the bound `εSound` on that event. -/
theorem aggregate_extractor_sound_quorum_reduction
    {Proof View : Type} {nVal n : Nat}
    (geom : Qsag.AggSigGeometry) (custody : Fin nVal → Qsag.Composed.Custody)
    (H : Qsag.Spec.Bytes → Qsag.Spec.Bytes)
    (verifyAgg : Qsag.Spec.AggregateStatement Qsag.AggValidatorPk nVal → Proof → Bool)
    (run : Fin n → Qsag.Spec.AggregateRun Qsag.AggValidatorPk Proof View nVal)
    (C : Qsag.Spec.AggregateExtractorSound (Qsag.verifyAggNativeSig geom) H verifyAgg run)
    (ω : Fin n)
    (hRoster : ∀ v : Fin nVal, (run ω).stmt.roster v = (custody v).state.pk)
    (hAcc : verifyAgg (run ω).stmt (run ω).proof = true) (hGood : C.bad ω = false)
    (v : Fin nVal) (hActive : (run ω).stmt.bitmap.getLsbD v.val = true) :
    (∃ b : Qsag.Spec.AggregateBreak,
      C.findBreak (run ω).view = some b ∧ Qsag.Spec.ValidBreak H b) ∨
    (∃ sig : Qsag.AggNativeSignature,
      Qsag.verifyAggNativeSig geom (custody v).state.pk (run ω).stmt.message sig = true ∧
      Qsag.Composed.quorumParticipated (custody v) (run ω).stmt.message = false) ∨
    Qsag.Composed.quorumParticipated (custody v) (run ω).stmt.message = true := by
  have h := C.accepted_signer_trichotomy
    (fun u => Qsag.Composed.quorumParticipated (custody u) (run ω).stmt.message)
    ω hAcc hGood v hActive
  rcases h with hB | ⟨sig, hSig, hNo⟩ | hYes
  · exact .inl hB
  · refine .inr (.inl ⟨sig, ?_, hNo⟩)
    rw [← hRoster v]
    exact hSig
  · exact .inr (.inr hYes)

/-- With an injective commitment hash the first alternative is empty: an accepted aggregate
    outside the soundness-error event extracts a valid individual signature for every active
    validator. -/
theorem aggregate_extractor_sound_valid_witness_of_injective
    {Proof View : Type} {nVal n : Nat}
    (geom : Qsag.AggSigGeometry)
    (H : Qsag.Spec.Bytes → Qsag.Spec.Bytes)
    (verifyAgg : Qsag.Spec.AggregateStatement Qsag.AggValidatorPk nVal → Proof → Bool)
    (run : Fin n → Qsag.Spec.AggregateRun Qsag.AggValidatorPk Proof View nVal)
    (C : Qsag.Spec.AggregateExtractorSound (Qsag.verifyAggNativeSig geom) H verifyAgg run)
    (hInj : ∀ a b : Qsag.Spec.Bytes, H a = H b → a = b) (ω : Fin n)
    (hAcc : verifyAgg (run ω).stmt (run ω).proof = true) (hGood : C.bad ω = false) :
    Qsag.Spec.ValidAggregateWitness (Qsag.verifyAggNativeSig geom) (run ω).stmt
      (C.extract (run ω).view) :=
  C.accepted_extracts_of_injective hInj ω hAcc hGood

#verify_constructive
  Qsag.Top.hemGoldilocksExt4Profile_basePrime_eq_goldilocksPrime
  Qsag.Top.aggregate_extractor_sound_quorum_reduction
  Qsag.Top.aggregate_extractor_sound_valid_witness_of_injective
  Qsag.Top.aggExt4_cwyz26_fold_and_point_reduction
  Qsag.Top.deployed_hem_stage_budget_and_aggExt4_transport
  Qsag.Top.qrom_hem_opening_and_invalid_coordinate_chain
  Qsag.Top.aggregate_merge_and_simt_gpu_noninterference
  Qsag.Top.multifold_salted_qrom_and_committee_boundary_chain

end Qsag.Top
end
