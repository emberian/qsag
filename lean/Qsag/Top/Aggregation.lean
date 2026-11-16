module
public import Qsag.Protocol.Aggregation.HemCommitteeBoundary
public import Qsag.Protocol.Aggregation.HemHighCapSlicedBudget
public import Qsag.Protocol.Aggregation.HemMultistageCascadeRbr
public import Qsag.Protocol.Aggregation.RecursivePoseidon2WhirSoundness
public import Qsag.Protocol.Aggregation.ZkHem
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
quorum layer of `ComposedQsAgAndMergeSecurity`. For an aggregate verifier over native signatures
that satisfies the contract with error `ε` and an extractor of a class `ℰ`, against every oracle
prover the probability of an accepted aggregate over the custody roster that names an active
validator for which there is neither a collision of the oracle among the prover's queries
(`Spec.TranscriptBreak`), nor a verifying signature in the extractor's output for that validator,
nor quorum participation, is at most `ε`. Runs whose extractor output is a verifying signature
of a non-participating validator are not bounded here: that is single-signature unforgeability.
The contract for the deployed verifier is a hypothesis; no instance is constructed.
-/

public import Qsag.Protocol.Aggregation.FieldTransport
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
public import Qsag.Protocol.Aggregation.HemOpening
public import Qsag.Protocol.Aggregation.HemRbrSoundness
public import Qsag.Oracle.Qrom
public import Qsag.Protocol.Aggregation.QromSaltedMerkleStateRestoration
public import Qsag.Protocol.Aggregation.ComposedQsAgAndMergeSecurity
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

/-- **Accepted aggregate, per validator (one run).** For an aggregate verifier `verifyAgg`
    over individual signatures checked by `verifyAggNativeSig geom`, an oracle `H` and a prover
    with query budget `q`: on a run whose statement lists the enrolled custody keys, where
    `verifyAgg` accepts and the prover does not win the knowledge-soundness game
    (`Spec.aggregateFailure … = false`), every active validator `v` satisfies one of:
    1. two different recorded queries of the prover collide under `H` (`Spec.TranscriptBreak`),
    2. the extractor's output for `v` on this run is a native signature that verifies under
       `v`'s key on the statement's message although the quorum of `v` did not participate,
    3. the quorum of `v` participated. -/
theorem aggregate_extractor_sound_quorum_reduction
    {Proof : Type} {nVal : Nat}
    (geom : Qsag.AggSigGeometry) (custody : Fin nVal → Qsag.Composed.Custody)
    (verifyAgg : (Qsag.Spec.Bytes → Qsag.Spec.Bytes) →
      Qsag.Spec.AggregateStatement Qsag.AggValidatorPk nVal → Proof → Bool)
    (extract : List (Qsag.Spec.Bytes × Qsag.Spec.Bytes) →
      Qsag.Spec.AggregateStatement Qsag.AggValidatorPk nVal → Proof →
      Fin nVal → Option Qsag.AggNativeSignature)
    (H : Qsag.Spec.Bytes → Qsag.Spec.Bytes) (q : Nat)
    (prover : Qsag.Spec.Code Qsag.Spec.byteOracleIface
      (Qsag.Spec.AggregateStatement Qsag.AggValidatorPk nVal × Proof))
    (hRoster : ∀ v : Fin nVal,
      (Qsag.Spec.aggregateRun H q prover).1.1.roster v = (custody v).state.pk)
    (hAcc : verifyAgg H (Qsag.Spec.aggregateRun H q prover).1.1
      (Qsag.Spec.aggregateRun H q prover).1.2 = true)
    (hLose : Qsag.Spec.aggregateFailure (Qsag.verifyAggNativeSig geom) verifyAgg extract H
      (Qsag.Spec.aggregateRun H q prover) = false)
    (v : Fin nVal)
    (hActive : (Qsag.Spec.aggregateRun H q prover).1.1.bitmap.getLsbD v.val = true) :
    (∃ b : Qsag.Spec.AggregateBreak,
      Qsag.Spec.TranscriptBreak H (Qsag.Spec.aggregateRun H q prover).2 b) ∨
    (∃ sig : Qsag.AggNativeSignature,
      extract (Qsag.Spec.aggregateRun H q prover).2 (Qsag.Spec.aggregateRun H q prover).1.1
        (Qsag.Spec.aggregateRun H q prover).1.2 v = some sig ∧
      Qsag.verifyAggNativeSig geom (custody v).state.pk
        (Qsag.Spec.aggregateRun H q prover).1.1.message sig = true ∧
      Qsag.Composed.quorumParticipated (custody v)
        (Qsag.Spec.aggregateRun H q prover).1.1.message = false) ∨
    Qsag.Composed.quorumParticipated (custody v)
      (Qsag.Spec.aggregateRun H q prover).1.1.message = true := by
  have h := (Qsag.Spec.aggregateFailure_false_outcome (Qsag.verifyAggNativeSig geom) verifyAgg
    extract H q prover hLose hAcc).signer_trichotomy
    (fun u => Qsag.Composed.quorumParticipated (custody u)
      (Qsag.Spec.aggregateRun H q prover).1.1.message) v hActive
  rcases h with hB | ⟨sig, hEx, hSig, hNo⟩ | hYes
  · exact .inl hB
  · refine .inr (.inl ⟨sig, hEx, ?_, hNo⟩)
    rw [← hRoster v]
    exact hSig
  · exact .inr (.inr hYes)

/-- **Quorum soundness bound.** Let `verifyAgg` with extractor `extract` of the class `ℰ`
    satisfy `Spec.AggregateExtractorSound` for the oracle family `oracle`, query budget `q` and
    error `ε`. For every prover on the adversary coordinate of a coin split, any event
    contained in

    * the statement lists the enrolled custody keys and `verifyAgg` accepts, and
    * some active validator `v` has no transcript collision, its quorum did not participate,
      and the extractor's output for `v` on the run is not a signature verifying under its key

    has probability at most `ε`. The event concerns the signature the extractor produced from
    the run, so it is not emptied by the existence of verifying signatures.

    This is not unforgeability of the aggregate: a run whose extractor output is a verifying
    signature of a non-participating validator is outside the event, and bounding such runs is
    single-signature unforgeability, which is not used here. The statement has content for a
    class `ℰ` such as `Spec.StraightLineExtractor`; with the unrestricted class the contract
    can hold for a verifier that checks nothing
    (`Spec.acceptAll_alwaysValid_unrestricted_extractorSound`).

    Open obligation: the contract `C` for the deployed verifier, i.e. an extractor of the class
    reading only the prover's oracle transcript, the statement and the proof, and the bound
    `ε`. -/
theorem aggregate_extractor_sound_quorum_bound
    {Proof : Type} {nVal nC n nA : Nat}
    (geom : Qsag.AggSigGeometry) (custody : Fin nVal → Qsag.Composed.Custody)
    (verifyAgg : (Qsag.Spec.Bytes → Qsag.Spec.Bytes) →
      Qsag.Spec.AggregateStatement Qsag.AggValidatorPk nVal → Proof → Bool)
    (extract : List (Qsag.Spec.Bytes × Qsag.Spec.Bytes) →
      Qsag.Spec.AggregateStatement Qsag.AggValidatorPk nVal → Proof →
      Fin nVal → Option Qsag.AggNativeSignature)
    (oracle : Fin nC → Qsag.Spec.Bytes → Qsag.Spec.Bytes) (q : Nat) (ε : Qsag.Spec.RatBound)
    {ℰ : (List (Qsag.Spec.Bytes × Qsag.Spec.Bytes) →
      Qsag.Spec.AggregateStatement Qsag.AggValidatorPk nVal → Proof →
      Fin nVal → Option Qsag.AggNativeSignature) → Prop}
    (C : Qsag.Spec.AggregateExtractorSound ℰ (Qsag.verifyAggNativeSig geom) verifyAgg extract
      oracle q ε)
    (hPos : 0 < n) (π : Qsag.Spec.CoinSplit n nC nA)
    (prover : Fin nA → Qsag.Spec.Code Qsag.Spec.byteOracleIface
      (Qsag.Spec.AggregateStatement Qsag.AggValidatorPk nVal × Proof))
    (fail : Fin n → Bool)
    (hFail : ∀ ω : Fin n, fail ω = true →
      (∀ v : Fin nVal,
        (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.1.roster v =
          (custody v).state.pk) ∧
      verifyAgg (oracle (π.chal ω))
        (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.1
        (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.2 = true ∧
      ∃ v : Fin nVal,
        (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q
          (prover (π.advc ω))).1.1.bitmap.getLsbD v.val = true ∧
        ¬ ((∃ b : Qsag.Spec.AggregateBreak,
            Qsag.Spec.TranscriptBreak (oracle (π.chal ω))
              (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).2 b) ∨
          (∃ sig : Qsag.AggNativeSignature,
            extract (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).2
              (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.1
              (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.2 v =
                some sig ∧
            Qsag.verifyAggNativeSig geom (custody v).state.pk
              (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q
                (prover (π.advc ω))).1.1.message sig = true ∧
            Qsag.Composed.quorumParticipated (custody v)
              (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q
                (prover (π.advc ω))).1.1.message = false) ∨
          Qsag.Composed.quorumParticipated (custody v)
            (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q
              (prover (π.advc ω))).1.1.message = true)) :
    Qsag.Spec.GameBound (Qsag.Spec.FinGame.mk hPos fail).winProb ε :=
  C.failure_bound hPos π prover fail (fun ω hF => by
    obtain ⟨hRoster, hAcc, v, hActive, hNone⟩ := hFail ω hF
    refine ⟨hAcc, fun hOut => hNone ?_⟩
    rcases hOut.signer_trichotomy
      (fun u => Qsag.Composed.quorumParticipated (custody u)
        (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.1.message)
      v hActive with hB | ⟨sig, hEx, hSig, hNo⟩ | hYes
    · exact .inl hB
    · refine .inr (.inl ⟨sig, hEx, ?_, hNo⟩)
      rw [← hRoster v]
      exact hSig
    · exact .inr (.inr hYes))

/-- **Extraction bound for an injective oracle.** If every oracle of the family is injective,
    no transcript collision exists, and the contract bounds the probability that the verifier
    accepts while the extracted witness map is not a valid individual signature for every
    active validator. -/
theorem aggregate_extractor_sound_valid_witness_of_injective
    {Proof : Type} {nVal nC n nA : Nat}
    (geom : Qsag.AggSigGeometry)
    (verifyAgg : (Qsag.Spec.Bytes → Qsag.Spec.Bytes) →
      Qsag.Spec.AggregateStatement Qsag.AggValidatorPk nVal → Proof → Bool)
    (extract : List (Qsag.Spec.Bytes × Qsag.Spec.Bytes) →
      Qsag.Spec.AggregateStatement Qsag.AggValidatorPk nVal → Proof →
      Fin nVal → Option Qsag.AggNativeSignature)
    (oracle : Fin nC → Qsag.Spec.Bytes → Qsag.Spec.Bytes) (q : Nat) (ε : Qsag.Spec.RatBound)
    {ℰ : (List (Qsag.Spec.Bytes × Qsag.Spec.Bytes) →
      Qsag.Spec.AggregateStatement Qsag.AggValidatorPk nVal → Proof →
      Fin nVal → Option Qsag.AggNativeSignature) → Prop}
    (C : Qsag.Spec.AggregateExtractorSound ℰ (Qsag.verifyAggNativeSig geom) verifyAgg extract
      oracle q ε)
    (hInj : ∀ (c : Fin nC) (a b : Qsag.Spec.Bytes), oracle c a = oracle c b → a = b)
    (hPos : 0 < n) (π : Qsag.Spec.CoinSplit n nC nA)
    (prover : Fin nA → Qsag.Spec.Code Qsag.Spec.byteOracleIface
      (Qsag.Spec.AggregateStatement Qsag.AggValidatorPk nVal × Proof))
    (fail : Fin n → Bool)
    (hFail : ∀ ω : Fin n, fail ω = true →
      verifyAgg (oracle (π.chal ω))
        (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.1
        (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.2 = true ∧
      ¬ Qsag.Spec.ValidAggregateWitness (Qsag.verifyAggNativeSig geom)
        (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.1
        (extract (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).2
          (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.1
          (Qsag.Spec.aggregateRun (oracle (π.chal ω)) q (prover (π.advc ω))).1.2)) :
    Qsag.Spec.GameBound (Qsag.Spec.FinGame.mk hPos fail).winProb ε :=
  C.failure_bound hPos π prover fail (fun ω hF =>
    ⟨(hFail ω hF).1, fun hOut =>
      (hFail ω hF).2 (hOut.witness_of_injective (hInj (π.chal ω)))⟩)

#verify_constructive
  Qsag.Top.hemGoldilocksExt4Profile_basePrime_eq_goldilocksPrime
  Qsag.Top.aggregate_extractor_sound_quorum_reduction
  Qsag.Top.aggregate_extractor_sound_quorum_bound
  Qsag.Top.aggregate_extractor_sound_valid_witness_of_injective
  Qsag.Top.aggExt4_cwyz26_fold_and_point_reduction
  Qsag.Top.deployed_hem_stage_budget_and_aggExt4_transport
  Qsag.Top.qrom_hem_opening_and_invalid_coordinate_chain
  Qsag.Top.aggregate_merge_and_simt_gpu_noninterference
  Qsag.Top.multifold_salted_qrom_and_committee_boundary_chain

open Qsag

open CommRingOps
open Qsag.Aggregation

-- BEGIN COMPARATOR ROSTER
theorem goldilocksReduce128Spec_sound {lo hi : Nat}
    (hLo : lo < 2 ^ 64) (hHi : hi < 2 ^ 64) :
    goldilocksReduce128Spec lo hi < goldilocksPrime ∧
    goldilocksReduce128Spec lo hi = (lo + 2 ^ 64 * hi) % goldilocksPrime :=
  _root_.Qsag.goldilocksReduce128Spec_sound hLo hHi

theorem Goldilocks_mul_inv_cancel {a : Goldilocks} (ha : a ≠ Goldilocks.zero) :
    CommRingOps.mul a (Goldilocks.inv a) = CommRingOps.one :=
  _root_.Qsag.Goldilocks.mul_inv_cancel ha

theorem towerMul_cancel_left (k : Nat) (a b c : TowerElem k)
    (ha : a ≠ towerZero k) (h : towerMul k a b = towerMul k a c) : b = c :=
  _root_.Qsag.towerMul_cancel_left k a b c ha h

theorem ghashDiff_roots_bound (bs₁ bs₂ : List Tower128) (L : Nat) (keys : List Tower128)
    (h₁ : bs₁.length ≤ L) (h₂ : bs₂.length ≤ L) (hnd : keys.Nodup)
    (hne : ∃ H, ghashPoly H bs₁ ≠ ghashPoly H bs₂)
    (heq : ∀ H ∈ keys, ghashPoly H bs₁ = ghashPoly H bs₂) : keys.length ≤ L :=
  _root_.Qsag.ghashDiff_roots_bound bs₁ bs₂ L keys h₁ h₂ hnd hne heq

theorem packTowerLenBlock_injective {a₁ c₁ a₂ c₂ : UInt64}
    (h : packTowerLenBlock a₁ c₁ = packTowerLenBlock a₂ c₂) : a₁ = a₂ ∧ c₁ = c₂ :=
  _root_.Qsag.packTowerLenBlock_injective h

theorem be_injective {w n m : Nat} (hn : n < 256 ^ w) (hm : m < 256 ^ w)
    (h : be w n = be w m) : n = m :=
  _root_.Qsag.be_injective hn hm h

theorem encodeMultiFrame_injective {xs ys : List (List UInt8)}
    (h : encodeMultiFrame xs = encodeMultiFrame ys) : xs = ys :=
  _root_.Qsag.encodeMultiFrame_injective h

theorem chiWordBit_eq_keccakChiBit (w0 w1 w2 : UInt64) (i : Nat) (hi : i < 64) :
    (w0 ^^^ ((~~~w1) &&& w2)).toBitVec.getLsbD i =
      keccakChiBit (w0.toBitVec.getLsbD i) (w1.toBitVec.getLsbD i) (w2.toBitVec.getLsbD i) :=
  _root_.Qsag.chiWordBit_eq_keccakChiBit w0 w1 w2 i hi

theorem cshake256Xof_empty_eq_shake256Xof (outLen : Nat) (input : List UInt8) :
    cshake256Xof outLen [] input = shake256Xof outLen input :=
  _root_.Qsag.cshake256Xof_empty_eq_shake256Xof outLen input

theorem poseidon2Perm12Inv_left_inv (st : Poseidon2State12) :
    poseidon2Perm12Inv (poseidon2Perm12 st) = st :=
  _root_.Qsag.poseidon2Perm12Inv_left_inv st

theorem poseidon2Perm12Inv_right_inv (st : Poseidon2State12) :
    poseidon2Perm12 (poseidon2Perm12Inv st) = st :=
  _root_.Qsag.poseidon2Perm12Inv_right_inv st

theorem bytesToLimbs56_injective {m₁ m₂ : List UInt8}
    (h : bytesToLimbs56 m₁ = bytesToLimbs56 m₂) : m₁ = m₂ :=
  _root_.Qsag.bytesToLimbs56_injective h

theorem popcount_union_disjoint_eq_add :
    ∀ (b1 b2 : SignerBitmapSpec),
      b1.length = b2.length →
      bitmapDisjointSpec b1 b2 = true →
      bitmapPopcountSpec (bitmapUnionSpec b1 b2) =
        bitmapPopcountSpec b1 + bitmapPopcountSpec b2 :=
  _root_.Qsag.popcount_union_disjoint_eq_add

open Aggregation in
theorem goldilocksExt4_mul_inv_cancel {z : Aggregation.GoldilocksExt4} (hz : z ≠ Aggregation.GoldilocksExt4.zero) :
    CommRingOps.mul z (Aggregation.GoldilocksExt4.inv z) = CommRingOps.one :=
  _root_.Qsag.Aggregation.goldilocksExt4_mul_inv_cancel hz

open Aggregation in
theorem goldilocksExt4_encodeBytes32_injective {x y : Aggregation.GoldilocksExt4}
    (h : Aggregation.GoldilocksExt4.encodeBytes32 x = Aggregation.GoldilocksExt4.encodeBytes32 y) : x = y :=
  _root_.Qsag.Aggregation.goldilocksExt4_encodeBytes32_injective h

open Aggregation in
theorem sumcheck_degree8_ext4_roots_le_eight
    (claimedPoly honestPoly : List Aggregation.GoldilocksExt4) (S : List Aggregation.GoldilocksExt4)
    (hNodup : S.Nodup)
    (hLenC : claimedPoly.length ≤ 9) (hLenH : honestPoly.length ≤ 9)
    (hDiff : ∃ x₀ : Aggregation.GoldilocksExt4,
      RoundPoly.evalCoeffs claimedPoly x₀ ≠ RoundPoly.evalCoeffs honestPoly x₀) :
    (S.filter (fun r =>
      decide (RoundPoly.evalCoeffs claimedPoly r = RoundPoly.evalCoeffs honestPoly r))).length ≤ 8 :=
  _root_.Qsag.Aggregation.sumcheck_degree8_ext4_roots_le_eight claimedPoly honestPoly S hNodup hLenC hLenH hDiff

open Aggregation in
theorem whir_ood_pin_roots_le_degree (d : Nat)
    (candA candB : List Aggregation.GoldilocksExt4) (S : List Aggregation.GoldilocksExt4)
    (hNodup : S.Nodup)
    (hLenA : candA.length ≤ d + 1) (hLenB : candB.length ≤ d + 1)
    (hDiff : ∃ z₀ : Aggregation.GoldilocksExt4,
      RoundPoly.evalCoeffs candA z₀ ≠ RoundPoly.evalCoeffs candB z₀) :
    (S.filter (fun z =>
      decide (RoundPoly.evalCoeffs candA z = RoundPoly.evalCoeffs candB z))).length ≤ d :=
  _root_.Qsag.Aggregation.whir_ood_pin_roots_le_degree d candA candB S hNodup hLenA hLenB hDiff

open Aggregation in
theorem aggregateInstanceFrame_injective (first second : AggPublicInstance)
    (a b : AggregatedSignature)
    (h : aggregateInstanceFrame first a = aggregateInstanceFrame second b) :
    first.message = second.message ∧
    first.signingModeDigest = second.signingModeDigest ∧
    first.regime = second.regime ∧
    first.suite.suiteId = second.suite.suiteId ∧
    first.committee = second.committee ∧
    first.params = second.params ∧
    a.bitmap = b.bitmap ∧
    a.traceCommitment = b.traceCommitment ∧
    a.childrenCommitment = b.childrenCommitment :=
  _root_.Qsag.Aggregation.aggregateInstanceFrame_injective first second a b h

open Aggregation in
theorem bciksJohnsonQrom128_positive_slack :
    ∀ s ∈ Aggregation.whirSchedule4Stage .bciksJohnsonQrom128,
      2 ^ 256 < s.johnsonSqrtBlowup ^ s.numQueries ∧
      (1024 / s.johnsonSqrtBlowup + 1) ^ s.numQueries * 2 ^ 256 < 1024 ^ s.numQueries :=
  _root_.Qsag.Aggregation.bciksJohnsonQrom128_positive_slack

open Aggregation in
theorem bciksJohnson_schedules_eq_minimum_queries :
    (Aggregation.whirSchedule4Stage .bciksJohnsonClassical128).map (·.numQueries) =
      [2, 4, 6, 8].map (fun logB => (256 + logB - 1) / logB + 1) ∧
    (Aggregation.whirSchedule4Stage .bciksJohnsonQrom128).map (·.numQueries) =
      [2, 4, 6, 8].map (fun logB => (512 + logB - 1) / logB + 2) ∧
    (Aggregation.whirSchedule4Stage .bciksJohnsonQrom128).map (·.blowup) = [2, 4, 6, 8].map (2 ^ ·) :=
  _root_.Qsag.Aggregation.bciksJohnson_schedules_eq_minimum_queries

theorem productionAggParams_queries_match_schedule :
    productionAggParams.classicalJohnsonQueries =
      (Aggregation.whirSchedule4Stage .bciksJohnsonClassical128).map (·.numQueries) ∧
    productionAggParams.defaultQromQueries =
      (Aggregation.whirSchedule4Stage .bciksJohnsonQrom128).map (·.numQueries) ∧
    productionAggParams.johnsonQromQueries =
      (Aggregation.whirSchedule4Stage .bciksJohnsonQrom128).map (·.numQueries) ∧
    (∀ r : Aggregation.WhirSecurityRegime, ∀ s ∈ Aggregation.whirSchedule4Stage r,
      s.numQueries ≤ productionAggParams.maxQueryCap) :=
  _root_.Qsag.productionAggParams_queries_match_schedule

theorem whir_query_miss_bound {α : Type} (bad : α → Bool) (dom : List α) (q dn dd : Nat)
    (hfar : dn * dom.length ≤ dd * countGood bad dom) :
    ((aggDistinctTuples q dom).filter (fun t => t.all (fun x => !bad x))).length * dd ^ q ≤
      (dd - dn) ^ q * (aggDistinctTuples q dom).length :=
  _root_.Qsag.whir_query_miss_bound bad dom q dn dd hfar

open Aggregation in
theorem whir_bciksJohnsonQrom128_query_miss_lt {α : Type}
    (s : Aggregation.WhirStageSpec) (hs : s ∈ Aggregation.whirSchedule4Stage .bciksJohnsonQrom128)
    (bad : α → Bool) (dom : List α)
    (hdom : s.numQueries ≤ dom.length)
    (hfar : (1024 - (1024 / s.johnsonSqrtBlowup + 1)) * dom.length ≤ 1024 * countGood bad dom) :
    ((aggDistinctTuples s.numQueries dom).filter (fun t => t.all (fun x => !bad x))).length *
      2 ^ 256 < (aggDistinctTuples s.numQueries dom).length :=
  _root_.Qsag.Aggregation.whir_bciksJohnsonQrom128_query_miss_lt s hs bad dom hdom hfar

open Aggregation in
theorem whir_bciksJohnsonClassical128_total_error_bound {β : Type}
    (S : List Aggregation.GoldilocksExt4) (n : Nat) (hn : 0 < n)
    (E : List Aggregation.GoldilocksExt4 → Aggregation.GoldilocksExt4 → Bool) (d : Nat → Nat)
    (hE : ∀ pre, (S.filter (E pre)).length ≤ d pre.length)
    (hBudget : roundBoundSum d n ≤ productionExt4RoundEventBudget)
    (hField : productionAggParams.fieldSize ≤ S.length)
    (dom : List β) (hdom : 129 ≤ dom.length)
    (bad : List Aggregation.GoldilocksExt4 → β → Bool)
    (hfar : ∀ cs ∈ challengeVectors S n, anyRoundEvent E cs = false →
      (512 - 257) * dom.length ≤ 512 * countGood (bad cs) dom) :
    (badTranscriptPairs S n E dom 129 bad).length * 2 ^ 127 <
      S.length ^ n * (aggDistinctTuples 129 dom).length :=
  _root_.Qsag.Aggregation.whir_bciksJohnsonClassical128_total_error_bound S n hn E d hE hBudget hField dom hdom bad hfar

open Aggregation in
theorem whir_bciksJohnsonQrom128_total_error_bound {β : Type}
    (s : Aggregation.WhirStageSpec) (hs : s ∈ Aggregation.whirSchedule4Stage .bciksJohnsonQrom128)
    (S : List Aggregation.GoldilocksExt4) (n : Nat) (hn : 0 < n)
    (E : List Aggregation.GoldilocksExt4 → Aggregation.GoldilocksExt4 → Bool) (d : Nat → Nat)
    (hE : ∀ pre, (S.filter (E pre)).length ≤ d pre.length)
    (hBudget : roundBoundSum d n ≤ productionExt4RoundEventBudget)
    (hField : productionAggParams.fieldSize ≤ S.length)
    (dom : List β) (hdom : s.numQueries ≤ dom.length)
    (bad : List Aggregation.GoldilocksExt4 → β → Bool)
    (hfar : ∀ cs ∈ challengeVectors S n, anyRoundEvent E cs = false →
      (1024 - (1024 / s.johnsonSqrtBlowup + 1)) * dom.length ≤ 1024 * countGood (bad cs) dom) :
    (badTranscriptPairs S n E dom s.numQueries bad).length * 2 ^ 210 <
      S.length ^ n * (aggDistinctTuples s.numQueries dom).length :=
  _root_.Qsag.Aggregation.whir_bciksJohnsonQrom128_total_error_bound s hs S n hn E d hE hBudget hField dom hdom bad hfar

open Aggregation in
theorem succinct_aggregation_knowledge_soundness_thm (arith : RowArithmetization)
    (dom : WhirDomain) (inst : AggPublicInstance) (law : arith.Lawful dom inst)
    (proof : SuccinctAggregateProof) (fs : List UInt8) (view : SuccinctExtractionView)
    (hAccept : verifySuccinctAggregate arith dom inst proof fs = true)
    (hBound : StagesBound view.authPath dom.stages view.allTables proof.stages) :
    SuccinctSoundOutcomeProp arith dom inst proof view :=
  _root_.Qsag.Aggregation.succinct_aggregation_knowledge_soundness_thm arith dom inst law proof fs view hAccept hBound

open Aggregation in
theorem succinct_merge_tree_knowledge_soundness_thm (arith : RowArithmetization)
    (dom : WhirDomain) (inst : AggPublicInstance) (law : arith.Lawful dom inst) :
    ∀ (budget : Nat) (node : MergeNode) (views : SuccinctViewTree),
      verifyMergeTree arith dom inst budget node = true →
      ViewTreeBound dom node views →
      SuccinctMergeTreeSoundProp arith dom inst node views :=
  _root_.Qsag.Aggregation.succinct_merge_tree_knowledge_soundness_thm arith dom inst law

open Aggregation in
theorem qsag_aggregate_unforgeability_reduction_thm
    (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) (law : arith.Lawful dom inst)
    (proof : SuccinctAggregateProof) (fs : List UInt8) (view : SuccinctExtractionView)
    (i : Nat) (hPk : i < inst.committee.length) (hB : i < proof.agg.bitmap.length)
    (sk_i : PqSecretKey)
    (hKey_i : inst.committee[i]'hPk = derivePublicKey inst.suite inst.params sk_i)
    (hActive_i : proof.agg.bitmap[i]'hB = true)
    (queriedMsgs : List (List UInt8))
    (qOracle : QueriedWotsOracle)
    (revealedFors : List (UInt64 × Nat × Nat))
    (hGeom : (inst.params.w = 4 ∧ inst.params.ell1 = 128) ∨
      (inst.params.w = 16 ∧ inst.params.ell1 = 64))
    (hFreshMsg : inst.message ∉ queriedMsgs)
    (hAccept : verifySuccinctAggregate arith dom inst proof fs = true)
    (hBound : StagesBound view.authPath dom.stages view.allTables proof.stages)
    (hStatefulLeaf0Msg : ∀ sig : PqHashSig, inst.params.statefulJorts = true →
      ∀ hRand hRoot hCtr hChains,
        qOracle 0 (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ inst.params.subtreeHeight))
          (sig.leafGlobalIdx % 2 ^ inst.params.subtreeHeight) = some (hRand, hRoot, hCtr, hChains) →
        ∃ mPrev ∈ queriedMsgs,
          hRoot = thPreHash inst.suite sk_i.pkSeed
            (derivePublicKey inst.suite inst.params sk_i).pkRoot mPrev)
    (hStatelessLayer0Root : ∀ sig : PqHashSig, inst.params.statefulJorts = false →
      ∀ hRand hRoot hCtr hChains,
        qOracle 0 (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ inst.params.subtreeHeight))
          (sig.leafGlobalIdx % 2 ^ inst.params.subtreeHeight) = some (hRand, hRoot, hCtr, hChains) →
        hRoot = computeForsPk inst.suite inst.params sk_i
          (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ inst.params.subtreeHeight))
          (sig.leafGlobalIdx % 2 ^ inst.params.subtreeHeight))
    (hUpperOracle : ∀ (l : Nat) (g : Nat), ReachableUpperHypertreePos inst.params l g →
      let hRoot0 := computeXmssSubtreeRoot inst.suite inst.params sk_i
        (UInt32.ofNat (l - 1)) (UInt64.ofNat g)
      (∀ hRand hCtr hChains,
        qOracle (UInt32.ofNat l) (UInt64.ofNat (g / 2 ^ inst.params.subtreeHeight))
          (g % 2 ^ inst.params.subtreeHeight) = some (hRand, hRoot0, hCtr, hChains) →
        let hmH := thHashMsg inst.suite hRand sk_i.pkSeed
          (derivePublicKey inst.suite inst.params sk_i).pkRoot hRoot0
          (UInt32.ofNat l) (UInt64.ofNat (g / 2 ^ inst.params.subtreeHeight))
          (UInt32.ofNat (g % 2 ^ inst.params.subtreeHeight)) hCtr
        let digH := extractBaseWDigits inst.params.w inst.params.ell1 hmH
        checkTargetSum inst.params.w inst.params.ell1 inst.params.targetSum digH = true ∧
        recoverWotsPkFromSig inst.suite inst.params sk_i.pkSeed (UInt32.ofNat l)
          (UInt64.ofNat (g / 2 ^ inst.params.subtreeHeight))
          (g % 2 ^ inst.params.subtreeHeight) digH hChains =
        computeWotsPk inst.suite inst.params sk_i (UInt32.ofNat l)
          (UInt64.ofNat (g / 2 ^ inst.params.subtreeHeight))
          (g % 2 ^ inst.params.subtreeHeight)) ∧
      (∀ hRand hR hCtr hChains,
        qOracle (UInt32.ofNat l) (UInt64.ofNat (g / 2 ^ inst.params.subtreeHeight))
          (g % 2 ^ inst.params.subtreeHeight) = some (hRand, hR, hCtr, hChains) → hR = hRoot0))
    (hLayer0Valid : ∀ sig : PqHashSig, ∀ hRand hRoot0 hCtr hChains,
      qOracle 0 (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ inst.params.subtreeHeight))
        (sig.leafGlobalIdx % 2 ^ inst.params.subtreeHeight) = some (hRand, hRoot0, hCtr, hChains) →
      let hmH := thHashMsg inst.suite hRand sk_i.pkSeed
        (derivePublicKey inst.suite inst.params sk_i).pkRoot hRoot0
        0 (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ inst.params.subtreeHeight))
        (UInt32.ofNat (sig.leafGlobalIdx % 2 ^ inst.params.subtreeHeight)) hCtr
      let digH := extractBaseWDigits inst.params.w inst.params.ell1 hmH
      checkTargetSum inst.params.w inst.params.ell1 inst.params.targetSum digH = true ∧
      recoverWotsPkFromSig inst.suite inst.params sk_i.pkSeed 0
        (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ inst.params.subtreeHeight))
        (sig.leafGlobalIdx % 2 ^ inst.params.subtreeHeight) digH hChains =
      computeWotsPk inst.suite inst.params sk_i 0
        (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ inst.params.subtreeHeight))
        (sig.leafGlobalIdx % 2 ^ inst.params.subtreeHeight)) :
    SuccinctUnforgeabilityProp arith dom inst sk_i revealedFors proof view :=
  _root_.Qsag.Aggregation.qsag_aggregate_unforgeability_reduction_thm arith dom inst law proof fs view i hPk hB sk_i hKey_i hActive_i queriedMsgs qOracle revealedFors hGeom hFreshMsg hAccept hBound hStatefulLeaf0Msg hStatelessLayer0Root hUpperOracle hLayer0Valid

open Aggregation in
theorem qsag_aggregate_unforgeability_reduction_of_statelessLog_thm
    (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) (law : arith.Lawful dom inst)
    (proof : SuccinctAggregateProof) (fs : List UInt8) (view : SuccinctExtractionView)
    (i : Nat) (hPk : i < inst.committee.length) (hB : i < proof.agg.bitmap.length)
    (sk_i : PqSecretKey)
    (hKey_i : inst.committee[i]'hPk = derivePublicKey inst.suite inst.params sk_i)
    (hActive_i : proof.agg.bitmap[i]'hB = true)
    (queries : List PqSigningQuery)
    (hGeom : (inst.params.w = 4 ∧ inst.params.ell1 = 128) ∨
      (inst.params.w = 16 ∧ inst.params.ell1 = 64))
    (hStateless : inst.params.statefulJorts = false)
    (hLayers : inst.params.numLayers ≤ 2 ^ 32)
    (hFreshMsg : inst.message ∉
      (signingOracleLog inst.suite inst.params sk_i queries).map Prod.fst)
    (hAccept : verifySuccinctAggregate arith dom inst proof fs = true)
    (hBound : StagesBound view.authPath dom.stages view.allTables proof.stages) :
    SuccinctUnforgeabilityProp arith dom inst sk_i
      ((signingOracleLog inst.suite inst.params sk_i queries).flatMap fun e =>
        (List.range inst.params.forsTrees).map fun j =>
          (UInt64.ofNat (e.2.leafGlobalIdx / 2 ^ inst.params.subtreeHeight),
           e.2.leafGlobalIdx % 2 ^ inst.params.subtreeHeight,
           sigForsLeafIdx inst.suite inst.params
             (derivePublicKey inst.suite inst.params sk_i) e.1 e.2 j))
      proof view :=
  _root_.Qsag.Aggregation.qsag_aggregate_unforgeability_reduction_of_statelessLog_thm arith dom inst law proof fs view i hPk hB sk_i hKey_i hActive_i queries hGeom hStateless hLayers hFreshMsg hAccept hBound

open Aggregation in
theorem qsag_aggregate_unforgeability_reduction_of_checkedStatefulLog_thm
    (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) (law : arith.Lawful dom inst)
    (proof : SuccinctAggregateProof) (fs : List UInt8) (view : SuccinctExtractionView)
    (i : Nat) (hPk : i < inst.committee.length) (hB : i < proof.agg.bitmap.length)
    (sk_i : PqSecretKey)
    (hKey_i : inst.committee[i]'hPk = derivePublicKey inst.suite inst.params sk_i)
    (hActive_i : proof.agg.bitmap[i]'hB = true)
    (queries : List CheckedStatefulQuery)
    (hGeom : (inst.params.w = 4 ∧ inst.params.ell1 = 128) ∨
      (inst.params.w = 16 ∧ inst.params.ell1 = 64))
    (hValidParams : inst.params.checkedStatefulValid = true)
    (hFreshMsg : inst.message ∉
      ((execCheckedStatefulOracle inst.suite inst.params sk_i initCheckedStatefulLatch
        queries).emittedLog.map fun e => e.2.1))
    (hAccept : verifySuccinctAggregate arith dom inst proof fs = true)
    (hBound : StagesBound view.authPath dom.stages view.allTables proof.stages) :
    SuccinctUnforgeabilityProp arith dom inst sk_i [] proof view :=
  _root_.Qsag.Aggregation.qsag_aggregate_unforgeability_reduction_of_checkedStatefulLog_thm arith dom inst law proof fs view i hPk hB sk_i hKey_i hActive_i queries hGeom hValidParams hFreshMsg hAccept hBound

open Aggregation in
theorem rsSbox7TraceArith_lawful (seed root : Goldilocks) (msg : List UInt8) :
    (rsSbox7TraceArith seed root).Lawful rsSbox7WhirDomain (rsSbox7Inst seed root msg) :=
  _root_.Qsag.Aggregation.rsSbox7TraceArith_lawful seed root msg

open Aggregation in
theorem honestSbox7WhirProof_accepts (seed x0 b1 : Goldilocks) (msg : List UInt8) :
    let root := CommRingOps.add (pow7Goldilocks x0) seed
    let bundle := buildHonestSbox7WhirBundle seed x0 b1 msg
    verifySuccinctAggregate (rsSbox7TraceArith seed root) rsSbox7WhirDomain
      (rsSbox7Inst seed root msg) bundle.1 bundle.2.1 = true ∧
    StagesBound bundle.2.2.authPath rsSbox7WhirDomain.stages bundle.2.2.allTables bundle.1.stages :=
  _root_.Qsag.Aggregation.honestSbox7WhirProof_accepts seed x0 b1 msg

open Aggregation in
theorem succinct_knowledge_soundness_hypotheses_satisfiable :
    ∃ (arith : RowArithmetization) (dom : WhirDomain) (inst : AggPublicInstance)
      (_law : arith.Lawful dom inst) (proof : SuccinctAggregateProof)
      (fs : List UInt8) (view : SuccinctExtractionView),
      verifySuccinctAggregate arith dom inst proof fs = true ∧
      StagesBound view.authPath dom.stages view.allTables proof.stages ∧
      verifyMergeTree arith dom inst 1 (.leaf proof fs) = true ∧
      ViewTreeBound dom (.leaf proof fs) (.leaf view) ∧
      checkAllActiveSigners inst.suite inst.params inst.message inst.committee
        proof.agg.bitmap (arith.decodeSigs ((view.allTables.headD []).headD [])) = true :=
  _root_.Qsag.Aggregation.succinct_knowledge_soundness_hypotheses_satisfiable

open Aggregation in
theorem tooth_corrupted_round0_symbol_rejected (table0 : List Aggregation.GoldilocksExt4)
    (idx : Nat) (v' : Aggregation.GoldilocksExt4)
    (hValid : isLinearBaseRs8 table0 = true)
    (hIdx : idx < 8)
    (hMut : v' ≠ table0.getD idx Aggregation.GoldilocksExt4.zero) :
    isLinearBaseRs8 (table0.set idx v') = false :=
  _root_.Qsag.Aggregation.tooth_corrupted_round0_symbol_rejected table0 idx v' hValid hIdx hMut

open Aggregation in
theorem succinct_degree9_round_rejected (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) (proof : SuccinctAggregateProof) (fs : List UInt8)
    (p : List Aggregation.GoldilocksExt4) (ps : List (List Aggregation.GoldilocksExt4))
    (r : Aggregation.GoldilocksExt4) (rs : List Aggregation.GoldilocksExt4)
    (hp : proof.agg.roundPolys = p :: ps) (hc : proof.agg.challenges = r :: rs)
    (hDeg : 9 < p.length) :
    verifySuccinctAggregate arith dom inst proof fs = false :=
  _root_.Qsag.Aggregation.succinct_degree9_round_rejected arith dom inst proof fs p ps r rs hp hc hDeg

open Aggregation in
theorem succinct_duplicate_query_rejected (rowChalls finalWord : List Aggregation.GoldilocksExt4)
    (prior : List UInt8) (sdom : WhirStageDomain) (sp : WhirStageProof)
    (nextInfo : Option (WhirStageDomain × List UInt8))
    (q q' : StageQueryOpening) (qs : List StageQueryOpening)
    (hEq : sp.queries = q :: q' :: qs) (hDup : q.index = q'.index) :
    verifyOneWhirStage rowChalls finalWord prior sdom sp nextInfo = false :=
  _root_.Qsag.Aggregation.succinct_duplicate_query_rejected rowChalls finalWord prior sdom sp nextInfo q q' qs hEq hDup

open Aggregation in
theorem tooth_whir_wrong_ood_challenge_rejected (rowChalls finalWord : List Aggregation.GoldilocksExt4)
    (prior : List UInt8) (sdom : WhirStageDomain) (sp : WhirStageProof)
    (nextInfo : Option (WhirStageDomain × List UInt8))
    (hBad : sp.oodChallenge ≠ deriveStageOodChallenge prior sp.stageRoot) :
    verifyOneWhirStage rowChalls finalWord prior sdom sp nextInfo = false :=
  _root_.Qsag.Aggregation.tooth_whir_wrong_ood_challenge_rejected rowChalls finalWord prior sdom sp nextInfo hBad

open Aggregation in
theorem tooth_whir_bad_pow_rejected (rowChalls finalWord : List Aggregation.GoldilocksExt4)
    (prior : List UInt8) (sdom : WhirStageDomain) (sp : WhirStageProof)
    (nextInfo : Option (WhirStageDomain × List UInt8))
    (hBad : verifyWhirStagePow
      (stagePowDigest (stagePowSeed prior sp (nextInfo.map Prod.snd) finalWord))
      sp.powNonce sdom.powBits = false) :
    verifyOneWhirStage rowChalls finalWord prior sdom sp nextInfo = false :=
  _root_.Qsag.Aggregation.tooth_whir_bad_pow_rejected rowChalls finalWord prior sdom sp nextInfo hBad

open Aggregation in
theorem tooth_whir_wrong_params_rejected (arith : RowArithmetization) (dom : WhirDomain)
    (inst : AggPublicInstance) (proof : SuccinctAggregateProof) (fs : List UInt8)
    (hNe : proof.agg.params ≠ inst.params) :
    verifySuccinctAggregate arith dom inst proof fs = false :=
  _root_.Qsag.Aggregation.tooth_whir_wrong_params_rejected arith dom inst proof fs hNe

open Aggregation in
theorem aggregate_message_substitution_rejected (arith : RowArithmetization) (dom : WhirDomain)
    (inst1 inst2 : AggPublicInstance) (proof : SuccinctAggregateProof) (fs : List UInt8)
    (hMsg : inst1.message ≠ inst2.message)
    (hAcc1 : verifySuccinctAggregate arith dom inst1 proof fs = true) :
    verifySuccinctAggregate arith dom inst2 proof fs = false :=
  _root_.Qsag.Aggregation.aggregate_message_substitution_rejected arith dom inst1 inst2 proof fs hMsg hAcc1

open Aggregation in
theorem checkSbox7Trace_sound (seeds : List Goldilocks) (x root : Goldilocks)
    (words : List (List Aggregation.GoldilocksExt4))
    (h : checkSbox7Trace seeds x root words = true) :
    words.length = seeds.length ∧ evalSbox7Rounds seeds x = root :=
  _root_.Qsag.Aggregation.checkSbox7Trace_sound seeds x root words h

open Aggregation in
theorem checkSbox7Trace_complete (seeds : List Goldilocks) (x : Goldilocks) :
    checkSbox7Trace seeds x (evalSbox7Rounds seeds x) (buildSbox7Trace seeds x) = true :=
  _root_.Qsag.Aggregation.checkSbox7Trace_complete seeds x

open Aggregation in
theorem nineRoundSbox7Trace_sound (seeds : List Goldilocks) (x root : Goldilocks)
    (words : List (List Aggregation.GoldilocksExt4))
    (h : checkNineRoundSbox7Trace seeds x root words = true) :
    seeds.length = 9 ∧ words.length = 9 ∧ evalSbox7Rounds seeds x = root :=
  _root_.Qsag.Aggregation.nineRoundSbox7Trace_sound seeds x root words h

open Aggregation in
theorem nineRoundSbox7Trace_complete (seeds : List Goldilocks) (x : Goldilocks)
    (hn : seeds.length = 9) :
    checkNineRoundSbox7Trace seeds x (evalSbox7Rounds seeds x)
      (buildSbox7Trace seeds x) = true :=
  _root_.Qsag.Aggregation.nineRoundSbox7Trace_complete seeds x hn

open Aggregation in
theorem sbox7Trace_wrong_root_rejected (seeds : List Goldilocks) (x root : Goldilocks)
    (words : List (List Aggregation.GoldilocksExt4)) (hroot : evalSbox7Rounds seeds x ≠ root) :
    checkSbox7Trace seeds x root words = false :=
  _root_.Qsag.Aggregation.sbox7Trace_wrong_root_rejected seeds x root words hroot

open Aggregation in
theorem sbox7Trace_head_signature (seed : Goldilocks) (seeds : List Goldilocks)
    (x root : Goldilocks) (word : List Aggregation.GoldilocksExt4) (words : List (List Aggregation.GoldilocksExt4))
    (msg : List UInt8) (h : checkSbox7Trace (seed :: seeds) x root (word :: words) = true) :
    verifyPqHashSig sbox7FieldSuite sbox7Params
      (mkSbox7Pk seed (sbox7TraceStates word).2) msg (mkSbox7Sig x) = true :=
  _root_.Qsag.Aggregation.sbox7Trace_head_signature seed seeds x root word words msg h

open Aggregation in
theorem sbox7WhirChain_sound (msg : List UInt8) (x root : Goldilocks)
    (rounds : List Sbox7WhirRound) (h : Sbox7WhirChainAccepted msg x root rounds) :
    evalSbox7Rounds (rounds.map (·.seed)) x = root ∨
      ∃ r ∈ rounds, Sbox7WhirRoundBreak r :=
  _root_.Qsag.Aggregation.sbox7WhirChain_sound msg x root rounds h

open Aggregation in
theorem sbox7WhirChain_complete (msg : List UInt8) (seeds : List Goldilocks) (x : Goldilocks) :
    Sbox7WhirChainAccepted msg x (evalSbox7Rounds seeds x) (buildSbox7WhirChain msg seeds x) :=
  _root_.Qsag.Aggregation.sbox7WhirChain_complete msg seeds x

open Aggregation in
theorem buildSbox7WhirChain_seeds (msg : List UInt8) (seeds : List Goldilocks) (x : Goldilocks) :
    (buildSbox7WhirChain msg seeds x).map (·.seed) = seeds :=
  _root_.Qsag.Aggregation.buildSbox7WhirChain_seeds msg seeds x

open Aggregation in
theorem nineRoundSbox7Whir_sound (msg : List UInt8) (x root : Goldilocks)
    (rounds : List Sbox7WhirRound) (hn : rounds.length = 9)
    (h : Sbox7WhirChainAccepted msg x root rounds) :
    (rounds.map (·.seed)).length = 9 ∧
      (evalSbox7Rounds (rounds.map (·.seed)) x = root ∨
        ∃ r ∈ rounds, Sbox7WhirRoundBreak r) :=
  _root_.Qsag.Aggregation.nineRoundSbox7Whir_sound msg x root rounds hn h

theorem validProductionJortsBatch_item_forgery_break (params : PqHashParams)
    (items : List JortsBatchItem) (hValid : ValidProductionJortsBatch params items = true)
    (item : JortsBatchItem) (hItem : item ∈ items)
    (sk : PqSecretKey) (queries : List ProdSigningQuery)
    (hPk : item.validatorPk = derivePublicKey poseidon2Suite params sk)
    (hw : params.w = 4 ∨ params.w = 16)
    (hOneTime : ∀ q, q ∈ queries → ∀ q', q' ∈ queries → q.epoch = q'.epoch → q = q')
    (hFresh : ∀ e ∈ productionSigningLog poseidon2Suite params sk queries, e.1 ≠ item.message) :
    ProdSmTcrBreak poseidon2Suite params sk (productionSigningLog poseidon2Suite params sk queries) ∨
    ProdPreimageBreak poseidon2Suite params sk (productionSigningLog poseidon2Suite params sk queries)
      item.message item.signature :=
  _root_.Qsag.validProductionJortsBatch_item_forgery_break params items hValid item hItem
    sk queries hPk hw hOneTime hFresh

theorem stepOp256TableOk_xmss_extract (slots : List StepOpSlot) (rows : List StepOpRow)
    (k : Nat) (pub : AggValidatorPk × Digest5) (msg : List UInt8)
    (hTable : stepOp256TableOk .xmssPoseidon2 slots rows = true)
    (hSlot : slots[k]? = some (some pub))
    (hProf : pub.1.profile = .xmssPoseidon2)
    (hMu : pub.2 = computeMessageMu pub.1 msg) :
    verifyAggNativeSig xmssPoseidon2Geom pub.1 msg
      (stepXmssSig (stepOpSlotRow .xmssPoseidon2 rows k)) = true :=
  _root_.Qsag.stepOp256TableOk_xmss_extract slots rows k pub msg hTable hSlot hProf hMu

theorem stepOp256TableOk_corduroy_extract (slots : List StepOpSlot) (rows : List StepOpRow)
    (k : Nat) (pub : AggValidatorPk × Digest5) (msg : List UInt8)
    (hTable : stepOp256TableOk .corduroyPoseidon2 slots rows = true)
    (hSlot : slots[k]? = some (some pub))
    (hProf : pub.1.profile = .corduroyPoseidon2)
    (hMu : pub.2 = computeMessageMu pub.1 msg) :
    verifyAggNativeSig corduroyPoseidon2Geom pub.1 msg
      (stepCordSig (stepOpSlotRow .corduroyPoseidon2 rows k)) = true :=
  _root_.Qsag.stepOp256TableOk_corduroy_extract slots rows k pub msg hTable hSlot hProf hMu

theorem stepXmssRows_roundTrip (pk : AggValidatorPk) (msg : List UInt8) (sig : AggNativeSignature)
    (h : verifyAggNativeSig xmssPoseidon2Geom pk msg sig = true) :
    verifyAggNativeSig xmssPoseidon2Geom pk msg
      (stepXmssSig (stepOpSlotRow .xmssPoseidon2 (stepXmssRows pk (computeMessageMu pk msg) sig) 0)) = true :=
  _root_.Qsag.stepXmssRows_roundTrip pk msg sig h
-- END COMPARATOR ROSTER

/-- Public Hem's two honest sumchecks share one assignment table, with the column
    claim equal to the random linear combination of the three revealed row operands. -/
theorem hem_public_sumchecks_complete {F : Type} [LawfulField F]
    (shape : ZkHem.HemPublicShape F) (Z : List Bool → F) (hZ : shape.Satisfied Z)
    (tau rx : List F) (nu : F) (rowChallenges colChallenges : Nat → F) :
    (shape.rowProver Z tau rowChallenges).H = CommRingOps.zero ∧
    (shape.rowProver Z tau rowChallenges).Honest shape.rowBits 9 rowChallenges ∧
    (shape.columnProver Z rx nu colChallenges).H = shape.columnClaim Z rx nu ∧
    (shape.columnProver Z rx nu colChallenges).Honest shape.varBits 2 colChallenges := by
  have hr := ZkHem.publicHem_row_prover_correct shape Z hZ tau rowChallenges
  have hc := ZkHem.publicHem_column_prover_correct shape Z rx nu colChallenges
  exact ⟨hr.1, hr.2.1, hc.1, hc.2.1⟩

/-- Round-by-round soundness of the public row sumcheck on the single assignment table.
    The terminal check evaluates the true row summand; the degree bound is nine. -/
def hem_public_row_rbr {F : Type} [LawfulField F] [DecidableEq F]
    (s : ZkHem.HemPublicShape F) (Z : List Bool → F) (tau : List F)
    (S : List F) (hS : S.Nodup) (hpos : 0 < S.length) :
    RbrStateFunction (ZkHem.cubeIop
      (ZkHem.rowLineRep s.rowBits tau s.selector
        (ZkHem.matrixProduct s.varBits s.matrixA Z)
        (ZkHem.matrixProduct s.varBits s.matrixB Z)
        (ZkHem.matrixProduct s.varBits s.matrixC Z)) s.rowBits S hS hpos) :=
  ZkHem.cubeRbr _ _ _ _ _

/-- The variable-subcube column sumcheck has the same executable soundness spine,
    with degree two and the matrix combination evaluated at the row point. -/
def hem_public_column_rbr {F : Type} [LawfulField F] [DecidableEq F]
    (s : ZkHem.HemPublicShape F) (Z : List Bool → F) (rx : List F) (nu : F)
    (S : List F) (hS : S.Nodup) (hpos : 0 < S.length) :
    RbrStateFunction (ZkHem.cubeIop
      (ZkHem.colLineRep s.varBits (s.columnMatrix rx nu) Z) s.varBits S hS hpos) :=
  ZkHem.cubeRbr _ _ _ _ _


end Qsag.Top
end
