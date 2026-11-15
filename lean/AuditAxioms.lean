module
import Qsag
import all Qsag.Tactic.AssuranceKit
import all Qsag.Tactic.ConstructiveRing
import all Qsag.Spec.Assumptions
import all Qsag.Spec.GameBound
import all Qsag.Spec.IdealAggregate
import all Qsag.Spec.IdealCred
import all Qsag.Spec.IdealCustody
import all Qsag.Spec.IdealMigrate
import all Qsag.Spec.IdealSign
import all Qsag.Spec.Parameters
import all Qsag.Spec.Primitives
import all Qsag.Spec.Refines
import all Qsag.Math.BinaryTower
import all Qsag.Math.Constructive
import all Qsag.Math.Digest256
import all Qsag.Math.Gf2Pow128
import all Qsag.Math.Goldilocks
import all Qsag.Math.GoldilocksPrimalityAndExt4Field
import all Qsag.Math.QuarticExt4
import all Qsag.Math.Tower128PolyBasisIso
import all Qsag.Coding.AffineIncidenceBound
import all Qsag.Coding.AffineProximityGaps
import all Qsag.Coding.BivariateFactorSplit
import all Qsag.Coding.BivariateGauss
import all Qsag.Coding.Cwyz26AffineGap
import all Qsag.Coding.Cwyz26DeployedStages
import all Qsag.Coding.Cwyz26EqualDegreeAndMultiFold
import all Qsag.Coding.Cwyz26JohnsonCertificate
import all Qsag.Coding.DynamicGcdSplit
import all Qsag.Coding.GoldilocksCharacteristic
import all Qsag.Coding.HenselNumerators
import all Qsag.Coding.JohnsonSetSystem
import all Qsag.Coding.MatrixDet
import all Qsag.Coding.ModMonicAlgebra
import all Qsag.Coding.NonpersistentIncidenceBound
import all Qsag.Coding.PersistentPairsBound
import all Qsag.Coding.PlaneBezoutResultant
import all Qsag.Coding.PolyMv3
import all Qsag.Coding.ShearedCurveGcd
import all Qsag.Coding.SimpleRootStratification
import all Qsag.Coding.SlicedJetIncidence
import all Qsag.Coding.SylvesterDeriv
import all Qsag.Coding.SylvesterElimination
import all Qsag.Coding.SylvesterResultant
import all Qsag.Coding.TrivariateGsExplainer
import all Qsag.Coding.UniversalHenselLift
import all Qsag.Oracle.ConcreteSecurityBudget
import all Qsag.Oracle.HashTrailSampling
import all Qsag.Oracle.Keccak
import all Qsag.Oracle.MultiRoundFsQrom
import all Qsag.Oracle.ParallelSeededPublicPermutation
import all Qsag.Oracle.ParallelSeededPublicPermutationGame
import all Qsag.Oracle.ParallelSeededSpnPolyBasis
import all Qsag.Oracle.ParallelSeededSpnSecurity
import all Qsag.Oracle.Poseidon2
import all Qsag.Oracle.QromBatchMerkleExtraction
import all Qsag.Oracle.QromClassicalQueryTransfer
import all Qsag.Oracle.QromCoherentOracleRegister
import all Qsag.Oracle.QromExtractionBoundary
import all Qsag.Oracle.QromFourierSupport
import all Qsag.Oracle.QromFourierTable
import all Qsag.Oracle.QromMeasuredMerkleExtraction
import all Qsag.Oracle.QromMeasuredQueryExperiment
import all Qsag.Oracle.QromMerkleOnlineExtraction
import all Qsag.Oracle.QromPreprocessingChecks
import all Qsag.Oracle.QromPreprocessingGame
import all Qsag.Oracle.SpnCommittedDifferential
import all Qsag.Oracle.SpnFixedConstantTrail
import all Qsag.Oracle.SpnRoundConstantExperiment
import all Qsag.Oracle.SpnWalshHull
import all Qsag.Oracle.SpongeFramingAndDomainSep
import all Qsag.Oracle.UcGames
import all Qsag.Protocol.Aggregation.Aggregation
import all Qsag.Protocol.Aggregation.ComposedQsAgAndMergeSecurity
import all Qsag.Protocol.Aggregation.CompositionInstances
import all Qsag.Protocol.Aggregation.CorduroyAndHemAirCompleteness
import all Qsag.Protocol.Aggregation.CrossProtocolAndDualOracleComposition
import all Qsag.Protocol.Aggregation.HemExtractedOpeningBridge
import all Qsag.Protocol.Aggregation.HemFoldDecompositionBridge
import all Qsag.Protocol.Aggregation.HemMultistageRbrAndSaltedQrom
import all Qsag.Protocol.Aggregation.HemPointReductionSoundness
import all Qsag.Protocol.Aggregation.HemSlicedFoldBudget
import all Qsag.Protocol.Aggregation.HemVerifierAcceptance
import all Qsag.Protocol.Aggregation.HemWhirRbrSoundness
import all Qsag.Protocol.Aggregation.Poseidon2AlgebraicAndRecursiveHem
import all Qsag.Protocol.Aggregation.QromCoherentMerkleBridge
import all Qsag.Protocol.Aggregation.QromSaltedMerkleStateRestoration
import all Qsag.Protocol.Aggregation.RecursivePoseidon2WhirSoundness
import all Qsag.Protocol.Aggregation.SuccinctAggregationIop
import all Qsag.Protocol.Credentials.AdvancedMpcAndCreds
import all Qsag.Protocol.Credentials.BlindVcCollisionFinder
import all Qsag.Protocol.Credentials.BlindVcQromSecurity
import all Qsag.Protocol.Migration.ActiveMigrationZeroTest
import all Qsag.Protocol.Migration.HdToprfAndMigrationSecurity
import all Qsag.Protocol.Migration.PallasAndBlsMigration
import all Qsag.Protocol.Migration.PrattPrimalityCert
import all Qsag.Protocol.Signing.Fips205
import all Qsag.Protocol.Signing.FrontierCompact1122AndCorduroySecurity
import all Qsag.Protocol.Signing.HashSigs
import all Qsag.Protocol.Signing.HybridAddrPolicyAndFullPresetSecurity
import all Qsag.Protocol.Signing.HypertreeEufCma
import all Qsag.Protocol.Signing.ProdAdaptiveTcrReduction
import all Qsag.Protocol.Signing.ProdCollisionAccounting
import all Qsag.Protocol.Signing.ProdCollisionEvents
import all Qsag.Protocol.Signing.ProdCollisionExtraction
import all Qsag.Protocol.Signing.ProdCollisionLayers
import all Qsag.Protocol.Signing.ProdCollisionWitness
import all Qsag.Protocol.Signing.ProdHashGameReductions
import all Qsag.Protocol.Signing.SignatureOutputAndCacheLaws
import all Qsag.Protocol.Threshold.BaggyAndRss256Security
import all Qsag.Protocol.Threshold.DensePcgProductionTaps
import all Qsag.Protocol.Threshold.DensePcgTapLinearTests
import all Qsag.Protocol.Threshold.GaussianHvzkAndDualLpn
import all Qsag.Protocol.Threshold.IdealTsig
import all Qsag.Protocol.Threshold.LatticePreprocessingFull
import all Qsag.Protocol.Threshold.MaliciousSecurity
import all Qsag.Protocol.Threshold.MlDsa44Parameters
import all Qsag.Protocol.Threshold.ParametricThresholdAndUnlinkableQsa
import all Qsag.Protocol.Threshold.Preprocessing
import all Qsag.Protocol.Threshold.ProductionCoinReduction
import all Qsag.Protocol.Threshold.RlweCyclotomicExtraction
import all Qsag.Protocol.Threshold.RlweExtractionBoundary
import all Qsag.Protocol.Threshold.Rss256TernaryRound
import all Qsag.Protocol.Threshold.Rss256TwoPassProductProof
import all Qsag.Protocol.Threshold.RssSlhFullSecurity
import all Qsag.Protocol.Threshold.ThresholdApproval
import all Qsag.Protocol.Threshold.ThresholdMlDsaAndToprf
import all Qsag.Protocol.Threshold.ThresholdMlDsaSecurity
import all Qsag.Protocol.Threshold.ThresholdMpc
import all Qsag.Custody.CompleteMediationBoundary
import all Qsag.Custody.CustodySuiteFull
import all Qsag.Custody.JortsBeltLatchAndQuorumSwitching
import all Qsag.Custody.SeparatedCustodyCollision
import all Qsag.Custody.SeparatedCustodyCore
import all Qsag.Custody.SeparatedCustodyHistory
import all Qsag.Custody.SeparatedCustodyPolicy
import all Qsag.Custody.SeparatedCustodyRelease
import all Qsag.Custody.SeparatedCustodyRequestHistory
import all Qsag.Custody.SeparatedCustodyRequestPolicy
import all Qsag.Custody.SeparatedCustodyResourceHistory
import all Qsag.Custody.SeparatedCustodyResourceSoundness
import all Qsag.Custody.SeparatedCustodySpine
import all Qsag.Custody.SeparatedCustodyUcBridge
import all Qsag.Custody.SeparatedCustodyUcResource
import all Qsag.Custody.ShamirThresholdCustodyRefinement
import all Qsag.Custody.ThresholdIdealServiceCustodyBridge
import all Qsag.Exec.CeremonyAtomicityAndAbort
import all Qsag.Exec.IdealOutputBoundary
import all Qsag.Exec.InteractiveSecurityContract
import all Qsag.Exec.InteractiveServiceContext
import all Qsag.Exec.InteractiveUcEngine
import all Qsag.Exec.MirSpecBridge
import all Qsag.Exec.MirSpecBridgeCore
import all Qsag.Exec.MirSpecBridgeWitnesses
import all Qsag.Exec.PosixCrashWal
import all Qsag.Exec.RssParticipantBinding
import all Qsag.Exec.RssParticipantFixedTape
import all Qsag.Exec.RssParticipantGateBatches
import all Qsag.Exec.RssParticipantGateChecks
import all Qsag.Exec.RssParticipantGateEvidence
import all Qsag.Exec.RssParticipantGateField
import all Qsag.Exec.RssParticipantGateProducer
import all Qsag.Exec.RssParticipantGateWeights
import all Qsag.Exec.RssParticipantKeccak
import all Qsag.Exec.RssParticipantLocalSimulation
import all Qsag.Exec.RssParticipantMachine
import all Qsag.Exec.RssParticipantNetwork
import all Qsag.Exec.RssParticipantPassiveSimulation
import all Qsag.Exec.RssParticipantSponge
import all Qsag.Exec.RssProductionProfile
import all Qsag.Exec.RssSigningBackend
import all Qsag.Exec.RssSigningBatches
import all Qsag.Exec.RssSigningControl
import all Qsag.Exec.RssSigningEnrollment
import all Qsag.Exec.RssSigningExecution
import all Qsag.Exec.RssSigningHashCalls
import all Qsag.Exec.RssSigningMachine
import all Qsag.Exec.RssSigningProgram
import all Qsag.Exec.RssSigningPublicCompletion
import all Qsag.Exec.RssSigningTreeCache
import all Qsag.Exec.SimulationSpine
import all Qsag.Exec.SpecOracle
import all Qsag.Exec.ThresholdIdealDurableService
import all Qsag.Exec.ThresholdIdealService
import all Qsag.Machine.CompiledRlibFixtures
import all Qsag.Machine.ConstantTimeIsa
import all Qsag.Machine.ElfBinaryVerify
import all Qsag.Machine.ElfFixtureSlices
import all Qsag.Machine.ElfFixtureVerify
import all Qsag.Machine.ElfFunctionalEquiv
import all Qsag.Machine.ElfInvCerts
import all Qsag.Machine.ElfParse
import all Qsag.Machine.FaultAndSpeculativeSafety
import all Qsag.Machine.Gf128ClmulLoopAgreement
import all Qsag.Machine.IsaCosim
import all Qsag.Machine.McRefine
import all Qsag.Machine.SimdBinaryEquiv
import all Qsag.Machine.SpirvSimtGpuEquiv
import all Qsag.Machine.SydTvTranslationValidation
import all Qsag.Top.Aggregation
import all Qsag.Top.Apex
import all Qsag.Top.Credentials
import all Qsag.Top.Custody
import all Qsag.Top.Migration
import all Qsag.Top.SecurityBounds
import all Qsag.Top.Signing
import all Qsag.Tests.HemExtractedOpeningBridgeTests
import all Qsag.Tests.ParallelSeededChainStepKat
import all Qsag.Tests.PersistentPairsBoundTests
import all Qsag.Tests.ProductionCoinReductionChecks
import all Qsag.Tests.QromCoherentOracleTests
import all Qsag.Tests.QromMeasuredMerkleExtractionTests
import all Qsag.Tests.RssParticipantChecks
import all Qsag.Tests.RssParticipantGateChecksRun
import all Qsag.Tests.RssParticipantGateEvidenceRun
import all Qsag.Tests.RssParticipantSimulationChecks
import all Qsag.Tests.RssProductionProfileChecks
import all Qsag.Tests.RssSigningBatchChecks
import all Qsag.Tests.RssSigningChecks
import all Qsag.Tests.RssSigningTreeChecks
import all Qsag.Tests.SeparatedCustodyChecks
import all Qsag.Tests.SeparatedCustodyHistoryChecks
import all Qsag.Tests.SeparatedCustodyReleaseChecks
import all Qsag.Tests.SeparatedCustodyUcResourceChecks
import all Qsag.Tests.SlicedJetIncidenceTests
import Lean
public meta import AxiomAuditSupport

/-!
# Constructive Kernel Axiom Gate (`AuditAxioms`)

Verifies that **every** declaration (both `public` and `.olean.private` via `import all` +
`setExporting false`) across the complete `Qsag` proof-module manifest depends strictly on a
subset of `{propext, Quot.sound}`:
1. **Zero Exclusions (`0` excluded modules):** Every proof module in `Qsag/` is held to the exact
   same constructive allowlist with zero diagnostic or exemption buckets.
2. **Negative Control:** Confirms `Lean.collectAxioms ``Classical.choice` is actively rejected.
3. **Manifest, `import all`, & Disk-Inventory Coverage:** Explicitly distinguishes meta/tactic
   infrastructure (`Qsag.Tactic.AssuranceKit`) from proof modules, verifies every manifest proof
   module is directly imported with `import all`, checks that no `Qsag/*.lean` file on disk or in
   the transitive import closure escapes the manifest, and verifies every proof module contributes
   `> 0` audited declarations.
-/

open Lean Elab Command in
run_cmd do
  let allow (ax : Name) : Bool := ax == ``propext || ax == ``Quot.sound

  -- 1. Negative control: the allowlist must reject `Classical.choice`.
  let negative ← Lean.collectAxioms ``Classical.choice
  if (negative.filter (!allow ·)).isEmpty then
    throwError "Axiom audit negative control unexpectedly passed"

  -- 2. Explicit proof-module vs meta-infrastructure manifest (all Qsag/*.lean modules).
  let infrastructureModules : Array Name := #[
    `Qsag.Tactic.AssuranceKit,
    `Qsag.Tactic.ConstructiveRing
  ]
  let auditedProofModules : Array Name := #[
    `Qsag.Spec.Assumptions,
    `Qsag.Spec.GameBound,
    `Qsag.Spec.IdealAggregate,
    `Qsag.Spec.IdealCred,
    `Qsag.Spec.IdealCustody,
    `Qsag.Spec.IdealMigrate,
    `Qsag.Spec.IdealSign,
    `Qsag.Spec.Parameters,
    `Qsag.Spec.Primitives,
    `Qsag.Spec.Refines,
    `Qsag.Math.BinaryTower,
    `Qsag.Math.Constructive,
    `Qsag.Math.Digest256,
    `Qsag.Math.Gf2Pow128,
    `Qsag.Math.Goldilocks,
    `Qsag.Math.GoldilocksPrimalityAndExt4Field,
    `Qsag.Math.QuarticExt4,
    `Qsag.Math.Tower128PolyBasisIso,
    `Qsag.Coding.AffineIncidenceBound,
    `Qsag.Coding.AffineProximityGaps,
    `Qsag.Coding.BivariateFactorSplit,
    `Qsag.Coding.BivariateGauss,
    `Qsag.Coding.Cwyz26AffineGap,
    `Qsag.Coding.Cwyz26DeployedStages,
    `Qsag.Coding.Cwyz26EqualDegreeAndMultiFold,
    `Qsag.Coding.Cwyz26JohnsonCertificate,
    `Qsag.Coding.DynamicGcdSplit,
    `Qsag.Coding.GoldilocksCharacteristic,
    `Qsag.Coding.HenselNumerators,
    `Qsag.Coding.JohnsonSetSystem,
    `Qsag.Coding.MatrixDet,
    `Qsag.Coding.ModMonicAlgebra,
    `Qsag.Coding.NonpersistentIncidenceBound,
    `Qsag.Coding.PersistentPairsBound,
    `Qsag.Coding.PlaneBezoutResultant,
    `Qsag.Coding.PolyMv3,
    `Qsag.Coding.ShearedCurveGcd,
    `Qsag.Coding.SimpleRootStratification,
    `Qsag.Coding.SlicedJetIncidence,
    `Qsag.Coding.SylvesterDeriv,
    `Qsag.Coding.SylvesterElimination,
    `Qsag.Coding.SylvesterResultant,
    `Qsag.Coding.TrivariateGsExplainer,
    `Qsag.Coding.UniversalHenselLift,
    `Qsag.Oracle.ConcreteSecurityBudget,
    `Qsag.Oracle.HashTrailSampling,
    `Qsag.Oracle.Keccak,
    `Qsag.Oracle.MultiRoundFsQrom,
    `Qsag.Oracle.ParallelSeededPublicPermutation,
    `Qsag.Oracle.ParallelSeededPublicPermutationGame,
    `Qsag.Oracle.ParallelSeededSpnPolyBasis,
    `Qsag.Oracle.ParallelSeededSpnSecurity,
    `Qsag.Oracle.Poseidon2,
    `Qsag.Oracle.QromBatchMerkleExtraction,
    `Qsag.Oracle.QromClassicalQueryTransfer,
    `Qsag.Oracle.QromCoherentOracleRegister,
    `Qsag.Oracle.QromExtractionBoundary,
    `Qsag.Oracle.QromFourierSupport,
    `Qsag.Oracle.QromFourierTable,
    `Qsag.Oracle.QromMeasuredMerkleExtraction,
    `Qsag.Oracle.QromMeasuredQueryExperiment,
    `Qsag.Oracle.QromMerkleOnlineExtraction,
    `Qsag.Oracle.QromPreprocessingChecks,
    `Qsag.Oracle.QromPreprocessingGame,
    `Qsag.Oracle.SpnCommittedDifferential,
    `Qsag.Oracle.SpnFixedConstantTrail,
    `Qsag.Oracle.SpnRoundConstantExperiment,
    `Qsag.Oracle.SpnWalshHull,
    `Qsag.Oracle.SpongeFramingAndDomainSep,
    `Qsag.Oracle.UcGames,
    `Qsag.Protocol.Aggregation.Aggregation,
    `Qsag.Protocol.Aggregation.ComposedQsAgAndMergeSecurity,
    `Qsag.Protocol.Aggregation.CompositionInstances,
    `Qsag.Protocol.Aggregation.CorduroyAndHemAirCompleteness,
    `Qsag.Protocol.Aggregation.CrossProtocolAndDualOracleComposition,
    `Qsag.Protocol.Aggregation.HemExtractedOpeningBridge,
    `Qsag.Protocol.Aggregation.HemFoldDecompositionBridge,
    `Qsag.Protocol.Aggregation.HemMultistageRbrAndSaltedQrom,
    `Qsag.Protocol.Aggregation.HemPointReductionSoundness,
    `Qsag.Protocol.Aggregation.HemSlicedFoldBudget,
    `Qsag.Protocol.Aggregation.HemVerifierAcceptance,
    `Qsag.Protocol.Aggregation.HemWhirRbrSoundness,
    `Qsag.Protocol.Aggregation.Poseidon2AlgebraicAndRecursiveHem,
    `Qsag.Protocol.Aggregation.QromCoherentMerkleBridge,
    `Qsag.Protocol.Aggregation.QromSaltedMerkleStateRestoration,
    `Qsag.Protocol.Aggregation.RecursivePoseidon2WhirSoundness,
    `Qsag.Protocol.Aggregation.SuccinctAggregationIop,
    `Qsag.Protocol.Credentials.AdvancedMpcAndCreds,
    `Qsag.Protocol.Credentials.BlindVcCollisionFinder,
    `Qsag.Protocol.Credentials.BlindVcQromSecurity,
    `Qsag.Protocol.Migration.ActiveMigrationZeroTest,
    `Qsag.Protocol.Migration.HdToprfAndMigrationSecurity,
    `Qsag.Protocol.Migration.PallasAndBlsMigration,
    `Qsag.Protocol.Migration.PrattPrimalityCert,
    `Qsag.Protocol.Signing.Fips205,
    `Qsag.Protocol.Signing.FrontierCompact1122AndCorduroySecurity,
    `Qsag.Protocol.Signing.HashSigs,
    `Qsag.Protocol.Signing.HybridAddrPolicyAndFullPresetSecurity,
    `Qsag.Protocol.Signing.HypertreeEufCma,
    `Qsag.Protocol.Signing.ProdAdaptiveTcrReduction,
    `Qsag.Protocol.Signing.ProdCollisionAccounting,
    `Qsag.Protocol.Signing.ProdCollisionEvents,
    `Qsag.Protocol.Signing.ProdCollisionExtraction,
    `Qsag.Protocol.Signing.ProdCollisionLayers,
    `Qsag.Protocol.Signing.ProdCollisionWitness,
    `Qsag.Protocol.Signing.ProdHashGameReductions,
    `Qsag.Protocol.Signing.SignatureOutputAndCacheLaws,
    `Qsag.Protocol.Threshold.BaggyAndRss256Security,
    `Qsag.Protocol.Threshold.DensePcgProductionTaps,
    `Qsag.Protocol.Threshold.DensePcgTapLinearTests,
    `Qsag.Protocol.Threshold.GaussianHvzkAndDualLpn,
    `Qsag.Protocol.Threshold.IdealTsig,
    `Qsag.Protocol.Threshold.LatticePreprocessingFull,
    `Qsag.Protocol.Threshold.MaliciousSecurity,
    `Qsag.Protocol.Threshold.MlDsa44Parameters,
    `Qsag.Protocol.Threshold.ParametricThresholdAndUnlinkableQsa,
    `Qsag.Protocol.Threshold.Preprocessing,
    `Qsag.Protocol.Threshold.ProductionCoinReduction,
    `Qsag.Protocol.Threshold.RlweCyclotomicExtraction,
    `Qsag.Protocol.Threshold.RlweExtractionBoundary,
    `Qsag.Protocol.Threshold.Rss256TernaryRound,
    `Qsag.Protocol.Threshold.Rss256TwoPassProductProof,
    `Qsag.Protocol.Threshold.RssSlhFullSecurity,
    `Qsag.Protocol.Threshold.ThresholdApproval,
    `Qsag.Protocol.Threshold.ThresholdMlDsaAndToprf,
    `Qsag.Protocol.Threshold.ThresholdMlDsaSecurity,
    `Qsag.Protocol.Threshold.ThresholdMpc,
    `Qsag.Custody.CompleteMediationBoundary,
    `Qsag.Custody.CustodySuiteFull,
    `Qsag.Custody.JortsBeltLatchAndQuorumSwitching,
    `Qsag.Custody.SeparatedCustodyCollision,
    `Qsag.Custody.SeparatedCustodyCore,
    `Qsag.Custody.SeparatedCustodyHistory,
    `Qsag.Custody.SeparatedCustodyPolicy,
    `Qsag.Custody.SeparatedCustodyRelease,
    `Qsag.Custody.SeparatedCustodyRequestHistory,
    `Qsag.Custody.SeparatedCustodyRequestPolicy,
    `Qsag.Custody.SeparatedCustodyResourceHistory,
    `Qsag.Custody.SeparatedCustodyResourceSoundness,
    `Qsag.Custody.SeparatedCustodySpine,
    `Qsag.Custody.SeparatedCustodyUcBridge,
    `Qsag.Custody.SeparatedCustodyUcResource,
    `Qsag.Custody.ShamirThresholdCustodyRefinement,
    `Qsag.Custody.ThresholdIdealServiceCustodyBridge,
    `Qsag.Exec.CeremonyAtomicityAndAbort,
    `Qsag.Exec.IdealOutputBoundary,
    `Qsag.Exec.InteractiveSecurityContract,
    `Qsag.Exec.InteractiveServiceContext,
    `Qsag.Exec.InteractiveUcEngine,
    `Qsag.Exec.MirSpecBridge,
    `Qsag.Exec.MirSpecBridgeCore,
    `Qsag.Exec.MirSpecBridgeWitnesses,
    `Qsag.Exec.PosixCrashWal,
    `Qsag.Exec.RssParticipantBinding,
    `Qsag.Exec.RssParticipantFixedTape,
    `Qsag.Exec.RssParticipantGateBatches,
    `Qsag.Exec.RssParticipantGateChecks,
    `Qsag.Exec.RssParticipantGateEvidence,
    `Qsag.Exec.RssParticipantGateField,
    `Qsag.Exec.RssParticipantGateProducer,
    `Qsag.Exec.RssParticipantGateWeights,
    `Qsag.Exec.RssParticipantKeccak,
    `Qsag.Exec.RssParticipantLocalSimulation,
    `Qsag.Exec.RssParticipantMachine,
    `Qsag.Exec.RssParticipantNetwork,
    `Qsag.Exec.RssParticipantPassiveSimulation,
    `Qsag.Exec.RssParticipantSponge,
    `Qsag.Exec.RssProductionProfile,
    `Qsag.Exec.RssSigningBackend,
    `Qsag.Exec.RssSigningBatches,
    `Qsag.Exec.RssSigningControl,
    `Qsag.Exec.RssSigningEnrollment,
    `Qsag.Exec.RssSigningExecution,
    `Qsag.Exec.RssSigningHashCalls,
    `Qsag.Exec.RssSigningMachine,
    `Qsag.Exec.RssSigningProgram,
    `Qsag.Exec.RssSigningPublicCompletion,
    `Qsag.Exec.RssSigningTreeCache,
    `Qsag.Exec.SimulationSpine,
    `Qsag.Exec.SpecOracle,
    `Qsag.Exec.ThresholdIdealDurableService,
    `Qsag.Exec.ThresholdIdealService,
    `Qsag.Machine.CompiledRlibFixtures,
    `Qsag.Machine.ConstantTimeIsa,
    `Qsag.Machine.ElfBinaryVerify,
    `Qsag.Machine.ElfFixtureSlices,
    `Qsag.Machine.ElfFixtureVerify,
    `Qsag.Machine.ElfFunctionalEquiv,
    `Qsag.Machine.ElfInvCerts,
    `Qsag.Machine.ElfParse,
    `Qsag.Machine.FaultAndSpeculativeSafety,
    `Qsag.Machine.Gf128ClmulLoopAgreement,
    `Qsag.Machine.IsaCosim,
    `Qsag.Machine.McRefine,
    `Qsag.Machine.SimdBinaryEquiv,
    `Qsag.Machine.SpirvSimtGpuEquiv,
    `Qsag.Machine.SydTvTranslationValidation,
    `Qsag.Top.Aggregation,
    `Qsag.Top.Apex,
    `Qsag.Top.Credentials,
    `Qsag.Top.Custody,
    `Qsag.Top.Migration,
    `Qsag.Top.SecurityBounds,
    `Qsag.Top.Signing,
    `Qsag.Tests.HemExtractedOpeningBridgeTests,
    `Qsag.Tests.ParallelSeededChainStepKat,
    `Qsag.Tests.PersistentPairsBoundTests,
    `Qsag.Tests.ProductionCoinReductionChecks,
    `Qsag.Tests.QromCoherentOracleTests,
    `Qsag.Tests.QromMeasuredMerkleExtractionTests,
    `Qsag.Tests.RssParticipantChecks,
    `Qsag.Tests.RssParticipantGateChecksRun,
    `Qsag.Tests.RssParticipantGateEvidenceRun,
    `Qsag.Tests.RssParticipantSimulationChecks,
    `Qsag.Tests.RssProductionProfileChecks,
    `Qsag.Tests.RssSigningBatchChecks,
    `Qsag.Tests.RssSigningChecks,
    `Qsag.Tests.RssSigningTreeChecks,
    `Qsag.Tests.SeparatedCustodyChecks,
    `Qsag.Tests.SeparatedCustodyHistoryChecks,
    `Qsag.Tests.SeparatedCustodyReleaseChecks,
    `Qsag.Tests.SeparatedCustodyUcResourceChecks,
    `Qsag.Tests.SlicedJetIncidenceTests
  ]

  let privEnv := (← getEnv).setExporting false
  let importedNames := privEnv.header.moduleNames
  let directImports := privEnv.header.imports
  for infraMod in infrastructureModules do
    unless importedNames.contains infraMod do
      throwError "Infrastructure module missing from import closure: {infraMod}"
  for modName in auditedProofModules do
    unless importedNames.contains modName do
      throwError "Manifest proof module missing from import closure: {modName}"
    unless directImports.any (fun imp => imp.module == modName && imp.importAll) do
      throwError "Manifest proof module must be directly imported with `import all`: {modName}"
  for importedMod in importedNames do
    if importedMod.toString.startsWith "Qsag." then
      unless auditedProofModules.contains importedMod || infrastructureModules.contains importedMod do
        throwError "Transitive Qsag module missing from explicit audit manifest: {importedMod}"

  -- 3. Dynamic filesystem check: zero Qsag/*.lean modules on disk may escape the manifest.
  let qsagDir : System.FilePath :=
    if ← (System.FilePath.mk "Qsag").pathExists then System.FilePath.mk "Qsag"
    else System.FilePath.mk "lean/Qsag"
  unless ← qsagDir.pathExists do
    throwError "Cannot locate Qsag source directory for inventory check"
  let mut pending := [(qsagDir, `Qsag)]
  while !pending.isEmpty do
    let (dir, modulePrefix) := pending.head!
    pending := pending.tail!
    for entry in (← dir.readDir) do
      if ← entry.path.isDir then
        pending := (entry.path, modulePrefix.str entry.fileName) :: pending
      else if entry.path.extension == some "lean" then
        if let some stem := entry.path.fileStem then
          let diskMod := modulePrefix.str stem
          unless auditedProofModules.contains diskMod || infrastructureModules.contains diskMod do
            throwError "Unregistered Qsag source module missing from AuditAxioms: {diskMod}"

  let mut perModuleCounts : Array Nat := Array.replicate auditedProofModules.size 0
  let mut checked : Nat := 0
  let mut rejected : Nat := 0
  let mut examples : Array Name := #[]

  for (name, _) in privEnv.constants.toList do
    if let some idx := privEnv.getModuleIdxFor? name then
      let owner := importedNames[idx.toNat]!
      -- Select by owning module, including private and non-Qsag-namespaced declarations.
      if let some mPos := auditedProofModules.findIdx? (· == owner) then
        checked := checked + 1
        perModuleCounts := perModuleCounts.modify mPos (· + 1)
        let axioms ← withEnv privEnv <| Lean.collectAxioms name
        let forbidden := axioms.filter (!allow ·)
        if !forbidden.isEmpty then
          rejected := rejected + 1
          examples := examples.push name
          logInfo m!"REJECT {name} ({owner}): {forbidden}"

  -- Tactic implementation executes at compile time; its pure definitions and proofs
  -- remain subject to the same axiom policy as the library.
  let mut infrastructureChecked : Nat := 0
  let mut metaSkipped : Nat := 0
  for (name, _) in privEnv.constants.toList do
    if let some idx := privEnv.getModuleIdxFor? name then
      if infrastructureModules.contains importedNames[idx.toNat]! then
        if QsagAudit.isCompileTimeAssurance privEnv name then
          metaSkipped := metaSkipped + 1
        else
          infrastructureChecked := infrastructureChecked + 1
          let axioms ← withEnv privEnv <| Lean.collectAxioms name
          let forbidden := axioms.filter (!allow ·)
          if !forbidden.isEmpty then
            rejected := rejected + 1
            examples := examples.push name
            logInfo m!"REJECT {name}: {forbidden}"
  logInfo m!"Assurance infrastructure: {infrastructureChecked} pure declarations audited; {metaSkipped} compile-time declarations"

  if checked == 0 then
    throwError "No project declarations found; audit coverage is empty"

  for i in [:auditedProofModules.size] do
    if perModuleCounts[i]! == 0 then
      throwError "Manifest proof module contributed 0 audited declarations: {auditedProofModules[i]!}"

  logInfo m!"Axiom inventory: {checked} declarations across {auditedProofModules.size} proof modules (0 excluded), {rejected} rejected"
  if rejected > 0 then
    throwError "Axiom policy failed for {rejected} of {checked} declarations. Examples: {examples}"
