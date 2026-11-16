module
/-
# Qsag — formal models, algebraic proofs, and executable verification predicates

This root imports the library proof modules under `Qsag/`. A module is registered here and in
`AuditAxioms.lean` once it compiles against the current tree; `scripts/check_lean_policy.py` lists
any on-disk module that is not yet registered, and the `AuditAxioms` disk-inventory check rejects
the audit while one exists. Theorems establish their stated propositions; protocol refinement,
computational security assumptions, and binary coverage must be assessed separately. The
independent comparator target list is in `comparator.json`. `AuditAxioms` checks the constructive
axiom closure (`{propext, Quot.sound}`) of every public and private declaration of the registered
modules.
-/

-- Qsag/Tactic
public import Qsag.Tactic.AssuranceKit
public import Qsag.Tactic.Prelude

-- Qsag/Spec
public import Qsag.Spec.Algebra
public import Qsag.Spec.Assumptions
public import Qsag.Spec.Bounds
public import Qsag.Spec.Encoding
public import Qsag.Spec.GameBound
public import Qsag.Spec.IdealAggregate
public import Qsag.Spec.IdealCred
public import Qsag.Spec.IdealCustody
public import Qsag.Spec.IdealMigrate
public import Qsag.Spec.IdealSign
public import Qsag.Spec.Parameters
public import Qsag.Spec.Primitives
public import Qsag.Spec.Refines

-- Qsag/Math
public import Qsag.Math.Algebra
public import Qsag.Math.CoeffPoly
public import Qsag.Math.Counting
public import Qsag.Math.EllipticCurves
public import Qsag.Math.Gf2Pow128
public import Qsag.Math.Goldilocks
public import Qsag.Math.HasseHensel
public import Qsag.Math.Lattices
public import Qsag.Math.PolyRing
public import Qsag.Math.Primality
public import Qsag.Math.QuarticExt4

-- Qsag/Math/Tactic
public import Qsag.Math.Tactic.CommRing
public import Qsag.Math.Tactic.MaskBijection

-- Qsag/Coding
public import Qsag.Coding.AffineProximity
public import Qsag.Coding.Cwyz26
public import Qsag.Coding.GuruswamiSudan
public import Qsag.Coding.ReedSolomon
public import Qsag.Coding.Resultant

-- Qsag/Oracle
public import Qsag.Oracle.FiatShamir
public import Qsag.Oracle.Keccak
public import Qsag.Oracle.Poseidon2
public import Qsag.Oracle.Qrom
public import Qsag.Oracle.SpecRatBridges
public import Qsag.Oracle.Spn
public import Qsag.Oracle.Sponge

-- Qsag/Protocol/Aggregation
public import Qsag.Protocol.Aggregation.Aggregation
public import Qsag.Protocol.Aggregation.ClosedFsQromCompile
public import Qsag.Protocol.Aggregation.ClosedWhirSchedule
public import Qsag.Protocol.Aggregation.ComposedQsAgAndMergeSecurity
public import Qsag.Protocol.Aggregation.CompositionInstances
public import Qsag.Protocol.Aggregation.ConcreteSecurityBudget
public import Qsag.Protocol.Aggregation.CorduroyAndHemAirCompleteness
public import Qsag.Protocol.Aggregation.CrossProtocolAndDualOracleComposition
public import Qsag.Protocol.Aggregation.Cwyz26EqualDegreeAndMultiFold
public import Qsag.Protocol.Aggregation.Cwyz26JohnsonCertificate
public import Qsag.Protocol.Aggregation.FieldTransport
public import Qsag.Protocol.Aggregation.HemExtractedOpeningBridge
public import Qsag.Protocol.Aggregation.HemMultistageRbrAndSaltedQrom
public import Qsag.Protocol.Aggregation.HemPointReductionSoundness
public import Qsag.Protocol.Aggregation.HemSlicedFoldBudget
public import Qsag.Protocol.Aggregation.HemVerifierAcceptance
public import Qsag.Protocol.Aggregation.HemWhirRbrSoundness
public import Qsag.Protocol.Aggregation.MultiRoundFsQrom
public import Qsag.Protocol.Aggregation.Poseidon2AlgebraicAndRecursiveHem
public import Qsag.Protocol.Aggregation.QromCoherentMerkleBridge
public import Qsag.Protocol.Aggregation.QromSaltedMerkleStateRestoration
public import Qsag.Protocol.Aggregation.RecursivePoseidon2WhirSoundness
public import Qsag.Protocol.Aggregation.SuccinctAggregationIop
public import Qsag.Protocol.Aggregation.UcGames

-- Qsag/Protocol/Credentials
public import Qsag.Protocol.Credentials.AdvancedMpcAndCreds
public import Qsag.Protocol.Credentials.BlindVcCollisionFinder
public import Qsag.Protocol.Credentials.BlindVcQromSecurity

-- Qsag/Protocol/Migration
public import Qsag.Protocol.Migration.ActiveMigrationZeroTest
public import Qsag.Protocol.Migration.HdToprfAndMigrationSecurity
public import Qsag.Protocol.Migration.PallasAndBlsMigration

-- Qsag/Protocol/Signing
public import Qsag.Protocol.Signing.ExecEufCmaClosedGame
public import Qsag.Protocol.Signing.Fips205
public import Qsag.Protocol.Signing.FrontierCompact1122AndCorduroySecurity
public import Qsag.Protocol.Signing.HashSigs
public import Qsag.Protocol.Signing.HybridAddrPolicyAndFullPresetSecurity
public import Qsag.Protocol.Signing.HypertreeEufCma
public import Qsag.Protocol.Signing.PreprocessingSeedSeparation
public import Qsag.Protocol.Signing.ProdAdaptiveTcrReduction
public import Qsag.Protocol.Signing.ProdCollisionAccounting
public import Qsag.Protocol.Signing.ProdCollisionEvents
public import Qsag.Protocol.Signing.ProdCollisionExtraction
public import Qsag.Protocol.Signing.ProdCollisionLayers
public import Qsag.Protocol.Signing.ProdCollisionWitness
public import Qsag.Protocol.Signing.ProdHashGameReductions
public import Qsag.Protocol.Signing.SignatureOutputAndCacheLaws

-- Qsag/Protocol/Threshold
public import Qsag.Protocol.Threshold.BaggyAndRss256Security
public import Qsag.Protocol.Threshold.DensePcgProductionTaps
public import Qsag.Protocol.Threshold.DensePcgTapLinearTests
public import Qsag.Protocol.Threshold.IdealTsig
public import Qsag.Protocol.Threshold.LatticePreprocessingFull
public import Qsag.Protocol.Threshold.MaliciousSecurity
public import Qsag.Protocol.Threshold.MlDsa44Parameters
public import Qsag.Protocol.Threshold.ParametricThresholdAndUnlinkableQsa
public import Qsag.Protocol.Threshold.Preprocessing
public import Qsag.Protocol.Threshold.ProductionCoinReduction
public import Qsag.Protocol.Threshold.RlweCyclotomicExtraction
public import Qsag.Protocol.Threshold.RlweExtractionBoundary
public import Qsag.Protocol.Threshold.Rss256TernaryRound
public import Qsag.Protocol.Threshold.Rss256TwoPassProductProof
public import Qsag.Protocol.Threshold.RssSlhFullSecurity
public import Qsag.Protocol.Threshold.ThresholdApproval
public import Qsag.Protocol.Threshold.ThresholdMlDsaAndToprf
public import Qsag.Protocol.Threshold.ThresholdMlDsaSecurity
public import Qsag.Protocol.Threshold.ThresholdMpc

-- Qsag/Custody
public import Qsag.Custody.CompleteMediationBoundary
public import Qsag.Custody.CustodySuiteFull
public import Qsag.Custody.JortsBeltLatchAndQuorumSwitching
public import Qsag.Custody.SeparatedCustodyCollision
public import Qsag.Custody.SeparatedCustodyCore
public import Qsag.Custody.SeparatedCustodyHistory
public import Qsag.Custody.SeparatedCustodyPolicy
public import Qsag.Custody.SeparatedCustodyRelease
public import Qsag.Custody.SeparatedCustodyRequestHistory
public import Qsag.Custody.SeparatedCustodyRequestPolicy
public import Qsag.Custody.SeparatedCustodyResourceHistory
public import Qsag.Custody.SeparatedCustodyResourceSoundness
public import Qsag.Custody.SeparatedCustodySpine
public import Qsag.Custody.SeparatedCustodyUcBridge
public import Qsag.Custody.SeparatedCustodyUcResource
public import Qsag.Custody.ShamirThresholdCustodyRefinement
public import Qsag.Custody.ThresholdIdealServiceCustodyBridge

-- Qsag/Exec
public import Qsag.Exec.CeremonyAtomicityAndAbort
public import Qsag.Exec.IdealOutputBoundary
public import Qsag.Exec.InteractiveSecurityContract
public import Qsag.Exec.InteractiveServiceContext
public import Qsag.Exec.InteractiveUcEngine
public import Qsag.Exec.MirSpecBridge
public import Qsag.Exec.MirSpecBridgeCore
public import Qsag.Exec.MirSpecBridgeWitnesses
public import Qsag.Exec.PlatformContractInstances
public import Qsag.Exec.PosixCrashWal
public import Qsag.Exec.RefinesBridges
public import Qsag.Exec.RssParticipantBinding
public import Qsag.Exec.RssParticipantFixedTape
public import Qsag.Exec.RssParticipantGateBatches
public import Qsag.Exec.RssParticipantGateChecks
public import Qsag.Exec.RssParticipantGateEvidence
public import Qsag.Exec.RssParticipantGateField
public import Qsag.Exec.RssParticipantGateProducer
public import Qsag.Exec.RssParticipantGateWeights
public import Qsag.Exec.RssParticipantKeccak
public import Qsag.Exec.RssParticipantLocalSimulation
public import Qsag.Exec.RssParticipantMachine
public import Qsag.Exec.RssParticipantNetwork
public import Qsag.Exec.RssParticipantPassiveSimulation
public import Qsag.Exec.RssParticipantSponge
public import Qsag.Exec.RssProductionProfile
public import Qsag.Exec.RssSigningBackend
public import Qsag.Exec.RssSigningBatches
public import Qsag.Exec.RssSigningControl
public import Qsag.Exec.RssSigningEnrollment
public import Qsag.Exec.RssSigningExecution
public import Qsag.Exec.RssSigningHashCalls
public import Qsag.Exec.RssSigningMachine
public import Qsag.Exec.RssSigningProgram
public import Qsag.Exec.RssSigningPublicCompletion
public import Qsag.Exec.RssSigningTreeCache
public import Qsag.Exec.SimulationSpine
public import Qsag.Exec.SpecOracle
public import Qsag.Exec.ThresholdIdealDurableService
public import Qsag.Exec.ThresholdIdealService

-- Qsag/Exec/Tactic
public import Qsag.Exec.Tactic.SimulationKit

-- Qsag/Machine
public import Qsag.Machine.CompiledRlibFixtures
public import Qsag.Machine.ConstantTimeIsa
public import Qsag.Machine.ElfBinaryVerify
public import Qsag.Machine.ElfFixtureSlices
public import Qsag.Machine.ElfFixtureVerify
public import Qsag.Machine.ElfFunctionalEquiv
public import Qsag.Machine.ElfInvCerts
public import Qsag.Machine.ElfParse
public import Qsag.Machine.FaultAndSpeculativeSafety
public import Qsag.Machine.Gf128ClmulLoopAgreement
public import Qsag.Machine.IsaCosim
public import Qsag.Machine.McRefine
public import Qsag.Machine.PlatformContractInstances
public import Qsag.Machine.SimdBinaryEquiv
public import Qsag.Machine.SpirvSimtGpuEquiv
public import Qsag.Machine.SydTvTranslationValidation

-- Qsag/Machine/Tactic
public import Qsag.Machine.Tactic.KernelRfl

-- Qsag/Top
public import Qsag.Top.Aggregation
public import Qsag.Top.Apex
public import Qsag.Top.ClosedProtocolReductions
public import Qsag.Top.Credentials
public import Qsag.Top.Custody
public import Qsag.Top.Migration
public import Qsag.Top.SecurityBounds
public import Qsag.Top.Signing

-- Qsag/Tests
public import Qsag.Tests.ClosedEufCmaTeeth
public import Qsag.Tests.ClosedReductionTeeth
public import Qsag.Tests.HemExtractedOpeningBridgeTests
public import Qsag.Tests.MathAndCoding
public import Qsag.Tests.OracleAndQrom
public import Qsag.Tests.ProductionCoinReductionChecks
public import Qsag.Tests.QromCoherentOracleTests
public import Qsag.Tests.RssParticipantChecks
public import Qsag.Tests.RssParticipantGateChecksRun
public import Qsag.Tests.RssParticipantGateEvidenceRun
public import Qsag.Tests.RssParticipantSimulationChecks
public import Qsag.Tests.RssProductionProfileChecks
public import Qsag.Tests.RssSigningBatchChecks
public import Qsag.Tests.RssSigningChecks
public import Qsag.Tests.RssSigningTreeChecks
public import Qsag.Tests.SeparatedCustodyChecks
public import Qsag.Tests.SeparatedCustodyHistoryChecks
public import Qsag.Tests.SeparatedCustodyReleaseChecks
public import Qsag.Tests.SeparatedCustodyUcResourceChecks

-- Qsag (unsorted)
public import Qsag.VolatileCouponAndCapabilitySecurity
public import Qsag.ZkHemSoundnessAndPrivacy
