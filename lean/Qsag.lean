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

public import Qsag.ActiveMigrationZeroTest
public import Qsag.AdvancedMpcAndCreds
public import Qsag.AffineProximityGaps
public import Qsag.Aggregation
public import Qsag.Apex
public import Qsag.BaggyAndRss256Security
public import Qsag.BinaryTower
public import Qsag.BlindVcQromSecurity
public import Qsag.CeremonyAtomicityAndAbort
public import Qsag.CompiledRlibFixtures
public import Qsag.ConcreteSecurityBudget
public import Qsag.ConstantTimeIsa
public import Qsag.Constructive
public import Qsag.Digest256
public import Qsag.MlDsa44Parameters
public import Qsag.CustodySuiteFull
public import Qsag.ElfBinaryVerify
public import Qsag.ElfFixtureSlices
public import Qsag.ElfFixtureVerify
public import Qsag.ElfInvCerts
public import Qsag.ElfParse
public import Qsag.FaultAndSpeculativeSafety
public import Qsag.Fips205
public import Qsag.GaussianHvzkAndDualLpn
public import Qsag.Goldilocks
public import Qsag.HashSigs
public import Qsag.HdToprfAndMigrationSecurity
public import Qsag.HypertreeEufCma
public import Qsag.IdealTsig
public import Qsag.InteractiveUcEngine
public import Qsag.IsaCosim
public import Qsag.JortsBeltLatchAndQuorumSwitching
public import Qsag.Keccak
public import Qsag.LatticePreprocessingFull
public import Qsag.MaliciousSecurity
public import Qsag.McRefine
public import Qsag.MirSpecBridge
public import Qsag.MirSpecBridgeCore
public import Qsag.MirSpecBridgeWitnesses
public import Qsag.MultiRoundFsQrom
public import Qsag.PallasAndBlsMigration
public import Qsag.ParallelSeededSpnSecurity
public import Qsag.Poseidon2
public import Qsag.Poseidon2AlgebraicAndRecursiveHem
public import Qsag.PosixCrashWal
public import Qsag.Preprocessing
public import Qsag.RlweCyclotomicExtraction
public import Qsag.RssSlhFullSecurity
public import Qsag.SimdBinaryEquiv
public import Qsag.SimulationSpine
public import Qsag.SpecOracle
public import Qsag.SpirvSimtGpuEquiv
public import Qsag.SuccinctAggregationIop
public import Qsag.SydTvTranslationValidation
public import Qsag.ThresholdApproval
public import Qsag.ThresholdMlDsaAndToprf
public import Qsag.ThresholdMlDsaSecurity
public import Qsag.ThresholdMpc
public import Qsag.UcGames

public import Qsag.CorduroyAndHemAirCompleteness

public import Qsag.ElfFunctionalEquiv

public import Qsag.CodingTheory.PolyMv3
public import Qsag.CodingTheory.SylvesterResultant
public import Qsag.CodingTheory.DynamicGcdSplit
public import Qsag.CodingTheory.HenselNumerators
public import Qsag.CodingTheory.UniversalHenselLift
public import Qsag.CodingTheory.TrivariateGsExplainer
public import Qsag.CodingTheory.SimpleRootStratification
public import Qsag.CodingTheory.AffineIncidenceBound
public import Qsag.CodingTheory.Cwyz26AffineGap

public import Qsag.CodingTheory.BivariateFactorSplit
public import Qsag.CodingTheory.BivariateGauss
public import Qsag.CodingTheory.Cwyz26JohnsonCertificate
public import Qsag.CodingTheory.GoldilocksCharacteristic
public import Qsag.CodingTheory.JohnsonSetSystem
public import Qsag.CodingTheory.MatrixDet
public import Qsag.CodingTheory.ModMonicAlgebra
public import Qsag.CodingTheory.NonpersistentIncidenceBound
public import Qsag.CodingTheory.PersistentPairsBound
public import Qsag.CodingTheory.PersistentPairsBoundTests
public import Qsag.CodingTheory.PlaneBezoutResultant
public import Qsag.CodingTheory.ShearedCurveGcd
public import Qsag.CodingTheory.SlicedJetIncidence
public import Qsag.CodingTheory.SlicedJetIncidenceTests
public import Qsag.CodingTheory.SylvesterDeriv
public import Qsag.CodingTheory.SylvesterElimination
public import Qsag.CompleteMediationBoundary
public import Qsag.ComposedQsAgAndMergeSecurity
public import Qsag.CompositionInstances
public import Qsag.CrossProtocolAndDualOracleComposition
public import Qsag.DensePcgProductionTaps
public import Qsag.DensePcgTapLinearTests
public import Qsag.GoldilocksPrimalityAndExt4Field
public import Qsag.HashTrailSampling
public import Qsag.HemFoldDecompositionBridge
public import Qsag.HemPointReductionSoundness
public import Qsag.HemVerifierAcceptance
public import Qsag.HemWhirRbrSoundness
public import Qsag.HybridAddrPolicyAndFullPresetSecurity
public import Qsag.PrattPrimalityCert
public import Qsag.QromClassicalQueryTransfer
public import Qsag.QromExtractionBoundary
public import Qsag.QromMeasuredMerkleExtraction
public import Qsag.QromMeasuredMerkleExtractionTests
public import Qsag.QromMeasuredQueryExperiment
public import Qsag.QromMerkleOnlineExtraction
public import Qsag.RlweExtractionBoundary
public import Qsag.Rss256TernaryRound
public import Qsag.Rss256TwoPassProductProof
public import Qsag.SeparatedCustodyChecks
public import Qsag.SeparatedCustodyCore
public import Qsag.SeparatedCustodyHistory
public import Qsag.SeparatedCustodyHistoryChecks
public import Qsag.SeparatedCustodyPolicy
public import Qsag.SeparatedCustodySpine
public import Qsag.SpongeFramingAndDomainSep

public import Qsag.BlindVcCollisionFinder
public import Qsag.CodingTheory.Cwyz26DeployedStages
public import Qsag.HemExtractedOpeningBridge
public import Qsag.HemExtractedOpeningBridgeTests
public import Qsag.IdealOutputBoundary
public import Qsag.ParallelSeededChainStepKat
public import Qsag.ParallelSeededSpnPolyBasis
public import Qsag.ProdCollisionAccounting
public import Qsag.ProdCollisionEvents
public import Qsag.ProdCollisionExtraction
public import Qsag.ProdCollisionLayers
public import Qsag.ProdCollisionWitness
public import Qsag.QromBatchMerkleExtraction
public import Qsag.SeparatedCustodyCollision
public import Qsag.SeparatedCustodyRelease
public import Qsag.SeparatedCustodyReleaseChecks
public import Qsag.SignatureOutputAndCacheLaws
public import Qsag.SpnCommittedDifferential
public import Qsag.SpnFixedConstantTrail
public import Qsag.SpnRoundConstantExperiment
public import Qsag.SpnWalshHull
public import Qsag.Tower128PolyBasisIso

public import Qsag.Tactic.AssuranceKit
public import Qsag.Tactic.ConstructiveRing
