module
/-
# Qsag.Spec.Parameters — Normative Cryptographic Parameter Profiles

Centralized, human-auditable parameter records aligned 1-for-1 with the production Rust crates
(`crates/qsag-core`, `crates/qsag-agg`, `crates/qsag-cred`, `crates/qsag-quorum`):
1. Stateless tweakable-hash hypertree + FORS/TSW signing (`baggy128fProfile`, `corduroyCustody128Profile`,
   and NIST FIPS-205 `slhDsaShake128fProfile`),
2. FORS-free stateful epoch XMSS/Jorts signing (`jortsPoseidon2Profile`, `hemJortsXmssProfile`),
3. Quartic-Goldilocks Reed-Solomon IOP succinct aggregation (`hemGoldilocksExt4Profile`),
4. `PiBlindVc` selective-disclosure anonymous credentials (`N = 256` parties, `33` quantum / `17`
   classical repetitions over `GF(p^5)`) and FIPS-204 `ML-DSA-44` (`pqCredentialProfile`),
5. `DensePCG V3` 4-tree `12`-regular QC-LPN & `RLWE-1024` preprocessing (`densePcgV3Profile`), and
6. Separated threshold custody quorum geometry (`CustodyQuorumProfile`).
-/

public import Qsag.Spec.Primitives
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Spec

set_option autoImplicit false

/-- Normative parameter profile for tweakable-hash hypertree signing (supporting both stateless
    FORS/TSW presets and FORS-free stateful `Jorts` presets with `forsTrees = 0`). -/
structure HashSigProfile where
  securityBits : Nat
  digestBytes : Nat
  winternitzRadix : Nat
  wotsChainCount : Nat
  subtreeHeight : Nat
  hypertreeLayers : Nat
  forsTrees : Nat
  forsTreeHeight : Nat
  maxSigsLog2 : Nat
  statefulBottomLayer : Bool
  deriving DecidableEq, Repr

/-- Well-formedness predicate for a `HashSigProfile`: stateless profiles require `0 < forsTrees` and
    `0 < forsTreeHeight`, while stateful FORS-free `Jorts` profiles set `forsTrees = 0` and `forsTreeHeight = 0`. -/
def HashSigProfile.WellFormed (p : HashSigProfile) : Prop :=
  128 ≤ p.securityBits ∧
  (p.digestBytes = 16 ∨ p.digestBytes = 32) ∧
  (p.winternitzRadix = 4 ∨ p.winternitzRadix = 16) ∧
  0 < p.wotsChainCount ∧
  0 < p.subtreeHeight ∧
  0 < p.hypertreeLayers ∧
  p.hypertreeLayers * p.subtreeHeight ≤ 66 ∧
  ((p.statefulBottomLayer = false ∧ 0 < p.forsTrees ∧ 0 < p.forsTreeHeight) ∨
   (p.statefulBottomLayer = true ∧ p.forsTrees = 0 ∧ p.forsTreeHeight = 0))

/-- Deployed 128-bit PQ stateless `Baggy-128f` profile (`PqHashParams::BAGGY_TSW_128F` in `tsw_baggy.rs`:
    32-byte digest, `w = 4, ell1 = 128`, `d = 16, h' = 2` (`h = 32`), `k = 33, a = 6`, `Q_max = 2^16`). -/
@[expose] def pq128StatelessProfile : HashSigProfile where
  securityBits := 128
  digestBytes := 32
  winternitzRadix := 4
  wotsChainCount := 128
  subtreeHeight := 2
  hypertreeLayers := 16
  forsTrees := 33
  forsTreeHeight := 6
  maxSigsLog2 := 16
  statefulBottomLayer := false

/-- Deployed 128-bit PQ stateless `Corduroy-Custody-128` profile (`PqHashParams::CORDUROY_CUSTODY_128`
    in `tsw_baggy.rs`: 32-byte digest, `w = 4, ell1 = 128`, `d = 7, h' = 4` (`h = 28`), `k = 33, a = 6`,
    `Q_max = 2^12`). -/
@[expose] def corduroyCustody128Profile : HashSigProfile where
  securityBits := 128
  digestBytes := 32
  winternitzRadix := 4
  wotsChainCount := 128
  subtreeHeight := 4
  hypertreeLayers := 7
  forsTrees := 33
  forsTreeHeight := 6
  maxSigsLog2 := 12
  statefulBottomLayer := false

/-- Deployed FORS-free stateful `JortsPoseidon2` `HashSigProfile` (`forsTrees = 0, forsTreeHeight = 0`). -/
def jortsPoseidon2HashProfile : HashSigProfile where
  securityBits := 128
  digestBytes := 32
  winternitzRadix := 4
  wotsChainCount := 128
  subtreeHeight := 16
  hypertreeLayers := 1
  forsTrees := 0
  forsTreeHeight := 0
  maxSigsLog2 := 16
  statefulBottomLayer := true

/-- NIST FIPS-205 `SLH-DSA-SHAKE-128f` reference profile (`n = 16`-byte digest, `w = 16, ell1 = 35`,
    `d = 22, h' = 3` (`h = 66`), `k = 33, a = 6`). -/
def slhDsaShake128fProfile : HashSigProfile where
  securityBits := 128
  digestBytes := 16
  winternitzRadix := 16
  wotsChainCount := 35
  subtreeHeight := 3
  hypertreeLayers := 22
  forsTrees := 33
  forsTreeHeight := 6
  maxSigsLog2 := 66
  statefulBottomLayer := false

theorem pq128StatelessProfile_wellFormed :
    pq128StatelessProfile.WellFormed ∧
    corduroyCustody128Profile.WellFormed ∧
    jortsPoseidon2HashProfile.WellFormed ∧
    slhDsaShake128fProfile.WellFormed := by
  unfold HashSigProfile.WellFormed pq128StatelessProfile corduroyCustody128Profile
    jortsPoseidon2HashProfile slhDsaShake128fProfile
  decide

/-- Normative parameter profile for FORS-free stateful epoch XMSS/Jorts signing. -/
structure StatefulJortsProfile where
  securityBits : Nat
  digestBytes : Nat
  winternitzRadix : Nat
  wotsChainCount : Nat
  treeHeight : Nat
  maxEpochLeavesLog2 : Nat
  deriving DecidableEq, Repr

/-- Well-formedness predicate for a FORS-free `StatefulJortsProfile`. -/
def StatefulJortsProfile.WellFormed (p : StatefulJortsProfile) : Prop :=
  128 ≤ p.securityBits ∧
  p.digestBytes = 32 ∧
  (p.winternitzRadix = 4 ∨ p.winternitzRadix = 16) ∧
  0 < p.wotsChainCount ∧
  0 < p.treeHeight ∧
  p.maxEpochLeavesLog2 = p.treeHeight

/-- Deployed stateful `JortsPoseidon2` profile (`PqHashParams::JORTS_POSEIDON2`: FORS-free,
    `w = 4, ell1 = 128`, `h = 16`, `2^16` leaves). -/
@[expose] def pq128StatefulEpochProfile : StatefulJortsProfile where
  securityBits := 128
  digestBytes := 32
  winternitzRadix := 4
  wotsChainCount := 128
  treeHeight := 16
  maxEpochLeavesLog2 := 16

/-- Committee shard `HEM_JORTS` XMSS profile (`HEM_JORTS_XMSS_HEIGHT = 6` in `poseidon2_mpc.rs`:
    FORS-free, `w = 4, ell1 = 128`, `h = 6`, `64` leaves). -/
def hemJortsXmssProfile : StatefulJortsProfile where
  securityBits := 128
  digestBytes := 32
  winternitzRadix := 4
  wotsChainCount := 128
  treeHeight := 6
  maxEpochLeavesLog2 := 6

theorem pq128StatefulEpochProfile_wellFormed :
    pq128StatefulEpochProfile.WellFormed ∧
    hemJortsXmssProfile.WellFormed := by
  unfold StatefulJortsProfile.WellFormed pq128StatefulEpochProfile hemJortsXmssProfile
  decide

/-- Normative parameter profile for quartic-Goldilocks Reed-Solomon IOP succinct aggregation (`HEM`/`WHIR`),
    matching `Aggregation.productionAggParams` and `crates/qsag-agg`. -/
structure AggregationProfile where
  basePrime : Nat
  extDegree : Nat
  maxPcsVars : Nat
  earlyStopVars : Nat
  logTraceCols : Nat
  rowSumcheckDegree : Nat
  stageBlowups : List Nat
  johnsonQromQueries : List Nat
  johnsonClassicalQueries : List Nat
  cdhzQromQueries : List Nat
  grindingBits : Nat
  maxMergeDepth : Nat
  deriving DecidableEq, Repr

/-- Production `GoldilocksExt4` (`p = 2^64 - 2^32 + 1`, degree `4`) 4-stage `WHIR`/`HEM` profile:
    blowups `B = [4, 16, 64, 256]`, `[BCIKS20]` Johnson QROM-128 queries `q = [258, 130, 88, 66]`,
    classical-128 queries `[129, 65, 44, 33]`, and `[CDHZ25]` capacity QROM queries `[202, 102, 70, 52]`. -/
@[expose] def hemGoldilocksExt4Profile : AggregationProfile where
  basePrime := 18446744069414584321
  extDegree := 4
  maxPcsVars := 24
  earlyStopVars := 8
  logTraceCols := 8
  rowSumcheckDegree := 8
  stageBlowups := [4, 16, 64, 256]
  johnsonQromQueries := [258, 130, 88, 66]
  johnsonClassicalQueries := [129, 65, 44, 33]
  cdhzQromQueries := [202, 102, 70, 52]
  grindingBits := 16
  maxMergeDepth := 16

theorem hemGoldilocksExt4Profile_basePrime_eq :
    hemGoldilocksExt4Profile.basePrime = Qsag.goldilocksPrime ∧
    hemGoldilocksExt4Profile.extDegree = 4 ∧
    hemGoldilocksExt4Profile.stageBlowups = [4, 16, 64, 256] ∧
    hemGoldilocksExt4Profile.johnsonQromQueries = [258, 130, 88, 66] ∧
    hemGoldilocksExt4Profile.cdhzQromQueries = [202, 102, 70, 52] := by
  unfold hemGoldilocksExt4Profile Qsag.goldilocksPrime
  decide

/-- Normative parameter profile for `PiBlindVc` selective-disclosure credentials (`crates/qsag-cred/src/blind_vc.rs`),
    threshold symmetric `VOPRF` (`crates/qsag-cred/src/voprf.rs`), and `ThresholdMlDsa` (`MlDsa44Parameters`). -/
structure CredentialProfile where
  maxAttrs : Nat
  accumulatorDepth : Nat
  spongeRate : Nat
  spongeCapacity : Nat
  voprfParties : Nat
  voprfThreshold : Nat
  issuanceParties : Nat
  issuanceRepsClassical : Nat
  issuanceRepsQuantum : Nat
  sdLimboParties : Nat
  sdGgmDepth : Nat
  sdExtDegree : Nat
  sdRepsClassical : Nat
  sdRepsQuantum : Nat
  mlDsaModulus : Nat
  mlDsaChallengeWeight : Nat
  mlDsaGamma1 : Nat
  mlDsaBeta : Nat
  mlDsaSacrificeExtDegree : Nat
  deriving DecidableEq, Repr

/-- Production `PiBlindVc` + `VOPRF` + `ThresholdMlDsa` credential profile (`MAX_VC_ATTRS = 6`,
    `VC_ACCUMULATOR_DEPTH = 20`, 2-of-3 symmetric `VOPRF`, `438` 3-party ZKBoo issuance repetitions,
    `N = 256 = 2^8` GGM MPCitH selective-disclosure parties, `33` quantum / `17` classical repetitions
    over `GF(p^5) = GF(p)[T]/(T^5 - 3)`, `ML-DSA-44` `τ = 39`, `𝔽_{q^6}` sacrifice). -/
@[expose] def pqCredentialProfile : CredentialProfile where
  maxAttrs := 6
  accumulatorDepth := 20
  spongeRate := 6
  spongeCapacity := 6
  voprfParties := 3
  voprfThreshold := 2
  issuanceParties := 3
  issuanceRepsClassical := 219
  issuanceRepsQuantum := 438
  sdLimboParties := 256
  sdGgmDepth := 8
  sdExtDegree := 5
  sdRepsClassical := 17
  sdRepsQuantum := 33
  mlDsaModulus := 8380417
  mlDsaChallengeWeight := 39
  mlDsaGamma1 := 131072
  mlDsaBeta := 78
  mlDsaSacrificeExtDegree := 6

/-- Normative parameter profile for `DensePCG V3` QC-LPN & `RLWE-1024` preprocessing
    (`crates/qsag-core/src/preprocessing.rs`). -/
structure DensePcgProfile where
  defaultTreeDepth : Nat
  leavesPerTree : Nat
  treesPerBundle : Nat
  bundleAmbientDim : Nat
  tapsPerTree : Nat
  lpnRowWeight : Nat
  numPackedWords : Nat
  numBoolTriples : Nat
  numTowerTriples : Nat
  maxSeedWireBytes : Nat
  rlweRingDim : Nat
  rlweModulus : Nat
  rlweZkpokReps : Nat
  rlweChallengeBits : Nat
  deriving DecidableEq, Repr

@[expose] def densePcgV3Profile : DensePcgProfile where
  defaultTreeDepth := 15
  leavesPerTree := 32768
  treesPerBundle := 4
  bundleAmbientDim := 131072
  tapsPerTree := 3
  lpnRowWeight := 12
  numPackedWords := 1025
  numBoolTriples := 65600
  numTowerTriples := 8
  maxSeedWireBytes := 24576
  rlweRingDim := 1024
  rlweModulus := 12289
  rlweZkpokReps := 24
  rlweChallengeBits := 11

theorem pqCredentialProfile_soundness_params :
    pqCredentialProfile.maxAttrs = 6 ∧
    pqCredentialProfile.sdLimboParties = 2 ^ pqCredentialProfile.sdGgmDepth ∧
    pqCredentialProfile.sdLimboParties = 256 ∧
    pqCredentialProfile.sdExtDegree = 5 ∧
    pqCredentialProfile.sdRepsQuantum = 33 ∧
    pqCredentialProfile.mlDsaChallengeWeight = 39 ∧
    densePcgV3Profile.bundleAmbientDim = densePcgV3Profile.treesPerBundle * densePcgV3Profile.leavesPerTree ∧
    densePcgV3Profile.lpnRowWeight = densePcgV3Profile.treesPerBundle * densePcgV3Profile.tapsPerTree := by
  unfold pqCredentialProfile densePcgV3Profile
  decide

/-- Normative quorum profile for separated threshold custody (`0 < threshold ≤ numParties`). -/
structure CustodyQuorumProfile where
  numParties : Nat
  threshold : Nat
  spendCap : Nat
  h_pos : 0 < threshold
  h_le : threshold ≤ numParties
  deriving DecidableEq, Repr

/-- Honest-custodian intersection guarantee: when strictly fewer than `threshold` parties are
    corrupted, every `threshold`-sized approval set contains at least one honest custodian. -/
@[expose] def CustodyQuorumProfile.ToleratesCorrupt
    (p : CustodyQuorumProfile) (corruptCount : Nat) : Prop :=
  corruptCount < p.threshold

theorem CustodyQuorumProfile.honest_quorum_intersection
    (p : CustodyQuorumProfile) {corruptCount approvalCount : Nat}
    (hTol : p.ToleratesCorrupt corruptCount)
    (hQuorum : p.threshold ≤ approvalCount) :
    0 < approvalCount - corruptCount := by
  unfold CustodyQuorumProfile.ToleratesCorrupt at hTol
  omega

#verify_constructive
  Qsag.Spec.pq128StatelessProfile_wellFormed
  Qsag.Spec.pq128StatefulEpochProfile_wellFormed
  Qsag.Spec.hemGoldilocksExt4Profile_basePrime_eq
  Qsag.Spec.pqCredentialProfile_soundness_params
  Qsag.Spec.CustodyQuorumProfile.honest_quorum_intersection

end Qsag.Spec
end
