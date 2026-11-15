module
/-
# Qsag.Spec.Parameters — Normative Cryptographic Parameter Profiles

Centralized, human-auditable parameter records for the verified post-quantum signing,
succinct aggregation, anonymous credential, and threshold custody subsystems.
-/

public import Qsag.Spec.Primitives
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Spec

set_option autoImplicit false

/-- Normative parameter profile for tweakable-hash hypertree + FORS/TSW signing. -/
structure HashSigProfile where
  securityBits : Nat
  digestBytes : Nat
  winternitzRadix : Nat
  hypertreeHeight : Nat
  hypertreeLayers : Nat
  forsTrees : Nat
  forsTreeHeight : Nat
  statefulBottomLayer : Bool
  grindCounterBits : Nat
  deriving DecidableEq, Repr

/-- Well-formedness predicate for a `HashSigProfile`. -/
def HashSigProfile.WellFormed (p : HashSigProfile) : Prop :=
  128 ≤ p.securityBits ∧
  p.digestBytes = 32 ∧
  (p.winternitzRadix = 4 ∨ p.winternitzRadix = 16) ∧
  0 < p.hypertreeLayers ∧
  p.hypertreeLayers ≤ p.hypertreeHeight ∧
  0 < p.forsTrees

/-- Deployed 128-bit PQ stateless hash-signature profile (`w = 16`, 32-byte digest). -/
@[expose] def pq128StatelessProfile : HashSigProfile where
  securityBits := 128
  digestBytes := 32
  winternitzRadix := 16
  hypertreeHeight := 66
  hypertreeLayers := 22
  forsTrees := 33
  forsTreeHeight := 6
  statefulBottomLayer := false
  grindCounterBits := 64

/-- Deployed 128-bit PQ stateful-epoch hash-signature profile (`w = 4`, Jorts bottom layer). -/
@[expose] def pq128StatefulEpochProfile : HashSigProfile where
  securityBits := 128
  digestBytes := 32
  winternitzRadix := 4
  hypertreeHeight := 60
  hypertreeLayers := 12
  forsTrees := 32
  forsTreeHeight := 6
  statefulBottomLayer := true
  grindCounterBits := 64

theorem pq128StatelessProfile_wellFormed : pq128StatelessProfile.WellFormed := by
  unfold HashSigProfile.WellFormed pq128StatelessProfile
  decide

theorem pq128StatefulEpochProfile_wellFormed : pq128StatefulEpochProfile.WellFormed := by
  unfold HashSigProfile.WellFormed pq128StatefulEpochProfile
  decide

/-- Normative parameter profile for quartic-Goldilocks Reed-Solomon IOP aggregation (`HEM`). -/
structure AggregationProfile where
  basePrime : Nat
  extDegree : Nat
  initialDomainLog2 : Nat
  foldFactorLog2 : Nat
  numFoldRounds : Nat
  queryCount : Nat
  grindingBits : Nat
  deriving DecidableEq, Repr

/-- Canonical Goldilocks prime `p = 2^64 - 2^32 + 1` and quartic extension degree `4` profile. -/
@[expose] def hemGoldilocksExt4Profile : AggregationProfile where
  basePrime := 18446744069414584321
  extDegree := 4
  initialDomainLog2 := 21
  foldFactorLog2 := 4
  numFoldRounds := 3
  queryCount := 48
  grindingBits := 16

theorem hemGoldilocksExt4Profile_basePrime_eq :
    hemGoldilocksExt4Profile.basePrime = Qsag.goldilocksPrime ∧
    hemGoldilocksExt4Profile.extDegree = 4 := by
  unfold hemGoldilocksExt4Profile Qsag.goldilocksPrime
  decide

/-- Normative parameter profile for RLWE / Dual-LPN credential preprocessing and HVZK proofs. -/
structure CredentialProfile where
  ringDim : Nat
  modulus : Nat
  zkpokRepetitions : Nat
  challengeWeight : Nat
  lpnAmbientDim : Nat
  lpnRowWeight : Nat
  deriving DecidableEq, Repr

@[expose] def pqCredentialProfile : CredentialProfile where
  ringDim := 1024
  modulus := 12289
  zkpokRepetitions := 24
  challengeWeight := 11
  lpnAmbientDim := 32768
  lpnRowWeight := 64

theorem pqCredentialProfile_soundness_params :
    pqCredentialProfile.ringDim = 1024 ∧
    pqCredentialProfile.modulus = 12289 ∧
    pqCredentialProfile.zkpokRepetitions = 24 := by
  unfold pqCredentialProfile
  decide

/-- Normative quorum profile for separated threshold custody (`0 < threshold ≤ numParties`). -/
structure CustodyQuorumProfile where
  numParties : Nat
  threshold : Nat
  spendCap : Nat
  h_pos : 0 < threshold
  h_le : threshold ≤ numParties
  deriving DecidableEq, Repr

/-- Dishonest-minority tolerance bound (`corruptCount < threshold`). -/
@[expose] def CustodyQuorumProfile.ToleratesCorrupt
    (p : CustodyQuorumProfile) (corruptCount : Nat) : Prop :=
  corruptCount < p.threshold

theorem CustodyQuorumProfile.honest_quorum_intersection
    (p : CustodyQuorumProfile) {corruptCount approvalCount : Nat}
    (hTol : p.ToleratesCorrupt corruptCount)
    (hApp : p.threshold ≤ approvalCount) :
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
