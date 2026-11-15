module
/-
# Coherent observable bridge to the authenticated Hem checker

For bit-output ideal hashes the actual authenticated checker has identical event mass
in the decoded Fourier runtime and the original coherent experiment, up to the explicit
normalization. This is NOT the measured-log extraction bound: no address log is manufactured.
-/
public import Qsag.Oracle.QromFourierSupport
public import Qsag.Protocol.Aggregation.HemExtractedOpeningBridge
import all Qsag.Oracle.QromFourierSupport
import all Qsag.Oracle.QromCoherentOracleRegister
import all Qsag.Oracle.QromFourierTable
import all Qsag.Protocol.Aggregation.HemExtractedOpeningBridge
import all Qsag.Oracle.QromBatchMerkleExtraction
import all Qsag.Oracle.MultiRoundFsQrom

public section
namespace Qsag
set_option autoImplicit false

/-- Direct consumer: the real path/shape/root and Hem checks on arbitrary coherent outputs.
    The bit-output width is explicit; the deployed 256-bit layout is not instantiated here. -/
theorem coherent_hem_authenticated_event_eq {n cardAnc Q : Nat}
    (A : QuantumAdv n 1 cardAnc Q) (L : MerkleAddressLayout n 1)
    (slots : List (MerkleOpeningSlot n 1)) (inst : HemWhirInstance QuarticGoldilocks)
    (decode : Fin n → List (Option (MerkleOpeningValue 1)) → List (HemTranscriptRound QuarticGoldilocks)) :
    coherentTableEventMass (verifyHemOpeningBatch L slots inst decode)
      (fourierOracleState (fourierAdvStateAt A Q (Nat.le_refl Q))) =
      4 ^ (n * Q + n) * uniformOracleSum 1 n (fun H =>
        QVec.queryMassOn (verifyHemOpeningBatch L slots inst decode H) (runQuantumAdv A H)) :=
  fourierAdv_event_eq A (verifyHemOpeningBatch L slots inst decode)

/-- The same event transformation applies to each standalone authenticated opening batch. -/
theorem coherent_merkle_batch_event_eq {n cardAnc Q : Nat}
    (A : QuantumAdv n 1 cardAnc Q) (L : MerkleAddressLayout n 1)
    (slots : List (MerkleOpeningSlot n 1)) :
    coherentTableEventMass (verifyOpeningBatch L slots)
      (fourierOracleState (fourierAdvStateAt A Q (Nat.le_refl Q))) =
      4 ^ (n * Q + n) * uniformOracleSum 1 n (fun H =>
        QVec.queryMassOn (verifyOpeningBatch L slots H) (runQuantumAdv A H)) :=
  fourierAdv_event_eq A (verifyOpeningBatch L slots)

/-- Both numerator and denominator undergo the same scale; this is an actual normalized
    experiment identity, not solely an amplitude identity. -/
theorem coherent_decoded_total_mass {n cardAnc Q : Nat} (A : QuantumAdv n 1 cardAnc Q) :
    coherentTableEventMass (fun _ _ => true)
      (fourierOracleState (fourierAdvStateAt A Q (Nat.le_refl Q))) =
      4 ^ (n * Q + n) * quantumExperimentTotal A := by
  rw [fourierAdv_event_eq]
  have he : ∀ H : Fin n → BitVec 1,
      QVec.queryMassOn (fun _ => true) (runQuantumAdv A H) =
        prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init := by
    intro H
    exact runQuantumAdv_normSq A H
  rw [uniformOracleSum_congr 1 n _ _ he, uniformOracleSum_const]
  rfl

#verify_constructive
  Qsag.coherent_hem_authenticated_event_eq
  Qsag.coherent_merkle_batch_event_eq
  Qsag.coherent_decoded_total_mass
end Qsag
end
