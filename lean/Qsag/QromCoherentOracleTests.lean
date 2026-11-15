module
/- Executed coherent superposition and database-measurement controls. -/
public import Qsag.QromCoherentMerkleBridge
public import Qsag.HemExtractedOpeningBridgeTests
import all Qsag.QromCoherentMerkleBridge
import all Qsag.QromFourierSupport
import all Qsag.QromCoherentOracleRegister
import all Qsag.QromFourierTable
import all Qsag.QromExtractionBoundary
import all Qsag.QromMeasuredQueryExperiment
import all Qsag.HemExtractedOpeningBridgeTests
import all Qsag.QromMeasuredMerkleExtractionTests
import all Qsag.HemExtractedOpeningBridge
import all Qsag.MultiRoundFsQrom

public section
namespace Qsag
set_option autoImplicit false

def paritySuccess (H : Fin 2 → BitVec 1) (x : Fin 2) : Bool :=
  decide (x.val = (H 0 ^^^ H 1).toNat)

/-- A genuine superposition query: both addresses have positive initial mass. All four
    oracles are included. The coherent runtime preserves perfect parity success and has
    Fourier support exactly on one-entry labels after one call. -/
theorem coherent_parity_runtime_execution :
    QVec.queryWeight qromParityAdv.init 0 = 2 ∧ QVec.queryWeight qromParityAdv.init 1 = 2 ∧
    uniformOracleSum 1 2 (fun H => QVec.queryMassOn (paritySuccess H) (runQuantumAdv qromParityAdv H)) = 32 ∧
    coherentTableEventMass paritySuccess
      (fourierOracleState (fourierAdvStateAt qromParityAdv 1 (Nat.le_refl 1))) = 8192 ∧
    oracleTableSum 2 (fun d => if tableWeight 2 d = 1 then
      QVec.stateNormSq (fourierAdvStateAt qromParityAdv 1 (Nat.le_refl 1) d) else 0) = 2048 ∧
    oracleTableSum 2 (fun d => if 1 < tableWeight 2 d then
      QVec.stateNormSq (fourierAdvStateAt qromParityAdv 1 (Nat.le_refl 1) d) else 0) = 0 := by
  decide +kernel

/-- Measuring the Fourier label before decoding changes oracle/output correlations. The
    coherent success mass 8192 falls to 4096 while total mass stays 8192. This refutes treating
    the Q-entry support invariant as a nondisturbing classical answer-table extractor. -/
theorem tooth_fourier_database_measurement_disturbs :
    oracleTableSum 2 (fun d => coherentTableEventMass paritySuccess
      (fourierOracleState (projectFourierLabel d (fourierAdvStateAt qromParityAdv 1 (Nat.le_refl 1))))) = 4096 ∧
    oracleTableSum 2 (fun d => coherentTableEventMass (fun _ _ => true)
      (fourierOracleState (projectFourierLabel d (fourierAdvStateAt qromParityAdv 1 (Nat.le_refl 1))))) = 8192 ∧
    uniformOracleSum 1 2 (fun H => sumLogs 2 1 (fun xs =>
      QVec.queryMassOn (paritySuccess H) (measuredStateAt qromParityAdv H 1 (Nat.le_refl 1) xs))) = 16 := by
  decide +kernel

/-- Actual authenticated Hem decoder consumer, on the earlier nonconstant one-bit layout. -/
theorem coherent_hem_decoder_execution :
    let honest := toyQueryAdv ⟨1, by decide⟩ (by decide)
    coherentTableEventMass
      (verifyHemOpeningBatch toyMerkleLayout toyOpeningSlots toyHemInstance toyHemDecode)
      (fourierOracleState (fourierAdvStateAt honest 1 (Nat.le_refl 1))) = 524288 := by
  dsimp only
  rw [coherent_hem_authenticated_event_eq]
  decide +kernel

#verify_constructive
  Qsag.coherent_parity_runtime_execution
  Qsag.tooth_fourier_database_measurement_disturbs
  Qsag.coherent_hem_decoder_execution
end Qsag
end
