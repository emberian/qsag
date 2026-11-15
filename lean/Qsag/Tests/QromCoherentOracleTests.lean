module
/- Executed coherent superposition and database-measurement controls. -/
public import Qsag.Protocol.Aggregation.QromCoherentMerkleBridge
public import Qsag.Tests.HemExtractedOpeningBridgeTests
import all Qsag.Protocol.Aggregation.QromCoherentMerkleBridge
import all Qsag.Oracle.Qrom
import all Qsag.Tests.HemExtractedOpeningBridgeTests
import all Qsag.Tests.OracleAndQrom
import all Qsag.Protocol.Aggregation.HemExtractedOpeningBridge
import all Qsag.Protocol.Aggregation.MultiRoundFsQrom

public section
namespace Qsag
set_option autoImplicit false

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
  Qsag.coherent_hem_decoder_execution
end Qsag
end
