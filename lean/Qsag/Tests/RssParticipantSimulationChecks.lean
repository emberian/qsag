module
public import Qsag.Oracle.Keccak
public import Qsag.Exec.RssParticipantPassiveSimulation
public import Qsag.Tests.RssParticipantChecks
public import Qsag.Exec.RssParticipantLocalSimulation
public import Qsag.Exec.RssParticipantMachine
public import Qsag.Protocol.Threshold.ThresholdMpc
import Qsag.Tactic.AssuranceKit

/-! Nonzero finite-prefix simulation check and a correlated-mask boundary witness.
The coupling check uses inverseTape only on the real side; the simulator receives
no global share state. The repeated-mask witness is not an ideal-independent
sampling experiment and cannot use the tape-product privacy interpretation. -/
public section
namespace Qsag.RssParticipant.SimulationChecks
set_option autoImplicit false
set_option maxRecDepth 4096

def known0 : KState := { zeroKState with a0 := 11, a7 := 19, a22 := 31 }
def known1 : KState := { zeroKState with a0 := 41, a7 := 53, a22 := 67 }
def plan : List PassiveRound := keccakRoundConstants.map (fun rc => ⟨rc, known0, known1⟩)
def samples : List KState := (List.range 24).map fun i =>
  { zeroKState with a0 := UInt64.ofNat (71 + i), a7 := UInt64.ofNat (101 + i), a22 := 131 }

def simulationCheck : IO Unit := do
  let input := Checks.input
  let nodes := initialNodes Checks.binding input keccakRoundConstants 0
  let realMasks := inverseTape input plan samples
  let realResult := runPassiveReal nodes plan realMasks
  let simulated := runPassiveSimulator nodes.n0 plan samples
  unless decide (realResult.n0 = simulated ∧ simulated.evidence.length = 24) do
    throw (IO.userError "passive local simulation mismatch")
  unless decide (forwardTape input plan realMasks = samples) do
    throw (IO.userError "forward/inverse coupling mismatch")
  let shortSamples := samples.take 9
  unless decide ((runPassiveReal nodes plan (inverseTape input plan shortSamples)).n0 =
    runPassiveSimulator nodes.n0 plan shortSamples) do
    throw (IO.userError "unfinished prefix simulation mismatch")
  IO.println "Participant simulator:24-round and9-round nonzero prefixes match complete local gate evidence; forward/inverse hidden-mask coupling passed"

/-- Two identical calls using the same hidden mask necessarily produce identical
incoming shares. Independent simulator samples need not satisfy that relation. -/
theorem reused_mask_does_not_model_two_independent_samples (state : RssKState) (rc : UInt64)
    (k0 k1 hidden : KState) :
    let observed := (roundNetwork state rc (roundMasks k0 k1 hidden)).s1
    (observed, observed) ≠ (zeroKState, { zeroKState with a0 := 1 }) := by
  intro observed h
  have ha := congrArg (fun pair : KState × KState => pair.1.a0) h
  have hb := congrArg (fun pair : KState × KState => pair.2.a0) h
  have h01 : (0 : UInt64) = 1 := ha.symm.trans hb
  exact (by decide : (0 : UInt64) ≠ 1) h01

#verify_constructive reused_mask_does_not_model_two_independent_samples
  reused_mask_does_not_model_two_independent_samples
end Qsag.RssParticipant.SimulationChecks
