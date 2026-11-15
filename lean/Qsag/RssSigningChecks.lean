module
public import Qsag.RssSigningExecution
public import Qsag.RssSigningEnrollment
public import Qsag.RssProductionProfileChecks
import all Qsag.RssSigningExecution
import all Qsag.RssSigningEnrollment
import all Qsag.RssSigningBackend
import all Qsag.RssSigningMachine
import all Qsag.RssSigningControl
import all Qsag.RssSigningProgram
import all Qsag.RssProductionProfileChecks
import all Qsag.HashSigs
import Qsag.Tactic.AssuranceKit

/-! Actual demand-driven participant executions and controller regressions.
No security claim is inferred from these honest executions; the gate checker has
not yet authorized their candidate cut outputs. The full execution retains every
cSHAKE node/evidence record rather than replacing the backend with a reference signer. -/
public section
namespace Qsag.RssSigning.Checks
set_option autoImplicit false
set_option maxRecDepth 4096

abbrev profile := RssProduction.Checks.profile
abbrev request := RssProduction.Checks.request

def tape (cut subcall round lane : Nat) : RssPrfZeroSeeds :=
  ⟨UInt64.ofNat (17 + 3 * cut + 5 * subcall + 7 * round + lane),
   UInt64.ofNat (29 + 11 * cut + 13 * subcall + 17 * round + lane),
   UInt64.ofNat (41 + 19 * cut + 23 * subcall + 29 * round + lane)⟩

private def require (b : Bool) (message : String) : IO Unit := do
  unless b do throw (IO.userError message)

/-- A full-width, actual shared-material signature produced by the resumable
public program and concrete local participant backend, with all evidence retained. -/
def fullSigningCheck : IO Unit := do
  let execution := honestSigningExecution profile request tape
  let some signature := execution.result
    | throw (IO.userError "participant program failed signing")
  let .ok wire := encodeProductionSigWire profile.params signature
    | throw (IO.userError "participant signature failed serialization")
  match verifyProductionWireBytes cshake256Suite profile.params
      (encodePublicKeyWire (RssProduction.enrolledKey profile))
      (RssProduction.payload profile request) wire with
  | .accept => pure ()
  | _ => throw (IO.userError "participant signature failed production verification")
  require (decide (0 < wire.length ∧ 0 < execution.cuts.length)) "empty execution"
  require (decide (execution.nextCut = execution.cuts.length)) "cut counter mismatch"
  let hashCount := execution.cuts.foldl (fun count cut => count + cut.computation.evidence.length) 0
  let gateCount := execution.cuts.foldl (fun count cut =>
    cut.computation.evidence.foldl (fun count hash =>
      hash.nodes.n0.evidence.foldl (fun count round => count + round.gates.length) count) count) 0
  require (execution.cuts.all fun cut => decide (cut.computation.evidence.length = queryHashCount cut.query))
    "hash trace contains missing or unsolicited subcalls"
  IO.println s!"Demand-driven participant signer: verified {wire.length}-byte signature; {execution.cuts.length} reached cuts, {hashCount} actual cSHAKE runs, {gateCount} pending gates at party0 retained"

/-- The executable online entry takes public enrollment separately from local
share material. Enrollment itself is constructed by the actual shared oracle;
no referenceKey or reference-signing evaluator is used in this execution. -/
def fullEnrolledSigningCheck : IO Unit := do
  let enrollment := sharedEnrollment profile
  let execution := enrolledExecution enrollment profile.material request tape
  let some signature := execution.result
    | throw (IO.userError "enrolled participant program failed signing")
  let .ok wire := encodeProductionSigWire enrollment.params signature
    | throw (IO.userError "enrolled participant signature failed serialization")
  match verifyProductionWireBytes cshake256Suite enrollment.params
      (encodePublicKeyWire enrollment.key) (publicPayload enrollment request) wire with
  | .accept => pure ()
  | _ => throw (IO.userError "enrolled participant signature failed verification")
  require (decide (0 < wire.length ∧ execution.nextCut = execution.cuts.length))
    "bad enrolled execution/counter"
  match execution.cuts with
  | [] => throw (IO.userError "enrolled signer performed no computation")
  | first :: _ => match first.query with
    | .prfMsg _ _ => pure ()
    | _ => throw (IO.userError "online signer reran enrollment queries")
  let hashCount := execution.cuts.foldl (fun count cut => count + cut.computation.evidence.length) 0
  IO.println s!"Public-enrollment participant signer: verified {wire.length}-byte signature; {execution.cuts.length} reached cuts and {hashCount} cSHAKE runs retained; first cut PRF-msg; enrollment derived through actual shared oracle"

def controllerAndFailureCheck : IO Unit := do
  let question := Query.prfMsg [7] [9]
  let program : Program Bytes := ask question
  let init := initial program 11
  let (waiting, output) := step init .advance
  require (decide (waiting.nextCut = 12 ∧ output = .request 11 question)) "index not burned before request"
  let (ready, _) := step waiting (.reply 11 [1, 2, 3])
  let (finished, result) := step ready .advance
  require (decide (finished.nextCut = 12 ∧ result = .finished [1, 2, 3])) "exact resume failed"
  require (decide ((step waiting (.reply 12 [0])).2 = .aborted)) "wrong reply index accepted"
  require (decide ((step ready (.reply 11 [0])).2 = .aborted)) "duplicate reply accepted"
  require (decide ((step waiting .abort).1.nextCut = 12)) "abort rolled back cut namespace"
  let exhausted := honestSigningExecution profile { request with reqEpoch := 4 } tape
  require (decide (exhausted.result = none ∧ exhausted.cuts = [])) "invalid leaf touched secret backend"
  let noGrind := { profile with grindLimit := 0 }
  let failed := evaluate (RssProduction.sharedOracle noGrind) (signingProgram noGrind request)
  require (decide (failed = none)) "grind exhaustion became success"
  IO.println "Resumable controller: matching reply, wrong/duplicate reply, abort burn and pre-query leaf failure passed; genuine grind failure preserved"

#verify_constructive evaluate_stateful evaluate_stateless queryRun_correct
  runPrepared_query_log honestSigningExecution_wire_refines request_burns_index wrong_reply_aborts
end Qsag.RssSigning.Checks
