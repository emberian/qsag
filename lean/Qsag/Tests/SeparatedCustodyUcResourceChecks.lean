module
public import Qsag.Custody.CustodySuiteFull
meta import Qsag.Custody.CustodySuiteFull
public import Qsag.Exec.SeparatedCustodyResource
meta import Qsag.Exec.SeparatedCustodyResource
public import Qsag.Tests.SeparatedCustodyChecks
meta import Qsag.Tests.SeparatedCustodyChecks
public import Qsag.Tests.RssProductionProfileChecks
meta import Qsag.Tests.RssProductionProfileChecks
public section
namespace Qsag.Custody.RequestPolicy.Checks
set_option autoImplicit false
set_option maxRecDepth 4096

def profile := RssProduction.Checks.profile
def peerKey : List UInt8 := List.replicate 32 0x55
def tx := demoQuorumSignedIntent peerKey 0 1 10 3 0 0x01
def request : SessionScheduleReq :=
  ⟨ofLE tx.1.session_id.reverse, 0, toCanonicalSigningBytes tx.1,
    List.replicate 32 0x08, [1, 0]⟩
def input : Input :=
  ⟨request, tx.1, tx.2, 1000, 0,
    [{ Custody.Checks.opening with session := request.sessionId }]⟩
def deployment : Deployment :=
  { deploymentId := Custody.Checks.dep
    signer := Custody.Checks.cfg
    keys := fun i => if i = 0 then Custody.Checks.key else
      ⟨List.replicate 32 0x18, List.replicate 32 0x2A, List.replicate 32 0x44⟩
    rounds := fun _ => ⟨fun _ _ => Custody.Checks.macKeys, [0],
      fun _ => roundCommitment Custody.Checks.dep (intent profile input)⟩
    caps := fun _ => 100
    policies := fun i => demoQuorumCustodian i peerKey (List.replicate 32 0x66)
    numParties := 2
    threshold := 2
    capacity := 5 }

def constructionCheck : IO Unit := do
  let commands := [HistoryCommand.invoke 0 0 input, .invoke 1 0 input]
  let hist := generatedHistory profile deployment commands
  let cs := hist.calls.filterMap (fun e => e.output)
  unless decide (cs.length = 2) && gate profile deployment [] hist input cs do
    throw (IO.userError "contextual production approval quorum failed")
  let s : ResourceState := { resourceInitial deployment with history := hist }
  let started := start profile deployment [] s input cs true
  unless decide (started.durable.nextLeaf = 1 ∧ started.active = [request] ∧
      started.history.shared.coordinator.spent = 3) do
    throw (IO.userError "actual accepted quorum did not burn before activation")
  for bad in [{ input with request := { request with optRand := [0x99] } },
      { input with request := { request with sessionId := request.sessionId + 1 } },
      { input with request := { request with honestApprovers := [0, 1] } }] do
    if gate profile deployment [] hist bad cs then
      throw (IO.userError "old certificate authorized changed request")
  let wrongProfile := { profile with context := [0x99] }
  if gate wrongProfile deployment [] hist input cs then
    throw (IO.userError "old certificate authorized wrong profile")
  let mutated := cs.map (fun c => { c with signature := { c.signature with msgTswCtr := 1 } })
  if gate profile deployment [] hist input mutated then
    throw (IO.userError "mutated production approval accepted")
  if gate profile deployment [] started.history input cs then
    throw (IO.userError "accepted session replayed")
  let lostActivation := start profile deployment [] s input cs false
  unless decide (lostActivation.durable.nextLeaf = 1 ∧ lostActivation.active = []) do
    throw (IO.userError "lost activation refunded reservation")
  let wireState := emit started request [0x73, 0x68, 0x61, 0x72, 0x65]
  let crashedWire := crash wireState
  unless decide (crashedWire.observed.length = 1 ∧ crashedWire.durable.nextLeaf = 1) do
    throw (IO.userError "crash erased intermediate useful wire or burn")
  let produced := produce profile wireState request
  let [(req, bytes)] := produced.buffered
    | throw (IO.userError "actual shared production failed")
  unless decide (req = request ∧ 0 < bytes.length ∧ produced.observed.length = 2) do
    throw (IO.userError "production observation accounting failed")
  match verifyProductionWireBytes cshake256Suite profile.params
      (encodePublicKeyWire (RssProduction.enrolledKey profile)) (RssProduction.payload profile request) bytes with
  | .accept => pure ()
  | _ => throw (IO.userError "actual shared production wire invalid")
  let lostReturn := crash (commitOutput produced)
  let retried := retry lostReturn request
  unless decide (retried.returned = [(request, bytes)] ∧ retried.observed.length = 2 ∧
      retried.durable.nextLeaf = 1 ∧ retried.active = []) do
    throw (IO.userError "lost-return retry recomputed or erased visible output")
  let changedRetry := retry lostReturn { request with optRand := [] }
  unless decide (changedRetry.returned = []) do
    throw (IO.userError "changed request obtained cached bytes")
  let crashBeforeCommit := crash produced
  unless decide (crashBeforeCommit.observed.length = 2 ∧ crashBeforeCommit.buffered = [] ∧
      crashBeforeCommit.durable.cached = []) do
    throw (IO.userError "precommit crash erased useful output or manufactured cache")
  IO.println s!"contextual custody resource: distinct-key approvals and actual shared {bytes.length}-byte production; full request/profile binding, mutation, replay, durable burn, intermediate wire, crash, and lost-return retry passed"

end Qsag.Custody.RequestPolicy.Checks
end
#eval Qsag.Custody.RequestPolicy.Checks.constructionCheck
