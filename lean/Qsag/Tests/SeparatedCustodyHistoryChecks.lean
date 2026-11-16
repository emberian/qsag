module
public import Qsag.Custody.CustodySuiteFull
public import Qsag.Custody.SeparatedCustody
public import Qsag.Tests.SeparatedCustodyChecks
public section
namespace Qsag.Custody.HistoryChecks
set_option autoImplicit false

def peerKey : List UInt8 := List.replicate 32 0x55
def firstTx := demoQuorumSignedIntent peerKey 0 1 10 3 0 0x01
def secondTx := demoQuorumSignedIntent peerKey 0 1 11 3 3 0x02
def firstIntent := transactionIntent firstTx.1 0 1
def secondIntent := transactionIntent secondTx.1 1 2

def deployment : Deployment :=
  { deploymentId := Checks.dep
    signer := Checks.cfg
    keys := fun i => if i = 0 then Checks.key else
      ⟨List.replicate 32 0x18, List.replicate 32 0x2A, List.replicate 32 0x44⟩
    rounds := fun _ =>
      ⟨fun _ _ => Checks.macKeys, [0], fun session =>
        if session = firstIntent.session then roundCommitment Checks.dep firstIntent
        else roundCommitment Checks.dep secondIntent⟩
    caps := fun _ => 100
    policies := fun i => demoQuorumCustodian i peerKey (List.replicate 32 0x66)
    numParties := 2
    threshold := 2
    capacity := 5 }

def firstInvocation : Invocation :=
  ⟨firstTx.1, firstTx.2, 1000, 0, 1,
    [{ Checks.opening with session := firstIntent.session }]⟩
def secondInvocation : Invocation :=
  ⟨secondTx.1, secondTx.2, 1000, 1, 2,
    [{ Checks.opening with session := secondIntent.session, round := 1 }]⟩

def certificatesFor (s : HistoryState) (r : Intent) : List Certificate :=
  (s.calls.filterMap (fun e => e.output)).filter (fun c => decide (c.intent = r))

/-- Real two-party execution uses distinct nonzero production signing keys.
The second pair of valid certificates is rejected by shared accounting, while
failed signing produces no certificate and still leaves its local burn. -/
def checkHistory : IO Unit := do
  let rejectedStart := generatedHistory deployment
    [.invoke 0 0 { firstInvocation with tags := [] }]
  unless !((rejectedStart.parties 0).vault.poisoned) &&
      decide ((rejectedStart.parties 0).vault.durable.spent = 0) do
    throw (IO.userError "ordinary policy rejection became an anchor fault")
  let anchorFault := generatedHistory deployment [.invoke 0 9 firstInvocation]
  unless (anchorFault.parties 0).vault.poisoned &&
      (anchorFault.calls.filterMap (fun e => e.output)).isEmpty do
    throw (IO.userError "real mismatched mint anchor was ignored")
  let ready := historyRun deployment rejectedStart
    [.invoke 0 0 firstInvocation, .invoke 1 0 firstInvocation]
  let certs := certificatesFor ready firstIntent
  unless decide (certs.length = 2) do
    throw (IO.userError "two actual policy invocations did not issue two certificates")
  unless certs.all (verifyCertificate deployment.signer (publicKeys deployment) deployment.deploymentId firstIntent) do
    throw (IO.userError "generated two-party certificates failed verification")
  let (shared, accepted) := submitRecorded deployment ready.shared firstIntent certs
  unless accepted do
    throw (IO.userError "actual two-party policy quorum rejected")
  -- A second deployment that reuses every key and parameter and differs only in its identifier.
  let twin := { deployment with deploymentId := Checks.dep + 1 }
  if (submitRecorded twin (historyInitial twin).shared firstIntent certs).2 then
    throw (IO.userError "same-key twin deployment consumed this deployment's certificates")
  let afterFirst := historyStep deployment ready (.submit firstIntent certs)
  unless decide (shared.coordinator.spent = 3 ∧ afterFirst.shared.coordinator.spent = 3 ∧
      afterFirst.shared.accepted.length = 1) do
    throw (IO.userError "shared accepted trace and amount diverged")
  if (submitRecorded deployment afterFirst.shared firstIntent certs).2 then
    throw (IO.userError "shared history accepted session replay")
  let bad := { firstIntent with message := [0x78] }
  let relabelled := certs.map (fun c => { c with intent := bad })
  if (submitRecorded deployment (historyInitial deployment).shared bad relabelled).2 then
    throw (IO.userError "full-context signature relabelling accepted by shared history")
  let readySecond := historyRun deployment afterFirst
    [.invoke 0 1 secondInvocation, .invoke 1 1 secondInvocation]
  let secondCerts := certificatesFor readySecond secondIntent
  unless decide (secondCerts.length = 2) &&
      secondCerts.all (verifyCertificate deployment.signer (publicKeys deployment) deployment.deploymentId secondIntent) do
    throw (IO.userError "second actual transaction lacked valid two-party certificates")
  let rejected := historyStep deployment readySecond (.submit secondIntent secondCerts)
  if (submitRecorded deployment readySecond.shared secondIntent secondCerts).2 then
    throw (IO.userError "valid second quorum exceeded aggregate accepted spend cap")
  unless decide (rejected.shared.coordinator.spent = 3 ∧ rejected.shared.accepted.length = 1 ∧
      (rejected.parties 0).vault.durable.spent = 6 ∧ (rejected.parties 1).vault.durable.spent = 6) do
    throw (IO.userError "rejected shared submission refunded local burns or charged acceptance")
  let abortDeployment := { deployment with signer := { deployment.signer with grindLimit := 0 } }
  let aborted := generatedHistory abortDeployment [.invoke 0 0 firstInvocation, .forget 0]
  unless decide ((aborted.parties 0).vault.durable.spent = 3 ∧
      (aborted.parties 0).vault.attempted.length = 1 ∧ aborted.shared.coordinator.spent = 0 ∧
      aborted.shared.accepted.length = 0) && (aborted.calls.filterMap (fun e => e.output)).isEmpty do
    throw (IO.userError "failed production signing lost its burn or manufactured an output")
  IO.println "custody history check: distinct-key two-party policy quorum, shared accepted spend/session trace, full-context rejection, same-key twin-deployment rejection, valid over-cap quorum rejection, and failed-signing burn accounting passed"

end Qsag.Custody.HistoryChecks
end
#eval Qsag.Custody.HistoryChecks.checkHistory
