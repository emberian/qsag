module
public import Qsag.Custody.SeparatedCustody
public import Qsag.Tests.SeparatedCustodyHistoryChecks
import all Qsag.Custody.SeparatedCustody
import all Qsag.Tests.SeparatedCustodyHistoryChecks
import all Qsag.Tests.SeparatedCustodyChecks
public section
namespace Qsag.Custody.ReleaseChecks
set_option autoImplicit false
open Release HistoryChecks

def ready (i : Nat) : Release.State :=
  let s := start ((historyInitial deployment).parties i)
  reserve (deployment.rounds i) (deployment.caps i) 0 s
    firstInvocation.transaction firstInvocation.tags firstInvocation.timestamp
    firstInvocation.round firstInvocation.leaf firstInvocation.openings

def check : IO Unit := do
  let s := ready 0
  unless decide (s.custody.vault.durable.spent = 3) && s.custody.vault.active.isSome do
    throw (IO.userError "policy reservation did not create the real admitted grant")
  let begun := begin s.custody.vault.durable.anchor s firstIntent
  unless begun.pending.isSome && begun.custody.vault.active.isNone &&
      decide (begun.custody.vault.attempted.length = 1) do
    throw (IO.userError "producer continuation preceded permit consumption")
  let preCrash := compute deployment.signer (deployment.keys 0) (crash begun)
  unless preCrash.buffered.isNone && preCrash.produced.isEmpty &&
      decide (preCrash.custody.vault.durable.spent = 3 ∧
        preCrash.custody.vault.attempted.length = 1) do
    throw (IO.userError "crash before compute refunded or manufactured a signature")
  let made := compute deployment.signer (deployment.keys 0) begun
  let some c := made.buffered | throw (IO.userError "actual partial production signer failed fixture")
  unless verify deployment.signer (publicKeys deployment 0) deployment.deploymentId
      c.party c.intent c.signature do
    throw (IO.userError "split producer returned an invalid certificate")
  let postCrash := publish (crash made)
  unless postCrash.published.isEmpty && postCrash.buffered.isNone &&
      decide (postCrash.produced.length = 1 ∧ postCrash.custody.vault.durable.spent = 3) do
    throw (IO.userError "post-computation crash erased useful-output accounting")
  let retried := compute deployment.signer (deployment.keys 0)
    (begin postCrash.custody.vault.durable.anchor postCrash firstIntent)
  unless retried.buffered.isNone && decide (retried.produced.length = 1 ∧
      retried.custody.vault.attempted.length = 1) do
    throw (IO.userError "copied handle after crash repeated producer")
  let returned := publish (publish made)
  unless decide (returned.published.length = 1) do
    throw (IO.userError "publication replay duplicated output")
  let other := ready 1
  let otherMade := compute deployment.signer (deployment.keys 1)
    (begin other.custody.vault.durable.anchor other firstIntent)
  let some otherCert := otherMade.buffered | throw (IO.userError "second production signer failed")
  -- The lost return does not make its already produced certificate useless.
  unless (submitRecorded deployment (historyInitial deployment).shared firstIntent [c, otherCert]).2 do
    throw (IO.userError "potentially useful pre-crash output did not compose into actual quorum")
  let failed := compute { deployment.signer with grindLimit := 0 } (deployment.keys 0) begun
  unless failed.buffered.isNone && decide (failed.produced.length = 1 ∧
      failed.custody.vault.attempted.length = 1 ∧ failed.custody.vault.durable.spent = 3) do
    throw (IO.userError "failed producer was refunded or successful output invented")
  IO.println "custody split release: actual distinct-key quorum; pre/post-production crashes, useful lost-return output, replay, zero-grind failure, and retained burns passed"

end Qsag.Custody.ReleaseChecks
end
#eval Qsag.Custody.ReleaseChecks.check
