module
public import Qsag.Exec.RssSigningBatches
public import Qsag.Tests.RssSigningChecks
public import Qsag.Exec.RssSigningBackend
public import Qsag.Exec.RssSigningProgram

/-! Actual grouped query producer checks. The candidate observation is external
correctness instrumentation; the producer has no unchecked bytes-release port. -/
public section
namespace Qsag.RssSigning.BatchChecks
set_option autoImplicit false

def groupedProducerCheck : IO Unit := do
  let profile := Checks.profile
  let request := Checks.request
  let digits := [0, 1]
  let selectedQueries := (wotsRowQueries profile.params 0 0 1 digits 1).take 2
  let otherQueries := (wotsRowQueries profile.params 0 0 1 digits 2).take 2
  let queries := selectedQueries ++ otherQueries
  let batch := produceBatch (preparePublic profile request) profile.material Checks.tape 42 queries
  unless decide (queries = [.wotsChain 0 0 1 0 0, .wotsChain 0 0 1 1 1,
      .wotsChain 0 0 2 0 (profile.params.w - 1), .wotsChain 0 0 2 1 (profile.params.w - 1)]) do
    throw (IO.userError "WOTS grouped coordinate/stop selection mismatch")
  unless decide (batch.nextInvocation = 46 ∧ batch.computations.length = 4) do
    throw (IO.userError "group did not preserve invocation count")
  unless decide (candidateBatch batch = queries.map (answer (RssProduction.sharedOracle profile))) do
    throw (IO.userError "actual grouped participant computation mismatch")
  unless batch.computations.all (fun computation => !computation.evidence.isEmpty) do
    throw (IO.userError "group discarded concrete participant evidence")
  let empty := produceBatch (preparePublic profile request) profile.material Checks.tape 46 []
  unless decide (empty.nextInvocation = 46 ∧ empty.computations.length = 0) do
    throw (IO.userError "empty group advanced or computed")
  IO.println "Grouped WOTS producer: selected digit stops and other-leaf endpoints match actual shared oracle;4 outputs retain participant evidence and distinct invocation coordinates"


end Qsag.RssSigning.BatchChecks
