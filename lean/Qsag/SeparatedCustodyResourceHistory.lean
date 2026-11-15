module
public import Qsag.SeparatedCustodyUcResource
import all Qsag.SeparatedCustodyUcResource
import all Qsag.SeparatedCustodyRequestHistory
import Qsag.Tactic.AssuranceKit
public section
namespace Qsag.Custody.RequestPolicy
set_option autoImplicit false

/-- Project only transitions actually performed by the operational resource.
In particular a rejected schedule does not manufacture a shared acceptance. -/
def historyCommandOf (profile : RssProduction.Profile) (d : Deployment) (corrupt : List Nat)
    (s : ResourceState) : ResourceCommand → List HistoryCommand
  | .approve i anchor a => [.invoke i anchor a]
  | .schedule a cs _ =>
    if s.poisoned || decide (a.request.reqEpoch ≠ s.durable.nextLeaf) then []
    else if gate profile d corrupt s.history a cs then [.submit (intent profile a) cs] else []
  | _ => []

theorem step_history (profile : RssProduction.Profile) (d : Deployment) (corrupt : List Nat)
    (s : ResourceState) (c : ResourceCommand) :
    (resourceStep profile d corrupt s c).history =
      historyRun profile d s.history (historyCommandOf profile d corrupt s c) := by
  cases c with
  | approve i anchor a => rfl
  | schedule a cs activate =>
    simp only [resourceStep, start, historyCommandOf]
    split
    · rfl
    · split <;> rfl
  | wire req bytes =>
    simp only [resourceStep, emit, historyCommandOf, historyRun]
    split <;> rfl
  | produce req =>
    simp only [resourceStep, produce, historyCommandOf, historyRun]
    split
    · split <;> rfl
    · rfl
  | commit => rfl
  | retry req =>
    simp only [resourceStep, retry, historyCommandOf, historyRun]
    split <;> rfl
  | crash => rfl

def projectedHistory (profile : RssProduction.Profile) (d : Deployment) (corrupt : List Nat) :
    ResourceState → List ResourceCommand → List HistoryCommand
  | _, [] => []
  | s, c :: cs => historyCommandOf profile d corrupt s c ++
      projectedHistory profile d corrupt (resourceStep profile d corrupt s c) cs

theorem historyRun_append (profile : RssProduction.Profile) (d : Deployment)
    (s : HistoryState) (xs ys : List HistoryCommand) :
    historyRun profile d s (xs ++ ys) = historyRun profile d (historyRun profile d s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih _

theorem run_history (profile : RssProduction.Profile) (d : Deployment) (corrupt : List Nat)
    (s : ResourceState) (cs : List ResourceCommand) :
    (resourceRun profile d corrupt s cs).history =
      historyRun profile d s.history (projectedHistory profile d corrupt s cs) := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    simp only [resourceRun, projectedHistory, historyRun_append]
    rw [ih, step_history]

theorem resource_history_is_generated (profile : RssProduction.Profile) (d : Deployment)
    (corrupt : List Nat) (cs : List ResourceCommand) :
    (resourceRun profile d corrupt (resourceInitial profile d) cs).history =
      generatedHistory profile d (projectedHistory profile d corrupt (resourceInitial profile d) cs) :=
  run_history profile d corrupt _ cs

/-- Contextual approval provenance and one-time accounting apply at every actual
resource execution prefix, including interrupted production and lost returns. -/
theorem resource_history_valid (profile : RssProduction.Profile) (d : Deployment)
    (corrupt : List Nat) (cs : List ResourceCommand) :
    Generated profile d (resourceRun profile d corrupt (resourceInitial profile d) cs).history := by
  rw [resource_history_is_generated]
  exact generatedHistory_valid profile d _

end Qsag.Custody.RequestPolicy
end
#verify_constructive Qsag.Custody.RequestPolicy.resource_history_is_generated
#verify_constructive Qsag.Custody.RequestPolicy.resource_history_valid
