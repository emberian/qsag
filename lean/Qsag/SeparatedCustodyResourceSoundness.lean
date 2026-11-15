module
public import Qsag.SeparatedCustodyUcResource
import all Qsag.SeparatedCustodyUcResource
import all Qsag.RssProductionProfile
import Qsag.Tactic.AssuranceKit
public section
namespace Qsag.Custody.RequestPolicy
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Only the actual shared producer creates a result eligible for durable cache
and API return. Arbitrary intermediate network observations are not signatures. -/
structure OutputValid (profile : RssProduction.Profile) (s : ResourceState) : Prop where
  buffered : ∀ e ∈ s.buffered, RssProduction.partialOutput profile e.1 = .ok e.2
  cached : ∀ e ∈ s.durable.cached, RssProduction.partialOutput profile e.1 = .ok e.2
  returned : ∀ e ∈ s.returned, RssProduction.partialOutput profile e.1 = .ok e.2

theorem initial_output_valid (profile : RssProduction.Profile) (d : Deployment) :
    OutputValid profile (resourceInitial profile d) := by
  constructor <;> intro e he <;> cases he

theorem step_output_valid (profile : RssProduction.Profile) (d : Deployment)
    (corrupt : List Nat) (s : ResourceState) (c : ResourceCommand)
    (h : OutputValid profile s) : OutputValid profile (resourceStep profile d corrupt s c) := by
  cases c with
  | approve i anchor a => exact ⟨h.buffered, h.cached, h.returned⟩
  | schedule a cs activate =>
    change OutputValid profile (start profile d corrupt s a cs activate)
    unfold start
    split
    · exact h
    · split <;> exact ⟨h.buffered, h.cached, h.returned⟩
  | wire req bytes =>
    change OutputValid profile (emit s req bytes)
    unfold emit
    split <;> exact ⟨h.buffered, h.cached, h.returned⟩
  | produce req =>
    change OutputValid profile (produce profile s req)
    unfold produce
    split
    · split
      · exact ⟨h.buffered, h.cached, h.returned⟩
      next bytes hout =>
        refine ⟨?_, h.cached, h.returned⟩
        intro e he
        rcases List.mem_cons.mp he with he | he
        · subst e; exact hout
        · exact h.buffered e he
    · exact h
  | commit =>
    refine ⟨(fun _ he => by cases he), ?_, h.returned⟩
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact h.buffered e he
    · exact h.cached e he
  | retry req =>
    change OutputValid profile (retry s req)
    unfold retry
    split
    · exact h
    next pair hf =>
      refine ⟨h.buffered, h.cached, ?_⟩
      intro e he
      rcases List.mem_cons.mp he with he | he
      · subst e; exact h.cached pair (List.mem_of_find?_eq_some hf)
      · exact h.returned e he
  | crash => exact ⟨(fun _ he => by cases he), h.cached, h.returned⟩

theorem run_output_valid (profile : RssProduction.Profile) (d : Deployment)
    (corrupt : List Nat) (s : ResourceState) (cs : List ResourceCommand)
    (h : OutputValid profile s) : OutputValid profile (resourceRun profile d corrupt s cs) := by
  induction cs generalizing s with
  | nil => exact h
  | cons c cs ih => exact ih _ (step_output_valid profile d corrupt s c h)

/-- Every returned or retried production signature verifies under the same
shared-material enrollment on the exact contextual request. Failures, crashes,
and arbitrary host wire bytes cannot be converted into a successful API output. -/
theorem returned_production_sound (profile : RssProduction.Profile) (d : Deployment)
    (corrupt : List Nat) (cs : List ResourceCommand) (req : SessionScheduleReq)
    (bytes : List UInt8)
    (he : (req, bytes) ∈ (resourceRun profile d corrupt (resourceInitial profile d) cs).returned) :
    ∃ sig, RssProduction.sharedSign profile req = some sig ∧
      encodeProductionSigWire profile.params sig = .ok bytes ∧
      decodeProductionSigWire profile.params bytes = .ok sig ∧
      bytes.length = profile.params.wireSigBytes ∧
      verifyProductionPqHashSig cshake256Suite profile.params (RssProduction.enrolledKey profile)
        (RssProduction.payload profile req) sig = true := by
  have hv := run_output_valid profile d corrupt (resourceInitial profile d) cs
    (initial_output_valid profile d)
  have ho : RssProduction.partialOutput profile req = .ok bytes := hv.returned (req, bytes) he
  exact RssProduction.partialOutput_sound profile req bytes ho

end Qsag.Custody.RequestPolicy
end
#verify_constructive Qsag.Custody.RequestPolicy.returned_production_sound
