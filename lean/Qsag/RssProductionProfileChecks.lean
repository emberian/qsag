module
public import Qsag.RssProductionProfile
import all Qsag.RssProductionProfile
import all Qsag.HashSigs
import all Qsag.ThresholdMpc
import Qsag.Tactic.AssuranceKit

/-! Executable construction checks, not a hardness benchmark. Full-width production
cSHAKE Jorts with four leaves is used. The checked reference evaluator reconstructs
the key; `release_eq_reference` transfers its exact result to the shared computation.
No successful-signature assumption or native-decision axiom is used in a theorem. -/

public section
namespace Qsag.RssProduction.Checks
set_option autoImplicit false
set_option maxRecDepth 4096

def seed : RssByteShares :=
  ⟨List.replicate 32 0x11, List.replicate 32 0x22, List.replicate 32 0x24⟩
def prf : RssByteShares :=
  ⟨List.replicate 32 0x33, List.replicate 32 0x44, List.replicate 32 0x5e⟩
def material : Material :=
  ⟨seed, prf, List.replicate 32 0x43, by exact ⟨rfl, rfl⟩, by exact ⟨rfl, rfl⟩, by decide, by decide, by decide⟩
def profile : Profile :=
  ⟨material, compactJortsProdParams, "integration-check".toUTF8.data.toList, 4096,
    fun _ _ _ _ => ⟨0x123, 0x456, 0x789⟩⟩
def request : SessionScheduleReq :=
  ⟨17, 0, List.replicate 32 0x55 ++ [1], List.replicate 32 0x08, [0, 1]⟩

theorem production_profile : profile.params.productionWellFormed = true := by decide

theorem nonzero_distinct_material :
    reconstructRssBytes seed = List.replicate 32 0x17 ∧
    reconstructRssBytes prf = List.replicate 32 0x29 ∧
    reconstructRssBytes seed ≠ reconstructRssBytes prf := by decide

/-- A concrete failure of the actual shared signing computation: leaf four is
    outside this valid four-leaf profile. -/
theorem exhausted_leaf_is_failure :
    partialOutput profile { request with reqEpoch := 4 } = .error .signingUnavailable := by
  exact partialOutput_outOfRange profile _ (by decide) (by decide)

/-- Full request binding retains the same-prefix regression for this actual profile. -/
theorem changed_suffix_binding :
    payload profile request ≠ payload profile
      { request with msg := List.replicate 32 0x55 ++ [2] } := by
  intro h
  have hr := payload_request_binding h
  have hm := congrArg SessionScheduleReq.msg hr
  exact (by decide : request.msg ≠ List.replicate 32 0x55 ++ [2]) hm

/-- Both production branches are linked to the shared oracle by a proved theorem;
    this concrete profile selects stateful Jorts. -/
theorem concrete_release_refinement (req : SessionScheduleReq) (wal : WalLatchState) :
    release profile req wal = referenceRelease profile req wal :=
  release_eq_reference profile req wal

private def rejectChanged (p : Profile) (req : SessionScheduleReq)
    (sig : PqHashSig) (label : String) : IO Unit := do
  if verifyProductionPqHashSig cshake256Suite p.params (enrolledKey p) (payload p req) sig then
    throw (IO.userError ("signature accepted changed " ++ label))

/-- Run explicitly with Lean's evaluator. Only the reference side is executed for
    the complete signature; the shared side is connected by the checked equality. -/
def constructionCheck : IO Unit := do
  let (committed, result) := referenceRelease profile request (initial profile)
  let .ok raw := result | throw (IO.userError "production signing or encoding failed")
  unless decide (0 < raw.length) do
    throw (IO.userError "empty signature output")
  let .ok sig := decodeProductionSigWire profile.params raw
    | throw (IO.userError "released bytes failed decoding")
  match verifyProductionWireBytes cshake256Suite profile.params
      (encodePublicKeyWire (enrolledKey profile)) (payload profile request) raw with
  | .accept => pure ()
  | _ => throw (IO.userError "released production wire failed verification")
  unless decide (committed.nextEpoch = 1 ∧ committed.poisoned = false) do
    throw (IO.userError "successful signing did not commit epoch")
  let (retried, replay) := referenceRelease profile request committed
  let .ok replayBytes := replay | throw (IO.userError "exact retry failed")
  unless decide (retried = committed ∧ replayBytes = raw) do
    throw (IO.userError "exact retry changed bytes or state")
  let changed := { request with msg := List.replicate 32 0x55 ++ [2] }
  match (referenceRelease profile changed committed).2 with
  | .error (.wal .staleOrOutOfOrderEpoch) => pure ()
  | _ => throw (IO.userError "changed suffix replayed prior signature")
  rejectChanged profile changed sig "message suffix"
  rejectChanged profile { request with sessionId := 18 } sig "session"
  rejectChanged profile { request with reqEpoch := 1 } sig "epoch"
  rejectChanged profile { request with optRand := [9] } sig "randomness"
  rejectChanged profile { request with honestApprovers := [0, 2] } sig "approvers"
  rejectChanged { profile with context := [99] } request sig "context"
  rejectChanged { profile with grindLimit := 4097 } request sig "resource limit"
  match (referenceRelease { profile with grindLimit := 4097 } request committed).2 with
  | .error (.wal .pkDigestMismatch) => pure ()
  | _ => throw (IO.userError "changed profile reused prior enrollment")
  match encodeResult profile.params (some { sig with msgTswCtr := 1 }) with
  | .error (.encoding .signatureFraming) => pure ()
  | _ => throw (IO.userError "malformed signature serialized as success")
  let exhausted := { request with reqEpoch := 4 }
  let (failed, failResult) := referenceRelease profile exhausted
    { initial profile with nextEpoch := 4 }
  let .error .signingUnavailable := failResult
    | throw (IO.userError "out-of-range leaf did not fail signing")
  unless decide (failed.poisoned = true ∧ failed.latchedRecord = none) do
    throw (IO.userError "out-of-range leaf was not a quarantined failure")
  let noGrind := { profile with grindLimit := 0 }
  let (grindFailed, grindResult) := referenceRelease noGrind request (initial noGrind)
  let .error .signingUnavailable := grindResult
    | throw (IO.userError "zero grind budget did not fail signing")
  unless grindFailed.poisoned do
    throw (IO.userError "zero grind budget was not a genuine failure")
  IO.println s!"RSS production profile: nonempty {raw.length}-byte signature verified; exact retry, changed fields, encoding failure, leaf exhaustion and grind exhaustion passed"

#verify_constructive production_profile nonzero_distinct_material exhausted_leaf_is_failure
  changed_suffix_binding concrete_release_refinement
end Qsag.RssProduction.Checks
end
