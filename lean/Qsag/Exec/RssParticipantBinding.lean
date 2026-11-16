module
public import Qsag.Exec.RssProductionProfile
public import Qsag.Exec.RssParticipantSponge
import all Qsag.Exec.RssProductionProfile
import all Qsag.Exec.IdealOutputBoundary
import all Qsag.Exec.InteractiveUcEngine
import all Qsag.Exec.RssParticipantSponge
import Qsag.Tactic.AssuranceKit

/-!
Canonical request/invocation binding shared by the production profile and local
participant messages. This is an explicit new protocol format. It does not claim
equality with the deployed Rust wire format. Invocation counters and distinct
phase labels prevent local round numbers from aliasing separate hash calls.
The caller must advance invocation numbers and provision corresponding mask
resources; injective labels alone do not establish freshness or independence.
-/
public section
namespace Qsag.RssParticipant
set_option autoImplicit false

/-- Enrollment projection supplied to one signing participant. Neither the third
seed share nor a reconstructed signing key appears in this local material. -/
structure LocalSigningMaterial where
  seedOwn : List UInt8
  seedNext : List UInt8
  prfOwn : List UInt8
  prfNext : List UInt8
  pkSeed : List UInt8
  deriving DecidableEq, Repr

def localSigningMaterial (profile : RssProduction.Profile) (party : Fin 3) : LocalSigningMaterial :=
  let m := profile.material
  if party.val = 0 then ⟨m.seed.b0, m.seed.b1, m.prf.b0, m.prf.b1, m.pkSeed⟩
  else if party.val = 1 then ⟨m.seed.b1, m.seed.b2, m.prf.b1, m.prf.b2, m.pkSeed⟩
  else ⟨m.seed.b2, m.seed.b0, m.prf.b2, m.prf.b0, m.pkSeed⟩

/-- Static corruption must expose long-lived local seed/PRF shares, in addition
to transient Node state and `corruptMaskQuery`. -/
def corruptSigningMaterial (profile : RssProduction.Profile) (corrupt : Option (Fin 3)) :
    Option LocalSigningMaterial := corrupt.map (localSigningMaterial profile)

theorem corruptSigningMaterial_exact (profile : RssProduction.Profile) (party : Fin 3) :
    corruptSigningMaterial profile (some party) = some (localSigningMaterial profile party) := by
  simp [corruptSigningMaterial]

def invocationBinding (profile : RssProduction.Profile) (request : SessionScheduleReq)
    (invocation : Nat) (phase : List UInt8) : List UInt8 :=
  encodeMultiFrame ["QSAG.RSS.PARTICIPANT/v1".toUTF8.data.toList,
    RssProduction.payload profile request, leb128 invocation, phase]

theorem invocationBinding_request (profile : RssProduction.Profile)
    (a b : SessionScheduleReq) (i j : Nat) (phase phase' : List UInt8)
    (h : invocationBinding profile a i phase = invocationBinding profile b j phase') : a = b := by
  have hf := encodeMultiFrame_injective h
  simp only [List.cons.injEq] at hf
  exact RssProduction.payload_request_binding hf.2.1

theorem invocationBinding_invocation (p q : RssProduction.Profile)
    (a b : SessionScheduleReq) (i j : Nat) (phase phase' : List UInt8)
    (h : invocationBinding p a i phase = invocationBinding q b j phase') : i = j := by
  have hf := encodeMultiFrame_injective h
  simp only [List.cons.injEq] at hf
  exact (leb128_prefix_inj (show leb128 i ++ [] = leb128 j ++ [] by
    simpa using hf.2.2.1)).1

theorem invocationBinding_phase (p q : RssProduction.Profile)
    (a b : SessionScheduleReq) (i j : Nat) (phase phase' : List UInt8)
    (h : invocationBinding p a i phase = invocationBinding q b j phase') : phase = phase' := by
  have hf := encodeMultiFrame_injective h
  simp only [List.cons.injEq] at hf
  exact hf.2.2.2.1

/-- Canonical application input to the honest participant driver. Gate evidence
remains pending in its Nodes result; this is not the ideal service's public cut. -/
def cshakeForRequest (profile : RssProduction.Profile) (request : SessionScheduleReq)
    (invocation : Nat) (phase customization : List UInt8) (input : RssByteShares)
    (localTape : Nat → Nat → RssPrfZeroSeeds) : Nodes × Option RssByteShares :=
  cshakeParticipant 32 (invocationBinding profile request invocation phase) customization input localTape

theorem cshakeForRequest_refines_existing (profile : RssProduction.Profile)
    (request : SessionScheduleReq) (invocation : Nat) (phase customization : List UInt8)
    (input : RssByteShares) (localTape : Nat → Nat → RssPrfZeroSeeds)
    (oldTape : Nat → Nat → Nat → RssPrfZeroSeeds) (hWf : input.WellFormed) :
    ((cshakeForRequest profile request invocation phase customization input localTape).2.map
      reconstructRssBytes) =
      some (reconstructRssBytes (mpcCshake256SharedRss 32 customization input oldTape)) := by
  exact cshakeParticipant_refines_existing 32 _ _ _ _ _ hWf (by rw [shake256RateBytes_eq]; decide)

/-- A message for a distinct invocation cannot be accepted even if its local
round number and nominal sender are otherwise valid. -/
theorem other_invocation_aborts (profile : RssProduction.Profile) (request : SessionScheduleReq)
    (i j : Nat) (phase phase' : List UInt8) (node : Node) (message : Envelope)
    (hn : node.binding = invocationBinding profile request i phase)
    (hm : message.binding = invocationBinding profile request j phase') (hne : j ≠ i) :
    (receive node message).phase = .aborted := by
  apply wrong_binding_aborts
  intro heq
  apply hne
  exact invocationBinding_invocation profile profile request request j i phase' phase
    (hm.symm.trans (heq.trans hn))

theorem other_request_aborts (profile : RssProduction.Profile) (a b : SessionScheduleReq)
    (i j : Nat) (phase phase' : List UInt8) (node : Node) (message : Envelope)
    (hn : node.binding = invocationBinding profile a i phase)
    (hm : message.binding = invocationBinding profile b j phase') (hne : b ≠ a) :
    (receive node message).phase = .aborted := by
  apply wrong_binding_aborts
  intro heq
  exact hne (invocationBinding_request profile b a j i phase' phase
    (hm.symm.trans (heq.trans hn)))

#verify_constructive corruptSigningMaterial_exact invocationBinding_request invocationBinding_invocation invocationBinding_phase
  cshakeForRequest_refines_existing other_invocation_aborts other_request_aborts
end Qsag.RssParticipant
