module
public import Qsag.Exec.RssParticipantMachine
import Qsag.Tactic.AssuranceKit

/-!
Static at-most-one-corrupt scheduler semantics for the participant round machine.
The communication resource is private and authenticated: the adversary sees
payloads only on channels incident to its corrupted party. All-message storage
is internal resource state, not the adversary view. The scheduler may delay,
reorder, duplicate, or omit delivery and let its corrupted sender send arbitrary
values. This module does not yet simulate the active-check transcript.
-/

public section
namespace Qsag.RssParticipant
set_option autoImplicit false

@[expose] def Nodes.get (nodes : Nodes) (party : Fin 3) : Node :=
  if party.val = 0 then nodes.n0 else if party.val = 1 then nodes.n1 else nodes.n2

@[expose] def Nodes.set (nodes : Nodes) (party : Fin 3) (node : Node) : Nodes :=
  if party.val = 0 then { nodes with n0 := node }
  else if party.val = 1 then { nodes with n1 := node } else { nodes with n2 := node }

/-- Observable metadata of an honest-to-honest private message. -/
structure MessageLabel where
  sender : Fin 3
  receiver : Fin 3
  binding : List UInt8
  round : Nat
  deriving DecidableEq, Repr

@[expose] def Envelope.label (m : Envelope) : MessageLabel :=
  ⟨m.sender, m.receiver, m.binding, m.round⟩

structure Network where
  nodes : Nodes
  emitted : List Envelope
  deriving DecidableEq, Repr

/-- The corrupted sender's strategy lives outside the honest node algorithm. -/
inductive Command where
  | compute (party : Fin 3)
  | deliver (messageIndex : Nat)
  | corruptSend (message : Envelope)
  | abort (party : Fin 3)
  deriving DecidableEq, Repr

/-- `none` or `some party` implements a static corruption budget of at most one. -/
structure NetworkView where
  corruptState : Option Node
  labels : List MessageLabel
  visiblePayloads : List Envelope
  deriving DecidableEq, Repr

@[expose] def incident (corrupt : Option (Fin 3)) (message : Envelope) : Bool :=
  match corrupt with
  | none => false
  | some party => decide (message.sender = party) || decide (message.receiver = party)

@[expose] def observe (corrupt : Option (Fin 3)) (network : Network) : NetworkView :=
  ⟨corrupt.map network.nodes.get, network.emitted.map Envelope.label,
   network.emitted.filter (incident corrupt)⟩

/-- Corruption also exposes its pairwise mask resource. This adaptive read port
permits arbitrary round/lane queries, including future coordinates. Omitting it
would understate the corrupted participant's knowledge. The actual finite PRF-key
resource and its distribution replacement are separate instantiations. -/
@[expose] def corruptMaskQuery (corrupt : Option (Fin 3))
    (localMasks : Fin 3 → Nat → LocalMasks) (round lane : Nat) : Option (UInt64 × UInt64) :=
  corrupt.map (fun party => localMasks party round lane)

theorem corruptMaskQuery_exact (party : Fin 3)
    (localMasks : Fin 3 → Nat → LocalMasks) (round lane : Nat) :
    corruptMaskQuery (some party) localMasks round lane = some (localMasks party round lane) := by
  simp [corruptMaskQuery]

/-- Only the selected party's mask resource is passed into its local transition. -/
@[expose] def networkStep (corrupt : Option (Fin 3))
    (localMasks : Fin 3 → Nat → LocalMasks) (network : Network) (command : Command) : Network :=
  match command with
  | .compute party =>
      let node := network.nodes.get party
      let result := prepare node (localMasks party node.cursor)
      { nodes := network.nodes.set party result.1,
        emitted := network.emitted ++ result.2.toList }
  | .deliver index =>
      match network.emitted[index]? with
      | none => network
      | some message =>
          { network with
            nodes := network.nodes.set message.receiver
              (receive (network.nodes.get message.receiver) message) }
  | .corruptSend message =>
      if corrupt = some message.sender then
        { network with emitted := network.emitted ++ [message] }
      else network
  | .abort party =>
      { network with nodes := network.nodes.set party (abortNode (network.nodes.get party)) }

@[expose] def runCommands (corrupt : Option (Fin 3)) (localMasks : Fin 3 → Nat → LocalMasks) :
    Network → List Command → Network
  | network, [] => network
  | network, command :: commands =>
      runCommands corrupt localMasks (networkStep corrupt localMasks network command) commands

theorem only_corrupt_sender_can_inject (corrupt : Option (Fin 3))
    (localMasks : Fin 3 → Nat → LocalMasks) (network : Network) (message : Envelope)
    (h : corrupt ≠ some message.sender) :
    networkStep corrupt localMasks network (.corruptSend message) = network := by
  simp [networkStep, h]

theorem delivered_payload_was_emitted (corrupt : Option (Fin 3))
    (localMasks : Fin 3 → Nat → LocalMasks) (network : Network) (index : Nat)
    (message : Envelope) (h : network.emitted[index]? = some message) :
    (networkStep corrupt localMasks network (.deliver index)).nodes =
      network.nodes.set message.receiver (receive (network.nodes.get message.receiver) message) := by
  simp [networkStep, h]

theorem no_payload_visible_without_corruption (network : Network) :
    (observe none network).visiblePayloads = [] := by
  change network.emitted.filter (incident none) = []
  induction network.emitted with
  | nil => rfl
  | cons message rest ih => exact ih

theorem visible_payload_incident (network : Network) (party : Fin 3) (message : Envelope)
    (h : message ∈ (observe (some party) network).visiblePayloads) :
    message.sender = party ∨ message.receiver = party := by
  simpa [observe, incident] using (List.mem_filter.mp h).2

theorem abort_retains_emitted_history (corrupt : Option (Fin 3))
    (localMasks : Fin 3 → Nat → LocalMasks) (network : Network) (party : Fin 3) :
    (networkStep corrupt localMasks network (.abort party)).emitted = network.emitted := by
  simp [networkStep]

/-- Adversarial scheduling and local erasure never retroactively delete wire history. -/
theorem networkStep_emitted_prefix (corrupt : Option (Fin 3))
    (localMasks : Fin 3 → Nat → LocalMasks) (network : Network) (command : Command) :
    ∃ suffix, (networkStep corrupt localMasks network command).emitted = network.emitted ++ suffix := by
  cases command with
  | compute party => exact ⟨_, rfl⟩
  | deliver index =>
      simp only [networkStep]
      split <;> exact ⟨[], by simp⟩
  | corruptSend message =>
      simp only [networkStep]
      split
      · exact ⟨[message], rfl⟩
      · exact ⟨[], by simp⟩
  | abort party => exact ⟨[], by simp [networkStep]⟩

theorem runCommands_emitted_prefix (corrupt : Option (Fin 3))
    (localMasks : Fin 3 → Nat → LocalMasks) (network : Network) (commands : List Command) :
    ∃ suffix, (runCommands corrupt localMasks network commands).emitted = network.emitted ++ suffix := by
  induction commands generalizing network with
  | nil => exact ⟨[], by simp [runCommands]⟩
  | cons command commands ih =>
      obtain ⟨first, hf⟩ := networkStep_emitted_prefix corrupt localMasks network command
      obtain ⟨rest, hr⟩ := ih (networkStep corrupt localMasks network command)
      exact ⟨first ++ rest, by simpa [runCommands, hf, List.append_assoc] using hr⟩

@[expose] def WellAddressed (nodes : Nodes) : Prop :=
  nodes.n0.party = 0 ∧ nodes.n1.party = 1 ∧ nodes.n2.party = 2

theorem wellAddressed_get (nodes : Nodes) (party : Fin 3) (h : WellAddressed nodes) :
    (nodes.get party).party = party := by
  have hp : party = 0 ∨ party = 1 ∨ party = 2 := by omega
  rcases hp with rfl | rfl | rfl <;> simp [Nodes.get, h.1, h.2.1, h.2.2]

theorem wellAddressed_set (nodes : Nodes) (party : Fin 3) (node : Node)
    (h : WellAddressed nodes) (hp : node.party = party) :
    WellAddressed (nodes.set party node) := by
  have hcases : party = 0 ∨ party = 1 ∨ party = 2 := by omega
  rcases hcases with rfl | rfl | rfl <;>
    simp [Nodes.set, WellAddressed, hp, h.1, h.2.1, h.2.2]

theorem prepare_preserves_party (node : Node) (m : LocalMasks) :
    (prepare node m).1.party = node.party := by
  cases h : node.phase <;> cases hr : node.remaining <;> simp [prepare, h, hr, abortNode]

theorem receive_preserves_party (node : Node) (message : Envelope) :
    (receive node message).party = node.party := by
  cases h : node.phase <;> simp only [receive, h]
  all_goals first | rfl | (split <;> rfl)

theorem networkStep_preserves_addresses (corrupt : Option (Fin 3))
    (localMasks : Fin 3 → Nat → LocalMasks) (network : Network) (command : Command)
    (h : WellAddressed network.nodes) :
    WellAddressed (networkStep corrupt localMasks network command).nodes := by
  cases command with
  | compute party =>
      exact wellAddressed_set _ _ _ h
        ((prepare_preserves_party _ _).trans (wellAddressed_get _ _ h))
  | deliver index =>
      simp only [networkStep]
      split
      · exact h
      · exact wellAddressed_set _ _ _ h
          ((receive_preserves_party _ _).trans (wellAddressed_get _ _ h))
  | corruptSend message =>
      simp only [networkStep]
      split <;> exact h
  | abort party =>
      exact wellAddressed_set _ _ _ h (wellAddressed_get _ _ h)

#verify_constructive corruptMaskQuery_exact only_corrupt_sender_can_inject delivered_payload_was_emitted
  no_payload_visible_without_corruption visible_payload_incident abort_retains_emitted_history
  networkStep_emitted_prefix runCommands_emitted_prefix wellAddressed_get wellAddressed_set
  prepare_preserves_party receive_preserves_party networkStep_preserves_addresses


/-! ## Anti-Replay Authenticated Scheduler Wrapper (`AuthNetwork`) -/

/-- Replay-protected participant network state pairing `Network` with a persistent table
    `deliveredIndices` of already-delivered wire slots so re-delivery of any wire index is
    dropped at the transport boundary before reaching `receive`. -/
structure AuthNetwork where
  base : Network
  deliveredIndices : List Nat
  deriving DecidableEq, Repr

/-- Replay-protected step over `AuthNetwork`: `.deliver index` executes iff `index` has not
    previously been delivered and points to a valid emitted envelope. -/
@[expose] def authNetworkStep (corrupt : Option (Fin 3))
    (localMasks : Fin 3 → Nat → LocalMasks) (anet : AuthNetwork) (command : Command) : AuthNetwork :=
  match command with
  | .deliver index =>
      if decide (index ∈ anet.deliveredIndices) then
        anet
      else
        match anet.base.emitted[index]? with
        | none => anet
        | some message =>
            { base := { anet.base with
                          nodes := anet.base.nodes.set message.receiver
                            (receive (anet.base.nodes.get message.receiver) message) }
              deliveredIndices := index :: anet.deliveredIndices }
  | other =>
      { base := networkStep corrupt localMasks anet.base other
        deliveredIndices := anet.deliveredIndices }

@[expose] def runAuthCommands (corrupt : Option (Fin 3)) (localMasks : Fin 3 → Nat → LocalMasks) :
    AuthNetwork → List Command → AuthNetwork
  | anet, [] => anet
  | anet, cmd :: cmds =>
      runAuthCommands corrupt localMasks (authNetworkStep corrupt localMasks anet cmd) cmds

/-- **Anti-Replay Tooth (`tooth_authNetworkStep_redelivery_blocked`)**:
    Re-delivering an already-delivered wire index `index ∈ anet.deliveredIndices` is a strict no-op. -/
theorem authNetworkStep_redelivery_noop (corrupt : Option (Fin 3))
    (localMasks : Fin 3 → Nat → LocalMasks) (anet : AuthNetwork) (index : Nat)
    (hReplay : index ∈ anet.deliveredIndices) :
    authNetworkStep corrupt localMasks anet (.deliver index) = anet := by
  simp [authNetworkStep, hReplay]

theorem tooth_authNetworkStep_redelivery_blocked (corrupt : Option (Fin 3))
    (localMasks : Fin 3 → Nat → LocalMasks) (anet : AuthNetwork) (index : Nat)
    (hReplay : index ∈ anet.deliveredIndices) :
    (authNetworkStep corrupt localMasks anet (.deliver index)).deliveredIndices ≠
      index :: anet.deliveredIndices := by
  rw [authNetworkStep_redelivery_noop corrupt localMasks anet index hReplay]
  intro hEq
  have hLen := congrArg List.length hEq
  rw [List.length_cons] at hLen
  omega

/-- Every delivered index recorded in `deliveredIndices` stays bounded by `emitted.length` and `Nodup`. -/
theorem authNetworkStep_preserves_nodup (corrupt : Option (Fin 3))
    (localMasks : Fin 3 → Nat → LocalMasks) (anet : AuthNetwork) (cmd : Command)
    (hNd : anet.deliveredIndices.Nodup) :
    (authNetworkStep corrupt localMasks anet cmd).deliveredIndices.Nodup := by
  cases cmd with
  | compute _ => exact hNd
  | corruptSend _ => exact hNd
  | abort _ => exact hNd
  | deliver idx =>
    dsimp only [authNetworkStep]
    by_cases hMem : idx ∈ anet.deliveredIndices
    · simp only [decide_eq_true hMem, ↓reduceIte]
      exact hNd
    · simp only [decide_eq_false hMem, Bool.false_eq_true, ↓reduceIte]
      cases anet.base.emitted[idx]? with
      | none => exact hNd
      | some _ => exact List.nodup_cons.mpr ⟨hMem, hNd⟩

theorem runAuthCommands_preserves_nodup (corrupt : Option (Fin 3))
    (localMasks : Fin 3 → Nat → LocalMasks) (anet : AuthNetwork) (cmds : List Command)
    (hNd : anet.deliveredIndices.Nodup) :
    (runAuthCommands corrupt localMasks anet cmds).deliveredIndices.Nodup := by
  induction cmds generalizing anet with
  | nil => exact hNd
  | cons cmd rest ih =>
    exact ih (authNetworkStep corrupt localMasks anet cmd)
      (authNetworkStep_preserves_nodup corrupt localMasks anet cmd hNd)

theorem authNetworkStep_preserves_addresses (corrupt : Option (Fin 3))
    (localMasks : Fin 3 → Nat → LocalMasks) (anet : AuthNetwork) (cmd : Command)
    (h : WellAddressed anet.base.nodes) :
    WellAddressed (authNetworkStep corrupt localMasks anet cmd).base.nodes := by
  cases cmd with
  | compute p => exact networkStep_preserves_addresses corrupt localMasks anet.base (.compute p) h
  | corruptSend m => exact networkStep_preserves_addresses corrupt localMasks anet.base (.corruptSend m) h
  | abort p => exact networkStep_preserves_addresses corrupt localMasks anet.base (.abort p) h
  | deliver idx =>
    dsimp only [authNetworkStep]
    split
    · exact h
    · cases hEm : anet.base.emitted[idx]? with
      | none => exact h
      | some msg =>
        exact wellAddressed_set _ _ _ h
          ((receive_preserves_party _ _).trans (wellAddressed_get _ _ h))

#verify_constructive tooth_authNetworkStep_redelivery_blocked authNetworkStep_preserves_nodup
  runAuthCommands_preserves_nodup authNetworkStep_preserves_addresses
#tooth_pair runAuthCommands_preserves_nodup vs tooth_authNetworkStep_redelivery_blocked

end Qsag.RssParticipant
