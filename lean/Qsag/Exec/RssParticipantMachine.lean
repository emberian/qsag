module
public import Qsag.Exec.RssParticipantKeccak
public import Qsag.Protocol.Threshold.ThresholdMpc
import Qsag.Tactic.AssuranceKit

/-!
Addressed, resumable RSS round exchange. A node sees only its two-share view,
its local masks, and one authenticated received message. The authentication
resource is external: this transition checks labels, not a MAC or signature.
`runHonestRounds` is a product-network driver of those local transitions.
Gate witnesses remain unverified; reaching `finished` does not authorize a cut.
-/

public section
namespace Qsag.RssParticipant
set_option autoImplicit false

@[expose] def nextParty (p : Fin 3) : Fin 3 := ⟨(p.val + 1) % 3, Nat.mod_lt _ (by decide)⟩
@[expose] def previousParty (p : Fin 3) : Fin 3 := ⟨(p.val + 2) % 3, Nat.mod_lt _ (by decide)⟩

structure Envelope where
  sender : Fin 3
  receiver : Fin 3
  binding : List UInt8
  round : Nat
  share : KState
  deriving DecidableEq, Repr

structure PendingRound where
  ownOutput : KState
  gates : List GateRecord
  deriving DecidableEq, Repr

/-- The received output is retained alongside actual local multiplication inputs.
A gate checker must consume these records before any cut can be disclosed. -/
structure RoundEvidence where
  round : Nat
  rc : UInt64
  gates : List GateRecord
  ownOutput : KState
  receivedOutput : KState
  deriving DecidableEq, Repr

inductive Phase where
  | ready (view : LocalView)
  | awaiting (rc : UInt64) (pending : PendingRound)
  | finished (view : LocalView)
  | aborted
  deriving DecidableEq, Repr

structure Node where
  party : Fin 3
  binding : List UInt8
  cursor : Nat
  remaining : List UInt64
  phase : Phase
  evidence : List RoundEvidence
  deriving DecidableEq, Repr

@[expose] def initialNode (party : Fin 3) (binding : List UInt8) (view : LocalView)
    (rcs : List UInt64 := keccakRoundConstants) (cursor : Nat := 0) : Node :=
  ⟨party, binding, cursor, rcs, .ready view, []⟩

/-- Abort erases live shares and private gate witnesses. Already emitted network
messages are external history and cannot be erased by this local transition. -/
@[expose] def abortNode (s : Node) : Node := { s with phase := .aborted, evidence := [] }

/-- One local computation and one outgoing message. No other party's state is an input. -/
@[expose] def prepare (s : Node) (masks : LocalMasks) : Node × Option Envelope :=
  match s.phase, s.remaining with
  | .ready v, rc :: rcs =>
      let own := roundLocal s.party v rc masks
      let pending := PendingRound.mk own (gateRecords (linearLocal v) masks)
      ({ s with remaining := rcs, phase := .awaiting rc pending },
       some ⟨s.party, previousParty s.party, s.binding, s.cursor, own⟩)
  | .ready v, [] => ({ s with phase := .finished v }, none)
  | _, _ => (abortNode s, none)

/-- This is an authenticated-channel receive port: the resource must ensure that
`sender` identifies the party that emitted the payload. Tag checks alone do not. -/
@[expose] def receive (s : Node) (message : Envelope) : Node :=
  match s.phase with
  | .awaiting rc pending =>
      if message.sender = nextParty s.party ∧ message.receiver = s.party ∧
          message.binding = s.binding ∧ message.round = s.cursor then
        { s with
          cursor := s.cursor + 1
          phase := .ready ⟨pending.ownOutput, message.share⟩
          evidence := s.evidence ++
            [⟨s.cursor, rc, pending.gates, pending.ownOutput, message.share⟩] }
      else abortNode s
  | _ => abortNode s

@[expose] def receiveOptional (s : Node) (message : Option Envelope) : Node :=
  match message with
  | none => abortNode s
  | some message => receive s message

/-- Product state belongs to the network semantics, never to the node transition. -/
structure Nodes where
  n0 : Node
  n1 : Node
  n2 : Node
  deriving DecidableEq, Repr

@[expose] def initialNodes (binding : List UInt8) (s : RssKState) (rcs : List UInt64)
    (cursor : Nat) : Nodes :=
  ⟨initialNode 0 binding ⟨s.s0, s.s1⟩ rcs cursor,
   initialNode 1 binding ⟨s.s1, s.s2⟩ rcs cursor,
   initialNode 2 binding ⟨s.s2, s.s0⟩ rcs cursor⟩

/-- An honest routed round; adversarial schedules use `prepare`/`receive` separately. -/
@[expose] def honestRound (nodes : Nodes) (r : Nat → RssPrfZeroSeeds) : Nodes :=
  let a := prepare nodes.n0 (mask0 r)
  let b := prepare nodes.n1 (mask1 r)
  let c := prepare nodes.n2 (mask2 r)
  ⟨receiveOptional a.1 b.2, receiveOptional b.1 c.2, receiveOptional c.1 a.2⟩

/-- Histories may be arbitrarily long: the local state invariant concerns live
views and cursors, and does not erase accumulated gate evidence between rounds. -/
@[expose] def Represents (nodes : Nodes) (binding : List UInt8) (s : RssKState)
    (rcs : List UInt64) (cursor : Nat) : Prop :=
  nodes.n0.party = 0 ∧ nodes.n1.party = 1 ∧ nodes.n2.party = 2 ∧
  nodes.n0.binding = binding ∧ nodes.n1.binding = binding ∧ nodes.n2.binding = binding ∧
  nodes.n0.cursor = cursor ∧ nodes.n1.cursor = cursor ∧ nodes.n2.cursor = cursor ∧
  nodes.n0.remaining = rcs ∧ nodes.n1.remaining = rcs ∧ nodes.n2.remaining = rcs ∧
  nodes.n0.phase = .ready ⟨s.s0, s.s1⟩ ∧
  nodes.n1.phase = .ready ⟨s.s1, s.s2⟩ ∧
  nodes.n2.phase = .ready ⟨s.s2, s.s0⟩

theorem initialNodes_represents (binding : List UInt8) (s : RssKState)
    (rcs : List UInt64) (cursor : Nat) :
    Represents (initialNodes binding s rcs cursor) binding s rcs cursor := by
  simp [Represents, initialNodes, initialNode]

theorem honestRound_represents (nodes : Nodes) (binding : List UInt8)
    (s : RssKState) (rc : UInt64) (rcs : List UInt64) (cursor : Nat)
    (r : Nat → RssPrfZeroSeeds)
    (h : Represents nodes binding s (rc :: rcs) cursor) :
    Represents (honestRound nodes r) binding (roundNetwork s rc r) rcs (cursor + 1) := by
  rcases h with ⟨h0, h1, h2, hb0, hb1, hb2, hc0, hc1, hc2,
    hr0, hr1, hr2, hp0, hp1, hp2⟩
  simp [honestRound, prepare, receiveOptional, receive, h0, h1, h2,
    hb0, hb1, hb2, hc0, hc1, hc2, hr0, hr1, hr2, hp0, hp1, hp2,
    nextParty, previousParty, Represents, roundNetwork]

def runHonestRounds : Nat → Nodes → (Nat → Nat → RssPrfZeroSeeds) → Nodes
  | 0, nodes, _ => nodes
  | n + 1, nodes, tape =>
      runHonestRounds n (honestRound nodes (tape nodes.n0.cursor)) tape

theorem runHonestRounds_represents (rcs : List UInt64) (nodes : Nodes)
    (binding : List UInt8) (s : RssKState) (cursor : Nat)
    (tape : Nat → Nat → RssPrfZeroSeeds)
    (h : Represents nodes binding s rcs cursor) :
    Represents (runHonestRounds rcs.length nodes tape) binding
      (roundsNetwork rcs cursor s tape) [] (cursor + rcs.length) := by
  induction rcs generalizing nodes s cursor with
  | nil => simpa [runHonestRounds, roundsNetwork] using h
  | cons rc rcs ih =>
    have hc : nodes.n0.cursor = cursor := h.2.2.2.2.2.2.1
    have hr := honestRound_represents nodes binding s rc rcs cursor (tape cursor) h
    have hi := ih (honestRound nodes (tape cursor)) (roundNetwork s rc (tape cursor))
      (cursor + 1) hr
    simpa [runHonestRounds, roundsNetwork, hc, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hi

def primaryOutput (node : Node) : Option KState :=
  match node.phase with
  | .ready v => some v.own
  | .finished v => some v.own
  | _ => none

/-- External correctness observer only; there is no cut/open instruction on nodes. -/
def reconstructedOutput (nodes : Nodes) : Option KState := do
  let a ← primaryOutput nodes.n0
  let b ← primaryOutput nodes.n1
  let c ← primaryOutput nodes.n2
  pure (xorKState a (xorKState b c))

theorem represents_output (nodes : Nodes) (binding : List UInt8) (s : RssKState)
    (rcs : List UInt64) (cursor : Nat) (h : Represents nodes binding s rcs cursor) :
    reconstructedOutput nodes = some (reconstructRssKState s) := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hp0, hp1, hp2⟩
  simp [reconstructedOutput, primaryOutput, hp0, hp1, hp2, reconstructRssKState.public_eq_1]

/-- Complete24-round participant execution refines the existing shared evaluator.
This correctness observer is not an authorized public opening operation. -/
theorem participant_keccak_refines_existing (binding : List UInt8) (s : RssKState)
    (tape : Nat → Nat → RssPrfZeroSeeds) :
    reconstructedOutput
      (runHonestRounds keccakRoundConstants.length
        (initialNodes binding s keccakRoundConstants 0) tape) =
      some (reconstructRssKState (mpcKeccakF1600Rss s tape)) := by
  have h := runHonestRounds_represents keccakRoundConstants
    (initialNodes binding s keccakRoundConstants 0) binding s 0 tape
    (initialNodes_represents binding s keccakRoundConstants 0)
  rw [represents_output _ _ _ _ _ h, keccak_refines_existing]

theorem wrong_binding_aborts (s : Node) (message : Envelope)
    (h : message.binding ≠ s.binding) : (receive s message).phase = .aborted := by
  cases hp : s.phase <;> simp [receive, hp, h, abortNode]

theorem wrong_round_aborts (s : Node) (message : Envelope)
    (h : message.round ≠ s.cursor) : (receive s message).phase = .aborted := by
  cases hp : s.phase <;> simp [receive, hp, h, abortNode]

theorem wrong_sender_aborts (s : Node) (message : Envelope)
    (h : message.sender ≠ nextParty s.party) : (receive s message).phase = .aborted := by
  cases hp : s.phase <;> simp [receive, hp, h, abortNode]

theorem receive_before_prepare_aborts (s : Node) (v : LocalView) (message : Envelope)
    (h : s.phase = .ready v) : (receive s message).phase = .aborted := by
  simp [receive, h, abortNode]

/-- Authentication does not validate a value: any payload with valid labels enters
pending evidence. The active gate-check proof is a separate required obligation. -/
theorem authenticated_payload_is_not_product_validation (s : Node) (rc : UInt64)
    (pending : PendingRound) (share : KState) (h : s.phase = .awaiting rc pending) :
    (receive s ⟨nextParty s.party, s.party, s.binding, s.cursor, share⟩).phase =
      .ready ⟨pending.ownOutput, share⟩ := by
  simp [receive, h]

#verify_constructive initialNodes_represents honestRound_represents runHonestRounds_represents represents_output participant_keccak_refines_existing wrong_binding_aborts wrong_round_aborts wrong_sender_aborts receive_before_prepare_aborts authenticated_payload_is_not_product_validation

end Qsag.RssParticipant
