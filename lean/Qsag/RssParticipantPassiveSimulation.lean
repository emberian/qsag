module
public import Qsag.RssParticipantLocalSimulation
import all Qsag.RssParticipantLocalSimulation
import all Qsag.RssParticipantMachine
import all Qsag.RssParticipantKeccak
import all Qsag.UcGames
import Qsag.Tactic.AssuranceKit

/-!
Constructive mask-tape coupling for arbitrary finite passive-corrupt arithmetic
prefixes. The simulator consumes only party0's local node, its known masks, and
sampled received shares. Forward/inverse tape maps may use hidden real state;
they prove a bijection and are not simulator inputs. This is before active proof
messages and public cuts, and assumes independent fresh hidden mask coordinates
when interpreted as a uniform-distribution replacement.
-/
public section
namespace Qsag.RssParticipant
set_option autoImplicit false

structure PassiveRound where
  constant : UInt64
  known0 : KState
  known1 : KState

def nextShared (state : RssKState) (round : PassiveRound) (hidden : KState) : RssKState :=
  roundNetwork state round.constant (roundMasks round.known0 round.known1 hidden)

/-- Map real unknown mask coordinates to the observed incoming-share coordinates. -/
def forwardTape : RssKState → List PassiveRound → List KState → List KState
  | _, [], tape => tape
  | _, _ :: _, [] => []
  | state, round :: rounds, hidden :: tape =>
      let next := nextShared state round hidden
      next.s1 :: forwardTape next rounds tape

/-- Recover the unique hidden mask that produces each simulator sample. -/
def inverseTape : RssKState → List PassiveRound → List KState → List KState
  | _, [], samples => samples
  | _, _ :: _, [] => []
  | state, round :: rounds, sample :: samples =>
      let hidden := (maskTranslation (receiveOffset state round.known1)).invFun sample
      hidden :: inverseTape (nextShared state round hidden) rounds samples

theorem inverse_forwardTape (state : RssKState) (rounds : List PassiveRound) (tape : List KState) :
    inverseTape state rounds (forwardTape state rounds tape) = tape := by
  induction rounds generalizing state tape with
  | nil => rfl
  | cons round rounds ih =>
      cases tape with
      | nil => rfl
      | cons hidden tape =>
          have h : (maskTranslation (receiveOffset state round.known1)).invFun
              (nextShared state round hidden).s1 = hidden := by
            rw [nextShared, received_share_translation]
            exact (maskTranslation _).left_inv hidden
          simp only [forwardTape, inverseTape, h, ih]

theorem forward_inverseTape (state : RssKState) (rounds : List PassiveRound) (samples : List KState) :
    forwardTape state rounds (inverseTape state rounds samples) = samples := by
  induction rounds generalizing state samples with
  | nil => rfl
  | cons round rounds ih =>
      cases samples with
      | nil => rfl
      | cons sample samples =>
          have h : (nextShared state round
              ((maskTranslation (receiveOffset state round.known1)).invFun sample)).s1 = sample := by
            rw [nextShared, received_share_translation]
            exact (maskTranslation _).right_inv sample
          simp only [inverseTape, forwardTape, h, ih]

def passiveTapeEquiv (state : RssKState) (rounds : List PassiveRound) :
    SimpleEquiv (List KState) (List KState) where
  toFun := forwardTape state rounds
  invFun := inverseTape state rounds
  left_inv := inverse_forwardTape state rounds
  right_inv := forward_inverseTape state rounds

def runPassiveReal : Nodes → List PassiveRound → List KState → Nodes
  | nodes, [], _ => nodes
  | nodes, _ :: _, [] => nodes
  | nodes, round :: rounds, hidden :: tape =>
      runPassiveReal (honestRound nodes (roundMasks round.known0 round.known1 hidden)) rounds tape

/-- No global share state or secret key appears in this simulator. -/
def runPassiveSimulator : Node → List PassiveRound → List KState → Node
  | node, [], _ => node
  | node, _ :: _, [] => node
  | node, round :: rounds, sample :: samples =>
      runPassiveSimulator (simulateLocalRound node
        (fun lane => (laneWord round.known0 lane, laneWord round.known1 lane)) sample) rounds samples

theorem routed_corrupt_round_of_represents (nodes : Nodes) (binding : List UInt8)
    (state : RssKState) (rc : UInt64) (remaining : List UInt64) (cursor : Nat)
    (r : Nat → RssPrfZeroSeeds) (h : Represents nodes binding state (rc :: remaining) cursor) :
    (honestRound nodes r).n0 = simulateLocalRound nodes.n0 (mask0 r) (roundNetwork state rc r).s1 := by
  rcases h with ⟨h0, h1, h2, hb0, hb1, hb2, hc0, hc1, hc2,
    hr0, hr1, hr2, hp0, hp1, hp2⟩
  simp [honestRound, prepare, receiveOptional, simulateLocalRound, receive,
    h0, h1, h2, hb0, hb1, hb2, hc0, hc1, hc2, hr0, hr1, hr2, hp0, hp1, hp2,
    nextParty, previousParty, roundNetwork]

/-- Exact equality of the full corrupt node state, including accumulated local
gate evidence, for an arbitrary number of rounds and unfinished prefixes. -/
theorem passive_prefix_simulation (nodes : Nodes) (binding : List UInt8) (state : RssKState)
    (rounds : List PassiveRound) (cursor : Nat) (samples : List KState)
    (h : Represents nodes binding state (rounds.map PassiveRound.constant) cursor) :
    (runPassiveReal nodes rounds ((passiveTapeEquiv state rounds).invFun samples)).n0 =
      runPassiveSimulator nodes.n0 rounds samples := by
  change (runPassiveReal nodes rounds (inverseTape state rounds samples)).n0 = _
  induction rounds generalizing nodes state cursor samples with
  | nil => rfl
  | cons round rounds ih =>
      cases samples with
      | nil => rfl
      | cons sample samples =>
        let hidden := (maskTranslation (receiveOffset state round.known1)).invFun sample
        let r := roundMasks round.known0 round.known1 hidden
        have hs : (roundNetwork state round.constant r).s1 = sample := by
          rw [received_share_translation]
          exact (maskTranslation _).right_inv sample
        have hn := honestRound_represents nodes binding state round.constant
          (rounds.map PassiveRound.constant) cursor r h
        have hv := routed_corrupt_round_of_represents nodes binding state round.constant
          (rounds.map PassiveRound.constant) cursor r h
        rw [hs] at hv
        have hi := ih (honestRound nodes r) (nextShared state round hidden) (cursor + 1) samples hn
        change (runPassiveReal (honestRound nodes r) rounds
          (inverseTape (nextShared state round hidden) rounds samples)).n0 = _
        rw [hi, hv]
        rfl

#verify_constructive inverse_forwardTape forward_inverseTape
  routed_corrupt_round_of_represents passive_prefix_simulation
end Qsag.RssParticipant
