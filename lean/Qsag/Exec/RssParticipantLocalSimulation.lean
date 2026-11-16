module
public import Qsag.Exec.RssParticipantMachine
public import Qsag.Exec.RssParticipantKeccak
public import Qsag.Protocol.Threshold.ThresholdMpc
public import Qsag.Protocol.Aggregation.UcGames
import Qsag.Tactic.AssuranceKit

/-!
Secret-free simulator for one passive-corrupt party's local round under an ideal
fresh pairwise-mask resource. A constructive1600-bit mask translation matches its
entire local node state/evidence. This does not simulate active gate checks,
commitments, public cut disclosures, or production PRG correlations. The
translation may depend on hidden real state; the simulator itself does not.
-/
public section
namespace Qsag.RssParticipant
set_option autoImplicit false

@[expose] def laneWord (s : KState) : Nat → UInt64
  | 0 => s.a0
  | 1 => s.a1
  | 2 => s.a2
  | 3 => s.a3
  | 4 => s.a4
  | 5 => s.a5
  | 6 => s.a6
  | 7 => s.a7
  | 8 => s.a8
  | 9 => s.a9
  | 10 => s.a10
  | 11 => s.a11
  | 12 => s.a12
  | 13 => s.a13
  | 14 => s.a14
  | 15 => s.a15
  | 16 => s.a16
  | 17 => s.a17
  | 18 => s.a18
  | 19 => s.a19
  | 20 => s.a20
  | 21 => s.a21
  | 22 => s.a22
  | 23 => s.a23
  | 24 => s.a24
  | _ => 0

@[expose] def roundMasks (known0 known1 hidden : KState) : Nat → RssPrfZeroSeeds :=
  fun lane => ⟨laneWord known0 lane, laneWord known1 lane, laneWord hidden lane⟩

theorem chiLane_hidden_xor (a b bn c cn known hidden : UInt64) :
    chiLane a b bn c cn (known, hidden) = chiLane a b bn c cn (known, 0) ^^^ hidden := by
  simp only [chiLane, productGate, UInt64.xor_zero]
  ac_rfl

@[expose] def chiOffset (view : LocalView) (known : KState) : KState :=
  chiLocal view (fun lane => (laneWord known lane, 0))

theorem chiLocal_hidden_xor (view : LocalView) (known hidden : KState) :
    chiLocal view (fun lane => (laneWord known lane, laneWord hidden lane)) =
      xorKState (chiOffset view known) hidden := by
  simp only [chiOffset, chiLocal, laneWord, xorKState_eq]
  congr 1 <;> exact chiLane_hidden_xor _ _ _ _ _ _ _

theorem xorKState_involution (offset state : KState) :
    xorKState offset (xorKState offset state) = state := by
  rw [xorKState_eq, xorKState_eq]
  simp only [← UInt64.xor_assoc, UInt64.xor_self, UInt64.zero_xor]

@[expose] def maskTranslation (offset : KState) : SimpleEquiv KState KState where
  toFun := xorKState offset
  invFun := xorKState offset
  left_inv := xorKState_involution offset
  right_inv := xorKState_involution offset

/-- Party0 receives party1's own output. The latter's unknown mask is r2. -/
@[expose] def receiveOffset (state : RssKState) (known1 : KState) : KState :=
  chiOffset (linearLocal ⟨state.s1, state.s2⟩) known1

theorem received_share_translation (state : RssKState) (rc : UInt64)
    (known0 known1 hidden : KState) :
    (roundNetwork state rc (roundMasks known0 known1 hidden)).s1 =
      (maskTranslation (receiveOffset state known1)).toFun hidden := by
  change chiLocal (linearLocal ⟨state.s1, state.s2⟩)
      (fun lane => (laneWord known1 lane, laneWord hidden lane)) =
    xorKState (receiveOffset state known1) hidden
  exact chiLocal_hidden_xor _ _ _

/-- This simulator consumes only party0's local state, its own two mask words,
and a fresh sampled incoming share. It has no key, third share, or ideal signature. -/
@[expose] def simulateLocalRound (node : Node) (masks : LocalMasks) (sample : KState) : Node :=
  let prepared := prepare node masks
  receive prepared.1 ⟨nextParty node.party, node.party, node.binding, node.cursor, sample⟩

theorem routed_corrupt_round (binding : List UInt8) (state : RssKState) (rc : UInt64)
    (remaining : List UInt64) (cursor : Nat) (r : Nat → RssPrfZeroSeeds) :
    (honestRound (initialNodes binding state (rc :: remaining) cursor) r).n0 =
      simulateLocalRound (initialNode 0 binding ⟨state.s0, state.s1⟩ (rc :: remaining) cursor)
        (mask0 r) (roundNetwork state rc r).s1 := by
  simp [honestRound, initialNodes, initialNode, prepare, receiveOptional,
    simulateLocalRound, receive, nextParty, previousParty, roundNetwork]

/-- Exact local-round simulation under a bijective change of the hidden fresh
mask. Includes actual local operands/products and received output in node evidence. -/
theorem passive_corrupt_round_simulation (binding : List UInt8) (state : RssKState)
    (rc : UInt64) (remaining : List UInt64) (cursor : Nat) (known0 known1 sample : KState) :
    let hidden := (maskTranslation (receiveOffset state known1)).invFun sample
    (honestRound (initialNodes binding state (rc :: remaining) cursor)
      (roundMasks known0 known1 hidden)).n0 =
      simulateLocalRound (initialNode 0 binding ⟨state.s0, state.s1⟩ (rc :: remaining) cursor)
        (fun lane => (laneWord known0 lane, laneWord known1 lane)) sample := by
  intro hidden
  rw [routed_corrupt_round, received_share_translation]
  rw [(maskTranslation (receiveOffset state known1)).right_inv sample]
  rfl

#verify_constructive chiLane_hidden_xor chiLocal_hidden_xor xorKState_involution
  received_share_translation routed_corrupt_round passive_corrupt_round_simulation
end Qsag.RssParticipant
