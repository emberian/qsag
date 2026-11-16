module
public import Qsag.Protocol.Threshold.ThresholdMpc
import Qsag.Tactic.AssuranceKit

/-!
Party-local RSS Keccak arithmetic and addressed round exchange. This is the
unpacked single-sponge representation of the uncomplemented product formula in
`keccak_mpc.rs`, not an assertion that its words equal Rust's packed-64 layout.
Each transition consumes two adjacent shares and two local mask words only.
The external network may contain all nodes; no node transition receives that map.
Authentication of an envelope is an explicit transport resource. Authentication
alone does not prove a product relation; pending gate records are retained and
there is deliberately no output-opening operation in this arithmetic machine.
-/

public section
namespace Qsag.RssParticipant
set_option autoImplicit false

structure LocalView where
  own : KState
  next : KState
  deriving DecidableEq, Repr

/-- Exactly the two mask words held by this participant. -/
abbrev LocalMasks := Nat → UInt64 × UInt64

/-- Actual uncomplemented AND operands and produced share, before χ's linear terms. -/
structure GateRecord where
  lhsOwn : UInt64
  lhsNext : UInt64
  rhsOwn : UInt64
  rhsNext : UInt64
  product : UInt64
  deriving DecidableEq, Repr

@[expose] def productGate (b bn c cn : UInt64) (m : UInt64 × UInt64) : GateRecord :=
  ⟨b, bn, c, cn, (b &&& c) ^^^ (b &&& cn) ^^^ (bn &&& c) ^^^ (m.1 ^^^ m.2)⟩

/-- Algebraic normalization of the unmasked multiplication expression appearing
in `eval_rss_keccak_f1600_batch64_record`. Packing and `activeMask` are separate
representation obligations, not silently discharged by this word identity. -/
theorem productGate_matches_unmasked_rust_formula (b bn c cn r rn : UInt64) :
    (productGate b bn c cn (r, rn)).product =
      (b &&& (c ^^^ cn)) ^^^ (bn &&& c) ^^^ r ^^^ rn := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [productGate, UInt64.toBitVec_xor, UInt64.toBitVec_and,
    BitVec.getLsbD_xor, BitVec.getLsbD_and]
  cases b.toBitVec.getLsbD i <;> cases bn.toBitVec.getLsbD i <;>
    cases c.toBitVec.getLsbD i <;> cases cn.toBitVec.getLsbD i <;>
    cases r.toBitVec.getLsbD i <;> cases rn.toBitVec.getLsbD i <;> rfl

@[expose] def chiLane (a b bn c cn : UInt64) (m : UInt64 × UInt64) : UInt64 :=
  a ^^^ c ^^^ (productGate b bn c cn m).product

/-- This follows Rust's `a_i XOR c_i XOR product(b,c)` convention. -/
@[expose] def chiLocal (v : LocalView) (m : LocalMasks) : KState :=
  ⟨chiLane v.own.a0 v.own.a1 v.next.a1 v.own.a2 v.next.a2 (m 0),
   chiLane v.own.a1 v.own.a2 v.next.a2 v.own.a3 v.next.a3 (m 1),
   chiLane v.own.a2 v.own.a3 v.next.a3 v.own.a4 v.next.a4 (m 2),
   chiLane v.own.a3 v.own.a4 v.next.a4 v.own.a0 v.next.a0 (m 3),
   chiLane v.own.a4 v.own.a0 v.next.a0 v.own.a1 v.next.a1 (m 4),
   chiLane v.own.a5 v.own.a6 v.next.a6 v.own.a7 v.next.a7 (m 5),
   chiLane v.own.a6 v.own.a7 v.next.a7 v.own.a8 v.next.a8 (m 6),
   chiLane v.own.a7 v.own.a8 v.next.a8 v.own.a9 v.next.a9 (m 7),
   chiLane v.own.a8 v.own.a9 v.next.a9 v.own.a5 v.next.a5 (m 8),
   chiLane v.own.a9 v.own.a5 v.next.a5 v.own.a6 v.next.a6 (m 9),
   chiLane v.own.a10 v.own.a11 v.next.a11 v.own.a12 v.next.a12 (m 10),
   chiLane v.own.a11 v.own.a12 v.next.a12 v.own.a13 v.next.a13 (m 11),
   chiLane v.own.a12 v.own.a13 v.next.a13 v.own.a14 v.next.a14 (m 12),
   chiLane v.own.a13 v.own.a14 v.next.a14 v.own.a10 v.next.a10 (m 13),
   chiLane v.own.a14 v.own.a10 v.next.a10 v.own.a11 v.next.a11 (m 14),
   chiLane v.own.a15 v.own.a16 v.next.a16 v.own.a17 v.next.a17 (m 15),
   chiLane v.own.a16 v.own.a17 v.next.a17 v.own.a18 v.next.a18 (m 16),
   chiLane v.own.a17 v.own.a18 v.next.a18 v.own.a19 v.next.a19 (m 17),
   chiLane v.own.a18 v.own.a19 v.next.a19 v.own.a15 v.next.a15 (m 18),
   chiLane v.own.a19 v.own.a15 v.next.a15 v.own.a16 v.next.a16 (m 19),
   chiLane v.own.a20 v.own.a21 v.next.a21 v.own.a22 v.next.a22 (m 20),
   chiLane v.own.a21 v.own.a22 v.next.a22 v.own.a23 v.next.a23 (m 21),
   chiLane v.own.a22 v.own.a23 v.next.a23 v.own.a24 v.next.a24 (m 22),
   chiLane v.own.a23 v.own.a24 v.next.a24 v.own.a20 v.next.a20 (m 23),
   chiLane v.own.a24 v.own.a20 v.next.a20 v.own.a21 v.next.a21 (m 24)⟩

def gateRecords (v : LocalView) (m : LocalMasks) : List GateRecord :=
  [productGate v.own.a1 v.next.a1 v.own.a2 v.next.a2 (m 0),
   productGate v.own.a2 v.next.a2 v.own.a3 v.next.a3 (m 1),
   productGate v.own.a3 v.next.a3 v.own.a4 v.next.a4 (m 2),
   productGate v.own.a4 v.next.a4 v.own.a0 v.next.a0 (m 3),
   productGate v.own.a0 v.next.a0 v.own.a1 v.next.a1 (m 4),
   productGate v.own.a6 v.next.a6 v.own.a7 v.next.a7 (m 5),
   productGate v.own.a7 v.next.a7 v.own.a8 v.next.a8 (m 6),
   productGate v.own.a8 v.next.a8 v.own.a9 v.next.a9 (m 7),
   productGate v.own.a9 v.next.a9 v.own.a5 v.next.a5 (m 8),
   productGate v.own.a5 v.next.a5 v.own.a6 v.next.a6 (m 9),
   productGate v.own.a11 v.next.a11 v.own.a12 v.next.a12 (m 10),
   productGate v.own.a12 v.next.a12 v.own.a13 v.next.a13 (m 11),
   productGate v.own.a13 v.next.a13 v.own.a14 v.next.a14 (m 12),
   productGate v.own.a14 v.next.a14 v.own.a10 v.next.a10 (m 13),
   productGate v.own.a10 v.next.a10 v.own.a11 v.next.a11 (m 14),
   productGate v.own.a16 v.next.a16 v.own.a17 v.next.a17 (m 15),
   productGate v.own.a17 v.next.a17 v.own.a18 v.next.a18 (m 16),
   productGate v.own.a18 v.next.a18 v.own.a19 v.next.a19 (m 17),
   productGate v.own.a19 v.next.a19 v.own.a15 v.next.a15 (m 18),
   productGate v.own.a15 v.next.a15 v.own.a16 v.next.a16 (m 19),
   productGate v.own.a21 v.next.a21 v.own.a22 v.next.a22 (m 20),
   productGate v.own.a22 v.next.a22 v.own.a23 v.next.a23 (m 21),
   productGate v.own.a23 v.next.a23 v.own.a24 v.next.a24 (m 22),
   productGate v.own.a24 v.next.a24 v.own.a20 v.next.a20 (m 23),
   productGate v.own.a20 v.next.a20 v.own.a21 v.next.a21 (m 24)]

@[expose] def mask0 (r : Nat → RssPrfZeroSeeds) : LocalMasks := fun i => ((r i).r0, (r i).r1)
@[expose] def mask1 (r : Nat → RssPrfZeroSeeds) : LocalMasks := fun i => ((r i).r1, (r i).r2)
@[expose] def mask2 (r : Nat → RssPrfZeroSeeds) : LocalMasks := fun i => ((r i).r2, (r i).r0)

/-- Central mathematical assembly, used only to specify the product network. -/
def chiNetwork (s : RssKState) (r : Nat → RssPrfZeroSeeds) : RssKState :=
  ⟨chiLocal ⟨s.s0, s.s1⟩ (mask0 r), chiLocal ⟨s.s1, s.s2⟩ (mask1 r),
   chiLocal ⟨s.s2, s.s0⟩ (mask2 r)⟩

theorem chiLane_reconstruct (a0 a1 a2 b0 b1 b2 c0 c1 c2 : UInt64)
    (s : RssPrfZeroSeeds) :
    chiLane a0 b0 b1 c0 c1 (s.r0, s.r1) ^^^
      (chiLane a1 b1 b2 c1 c2 (s.r1, s.r2) ^^^
       chiLane a2 b2 b0 c2 c0 (s.r2, s.r0)) =
      (a0 ^^^ (a1 ^^^ a2)) ^^^ ((~~~(b0 ^^^ (b1 ^^^ b2))) &&&
        (c0 ^^^ (c1 ^^^ c2))) := by
  unfold chiLane productGate
  dsimp only
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt64.toBitVec_xor, UInt64.toBitVec_and, UInt64.toBitVec_not,
    BitVec.getLsbD_xor, BitVec.getLsbD_and, Constructive.getLsbD_not, hi,
    decide_true, Bool.true_and]
  cases a0.toBitVec.getLsbD i <;> cases a1.toBitVec.getLsbD i <;>
    cases a2.toBitVec.getLsbD i <;> cases b0.toBitVec.getLsbD i <;>
    cases b1.toBitVec.getLsbD i <;> cases b2.toBitVec.getLsbD i <;>
    cases c0.toBitVec.getLsbD i <;> cases c1.toBitVec.getLsbD i <;>
    cases c2.toBitVec.getLsbD i <;> cases s.r0.toBitVec.getLsbD i <;>
    cases s.r1.toBitVec.getLsbD i <;> cases s.r2.toBitVec.getLsbD i <;> rfl

theorem reconstruct_chiNetwork (s : RssKState) (r : Nat → RssPrfZeroSeeds) :
    reconstructRssKState (chiNetwork s r) = chiS (reconstructRssKState s) := by
  rw [reconstructRssKState.public_eq_1, reconstructRssKState.public_eq_1]
  unfold chiNetwork chiLocal mask0 mask1 mask2
  rw [xorKState_eq, xorKState_eq, xorKState_eq, xorKState_eq, chiS_eq]
  dsimp only
  simp only [chiLane_reconstruct]

@[expose] def linearLocal (v : LocalView) : LocalView :=
  ⟨rhoPiS (thetaS v.own), rhoPiS (thetaS v.next)⟩

@[expose] def addIota (party : Fin 3) (rc : UInt64) (s : KState) : KState :=
  if party.val = 0 then { s with a0 := s.a0 ^^^ rc } else s

@[expose] def roundLocal (party : Fin 3) (v : LocalView) (rc : UInt64) (m : LocalMasks) : KState :=
  addIota party rc (chiLocal (linearLocal v) m)

@[expose] def roundNetwork (s : RssKState) (rc : UInt64) (r : Nat → RssPrfZeroSeeds) : RssKState :=
  ⟨roundLocal 0 ⟨s.s0, s.s1⟩ rc (mask0 r),
   roundLocal 1 ⟨s.s1, s.s2⟩ rc (mask1 r),
   roundLocal 2 ⟨s.s2, s.s0⟩ rc (mask2 r)⟩

theorem reconstruct_roundNetwork (s : RssKState) (rc : UInt64)
    (r : Nat → RssPrfZeroSeeds) :
    reconstructRssKState (roundNetwork s rc r) = roundS (reconstructRssKState s) rc := by
  have hTheta : reconstructRssKState (mpcThetaRss s) = thetaS (reconstructRssKState s) := by
    rw [reconstructRssKState.public_eq_1, reconstructRssKState.public_eq_1, mpcThetaRss.public_eq_1]
    rw [thetaS_xorKState, thetaS_xorKState]
  have hRho : ∀ u : RssKState, reconstructRssKState (mpcRhoPiRss u) = rhoPiS (reconstructRssKState u) := by
    intro u
    rw [reconstructRssKState.public_eq_1, reconstructRssKState.public_eq_1, mpcRhoPiRss.public_eq_1]
    rw [rhoPiS_xorKState, rhoPiS_xorKState]
  let m := chiNetwork (mpcRhoPiRss (mpcThetaRss s)) r
  have hMid : reconstructRssKState m = chiS (rhoPiS (thetaS (reconstructRssKState s))) :=
    (reconstruct_chiNetwork _ r).trans
      (congrArg chiS ((hRho _).trans (congrArg rhoPiS hTheta)))
  have hIota : (m.s0.a0 ^^^ rc) ^^^ (m.s1.a0 ^^^ m.s2.a0) =
      (m.s0.a0 ^^^ (m.s1.a0 ^^^ m.s2.a0)) ^^^ rc := by ac_rfl
  have hM : m = ⟨chiLocal (linearLocal ⟨s.s0, s.s1⟩) (mask0 r),
      chiLocal (linearLocal ⟨s.s1, s.s2⟩) (mask1 r),
      chiLocal (linearLocal ⟨s.s2, s.s0⟩) (mask2 r)⟩ := by
    dsimp only [m]
    rw [mpcThetaRss.public_eq_1, mpcRhoPiRss.public_eq_1]
    rfl
  have hRN : roundNetwork s rc r =
      ⟨{ m.s0 with a0 := m.s0.a0 ^^^ rc }, m.s1, m.s2⟩ := by
    rw [hM]
    rfl
  rw [hRN, roundS_eq, ← hMid, reconstructRssKState.public_eq_1, reconstructRssKState.public_eq_1]
  dsimp only
  rw [xorKState_eq]
  dsimp only
  rw [xorKState_eq, xorKState_eq]
  dsimp only
  rw [hIota]

/-- Reconstruction refinement, without claiming equality of shares under the two χ conventions. -/
theorem round_refines_existing (s : RssKState) (rc : UInt64)
    (r : Nat → RssPrfZeroSeeds) :
    reconstructRssKState (roundNetwork s rc r) =
      reconstructRssKState (mpcRoundSRss s rc r) := by
  rw [reconstruct_roundNetwork, reconstructRssKState_mpcRoundSRss]

@[expose] def roundsNetwork : List UInt64 → Nat → RssKState →
    (Nat → Nat → RssPrfZeroSeeds) → RssKState
  | [], _, s, _ => s
  | rc :: rcs, i, s, tape => roundsNetwork rcs (i + 1) (roundNetwork s rc (tape i)) tape

theorem reconstruct_roundsNetwork (rcs : List UInt64) (i : Nat) (s : RssKState)
    (tape : Nat → Nat → RssPrfZeroSeeds) :
    reconstructRssKState (roundsNetwork rcs i s tape) =
      rcs.foldl roundS (reconstructRssKState s) := by
  induction rcs generalizing i s with
  | nil => rfl
  | cons rc rcs ih =>
    simp only [roundsNetwork, ih, List.foldl_cons, reconstruct_roundNetwork]

theorem keccak_refines_existing (s : RssKState) (tape : Nat → Nat → RssPrfZeroSeeds) :
    reconstructRssKState (roundsNetwork keccakRoundConstants 0 s tape) =
      reconstructRssKState (mpcKeccakF1600Rss s tape) := by
  rw [reconstruct_roundsNetwork, reconstructRssKState_mpcKeccakF1600Rss, keccakF1600_eq]

#verify_constructive productGate_matches_unmasked_rust_formula chiLane_reconstruct reconstruct_chiNetwork reconstruct_roundNetwork round_refines_existing reconstruct_roundsNetwork keccak_refines_existing

end Qsag.RssParticipant

public section
namespace Qsag.RssParticipant
#export_eqns gateRecords
end Qsag.RssParticipant
