module
import all QsagVerified.Funs
public import QsagVerified.Proofs.BeltAckProvenance
public import Qsag.JortsBeltLatchAndQuorumSwitching
import all Qsag.JortsBeltLatchAndQuorumSwitching

/-!
This is the local authenticated guard's certificate-to-mask refinement. It includes
constructor-established invariants and histories containing rejected calls. Production
BeltLatch durable records, retry salts, recovery, and receiver-specific peer echoes are
not represented by this extracted guard; no whole-network transition refinement is claimed.
-/

public section
namespace qsag_verified.proofs
open Aeneas Aeneas.Std Result
open qsag_verified

/-- Embed the extracted bitmap in the canonical finite custodian-set type. -/
def beltMaskAbs (bm : Std.U64) : Qsag.CustodiansMask 64 := ⟨fun i => bm.bv.getLsbD i.val⟩

private theorem maskCard_nat (n : Nat) (f : Nat → Bool) :
    Qsag.maskCard (⟨fun i => f i.val⟩ : Qsag.CustodiansMask n) = (List.range n).countP f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [Qsag.maskCard_succ, List.range_succ_eq_map, List.countP_cons, List.countP_map]
    change (if f 0 then 1 else 0) +
      Qsag.maskCard (⟨fun i => f (i.val + 1)⟩ : Qsag.CustodiansMask n) = _
    rw [ih (fun j => f (j + 1))]
    split <;> simp_all [Function.comp_def, Nat.add_comm]

theorem beltMaskAbs_card (bm : Std.U64) : Qsag.maskCard (beltMaskAbs bm) = beltPopcount bm :=
  maskCard_nat 64 bm.bv.getLsbD

theorem beltMaskAbs_inter (a b : Std.U64) :
    beltMaskAbs (a &&& b) = Qsag.maskInter (beltMaskAbs a) (beltMaskAbs b) := by
  apply congrArg Qsag.CustodiansMask.mk
  funext i
  exact BitVec.getLsbD_and

/-- Direct refinement of an extracted grant to the canonical custodian mask algebra.
This is a certificate/set weld, not a claim that the distinct BeltLatch network machine
and the local authenticated quorum guard have identical transitions. -/
theorem belt_grant_refines_qsag_mask
    {initial st st' : authenticated_belt.VerifiedBeltQuorumGuard} {calls : List BeltCall}
    {a : BeltAction} {g : pants_and_quorum_guards.BeltAuthorizationGrant} {n q : Std.U32}
    (hr : BeltRun initial calls st) (hz : initial.ack_bitmap = 0#u64)
    (hinv : BeltGuardInv n q initial)
    (hg : authenticated_belt.VerifiedBeltQuorumGuard.step st a = .ok (st', .Ok (.SharesAuthorized g))) :
    q.val ≤ Qsag.maskCard (beltMaskAbs st.ack_bitmap) ∧
    g.certified_acks.val = Qsag.maskCard (beltMaskAbs st.ack_bitmap) ∧
    ∀ i : Fin 64, (beltMaskAbs st.ack_bitmap).mem i = true →
      i.val < n.val ∧ BeltAckSeen st g.authorized_epoch g.msg_tag i.val calls := by
  have hi := belt_run_guard_inv hr hinv
  obtain ⟨_, _, he, hm, hc, hq, _⟩ := belt_outcome_granted_inv (belt_step_outcome hg)
  rw [beltMaskAbs_card]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hi.2.1, ← hi.2.2.1]; exact hq
  · rw [hc]; exact hi.2.2.1
  · intro i hb
    exact ⟨hi.2.2.2 i.val hb, he ▸ hm ▸ belt_run_bitmap_provenance hr hz i.val hb⟩

/-- The canonical mask intersection inherits the extracted quorum intersection bound. -/
theorem belt_quorum_intersection_refines_qsag
    {n f q : Std.U32} {a b : Std.U64}
    (hc : n.val + f.val < 2 * q.val)
    (ha : q.val ≤ beltPopcount a) (hba : ∀ i, a.bv.getLsbD i = true → i < n.val)
    (hb : q.val ≤ beltPopcount b) (hbb : ∀ i, b.bv.getLsbD i = true → i < n.val) :
    f.val < Qsag.maskCard (Qsag.maskInter (beltMaskAbs a) (beltMaskAbs b)) := by
  rw [← beltMaskAbs_inter, beltMaskAbs_card]
  exact belt_quorum_intersection hc ha hba hb hbb
/-- Constructor-to-grant weld: the caller need not assume empty bitmap, count/range
invariants, or the quorum intersection configuration separately. They follow from the
actual validated constructor, and the run includes rejected calls. -/
theorem belt_validated_grant_refines_qsag_mask
    {n t f q : Std.U32} {gl : Bool} {e0 window : Std.U64}
    {commit wal : Array Std.U8 32#usize} {keys : Array (Array Std.U8 32#usize) 64#usize}
    {initial st st' : authenticated_belt.VerifiedBeltQuorumGuard}
    {calls : List BeltCall} {a : BeltAction}
    {g : pants_and_quorum_guards.BeltAuthorizationGrant}
    (hn : authenticated_belt.VerifiedBeltQuorumGuard.new_validated
      n t f q gl e0 window commit keys wal = .ok (.Ok initial))
    (hr : BeltRun initial calls st)
    (hg : authenticated_belt.VerifiedBeltQuorumGuard.step st a =
      .ok (st', .Ok (.SharesAuthorized g))) :
    n.val + f.val < 2 * q.val ∧
    q.val ≤ Qsag.maskCard (beltMaskAbs st.ack_bitmap) ∧
    g.certified_acks.val = Qsag.maskCard (beltMaskAbs st.ack_bitmap) ∧
    ∀ i : Fin 64, (beltMaskAbs st.ack_bitmap).mem i = true →
      i.val < n.val ∧ BeltAckSeen st g.authorized_epoch g.msg_tag i.val calls := by
  obtain ⟨hz, hi, hq⟩ := belt_new_validated_provenance_init hn
  exact ⟨hq, belt_grant_refines_qsag_mask hr hz hi hg⟩

end qsag_verified.proofs
