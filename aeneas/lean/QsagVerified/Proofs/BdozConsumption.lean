module
import all QsagVerified.Funs
public import QsagVerified.Proofs.Bdoz

public section
namespace qsag_verified.proofs
open Aeneas Aeneas.Std Result qsag_verified

/-- Post-attempt state: keys are cleared whether verification accepts or rejects. -/
@[expose] def bdozSpent (s : tower.BdozOpeningGuard2Lane) : tower.BdozOpeningGuard2Lane :=
  { s with alpha_lanes := Array.make 2#usize [0#u128, 0#u128], consumed := true }

/-- Total context-bound verification equation. The cryptographic decision is computed
by MIR, rather than supplied as a trusted boolean by the caller. -/
theorem bdoz_verify_once_eq (s : tower.BdozOpeningGuard2Lane)
    (b : tower.BdozCommittedBatchOpening2Lane) (xs : Slice tower.BdozWireOpening2Lane) :
    tower.BdozOpeningGuard2Lane.verify_once s b xs =
      if s.consumed then .ok (bdozSpent s, false)
      else if s.session_id = b.session_id ∧ s.round_id = b.round_id then
        (do let ok ← tower.verify_mac_2lane s.alpha_lanes b xs; .ok (bdozSpent s, ok))
      else .ok (bdozSpent s, false) := by
  unfold tower.BdozOpeningGuard2Lane.verify_once
  cases hc : s.consumed with
  | true => simp only [ite_true, bdozSpent]
  | false =>
    rw [ct_eq_bytes32_spec]
    simp only [Bool.false_eq_true, ite_false, bind_eq_result_bind, result_bind_ok]
    by_cases hs : s.session_id = b.session_id
    · by_cases hr : s.round_id = b.round_id
      · simp only [hs, hr, decide_true, ite_true, bne_self_eq_false,
          Bool.false_eq_true, ite_false, true_and, bdozSpent]
      · simp [hs, hr, bdozSpent]
    · simp [hs, bdozSpent]

/-- Every attempt terminates with the consumed state; no input can bypass the
lifecycle guarantee by causing failure or divergence in the extracted model. -/
theorem bdoz_verify_once_total (s : tower.BdozOpeningGuard2Lane)
    (b : tower.BdozCommittedBatchOpening2Lane) (xs : Slice tower.BdozWireOpening2Lane) :
    ∃ ok, tower.BdozOpeningGuard2Lane.verify_once s b xs = .ok (bdozSpent s, ok) := by
  obtain ⟨ok, ho⟩ := bdoz_verify_total s.alpha_lanes b xs
  rw [bdoz_verify_once_eq]
  cases s.consumed
  · simp only [Bool.false_eq_true, ite_false]
    split
    · exact ⟨ok, by rw [ho]; rfl⟩
    · exact ⟨false, rfl⟩
  · exact ⟨false, rfl⟩

/-- Reusing a consumed handle always refuses, without touching the batch or MAC. -/
theorem bdoz_verify_once_replay (s : tower.BdozOpeningGuard2Lane)
    (b : tower.BdozCommittedBatchOpening2Lane) (xs : Slice tower.BdozWireOpening2Lane)
    (h : s.consumed = true) :
    tower.BdozOpeningGuard2Lane.verify_once s b xs = .ok (bdozSpent s, false) := by
  rw [bdoz_verify_once_eq, h]; rfl

/-- Any completed attempt consumes the handle and clears both key lanes. -/
theorem bdoz_verify_once_consumes (s t : tower.BdozOpeningGuard2Lane)
    (b : tower.BdozCommittedBatchOpening2Lane) (xs : Slice tower.BdozWireOpening2Lane)
    (ok : Bool) (h : tower.BdozOpeningGuard2Lane.verify_once s b xs = .ok (t, ok)) :
    t = bdozSpent s := by
  rw [bdoz_verify_once_eq] at h
  cases hc : s.consumed <;> simp only [hc, Bool.false_eq_true, ite_false, ite_true] at h
  · split at h
    · cases hv : tower.verify_mac_2lane s.alpha_lanes b xs <;>
        simp only [hv, bind_eq_result_bind, Result.bind, Result.ok.injEq,
          Prod.mk.injEq, reduceCtorEq] at h
      exact h.1.symm
    · exact (Prod.mk.inj (Result.ok.inj h)).1.symm
  · exact (Prod.mk.inj (Result.ok.inj h)).1.symm

/-- No two successive attempts on one handle can both accept. -/
theorem bdoz_verify_once_single_consumption (s t : tower.BdozOpeningGuard2Lane)
    (b b' : tower.BdozCommittedBatchOpening2Lane)
    (xs ys : Slice tower.BdozWireOpening2Lane) (ok : Bool)
    (h : tower.BdozOpeningGuard2Lane.verify_once s b xs = .ok (t, ok)) :
    tower.BdozOpeningGuard2Lane.verify_once t b' ys = .ok (bdozSpent t, false) := by
  apply bdoz_verify_once_replay
  rw [bdoz_verify_once_consumes s t b xs ok h]
  rfl

/-- Acceptance requires the provisioned session and round, and actual MAC verification. -/
theorem bdoz_verify_once_accepted (s t : tower.BdozOpeningGuard2Lane)
    (b : tower.BdozCommittedBatchOpening2Lane) (xs : Slice tower.BdozWireOpening2Lane)
    (h : tower.BdozOpeningGuard2Lane.verify_once s b xs = .ok (t, true)) :
    s.consumed = false ∧ s.session_id = b.session_id ∧ s.round_id = b.round_id ∧
      tower.verify_mac_2lane s.alpha_lanes b xs = .ok true := by
  rw [bdoz_verify_once_eq] at h
  cases hc : s.consumed <;> simp only [hc, Bool.false_eq_true, ite_false, ite_true] at h
  · split at h
    · rename_i hb
      refine ⟨rfl, hb.1, hb.2, ?_⟩
      cases hv : tower.verify_mac_2lane s.alpha_lanes b xs <;>
        simp only [hv, bind_eq_result_bind, Result.bind, Result.ok.injEq,
          Prod.mk.injEq, reduceCtorEq] at h
      rw [h.2]
    · cases (Prod.mk.inj (Result.ok.inj h)).2
  · cases (Prod.mk.inj (Result.ok.inj h)).2

end qsag_verified.proofs
