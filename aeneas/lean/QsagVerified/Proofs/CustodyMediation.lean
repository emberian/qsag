module
import all QsagVerified.Funs
public import QsagVerified.Proofs.ConsumingOpening

/-!
Mediation of the two production opening rounds by the extracted guard, in the shape
production calls it: the request names the provisioned session, round and binding.

* `sigma_release_iff`: the policy sigma round (`qsag-policy`, `release_sigma_round`) yields a
  permit exactly when the expected nonzero number of openings was folded, each matched its
  frozen commitment, and both sigma lanes XOR to zero. `AuthorizedSignReleaseToken::mint`
  takes that permit by value.
* `plane_open_release_iff`: the quorum plane opening (`qsag-quorum`, `open_inner`) folds one
  opening with zero lanes whose two digests are the copies of the missing share slot; the
  permit `reconstruct_opened` consumes exists exactly when the copies' digests agree.
* `opening_round_single_release` (in `ConsumingOpening`): neither round releases twice.

These are statements about the extracted guard. That production constructs its outputs only
from the permit is enforced by Rust privacy and move semantics, not proved here.
-/

public section
namespace qsag_verified.proofs
open Aeneas Aeneas.Std Result qsag_verified

private theorem u128_or_eq_zero_iff (a b : Std.U128) :
    a ||| b = 0#u128 ↔ a = 0#u128 ∧ b = 0#u128 := by
  constructor
  · intro h
    obtain ⟨ha, hb⟩ := BitVec.or_eq_zero_iff.mp (congrArg UScalar.bv h)
    exact ⟨UScalar.ext ha, UScalar.ext hb⟩
  · rintro ⟨rfl, rfl⟩; rfl

private theorem laneSum_single (x : OpeningInput) (k : Nat) :
    openingLaneSum [x] k = x.2.2.val.getD k 0#u128 := by
  simp only [openingLaneSum, List.foldl_cons, List.foldl_nil]
  exact UScalar.ext BitVec.zero_xor

/-- The policy sigma round releases exactly on a complete, committed, zero-sum opening. -/
theorem sigma_release_iff (sid : Array Std.U8 32#usize) (round : Std.U64)
    (binding : Array Std.U8 32#usize) (n : Std.U64) (xs : List OpeningInput) :
    (∃ t p, openingRound sid round binding n xs sid round binding = .ok (t, some p)) ↔
      (n ≠ 0#u64 ∧ xs.length = n.val ∧ (∀ x ∈ xs, x.1 = x.2.1) ∧
        openingLaneSum xs 0 = 0#u128 ∧ openingLaneSum xs 1 = 0#u128) := by
  constructor
  · rintro ⟨t, p, h⟩
    obtain ⟨⟨_, _, _, hn, hlen, hmem, hz⟩, _⟩ :=
      opening_round_permit_sound sid round binding n xs sid round binding t p h
    exact ⟨hn, hlen, hmem, (u128_or_eq_zero_iff _ _).mp hz⟩
  · rintro ⟨hn, hlen, hmem, hz⟩
    exact opening_round_permit_complete sid round binding n xs sid round binding
      ⟨rfl, rfl, rfl, hn, hlen, hmem, (u128_or_eq_zero_iff _ _).mpr hz⟩

/-- A sigma permit names the session and round it was provisioned for and the number of
openings it folded, and its guard is spent. -/
theorem sigma_release_permit (sid : Array Std.U8 32#usize) (round : Std.U64)
    (binding : Array Std.U8 32#usize) (n : Std.U64) (xs : List OpeningInput)
    (t : OpeningGuard) (p : OpeningPermit)
    (h : openingRound sid round binding n xs sid round binding = .ok (t, some p)) :
    p.session_id = sid ∧ p.round_id = round ∧ p.openings = n ∧ t.consumed = true :=
  (opening_round_permit_sound sid round binding n xs sid round binding t p h).2

/-- The quorum plane opening releases exactly when the two copies' digests agree. -/
theorem plane_open_release_iff (sid : Array Std.U8 32#usize) (round : Std.U64)
    (binding copyPred copySucc : Array Std.U8 32#usize) :
    (∃ t p, openingRound sid round binding 1#u64
        [(copyPred, copySucc, Array.repeat 2#usize 0#u128)] sid round binding =
          .ok (t, some p)) ↔ copyPred = copySucc := by
  rw [sigma_release_iff]
  constructor
  · rintro ⟨_, _, hmem, _, _⟩
    exact hmem _ (List.mem_singleton.mpr rfl)
  · intro h
    refine ⟨by decide, rfl, fun x hx => ?_, ?_, ?_⟩
    · rw [List.mem_singleton.mp hx]
      exact h
    · rw [laneSum_single]; rfl
    · rw [laneSum_single]; rfl

/-- A wrong session, round or binding in the request never releases, whatever was folded. -/
theorem tooth_opening_wrong_context_refused (sid : Array Std.U8 32#usize) (round : Std.U64)
    (binding : Array Std.U8 32#usize) (n : Std.U64) (xs : List OpeningInput)
    (sid' : Array Std.U8 32#usize) (round' : Std.U64) (binding' : Array Std.U8 32#usize)
    (hctx : sid' ≠ sid ∨ round' ≠ round ∨ binding' ≠ binding) :
    ∃ t, openingRound sid round binding n xs sid' round' binding' = .ok (t, none) ∧
      t.consumed = true := by
  apply opening_round_refused
  rintro ⟨hs, hr, hb, _⟩
  rcases hctx with h | h | h
  · exact h hs
  · exact h hr
  · exact h hb

/-- One nonzero sigma lane refuses a single committed opening. -/
theorem tooth_sigma_nonzero_lane_refused (sid : Array Std.U8 32#usize) (round : Std.U64)
    (binding c : Array Std.U8 32#usize) :
    ∃ t, openingRound sid round binding 1#u64
        [(c, c, Array.make 2#usize [1#u128, 0#u128])] sid round binding = .ok (t, none) := by
  obtain ⟨t, h, _⟩ := opening_round_refused sid round binding 1#u64
    [(c, c, Array.make 2#usize [1#u128, 0#u128])] sid round binding (by
      rintro ⟨_, _, _, _, _, _, hz⟩
      rw [laneSum_single, laneSum_single] at hz
      have h1 : (1#u128 : Std.U128) = 0#u128 := ((u128_or_eq_zero_iff _ _).mp hz).1
      exact absurd h1 (by decide))
  exact ⟨t, h⟩

end qsag_verified.proofs
