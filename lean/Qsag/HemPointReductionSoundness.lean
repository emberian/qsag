module
/-
# Hem point-reduction sumcheck: wire decoding and bad-challenge counting

The point-reduction verifier in pcs.rs uses two coefficients c0,c2 and reconstructs
c1 = claim - 2*c0 - c2. Its sum equation is therefore a consequence of the wire decoder,
not an independent premise. This module proves that identity and a two-root bound for
agreement with a genuine quadratic having a different hypercube sum.

The polynomial root argument is integrated from the earlier HemStateFunctionRbr draft.
It is a local algebraic result; neither adaptive composition nor a Rust refinement theorem
is claimed here. The separate implementation refinement lives in the WHIR leaf project.
-/
public import Qsag.MultiRoundFsQrom
public import Qsag.Tactic.ConstructiveRing
public import Qsag.Tactic.AssuranceKit
import all Qsag.MultiRoundFsQrom

public section
namespace Qsag
set_option autoImplicit false

private theorem cFilter_congr {α : Type} {p q : α → Bool} :
    ∀ (xs : List α), (∀ x ∈ xs, p x = q x) → xs.filter p = xs.filter q
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.filter_cons, h x (.head xs),
      cFilter_congr xs (fun y hy => h y (.tail x hy))]

/-- A checked false sumcheck message can agree with a true bounded-degree polynomial at
    at most `deg` challenges in a duplicate-free pool. -/
theorem hemSumcheck_polynomial_collision_count {F : Type} [LawfulField F] [DecidableEq F]
    (deg : Nat) (G H_sent S : List F) (claim : F)
    (hS : S.Nodup) (hG : G.length ≤ deg + 1) (hH : H_sent.length ≤ deg + 1)
    (hCheck : CommRingOps.add (RoundPoly.evalCoeffs H_sent CommRingOps.zero)
                (RoundPoly.evalCoeffs H_sent CommRingOps.one) = claim)
    (hFalse : claim ≠ CommRingOps.add (RoundPoly.evalCoeffs G CommRingOps.zero)
                        (RoundPoly.evalCoeffs G CommRingOps.one)) :
    (S.filter (fun r => decide (RoundPoly.evalCoeffs H_sent r = RoundPoly.evalCoeffs G r))).length ≤
      deg := by
  let diff := polySubVar H_sent G
  have hNz : ∃ x₀ : F, RoundPoly.evalCoeffs diff x₀ ≠ CommRingOps.zero := by
    by_cases h0 : RoundPoly.evalCoeffs H_sent CommRingOps.zero =
        RoundPoly.evalCoeffs G CommRingOps.zero
    · refine ⟨CommRingOps.one, fun h1 => hFalse ?_⟩
      rw [evalCoeffs_polySubVar] at h1
      rw [← hCheck, h0, LawfulCommRing.sub_eq_zero_iff.mp h1]
    · exact ⟨CommRingOps.zero, fun hz =>
        h0 (LawfulCommRing.sub_eq_zero_iff.mp (by rwa [evalCoeffs_polySubVar] at hz))⟩
  have hEq : S.filter (fun r => decide (RoundPoly.evalCoeffs H_sent r = RoundPoly.evalCoeffs G r)) =
      S.filter (fun r => decide (RoundPoly.evalCoeffs diff r = CommRingOps.zero)) := by
    refine cFilter_congr S (fun r _ => ?_)
    dsimp only [diff]; rw [evalCoeffs_polySubVar]
    by_cases he : RoundPoly.evalCoeffs H_sent r = RoundPoly.evalCoeffs G r
    · simp only [he, LawfulCommRing.sub_self, decide_true]
    · have hSub : CommRingOps.sub (RoundPoly.evalCoeffs H_sent r)
          (RoundPoly.evalCoeffs G r) ≠ CommRingOps.zero :=
        fun h0 => he (LawfulCommRing.sub_eq_zero_iff.mp h0)
      simp only [he, hSub, decide_false]
  rw [hEq]
  exact @RoundPoly.roots_nodup_length_le F _ _ (LawfulField.toNoZeroDivisors F)
    deg diff S hS (polySubVar_length_le H_sent G (deg + 1) hH hG) hNz


/-- Mathematical coefficient list decoded by the PCS point-reduction quadratic wire. -/
def hemPointReductionWirePoly {F : Type} [CommRingOps F]
    (c0 c2 claim : F) : List F :=
  [c0, CommRingOps.sub (CommRingOps.sub claim (CommRingOps.add c0 c0)) c2, c2]

/-- The compact wire enforces the hypercube sum for every pair of transmitted coefficients. -/
theorem hemPointReductionWire_sum {F : Type} [LawfulCommRing F] (c0 c2 claim : F) :
    CommRingOps.add
      (RoundPoly.evalCoeffs (hemPointReductionWirePoly c0 c2 claim) CommRingOps.zero)
      (RoundPoly.evalCoeffs (hemPointReductionWirePoly c0 c2 claim) CommRingOps.one) = claim := by
  simp only [hemPointReductionWirePoly, RoundPoly.evalCoeffs]
  constructive_ring

/-- The PCS point-reduction wire has at most two challenges agreeing with any genuine
    quadratic whose sum differs from `claim`. The message-length and sum-check premises
    of the general root lemma are discharged from the decoder itself. -/
theorem hemPointReductionWire_bad_challenges_le_two {F : Type} [LawfulField F] [DecidableEq F]
    (G S : List F) (c0 c2 claim : F) (hS : S.Nodup) (hG : G.length ≤ 3)
    (hFalse : claim ≠ CommRingOps.add (RoundPoly.evalCoeffs G CommRingOps.zero)
      (RoundPoly.evalCoeffs G CommRingOps.one)) :
    (S.filter (fun r => decide
      (RoundPoly.evalCoeffs (hemPointReductionWirePoly c0 c2 claim) r =
        RoundPoly.evalCoeffs G r))).length ≤ 2 :=
  hemSumcheck_polynomial_collision_count 2 G (hemPointReductionWirePoly c0 c2 claim) S claim
    hS hG (Nat.le_refl 3) (hemPointReductionWire_sum c0 c2 claim) hFalse

/-- The bound is attained by a false claim: over the pool {0,1,2}, the decoded message
    X(X-2) agrees with the zero polynomial at two points and disagrees at the third. -/
theorem hemPointReductionWire_bound_attained :
    let S : List QuarticGoldilocks :=
      [CommRingOps.zero, CommRingOps.one, CommRingOps.add CommRingOps.one CommRingOps.one]
    let claim : QuarticGoldilocks := CommRingOps.neg CommRingOps.one
    claim ≠ CommRingOps.add
      (RoundPoly.evalCoeffs ([] : List QuarticGoldilocks) CommRingOps.zero)
      (RoundPoly.evalCoeffs ([] : List QuarticGoldilocks) CommRingOps.one) ∧
    (S.filter (fun r => decide
      (RoundPoly.evalCoeffs (hemPointReductionWirePoly CommRingOps.zero CommRingOps.one claim) r =
        RoundPoly.evalCoeffs ([] : List QuarticGoldilocks) r))).length = 2 ∧
    2 < S.length := by decide

#verify_constructive
  Qsag.hemSumcheck_polynomial_collision_count
  Qsag.hemPointReductionWire_sum
  Qsag.hemPointReductionWire_bad_challenges_le_two
  Qsag.hemPointReductionWire_bound_attained
end Qsag
