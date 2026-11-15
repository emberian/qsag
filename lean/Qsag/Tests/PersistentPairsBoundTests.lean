module
/- Nonempty instances and countermodels for the persistent CWYZ count. -/
public import Qsag.Coding.PersistentPairsBound
import all Qsag.Coding.PersistentPairsBound
import all Qsag.Coding.AffineIncidenceBound
import all Qsag.Coding.PolyMv3
import all Qsag.Coding.AffineProximityGaps
import all Qsag.Math.Goldilocks
public section
namespace Qsag
open CommRingOps RoundPoly

/-! ## Assurance Witnesses -/

namespace PersistentPairsTests
open UPoly Poly3

def g (n : Nat) : Goldilocks := Goldilocks.ofNat n

def dom4 : List Goldilocks := [g 0, g 1, g 2, g 3]
def pool2 : List Goldilocks := [g 1, g 2]

/-- Witness that `persistent_pairs_card_le` is inhabited on `Goldilocks` (`|D| = 4`, `d = 1`,
    `B = 3`, `A = 4`, where `4 * 2 = 8 < 9 = 3^2`, using `poleWords` which has no correlated
    agreement `≥ 3` while diagonal challenges `(β, β)` have rational explanation `H = 1, L = X + 1`). -/
theorem inhabited_persistent_pairs_card_le :
    ∃ (x : (Goldilocks → Goldilocks) × (Goldilocks → Goldilocks))
      (D S : List Goldilocks) (d A B : Nat) (L : List (Goldilocks × Goldilocks)),
      D.Nodup ∧ S.Nodup ∧ D.length * (d + 1) < B * B ∧
      ¬ HasCorrelatedAgreement d (A - 1) x.1 x.2 D ∧
      L.Nodup ∧ (∀ p ∈ L, p ∈ prodPool S) ∧ 1 ≤ L.length ∧
      (∀ p ∈ L, ∃ P : UPoly Goldilocks, P.natDeg ≤ d ∧
        A ≤ (D.filter (foldAgreePt x p.1 p.2 P)).length ∧
        IsPersistent x D d B p.1 p.2 P) := by
  refine ⟨poleWords, dom4, pool2, 1, 4, 3, [(g 1, g 1)],
    by decide, by decide, by decide,
    poleWords_far dom4 1 4 (by decide) (by decide +kernel) (by decide) (by decide),
    by decide, by decide, by decide, ?_⟩
  intro p hp
  rw [List.mem_singleton.mp hp]
  refine ⟨C (g 1), by decide +kernel, by decide +kernel,
    one, ofList [one, one], by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

/-- `#tooth`: dropping `¬ HasCorrelatedAgreement d (A - 1) f g D` invalidates Lemma 4.5:
    for `f = 0, g = 0` on `D = [0, 1, 2, 3]`, `S = [0, 1, 2]` (`|S| = 3`), `d = 1, B = 3, A = 4`,
    ALL `|S|² = 9` challenges admit `P = 0` (persistent via `H = 0, L = 1`), exceeding
    `ℓ · max(|S|, n(n-1)/2) = (4·1 / 1) · max(3, 6)` at `S = [0, 1, 2, 3, 4, 5, 6]` (`49 > 4 · 7 = 28`). -/
theorem tooth_persistent_needs_far :
    ∃ (x : (Goldilocks → Goldilocks) × (Goldilocks → Goldilocks))
      (D S : List Goldilocks) (d A B : Nat) (L : List (Goldilocks × Goldilocks)),
      D.Nodup ∧ S.Nodup ∧ D.length * (d + 1) < B * B ∧
      L.Nodup ∧ (∀ p ∈ L, p ∈ prodPool S) ∧
      (∀ p ∈ L, ∃ P : UPoly Goldilocks, P.natDeg ≤ d ∧
        A ≤ (D.filter (foldAgreePt x p.1 p.2 P)).length ∧
        IsPersistent x D d B p.1 p.2 P) ∧
      ¬ (L.length ≤ ((D.length * (B - (d + 1))) / (B * B - D.length * (d + 1))) *
          Nat.max S.length (D.length * (D.length - 1) / 2)) := by
  let S7 : List Goldilocks := [g 0, g 1, g 2, g 3, g 4, g 5, g 6]
  refine ⟨(fun _ => zero, fun _ => zero), dom4, S7, 1, 4, 3, prodPool S7,
    by decide, by decide, by decide, prodPool_nodup (by decide), fun _ h => h, ?_, by decide⟩
  intro p _
  have hz0 : ∀ z : Goldilocks, (zero : UPoly Goldilocks).eval z = zero := fun _ => rfl
  have hAgAll : dom4.filter (foldAgreePt (fun _ => zero, fun _ => zero) p.1 p.2 zero) = dom4 :=
    filter_eq_self_of_all _ dom4 (fun z _ => decide_eq_true (by
      show (zero : UPoly Goldilocks).eval z = add zero (mul (add p.1 (mul p.2 z)) zero)
      rw [hz0 z, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]))
  have hPersAll : dom4.filter (fun z =>
      decide ((one : UPoly Goldilocks).eval z ≠ zero) &&
      foldAgreePt (fun _ => zero, fun _ => zero) p.1 p.2 zero z &&
      decide ((zero : UPoly Goldilocks).eval z = mul zero ((one : UPoly Goldilocks).eval z))) = dom4 :=
    filter_eq_self_of_all _ dom4 (fun z _ => by
      simp only [Bool.and_eq_true]
      have h1 : (one : UPoly Goldilocks).eval z = one := by rw [one_eq_C, eval_C]
      refine ⟨⟨decide_eq_true (by rw [h1]; exact LawfulField.one_ne_zero), ?_⟩,
        decide_eq_true (by rw [hz0 z, LawfulCommRing.zero_mul])⟩
      exact decide_eq_true (by
        show (zero : UPoly Goldilocks).eval z = add zero (mul (add p.1 (mul p.2 z)) zero)
        rw [hz0 z, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]))
  refine ⟨zero, by decide +kernel, ?_, zero, one, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  · rw [hAgAll]; decide
  · rw [hPersAll]; decide

/-- The candidate-specific theorem has the same nonempty pole-word instance, including
an explicit selected polynomial for every counted challenge. -/
theorem inhabited_exceptional_persistent_pairs :
    ∃ (x : (Goldilocks → Goldilocks) × (Goldilocks → Goldilocks))
      (D S : List Goldilocks) (d A B : Nat) (L : List (Goldilocks × Goldilocks)),
      D.Nodup ∧ S.Nodup ∧ D.length * (d + 1) < B * B ∧
      L.Nodup ∧ (∀ p ∈ L, p ∈ prodPool S) ∧ 1 ≤ L.length ∧
      (∀ p ∈ L, ∃ P : UPoly Goldilocks, P.natDeg ≤ d ∧
        A ≤ (D.filter (foldAgreePt x p.1 p.2 P)).length ∧
        IsPersistent x D d B p.1 p.2 P ∧
        ¬ HasPolynomialExplanation x D d (A - 1) p.1 p.2 P) := by
  refine ⟨poleWords, dom4, pool2, 1, 4, 3, [(g 1, g 1)],
    by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  intro p hp
  rw [List.mem_singleton.mp hp]
  refine ⟨C (g 1), by decide +kernel, by decide +kernel, ?_, ?_⟩
  · exact ⟨one, ofList [one, one], by decide +kernel, by decide +kernel,
      by decide +kernel, by decide +kernel⟩
  · rintro ⟨Fp, Gp, hF, hG, hAgree, _⟩
    exact poleWords_far dom4 1 4 (by decide) (by decide +kernel) (by decide) (by decide)
      ⟨Fp, Gp, hF, hG, hAgree⟩

#verify_constructive inhabited_exceptional_persistent_pairs
#verify_inhabited exceptional_persistent_pairs_card_le inhabited_exceptional_persistent_pairs
#tooth_pair exceptional_persistent_pairs_card_le vs tooth_persistent_needs_far
#verify_constructive nonpersistent_common_agree_le rat_pair_collinear_or_polys
#verify_constructive exceptional_persistent_challenges_per_witness_le exceptional_persistent_pairs_card_le
#verify_constructive persistent_challenges_per_witness_le persistent_pairs_card_le
#verify_constructive inhabited_persistent_pairs_card_le tooth_persistent_needs_far
#tooth_pair persistent_pairs_card_le vs tooth_persistent_needs_far
#verify_inhabited persistent_pairs_card_le inhabited_persistent_pairs_card_le

end PersistentPairsTests

end Qsag
end
