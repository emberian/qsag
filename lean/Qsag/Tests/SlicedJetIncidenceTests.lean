module
/-
# Witnesses for `SlicedJetIncidence`

* `inhabited_slice` and `inhabited_nonExcluded_pairs`: the hypotheses of `slice_card_le` and
  `nonExcluded_pairs_card_le` hold together on a nonempty list, with an accepted root that is
  neither persistent nor explained by a polynomial pair.
* `tooth_slice_needs_nonpersistent`: for the zero words every intercept is accepted on the
  slice `β = 0`; ten of them exceed the slice bound `9`. So the count on a slice is a count of
  nonpersistent candidates only.
-/
public import Qsag.Coding.SlicedJetIncidence
import all Qsag.Coding.SlicedJetIncidence
import all Qsag.Coding.PersistentPairsBound
import all Qsag.Coding.PolyMv3
import all Qsag.Coding.SylvesterResultant
import all Qsag.Coding.DynamicGcdSplit
import all Qsag.Coding.SimpleRootStratification
import all Qsag.Coding.AffineIncidenceBound
import all Qsag.Coding.AffineProximityGaps
import all Qsag.Math.Goldilocks

public section
namespace Qsag
namespace SlicedJetTests

set_option autoImplicit false

open CommRingOps RoundPoly UPoly Poly3

local instance : NoZeroDivisors Goldilocks := LawfulField.toNoZeroDivisors Goldilocks

def two : Goldilocks := Goldilocks.ofNat 2
def three : Goldilocks := Goldilocks.ofNat 3

/-- `f = 0`, `g = (0, 0, 1, 1)` on `D = {0, 1, 2, 3}`. -/
def stepWords : (Goldilocks → Goldilocks) × (Goldilocks → Goldilocks) :=
  (fun _ => zero, fun z => if z = zero ∨ z = one then zero else one)
def zeroWords : (Goldilocks → Goldilocks) × (Goldilocks → Goldilocks) :=
  (fun _ => zero, fun _ => zero)
def dom : List Goldilocks := [zero, one, two, three]
def tenPts : List Goldilocks :=
  [zero, one, two, three, Goldilocks.ofNat 4, Goldilocks.ofNat 5, Goldilocks.ofNat 6,
    Goldilocks.ofNat 7, Goldilocks.ofNat 8, Goldilocks.ofNat 9]

/-- The surface `Z = 0`. -/
def zSurface : Poly3 Goldilocks := X

private theorem three_of_four (p : Goldilocks → Bool) (h : 3 ≤ (dom.filter p).length) :
    (p zero = true ∧ p one = true ∧ (p two = true ∨ p three = true)) ∨
    (p two = true ∧ p three = true ∧ (p zero = true ∨ p one = true)) := by
  unfold dom at h
  cases h0 : p zero <;> cases h1 : p one <;> cases h2 : p two <;> cases h3 : p three <;>
    first
    | exact .inl ⟨rfl, rfl, .inl rfl⟩
    | exact .inl ⟨rfl, rfl, .inr rfl⟩
    | exact .inr ⟨rfl, rfl, .inl rfl⟩
    | exact .inr ⟨rfl, rfl, .inr rfl⟩
    | (exfalso
       simp only [List.filter, h0, h1, h2, h3, List.length_cons, List.length_nil] at h
       exact absurd h (by decide))

private theorem eq_zero_of_two_roots (H : UPoly Goldilocks) (hd : H.natDeg ≤ 1)
    (a b : Goldilocks) (hab : a ≠ b) (ha : H.eval a = zero) (hb : H.eval b = zero) :
    H = zero := by
  apply Decidable.byContradiction
  intro hne
  have hr := uPoly_roots_le_natDeg H hne [a, b]
    (List.pairwise_cons.mpr ⟨(fun c hc => by rw [List.mem_singleton.mp hc]; exact hab),
      List.pairwise_cons.mpr ⟨(fun _ hc => absurd hc List.not_mem_nil), List.Pairwise.nil⟩⟩)
    (fun z hz => by
      rcases List.mem_cons.mp hz with e | hz'
      · rw [e]; exact ha
      · rw [List.mem_singleton.mp hz']; exact hb)
  exact absurd (Nat.le_trans hr hd) (Nat.not_succ_le_self 1)

/-- The candidate `(α, β, P) = (0, 0, 0)` agrees with the fold of `stepWords` everywhere and
    has no rational explanation `H / L` on three coordinates. -/
theorem stepWords_nonpersistent :
    ¬ IsPersistent stepWords dom 1 3 zero zero (zero : UPoly Goldilocks) := by
  rintro ⟨H, L, _, hLd, hHd, hsize⟩
  have hmem : ∀ z : Goldilocks, (decide (L.eval z ≠ zero) &&
      foldAgreePt stepWords zero zero zero z &&
      decide (H.eval z = mul (stepWords.2 z) (L.eval z))) = true →
      L.eval z ≠ zero ∧ H.eval z = mul (stepWords.2 z) (L.eval z) := fun z hz => by
    obtain ⟨hl, hh⟩ := Bool.and_eq_true_iff.mp hz
    exact ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp hl).1, of_decide_eq_true hh⟩
  have hlow : ∀ z : Goldilocks, stepWords.2 z = zero → (decide (L.eval z ≠ zero) &&
      foldAgreePt stepWords zero zero zero z &&
      decide (H.eval z = mul (stepWords.2 z) (L.eval z))) = true →
      L.eval z ≠ zero ∧ H.eval z = zero := fun z hg hz => by
    obtain ⟨h1, h2⟩ := hmem z hz
    rw [hg, LawfulCommRing.zero_mul] at h2
    exact ⟨h1, h2⟩
  have hhigh : ∀ z : Goldilocks, stepWords.2 z = one → (decide (L.eval z ≠ zero) &&
      foldAgreePt stepWords zero zero zero z &&
      decide (H.eval z = mul (stepWords.2 z) (L.eval z))) = true →
      L.eval z ≠ zero ∧ H.eval z = L.eval z := fun z hg hz => by
    obtain ⟨h1, h2⟩ := hmem z hz
    rw [hg, LawfulCommRing.one_mul] at h2
    exact ⟨h1, h2⟩
  have g0 : stepWords.2 zero = zero := by decide +kernel
  have g1 : stepWords.2 one = zero := by decide +kernel
  have g2 : stepWords.2 two = one := by decide +kernel
  have g3 : stepWords.2 three = one := by decide +kernel
  rcases three_of_four _ hsize with ⟨h0, h1, h23⟩ | ⟨h2, h3, h01⟩
  · have hH : H = zero := eq_zero_of_two_roots H hHd zero one (by decide +kernel)
      (hlow zero g0 h0).2 (hlow one g1 h1).2
    have hcontra : ∀ w : Goldilocks, L.eval w ≠ zero ∧ H.eval w = L.eval w → False :=
      fun w hw => hw.1 (by rw [← hw.2, hH]; rfl)
    rcases h23 with h | h
    · exact hcontra two (hhigh two g2 h)
    · exact hcontra three (hhigh three g3 h)
  · have hsub : sub H L = zero := eq_zero_of_two_roots (sub H L)
      (natDeg_sub_le_max H L 1 hHd hLd) two three (by decide +kernel)
      (by rw [eval_sub_eq, (hhigh two g2 h2).2, LawfulCommRing.sub_self])
      (by rw [eval_sub_eq, (hhigh three g3 h3).2, LawfulCommRing.sub_self])
    have hHL : H = L := LawfulCommRing.sub_eq_zero_iff.mp hsub
    have hcontra : ∀ u : Goldilocks, L.eval u ≠ zero ∧ H.eval u = zero → False :=
      fun u hu => hu.1 (by rw [← hHL]; exact hu.2)
    rcases h01 with h | h
    · exact hcontra zero (hlow zero g0 h)
    · exact hcontra one (hlow one g1 h)

/-- No pair `(F, G)` with `G` constant agrees with `stepWords` on three coordinates. -/
theorem stepWords_unexplained :
    ¬ HasPolynomialExplanation stepWords dom 1 (4 - 1) zero zero (zero : UPoly Goldilocks) := by
  rintro ⟨Fp, Gp, _, hG, hAg, _⟩
  have hdomNd : dom.Nodup := by decide +kernel
  obtain ⟨c, hc⟩ : ∃ c : Goldilocks, ∀ z, evalCoeffs Gp z = c := by
    match Gp, hG with
    | [], _ => exact ⟨zero, fun _ => rfl⟩
    | [c], _ =>
      exact ⟨c, fun z => by
        show add c (mul z zero) = c
        rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]⟩
    | _ :: _ :: _, h => exact absurd (Nat.le_of_succ_le_succ h) (Nat.not_succ_le_zero _)
  have hb : (dom.filter (fun z => decide (evalCoeffs Fp z = stepWords.1 z) &&
      decide (evalCoeffs Gp z = stepWords.2 z))).length ≤
      (dom.filter (fun z => decide (stepWords.2 z = c))).length :=
    nodup_length_le_of_subset (nodup_filter _ dom hdomNd) (fun z hz => by
      obtain ⟨hzD, hpair⟩ := List.mem_filter.mp hz
      have he : evalCoeffs Gp z = stepWords.2 z :=
        of_decide_eq_true (Bool.and_eq_true_iff.mp hpair).2
      exact List.mem_filter.mpr ⟨hzD, decide_eq_true (he.symm.trans (hc z))⟩)
  have h2 : (dom.filter (fun z => decide (stepWords.2 z = c))).length ≤ 2 := by
    if h0 : c = zero then
      rw [h0]; decide +kernel
    else
      have hs : (dom.filter (fun z => decide (stepWords.2 z = c))).length ≤
          (dom.filter (fun z => decide (stepWords.2 z ≠ zero))).length :=
        nodup_length_le_of_subset (nodup_filter _ dom hdomNd) (fun z hz => by
          obtain ⟨hzD, he⟩ := List.mem_filter.mp hz
          have he' : stepWords.2 z = c := of_decide_eq_true he
          exact List.mem_filter.mpr ⟨hzD, decide_eq_true (fun e => h0 (he'.symm.trans e))⟩)
      have hn : (dom.filter (fun z => decide (stepWords.2 z ≠ zero))).length = 2 := by
        decide +kernel
      rw [hn] at hs
      exact hs
  exact absurd (Nat.le_trans hAg (Nat.le_trans hb h2)) (by decide)

/-- The hypotheses of `slice_card_le` hold on a nonempty slice. -/
theorem inhabited_slice :
    ∃ (x : (Goldilocks → Goldilocks) × (Goldilocks → Goldilocks)) (D : List Goldilocks)
      (d A B h : Nat) (R : Poly3 Goldilocks) (β : Goldilocks) (as : List Goldilocks),
      D.Nodup ∧ 1 ≤ d ∧ 1 ≤ h ∧ B < A ∧ d + 1 ≤ B ∧ R.degYZ ≤ h ∧ R.degZ ≤ 1 ∧
      (∀ a ∈ as, ∃ P : UPoly Goldilocks, P.natDeg ≤ d ∧
        A ≤ (D.filter (foldAgreePt x a β P)).length ∧ evalAffineLine R a β P = zero ∧
        evalAffineLine (hasseZ 1 R) a β P ≠ zero ∧ ¬ IsPersistent x D d B a β P) ∧
      as.Nodup ∧ as.length = 1 := by
  refine ⟨stepWords, dom, 1, 4, 3, 1, zSurface, zero, [zero], by decide +kernel, by decide,
    by decide, by decide, by decide, by decide +kernel, by decide +kernel, ?_,
    by decide +kernel, rfl⟩
  intro a ha
  rw [List.mem_singleton.mp ha]
  exact ⟨zero, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    stepWords_nonpersistent⟩

/-- Without nonpersistence the slice bound fails: all ten intercepts are accepted for the
    zero words, against a bound of `9`. -/
theorem tooth_slice_needs_nonpersistent :
    ∃ (x : (Goldilocks → Goldilocks) × (Goldilocks → Goldilocks)) (D : List Goldilocks)
      (d A B h : Nat) (R : Poly3 Goldilocks) (β : Goldilocks) (as : List Goldilocks),
      D.Nodup ∧ 1 ≤ d ∧ 1 ≤ h ∧ B < A ∧ d + 1 ≤ B ∧ R.degYZ ≤ h ∧ R.degZ ≤ 1 ∧
      (∀ a ∈ as, ∃ P : UPoly Goldilocks, P.natDeg ≤ d ∧
        A ≤ (D.filter (foldAgreePt x a β P)).length ∧ evalAffineLine R a β P = zero ∧
        evalAffineLine (hasseZ 1 R) a β P ≠ zero) ∧
      as.Nodup ∧ ¬ as.length ≤ h * (D.length * (1 * (2 * d * h)) / (A - B) + 1) := by
  have key : ∀ a ∈ tenPts, (zero : UPoly Goldilocks).natDeg ≤ 1 ∧
      4 ≤ (dom.filter (foldAgreePt zeroWords a zero zero)).length ∧
      evalAffineLine zSurface a zero zero = zero ∧
      evalAffineLine (hasseZ 1 zSurface) a zero zero ≠ zero := by decide +kernel
  exact ⟨zeroWords, dom, 1, 4, 3, 1, zSurface, zero, tenPts, by decide +kernel, by decide,
    by decide, by decide, by decide, by decide +kernel, by decide +kernel,
    fun a ha => ⟨zero, key a ha⟩, by decide +kernel, by decide⟩

/-- The hypotheses of `nonExcluded_pairs_card_le` hold together with a counted challenge. -/
theorem inhabited_nonExcluded_pairs :
    ∃ (x : (Goldilocks → Goldilocks) × (Goldilocks → Goldilocks)) (D S : List Goldilocks)
      (d A B h : Nat) (Q : Poly3 Goldilocks) (L : List (Goldilocks × Goldilocks)),
      D.Nodup ∧ S.Nodup ∧ 1 ≤ d ∧ 1 ≤ h ∧ B < A ∧ d + 1 ≤ B ∧
      D.length * (d + 1) < B * B ∧ Q.degYZ ≤ h ∧ Q.deg11d d ≤ 1 ∧
      (∀ k, 1 ≤ k → k ≤ Q.degZ → (CRing.natCast k : Goldilocks) ≠ zero) ∧ L.Nodup ∧
      (∀ p ∈ L, p ∈ prodPool S ∧ lineSpec Q p.1 p.2 ≠ zero ∧
        ∃ P : UPoly Goldilocks, P.natDeg ≤ d ∧
          A ≤ (D.filter (foldAgreePt x p.1 p.2 P)).length ∧
          evalAffineLine Q p.1 p.2 P = zero ∧
          ¬ HasPolynomialExplanation x D d (A - 1) p.1 p.2 P) ∧
      L.length = 1 := by
  have hdz : zSurface.degZ = 1 := by decide +kernel
  refine ⟨stepWords, dom, dom, 1, 4, 3, 1, zSurface, [(zero, zero)], by decide +kernel,
    by decide +kernel, by decide, by decide, by decide, by decide, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_, by decide +kernel, ?_, rfl⟩
  · intro k h1 h2
    rw [hdz] at h2
    rw [Nat.le_antisymm h2 h1]
    exact LawfulField.one_ne_zero
  · intro p hp
    rw [List.mem_singleton.mp hp]
    exact ⟨by decide +kernel, by decide +kernel, zero, by decide +kernel, by decide +kernel,
      by decide +kernel, stepWords_unexplained⟩

#verify_constructive Poly3.jetEq_pt Poly3.deg_jetEq_le Poly3.primY_liftK_eval
#verify_constructive Poly3.slice_card_le Poly3.nonExcluded_pairs_card_le
#verify_constructive SlicedJet.cover_count SlicedJet.leaf_bound_arith
#verify_constructive stepWords_nonpersistent stepWords_unexplained
#verify_constructive inhabited_slice tooth_slice_needs_nonpersistent inhabited_nonExcluded_pairs
#verify_inhabited Poly3.slice_card_le inhabited_slice
#tooth_pair Poly3.slice_card_le vs tooth_slice_needs_nonpersistent
#verify_inhabited Poly3.nonExcluded_pairs_card_le inhabited_nonExcluded_pairs

end SlicedJetTests
end Qsag
end
