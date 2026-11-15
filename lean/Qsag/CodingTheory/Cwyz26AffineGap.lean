module
/-
# Qsag.CodingTheory.Cwyz26AffineGap — assembling `[CWYZ26]` Lemma 4.1 onto `AffineMcaBound`

`[CWYZ26]` Lemma 4.1 bounds the exceptional challenges by `|E| + |P| + |N|`: excluded,
persistent and nonpersistent coefficient pairs. This file carries out the part of that
decomposition which is proved in this directory and states the remainder as one hypothesis.

* `NonExcludedBound D S d A m Wx Dy rest`: for words without correlated agreement, at most
  `rest` challenges `(α, β) ∈ S × S` are *not excluded* for the explainer `Q` of Lemma 4.2
  (`Q(X, α + βX, Z) ≠ 0`) and admit `P` of degree at most `d` with agreement at least `A` and
  `Q(X, α + βX, P(X)) = 0`. This is `|P| + |N| ≤ rest`.
* `cwyz26_affineMcaBound_of_nonExcluded`: under the interpolation count (4.5) and
  `Wx + Dy ≤ m·A`, `NonExcludedBound … rest` gives `AffineMcaBound D S d A (Dy + rest)`.
  The interpolation (Lemma 4.2), the passage from acceptance to a root of `Q`, and the count
  `|E| ≤ Dy` of excluded challenges are discharged here.

**Not proved**: `NonExcludedBound` itself for a `rest` of the size in `[CWYZ26]` Theorem 4.10,
namely `ℓ·max{q, n²} + 4d²M²D³(n/(A - B))²`. That needs Lemma 4.5 (the Johnson bound for
agreement sets of rational pairs) and Lemma 4.7 (the incidence count on the image of the
reconstruction map, Claims 4.8 and 4.9). By `affineMcaBound_ge_card` any valid `rest` is at
least `|S| - Dy`. So this file does not prove a proximity gap at the Johnson radius; the
unconditional instance of `AffineMcaBound` remains `affineMcaBound_welch_berlekamp`.
-/

public import Qsag.CodingTheory.AffineIncidenceBound
public import Qsag.CodingTheory.TrivariateGsExplainer
import all Qsag.MultiRoundFsQrom
import all Qsag.CodingTheory.PolyMv3
import all Qsag.CodingTheory.SylvesterResultant
import all Qsag.CodingTheory.DynamicGcdSplit
import all Qsag.CodingTheory.HenselNumerators
import all Qsag.CodingTheory.UniversalHenselLift
import all Qsag.CodingTheory.SimpleRootStratification
import all Qsag.CodingTheory.TrivariateGsExplainer
import all Qsag.CodingTheory.AffineIncidenceBound
import all Qsag.AffineProximityGaps
import all Qsag.Goldilocks

public section
namespace Qsag

set_option autoImplicit false

open CommRingOps RoundPoly

theorem length_filter_add_not {α : Type} (p : α → Bool) : ∀ l : List α,
    (l.filter p).length + (l.filter (fun a => !p a)).length = l.length
  | [] => rfl
  | a :: l => by
    have ih := length_filter_add_not p l
    cases hpa : p a with
    | true =>
      rw [List.filter_cons_of_pos hpa, List.filter_cons_of_neg (by
        show ¬ (!p a) = true
        rw [hpa]; decide)]
      show (l.filter p).length + 1 + _ = l.length + 1
      omega
    | false =>
      rw [List.filter_cons_of_neg (by rw [hpa]; exact Bool.false_ne_true),
        List.filter_cons_of_pos (by show (!p a) = true; rw [hpa]; rfl)]
      show _ + ((l.filter _).length + 1) = l.length + 1
      omega

section Assembly
variable {F : Type} [LawfulField F] [DecidableEq F]
open UPoly Poly3

/-- `P` agrees at `z` with the fold `f + (α + βX)·g` of the words `x = (f, g)`. -/
def foldAgree (x : (F → F) × (F → F)) (α β : F) (P : UPoly F) (z : F) : Bool :=
  decide (P.eval z = add (x.1 z) (mul (add α (mul β z)) (x.2 z)))

/-- **The residual count `|P| + |N| ≤ rest` of `[CWYZ26]` Lemma 4.1**, relative to the
    explainer of Lemma 4.2: among challenges on which the explainer does not vanish
    identically, at most `rest` admit a root of degree at most `d` with agreement `≥ A`. -/
def NonExcludedBound (D S : List F) (d A m Wx Dy rest : Nat) : Prop :=
  ∀ x : (F → F) × (F → F), ¬ HasCorrelatedAgreement d (A - 1) x.1 x.2 D →
    ∀ L : List (F × F), L.Nodup →
      (∀ p ∈ L, p ∈ prodPool S ∧ lineSpec (explainer x.1 x.2 D m d Wx Dy) p.1 p.2 ≠ zero ∧
        ∃ P : UPoly F, P.natDeg ≤ d ∧ A ≤ (D.filter (foldAgree x p.1 p.2 P)).length ∧
          evalAffineLine (explainer x.1 x.2 D m d Wx Dy) p.1 p.2 P = zero) →
      L.length ≤ rest

theorem NonExcludedBound.mono {D S : List F} {d A m Wx Dy rest rest' : Nat}
    (h : NonExcludedBound D S d A m Wx Dy rest) (hle : rest ≤ rest') :
    NonExcludedBound D S d A m Wx Dy rest' :=
  fun x hFar L hNd hL => Nat.le_trans (h x hFar L hNd hL) hle

/-- **`[CWYZ26]` Lemma 4.1, assembled up to the residual count.** Under the interpolation
    count (4.5) and `Wx + Dy ≤ m·A`, a bound `rest` on the non-excluded exceptional
    challenges gives the mutual correlated agreement bound `Dy + rest`: every accepted
    response is a root of the explainer (Lemma 4.2), and at most `Dy` challenges are
    excluded. -/
theorem cwyz26_affineMcaBound_of_nonExcluded (D S : List F) (d A m Wx Dy rest : Nat)
    (hrest : NonExcludedBound D S d A m Wx Dy rest) (hD : D.Nodup) (hS : S.Nodup)
    (hcount : D.length * triCount 1 m Dy m < triCount d Wx Dy (Dy + 1))
    (hWA : Wx + Dy ≤ m * A) : AffineMcaBound D S d A (Dy + rest) := by
  intro x hFar L hNd hEx
  apply Decidable.byContradiction
  intro hGt
  refine not_not_forall_mem _ L hEx (fun hAll => hGt ?_)
  obtain ⟨hQne, hQdeg, _, _⟩ := explainer_spec x.1 x.2 D m d Wx Dy hcount
  have hr := hrest x hFar
  have hfact : ∀ p ∈ L.map (fun ch => (prodPool S).get ch), p ∈ prodPool S ∧
      ∃ P : UPoly F, P.natDeg ≤ d ∧ A ≤ (D.filter (foldAgree x p.1 p.2 P)).length ∧
        evalAffineLine (explainer x.1 x.2 D m d Wx Dy) p.1 p.2 P = zero := by
    intro p hp
    obtain ⟨ch, _, rfl⟩ := List.mem_map.mp hp
    obtain ⟨Pl, hPl⟩ := hAll ch (by assumption)
    unfold affineMcaAccepts at hPl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hPl
    rw [list_getD_eq_get (prodPool S) _ ch] at hPl
    have hfilt : D.filter (foldAgree x ((prodPool S).get ch).1 ((prodPool S).get ch).2
        (ofList Pl)) = D.filter (fun z => decide (evalCoeffs Pl z = add (x.1 z)
          (mul (add ((prodPool S).get ch).1 (mul ((prodPool S).get ch).2 z)) (x.2 z)))) :=
      congrArg (fun q => List.filter q D) (funext fun z => by
        show decide ((ofList Pl).eval z = _) = _
        rw [eval_ofList])
    have hlen : A ≤ (D.filter (foldAgree x ((prodPool S).get ch).1 ((prodPool S).get ch).2
        (ofList Pl))).length := by rw [hfilt]; exact hPl.2
    have hdeg : (ofList Pl).natDeg ≤ d := by
      have h1 := natDeg_ofList_le Pl
      have h2 := hPl.1.2
      omega
    exact ⟨list_get_mem _ ch, ofList Pl, hdeg, hlen,
      explainer_vanishes x.1 x.2 D m d Wx Dy hcount _ _ (ofList Pl) _ hdeg (nodup_filter _ D hD)
        (fun z hz => (List.mem_filter.mp hz).1)
        (fun z hz => of_decide_eq_true (List.mem_filter.mp hz).2)
        (Nat.le_trans hWA (Nat.mul_le_mul_left m hlen))⟩
  have hpNd : (L.map (fun ch => (prodPool S).get ch)).Nodup :=
    List.Pairwise.map _ (fun a b hab hEq => hab (nodup_get_inj (prodPool_nodup hS) hEq)) hNd
  have hlenp : (L.map (fun ch => (prodPool S).get ch)).length = L.length := List.length_map _
  generalize explainer x.1 x.2 D m d Wx Dy = Q at hQne hQdeg hr hfact
  generalize L.map (fun ch => (prodPool S).get ch) = pairs at hfact hpNd hlenp
  have hexc : (pairs.filter (fun p => decide (lineSpec Q p.1 p.2 = zero))).length ≤ Q.degYZ :=
    lineSpec_zero_card_le Q hQne _ (nodup_filter _ _ hpNd)
      (fun p hp => of_decide_eq_true (List.mem_filter.mp hp).2)
  have hnon : (pairs.filter (fun p => !decide (lineSpec Q p.1 p.2 = zero))).length ≤ rest :=
    hr _ (nodup_filter _ _ hpNd) (fun p hp => by
      obtain ⟨hm, hb⟩ := List.mem_filter.mp hp
      obtain ⟨h1, h2⟩ := hfact p hm
      exact ⟨h1, fun e => by
        rw [decide_eq_true e] at hb
        exact absurd hb (by decide), h2⟩)
  have hsum := length_filter_add_not (fun p : F × F => decide (lineSpec Q p.1 p.2 = zero)) pairs
  omega

end Assembly

/-! ## Witnesses -/

namespace GapTests
open UPoly Poly3

def g (n : Nat) : Goldilocks := Goldilocks.ofNat n

/-- The hypotheses of the assembly theorem hold together (with an empty challenge set, where
    the residual count is `0`). -/
theorem inhabited_assembly :
    ∃ (D S : List Goldilocks) (d A m Wx Dy rest : Nat), NonExcludedBound D S d A m Wx Dy rest ∧
      D.Nodup ∧ S.Nodup ∧ D.length * triCount 1 m Dy m < triCount d Wx Dy (Dy + 1) ∧
      Wx + Dy ≤ m * A :=
  ⟨[g 0, g 1], [], 1, 3, 1, 2, 1, 0, (fun _ _ L _ h => by
      cases L with
      | nil => exact Nat.le_refl 0
      | cons p _ =>
        have hp : p ∈ ([] : List (Goldilocks × Goldilocks)) := (h p (.head _)).1
        cases hp),
    by decide, by decide, by decide, by decide⟩

/-- The residual term cannot be dropped: `Dy + rest = 0` is not a valid bound on
    `|D| = 3`, `|S| = 2`, `d = 1`, `A = 3`, where the diagonal challenges are exceptional. -/
theorem tooth_assembly_needs_rest :
    ∃ (D S : List Goldilocks) (d A : Nat), D.Nodup ∧ S.Nodup ∧ ¬ AffineMcaBound D S d A (0 + 0) :=
  ⟨IncidenceTests.dom, IncidenceTests.pool, 1, 3, by decide, by decide,
    IncidenceTests.field_independent_bound_fails_example⟩

#verify_constructive cwyz26_affineMcaBound_of_nonExcluded NonExcludedBound.mono
#verify_constructive inhabited_assembly tooth_assembly_needs_rest
#tooth_pair cwyz26_affineMcaBound_of_nonExcluded vs tooth_assembly_needs_rest
#verify_inhabited cwyz26_affineMcaBound_of_nonExcluded inhabited_assembly

end GapTests

end Qsag
end
