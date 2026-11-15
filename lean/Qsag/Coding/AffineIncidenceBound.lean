module
/-
# Qsag.Coding.AffineIncidenceBound — what can and cannot be counted per line

* `Poly3.roots_on_line_card_le`: on a non-excluded line `Y = α + βX`, an explainer `Q` has at
  most `deg_Z Q` roots `P` with `Q(X, α + βX, P(X)) = 0`. This is the univariate root count
  over the domain `F[X]`, and it bounds candidates *per challenge*.
* `Poly3.jet_hyps`, `Poly3.jet_cover`: the covering half of `[CWYZ26]` Claim 4.9. A simple
  root `P` of `R` on a line has the jet `(α + βT₀, β, P(T₀))` at the generic point of `F(T₀)`,
  it satisfies the hypotheses of Lemma 3.11 to every order, and its Taylor coefficients at
  `T₀` are the reconstruction coefficients `reconCoeff` over `s^(2d-1)`.
* `affineMcaBound_ge_card`: **every** mutual correlated agreement bound for the affine fold
  has `bad ≥ |S|` (when `-1 ∉ D`, `1 ≤ d`, `d + 2 ≤ A ≤ |D|`). The words are `f = 0`,
  `g(z) = 1/(z + 1)`: on the diagonal challenges `(β, β)` the fold `β(1 + z)/(z + 1)` is the
  constant `β`, which agrees everywhere, while `g` is far from every polynomial of degree
  below `d`. This is the `max{q, n²}`-term of `[CWYZ26]` Lemma 4.5 seen from below.
* `affineMcaBound_without_field_term_fails`: consequently a bound of the form
  `D² + 2·d·D`, with no term growing with the challenge set, is false for `|S|` large.

The count of challenges `(α, β)` that admit a root is the content of `[CWYZ26]` Lemmas 4.5
(persistent pairs, Johnson bound) and 4.7 (nonpersistent pairs, incidence geometry of the
image of the reconstruction map). Neither is proved here; `roots_on_line_card_le` does not
bound it, because it fixes the challenge.
-/

public import Qsag.Coding.SimpleRootStratification
public import Qsag.Coding.AffineProximityGaps
import all Qsag.Coding.PolyMv3
import all Qsag.Coding.SylvesterResultant
import all Qsag.Coding.DynamicGcdSplit
import all Qsag.Coding.HenselNumerators
import all Qsag.Coding.UniversalHenselLift
import all Qsag.Coding.SimpleRootStratification
import all Qsag.Coding.AffineProximityGaps
import all Qsag.Math.Goldilocks

public section
namespace Qsag

set_option autoImplicit false

open CommRingOps RoundPoly

/-! ## List lemmas & Mutual Correlated Agreement Bound -/

theorem list_getD_eq_get {α : Type} :
    ∀ (xs : List α) (d : α) (idx : Fin xs.length), xs.getD idx.1 d = xs.get idx
  | [], _, idx => absurd idx.2 (Nat.not_lt_zero _)
  | _ :: _, _, ⟨0, _⟩ => rfl
  | _ :: xs, d, ⟨i + 1, hi⟩ => list_getD_eq_get xs d ⟨i, Nat.lt_of_succ_lt_succ hi⟩

theorem list_get_mem {α : Type} : ∀ (xs : List α) (k : Fin xs.length), xs.get k ∈ xs
  | _ :: _, ⟨0, _⟩ => .head _
  | _ :: xs, ⟨k + 1, hk⟩ => .tail _ (list_get_mem xs ⟨k, Nat.lt_of_succ_lt_succ hk⟩)

theorem nodup_get_inj {α : Type} :
    ∀ {S : List α} (_ : S.Nodup) {i j : Fin S.length}, S.get i = S.get j → i = j
  | [], _, ⟨_, hi⟩, _, _ => absurd hi (Nat.not_lt_zero _)
  | _ :: _, _, ⟨0, _⟩, ⟨0, _⟩, _ => rfl
  | _ :: xs, hNodup, ⟨0, _⟩, ⟨j + 1, hj⟩, hEq =>
    absurd hEq ((List.pairwise_cons.mp hNodup).1 _
      (list_get_mem xs ⟨j, Nat.lt_of_succ_lt_succ hj⟩))
  | _ :: xs, hNodup, ⟨i + 1, hi⟩, ⟨0, _⟩, hEq =>
    absurd hEq.symm ((List.pairwise_cons.mp hNodup).1 _
      (list_get_mem xs ⟨i, Nat.lt_of_succ_lt_succ hi⟩))
  | _ :: xs, hNodup, ⟨i + 1, hi⟩, ⟨j + 1, hj⟩, hEq => by
    have hSub := nodup_get_inj (List.pairwise_cons.mp hNodup).2
      (i := ⟨i, Nat.lt_of_succ_lt_succ hi⟩) (j := ⟨j, Nat.lt_of_succ_lt_succ hj⟩) hEq
    exact Fin.ext (by simpa using congrArg Fin.val hSub)

theorem not_not_forall_mem {α : Type} (Q : α → Prop) :
    ∀ l : List α, (∀ a ∈ l, ¬¬ Q a) → ¬¬ (∀ a ∈ l, Q a)
  | [], _ => fun h => h (fun _ hm => nomatch hm)
  | a :: l, h => fun hn =>
    h a (.head l) (fun hQa =>
      not_not_forall_mem Q l (fun a' ha' => h a' (.tail a ha')) (fun hRest =>
        hn (fun a' ha' => by
          rcases List.mem_cons.mp ha' with hEq | h1
          · rw [hEq]; exact hQa
          · exact hRest a' h1)))

theorem list_finite_choice {α β : Type} [DecidableEq α] (Q : α → β → Prop) (dflt : β) :
    ∀ l : List α, (∀ a ∈ l, ∃ b, Q a b) → ∃ f : α → β, ∀ a ∈ l, Q a (f a)
  | [], _ => ⟨fun _ => dflt, fun _ hm => nomatch hm⟩
  | a :: l, h => by
    rcases h a (.head l) with ⟨b, hb⟩
    rcases list_finite_choice Q dflt l (fun a' ha' => h a' (.tail a ha')) with ⟨f, hf⟩
    refine ⟨fun a' => if a' = a then b else f a', ?_⟩
    intro a' ha'
    if hEq : a' = a then
      rw [hEq]
      simp only [↓reduceIte]
      exact hb
    else
      simp only [hEq, ↓reduceIte]
      rcases List.mem_cons.mp ha' with h1 | h1
      · exact absurd h1 hEq
      · exact hf a' h1

private theorem length_filter_split_bool {α : Type} (p : α → Bool) :
    ∀ l : List α, l.length = (l.filter p).length + (l.filter (fun x => !p x)).length
  | [] => rfl
  | a :: l => by
    have ih := length_filter_split_bool p l
    cases hp : p a <;>
      simp only [List.filter_cons, hp, Bool.not_false, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte, List.length_cons] <;> omega

private theorem length_filter_filter_le_bool {α : Type} (p q : α → Bool) :
    ∀ l : List α, ((l.filter q).filter p).length ≤ (l.filter p).length
  | [] => Nat.le_refl _
  | a :: l => by
    have ih := length_filter_filter_le_bool p q l
    cases hq : q a <;> cases hp : p a <;>
      simp only [List.filter_cons, hq, hp, Bool.false_eq_true, ↓reduceIte, List.length_cons] <;>
      omega

section McaDefs
variable {F : Type} [LawfulField F] [DecidableEq F]

/-- **Correlated agreement**: ONE polynomial pair `(F_poly, G_poly)` (`deg F_poly ≤ d`,
    `deg G_poly ≤ d - 1`) simultaneously agrees with the received words `(f, g)` on at least `A`
    coordinates of the evaluation domain `D`. -/
@[expose] def HasCorrelatedAgreement (d A : Nat) (f g : F → F) (D : List F) : Prop :=
  ∃ F_poly G_poly : List F,
    F_poly.length ≤ d + 1 ∧
    G_poly.length ≤ d ∧
    A ≤ (D.filter (fun z =>
      decide (RoundPoly.evalCoeffs F_poly z = f z) &&
      decide (RoundPoly.evalCoeffs G_poly z = g z))).length

/-- An `s = 1` affine witness for a fold that is `A`-close forces correlated agreement `≥ A - 1`:
    the decomposition `P = F + (α + β X) G` loses at most one coordinate of the agreement set. -/
theorem hasCorrelatedAgreement_of_affineWitnessS1
    {d A : Nat} {f g : F → F} {D : List F} {α β : F} {P : List F}
    (hW : HasAffineWitnessS1 d f g D α β P)
    (hAgree : A ≤ (D.filter (fun z =>
      decide (RoundPoly.evalCoeffs P z =
        CommRingOps.add (f z)
          (CommRingOps.mul (CommRingOps.add α (CommRingOps.mul β z)) (g z))))).length) :
    HasCorrelatedAgreement d (A - 1) f g D := by
  rcases hW with ⟨F_poly, G_poly, hF, hG, _, hLoss⟩
  refine ⟨F_poly, G_poly, hF, hG, ?_⟩
  have hSplit := length_filter_split_bool
    (fun z => decide (RoundPoly.evalCoeffs F_poly z = f z) &&
      decide (RoundPoly.evalCoeffs G_poly z = g z))
    (D.filter (fun z =>
      decide (RoundPoly.evalCoeffs P z =
        CommRingOps.add (f z)
          (CommRingOps.mul (CommRingOps.add α (CommRingOps.mul β z)) (g z)))))
  have hLe := length_filter_filter_le_bool
    (fun z => decide (RoundPoly.evalCoeffs F_poly z = f z) &&
      decide (RoundPoly.evalCoeffs G_poly z = g z))
    (fun z =>
      decide (RoundPoly.evalCoeffs P z =
        CommRingOps.add (f z)
          (CommRingOps.mul (CommRingOps.add α (CommRingOps.mul β z)) (g z)))) D
  apply Nat.sub_le_of_le_add
  apply Nat.le_trans hAgree
  rw [hSplit]
  exact Nat.add_le_add hLe hLoss

/-- Verifier predicate of the affine-fold proximity IOP: challenge index `c` selects
    `(α, β) = (prodPool S)[c]`, and the prover's response `P` has degree `≤ d` and agrees with the
    fold word `f + (α + β X) g` on at least `A` points of `D`. -/
@[expose] def affineMcaAccepts (D S : List F) (d A : Nat) (x : (F → F) × (F → F)) (c : Nat)
    (P : List F) : Bool :=
  decide (c < (prodPool S).length) &&
  decide (P.length ≤ d + 1) &&
  decide (A ≤ (D.filter (fun z =>
    decide (RoundPoly.evalCoeffs P z =
      CommRingOps.add (x.1 z)
        (CommRingOps.mul
          (CommRingOps.add ((prodPool S).getD c (CommRingOps.zero, CommRingOps.zero)).1
            (CommRingOps.mul ((prodPool S).getD c (CommRingOps.zero, CommRingOps.zero)).2 z))
          (x.2 z))))).length)

/-- **Mutual correlated agreement bound** for the affine fold of words on `D` with challenges
    `(α, β) ∈ S × S`, degree bound `d` and agreement threshold `A`: for every pair of words
    WITHOUT correlated agreement `≥ A - 1`, at most `bad` challenges admit a degree-`≤ d`
    polynomial `A`-close to the fold word. -/
@[expose] def AffineMcaBound (D S : List F) (d A bad : Nat) : Prop :=
  ∀ x : (F → F) × (F → F), ¬ HasCorrelatedAgreement d (A - 1) x.1 x.2 D →
    ∀ L : List (Fin (prodPool S).length), L.Nodup →
      (∀ ch ∈ L, ¬¬ ∃ P : List F, affineMcaAccepts D S d A x ch.1 P = true) →
      L.length ≤ bad

/-- The bound is monotone in the number of exceptional challenges. -/
theorem AffineMcaBound.mono {D S : List F} {d A bad bad' : Nat}
    (h : AffineMcaBound D S d A bad) (hLe : bad ≤ bad') : AffineMcaBound D S d A bad' :=
  fun x hFar L hNd hEx => Nat.le_trans (h x hFar L hNd hEx) hLe

/-- **Welch–Berlekamp instance of the mutual correlated agreement bound**, proved from
    `welch_berlekamp_affine_proximity_gap` in the regime `2 |D| + d + 1 < 3 A`. -/
theorem affineMcaBound_welch_berlekamp (D S : List F) (d A : Nat)
    (hD : D.Nodup) (hS : S.Nodup) (hAD : A ≤ D.length) (hWB : 2 * D.length + d + 1 < 3 * A) :
    AffineMcaBound D S d A (Nat.max S.length (D.length * (D.length - 1) / 2)) := by
  intro x hFar L hNd hEx
  apply Decidable.byContradiction
  intro hGt
  refine not_not_forall_mem _ L hEx (fun hAll => hGt ?_)
  have hPairs : ∀ p ∈ L.map (fun ch => (prodPool S).get ch), ∃ P : List F,
      P.length ≤ d + 1 ∧
      A ≤ (D.filter (fun z =>
        decide (RoundPoly.evalCoeffs P z =
          CommRingOps.add (x.1 z)
            (CommRingOps.mul (CommRingOps.add p.1 (CommRingOps.mul p.2 z)) (x.2 z))))).length := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨ch, hch, rfl⟩
    rcases hAll ch hch with ⟨P, hP⟩
    unfold affineMcaAccepts at hP
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
    rw [list_getD_eq_get (prodPool S) _ ch] at hP
    exact ⟨P, hP.1.2, hP.2⟩
  rcases list_finite_choice _ ([] : List F) _ hPairs with ⟨P_of, hP_of⟩
  have hBound := welch_berlekamp_affine_proximity_gap x.1 x.2 D S d A
    (L.map (fun ch => (prodPool S).get ch)) P_of hD hS hAD hWB
    (List.Pairwise.map _
      (fun a b hab hEq => hab (nodup_get_inj (prodPool_nodup hS) hEq)) hNd)
    (fun p hp => by
      rcases List.mem_map.mp hp with ⟨ch, _, rfl⟩
      exact list_get_mem (prodPool S) ch)
    (fun p hp => (hP_of p hp).1)
    (fun p hp => (hP_of p hp).2)
    (fun p hp hW => hFar (hasCorrelatedAgreement_of_affineWitnessS1 hW (hP_of p hp).2))
  rw [List.length_map] at hBound
  exact hBound

end McaDefs

theorem exists_mem_ne_zero_of_coeffAt {R : Type} [CommRingOps R] : ∀ (l : List R) (k : Nat),
    coeffAt l k ≠ zero → ∃ c ∈ l, c ≠ zero
  | [], k, h => absurd (coeffAt_nil k) h
  | c :: _, 0, h => ⟨c, .head _, by rwa [coeffAt_cons_zero] at h⟩
  | _ :: cs, k + 1, h => by
    rw [coeffAt_cons_succ] at h
    obtain ⟨c', hc', hne⟩ := exists_mem_ne_zero_of_coeffAt cs k h
    exact ⟨c', .tail _ hc', hne⟩

theorem exists_fin_of_mem {α : Type} : ∀ (l : List α) (a : α), a ∈ l →
    ∃ i : Fin l.length, l.get i = a
  | _ :: _, _, .head _ => ⟨⟨0, Nat.succ_pos _⟩, rfl⟩
  | _ :: l, a, .tail _ h => by
    obtain ⟨i, hi⟩ := exists_fin_of_mem l a h
    exact ⟨⟨i.1 + 1, Nat.succ_lt_succ i.2⟩, hi⟩

theorem filter_eq_self_of_all {α : Type} (p : α → Bool) : ∀ l : List α,
    (∀ a ∈ l, p a = true) → l.filter p = l
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filter_cons_of_pos (h a (.head _)),
      filter_eq_self_of_all p l (fun b hb => h b (.tail _ hb))]

theorem nodup_filter {α : Type} (p : α → Bool) : ∀ l : List α, l.Nodup → (l.filter p).Nodup
  | [], _ => .nil
  | a :: l, h => by
    have hp := List.pairwise_cons.mp h
    have ih := nodup_filter p l hp.2
    cases hpa : p a with
    | true =>
      rw [List.filter_cons_of_pos hpa]
      exact List.pairwise_cons.mpr ⟨fun b hb => hp.1 b (List.mem_filter.mp hb).1, ih⟩
    | false =>
      rw [List.filter_cons_of_neg (by rw [hpa]; exact Bool.false_ne_true)]
      exact ih

/-! ## Roots on a fixed line -/

namespace Poly3
variable {F : Type} [LawfulField F] [DecidableEq F]
open UPoly

/-- **Candidates per challenge.** If `Q(X, α + βX, Z) ≠ 0`, at most `deg_Z Q` polynomials `P`
    satisfy `Q(X, α + βX, P(X)) = 0`. -/
theorem roots_on_line_card_le (Q : Poly3 F) (α β : F) (hnv : lineSpec Q α β ≠ zero)
    (Ps : List (UPoly F)) (hnd : Ps.Nodup) (hroot : ∀ P ∈ Ps, evalAffineLine Q α β P = zero) :
    Ps.length ≤ Q.degZ := by
  have h := gs_formal_root_bound (lineSpec Q α β).natDeg (lineSpec Q α β).coeffs Ps
    (by show _ ≤ (lineSpec Q α β).coeffs.length - 1 + 1; omega)
    (exists_mem_ne_zero_of_coeffAt _ _ (lead_ne_zero hnv)) hnd (fun P hP => by
      rw [← eval_eq]
      show eval₂ (RingHom.id _) P ((mapHom (evalHom (line α β))).toFun Q) = zero
      rw [eval₂_mapHom]
      exact hroot P hP)
  exact Nat.le_trans h (natDeg_mapHom_le _ Q)

end Poly3

/-! ## The jet of a root at the generic point (`[CWYZ26]` Claim 4.9, covering part) -/

namespace UPoly

theorem mapHom_shift2 {R S : Type} [LawfulCommRing R] [DecidableEq R] [LawfulCommRing S]
    [DecidableEq S] (φ : RingHom R S) (p : UPoly R) :
    (mapHom (mapHom φ)).toFun ((shift2 (R := R)).toFun p) =
      (shift2 (R := S)).toFun ((mapHom φ).toFun p) := by
  refine hom_ext ((mapHom (mapHom φ)).comp shift2) (shift2.comp (mapHom φ)) (fun c => ?_) ?_ p
  · show (mapHom (mapHom φ)).toFun (eval₂ (CHom.comp CHom) (add (C X) X) (C c)) =
      eval₂ (CHom.comp CHom) (add (C X) X) ((mapHom φ).toFun (C c))
    rw [eval₂_C, mapHom_C, eval₂_C]
    show (mapHom (mapHom φ)).toFun (C (C c)) = C (C (φ.toFun c))
    rw [mapHom_C, mapHom_C]
  · show (mapHom (mapHom φ)).toFun (eval₂ (CHom.comp CHom) (add (C X) X) X) =
      eval₂ (CHom.comp CHom) (add (C X) X) ((mapHom φ).toFun X)
    rw [eval₂_X, mapHom_X, eval₂_X, RingHom.map_add, mapHom_C, mapHom_X, mapHom_X]

/-- Hasse derivatives commute with base change of the coefficients. -/
theorem mapHom_hasse {R S : Type} [LawfulCommRing R] [DecidableEq R] [LawfulCommRing S]
    [DecidableEq S] (φ : RingHom R S) (k : Nat) (p : UPoly R) :
    (mapHom φ).toFun (hasse k p) = hasse k ((mapHom φ).toFun p) := by
  rw [hasse_eq_coeff, hasse_eq_coeff, ← mapHom_shift2, coeffAt_mapHom]

end UPoly

namespace Poly3
section Generic
variable {F : Type} [LawfulField F] [DecidableEq F]
open UPoly

/-- Scalars into `F(T₀)`. -/
def scalK : RingHom F (RatFunc F) := (Frac.of (D := UPoly F)).comp CHom

/-- The generic point `T₀ ∈ F(T₀)`. -/
def genPt : RatFunc F := (Frac.of (D := UPoly F)).toFun X

/-- Base change `F[X][Y][Z] → F(T₀)[X][Y][Z]`. -/
def baseK : RingHom (Poly3 F) (Poly3 (RatFunc F)) := mapHom (mapHom (mapHom scalK))

/-- The root series of `P` at the generic point: `P(T₀ + W) - P(T₀)`. -/
def genSeries (P : UPoly F) : UPoly (RatFunc F) :=
  sub ((taylorShift genPt).toFun ((mapHom scalK).toFun P)) (C ((Frac.of (D := UPoly F)).toFun P))

/-- Evaluating a polynomial at the generic point is the embedding `F[X] → F(T₀)`. -/
theorem eval_gen (c : UPoly F) :
    ((mapHom (scalK (F := F))).toFun c).eval genPt = (Frac.of (D := UPoly F)).toFun c := by
  show eval₂ (RingHom.id _) genPt ((mapHom scalK).toFun c) = _
  rw [eval₂_mapHom]
  have h := hom_eval₂ (Frac.of (D := UPoly F)) CHom X c
  have e : eval₂ (CHom (R := F)) X c = c := evalCoeffs_C_X c
  rw [e] at h
  exact (eval₂_congr _ _ (fun _ => rfl) _ c).trans h.symm

theorem eval₂_gen (y₀ : UPoly F) (q : UPoly (UPoly F)) :
    eval₂ (evalHom genPt) ((Frac.of (D := UPoly F)).toFun y₀) ((mapHom (mapHom scalK)).toFun q) =
      (Frac.of (D := UPoly F)).toFun (q.eval y₀) := by
  rw [eval₂_mapHom]
  show _ = (Frac.of (D := UPoly F)).toFun (eval₂ (RingHom.id _) y₀ q)
  rw [hom_eval₂]
  exact eval₂_congr _ _ (fun c => eval_gen c) _ q

theorem eval3_gen (R : Poly3 F) (y₀ P : UPoly F) :
    eval3 (baseK.toFun R) genPt ((Frac.of (D := UPoly F)).toFun y₀)
      ((Frac.of (D := UPoly F)).toFun P) =
      (Frac.of (D := UPoly F)).toFun (eval₂ (evalHom y₀) P R) := by
  show eval₂ (eval₂Hom (evalHom genPt) ((Frac.of (D := UPoly F)).toFun y₀))
    ((Frac.of (D := UPoly F)).toFun P) ((mapHom (mapHom (mapHom scalK))).toFun R) = _
  rw [eval₂_mapHom, hom_eval₂]
  exact eval₂_congr _ _ (fun q => eval₂_gen y₀ q) _ R

theorem jet_gen (α β : F) (q : UPoly (UPoly F)) :
    (jetHom genPt ((Frac.of (D := UPoly F)).toFun (line α β)) (scalK.toFun β)).toFun
      ((mapHom (mapHom scalK)).toFun q) =
      (taylorShift genPt).toFun ((mapHom scalK).toFun (q.eval (line α β))) := by
  have e1 : line α β = add (C α) (mul X (C β)) := ofList_cons α [β]
  have hL : (taylorShift genPt).toFun ((mapHom (scalK (F := F))).toFun (line α β)) =
      add (C (scalK.toFun α)) (mul (add (C genPt) X) (C (scalK.toFun β))) := by
    rw [e1, RingHom.map_add, RingHom.map_mul, mapHom_C, mapHom_C, mapHom_X, RingHom.map_add,
      RingHom.map_mul, taylorShift_C, taylorShift_C, taylorShift_X]
  have hR : (C ((Frac.of (D := UPoly F)).toFun (line α β)) : UPoly (RatFunc F)) =
      add (C (scalK.toFun α)) (mul (C genPt) (C (scalK.toFun β))) := by
    rw [e1, RingHom.map_add, RingHom.map_mul]
    exact ((CHom (R := RatFunc F)).map_add _ _).trans
      (congrArg (add _) ((CHom (R := RatFunc F)).map_mul _ _))
  have hline : (taylorShift genPt).toFun ((mapHom (scalK (F := F))).toFun (line α β)) =
      add (C ((Frac.of (D := UPoly F)).toFun (line α β))) (mul (C (scalK.toFun β)) X) := by
    rw [hL, hR]; constructive_ring
  show eval₂ (taylorShift genPt) _ ((mapHom (mapHom scalK)).toFun q) =
    (taylorShift genPt).toFun ((mapHom scalK).toFun (eval₂ (RingHom.id _) (line α β) q))
  rw [eval₂_mapHom, hom_eval₂, hom_eval₂, hline]
  exact eval₂_congr _ _ (fun _ => rfl) _ q

/-- The hypotheses of `henselNum_spec` hold for every simple root on a line, at the generic
    point of `F(T₀)`: the jet is `(y, v, z) = (α + βT₀, β, P(T₀))` and the series is
    `P(T₀ + W) - P(T₀)`, to every order. -/
theorem jet_hyps (R : Poly3 F) (α β : F) (P : UPoly F) (hroot : evalAffineLine R α β P = zero)
    (hsep : evalAffineLine (hasseZ 1 R) α β P ≠ zero) :
    (genSeries P).eval zero = zero ∧
    eval3 (baseK.toFun R) genPt ((Frac.of (D := UPoly F)).toFun (line α β))
      ((Frac.of (D := UPoly F)).toFun P) = zero ∧
    eval3 (hasseZ 1 (baseK.toFun R)) genPt ((Frac.of (D := UPoly F)).toFun (line α β))
      ((Frac.of (D := UPoly F)).toFun P) =
        (Frac.of (D := UPoly F)).toFun (evalAffineLine (hasseZ 1 R) α β P) ∧
    (Frac.of (D := UPoly F)).toFun (evalAffineLine (hasseZ 1 R) α β P) ≠ zero ∧
    eval₂ (jetHom genPt ((Frac.of (D := UPoly F)).toFun (line α β)) (scalK.toFun β))
      (add (C ((Frac.of (D := UPoly F)).toFun P)) (genSeries P)) (baseK.toFun R) = zero := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show (evalHom zero).toFun (sub ((taylorShift genPt).toFun ((mapHom scalK).toFun P))
      (C ((Frac.of (D := UPoly F)).toFun P))) = zero
    rw [RingHom.map_sub, evalHom_apply, evalHom_apply, eval_taylorShift, LawfulCommRing.add_zero,
      eval_gen, eval_C, LawfulCommRing.sub_self]
  · rw [eval3_gen]
    show (Frac.of (D := UPoly F)).toFun (evalAffineLine R α β P) = zero
    rw [hroot, RingHom.map_zero]
  · have e : hasseZ 1 (baseK.toFun R) = baseK.toFun (hasseZ 1 R) :=
      (mapHom_hasse (mapHom (mapHom (scalK (F := F)))) 1 R).symm
    rw [e, eval3_gen]; rfl
  · exact fun e => hsep (Frac.of_injective (e.trans (Frac.of (D := UPoly F)).map_zero.symm))
  · have hadd : add (C ((Frac.of (D := UPoly F)).toFun P)) (genSeries P) =
        (taylorShift genPt).toFun ((mapHom scalK).toFun P) := by
      show add _ (sub _ _) = _
      constructive_ring
    rw [hadd]
    show eval₂ _ _ ((mapHom (mapHom (mapHom scalK))).toFun R) = zero
    rw [eval₂_mapHom]
    have h := hom_eval₂ ((taylorShift genPt).comp (mapHom (scalK (F := F))))
      (evalHom (line α β)) P R
    have h0 : eval₂ (evalHom (line α β)) P R = zero := hroot
    rw [h0, RingHom.map_zero] at h
    exact (eval₂_congr _ _ (fun q => jet_gen α β q) _ R).trans h.symm

/-- **`[CWYZ26]` Claim 4.9, covering part.** Let `P` be a simple root of `R` on the line
    `Y = α + βX`. At the jet `(y, v, z) = (α + βT₀, β, P(T₀)) ∈ F(T₀)³`, the cleared
    reconstruction coefficients evaluate to `s^(2d-1)` times the Taylor coefficients of `P` at
    `T₀`, for `j ≤ d`, where `s = ∂_Z R(T₀, y, z) ≠ 0`. So the triple `(α, β, P)` is the image
    of its jet under a map with numerators of degree at most `2·d·h` (`deg_reconCoeff_le`) on
    the surface `R(T₀, Y, Z) = 0`. -/
theorem jet_cover (R : Poly3 F) (α β : F) (P : UPoly F) (d : Nat) (hd : 1 ≤ d)
    (hroot : evalAffineLine R α β P = zero)
    (hsep : evalAffineLine (hasseZ 1 R) α β P ≠ zero) (j : Nat) (hj : j ≤ d) :
    (ptHom ((Frac.of (D := UPoly F)).toFun (line α β)) (scalK.toFun β)
      ((Frac.of (D := UPoly F)).toFun P)).toFun (reconCoeff (baseK.toFun R) genPt d j) =
      mul (CRing.npow ((Frac.of (D := UPoly F)).toFun (evalAffineLine (hasseZ 1 R) α β P))
        (2 * d - 1))
        (coeffAt ((taylorShift genPt).toFun ((mapHom scalK).toFun P)).coeffs j) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := jet_hyps R α β P hroot hsep
  have key := reconCoeff_spec (baseK.toFun R) genPt _ (scalK.toFun β) _ (genSeries P) d hd h1 h2
    (by rw [h3]; exact h4) (fun k _ => by rw [h5, coeffs_zero, coeffAt_nil]) j hj
  have hadd : add (C ((Frac.of (D := UPoly F)).toFun P)) (genSeries P) =
      (taylorShift genPt).toFun ((mapHom scalK).toFun P) := by
    show add _ (sub _ _) = _
    constructive_ring
  rw [h3, hadd] at key
  exact key

end Generic
end Poly3

/-! ## Every bound is at least the size of the challenge set -/

section LowerBound
variable {F : Type} [LawfulField F] [DecidableEq F]
open UPoly

local instance : NoZeroDivisors F := LawfulField.toNoZeroDivisors F

/-- The received words `f = 0`, `g(z) = 1/(z + 1)`. -/
def poleWords : (F → F) × (F → F) := (fun _ => zero, fun z => LawfulField.inv (add z one))

theorem eval_ofList (l : List F) (z : F) : (ofList l).eval z = evalCoeffs l z := by
  rw [eval_eq]
  show evalCoeffs (trimPoly l) z = _
  rw [evalCoeffs_trimPoly]

theorem natDeg_ofList_le (l : List F) : (ofList l).natDeg ≤ l.length - 1 := by
  have := trimPoly_length_le l
  show (trimPoly l).length - 1 ≤ l.length - 1
  omega

omit [DecidableEq F] in
theorem add_one_ne_zero {D : List F} (hneg : neg one ∉ D) {z : F} (hz : z ∈ D) :
    add z one ≠ zero := fun e => hneg (by
  have h1 : z = add (add z one) (neg one) := by constructive_ring
  rw [e, LawfulCommRing.zero_add] at h1
  rw [← h1]; exact hz)

/-- `g(z) = 1/(z + 1)` agrees with a polynomial of degree below `d` on at most `d` points
    of a domain avoiding `-1`, so the pole words have no correlated agreement `≥ A - 1`. -/
theorem poleWords_far (D : List F) (d A : Nat) (hD : D.Nodup) (hneg : neg one ∉ D)
    (hd : 1 ≤ d) (hA : d + 2 ≤ A) :
    ¬ HasCorrelatedAgreement d (A - 1) (poleWords (F := F)).1 poleWords.2 D := by
  rintro ⟨Fp, Gp, _, hG, hlen⟩
  generalize hH : sub (mul (ofList [(one : F), one]) (ofList Gp)) one = H
  have hHeval : ∀ z, H.eval z = sub (mul (add one z) (evalCoeffs Gp z)) one := by
    intro z
    rw [← hH]
    show (evalHom z).toFun (sub (mul (ofList [(one : F), one]) (ofList Gp)) one) = _
    rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_one, evalHom_apply, evalHom_apply,
      eval_ofList, eval_ofList]
    show sub (mul (add one (mul z (add one (mul z zero)))) (evalCoeffs Gp z)) one = _
    constructive_ring
  have hHne : H ≠ zero := fun e => by
    have h1 := hHeval (neg one)
    rw [e] at h1
    have h2 : (zero : UPoly F).eval (neg one) = zero := eval₂_zero _ _
    rw [h2, LawfulCommRing.add_right_neg, LawfulCommRing.zero_mul] at h1
    have h3 : (one : F) = sub zero (sub zero one) := by constructive_ring
    rw [← h1, LawfulCommRing.sub_self] at h3
    exact LawfulField.one_ne_zero h3
  have hdeg : H.natDeg ≤ d := by
    have h1 := natDeg_mul_le (ofList [(one : F), one]) (ofList Gp)
    have h2 := natDeg_ofList_le [(one : F), one]
    have h3 := natDeg_ofList_le Gp
    have h4 := (degFn_natDeg (R := F)).add_le (mul (ofList [(one : F), one]) (ofList Gp)) (neg one)
    have h5 := (degFn_natDeg (R := F)).neg_le one
    have h6 := natDeg_one (R := F)
    have h7 : H = add (mul (ofList [(one : F), one]) (ofList Gp)) (neg one) := by
      rw [← hH]; exact LawfulCommRing.sub_eq_add_neg _ _
    have h2' : (ofList [(one : F), one]).natDeg ≤ 1 := h2
    rw [h7]
    omega
  have hroot : ∀ z ∈ D.filter (fun z => decide (evalCoeffs Fp z = (poleWords (F := F)).1 z) &&
      decide (evalCoeffs Gp z = (poleWords (F := F)).2 z)), evalCoeffs H.coeffs z = zero := by
    intro z hz
    obtain ⟨hzD, hp⟩ := List.mem_filter.mp hz
    have hg : evalCoeffs Gp z = LawfulField.inv (add z one) :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp hp).2
    rw [← eval_eq, hHeval, hg, LawfulCommRing.add_comm one z,
      LawfulField.mul_inv_cancel (add_one_ne_zero hneg hzD), LawfulCommRing.sub_self]
  have hcount := gs_formal_root_bound H.natDeg H.coeffs _
    (by show _ ≤ H.coeffs.length - 1 + 1; omega)
    (exists_mem_ne_zero_of_coeffAt _ _ (lead_ne_zero hHne)) (nodup_filter _ D hD) hroot
  omega

/-- On a diagonal challenge `(β, β)` the constant `β` is accepted with full agreement. -/
theorem poleWords_accept (D S : List F) (d A : Nat) (hneg : neg one ∉ D) (hAD : A ≤ D.length)
    (ch : Fin (prodPool S).length) (β : F) (hch : (prodPool S).get ch = (β, β)) :
    affineMcaAccepts D S d A poleWords ch.1 [β] = true := by
  unfold affineMcaAccepts
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [list_getD_eq_get (prodPool S) _ ch, hch]
  refine ⟨⟨ch.2, Nat.succ_le_succ (Nat.zero_le d)⟩, ?_⟩
  rw [filter_eq_self_of_all _ D (fun z hz => decide_eq_true (by
    show add β (mul z zero) = add zero (mul (add β (mul β z)) (LawfulField.inv (add z one)))
    have e : mul (add β (mul β z)) (LawfulField.inv (add z one)) =
        mul β (mul (add z one) (LawfulField.inv (add z one))) := by constructive_ring
    rw [e, LawfulField.mul_inv_cancel (add_one_ne_zero hneg hz)]
    constructive_ring))]
  exact hAD

/-- **Necessity of the field-size term.** Any mutual correlated agreement bound for the
    affine fold on a domain avoiding `-1` has at least `|S|` exceptional challenges: the
    diagonal `(β, β)`, `β ∈ S`. -/
theorem affineMcaBound_ge_card (D S : List F) (d A bad : Nat) (h : AffineMcaBound D S d A bad)
    (hD : D.Nodup) (hS : S.Nodup) (hneg : neg one ∉ D) (hd : 1 ≤ d) (hA : d + 2 ≤ A)
    (hAD : A ≤ D.length) : S.length ≤ bad := by
  if h0 : (prodPool S).length = 0 then
    rw [prodPool_length] at h0
    have : S.length = 0 := by
      rcases Nat.eq_zero_or_pos S.length with h1 | h1
      · exact h1
      · exact absurd h0 (Nat.ne_of_gt (Nat.mul_pos h1 h1))
    rw [this]; exact Nat.zero_le _
  else
    have hidx : ∀ β ∈ S, ∃ ch : Fin (prodPool S).length, (prodPool S).get ch = (β, β) :=
      fun β hβ => exists_fin_of_mem _ _ (mem_prodPool_iff.mpr ⟨hβ, hβ⟩)
    obtain ⟨f, hf⟩ := list_finite_choice (fun β ch => (prodPool S).get ch = (β, β))
      ⟨0, Nat.pos_of_ne_zero h0⟩ S hidx
    have hNd : (S.map f).Nodup := List.pairwise_map.mpr (List.Pairwise.imp_of_mem
      (fun {a b} ha hb hne e => hne (by
        have h1 := (hf a ha).symm.trans ((congrArg (prodPool S).get e).trans (hf b hb))
        exact (Prod.mk.inj h1).1)) hS)
    have key := h poleWords (poleWords_far D d A hD hneg hd hA) (S.map f) hNd (fun ch hch hno => by
      obtain ⟨β, hβ, rfl⟩ := List.mem_map.mp hch
      exact hno ⟨[β], poleWords_accept D S d A hneg hAD (f β) β (hf β hβ)⟩)
    rwa [List.length_map] at key

/-- A bound `Dg² + 2·d·Dg` with no term in the size of the challenge set is not a mutual
    correlated agreement bound once `|S|` exceeds it. -/
theorem affineMcaBound_without_field_term_fails (D S : List F) (d A Dg : Nat) (hD : D.Nodup)
    (hS : S.Nodup) (hneg : neg one ∉ D) (hd : 1 ≤ d) (hA : d + 2 ≤ A) (hAD : A ≤ D.length)
    (hbig : Dg ^ 2 + 2 * d * Dg < S.length) : ¬ AffineMcaBound D S d A (Dg ^ 2 + 2 * d * Dg) :=
  fun h => Nat.not_le_of_lt hbig (affineMcaBound_ge_card D S d A _ h hD hS hneg hd hA hAD)

end LowerBound

/-! ## Witnesses -/

namespace IncidenceTests
open UPoly Poly3

def g (n : Nat) : Goldilocks := Goldilocks.ofNat n

def dom : List Goldilocks := [g 0, g 1, g 2]
def pool : List Goldilocks := [g 0, g 1]

/-- The hypotheses of `affineMcaBound_ge_card` hold together: in the unique-decoding regime
    `2|D| + d + 1 < 3A` the Welch–Berlekamp bound `max(|S|, |D|(|D|-1)/2) = 3` is a valid
    bound, and it is indeed at least `|S| = 2`. -/
theorem inhabited_affineMcaBound_ge_card :
    ∃ (D S : List Goldilocks) (d A bad : Nat), AffineMcaBound D S d A bad ∧ D.Nodup ∧
      S.Nodup ∧ neg one ∉ D ∧ 1 ≤ d ∧ d + 2 ≤ A ∧ A ≤ D.length :=
  ⟨dom, pool, 1, 3, _,
    affineMcaBound_welch_berlekamp dom pool 1 3 (by decide) (by decide) (by decide) (by decide),
    by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The threshold hypothesis `d + 2 ≤ A` is needed: at `A = 1` every pair of words has
    correlated agreement `≥ 0`, so `bad = 0` is a valid bound although `|S| = 2`. -/
theorem tooth_ge_card_needs_threshold :
    ∃ (D S : List Goldilocks) (d A bad : Nat), D.Nodup ∧ S.Nodup ∧ neg one ∉ D ∧ 1 ≤ d ∧
      A ≤ D.length ∧ AffineMcaBound D S d A bad ∧ ¬ S.length ≤ bad :=
  ⟨dom, pool, 1, 1, 0, by decide, by decide, by decide, by decide, by decide,
    fun _ hFar => absurd ⟨[], [], Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩ hFar, by decide⟩

/-- A concrete failure of a field-independent bound: with `Dg = 0` the bound `0` is refuted
    on `|D| = 3`, `|S| = 2`, `d = 1`, `A = 3`. -/
theorem field_independent_bound_fails_example :
    ¬ AffineMcaBound dom pool 1 3 (0 ^ 2 + 2 * 1 * 0) :=
  affineMcaBound_without_field_term_fails dom pool 1 3 0 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

#verify_constructive affineMcaBound_ge_card affineMcaBound_without_field_term_fails
#verify_constructive Poly3.roots_on_line_card_le poleWords_far poleWords_accept
#verify_constructive Poly3.jet_cover Poly3.jet_hyps UPoly.mapHom_hasse
#verify_constructive tooth_ge_card_needs_threshold field_independent_bound_fails_example
#tooth_pair affineMcaBound_ge_card vs tooth_ge_card_needs_threshold
#verify_inhabited affineMcaBound_ge_card inhabited_affineMcaBound_ge_card

end IncidenceTests

end Qsag
end
