module
public import Qsag.Coding.AffineProximity
public import Qsag.Math.QuarticExt4
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
@[expose] def foldAgree (x : (F → F) × (F → F)) (α β : F) (P : UPoly F) (z : F) : Bool :=
  decide (P.eval z = add (x.1 z) (mul (add α (mul β z)) (x.2 z)))

/-- **The residual count `|P| + |N| ≤ rest` of `[CWYZ26]` Lemma 4.1**, relative to the
    explainer of Lemma 4.2: among challenges on which the explainer does not vanish
    identically, at most `rest` admit a root of degree at most `d` with agreement `≥ A`. -/
@[expose] def NonExcludedBound (D S : List F) (d A m Wx Dy rest : Nat) : Prop :=
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

/-- **The residual count, proved.** For `d + 1 ≤ B < A` with `|D|·(d + 1) < B²` and
    `1, …, Dy` invertible, the explainer of Lemma 4.2 has at most
    `ℓ·max{|S|, n(n-1)/2} + |S|·z·Dy·(n·z·2dDy/(A-B) + 1)` non-excluded exceptional
    challenges. -/
theorem nonExcludedBound_sliced (D S : List F) (d A B m Wx Dy : Nat)
    (hD : D.Nodup) (hS : S.Nodup)
    (hcount : D.length * triCount 1 m Dy m < triCount d Wx Dy (Dy + 1))
    (hd : 1 ≤ d) (hDy : 1 ≤ Dy) (hB : d + 1 ≤ B) (hDen : D.length * (d + 1) < B * B)
    (hAB : B < A) (hchar : ∀ k, 1 ≤ k → k ≤ Dy → (CRing.natCast k : F) ≠ zero) :
    NonExcludedBound D S d A m Wx Dy
      (((D.length * (B - (d + 1))) / (B * B - D.length * (d + 1))) *
          Nat.max S.length (D.length * (D.length - 1) / 2) +
        S.length * ((Nat.min Dy ((Wx + Dy - 1) / d)) *
          (Dy * (D.length * ((Nat.min Dy ((Wx + Dy - 1) / d)) * (2 * d * Dy)) / (A - B) + 1)))) := by
  intro x hFar L hNd hL
  obtain ⟨_, hQdeg, hQw, _⟩ := explainer_spec x.1 x.2 D m d Wx Dy hcount
  have hZ : (explainer x.1 x.2 D m d Wx Dy).degZ ≤ Dy :=
    Nat.le_trans (degZ_le_degYZ _) hQdeg
  have h := nonExcluded_pairs_card_le x D S hD hS d A B Dy hd hDy hAB hB hDen
    (explainer x.1 x.2 D m d Wx Dy) hQdeg (Wx + Dy - 1) hQw
    (fun k h1 h2 => hchar k h1 (Nat.le_trans h2 hZ))
    L hNd (fun p hp => by
      obtain ⟨h1, h2, P, hPd, hPa, hroot⟩ := hL p hp
      refine ⟨h1, h2, P, hPd, hPa, hroot, ?_⟩
      rintro ⟨Fp, Gp, hF, hG, hAg, _⟩
      exact hFar ⟨Fp, Gp, hF, hG, hAg⟩)
  exact h

/-- **Mutual correlated agreement beyond unique decoding, without a residual hypothesis.**
    Under the interpolation count (4.5), `Wx + Dy ≤ m·A`, `d + 1 ≤ B < A`,
    `|D|·(d + 1) < B²` and `1, …, Dy` invertible, at most
    `Dy + ℓ·max{|S|, n(n-1)/2} + |S|·z·Dy·(n·z·2dDy/(A-B) + 1)` challenges are
    exceptional. -/
theorem cwyz26_affineMcaBound_sliced (D S : List F) (d A B m Wx Dy : Nat)
    (hD : D.Nodup) (hS : S.Nodup)
    (hcount : D.length * triCount 1 m Dy m < triCount d Wx Dy (Dy + 1))
    (hWA : Wx + Dy ≤ m * A)
    (hd : 1 ≤ d) (hDy : 1 ≤ Dy) (hB : d + 1 ≤ B) (hDen : D.length * (d + 1) < B * B)
    (hAB : B < A) (hchar : ∀ k, 1 ≤ k → k ≤ Dy → (CRing.natCast k : F) ≠ zero) :
    AffineMcaBound D S d A
      (Dy + (((D.length * (B - (d + 1))) / (B * B - D.length * (d + 1))) *
          Nat.max S.length (D.length * (D.length - 1) / 2) +
        S.length * ((Nat.min Dy ((Wx + Dy - 1) / d)) *
          (Dy * (D.length * ((Nat.min Dy ((Wx + Dy - 1) / d)) * (2 * d * Dy)) / (A - B) + 1))))) :=
  cwyz26_affineMcaBound_of_nonExcluded D S d A m Wx Dy _
    (nonExcludedBound_sliced D S d A B m Wx Dy hD hS hcount hd hDy hB hDen hAB hchar)
    hD hS hcount hWA

end Assembly


end Qsag

namespace Qsag
open CommRingOps RoundPoly UPoly Poly3
/-- Explicit correlated-agreement pair witness `(F_poly, G_poly)` for `(f, g)` at `(d, B)` on `D`. -/
@[expose] def HasCorrelatedPairAt {F : Type} [CommRingOps F] [DecidableEq F]
    (d B : Nat) (f g : F → F) (D : List F) (F_poly G_poly : List F) : Prop :=
  F_poly.length ≤ d + 1 ∧
  G_poly.length ≤ d ∧
  B ≤ (D.filter (fun z =>
    decide (RoundPoly.evalCoeffs F_poly z = f z) &&
    decide (RoundPoly.evalCoeffs G_poly z = g z))).length

/-- `P` decomposes as `F_poly + (α + β X) G_poly` (up to trailing zeros) for a `(d, B)`
    correlated-agreement pair `(F_poly, G_poly)` of `(f, g)` on `D`. -/
@[expose] def DecomposesViaCorrelatedPair {F : Type} [CommRingOps F] [DecidableEq F]
    (d B : Nat) (f g : F → F) (D : List F) (α β : F) (P : List F) : Prop :=
  ∃ F_poly G_poly : List F,
    HasCorrelatedPairAt d B f g D F_poly G_poly ∧
    trimPoly P = trimPoly
      (polyAddVar F_poly
        (polyAddVar (polyScaleVar α G_poly) (polyScaleVar β (shiftPoly G_poly))))

/-- **`[CWYZ26]` Lemma 4.1 + 4.2 Non-Excluded Decomposition Hypothesis (`NonExcludedDecompBound`)**:
    At arbitrary Johnson list-decoding radius (`D_list ≥ 1`), bounds the number of non-excluded
    challenges `(α, β) ∈ prodPool S` whose explainer `Q(X, α + β X, Z)` admits a degree-`≤ d`,
    agreement-`≥ A` root `P` that does NOT arise from a `(d, A - 1)` correlated-agreement branch. -/
@[expose] def NonExcludedDecompBound {F : Type} [LawfulField F] [DecidableEq F]
    (D S : List F) (d A m Wx Dy rest : Nat) : Prop :=
  ∀ x : (F → F) × (F → F),
    ∀ L : List (F × F), L.Nodup →
      (∀ p ∈ L, p ∈ prodPool S ∧
        Poly3.lineSpec (Poly3.explainer x.1 x.2 D m d Wx Dy) p.1 p.2 ≠ CommRingOps.zero ∧
        ∃ P : List F, P.length ≤ d + 1 ∧
          A ≤ (D.filter (foldAgree x p.1 p.2 (UPoly.ofList P))).length ∧
          Poly3.evalAffineLine (Poly3.explainer x.1 x.2 D m d Wx Dy) p.1 p.2 (UPoly.ofList P) =
            CommRingOps.zero ∧
          ¬ DecomposesViaCorrelatedPair d (A - 1) x.1 x.2 D p.1 p.2 P) →
      L.length ≤ rest

/-- The selected-polynomial incidence predicate is exactly the transcript decomposition
    predicate. Ordinary existential proximity alone would not establish this equivalence. -/
theorem hasPolynomialExplanation_iff_decomposes {F : Type} [LawfulField F] [DecidableEq F]
    (x : (F → F) × (F → F)) (D : List F) (d B : Nat) (α β : F) (P : List F) :
    HasPolynomialExplanation x D d B α β (UPoly.ofList P) ↔
      DecomposesViaCorrelatedPair d B x.1 x.2 D α β P := by
  constructor
  · rintro ⟨Fp, Gp, hF, hG, hAg, hEq⟩
    refine ⟨Fp, Gp, ⟨hF, hG, hAg⟩, ?_⟩
    have he := (ofList_affineClaimCombine α β Fp Gp).trans hEq
    simpa only [UPoly.coeffs_ofList] using (congrArg UPoly.coeffs he).symm
  · rintro ⟨Fp, Gp, ⟨hF, hG, hAg⟩, hEq⟩
    refine ⟨Fp, Gp, hF, hG, hAg, ?_⟩
    rw [← ofList_affineClaimCombine]
    exact UPoly.ext (by simpa only [UPoly.coeffs_ofList] using hEq.symm)

/-- **`NonExcludedDecompBound`, proved.** For `d + 1 ≤ B < A`, `|D|·(d + 1) < B²`, the
    interpolation count (4.5) and `1, …, Dy` invertible, at most
    `ℓ·max{|S|, n(n-1)/2} + |S|·z·Dy·(n·z·2dDy/(A-B) + 1)` non-excluded challenges carry an
    accepted root of the explainer that does not decompose through a correlated pair. -/
theorem nonExcludedDecompBound_sliced {F : Type} [LawfulField F] [DecidableEq F]
    (D S : List F) (d A B m Wx Dy : Nat) (hD : D.Nodup) (hS : S.Nodup)
    (hcount : D.length * triCount 1 m Dy m < triCount d Wx Dy (Dy + 1))
    (hd : 1 ≤ d) (hDy : 1 ≤ Dy) (hB : d + 1 ≤ B) (hDen : D.length * (d + 1) < B * B)
    (hAB : B < A) (hchar : ∀ k, 1 ≤ k → k ≤ Dy → (CRing.natCast k : F) ≠ zero) :
    NonExcludedDecompBound D S d A m Wx Dy
      (((D.length * (B - (d + 1))) / (B * B - D.length * (d + 1))) *
          Nat.max S.length (D.length * (D.length - 1) / 2) +
        S.length * ((Nat.min Dy ((Wx + Dy - 1) / d)) *
          (Dy * (D.length * ((Nat.min Dy ((Wx + Dy - 1) / d)) * (2 * d * Dy)) / (A - B) + 1)))) := by
  intro x L hNd hL
  obtain ⟨_, hQdeg, hQw, _⟩ := explainer_spec x.1 x.2 D m d Wx Dy hcount
  have hZ : (explainer x.1 x.2 D m d Wx Dy).degZ ≤ Dy :=
    Nat.le_trans (degZ_le_degYZ _) hQdeg
  have h := nonExcluded_pairs_card_le x D S hD hS d A B Dy hd hDy hAB hB hDen
    (explainer x.1 x.2 D m d Wx Dy) hQdeg (Wx + Dy - 1) hQw
    (fun k h1 h2 => hchar k h1 (Nat.le_trans h2 hZ))
    L hNd (fun p hp => by
      obtain ⟨h1, h2, P, hPlen, hPa, hroot, hNoDec⟩ := hL p hp
      have hdeg : (ofList P).natDeg ≤ d := by
        have h3 := natDeg_ofList_le P
        omega
      exact ⟨h1, h2, ofList P, hdeg, hPa, hroot, fun hE =>
        hNoDec ((hasPolynomialExplanation_iff_decomposes x D d (A - 1) p.1 p.2 P).mp hE)⟩)
  exact h


end Qsag

public section
namespace Qsag
open RoundPoly
set_option exponentiation.threshold 2048
/-! ## §5. Finite `Theorem 4.8 + Theorem 5.1` Witness Verifier Bound to the Deployed `Hem` WHIR Schedule -/

/-- Explicit finite witness for `[CWYZ26]` Theorem 4.8 (finite MCA bound) + Theorem 5.1 (`Eq. 5.7`
    equal-degree affine folding with linear evaluation claims across `sFolds` binary folds). -/
structure WhirAffineWitness where
  /-- Number of coset fibers of the stage oracle (`n = blowup * 2^rem`, the folded evaluation
      domain the proximity gap is applied on; `rem` = variables left after the stage's folds). -/
  n : Nat
  /-- Folded univariate degree bound `d = n / blowup + 2` (carrying the `+2` overflow monomials). -/
  d : Nat
  /-- Number of binary affine folds `s_i` executed in this WHIR stage (= agreement loss). -/
  sFolds : Nat
  /-- Agreement threshold `A` (`|S_{θ,α,β}(P)| ≥ A`). -/
  A : Nat
  /-- Intermediate persistent-agreement threshold `B` (`n * (d + 1) < B^2`, `B < A`). -/
  B : Nat
  /-- Multiplicity parameter `m ≥ 1` in `[CWYZ26]` Lemma 4.2 / Theorem 4.8. -/
  m : Nat
  /-- Total `(Y, Z)`-degree bound `D ≥ 1` of the explainer polynomial `Q(X, Y, Z)`. -/
  D : Nat
  /-- Stage query count `q_i` (distinct fibers, sampled without replacement). -/
  queries : Nat
  /-- Pure query soundness target bits (`128` classical, `256` QROM Grover pre-square-root). -/
  queryTargetBits : Nat
  deriving Repr, DecidableEq

/-- Primitive-recursive accumulator for the unknown count `∑_{j=0}^M (m A - D - d j) (D - j + 1)`
    in `[CWYZ26]` Equation `(4.5)` (`0` `WellFounded.fix`). -/
def interpUnknownsAux (mA_sub_D d D : Nat) : Nat → Nat
  | 0 => mA_sub_D * (D + 1)
  | j + 1 => interpUnknownsAux mA_sub_D d D j + (mA_sub_D - d * (j + 1)) * (D - (j + 1) + 1)

/-- Primitive-recursive accumulator for the per-point equation count
    `∑_{s=0}^K (m - s) (D - s + 1)` in `[CWYZ26]` Equation `(4.2)` / `(4.5)`. -/
def interpEquationsAux (m D : Nat) : Nat → Nat
  | 0 => m * (D + 1)
  | s + 1 => interpEquationsAux m D s + (m - (s + 1)) * (D - (s + 1) + 1)

/-- Exact ceiling `⌈a / b⌉` for `b > 0`. -/
def natCeilDiv (a b : Nat) : Nat :=
  (a + b - 1) / b

/-- Conservative `1/q`-scaled numerator `s_i * (ℓ + 2 ℓ₀ + 1)` for `[CWYZ26]` Theorem 4.8 + Theorem 5.1
    (`Eq. 5.7`, equal-degree affine folding **with linear claims** across `s_i` binary folds), valid
    whenever `checkWhirAffineWitness w q = true` (`nonpersCeil ≤ q` and `n(n-1)/2 ≤ q`). This is the
    quantity `loss * (list + 2 * list0 + 1)` of `affine_schedule.rs`. -/
def whirAffineStageSimpleNum (w : WhirAffineWitness) : Nat :=
  let ell := (w.n * (w.B - w.d - 1)) / (w.B * w.B - w.n * (w.d + 1))
  let ell0 := (w.n * (w.A - 1 - w.d)) / ((w.A - 1) * (w.A - 1) - w.n * w.d)
  w.sFolds * (ell + 2 * ell0 + 1)

/-- Exact `q^2`-scaled numerator from `[CWYZ26]` Theorem 4.8 (`Eq. 4.13`) + Theorem 5.1 (`Eq. 5.7`)
    across `w.sFolds` folds over a field of cardinality `q`. -/
def whirAffineStageExactNumQ2 (w : WhirAffineWitness) (q : Nat) : Nat :=
  let M := Nat.min w.D ((w.m * w.A - w.D - 1) / w.d)
  let ell := (w.n * (w.B - w.d - 1)) / (w.B * w.B - w.n * (w.d + 1))
  let ell0 := (w.n * (w.A - 1 - w.d)) / ((w.A - 1) * (w.A - 1) - w.n * w.d)
  let maxQChoose := Nat.max q (w.n * (w.n - 1) / 2)
  let nonpersCeil := w.D * w.D +
    natCeilDiv (4 * w.d * w.d * M * M * w.D * w.D * w.D * w.n * w.n)
               ((w.A - w.B) * (w.A - w.B))
  w.sFolds * (ell * maxQChoose + 2 * ell0 * q + nonpersCeil)

/-- Decidable verifier checking **every** side condition of `[CWYZ26]` Theorem 4.8 + Theorem 5.1
    exactly as stated in the paper (`m, D ≥ 1`, `M = min {D, ⌊(mA - D - 1)/d⌋} ≥ 1`) and as
    asserted by `affine_schedule.rs::finite_johnson_witnesses_cover_every_canonical_stage`, plus
    the exact `s_i`-loss distinct-fiber query soundness:
    1. `sFolds ≥ 1`, `n ≥ 2`, `d ≥ 1`, `d + 2 ≤ B < A`, `A + sFolds ≤ n`, `m ≥ 1`, `D ≥ 1`,
    2. `D + 1 + d ≤ m * A` and `M ≥ 1` (every term `m * A - D - d * j ≥ 1`, `D - j + 1 ≥ 1`
       for `j ≤ M`, so the truncated `Nat` sums equal the integer sums of Equation `(4.5)`),
    3. Exact Equation `(4.5)` interpolation dimension inequality `unknowns > n * equations`,
    4. Johnson denominator positivity `B^2 > n * (d + 1)` and `(A - 1)^2 > n * d`,
    5. Field-size domination `n * (n - 1) / 2 ≤ q` and `nonpersCeil ≤ q`,
    6. `queries ≤ n` and the EXACT hypergeometric bound
       `affineFallingFactorial (A + sFolds) queries * 2^queryTargetBits < affineFallingFactorial n queries`
       (implied by the upward-rounded dyadic check `query_error_below_2pow_minus256`; the
       with-replacement bound `((A + s)/n)^q` is strictly weaker and REJECTS the deployed table). -/
def checkWhirAffineWitness (w : WhirAffineWitness) (q : Nat) : Bool :=
  let mA := w.m * w.A
  let M := Nat.min w.D ((mA - w.D - 1) / w.d)
  let K := Nat.min (w.m - 1) M
  let unknowns := interpUnknownsAux (mA - w.D) w.d w.D M
  let eqsPerPoint := interpEquationsAux w.m w.D K
  let nonpersCeil := w.D * w.D +
    natCeilDiv (4 * w.d * w.d * M * M * w.D * w.D * w.D * w.n * w.n)
               ((w.A - w.B) * (w.A - w.B))
  decide (
    1 ≤ w.sFolds ∧
    2 ≤ w.n ∧
    1 ≤ w.d ∧
    w.d + 2 ≤ w.B ∧
    w.B < w.A ∧
    w.A + w.sFolds ≤ w.n ∧
    1 ≤ w.m ∧
    1 ≤ w.D ∧
    w.D + 1 + w.d ≤ mA ∧
    1 ≤ M ∧
    w.n * eqsPerPoint < unknowns ∧
    w.n * (w.d + 1) < w.B * w.B ∧
    w.n * w.d < (w.A - 1) * (w.A - 1) ∧
    w.n * (w.n - 1) / 2 ≤ q ∧
    nonpersCeil ≤ q ∧
    w.queries ≤ w.n ∧
    affineFallingFactorial (w.A + w.sFolds) w.queries * 2 ^ w.queryTargetBits <
      affineFallingFactorial w.n w.queries
  )

/-- **Exact-to-Simple Bound Reduction (`whirAffineStageExactNumQ2_le_simple_mul_q`)**:
    Whenever `checkWhirAffineWitness w q = true`, the exact `q^2`-scaled Theorem 4.8 + Theorem 5.1
    numerator is bounded above by `whirAffineStageSimpleNum w * q`, certifying that
    `whirAffineStageSimpleNum w / q` is a sound upper bound on `whirAffineStageExactNumQ2 w q / q^2`! -/
theorem whirAffineStageExactNumQ2_le_simple_mul_q (w : WhirAffineWitness) (q : Nat)
    (hok : checkWhirAffineWitness w q = true) :
    whirAffineStageExactNumQ2 w q ≤ whirAffineStageSimpleNum w * q := by
  unfold checkWhirAffineWitness at hok
  have hProps := of_decide_eq_true hok
  rcases hProps with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hChooseQ, hNonpersQ, _, _⟩
  unfold whirAffineStageExactNumQ2 whirAffineStageSimpleNum
  dsimp only
  have hMaxEq : Nat.max q (w.n * (w.n - 1) / 2) = q :=
    Nat.max_eq_left hChooseQ
  rw [hMaxEq, Nat.mul_assoc w.sFolds _ q]
  apply Nat.mul_le_mul_left
  rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
  exact Nat.add_le_add_left hNonpersQ _

/-! ### §5.1 Mirror of the Deployed Folding Geometry (`pcs.rs::stage_geometry`) -/

/-- Mirror of `pcs.rs::stage_geometry`: `(log₂ blowup, step_vars)` of every WHIR stage. -/
def hemStageGeometry (nv : Nat) : List (Nat × Nat) :=
  if nv ≤ 6 then
    let es := if nv ≤ 3 then 1 else 2
    [(4, nv - es)]
  else if nv ≤ 11 then
    let es := if nv ≤ 8 then 3 else 4
    let rem := nv - es
    let s0 := (rem + 1) / 2
    [(2, s0), (4, rem - s0)]
  else if nv ≤ 16 then
    let es := if nv ≤ 13 then 4 else if nv ≤ 15 then 5 else 6
    let rem := nv - es
    let s0 := Nat.min 4 (rem - 4)
    let s1 := (rem - s0) / 2
    [(2, s0), (4, s1), (6, rem - s0 - s1)]
  else if nv ≤ 20 then [(2, 5), (4, 3), (6, 4)]
  else if nv = 21 then [(2, 6), (4, 3), (6, 4)]
  else if nv = 22 then [(2, 6), (4, 4), (6, 4)]
  else [(2, 6), (4, 4), (6, 3), (8, 3)]

/-- Mirror of the `early_stop_vars` field produced by `pcs.rs::stage_geometry`. -/
def hemEarlyStopVars (nv : Nat) : Nat :=
  if nv ≤ 3 then 1 else if nv ≤ 6 then 2 else if nv ≤ 8 then 3 else if nv ≤ 13 then 4
  else if nv ≤ 15 then 5 else if nv ≤ 16 then 6 else if nv ≤ 20 then nv - 12
  else if nv = 23 then 7 else 8

/-- Mirror of `WhirSecurityRegime::minimum_queries` for the two unconditional Johnson regimes:
    `BciksJohnsonQrom128` uses `⌈512 / log₂ B⌉ + 2`, `BciksJohnsonClassical128` uses
    `⌈256 / log₂ B⌉ + 1`. -/
def hemJohnsonMinQueries (isQrom : Bool) (logBlowup : Nat) : Nat :=
  if isQrom then natCeilDiv 512 logBlowup + 2 else natCeilDiv 256 logBlowup + 1

/-- Resolved per-stage geometry: `n = blowup * 2^rem` coset fibers and folded degree bound
    `d = 2^rem + 2`, where `rem` counts the variables left AFTER this stage's `stepVars` folds
    (exactly the `n`, `d` computed inside `affine_schedule.rs`). -/
structure HemStageGeom where
  stageIdx : Nat
  logBlowup : Nat
  stepVars : Nat
  n : Nat
  d : Nat
  deriving Repr, DecidableEq

def hemStageGeomsAux : Nat → Nat → List (Nat × Nat) → List HemStageGeom
  | _, _, [] => []
  | idx, rem, (lb, sv) :: rest =>
    { stageIdx := idx, logBlowup := lb, stepVars := sv,
      n := 2 ^ lb * 2 ^ (rem - sv), d := 2 ^ (rem - sv) + 2 } ::
      hemStageGeomsAux (idx + 1) (rem - sv) rest

def hemStageGeoms (nv : Nat) : List HemStageGeom :=
  hemStageGeomsAux 0 nv (hemStageGeometry nv)

/-- Mirror of `WhirSchedule::validate` on the canonical geometry: at most `4` stages, blowups in
    `{4, 16, 64, 256}`, every stage folds `1..6` variables and strictly fewer than remain, and
    `early_stop_vars + ∑ step_vars = num_vars` with `1 ≤ early_stop_vars ≤ 8`. -/
def hemStageGeometryValid (nv : Nat) : Bool :=
  let g := hemStageGeometry nv
  decide (1 ≤ g.length ∧ g.length ≤ 4) &&
  g.all (fun p => (p.1 == 2 || p.1 == 4 || p.1 == 6 || p.1 == 8) &&
    decide (1 ≤ p.2 ∧ p.2 ≤ 6)) &&
  decide (hemEarlyStopVars nv + (g.map (·.2)).sum = nv) &&
  decide (1 ≤ hemEarlyStopVars nv ∧ hemEarlyStopVars nv ≤ 8)

/-- Every supported `num_vars ∈ 2..=24` has a schedule accepted by the `validate` mirror, and
    every stage's Johnson QROM query count fits the wire cap `NUM_PCS_QUERIES = 512`. -/
theorem hemStageGeometry_valid_and_under_query_cap :
    ∀ nv : Nat, 2 ≤ nv → nv ≤ 24 →
      hemStageGeometryValid nv = true ∧
      ∀ p ∈ hemStageGeometry nv, hemJohnsonMinQueries true p.1 ≤ 512 := by
  have hAll : ((List.range 23).all fun i =>
      hemStageGeometryValid (i + 2) &&
      (hemStageGeometry (i + 2)).all (fun p => decide (hemJohnsonMinQueries true p.1 ≤ 512))) = true := by
    decide +kernel
  intro nv h2 h24
  have h1 := List.all_eq_true.mp hAll (nv - 2) (List.mem_range.mpr (by omega))
  have hEq : nv - 2 + 2 = nv := by omega
  rw [hEq, Bool.and_eq_true] at h1
  refine ⟨h1.1, fun p hp => ?_⟩
  exact of_decide_eq_true (List.all_eq_true.mp h1.2 p hp)

/-! ### §5.2 The Deployed Witness Table (`affine_schedule.rs::WITNESSES`, Verbatim) -/

/-- VERBATIM copy of `crates/qsag-agg/src/pcs/affine_schedule.rs::WITNESSES`:
    `(num_vars, stage, A, m, D)` with `B = A - 1`, for the canonical `BciksJohnsonQrom128`
    schedule. Stages whose query count reaches the fiber count are exhaustively queried and carry
    no row. -/
def hemJohnsonQromWitnessTable : List (Nat × Nat × Nat × Nat × Nat) :=
  [ (9, 1, 127, 1, 20),
    (10, 0, 329, 1, 14),
    (10, 1, 126, 1, 20),
    (11, 0, 328, 1, 14),
    (11, 1, 126, 1, 20),
    (12, 0, 579, 4, 75),
    (12, 1, 310, 4, 59),
    (12, 2, 174, 8, 139),
    (13, 0, 1091, 8, 143),
    (13, 1, 570, 16, 351),
    (13, 2, 173, 8, 135),
    (14, 0, 2119, 32, 863),
    (14, 1, 1092, 32, 860),
    (14, 2, 308, 32, 706),
    (15, 0, 4178, 64, 2079),
    (15, 1, 1091, 32, 844),
    (15, 2, 308, 32, 706),
    (16, 0, 8296, 128, 5567),
    (16, 1, 2137, 64, 2392),
    (16, 2, 580, 64, 1921),
    (17, 0, 8295, 128, 5503),
    (17, 1, 2137, 64, 2392),
    (17, 2, 307, 32, 691),
    (18, 0, 16531, 128, 7295),
    (18, 1, 4229, 64, 3418),
    (18, 2, 579, 64, 1890),
    (19, 0, 33003, 128, 10879),
    (19, 1, 8413, 64, 5471),
    (19, 2, 1124, 32, 1305),
    (20, 0, 65948, 128, 18111),
    (20, 1, 16782, 32, 3286),
    (20, 2, 2215, 32, 2149),
    (21, 0, 65947, 128, 18047),
    (21, 1, 16782, 32, 3286),
    (21, 2, 2215, 32, 2149),
    (22, 0, 131836, 128, 32511),
    (22, 1, 16781, 32, 3270),
    (22, 2, 2215, 32, 2149),
    (23, 0, 263614, 64, 14494),
    (23, 1, 33518, 32, 5870),
    (23, 2, 8759, 16, 2733),
    (23, 3, 2254, 32, 2672),
    (24, 0, 527170, 64, 27164),
    (24, 1, 66992, 32, 11069),
    (24, 2, 17484, 16, 5228),
    (24, 3, 4482, 16, 2067) ]

def hemJohnsonQromTableRow (nv stage : Nat) : Option (Nat × Nat × Nat × Nat × Nat) :=
  hemJohnsonQromWitnessTable.find? (fun r => r.1 == nv && r.2.1 == stage)

/-- Stage is exhaustively queried (`num_queries ≥ n`): every fiber is opened, no proximity
    witness is needed (`if spec.num_queries as u128 >= n { continue; }`). -/
def hemJohnsonQromStageExhaustive (g : HemStageGeom) : Bool :=
  decide (g.n ≤ hemJohnsonMinQueries true g.logBlowup)

/-- The deployed stage witness: geometry from `hemStageGeoms`, `(A, m, D)` from the table row,
    `B = A - 1`, and the deployed QROM query count. -/
def hemJohnsonQromStageWitness (nv : Nat) (g : HemStageGeom) : Option WhirAffineWitness :=
  (hemJohnsonQromTableRow nv g.stageIdx).map (fun r =>
    { n := g.n, d := g.d, sFolds := g.stepVars, A := r.2.2.1, B := r.2.2.1 - 1,
      m := r.2.2.2.1, D := r.2.2.2.2,
      queries := hemJohnsonMinQueries true g.logBlowup, queryTargetBits := 256 })

/-- Per-stage coverage check mirroring one loop iteration of
    `finite_johnson_witnesses_cover_every_canonical_stage`: an exhaustive stage must carry no
    row; every other stage must carry a row passing `checkWhirAffineWitness` with
    `loss * (list + 2 * list0 + 1) + 1 < 2000`. -/
def hemJohnsonQromStageCovered (q nv : Nat) (g : HemStageGeom) : Bool :=
  if hemJohnsonQromStageExhaustive g = true then
    (hemJohnsonQromTableRow nv g.stageIdx).isNone
  else
    match hemJohnsonQromStageWitness nv g with
    | none => false
    | some w => checkWhirAffineWitness w q && decide (whirAffineStageSimpleNum w + 1 < 2000)

/-- Number of non-exhaustive canonical stages across `num_vars ∈ 2..=24` (the Rust `seen`). -/
def hemJohnsonQromSeenCount : Nat :=
  ((List.range 23).map (fun i =>
    ((hemStageGeoms (i + 2)).filter (fun g => !hemJohnsonQromStageExhaustive g)).length)).sum

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **Deployed-Table Coverage Certificate (`hem_johnson_qrom_witnesses_cover_every_canonical_stage`)**:
    Lean mirror of the Rust test `finite_johnson_witnesses_cover_every_canonical_stage`, decided
    by the kernel over `GoldilocksExt4` (`q = p^4`) on the VERBATIM deployed table:
    1. for every `num_vars ∈ 2..=24` and every stage of the canonical `BciksJohnsonQrom128`
       schedule, the stage is either exhaustively queried or carries a table row satisfying every
       `[CWYZ26]` Theorem 4.8 + Theorem 5.1 side condition, the exact distinct-fiber `< 2^-256`
       query bound, and folding numerator `+ 1 < 2000`;
    2. the number of non-exhaustive stages equals the table length (`seen == WITNESSES.len()`),
       so the table has no dead rows. -/
theorem hem_johnson_qrom_witnesses_cover_every_canonical_stage :
    (∀ nv : Nat, 2 ≤ nv → nv ≤ 24 → ∀ g ∈ hemStageGeoms nv,
      hemJohnsonQromStageCovered (goldilocksPrime ^ 4) nv g = true) ∧
    hemJohnsonQromSeenCount = hemJohnsonQromWitnessTable.length := by
  have hAll : ((List.range 23).all fun i =>
      (hemStageGeoms (i + 2)).all
        (hemJohnsonQromStageCovered (goldilocksPrime ^ 4) (i + 2))) = true := by
    decide +kernel
  refine ⟨?_, by decide +kernel⟩
  intro nv h2 h24 g hg
  have h1 := List.all_eq_true.mp hAll (nv - 2) (List.mem_range.mpr (by omega))
  have hEq : nv - 2 + 2 = nv := by omega
  rw [hEq] at h1
  exact List.all_eq_true.mp h1 g hg

/-- Stage witnesses for `Hem` WHIR at `num_vars = nv`.
    * `isQrom = true` (`BciksJohnsonQrom128`): EXACTLY the deployed rows of
      `hemJohnsonQromWitnessTable` on the deployed geometry, for every `nv`.
    * `isQrom = false` (`BciksJohnsonClassical128`, `q = (129, 65, 44, 33)`): Lean-side witnesses
      at `nv = 20` and `nv = 24` only. The Rust tree ships NO classical-regime table (the QROM rows
      do not meet the `2^-128` target at half the queries), so these rows have no Rust twin. -/
