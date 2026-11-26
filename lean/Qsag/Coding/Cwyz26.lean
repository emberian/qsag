module
public import Qsag.Coding.WhirProfiles
import Qsag.Tactic.AssuranceKit
public import Qsag.Coding.AffineProximity
public import Qsag.Math.GoldilocksEncoding
public import Qsag.Math.QuinticExt5
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


/-! ### §5.2 The Deployed Witness Table (`affine_schedule.rs::WITNESSES`, Verbatim) -/


/-- Columns beyond this Y degree have zero dimension at weighted budget `m*A`. -/
def gsDeployedYDegree (w : WhirAffineWitness) : Nat :=
  min w.D ((w.m * w.A - 1) / w.d)


end Qsag
end

public section
namespace Qsag
open CommRingOps RoundPoly UPoly Poly3
/-- Selected-polynomial decomposition bound for one binary affine fold. This is a
    component needed by the equal-degree three-challenge lift, not that full lift:
    At most `bad` challenges `(α, β) ∈ prodPool S` admit a degree-`≤ d` polynomial `P` agreeing
    with `f + (α + β X) g` on `≥ A` points of `D` that does NOT decompose as `F + (α + β X) G`
    for a `(d, A - 1)` correlated-agreement pair `(F, G)` of `(f, g)`. -/
@[expose] def AffineFoldDecompBound {F : Type} [LawfulField F] [DecidableEq F]
    (D S : List F) (d A bad : Nat) : Prop :=
  ∀ x : (F → F) × (F → F),
    ∀ L : List (Fin (prodPool S).length), L.Nodup →
      (∀ ch ∈ L, ¬¬ ∃ P : List F,
        affineMcaAccepts D S d A x ch.1 P = true ∧
        ¬ DecomposesViaCorrelatedPair d (A - 1) x.1 x.2 D
            ((prodPool S).get ch).1 ((prodPool S).get ch).2 P) →
      L.length ≤ bad

/-- `AffineFoldDecompBound` implies `AffineMcaBound` at the identical parameters. -/
theorem AffineFoldDecompBound.toAffineMcaBound {F : Type} [LawfulField F] [DecidableEq F]
    {D S : List F} {d A bad : Nat}
    (h : AffineFoldDecompBound D S d A bad) : AffineMcaBound D S d A bad := by
  intro x hFar L hNd hEx
  refine h x L hNd (fun ch hch hNo => hEx ch hch (fun ⟨P, hP⟩ => hNo ⟨P, hP, ?_⟩))
  rintro ⟨F_poly, G_poly, ⟨hF, hG, hJ⟩, _⟩
  exact hFar ⟨F_poly, G_poly, hF, hG, hJ⟩

/-- **Constructive Lift from `AffineMcaBound` to `AffineFoldDecompBound`
    (`affineFoldDecompBound_of_affineMcaBound`, `0` classical choice)**:
    Whenever `D.Nodup` and `D.length + d + 1 < 2 * A`, ANY `AffineMcaBound D S d A bad`
    (including both `affineMcaBound_welch_berlekamp` and `cwyz26_affineMcaBound_of_nonExcluded`)
    lifts to `AffineFoldDecompBound D S d A bad` with the identical exceptional-challenge count `bad`. -/
theorem affineFoldDecompBound_of_affineMcaBound {F : Type} [LawfulField F] [DecidableEq F]
    {D S : List F} {d A bad : Nat}
    (hMca : AffineMcaBound D S d A bad)
    (hD : D.Nodup) (hOverlap : D.length + d + 1 < 2 * A) :
    AffineFoldDecompBound D S d A bad := by
  intro x L hNd hEx
  cases L with
  | nil => exact Nat.zero_le bad
  | cons ch₀ rest =>
    -- Intuitionistically deduce `¬ HasCorrelatedAgreement d (A - 1) x.1 x.2 D` from `ch₀`:
    have hNotCA : ¬ HasCorrelatedAgreement d (A - 1) x.1 x.2 D := by
      rintro ⟨F₀, G₀, hF₀, hG₀, hJoint⟩
      refine hEx ch₀ (.head rest) ?_
      rintro ⟨P, hAcc, hNoDecomp⟩
      apply hNoDecomp
      unfold affineMcaAccepts at hAcc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hAcc
      rw [list_getD_eq_get (prodPool S) _ ch₀] at hAcc
      rcases hAcc with ⟨⟨_, hPLen⟩, hPAg⟩
      let α := ((prodPool S).get ch₀).1
      let β := ((prodPool S).get ch₀).2
      let Q := polyAddVar F₀ (polyAddVar (polyScaleVar α G₀) (polyScaleVar β (shiftPoly G₀)))
      have hQLen : Q.length ≤ d + 1 := by
        have h1 : (polyScaleVar α G₀).length ≤ d + 1 := by
          simp only [polyScaleVar_length]; omega
        have h2 : (polyScaleVar β (shiftPoly G₀)).length ≤ d + 1 := by
          simp only [polyScaleVar_length, shiftPoly_length]; omega
        exact polyAddVar_length_le F₀ _ (d + 1) hF₀ (polyAddVar_length_le _ _ (d + 1) h1 h2)
      let pJoint : F → Bool := fun z =>
        decide (RoundPoly.evalCoeffs F₀ z = x.1 z) && decide (RoundPoly.evalCoeffs G₀ z = x.2 z)
      let pFold : F → Bool := fun z =>
        decide (RoundPoly.evalCoeffs P z =
          CommRingOps.add (x.1 z) (CommRingOps.mul (CommRingOps.add α (CommRingOps.mul β z)) (x.2 z)))
      let U := D.filter (fun z => pJoint z && pFold z)
      have hULen : d + 1 ≤ U.length := by
        have hOv := filter_overlap_len pJoint pFold D
        change (D.filter pJoint).length + (D.filter pFold).length ≤ D.length + U.length at hOv
        have hA1 : A - 1 ≤ (D.filter pJoint).length := hJoint
        have hA2 : A ≤ (D.filter pFold).length := hPAg
        omega
      have hTrimEq : trimPoly P = trimPoly Q := by
        refine trimPoly_eq_of_agree_on_nodup hPLen hQLen (List.Pairwise.filter _ hD) hULen ?_
        intro z hz
        rcases List.mem_filter.mp hz with ⟨_, hBoth⟩
        rcases (Bool.and_eq_true _ _).mp hBoth with ⟨hJ, hFl⟩
        have hFz : RoundPoly.evalCoeffs F₀ z = x.1 z :=
          of_decide_eq_true ((Bool.and_eq_true _ _).mp hJ).1
        have hGz : RoundPoly.evalCoeffs G₀ z = x.2 z :=
          of_decide_eq_true ((Bool.and_eq_true _ _).mp hJ).2
        have hPz : RoundPoly.evalCoeffs P z =
            CommRingOps.add (x.1 z) (CommRingOps.mul (CommRingOps.add α (CommRingOps.mul β z)) (x.2 z)) :=
          of_decide_eq_true hFl
        rw [hPz]
        dsimp only [Q]
        rw [evalCoeffs_polyAddVar, evalCoeffs_polyAddVar, evalCoeffs_polyScaleVar,
            evalCoeffs_polyScaleVar, evalCoeffs_shiftPoly, hFz, hGz,
            ← LawfulCommRing.mul_assoc β z (x.2 z), ← LawfulCommRing.right_distrib]
      exact ⟨F₀, G₀, ⟨hF₀, hG₀, hJoint⟩, hTrimEq⟩
    exact hMca x hNotCA (ch₀ :: rest) hNd
      (fun ch hch hNo => hEx ch hch (fun ⟨P, hP, _⟩ => hNo ⟨P, hP⟩))

/-- The Welch–Berlekamp agreement inequality, together with `A ≤ D.length`, implies the
    overlap condition needed for claim-preserving decomposition. No separate rate premise
    is required. -/
theorem affineFoldDecompBound_welch_berlekamp {F : Type} [LawfulField F] [DecidableEq F]
    (D S : List F) (d A : Nat)
    (hD : D.Nodup) (hS : S.Nodup) (hAD : A ≤ D.length)
    (hWB : 2 * D.length + d + 1 < 3 * A) :
    AffineFoldDecompBound D S d A (Nat.max S.length (D.length * (D.length - 1) / 2)) :=
  affineFoldDecompBound_of_affineMcaBound
    (affineMcaBound_welch_berlekamp D S d A hD hS hAD hWB)
    hD (by omega)

/-- **Direct `[CWYZ26]` Johnson-Radius Assembly onto `AffineFoldDecompBound`
    (`cwyz26_affineFoldDecompBound_of_nonExcluded`)**:
    Under Equation (4.5) (`D.length * Poly3.triCount 1 m Dy m < Poly3.triCount d Wx Dy (Dy + 1)`) and
    `Wx + Dy ≤ m * A`, every accepted post-fold witness vanishes in `Poly3.explainer` (Lemma 4.2) and
    at most `Dy` challenges are excluded (`|E| ≤ Dy`), yielding `AffineFoldDecompBound D S d A (Dy + rest)`. -/
theorem cwyz26_affineFoldDecompBound_of_nonExcluded {F : Type} [LawfulField F] [DecidableEq F]
    (D S : List F) (d A m Wx Dy rest : Nat)
    (hrest : NonExcludedDecompBound D S d A m Wx Dy rest)
    (hD : D.Nodup) (hS : S.Nodup)
    (hcount : D.length * Poly3.triCount 1 m Dy m < Poly3.triCount d Wx Dy (Dy + 1))
    (hWA : Wx + Dy ≤ m * A) :
    AffineFoldDecompBound D S d A (Dy + rest) := by
  intro x L hNd hEx
  apply Decidable.byContradiction
  intro hGt
  refine not_not_forall_mem _ L hEx (fun hAll => hGt ?_)
  obtain ⟨hQne, hQdeg, _, _⟩ := Poly3.explainer_spec x.1 x.2 D m d Wx Dy hcount
  have hr := hrest x
  have hfact : ∀ p ∈ L.map (fun ch => (prodPool S).get ch), p ∈ prodPool S ∧
      ∃ P : List F, P.length ≤ d + 1 ∧
        A ≤ (D.filter (foldAgree x p.1 p.2 (UPoly.ofList P))).length ∧
        Poly3.evalAffineLine (Poly3.explainer x.1 x.2 D m d Wx Dy) p.1 p.2 (UPoly.ofList P) =
          CommRingOps.zero ∧
        ¬ DecomposesViaCorrelatedPair d (A - 1) x.1 x.2 D p.1 p.2 P := by
    intro p hp
    obtain ⟨ch, hchL, rfl⟩ := List.mem_map.mp hp
    obtain ⟨Pl, hPlAcc, hNoDecomp⟩ := hAll ch hchL
    unfold affineMcaAccepts at hPlAcc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hPlAcc
    rw [list_getD_eq_get (prodPool S) _ ch] at hPlAcc
    have hfilt : D.filter (foldAgree x ((prodPool S).get ch).1 ((prodPool S).get ch).2
        (UPoly.ofList Pl)) = D.filter (fun z => decide (RoundPoly.evalCoeffs Pl z =
          CommRingOps.add (x.1 z)
            (CommRingOps.mul (CommRingOps.add ((prodPool S).get ch).1
              (CommRingOps.mul ((prodPool S).get ch).2 z)) (x.2 z)))) :=
      congrArg (fun q => List.filter q D) (funext fun z => by
        show decide ((UPoly.ofList Pl).eval z = _) = _
        rw [eval_ofList])
    have hlen : A ≤ (D.filter (foldAgree x ((prodPool S).get ch).1 ((prodPool S).get ch).2
        (UPoly.ofList Pl))).length := by rw [hfilt]; exact hPlAcc.2
    have hdeg : (UPoly.ofList Pl).natDeg ≤ d := by
      have h1 := natDeg_ofList_le Pl
      have h2 := hPlAcc.1.2
      omega
    exact ⟨list_get_mem _ ch, Pl, hPlAcc.1.2, hlen,
      Poly3.explainer_vanishes x.1 x.2 D m d Wx Dy hcount _ _ (UPoly.ofList Pl) _ hdeg
        (nodup_filter _ D hD)
        (fun z hz => (List.mem_filter.mp hz).1)
        (fun z hz => of_decide_eq_true (List.mem_filter.mp hz).2)
        (Nat.le_trans hWA (Nat.mul_le_mul_left m hlen)),
      hNoDecomp⟩
  have hpNd : (L.map (fun ch => (prodPool S).get ch)).Nodup :=
    List.Pairwise.map _ (fun a b hab hEq => hab (nodup_get_inj (prodPool_nodup hS) hEq)) hNd
  have hlenp : (L.map (fun ch => (prodPool S).get ch)).length = L.length := List.length_map _
  generalize Poly3.explainer x.1 x.2 D m d Wx Dy = Q at hQne hQdeg hr hfact
  generalize L.map (fun ch => (prodPool S).get ch) = pairs at hfact hpNd hlenp
  have hexc : (pairs.filter (fun p => decide (Poly3.lineSpec Q p.1 p.2 = CommRingOps.zero))).length ≤
      Q.degYZ :=
    Poly3.lineSpec_zero_card_le Q hQne _ (nodup_filter _ _ hpNd)
      (fun p hp => of_decide_eq_true (List.mem_filter.mp hp).2)
  have hnon : (pairs.filter (fun p => !decide (Poly3.lineSpec Q p.1 p.2 = CommRingOps.zero))).length ≤
      rest :=
    hr _ (nodup_filter _ _ hpNd) (fun p hp => by
      obtain ⟨hm, hb⟩ := List.mem_filter.mp hp
      obtain ⟨h1, h2⟩ := hfact p hm
      exact ⟨h1, fun e => by
        rw [decide_eq_true e] at hb
        exact absurd hb (by decide), h2⟩)
  have hsum := length_filter_add_not
    (fun p : F × F => decide (Poly3.lineSpec Q p.1 p.2 = CommRingOps.zero)) pairs
  omega


end Qsag
end

public section
namespace Qsag
open CommRingOps Poly3
theorem sumTo_le_of_le (f : Nat → Nat) {a b : Nat} (h : a ≤ b) : sumTo f a ≤ sumTo f b := by
  have key : ∀ k, sumTo f a ≤ sumTo f (a + k) := by
    intro k
    induction k with
    | zero => exact Nat.le_refl _
    | succ k ih => exact Nat.le_trans ih (Nat.le_add_right _ _)
  have h2 := key (b - a)
  rwa [Nat.add_sub_cancel' h] at h2

/-- The proved residual count of `nonExcludedDecompBound_sliced`, as a function of the domain
    size `n` and the size `s` of the challenge set. -/
@[expose] def slicedRest (n d A B Wx Dy s : Nat) : Nat :=
  ((n * (B - (d + 1))) / (B * B - n * (d + 1))) * Nat.max s (n * (n - 1) / 2) +
    s * ((Nat.min Dy ((Wx + Dy - 1) / d)) *
      (Dy * (n * ((Nat.min Dy ((Wx + Dy - 1) / d)) * (2 * d * Dy)) / (A - B) + 1)))

/-- The numerical hypotheses of `nonExcludedDecompBound_sliced` at `Wx = m·A - Dy`. The
    interpolation count (4.5) is checked on a truncation of its left-hand sum, which only
    drops zero terms. -/
@[expose] def slicedParamsOk (n d A B m Dy : Nat) : Bool :=
  decide (1 ≤ d ∧ 1 ≤ Dy ∧ d + 1 ≤ B ∧ B < A ∧ n * (d + 1) < B * B ∧ Dy ≤ m * A ∧
    Dy < goldilocksPrime ∧
    n * sumTo (fun j => (Dy + 1 - j) * (m - 1 * j)) m <
      sumTo (fun j => (Dy + 1 - j) * (m * A - Dy - d * j))
        (Nat.min (Dy + 1) ((m * A - Dy) / d + 1)))

/-- **A passing parameter set gives the decomposition bound.** For every duplicate-free
    domain of size `n` and challenge set `S` in `QuinticGoldilocks`, at most
    `Dy + slicedRest n d A B (m·A - Dy) Dy |S|` challenges in `S × S` admit an accepted
    polynomial that does not decompose through a correlated pair. -/
theorem slicedParamsOk_sound (n d A B m Dy : Nat) (h : slicedParamsOk n d A B m Dy = true)
    (D S : List QuinticGoldilocks) (hD : D.Nodup) (hS : S.Nodup) (hn : D.length = n) :
    AffineFoldDecompBound D S d A (Dy + slicedRest n d A B (m * A - Dy) Dy S.length) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := of_decide_eq_true h
  subst hn
  have hcount : D.length * triCount 1 m Dy m < triCount d (m * A - Dy) Dy (Dy + 1) := by
    rw [triCount_eq, triCount_eq]
    exact Nat.lt_of_lt_of_le h8 (sumTo_le_of_le _ (Nat.min_le_left _ _))
  have hWA : m * A - Dy + Dy ≤ m * A := Nat.le_of_eq (Nat.sub_add_cancel h6)
  exact cwyz26_affineFoldDecompBound_of_nonExcluded D S d A m (m * A - Dy) Dy _
    (nonExcludedDecompBound_sliced D S d A B m (m * A - Dy) Dy hD hS hcount h1 h2 h3 h5 h4
      (fun k a b => QuinticGoldilocks.natCast_ne_zero k a (Nat.lt_of_le_of_lt b h7)))
    hD hS hcount hWA


/-! ### Exports for lane agg-budget -/

/-- The last two conjuncts of `checkWhirAffineWitness`: the query count fits the fiber count and
    the exact distinct-fiber query bound is below `2^-queryTargetBits`. -/
theorem checkWhirAffineWitness_query_bound (w : WhirAffineWitness) (q : Nat)
    (hok : checkWhirAffineWitness w q = true) :
    w.queries ≤ w.n ∧
      affineFallingFactorial (w.A + w.sFolds) w.queries * 2 ^ w.queryTargetBits <
        affineFallingFactorial w.n w.queries := by
  unfold checkWhirAffineWitness at hok
  have hProps := of_decide_eq_true hok
  rcases hProps with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hqn, hQuery⟩
  exact ⟨hqn, hQuery⟩


theorem natCeilDiv_def (a b : Nat) : natCeilDiv a b = (a + b - 1) / b := by rfl


theorem whirAffineStageSimpleNum_def (w : WhirAffineWitness) :
    whirAffineStageSimpleNum w =
      w.sFolds * ((w.n * (w.B - w.d - 1)) / (w.B * w.B - w.n * (w.d + 1)) +
        2 * ((w.n * (w.A - 1 - w.d)) / ((w.A - 1) * (w.A - 1) - w.n * w.d)) + 1) := by rfl

theorem interpUnknownsAux_zero (mA_sub_D d D : Nat) :
    interpUnknownsAux mA_sub_D d D 0 = mA_sub_D * (D + 1) := by rfl

theorem interpUnknownsAux_succ (mA_sub_D d D j : Nat) :
    interpUnknownsAux mA_sub_D d D (j + 1) =
      interpUnknownsAux mA_sub_D d D j + (mA_sub_D - d * (j + 1)) * (D - (j + 1) + 1) := by rfl

theorem interpEquationsAux_zero (m D : Nat) : interpEquationsAux m D 0 = m * (D + 1) := by rfl

theorem interpEquationsAux_succ (m D s : Nat) :
    interpEquationsAux m D (s + 1) =
      interpEquationsAux m D s + (m - (s + 1)) * (D - (s + 1) + 1) := by rfl

theorem checkWhirAffineWitness_def (w : WhirAffineWitness) (q : Nat) :
    checkWhirAffineWitness w q =
    (let mA := w.m * w.A
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
      )) := by rfl


-- (end exports for lane agg-budget)

/-! ### Exports for lane agg-whir-cert -/


theorem slicedRest_def (n d A B Wx Dy s : Nat) :
    slicedRest n d A B Wx Dy s =
      ((n * (B - (d + 1))) / (B * B - n * (d + 1))) * Nat.max s (n * (n - 1) / 2) +
        s * ((Nat.min Dy ((Wx + Dy - 1) / d)) *
          (Dy * (n * ((Nat.min Dy ((Wx + Dy - 1) / d)) * (2 * d * Dy)) / (A - B) + 1))) := by rfl

theorem slicedParamsOk_def (n d A B m Dy : Nat) :
    slicedParamsOk n d A B m Dy =
      decide (1 ≤ d ∧ 1 ≤ Dy ∧ d + 1 ≤ B ∧ B < A ∧ n * (d + 1) < B * B ∧ Dy ≤ m * A ∧
        Dy < goldilocksPrime ∧
        n * sumTo (fun j => (Dy + 1 - j) * (m - 1 * j)) m <
          sumTo (fun j => (Dy + 1 - j) * (m * A - Dy - d * j))
            (Nat.min (Dy + 1) ((m * A - Dy) / d + 1))) := by rfl

-- (end exports for lane agg-whir-cert)

end Qsag
end

public section
namespace Qsag
end Qsag
end

-- Owning-module audit certificates for theorems audited and paired in `Tests/MathAndCoding`.
#verify_constructive Qsag.cwyz26_affineMcaBound_of_nonExcluded
  Qsag.cwyz26_affineMcaBound_sliced
  Qsag.slicedParamsOk_sound
  Qsag.sumTo_le_of_le

-- Kernel-checked defining equations for the executed controls in `Tests/MathAndCoding` (no body is exposed).


/-! ## Executed controls for `Tests/MathAndCoding`

Kernel-evaluated witnesses and teeth, stated here because the definitions they execute are sealed outside
this module. `Tests/MathAndCoding` audits and pairs them. -/
public section
namespace Qsag

set_option autoImplicit false
set_option exponentiation.threshold 512


/-! ### Executed table lookups at `nv = 24`, stage `0`

Cited by the stage-profile teeth of `Protocol/Aggregation/HemOpening` (audited in
`Tests/HemExtractedOpeningBridgeTests`); the tables are not exported. -/


-- (math-teeth anchor Qsag )
end Qsag
end
