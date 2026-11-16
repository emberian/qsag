module
public import Qsag.Coding.WhirProfiles
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
def whirAffineStageWitnesses (nv : Nat) (isQrom : Bool) : List WhirAffineWitness :=
  if isQrom then
    (hemStageGeoms nv).filterMap (fun g =>
      if hemJohnsonQromStageExhaustive g = true then none else hemJohnsonQromStageWitness nv g)
  else if nv = 20 then
    [ { n := 131072, d := 32770, sFolds := 5, A := 65884, B := 65798,
        m := 122, D := 12150, queries := 129, queryTargetBits := 128 },
      { n := 65536,  d := 4098,  sFolds := 3, A := 16734, B := 16648,
        m := 48,  D := 3072,  queries := 65, queryTargetBits := 128 },
      { n := 16384,  d := 258,   sFolds := 4, A := 2177,  B := 2148,
        m := 64,  D := 3072,  queries := 44, queryTargetBits := 128 } ]
  else if nv = 24 then
    [ { n := 1048576, d := 262146, sFolds := 6, A := 527106, B := 526403,
        m := 64,  D := 11007, queries := 129, queryTargetBits := 128 },
      { n := 262144,  d := 16386,  sFolds := 4, A := 66944,  B := 66594,
        m := 24,  D := 3200,  queries := 65, queryTargetBits := 128 },
      { n := 131072,  d := 2050,   sFolds := 3, A := 17446,  B := 17184,
        m := 12,  D := 768,   queries := 44, queryTargetBits := 128 },
      { n := 65536,   d := 258,    sFolds := 3, A := 4452,   B := 4369,
        m := 16,  D := 1536,  queries := 33, queryTargetBits := 128 } ]
  else []

/-- Columns beyond this Y degree have zero dimension at weighted budget `m*A`. -/
def gsDeployedYDegree (w : WhirAffineWitness) : Nat :=
  min w.D ((w.m * w.A - 1) / w.d)

/-- All 46 deployed rows satisfy the genuine bivariate Hasse-interpolation dimension
    inequality, including the multiplicity-one rows. This is separate from the trivariate
    affine-proximity explainer checked by `checkWhirAffineWitness`. -/
theorem hem_gs_interpolation_dimensions :
    ∀ nv : Nat, 2 ≤ nv → nv ≤ 24 → ∀ w ∈ whirAffineStageWitnesses nv true,
      w.n * (w.m * (w.m + 1) / 2) <
        gsMonomialCount (w.m * w.A) w.d (gsDeployedYDegree w) := by
  have hAll : ((List.range 23).all (fun i =>
      (whirAffineStageWitnesses (i + 2) true).all (fun w =>
        decide (w.n * (w.m * (w.m + 1) / 2) <
          gsMonomialCount (w.m * w.A) w.d (gsDeployedYDegree w))))) = true := by
    decide +kernel
  intro nv h2 h24 w hw
  have h := List.all_eq_true.mp hAll (nv - 2) (List.mem_range.mpr (by omega))
  have he : nv - 2 + 2 = nv := by omega
  rw [he] at h
  exact of_decide_eq_true (List.all_eq_true.mp h w hw)

/-- Executable interpolation witnesses at every deployed row, over any decidable field and
    any received word of the deployed length. No decoder or polynomial witness is an input. -/
theorem hem_gs_constructive_interpolation {F : Type} [LawfulField F] [DecidableEq F]
    (nv : Nat) (h2 : 2 ≤ nv) (h24 : nv ≤ 24)
    (w : WhirAffineWitness) (hw : w ∈ whirAffineStageWitnesses nv true)
    (points : List (F × F)) (hN : points.length = w.n) :
    let B := w.m * w.A
    let D := gsDeployedYDegree w
    let coeffs := solveHomogeneous (gsMonomialCount B w.d D)
      (gsInterpolationRows B w.d D w.m points)
    coeffs.length = gsMonomialCount B w.d D ∧
    coeffs.any (fun c => !(decide (c = CommRingOps.zero))) = true ∧
    ∀ p ∈ points, ∀ r s, r + s < w.m → gsHasseEval B w.d D coeffs (r, s) p = CommRingOps.zero := by
  apply guruswami_sudan_interpolation
  rw [hN]
  exact hem_gs_interpolation_dimensions nv h2 h24 w hw

/-- All classical-regime stage witnesses (`nv = 20` and `nv = 24`) also satisfy the exact bivariate
    Hasse-interpolation dimension inequality. -/
theorem hem_gs_classical_interpolation_dimensions :
    (∀ w ∈ whirAffineStageWitnesses 20 false,
      w.n * (w.m * (w.m + 1) / 2) <
        gsMonomialCount (w.m * w.A) w.d (gsDeployedYDegree w)) ∧
    (∀ w ∈ whirAffineStageWitnesses 24 false,
      w.n * (w.m * (w.m + 1) / 2) <
        gsMonomialCount (w.m * w.A) w.d (gsDeployedYDegree w)) := by
  constructor <;> decide +kernel

/-- **Unconditional Guruswami–Sudan List Bound Across All 46 Deployed `BciksJohnsonQrom128` Rows
    (`hem_gs_deployed_list_bound`)**:
    For EVERY `nv ∈ 2..=24`, EVERY deployed stage witness `w ∈ whirAffineStageWitnesses nv true`,
    ANY decidable field `F`, ANY duplicate-free domain `domain : List F` of length `w.n`, ANY
    received word `word : F → F`, and ANY duplicate-free list `polys : List (GsUniPoly F)` of
    degree-`≤ w.d` polynomials each agreeing with `word` on `≥ w.A` distinct points of `domain`,
    **`polys.length ≤ gsDeployedYDegree w ∧ polys.length ≤ w.D`** (`0` interpolant or candidate-list
    assumptions!). -/
theorem hem_gs_deployed_list_bound {F : Type} [LawfulField F] [DecidableEq F]
    (nv : Nat) (h2 : 2 ≤ nv) (h24 : nv ≤ 24)
    (w : WhirAffineWitness) (hw : w ∈ whirAffineStageWitnesses nv true)
    (domain : List F) (hDomNd : domain.Nodup) (hDomLen : domain.length = w.n)
    (word : F → F)
    (polys : List (GsUniPoly F)) (hDistinct : polys.Nodup)
    (hClose : ∀ P ∈ polys, P.coeffs.length ≤ w.d + 1 ∧
      w.A ≤ (domain.filter (fun x => decide (evalCoeffs P.coeffs x = word x))).length) :
    polys.length ≤ gsDeployedYDegree w ∧ polys.length ≤ w.D := by
  have hDim : domain.length * (w.m * (w.m + 1) / 2) <
      gsMonomialCount (w.m * w.A) w.d (gsDeployedYDegree w) := by
    rw [hDomLen]
    exact hem_gs_interpolation_dimensions nv h2 h24 w hw
  have hBound := guruswami_sudan_filter_list_bound domain word w.d w.A (gsDeployedYDegree w)
    w.m hDomNd hDim polys hDistinct hClose
  exact ⟨hBound, Nat.le_trans hBound (Nat.min_le_left _ _)⟩

/-- Unconditional Guruswami–Sudan list bound for the `BciksJohnsonClassical128` witnesses at
    `nv = 20` and `nv = 24`. -/
theorem hem_gs_classical_list_bound {F : Type} [LawfulField F] [DecidableEq F]
    (nv : Nat) (hnv : nv = 20 ∨ nv = 24)
    (w : WhirAffineWitness) (hw : w ∈ whirAffineStageWitnesses nv false)
    (domain : List F) (hDomNd : domain.Nodup) (hDomLen : domain.length = w.n)
    (word : F → F)
    (polys : List (GsUniPoly F)) (hDistinct : polys.Nodup)
    (hClose : ∀ P ∈ polys, P.coeffs.length ≤ w.d + 1 ∧
      w.A ≤ (domain.filter (fun x => decide (evalCoeffs P.coeffs x = word x))).length) :
    polys.length ≤ gsDeployedYDegree w ∧ polys.length ≤ w.D := by
  have hDim : domain.length * (w.m * (w.m + 1) / 2) <
      gsMonomialCount (w.m * w.A) w.d (gsDeployedYDegree w) := by
    rw [hDomLen]
    rcases hnv with rfl | rfl
    · exact hem_gs_classical_interpolation_dimensions.1 w hw
    · exact hem_gs_classical_interpolation_dimensions.2 w hw
  have hBound := guruswami_sudan_filter_list_bound domain word w.d w.A (gsDeployedYDegree w)
    w.m hDomNd hDim polys hDistinct hClose
  exact ⟨hBound, Nat.le_trans hBound (Nat.min_le_left _ _)⟩

/-- The `nv = 20` and `nv = 24` QROM witness lists ARE the deployed `(A, B = A - 1, m, D)` rows
    on the deployed `(n, d, s_i, q_i)` geometry (`q = (258, 130, 88, 66)`). -/
theorem whirAffineStageWitnesses_qrom_eq_deployed :
    whirAffineStageWitnesses 20 true =
      [ { n := 131072, d := 32770, sFolds := 5, A := 65948, B := 65947,
          m := 128, D := 18111, queries := 258, queryTargetBits := 256 },
        { n := 65536, d := 4098, sFolds := 3, A := 16782, B := 16781,
          m := 32, D := 3286, queries := 130, queryTargetBits := 256 },
        { n := 16384, d := 258, sFolds := 4, A := 2215, B := 2214,
          m := 32, D := 2149, queries := 88, queryTargetBits := 256 } ] ∧
    whirAffineStageWitnesses 24 true =
      [ { n := 1048576, d := 262146, sFolds := 6, A := 527170, B := 527169,
          m := 64, D := 27164, queries := 258, queryTargetBits := 256 },
        { n := 262144, d := 16386, sFolds := 4, A := 66992, B := 66991,
          m := 32, D := 11069, queries := 130, queryTargetBits := 256 },
        { n := 131072, d := 2050, sFolds := 3, A := 17484, B := 17483,
          m := 16, D := 5228, queries := 88, queryTargetBits := 256 },
        { n := 65536, d := 258, sFolds := 3, A := 4482, B := 4481,
          m := 16, D := 2067, queries := 66, queryTargetBits := 256 } ] := by
  constructor <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- **Kernel-Decided `Theorem 4.8 + Theorem 5.1` Soundness Certificate (`cwyz26_whir_nv20_and_nv24_all_stages_valid`)**:
    Certifies by exact kernel arithmetic (`0` floating point, `0` trust) that ALL 14 stage
    witnesses across `nv = 20` (`3` stages) and `nv = 24` (`4` stages) for both
    `BciksJohnsonClassical128` (`q = (129, 65, 44, 33)`, Lean-side rows) and `BciksJohnsonQrom128`
    (`q = (258, 130, 88, 66)`, the DEPLOYED rows) over `GoldilocksExt4` (`q = goldilocksPrime ^ 4`)
    satisfy `checkWhirAffineWitness` AND have commit-folding numerator **`< 1900`**
    (`> 245` bits of unconditional folding soundness per stage!). -/
theorem cwyz26_whir_nv20_and_nv24_all_stages_valid :
    let q := goldilocksPrime ^ 4
    (∀ w ∈ whirAffineStageWitnesses 20 false,
      checkWhirAffineWitness w q = true ∧ whirAffineStageSimpleNum w < 1900) ∧
    (∀ w ∈ whirAffineStageWitnesses 20 true,
      checkWhirAffineWitness w q = true ∧ whirAffineStageSimpleNum w < 1900) ∧
    (∀ w ∈ whirAffineStageWitnesses 24 false,
      checkWhirAffineWitness w q = true ∧ whirAffineStageSimpleNum w < 1900) ∧
    (∀ w ∈ whirAffineStageWitnesses 24 true,
      checkWhirAffineWitness w q = true ∧ whirAffineStageSimpleNum w < 1900) := by
  decide +kernel


/-- The deployed Johnson agreement thresholds permit complete interpolation-based decoding. -/
theorem hem_gs_deployed_degree_lt_agreement :
    ∀ nv : Nat, 2 ≤ nv → nv ≤ 24 → ∀ w ∈ whirAffineStageWitnesses nv true,
      w.d + 1 ≤ w.A := by
  have hAll : ((List.range 23).all (fun i =>
      (whirAffineStageWitnesses (i + 2) true).all (fun w => decide (w.d + 1 ≤ w.A)))) = true := by
    decide +kernel
  intro nv h2 h24 w hw
  have h := List.all_eq_true.mp hAll (nv - 2) (List.mem_range.mpr (by omega))
  have he : nv - 2 + 2 = nv := by omega
  rw [he] at h
  exact of_decide_eq_true (List.all_eq_true.mp h w hw)

/-- Complete, bounded candidate enumeration at the deployed Johnson radius. Neither the
    candidate list nor Hasse multiplicity is supplied by the prover. -/
theorem hem_gs_deployed_decoder {F : Type} [LawfulField F] [DecidableEq F]
    (nv : Nat) (h2 : 2 ≤ nv) (h24 : nv ≤ 24)
    (w : WhirAffineWitness) (hw : w ∈ whirAffineStageWitnesses nv true)
    (domain : List F) (hDom : domain.Nodup) (hLen : domain.length = w.n)
    (word : F → F) :
    (gsDecodeList w.d w.A domain word).length ≤ w.D ∧
    ∀ P : GsUniPoly F, P ∈ gsDecodeList w.d w.A domain word ↔
      P.coeffs.length ≤ w.d + 1 ∧
      w.A ≤ (domain.filter (fun x => decide (RoundPoly.evalCoeffs P.coeffs x = word x))).length := by
  have hdA := hem_gs_deployed_degree_lt_agreement nv h2 h24 w hw
  refine ⟨?_, fun P => mem_gsDecodeList_iff word hDom hdA P⟩
  exact Nat.le_trans
    (gsDecodeList_length_le domain word w.d w.A (gsDeployedYDegree w) w.m hDom hdA
      (by rw [hLen]; exact hem_gs_interpolation_dimensions nv h2 h24 w hw))
    (Nat.min_le_left _ _)


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
    domain of size `n` and challenge set `S` in `QuarticGoldilocks`, at most
    `Dy + slicedRest n d A B (m·A - Dy) Dy |S|` challenges in `S × S` admit an accepted
    polynomial that does not decompose through a correlated pair. -/
theorem slicedParamsOk_sound (n d A B m Dy : Nat) (h : slicedParamsOk n d A B m Dy = true)
    (D S : List QuarticGoldilocks) (hD : D.Nodup) (hS : S.Nodup) (hn : D.length = n) :
    AffineFoldDecompBound D S d A (Dy + slicedRest n d A B (m * A - Dy) Dy S.length) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := of_decide_eq_true h
  subst hn
  have hcount : D.length * triCount 1 m Dy m < triCount d (m * A - Dy) Dy (Dy + 1) := by
    rw [triCount_eq, triCount_eq]
    exact Nat.lt_of_lt_of_le h8 (sumTo_le_of_le _ (Nat.min_le_left _ _))
  have hWA : m * A - Dy + Dy ≤ m * A := Nat.le_of_eq (Nat.sub_add_cancel h6)
  exact cwyz26_affineFoldDecompBound_of_nonExcluded D S d A m (m * A - Dy) Dy _
    (nonExcludedDecompBound_sliced D S d A B m (m * A - Dy) Dy hD hS hcount h1 h2 h3 h5 h4
      (fun k a b => QuarticGoldilocks.natCast_ne_zero k a (Nat.lt_of_le_of_lt b h7)))
    hD hS hcount hWA

/-- `(num_vars, stage, B, bits)`: one persistence threshold `B` per non-exhaustive canonical
    stage, and a floor of `log₂ (q² / (Dy + rest))` at `q = p⁴`. -/
def slicedStageTable : List (Nat × Nat × Nat × Nat) :=
  [
    (9, 1, 70, 234),
    (10, 0, 259, 235),
    (10, 1, 70, 234),
    (11, 0, 259, 235),
    (11, 1, 70, 234),
    (12, 0, 515, 224),
    (12, 1, 262, 224),
    (12, 2, 140, 219),
    (13, 0, 1027, 218),
    (13, 1, 518, 213),
    (13, 2, 140, 219),
    (14, 0, 2051, 207),
    (14, 1, 1030, 207),
    (14, 2, 268, 208),
    (15, 0, 4099, 201),
    (15, 1, 1030, 207),
    (15, 2, 268, 208),
    (16, 0, 8195, 194),
    (16, 1, 2054, 200),
    (16, 2, 524, 202),
    (17, 0, 8195, 194),
    (17, 1, 2054, 200),
    (17, 2, 268, 208),
    (18, 0, 16387, 192),
    (18, 1, 4102, 198),
    (18, 2, 524, 202),
    (19, 0, 32771, 190),
    (19, 1, 8198, 195),
    (19, 2, 1036, 204),
    (20, 0, 65539, 187),
    (20, 1, 16390, 198),
    (20, 2, 2060, 201),
    (21, 0, 65539, 187),
    (21, 1, 16390, 198),
    (21, 2, 2060, 201),
    (22, 0, 131075, 184),
    (22, 1, 16390, 198),
    (22, 2, 2060, 201),
    (23, 0, 262147, 187),
    (23, 1, 32774, 195),
    (23, 2, 8204, 201),
    (23, 3, 2072, 199),
    (24, 0, 524291, 185),
    (24, 1, 65542, 192),
    (24, 2, 16396, 198),
    (24, 3, 4120, 201) ]

def slicedStageRow (nv stage : Nat) : Option (Nat × Nat × Nat × Nat) :=
  slicedStageTable.find? (fun r => r.1 == nv && r.2.1 == stage)

/-- The bad-challenge count proved for one binary fold of a stage, at challenge-set size `q`:
    `r` is the deployed row `(num_vars, stage, A, m, D)`, `w` the row of `slicedStageTable`. -/
@[expose] def slicedStageCount (q : Nat) (g : HemStageGeom) (r : Nat × Nat × Nat × Nat × Nat)
    (w : Nat × Nat × Nat × Nat) : Nat :=
  r.2.2.2.2 + slicedRest g.n g.d r.2.2.1 w.2.2.1 (r.2.2.2.1 * r.2.2.1 - r.2.2.2.2) r.2.2.2.2 q

/-- One stage: exhaustively queried with no row, or a row passing `slicedParamsOk` whose
    count is at most `q² / 2^bits` with `bits ≥ 184`. -/
def slicedStageCovered (q nv : Nat) (g : HemStageGeom) : Bool :=
  if hemJohnsonQromStageExhaustive g = true then
    (slicedStageRow nv g.stageIdx).isNone
  else
    match hemJohnsonQromTableRow nv g.stageIdx, slicedStageRow nv g.stageIdx with
    | some r, some w =>
      slicedParamsOk g.n g.d r.2.2.1 w.2.2.1 r.2.2.2.1 r.2.2.2.2 &&
        decide (slicedStageCount q g r w * 2 ^ w.2.2.2 ≤ q * q) && decide (184 ≤ w.2.2.2)
    | _, _ => false

/-- One stage: the proved count is above `2000·q`. -/
def slicedStageAboveSimpleBudget (q nv : Nat) (g : HemStageGeom) : Bool :=
  match hemJohnsonQromTableRow nv g.stageIdx, slicedStageRow nv g.stageIdx with
  | some r, some w => decide (2000 * q < slicedStageCount q g r w)
  | _, _ => hemJohnsonQromStageExhaustive g

def slicedStageSeenCount : Nat :=
  ((List.range 23).map (fun i =>
    ((hemStageGeoms (i + 2)).filter (fun g => !hemJohnsonQromStageExhaustive g)).length)).sum

/-- **Every canonical stage is covered by the proved count**, and the table has no dead rows. -/
theorem sliced_stage_table_covers_every_canonical_stage :
    (∀ nv : Nat, 2 ≤ nv → nv ≤ 24 → ∀ g ∈ hemStageGeoms nv,
      slicedStageCovered (goldilocksPrime ^ 4) nv g = true) ∧
    slicedStageSeenCount = slicedStageTable.length := by
  have hAll : ((List.range 23).all fun i =>
      (hemStageGeoms (i + 2)).all (slicedStageCovered (goldilocksPrime ^ 4) (i + 2))) = true := by
    decide +kernel
  refine ⟨?_, by decide +kernel⟩
  intro nv h2 h24 g hg
  have h1 := List.all_eq_true.mp hAll (nv - 2) (List.mem_range.mpr (by omega))
  have hEq : nv - 2 + 2 = nv := by omega
  rw [hEq] at h1
  exact List.all_eq_true.mp h1 g hg

/-- **The proved decomposition bound on a deployed stage.** A non-exhaustive canonical stage
    has a deployed row `r = (_, _, A, m, D)` and a row `w = (_, _, B, bits)` such that, on every
    duplicate-free domain of the stage size, at most `slicedStageCount |S| g r w` challenges in
    `S × S` break claim-preserving decomposition of one binary fold; at `|S| = p⁴` this is at
    most `p⁸ / 2^bits`, and `bits ≥ 184`. -/
theorem sliced_stage_decomp_bound (nv : Nat) (h2 : 2 ≤ nv) (h24 : nv ≤ 24) (g : HemStageGeom)
    (hg : g ∈ hemStageGeoms nv) (hne : hemJohnsonQromStageExhaustive g = false) :
    ∃ (r : Nat × Nat × Nat × Nat × Nat) (w : Nat × Nat × Nat × Nat),
      hemJohnsonQromTableRow nv g.stageIdx = some r ∧ slicedStageRow nv g.stageIdx = some w ∧
      (∀ D S : List QuarticGoldilocks, D.Nodup → S.Nodup → D.length = g.n →
        AffineFoldDecompBound D S g.d r.2.2.1 (slicedStageCount S.length g r w)) ∧
      slicedStageCount (goldilocksPrime ^ 4) g r w * 2 ^ w.2.2.2 ≤
        goldilocksPrime ^ 4 * goldilocksPrime ^ 4 ∧
      184 ≤ w.2.2.2 := by
  have hc := sliced_stage_table_covers_every_canonical_stage.1 nv h2 h24 g hg
  unfold slicedStageCovered at hc
  rw [hne] at hc
  simp only [Bool.false_eq_true, ↓reduceIte] at hc
  split at hc
  · next r w hr hw =>
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc
    exact ⟨r, w, hr, hw,
      fun D S hD hS hn => slicedParamsOk_sound g.n g.d r.2.2.1 w.2.2.1 r.2.2.2.1 r.2.2.2.2
        hc.1.1 D S hD hS hn,
      of_decide_eq_true hc.1.2, of_decide_eq_true hc.2⟩
  · exact absurd hc Bool.false_ne_true

/-- **The proved count does not reach the deployed simple budget.** On every canonical stage
    the count at `|S| = p⁴` exceeds `2000·p⁴`. -/
theorem sliced_rest_exceeds_simple_budget :
    ∀ nv : Nat, 2 ≤ nv → nv ≤ 24 → ∀ g ∈ hemStageGeoms nv,
      slicedStageAboveSimpleBudget (goldilocksPrime ^ 4) nv g = true := by
  have hAll : ((List.range 23).all fun i =>
      (hemStageGeoms (i + 2)).all
        (slicedStageAboveSimpleBudget (goldilocksPrime ^ 4) (i + 2))) = true := by
    decide +kernel
  intro nv h2 h24 g hg
  have h1 := List.all_eq_true.mp hAll (nv - 2) (List.mem_range.mpr (by omega))
  have hEq : nv - 2 + 2 = nv := by omega
  rw [hEq] at h1
  exact List.all_eq_true.mp h1 g hg


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

/-- Every deployed `BciksJohnsonQrom128` witness row (`num_vars ∈ 2..=24`) passes
    `checkWhirAffineWitness` over `GoldilocksExt4`, has folding numerator `+ 1 < 2000`, and carries
    the `256`-bit query target. -/
theorem whirAffineStageWitnesses_qrom_checked :
    ∀ nv : Nat, 2 ≤ nv → nv ≤ 24 → ∀ w ∈ whirAffineStageWitnesses nv true,
      checkWhirAffineWitness w (goldilocksPrime ^ 4) = true ∧
      whirAffineStageSimpleNum w + 1 < 2000 ∧ w.queryTargetBits = 256 := by
  intro nv h2 h24 w hw
  unfold whirAffineStageWitnesses at hw
  rw [ite_eq_left rfl] at hw
  obtain ⟨g, hg, hgw⟩ := List.mem_filterMap.mp hw
  have hc := (hem_johnson_qrom_witnesses_cover_every_canonical_stage).1 nv h2 h24 g hg
  unfold hemJohnsonQromStageCovered at hc
  by_cases hex : hemJohnsonQromStageExhaustive g = true
  · rw [ite_eq_left hex] at hgw
    exact absurd hgw (fun h => nomatch h)
  · rw [ite_eq_right hex] at hgw
    rw [ite_eq_right hex, hgw] at hc
    dsimp only at hc
    rw [Bool.and_eq_true] at hc
    refine ⟨hc.1, of_decide_eq_true hc.2, ?_⟩
    unfold hemJohnsonQromStageWitness at hgw
    obtain ⟨r, _, hr⟩ := Option.map_eq_some_iff.mp hgw
    rw [← hr]

/-- The resolved `num_vars = 24` stage geometry of `pcs.rs::stage_geometry`. -/
theorem hemStageGeoms_24_eq :
    hemStageGeoms 24 =
      [ { stageIdx := 0, logBlowup := 2, stepVars := 6, n := 1048576, d := 262146 },
        { stageIdx := 1, logBlowup := 4, stepVars := 4, n := 262144, d := 16386 },
        { stageIdx := 2, logBlowup := 6, stepVars := 3, n := 131072, d := 2050 },
        { stageIdx := 3, logBlowup := 8, stepVars := 3, n := 65536, d := 258 } ] := by
  rfl

/-- The resolved `num_vars = 20` stage geometry of `pcs.rs::stage_geometry`. -/
theorem hemStageGeoms_20_eq :
    hemStageGeoms 20 =
      [ { stageIdx := 0, logBlowup := 2, stepVars := 5, n := 131072, d := 32770 },
        { stageIdx := 1, logBlowup := 4, stepVars := 3, n := 65536, d := 4098 },
        { stageIdx := 2, logBlowup := 6, stepVars := 4, n := 16384, d := 258 } ] := by
  rfl

theorem natCeilDiv_def (a b : Nat) : natCeilDiv a b = (a + b - 1) / b := by rfl

theorem hemJohnsonMinQueries_def (isQrom : Bool) (logBlowup : Nat) :
    hemJohnsonMinQueries isQrom logBlowup =
      if isQrom then natCeilDiv 512 logBlowup + 2 else natCeilDiv 256 logBlowup + 1 := by rfl

theorem whirAffineStageSimpleNum_def (w : WhirAffineWitness) :
    whirAffineStageSimpleNum w =
      w.sFolds * ((w.n * (w.B - w.d - 1)) / (w.B * w.B - w.n * (w.d + 1)) +
        2 * ((w.n * (w.A - 1 - w.d)) / ((w.A - 1) * (w.A - 1) - w.n * w.d)) + 1) := by rfl
/-- Deployed per-stage query counts of the two Johnson regimes (`pcs.rs::minimum_queries` at
    `log₂ B ∈ {2, 4, 6, 8}`). -/
theorem hemJohnsonMinQueries_deployed :
    (hemJohnsonMinQueries true 2 = 258 ∧ hemJohnsonMinQueries true 4 = 130 ∧
      hemJohnsonMinQueries true 6 = 88 ∧ hemJohnsonMinQueries true 8 = 66) ∧
    (hemJohnsonMinQueries false 2 = 129 ∧ hemJohnsonMinQueries false 4 = 65 ∧
      hemJohnsonMinQueries false 6 = 44 ∧ hemJohnsonMinQueries false 8 = 33) := by
  decide +kernel

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

theorem hemStageGeometry_def (nv : Nat) :
    hemStageGeometry nv =
    (if nv ≤ 6 then
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
      else if nv ≤ 24 then [(2, 6), (4, 4), (6, 3), (8, 3)]
      else if nv = 25 then [(2, 6), (4, 4), (6, 4), (8, 3)]
      else if nv = 26 then [(2, 6), (4, 5), (6, 4), (8, 3)]
      else if nv = 27 then [(2, 6), (4, 5), (6, 4), (8, 4)]
      else if nv = 28 then [(2, 6), (4, 6), (6, 4), (8, 4)]
      else []) := by rfl

theorem hemJohnsonQromTableRow_def (nv stage : Nat) :
    hemJohnsonQromTableRow nv stage =
      hemJohnsonQromWitnessTable.find? (fun r => r.1 == nv && r.2.1 == stage) := by rfl

theorem hemJohnsonQromWitnessTable_def :
    hemJohnsonQromWitnessTable =
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
        (24, 3, 4482, 16, 2067) ] := by rfl

/-- **Three-challenge table certificate.** Kernel-decided over the deployed tables: every
    non-exhaustive canonical `BciksJohnsonQrom128` stage (`num_vars ∈ 2..=24`) has a deployed row
    `r` and a `slicedStageTable` row `w` passing `slicedParamsOk`, and the three-challenge count
    `q·(Dy + slicedRest) + J(d)²·q² + J(d+1)²·q²` at `d = g.d - 1`, `A = r.A - 1` is at most
    `q³ / 2^184`. `jb` is the Johnson bound `n (B - t) / (B² - n t)` and `q = p⁴`; both are
    parameters constrained by their defining equations, so a downstream module can instantiate
    them with its own names for these two quantities. -/
theorem sliced_three_challenge_table_certificate
    (jb : Nat → Nat → Nat → Nat)
    (hjb : ∀ n B t : Nat, jb n B t = (n * (B - t)) / (B * B - n * t))
    (q : Nat) (hq : q = goldilocksPrime ^ 4)
    (nv : Nat) (h2 : 2 ≤ nv) (h24 : nv ≤ 24)
    (g : HemStageGeom) (hg : g ∈ hemStageGeoms nv)
    (hne : hemJohnsonQromStageExhaustive g = false) :
    ∃ (r : Nat × Nat × Nat × Nat × Nat) (w : Nat × Nat × Nat × Nat),
      hemJohnsonQromTableRow nv g.stageIdx = some r ∧
      slicedStageRow nv g.stageIdx = some w ∧
      2 ≤ g.d ∧ g.d + 1 ≤ r.2.2.1 - 1 ∧
      slicedParamsOk g.n g.d r.2.2.1 w.2.2.1 r.2.2.2.1 r.2.2.2.2 = true ∧
      ((q * (r.2.2.2.2 + slicedRest g.n ((g.d - 1) + 1) ((r.2.2.1 - 1) + 1) w.2.2.1
              (r.2.2.2.1 * ((r.2.2.1 - 1) + 1) - r.2.2.2.2) r.2.2.2.2 q) +
            (jb g.n (r.2.2.1 - 1) (g.d - 1) * jb g.n (r.2.2.1 - 1) (g.d - 1)) * (q * q) +
            (jb g.n (r.2.2.1 - 1) ((g.d - 1) + 1) * jb g.n (r.2.2.1 - 1) ((g.d - 1) + 1)) * (q * q)) * 2 ^ 184 ≤
          q * (q * q)) := by
  obtain rfl : jb = (fun n B t : Nat => (n * (B - t)) / (B * B - n * t)) :=
    funext fun n => funext fun B => funext fun t => hjb n B t
  subst hq
  have hAll : ((List.range 23).all fun i =>
      (hemStageGeoms (i + 2)).all (fun g =>
        if hemJohnsonQromStageExhaustive g = true then true
        else
          match hemJohnsonQromTableRow (i + 2) g.stageIdx, slicedStageRow (i + 2) g.stageIdx with
          | some r, some w =>
            decide (2 ≤ g.d) && decide (g.d + 1 ≤ r.2.2.1 - 1) &&
            slicedParamsOk g.n g.d r.2.2.1 w.2.2.1 r.2.2.2.1 r.2.2.2.2 &&
            decide (((goldilocksPrime ^ 4) * (r.2.2.2.2 + slicedRest g.n ((g.d - 1) + 1) ((r.2.2.1 - 1) + 1) w.2.2.1
              (r.2.2.2.1 * ((r.2.2.1 - 1) + 1) - r.2.2.2.2) r.2.2.2.2 (goldilocksPrime ^ 4)) +
            ((fun n B t : Nat => (n * (B - t)) / (B * B - n * t)) g.n (r.2.2.1 - 1) (g.d - 1) * (fun n B t : Nat => (n * (B - t)) / (B * B - n * t)) g.n (r.2.2.1 - 1) (g.d - 1)) * ((goldilocksPrime ^ 4) * (goldilocksPrime ^ 4)) +
            ((fun n B t : Nat => (n * (B - t)) / (B * B - n * t)) g.n (r.2.2.1 - 1) ((g.d - 1) + 1) * (fun n B t : Nat => (n * (B - t)) / (B * B - n * t)) g.n (r.2.2.1 - 1) ((g.d - 1) + 1)) * ((goldilocksPrime ^ 4) * (goldilocksPrime ^ 4))) * 2 ^ 184 ≤
          (goldilocksPrime ^ 4) * ((goldilocksPrime ^ 4) * (goldilocksPrime ^ 4)))
          | _, _ => false)) = true := by
    decide +kernel
  have h1 := List.all_eq_true.mp hAll (nv - 2) (List.mem_range.mpr (by omega))
  have hEq : nv - 2 + 2 = nv := by omega
  rw [hEq] at h1
  have hc := List.all_eq_true.mp h1 g hg
  simp only [hne, Bool.false_eq_true, ↓reduceIte] at hc
  split at hc
  · next r w hr hw =>
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hc
    exact ⟨r, w, hr, hw, of_decide_eq_true hc.1.1.1, of_decide_eq_true hc.1.1.2, hc.1.2,
      of_decide_eq_true hc.2⟩
  · exact absurd hc Bool.false_ne_true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Kernel-decided bivariate Hasse Guruswami–Sudan interpolation dimensions at both `(g.d - 1,
    r.A - 1)` and `(g.d, r.A)` across all non-exhaustive stages of `nv ∈ 2..=24`. -/
theorem hem_gs_stage_row_dimensions_nv2_to_24
    (nv : Nat) (h2 : 2 ≤ nv) (h24 : nv ≤ 24)
    (g : HemStageGeom) (hg : g ∈ hemStageGeoms nv)
    (hne : hemJohnsonQromStageExhaustive g = false) :
    ∃ r : Nat × Nat × Nat × Nat × Nat,
      hemJohnsonQromTableRow nv g.stageIdx = some r ∧
      r.2.2.1 ≤ g.n ∧
      g.n * (r.2.2.2.1 * (r.2.2.2.1 + 1) / 2) <
        gsMonomialCount (r.2.2.2.1 * (r.2.2.1 - 1)) (g.d - 1)
          (Nat.min r.2.2.2.2 ((r.2.2.2.1 * (r.2.2.1 - 1) - 1) / (g.d - 1))) ∧
      g.n * (r.2.2.2.1 * (r.2.2.2.1 + 1) / 2) <
        gsMonomialCount (r.2.2.2.1 * r.2.2.1) g.d
          (Nat.min r.2.2.2.2 ((r.2.2.2.1 * r.2.2.1 - 1) / g.d)) := by
  have hAll : ((List.range 23).all fun i =>
      (hemStageGeoms (i + 2)).all (fun g =>
        if hemJohnsonQromStageExhaustive g = true then true
        else
          match hemJohnsonQromTableRow (i + 2) g.stageIdx with
          | some r =>
            decide (r.2.2.1 ≤ g.n) &&
            decide (g.n * (r.2.2.2.1 * (r.2.2.2.1 + 1) / 2) <
              gsMonomialCount (r.2.2.2.1 * (r.2.2.1 - 1)) (g.d - 1)
                (Nat.min r.2.2.2.2 ((r.2.2.2.1 * (r.2.2.1 - 1) - 1) / (g.d - 1)))) &&
            decide (g.n * (r.2.2.2.1 * (r.2.2.2.1 + 1) / 2) <
              gsMonomialCount (r.2.2.2.1 * r.2.2.1) g.d
                (Nat.min r.2.2.2.2 ((r.2.2.2.1 * r.2.2.1 - 1) / g.d)))
          | none => false)) = true := by
    decide +kernel
  have h1 := List.all_eq_true.mp hAll (nv - 2) (List.mem_range.mpr (by omega))
  have hEq : nv - 2 + 2 = nv := by omega
  rw [hEq] at h1
  have hc := List.all_eq_true.mp h1 g hg
  simp only [hne, Bool.false_eq_true, ↓reduceIte] at hc
  cases hr : hemJohnsonQromTableRow nv g.stageIdx with
  | none => rw [hr] at hc; exact absurd hc Bool.false_ne_true
  | some r =>
    rw [hr] at hc
    dsimp only at hc
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc
    exact ⟨r, rfl, of_decide_eq_true hc.1.1, of_decide_eq_true hc.1.2, of_decide_eq_true hc.2⟩

/-- **Multi-fold table certificate.** Kernel-decided over the deployed tables: every
    non-exhaustive canonical `BciksJohnsonQrom128` stage (`num_vars ∈ 2..=24`) has `1..6` binary
    folds, passes `slicedParamsOk` at every intermediate fold geometry
    `(2^t n, 2^t (d - 2) + 1, 2^t (A - 2) + 2, stepB B t)`, and the sum over its folds of the
    four-challenge counts `q²·(Dy + slicedRest) + (3 J(d)² + J(d+1)²)·q³` is at most `q⁴ / 2^175`,
    and at most `q⁴ / 2^186` when the stage has at most four folds. `jb` (Johnson bound), `stepB`
    (intermediate persistent-agreement threshold) and `q = p⁴` are parameters constrained by
    their defining equations. -/
theorem sliced_multifold_table_certificate
    (jb : Nat → Nat → Nat → Nat)
    (hjb : ∀ n B t : Nat, jb n B t = (n * (B - t)) / (B * B - n * t))
    (stepB : Nat → Nat → Nat)
    (hStepB : ∀ B t : Nat, stepB B t = if t = 0 then B else 2 ^ t * (B - 2) + 3)
    (q : Nat) (hq : q = goldilocksPrime ^ 4)
    (nv : Nat) (h2 : 2 ≤ nv) (h24 : nv ≤ 24)
    (g : HemStageGeom) (hg : g ∈ hemStageGeoms nv)
    (hne : hemJohnsonQromStageExhaustive g = false) :
    ∃ (r : Nat × Nat × Nat × Nat × Nat) (w : Nat × Nat × Nat × Nat),
      hemJohnsonQromTableRow nv g.stageIdx = some r ∧
      slicedStageRow nv g.stageIdx = some w ∧
      (1 ≤ g.stepVars ∧ g.stepVars ≤ 6) ∧
      (1 ≤ g.d - 2 ∧ (g.d - 2) + 3 ≤ r.2.2.1) ∧
      (∀ t : Nat, t < g.stepVars →
        slicedParamsOk (2 ^ t * g.n) (2 ^ t * (g.d - 2) + 1)
            (2 ^ t * (r.2.2.1 - 2) + 2) (stepB w.2.2.1 t) r.2.2.2.1 r.2.2.2.2 = true) ∧
      ((List.range g.stepVars).map (fun t =>
            (q * q) * (r.2.2.2.2 + slicedRest (2 ^ t * g.n) ((2 ^ t * (g.d - 2)) + 1) ((2 ^ t * (r.2.2.1 - 2) + 1) + 1) (stepB w.2.2.1 t)
                (r.2.2.2.1 * ((2 ^ t * (r.2.2.1 - 2) + 1) + 1) - r.2.2.2.2) r.2.2.2.2 q) +
              (3 * (jb (2 ^ t * g.n) (2 ^ t * (r.2.2.1 - 2) + 1) (2 ^ t * (g.d - 2)) * jb (2 ^ t * g.n) (2 ^ t * (r.2.2.1 - 2) + 1) (2 ^ t * (g.d - 2))) +
                jb (2 ^ t * g.n) (2 ^ t * (r.2.2.1 - 2) + 1) ((2 ^ t * (g.d - 2)) + 1) * jb (2 ^ t * g.n) (2 ^ t * (r.2.2.1 - 2) + 1) ((2 ^ t * (g.d - 2)) + 1)) * (q ^ 3))).sum * 2 ^ 175 ≤ q ^ 4 ∧
      (g.stepVars ≤ 4 →
        ((List.range g.stepVars).map (fun t =>
            (q * q) * (r.2.2.2.2 + slicedRest (2 ^ t * g.n) ((2 ^ t * (g.d - 2)) + 1) ((2 ^ t * (r.2.2.1 - 2) + 1) + 1) (stepB w.2.2.1 t)
                (r.2.2.2.1 * ((2 ^ t * (r.2.2.1 - 2) + 1) + 1) - r.2.2.2.2) r.2.2.2.2 q) +
              (3 * (jb (2 ^ t * g.n) (2 ^ t * (r.2.2.1 - 2) + 1) (2 ^ t * (g.d - 2)) * jb (2 ^ t * g.n) (2 ^ t * (r.2.2.1 - 2) + 1) (2 ^ t * (g.d - 2))) +
                jb (2 ^ t * g.n) (2 ^ t * (r.2.2.1 - 2) + 1) ((2 ^ t * (g.d - 2)) + 1) * jb (2 ^ t * g.n) (2 ^ t * (r.2.2.1 - 2) + 1) ((2 ^ t * (g.d - 2)) + 1)) * (q ^ 3))).sum * 2 ^ 186 ≤ q ^ 4) := by
  obtain rfl : jb = (fun n B t : Nat => (n * (B - t)) / (B * B - n * t)) :=
    funext fun n => funext fun B => funext fun t => hjb n B t
  obtain rfl : stepB = (fun B t : Nat => if t = 0 then B else 2 ^ t * (B - 2) + 3) :=
    funext fun B => funext fun t => hStepB B t
  subst hq
  have hAll : ((List.range 23).all fun i =>
      (hemStageGeoms (i + 2)).all (fun g =>
        if hemJohnsonQromStageExhaustive g = true then true
        else
          match hemJohnsonQromTableRow (i + 2) g.stageIdx, slicedStageRow (i + 2) g.stageIdx with
          | some r, some w =>
            decide (1 ≤ g.stepVars ∧ g.stepVars ≤ 6) &&
            decide (1 ≤ g.d - 2 ∧ (g.d - 2) + 3 ≤ r.2.2.1) &&
            (List.range g.stepVars).all (fun t =>
              slicedParamsOk (2 ^ t * g.n) (2 ^ t * (g.d - 2) + 1)
            (2 ^ t * (r.2.2.1 - 2) + 2) ((fun B t : Nat => if t = 0 then B else 2 ^ t * (B - 2) + 3) w.2.2.1 t) r.2.2.2.1 r.2.2.2.2) &&
            decide (((List.range g.stepVars).map (fun t =>
            ((goldilocksPrime ^ 4) * (goldilocksPrime ^ 4)) * (r.2.2.2.2 + slicedRest (2 ^ t * g.n) ((2 ^ t * (g.d - 2)) + 1) ((2 ^ t * (r.2.2.1 - 2) + 1) + 1) ((fun B t : Nat => if t = 0 then B else 2 ^ t * (B - 2) + 3) w.2.2.1 t)
                (r.2.2.2.1 * ((2 ^ t * (r.2.2.1 - 2) + 1) + 1) - r.2.2.2.2) r.2.2.2.2 (goldilocksPrime ^ 4)) +
              (3 * ((fun n B t : Nat => (n * (B - t)) / (B * B - n * t)) (2 ^ t * g.n) (2 ^ t * (r.2.2.1 - 2) + 1) (2 ^ t * (g.d - 2)) * (fun n B t : Nat => (n * (B - t)) / (B * B - n * t)) (2 ^ t * g.n) (2 ^ t * (r.2.2.1 - 2) + 1) (2 ^ t * (g.d - 2))) +
                (fun n B t : Nat => (n * (B - t)) / (B * B - n * t)) (2 ^ t * g.n) (2 ^ t * (r.2.2.1 - 2) + 1) ((2 ^ t * (g.d - 2)) + 1) * (fun n B t : Nat => (n * (B - t)) / (B * B - n * t)) (2 ^ t * g.n) (2 ^ t * (r.2.2.1 - 2) + 1) ((2 ^ t * (g.d - 2)) + 1)) * ((goldilocksPrime ^ 4) ^ 3))).sum * 2 ^ 175 ≤ (goldilocksPrime ^ 4) ^ 4) &&
            decide (g.stepVars ≤ 4 →
              ((List.range g.stepVars).map (fun t =>
            ((goldilocksPrime ^ 4) * (goldilocksPrime ^ 4)) * (r.2.2.2.2 + slicedRest (2 ^ t * g.n) ((2 ^ t * (g.d - 2)) + 1) ((2 ^ t * (r.2.2.1 - 2) + 1) + 1) ((fun B t : Nat => if t = 0 then B else 2 ^ t * (B - 2) + 3) w.2.2.1 t)
                (r.2.2.2.1 * ((2 ^ t * (r.2.2.1 - 2) + 1) + 1) - r.2.2.2.2) r.2.2.2.2 (goldilocksPrime ^ 4)) +
              (3 * ((fun n B t : Nat => (n * (B - t)) / (B * B - n * t)) (2 ^ t * g.n) (2 ^ t * (r.2.2.1 - 2) + 1) (2 ^ t * (g.d - 2)) * (fun n B t : Nat => (n * (B - t)) / (B * B - n * t)) (2 ^ t * g.n) (2 ^ t * (r.2.2.1 - 2) + 1) (2 ^ t * (g.d - 2))) +
                (fun n B t : Nat => (n * (B - t)) / (B * B - n * t)) (2 ^ t * g.n) (2 ^ t * (r.2.2.1 - 2) + 1) ((2 ^ t * (g.d - 2)) + 1) * (fun n B t : Nat => (n * (B - t)) / (B * B - n * t)) (2 ^ t * g.n) (2 ^ t * (r.2.2.1 - 2) + 1) ((2 ^ t * (g.d - 2)) + 1)) * ((goldilocksPrime ^ 4) ^ 3))).sum * 2 ^ 186 ≤ (goldilocksPrime ^ 4) ^ 4)
          | _, _ => false)) = true := by
    decide +kernel
  have h1 := List.all_eq_true.mp hAll (nv - 2) (List.mem_range.mpr (by omega))
  have hEq : nv - 2 + 2 = nv := by omega
  rw [hEq] at h1
  have hc := List.all_eq_true.mp h1 g hg
  simp only [hne, Bool.false_eq_true, ↓reduceIte] at hc
  split at hc
  · next r w hr hw =>
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hc
    exact ⟨r, w, hr, hw, of_decide_eq_true hc.1.1.1.1, of_decide_eq_true hc.1.1.1.2,
      fun t ht => List.all_eq_true.mp hc.1.1.2 t (List.mem_range.mpr ht),
      of_decide_eq_true hc.1.2, of_decide_eq_true hc.2⟩
  · exact absurd hc Bool.false_ne_true

-- (end exports for lane agg-budget)

/-! ### Exports for lane agg-whir-cert -/

theorem hemStageGeomsAux_nil (idx rem : Nat) : hemStageGeomsAux idx rem [] = [] := by rfl

theorem hemStageGeomsAux_cons (idx rem lb sv : Nat) (rest : List (Nat × Nat)) :
    hemStageGeomsAux idx rem ((lb, sv) :: rest) =
      { stageIdx := idx, logBlowup := lb, stepVars := sv,
        n := 2 ^ lb * 2 ^ (rem - sv), d := 2 ^ (rem - sv) + 2 } ::
        hemStageGeomsAux (idx + 1) (rem - sv) rest := by rfl

theorem hemStageGeoms_def (nv : Nat) :
    hemStageGeoms nv = hemStageGeomsAux 0 nv (hemStageGeometry nv) := by rfl

theorem hemJohnsonQromStageExhaustive_def (g : HemStageGeom) :
    hemJohnsonQromStageExhaustive g = decide (g.n ≤ hemJohnsonMinQueries true g.logBlowup) := by rfl

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

theorem slicedStageCount_def (q : Nat) (g : HemStageGeom) (r : Nat × Nat × Nat × Nat × Nat)
    (w : Nat × Nat × Nat × Nat) :
    slicedStageCount q g r w =
      r.2.2.2.2 +
        slicedRest g.n g.d r.2.2.1 w.2.2.1 (r.2.2.2.1 * r.2.2.1 - r.2.2.2.2) r.2.2.2.2 q := by rfl
-- (end exports for lane agg-whir-cert)

end Qsag
end

public section
namespace Qsag
theorem slicedStageRow_def (nv stage : Nat) :
    slicedStageRow nv stage = slicedStageTable.find? (fun r => r.1 == nv && r.2.1 == stage) := by rfl
theorem slicedStageTable_def : slicedStageTable =
  [
    (9, 1, 70, 234),
    (10, 0, 259, 235),
    (10, 1, 70, 234),
    (11, 0, 259, 235),
    (11, 1, 70, 234),
    (12, 0, 515, 224),
    (12, 1, 262, 224),
    (12, 2, 140, 219),
    (13, 0, 1027, 218),
    (13, 1, 518, 213),
    (13, 2, 140, 219),
    (14, 0, 2051, 207),
    (14, 1, 1030, 207),
    (14, 2, 268, 208),
    (15, 0, 4099, 201),
    (15, 1, 1030, 207),
    (15, 2, 268, 208),
    (16, 0, 8195, 194),
    (16, 1, 2054, 200),
    (16, 2, 524, 202),
    (17, 0, 8195, 194),
    (17, 1, 2054, 200),
    (17, 2, 268, 208),
    (18, 0, 16387, 192),
    (18, 1, 4102, 198),
    (18, 2, 524, 202),
    (19, 0, 32771, 190),
    (19, 1, 8198, 195),
    (19, 2, 1036, 204),
    (20, 0, 65539, 187),
    (20, 1, 16390, 198),
    (20, 2, 2060, 201),
    (21, 0, 65539, 187),
    (21, 1, 16390, 198),
    (21, 2, 2060, 201),
    (22, 0, 131075, 184),
    (22, 1, 16390, 198),
    (22, 2, 2060, 201),
    (23, 0, 262147, 187),
    (23, 1, 32774, 195),
    (23, 2, 8204, 201),
    (23, 3, 2072, 199),
    (24, 0, 524291, 185),
    (24, 1, 65542, 192),
    (24, 2, 16396, 198),
    (24, 3, 4120, 201) ] := by rfl
end Qsag
end
