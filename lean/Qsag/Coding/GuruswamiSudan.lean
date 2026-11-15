module
public import Qsag.Coding.Resultant
public import Qsag.Tactic.Prelude

public section
namespace Qsag
set_option autoImplicit false
open RoundPoly


/-- A nonzero bivariate polynomial of Y-degree at most D has at most D distinct polynomial
    roots. Synthetic division works directly in the integral domain `F[X]`; a fraction-field
    construction is unnecessary. Equality here is formal polynomial equality, not pointwise
    equality as functions on a finite field. -/
theorem guruswami_sudan_polynomial_list_bound {F : Type} [LawfulField F] [DecidableEq F]
    (D : Nat) (Q : List (GsUniPoly F)) (polys : List (GsUniPoly F))
    (hdeg : Q.length ≤ D + 1)
    (hnz : ∃ c ∈ Q, c ≠ CommRingOps.zero)
    (hDistinct : polys.Nodup)
    (hRoots : ∀ P ∈ polys, evalCoeffs Q P = CommRingOps.zero) :
    polys.length ≤ D :=
  gs_formal_root_bound D Q polys hdeg hnz hDistinct hRoots

/-- Formal weighted-degree condition on the coefficient polynomials of `Q(X,Y)`. -/
def GsWeightedDegree {F : Type} [LawfulField F] [DecidableEq F]
    (Q : List (GsUniPoly F)) (d B : Nat) : Prop :=
  ∀ (j : Nat) (c : GsUniPoly F), Q[j]? = some c → c.coeffs.length ≤ B - j * d

/-- Substitution of a degree-at-most-d polynomial into a bivariate polynomial of weighted
    degree below B has formal univariate degree below B, including all zero-polynomial cases. -/
theorem gs_substitution_length {F : Type} [LawfulField F] [DecidableEq F]
    (P : GsUniPoly F) (d : Nat) (hP : P.coeffs.length ≤ d + 1) :
    ∀ (Q : List (GsUniPoly F)) (B : Nat), GsWeightedDegree Q d B →
      (evalCoeffs Q P).coeffs.length ≤ B
  | [], _, _ => by simp only [evalCoeffs_nil, UPoly.coeffs_zero, List.length_nil]; exact Nat.zero_le _
  | c :: cs, B, hW => by
    have hc : c.coeffs.length ≤ B := by
      have h := hW 0 c rfl
      simpa only [Nat.zero_mul, Nat.sub_zero] using h
    have ht : GsWeightedDegree cs d (B - d) := by
      intro j a ha
      have h := hW (j + 1) a ha
      simpa only [Nat.add_mul, Nat.one_mul, Nat.sub_sub, Nat.add_comm] using h
    have hi := gs_substitution_length P d hP cs (B - d) ht
    change (pAdd c.coeffs (pMul P.coeffs (evalCoeffs cs P).coeffs)).length ≤ B
    apply pAdd_length_le _ _ B hc
    if hz : B ≤ d then
      have he : (evalCoeffs cs P).coeffs = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [he, pMul_comm, pMul_nil_left_eq]
      exact Nat.zero_le _
    else
      have hm := pMul_length_le P.coeffs (evalCoeffs cs P).coeffs d (B - d - 1)
        hP (by omega)
      omega

/-- Evaluation commutes with bivariate substitution. -/
theorem gs_eval_substitution {F : Type} [LawfulField F] [DecidableEq F]
    (P : GsUniPoly F) (x : F) : ∀ (Q : List (GsUniPoly F)),
    evalCoeffs (evalCoeffs Q P).coeffs x =
      evalCoeffs (Q.map (fun c => evalCoeffs c.coeffs x)) (evalCoeffs P.coeffs x)
  | [] => by simp only [evalCoeffs_nil, UPoly.coeffs_zero, List.map_nil]
  | c :: cs => by
    change evalCoeffs (pAdd c.coeffs (pMul P.coeffs (evalCoeffs cs P).coeffs)) x = _
    rw [evalCoeffs_pAdd, evalCoeffs_pMul, gs_eval_substitution P x cs]
    rfl

/-- Sudan's multiplicity-one factor theorem, beyond the unique-decoding radius. All
    agreement points are distinct, and their number reaches the weighted-degree threshold. -/
theorem sudan_factor {F : Type} [LawfulField F] [DecidableEq F]
    (Q : List (GsUniPoly F)) (P : GsUniPoly F) (d B : Nat)
    (hP : P.coeffs.length ≤ d + 1) (hW : GsWeightedDegree Q d B)
    (xs : List F) (ys : F → F) (hDistinct : xs.Nodup) (hCount : B ≤ xs.length)
    (hAgree : ∀ x ∈ xs, evalCoeffs P.coeffs x = ys x)
    (hZero : ∀ x ∈ xs, evalCoeffs (Q.map (fun c => evalCoeffs c.coeffs x)) (ys x) = CommRingOps.zero) :
    evalCoeffs Q P = CommRingOps.zero := by
  letI : NoZeroDivisors F := LawfulField.toNoZeroDivisors F
  have hlen := gs_substitution_length P d hP Q B hW
  let g := (evalCoeffs Q P).coeffs
  have hRoots : ∀ x ∈ xs, evalCoeffs g x = CommRingOps.zero := by
    intro x hx
    rw [gs_eval_substitution, hAgree x hx]
    exact hZero x hx
  have hz : trimPoly g = [] := by
    if he : trimPoly g = [] then exact he else
      have hNonzero : ∃ c ∈ g, c ≠ CommRingOps.zero := by
        cases ht : g.any (fun c => decide (c ≠ CommRingOps.zero)) with
        | true =>
          obtain ⟨c, hc, hn⟩ := List.any_eq_true.mp ht
          exact ⟨c, hc, of_decide_eq_true hn⟩
        | false =>
          have hall : ∀ c ∈ g, c = CommRingOps.zero := by
            intro c hc
            have h := List.any_eq_false.mp ht c hc
            simpa only [decide_eq_true_eq, Decidable.not_not] using h
          have hallcoeff : ∀ k, coeffAt g k = CommRingOps.zero := by
            intro k
            rw [coeffAt_eq_getD]
            rw [List.getD_eq_getElem?_getD]
            cases hk : g[k]? with
            | none => rfl
            | some c => exact hall c (List.mem_of_getElem? hk)
          exact False.elim (he ((trimPoly_eq_nil_iff g).mpr hallcoeff))
      have hpos : 0 < B := by
        obtain ⟨c, hc, _⟩ := hNonzero
        have := List.length_pos_of_mem hc
        change g.length ≤ B at hlen
        omega
      have hbound := gs_formal_root_bound (B - 1) g xs (by dsimp [g]; omega)
        hNonzero hDistinct hRoots
      omega
  apply UPoly.ext
  rw [UPoly.coeffs_zero]
  exact (evalCoeffs Q P).trimmed.symm.trans hz

/-- Sudan factor and list bound for an arbitrary list of distinct candidate polynomials.
    Candidate-specific agreement sets need not be supplied in the protocol transcript. -/
theorem sudan_factor_and_list_bound {F : Type} [LawfulField F] [DecidableEq F]
    (Q : List (GsUniPoly F)) (polys : List (GsUniPoly F)) (d B D : Nat)
    (hQ : Q.length ≤ D + 1) (hnz : ∃ c ∈ Q, c ≠ CommRingOps.zero)
    (hW : GsWeightedDegree Q d B) (hDistinct : polys.Nodup)
    (ys : F → F)
    (hCandidates : ∀ P ∈ polys, P.coeffs.length ≤ d + 1 ∧
      ∃ xs : List F, xs.Nodup ∧ B ≤ xs.length ∧
        (∀ x ∈ xs, evalCoeffs P.coeffs x = ys x) ∧
        (∀ x ∈ xs, evalCoeffs (Q.map (fun c => evalCoeffs c.coeffs x)) (ys x) = CommRingOps.zero)) :
    (∀ P ∈ polys, evalCoeffs Q P = CommRingOps.zero) ∧ polys.length ≤ D := by
  have hf : ∀ P ∈ polys, evalCoeffs Q P = CommRingOps.zero := by
    intro P hP
    obtain ⟨hdeg, xs, hxs, hcount, hagree, hzero⟩ := hCandidates P hP
    exact sudan_factor Q P d B hdeg hW xs ys hxs hcount hagree hzero
  exact ⟨hf, guruswami_sudan_polynomial_list_bound D Q polys hQ hnz hDistinct hf⟩

/-! ## Constructive bivariate Hasse interpolation -/

/-- Distinct monomial positions of `(1,d)`-weighted degree strictly below `B`, with Y degree ≤ D. -/
def gsMonomials (B d D : Nat) : List (Nat × Nat) :=
  (List.range (D + 1)).flatMap (fun j => (List.range (B - j * d)).map (fun i => (i, j)))

/-- Exact interpolation dimension, including empty columns. -/
@[expose] def gsMonomialCount (B d D : Nat) : Nat :=
  ((List.range (D + 1)).map (fun j => B - j * d)).sum

theorem gsMonomials_length (B d D : Nat) :
    (gsMonomials B d D).length = gsMonomialCount B d D := by
  simp [gsMonomials, gsMonomialCount, List.length_flatMap]

theorem gsMonomials_weight (B d D : Nat) (e : Nat × Nat)
    (he : e ∈ gsMonomials B d D) : e.1 + e.2 * d < B ∧ e.2 ≤ D := by
  obtain ⟨j, hj, he⟩ := List.mem_flatMap.mp he
  obtain ⟨i, hi, heq⟩ := List.mem_map.mp he
  have hjlt := List.mem_range.mp hj
  have hilt := List.mem_range.mp hi
  cases heq
  exact ⟨Nat.add_lt_of_lt_sub hilt, Nat.le_of_lt_succ hjlt⟩

theorem gsMonomials_nodup (B d D : Nat) : (gsMonomials B d D).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro j _
    apply List.pairwise_map.mpr
    exact (Qsag.Constructive.nodup_range _).imp (fun h he => h (congrArg Prod.fst he))
  · apply (Qsag.Constructive.nodup_range _).imp
    intro a b hab x hx y hy heq
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hy
    exact hab (congrArg Prod.snd heq)

/-- Hasse orders of total degree strictly below `m`. -/
def gsHasseOrders : Nat → List (Nat × Nat)
  | 0 => []
  | m + 1 => (List.range (m + 1)).map (fun s => (0, s)) ++
      (gsHasseOrders m).map (fun e => (e.1 + 1, e.2))

theorem gsHasseOrders_length : ∀ m : Nat,
    2 * (gsHasseOrders m).length = m * (m + 1)
  | 0 => rfl
  | m + 1 => by
    simp only [gsHasseOrders, List.length_append, List.length_map, List.length_range,
      Nat.mul_add, gsHasseOrders_length m, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega

theorem gsHasseOrders_mem : ∀ (m : Nat) (e : Nat × Nat),
    e ∈ gsHasseOrders m ↔ e.1 + e.2 < m
  | 0, e => by simp [gsHasseOrders]
  | m + 1, (0, s) => by
    simp [gsHasseOrders, List.mem_map, List.mem_range]
  | m + 1, (r + 1, s) => by
    simp only [gsHasseOrders, List.mem_append, List.mem_map, Prod.mk.injEq,
      Nat.zero_ne_add_one, false_and, and_false, exists_false, false_or]
    constructor
    · intro h
      obtain ⟨⟨a, b⟩, he, hab⟩ := h
      have := (gsHasseOrders_mem m (a, b)).mp he
      dsimp at this
      omega
    · intro h
      exact ⟨(r, s), (gsHasseOrders_mem m (r, s)).mpr (by dsimp; omega), rfl, rfl⟩

/-- Coefficients indexed by the distinct weighted monomials. Hasse evaluation is linear in
    these coefficients and therefore exactly the row used by Gaussian elimination. -/
def gsHasseEval {F : Type} [CommRingOps F] (B d D : Nat)
    (coeffs : List F) (order : Nat × Nat) (point : F × F) : F :=
  dotVec ((gsMonomials B d D).map (fun e => gsHasseMonomial e order point)) coeffs

/-- The entire homogeneous Hasse system; each point contributes `m(m+1)/2` equations. -/
def gsInterpolationRows {F : Type} [CommRingOps F] (B d D m : Nat)
    (points : List (F × F)) : List (List F) :=
  points.flatMap (fun p => (gsHasseOrders m).map (fun order =>
    (gsMonomials B d D).map (fun e => gsHasseMonomial e order p)))

theorem gsInterpolationRows_length {F : Type} [CommRingOps F]
    (B d D m : Nat) (points : List (F × F)) :
    (gsInterpolationRows B d D m points).length = points.length * (m * (m + 1) / 2) := by
  have hc : (gsHasseOrders m).length = m * (m + 1) / 2 := by
    have := gsHasseOrders_length m
    omega
  induction points with
  | nil => simp [gsInterpolationRows]
  | cons p ps ih =>
    simp only [gsInterpolationRows, List.flatMap_cons, List.length_append, List.length_map,
      List.length_cons, Nat.add_mul, Nat.one_mul] at ih ⊢
    rw [ih, hc, Nat.add_comm]

/-- Constructive Guruswami–Sudan interpolation for arbitrary decidable fields. The returned
    coefficient vector has a nonzero coordinate and all formal Hasse derivatives of total order
    below `m` vanish at every input point. The witness is the executable Gaussian solver. -/
theorem guruswami_sudan_interpolation {F : Type} [LawfulField F] [DecidableEq F]
    (B d D m : Nat) (points : List (F × F))
    (hDim : points.length * (m * (m + 1) / 2) < gsMonomialCount B d D) :
    let coeffs := solveHomogeneous (gsMonomialCount B d D) (gsInterpolationRows B d D m points)
    coeffs.length = gsMonomialCount B d D ∧
    coeffs.any (fun c => !(decide (c = CommRingOps.zero))) = true ∧
    ∀ p ∈ points, ∀ r s, r + s < m → gsHasseEval B d D coeffs (r, s) p = CommRingOps.zero := by
  have h := gauss_nullspace_witness (gsMonomialCount B d D)
    (gsInterpolationRows B d D m points)
    (by rw [gsInterpolationRows_length]; exact hDim) (by
      intro row hr
      obtain ⟨p, _, hr⟩ := List.mem_flatMap.mp hr
      obtain ⟨order, _, rfl⟩ := List.mem_map.mp hr
      simp only [List.length_map, gsMonomials_length])
  refine ⟨h.1, h.2.1, ?_⟩
  intro p hp r s hrs
  apply h.2.2
  apply List.mem_flatMap.mpr
  refine ⟨p, hp, ?_⟩
  exact List.mem_map.mpr ⟨(r, s), (gsHasseOrders_mem m (r, s)).mpr hrs, rfl⟩

/-! ## Guruswami–Sudan factor theorem at arbitrary multiplicity -/

/-- `Q ∈ (X - a, Y - b)^m`. After the Taylor shift `Y ↦ Y - b` (coefficients
    `gsTaylor Q.length Q (gsConst b)`, the Hasse derivatives of `Q` in `Y` at `b`), the
    coefficient of `(Y - b)^s` is divisible by `(X - a)^(m - s)` for every `s < m`; equivalently
    every mixed Hasse derivative of total order below `m` vanishes at `(a, b)`. The condition
    mentions no candidate polynomial. -/
def GsMultiplicity {F : Type} [LawfulField F] [DecidableEq F]
    (Q : List (GsUniPoly F)) (m : Nat) (a b : F) : Prop :=
  ∀ s : Nat, s < m → ∃ h : GsUniPoly F,
    coeffAt (gsTaylor Q.length Q (gsConst b)) s =
      CommRingOps.mul (gsPow (gsLinear a) (m - s)) h

/-- `GsMultiplicity` is inhabited at every multiplicity by the nonzero polynomial `(X - a)^m`. -/
theorem gsMultiplicity_linear_power {F : Type} [LawfulField F] [DecidableEq F]
    (m : Nat) (a b : F) : GsMultiplicity [gsPow (gsLinear a) m] m a b := by
  unfold GsMultiplicity
  intro s _
  have hT : gsTaylor [gsPow (gsLinear a) m].length [gsPow (gsLinear a) m] (gsConst b) =
      [evalCoeffs [gsPow (gsLinear a) m] (gsConst b)] := by simp only [List.length_cons, List.length_nil, gsTaylor_succ, gsTaylor_zero]
  rw [hT]
  cases s with
  | zero =>
    refine ⟨CommRingOps.one, ?_⟩
    rw [coeffAt_cons_zero, Nat.sub_zero, LawfulCommRing.mul_one]
    simp only [evalCoeffs_cons, evalCoeffs_nil, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | succ _ =>
    refine ⟨CommRingOps.zero, ?_⟩
    rw [coeffAt_cons_succ, coeffAt_nil, LawfulCommRing.mul_zero]

/-- **Guruswami–Sudan factor theorem at arbitrary multiplicity.** Let `Q(X, Y)` have
    `(1, d)`-weighted degree below `B` and lie in `(X - x, Y - ys x)^m` at each of `A` distinct
    points `x`, with `B ≤ m * A`. Every polynomial `P` of degree at most `d` passing through
    those points satisfies `Q(X, P(X)) = 0` formally. The substitution `Y - ys x = (X - x) · u`
    turns the ideal-power hypothesis into `(X - x)^m ∣ Q(X, P(X))`; distinct linear factors are
    coprime, so the nonzero case would need more than `m * A ≥ B` coefficients. Multiplicity
    one is `sudan_factor`. -/
theorem guruswami_sudan_factor {F : Type} [LawfulField F] [DecidableEq F]
    (Q : List (GsUniPoly F)) (P : GsUniPoly F) (d B m : Nat)
    (hP : P.coeffs.length ≤ d + 1) (hW : GsWeightedDegree Q d B)
    (xs : List F) (ys : F → F) (hDistinct : xs.Nodup) (hCount : B ≤ m * xs.length)
    (hAgree : ∀ x ∈ xs, evalCoeffs P.coeffs x = ys x)
    (hMult : ∀ x ∈ xs, GsMultiplicity Q m x (ys x)) :
    evalCoeffs Q P = CommRingOps.zero := by
  have hlen := gs_substitution_length P d hP Q B hW
  have hdiv : ∀ x ∈ xs, ∃ k : GsUniPoly F,
      evalCoeffs Q P = CommRingOps.mul (gsPow (gsLinear x) m) k := by
    intro x hx
    have hc : evalCoeffs [ys x] x = ys x := by
      simp only [evalCoeffs_cons, evalCoeffs_nil, LawfulCommRing.mul_zero,
        LawfulCommRing.add_zero]
    have hroot : evalCoeffs (CommRingOps.sub P (gsConst (ys x))).coeffs x = CommRingOps.zero := by
      rw [UPoly.coeffs_sub, gsConst_coeffs]
      show evalCoeffs (pSub P.coeffs (trimPoly [ys x])) x = CommRingOps.zero
      rw [evalCoeffs_pSub, evalCoeffs_trimPoly, hAgree x hx, hc, LawfulCommRing.sub_self]
    obtain ⟨u, hu⟩ := gsLinear_factor x _ hroot
    rw [gsTaylor_eval (gsConst (ys x)) P Q.length Q (Nat.le_refl _), hu]
    exact gs_low_order_divisible (gsLinear x) u _ m (hMult x hx)
  if hz : (evalCoeffs Q P).coeffs = [] then
    exact (UPoly.eq_zero_iff _).mpr hz
  else
    have hcl := gs_multiplicity_length m xs (evalCoeffs Q P) hDistinct hz hdiv
    exfalso
    omega

/-- Factor theorem and list bound at arbitrary multiplicity, for any list of distinct candidate
    polynomials. Candidate-specific agreement sets are existential, not transcript data. -/
theorem guruswami_sudan_factor_and_list_bound {F : Type} [LawfulField F] [DecidableEq F]
    (Q : List (GsUniPoly F)) (polys : List (GsUniPoly F)) (d B D m : Nat)
    (hQ : Q.length ≤ D + 1) (hnz : ∃ c ∈ Q, c ≠ CommRingOps.zero)
    (hW : GsWeightedDegree Q d B) (hDistinct : polys.Nodup)
    (ys : F → F)
    (hCandidates : ∀ P ∈ polys, P.coeffs.length ≤ d + 1 ∧
      ∃ xs : List F, xs.Nodup ∧ B ≤ m * xs.length ∧
        (∀ x ∈ xs, evalCoeffs P.coeffs x = ys x) ∧
        (∀ x ∈ xs, GsMultiplicity Q m x (ys x))) :
    (∀ P ∈ polys, evalCoeffs Q P = CommRingOps.zero) ∧ polys.length ≤ D := by
  have hf : ∀ P ∈ polys, evalCoeffs Q P = CommRingOps.zero := by
    intro P hP
    obtain ⟨hdeg, xs, hxs, hcount, hagree, hmult⟩ := hCandidates P hP
    exact guruswami_sudan_factor Q P d B m hdeg hW xs ys hxs hcount hagree hmult
  exact ⟨hf, guruswami_sudan_polynomial_list_bound D Q polys hQ hnz hDistinct hf⟩

/-- List-decoding form used by every deployed row (`B = m * A`, `D = gsDeployedYDegree`): a
    nonzero interpolant of `(1, d)`-weighted degree below `m * A` and multiplicity `m` at every
    point of the received word bounds, by its `Y`-degree, the number of distinct polynomials of
    degree at most `d` agreeing with the word on at least `A` domain points. -/
theorem guruswami_sudan_agreement_list_bound {F : Type} [LawfulField F] [DecidableEq F]
    (domain : List F) (word : F → F) (d A D m : Nat)
    (Q : List (GsUniPoly F)) (hQ : Q.length ≤ D + 1) (hnz : ∃ c ∈ Q, c ≠ CommRingOps.zero)
    (hW : GsWeightedDegree Q d (m * A))
    (hMult : ∀ x ∈ domain, GsMultiplicity Q m x (word x))
    (polys : List (GsUniPoly F)) (hDistinct : polys.Nodup)
    (hClose : ∀ P ∈ polys, P.coeffs.length ≤ d + 1 ∧
      ∃ xs : List F, xs.Nodup ∧ A ≤ xs.length ∧
        ∀ x ∈ xs, x ∈ domain ∧ evalCoeffs P.coeffs x = word x) :
    polys.length ≤ D := by
  refine (guruswami_sudan_factor_and_list_bound Q polys d (m * A) D m hQ hnz hW hDistinct
    word ?_).2
  intro P hP
  obtain ⟨hdeg, xs, hxs, hcount, hx⟩ := hClose P hP
  exact ⟨hdeg, xs, hxs, Nat.mul_le_mul_left m hcount, fun x h => (hx x h).2,
    fun x h => hMult x (hx x h).1⟩

/-! ## Characteristic-free Hasse-to-Taylor bridge & unconditional Guruswami–Sudan list bound -/

/-- Horner recursion for the `k`-th univariate formal Hasse derivative at `b`, valid over every
    commutative ring without binomial or factorial division. -/
def gsSliceByWidths {α : Type} : List Nat → List α → List (List α)
  | [], _ => []
  | w :: ws, xs => xs.take w :: gsSliceByWidths ws (xs.drop w)

/-- Assemble a flat `gsMonomials B d D` coefficient vector into a bivariate polynomial in `F[X][Y]`. -/
def gsAssembleBivariate {F : Type} [LawfulField F] [DecidableEq F]
    (B d D : Nat) (coeffs : List F) : List (GsUniPoly F) :=
  (gsSliceByWidths ((List.range (D + 1)).map (fun j => B - j * d)) coeffs).map GsUniPoly.ofCoeffs

private theorem gsSliceByWidths_length {α : Type} :
    ∀ (ws : List Nat) (xs : List α), (gsSliceByWidths ws xs).length = ws.length
  | [], _ => rfl
  | _ :: ws, xs => congrArg Nat.succ (gsSliceByWidths_length ws (xs.drop _))

private theorem gsSliceByWidths_getElem?_le {α : Type} :
    ∀ (ws : List Nat) (xs : List α) (j : Nat) (sl : List α) (w : Nat),
      (gsSliceByWidths ws xs)[j]? = some sl → ws[j]? = some w → sl.length ≤ w
  | [], _, _, _, _, hsl, _ => by simp [gsSliceByWidths] at hsl
  | w₀ :: _, xs, 0, sl, w, hsl, hw => by
    simp only [gsSliceByWidths, List.getElem?_cons_zero, Option.some.injEq] at hsl hw
    subst hsl; subst hw
    exact List.length_take_le w₀ xs
  | _ :: ws, xs, j + 1, sl, w, hsl, hw => by
    simp only [gsSliceByWidths, List.getElem?_cons_succ] at hsl hw
    exact gsSliceByWidths_getElem?_le ws (xs.drop _) j sl w hsl hw

private theorem gsSliceByWidths_flatten {α : Type} :
    ∀ (ws : List Nat) (xs : List α),
      xs.length = ws.sum → (gsSliceByWidths ws xs).flatten = xs
  | [], xs, h => List.eq_nil_of_length_eq_zero h ▸ rfl
  | w :: ws, xs, h => by
    simp only [List.sum_cons] at h
    have ih := gsSliceByWidths_flatten ws (xs.drop w) (by rw [List.length_drop]; omega)
    simp only [gsSliceByWidths, List.flatten_cons, ih, List.take_append_drop]

theorem gsAssembleBivariate_length {F : Type} [LawfulField F] [DecidableEq F]
    (B d D : Nat) (coeffs : List F) :
    (gsAssembleBivariate B d D coeffs).length = D + 1 := by
  simp [gsAssembleBivariate, gsSliceByWidths_length]

theorem gsAssembleBivariate_weightedDegree {F : Type} [LawfulField F] [DecidableEq F]
    (B d D : Nat) (coeffs : List F) :
    GsWeightedDegree (gsAssembleBivariate B d D coeffs) d B := by
  intro j c hj
  unfold gsAssembleBivariate at hj
  rw [List.getElem?_map] at hj
  cases hsl : (gsSliceByWidths ((List.range (D + 1)).map (fun k => B - k * d)) coeffs)[j]? with
  | none => rw [hsl] at hj; cases hj
  | some sl =>
    rw [hsl, Option.map_some, Option.some.injEq] at hj
    subst hj
    have hjLt : j < D + 1 := by
      have hlen := lt_length_of_getElem?_eq_some hsl
      rw [gsSliceByWidths_length, List.length_map, List.length_range] at hlen
      exact hlen
    have hw : ((List.range (D + 1)).map (fun k => B - k * d))[j]? = some (B - j * d) := by
      rw [List.getElem?_map, List.getElem?_range hjLt]
      rfl
    rw [GsUniPoly.ofCoeffs, UPoly.coeffs_ofList]
    exact Nat.le_trans (trimPoly_length_le sl) (gsSliceByWidths_getElem?_le _ coeffs j sl _ hsl hw)

theorem gsAssembleBivariate_nonzero {F : Type} [LawfulField F] [DecidableEq F]
    (B d D : Nat) (coeffs : List F)
    (hLen : coeffs.length = gsMonomialCount B d D)
    (hAny : coeffs.any (fun c => !(decide (c = CommRingOps.zero))) = true) :
    ∃ c ∈ gsAssembleBivariate B d D coeffs, c ≠ CommRingOps.zero := by
  let ws := (List.range (D + 1)).map (fun j => B - j * d)
  have hflat : (gsSliceByWidths ws coeffs).flatten = coeffs :=
    gsSliceByWidths_flatten ws coeffs hLen
  rcases mem_of_any_true hAny with ⟨x, hxMem, hxPred⟩
  have hxNe : x ≠ CommRingOps.zero := by
    intro hx0; simp [hx0] at hxPred
  rw [← hflat, List.mem_flatten] at hxMem
  rcases hxMem with ⟨sl, hslMem, hxSl⟩
  refine ⟨GsUniPoly.ofCoeffs sl, List.mem_map.mpr ⟨sl, hslMem, rfl⟩, ?_⟩
  intro hzero
  have htrim0 : trimPoly sl = [] := by simpa only [GsUniPoly.ofCoeffs, UPoly.coeffs_ofList, UPoly.coeffs_zero] using congrArg UPoly.coeffs hzero
  rcases List.getElem?_of_mem hxSl with ⟨idx, hidx⟩
  have hc0 := (trimPoly_eq_nil_iff sl).mp htrim0 idx
  have hget : coeffAt sl idx = x := by simp [coeffAt_eq_getD, List.getD, hidx]
  exact hxNe (hget.symm.trans hc0)

private theorem gsSlice_dotVec_eq_flatMap {F : Type} [LawfulCommRing F]
    (B d r s : Nat) (a b : F) :
    ∀ (js : List Nat) (xs : List F),
      xs.length = (js.map (fun j => B - j * d)).sum →
      dotVec (js.map (gsUniHasseBasis s b))
          ((gsSliceByWidths (js.map (fun j => B - j * d)) xs).map (fun sl => gsUniHasse sl r a)) =
        dotVec (js.flatMap (fun j =>
          (List.range (B - j * d)).map (fun i => gsHasseMonomial (i, j) (r, s) (a, b)))) xs
  | [], _, _ => by simp only [List.map_nil, List.flatMap_nil, dotVec_nil_left]
  | j :: js, xs, hLen => by
    simp only [List.map_cons, List.sum_cons] at hLen
    let w := B - j * d
    have hTakeLen : (xs.take w).length = w := List.length_take_of_le (by omega)
    have hDropLen : (xs.drop w).length = (js.map (fun k => B - k * d)).sum := by
      rw [List.length_drop]; omega
    have ih := gsSlice_dotVec_eq_flatMap B d r s a b js (xs.drop w) hDropLen
    have hSplit : xs = xs.take w ++ xs.drop w := (List.take_append_drop w xs).symm
    have hHead : CommRingOps.mul (gsUniHasseBasis s b j) (gsUniHasse (xs.take w) r a) =
        dotVec ((List.range w).map (fun i => gsHasseMonomial (i, j) (r, s) (a, b))) (xs.take w) := by
      rw [gsUniHasse_eq_dotVec (xs.take w) r a, hTakeLen, ← dotVec_scaleVec]
      rw [scaleVec_eq]
      rw [List.map_map]
      refine congrArg (fun v => dotVec v (xs.take w)) (List.map_congr_left ?_)
      intro i _
      dsimp only [Function.comp]
      exact gsUniHasseBasis_mul_eq_monomial r s a b i j
    simp only [List.map_cons, gsSliceByWidths, dotVec_cons, List.flatMap_cons]
    conv => rhs; rw [hSplit]
    rw [dotVec_append_eq _ _ (xs.take w) (xs.drop w) (by rw [List.length_map, List.length_range, hTakeLen]),
        hHead, ih]

theorem gsAssembleBivariate_hasse_eq {F : Type} [LawfulField F] [DecidableEq F]
    (B d D : Nat) (coeffs : List F) (r s : Nat) (a b : F)
    (hLen : coeffs.length = gsMonomialCount B d D) :
    let Q := gsAssembleBivariate B d D coeffs
    gsUniHasse (gsUniHasse Q s (gsConst b)).coeffs r a =
      gsHasseEval B d D coeffs (r, s) (a, b) := by
  dsimp only
  rw [gsUniHasse_bivariate_comm]
  have hmap : ((gsAssembleBivariate B d D coeffs).map (fun p => gsUniHasse p.coeffs r a)) =
      (gsSliceByWidths ((List.range (D + 1)).map (fun j => B - j * d)) coeffs).map
        (fun sl => gsUniHasse sl r a) := by
    unfold gsAssembleBivariate
    rw [List.map_map]
    apply List.map_congr_left
    intro sl _
    simpa only [Function.comp_def, GsUniPoly.ofCoeffs, UPoly.coeffs_ofList] using gsUniHasse_trimPoly sl r a
  rw [hmap, gsUniHasse_eq_dotVec]
  have hlenS : ((gsSliceByWidths ((List.range (D + 1)).map (fun j => B - j * d)) coeffs).map
      (fun sl => gsUniHasse sl r a)).length = D + 1 := by
    simp [gsSliceByWidths_length]
  rw [hlenS]
  unfold gsHasseEval gsMonomials
  simp only [List.map_flatMap, List.map_map, Function.comp_def]
  exact gsSlice_dotVec_eq_flatMap B d r s a b (List.range (D + 1)) coeffs hLen

/-- **Characteristic-Free Hasse-to-`GsMultiplicity` Bridge (`gsAssembleBivariate_multiplicity`)**:
    Assembling ANY length-`gsMonomialCount B d D` vector whose formal binomial Hasse derivatives
    `gsHasseEval B d D coeffs (r, s) (a, b)` vanish for all `r + s < m` produces a bivariate
    polynomial `Q : List (GsUniPoly F)` satisfying `GsMultiplicity Q m a b`! -/
theorem gsAssembleBivariate_multiplicity {F : Type} [LawfulField F] [DecidableEq F]
    (B d D m : Nat) (coeffs : List F) (a b : F)
    (hLen : coeffs.length = gsMonomialCount B d D)
    (hVanish : ∀ r s, r + s < m → gsHasseEval B d D coeffs (r, s) (a, b) = CommRingOps.zero) :
    GsMultiplicity (gsAssembleBivariate B d D coeffs) m a b := by
  let Q := gsAssembleBivariate B d D coeffs
  intro s hs
  let g := coeffAt (gsTaylor Q.length Q (gsConst b)) s
  have hgEq : g = gsUniHasse Q s (gsConst b) :=
    coeffAt_gsTaylor_eq_gsUniHasse Q.length Q s (gsConst b) (Nat.le_refl _)
  have hgSelf : g = evalCoeffs (g.coeffs.map gsConst) gsVarX := by
    rw [evalCoeffs_map_gsConst_gsVarX]
    exact (UPoly.ofList_coeffs g).symm
  have hgShift : g = evalCoeffs ((gsTaylor g.coeffs.length g.coeffs a).map gsConst)
      (CommRingOps.mul (gsLinear a) CommRingOps.one) := by
    rw [LawfulCommRing.mul_one, ← gsVarX_sub_gsConst a, ← gsTaylor_map_gsConst]
    exact hgSelf.trans (gsTaylor_eval (gsConst a) gsVarX g.coeffs.length (g.coeffs.map gsConst)
      (by rw [List.length_map]; exact Nat.le_refl _))
  have hLow : ∀ r : Nat, r < m - s →
      ∃ h : GsUniPoly F, coeffAt ((gsTaylor g.coeffs.length g.coeffs a).map gsConst) r =
        CommRingOps.mul (gsPow (gsLinear a) (m - s - r)) h := by
    intro r hr
    refine ⟨CommRingOps.zero, ?_⟩
    rw [LawfulCommRing.mul_zero, coeffAt_map_gsConst,
        coeffAt_gsTaylor_eq_gsUniHasse g.coeffs.length g.coeffs r a (Nat.le_refl _),
        hgEq, gsAssembleBivariate_hasse_eq B d D coeffs r s a b hLen,
        hVanish r s (by omega), gsConst_zero]
  rcases gs_low_order_divisible (gsLinear a) CommRingOps.one
      ((gsTaylor g.coeffs.length g.coeffs a).map gsConst) (m - s) hLow with ⟨k, hk⟩
  exact ⟨k, hgShift.trans hk⟩

/-- **Unconditional Guruswami–Sudan List-Decoding Theorem (`guruswami_sudan_unconditional_list_bound`)**:
    Over ANY `[LawfulField F] [DecidableEq F]` (every characteristic, `0` classical choice, `0` candidate
    hints, `0` interpolant inputs), whenever the Hasse dimension inequality
    `domain.length * (m * (m + 1) / 2) < gsMonomialCount (m * A) d D` holds, EVERY duplicate-free list
    `polys` of degree-`≤ d` polynomials agreeing with `word` on `≥ A` distinct points of `domain`
    satisfies **`polys.length ≤ D`**! -/
theorem guruswami_sudan_unconditional_list_bound {F : Type} [LawfulField F] [DecidableEq F]
    (domain : List F) (word : F → F) (d A D m : Nat)
    (hDim : domain.length * (m * (m + 1) / 2) < gsMonomialCount (m * A) d D)
    (polys : List (GsUniPoly F)) (hDistinct : polys.Nodup)
    (hClose : ∀ P ∈ polys, P.coeffs.length ≤ d + 1 ∧
      ∃ xs : List F, xs.Nodup ∧ A ≤ xs.length ∧
        ∀ x ∈ xs, x ∈ domain ∧ evalCoeffs P.coeffs x = word x) :
    polys.length ≤ D := by
  let points := domain.map (fun x => (x, word x))
  have hPtsDim : points.length * (m * (m + 1) / 2) < gsMonomialCount (m * A) d D := by
    simpa [points] using hDim
  rcases guruswami_sudan_interpolation (m * A) d D m points hPtsDim with ⟨hLen, hAny, hVanish⟩
  let coeffs := solveHomogeneous (gsMonomialCount (m * A) d D)
    (gsInterpolationRows (m * A) d D m points)
  let Q := gsAssembleBivariate (m * A) d D coeffs
  have hQ : Q.length ≤ D + 1 := Nat.le_of_eq (gsAssembleBivariate_length (m * A) d D coeffs)
  have hnz : ∃ c ∈ Q, c ≠ CommRingOps.zero :=
    gsAssembleBivariate_nonzero (m * A) d D coeffs hLen hAny
  have hW : GsWeightedDegree Q d (m * A) :=
    gsAssembleBivariate_weightedDegree (m * A) d D coeffs
  have hMult : ∀ x ∈ domain, GsMultiplicity Q m x (word x) := by
    intro x hx
    exact gsAssembleBivariate_multiplicity (m * A) d D m coeffs x (word x) hLen
      (fun r s hrs => hVanish (x, word x) (List.mem_map.mpr ⟨x, hx, rfl⟩) r s hrs)
  exact guruswami_sudan_agreement_list_bound domain word d A D m Q hQ hnz hW hMult
    polys hDistinct hClose

/-- Domain-filter form of `guruswami_sudan_unconditional_list_bound` for duplicate-free domains. -/
theorem guruswami_sudan_filter_list_bound {F : Type} [LawfulField F] [DecidableEq F]
    (domain : List F) (word : F → F) (d A D m : Nat)
    (hDomNd : domain.Nodup)
    (hDim : domain.length * (m * (m + 1) / 2) < gsMonomialCount (m * A) d D)
    (polys : List (GsUniPoly F)) (hDistinct : polys.Nodup)
    (hClose : ∀ P ∈ polys, P.coeffs.length ≤ d + 1 ∧
      A ≤ (domain.filter (fun x => decide (evalCoeffs P.coeffs x = word x))).length) :
    polys.length ≤ D := by
  refine guruswami_sudan_unconditional_list_bound domain word d A D m hDim polys hDistinct ?_
  intro P hP
  rcases hClose P hP with ⟨hdeg, hAg⟩
  refine ⟨hdeg, domain.filter (fun x => decide (evalCoeffs P.coeffs x = word x)),
    List.Pairwise.filter _ hDomNd, hAg, ?_⟩
  intro x hx
  rcases List.mem_filter.mp hx with ⟨hxDom, hxEq⟩
  exact ⟨hxDom, of_decide_eq_true hxEq⟩



end Qsag
namespace Qsag
set_option autoImplicit false
open CommRingOps RoundPoly UPoly
namespace Poly3
variable {F : Type} [LawfulField F] [DecidableEq F]

local instance : NoZeroDivisors (RatFunc F) := LawfulField.toNoZeroDivisors (RatFunc F)

/-- `∂_Z` lowers the `(Y, Z)`-degree. -/
