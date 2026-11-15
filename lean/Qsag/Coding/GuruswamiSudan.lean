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
theorem degYZ_hasseZ_le (s : Nat) (Q : Poly3 F) : (hasseZ s Q).degYZ ≤ Q.degYZ - s := by
  have := UPoly.wdeg_hasse_le UPoly.natDeg UPoly.degFn_natDeg 1 s Q
  simpa only [Nat.one_mul, degYZ, hasseZ_eq] using this

/-- Base change `F[X][Y][Z] → F(X)[Y][Z]`. -/
def liftK : RingHom (Poly3 F) (Poly2 (RatFunc F)) := UPoly.mapHom (UPoly.mapHom Frac.of)

private theorem of_inj (x : UPoly F) (h : (Frac.of (D := UPoly F)).toFun x = zero) : x = zero :=
  Frac.of_injective (h.trans (Frac.of (D := UPoly F)).map_zero.symm)

theorem map_of_inj (q : UPoly (UPoly F))
    (h : (UPoly.mapHom (Frac.of (D := UPoly F))).toFun q = zero) : q = zero :=
  UPoly.mapHom_inj _ of_inj q h

/-- The separant eliminant `Δ_R ∈ F(X)[Y]`, a member of the ideal `(R, ∂_Z R)`. -/
def sepElim (R : Poly3 F) : UPoly (RatFunc F) :=
  Poly2.resZ (liftK.toFun R) (liftK.toFun (hasseZ 1 R))

/-- A squarefree factor: positive `Z`-degree, and coprime to its `Z`-derivative over
    `F(X)(Y)`. -/
structure SqFactor (R : Poly3 F) : Prop where
  degZ_pos : 1 ≤ R.degZ
  coprime : Poly2.CoprimeZ (liftK.toFun R) (liftK.toFun (hasseZ 1 R))

/-- An integral Bézout certificate `u·R + v·∂_Z R = c ∈ F[X][Y]`, `c ≠ 0`, proves
    squarefreeness. Such certificates are what a computer-algebra system returns. -/
theorem SqFactor.of_cert {R : Poly3 F} (hdeg : 1 ≤ R.degZ) (u v : Poly3 F)
    (c : UPoly (UPoly F)) (hc : c ≠ zero)
    (h : add (mul u R) (mul v (hasseZ 1 R)) = UPoly.C c) : SqFactor R :=
  ⟨hdeg, liftK.toFun u, liftK.toFun v, (UPoly.mapHom Frac.of).toFun c,
    fun e => hc (map_of_inj c e), by
      rw [← liftK.map_mul, ← liftK.map_mul, ← liftK.map_add, h]
      exact UPoly.mapHom_C _ c⟩

theorem SqFactor.natDeg_liftK {R : Poly3 F} (h : SqFactor R) : 1 ≤ (liftK.toFun R).natDeg := by
  have : (liftK.toFun R).natDeg = R.natDeg := UPoly.natDeg_mapHom _ map_of_inj R
  rw [this]; simpa only [degZ_eq] using h.degZ_pos

theorem SqFactor.liftK_hasse_ne_zero {R : Poly3 F} (h : SqFactor R) :
    liftK.toFun (hasseZ 1 R) ≠ zero := by
  intro e
  obtain ⟨u, v, c, hc, hcert⟩ := h.coprime
  rw [e, LawfulCommRing.mul_zero, LawfulCommRing.add_zero] at hcert
  have hu : u ≠ zero := fun e' => Poly2.C_ne_zero hc (by
    rw [← hcert, e', LawfulCommRing.zero_mul])
  have hA : liftK.toFun R ≠ zero := fun e' => Poly2.C_ne_zero hc (by
    rw [← hcert, e', LawfulCommRing.mul_zero])
  have h1 := UPoly.natDeg_mul hu hA
  rw [hcert, Poly2.natDeg_C] at h1
  have := h.natDeg_liftK
  omega

theorem sepElim_ne_zero {R : Poly3 F} (h : SqFactor R) : sepElim R ≠ zero :=
  (Poly2.resZ_ne_zero_iff _ _ h.natDeg_liftK h.liftK_hasse_ne_zero).mpr h.coprime

theorem natDeg_sepElim_le {R : Poly3 F} (h : SqFactor R) :
    (sepElim R).natDeg ≤ R.degYZ * R.degYZ := by
  have h1 := Poly2.natDeg_resZ_le (liftK.toFun R) (liftK.toFun (hasseZ 1 R)) h.natDeg_liftK
  have h2 : Poly2.tdeg (liftK.toFun R) ≤ R.degYZ := UPoly.wdeg_mapHom_mapHom_le _ R
  have h3 : Poly2.tdeg (liftK.toFun (hasseZ 1 R)) ≤ (hasseZ 1 R).degYZ :=
    UPoly.wdeg_mapHom_mapHom_le _ _
  have h4 := degYZ_hasseZ_le 1 R
  exact Nat.le_trans h1 (Nat.mul_le_mul h2 (by omega))

/-- `(α, β)` is excluded when the `Z`-free content `Cc` vanishes on the line `Y = α + βX`,
    or the separant eliminant of some factor does. Outside this set every factor
    specializes to a polynomial without repeated roots along the line. -/
def Excluded (Cc : UPoly (UPoly F)) (Rs : List (Poly3 F)) (α β : F) : Prop :=
  Cc.eval (line α β) = zero ∨
    ∃ R ∈ Rs, (sepElim R).eval ((Frac.of (D := UPoly F)).toFun (line α β)) = zero

private theorem natDeg_prod_sepElim_le : ∀ Rs : List (Poly3 F), (∀ R ∈ Rs, SqFactor R) →
    (UPoly.prodList (Rs.map sepElim)).natDeg ≤ (Rs.map degYZ).sum * (Rs.map degYZ).sum
  | [], _ => by simp only [List.map_nil, UPoly.prodList_nil]; show (one : UPoly (RatFunc F)).natDeg ≤ _; rw [UPoly.natDeg_one]; exact Nat.zero_le _
  | R :: Rs, h => by
    have ih := natDeg_prod_sepElim_le Rs (fun R' hR' => h R' (.tail _ hR'))
    have h1 := natDeg_sepElim_le (h R (.head _))
    have h2 := UPoly.natDeg_mul_le (sepElim R) (UPoly.prodList (Rs.map sepElim))
    simp only [List.map_cons, List.sum_cons, UPoly.prodList_cons]
    show (mul (sepElim R) (UPoly.prodList (Rs.map sepElim))).natDeg ≤
      (R.degYZ + (Rs.map degYZ).sum) * (R.degYZ + (Rs.map degYZ).sum)
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    omega

theorem line_inj {α β α' β' : F} (h : line α β = line α' β') : α = α' ∧ β = β' := by
  have h0 := congrArg (fun p : UPoly F => coeffAt p.coeffs 0) h
  have h1 := congrArg (fun p : UPoly F => coeffAt p.coeffs 1) h
  simp only [line, UPoly.coeffAt_ofList, coeffAt_cons_zero, coeffAt_cons_succ] at h0 h1
  exact ⟨h0, h1⟩

/-- **`[CWYZ26]` Lemma 4.3, counting part.** If `deg_Y Cc + Σ deg_{Y,Z} Rᵢ ≤ D` for squarefree
    factors `Rᵢ`, at most `D²` coefficient pairs `(α, β)` are excluded. -/
theorem excluded_pairs_card_le (Cc : UPoly (UPoly F)) (Rs : List (Poly3 F)) (hC : Cc ≠ zero)
    (hRs : ∀ R ∈ Rs, SqFactor R) (D : Nat) (hD : Cc.natDeg + (Rs.map degYZ).sum ≤ D)
    (E : List (F × F)) (hnd : E.Nodup) (hE : ∀ p ∈ E, Excluded Cc Rs p.1 p.2) :
    E.length ≤ D ^ 2 := by
  let lineK : F × F → RatFunc F := fun p => (Frac.of (D := UPoly F)).toFun (line p.1 p.2)
  let Pr : UPoly (RatFunc F) :=
    mul ((UPoly.mapHom Frac.of).toFun Cc) (UPoly.prodList (Rs.map sepElim))
  have hPrne : Pr ≠ zero := mul_ne_zero' (fun e => hC (map_of_inj Cc e))
    (UPoly.prodList_ne_zero _ (fun q hq => by
      obtain ⟨R, hR, rfl⟩ := List.mem_map.mp hq
      exact sepElim_ne_zero (hRs R hR)))
  have hPrdeg : Pr.natDeg ≤ Cc.natDeg + (Rs.map degYZ).sum * (Rs.map degYZ).sum := by
    have h1 := UPoly.natDeg_mul_le ((UPoly.mapHom Frac.of).toFun Cc)
      (UPoly.prodList (Rs.map sepElim))
    have h2 := UPoly.natDeg_mapHom_le (Frac.of (D := UPoly F)) Cc
    have h3 := natDeg_prod_sepElim_le Rs hRs
    show UPoly.natDeg (mul ((UPoly.mapHom Frac.of).toFun Cc)
      (UPoly.prodList (Rs.map sepElim))) ≤ _
    omega
  have hroot : ∀ y ∈ E.map lineK, evalCoeffs Pr.coeffs y = zero := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
    rw [← UPoly.eval_eq]
    rw [← UPoly.evalHom_apply]
    show (UPoly.evalHom (lineK p)).toFun (mul _ _) = zero
    rw [RingHom.map_mul, UPoly.evalHom_apply, UPoly.evalHom_apply]
    rcases hE p hp with h | ⟨R, hR, h⟩
    · rw [UPoly.eval_mapHom, h, RingHom.map_zero, LawfulCommRing.zero_mul]
    · rw [UPoly.eval_prodList_eq_zero _ _ ⟨sepElim R, List.mem_map.mpr ⟨R, hR, rfl⟩, h⟩,
        LawfulCommRing.mul_zero]
  have hndK : (E.map lineK).Nodup :=
    List.pairwise_map.mpr (List.Pairwise.imp (fun {p q} hne e => hne (by
      have := line_inj (Frac.of_injective e)
      exact Prod.ext this.1 this.2)) hnd)
  have hcount := gs_formal_root_bound Pr.natDeg Pr.coeffs (E.map lineK)
    (by show _ ≤ Pr.coeffs.length - 1 + 1; omega)
    (Poly2.exists_ne_zero_of_ne_zero hPrne) hndK hroot
  rw [List.length_map] at hcount
  have hsq : Cc.natDeg + (Rs.map degYZ).sum * (Rs.map degYZ).sum ≤
      (Cc.natDeg + (Rs.map degYZ).sum) * (Cc.natDeg + (Rs.map degYZ).sum) := by
    have := Nat.le_mul_self Cc.natDeg
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
  have hDD := Nat.mul_le_mul hD hD
  rw [Nat.pow_two]
  omega

/-- `C · Π Rᵢ^{eᵢ}`. -/
def factored (Cc : UPoly (UPoly F)) (Rs : List (Poly3 F)) (e : Poly3 F → Nat) : Poly3 F :=
  mul (UPoly.C Cc) (UPoly.prodList (Rs.map fun R => CRing.npow R (e R)))

private theorem affine_npow_eq_zero (α β : F) (P : UPoly F) (R : Poly3 F) : ∀ k : Nat,
    evalAffineLine (CRing.npow R k) α β P = zero → evalAffineLine R α β P = zero
  | 0, h => by
    have h1 : evalAffineLine (one : Poly3 F) α β P = one := evalAffineLine_one α β P
    exact absurd (h1.symm.trans h) NontrivialRing.one_ne_zero
  | k + 1, h => by
    have h1 : evalAffineLine (mul (CRing.npow R k) R) α β P = zero := h
    rw [evalAffineLine_mul] at h1
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h1 with h2 | h2
    · exact affine_npow_eq_zero α β P R k h2
    · exact h2

private theorem affine_prod_eq_zero (α β : F) (P : UPoly F) (e : Poly3 F → Nat) :
    ∀ Rs : List (Poly3 F),
      evalAffineLine (UPoly.prodList (Rs.map fun R => CRing.npow R (e R))) α β P = zero →
      ∃ R ∈ Rs, evalAffineLine R α β P = zero
  | [], h => by
    simp only [List.map_nil, UPoly.prodList_nil] at h
    have h1 : evalAffineLine (one : Poly3 F) α β P = one := evalAffineLine_one α β P
    exact absurd (h1.symm.trans h) NontrivialRing.one_ne_zero
  | R :: Rs, h => by
    simp only [List.map_cons, UPoly.prodList_cons] at h
    have h1 : evalAffineLine (mul (CRing.npow R (e R))
        (UPoly.prodList (Rs.map fun R => CRing.npow R (e R)))) α β P = zero := h
    rw [evalAffineLine_mul] at h1
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h1 with h2 | h2
    · exact ⟨R, .head _, affine_npow_eq_zero α β P R _ h2⟩
    · obtain ⟨R', hR', hz⟩ := affine_prod_eq_zero α β P e Rs h2
      exact ⟨R', .tail _ hR', hz⟩

/-- **`[CWYZ26]` Lemma 4.3, simple-root part.** Outside the excluded set, a root `P` of
    `Q = C · Π Rᵢ^{eᵢ}` along the line `Y = α + βX` is a root of some factor `Rᵢ` at which the
    separant `∂_Z Rᵢ` does not vanish. -/
theorem simple_root_of_not_excluded (Cc : UPoly (UPoly F)) (Rs : List (Poly3 F))
    (e : Poly3 F → Nat) (hRs : ∀ R ∈ Rs, SqFactor R) (α β : F)
    (hnot : ¬ Excluded Cc Rs α β) (P : UPoly F)
    (hroot : evalAffineLine (factored Cc Rs e) α β P = zero) :
    ∃ R ∈ Rs, evalAffineLine R α β P = zero ∧ evalAffineLine (hasseZ 1 R) α β P ≠ zero := by
  have h1 : evalAffineLine (mul (UPoly.C Cc)
      (UPoly.prodList (Rs.map fun R => CRing.npow R (e R)))) α β P = zero := hroot
  rw [evalAffineLine_mul, evalAffineLine_C] at h1
  rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h1 with h2 | h2
  · exact absurd (.inl h2) hnot
  · obtain ⟨R, hR, hz⟩ := affine_prod_eq_zero α β P e Rs h2
    refine ⟨R, hR, hz, fun hsep => hnot (.inr ⟨R, hR, ?_⟩)⟩
    have key : ∀ Q : Poly3 F, evalAffineLine Q α β P = zero →
        (liftK.toFun Q).eval2 ((Frac.of (D := UPoly F)).toFun (line α β))
          ((Frac.of (D := UPoly F)).toFun P) = zero := by
      intro Q hQ
      have := UPoly.eval₂_mapHom_mapHom (Frac.of (D := UPoly F)) Q (line α β) P
      show UPoly.eval₂ _ _ ((UPoly.mapHom (UPoly.mapHom Frac.of)).toFun Q) = zero
      rw [this]
      rw [← evalAffineLine_eq_eval₂]
      show (Frac.of (D := UPoly F)).toFun (evalAffineLine Q α β P) = zero
      rw [hQ, RingHom.map_zero]
    exact Poly2.eval_resZ_eq_zero _ _ (hRs R hR).natDeg_liftK _ _ (key R hz) (key _ hsep)

end Poly3

end Qsag

section
namespace Qsag

set_option autoImplicit false

open CommRingOps RoundPoly

namespace Poly3
variable {F : Type} [LawfulField F] [DecidableEq F]
open UPoly

local instance : NoZeroDivisors (RatFunc F) := LawfulField.toNoZeroDivisors (RatFunc F)

/-- `Q(X, α + βX, Z) ∈ F[X][Z]`: the specialization of `Q` to the line `Y = α + βX`. -/
def lineSpec (Q : Poly3 F) (α β : F) : UPoly (UPoly F) := (mapHom (evalHom (line α β))).toFun Q

theorem coeffAt_lineSpec (Q : Poly3 F) (α β : F) (j : Nat) :
    coeffAt (lineSpec Q α β).coeffs j = (coeffAt Q.coeffs j).eval (line α β) :=
  by unfold lineSpec; rw [coeffAt_mapHom, evalHom_apply]

/-- **Excluded lines.** A nonzero `Q` vanishes identically on at most `deg_{Y,Z} Q` lines
    `Y = α + βX`. -/
theorem lineSpec_zero_card_le (Q : Poly3 F) (hQ : Q ≠ zero) (E : List (F × F)) (hnd : E.Nodup)
    (hE : ∀ p ∈ E, lineSpec Q p.1 p.2 = zero) : E.length ≤ Q.degYZ := by
  let lineK : F × F → RatFunc F := fun p => (Frac.of (D := UPoly F)).toFun (line p.1 p.2)
  have hc : Q.lead ≠ zero := lead_ne_zero hQ
  have hcK : (mapHom (Frac.of (D := UPoly F))).toFun Q.lead ≠ zero := fun e => hc (map_of_inj _ e)
  have hroot : ∀ y ∈ E.map lineK,
      evalCoeffs ((mapHom (Frac.of (D := UPoly F))).toFun Q.lead).coeffs y = zero := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
    rw [← eval_eq]
    show ((mapHom (Frac.of (D := UPoly F))).toFun Q.lead).eval
      ((Frac.of (D := UPoly F)).toFun (line p.1 p.2)) = zero
    have h1 : Q.lead.eval (line p.1 p.2) = zero := by
      have := congrArg (fun q : UPoly (UPoly F) => coeffAt q.coeffs Q.natDeg) (hE p hp)
      simp only [coeffAt_lineSpec, coeffs_zero, coeffAt_nil] at this
      simpa only [lead_eq] using this
    rw [eval_mapHom, h1, RingHom.map_zero]
  have hndK : (E.map lineK).Nodup :=
    List.pairwise_map.mpr (List.Pairwise.imp (fun {p q} hne e => hne (by
      have := line_inj (Frac.of_injective e)
      exact Prod.ext this.1 this.2)) hnd)
  have hcount := gs_formal_root_bound ((mapHom (Frac.of (D := UPoly F))).toFun Q.lead).natDeg
    ((mapHom (Frac.of (D := UPoly F))).toFun Q.lead).coeffs (E.map lineK)
    (by show _ ≤ ((mapHom (Frac.of (D := UPoly F))).toFun Q.lead).coeffs.length - 1 + 1; omega)
    (Poly2.exists_ne_zero_of_ne_zero hcK) hndK hroot
  rw [List.length_map] at hcount
  have h2 := natDeg_mapHom_le (Frac.of (D := UPoly F)) Q.lead
  have h3 := le_wdeg natDeg 1 Q Q.natDeg (by simpa only [lead_eq] using hc)
  have h3' : Q.lead.natDeg + 1 * Q.natDeg ≤ Q.degYZ := by simpa only [lead_eq, degYZ] using h3
  omega

theorem evalAffineLine_hasseZ (k : Nat) (Q : Poly3 F) (α β : F) (P : UPoly F) :
    evalAffineLine (hasseZ k Q) α β P =
      gsUniHasse (Q.coeffs.map (evalHom (line α β)).toFun) k P := by rw [evalAffineLine_eq_eval₂, hasseZ_eq]; exact eval₂_hasse _ _ _ _

/-- **Multiplicity of a root on a non-excluded line.** If `Q(X, α + βX, Z) ≠ 0` and
    `Q(X, α + βX, P(X)) = 0`, there is `1 ≤ μ ≤ deg_Z Q` with `∂_Z^{(k)} Q` vanishing at `P`
    for all `k < μ` and `∂_Z^{(μ)} Q` not vanishing there. No assumption on the
    characteristic. -/
theorem exists_multiplicity (Q : Poly3 F) (α β : F) (P : UPoly F)
    (hnv : lineSpec Q α β ≠ zero) (hroot : evalAffineLine Q α β P = zero) :
    ∃ μ, 1 ≤ μ ∧ μ ≤ Q.degZ ∧ (∀ k, k < μ → evalAffineLine (hasseZ k Q) α β P = zero) ∧
      evalAffineLine (hasseZ μ Q) α β P ≠ zero := by
  have hhigh : ∀ k, Q.coeffs.length ≤ k → evalAffineLine (hasseZ k Q) α β P = zero :=
    fun k hk => by
      rw [evalAffineLine_hasseZ]
      exact gsUniHasse_eq_zero_of_length_le P _ k (by rw [List.length_map]; exact hk)
  rcases first_or_none (fun k => evalAffineLine (hasseZ k Q) α β P ≠ zero) Q.coeffs.length
    with hall | ⟨μ, hμ, hp, hlt⟩
  · exfalso
    apply hnv
    have hz : ∀ k, gsUniHasse (Q.coeffs.map (evalHom (line α β)).toFun) k P = zero := fun k => by
      rw [← evalAffineLine_hasseZ]
      if hk : k ≤ Q.coeffs.length then exact Decidable.not_not.mp (hall k hk)
      else exact hhigh k (by omega)
    have hc := coeffs_zero_of_hasse_zero _ P hz
    exact ext_coeffAt fun j => by
      rw [coeffAt_lineSpec, coeffs_zero, coeffAt_nil]
      have := hc j
      rwa [RingHom.coeffAt_map, evalHom_apply] at this
  · refine ⟨μ, Nat.pos_of_ne_zero (fun e => ?_), ?_, fun k hk => Decidable.not_not.mp (hlt k hk),
      hp⟩
    · subst e
      apply hp
      rw [hasseZ_eq]
      show evalAffineLine (hasse 0 Q) α β P = zero
      rw [hasse_zero]; exact hroot
    · have : μ < Q.coeffs.length := Nat.lt_of_not_le (fun hle => hp (hhigh μ hle))
      rw [degZ_eq]
      show μ ≤ Q.coeffs.length - 1
      omega

/-- **Simple roots without factoring** (the role of `[CWYZ26]` Lemma 4.3 when
    `1, …, deg_Z Q` are invertible). On a non-excluded line every root `P` of `Q` is a simple
    root of the Hasse derivative `R = ∂_Z^{(μ-1)} Q` for its multiplicity `μ`:
    `R(X, α + βX, P) = 0` and `∂_Z R(X, α + βX, P) ≠ 0`. -/
theorem simple_root_of_hasse (Q : Poly3 F)
    (hchar : ∀ k, 1 ≤ k → k ≤ Q.degZ → (CRing.natCast k : F) ≠ zero) (α β : F) (P : UPoly F)
    (hnv : lineSpec Q α β ≠ zero) (hroot : evalAffineLine Q α β P = zero) :
    ∃ μ, 1 ≤ μ ∧ μ ≤ Q.degZ ∧ evalAffineLine (hasseZ (μ - 1) Q) α β P = zero ∧
      evalAffineLine (hasseZ 1 (hasseZ (μ - 1) Q)) α β P ≠ zero := by
  obtain ⟨μ, h1, h2, h3, h4⟩ := exists_multiplicity Q α β P hnv hroot
  refine ⟨μ, h1, h2, h3 (μ - 1) (by omega), ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, μ = m + 1 := ⟨μ - 1, by omega⟩
  simp only [Nat.add_sub_cancel, evalAffineLine_eq, hasseZ_eq]
  show (affineLineHom α β P).toFun (hasse 1 (hasse m Q)) ≠ zero
  rw [hasse_one_hasse, RingHom.map_mul, RingHom.map_natCast]
  exact mul_ne_zero' (natCast_ne_zero (m + 1) (hchar (m + 1) h1 h2)) (by simpa only [evalAffineLine_eq, hasseZ_eq] using h4)

end Poly3

/-! ## Witnesses -/

end Qsag

end

section
namespace Qsag

set_option autoImplicit false

open CommRingOps RoundPoly

/-! ## Coefficient functionals and linear combinations in `F[X][Y][Z]` -/

namespace Poly3
variable {F : Type} [LawfulField F] [DecidableEq F]
open UPoly

/-- `X^i Y^t Z^j`. -/
def mono3 (i t j : Nat) : Poly3 F := ofList (monomial j (Poly2.mono (K := F) i t))

theorem coeffAt_mono3 (i t j k : Nat) :
    coeffAt (mono3 (F := F) i t j).coeffs k = if k = j then Poly2.mono i t else zero := by
  show coeffAt (ofList _).coeffs k = _
  rw [coeffAt_ofList, coeffAt_monomial]

theorem coeff3_mono3_self (i t j : Nat) : coeff3 (mono3 (F := F) i t j) i t j = one := by
  rw [coeff3_eq]
  show coeffAt (coeffAt (coeffAt (mono3 (F := F) i t j).coeffs j).coeffs t).coeffs i = one
  rw [coeffAt_mono3]; simp only [↓reduceIte]
  simpa only [Poly2.coeff2_eq] using Poly2.coeff2_mono_self (K := F) i t

theorem coeff3_mono3_ne (p q : Nat × Nat × Nat) (h : q ≠ p) :
    coeff3 (mono3 (F := F) p.1 p.2.1 p.2.2) q.1 q.2.1 q.2.2 = zero := by
  rw [coeff3_eq]
  show coeffAt (coeffAt (coeffAt (mono3 (F := F) p.1 p.2.1 p.2.2).coeffs q.2.2).coeffs
    q.2.1).coeffs q.1 = zero
  rw [coeffAt_mono3]
  if hj : q.2.2 = p.2.2 then
    simp only [hj, ↓reduceIte]
    apply Eq.trans (a := coeffAt (coeffAt (Poly2.mono (K := F) p.1 p.2.1).coeffs q.2.1).coeffs q.1) (by rfl)
    rw [← Poly2.coeff2_eq]
    refine Poly2.coeff2_mono_ne (K := F) p.1 p.2.1 q.1 q.2.1 (fun e => h ?_)
    have e1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    exact Prod.ext e1 (Prod.ext e2 hj)
  else
    simp only [hj, ↓reduceIte]
    rw [coeffs_zero, coeffAt_nil, coeffs_zero, coeffAt_nil]

/-- Distinct monomials are linearly independent over `F`. -/
theorem eq_zero_of_comb_mono3 : ∀ (ps : List (Nat × Nat × Nat)) (xs : List F), ps.Nodup →
    xs.length = ps.length →
    (∀ q : Nat × Nat × Nat, dotVec ((ps.map (fun p => mono3 (F := F) p.1 p.2.1 p.2.2)).map
      (fun g => coeff3 g q.1 q.2.1 q.2.2)) xs = zero) → ∀ c ∈ xs, c = zero
  | [], [], _, _, _, c, hc => by cases hc
  | [], _ :: _, _, hl, _, _, _ => by cases hl
  | _ :: _, [], _, hl, _, _, _ => by cases hl
  | p :: ps, x :: xs, hnd, hl, h, c, hc => by
    have hp := List.pairwise_cons.mp hnd
    have hx : x = zero := by
      have hz : dotVec ((ps.map (fun q => mono3 (F := F) q.1 q.2.1 q.2.2)).map
          (fun g => coeff3 g p.1 p.2.1 p.2.2)) xs = zero := by
        apply Poly2.dotVec_zero_left
        intro r hr
        obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hr
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
        exact coeff3_mono3_ne q p (fun e => hp.1 q hq e)
      have h1 : add (mul (coeff3 (mono3 (F := F) p.1 p.2.1 p.2.2) p.1 p.2.1 p.2.2) x)
          (dotVec ((ps.map (fun q => mono3 (F := F) q.1 q.2.1 q.2.2)).map
            (fun g => coeff3 g p.1 p.2.1 p.2.2)) xs) = zero := by simpa only [List.map_cons, dotVec_cons] using h p
      rw [hz, coeff3_mono3_self, LawfulCommRing.one_mul, LawfulCommRing.add_zero] at h1
      exact h1
    cases hc with
    | head => exact hx
    | tail _ hc' =>
      refine eq_zero_of_comb_mono3 ps xs hp.2 (Nat.succ.inj hl) (fun q => ?_) c hc'
      have h1 : add (mul (coeff3 (mono3 (F := F) p.1 p.2.1 p.2.2) q.1 q.2.1 q.2.2) x)
          (dotVec ((ps.map (fun q => mono3 (F := F) q.1 q.2.1 q.2.2)).map
            (fun g => coeff3 g q.1 q.2.1 q.2.2)) xs) = zero := by simpa only [List.map_cons, dotVec_cons] using h q
      rwa [hx, LawfulCommRing.mul_zero, LawfulCommRing.zero_add] at h1

theorem degYZ_mono3_le (i t j : Nat) : degYZ (mono3 (F := F) i t j) ≤ t + j := by
  apply wdeg_le
  intro k hk
  rw [coeffAt_mono3] at hk ⊢
  if hkj : k = j then
    subst hkj
    simp only [↓reduceIte] at hk ⊢
    have := Poly2.natDeg_mono_le (K := F) i t
    omega
  else
    simp only [hkj, ↓reduceIte] at hk
    exact absurd rfl hk

theorem deg11d_mono3_le (d i t j : Nat) : deg11d d (mono3 (F := F) i t j) ≤ i + t + d * j := by
  apply wdeg_le
  intro k hk
  rw [coeffAt_mono3] at hk ⊢
  if hkj : k = j then
    subst hkj
    simp only [↓reduceIte] at hk ⊢
    have : (Poly2.mono (K := F) i t).wdeg natDeg 1 ≤ i + t := Poly2.tdeg_mono_le i t
    omega
  else
    simp only [hkj, ↓reduceIte] at hk
    exact absurd rfl hk

/-! ## The shift and the multiplicity constraints -/

/-- **Agreement forces vanishing** (`[CWYZ26]` Lemma 4.2, third item). If `Q` satisfies the
    order-`m` constraints at the distinct points `zs`, `P` has degree at most `d` and agrees
    with the fold `f + (α + βX)·g` on `zs`, and `deg_{1,1,d} Q < m·|zs|`, then
    `Q(X, α + βX, P(X)) = 0`. -/
theorem evalAffineLine_eq_zero_of_agree (Q : Poly3 F) (m d : Nat) (f g : F → F) (α β : F)
    (P : UPoly F) (zs : List F) (hnd : zs.Nodup)
    (hcons : ∀ z ∈ zs, ∀ r t s, r + s < m → cons z (f z) (g z) r t s Q = zero)
    (hagree : ∀ z ∈ zs, P.eval z = add (f z) (mul (add α (mul β z)) (g z)))
    (hP : P.natDeg ≤ d) (hdeg : Q.deg11d d < m * zs.length) :
    evalAffineLine Q α β P = zero := by
  if hz : evalAffineLine Q α β P = zero then exact hz
  else
    exfalso
    have hne : (toGs (evalAffineLine Q α β P)).coeffs ≠ [] := fun e =>
      hz ((eq_zero_iff _).mpr (by simpa only [toGs_eq] using e))
    have hdiv : ∀ x ∈ zs, ∃ k : GsUniPoly F,
        toGs (evalAffineLine Q α β P) = mul (gsPow (gsLinear x) m) k := by
      intro x hx
      obtain ⟨q, hq⟩ := (UPoly.inPow_iff _ _ _).mp (inPow_affine_of_cons Q x (f x) (g x) α β P m (hcons x hx) (hagree x hx))
      exact ⟨toGs q, by rw [hq, toGs_mul, toGs_npow, toGs_linear]⟩
    have hlen := gs_multiplicity_length m zs _ hnd hne hdiv
    have hd := deg_evalAffineLine_le Q α β P d hP
    have hl : (evalAffineLine Q α β P).natDeg = (evalAffineLine Q α β P).coeffs.length - 1 := rfl
    have hv : (toGs (evalAffineLine Q α β P)).coeffs = (evalAffineLine Q α β P).coeffs := by rw [toGs_eq]
    rw [hv] at hlen
    omega

/-! ## Index sets and the interpolation count -/

/-! ## The explainer -/

/-- The monomial basis `X^i Y^t Z^j`, `t + j ≤ Dy`, `i + d·j < Wx`. -/
def gens (d Wx Dy : Nat) : List (Poly3 F) :=
  (triples d Wx Dy (Dy + 1)).map fun p => mono3 p.1 p.2.1 p.2.2

/-- The constraint matrix of equation (4.3): one row per point `z` and per `(r, t, s)` with
    `s < m`, `r < m - s`, `t ≤ Dy - s`. -/
def consRows (f g : F → F) (Dm : List F) (m Dy : Nat) (gs : List (Poly3 F)) : List (List F) :=
  Dm.flatMap fun z => (triples 1 m Dy m).map fun c => gs.map (cons z (f z) (g z) c.1 c.2.1 c.2.2)

/-- **The trivariate explainer** of `[CWYZ26]` Lemma 4.2, computed by the homogeneous solver. -/
def explainer (f g : F → F) (Dm : List F) (m d Wx Dy : Nat) : Poly3 F :=
  comb (solveHomogeneous (gens (F := F) d Wx Dy).length
    (consRows f g Dm m Dy (gens d Wx Dy))) (gens d Wx Dy)

theorem explainer_spec (f g : F → F) (Dm : List F) (m d Wx Dy : Nat)
    (hcount : Dm.length * triCount 1 m Dy m < triCount d Wx Dy (Dy + 1)) :
    explainer f g Dm m d Wx Dy ≠ zero ∧ (explainer f g Dm m d Wx Dy).degYZ ≤ Dy ∧
      (explainer f g Dm m d Wx Dy).deg11d d ≤ Wx + Dy - 1 ∧
      ∀ z ∈ Dm, ∀ r t s, r + s < m → cons z (f z) (g z) r t s (explainer f g Dm m d Wx Dy) = zero := by
  have hglen : (gens (F := F) d Wx Dy).length = triCount d Wx Dy (Dy + 1) := by
    show (List.map _ _).length = _
    rw [List.length_map, length_triples]
  have hrlen : (consRows f g Dm m Dy (gens d Wx Dy)).length = Dm.length * triCount 1 m Dy m :=
    flatMap_const_length _ _ Dm (fun z _ => by rw [List.length_map, length_triples])
  obtain ⟨h1, h2, h3⟩ := gauss_nullspace_witness (gens (F := F) d Wx Dy).length
    (consRows f g Dm m Dy (gens d Wx Dy)) (by rw [hrlen, hglen]; exact hcount)
    (fun row hrow => by
      obtain ⟨z, _, hz⟩ := List.mem_flatMap.mp hrow
      obtain ⟨c, _, rfl⟩ := List.mem_map.mp hz
      exact List.length_map _)
  have hdegYZ : (explainer f g Dm m d Wx Dy).degYZ ≤ Dy :=
    degFn_comb_le degFn_degYZ degYZ_C3 Dy _ _ (fun q hq => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      obtain ⟨i, t, j⟩ := p
      have hm := (mem_triples d Wx Dy i t j (Dy + 1)).mp hp
      have := degYZ_mono3_le (F := F) i t j
      show degYZ (mono3 (F := F) i t j) ≤ Dy
      omega)
  refine ⟨fun e => ?_, hdegYZ, ?_, ?_⟩
  · obtain ⟨c, hc, hne⟩ := List.any_eq_true.mp h2
    have hall := eq_zero_of_comb_mono3 (F := F) (triples d Wx Dy (Dy + 1)) _
      (nodup_triples d Wx Dy (Dy + 1)) (by rw [h1]; exact List.length_map _)
      (fun q => by
        rw [← lin_comb (isLin_coeff3 q.1 q.2.1 q.2.2)]
        show coeff3 (explainer f g Dm m d Wx Dy) q.1 q.2.1 q.2.2 = zero
        rw [e]; exact (isLin_coeff3 q.1 q.2.1 q.2.2).map_zero) c hc
    simp [hall] at hne
  · exact degFn_comb_le (degFn_deg11d d) (deg11d_C3 d) _ _ _ (fun q hq => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
      obtain ⟨i, t, j⟩ := p
      have hm := (mem_triples d Wx Dy i t j (Dy + 1)).mp hp
      have := deg11d_mono3_le (F := F) d i t j
      show deg11d d (mono3 (F := F) i t j) ≤ Wx + Dy - 1
      omega)
  · intro z hz r t s hrs
    if ht : t < Dy + 1 - s then
      have hmem : (r, t, s) ∈ triples 1 m Dy m :=
        (mem_triples 1 m Dy r t s m).mpr ⟨by omega, ht, by omega⟩
      have := h3 _ (List.mem_flatMap.mpr ⟨z, hz, List.mem_map.mpr ⟨(r, t, s), hmem, rfl⟩⟩)
      rw [← lin_comb (isLin_cons z (f z) (g z) r t s)] at this
      exact this
    else
      have hsh : ((shiftHom z (f z) (g z)).toFun (explainer f g Dm m d Wx Dy)).wdeg natDeg 1
          ≤ (explainer f g Dm m d Wx Dy).wdeg natDeg 1 :=
        degYZ_shiftHom_le z (f z) (g z) (explainer f g Dm m d Wx Dy)
      have hdy : (explainer f g Dm m d Wx Dy).wdeg natDeg 1 ≤ Dy := hdegYZ
      rw [cons_eq, coeff3_eq]
      show coeffAt (coeffAt (coeffAt
        ((shiftHom z (f z) (g z)).toFun (explainer f g Dm m d Wx Dy)).coeffs s).coeffs
          t).coeffs r = zero
      generalize (shiftHom z (f z) (g z)).toFun (explainer f g Dm m d Wx Dy) = T at hsh ⊢
      have hzero : coeffAt (coeffAt T.coeffs s).coeffs t = zero := by
        if hq : coeffAt T.coeffs s = zero then
          rw [hq, coeffs_zero, coeffAt_nil]
        else
          have hle := le_wdeg natDeg 1 T s hq
          exact coeffAt_eq_zero_of_natDeg_lt (coeffAt T.coeffs s) (by omega)
      rw [hzero, coeffs_zero, coeffAt_nil]

/-- The explainer vanishes on every sufficiently agreeing candidate: for `P` of degree at most
    `d` agreeing with `f + (α + βX)·g` on distinct points `zs` of `Dm` with
    `Wx + Dy ≤ m·|zs|`, `Q(X, α + βX, P(X)) = 0`. -/
theorem explainer_vanishes (f g : F → F) (Dm : List F) (m d Wx Dy : Nat)
    (hcount : Dm.length * triCount 1 m Dy m < triCount d Wx Dy (Dy + 1)) (α β : F)
    (P : UPoly F) (zs : List F) (hP : P.natDeg ≤ d) (hnd : zs.Nodup) (hsub : ∀ z ∈ zs, z ∈ Dm)
    (hag : ∀ z ∈ zs, P.eval z = add (f z) (mul (add α (mul β z)) (g z)))
    (hlen : Wx + Dy ≤ m * zs.length) :
    evalAffineLine (explainer f g Dm m d Wx Dy) α β P = zero := by
  obtain ⟨_, _, h11, hc⟩ := explainer_spec f g Dm m d Wx Dy hcount
  have hW : 1 ≤ Wx := Nat.pos_of_ne_zero (fun e => by
    rw [e, triCount_zero_width] at hcount
    exact Nat.not_lt_zero _ hcount)
  exact evalAffineLine_eq_zero_of_agree _ m d f g α β P zs hnd
    (fun z hz => hc z (hsub z hz)) hag hP (by omega)

/-- **`[CWYZ26]` Lemma 4.2.** Under the count hypothesis (4.5) there is a nonzero
    `Q ∈ F[X][Y][Z]` with `deg_{Y,Z} Q ≤ Dy` and `deg_{1,1,d} Q < Wx + Dy` such that, for all
    `α, β` and every `P` of degree at most `d` agreeing with `f + (α + βX)·g` on a set `zs` of
    points of `Dm` with `Wx + Dy ≤ m·|zs|`, the specialization `Q(X, α + βX, P(X))` is zero. -/
theorem exists_trivariate_affine_explainer (f g : F → F) (Dm : List F) (m d Wx Dy : Nat)
    (hcount : Dm.length * triCount 1 m Dy m < triCount d Wx Dy (Dy + 1)) :
    ∃ Q : Poly3 F, Q ≠ zero ∧ Q.degYZ ≤ Dy ∧ Q.deg11d d ≤ Wx + Dy - 1 ∧
      ∀ (α β : F) (P : UPoly F) (zs : List F), P.natDeg ≤ d → zs.Nodup → (∀ z ∈ zs, z ∈ Dm) →
        (∀ z ∈ zs, P.eval z = add (f z) (mul (add α (mul β z)) (g z))) →
        Wx + Dy ≤ m * zs.length → evalAffineLine Q α β P = zero := by
  obtain ⟨hne, hYZ, h11, _⟩ := explainer_spec f g Dm m d Wx Dy hcount
  exact ⟨_, hne, hYZ, h11, fun α β P zs hP hnd hsub hag hlen =>
    explainer_vanishes f g Dm m d Wx Dy hcount α β P zs hP hnd hsub hag hlen⟩

end Poly3

/-! ## Witnesses -/

end Qsag

end

namespace Qsag.Poly3
open UPoly
variable {F : Type} [LawfulField F] [DecidableEq F]
theorem liftK_apply (q : Poly3 F) : (liftK (F := F)).toFun q = (mapHom (mapHom Frac.of)).toFun q := by unfold liftK; rfl
theorem lineSpec_apply (Q : Poly3 F) (α β : F) : lineSpec Q α β = (mapHom (evalHom (line α β))).toFun Q := by unfold lineSpec; rfl
end Qsag.Poly3
