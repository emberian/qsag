module
public import Qsag.Coding.WhirProfiles
public import Qsag.Math.CoeffPoly

/-! Half-threshold correlated agreement, the affine fold's agreement loss, and
    distinct-fiber sampling. Halving an outer error count `2e < n - k` on the
    first scalar fold enters the unique-decoding ball `e < (n - k) / 2`, so the
    resulting per-query survival ratio `(n - e + 1) / n` matches the unique-decoding
    factor `(1 + ρ) / 2` (`3 / 4` at rate `ρ = 1 / 2`) rather than reducing query count.
    Distances are counted in positions on a common domain, so all threshold comparisons
    are exact integer inequalities. -/
public section
namespace Qsag
set_option autoImplicit false
set_option exponentiation.threshold 512
open CommRingOps

/-- Strict entry below the unique radius, with denominator `n` and rate `k/n`. -/
theorem aboveJohnson_half_lt_unique {k n half outer : Nat}
    (h : 2 * half ≤ outer) (hcap : k + outer < n) : k + 2 * half < n := by omega

/-- The two-witness proof of RVW13. Two scalar combinations with at most `e`
    errors give an explicit pair of codewords with at most `2e` joint errors.
    Taking the contrapositive gives at most one exceptional scalar. -/
theorem aboveJohnson_rvw {I F : Type} [LawfulField F] [DecidableEq F]
    (D : List I) (C : (I → F) → Prop)
    (hsub : ∀ u v, C u → C v → C (fun x => sub (u x) (v x)))
    (hscale : ∀ a u, C u → C (fun x => mul a (u x)))
    (f g u v : I → F) (a b : F) (hab : a ≠ b) (hu : C u) (hv : C v) (e : Nat)
    (ha : D.length ≤ (D.filter (fun x => decide (u x = add (f x) (mul a (g x))))).length + e)
    (hb : D.length ≤ (D.filter (fun x => decide (v x = add (f x) (mul b (g x))))).length + e) :
    ∃ U V, C U ∧ C V ∧ D.length ≤
      (D.filter (fun x => decide (U x = f x) && decide (V x = g x))).length + 2 * e := by
  let pa := fun x => decide (u x = add (f x) (mul a (g x)))
  let pb := fun x => decide (v x = add (f x) (mul b (g x)))
  let V := fun x => mul (LawfulField.inv (sub a b)) (sub (u x) (v x))
  have hV : C V := hscale _ _ (hsub u v hu hv)
  let U := fun x => sub (u x) (mul a (V x))
  refine ⟨U, V, hsub _ _ hu (hscale a V hV), hV, ?_⟩
  have hm := filter_sub_length_le (fun x => pa x && pb x)
    (fun x => decide (U x = f x) && decide (V x = g x)) (by
      intro x hx
      obtain ⟨hx₁, hx₂⟩ := Bool.and_eq_true_iff.mp hx
      have h₁ := of_decide_eq_true hx₁
      have h₂ := of_decide_eq_true hx₂
      have hd : sub (u x) (v x) = mul (sub a b) (g x) := by
        rw [h₁, h₂]
        constructive_ring
      have hg : V x = g x := by
        dsimp [V]
        rw [hd, ← LawfulCommRing.mul_assoc, LawfulField.inv_mul_cancel
          (fun hz => hab (LawfulCommRing.sub_eq_zero_iff.mp hz)), LawfulCommRing.one_mul]
      have hf : U x = f x := by
        dsimp only [U]
        rw [hg, h₁]
        constructive_ring
      simp [hf, hg]) D
  have ho := filter_overlap_len pa pb D
  change D.length ≤ (D.filter pa).length + e at ha
  change D.length ≤ (D.filter pb).length + e at hb
  omega

/-- Two RS explanations inside the half-distance ball represent the same polynomial. -/
theorem aboveJohnson_unique_agreement {F : Type} [LawfulField F] [DecidableEq F]
    (D : List F) (hD : D.Nodup) (f : F → F) (P Q : List F) (d e : Nat)
    (hp : P.length ≤ d + 1) (hq : Q.length ≤ d + 1) (hr : d + 2 * e < D.length)
    (hP : D.length ≤ (D.filter (fun x => decide (RoundPoly.evalCoeffs P x = f x))).length + e)
    (hQ : D.length ≤ (D.filter (fun x => decide (RoundPoly.evalCoeffs Q x = f x))).length + e) :
    trimPoly P = trimPoly Q := by
  let p := fun x => decide (RoundPoly.evalCoeffs P x = f x)
  let q := fun x => decide (RoundPoly.evalCoeffs Q x = f x)
  have hov := filter_overlap_len p q D
  change D.length ≤ (D.filter p).length + e at hP
  change D.length ≤ (D.filter q).length + e at hQ
  apply trimPoly_eq_of_agree_on_nodup hp hq (List.Pairwise.filter (fun x => p x && q x) hD) (by omega)
  intro x hx
  obtain ⟨h₁, h₂⟩ := Bool.and_eq_true_iff.mp (List.mem_filter.mp hx).2
  exact (of_decide_eq_true h₁).trans (of_decide_eq_true h₂).symm

/-- Correlated witnesses retain all their joint agreements under every scalar
    combination, including the separate nonzero mask challenge. Together with
    uniqueness this identifies the only possible nearby combination. -/
theorem aboveJohnson_line_preserves {I F : Type} [LawfulField F] [DecidableEq F]
    (D : List I) (f g u v : I → F) (z : F) :
    (D.filter (fun x => decide (u x = f x) && decide (v x = g x))).length ≤
    (D.filter (fun x => decide (add (u x) (mul z (v x)) = add (f x) (mul z (g x))))).length := by
  apply filter_sub_length_le
  intro x hx
  obtain ⟨hu, hv⟩ := Bool.and_eq_true_iff.mp hx
  simp [of_decide_eq_true hu, of_decide_eq_true hv]

/-- At a unique radius the output polynomial agrees with the fold of the
    correlated witnesses on the whole field. The coordinate-dependent combiner
    includes both the scalar mask line and the affine data fold. -/
theorem aboveJohnson_unique_fold {F : Type} [LawfulField F] [DecidableEq F]
    (D : List F) (hD : D.Nodup) (f g u v : F → F) (combine : F → F → F → F)
    (P Q : List F) (d e : Nat) (hp : P.length ≤ d + 1) (hq : Q.length ≤ d + 1)
    (hr : d + 2 * e < D.length)
    (hjoint : D.length ≤
      (D.filter (fun x => decide (u x = f x) && decide (v x = g x))).length + e)
    (hfold : ∀ x, RoundPoly.evalCoeffs Q x = combine x (u x) (v x))
    (hout : D.length ≤
      (D.filter (fun x => decide (RoundPoly.evalCoeffs P x = combine x (f x) (g x)))).length + e) :
    trimPoly P = trimPoly Q := by
  apply aboveJohnson_unique_agreement D hD (fun x => combine x (f x) (g x)) P Q d e hp hq hr hout
  apply Nat.le_trans hjoint (Nat.add_le_add_right _ _)
  apply filter_sub_length_le
  intro x hx
  obtain ⟨hu, hv⟩ := Bool.and_eq_true_iff.mp hx
  simp [hfold, of_decide_eq_true hu, of_decide_eq_true hv]

/-- One exceptional output coordinate per affine decomposition. Each surviving
    agreement lifts to both antipodes in the parent domain. -/
@[expose] def whirLiftedAgreements : Nat → Nat → Nat
  | 0, m => m
  | s + 1, m => 2 * (whirLiftedAgreements s m - 1)

/-- Exact composition of the per-fold guarantee for an output with at least two
    agreements. The loss in units of the final domain is strictly below two. -/
theorem aboveJohnson_packed_agreement (s a : Nat) :
    whirLiftedAgreements s (a + 2) = 2 ^ s * a + 2 := by
  induction s with
  | zero => simp [whirLiftedAgreements]
  | succ s ih =>
    rw [whirLiftedAgreements, ih, Nat.pow_succ', Nat.mul_assoc]
    omega

/-- Compose the one-coordinate affine decomposition and antipodal lift along
    an actual sequence of witness agreement counts, indexed from the exit. -/
theorem aboveJohnson_lift_chain (agreements : Nat → Nat) (a s : Nat)
    (exitAgrees : a + 2 ≤ agreements 0)
    (step : ∀ j, j < s → 2 * (agreements j - 1) ≤ agreements (j + 1)) :
    2^s * a + 2 ≤ agreements s := by
  induction s with
  | zero => simpa using exitAgrees
  | succ s ih =>
    have h := ih (fun j hj => step j (by omega))
    have hs := step s (by omega)
    rw [Nat.pow_succ', Nat.mul_assoc]
    omega

/-- After RVW on the first theta, a good affine decomposition can spend one
    coordinate. Subsequent steps project pairs then spend one coordinate each. -/
@[expose] def whirAffineAgreementCap : Nat → Nat → Nat
  | 0, m => m
  | j + 1, m => whirAffineAgreementCap j (m / 2 + 1)

theorem aboveJohnson_unique_folds (r a : Nat) :
    whirAffineAgreementCap r (2^r * a + 1) = a + 1 := by
  induction r with
  | zero => simp [whirAffineAgreementCap]
  | succ r ih =>
    rw [whirAffineAgreementCap, Nat.pow_succ', Nat.mul_assoc]
    rw [show (2 * (2 ^ r * a) + 1) / 2 = 2 ^ r * a by omega]
    exact ih

/-- `r+1` further affine folds after the first scalar combination.
    Starting at an integral common threshold leaves exactly one extra agreement
    in this worst-case integer recurrence, for any positive number of folds. -/
theorem aboveJohnson_after_entry (r a : Nat) :
    whirAffineAgreementCap (r + 1) (2^(r + 1) * a) = a + 1 := by
  rw [whirAffineAgreementCap, Nat.pow_succ', Nat.mul_assoc]
  rw [show 2 * (2 ^ r * a) / 2 = 2 ^ r * a by omega]
  exact aboveJohnson_unique_folds r a

structure WhirAboveJohnsonWitness where
  n : Nat
  k : Nat
  outerErrors : Nat
  halfErrors : Nat
  folds : Nat
  queries : Nat
  queryTargetBits : Nat
  deriving Repr, DecidableEq

/-- Premise above Johnson, strict entry below the unique radius (including
    overflow), and the final one-coordinate allowance from the packed recurrence. -/
@[expose] def checkWhirAboveJohnsonWitness (w : WhirAboveJohnsonWitness) : Bool :=
  decide (0 < w.k ∧ 0 < w.folds ∧ 0 < w.halfErrors ∧
    (w.n - w.outerErrors)^2 < w.n * w.k ∧
    2 * w.halfErrors ≤ w.outerErrors ∧ w.k + w.outerErrors < w.n ∧
    0 < w.queries ∧ w.queries ≤ w.n ∧
    affineFallingFactorial (w.n - w.halfErrors + 1) w.queries * 2^w.queryTargetBits <
      affineFallingFactorial w.n w.queries)

/-- Soundness for actual duplicate-free query tuples on any finite domain. -/
theorem aboveJohnson_query_bound {I : Type} [DecidableEq I] (w : WhirAboveJohnsonWitness)
    (hw : checkWhirAboveJohnsonWitness w = true)
    (D : List I) (hD : D.Nodup) (hn : D.length = w.n) (good : I → Bool)
    (hg : (D.filter good).length ≤ w.n - w.halfErrors + 1) :
    w.k + 2 * w.halfErrors < w.n ∧
    ((affineDistinctTuples w.queries D).filter (fun t => t.all good)).length * 2^w.queryTargetBits <
      (affineDistinctTuples w.queries D).length := by
  obtain ⟨_, _, _, _, hhalf, hcap, _, _, hquery⟩ := of_decide_eq_true hw
  refine ⟨aboveJohnson_half_lt_unique hhalf hcap, ?_⟩
  rw [affineDistinctTuples_length w.queries hD, hn]
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (affineDistinctTuples_all_good_le
    w.queries _ D good hD hg)) hquery

/-- On challenges admitting the affine witness lifts, a failed entry claim
    bounds the set that a distinct-fiber query can miss. -/
theorem aboveJohnson_query_of_lifts {I : Type} [DecidableEq I] (w : WhirAboveJohnsonWitness)
    (hw : checkWhirAboveJohnsonWitness w = true)
    (D : List I) (hD : D.Nodup) (hn : D.length = w.n) (good : I → Bool)
    (agreements : Nat → Nat) (hout : (D.filter good).length = agreements 0)
    (step : ∀ j, j < w.folds → 2 * (agreements j - 1) ≤ agreements (j + 1))
    (entry : agreements w.folds < 2^w.folds * (w.n - w.halfErrors) + 2) :
    ((affineDistinctTuples w.queries D).filter (fun t => t.all good)).length * 2^w.queryTargetBits <
      (affineDistinctTuples w.queries D).length := by
  apply (aboveJohnson_query_bound w hw D hD hn good ?_).2
  rw [hout]
  if h : w.n - w.halfErrors + 2 ≤ agreements 0 then
    exact False.elim (Nat.not_le_of_lt entry (aboveJohnson_lift_chain agreements _ _ h step))
  else omega

/-- Canonical rate-half Stage-0 arithmetic (`k = n / 2 + 2` including two overflow slots,
    inner error budget `e = n / 4 - 2` inside unique decoding, `644` distinct-fiber queries). -/
@[expose] def rateHalfWitness (logCells : Nat) : WhirAboveJohnsonWitness :=
  let s := if logCells = 16 then 4 else if logCells ≤ 20 then 5 else 6
  let n := 2 ^ (logCells + 1 - s)
  let e := n / 4 - 2
  ⟨n, n / 2 + 2, 2 * e, e, s, 644, 266⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
theorem aboveJohnson_rate_half_queries :
    (List.range 13).all (fun i => checkWhirAboveJohnsonWitness (rateHalfWitness (16 + i))) = true := by
  decide +kernel

/-- A finite CWYZ witness for each intermediate affine output domain. The
    numerical list bound is independent of which passing interpolation witness
    is used. A single test query here checks only the interpolation parameters;
    the packed query certificate is `aboveJohnson_rate_half_queries`. -/
@[expose] def rateHalfAffineWitness (w : WhirAboveJohnsonWitness) (j : Nat) : WhirAffineWitness :=
  let n := 2^j * w.n
  let a := 2^j * (w.n - w.halfErrors)
  ⟨n, n / 2 + 2, 1, a, a - 1, 3, 14, 1, 0⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
theorem aboveJohnson_rate_half_affine_parameters :
    (List.range 13).all (fun i =>
      let w := rateHalfWitness (16 + i)
      (List.range w.folds).all (fun j =>
        checkWhirAffineWitness (rateHalfAffineWitness w j) ((2^64 - 2^32 + 1)^5))) = true := by
  decide +kernel

/-- DKT26 Theorem 5.12 at multiplicity 16, including rounding, the joint-list
    term and the nonzero scalar denominator used for the mask claim. -/
theorem aboveJohnson_rate_half_mask_budget :
    (List.range 13).all (fun i =>
      let w := rateHalfWitness (16 + i)
      let a := w.n - w.halfErrors
      let d := w.k - 1
      let pairs := w.n * (a - d) / (a*a - w.n*d)
      let bad := natCeilDiv (33^3 * w.n^2) (3*d) + pairs
      decide (1 ≤ d ∧ d + 2 ≤ w.n ∧ 33^2 * w.n * w.k ≤ (32*a)^2 ∧
        (a - 1)^2 > w.n*d ∧ 2^266 * bad < (2^64 - 2^32 + 1)^5 - 1)) = true := by
  decide +kernel

#verify_constructive aboveJohnson_rvw aboveJohnson_half_lt_unique aboveJohnson_unique_agreement
  aboveJohnson_line_preserves aboveJohnson_unique_fold aboveJohnson_packed_agreement aboveJohnson_unique_folds
  aboveJohnson_after_entry aboveJohnson_lift_chain aboveJohnson_query_bound aboveJohnson_query_of_lifts
  aboveJohnson_rate_half_queries aboveJohnson_rate_half_affine_parameters aboveJohnson_rate_half_mask_budget

end Qsag
end
