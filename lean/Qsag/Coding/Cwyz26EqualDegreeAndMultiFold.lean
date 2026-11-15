module
/-
# Qsag.Coding.Cwyz26EqualDegreeAndMultiFold — Three-Challenge Equal-Degree Lift, Intra-Stage Multi-Fold Composition, and Multi-Sheet Space-Curve GCD

1. **Three-Challenge Equal-Degree Claim-Fold Soundness (`[CWYZ26]` Theorem 5.1 Lift)**:
   - `gsDecodeList_length_le_johnson`: parameter-free Guruswami–Sudan list bound from integer Cauchy–Schwarz.
   - `equal_degree_bad_theta_count_le`: bounds exceptional `θ` values where invalid input claims cancel in `f + θ g`.
   - `equal_degree_three_challenge_fold_bound`: unconditional 1-loss `(θ, α, β) ∈ S_θ × S × S` claim-fold soundness without any `hInvalidMix` hypothesis.
   - `sliced_equal_degree_three_challenge_bound` and `sliced_stage_three_challenge_supported_budget`: closed-form `QuarticGoldilocks` specialization certifying `≥ 184` bits across all 46 non-exhaustive `BciksJohnsonQrom128` stages.
2. **Intra-Stage `k`-Fold Schedule Composition (`foldSteps = 1..6`)**:
   - Antipodal coset pairing, polynomial interleaving `Q(X) = F(X²) + X G(X²)`, and 4-challenge `(φ, θ, α, β)` `5`-wire dual-bridge step soundness.
   - Inductive `k`-step sequential `SeqRoundSpec` composition across intermediate geometries `(2^t n, 2^(rem + t) + 2)` and concrete `BciksJohnsonQrom128` multi-fold budgets.
3. **Multi-Sheet Space-Curve GCD Decomposition (`ShearedCurveGcd` Refinement)**:
   - Unconditional leaf `Z`-gcd `Gj` (`1 ≤ Gj.deg ≤ h_C`), universal sheet root `ModMonic.modGen Gj`, subresultant-derivative multiplicity dichotomy, and coordinate fiber refinement.
-/

public import Qsag.Protocol.Aggregation.HemSlicedFoldBudget
public import Qsag.Coding.ShearedCurveGcd
import all Qsag.Protocol.Aggregation.HemSlicedFoldBudget
import all Qsag.Coding.Cwyz26DeployedStages
import all Qsag.Coding.Cwyz26JohnsonCertificate
import all Qsag.Coding.JohnsonSetSystem
import all Qsag.Coding.ShearedCurveGcd
import all Qsag.Coding.ModMonicAlgebra
import all Qsag.Coding.SylvesterDeriv
import all Qsag.Coding.SylvesterElimination
import all Qsag.Coding.SylvesterResultant
import all Qsag.Coding.BivariateFactorSplit
import all Qsag.Coding.BivariateGauss
import all Qsag.Coding.DynamicGcdSplit
import all Qsag.Coding.PolyMv3
import all Qsag.Protocol.Aggregation.HemWhirRbrSoundness
import all Qsag.Protocol.Aggregation.HemVerifierAcceptance
import all Qsag.Oracle.MultiRoundFsQrom
import all Qsag.Oracle.ConcreteSecurityBudget
import all Qsag.Coding.AffineProximityGaps
import all Qsag.Math.Goldilocks

public section
namespace Qsag
set_option autoImplicit false
set_option exponentiation.threshold 2048

/-! ## §1. Unconditional Johnson List Bound & Three-Challenge Equal-Degree Lift -/

/-- **Parameter-Free Johnson List Size Bound on `gsDecodeList`**:
    Over any `[LawfulField F] [DecidableEq F]`, whenever `D.Nodup`, `d + 1 ≤ A`, and
    `D.length * d < A * A`, the complete decoded list `gsDecodeList d A D word` has length at most
    `JohnsonBound.johnsonBound D.length A d = (D.length * (A - d)) / (A * A - D.length * d)`. -/
theorem gsDecodeList_length_le_johnson {F : Type} [LawfulField F] [DecidableEq F]
    (D : List F) (word : F → F) (d A : Nat)
    (hD : D.Nodup) (hdA : d + 1 ≤ A) (hDen : D.length * d < A * A) :
    (gsDecodeList d A D word).length ≤ JohnsonBound.johnsonBound D.length A d := by
  let fam := gsDecodeList d A D word
  let memP : GsUniPoly F → F → Bool := fun P z => decide (RoundPoly.evalCoeffs P.val z = word z)
  refine JohnsonBound.johnson_set_system_card_le D fam memP A d hD ?_ ?_ hDen
  · intro P hP
    exact ((mem_gsDecodeList_iff word hD hdA P).mp hP).2
  · refine JohnsonBound.pairwise_of_nodup (gsDecodeList_nodup d A D word) ?_
    intro P₁ hP₁ P₂ hP₂ hNe
    have h₁ := ((mem_gsDecodeList_iff word hD hdA P₁).mp hP₁).1
    have h₂ := ((mem_gsDecodeList_iff word hD hdA P₂).mp hP₂).1
    apply Decidable.byContradiction
    intro hGt
    have hULen : d + 1 ≤ (D.filter (fun z => memP P₁ z && memP P₂ z)).length := by omega
    have hUNd : (D.filter (fun z => memP P₁ z && memP P₂ z)).Nodup := List.Pairwise.filter _ hD
    obtain ⟨x₀, hx₀U, hx₀Diff⟩ := gsUniPoly_exists_diff_on_domain hNe h₁ h₂ hUNd hULen
    rcases (Bool.and_eq_true _ _).mp (List.mem_filter.mp hx₀U).2 with ⟨he₁, he₂⟩
    exact hx₀Diff ((of_decide_eq_true he₁).trans (of_decide_eq_true he₂).symm)

private theorem isTrimmed_length_le_of_coeffAt_zero {F : Type} [CommRingOps F] [DecidableEq F]
    (p : List F) (d : Nat) (hTrim : IsTrimmed p) (hLen : p.length ≤ d + 2)
    (hZero : coeffAt p (d + 1) = CommRingOps.zero) :
    p.length ≤ d + 1 := by
  have hEq : trimPoly p = p := hTrim
  rw [← hEq]
  apply length_trimPoly_le_of_coeffAt_zero p (d + 1)
  intro k hk
  if hkEq : k = d + 1 then
    subst hkEq; exact hZero
  else
    exact coeffAt_eq_zero_of_ge p k (by omega)

private theorem coeffAt_polyAddVar {F : Type} [LawfulCommRing F] :
    ∀ (a b : List F) (k : Nat),
      coeffAt (polyAddVar a b) k = CommRingOps.add (coeffAt a k) (coeffAt b k)
  | [], ys, k => by
    simp only [polyAddVar, coeffAt_nil, LawfulCommRing.zero_add]
  | x :: xs, [], k => by
    simp only [polyAddVar, coeffAt_nil, LawfulCommRing.add_zero]
  | x :: xs, y :: ys, 0 => rfl
  | x :: xs, y :: ys, k + 1 => coeffAt_polyAddVar xs ys k

private theorem coeffAt_polyScaleVar {F : Type} [LawfulCommRing F] (c : F) (a : List F) (k : Nat) :
    coeffAt (polyScaleVar c a) k = CommRingOps.mul c (coeffAt a k) :=
  coeffAt_map_mul c a k

private theorem ringDot_shiftPoly_polyAddVar {F : Type} [LawfulCommRing F]
    (a b ks : List F) :
    ringDot (shiftPoly (polyAddVar a b)) ks =
      CommRingOps.add (ringDot (shiftPoly a) ks) (ringDot (shiftPoly b) ks) := by
  cases ks with
  | nil =>
    simp only [shiftPoly, ringDot, LawfulCommRing.add_zero]
  | cons k₀ ks' =>
    simp only [shiftPoly, ringDot, LawfulCommRing.zero_mul, LawfulCommRing.zero_add]
    exact ringDot_polyAddVar a b ks'

private theorem nodup_attach {α : Type} : ∀ {xs : List α}, xs.Nodup → xs.attach.Nodup
  | [], _ => .nil
  | a :: rest, hNd => by
    rcases List.pairwise_cons.mp hNd with ⟨hNotMem, hRestNd⟩
    rw [List.attach_cons]
    refine List.Pairwise.cons ?_ ?_
    · intro u hu hEq
      rcases List.mem_map.mp hu with ⟨v, _, rfl⟩
      have hVal : a = v.1 := congrArg Subtype.val hEq
      exact hNotMem v.1 v.2 hVal
    · refine List.Pairwise.map _ (fun u v huv hEq => huv ?_) (nodup_attach hRestNd)
      cases u; cases v
      injection hEq with h
      exact Subtype.ext h

/-- Cartesian challenge pool `S_θ × (S × S)` for the 3-challenge equal-degree fold `(θ, α, β)`. -/
def threePool {F : Type} (S_θ S : List F) : List (F × F × F) :=
  S_θ.flatMap (fun θ => (prodPool S).map (fun p => (θ, p.1, p.2)))

theorem threePool_length {F : Type} (S_θ S : List F) :
    (threePool S_θ S).length = S_θ.length * (S.length * S.length) := by
  unfold threePool
  induction S_θ with
  | nil => simp
  | cons _ rest ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, prodPool_length,
      List.length_cons, ih]
    rw [Nat.succ_mul, Nat.add_comm]

theorem threePool_nodup {F : Type} {S_θ S : List F} (hθ : S_θ.Nodup) (hS : S.Nodup) :
    (threePool S_θ S).Nodup := by
  have hP := prodPool_nodup hS
  unfold threePool
  induction S_θ with
  | nil => exact .nil
  | cons θ rest ih =>
    rcases List.pairwise_cons.mp hθ with ⟨hNotMem, hRestNd⟩
    simp only [List.flatMap_cons]
    refine List.nodup_append.mpr ⟨?_, ih hRestNd, ?_⟩
    · refine List.Pairwise.map _ (fun a b hab hEq => hab ?_) hP
      cases a; cases b
      injection hEq
    · intro x hx₁ y hx₂ hEq
      subst hEq
      rcases List.mem_map.mp hx₁ with ⟨_, _, rfl⟩
      rcases List.mem_flatMap.mp hx₂ with ⟨θ', hθ'Mem, hMap'⟩
      rcases List.mem_map.mp hMap' with ⟨_, _, hEq'⟩
      injection hEq' with hEqθ _
      exact hNotMem θ' hθ'Mem hEqθ.symm

private theorem mem_threePool_iff {F : Type} {S_θ S : List F} (t : F × F × F) :
    t ∈ threePool S_θ S ↔ t.1 ∈ S_θ ∧ (t.2.1, t.2.2) ∈ prodPool S := by
  unfold threePool
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨θ, hθ, hMap⟩
    rcases List.mem_map.mp hMap with ⟨p, hp, hEq⟩
    cases t with
    | mk a bc =>
      cases bc with
      | mk b c =>
        cases p with
        | mk p1 p2 =>
          injection hEq with ha hbc
          injection hbc with hb hc
          subst ha; subst hb; subst hc
          exact ⟨hθ, hp⟩
  · rintro ⟨hθ, hp⟩
    refine ⟨t.1, hθ, List.mem_map.mpr ⟨(t.2.1, t.2.2), hp, ?_⟩⟩
    cases t with
    | mk a bc => cases bc; rfl

/-- **Standalone `θ`-Exception Bound for Equal-Degree Claim Mixing (`equal_degree_bad_theta_count_le`)**:
    When `0 ∈ S` and `S_θ ⊆ S`, if `(f, e_f)` or `(g, e_g)` has no valid degree-`≤ d` witness at
    agreement `A - 1` on `D`, then at most
    `badMca0 + (gsDecodeList d (A - 1) D f).length * (gsDecodeList d (A - 1) D g).length`
    indices `i ∈ S_θ` allow the mixed word `f + θ g` to acquire a degree-`≤ d` witness `H` at
    agreement `A` with `ringDot H kernel = e_f + θ e_g`. -/
theorem equal_degree_bad_theta_count_le {F : Type} [LawfulField F] [DecidableEq F]
    (D S_θ S kernel : List F) (d A badMca0 : Nat)
    (f g : F → F) (e_f e_g : F)
    (hD : D.Nodup) (hSθ : S_θ.Nodup)
    (h0Mem : CommRingOps.zero ∈ S) (hSubθ : ∀ θ ∈ S_θ, θ ∈ S)
    (hdA : d + 2 ≤ A)
    (hDecomp0 : AffineFoldDecompBound D S (d + 1) A badMca0)
    (hInvalidFG :
      (∀ Fw : List F, Fw.length ≤ d + 1 →
        A - 1 ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs Fw z = f z))).length →
        ringDot Fw kernel ≠ e_f) ∨
      (∀ Gw : List F, Gw.length ≤ d + 1 →
        A - 1 ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs Gw z = g z))).length →
        ringDot Gw kernel ≠ e_g))
    (L_θ : List (Fin S_θ.length)) (hNd : L_θ.Nodup)
    (hMixValid : ∀ i ∈ L_θ, ¬¬ ∃ H : List F,
      H.length ≤ d + 1 ∧
      A ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs H z =
        CommRingOps.add (f z) (CommRingOps.mul (S_θ.get i) (g z))))).length ∧
      ringDot H kernel = CommRingOps.add e_f (CommRingOps.mul (S_θ.get i) e_g)) :
    L_θ.length ≤ badMca0 +
      (gsDecodeList d (A - 1) D f).length * (gsDecodeList d (A - 1) D g).length := by
  let candF := gsDecodeList d (A - 1) D f
  let candG := gsDecodeList d (A - 1) D g
  let pairsFG := candF.flatMap (fun pF => candG.map (fun pG => (pF, pG)))
  have hPairsLen : pairsFG.length = candF.length * candG.length := by
    dsimp only [pairsFG]
    clear hMixValid hNd L_θ hDecomp0 hInvalidFG
    induction candF with
    | nil => simp
    | cons _ rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons, ih]
      rw [Nat.succ_mul, Nat.add_comm]
  let matchPair : GsUniPoly F × GsUniPoly F → Fin S_θ.length → Bool :=
    fun fg i =>
      let θ := S_θ.get i
      decide (CommRingOps.add (CommRingOps.sub (ringDot fg.1.val kernel) e_f)
        (CommRingOps.mul θ (CommRingOps.sub (ringDot fg.2.val kernel) e_g)) = CommRingOps.zero)
  let anyMatch : Fin S_θ.length → Bool := fun i => pairsFG.any (fun fg => matchPair fg i)
  have hSplit := length_filter_add_not anyMatch L_θ
  have hMatchLe : (L_θ.filter anyMatch).length ≤ pairsFG.length * 1 := by
    refine filter_any_length_le pairsFG matchPair L_θ 1 ?_
    intro fg hfg
    rcases List.mem_flatMap.mp hfg with ⟨pF, hpFMem, hInG⟩
    rcases List.mem_map.mp hInG with ⟨pG, hpGMem, rfl⟩
    have hpFProps := (mem_gsDecodeList_iff f hD (by omega) pF).mp hpFMem
    have hpGProps := (mem_gsDecodeList_iff g hD (by omega) pG).mp hpGMem
    let Δ_f := CommRingOps.sub (ringDot pF.val kernel) e_f
    let Δ_g := CommRingOps.sub (ringDot pG.val kernel) e_g
    have hNzFG : Δ_f ≠ CommRingOps.zero ∨ Δ_g ≠ CommRingOps.zero := by
      rcases hInvalidFG with hInvF | hInvG
      · exact .inl (fun h0 => hInvF pF.val hpFProps.1 hpFProps.2 (LawfulCommRing.sub_eq_zero_iff.mp h0))
      · exact .inr (fun h0 => hInvG pG.val hpGProps.1 hpGProps.2 (LawfulCommRing.sub_eq_zero_iff.mp h0))
    if hΔg : Δ_g ≠ CommRingOps.zero then
      have hMapNd : ((L_θ.filter (matchPair (pF, pG))).map (fun i => S_θ.get i)).Nodup :=
        List.Pairwise.map _ (fun a b hab hEq => hab (nodup_get_inj hSθ hEq))
          (List.Pairwise.filter _ hNd)
      have hSub : ∀ θ ∈ (L_θ.filter (matchPair (pF, pG))).map (fun i => S_θ.get i),
          θ ∈ S_θ.filter (fun θ => decide (CommRingOps.add Δ_f (CommRingOps.mul θ Δ_g) = CommRingOps.zero)) := by
        intro θ hθ
        rcases List.mem_map.mp hθ with ⟨i, hiF, rfl⟩
        exact List.mem_filter.mpr ⟨list_get_mem S_θ i, (List.mem_filter.mp hiF).2⟩
      have hLenMap := nodup_length_le_of_subset hMapNd hSub
      rw [List.length_map] at hLenMap
      exact Nat.le_trans hLenMap (linear_one_var_bad_le_one S_θ hSθ Δ_f Δ_g hΔg)
    else
      have hΔg0 : Δ_g = CommRingOps.zero := Decidable.of_not_not hΔg
      have hΔfNe : Δ_f ≠ CommRingOps.zero := by
        rcases hNzFG with h1 | h2
        · exact h1
        · exact False.elim (hΔg h2)
      have hEmpty : L_θ.filter (matchPair (pF, pG)) = [] := by
        apply filter_eq_nil_of_false
        intro i _
        dsimp only [matchPair]
        change decide (CommRingOps.add Δ_f (CommRingOps.mul (S_θ.get i) Δ_g) = CommRingOps.zero) = false
        rw [hΔg0, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
        exact decide_eq_false hΔfNe
      rw [hEmpty]; exact Nat.zero_le 1
  let toPoolIdx : Fin S_θ.length → Fin (prodPool S).length := fun i =>
    let target := (S_θ.get i, CommRingOps.zero)
    have hMem : target ∈ prodPool S := by
      unfold prodPool
      exact List.mem_flatMap.mpr ⟨S_θ.get i, hSubθ _ (list_get_mem S_θ i),
        List.mem_map.mpr ⟨CommRingOps.zero, h0Mem, rfl⟩⟩
    ⟨(prodPool S).idxOf target, List.idxOf_lt_length_of_mem hMem⟩
  have hPoolGet : ∀ i : Fin S_θ.length,
      (prodPool S).get (toPoolIdx i) = (S_θ.get i, CommRingOps.zero) := by
    intro i
    dsimp only [toPoolIdx]
    exact List.getElem_idxOf _
  let L_non := L_θ.filter (fun i => !anyMatch i)
  have hMapPoolNd : (L_non.map toPoolIdx).Nodup := by
    refine List.Pairwise.map _ (fun a b hab hEq => hab ?_) (List.Pairwise.filter _ hNd)
    have h1 := hPoolGet a
    have h2 := hPoolGet b
    rw [hEq] at h1
    have hPairEq := h1.symm.trans h2
    injection hPairEq with hθEq _
    exact nodup_get_inj hSθ hθEq
  have hNonMatchLe : (L_non.map toPoolIdx).length ≤ badMca0 := by
    refine hDecomp0 (f, g) (L_non.map toPoolIdx) hMapPoolNd ?_
    intro ch hch hNo
    rcases List.mem_map.mp hch with ⟨i, hiNon, rfl⟩
    rcases List.mem_filter.mp hiNon with ⟨hiL, hNotAny⟩
    refine hMixValid i hiL ?_
    rintro ⟨H, hHLen, hHAg, hHDot⟩
    refine hNo ⟨H, ?_, ?_⟩
    · unfold affineMcaAccepts
      rw [list_getD_eq_get (prodPool S) _ (toPoolIdx i), hPoolGet i]
      have hSubLen : H.length ≤ d + 2 := by omega
      have hIdxLt : (toPoolIdx i).1 < (prodPool S).length := (toPoolIdx i).2
      have hFiltEq : D.filter (fun z => decide (RoundPoly.evalCoeffs H z =
          CommRingOps.add (f z) (CommRingOps.mul (CommRingOps.add (S_θ.get i)
            (CommRingOps.mul CommRingOps.zero z)) (g z)))) =
          D.filter (fun z => decide (RoundPoly.evalCoeffs H z =
            CommRingOps.add (f z) (CommRingOps.mul (S_θ.get i) (g z)))) := by
        apply congrArg (fun q => List.filter q D)
        funext z
        rw [LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
      rw [hFiltEq]
      simp only [hIdxLt, hSubLen, hHAg, decide_true, Bool.and_self]
    · rintro ⟨F_poly, G_poly, ⟨hFLen, hGLen, hJoint⟩, hTrimEq⟩
      rw [hPoolGet i] at hTrimEq
      let pF : GsUniPoly F := GsUniPoly.ofCoeffs F_poly
      let pG : GsUniPoly F := GsUniPoly.ofCoeffs G_poly
      have hpFLen : pF.val.length ≤ d + 1 := by
        refine isTrimmed_length_le_of_coeffAt_zero pF.val d pF.property
          (Nat.le_trans (trimPoly_length_le F_poly) hFLen) ?_
        have hc := congrArg (fun u => coeffAt u (d + 1)) hTrimEq
        rw [coeffAt_trimPoly, coeffAt_trimPoly, coeffAt_polyAddVar, coeffAt_polyAddVar,
            coeffAt_polyScaleVar, coeffAt_polyScaleVar, LawfulCommRing.zero_mul, LawfulCommRing.add_zero,
            coeffAt_eq_zero_of_ge H (d + 1) hHLen,
            coeffAt_eq_zero_of_ge G_poly (d + 1) hGLen,
            LawfulCommRing.mul_zero, LawfulCommRing.add_zero] at hc
        change coeffAt (trimPoly F_poly) (d + 1) = CommRingOps.zero
        rw [coeffAt_trimPoly]
        exact hc.symm
      have hJointF : A - 1 ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs pF.val z = f z))).length := by
        have hSub : ∀ z ∈ D.filter (fun z =>
            decide (RoundPoly.evalCoeffs F_poly z = f z) &&
            decide (RoundPoly.evalCoeffs G_poly z = g z)),
            z ∈ D.filter (fun z => decide (RoundPoly.evalCoeffs pF.val z = f z)) := by
          intro z hz
          rcases List.mem_filter.mp hz with ⟨hzD, hB⟩
          refine List.mem_filter.mpr ⟨hzD, decide_eq_true ?_⟩
          change RoundPoly.evalCoeffs (trimPoly F_poly) z = f z
          rw [evalCoeffs_trimPoly]
          exact of_decide_eq_true ((Bool.and_eq_true _ _).mp hB).1
        exact Nat.le_trans hJoint (nodup_length_le_of_subset (List.Pairwise.filter _ hD) hSub)
      have hJointG : A - 1 ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs pG.val z = g z))).length := by
        have hSub : ∀ z ∈ D.filter (fun z =>
            decide (RoundPoly.evalCoeffs F_poly z = f z) &&
            decide (RoundPoly.evalCoeffs G_poly z = g z)),
            z ∈ D.filter (fun z => decide (RoundPoly.evalCoeffs pG.val z = g z)) := by
          intro z hz
          rcases List.mem_filter.mp hz with ⟨hzD, hB⟩
          refine List.mem_filter.mpr ⟨hzD, decide_eq_true ?_⟩
          change RoundPoly.evalCoeffs (trimPoly G_poly) z = g z
          rw [evalCoeffs_trimPoly]
          exact of_decide_eq_true ((Bool.and_eq_true _ _).mp hB).2
        exact Nat.le_trans hJoint (nodup_length_le_of_subset (List.Pairwise.filter _ hD) hSub)
      have hpFMem : pF ∈ candF :=
        (mem_gsDecodeList_iff f hD (by omega) pF).mpr ⟨hpFLen, hJointF⟩
      have hpGMem : pG ∈ candG :=
        (mem_gsDecodeList_iff g hD (by omega) pG).mpr
          ⟨Nat.le_trans (trimPoly_length_le G_poly) hGLen, hJointG⟩
      have hMemPairs : (pF, pG) ∈ pairsFG :=
        List.mem_flatMap.mpr ⟨pF, hpFMem, List.mem_map.mpr ⟨pG, hpGMem, rfl⟩⟩
      have hMatchTrue : matchPair (pF, pG) i = true := by
        dsimp only [matchPair]
        apply decide_eq_true
        have hDot := congrArg (fun u => ringDot u kernel) hTrimEq
        rw [ringDot_trimPoly_eq, ringDot_trimPoly_eq,
            ringDot_polyAddVar, ringDot_polyAddVar,
            ringDot_polyScaleVar, ringDot_polyScaleVar,
            LawfulCommRing.zero_mul, LawfulCommRing.add_zero] at hDot
        change CommRingOps.add (CommRingOps.sub (ringDot (trimPoly F_poly) kernel) e_f)
          (CommRingOps.mul (S_θ.get i) (CommRingOps.sub (ringDot (trimPoly G_poly) kernel) e_g)) =
          CommRingOps.zero
        rw [ringDot_trimPoly_eq, ringDot_trimPoly_eq]
        have hEqCl : CommRingOps.add (ringDot F_poly kernel)
            (CommRingOps.mul (S_θ.get i) (ringDot G_poly kernel)) =
            CommRingOps.add e_f (CommRingOps.mul (S_θ.get i) e_g) := hDot.symm.trans hHDot
        have hId : CommRingOps.add (CommRingOps.sub (ringDot F_poly kernel) e_f)
            (CommRingOps.mul (S_θ.get i) (CommRingOps.sub (ringDot G_poly kernel) e_g)) =
          CommRingOps.sub
            (CommRingOps.add (ringDot F_poly kernel) (CommRingOps.mul (S_θ.get i) (ringDot G_poly kernel)))
            (CommRingOps.add e_f (CommRingOps.mul (S_θ.get i) e_g)) := by
          constructive_ring
        rw [hId, hEqCl, LawfulCommRing.sub_self]
      have hAnyTrue : anyMatch i = true := List.any_eq_true.mpr ⟨(pF, pG), hMemPairs, hMatchTrue⟩
      rw [hAnyTrue] at hNotAny
      exact absurd hNotAny (by decide)
  rw [List.length_map] at hNonMatchLe
  rw [hPairsLen, Nat.mul_one] at hMatchLe
  dsimp only [candF, candG, L_non] at hMatchLe hNonMatchLe
  omega

/-- **Unconditional Three-Challenge Equal-Degree Claim-Fold Bound (`[CWYZ26]` Theorem 5.1 Lift)**:
    Over any `[LawfulField F] [DecidableEq F]`, if `(f, e_f)` or `(g, e_g)` has NO valid degree-`≤ d`
    witness at agreement `A` on `D` (`D.Nodup`, `d + 2 ≤ A`), then WITHOUT any `hInvalidMix` premise,
    the number of challenge triples `(θ, α, β) ∈ threePool S_θ S` (`S_θ.Nodup`, `S.Nodup`) yielding a
    post-fold witness `P` (`P.length ≤ d + 2`, agreement `≥ A + 1` with `g + (α + β X)(f + θ g)`, and
    `ringDot P kernel = hemFoldClaimUpdate e_f e_g c_f c_g θ α β`) is at most:
    `S_θ.length * badMca +
     (gsDecodeList d A D f).length * (gsDecodeList d A D g).length * (S_θ.length * S.length) +
     (gsDecodeList (d + 1) A D f).length * (gsDecodeList (d + 1) A D g).length * (S.length * S.length)`. -/
theorem equal_degree_three_challenge_fold_bound {F : Type} [LawfulField F] [DecidableEq F]
    (D S_θ S kernel : List F) (d A badMca : Nat)
    (f g : F → F) (e_f e_g c_f c_g : F)
    (hD : D.Nodup) (hSθ : S_θ.Nodup) (hS : S.Nodup) (hdA : d + 2 ≤ A)
    (hDecomp : AffineFoldDecompBound D S (d + 1) (A + 1) badMca)
    (hInvalidFG :
      (∀ Fw : List F, Fw.length ≤ d + 1 →
        A ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs Fw z = f z))).length →
        ringDot Fw kernel ≠ e_f) ∨
      (∀ Gw : List F, Gw.length ≤ d + 1 →
        A ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs Gw z = g z))).length →
        ringDot Gw kernel ≠ e_g))
    (L : List (Fin (threePool S_θ S).length)) (hNd : L.Nodup)
    (hFlip : ∀ ch ∈ L, ¬¬ ∃ P : List F,
      P.length ≤ d + 2 ∧
      A + 1 ≤ (D.filter (fun z =>
        let t := (threePool S_θ S).get ch
        let h_θ := CommRingOps.add (f z) (CommRingOps.mul t.1 (g z))
        decide (RoundPoly.evalCoeffs P z =
          CommRingOps.add (g z)
            (CommRingOps.mul (CommRingOps.add t.2.1 (CommRingOps.mul t.2.2 z)) h_θ)))).length ∧
      ringDot P kernel =
        let t := (threePool S_θ S).get ch
        hemFoldClaimUpdate e_f e_g c_f c_g t.1 t.2.1 t.2.2) :
    L.length ≤ S_θ.length * badMca +
      (gsDecodeList d A D f).length * (gsDecodeList d A D g).length * (S_θ.length * S.length) +
      (gsDecodeList (d + 1) A D f).length * (gsDecodeList (d + 1) A D g).length *
        (S.length * S.length) := by
  let T : List (F × F × F) := L.map (fun ch => (threePool S_θ S).get ch)
  have hTLen : T.length = L.length := List.length_map _
  have hTNd : T.Nodup :=
    List.Pairwise.map _ (fun a b hab hEq => hab (nodup_get_inj (threePool_nodup hSθ hS) hEq)) hNd
  have hTMemPool : ∀ t ∈ T, t.1 ∈ S_θ ∧ (t.2.1, t.2.2) ∈ prodPool S := by
    intro t ht
    rcases List.mem_map.mp ht with ⟨ch, _, rfl⟩
    exact (mem_threePool_iff _).mp (list_get_mem _ ch)
  have hTFlip : ∀ t ∈ T, ¬¬ ∃ P : List F,
      P.length ≤ d + 2 ∧
      A + 1 ≤ (D.filter (fun z =>
        let h_θ := CommRingOps.add (f z) (CommRingOps.mul t.1 (g z))
        decide (RoundPoly.evalCoeffs P z =
          CommRingOps.add (g z)
            (CommRingOps.mul (CommRingOps.add t.2.1 (CommRingOps.mul t.2.2 z)) h_θ)))).length ∧
      ringDot P kernel = hemFoldClaimUpdate e_f e_g c_f c_g t.1 t.2.1 t.2.2 := by
    intro t ht
    rcases List.mem_map.mp ht with ⟨ch, hchL, rfl⟩
    exact hFlip ch hchL
  let candFLo := gsDecodeList d A D f
  let candGLo := gsDecodeList d A D g
  let candFHi := gsDecodeList (d + 1) A D f
  let candGHi := gsDecodeList (d + 1) A D g
  let pairsLo := candFLo.flatMap (fun pF => candGLo.map (fun pG => (pF, pG)))
  let pairsHi := candFHi.flatMap (fun pF => candGHi.map (fun pG => (pF, pG)))
  have hPairsLoLen : pairsLo.length = candFLo.length * candGLo.length := by
    dsimp only [pairsLo]
    clear hTFlip hTMemPool hTNd hTLen T hFlip hNd L hDecomp hInvalidFG
    induction candFLo with
    | nil => simp
    | cons _ rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons, ih]
      rw [Nat.succ_mul, Nat.add_comm]
  have hPairsHiLen : pairsHi.length = candFHi.length * candGHi.length := by
    dsimp only [pairsHi]
    clear hTFlip hTMemPool hTNd hTLen T hFlip hNd L hDecomp hInvalidFG
    induction candFHi with
    | nil => simp
    | cons _ rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons, ih]
      rw [Nat.succ_mul, Nat.add_comm]
  let matchLo : GsUniPoly F × GsUniPoly F → F × F × F → Bool :=
    fun fg t =>
      let γF := ringDot fg.1.val kernel
      let γG := ringDot fg.2.val kernel
      let sF := ringDot (shiftPoly fg.1.val) kernel
      let sG := ringDot (shiftPoly fg.2.val) kernel
      decide (CommRingOps.add γG
        (CommRingOps.add
          (CommRingOps.mul t.2.1 (CommRingOps.add γF (CommRingOps.mul t.1 γG)))
          (CommRingOps.mul t.2.2 (CommRingOps.add sF (CommRingOps.mul t.1 sG)))) =
        hemFoldClaimUpdate e_f e_g c_f c_g t.1 t.2.1 t.2.2)
  let matchOv : GsUniPoly F × GsUniPoly F → F × F × F → Bool :=
    fun fg t =>
      decide (coeffAt fg.1.val (d + 1) ≠ CommRingOps.zero ∨
        coeffAt fg.2.val (d + 1) ≠ CommRingOps.zero) &&
      decide (CommRingOps.add (coeffAt fg.1.val (d + 1))
        (CommRingOps.mul t.1 (coeffAt fg.2.val (d + 1))) = CommRingOps.zero)
  let anyLo : F × F × F → Bool := fun t => pairsLo.any (fun fg => matchLo fg t)
  let anyOv : F × F × F → Bool := fun t => pairsHi.any (fun fg => matchOv fg t)
  let anyAll : F × F × F → Bool := fun t => anyLo t || anyOv t
  have hSplitAll := length_filter_add_not anyAll T
  have hSubUnion : (T.filter anyAll).length ≤ (T.filter anyLo).length + (T.filter anyOv).length :=
    JohnsonBound.filter_length_le_add anyAll anyLo anyOv T (fun _ _ h => Bool.or_eq_true_iff.mp h)
  -- 1. Bound `T.filter anyLo`: each `(pF, pG) ∈ pairsLo` contributes at most `S_θ.length * S.length`:
  have hLoBound : (T.filter anyLo).length ≤ pairsLo.length * (S_θ.length * S.length) := by
    refine filter_any_length_le pairsLo matchLo T (S_θ.length * S.length) ?_
    intro fg hfg
    rcases List.mem_flatMap.mp hfg with ⟨pF, hpFMem, hInG⟩
    rcases List.mem_map.mp hInG with ⟨pG, hpGMem, rfl⟩
    have hpFProps := (mem_gsDecodeList_iff f hD (by omega) pF).mp hpFMem
    have hpGProps := (mem_gsDecodeList_iff g hD (by omega) pG).mp hpGMem
    have hNeFG : ringDot pF.val kernel ≠ e_f ∨ ringDot pG.val kernel ≠ e_g := by
      rcases hInvalidFG with hInvF | hInvG
      · exact .inl (hInvF pF.val hpFProps.1 hpFProps.2)
      · exact .inr (hInvG pG.val hpGProps.1 hpGProps.2)
    let subT := T.filter (matchLo (pF, pG))
    refine JohnsonBound.count_partition_le (fun t => t.1) S.length subT S_θ ?_ ?_
    · intro t ht
      exact (hTMemPool t (List.mem_filter.mp ht).1).1
    · intro θ _
      let fib := subT.filter (fun t => decide (t.1 = θ))
      let Δ₀ := CommRingOps.sub (ringDot pG.val kernel) e_g
      let Δ_α := CommRingOps.add (CommRingOps.sub (ringDot pF.val kernel) e_f)
        (CommRingOps.mul θ Δ₀)
      let Δ_β := CommRingOps.sub
        (CommRingOps.add (ringDot (shiftPoly pF.val) kernel)
          (CommRingOps.mul θ (ringDot (shiftPoly pG.val) kernel)))
        (CommRingOps.add c_f (CommRingOps.mul θ c_g))
      have hNz : Δ₀ ≠ CommRingOps.zero ∨ Δ_α ≠ CommRingOps.zero := by
        if h0 : Δ₀ = CommRingOps.zero then
          right
          intro hα0
          have hEg : ringDot pG.val kernel = e_g := LawfulCommRing.sub_eq_zero_iff.mp h0
          have hEf0 : CommRingOps.sub (ringDot pF.val kernel) e_f = CommRingOps.zero := by
            dsimp only [Δ_α] at hα0
            rw [h0, LawfulCommRing.mul_zero, LawfulCommRing.add_zero] at hα0
            exact hα0
          have hEf : ringDot pF.val kernel = e_f := LawfulCommRing.sub_eq_zero_iff.mp hEf0
          rcases hNeFG with h1 | h2
          · exact h1 hEf
          · exact h2 hEg
        else
          exact .inl h0
      have hFibNd : fib.Nodup := List.Pairwise.filter _ (List.Pairwise.filter _ hTNd)
      let projPairs := fib.attach.map (fun u => (u.1.2.1, u.1.2.2))
      have hProjNd : projPairs.Nodup := by
        refine List.Pairwise.map _ (fun u v huv hEq => huv ?_) (nodup_attach hFibNd)
        apply Subtype.ext
        have huθ : u.1.1 = θ := of_decide_eq_true (List.mem_filter.mp u.2).2
        have hvθ : v.1.1 = θ := of_decide_eq_true (List.mem_filter.mp v.2).2
        cases u with
        | mk tu hu =>
          cases v with
          | mk tv hv =>
            cases tu with
            | mk u1 u23 =>
              cases u23 with
              | mk u2 u3 =>
                cases tv with
                | mk v1 v23 =>
                  cases v23 with
                  | mk v2 v3 =>
                    dsimp only at huθ hvθ hEq
                    injection hEq with h2 h3
                    subst huθ; subst hvθ; subst h2; subst h3; rfl
      have hSubPool : ∀ p ∈ projPairs,
          p ∈ (prodPool S).filter (fun p =>
            decide (CommRingOps.add Δ₀
              (CommRingOps.add (CommRingOps.mul p.1 Δ_α) (CommRingOps.mul p.2 Δ_β)) =
                CommRingOps.zero)) := by
        intro p hp
        rcases List.mem_map.mp hp with ⟨⟨t, htFib⟩, _, rfl⟩
        rcases List.mem_filter.mp htFib with ⟨htSub, htθDec⟩
        have htθ : t.1 = θ := of_decide_eq_true htθDec
        rcases List.mem_filter.mp htSub with ⟨htT, htMatch⟩
        have hpMem : (t.2.1, t.2.2) ∈ prodPool S := (hTMemPool t htT).2
        refine List.mem_filter.mpr ⟨hpMem, decide_eq_true ?_⟩
        have hEqCl := of_decide_eq_true htMatch
        rw [htθ] at hEqCl
        dsimp only [Δ₀, Δ_α, Δ_β]
        unfold hemFoldClaimUpdate at hEqCl
        have hId :
            CommRingOps.add (CommRingOps.sub (ringDot pG.val kernel) e_g)
              (CommRingOps.add
                (CommRingOps.mul t.2.1
                  (CommRingOps.add (CommRingOps.sub (ringDot pF.val kernel) e_f)
                    (CommRingOps.mul θ (CommRingOps.sub (ringDot pG.val kernel) e_g))))
                (CommRingOps.mul t.2.2
                  (CommRingOps.sub
                    (CommRingOps.add (ringDot (shiftPoly pF.val) kernel)
                      (CommRingOps.mul θ (ringDot (shiftPoly pG.val) kernel)))
                    (CommRingOps.add c_f (CommRingOps.mul θ c_g))))) =
            CommRingOps.sub
              (CommRingOps.add (ringDot pG.val kernel)
                (CommRingOps.add
                  (CommRingOps.mul t.2.1
                    (CommRingOps.add (ringDot pF.val kernel) (CommRingOps.mul θ (ringDot pG.val kernel))))
                  (CommRingOps.mul t.2.2
                    (CommRingOps.add (ringDot (shiftPoly pF.val) kernel)
                      (CommRingOps.mul θ (ringDot (shiftPoly pG.val) kernel))))))
              (CommRingOps.add e_g
                (CommRingOps.add
                  (CommRingOps.mul t.2.1 (CommRingOps.add e_f (CommRingOps.mul θ e_g)))
                  (CommRingOps.mul t.2.2 (CommRingOps.add c_f (CommRingOps.mul θ c_g))))) := by
          constructive_ring
        rw [hId, hEqCl, LawfulCommRing.sub_self]
      have hLenProj := nodup_length_le_of_subset hProjNd hSubPool
      have hProjLenEq : projPairs.length = fib.length := by
        dsimp only [projPairs]
        rw [List.length_map, List.length_attach]
      rw [hProjLenEq] at hLenProj
      exact Nat.le_trans hLenProj (absorbed_linear_claim_bad_pairs_le_card S hS Δ₀ Δ_α Δ_β hNz)
  -- 2. Bound `T.filter anyOv`: each `(pF, pG) ∈ pairsHi` with overflow has at most `1` valid `θ`,
  --    hence at most `1 * (S.length * S.length)` triples in `T`:
  have hOvBound : (T.filter anyOv).length ≤ pairsHi.length * (S.length * S.length) := by
    refine filter_any_length_le pairsHi matchOv T (S.length * S.length) ?_
    intro fg hfg
    rcases List.mem_flatMap.mp hfg with ⟨pF, _, hInG⟩
    rcases List.mem_map.mp hInG with ⟨pG, _, rfl⟩
    let cF := coeffAt pF.val (d + 1)
    let cG := coeffAt pG.val (d + 1)
    let subT := T.filter (matchOv (pF, pG))
    let goodθ := S_θ.filter (fun θ =>
      decide (cF ≠ CommRingOps.zero ∨ cG ≠ CommRingOps.zero) &&
      decide (CommRingOps.add cF (CommRingOps.mul θ cG) = CommRingOps.zero))
    have hGoodθLe1 : goodθ.length ≤ 1 := by
      if hcG : cG ≠ CommRingOps.zero then
        have hSub : ∀ θ ∈ goodθ,
            θ ∈ S_θ.filter (fun θ => decide (CommRingOps.add cF (CommRingOps.mul θ cG) = CommRingOps.zero)) := by
          intro θ hθ
          rcases List.mem_filter.mp hθ with ⟨hθS, hBoth⟩
          exact List.mem_filter.mpr ⟨hθS, ((Bool.and_eq_true _ _).mp hBoth).2⟩
        exact Nat.le_trans
          (nodup_length_le_of_subset (List.Pairwise.filter _ hSθ) hSub)
          (linear_one_var_bad_le_one S_θ hSθ cF cG hcG)
      else
        have hcG0 : cG = CommRingOps.zero := Decidable.of_not_not hcG
        have hEmpty : goodθ = [] := by
          apply filter_eq_nil_of_false
          intro θ _
          cases hOr : decide (cF ≠ CommRingOps.zero ∨ cG ≠ CommRingOps.zero)
          · rfl
          · simp only [Bool.true_and]
            have hcFNe : cF ≠ CommRingOps.zero := by
              rcases of_decide_eq_true hOr with h1 | h2
              · exact h1
              · exact False.elim (hcG h2)
            rw [hcG0, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
            exact decide_eq_false hcFNe
        rw [hEmpty]; exact Nat.zero_le 1
    have hPart := JohnsonBound.count_partition_le (fun t => t.1) (S.length * S.length) subT goodθ ?_ ?_
    · exact Nat.le_trans hPart (by
        have hMul := Nat.mul_le_mul_right (S.length * S.length) hGoodθLe1
        rw [Nat.one_mul] at hMul
        exact hMul)
    · intro t ht
      rcases List.mem_filter.mp ht with ⟨htT, htOv⟩
      exact List.mem_filter.mpr ⟨(hTMemPool t htT).1, htOv⟩
    · intro θ _
      let fib := subT.filter (fun t => decide (t.1 = θ))
      have hFibNd : fib.Nodup := List.Pairwise.filter _ (List.Pairwise.filter _ hTNd)
      let projPairs := fib.attach.map (fun u => (u.1.2.1, u.1.2.2))
      have hProjNd : projPairs.Nodup := by
        refine List.Pairwise.map _ (fun u v huv hEq => huv ?_) (nodup_attach hFibNd)
        apply Subtype.ext
        have huθ : u.1.1 = θ := of_decide_eq_true (List.mem_filter.mp u.2).2
        have hvθ : v.1.1 = θ := of_decide_eq_true (List.mem_filter.mp v.2).2
        cases u with
        | mk tu hu =>
          cases v with
          | mk tv hv =>
            cases tu with
            | mk u1 u23 =>
              cases u23 with
              | mk u2 u3 =>
                cases tv with
                | mk v1 v23 =>
                  cases v23 with
                  | mk v2 v3 =>
                    dsimp only at huθ hvθ hEq
                    injection hEq with h2 h3
                    subst huθ; subst hvθ; subst h2; subst h3; rfl
      have hSubP : ∀ p ∈ projPairs, p ∈ prodPool S := by
        intro p hp
        rcases List.mem_map.mp hp with ⟨⟨t, htFib⟩, _, rfl⟩
        exact (hTMemPool t (List.mem_filter.mp (List.mem_filter.mp htFib).1).1).2
      have hLen := nodup_length_le_of_subset hProjNd hSubP
      have hProjLenEq : projPairs.length = fib.length := by
        dsimp only [projPairs]
        rw [List.length_map, List.length_attach]
      rw [hProjLenEq, prodPool_length] at hLen
      exact hLen
  -- 3. Bound `T.filter (!anyAll ·)` via `hDecomp` fiberwise over `θ ∈ S_θ`:
  let T_non := T.filter (fun t => !anyAll t)
  have hNonBound : T_non.length ≤ S_θ.length * badMca := by
    refine JohnsonBound.count_partition_le (fun t => t.1) badMca T_non S_θ ?_ ?_
    · intro t ht
      exact (hTMemPool t (List.mem_filter.mp ht).1).1
    · intro θ _
      let fib := T_non.filter (fun t => decide (t.1 = θ))
      have hFibNd : fib.Nodup := List.Pairwise.filter _ (List.Pairwise.filter _ hTNd)
      let toIdx : { t : F × F × F // t ∈ fib } → Fin (prodPool S).length := fun u =>
        let p := (u.1.2.1, u.1.2.2)
        have hpMem : p ∈ prodPool S :=
          (hTMemPool u.1 (List.mem_filter.mp (List.mem_filter.mp u.2).1).1).2
        ⟨(prodPool S).idxOf p, List.idxOf_lt_length_of_mem hpMem⟩
      have hToIdxGet : ∀ u : { t : F × F × F // t ∈ fib },
          (prodPool S).get (toIdx u) = (u.1.2.1, u.1.2.2) := by
        intro u
        dsimp only [toIdx]
        exact List.getElem_idxOf _
      let idxList := fib.attach.map toIdx
      have hIdxNd : idxList.Nodup := by
        refine List.Pairwise.map _ (fun u v huv hEq => huv ?_) (nodup_attach hFibNd)
        apply Subtype.ext
        have h1 := hToIdxGet u
        have h2 := hToIdxGet v
        rw [hEq] at h1
        have hpEq := h1.symm.trans h2
        have huθ : u.1.1 = θ := of_decide_eq_true (List.mem_filter.mp u.2).2
        have hvθ : v.1.1 = θ := of_decide_eq_true (List.mem_filter.mp v.2).2
        cases u with
        | mk tu hu =>
          cases v with
          | mk tv hv =>
            cases tu with
            | mk u1 u23 =>
              cases u23 with
              | mk u2 u3 =>
                cases tv with
                | mk v1 v23 =>
                  cases v23 with
                  | mk v2 v3 =>
                    dsimp only at huθ hvθ hpEq
                    injection hpEq with h2' h3'
                    subst huθ; subst hvθ; subst h2'; subst h3'; rfl
      have hDecompFib : idxList.length ≤ badMca := by
        refine hDecomp (g, fun z => CommRingOps.add (f z) (CommRingOps.mul θ (g z))) idxList hIdxNd ?_
        intro ch hch hNo
        rcases List.mem_map.mp hch with ⟨u, _, rfl⟩
        rcases List.mem_filter.mp u.2 with ⟨huNon, huθDec⟩
        have huθ : u.1.1 = θ := of_decide_eq_true huθDec
        rcases List.mem_filter.mp huNon with ⟨huT, hNotAll⟩
        refine hTFlip u.1 huT ?_
        rintro ⟨P, hPLen, hPAg, hPCl⟩
        refine hNo ⟨P, ?_, ?_⟩
        · unfold affineMcaAccepts
          rw [list_getD_eq_get (prodPool S) _ (toIdx u), hToIdxGet u]
          have hLt : (toIdx u).1 < (prodPool S).length := (toIdx u).2
          rw [huθ] at hPAg
          simp only [hLt, hPLen, hPAg, decide_true, Bool.and_self]
        · rintro ⟨G_poly, H_poly, ⟨hGLen, hHLen, hJoint⟩, hTrimEq⟩
          rw [hToIdxGet u] at hTrimEq
          let F_poly := polyAddVar H_poly (polyScaleVar (CommRingOps.neg θ) G_poly)
          have hScaleLen : (polyScaleVar (CommRingOps.neg θ) G_poly).length ≤ d + 2 := by
            simp only [polyScaleVar, List.length_map]; exact hGLen
          have hFLen : F_poly.length ≤ d + 2 :=
            polyAddVar_length_le H_poly (polyScaleVar (CommRingOps.neg θ) G_poly) (d + 2) (by omega) hScaleLen
          let pF : GsUniPoly F := GsUniPoly.ofCoeffs F_poly
          let pG : GsUniPoly F := GsUniPoly.ofCoeffs G_poly
          have hJointF : A ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs pF.val z = f z))).length := by
            have hSub : ∀ z ∈ D.filter (fun z =>
                decide (RoundPoly.evalCoeffs G_poly z = g z) &&
                decide (RoundPoly.evalCoeffs H_poly z = CommRingOps.add (f z) (CommRingOps.mul θ (g z)))),
                z ∈ D.filter (fun z => decide (RoundPoly.evalCoeffs pF.val z = f z)) := by
              intro z hz
              rcases List.mem_filter.mp hz with ⟨hzD, hB⟩
              rcases (Bool.and_eq_true _ _).mp hB with ⟨hGzDec, hHzDec⟩
              have hGz := of_decide_eq_true hGzDec
              have hHz := of_decide_eq_true hHzDec
              refine List.mem_filter.mpr ⟨hzD, decide_eq_true ?_⟩
              change RoundPoly.evalCoeffs (trimPoly F_poly) z = f z
              rw [evalCoeffs_trimPoly]
              dsimp only [F_poly]
              rw [evalCoeffs_polyAddVar, evalCoeffs_polyScaleVar, hHz, hGz]
              constructive_ring
            exact Nat.le_trans hJoint (nodup_length_le_of_subset (List.Pairwise.filter _ hD) hSub)
          have hJointG : A ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs pG.val z = g z))).length := by
            have hSub : ∀ z ∈ D.filter (fun z =>
                decide (RoundPoly.evalCoeffs G_poly z = g z) &&
                decide (RoundPoly.evalCoeffs H_poly z = CommRingOps.add (f z) (CommRingOps.mul θ (g z)))),
                z ∈ D.filter (fun z => decide (RoundPoly.evalCoeffs pG.val z = g z)) := by
              intro z hz
              rcases List.mem_filter.mp hz with ⟨hzD, hB⟩
              refine List.mem_filter.mpr ⟨hzD, decide_eq_true ?_⟩
              change RoundPoly.evalCoeffs (trimPoly G_poly) z = g z
              rw [evalCoeffs_trimPoly]
              exact of_decide_eq_true ((Bool.and_eq_true _ _).mp hB).1
            exact Nat.le_trans hJoint (nodup_length_le_of_subset (List.Pairwise.filter _ hD) hSub)
          have hpFHi : pF ∈ candFHi :=
            (mem_gsDecodeList_iff f hD (by omega) pF).mpr
              ⟨Nat.le_trans (trimPoly_length_le F_poly) hFLen, hJointF⟩
          have hpGHi : pG ∈ candGHi :=
            (mem_gsDecodeList_iff g hD (by omega) pG).mpr
              ⟨Nat.le_trans (trimPoly_length_le G_poly) hGLen, hJointG⟩
          have hTopSum : CommRingOps.add (coeffAt pF.val (d + 1))
              (CommRingOps.mul θ (coeffAt pG.val (d + 1))) = CommRingOps.zero := by
            change CommRingOps.add (coeffAt (trimPoly F_poly) (d + 1))
              (CommRingOps.mul θ (coeffAt (trimPoly G_poly) (d + 1))) = CommRingOps.zero
            rw [coeffAt_trimPoly, coeffAt_trimPoly]
            dsimp only [F_poly]
            rw [coeffAt_polyAddVar, coeffAt_polyScaleVar, coeffAt_eq_zero_of_ge H_poly (d + 1) hHLen]
            constructive_ring
          if hBothZero : coeffAt pF.val (d + 1) = CommRingOps.zero ∧
              coeffAt pG.val (d + 1) = CommRingOps.zero then
            have hpFLoLen : pF.val.length ≤ d + 1 :=
              isTrimmed_length_le_of_coeffAt_zero pF.val d pF.property
                (Nat.le_trans (trimPoly_length_le F_poly) hFLen) hBothZero.1
            have hpGLoLen : pG.val.length ≤ d + 1 :=
              isTrimmed_length_le_of_coeffAt_zero pG.val d pG.property
                (Nat.le_trans (trimPoly_length_le G_poly) hGLen) hBothZero.2
            have hpFLo : pF ∈ candFLo :=
              (mem_gsDecodeList_iff f hD (by omega) pF).mpr ⟨hpFLoLen, hJointF⟩
            have hpGLo : pG ∈ candGLo :=
              (mem_gsDecodeList_iff g hD (by omega) pG).mpr ⟨hpGLoLen, hJointG⟩
            have hMemLo : (pF, pG) ∈ pairsLo :=
              List.mem_flatMap.mpr ⟨pF, hpFLo, List.mem_map.mpr ⟨pG, hpGLo, rfl⟩⟩
            have hMatchLoTrue : matchLo (pF, pG) u.1 = true := by
              dsimp only [matchLo]
              apply decide_eq_true
              rw [huθ] at hPCl ⊢
              have hDot := congrArg (fun q => ringDot q kernel) hTrimEq
              rw [ringDot_trimPoly_eq, ringDot_trimPoly_eq,
                  ringDot_polyAddVar, ringDot_polyAddVar,
                  ringDot_polyScaleVar, ringDot_polyScaleVar] at hDot
              have hDotF : CommRingOps.add (ringDot pF.val kernel)
                  (CommRingOps.mul θ (ringDot pG.val kernel)) = ringDot H_poly kernel := by
                change CommRingOps.add (ringDot (trimPoly F_poly) kernel)
                  (CommRingOps.mul θ (ringDot (trimPoly G_poly) kernel)) = _
                rw [ringDot_trimPoly_eq, ringDot_trimPoly_eq]
                dsimp only [F_poly]
                rw [ringDot_polyAddVar, ringDot_polyScaleVar]
                constructive_ring
              have hShiftF : CommRingOps.add (ringDot (shiftPoly pF.val) kernel)
                  (CommRingOps.mul θ (ringDot (shiftPoly pG.val) kernel)) =
                  ringDot (shiftPoly H_poly) kernel := by
                change CommRingOps.add (ringDot (shiftPoly (trimPoly F_poly)) kernel)
                  (CommRingOps.mul θ (ringDot (shiftPoly (trimPoly G_poly)) kernel)) = _
                rw [ringDot_shiftPoly_trimPoly_eq, ringDot_shiftPoly_trimPoly_eq]
                dsimp only [F_poly]
                have hScaleShift : shiftPoly (polyScaleVar (CommRingOps.neg θ) G_poly) =
                    polyScaleVar (CommRingOps.neg θ) (shiftPoly G_poly) := by
                  simp only [shiftPoly, polyScaleVar, List.map_cons, LawfulCommRing.mul_zero]
                rw [ringDot_shiftPoly_polyAddVar, hScaleShift, ringDot_polyScaleVar]
                constructive_ring
              have hGTrim : ringDot pG.val kernel = ringDot G_poly kernel :=
                ringDot_trimPoly_eq G_poly kernel
              rw [hDotF, hShiftF, hGTrim]
              exact hDot.symm.trans hPCl
            have hAnyLo : anyLo u.1 = true := List.any_eq_true.mpr ⟨(pF, pG), hMemLo, hMatchLoTrue⟩
            have hAllTrue : anyAll u.1 = true := by simp [anyAll, hAnyLo]
            rw [hAllTrue] at hNotAll
            exact absurd hNotAll (by decide)
          else
            have hOrNz : coeffAt pF.val (d + 1) ≠ CommRingOps.zero ∨
                coeffAt pG.val (d + 1) ≠ CommRingOps.zero := by
              if h1 : coeffAt pF.val (d + 1) = CommRingOps.zero then
                right
                exact fun h2 => hBothZero ⟨h1, h2⟩
              else
                exact .inl h1
            have hMemHi : (pF, pG) ∈ pairsHi :=
              List.mem_flatMap.mpr ⟨pF, hpFHi, List.mem_map.mpr ⟨pG, hpGHi, rfl⟩⟩
            have hMatchOvTrue : matchOv (pF, pG) u.1 = true := by
              dsimp only [matchOv]
              rw [huθ]
              exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true hOrNz, decide_eq_true hTopSum⟩
            have hAnyOv : anyOv u.1 = true := List.any_eq_true.mpr ⟨(pF, pG), hMemHi, hMatchOvTrue⟩
            have hAllTrue : anyAll u.1 = true := by simp [anyAll, hAnyOv]
            rw [hAllTrue] at hNotAll
            exact absurd hNotAll (by decide)
      have hIdxLenEq : idxList.length = fib.length := by
        dsimp only [idxList]
        rw [List.length_map, List.length_attach]
      rwa [hIdxLenEq] at hDecompFib
  rw [hPairsLoLen] at hLoBound
  rw [hPairsHiLen] at hOvBound
  dsimp only [candFLo, candGLo, candFHi, candGHi, T_non] at hLoBound hOvBound hNonBound
  omega

/-- Closed-form bad-triple count for the 3-challenge `(θ, α, β)` equal-degree fold at `(n, d, A, B, m, Dy)`
    with `q_θ = S_θ.length` and `q = S.length`. -/
def slicedThreeChallengeCount (n d A B m Dy q_θ q : Nat) : Nat :=
  let badMca := Dy + slicedRest n (d + 1) (A + 1) B (m * (A + 1) - Dy) Dy q
  let jbLo := JohnsonBound.johnsonBound n A d
  let jbHi := JohnsonBound.johnsonBound n A (d + 1)
  q_θ * badMca + (jbLo * jbLo) * (q_θ * q) + (jbHi * jbHi) * (q * q)

/-- **Closed-Form `QuarticGoldilocks` Three-Challenge Equal-Degree Claim-Fold Bound**:
    Combines `equal_degree_three_challenge_fold_bound`, `slicedParamsOk_sound`, and
    `gsDecodeList_length_le_johnson` into an input-word-independent count over `S_θ × S × S`. -/
theorem sliced_equal_degree_three_challenge_bound
    (D S_θ S kernel : List QuarticGoldilocks) (d A B m Dy : Nat)
    (f g : QuarticGoldilocks → QuarticGoldilocks) (e_f e_g c_f c_g : QuarticGoldilocks)
    (hD : D.Nodup) (hSθ : S_θ.Nodup) (hS : S.Nodup) (hdA : d + 2 ≤ A)
    (hParams : slicedParamsOk D.length (d + 1) (A + 1) B m Dy = true)
    (hInvalidFG :
      (∀ Fw : List QuarticGoldilocks, Fw.length ≤ d + 1 →
        A ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs Fw z = f z))).length →
        ringDot Fw kernel ≠ e_f) ∨
      (∀ Gw : List QuarticGoldilocks, Gw.length ≤ d + 1 →
        A ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs Gw z = g z))).length →
        ringDot Gw kernel ≠ e_g))
    (L : List (Fin (threePool S_θ S).length)) (hNd : L.Nodup)
    (hFlip : ∀ ch ∈ L, ¬¬ ∃ P : List QuarticGoldilocks,
      P.length ≤ d + 2 ∧
      A + 1 ≤ (D.filter (fun z =>
        let t := (threePool S_θ S).get ch
        let h_θ := CommRingOps.add (f z) (CommRingOps.mul t.1 (g z))
        decide (RoundPoly.evalCoeffs P z =
          CommRingOps.add (g z)
            (CommRingOps.mul (CommRingOps.add t.2.1 (CommRingOps.mul t.2.2 z)) h_θ)))).length ∧
      ringDot P kernel =
        let t := (threePool S_θ S).get ch
        hemFoldClaimUpdate e_f e_g c_f c_g t.1 t.2.1 t.2.2) :
    L.length ≤ slicedThreeChallengeCount D.length d A B m Dy S_θ.length S.length := by
  have hBase := equal_degree_three_challenge_fold_bound D S_θ S kernel d A
    (Dy + slicedRest D.length (d + 1) (A + 1) B (m * (A + 1) - Dy) Dy S.length)
    f g e_f e_g c_f c_g hD hSθ hS hdA
    (slicedParamsOk_sound D.length (d + 1) (A + 1) B m Dy hParams D S hD hS rfl)
    hInvalidFG L hNd hFlip
  obtain ⟨_, _, _, hBltA1, hDenB, _, _, _⟩ := of_decide_eq_true hParams
  have hBLeA : B ≤ A := by omega
  have hBBLeAA : B * B ≤ A * A := Nat.mul_le_mul hBLeA hBLeA
  have hDenHi : D.length * (d + 1) < A * A :=
    Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.mul_le_mul_left D.length (by omega)) hDenB) hBBLeAA
  have hDenLo : D.length * d < A * A :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left D.length (by omega)) hDenHi
  have hF_lo := gsDecodeList_length_le_johnson D f d A hD (by omega) hDenLo
  have hG_lo := gsDecodeList_length_le_johnson D g d A hD (by omega) hDenLo
  have hF_hi := gsDecodeList_length_le_johnson D f (d + 1) A hD hdA hDenHi
  have hG_hi := gsDecodeList_length_le_johnson D g (d + 1) A hD hdA hDenHi
  unfold slicedThreeChallengeCount
  dsimp only
  have hMulLo : (gsDecodeList d A D f).length * (gsDecodeList d A D g).length * (S_θ.length * S.length) ≤
      (JohnsonBound.johnsonBound D.length A d * JohnsonBound.johnsonBound D.length A d) *
        (S_θ.length * S.length) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul hF_lo hG_lo)
  have hMulHi : (gsDecodeList (d + 1) A D f).length * (gsDecodeList (d + 1) A D g).length *
      (S.length * S.length) ≤
      (JohnsonBound.johnsonBound D.length A (d + 1) * JohnsonBound.johnsonBound D.length A (d + 1)) *
        (S.length * S.length) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul hF_hi hG_hi)
  omega

/-- Full 3-challenge `(θ, α, β)` rational error bound at stage geometry `g` over `QuarticGoldilocks³`
    (denominator `q³ = (p⁴)³`, setting `d = g.d - 1` and `A = r.2.2.1 - 1`). -/
