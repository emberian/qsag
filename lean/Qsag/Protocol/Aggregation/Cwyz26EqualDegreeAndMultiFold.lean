module
/-
# Qsag.CodingTheory.Cwyz26EqualDegreeAndMultiFold — Three-Challenge Equal-Degree Lift, Intra-Stage Multi-Fold Composition, and Multi-Sheet Space-Curve GCD

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
public import Qsag.Coding.Resultant
import all Qsag.Protocol.Aggregation.HemSlicedFoldBudget
import all Qsag.Coding.Cwyz26
import all Qsag.Protocol.Aggregation.Cwyz26JohnsonCertificate
import all Qsag.Math.Algebra
import all Qsag.Coding.Resultant
import all Qsag.Coding.GuruswamiSudan
import all Qsag.Protocol.Aggregation.HemWhirRbrSoundness
import all Qsag.Protocol.Aggregation.HemVerifierAcceptance
import all Qsag.Protocol.Aggregation.MultiRoundFsQrom
import all Qsag.Protocol.Aggregation.ConcreteSecurityBudget
import all Qsag.Math.Goldilocks

public section
namespace Qsag
set_option autoImplicit false
set_option exponentiation.threshold 2048

/-! ## §1. Unconditional Johnson List Bound & Three-Challenge Equal-Degree Lift -/

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
def slicedThreeChallengeStageBound (g : HemStageGeom) (r : Nat × Nat × Nat × Nat × Nat)
    (w : Nat × Nat × Nat × Nat) : RatBound :=
  let q := goldilocksExt4Card
  ⟨slicedThreeChallengeCount g.n (g.d - 1) (r.2.2.1 - 1) w.2.2.1 r.2.2.2.1 r.2.2.2.2 q q,
   q * (q * q),
   Nat.mul_pos goldilocksExt4Card_pos (Nat.mul_pos goldilocksExt4Card_pos goldilocksExt4Card_pos)⟩

def slicedStageThreeChallengeCovered (nv : Nat) (g : HemStageGeom) : Bool :=
  if hemJohnsonQromStageExhaustive g = true then
    (slicedStageRow nv g.stageIdx).isNone
  else
    match hemJohnsonQromTableRow nv g.stageIdx, slicedStageRow nv g.stageIdx with
    | some r, some w =>
      decide (2 ≤ g.d) &&
      decide (g.d + 1 ≤ r.2.2.1 - 1) &&
      slicedParamsOk g.n g.d r.2.2.1 w.2.2.1 r.2.2.2.1 r.2.2.2.2 &&
      decide (atLeastBits 184 (slicedThreeChallengeStageBound g r w))
    | _, _ => false

/-- **Every non-exhaustive canonical `BciksJohnsonQrom128` stage (`nv = 2..24`) satisfies the
    unconditional 3-challenge `(θ, α, β)` equal-degree claim-fold bound at `≥ 184` bits**
    (preserving `≥ 128` bits under `dfmRoundScale Q` for all `Q + 1 ≤ 2 ^ 27`). -/
theorem sliced_stage_three_challenge_supported_budget
    (nv : Nat) (h2 : 2 ≤ nv) (h24 : nv ≤ 24)
    (g : HemStageGeom) (hg : g ∈ hemStageGeoms nv)
    (hne : hemJohnsonQromStageExhaustive g = false) :
    ∃ (r : Nat × Nat × Nat × Nat × Nat) (w : Nat × Nat × Nat × Nat),
      hemJohnsonQromTableRow nv g.stageIdx = some r ∧
      slicedStageRow nv g.stageIdx = some w ∧
      2 ≤ g.d ∧ g.d + 1 ≤ r.2.2.1 - 1 ∧
      slicedParamsOk g.n g.d r.2.2.1 w.2.2.1 r.2.2.2.1 r.2.2.2.2 = true ∧
      atLeastBits 184 (slicedThreeChallengeStageBound g r w) ∧
      (∀ Q : Nat, Q + 1 ≤ 2 ^ 27 →
        atLeastBits 128 (dfmRoundScale Q (slicedThreeChallengeStageBound g r w))) := by
  have hAll : ((List.range 23).all fun i =>
      (hemStageGeoms (i + 2)).all (slicedStageThreeChallengeCovered (i + 2))) = true := by
    decide +kernel
  have h1 := List.all_eq_true.mp hAll (nv - 2) (List.mem_range.mpr (by omega))
  have hEq : nv - 2 + 2 = nv := by omega
  rw [hEq] at h1
  have hc := List.all_eq_true.mp h1 g hg
  unfold slicedStageThreeChallengeCovered at hc
  rw [hne] at hc
  simp only [Bool.false_eq_true, ↓reduceIte] at hc
  split at hc
  · next r w hr hw =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    rcases hc with ⟨⟨⟨hd2, hdA⟩, hOk⟩, hBits⟩
    exact ⟨r, w, hr, hw, hd2, hdA, hOk, hBits,
      fun Q hQ => dfm184_budget_at_2pow27 _ hBits Q hQ⟩
  · exact absurd hc Bool.false_ne_true

/-! ## §2. Intra-Stage `k`-Fold Schedule Composition (`foldSteps = 1..6`) -/

/-- Split an even-length list into even- and odd-indexed halves. -/
def splitEvenOdd {F : Type} : List F → List F × List F
  | [] => ([], [])
  | [_] => ([], [])
  | a :: b :: rest =>
    let p := splitEvenOdd rest
    (a :: p.1, b :: p.2)
termination_by structural xs => xs

theorem splitEvenOdd_spec {F : Type} [CommRingOps F] :
    ∀ (m : Nat) (K : List F) (φ : F),
      K.length = 2 * m →
      (splitEvenOdd K).1.length = m ∧
      (splitEvenOdd K).2.length = m ∧
      hemInterleave (splitEvenOdd K).1 (splitEvenOdd K).2 = K ∧
      hemKernelFold φ K =
        List.zipWith (fun a b => CommRingOps.add a (CommRingOps.mul φ b))
          (splitEvenOdd K).1 (splitEvenOdd K).2 ++ [CommRingOps.zero] ∧
      (hemKernelFold φ K).length = m + 1
  | 0, [], _, _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
  | 0, _ :: _, _, h => absurd h (Nat.succ_ne_zero _)
  | _ + 1, [], _, h => absurd h.symm (Nat.succ_ne_zero _)
  | m + 1, [_], _, h =>
    absurd (Nat.succ.inj (h.trans (Nat.mul_succ 2 m))).symm (Nat.succ_ne_zero _)
  | m + 1, a :: b :: rest, φ, h => by
    have hRest : rest.length = 2 * m :=
      Nat.succ.inj (Nat.succ.inj (h.trans (Nat.mul_succ 2 m)))
    obtain ⟨h1, h2, hInt, hFold, hFLen⟩ := splitEvenOdd_spec m rest φ hRest
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change (splitEvenOdd rest).1.length + 1 = m + 1; rw [h1]
    · change (splitEvenOdd rest).2.length + 1 = m + 1; rw [h2]
    · change a :: b :: hemInterleave (splitEvenOdd rest).1 (splitEvenOdd rest).2 = a :: b :: rest
      rw [hInt]
    · exact congrArg (List.cons (CommRingOps.add a (CommRingOps.mul φ b))) hFold
    · exact congrArg Nat.succ hFLen
termination_by structural m => m

/-- Appending the trailing zero overflow slot of `hemKernelFold` leaves `ringDot` invariant. -/
theorem ringDot_append_zero {F : Type} [LawfulCommRing F] :
    ∀ (P xs : List F), ringDot P (xs ++ [CommRingOps.zero]) = ringDot P xs
  | [], _ => rfl
  | c :: cs, [] => by
    simp only [List.nil_append, ringDot, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | c :: cs, y :: ys => by
    simp only [List.cons_append, ringDot, ringDot_append_zero cs ys]

/-- Even/odd polynomial interleaving `Q(X) = F(X²) + X · G(X²)` preserving variable-length tails. -/
def interleavePoly {F : Type} [CommRingOps F] : List F → List F → List F
  | [], [] => []
  | a :: as, [] => a :: CommRingOps.zero :: interleavePoly as []
  | [], b :: bs => CommRingOps.zero :: b :: interleavePoly [] bs
  | a :: as, b :: bs => a :: b :: interleavePoly as bs

theorem interleavePoly_length_le {F : Type} [CommRingOps F] :
    ∀ (m : Nat) (F_poly G_poly : List F),
      F_poly.length ≤ m → G_poly.length ≤ m →
      (interleavePoly F_poly G_poly).length ≤ 2 * m
  | 0, F_poly, G_poly, hF, hG => by
    have eF : F_poly = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hF)
    have eG : G_poly = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hG)
    subst eF; subst eG
    simp only [interleavePoly, List.length_nil, Nat.zero_le]
  | m + 1, [], [], _, _ => by
    simp only [interleavePoly, List.length_nil, Nat.zero_le]
  | m + 1, a :: as, [], hF, _ => by
    simp only [interleavePoly, List.length_cons]
    have ih := interleavePoly_length_le m as [] (Nat.le_of_succ_le_succ hF) (Nat.zero_le m)
    omega
  | m + 1, [], b :: bs, _, hG => by
    simp only [interleavePoly, List.length_cons]
    have ih := interleavePoly_length_le m [] bs (Nat.zero_le m) (Nat.le_of_succ_le_succ hG)
    omega
  | m + 1, a :: as, b :: bs, hF, hG => by
    simp only [interleavePoly, List.length_cons]
    have ih := interleavePoly_length_le m as bs
      (Nat.le_of_succ_le_succ hF) (Nat.le_of_succ_le_succ hG)
    omega

private theorem evalCoeffs_interleavePoly_nil_right {F : Type} [LawfulCommRing F] :
    ∀ (as : List F) (x : F),
      RoundPoly.evalCoeffs (interleavePoly as []) x =
        RoundPoly.evalCoeffs as (CommRingOps.mul x x)
  | [], _ => by simp only [interleavePoly]; rfl
  | a :: as, x => by
    simp only [interleavePoly, RoundPoly.evalCoeffs_cons, evalCoeffs_interleavePoly_nil_right as x]
    constructive_ring

private theorem evalCoeffs_interleavePoly_nil_left {F : Type} [LawfulCommRing F] :
    ∀ (bs : List F) (x : F),
      RoundPoly.evalCoeffs (interleavePoly [] bs) x =
        CommRingOps.mul x (RoundPoly.evalCoeffs bs (CommRingOps.mul x x))
  | [], x => by
    simp only [interleavePoly]
    change CommRingOps.zero = CommRingOps.mul x CommRingOps.zero
    rw [LawfulCommRing.mul_zero]
  | b :: bs, x => by
    simp only [interleavePoly, RoundPoly.evalCoeffs_cons, evalCoeffs_interleavePoly_nil_left bs x]
    constructive_ring

theorem evalCoeffs_interleavePoly {F : Type} [LawfulCommRing F] :
    ∀ (F_poly G_poly : List F) (x : F),
      RoundPoly.evalCoeffs (interleavePoly F_poly G_poly) x =
        CommRingOps.add
          (RoundPoly.evalCoeffs F_poly (CommRingOps.mul x x))
          (CommRingOps.mul x (RoundPoly.evalCoeffs G_poly (CommRingOps.mul x x)))
  | [], G_poly, x => by
    rw [evalCoeffs_interleavePoly_nil_left]
    change _ = CommRingOps.add CommRingOps.zero _
    rw [LawfulCommRing.zero_add]
  | a :: as, [], x => by
    rw [evalCoeffs_interleavePoly_nil_right]
    change _ = CommRingOps.add _ (CommRingOps.mul x CommRingOps.zero)
    rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | a :: as, b :: bs, x => by
    simp only [interleavePoly, RoundPoly.evalCoeffs_cons, evalCoeffs_interleavePoly as bs x]
    constructive_ring
termination_by structural F_poly => F_poly

theorem ringDot_interleavePoly_hemInterleave {F : Type} [LawfulCommRing F] :
    ∀ (kE kO F_poly G_poly : List F),
      kE.length = kO.length →
      ringDot (interleavePoly F_poly G_poly) (hemInterleave kE kO) =
        CommRingOps.add (ringDot F_poly kE) (ringDot G_poly kO)
  | [], [], F_poly, G_poly, _ => by
    have h1 : ringDot (interleavePoly F_poly G_poly) ([] : List F) = CommRingOps.zero := by
      cases interleavePoly F_poly G_poly <;> rfl
    have h2 : ringDot F_poly ([] : List F) = CommRingOps.zero := by cases F_poly <;> rfl
    have h3 : ringDot G_poly ([] : List F) = CommRingOps.zero := by cases G_poly <;> rfl
    simp only [hemInterleave, h1, h2, h3, LawfulCommRing.add_zero]
  | _ :: _, [], _, _, h => absurd h (Nat.succ_ne_zero _)
  | [], _ :: _, _, _, h => absurd h.symm (Nat.succ_ne_zero _)
  | e :: es, o :: os, F_poly, G_poly, h => by
    have hSub : es.length = os.length := Nat.succ.inj h
    cases F_poly with
    | nil =>
      cases G_poly with
      | nil =>
        simp only [interleavePoly, hemInterleave, ringDot, LawfulCommRing.add_zero]
      | cons b bs =>
        simp only [interleavePoly, hemInterleave, ringDot,
          ringDot_interleavePoly_hemInterleave es os [] bs hSub]
        constructive_ring
    | cons a as =>
      cases G_poly with
      | nil =>
        simp only [interleavePoly, hemInterleave, ringDot,
          ringDot_interleavePoly_hemInterleave es os as [] hSub]
        constructive_ring
      | cons b bs =>
        simp only [interleavePoly, hemInterleave, ringDot,
          ringDot_interleavePoly_hemInterleave es os as bs hSub]
        constructive_ring
termination_by structural kE => kE

/-- Antipodal coset pairing between pre-fold domain `D_in` (length `2 n`, pairs `(x, -x)`) and
    squared post-fold domain `D_out` (length `n`, points `y = x²`) in characteristic `≠ 2`. -/
structure IsAntipodalDomainPair {F : Type} [LawfulField F] (D_in D_out : List F) : Prop where
  nodup_in : D_in.Nodup
  nodup_out : D_out.Nodup
  len_eq : D_in.length = 2 * D_out.length
  two_ne_zero : (CommRingOps.add CommRingOps.one CommRingOps.one : F) ≠ CommRingOps.zero
  even_nz : ∀ idx : Nat, idx < D_out.length →
    D_in.getD (2 * idx) CommRingOps.one ≠ CommRingOps.zero
  odd_neg : ∀ idx : Nat, idx < D_out.length →
    D_in.getD (2 * idx + 1) CommRingOps.zero =
      CommRingOps.neg (D_in.getD (2 * idx) CommRingOps.one)
  sq_eq : ∀ idx : Nat, idx < D_out.length →
    D_out.getD idx CommRingOps.zero =
      CommRingOps.mul (D_in.getD (2 * idx) CommRingOps.one) (D_in.getD (2 * idx) CommRingOps.one)

/-- Even coset projection `f_E(idx) = (O(2 idx) + O(2 idx + 1)) / 2`. -/
def cosetEvenOracle {F : Type} [LawfulField F] (curOracle : Nat → F) (idx : Nat) : F :=
  let two := CommRingOps.add CommRingOps.one CommRingOps.one
  CommRingOps.mul (LawfulField.inv two)
    (CommRingOps.add (curOracle (2 * idx)) (curOracle (2 * idx + 1)))

/-- Odd coset projection `f_O(idx) = (O(2 idx) - O(2 idx + 1)) / (2 x_idx)`. -/
def cosetOddOracle {F : Type} [LawfulField F] (curDom : List F) (curOracle : Nat → F)
    (idx : Nat) : F :=
  let two := CommRingOps.add CommRingOps.one CommRingOps.one
  let x := curDom.getD (2 * idx) CommRingOps.one
  CommRingOps.mul (LawfulField.inv (CommRingOps.mul two x))
    (CommRingOps.sub (curOracle (2 * idx)) (curOracle (2 * idx + 1)))

private theorem qsum_even_pairs :
    ∀ (n m : Nat) (hm : m = 2 * n) (g : Fin m → Nat),
      qsum m g =
        qsum n (fun idx =>
          g ⟨2 * idx.1, by omega⟩ + g ⟨2 * idx.1 + 1, by omega⟩)
  | 0, m, hm, _ => by subst hm; rfl
  | _ + 1, 0, hm, _ => by omega
  | _ + 1, 1, hm, _ => by omega
  | n + 1, m' + 2, hm, g => by
    have hm' : m' = 2 * n := by omega
    change g ⟨0, Nat.zero_lt_succ _⟩ +
        (g ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _)⟩ +
          qsum m' (fun j => g ⟨j.1 + 2, Nat.add_lt_add_right j.2 2⟩)) =
      (g ⟨0, by omega⟩ + g ⟨1, by omega⟩) +
        qsum n (fun idx => g ⟨2 * (idx.1 + 1), by omega⟩ + g ⟨2 * (idx.1 + 1) + 1, by omega⟩)
    rw [qsum_even_pairs n m' hm' (fun j => g ⟨j.1 + 2, Nat.add_lt_add_right j.2 2⟩)]
    have hCongr :
        qsum n (fun idx =>
          g ⟨2 * idx.1 + 2, Nat.add_lt_add_right (by omega) 2⟩ +
          g ⟨(2 * idx.1 + 1) + 2, Nat.add_lt_add_right (by omega) 2⟩) =
        qsum n (fun idx =>
          g ⟨2 * (idx.1 + 1), by omega⟩ + g ⟨2 * (idx.1 + 1) + 1, by omega⟩) := by
      apply qsum_congr; intro idx
      have e1 : (⟨2 * idx.1 + 2, Nat.add_lt_add_right (by omega) 2⟩ : Fin (m' + 2)) =
          ⟨2 * (idx.1 + 1), by omega⟩ := Fin.ext (by dsimp only; omega)
      have e2 : (⟨(2 * idx.1 + 1) + 2, Nat.add_lt_add_right (by omega) 2⟩ : Fin (m' + 2)) =
          ⟨2 * (idx.1 + 1) + 1, by omega⟩ := Fin.ext (by dsimp only; omega)
      rw [e1, e2]
    rw [hCongr, Nat.add_assoc]

private theorem qsum_two_mul_left :
    ∀ (n : Nat) (f : Fin n → Nat), 2 * qsum n f = qsum n (fun i => 2 * f i)
  | 0, _ => rfl
  | n + 1, f => by
    simp only [qsum, Nat.mul_add, qsum_two_mul_left n]

private theorem ite_true_eq {P : Prop} [inst : Decidable P] {α : Sort _} (t e : α) (h : P) :
    (if P then t else e) = t := by
  cases inst with
  | isFalse hn => exact absurd h hn
  | isTrue _ => rfl

private theorem ite_false_eq {P : Prop} [inst : Decidable P] {α : Sort _} (t e : α) (h : ¬ P) :
    (if P then t else e) = e := by
  cases inst with
  | isFalse _ => rfl
  | isTrue hp => exact absurd hp h

private theorem ite_decide_eq {P : Prop} [inst : Decidable P] :
    (if decide P = true then 1 else 0) = (if P then 1 else 0) := by
  cases inst <;> rfl

private theorem dite_true_eq {P : Prop} [inst : Decidable P] {α : Sort _} {t : P → α} {e : ¬ P → α}
    (h : P) : dite P t e = t h := by
  cases inst with
  | isFalse hn => exact absurd h hn
  | isTrue _ => rfl

private theorem dite_false_eq {P : Prop} [inst : Decidable P] {α : Sort _} {t : P → α} {e : ¬ P → α}
    (h : ¬ P) : dite P t e = e h := by
  cases inst with
  | isFalse _ => rfl
  | isTrue hp => exact absurd hp h

private theorem lookupDomOracle_get_c {F : Type} [CommRingOps F] [DecidableEq F] :
    ∀ (domPts : List F) (O : Nat → F), domPts.Nodup →
      ∀ (idx : Fin domPts.length), lookupDomOracle domPts O (domPts.get idx) = O idx.1
  | [], _, _, idx => Fin.elim0 idx
  | d :: ds, O, _, ⟨0, _⟩ => by
    change (if d = d then O 0 else lookupDomOracle ds (fun i => O (i + 1)) d) = O 0
    exact ite_true_eq _ _ rfl
  | d :: ds, O, hNd, ⟨k + 1, hk⟩ => by
    rcases List.pairwise_cons.mp hNd with ⟨hNotMem, hTailNd⟩
    have hk' : k < ds.length := Nat.lt_of_succ_lt_succ hk
    have hMem : ds.get ⟨k, hk'⟩ ∈ ds := list_get_mem ds ⟨k, hk'⟩
    have hNe : ds.get ⟨k, hk'⟩ ≠ d := fun hEq => hNotMem _ hMem hEq.symm
    change (if ds.get ⟨k, hk'⟩ = d then O 0 else
      lookupDomOracle ds (fun i => O (i + 1)) (ds.get ⟨k, hk'⟩)) = O (k + 1)
    rw [ite_false_eq _ _ hNe]
    exact lookupDomOracle_get_c ds (fun i => O (i + 1)) hTailNd ⟨k, hk'⟩

private theorem hemCosetAgreeCount_eq_filter_lookup_c {F : Type} [CommRingOps F] [DecidableEq F]
    (domPts : List F) (O : Nat → F) (P : List F) (hNd : domPts.Nodup) :
    hemCosetAgreeCount domPts O P =
      (domPts.filter (fun z =>
        decide (RoundPoly.evalCoeffs P z = lookupDomOracle domPts O z))).length := by
  unfold hemCosetAgreeCount
  rw [← qsum_get_filter_eq]
  apply qsum_congr; intro idx
  rw [lookupDomOracle_get_c domPts O hNd idx]
  if h : O idx.1 = RoundPoly.evalCoeffs P (domPts.get idx) then
    rw [ite_true_eq _ _ h, decide_eq_true h.symm, ite_true_eq _ _ rfl]
  else
    have h' : RoundPoly.evalCoeffs P (domPts.get idx) ≠ O idx.1 := fun e => h e.symm
    rw [ite_false_eq _ _ h, decide_eq_false h', ite_false_eq _ _ Bool.false_ne_true]

/-- **Antipodal Joint-Agreement Lifting Lemma**:
    Every point `y ∈ D_out` at which `(F_poly, G_poly)` jointly matches `(cosetEvenOracle, cosetOddOracle)`
    yields two distinct antipodal agreements `(x, -x)` of `interleavePoly F_poly G_poly` with `curOracle`
    on `D_in`, so `A` joint agreements on `D_out` lift to `2 * A` coset agreements on `D_in`. -/
theorem antipodal_joint_agree_lifts {F : Type} [LawfulField F] [DecidableEq F]
    {D_in D_out : List F} (hPair : IsAntipodalDomainPair D_in D_out)
    (curOracle : Nat → F) (F_poly G_poly : List F) :
    2 * (D_out.filter (fun y =>
      decide (RoundPoly.evalCoeffs F_poly y = lookupDomOracle D_out (cosetEvenOracle curOracle) y) &&
      decide (RoundPoly.evalCoeffs G_poly y = lookupDomOracle D_out (cosetOddOracle D_in curOracle) y))).length ≤
    hemCosetAgreeCount D_in curOracle (interleavePoly F_poly G_poly) := by
  let jointPred : F → Bool := fun y =>
    decide (RoundPoly.evalCoeffs F_poly y = lookupDomOracle D_out (cosetEvenOracle curOracle) y) &&
    decide (RoundPoly.evalCoeffs G_poly y = lookupDomOracle D_out (cosetOddOracle D_in curOracle) y)
  rw [← qsum_get_filter_eq jointPred D_out, qsum_two_mul_left]
  unfold hemCosetAgreeCount
  rw [qsum_even_pairs D_out.length D_in.length hPair.len_eq]
  apply qsum_le_qsum; intro idx
  cases hj : jointPred (D_out.get idx)
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.mul_zero, Nat.zero_le]
  · simp only [↓reduceIte, Nat.mul_one]
    dsimp only [jointPred] at hj
    rcases (Bool.and_eq_true _ _).mp hj with ⟨hFEdec, hFOdec⟩
    have hFE := of_decide_eq_true hFEdec
    have hFO := of_decide_eq_true hFOdec
    rw [lookupDomOracle_get_c D_out _ hPair.nodup_out idx] at hFE hFO
    let two : F := CommRingOps.add CommRingOps.one CommRingOps.one
    have hTwoInv : CommRingOps.mul two (LawfulField.inv two) = CommRingOps.one :=
      LawfulField.mul_inv_cancel hPair.two_ne_zero
    let idxE : Fin D_in.length := ⟨2 * idx.1, by have := hPair.len_eq; omega⟩
    let idxO : Fin D_in.length := ⟨2 * idx.1 + 1, by have := hPair.len_eq; omega⟩
    let x := D_in.get idxE
    have hxGetD : D_in.getD (2 * idx.1) CommRingOps.one = x :=
      list_getD_eq_get D_in CommRingOps.one idxE
    have hxONeg : D_in.get idxO = CommRingOps.neg x := by
      have h1 := list_getD_eq_get D_in CommRingOps.zero idxO
      rw [← h1, hPair.odd_neg idx.1 idx.2, hxGetD]
    have hySq : D_out.get idx = CommRingOps.mul x x := by
      have h1 := list_getD_eq_get D_out CommRingOps.zero idx
      rw [← h1, hPair.sq_eq idx.1 idx.2, hxGetD]
    have hxNz : x ≠ CommRingOps.zero := by
      rw [← hxGetD]; exact hPair.even_nz idx.1 idx.2
    have hTwoXNz : CommRingOps.mul two x ≠ CommRingOps.zero := by
      intro h0
      rcases LawfulField.mul_eq_zero h0 with h20 | hx0
      · exact hPair.two_ne_zero h20
      · exact hxNz hx0
    have hTwoXInv : CommRingOps.mul (CommRingOps.mul two x)
        (LawfulField.inv (CommRingOps.mul two x)) = CommRingOps.one :=
      LawfulField.mul_inv_cancel hTwoXNz
    unfold cosetEvenOracle at hFE
    unfold cosetOddOracle at hFO
    dsimp only at hFE hFO
    rw [hxGetD] at hFO
    have hSumAB : CommRingOps.mul two (RoundPoly.evalCoeffs F_poly (D_out.get idx)) =
        CommRingOps.add (curOracle (2 * idx.1)) (curOracle (2 * idx.1 + 1)) := by
      rw [hFE]
      have hAssoc : CommRingOps.mul two
          (CommRingOps.mul (LawfulField.inv two)
            (CommRingOps.add (curOracle (2 * idx.1)) (curOracle (2 * idx.1 + 1)))) =
        CommRingOps.mul (CommRingOps.mul two (LawfulField.inv two))
          (CommRingOps.add (curOracle (2 * idx.1)) (curOracle (2 * idx.1 + 1))) := by
        constructive_ring
      rw [hAssoc, hTwoInv, LawfulCommRing.one_mul]
    have hDiffAB : CommRingOps.mul (CommRingOps.mul two x)
        (RoundPoly.evalCoeffs G_poly (D_out.get idx)) =
        CommRingOps.sub (curOracle (2 * idx.1)) (curOracle (2 * idx.1 + 1)) := by
      rw [hFO]
      have hAssoc : CommRingOps.mul (CommRingOps.mul two x)
          (CommRingOps.mul (LawfulField.inv (CommRingOps.mul two x))
            (CommRingOps.sub (curOracle (2 * idx.1)) (curOracle (2 * idx.1 + 1)))) =
        CommRingOps.mul (CommRingOps.mul (CommRingOps.mul two x)
            (LawfulField.inv (CommRingOps.mul two x)))
          (CommRingOps.sub (curOracle (2 * idx.1)) (curOracle (2 * idx.1 + 1))) := by
        constructive_ring
      rw [hAssoc, hTwoXInv, LawfulCommRing.one_mul]
    have hEvalEven : curOracle (2 * idx.1) =
        RoundPoly.evalCoeffs (interleavePoly F_poly G_poly) x := by
      rw [evalCoeffs_interleavePoly, ← hySq]
      have hTwoEq : CommRingOps.mul two
          (CommRingOps.add (RoundPoly.evalCoeffs F_poly (D_out.get idx))
            (CommRingOps.mul x (RoundPoly.evalCoeffs G_poly (D_out.get idx)))) =
          CommRingOps.mul two (curOracle (2 * idx.1)) := by
        have hLin : CommRingOps.mul two
            (CommRingOps.add (RoundPoly.evalCoeffs F_poly (D_out.get idx))
              (CommRingOps.mul x (RoundPoly.evalCoeffs G_poly (D_out.get idx)))) =
          CommRingOps.add
            (CommRingOps.mul two (RoundPoly.evalCoeffs F_poly (D_out.get idx)))
            (CommRingOps.mul (CommRingOps.mul two x) (RoundPoly.evalCoeffs G_poly (D_out.get idx))) := by
          constructive_ring
        rw [hLin, hSumAB, hDiffAB]
        dsimp only [two]
        constructive_ring
      have hMulInv := congrArg (CommRingOps.mul (LawfulField.inv two)) hTwoEq
      have hCancel : ∀ v : F,
          CommRingOps.mul (LawfulField.inv two) (CommRingOps.mul two v) = v := by
        intro v
        have hA : CommRingOps.mul (LawfulField.inv two) (CommRingOps.mul two v) =
            CommRingOps.mul (CommRingOps.mul two (LawfulField.inv two)) v := by constructive_ring
        rw [hA, hTwoInv, LawfulCommRing.one_mul]
      rw [hCancel, hCancel] at hMulInv
      exact hMulInv.symm
    have hEvalOdd : curOracle (2 * idx.1 + 1) =
        RoundPoly.evalCoeffs (interleavePoly F_poly G_poly) (D_in.get idxO) := by
      rw [hxONeg, evalCoeffs_interleavePoly]
      have hNegSq : CommRingOps.mul (CommRingOps.neg x) (CommRingOps.neg x) = D_out.get idx := by
        rw [hySq]; constructive_ring
      rw [hNegSq]
      have hTwoEq : CommRingOps.mul two
          (CommRingOps.add (RoundPoly.evalCoeffs F_poly (D_out.get idx))
            (CommRingOps.mul (CommRingOps.neg x) (RoundPoly.evalCoeffs G_poly (D_out.get idx)))) =
          CommRingOps.mul two (curOracle (2 * idx.1 + 1)) := by
        have hLin : CommRingOps.mul two
            (CommRingOps.add (RoundPoly.evalCoeffs F_poly (D_out.get idx))
              (CommRingOps.mul (CommRingOps.neg x) (RoundPoly.evalCoeffs G_poly (D_out.get idx)))) =
          CommRingOps.sub
            (CommRingOps.mul two (RoundPoly.evalCoeffs F_poly (D_out.get idx)))
            (CommRingOps.mul (CommRingOps.mul two x) (RoundPoly.evalCoeffs G_poly (D_out.get idx))) := by
          constructive_ring
        rw [hLin, hSumAB, hDiffAB]
        dsimp only [two]
        constructive_ring
      have hMulInv := congrArg (CommRingOps.mul (LawfulField.inv two)) hTwoEq
      have hCancel : ∀ v : F,
          CommRingOps.mul (LawfulField.inv two) (CommRingOps.mul two v) = v := by
        intro v
        have hA : CommRingOps.mul (LawfulField.inv two) (CommRingOps.mul two v) =
            CommRingOps.mul (CommRingOps.mul two (LawfulField.inv two)) v := by constructive_ring
        rw [hA, hTwoInv, LawfulCommRing.one_mul]
      rw [hCancel, hCancel] at hMulInv
      exact hMulInv.symm
    change 2 ≤ (if curOracle (2 * idx.1) = RoundPoly.evalCoeffs (interleavePoly F_poly G_poly) x then 1 else 0) +
      (if curOracle (2 * idx.1 + 1) = RoundPoly.evalCoeffs (interleavePoly F_poly G_poly) (D_in.get idxO) then 1 else 0)
    rw [ite_true_eq 1 0 hEvalEven, ite_true_eq 1 0 hEvalOdd]
    exact Nat.le_refl 2

private theorem filter_congr_mem {α : Type} {p q : α → Bool} :
    ∀ (xs : List α), (∀ x ∈ xs, p x = q x) → xs.filter p = xs.filter q
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.filter_cons, h x (.head xs), filter_congr_mem xs (fun z hz => h z (.tail x hz))]

private theorem hemVirtualFoldOracle_filter_eq {F : Type} [LawfulField F] [DecidableEq F]
    (D_in D_out : List F) (hOut : D_out.Nodup) (curOracle : Nat → F)
    (θ α β : F) (P : List F) :
    let fE := lookupDomOracle D_out (cosetEvenOracle curOracle)
    let fO := lookupDomOracle D_out (cosetOddOracle D_in curOracle)
    D_out.filter (fun y =>
      decide (RoundPoly.evalCoeffs P y =
        lookupDomOracle D_out (hemVirtualFoldOracle θ α β D_in D_out curOracle) y)) =
    D_out.filter (fun y =>
      let h_θ := CommRingOps.add (fE y) (CommRingOps.mul θ (fO y))
      decide (RoundPoly.evalCoeffs P y =
        CommRingOps.add (fO y)
          (CommRingOps.mul (CommRingOps.add α (CommRingOps.mul β y)) h_θ))) := by
  dsimp only
  refine filter_congr_mem D_out ?_
  intro y hy
  let idx : Fin D_out.length := ⟨D_out.idxOf y, List.idxOf_lt_length_of_mem hy⟩
  have hGet : D_out.get idx = y := List.getElem_idxOf _
  rw [← hGet,
      lookupDomOracle_get_c D_out _ hOut idx,
      lookupDomOracle_get_c D_out _ hOut idx,
      lookupDomOracle_get_c D_out _ hOut idx]
  unfold hemVirtualFoldOracle cosetEvenOracle cosetOddOracle
  dsimp only
  rw [list_getD_eq_get D_out CommRingOps.zero idx]

/-- Cartesian 4-challenge pool `S^4` for `(φ, θ, α, β)`. -/
def quadPool {F : Type} (S : List F) : List (F × F × F × F) :=
  S.flatMap (fun φ => (threePool S S).map (fun t => (φ, t.1, t.2.1, t.2.2)))

theorem quadPool_length {F : Type} (S : List F) :
    (quadPool S).length = S.length ^ 4 := by
  unfold quadPool
  have hAux : ∀ xs : List F,
      (xs.flatMap (fun φ => (threePool S S).map (fun t => (φ, t.1, t.2.1, t.2.2)))).length =
        xs.length * (threePool S S).length := by
    intro xs
    induction xs with
    | nil => simp
    | cons _ rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons, ih]
      rw [Nat.succ_mul, Nat.add_comm]
  rw [hAux S, threePool_length]
  change S.length * (S.length * (S.length * S.length)) = ((1 * S.length * S.length) * S.length) * S.length
  rw [Nat.one_mul, Nat.mul_assoc, Nat.mul_assoc]

theorem quadPool_nodup {F : Type} {S : List F} (hS : S.Nodup) : (quadPool S).Nodup := by
  have hT := threePool_nodup hS hS
  unfold quadPool
  have hAux : ∀ {xs : List F}, xs.Nodup →
      (xs.flatMap (fun φ => (threePool S S).map (fun t => (φ, t.1, t.2.1, t.2.2)))).Nodup := by
    intro xs hxs
    induction xs with
    | nil => exact .nil
    | cons φ rest ih =>
      rcases List.pairwise_cons.mp hxs with ⟨hNotMem, hRestNd⟩
      simp only [List.flatMap_cons]
      refine List.nodup_append.mpr ⟨?_, ih hRestNd, ?_⟩
      · refine List.Pairwise.map _ (fun a b hab hEq => hab ?_) hT
        rcases a with ⟨a2, a3, a4⟩
        rcases b with ⟨b2, b3, b4⟩
        injection hEq
      · intro x hx₁ y hx₂ hEq
        subst hEq
        rcases List.mem_map.mp hx₁ with ⟨_, _, rfl⟩
        rcases List.mem_flatMap.mp hx₂ with ⟨φ', hφ'Mem, hMap'⟩
        rcases List.mem_map.mp hMap' with ⟨_, _, hEq'⟩
        injection hEq' with hEqφ _
        exact hNotMem φ' hφ'Mem hEqφ.symm
  exact hAux hS

private theorem mem_quadPool_iff {F : Type} {S : List F} (q : F × F × F × F) :
    q ∈ quadPool S ↔ q.1 ∈ S ∧ (q.2.1, q.2.2.1, q.2.2.2) ∈ threePool S S := by
  unfold quadPool
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨φ, hφ, hMap⟩
    rcases List.mem_map.mp hMap with ⟨t, ht, hEq⟩
    rcases q with ⟨q1, q2, q3, q4⟩
    rcases t with ⟨t1, t2, t3⟩
    injection hEq with h1 h234
    injection h234 with h2 h34
    injection h34 with h3 h4
    subst h1; subst h2; subst h3; subst h4
    exact ⟨hφ, ht⟩
  · rintro ⟨hφ, ht⟩
    refine ⟨q.1, hφ, List.mem_map.mpr ⟨(q.2.1, q.2.2.1, q.2.2.2), ht, ?_⟩⟩
    rcases q with ⟨_, _, _, _⟩; rfl

private theorem flatMap_map_filter_eq_qsum {α β γ : Type} (xs : List α) (inner : List β)
    (mk : α → β → γ) (pred : γ → Bool) :
    ((xs.flatMap (fun a => inner.map (mk a))).filter pred).length =
      qsum xs.length (fun i => (inner.filter (fun b => pred (mk (xs.get i) b))).length) := by
  induction xs with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.flatMap_cons, List.filter_append, List.length_append, List.length_cons,
      qsum, List.get, ih]
    congr 1
    clear ih rest
    induction inner with
    | nil => rfl
    | cons b bs ihb =>
      simp only [List.map_cons, List.filter_cons]
      cases pred (mk a b) <;>
        simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons, ihb]

private theorem quadPool_filter_length_eq_qsum {F : Type} (S : List F)
    (pred : F × F × F × F → Bool) :
    ((quadPool S).filter pred).length =
      qsum S.length (fun iφ =>
        qsum S.length (fun iθ =>
          qsum S.length (fun iα =>
            qsum S.length (fun iβ =>
              if pred (S.get iφ, S.get iθ, S.get iα, S.get iβ) = true then 1 else 0)))) := by
  unfold quadPool
  rw [flatMap_map_filter_eq_qsum]
  apply qsum_congr; intro iφ
  unfold threePool
  rw [flatMap_map_filter_eq_qsum]
  apply qsum_congr; intro iθ
  unfold prodPool
  rw [flatMap_map_filter_eq_qsum]
  apply qsum_congr; intro iα
  exact (qsum_get_filter_eq (fun β => pred (S.get iφ, S.get iθ, S.get iα, β)) S).symm

/-- **Single-Step Four-Challenge `(φ, θ, α, β)` Dual-Bridge Coset Fold Soundness**:
    Over `[LawfulField F] [DecidableEq F]`, if `(curOracle, kernel, curClaim)` has no valid
    degree-`≤ 2 d + 1` witness at agreement `2 * A` on `D_in` (`IsAntipodalDomainPair D_in D_out`,
    `kernel.length = 2 * m_K`, `d + 2 ≤ A`), then for ANY 5 bridge wires `(w₀, w₁, w₂, c_F, c_G)`,
    at most
    `(S.length * S.length) * badMca +
     (3 * |gsDecodeList d A D_out fE| * |gsDecodeList d A D_out fO| +
      |gsDecodeList (d + 1) A D_out fE| * |gsDecodeList (d + 1) A D_out fO|) * S.length ^ 3`
    quadruples `(φ, θ, α, β) ∈ quadPool S` admit a post-fold witness `P` passing `polyWitnessValid`
    at `(D_out, A + 1, d + 1, hemVirtualFoldOracle, hemKernelFold, hemBridgeFoldClaim)`. -/
theorem singleStep_bridge_four_challenge_fold_bound {F : Type} [LawfulField F] [DecidableEq F]
    (D_in D_out S kernel : List F) (d A m_K badMca : Nat)
    (curOracle : Nat → F) (curClaim w₀ w₁ w₂ c_F c_G : F)
    (hPair : IsAntipodalDomainPair D_in D_out)
    (hS : S.Nodup) (hdA : d + 2 ≤ A)
    (hKernLen : kernel.length = 2 * m_K)
    (hDecomp : AffineFoldDecompBound D_out S (d + 1) (A + 1) badMca)
    (hInvalidIn : ∀ Q : List F,
      polyWitnessValid D_in (2 * A) (2 * d + 1) curOracle kernel curClaim Q = false)
    (L : List (Fin (quadPool S).length)) (hNd : L.Nodup)
    (hFlip : ∀ ch ∈ L, ¬¬ ∃ P : List F,
      let q := (quadPool S).get ch
      polyWitnessValid D_out (A + 1) (d + 1)
        (hemVirtualFoldOracle q.2.1 q.2.2.1 q.2.2.2 D_in D_out curOracle)
        (hemKernelFold q.1 kernel)
        (hemBridgeFoldClaim curClaim w₀ w₁ w₂ c_F c_G q.1 q.2.1 q.2.2.1 q.2.2.2) P = true) :
    let fE := lookupDomOracle D_out (cosetEvenOracle curOracle)
    let fO := lookupDomOracle D_out (cosetOddOracle D_in curOracle)
    L.length ≤ (S.length * S.length) * badMca +
      (3 * ((gsDecodeList d A D_out fE).length * (gsDecodeList d A D_out fO).length) +
       (gsDecodeList (d + 1) A D_out fE).length * (gsDecodeList (d + 1) A D_out fO).length) *
        (S.length ^ 3) := by
  dsimp only
  let fE := lookupDomOracle D_out (cosetEvenOracle curOracle)
  let fO := lookupDomOracle D_out (cosetOddOracle D_in curOracle)
  let kE := (splitEvenOdd kernel).1
  let kO := (splitEvenOdd kernel).2
  have hkSpec0 := splitEvenOdd_spec m_K kernel CommRingOps.zero hKernLen
  have hkLenEq : kE.length = kO.length := hkSpec0.1.trans hkSpec0.2.1.symm
  have hkInt : hemInterleave kE kO = kernel := hkSpec0.2.2.1
  let Qs : List (F × F × F × F) := L.map (fun ch => (quadPool S).get ch)
  have hQsLen : Qs.length = L.length := List.length_map _
  have hQsNd : Qs.Nodup :=
    List.Pairwise.map _ (fun a b hab hEq => hab (nodup_get_inj (quadPool_nodup hS) hEq)) hNd
  have hQsMem : ∀ q ∈ Qs, q ∈ quadPool S := by
    intro q hq
    rcases List.mem_map.mp hq with ⟨ch, _, rfl⟩
    exact list_get_mem _ ch
  have hQsFlip : ∀ q ∈ Qs, ¬¬ ∃ P : List F,
      polyWitnessValid D_out (A + 1) (d + 1)
        (hemVirtualFoldOracle q.2.1 q.2.2.1 q.2.2.2 D_in D_out curOracle)
        (hemKernelFold q.1 kernel)
        (hemBridgeFoldClaim curClaim w₀ w₁ w₂ c_F c_G q.1 q.2.1 q.2.2.1 q.2.2.2) P = true := by
    intro q hq
    rcases List.mem_map.mp hq with ⟨ch, hchL, rfl⟩
    exact hFlip ch hchL
  let candFLo := gsDecodeList d A D_out fE
  let candGLo := gsDecodeList d A D_out fO
  let candFHi := gsDecodeList (d + 1) A D_out fE
  let candGHi := gsDecodeList (d + 1) A D_out fO
  let rawPairsLo := candFLo.flatMap (fun pF => candGLo.map (fun pG => (pF, pG)))
  let jointPairsLo := rawPairsLo.filter (fun fg =>
    decide (A ≤ (D_out.filter (fun y =>
      decide (RoundPoly.evalCoeffs fg.1.val y = fE y) &&
      decide (RoundPoly.evalCoeffs fg.2.val y = fO y))).length))
  let pairsHi := candFHi.flatMap (fun pF => candGHi.map (fun pG => (pF, pG)))
  have hRawLoLen : rawPairsLo.length = candFLo.length * candGLo.length := by
    dsimp only [rawPairsLo]
    clear hQsFlip hQsMem hQsNd hQsLen Qs hFlip hNd L hDecomp hInvalidIn
    induction candFLo with
    | nil => simp
    | cons _ rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons, ih]
      rw [Nat.succ_mul, Nat.add_comm]
  have hJointLoLen : jointPairsLo.length ≤ candFLo.length * candGLo.length := by
    rw [← hRawLoLen]; exact List.length_filter_le _ _
  have hPairsHiLen : pairsHi.length = candFHi.length * candGHi.length := by
    dsimp only [pairsHi]
    clear hQsFlip hQsMem hQsNd hQsLen Qs hFlip hNd L hDecomp hInvalidIn
    induction candFHi with
    | nil => simp
    | cons _ rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons, ih]
      rw [Nat.succ_mul, Nat.add_comm]
  let matchLo : GsUniPoly F × GsUniPoly F → F × F × F × F → Bool :=
    fun fg q =>
      let k' := List.zipWith (fun a b => CommRingOps.add a (CommRingOps.mul q.1 b)) kE kO
      decide (ringDot (affineCombine q.2.1 q.2.2.1 q.2.2.2 fg.1.val fg.2.val) k' =
        hemBridgeFoldClaim curClaim w₀ w₁ w₂ c_F c_G q.1 q.2.1 q.2.2.1 q.2.2.2)
  let matchOv : GsUniPoly F × GsUniPoly F → F × F × F × F → Bool :=
    fun fg q =>
      decide (coeffAt fg.1.val (d + 1) ≠ CommRingOps.zero ∨
        coeffAt fg.2.val (d + 1) ≠ CommRingOps.zero) &&
      decide (CommRingOps.add (coeffAt fg.1.val (d + 1))
        (CommRingOps.mul q.2.1 (coeffAt fg.2.val (d + 1))) = CommRingOps.zero)
  let anyLo : F × F × F × F → Bool := fun q => jointPairsLo.any (fun fg => matchLo fg q)
  let anyOv : F × F × F × F → Bool := fun q => pairsHi.any (fun fg => matchOv fg q)
  let anyAll : F × F × F × F → Bool := fun q => anyLo q || anyOv q
  have hSplitAll := length_filter_add_not anyAll Qs
  have hSubUnion : (Qs.filter anyAll).length ≤ (Qs.filter anyLo).length + (Qs.filter anyOv).length :=
    JohnsonBound.filter_length_le_add anyAll anyLo anyOv Qs (fun _ _ h => Bool.or_eq_true_iff.mp h)
  -- 1. Low-degree correlated pairs: each `(pF, pG) ∈ jointPairsLo` contributes `≤ 3 * S.length ^ 3`:
  have hLoBound : (Qs.filter anyLo).length ≤ jointPairsLo.length * (3 * S.length ^ 3) := by
    refine filter_any_length_le jointPairsLo matchLo Qs (3 * S.length ^ 3) ?_
    intro fg hfg
    rcases List.mem_filter.mp hfg with ⟨hfgRaw, hfgJointDec⟩
    rcases List.mem_flatMap.mp hfgRaw with ⟨pF, hpFMem, hInG⟩
    rcases List.mem_map.mp hInG with ⟨pG, hpGMem, rfl⟩
    have hpFLen := ((mem_gsDecodeList_iff fE hPair.nodup_out (by omega) pF).mp hpFMem).1
    have hpGLen := ((mem_gsDecodeList_iff fO hPair.nodup_out (by omega) pG).mp hpGMem).1
    have hfgJoint := of_decide_eq_true hfgJointDec
    have hFalseClaim : CommRingOps.add (ringDot pF.val kE) (ringDot pG.val kO) ≠ curClaim := by
      intro hSumEq
      let Q_lift := interleavePoly pF.val pG.val
      have hQLen : Q_lift.length ≤ (2 * d + 1) + 1 := by
        have h := interleavePoly_length_le (d + 1) pF.val pG.val hpFLen hpGLen
        omega
      have hQAg : 2 * A ≤ hemCosetAgreeCount D_in curOracle Q_lift :=
        Nat.le_trans (Nat.mul_le_mul_left 2 hfgJoint)
          (antipodal_joint_agree_lifts hPair curOracle pF.val pG.val)
      have hQDot : ringDot Q_lift kernel = curClaim := by
        rw [← hkInt, ringDot_interleavePoly_hemInterleave kE kO pF.val pG.val hkLenEq]
        exact hSumEq
      have hVal : polyWitnessValid D_in (2 * A) (2 * d + 1) curOracle kernel curClaim Q_lift = true := by
        unfold polyWitnessValid
        rw [decide_eq_true hQLen, decide_eq_true hQAg, decide_eq_true hQDot]
        rfl
      rw [hInvalidIn Q_lift] at hVal
      exact Bool.noConfusion hVal
    have hSubQuad : ∀ q ∈ Qs.filter (matchLo (pF, pG)),
        q ∈ (quadPool S).filter (matchLo (pF, pG)) := by
      intro q hq
      rcases List.mem_filter.mp hq with ⟨hqQs, hqM⟩
      exact List.mem_filter.mpr ⟨hQsMem q hqQs, hqM⟩
    have hSubLen := nodup_length_le_of_subset (List.Pairwise.filter _ hQsNd) hSubQuad
    rw [quadPool_filter_length_eq_qsum] at hSubLen
    have hEqSum :
        qsum S.length (fun iφ =>
          qsum S.length (fun iθ =>
            qsum S.length (fun iα =>
              qsum S.length (fun iβ =>
                if matchLo (pF, pG) (S.get iφ, S.get iθ, S.get iα, S.get iβ) = true then 1 else 0)))) =
        qsum S.length (fun iφ =>
          qsum S.length (fun iθ =>
            qsum S.length (fun iα =>
              qsum S.length (fun iβ =>
                let φ := S.get iφ; let θ := S.get iθ; let α := S.get iα; let β := S.get iβ
                let k' := List.zipWith (fun a b => CommRingOps.add a (CommRingOps.mul φ b)) kE kO
                if ringDot (affineCombine θ α β pF.val pG.val) k' =
                    hemBridgeFoldClaim curClaim w₀ w₁ w₂ c_F c_G φ θ α β then 1 else 0)))) := by
      apply qsum_congr; intro iφ
      apply qsum_congr; intro iθ
      apply qsum_congr; intro iα
      apply qsum_congr; intro iβ
      dsimp only [matchLo]
      exact ite_decide_eq
    rw [hEqSum] at hSubLen
    exact Nat.le_trans hSubLen
      (hemBridge_bad_quads_le_three_cube S hS curClaim w₀ w₁ w₂ c_F c_G pF.val pG.val kE kO
        hkLenEq hFalseClaim)
  -- 2. Overflow pairs: each `(pF, pG) ∈ pairsHi` determines at most `1` valid `θ`, hence `≤ S.length ^ 3` quads:
  have hOvBound : (Qs.filter anyOv).length ≤ pairsHi.length * (S.length ^ 3) := by
    refine filter_any_length_le pairsHi matchOv Qs (S.length ^ 3) ?_
    intro fg hfg
    rcases List.mem_flatMap.mp hfg with ⟨pF, _, hInG⟩
    rcases List.mem_map.mp hInG with ⟨pG, _, rfl⟩
    let cF := coeffAt pF.val (d + 1)
    let cG := coeffAt pG.val (d + 1)
    let subQ := Qs.filter (matchOv (pF, pG))
    let goodθ := S.filter (fun θ =>
      decide (cF ≠ CommRingOps.zero ∨ cG ≠ CommRingOps.zero) &&
      decide (CommRingOps.add cF (CommRingOps.mul θ cG) = CommRingOps.zero))
    have hGoodθLe1 : goodθ.length ≤ 1 := by
      if hcG : cG ≠ CommRingOps.zero then
        have hSub : ∀ θ ∈ goodθ,
            θ ∈ S.filter (fun θ => decide (CommRingOps.add cF (CommRingOps.mul θ cG) = CommRingOps.zero)) := by
          intro θ hθ
          rcases List.mem_filter.mp hθ with ⟨hθS, hBoth⟩
          exact List.mem_filter.mpr ⟨hθS, ((Bool.and_eq_true _ _).mp hBoth).2⟩
        exact Nat.le_trans (nodup_length_le_of_subset (List.Pairwise.filter _ hS) hSub)
          (linear_one_var_bad_le_one S hS cF cG hcG)
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
    have hPart := JohnsonBound.count_partition_le (fun q => q.2.1) (S.length ^ 3) subQ goodθ ?_ ?_
    · exact Nat.le_trans hPart (by
        have hMul := Nat.mul_le_mul_right (S.length ^ 3) hGoodθLe1
        rw [Nat.one_mul] at hMul
        exact hMul)
    · intro q hq
      rcases List.mem_filter.mp hq with ⟨hqQs, hqOv⟩
      have hMem3 := (mem_quadPool_iff q).mp (hQsMem q hqQs)
      have hθS := ((mem_threePool_iff _).mp hMem3.2).1
      exact List.mem_filter.mpr ⟨hθS, hqOv⟩
    · intro θ _
      let fib := subQ.filter (fun q => decide (q.2.1 = θ))
      have hFibNd : fib.Nodup := List.Pairwise.filter _ (List.Pairwise.filter _ hQsNd)
      let proj3 := fib.attach.map (fun u => (u.1.1, u.1.2.2.1, u.1.2.2.2))
      have hProjNd : proj3.Nodup := by
        refine List.Pairwise.map _ (fun u v huv hEq => huv ?_) (nodup_attach hFibNd)
        apply Subtype.ext
        have huθ : u.1.2.1 = θ := of_decide_eq_true (List.mem_filter.mp u.2).2
        have hvθ : v.1.2.1 = θ := of_decide_eq_true (List.mem_filter.mp v.2).2
        rcases u with ⟨⟨u1, u2, u3, u4⟩, _⟩
        rcases v with ⟨⟨v1, v2, v3, v4⟩, _⟩
        dsimp only at huθ hvθ hEq
        injection hEq with h1 h34
        injection h34 with h3 h4
        subst huθ; subst hvθ; subst h1; subst h3; subst h4; rfl
      have hSub3 : ∀ t ∈ proj3, t ∈ threePool S S := by
        intro t ht
        rcases List.mem_map.mp ht with ⟨⟨q, hqFib⟩, _, rfl⟩
        have hqMem := (mem_quadPool_iff q).mp
          (hQsMem q (List.mem_filter.mp (List.mem_filter.mp hqFib).1).1)
        have hPairMem := ((mem_threePool_iff _).mp hqMem.2).2
        exact (mem_threePool_iff _).mpr ⟨hqMem.1, hPairMem⟩
      have hLen := nodup_length_le_of_subset hProjNd hSub3
      have hProjLen : proj3.length = fib.length := by
        dsimp only [proj3]; rw [List.length_map, List.length_attach]
      have hPow3 : S.length * (S.length * S.length) = S.length ^ 3 := by
        change S.length * (S.length * S.length) = (1 * S.length * S.length) * S.length
        rw [Nat.one_mul, Nat.mul_assoc]
      rw [hProjLen, threePool_length, hPow3] at hLen
      exact hLen
  -- 3. Non-decomposing quadruples: partition over `(φ, θ) ∈ prodPool S`, each fiber `≤ badMca`:
  let Qs_non := Qs.filter (fun q => !anyAll q)
  have hNonBound : Qs_non.length ≤ (S.length * S.length) * badMca := by
    have hPart := JohnsonBound.count_partition_le (fun q => (q.1, q.2.1)) badMca Qs_non (prodPool S) ?_ ?_
    · rwa [prodPool_length] at hPart
    · intro q hq
      have hqMem := (mem_quadPool_iff q).mp (hQsMem q (List.mem_filter.mp hq).1)
      have hθS := ((mem_threePool_iff _).mp hqMem.2).1
      unfold prodPool
      exact List.mem_flatMap.mpr ⟨q.1, hqMem.1, List.mem_map.mpr ⟨q.2.1, hθS, rfl⟩⟩
    · intro φθ _
      let φ := φθ.1
      let θ := φθ.2
      let fib := Qs_non.filter (fun q => decide ((q.1, q.2.1) = φθ))
      have hFibNd : fib.Nodup := List.Pairwise.filter _ (List.Pairwise.filter _ hQsNd)
      let toIdx : { q : F × F × F × F // q ∈ fib } → Fin (prodPool S).length := fun u =>
        let p := (u.1.2.2.1, u.1.2.2.2)
        have hqMem := (mem_quadPool_iff u.1).mp
          (hQsMem u.1 (List.mem_filter.mp (List.mem_filter.mp u.2).1).1)
        have hpMem : p ∈ prodPool S := ((mem_threePool_iff _).mp hqMem.2).2
        ⟨(prodPool S).idxOf p, List.idxOf_lt_length_of_mem hpMem⟩
      have hToIdxGet : ∀ u : { q : F × F × F × F // q ∈ fib },
          (prodPool S).get (toIdx u) = (u.1.2.2.1, u.1.2.2.2) := by
        intro u; dsimp only [toIdx]; exact List.getElem_idxOf _
      let idxList := fib.attach.map toIdx
      have hIdxNd : idxList.Nodup := by
        refine List.Pairwise.map _ (fun u v huv hEq => huv ?_) (nodup_attach hFibNd)
        apply Subtype.ext
        have h1 := hToIdxGet u
        have h2 := hToIdxGet v
        rw [hEq] at h1
        have hpEq := h1.symm.trans h2
        have huφθ : (u.1.1, u.1.2.1) = φθ := of_decide_eq_true (List.mem_filter.mp u.2).2
        have hvφθ : (v.1.1, v.1.2.1) = φθ := of_decide_eq_true (List.mem_filter.mp v.2).2
        have hφθEq := huφθ.trans hvφθ.symm
        rcases u with ⟨⟨u1, u2, u3, u4⟩, _⟩
        rcases v with ⟨⟨v1, v2, v3, v4⟩, _⟩
        dsimp only at hφθEq hpEq
        injection hφθEq with e1 e2
        injection hpEq with e3 e4
        subst e1; subst e2; subst e3; subst e4; rfl
      have hDecompFib : idxList.length ≤ badMca := by
        refine hDecomp (fO, fun y => CommRingOps.add (fE y) (CommRingOps.mul θ (fO y)))
          idxList hIdxNd ?_
        intro ch hch hNo
        rcases List.mem_map.mp hch with ⟨u, _, rfl⟩
        rcases List.mem_filter.mp u.2 with ⟨huNon, huφθDec⟩
        have huφθ : (u.1.1, u.1.2.1) = φθ := of_decide_eq_true huφθDec
        have huφ : u.1.1 = φ := congrArg Prod.fst huφθ
        have huθ : u.1.2.1 = θ := congrArg Prod.snd huφθ
        rcases List.mem_filter.mp huNon with ⟨huQs, hNotAll⟩
        refine hQsFlip u.1 huQs ?_
        rintro ⟨P, hPVal⟩
        unfold polyWitnessValid at hPVal
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hPVal
        rcases hPVal with ⟨⟨hPLen, hPAg⟩, hPCl⟩
        rw [hemCosetAgreeCount_eq_filter_lookup_c D_out _ P hPair.nodup_out,
            hemVirtualFoldOracle_filter_eq D_in D_out hPair.nodup_out curOracle] at hPAg
        refine hNo ⟨P, ?_, ?_⟩
        · unfold affineMcaAccepts
          rw [list_getD_eq_get (prodPool S) _ (toIdx u), hToIdxGet u]
          have hLt : (toIdx u).1 < (prodPool S).length := (toIdx u).2
          rw [huθ] at hPAg
          rw [decide_eq_true hLt, decide_eq_true hPLen, decide_eq_true hPAg]
          rfl
        · rintro ⟨G_poly, H_poly, ⟨hGLen, hHLen, hJoint⟩, hTrimEq⟩
          rw [hToIdxGet u] at hTrimEq
          let F_poly := polyAddVar H_poly (polyScaleVar (CommRingOps.neg θ) G_poly)
          have hScaleLen : (polyScaleVar (CommRingOps.neg θ) G_poly).length ≤ d + 2 := by
            simp only [polyScaleVar, List.length_map]; exact hGLen
          have hFLen : F_poly.length ≤ d + 2 :=
            polyAddVar_length_le H_poly _ (d + 2) (by omega) hScaleLen
          let pF : GsUniPoly F := GsUniPoly.ofCoeffs F_poly
          let pG : GsUniPoly F := GsUniPoly.ofCoeffs G_poly
          have hJointFG : A ≤ (D_out.filter (fun y =>
              decide (RoundPoly.evalCoeffs pF.val y = fE y) &&
              decide (RoundPoly.evalCoeffs pG.val y = fO y))).length := by
            have hSub : ∀ y ∈ D_out.filter (fun y =>
                decide (RoundPoly.evalCoeffs G_poly y = fO y) &&
                decide (RoundPoly.evalCoeffs H_poly y = CommRingOps.add (fE y) (CommRingOps.mul θ (fO y)))),
                y ∈ D_out.filter (fun y =>
                  decide (RoundPoly.evalCoeffs pF.val y = fE y) &&
                  decide (RoundPoly.evalCoeffs pG.val y = fO y)) := by
              intro y hy
              rcases List.mem_filter.mp hy with ⟨hyD, hB⟩
              rcases (Bool.and_eq_true _ _).mp hB with ⟨hGyDec, hHyDec⟩
              have hGy := of_decide_eq_true hGyDec
              have hHy := of_decide_eq_true hHyDec
              refine List.mem_filter.mpr ⟨hyD, Bool.and_eq_true_iff.mpr ⟨decide_eq_true ?_, decide_eq_true ?_⟩⟩
              · change RoundPoly.evalCoeffs (trimPoly F_poly) y = fE y
                rw [evalCoeffs_trimPoly]
                dsimp only [F_poly]
                rw [evalCoeffs_polyAddVar, evalCoeffs_polyScaleVar, hHy, hGy]
                constructive_ring
              · change RoundPoly.evalCoeffs (trimPoly G_poly) y = fO y
                rw [evalCoeffs_trimPoly]; exact hGy
            exact Nat.le_trans hJoint (nodup_length_le_of_subset (List.Pairwise.filter _ hPair.nodup_out) hSub)
          have hJointF : A ≤ (D_out.filter (fun y => decide (RoundPoly.evalCoeffs pF.val y = fE y))).length := by
            have hSub : ∀ y ∈ D_out.filter (fun y =>
                decide (RoundPoly.evalCoeffs pF.val y = fE y) &&
                decide (RoundPoly.evalCoeffs pG.val y = fO y)),
                y ∈ D_out.filter (fun y => decide (RoundPoly.evalCoeffs pF.val y = fE y)) := by
              intro y hy
              rcases List.mem_filter.mp hy with ⟨hyD, hB⟩
              exact List.mem_filter.mpr ⟨hyD, ((Bool.and_eq_true _ _).mp hB).1⟩
            exact Nat.le_trans hJointFG (nodup_length_le_of_subset (List.Pairwise.filter _ hPair.nodup_out) hSub)
          have hJointG : A ≤ (D_out.filter (fun y => decide (RoundPoly.evalCoeffs pG.val y = fO y))).length := by
            have hSub : ∀ y ∈ D_out.filter (fun y =>
                decide (RoundPoly.evalCoeffs pF.val y = fE y) &&
                decide (RoundPoly.evalCoeffs pG.val y = fO y)),
                y ∈ D_out.filter (fun y => decide (RoundPoly.evalCoeffs pG.val y = fO y)) := by
              intro y hy
              rcases List.mem_filter.mp hy with ⟨hyD, hB⟩
              exact List.mem_filter.mpr ⟨hyD, ((Bool.and_eq_true _ _).mp hB).2⟩
            exact Nat.le_trans hJointFG (nodup_length_le_of_subset (List.Pairwise.filter _ hPair.nodup_out) hSub)
          have hpFHi : pF ∈ candFHi :=
            (mem_gsDecodeList_iff fE hPair.nodup_out (by omega) pF).mpr
              ⟨Nat.le_trans (trimPoly_length_le F_poly) hFLen, hJointF⟩
          have hpGHi : pG ∈ candGHi :=
            (mem_gsDecodeList_iff fO hPair.nodup_out (by omega) pG).mpr
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
              (mem_gsDecodeList_iff fE hPair.nodup_out (by omega) pF).mpr ⟨hpFLoLen, hJointF⟩
            have hpGLo : pG ∈ candGLo :=
              (mem_gsDecodeList_iff fO hPair.nodup_out (by omega) pG).mpr ⟨hpGLoLen, hJointG⟩
            have hMemJointLo : (pF, pG) ∈ jointPairsLo :=
              List.mem_filter.mpr ⟨List.mem_flatMap.mpr ⟨pF, hpFLo, List.mem_map.mpr ⟨pG, hpGLo, rfl⟩⟩,
                decide_eq_true hJointFG⟩
            have hMatchLoTrue : matchLo (pF, pG) u.1 = true := by
              dsimp only [matchLo]
              apply decide_eq_true
              rw [huφ, huθ] at hPCl ⊢
              let k' := List.zipWith (fun a b => CommRingOps.add a (CommRingOps.mul φ b)) kE kO
              have hkFold := (splitEvenOdd_spec m_K kernel φ hKernLen).2.2.2.1
              rw [hkFold, ringDot_append_zero] at hPCl
              have hDot := congrArg (fun q => ringDot q k') hTrimEq
              rw [ringDot_trimPoly_eq, ringDot_trimPoly_eq,
                  ringDot_polyAddVar, ringDot_polyAddVar,
                  ringDot_polyScaleVar, ringDot_polyScaleVar] at hDot
              have hCombDot : ringDot (affineCombine θ u.1.2.2.1 u.1.2.2.2 pF.val pG.val) k' =
                  CommRingOps.add (ringDot pG.val k')
                    (CommRingOps.add
                      (CommRingOps.mul u.1.2.2.1
                        (CommRingOps.add (ringDot pF.val k') (CommRingOps.mul θ (ringDot pG.val k'))))
                      (CommRingOps.mul u.1.2.2.2
                        (CommRingOps.add (ringDot (shiftPoly pF.val) k')
                          (CommRingOps.mul θ (ringDot (shiftPoly pG.val) k'))))) := by
                unfold affineCombine
                dsimp only
                rw [ringDot_polyAddVar, ringDot_polyAddVar, ringDot_polyScaleVar, ringDot_polyScaleVar,
                    ringDot_polyAddVar, ringDot_polyScaleVar,
                    ringDot_shiftPoly_polyAddVar]
                have hScaleShift : shiftPoly (polyScaleVar θ pG.val) =
                    polyScaleVar θ (shiftPoly pG.val) := by
                  simp only [shiftPoly, polyScaleVar, List.map_cons, LawfulCommRing.mul_zero]
                rw [hScaleShift, ringDot_polyScaleVar]
              have hDotF : CommRingOps.add (ringDot pF.val k')
                  (CommRingOps.mul θ (ringDot pG.val k')) = ringDot H_poly k' := by
                change CommRingOps.add (ringDot (trimPoly F_poly) k')
                  (CommRingOps.mul θ (ringDot (trimPoly G_poly) k')) = _
                rw [ringDot_trimPoly_eq, ringDot_trimPoly_eq]
                dsimp only [F_poly]
                rw [ringDot_polyAddVar, ringDot_polyScaleVar]
                constructive_ring
              have hShiftF : CommRingOps.add (ringDot (shiftPoly pF.val) k')
                  (CommRingOps.mul θ (ringDot (shiftPoly pG.val) k')) =
                  ringDot (shiftPoly H_poly) k' := by
                change CommRingOps.add (ringDot (shiftPoly (trimPoly F_poly)) k')
                  (CommRingOps.mul θ (ringDot (shiftPoly (trimPoly G_poly)) k')) = _
                rw [ringDot_shiftPoly_trimPoly_eq, ringDot_shiftPoly_trimPoly_eq]
                dsimp only [F_poly]
                have hScaleShift : shiftPoly (polyScaleVar (CommRingOps.neg θ) G_poly) =
                    polyScaleVar (CommRingOps.neg θ) (shiftPoly G_poly) := by
                  simp only [shiftPoly, polyScaleVar, List.map_cons, LawfulCommRing.mul_zero]
                rw [ringDot_shiftPoly_polyAddVar, hScaleShift, ringDot_polyScaleVar]
                constructive_ring
              have hGTrim : ringDot pG.val k' = ringDot G_poly k' :=
                ringDot_trimPoly_eq G_poly k'
              rw [hCombDot, hDotF, hShiftF, hGTrim]
              exact hDot.symm.trans hPCl
            have hAnyLo : anyLo u.1 = true :=
              List.any_eq_true.mpr ⟨(pF, pG), hMemJointLo, hMatchLoTrue⟩
            have hAllTrue : anyAll u.1 = true := by simp [anyAll, hAnyLo]
            rw [hAllTrue] at hNotAll
            exact absurd hNotAll (by decide)
          else
            have hOrNz : coeffAt pF.val (d + 1) ≠ CommRingOps.zero ∨
                coeffAt pG.val (d + 1) ≠ CommRingOps.zero := by
              if h1 : coeffAt pF.val (d + 1) = CommRingOps.zero then
                right; exact fun h2 => hBothZero ⟨h1, h2⟩
              else
                exact .inl h1
            have hMemHi : (pF, pG) ∈ pairsHi :=
              List.mem_flatMap.mpr ⟨pF, hpFHi, List.mem_map.mpr ⟨pG, hpGHi, rfl⟩⟩
            have hMatchOvTrue : matchOv (pF, pG) u.1 = true := by
              dsimp only [matchOv]
              rw [huθ]
              exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true hOrNz, decide_eq_true hTopSum⟩
            have hAnyOv : anyOv u.1 = true :=
              List.any_eq_true.mpr ⟨(pF, pG), hMemHi, hMatchOvTrue⟩
            have hAllTrue : anyAll u.1 = true := by simp [anyAll, hAnyOv]
            rw [hAllTrue] at hNotAll
            exact absurd hNotAll (by decide)
      have hIdxLenEq : idxList.length = fib.length := by
        dsimp only [idxList]; rw [List.length_map, List.length_attach]
      rwa [hIdxLenEq] at hDecompFib
  have hLoBound2 : (Qs.filter anyLo).length ≤
      (candFLo.length * candGLo.length) * (3 * S.length ^ 3) :=
    Nat.le_trans hLoBound (Nat.mul_le_mul_right _ hJointLoLen)
  rw [hPairsHiLen] at hOvBound
  dsimp only [candFLo, candGLo, candFHi, candGHi, Qs_non, fE, fO] at hLoBound2 hOvBound hNonBound
  have hArith :
      ((gsDecodeList d A D_out (lookupDomOracle D_out (cosetEvenOracle curOracle))).length *
        (gsDecodeList d A D_out (lookupDomOracle D_out (cosetOddOracle D_in curOracle))).length) *
        (3 * S.length ^ 3) +
      ((gsDecodeList (d + 1) A D_out (lookupDomOracle D_out (cosetEvenOracle curOracle))).length *
        (gsDecodeList (d + 1) A D_out (lookupDomOracle D_out (cosetOddOracle D_in curOracle))).length) *
        (S.length ^ 3) =
      (3 * ((gsDecodeList d A D_out (lookupDomOracle D_out (cosetEvenOracle curOracle))).length *
        (gsDecodeList d A D_out (lookupDomOracle D_out (cosetOddOracle D_in curOracle))).length) +
       (gsDecodeList (d + 1) A D_out (lookupDomOracle D_out (cosetEvenOracle curOracle))).length *
        (gsDecodeList (d + 1) A D_out (lookupDomOracle D_out (cosetOddOracle D_in curOracle))).length) *
        (S.length ^ 3) := by
    rw [Nat.add_mul, Nat.mul_assoc 3 _ (S.length ^ 3),
        Nat.mul_left_comm
          ((gsDecodeList d A D_out (lookupDomOracle D_out (cosetEvenOracle curOracle))).length *
            (gsDecodeList d A D_out (lookupDomOracle D_out (cosetOddOracle D_in curOracle))).length)
          3 (S.length ^ 3)]
  omega

/-- Closed-form bad-quadruple count for one 4-challenge `(φ, θ, α, β)` binary coset fold at
    `(n, d, A, B, m, Dy)` over pool size `q = S.length`. -/
