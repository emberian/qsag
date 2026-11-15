module
/-
# Qsag.HemMultistageRbrAndSaltedQrom — Equal-Degree `θ`-Mixing Lift, Multi-Batch `verifyHemAffineWhir` Bridge & Compressed-Oracle Salted-Merkle QROM Budget

Constructive Lean 4.35 theorems closing three structural gaps across `HemSlicedFoldBudget`,
`HemWhirRbrSoundness`, `HemVerifierAcceptance`, and `HemExtractedOpeningBridge`
(zero custom axioms, purely constructive extractors):

1. **Equal-Degree `θ`-Exception Bound & Full Three-Challenge `(θ, α, β)` Lift
   (`equal_degree_bad_theta_bound`, `equal_degree_three_challenge_bound`)**:
   - Eliminates the unproved `hInvalidMix` premise in `HemSlicedFoldBudget.sliced_equal_degree_fixed_theta_bound`
     (witnessed necessary by `tooth_equal_degree_invalid_mixture`).
   - Observes that `f(z) + θ g(z) = f(z) + (θ + 0 · z) g(z)` is the `β = 0` slice of `prodPool S`
     when `0 ∈ S`. Any `AffineFoldDecompBound D S (d + 1) A badTheta` combined with degree collapse
     `F_sub := polySubVar H (polyScaleVar θ G_poly)` (`length ≤ d + 1`) bounds the exceptional
     `θ ∈ S` violating `hInvalidMix` by `badTheta + |gsDecodeList d (A - 1) D f| · |gsDecodeList d (A - 1) D g|`
     under symmetric input invalidity (`(f, e_f)` invalid or `(g, e_g)` invalid).
   - Composes with `claimFold_bad_pairs_bound` over all `(θ, (α, β)) ∈ S × prodPool S` (`|S|^3` triples).

2. **Arbitrary-Batch (`1 ≤ m ≤ 16`) Multi-Stage `verifyHemAffineWhir` & Extracted-Opening Bridge
   (`arbitrary_batch_cascade_fiber_bound`, `hem_multistage_extracted_acceptance_and_witness`)**:
   - Generalizes the `m = 1` cascade argument in `HemWhirRbrSoundness`: for any batch arity `m ≥ 1`
     with an invalid coordinate `i₀ < m`, conditioning on any fixed assignment of the `m - 1`
     remaining weight pairs reduces the `i₀`-th slice to `claimFold_bad_pairs_bound` with identical
     error density `(badMca + listF · listG · |S|) / |S|^2`.
   - Composes `HemExtractedOpeningBridge.measured_hem_acceptance_from_extracted` with
     `HemVerifierAcceptance.verifyHemAffineWhir_invalid_coordinate` and `hemAffineWhirStateFunction`
     over arbitrary batch sizes `1 ≤ m ≤ 16` and arbitrary multi-stage `inst.stages`.

3. **State-Restoration & `[CDHZ25]` PoW-Adjusted Salted-Merkle QROM Budgets
   (`cdhz_sliced_stage_clears_128bits_at_2pow50`, `cdhzPqsrPow16_clears_128bits_at_2pow40`)**:
   - Separates linear state-restoration scaling `(Q + 1) · numRounds · b` (`[BCS16; CMS19; CY24]`,
     clearing `128` bits across all `nv ∈ [2, 24]` non-exhaustive sliced stages up to `Q ≤ 2^50`)
     from `[CDHZ25, Thm 6.9]` quadratic Grover post-quantum state restoration combined with the
     deployed `WHIR_FOLD_POW_BITS = 16` joint `(PoW × Challenge)` reduction
     (`23 (Q + 1 + numRounds)^2 · b / 2^16`), clearing `128` bits universally up to
     `Q + 1 + numRounds ≤ 2^33` on `184`-bit stages and up to `Q + 1 + numRounds ≤ 2^40` on all
     `≥ 197`-bit stages alongside the `256`-bit salted-Merkle compressed-oracle collision tail.
-/

public import Qsag.HemSlicedFoldBudget
public import Qsag.HemExtractedOpeningBridge
public import Qsag.HemFoldDecompositionBridge
import all Qsag.HemSlicedFoldBudget
import all Qsag.HemExtractedOpeningBridge
import all Qsag.HemFoldDecompositionBridge
import all Qsag.HemVerifierAcceptance
import all Qsag.HemWhirRbrSoundness
import all Qsag.MultiRoundFsQrom
import all Qsag.ConcreteSecurityBudget
import all Qsag.AffineProximityGaps
import all Qsag.CodingTheory.TrivariateGsExplainer
import all Qsag.CodingTheory.Cwyz26DeployedStages
public import Qsag.Tactic.ConstructiveRing
public import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false
set_option exponentiation.threshold 2048
set_option maxRecDepth 65536

/-! ## §1. Equal-Degree `θ`-Exception Bound & Three-Challenge `(θ, α, β)` Lift -/

/-- Constructive index witness for membership in a `DecidableEq` list. -/
def findListMemIdx {α : Type} [DecidableEq α] (x : α) :
    (ys : List α) → x ∈ ys → { i : Fin ys.length // ys.get i = x }
  | [], h => nomatch h
  | y :: ys, h =>
    if hEq : x = y then
      ⟨⟨0, Nat.zero_lt_succ _⟩, hEq.symm⟩
    else
      have hTail : x ∈ ys := by
        rcases List.mem_cons.mp h with rfl | hm
        · exact False.elim (hEq rfl)
        · exact hm
      let sub := findListMemIdx x ys hTail
      ⟨⟨sub.1.1 + 1, Nat.succ_lt_succ sub.1.2⟩, sub.2⟩

private theorem filter_any_le_mul_one {α β : Type} (items : List α) (pred : α → β → Bool)
    (xs : List β) (hEach : ∀ a ∈ items, (xs.filter (pred a)).length ≤ 1) :
    (xs.filter (fun x => items.any (fun a => pred a x))).length ≤ items.length := by
  have h := filter_any_length_le items pred xs 1 hEach
  rw [Nat.mul_one] at h
  exact h

private theorem linear_theta_fin_le_one {F : Type} [LawfulField F] [DecidableEq F]
    (S : List F) (hS : S.Nodup) (Δ_f Δ_g : F)
    (hNz : Δ_f ≠ CommRingOps.zero ∨ Δ_g ≠ CommRingOps.zero)
    (L : List (Fin S.length)) (hNd : L.Nodup) :
    (L.filter (fun iθ =>
      decide (CommRingOps.add Δ_f (CommRingOps.mul (S.get iθ) Δ_g) = CommRingOps.zero))).length ≤ 1 := by
  generalize hFilt : L.filter (fun iθ =>
    decide (CommRingOps.add Δ_f (CommRingOps.mul (S.get iθ) Δ_g) = CommRingOps.zero)) = fl
  have hFlNd : fl.Nodup := hFilt ▸ List.Pairwise.filter _ hNd
  rcases fl with _ | ⟨i₁, _ | ⟨i₂, _⟩⟩
  · exact Nat.zero_le 1
  · exact Nat.le_refl 1
  · exfalso
    have hMem₁ : i₁ ∈ L.filter (fun iθ =>
        decide (CommRingOps.add Δ_f (CommRingOps.mul (S.get iθ) Δ_g) = CommRingOps.zero)) := by
      rw [hFilt]; exact .head _
    have hMem₂ : i₂ ∈ L.filter (fun iθ =>
        decide (CommRingOps.add Δ_f (CommRingOps.mul (S.get iθ) Δ_g) = CommRingOps.zero)) := by
      rw [hFilt]; exact .tail _ (.head _)
    have e₁ : CommRingOps.add Δ_f (CommRingOps.mul (S.get i₁) Δ_g) = CommRingOps.zero :=
      of_decide_eq_true (List.mem_filter.mp hMem₁).2
    have e₂ : CommRingOps.add Δ_f (CommRingOps.mul (S.get i₂) Δ_g) = CommRingOps.zero :=
      of_decide_eq_true (List.mem_filter.mp hMem₂).2
    have hDiffId : CommRingOps.mul (CommRingOps.sub (S.get i₁) (S.get i₂)) Δ_g =
        CommRingOps.sub
          (CommRingOps.add Δ_f (CommRingOps.mul (S.get i₁) Δ_g))
          (CommRingOps.add Δ_f (CommRingOps.mul (S.get i₂) Δ_g)) := by
      constructive_ring
    have hProd0 : CommRingOps.mul (CommRingOps.sub (S.get i₁) (S.get i₂)) Δ_g = CommRingOps.zero := by
      rw [hDiffId, e₁, e₂, LawfulCommRing.sub_self]
    rcases LawfulField.mul_eq_zero hProd0 with hSub0 | hg0
    · have hIdxEq : i₁ = i₂ := nodup_get_inj hS (LawfulCommRing.sub_eq_zero_iff.mp hSub0)
      exact (List.pairwise_cons.mp hFlNd).1 i₂ (.head _) hIdxEq
    · rw [hg0, LawfulCommRing.mul_zero, LawfulCommRing.add_zero] at e₁
      rcases hNz with hfNe | hgNe
      · exact hfNe e₁
      · exact hgNe hg0

/-- **Equal-Degree `θ`-Mixing Exception Bound (`equal_degree_bad_theta_bound`)**:
    Suppose `0 ∈ S`, `D.Nodup`, `S.Nodup`, `d + 3 ≤ A ≤ D.length`, and `AffineFoldDecompBound D S (d + 1) A badTheta`.
    Whenever EITHER `(f, e_f)` OR `(g, e_g)` has no degree-`≤ d` witness at agreement `≥ A - 1` on `D`,
    at most `badTheta + |gsDecodeList d (A - 1) D f| · |gsDecodeList d (A - 1) D g|` indices `iθ ∈ Fin S.length`
    admit a degree-`≤ d` witness `H` (`H.length ≤ d + 1`) at agreement `≥ A` for `(f + θ g, e_f + θ e_g)`. -/
theorem equal_degree_bad_theta_bound
    (D S kernel : List QuarticGoldilocks) (d A badTheta : Nat)
    (f g : QuarticGoldilocks → QuarticGoldilocks) (e_f e_g : QuarticGoldilocks)
    (hD : D.Nodup) (hS : S.Nodup) (hZeroS : (CommRingOps.zero : QuarticGoldilocks) ∈ S)
    (hdA : d + 3 ≤ A) (hAD : A ≤ D.length)
    (hDecompTheta : AffineFoldDecompBound D S (d + 1) A badTheta)
    (hInvalidFG :
      (∀ Fp : List QuarticGoldilocks, Fp.length ≤ d + 1 →
        A - 1 ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs Fp z = f z))).length →
        ringDot Fp kernel ≠ e_f) ∨
      (∀ Gp : List QuarticGoldilocks, Gp.length ≤ d + 1 →
        A - 1 ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs Gp z = g z))).length →
        ringDot Gp kernel ≠ e_g))
    (L_θ : List (Fin S.length)) (hNd : L_θ.Nodup)
    (hBadθ : ∀ iθ ∈ L_θ, ¬¬ ∃ H : List QuarticGoldilocks,
      H.length ≤ d + 1 ∧
      A ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs H z =
        CommRingOps.add (f z) (CommRingOps.mul (S.get iθ) (g z))))).length ∧
      ringDot H kernel = CommRingOps.add e_f (CommRingOps.mul (S.get iθ) e_g)) :
    L_θ.length ≤ badTheta +
      (gsDecodeList d (A - 1) D f).length * (gsDecodeList d (A - 1) D g).length := by
  let candF := gsDecodeList d (A - 1) D f
  let candG := gsDecodeList d (A - 1) D g
  let pairsFG := candF.flatMap (fun pF => candG.map (fun pG => (pF, pG)))
  have hPairsLen : pairsFG.length = candF.length * candG.length := by
    dsimp only [pairsFG]
    induction candF with
    | nil => simp
    | cons _ rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons, ih]
      rw [Nat.succ_mul, Nat.add_comm]
  let matchTheta : GsUniPoly QuarticGoldilocks × GsUniPoly QuarticGoldilocks → Fin S.length → Bool :=
    fun fg iθ =>
      decide (CommRingOps.add (ringDot fg.1.val kernel)
        (CommRingOps.mul (S.get iθ) (ringDot fg.2.val kernel)) =
        CommRingOps.add e_f (CommRingOps.mul (S.get iθ) e_g))
  let anyMatch : Fin S.length → Bool := fun iθ => pairsFG.any (fun fg => matchTheta fg iθ)
  have hSplit := length_filter_add_not anyMatch L_θ
  have hMatchLe : (L_θ.filter anyMatch).length ≤ pairsFG.length := by
    refine filter_any_le_mul_one pairsFG matchTheta L_θ ?_
    intro fg hfg
    rcases List.mem_flatMap.mp hfg with ⟨pF, hpFMem, hInG⟩
    rcases List.mem_map.mp hInG with ⟨pG, hpGMem, rfl⟩
    have hpFProps := (mem_gsDecodeList_iff f hD (by omega) pF).mp hpFMem
    have hpGProps := (mem_gsDecodeList_iff g hD (by omega) pG).mp hpGMem
    let Δ_f := CommRingOps.sub (ringDot pF.val kernel) e_f
    let Δ_g := CommRingOps.sub (ringDot pG.val kernel) e_g
    have hNz : Δ_f ≠ CommRingOps.zero ∨ Δ_g ≠ CommRingOps.zero := by
      rcases hInvalidFG with invF | invG
      · exact .inl (fun h0 => invF pF.val hpFProps.1 hpFProps.2 (LawfulCommRing.sub_eq_zero_iff.mp h0))
      · exact .inr (fun h0 => invG pG.val hpGProps.1 hpGProps.2 (LawfulCommRing.sub_eq_zero_iff.mp h0))
    have hEqFilt : L_θ.filter (matchTheta (pF, pG)) =
        L_θ.filter (fun iθ => decide (CommRingOps.add Δ_f (CommRingOps.mul (S.get iθ) Δ_g) = CommRingOps.zero)) := by
      apply congrArg (fun q => List.filter q L_θ)
      funext iθ
      dsimp only [matchTheta, Δ_f, Δ_g]
      if hEq : CommRingOps.add (ringDot pF.val kernel)
          (CommRingOps.mul (S.get iθ) (ringDot pG.val kernel)) =
          CommRingOps.add e_f (CommRingOps.mul (S.get iθ) e_g) then
        have h0 : CommRingOps.add (CommRingOps.sub (ringDot pF.val kernel) e_f)
            (CommRingOps.mul (S.get iθ) (CommRingOps.sub (ringDot pG.val kernel) e_g)) = CommRingOps.zero := by
          have hId : CommRingOps.add (CommRingOps.sub (ringDot pF.val kernel) e_f)
              (CommRingOps.mul (S.get iθ) (CommRingOps.sub (ringDot pG.val kernel) e_g)) =
            CommRingOps.sub
              (CommRingOps.add (ringDot pF.val kernel) (CommRingOps.mul (S.get iθ) (ringDot pG.val kernel)))
              (CommRingOps.add e_f (CommRingOps.mul (S.get iθ) e_g)) := by constructive_ring
          rw [hId, hEq, LawfulCommRing.sub_self]
        rw [decide_eq_true hEq, decide_eq_true h0]
      else
        have hNe0 : CommRingOps.add (CommRingOps.sub (ringDot pF.val kernel) e_f)
            (CommRingOps.mul (S.get iθ) (CommRingOps.sub (ringDot pG.val kernel) e_g)) ≠ CommRingOps.zero := by
          intro h0
          apply hEq
          have hId : CommRingOps.sub
              (CommRingOps.add (ringDot pF.val kernel) (CommRingOps.mul (S.get iθ) (ringDot pG.val kernel)))
              (CommRingOps.add e_f (CommRingOps.mul (S.get iθ) e_g)) =
            CommRingOps.add (CommRingOps.sub (ringDot pF.val kernel) e_f)
              (CommRingOps.mul (S.get iθ) (CommRingOps.sub (ringDot pG.val kernel) e_g)) := by constructive_ring
          exact LawfulCommRing.sub_eq_zero_iff.mp (hId.trans h0)
        rw [decide_eq_false hEq, decide_eq_false hNe0]
    rw [hEqFilt]
    exact linear_theta_fin_le_one S hS Δ_f Δ_g hNz L_θ hNd
  -- Embed non-matching `iθ` into `prodPool S` via `iθ ↦ (S.get iθ, 0)`:
  let embedZero : (iθ : Fin S.length) → { ch : Fin (prodPool S).length //
      (prodPool S).get ch = (S.get iθ, CommRingOps.zero) } :=
    fun iθ => findListMemIdx (S.get iθ, CommRingOps.zero) (prodPool S)
      (mem_prodPool_iff.mpr ⟨list_get_mem S iθ, hZeroS⟩)
  let L_non := L_θ.filter (fun iθ => !anyMatch iθ)
  let L_pool := L_non.map (fun iθ => (embedZero iθ).1)
  have hPoolNd : L_pool.Nodup := by
    refine List.Pairwise.map _ ?_ (List.Pairwise.filter _ hNd)
    intro i₁ i₂ hNe hEqIdx
    have hPairEq : (S.get i₁, (CommRingOps.zero : QuarticGoldilocks)) = (S.get i₂, CommRingOps.zero) :=
      (embedZero i₁).2.symm.trans ((congrArg (prodPool S).get hEqIdx).trans (embedZero i₂).2)
    exact hNe (nodup_get_inj hS (Prod.mk.inj hPairEq).1)
  have hNonLe : L_pool.length ≤ badTheta := by
    refine hDecompTheta (f, g) L_pool hPoolNd ?_
    intro ch hch hNo
    rcases List.mem_map.mp hch with ⟨iθ, hiθNon, rfl⟩
    rcases List.mem_filter.mp hiθNon with ⟨hiθL, hNotAny⟩
    have hChEq : (prodPool S).get (embedZero iθ).1 = (S.get iθ, CommRingOps.zero) := (embedZero iθ).2
    refine hBadθ iθ hiθL ?_
    rintro ⟨H, hHLen, hHAg, hHDot⟩
    refine hNo ⟨H, ?_, ?_⟩
    · unfold affineMcaAccepts
      rw [list_getD_eq_get (prodPool S) _ (embedZero iθ).1, hChEq]
      have hPredEq : (fun z => decide (RoundPoly.evalCoeffs H z =
          CommRingOps.add (f z) (CommRingOps.mul
            (CommRingOps.add (S.get iθ) (CommRingOps.mul CommRingOps.zero z)) (g z)))) =
          (fun z => decide (RoundPoly.evalCoeffs H z =
            CommRingOps.add (f z) (CommRingOps.mul (S.get iθ) (g z)))) := by
        funext z
        rw [LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
      rw [hPredEq]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨(embedZero iθ).1.2, Nat.le_trans hHLen (Nat.le_succ _)⟩, hHAg⟩
    · rintro ⟨F_poly, G_poly, ⟨hFLen, hGLen, hJoint⟩, hTrimEq⟩
      rw [hChEq] at hTrimEq
      -- Degree collapse: `F_sub := H - θ * G_poly` has length `≤ d + 1` and agrees everywhere with `F_poly`!
      let F_sub := polySubVar H (polyScaleVar (S.get iθ) G_poly)
      have hScaleLen : (polyScaleVar (S.get iθ) G_poly).length ≤ d + 1 := by
        simp only [polyScaleVar, List.length_map]; exact hGLen
      have hFsubLen : F_sub.length ≤ d + 1 := polySubVar_length_le H _ (d + 1) hHLen hScaleLen
      have hAgreeAll : ∀ z ∈ D, RoundPoly.evalCoeffs F_poly z = RoundPoly.evalCoeffs F_sub z := by
        intro z _
        have hEvH : RoundPoly.evalCoeffs H z =
            CommRingOps.add (RoundPoly.evalCoeffs F_poly z)
              (CommRingOps.mul (S.get iθ) (RoundPoly.evalCoeffs G_poly z)) := by
          rw [← evalCoeffs_trimPoly z H, hTrimEq, evalCoeffs_trimPoly,
              evalCoeffs_polyAddVar, evalCoeffs_polyAddVar,
              evalCoeffs_polyScaleVar, evalCoeffs_polyScaleVar,
              LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
        dsimp only [F_sub]
        rw [evalCoeffs_polySubVar, evalCoeffs_polyScaleVar, hEvH]
        constructive_ring
      have hTrimFEq : trimPoly F_poly = trimPoly F_sub :=
        trimPoly_eq_of_agree_on_nodup (d := d + 1) hFLen
          (Nat.le_trans hFsubLen (Nat.le_succ _)) hD (by omega) hAgreeAll
      let pF : GsUniPoly QuarticGoldilocks := GsUniPoly.ofCoeffs F_poly
      let pG : GsUniPoly QuarticGoldilocks := GsUniPoly.ofCoeffs G_poly
      have hpFLen : pF.val.length ≤ d + 1 := by
        change (trimPoly F_poly).length ≤ d + 1
        rw [hTrimFEq]
        exact Nat.le_trans (trimPoly_length_le F_sub) hFsubLen
      have hJointF : A - 1 ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs pF.val z = f z))).length := by
        refine Nat.le_trans hJoint (nodup_length_le_of_subset (List.Pairwise.filter _ hD) ?_)
        intro z hz
        rcases List.mem_filter.mp hz with ⟨hzD, hB⟩
        refine List.mem_filter.mpr ⟨hzD, decide_eq_true ?_⟩
        change RoundPoly.evalCoeffs (trimPoly F_poly) z = f z
        rw [evalCoeffs_trimPoly]
        exact of_decide_eq_true ((Bool.and_eq_true _ _).mp hB).1
      have hJointG : A - 1 ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs pG.val z = g z))).length := by
        refine Nat.le_trans hJoint (nodup_length_le_of_subset (List.Pairwise.filter _ hD) ?_)
        intro z hz
        rcases List.mem_filter.mp hz with ⟨hzD, hB⟩
        refine List.mem_filter.mpr ⟨hzD, decide_eq_true ?_⟩
        change RoundPoly.evalCoeffs (trimPoly G_poly) z = g z
        rw [evalCoeffs_trimPoly]
        exact of_decide_eq_true ((Bool.and_eq_true _ _).mp hB).2
      have hpFMem : pF ∈ candF :=
        (mem_gsDecodeList_iff f hD (by omega) pF).mpr ⟨hpFLen, hJointF⟩
      have hpGMem : pG ∈ candG :=
        (mem_gsDecodeList_iff g hD (by omega) pG).mpr
          ⟨Nat.le_trans (trimPoly_length_le G_poly) hGLen, hJointG⟩
      have hZeroScale : polyScaleVar (CommRingOps.zero : QuarticGoldilocks) (shiftPoly G_poly) =
          (shiftPoly G_poly).map (fun _ => CommRingOps.zero) := by
        unfold polyScaleVar
        apply List.map_congr_left
        intro a _; exact LawfulCommRing.zero_mul a
      have hDotZero : ringDot (polyScaleVar (CommRingOps.zero : QuarticGoldilocks) (shiftPoly G_poly)) kernel =
          CommRingOps.zero := by
        rw [ringDot_polyScaleVar, LawfulCommRing.zero_mul]
      have hDotEq : CommRingOps.add (ringDot pF.val kernel)
          (CommRingOps.mul (S.get iθ) (ringDot pG.val kernel)) =
          CommRingOps.add e_f (CommRingOps.mul (S.get iθ) e_g) := by
        change CommRingOps.add (ringDot (trimPoly F_poly) kernel)
            (CommRingOps.mul (S.get iθ) (ringDot (trimPoly G_poly) kernel)) = _
        rw [ringDot_trimPoly_eq, ringDot_trimPoly_eq]
        have hDT := congrArg (fun u => ringDot u kernel) hTrimEq
        rw [ringDot_trimPoly_eq, ringDot_trimPoly_eq,
            ringDot_polyAddVar, ringDot_polyAddVar,
            ringDot_polyScaleVar, hDotZero, LawfulCommRing.add_zero] at hDT
        exact hDT.symm.trans hHDot
      have hMemP : (pF, pG) ∈ pairsFG :=
        List.mem_flatMap.mpr ⟨pF, hpFMem, List.mem_map.mpr ⟨pG, hpGMem, rfl⟩⟩
      have hAnyTrue : anyMatch iθ = true :=
        List.any_eq_true.mpr ⟨(pF, pG), hMemP, decide_eq_true hDotEq⟩
      rw [hAnyTrue] at hNotAny
      exact absurd hNotAny (by decide)
  have hLenPool : L_pool.length = L_non.length := List.length_map _
  rw [hLenPool] at hNonLe
  rw [hPairsLen] at hMatchLe
  dsimp only [candF, candG, L_non] at hMatchLe hNonLe
  omega

private theorem nodup_map_snd_filter_fst {α β : Type} [DecidableEq α] (a : α) :
    ∀ (xs : List (α × β)), xs.Nodup →
      ((xs.filter (fun p => decide (p.1 = a))).map Prod.snd).Nodup
  | [], _ => .nil
  | (x, y) :: tl, hNd => by
    obtain ⟨hNotIn, hTlNd⟩ := List.pairwise_cons.mp hNd
    if hx : x = a then
      simp only [List.filter_cons, decide_eq_true hx, ↓reduceIte, List.map_cons]
      refine List.pairwise_cons.mpr ⟨?_, nodup_map_snd_filter_fst a tl hTlNd⟩
      intro y' hy' hEqY
      rcases List.mem_map.mp hy' with ⟨⟨x', y''⟩, hMemF, hSnd⟩
      dsimp only at hSnd
      rcases List.mem_filter.mp hMemF with ⟨hMemTl, hDecX⟩
      have hxEq : x' = x := (of_decide_eq_true hDecX).trans hx.symm
      have hyEq : y'' = y := hSnd.trans hEqY.symm
      rw [hxEq, hyEq] at hMemTl
      exact hNotIn (x, y) hMemTl rfl
    else
      simp only [List.filter_cons, decide_eq_false hx, Bool.false_eq_true, ↓reduceIte]
      exact nodup_map_snd_filter_fst a tl hTlNd

/-- **Full Three-Challenge `(θ, α, β)` Equal-Degree Lift (`equal_degree_three_challenge_bound`)**:
    Eliminates `hInvalidMix` entirely by uniting `equal_degree_bad_theta_bound` (for `θ ∈ S`) with
    `claimFold_bad_pairs_bound` (for `(α, β) ∈ prodPool S` on every non-exceptional `θ`). -/
theorem equal_degree_three_challenge_bound
    (D S kernel : List QuarticGoldilocks) (d A badTheta badAlphaBeta maxMixList : Nat)
    (f g : QuarticGoldilocks → QuarticGoldilocks) (e_f e_g c_f c_g : QuarticGoldilocks)
    (hD : D.Nodup) (hS : S.Nodup) (hZeroS : (CommRingOps.zero : QuarticGoldilocks) ∈ S)
    (hdA : d + 3 ≤ A) (hAD : A ≤ D.length)
    (hDecompTheta : AffineFoldDecompBound D S (d + 1) A badTheta)
    (hDecompAB : AffineFoldDecompBound D S (d + 1) (A + 1) badAlphaBeta)
    (hMixList : ∀ θ : QuarticGoldilocks,
      (gsDecodeList d A D (fun z => CommRingOps.add (f z) (CommRingOps.mul θ (g z)))).length ≤ maxMixList)
    (hInvalidFG :
      (∀ Fp : List QuarticGoldilocks, Fp.length ≤ d + 1 →
        A - 1 ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs Fp z = f z))).length →
        ringDot Fp kernel ≠ e_f) ∨
      (∀ Gp : List QuarticGoldilocks, Gp.length ≤ d + 1 →
        A - 1 ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs Gp z = g z))).length →
        ringDot Gp kernel ≠ e_g))
    (triples : List (Fin S.length × Fin (prodPool S).length)) (hNd : triples.Nodup)
    (hFlip : ∀ tr ∈ triples, ¬¬ ∃ P : List QuarticGoldilocks,
      affineMcaAccepts D S (d + 1) (A + 1)
        (g, fun z => CommRingOps.add (f z) (CommRingOps.mul (S.get tr.1) (g z))) tr.2.1 P = true ∧
      ringDot P kernel = hemFoldClaimUpdate e_f e_g c_f c_g (S.get tr.1)
        ((prodPool S).get tr.2).1 ((prodPool S).get tr.2).2) :
    triples.length ≤
      (badTheta + (gsDecodeList d (A - 1) D f).length * (gsDecodeList d (A - 1) D g).length) *
        (prodPool S).length +
      S.length * (badAlphaBeta + (gsDecodeList (d + 1) A D g).length * maxMixList * S.length) := by
  let isExcTheta : Fin S.length → Bool := fun iθ =>
    let θ := S.get iθ
    let mixWord := fun z => CommRingOps.add (f z) (CommRingOps.mul θ (g z))
    (gsDecodeList d A D mixWord).any (fun pH =>
      decide (ringDot pH.val kernel = CommRingOps.add e_f (CommRingOps.mul θ e_g)))
  let excThetas := (List.finRange S.length).filter isExcTheta
  have hExcBound : excThetas.length ≤
      badTheta + (gsDecodeList d (A - 1) D f).length * (gsDecodeList d (A - 1) D g).length := by
    refine equal_degree_bad_theta_bound D S kernel d A badTheta f g e_f e_g
      hD hS hZeroS hdA hAD hDecompTheta hInvalidFG excThetas
      (List.Pairwise.filter _ (List.nodup_finRange S.length)) ?_
    intro iθ hiθ hNo
    have hAny : isExcTheta iθ = true := (List.mem_filter.mp hiθ).2
    rcases List.any_eq_true.mp hAny with ⟨pH, hpHMem, hpHDot⟩
    have hpHProps := (mem_gsDecodeList_iff _ hD (by omega) pH).mp hpHMem
    exact hNo ⟨pH.val, hpHProps.1, hpHProps.2, of_decide_eq_true hpHDot⟩
  have hSplit := length_filter_add_not (fun tr => isExcTheta tr.1) triples
  have hExcTriples : (triples.filter (fun tr => isExcTheta tr.1)).length ≤
      excThetas.length * (prodPool S).length := by
    let allPool := List.finRange (prodPool S).length
    let box := excThetas.flatMap (fun iθ => allPool.map (fun ch => (iθ, ch)))
    have hBoxLen : box.length = excThetas.length * (prodPool S).length := by
      dsimp only [box]
      have hAP : allPool.length = (prodPool S).length := List.length_finRange
      induction excThetas with
      | nil => simp
      | cons _ tl ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons, ih, hAP]
        rw [Nat.succ_mul, Nat.add_comm]
    rw [← hBoxLen]
    refine nodup_length_le_of_subset (List.Pairwise.filter _ hNd) ?_
    intro tr htr
    rcases List.mem_filter.mp htr with ⟨_, hEx⟩
    exact List.mem_flatMap.mpr ⟨tr.1, List.mem_filter.mpr ⟨List.mem_finRange tr.1, hEx⟩,
      List.mem_map.mpr ⟨tr.2, List.mem_finRange tr.2, rfl⟩⟩
  let goodTriples := triples.filter (fun tr => !isExcTheta tr.1)
  have hGoodPerTheta : ∀ iθ : Fin S.length,
      (goodTriples.filter (fun tr => decide (tr.1 = iθ))).length ≤
        badAlphaBeta + (gsDecodeList (d + 1) A D g).length * maxMixList * S.length := by
    intro iθ
    cases hIsEx : isExcTheta iθ
    · let θ := S.get iθ
      let mixWord := fun z => CommRingOps.add (f z) (CommRingOps.mul θ (g z))
      have hInvMix : ∀ G : List QuarticGoldilocks, G.length ≤ d + 1 →
          A ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs G z = mixWord z))).length →
          ringDot G kernel ≠ CommRingOps.add e_f (CommRingOps.mul θ e_g) := by
        intro G hGLen hGAg hGDot
        let pG : GsUniPoly QuarticGoldilocks := GsUniPoly.ofCoeffs G
        have hpGAg : A ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs pG.val z = mixWord z))).length := by
          have hEqF : D.filter (fun z => decide (RoundPoly.evalCoeffs pG.val z = mixWord z)) =
              D.filter (fun z => decide (RoundPoly.evalCoeffs G z = mixWord z)) :=
            congrArg (fun q => List.filter q D) (funext fun z => by
              show decide (RoundPoly.evalCoeffs (trimPoly G) z = mixWord z) = _
              rw [evalCoeffs_trimPoly])
          rw [hEqF]; exact hGAg
        have hpGMem : pG ∈ gsDecodeList d A D mixWord :=
          (mem_gsDecodeList_iff mixWord hD (by omega) pG).mpr
            ⟨Nat.le_trans (trimPoly_length_le G) hGLen, hpGAg⟩
        have hpGDot : ringDot pG.val kernel = CommRingOps.add e_f (CommRingOps.mul θ e_g) := by
          change ringDot (trimPoly G) kernel = _
          rw [ringDot_trimPoly_eq]; exact hGDot
        have hExTrue : isExcTheta iθ = true :=
          List.any_eq_true.mpr ⟨pG, hpGMem, decide_eq_true hpGDot⟩
        rw [hExTrue] at hIsEx
        exact Bool.noConfusion hIsEx
      let slice := (goodTriples.filter (fun tr => decide (tr.1 = iθ))).map Prod.snd
      have hSliceNd : slice.Nodup :=
        nodup_map_snd_filter_fst iθ goodTriples (List.Pairwise.filter _ hNd)
      have hSliceBound := claimFold_bad_pairs_bound D S kernel d A badAlphaBeta
        g mixWord e_g (CommRingOps.add e_f (CommRingOps.mul θ e_g))
        (CommRingOps.add c_f (CommRingOps.mul θ c_g))
        hD hS (Nat.le_of_succ_le hdA) hDecompAB hInvMix slice hSliceNd
        (fun ch hch hNo => by
          rcases List.mem_map.mp hch with ⟨tr, htrF, rfl⟩
          rcases List.mem_filter.mp htrF with ⟨htrGood, hTr1⟩
          have hTrMem : tr ∈ triples := (List.mem_filter.mp htrGood).1
          have hEq1 : tr.1 = iθ := of_decide_eq_true hTr1
          refine hFlip tr hTrMem (fun ⟨P, hPAcc, hPDot⟩ => hNo ⟨P, ?_, ?_⟩)
          · rw [hEq1] at hPAcc; exact hPAcc
          · rw [hEq1] at hPDot; rw [hPDot]; unfold hemFoldClaimUpdate; constructive_ring)
      have hLenEq : slice.length = (goodTriples.filter (fun tr => decide (tr.1 = iθ))).length :=
        List.length_map _
      rw [hLenEq] at hSliceBound
      have hMixLe := hMixList θ
      have hTermLe : (gsDecodeList (d + 1) A D g).length * (gsDecodeList d A D mixWord).length * S.length ≤
          (gsDecodeList (d + 1) A D g).length * maxMixList * S.length :=
        Nat.mul_le_mul_right S.length (Nat.mul_le_mul_left _ hMixLe)
      exact Nat.le_trans hSliceBound (Nat.add_le_add_left hTermLe badAlphaBeta)
    · have hEmpty : goodTriples.filter (fun tr => decide (tr.1 = iθ)) = [] := by
        have hAux : ∀ xs : List (Fin S.length × Fin (prodPool S).length),
            (∀ t ∈ xs, !isExcTheta t.1 = true) →
            xs.filter (fun tr => decide (tr.1 = iθ)) = [] := by
          intro xs hAll; induction xs with
          | nil => rfl
          | cons hd tl ih =>
            have hHd := hAll hd (.head tl)
            if hE : hd.1 = iθ then
              rw [hE, hIsEx] at hHd; cases hHd
            else
              simp only [List.filter_cons, decide_eq_false hE, Bool.false_eq_true, ↓reduceIte]
              exact ih (fun u hu => hAll u (.tail hd hu))
        exact hAux goodTriples (fun t ht => (List.mem_filter.mp ht).2)
      rw [hEmpty]; exact Nat.zero_le _
  have hGoodCover : goodTriples =
      goodTriples.filter (fun tr => (List.finRange S.length).any (fun iθ => decide (tr.1 = iθ))) := by
    have hAllTrue : ∀ xs : List (Fin S.length × Fin (prodPool S).length),
        xs = xs.filter (fun tr => (List.finRange S.length).any (fun iθ => decide (tr.1 = iθ))) := by
      intro xs; induction xs with
      | nil => rfl
      | cons hd tl ih =>
        have hAny : (List.finRange S.length).any (fun iθ => decide (hd.1 = iθ)) = true :=
          List.any_eq_true.mpr ⟨hd.1, List.mem_finRange hd.1, decide_eq_true rfl⟩
        simp only [List.filter_cons, hAny, ↓reduceIte]
        exact congrArg (hd :: ·) ih
    exact hAllTrue goodTriples
  have hGoodTotal : goodTriples.length ≤
      S.length * (badAlphaBeta + (gsDecodeList (d + 1) A D g).length * maxMixList * S.length) := by
    have hF := filter_any_length_le (List.finRange S.length)
      (fun iθ (tr : Fin S.length × Fin (prodPool S).length) => decide (tr.1 = iθ))
      goodTriples
      (badAlphaBeta + (gsDecodeList (d + 1) A D g).length * maxMixList * S.length)
      (fun iθ _ => hGoodPerTheta iθ)
    rw [← hGoodCover, List.length_finRange] at hF
    exact hF
  have hExcProd : (triples.filter (fun tr => isExcTheta tr.1)).length ≤
      (badTheta + (gsDecodeList d (A - 1) D f).length * (gsDecodeList d (A - 1) D g).length) *
        (prodPool S).length :=
    Nat.le_trans hExcTriples (Nat.mul_le_mul_right (prodPool S).length hExcBound)
  dsimp only [goodTriples] at hGoodTotal
  omega

/-- Specialization of `equal_degree_three_challenge_bound` to `slicedParamsOk` certificates at
    agreement thresholds `A` (for the `θ`-exception slice) and `A + 1` (for the `(α, β)` fold). -/
theorem sliced_equal_degree_three_challenge_bound
    (D S kernel : List QuarticGoldilocks)
    (d A B₀ m₀ Dy₀ B₁ m₁ Dy₁ maxMixList : Nat)
    (f g : QuarticGoldilocks → QuarticGoldilocks) (e_f e_g c_f c_g : QuarticGoldilocks)
    (hD : D.Nodup) (hS : S.Nodup) (hZeroS : (CommRingOps.zero : QuarticGoldilocks) ∈ S)
    (hdA : d + 3 ≤ A) (hAD : A ≤ D.length)
    (hParamsTheta : slicedParamsOk D.length (d + 1) A B₀ m₀ Dy₀ = true)
    (hParamsAB : slicedParamsOk D.length (d + 1) (A + 1) B₁ m₁ Dy₁ = true)
    (hMixList : ∀ θ : QuarticGoldilocks,
      (gsDecodeList d A D (fun z => CommRingOps.add (f z) (CommRingOps.mul θ (g z)))).length ≤ maxMixList)
    (hInvalidFG :
      (∀ Fp : List QuarticGoldilocks, Fp.length ≤ d + 1 →
        A - 1 ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs Fp z = f z))).length →
        ringDot Fp kernel ≠ e_f) ∨
      (∀ Gp : List QuarticGoldilocks, Gp.length ≤ d + 1 →
        A - 1 ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs Gp z = g z))).length →
        ringDot Gp kernel ≠ e_g))
    (triples : List (Fin S.length × Fin (prodPool S).length)) (hNd : triples.Nodup)
    (hFlip : ∀ tr ∈ triples, ¬¬ ∃ P : List QuarticGoldilocks,
      affineMcaAccepts D S (d + 1) (A + 1)
        (g, fun z => CommRingOps.add (f z) (CommRingOps.mul (S.get tr.1) (g z))) tr.2.1 P = true ∧
      ringDot P kernel = hemFoldClaimUpdate e_f e_g c_f c_g (S.get tr.1)
        ((prodPool S).get tr.2).1 ((prodPool S).get tr.2).2) :
    let badTheta := Dy₀ + slicedRest D.length (d + 1) A B₀ (m₀ * A - Dy₀) Dy₀ S.length
    let badAB := Dy₁ + slicedRest D.length (d + 1) (A + 1) B₁ (m₁ * (A + 1) - Dy₁) Dy₁ S.length
    triples.length ≤
      (badTheta + (gsDecodeList d (A - 1) D f).length * (gsDecodeList d (A - 1) D g).length) *
        (prodPool S).length +
      S.length * (badAB + (gsDecodeList (d + 1) A D g).length * maxMixList * S.length) :=
  equal_degree_three_challenge_bound D S kernel d A _ _ maxMixList f g e_f e_g c_f c_g
    hD hS hZeroS hdA hAD
    (slicedParamsOk_sound D.length (d + 1) A B₀ m₀ Dy₀ hParamsTheta D S hD hS rfl)
    (slicedParamsOk_sound D.length (d + 1) (A + 1) B₁ m₁ Dy₁ hParamsAB D S hD hS rfl)
    hMixList hInvalidFG triples hNd hFlip

def qgNat : Nat → QuarticGoldilocks
  | 0 => CommRingOps.zero
  | n + 1 => CommRingOps.add (qgNat n) CommRingOps.one

def toothDeg1Dom : List QuarticGoldilocks :=
  [qgNat 0, qgNat 1, qgNat 2, qgNat 3]

def toothDeg1Pool : List QuarticGoldilocks :=
  [qgNat 0, qgNat 1, CommRingOps.sub CommRingOps.zero CommRingOps.one]

/-- **Equal-Degree `θ`-Exception Necessity Counterexample (`tooth_equal_degree_drop_theta_exception_unsound`)**:
    Let `D = [0, 1, 2, 3]`, `S = [0, 1, -1]`, `d = 0, A = 3`, `f(z) = z`, `g(z) = z`, and all claims `0`.
    Neither `(f, 0)` nor `(g, 0)` admits any degree-`≤ 0` witness at agreement `≥ A - 1 = 2`
    (`gsDecodeList 0 2 D id = []`). Yet at `θ = -1` (`iθ = 2`), `f + θ g = 0` and **all**
    `|prodPool S| = 9 = |S|^2` pairs `(α, β)` accept `P(X) = X` (`deg 1 ≤ d + 1`), proving that
    the `(badTheta + ...) · |prodPool S|` term in `equal_degree_three_challenge_bound` cannot be omitted. -/
theorem tooth_equal_degree_drop_theta_exception_unsound :
    ∃ iθ : Fin toothDeg1Pool.length,
      (gsDecodeList 0 2 toothDeg1Dom (fun z => z)).length = 0 ∧
      (∀ Fp : List QuarticGoldilocks, Fp.length ≤ 1 →
        2 ≤ (toothDeg1Dom.filter (fun z => decide (RoundPoly.evalCoeffs Fp z = z))).length → False) ∧
      (prodPool toothDeg1Pool).length = 9 ∧
      ∀ ch : Fin (prodPool toothDeg1Pool).length,
        affineMcaAccepts toothDeg1Dom toothDeg1Pool 1 4
          ((fun z => z),
           fun z => CommRingOps.add z (CommRingOps.mul (toothDeg1Pool.get iθ) z))
          ch.1 [qgNat 0, qgNat 1] = true ∧
        ringDot [qgNat 0, qgNat 1] [qgNat 1] =
          hemFoldClaimUpdate (qgNat 0) (qgNat 0) (qgNat 0) (qgNat 0)
            (toothDeg1Pool.get iθ)
            ((prodPool toothDeg1Pool).get ch).1 ((prodPool toothDeg1Pool).get ch).2 := by
  have hEmpty : gsDecodeList 0 2 toothDeg1Dom (fun z => z) = [] := by decide +kernel
  have hD : toothDeg1Dom.Nodup := by decide +kernel
  refine ⟨⟨2, by decide⟩, by rw [hEmpty]; rfl, ?_, by decide +kernel, by decide +kernel⟩
  intro Fp hLen hAg
  let pF : GsUniPoly QuarticGoldilocks := GsUniPoly.ofCoeffs Fp
  have hpAg : 2 ≤ (toothDeg1Dom.filter (fun z => decide (RoundPoly.evalCoeffs pF.val z = z))).length := by
    have hEq : toothDeg1Dom.filter (fun z => decide (RoundPoly.evalCoeffs pF.val z = z)) =
        toothDeg1Dom.filter (fun z => decide (RoundPoly.evalCoeffs Fp z = z)) :=
      congrArg (fun q => List.filter q toothDeg1Dom) (funext fun z => by
        show decide (RoundPoly.evalCoeffs (trimPoly Fp) z = z) = _
        rw [evalCoeffs_trimPoly])
    rw [hEq]; exact hAg
  have hpMem : pF ∈ gsDecodeList 0 2 toothDeg1Dom (fun z => z) :=
    (mem_gsDecodeList_iff (fun z => z) hD (by decide) pF).mpr
      ⟨Nat.le_trans (trimPoly_length_le Fp) hLen, hpAg⟩
  rw [hEmpty] at hpMem
  cases hpMem

/-! ## §2. Arbitrary-Batch (`1 ≤ m ≤ 16`) Multi-Stage `verifyHemAffineWhir` & Extracted-Opening Bridge -/

private theorem evalCascadeClaim_set_split :
    ∀ (es shifts : List QuarticGoldilocks)
      (ws : List (QuarticGoldilocks × QuarticGoldilocks))
      (i : Nat) (p : QuarticGoldilocks × QuarticGoldilocks),
      i < es.length → es.length = shifts.length → shifts.length = ws.length →
      evalCascadeClaim es shifts (ws.set i p) =
        CommRingOps.add
          (evalCascadeClaim es shifts (ws.set i (CommRingOps.zero, CommRingOps.zero)))
          (CommRingOps.add
            (CommRingOps.mul p.1 (es.getD i CommRingOps.zero))
            (CommRingOps.mul p.2 (shifts.getD i CommRingOps.zero)))
  | [], _, _, _, _, hi, _, _ => nomatch hi
  | _ :: _, [], _, _, _, _, hES, _ => nomatch hES
  | _ :: _, _ :: _, [], _, _, _, _, hSW => nomatch hSW
  | e :: es, s :: shifts, _ :: ws, 0, (α, β), _, _, _ => by
    simp only [List.set_cons_zero, evalCascadeClaim, List.getD, List.getElem?_cons_zero, Option.getD_some]
    constructive_ring
  | e :: es, s :: shifts, w :: ws, i + 1, p, hi, hES, hSW => by
    rcases w with ⟨α₀, β₀⟩
    have ih := evalCascadeClaim_set_split es shifts ws i p
      (Nat.lt_of_succ_lt_succ hi) (Nat.succ.inj hES) (Nat.succ.inj hSW)
    simp only [List.set_cons_succ, evalCascadeClaim, List.getD, List.getElem?_cons_succ] at ih ⊢
    rw [ih]
    constructive_ring

private theorem evalCascadeOracle_set_split (domPts : List QuarticGoldilocks) :
    ∀ (os : List (Nat → QuarticGoldilocks))
      (ws : List (QuarticGoldilocks × QuarticGoldilocks))
      (i idx : Nat) (p : QuarticGoldilocks × QuarticGoldilocks),
      i < os.length → os.length = ws.length →
      evalCascadeOracle domPts os (ws.set i p) idx =
        CommRingOps.add
          (evalCascadeOracle domPts os (ws.set i (CommRingOps.zero, CommRingOps.zero)) idx)
          (CommRingOps.mul
            (CommRingOps.add p.1 (CommRingOps.mul p.2 (domPts.getD idx CommRingOps.zero)))
            ((os.getD i (fun _ => CommRingOps.zero)) idx))
  | [], _, _, _, _, hi, _ => nomatch hi
  | _ :: _, [], _, _, _, _, hOW => nomatch hOW
  | O :: os, _ :: ws, 0, idx, (α, β), _, _ => by
    simp only [List.set_cons_zero, evalCascadeOracle, List.getD, List.getElem?_cons_zero, Option.getD_some]
    constructive_ring
  | O :: os, w :: ws, i + 1, idx, p, hi, hOW => by
    rcases w with ⟨α₀, β₀⟩
    have ih := evalCascadeOracle_set_split domPts os ws i idx p
      (Nat.lt_of_succ_lt_succ hi) (Nat.succ.inj hOW)
    simp only [List.set_cons_succ, evalCascadeOracle]
    have hGet : (O :: os).getD (i + 1) (fun _ => CommRingOps.zero) =
        os.getD i (fun _ => CommRingOps.zero) := by
      simp only [List.getD, List.getElem?_cons_succ]
    rw [ih, hGet]
    constructive_ring

private theorem lookupDomOracle_evalCascadeOracle_set
    (domPts : List QuarticGoldilocks) (hDom : domPts.Nodup)
    (os : List (Nat → QuarticGoldilocks))
    (ws : List (QuarticGoldilocks × QuarticGoldilocks))
    (i : Nat) (p : QuarticGoldilocks × QuarticGoldilocks)
    (hi : i < os.length) (hOW : os.length = ws.length)
    (z : QuarticGoldilocks) (hz : z ∈ domPts) :
    lookupDomOracle domPts (evalCascadeOracle domPts os (ws.set i p)) z =
      CommRingOps.add
        (lookupDomOracle domPts
          (evalCascadeOracle domPts os (ws.set i (CommRingOps.zero, CommRingOps.zero))) z)
        (CommRingOps.mul
          (CommRingOps.add p.1 (CommRingOps.mul p.2 z))
          (lookupDomOracle domPts (os.getD i (fun _ => CommRingOps.zero)) z)) := by
  let ⟨idx, hIdxEq⟩ := findListMemIdx z domPts hz
  rw [← hIdxEq,
      lookupDomOracle_get domPts _ hDom idx,
      lookupDomOracle_get domPts _ hDom idx,
      lookupDomOracle_get domPts _ hDom idx,
      evalCascadeOracle_set_split domPts os ws i idx.1 p hi hOW,
      list_getD_eq_get domPts CommRingOps.zero idx]

/-- **Arbitrary-Batch (`1 ≤ m ≤ 16`), Multi-Stage `verifyHemAffineWhir` Cascade Fiber Bound
    (`arbitrary_batch_cascade_fiber_bound`)**:
    For ANY `inst : HemWhirInstance QuarticGoldilocks` with `1 ≤ m ≤ 16` batch oracles, ANY stage
    schedule `inst.stages`, `inst.initDomainPts.Nodup`, `inst.initDegBound + 3 ≤ inst.initMinAgree`,
    and `¬ HemStatementValid { inst with initMinAgree := inst.initMinAgree - 1 }` (accounting for
    `verifyHemAffineWhir`'s unincremented `initMinAgree` at `.cascade`), constructively extracts an
    invalid coordinate `i₀ < m` such that for ANY fixed `m - 1` sibling weights (`baseWeights`) and
    ANY adaptive continuation `(decoded, rest)`, at most `badMca + listRest · listTarget · |S|`
    challenge pairs `ch ∈ L` pass `verifyHemAffineWhir`. -/
theorem arbitrary_batch_cascade_fiber_bound
    (inst : HemWhirInstance QuarticGoldilocks)
    (S : List QuarticGoldilocks) (badMca : Nat)
    (shifts : List QuarticGoldilocks)
    (baseWeights : List (QuarticGoldilocks × QuarticGoldilocks))
    (hShape : 1 ≤ inst.batchOracles.length ∧ inst.batchOracles.length ≤ 16)
    (hArity : inst.batchClaims.length = inst.batchOracles.length)
    (hShifts : shifts.length = inst.batchClaims.length)
    (hWeights : baseWeights.length = inst.batchClaims.length)
    (hDom : inst.initDomainPts.Nodup) (hS : S.Nodup)
    (hEnough : inst.initDegBound + 3 ≤ inst.initMinAgree)
    (hDecomp : AffineFoldDecompBound inst.initDomainPts S
      (inst.initDegBound + 1) inst.initMinAgree badMca)
    (hInvalid : ¬ HemStatementValid { inst with initMinAgree := inst.initMinAgree - 1 }) :
    ∃ i₀ : Nat, i₀ < inst.batchOracles.length ∧
      ∀ (decoded : QuarticGoldilocks × QuarticGoldilocks → List (List QuarticGoldilocks))
        (rest : QuarticGoldilocks × QuarticGoldilocks → List (HemTranscriptRound QuarticGoldilocks))
        (L : List (Fin (prodPool S).length)),
        L.Nodup →
        (∀ ch ∈ L, verifyHemAffineWhir inst
          (.cascade shifts (baseWeights.set i₀ ((prodPool S).get ch))
            (decoded ((prodPool S).get ch)) :: rest ((prodPool S).get ch)) = true) →
        L.length ≤ badMca +
          (gsDecodeList (inst.initDegBound + 1) (inst.initMinAgree - 1) inst.initDomainPts
            (lookupDomOracle inst.initDomainPts
              (evalCascadeOracle inst.initDomainPts inst.batchOracles
                (baseWeights.set i₀ (CommRingOps.zero, CommRingOps.zero))))).length *
          (gsDecodeList inst.initDegBound (inst.initMinAgree - 1) inst.initDomainPts
            (lookupDomOracle inst.initDomainPts
              (inst.batchOracles.getD i₀ (fun _ => CommRingOps.zero)))).length *
          S.length := by
  have hNotBatch : ¬ HemBatchValid inst.initDomainPts (inst.initMinAgree - 1) inst.initDegBound
      inst.initKernel inst.batchOracles inst.batchClaims :=
    fun hb => hInvalid ⟨hShape, hb⟩
  obtain ⟨i₀, _, hi₀Lt, hi₀Inv⟩ := findInvalidBatchIdx_complete inst.initDomainPts
    (inst.initMinAgree - 1) inst.initDegBound inst.initKernel hDom (by omega)
    inst.batchOracles inst.batchClaims hArity.symm hNotBatch
  refine ⟨i₀, hi₀Lt, ?_⟩
  intro decoded rest L hNd hAcc
  let domPts := inst.initDomainPts
  let d₀ := inst.initDegBound
  let A₀ := inst.initMinAgree
  have hA : (A₀ - 1) + 1 = A₀ := by omega
  have hOW : inst.batchOracles.length = baseWeights.length := hArity.symm.trans hWeights.symm
  have hi₀Claims : i₀ < inst.batchClaims.length := hArity.symm ▸ hi₀Lt
  let restOracle := evalCascadeOracle domPts inst.batchOracles
    (baseWeights.set i₀ (CommRingOps.zero, CommRingOps.zero))
  let fWord := lookupDomOracle domPts restOracle
  let O_target := inst.batchOracles.getD i₀ (fun _ => CommRingOps.zero)
  let gWord := lookupDomOracle domPts O_target
  let e_f := evalCascadeClaim inst.batchClaims shifts
    (baseWeights.set i₀ (CommRingOps.zero, CommRingOps.zero))
  let e_g := inst.batchClaims.getD i₀ CommRingOps.zero
  let s_g := shifts.getD i₀ CommRingOps.zero
  have hInvalidG : ∀ G : List QuarticGoldilocks, G.length ≤ d₀ + 1 →
      A₀ - 1 ≤ (domPts.filter (fun z => decide (RoundPoly.evalCoeffs G z = gWord z))).length →
      ringDot G inst.initKernel ≠ e_g := by
    intro G hGLen hGAg hGDot
    have hVal : polyWitnessValid domPts (A₀ - 1) d₀ O_target inst.initKernel e_g G = true := by
      unfold polyWitnessValid
      rw [hemCosetAgreeCount_eq_filter_lookup domPts O_target G hDom]
      dsimp only [gWord] at hGAg
      rw [decide_eq_true hGLen, decide_eq_true hGAg, decide_eq_true hGDot]
      rfl
    rw [hi₀Inv G] at hVal
    exact Bool.noConfusion hVal
  have hDecompPrev : AffineFoldDecompBound domPts S (d₀ + 1) ((A₀ - 1) + 1) badMca :=
    hA.symm ▸ hDecomp
  refine claimFold_bad_pairs_bound domPts S inst.initKernel d₀ (A₀ - 1) badMca
    fWord gWord e_f e_g s_g hDom hS (by omega) hDecompPrev hInvalidG L hNd ?_
  intro ch hch hNo
  obtain ⟨_, _, _, P, _, hPV⟩ :=
    verifyHemAffineWhir_cascade_witness inst shifts
      (baseWeights.set i₀ ((prodPool S).get ch))
      (decoded ((prodPool S).get ch)) (rest ((prodPool S).get ch)) (hAcc ch hch)
  unfold polyWitnessValid at hPV
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hPV
  rcases hPV with ⟨⟨hPLen, hPAg⟩, hPDot⟩
  rw [hemCosetAgreeCount_eq_filter_lookup domPts _ P hDom] at hPAg
  refine hNo ⟨P, ?_, ?_⟩
  · unfold affineMcaAccepts
    rw [list_getD_eq_get (prodPool S) _ ch, hA]
    dsimp only [domPts, d₀, A₀, fWord, gWord, restOracle, O_target] at hPLen hPAg ⊢
    have hEqFilt : inst.initDomainPts.filter (fun z =>
        decide (RoundPoly.evalCoeffs P z =
          CommRingOps.add
            (lookupDomOracle inst.initDomainPts
              (evalCascadeOracle inst.initDomainPts inst.batchOracles
                (baseWeights.set i₀ (CommRingOps.zero, CommRingOps.zero))) z)
            (CommRingOps.mul (CommRingOps.add ((prodPool S).get ch).1
              (CommRingOps.mul ((prodPool S).get ch).2 z))
              (lookupDomOracle inst.initDomainPts
                (inst.batchOracles.getD i₀ (fun _ => CommRingOps.zero)) z)))) =
        inst.initDomainPts.filter (fun z =>
          decide (RoundPoly.evalCoeffs P z =
            lookupDomOracle inst.initDomainPts
              (evalCascadeOracle inst.initDomainPts inst.batchOracles
                (baseWeights.set i₀ ((prodPool S).get ch))) z)) := by
      have hMemCongr : ∀ xs : List QuarticGoldilocks, (∀ z ∈ xs, z ∈ inst.initDomainPts) →
          xs.filter (fun z =>
            decide (RoundPoly.evalCoeffs P z =
              CommRingOps.add
                (lookupDomOracle inst.initDomainPts
                  (evalCascadeOracle inst.initDomainPts inst.batchOracles
                    (baseWeights.set i₀ (CommRingOps.zero, CommRingOps.zero))) z)
                (CommRingOps.mul (CommRingOps.add ((prodPool S).get ch).1
                  (CommRingOps.mul ((prodPool S).get ch).2 z))
                  (lookupDomOracle inst.initDomainPts
                    (inst.batchOracles.getD i₀ (fun _ => CommRingOps.zero)) z)))) =
          xs.filter (fun z =>
            decide (RoundPoly.evalCoeffs P z =
              lookupDomOracle inst.initDomainPts
                (evalCascadeOracle inst.initDomainPts inst.batchOracles
                  (baseWeights.set i₀ ((prodPool S).get ch))) z)) := by
        intro xs hSub; induction xs with
        | nil => rfl
        | cons z zs ih =>
          have hValEq := lookupDomOracle_evalCascadeOracle_set inst.initDomainPts hDom
            inst.batchOracles baseWeights i₀ ((prodPool S).get ch)
            hi₀Lt hOW z (hSub z (.head zs))
          simp only [List.filter_cons, hValEq, ih (fun y hy => hSub y (.tail z hy))]
      exact hMemCongr inst.initDomainPts (fun _ h => h)
    rw [hEqFilt, decide_eq_true ch.2, decide_eq_true hPLen, decide_eq_true hPAg]
    rfl
  · rw [hPDot, evalCascadeClaim_set_split inst.batchClaims shifts baseWeights
      i₀ ((prodPool S).get ch) hi₀Claims hShifts.symm (hShifts.trans hWeights.symm)]

/-- **Unincremented Cascade Agreement Counterexample
    (`tooth_verifyHemAffineWhir_unincremented_agree_accepts_all`)**:
    In `MultiRoundFsQrom.verifyHemAffineWhir`, `.cascade` checks `polyWitnessValid` at
    `inst.initMinAgree` (`A₀`) rather than `A₀ + 1`. At `domPts = [0, 1, 2]`, `d₀ = 0`, `A₀ = 2`,
    the oracle `0 ↦ 1, _ ↦ 0` with claim `1` violates `HemStatementValid inst` at `A₀ = 2`, yet
    has an `(A₀ - 1) = 1`-agreeing witness `G = [1]` and therefore passes `verifyHemAffineWhir`
    via `P(z) = α - α z` on **every** `(α, β) ∈ prodPool S` (`100%` acceptance)!
    This proves that the `initMinAgree - 1` premise in `arbitrary_batch_cascade_fiber_bound`
    cannot be weakened to `¬ HemStatementValid inst` unless `verifyHemAffineWhir` increments
    agreement by `+1` at `.cascade`. -/
def toothUnincCascadeInst : HemWhirInstance QuarticGoldilocks :=
  { batchOracles := [fun idx => if idx = 0 then qgNat 1 else qgNat 0]
    batchClaims := [qgNat 1]
    initDomainPts := [qgNat 0, qgNat 1, qgNat 2]
    initDegBound := 0
    initMinAgree := 2
    initKernel := [qgNat 1]
    stages := [] }

theorem tooth_verifyHemAffineWhir_unincremented_agree_accepts_all :
    ∃ inst : HemWhirInstance QuarticGoldilocks,
      ¬ HemStatementValid inst ∧
      HemStatementValid { inst with initMinAgree := 1 } ∧
      ∀ ch : Fin (prodPool toothDeg1Pool).length,
        let p := (prodPool toothDeg1Pool).get ch
        let P : List QuarticGoldilocks := [p.1, CommRingOps.sub CommRingOps.zero p.1]
        verifyHemAffineWhir inst
          [.cascade [qgNat 0] [p] [P], .finalQuery P] = true := by
  refine ⟨toothUnincCascadeInst, ?_, ⟨by decide, ⟨[qgNat 1], by decide +kernel⟩, trivial⟩, by decide +kernel⟩
  rintro ⟨_, ⟨G, hG⟩, _⟩
  unfold polyWitnessValid toothUnincCascadeInst at hG
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hG
  rcases hG with ⟨⟨hGLen, hGAg⟩, hGDot⟩
  rcases G with _ | ⟨c, _ | _⟩
  · change CommRingOps.zero = qgNat 1 at hGDot
    exact (by decide : CommRingOps.zero ≠ qgNat 1) hGDot
  · have hOne : qgNat 1 = CommRingOps.one := by decide
    have hc1 : c = CommRingOps.one := by
      rw [hOne] at hGDot
      simpa only [ringDot, LawfulCommRing.mul_one, LawfulCommRing.add_zero] using hGDot
    subst hc1
    exact absurd hGAg (by decide +kernel)
  · simp only [List.length_cons] at hGLen
    omega

/-- **Multi-Stage Authenticated Opening Substitution + Cascade Fiber Bridge
    (`hem_multistage_extracted_acceptance_and_fiber_bound`)**:
    Composes `HemExtractedOpeningBridge.measured_hem_acceptance_from_extracted` (bounding
    authenticated `verifyHemOpeningBatch` acceptance by extracted-opening `verifyHemAffineWhir`
    acceptance plus `batchMerkleCost Q slots`) with `arbitrary_batch_cascade_fiber_bound` over
    arbitrary `1 ≤ m ≤ 16` batch arities and arbitrary `inst.stages`. -/
theorem hem_multistage_extracted_acceptance_and_fiber_bound
    {cardX w cardAnc Q : Nat}
    (A : QuantumAdv cardX w cardAnc Q) (L_merkle : MerkleAddressLayout cardX w)
    (slots : List (MerkleOpeningSlot cardX w))
    (hLevels : ∀ s ∈ slots, s.level + s.depth ≤ L_merkle.levels)
    (inst : HemWhirInstance QuarticGoldilocks)
    (decode : Fin cardX → List (Option (MerkleOpeningValue w)) →
      List (HemTranscriptRound QuarticGoldilocks))
    (S : List QuarticGoldilocks) (badMca : Nat)
    (shifts : List QuarticGoldilocks)
    (baseWeights : List (QuarticGoldilocks × QuarticGoldilocks))
    (hShape : 1 ≤ inst.batchOracles.length ∧ inst.batchOracles.length ≤ 16)
    (hArity : inst.batchClaims.length = inst.batchOracles.length)
    (hShifts : shifts.length = inst.batchClaims.length)
    (hWeights : baseWeights.length = inst.batchClaims.length)
    (hDom : inst.initDomainPts.Nodup) (hS : S.Nodup)
    (hEnough : inst.initDegBound + 3 ≤ inst.initMinAgree)
    (hDecomp : AffineFoldDecompBound inst.initDomainPts S
      (inst.initDegBound + 1) inst.initMinAgree badMca)
    (hInvalid : ¬ HemStatementValid { inst with initMinAgree := inst.initMinAgree - 1 }) :
    (2 ^ w * measuredEventMass A (fun H _ x => verifyHemOpeningBatch L_merkle slots inst decode H x) ≤
      2 ^ w * measuredEventMass A (fun H xs x =>
        verifyHemAffineWhir inst (decode x (extractedOpeningValues L_merkle slots H xs x))) +
      batchMerkleCost Q slots * quantumExperimentTotal A) ∧
    ∃ i₀ : Nat, i₀ < inst.batchOracles.length ∧
      ∀ (decoded : QuarticGoldilocks × QuarticGoldilocks → List (List QuarticGoldilocks))
        (rest : QuarticGoldilocks × QuarticGoldilocks → List (HemTranscriptRound QuarticGoldilocks))
        (L_ch : List (Fin (prodPool S).length)),
        L_ch.Nodup →
        (∀ ch ∈ L_ch, verifyHemAffineWhir inst
          (.cascade shifts (baseWeights.set i₀ ((prodPool S).get ch))
            (decoded ((prodPool S).get ch)) :: rest ((prodPool S).get ch)) = true) →
        L_ch.length ≤ badMca +
          (gsDecodeList (inst.initDegBound + 1) (inst.initMinAgree - 1) inst.initDomainPts
            (lookupDomOracle inst.initDomainPts
              (evalCascadeOracle inst.initDomainPts inst.batchOracles
                (baseWeights.set i₀ (CommRingOps.zero, CommRingOps.zero))))).length *
          (gsDecodeList inst.initDegBound (inst.initMinAgree - 1) inst.initDomainPts
            (lookupDomOracle inst.initDomainPts
              (inst.batchOracles.getD i₀ (fun _ => CommRingOps.zero)))).length *
          S.length :=
  ⟨measured_hem_acceptance_from_extracted A L_merkle slots hLevels inst decode,
   arbitrary_batch_cascade_fiber_bound inst S badMca shifts baseWeights
     hShape hArity hShifts hWeights hDom hS hEnough hDecomp hInvalid⟩

/-! ## §3. State-Restoration & `[CDHZ25]` PoW-Adjusted Salted-Merkle QROM Budgets -/

/-- Linear state-restoration Fiat–Shamir scaling `(Q + 1) · numRounds · b` (`[BCS16; CMS19; CY24]`). -/
def cdhzStateRestorationScale (Q numRounds : Nat) (b : RatBound) : RatBound :=
  ⟨(Q + 1) * numRounds * b.num, b.den, b.h_pos⟩

/-- Quadratic QROM post-quantum state-restoration scaling (`[CDHZ25, Thm 6.9]`, `8 e < 23`)
    combined with joint `powBits`-bit Fiat–Shamir grinding (`WHIR_FOLD_POW_BITS = 16`). -/
def cdhzPqsrPowScale (Q numRounds powBits : Nat) (b : RatBound) : RatBound :=
  ⟨23 * (Q + 1 + numRounds) ^ 2 * b.num, b.den * 2 ^ powBits,
   Nat.mul_pos b.h_pos (Nat.pow_pos (by decide))⟩

/-- Compressed-oracle 256-bit salted-Merkle extraction / collision tail `16 (Q + 1)^2 / 2^256`. -/
def cdhzSaltedMerkleCollisionBound (Q : Nat) : RatBound :=
  ⟨16 * (Q + 1) ^ 2, 2 ^ 256, Nat.pow_pos (by decide)⟩

/-- Under `[CDHZ25, Thm 6.9]` quadratic PQSR + `WHIR_FOLD_POW_BITS = 16` joint PoW, any `184`-bit
    sliced stage clears `128` bits up to `Q + 1 + numRounds ≤ 2^33`, and any `197`-bit stage clears
    `128` bits up to `Q + 1 + numRounds ≤ 2^40`. -/
theorem cdhzPqsrPow16_clears_128bits (b : RatBound) (Q numRounds : Nat) :
    (atLeastBits 184 b → Q + 1 + numRounds ≤ 2 ^ 33 →
      atLeastBits 128 (cdhzPqsrPowScale Q numRounds 16 b)) ∧
    (atLeastBits 197 b → Q + 1 + numRounds ≤ 2 ^ 40 →
      atLeastBits 128 (cdhzPqsrPowScale Q numRounds 16 b)) := by
  refine ⟨fun hb184 hQ33 => ?_, fun hb197 hQ40 => ?_⟩
  · change 23 * (Q + 1 + numRounds) ^ 2 * b.num * 2 ^ 128 ≤ b.den * 2 ^ 16
    have hCoeff : 23 * (Q + 1 + numRounds) ^ 2 ≤ 2 ^ 72 :=
      Nat.le_trans (Nat.mul_le_mul_left 23 (Nat.pow_le_pow_left hQ33 2)) (by decide)
    have h1 := Nat.mul_le_mul_right (b.num * 2 ^ 128) hCoeff
    rw [Nat.mul_assoc]
    refine Nat.le_trans h1 ?_
    have hPow : 2 ^ 72 * (b.num * 2 ^ 128) = (b.num * 2 ^ 184) * 2 ^ 16 := by
      calc 2 ^ 72 * (b.num * 2 ^ 128) = b.num * (2 ^ 72 * 2 ^ 128) := Nat.mul_left_comm _ _ _
           _ = b.num * (2 ^ 184 * 2 ^ 16) := by
               rw [show 2 ^ 72 * 2 ^ 128 = 2 ^ 184 * 2 ^ 16 from by decide]
           _ = (b.num * 2 ^ 184) * 2 ^ 16 := (Nat.mul_assoc _ _ _).symm
    rw [hPow]
    exact Nat.mul_le_mul_right (2 ^ 16) hb184
  · change 23 * (Q + 1 + numRounds) ^ 2 * b.num * 2 ^ 128 ≤ b.den * 2 ^ 16
    have hCoeff : 23 * (Q + 1 + numRounds) ^ 2 ≤ 2 ^ 85 :=
      Nat.le_trans (Nat.mul_le_mul_left 23 (Nat.pow_le_pow_left hQ40 2)) (by decide)
    have h1 := Nat.mul_le_mul_right (b.num * 2 ^ 128) hCoeff
    rw [Nat.mul_assoc]
    refine Nat.le_trans h1 ?_
    have hPow : 2 ^ 85 * (b.num * 2 ^ 128) = (b.num * 2 ^ 197) * 2 ^ 16 := by
      calc 2 ^ 85 * (b.num * 2 ^ 128) = b.num * (2 ^ 85 * 2 ^ 128) := Nat.mul_left_comm _ _ _
           _ = b.num * (2 ^ 197 * 2 ^ 16) := by
               rw [show 2 ^ 85 * 2 ^ 128 = 2 ^ 197 * 2 ^ 16 from by decide]
           _ = (b.num * 2 ^ 197) * 2 ^ 16 := (Nat.mul_assoc _ _ _).symm
    rw [hPow]
    exact Nat.mul_le_mul_right (2 ^ 16) hb197

/-- Pure arithmetic: any `184`-bit per-round soundness bound clears `128` bits under
    state-restoration Fiat–Shamir scaling up to `Q ≤ 2^50` and `numRounds ≤ 63`
    (`(2^50 + 1) · 63 ≤ 2^56` and `2^56 · 2^128 = 2^184`). -/
theorem cdhz184_budget_at_2pow50 (b : RatBound) (hb : atLeastBits 184 b)
    (Q numRounds : Nat) (hQ : Q ≤ 2 ^ 50) (hRounds : numRounds ≤ 63) :
    atLeastBits 128 (cdhzStateRestorationScale Q numRounds b) := by
  have hScale : (Q + 1) * numRounds ≤ 2 ^ 56 := by
    have h1 : (Q + 1) * numRounds ≤ (2 ^ 50 + 1) * 63 :=
      Nat.mul_le_mul (Nat.succ_le_succ hQ) hRounds
    exact Nat.le_trans h1 (by decide)
  change (Q + 1) * numRounds * b.num * 2 ^ 128 ≤ b.den
  have hMul := Nat.mul_le_mul_right (b.num * 2 ^ 128) hScale
  rw [Nat.mul_assoc]
  refine Nat.le_trans hMul ?_
  have hPow : 2 ^ 56 * (b.num * 2 ^ 128) = b.num * 2 ^ 184 := by
    calc 2 ^ 56 * (b.num * 2 ^ 128) = b.num * (2 ^ 56 * 2 ^ 128) := Nat.mul_left_comm _ _ _
         _ = b.num * 2 ^ 184 := by rw [show 2 ^ 56 * 2 ^ 128 = 2 ^ 184 from by decide]
  rw [hPow]
  exact hb

/-- Compressed-oracle 256-bit salted-Merkle collision tail clears `128` bits for all `Q ≤ 2^50`
    (in fact with `> 20` bits to spare since `16 (2^50 + 1)^2 < 2^105 ≤ 2^128`). -/
theorem cdhzSaltedMerkle_clears_128bits_at_2pow50 (Q : Nat) (hQ : Q ≤ 2 ^ 50) :
    atLeastBits 128 (cdhzSaltedMerkleCollisionBound Q) := by
  change 16 * (Q + 1) ^ 2 * 2 ^ 128 ≤ 2 ^ 256
  have hBase : Q + 1 ≤ 2 ^ 51 := by omega
  have hSq : (Q + 1) ^ 2 ≤ (2 ^ 51) ^ 2 := Nat.pow_le_pow_left hBase 2
  have hMul : 16 * (Q + 1) ^ 2 * 2 ^ 128 ≤ 16 * (2 ^ 51) ^ 2 * 2 ^ 128 :=
    Nat.mul_le_mul_right (2 ^ 128) (Nat.mul_le_mul_left 16 hSq)
  exact Nat.le_trans hMul (by decide)

/-- **All Non-Exhaustive Canonical Sliced Stages (`nv ∈ [2, 24]`) Clear `128`-Bit Security at `Q ≤ 2^50`
    Under State-Restoration + Salted-Merkle QROM Scaling (`cdhz_sliced_stage_clears_128bits_at_2pow50`)**:
    Without waiting on `[CWYZ26]` Claim 4.8's multi-sheet space-curve constant, every already-proved
    `sliced_stage_supported_budget` row (`≥ 184` bits) clears `atLeastBits 128` at `Q ≤ 2^50` and
    `numRounds ≤ 63`, together with the `256`-bit salted-Merkle compressed-oracle tail. -/
theorem cdhz_sliced_stage_clears_128bits_at_2pow50
    (nv : Nat) (h2 : 2 ≤ nv) (h24 : nv ≤ 24)
    (g : HemStageGeom) (hg : g ∈ hemStageGeoms nv)
    (hne : hemJohnsonQromStageExhaustive g = false) :
    ∃ (r : Nat × Nat × Nat × Nat × Nat) (w : Nat × Nat × Nat × Nat),
      hemJohnsonQromTableRow nv g.stageIdx = some r ∧
      slicedStageRow nv g.stageIdx = some w ∧
      (∀ D S : List QuarticGoldilocks, D.Nodup → S.Nodup → D.length = g.n →
        AffineFoldDecompBound D S g.d r.2.2.1 (slicedStageCount S.length g r w)) ∧
      (∀ Q numRounds : Nat, Q ≤ 2 ^ 50 → numRounds ≤ 63 →
        atLeastBits 128 (cdhzStateRestorationScale Q numRounds (slicedBinaryStageBound g r w)) ∧
        atLeastBits 128 (cdhzSaltedMerkleCollisionBound Q)) := by
  obtain ⟨r, w, hr, hw, hd, hb184, _⟩ := sliced_stage_supported_budget nv h2 h24 g hg hne
  exact ⟨r, w, hr, hw, hd, fun Q numRounds hQ hR =>
    ⟨cdhz184_budget_at_2pow50 _ hb184 Q numRounds hQ hR,
     cdhzSaltedMerkle_clears_128bits_at_2pow50 Q hQ⟩⟩

/-- **DFM vs State-Restoration Scaling Contrast at `Q = 2^50` (`tooth_dfmRoundScale_fails_128bits_at_2pow50`)**:
    On `nv = 24` stage `0`, `cdhzStateRestorationScale (2^50) 32 b` and `cdhzSaltedMerkleCollisionBound (2^50)`
    both clear `128` bits, whereas naive `[DFM20]` `dfmRoundScale (2^50) b` fails `128` bits. -/
theorem tooth_dfmRoundScale_fails_128bits_at_2pow50 :
    ∃ g : HemStageGeom, g ∈ hemStageGeoms 24 ∧
      atLeastBits 128 (cdhzStateRestorationScale (2 ^ 50) 32 (slicedBinaryStageProfile 24 g)) ∧
      atLeastBits 128 (cdhzSaltedMerkleCollisionBound (2 ^ 50)) ∧
      ¬ atLeastBits 128 (dfmRoundScale (2 ^ 50) (slicedBinaryStageProfile 24 g)) :=
  ⟨(hemStageGeoms 24).get ⟨0, by decide⟩, list_get_mem (hemStageGeoms 24) ⟨0, by decide⟩,
   by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## §4. Non-Vacuity Inhabitedness Witnesses & Assurance Gates -/

private def witEqDegDom : List QuarticGoldilocks := [qgNat 0, qgNat 1, qgNat 2, qgNat 3]

private theorem witEqDegDecomp3 :
    AffineFoldDecompBound witEqDegDom witEqDegDom 1 3 16 := by
  intro _ L hNd _
  have hLen : (prodPool witEqDegDom).length = 16 := by decide +kernel
  rw [← hLen]
  exact nodup_length_le_of_subset hNd (fun ch _ => List.mem_finRange ch)

private theorem witEqDegDecomp4 :
    AffineFoldDecompBound witEqDegDom witEqDegDom 1 4 16 := by
  intro _ L hNd _
  have hLen : (prodPool witEqDegDom).length = 16 := by decide +kernel
  rw [← hLen]
  exact nodup_length_le_of_subset hNd (fun ch _ => List.mem_finRange ch)

private theorem witEqDegMixList :
    ∀ θ : QuarticGoldilocks,
      (gsDecodeList 0 3 witEqDegDom
        (fun _ => CommRingOps.add (qgNat 0) (CommRingOps.mul θ (qgNat 0)))).length ≤ 1 := by
  intro θ
  have hZero : (fun _ : QuarticGoldilocks => CommRingOps.add (qgNat 0) (CommRingOps.mul θ (qgNat 0))) =
      (fun _ => CommRingOps.zero) := by
    funext _; dsimp only [qgNat]; rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  rw [hZero]
  exact gsDecodeList_zero_length_le_one witEqDegDom 0 3 (by decide +kernel) (by decide)

private theorem witEqDegInvalid :
    (∀ Fp : List QuarticGoldilocks, Fp.length ≤ 1 →
      2 ≤ (witEqDegDom.filter (fun z => decide (RoundPoly.evalCoeffs Fp z = qgNat 0))).length →
      ringDot Fp [qgNat 1] ≠ qgNat 1) ∨
    (∀ Gp : List QuarticGoldilocks, Gp.length ≤ 1 →
      2 ≤ (witEqDegDom.filter (fun z => decide (RoundPoly.evalCoeffs Gp z = qgNat 0))).length →
      ringDot Gp [qgNat 1] ≠ qgNat 0) := by
  refine .inl (fun Fp hLen hAg hDot => ?_)
  rcases Fp with _ | ⟨c, _ | _⟩
  · change CommRingOps.zero = qgNat 1 at hDot
    exact (by decide : CommRingOps.zero ≠ qgNat 1) hDot
  · have hOne : qgNat 1 = CommRingOps.one := by decide
    have hc1 : c = CommRingOps.one := by
      rw [hOne] at hDot
      simpa only [ringDot, LawfulCommRing.mul_one, LawfulCommRing.add_zero] using hDot
    subst hc1
    exact absurd hAg (by decide +kernel)
  · simp only [List.length_cons] at hLen
    omega

theorem witness_equal_degree_three_challenge_bound :
    ∃ (D S kernel : List QuarticGoldilocks) (d A badTheta badAB maxMix : Nat)
      (f g : QuarticGoldilocks → QuarticGoldilocks) (e_f e_g c_f c_g : QuarticGoldilocks)
      (triples : List (Fin S.length × Fin (prodPool S).length)),
      D.Nodup ∧ S.Nodup ∧ (CommRingOps.zero : QuarticGoldilocks) ∈ S ∧
      d + 3 ≤ A ∧ A ≤ D.length ∧
      AffineFoldDecompBound D S (d + 1) A badTheta ∧
      AffineFoldDecompBound D S (d + 1) (A + 1) badAB ∧
      (∀ θ : QuarticGoldilocks,
        (gsDecodeList d A D (fun z => CommRingOps.add (f z) (CommRingOps.mul θ (g z)))).length ≤ maxMix) ∧
      ((∀ Fp : List QuarticGoldilocks, Fp.length ≤ d + 1 →
          A - 1 ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs Fp z = f z))).length →
          ringDot Fp kernel ≠ e_f) ∨
       (∀ Gp : List QuarticGoldilocks, Gp.length ≤ d + 1 →
          A - 1 ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs Gp z = g z))).length →
          ringDot Gp kernel ≠ e_g)) ∧
      triples.Nodup ∧
      (∀ tr ∈ triples, ¬¬ ∃ P : List QuarticGoldilocks,
        affineMcaAccepts D S (d + 1) (A + 1)
          (g, fun z => CommRingOps.add (f z) (CommRingOps.mul (S.get tr.1) (g z))) tr.2.1 P = true ∧
        ringDot P kernel = hemFoldClaimUpdate e_f e_g c_f c_g (S.get tr.1)
          ((prodPool S).get tr.2).1 ((prodPool S).get tr.2).2) :=
  ⟨witEqDegDom, witEqDegDom, [qgNat 1], 0, 3, 16, 16, 1,
   (fun _ => qgNat 0), (fun _ => qgNat 0), qgNat 1, qgNat 0, qgNat 0, qgNat 0, [],
   by decide +kernel, by decide +kernel, by decide, by decide, by decide,
   witEqDegDecomp3, witEqDegDecomp4, witEqDegMixList, witEqDegInvalid, .nil, fun _ h => nomatch h⟩

private def witCascInst : HemWhirInstance QuarticGoldilocks :=
  hemZeroOracleClaimInstance witEqDegDom 0 3 []

private theorem witCascInstInvalidPrev :
    ¬ HemStatementValid { witCascInst with initMinAgree := witCascInst.initMinAgree - 1 } :=
  hemZeroOracleClaimInstance_invalid witEqDegDom 0 2 [] (by decide +kernel) (by decide)

theorem witness_arbitrary_batch_cascade_fiber_bound :
    ∃ (inst : HemWhirInstance QuarticGoldilocks)
      (S : List QuarticGoldilocks) (badMca : Nat)
      (shifts : List QuarticGoldilocks)
      (baseWeights : List (QuarticGoldilocks × QuarticGoldilocks)),
      (1 ≤ inst.batchOracles.length ∧ inst.batchOracles.length ≤ 16) ∧
      inst.batchClaims.length = inst.batchOracles.length ∧
      shifts.length = inst.batchClaims.length ∧
      baseWeights.length = inst.batchClaims.length ∧
      inst.initDomainPts.Nodup ∧ S.Nodup ∧
      inst.initDegBound + 3 ≤ inst.initMinAgree ∧
      AffineFoldDecompBound inst.initDomainPts S (inst.initDegBound + 1) inst.initMinAgree badMca ∧
      ¬ HemStatementValid { inst with initMinAgree := inst.initMinAgree - 1 } :=
  ⟨witCascInst, witEqDegDom, 16, [qgNat 0], [(qgNat 0, qgNat 0)],
   by decide, rfl, rfl, rfl, by decide +kernel, by decide +kernel, by decide,
   witEqDegDecomp3, witCascInstInvalidPrev⟩

private def witStage24 : HemStageGeom := (hemStageGeoms 24).get ⟨0, by decide⟩

theorem witness_cdhz_sliced_stage_clears_128bits_at_2pow50 :
    ∃ (nv : Nat) (g : HemStageGeom),
      2 ≤ nv ∧ nv ≤ 24 ∧ g ∈ hemStageGeoms nv ∧ hemJohnsonQromStageExhaustive g = false :=
  ⟨24, witStage24, by decide, by decide, list_get_mem (hemStageGeoms 24) ⟨0, by decide⟩, by decide +kernel⟩

#tooth_pair Qsag.equal_degree_three_challenge_bound Qsag.tooth_equal_degree_drop_theta_exception_unsound
#tooth_pair Qsag.arbitrary_batch_cascade_fiber_bound Qsag.tooth_verifyHemAffineWhir_unincremented_agree_accepts_all
#tooth_pair Qsag.cdhz_sliced_stage_clears_128bits_at_2pow50 Qsag.tooth_dfmRoundScale_fails_128bits_at_2pow50

#verify_inhabited Qsag.equal_degree_three_challenge_bound Qsag.witness_equal_degree_three_challenge_bound
#verify_inhabited Qsag.arbitrary_batch_cascade_fiber_bound Qsag.witness_arbitrary_batch_cascade_fiber_bound
#verify_inhabited Qsag.cdhz_sliced_stage_clears_128bits_at_2pow50 Qsag.witness_cdhz_sliced_stage_clears_128bits_at_2pow50

#verify_constructive
  Qsag.equal_degree_bad_theta_bound
  Qsag.equal_degree_three_challenge_bound
  Qsag.sliced_equal_degree_three_challenge_bound
  Qsag.tooth_equal_degree_drop_theta_exception_unsound
  Qsag.arbitrary_batch_cascade_fiber_bound
  Qsag.tooth_verifyHemAffineWhir_unincremented_agree_accepts_all
  Qsag.hem_multistage_extracted_acceptance_and_fiber_bound
  Qsag.cdhzPqsrPow16_clears_128bits
  Qsag.cdhz184_budget_at_2pow50
  Qsag.cdhzSaltedMerkle_clears_128bits_at_2pow50
  Qsag.cdhz_sliced_stage_clears_128bits_at_2pow50
  Qsag.tooth_dfmRoundScale_fails_128bits_at_2pow50

end Qsag
end
