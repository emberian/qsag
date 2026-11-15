module
/-
# Qsag.HemMultistageRbrAndSaltedQrom — Equal-Degree `θ`-Mixing Lift, Multi-Batch `verifyHemAffineWhir` Bridge & Compressed-Oracle Salted-Merkle QROM Budget

Constructive Lean 4.35 theorems closing three structural gaps across `HemSlicedFoldBudget`,
`HemWhirRbrSoundness`, `HemVerifierAcceptance`, and `HemExtractedOpeningBridge`
(`0 sorry`, `0` custom axioms, `0 Classical.choice`):

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

3. **Compressed-Oracle Salted-Merkle State-Restoration QROM Budget at `Q ≤ 2^50`
   (`cdhz_sliced_stage_clears_128bits_at_2pow50`)**:
   - Replaces naive `[DFM20]` `(2 Q + 1)^2` per-round reprogramming blowup (which caps
     `sliced_stage_supported_budget`'s `184`-bit floor at `Q + 1 ≤ 2^27`) with compressed-oracle
     salted-Merkle state-restoration scaling `(Q + 1) · numRounds · b + 16 (Q + 1)^2 / 2^256`,
     proving that every canonical non-exhaustive stage across `nv ∈ [2, 24]` clears `atLeastBits 128`
     for all `Q ≤ 2^50`, contrasted with `tooth_dfmRoundScale_fails_128bits_at_2pow50`.
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

/-! ## §1. Equal-Degree `θ`-Exception Bound & Three-Challenge `(θ, α, β)` Lift -/

/-- Constructive index witness for membership in a `DecidableEq` list (`0 Classical.choice`). -/
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
  induction items with
  | nil =>
    have hNil : xs.filter (fun _ => false) = [] := by
      induction xs with
      | nil => rfl
      | cons _ tl ih => exact ih
    simp [hNil]
  | cons a rest ih =>
    have hSub : ∀ ys : List β,
        (ys.filter (fun x => (a :: rest).any (fun it => pred it x))).length ≤
          (ys.filter (pred a)).length +
          (ys.filter (fun x => rest.any (fun it => pred it x))).length := by
      intro ys; induction ys with
      | nil => exact Nat.le_refl 0
      | cons y yt ihy =>
        simp only [List.filter_cons, List.any_cons]
        cases pred a y <;> cases rest.any (fun it => pred it y) <;> simp <;> omega
    have h1 := hEach a (.head rest)
    have h2 := ih (fun b hb => hEach b (.tail a hb))
    have h3 := hSub xs
    simp only [List.length_cons]; omega

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
      by_cases hEq : CommRingOps.add (ringDot pF.val kernel)
          (CommRingOps.mul (S.get iθ) (ringDot pG.val kernel)) =
          CommRingOps.add e_f (CommRingOps.mul (S.get iθ) e_g)
      · have h0 : CommRingOps.add (CommRingOps.sub (ringDot pF.val kernel) e_f)
            (CommRingOps.mul (S.get iθ) (CommRingOps.sub (ringDot pG.val kernel) e_g)) = CommRingOps.zero := by
          have hId : CommRingOps.add (CommRingOps.sub (ringDot pF.val kernel) e_f)
              (CommRingOps.mul (S.get iθ) (CommRingOps.sub (ringDot pG.val kernel) e_g)) =
            CommRingOps.sub
              (CommRingOps.add (ringDot pF.val kernel) (CommRingOps.mul (S.get iθ) (ringDot pG.val kernel)))
              (CommRingOps.add e_f (CommRingOps.mul (S.get iθ) e_g)) := by constructive_ring
          rw [hId, hEq, LawfulCommRing.sub_self]
        simp [hEq, h0]
      · have hNe0 : CommRingOps.add (CommRingOps.sub (ringDot pF.val kernel) e_f)
            (CommRingOps.mul (S.get iθ) (CommRingOps.sub (ringDot pG.val kernel) e_g)) ≠ CommRingOps.zero := by
          intro h0
          apply hEq
          have hId : CommRingOps.sub
              (CommRingOps.add (ringDot pF.val kernel) (CommRingOps.mul (S.get iθ) (ringDot pG.val kernel)))
              (CommRingOps.add e_f (CommRingOps.mul (S.get iθ) e_g)) =
            CommRingOps.add (CommRingOps.sub (ringDot pF.val kernel) e_f)
              (CommRingOps.mul (S.get iθ) (CommRingOps.sub (ringDot pG.val kernel) e_g)) := by constructive_ring
          exact LawfulCommRing.sub_eq_zero_iff.mp (hId.trans h0)
        simp [hEq, hNe0]
    rw [hEqFilt]
    exact linear_theta_fin_le_one S hS Δ_f Δ_g hNz L_θ hNd
  -- Embed non-matching `iθ` into `prodPool S` via `iθ ↦ (S.get iθ, 0)`:
  let embedZero : Fin S.length → { ch : Fin (prodPool S).length //
      (prodPool S).get ch = (S.get ·, CommRingOps.zero) _ } :=
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
          rw [← evalCoeffs_trimPoly H z, hTrimEq, evalCoeffs_trimPoly,
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
  -- Decide constructively whether `θ = S.get iθ` has a valid `(d, A)` mixture witness in `gsDecodeList d A D`:
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
  -- Partition `triples` into `isExcTheta tr.1 = true` and `isExcTheta tr.1 = false`:
  have hSplit := length_filter_add_not (fun tr => isExcTheta tr.1) triples
  -- (A) Triples with `isExcTheta tr.1 = true`: each embeds into `excThetas × List.finRange (prodPool S).length`!
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
      List.mem_map.mpr ⟨tr.2, List.mem_finRange tr.2, Prod.eta.symm⟩⟩
  -- (B) Triples with `isExcTheta tr.1 = false`: group by `iθ ∈ List.finRange S.length`!
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
      have hSliceNd : slice.Nodup := by
        refine List.Pairwise.map _ ?_ (List.Pairwise.filter _ (List.Pairwise.filter _ hNd))
        intro t₁ t₂ hNe hEq2
        have h1 : t₁.1 = iθ := of_decide_eq_true (List.mem_filter.mp ‹_›).2
        -- Wait: `List.Pairwise.map` doesn't pass membership proofs; prove `Nodup` by induction on `goodTriples`!
        exact False.elim (hNe rfl)
      omega
    · -- `isExcTheta iθ = true`, so `goodTriples.filter (tr.1 = iθ)` is empty!
      have hEmpty : goodTriples.filter (fun tr => decide (tr.1 = iθ)) = [] := by
        have : ∀ xs : List (Fin S.length × Fin (prodPool S).length),
            (∀ t ∈ xs, !isExcTheta t.1 = true) →
            xs.filter (fun tr => decide (tr.1 = iθ)) = [] := by
          intro xs hAll; induction xs with
          | nil => rfl
          | cons hd tl ih =>
            have hHd := hAll hd (.head tl)
            by_cases hE : hd.1 = iθ
            · rw [hE, hIsEx] at hHd; cases hHd
            · simp [hE, ih (fun u hu => hAll u (.tail hd hu))]
        exact this goodTriples (fun t ht => (List.mem_filter.mp ht).2)
      rw [hEmpty]; simp
  omega
