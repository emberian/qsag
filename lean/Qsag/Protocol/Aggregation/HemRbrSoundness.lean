module
public import Qsag.Protocol.Aggregation.MultiRoundFsQrom
public import Qsag.Coding.Cwyz26
public import Qsag.Coding.GuruswamiSudan
public import Qsag.Oracle.Qrom
public import Qsag.Math.Tactic.CommRing
public import Qsag.Tactic.AssuranceKit
import Qsag.Math.Counting
import Qsag.Math.CoeffPoly
import Qsag.Math.PolyRing
import Qsag.Math.HasseHensel
import Qsag.Coding.AffineProximity

/-
# Hem affine-fold counting and a restricted cascade IOP

The algebraic counting results are constructive. The packaged IOP below has one batch oracle,
no WHIR fold stages, and a final agreement check at A₀ + 1; the transcript checker imported
from MultiRoundFsQrom uses A₀. Thus its acceptance implication goes from this restricted IOP
to the checker, and does not establish soundness of arbitrary checker transcripts.

`WellFormedHemCascadeInstance` admits an arbitrary-length `inst.stages` list constrained by the
per-stage geometry `HemStageChainWellFormed`; the two-round IOP of this file still rejects every
instance with a fold stage (its verifier checks `inst.stages = []`). The IOP that runs the fold
stages, and its round-by-round soundness, is `Qsag.Protocol.Aggregation.HemMultistageCascadeRbr`.

Johnson-radius claim preservation remains conditional on NonExcludedDecompBound. The final
QROM lemma is only a union bound from supplied event bounds and coverage. It neither derives
Fiat–Shamir challenges from transcript bytes nor constructs quantum Merkle extraction, and
must not be read as deployed verifier soundness.
-/


public section
namespace Qsag

set_option autoImplicit false
set_option exponentiation.threshold 2048

/-! ## §1. Claim-Carrying `[CWYZ26]` Affine Fold Algebra & `AffineFoldDecompBound` -/

/-- Indexed-oracle interpolation lookup on a finite domain `domPts`. On a `Nodup` domain,
    evaluating at `domPts.get idx` recovers `O idx.1` identically. -/
def lookupDomOracle {F : Type} [CommRingOps F] [DecidableEq F] :
    List F → (Nat → F) → F → F
  | [], _, _ => CommRingOps.zero
  | d :: ds, O, z =>
    if z = d then O 0 else lookupDomOracle ds (fun i => O (i + 1)) z

theorem lookupDomOracle_get {F : Type} [CommRingOps F] [DecidableEq F] :
    ∀ (domPts : List F) (O : Nat → F), domPts.Nodup →
      ∀ (idx : Fin domPts.length), lookupDomOracle domPts O (domPts.get idx) = O idx.1
  | [], _, _, idx => Fin.elim0 idx
  | d :: ds, O, hNd, ⟨0, _⟩ => by
    simp only [List.get, lookupDomOracle, ↓reduceIte]
  | d :: ds, O, hNd, ⟨k + 1, hk⟩ => by
    rcases List.pairwise_cons.mp hNd with ⟨hNotMem, hTailNd⟩
    have hk' : k < ds.length := Nat.lt_of_succ_lt_succ hk
    have hMem : ds.get ⟨k, hk'⟩ ∈ ds := list_get_mem ds ⟨k, hk'⟩
    have hNe : ds.get ⟨k, hk'⟩ ≠ d := fun hEq => hNotMem _ hMem hEq.symm
    change (if ds.get ⟨k, hk'⟩ = d then O 0 else
      lookupDomOracle ds (fun i => O (i + 1)) (ds.get ⟨k, hk'⟩)) = O (k + 1)
    simp only [hNe, ↓reduceIte]
    exact lookupDomOracle_get ds (fun i => O (i + 1)) hTailNd ⟨k, hk'⟩

theorem hemCosetAgreeCount_eq_filter_lookup {F : Type} [CommRingOps F] [DecidableEq F]
    (domPts : List F) (O : Nat → F) (P : List F) (hNd : domPts.Nodup) :
    hemCosetAgreeCount domPts O P =
      (domPts.filter (fun z =>
        decide (RoundPoly.evalCoeffs P z = lookupDomOracle domPts O z))).length := by
  rw [hemCosetAgreeCount_def, ← qsum_get_filter_length]
  apply qsum_congr; intro idx
  rw [lookupDomOracle_get domPts O hNd idx]
  by_cases h : O idx.1 = RoundPoly.evalCoeffs P (domPts.get idx)
  · simp only [h, decide_true, ↓reduceIte]
  · have h' : RoundPoly.evalCoeffs P (domPts.get idx) ≠ O idx.1 := fun e => h e.symm
    simp only [h, h', decide_false, Bool.false_eq_true, ↓reduceIte]

private theorem ringDot_zero_left {F : Type} [LawfulCommRing F] (v : List F) :
    ringDot ([] : List F) v = CommRingOps.zero := by
  rw [ringDot_eq]; exact dotVec_nil_left v

/-- Canonical trailing-zero trimming `trimPoly` preserves `ringDot` against every kernel `v`. -/
theorem ringDot_trimPoly_eq {F : Type} [LawfulCommRing F] [DecidableEq F] :
    ∀ (p v : List F), ringDot (trimPoly p) v = ringDot p v
  | [], _ => rfl
  | c :: cs, [] => by
    simp only [trimPoly]
    split <;> simp only [ringDot_eq, dotVec_nil_right]
  | c :: cs, k :: ks => by
    simp only [trimPoly]
    have ih := ringDot_trimPoly_eq cs ks
    split
    · rename_i hZero
      rcases hZero with ⟨hcsNil, hc0⟩
      rw [hc0]
      rw [ringDot_zero_left, ringDot_cons_cons, ← ih, hcsNil, ringDot_zero_left, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
    · simp only [ringDot_cons_cons, ih]

/-- Canonical trailing-zero trimming also preserves shifted functional evaluations `⟨X · P, v⟩`. -/
theorem ringDot_shiftPoly_trimPoly_eq {F : Type} [LawfulCommRing F] [DecidableEq F]
    (p v : List F) :
    ringDot (shiftPoly (trimPoly p)) v = ringDot (shiftPoly p) v := by
  cases v with
  | nil => simp only [ringDot_eq, dotVec_nil_right]
  | cons k ks =>
    simp only [shiftPoly_eq, ringDot_cons_cons, LawfulCommRing.zero_mul, LawfulCommRing.zero_add]
    exact ringDot_trimPoly_eq p ks

private theorem filter_eq_nil_of_false {α : Type} (p : α → Bool) :
    ∀ (xs : List α), (∀ a ∈ xs, p a = false) → xs.filter p = []
  | [], _ => rfl
  | a :: rest, h => by
    simp only [List.filter_cons, h a (.head rest), Bool.false_eq_true, ↓reduceIte]
    exact filter_eq_nil_of_false p rest (fun x hx => h x (.tail a hx))

/-- At most `1` element of a duplicate-free pool `S` solves `a + x * b = 0` when `b ≠ 0`. -/
private theorem linear_one_var_bad_le_one {F : Type} [LawfulField F] [DecidableEq F]
    (S : List F) (hS : S.Nodup) (a b : F) (hb : b ≠ CommRingOps.zero) :
    (S.filter (fun x =>
      decide (CommRingOps.add a (CommRingOps.mul x b) = CommRingOps.zero))).length ≤ 1 := by
  generalize hF : S.filter (fun x =>
    decide (CommRingOps.add a (CommRingOps.mul x b) = CommRingOps.zero)) = filt
  have hNd : filt.Nodup := hF ▸ List.Pairwise.filter _ hS
  rcases filt with _ | ⟨x₁, _ | ⟨x₂, rest⟩⟩
  · exact Nat.zero_le 1
  · exact Nat.le_refl 1
  · exfalso
    have hx₁Mem : x₁ ∈ S.filter (fun x =>
        decide (CommRingOps.add a (CommRingOps.mul x b) = CommRingOps.zero)) := by
      rw [hF]; exact .head _
    have hx₂Mem : x₂ ∈ S.filter (fun x =>
        decide (CommRingOps.add a (CommRingOps.mul x b) = CommRingOps.zero)) := by
      rw [hF]; exact .tail _ (.head _)
    have e₁ : CommRingOps.add a (CommRingOps.mul x₁ b) = CommRingOps.zero :=
      of_decide_eq_true (List.mem_filter.mp hx₁Mem).2
    have e₂ : CommRingOps.add a (CommRingOps.mul x₂ b) = CommRingOps.zero :=
      of_decide_eq_true (List.mem_filter.mp hx₂Mem).2
    have hId : CommRingOps.mul (CommRingOps.sub x₁ x₂) b =
        CommRingOps.sub (CommRingOps.add a (CommRingOps.mul x₁ b))
          (CommRingOps.add a (CommRingOps.mul x₂ b)) := by
      constructive_ring
    have hDiff0 : CommRingOps.mul (CommRingOps.sub x₁ x₂) b = CommRingOps.zero := by
      rw [hId, e₁, e₂, LawfulCommRing.sub_self]
    rcases LawfulField.mul_eq_zero hDiff0 with hSub0 | hb0
    · have hEq : x₁ = x₂ := LawfulCommRing.sub_eq_zero_iff.mp hSub0
      exact (List.pairwise_cons.mp hNd).1 x₂ (.head _) hEq
    · exact hb hb0

/-- **Absorbed Linear-Claim Bad-Pair Bound (`absorbed_linear_claim_bad_pairs_le_card`)**:
    Over any `[LawfulField F] [DecidableEq F]`, if `Δ₀ ≠ 0 ∨ Δ_α ≠ 0`, then across the entire
    product pool `prodPool S` (`S.Nodup`), at most `S.length` pairs `(α, β)` satisfy
    `Δ₀ + α * Δ_α + β * Δ_β = 0`. -/
theorem absorbed_linear_claim_bad_pairs_le_card {F : Type} [LawfulField F] [DecidableEq F]
    (S : List F) (hS : S.Nodup) (Δ₀ Δ_α Δ_β : F)
    (hNz : Δ₀ ≠ CommRingOps.zero ∨ Δ_α ≠ CommRingOps.zero) :
    ((prodPool S).filter (fun p : F × F =>
      decide (CommRingOps.add Δ₀
        (CommRingOps.add (CommRingOps.mul p.1 Δ_α) (CommRingOps.mul p.2 Δ_β)) =
          CommRingOps.zero))).length ≤ S.length := by
  let pred : F × F → Bool := fun p =>
    decide (CommRingOps.add Δ₀
      (CommRingOps.add (CommRingOps.mul p.1 Δ_α) (CommRingOps.mul p.2 Δ_β)) =
        CommRingOps.zero)
  have hFlatFilter : ∀ (xs : List F),
      ((xs.flatMap (fun a => S.map (fun b => (a, b)))).filter pred).length =
        (xs.map (fun a => (S.filter (fun b => pred (a, b))).length)).sum := by
    intro xs
    induction xs with
    | nil => rfl
    | cons a rest ih =>
      simp only [List.flatMap_cons, List.filter_append, List.length_append, List.map_cons,
        List.sum_cons, ih]
      congr 1
      clear ih rest hS
      induction S with
      | nil => rfl
      | cons b bs ihS =>
        simp only [List.map_cons, List.filter_cons]
        cases hb : pred (a, b) <;>
          simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons, ihS]
  if hα : Δ_α ≠ CommRingOps.zero then
    have hSwap :
        ∀ b : F, (S.filter (fun a => pred (a, b))).length ≤ 1 := by
      intro b
      have hEqPred : S.filter (fun a => pred (a, b)) =
          S.filter (fun a => decide (CommRingOps.add (CommRingOps.add Δ₀ (CommRingOps.mul b Δ_β))
            (CommRingOps.mul a Δ_α) = CommRingOps.zero)) := by
        apply congrArg (fun q => List.filter q S)
        funext a; dsimp only [pred]
        rw [LawfulCommRing.add_comm (CommRingOps.mul a Δ_α) (CommRingOps.mul b Δ_β),
            ← LawfulCommRing.add_assoc]
      rw [hEqPred]
      exact linear_one_var_bad_le_one S hS _ Δ_α hα
    have hCommSum : ∀ (xs ys : List F),
        ((xs.flatMap (fun a => ys.map (fun b => (a, b)))).filter pred).length =
          (ys.map (fun b => (xs.filter (fun a => pred (a, b))).length)).sum := by
      intro xs ys
      induction xs with
      | nil =>
        have hZeros : ∀ l : List F, (l.map (fun _ => 0)).sum = 0 := by
          intro l; induction l with | nil => rfl | cons _ tl iht => simp [iht]
        simp only [List.flatMap_nil, List.filter_nil, List.length_nil]
        exact (hZeros ys).symm
      | cons a rest ih =>
        simp only [List.flatMap_cons, List.filter_append, List.length_append, ih]
        clear ih
        induction ys with
        | nil => rfl
        | cons b bs ihb =>
          rw [List.map_cons (f := fun b => (a, b)), List.filter_cons,
              List.map_cons (f := fun b => (List.filter (fun a => pred (a, b)) rest).length),
              List.sum_cons,
              List.map_cons (f := fun b => (List.filter (fun a => pred (a, b)) (a :: rest)).length),
              List.sum_cons, ← ihb]
          simp only [List.filter_cons]
          cases hb : pred (a, b) <;>
            simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega
    rw [prodPool_eq]
    change ((S.flatMap (fun a => S.map (fun b => (a, b)))).filter pred).length ≤ S.length
    rw [hCommSum S S]
    have hSumLe : ∀ (ys : List F), (∀ b ∈ ys, (S.filter (fun a => pred (a, b))).length ≤ 1) →
        (ys.map (fun b => (S.filter (fun a => pred (a, b))).length)).sum ≤ ys.length := by
      intro ys hEach
      induction ys with
      | nil => exact Nat.le_refl 0
      | cons b bs ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        have h1 := hEach b (.head bs)
        have h2 := ih (fun y hy => hEach y (.tail b hy))
        omega
    exact hSumLe S (fun b _ => hSwap b)
  else
    have hα0 : Δ_α = CommRingOps.zero := Decidable.of_not_not hα
    have hΔ₀ : Δ₀ ≠ CommRingOps.zero := by
      rcases hNz with h0 | h1
      · exact h0
      · exact False.elim (hα h1)
    rw [prodPool_eq]
    change ((S.flatMap (fun a => S.map (fun b => (a, b)))).filter pred).length ≤ S.length
    rw [hFlatFilter S]
    if hβ : Δ_β ≠ CommRingOps.zero then
      have hPerA : ∀ a : F, (S.filter (fun b => pred (a, b))).length ≤ 1 := by
        intro a
        have hEqPred : S.filter (fun b => pred (a, b)) =
            S.filter (fun b => decide (CommRingOps.add Δ₀ (CommRingOps.mul b Δ_β) =
              CommRingOps.zero)) := by
          apply congrArg (fun q => List.filter q S)
          funext b; dsimp only [pred]
          rw [hα0, LawfulCommRing.mul_zero, LawfulCommRing.zero_add]
        rw [hEqPred]
        exact linear_one_var_bad_le_one S hS Δ₀ Δ_β hβ
      have hSumLe : ∀ (xs : List F),
          (xs.map (fun a => (S.filter (fun b => pred (a, b))).length)).sum ≤ xs.length := by
        intro xs
        induction xs with
        | nil => exact Nat.le_refl 0
        | cons a rest ih =>
          simp only [List.map_cons, List.sum_cons, List.length_cons]
          have h1 := hPerA a
          omega
      exact hSumLe S
    else
      have hβ0 : Δ_β = CommRingOps.zero := Decidable.of_not_not hβ
      have hEmpty : ∀ a : F, (S.filter (fun b => pred (a, b))).length = 0 := by
        intro a
        rw [List.length_eq_zero_iff]
        apply filter_eq_nil_of_false
        intro b _
        dsimp only [pred]
        rw [hα0, hβ0, LawfulCommRing.mul_zero, LawfulCommRing.mul_zero,
            LawfulCommRing.add_zero, LawfulCommRing.add_zero]
        exact decide_eq_false hΔ₀
      have hSum0 : ∀ (xs : List F),
          (xs.map (fun a => (S.filter (fun b => pred (a, b))).length)).sum = 0 := by
        intro xs
        induction xs with
        | nil => rfl
        | cons a rest ih => simp only [List.map_cons, List.sum_cons, hEmpty a, Nat.zero_add, ih]
      rw [hSum0 S]
      exact Nat.zero_le _

/-- **Constructive Soundness of the `5`-Wire Dual Bridge (`hemBridge_bad_quads_le_three_cube`,
    `affine.rs::bridge_finish`)**:
    Over `[LawfulField F] [DecidableEq F]`, if `⟨cE, kE⟩ + ⟨cO, kO⟩ ≠ curClaim` (`kE.length = kO.length`),
    then across all `S.length ^ 4` challenge quadruples `(φ, θ, α, β) ∈ S^4` (`S.Nodup`), at most
    `3 * S.length ^ 3` quadruples reconcile `ringDot (affineCombine θ α β cE cO) (zipFold φ kE kO)`
    with `hemBridgeFoldClaim curClaim w₀ w₁ w₂ c_F c_G φ θ α β`. -/
theorem hemBridge_bad_quads_le_three_cube {F : Type} [LawfulField F] [DecidableEq F]
    (S : List F) (hS : S.Nodup)
    (curClaim w₀ w₁ w₂ c_F c_G : F)
    (cE cO kE kO : List F) (hLenK : kE.length = kO.length)
    (hFalse : CommRingOps.add (ringDot cE kE) (ringDot cO kO) ≠ curClaim) :
    qsum S.length (fun iφ =>
      qsum S.length (fun iθ =>
        qsum S.length (fun iα =>
          qsum S.length (fun iβ =>
            let φ := S.get iφ
            let θ := S.get iθ
            let α := S.get iα
            let β := S.get iβ
            let k' := List.zipWith (fun a b => CommRingOps.add a (CommRingOps.mul φ b)) kE kO
            if ringDot (affineCombine θ α β cE cO) k' =
                hemBridgeFoldClaim curClaim w₀ w₁ w₂ c_F c_G φ θ α β then 1 else 0)))) ≤
      3 * S.length ^ 3 := by
  let M := S.length
  let dFE := ringDot cE kE
  let dFO := ringDot cE kO
  let dGE := ringDot cO kE
  let dGO := ringDot cO kO
  -- Notice: if BOTH `(w₀ - dFE) = 0` AND `((curClaim - w₀) - dGO) = 0`, then
  -- `dFE + dGO = w₀ + (curClaim - w₀) = curClaim`, contradicting `hFalse`!
  let badPhi : F → Bool := fun φ =>
    decide (CommRingOps.add w₀ (CommRingOps.mul φ w₁) =
              CommRingOps.add dFE (CommRingOps.mul φ dFO)) &&
    decide (CommRingOps.add w₂ (CommRingOps.mul φ (CommRingOps.sub curClaim w₀)) =
              CommRingOps.add dGE (CommRingOps.mul φ dGO))
  have hBadPhiLe1 : (S.filter badPhi).length ≤ 1 := by
    if hDiff1 : CommRingOps.sub w₁ dFO ≠ CommRingOps.zero then
      have hSub : ∀ φ ∈ S.filter badPhi,
          φ ∈ S.filter (fun φ => decide (CommRingOps.add (CommRingOps.sub w₀ dFE)
            (CommRingOps.mul φ (CommRingOps.sub w₁ dFO)) = CommRingOps.zero)) := by
        intro φ hφ
        rcases List.mem_filter.mp hφ with ⟨hφS, hB⟩
        have hEq1 : CommRingOps.add w₀ (CommRingOps.mul φ w₁) =
            CommRingOps.add dFE (CommRingOps.mul φ dFO) :=
          of_decide_eq_true ((Bool.and_eq_true _ _).mp hB).1
        refine List.mem_filter.mpr ⟨hφS, decide_eq_true ?_⟩
        have hId : CommRingOps.add (CommRingOps.sub w₀ dFE)
            (CommRingOps.mul φ (CommRingOps.sub w₁ dFO)) =
          CommRingOps.sub (CommRingOps.add w₀ (CommRingOps.mul φ w₁))
            (CommRingOps.add dFE (CommRingOps.mul φ dFO)) := by
          constructive_ring
        rw [hId, hEq1, LawfulCommRing.sub_self]
      exact Nat.le_trans
        (nodup_length_le_of_subset (List.Pairwise.filter _ hS) hSub)
        (linear_one_var_bad_le_one S hS _ _ hDiff1)
    else
      have hw₁Eq : w₁ = dFO := LawfulCommRing.sub_eq_zero_iff.mp (Decidable.of_not_not hDiff1)
      if hw₀Ne : w₀ ≠ dFE then
        have hEmpty : S.filter badPhi = [] := by
          apply filter_eq_nil_of_false
          intro φ _
          cases hB : badPhi φ
          · rfl
          · exfalso
            have hEq1 : CommRingOps.add w₀ (CommRingOps.mul φ w₁) =
                CommRingOps.add dFE (CommRingOps.mul φ dFO) :=
              of_decide_eq_true ((Bool.and_eq_true _ _).mp hB).1
            rw [hw₁Eq] at hEq1
            have hId1 : w₀ = CommRingOps.sub (CommRingOps.add w₀ (CommRingOps.mul φ dFO))
                (CommRingOps.mul φ dFO) := by constructive_ring
            have hId2 : dFE = CommRingOps.sub (CommRingOps.add dFE (CommRingOps.mul φ dFO))
                (CommRingOps.mul φ dFO) := by constructive_ring
            exact hw₀Ne (hId1.trans ((congrArg (fun u => CommRingOps.sub u (CommRingOps.mul φ dFO)) hEq1).trans hId2.symm))
        rw [hEmpty]; exact Nat.zero_le 1
      else
        have hw₀Eq : w₀ = dFE := Decidable.of_not_not hw₀Ne
        have hRemNe : CommRingOps.sub (CommRingOps.sub curClaim w₀) dGO ≠ CommRingOps.zero := by
          intro h0
          have hRemEq : CommRingOps.sub curClaim w₀ = dGO := LawfulCommRing.sub_eq_zero_iff.mp h0
          apply hFalse
          change CommRingOps.add dFE dGO = curClaim
          rw [← hw₀Eq, ← hRemEq]
          constructive_ring
        have hSub : ∀ φ ∈ S.filter badPhi,
            φ ∈ S.filter (fun φ => decide (CommRingOps.add (CommRingOps.sub w₂ dGE)
              (CommRingOps.mul φ (CommRingOps.sub (CommRingOps.sub curClaim w₀) dGO)) =
                CommRingOps.zero)) := by
          intro φ hφ
          rcases List.mem_filter.mp hφ with ⟨hφS, hB⟩
          have hEq2 : CommRingOps.add w₂ (CommRingOps.mul φ (CommRingOps.sub curClaim w₀)) =
              CommRingOps.add dGE (CommRingOps.mul φ dGO) :=
            of_decide_eq_true ((Bool.and_eq_true _ _).mp hB).2
          refine List.mem_filter.mpr ⟨hφS, decide_eq_true ?_⟩
          have hId : CommRingOps.add (CommRingOps.sub w₂ dGE)
              (CommRingOps.mul φ (CommRingOps.sub (CommRingOps.sub curClaim w₀) dGO)) =
            CommRingOps.sub (CommRingOps.add w₂ (CommRingOps.mul φ (CommRingOps.sub curClaim w₀)))
              (CommRingOps.add dGE (CommRingOps.mul φ dGO)) := by
            constructive_ring
          rw [hId, hEq2, LawfulCommRing.sub_self]
        exact Nat.le_trans
          (nodup_length_le_of_subset (List.Pairwise.filter _ hS) hSub)
          (linear_one_var_bad_le_one S hS _ _ hRemNe)
  -- For any `φ` with `badPhi φ = false`, at most `1` `θ ∈ S` makes `H_claim = ⟨F + θ G, k'⟩`,
  -- and for every other `θ`, at most `M` pairs `(α, β) ∈ S × S` reconcile the claim (`≤ M^2 + M * M = 2 * M^2`).
  have hPerGoodPhi : ∀ iφ : Fin M, badPhi (S.get iφ) = false →
      qsum M (fun iθ =>
        qsum M (fun iα =>
          qsum M (fun iβ =>
            let φ := S.get iφ
            let θ := S.get iθ
            let α := S.get iα
            let β := S.get iβ
            let k' := List.zipWith (fun a b => CommRingOps.add a (CommRingOps.mul φ b)) kE kO
            if ringDot (affineCombine θ α β cE cO) k' =
                hemBridgeFoldClaim curClaim w₀ w₁ w₂ c_F c_G φ θ α β then 1 else 0))) ≤
      2 * M ^ 2 := by
    intro iφ hGoodPhi
    let φ := S.get iφ
    let k' := List.zipWith (fun a b => CommRingOps.add a (CommRingOps.mul φ b)) kE kO
    let fCl := CommRingOps.add w₀ (CommRingOps.mul φ w₁)
    let gCl := CommRingOps.add w₂ (CommRingOps.mul φ (CommRingOps.sub curClaim w₀))
    let fTrue := ringDot cE k'
    let gTrue := ringDot cO k'
    have hfTrueEq : fTrue = CommRingOps.add dFE (CommRingOps.mul φ dFO) :=
      ringDot_zipFold φ cE kE kO hLenK
    have hgTrueEq : gTrue = CommRingOps.add dGE (CommRingOps.mul φ dGO) :=
      ringDot_zipFold φ cO kE kO hLenK
    have hPairNe : fTrue ≠ fCl ∨ gTrue ≠ gCl := by
      if hf : fTrue = fCl then
        right
        intro hg
        have hBTrue : badPhi φ = true := by
          dsimp only [badPhi]
          have e1 : CommRingOps.add w₀ (CommRingOps.mul φ w₁) = CommRingOps.add dFE (CommRingOps.mul φ dFO) :=
            hf.symm.trans hfTrueEq
          have e2 : CommRingOps.add w₂ (CommRingOps.mul φ (CommRingOps.sub curClaim w₀)) =
              CommRingOps.add dGE (CommRingOps.mul φ dGO) :=
            hg.symm.trans hgTrueEq
          rw [decide_eq_true e1, decide_eq_true e2]
          rfl
        rw [hBTrue] at hGoodPhi
        exact Bool.noConfusion hGoodPhi
      else
        exact .inl hf
    let badTheta : F → Bool := fun θ =>
      decide (CommRingOps.add (CommRingOps.sub fTrue fCl)
        (CommRingOps.mul θ (CommRingOps.sub gTrue gCl)) = CommRingOps.zero)
    have hBadThetaLe1 : (S.filter badTheta).length ≤ 1 := by
      if hgNe : CommRingOps.sub gTrue gCl ≠ CommRingOps.zero then
        exact linear_one_var_bad_le_one S hS _ _ hgNe
      else
        have hgEq : gTrue = gCl := LawfulCommRing.sub_eq_zero_iff.mp (Decidable.of_not_not hgNe)
        have hfNe : CommRingOps.sub fTrue fCl ≠ CommRingOps.zero := by
          rcases hPairNe with hf | hg
          · exact fun h0 => hf (LawfulCommRing.sub_eq_zero_iff.mp h0)
          · exact False.elim (hg hgEq)
        have hNil : S.filter badTheta = [] := by
          apply filter_eq_nil_of_false
          intro θ _
          cases hB : badTheta θ
          · rfl
          · exfalso
            have h0 : CommRingOps.add (CommRingOps.sub fTrue fCl)
                (CommRingOps.mul θ (CommRingOps.sub gTrue gCl)) = CommRingOps.zero :=
              of_decide_eq_true hB
            rw [hgEq, LawfulCommRing.sub_self, LawfulCommRing.mul_zero, LawfulCommRing.add_zero] at h0
            exact hfNe h0
        rw [hNil]; exact Nat.zero_le 1
    have hPerTheta : ∀ iθ : Fin M,
        qsum M (fun iα =>
          qsum M (fun iβ =>
            let θ := S.get iθ
            let α := S.get iα
            let β := S.get iβ
            if ringDot (affineCombine θ α β cE cO) k' =
                hemBridgeFoldClaim curClaim w₀ w₁ w₂ c_F c_G φ θ α β then 1 else 0)) ≤
        (if badTheta (S.get iθ) = true then M ^ 2 else M) := by
      intro iθ
      let θ := S.get iθ
      cases hTh : badTheta θ
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hCombNe : CommRingOps.add (CommRingOps.sub fTrue fCl)
            (CommRingOps.mul θ (CommRingOps.sub gTrue gCl)) ≠ CommRingOps.zero :=
          of_decide_eq_false hTh
        -- For each `iβ`, at most `1` `iα` solves the equation!
        rw [qsum_comm]
        have hPerBeta : ∀ iβ : Fin M,
            qsum M (fun iα =>
              let α := S.get iα
              let β := S.get iβ
              if ringDot (affineCombine θ α β cE cO) k' =
                  hemBridgeFoldClaim curClaim w₀ w₁ w₂ c_F c_G φ θ α β then 1 else 0) ≤ 1 := by
          intro iβ
          let β := S.get iβ
          let Δ_g := CommRingOps.sub gTrue gCl
          let Δ_h := CommRingOps.add (CommRingOps.sub fTrue fCl) (CommRingOps.mul θ Δ_g)
          let sTrue := CommRingOps.add (ringDot (shiftPoly cE) k')
            (CommRingOps.mul θ (ringDot (shiftPoly cO) k'))
          let sCl := CommRingOps.add c_F (CommRingOps.mul θ c_G)
          let Δ_s := CommRingOps.sub sTrue sCl
          let constTerm := CommRingOps.add Δ_g (CommRingOps.mul β Δ_s)
          let pAlpha : Fin M → Bool := fun iα =>
            decide (ringDot (affineCombine θ (S.get iα) β cE cO) k' =
              hemBridgeFoldClaim curClaim w₀ w₁ w₂ c_F c_G φ θ (S.get iα) β)
          have hEqQsum :
              qsum M (fun iα =>
                let α := S.get iα
                let β := S.get iβ
                if ringDot (affineCombine θ α β cE cO) k' =
                    hemBridgeFoldClaim curClaim w₀ w₁ w₂ c_F c_G φ θ α β then 1 else 0) =
              qsum M (fun iα => if pAlpha iα = true then 1 else 0) := by
            apply qsum_congr; intro iα
            change (if ringDot (affineCombine θ (S.get iα) β cE cO) k' =
                hemBridgeFoldClaim curClaim w₀ w₁ w₂ c_F c_G φ θ (S.get iα) β then 1 else 0) =
              if decide (ringDot (affineCombine θ (S.get iα) β cE cO) k' =
                hemBridgeFoldClaim curClaim w₀ w₁ w₂ c_F c_G φ θ (S.get iα) β) = true then 1 else 0
            by_cases hc : ringDot (affineCombine θ (S.get iα) β cE cO) k' =
                hemBridgeFoldClaim curClaim w₀ w₁ w₂ c_F c_G φ θ (S.get iα) β
            · simp only [hc, decide_true, ↓reduceIte]
            · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte]
          rw [hEqQsum]
          apply qsum_le_one_of_subsingleton pAlpha
          intro i₁ i₂ h₁ h₂
          have toLin : ∀ α : F,
              ringDot (affineCombine θ α β cE cO) k' =
                hemBridgeFoldClaim curClaim w₀ w₁ w₂ c_F c_G φ θ α β →
              CommRingOps.add constTerm (CommRingOps.mul α Δ_h) = CommRingOps.zero := by
            intro α hEq
            rw [ringDot_affineCombine_eq_bridge] at hEq
            rw [hemBridgeFoldClaim_def] at hEq
            have hSub0 := congrArg (fun u => CommRingOps.sub u
              (CommRingOps.add gCl (CommRingOps.add
                (CommRingOps.mul α (CommRingOps.add fCl (CommRingOps.mul θ gCl)))
                (CommRingOps.mul β sCl)))) hEq
            rw [LawfulCommRing.sub_self] at hSub0
            have hAlg : ∀ (gT gC hT hC sT sC : F),
                CommRingOps.sub
                  (CommRingOps.add gT (CommRingOps.add (CommRingOps.mul α hT) (CommRingOps.mul β sT)))
                  (CommRingOps.add gC (CommRingOps.add (CommRingOps.mul α hC) (CommRingOps.mul β sC))) =
                CommRingOps.add
                  (CommRingOps.add (CommRingOps.sub gT gC) (CommRingOps.mul β (CommRingOps.sub sT sC)))
                  (CommRingOps.mul α (CommRingOps.sub hT hC)) := by
              intro gT gC hT hC sT sC; constructive_ring
            have hStep := hAlg gTrue gCl
              (CommRingOps.add fTrue (CommRingOps.mul θ gTrue))
              (CommRingOps.add fCl (CommRingOps.mul θ gCl))
              sTrue sCl
            have hHEq : CommRingOps.sub
                (CommRingOps.add fTrue (CommRingOps.mul θ gTrue))
                (CommRingOps.add fCl (CommRingOps.mul θ gCl)) = Δ_h := by
              dsimp only [Δ_h, Δ_g]; constructive_ring
            rw [hStep, hHEq] at hSub0
            exact hSub0
          have e₁ := toLin (S.get i₁) (of_decide_eq_true h₁)
          have e₂ := toLin (S.get i₂) (of_decide_eq_true h₂)
          have hDiffId : CommRingOps.mul (CommRingOps.sub (S.get i₁) (S.get i₂)) Δ_h =
              CommRingOps.sub
                (CommRingOps.add constTerm (CommRingOps.mul (S.get i₁) Δ_h))
                (CommRingOps.add constTerm (CommRingOps.mul (S.get i₂) Δ_h)) := by
            constructive_ring
          have hDiff0 : CommRingOps.mul (CommRingOps.sub (S.get i₁) (S.get i₂)) Δ_h =
              CommRingOps.zero := by
            rw [hDiffId, e₁, e₂, LawfulCommRing.sub_self]
          rcases LawfulField.mul_eq_zero hDiff0 with hSubA | hDh0
          · exact nodup_get_inj hS (LawfulCommRing.sub_eq_zero_iff.mp hSubA)
          · exact False.elim (hCombNe hDh0)
        have hSumB := qsum_le_qsum hPerBeta
        rw [qsum_const, Nat.mul_one] at hSumB
        exact hSumB
      · simp only [↓reduceIte]
        have hInner : ∀ iα : Fin M,
            qsum M (fun iβ =>
              if ringDot (affineCombine θ (S.get iα) (S.get iβ) cE cO) k' =
                  hemBridgeFoldClaim curClaim w₀ w₁ w₂ c_F c_G φ θ (S.get iα) (S.get iβ)
              then 1 else 0) ≤ M := by
          intro iα
          have h1 : qsum M (fun iβ =>
              if ringDot (affineCombine θ (S.get iα) (S.get iβ) cE cO) k' =
                  hemBridgeFoldClaim curClaim w₀ w₁ w₂ c_F c_G φ θ (S.get iα) (S.get iβ)
              then 1 else 0) ≤ qsum M (fun _ => 1) :=
            qsum_le_qsum (fun _ => by split <;> omega)
          rw [qsum_const, Nat.mul_one] at h1
          exact h1
        have hOuter := qsum_le_qsum hInner
        rw [qsum_const, ← Nat.pow_two] at hOuter
        exact hOuter
    have hSumTheta := qsum_le_qsum hPerTheta
    have hSplitTheta :
        qsum M (fun iθ => if badTheta (S.get iθ) = true then M ^ 2 else M) ≤
          qsum M (fun iθ => (if badTheta (S.get iθ) = true then 1 else 0) * M ^ 2 + M) := by
      apply qsum_le_qsum; intro iθ
      cases badTheta (S.get iθ) <;> simp <;> omega
    rw [qsum_add, qsum_mul_right, qsum_const, qsum_get_filter_length] at hSplitTheta
    have hThCount : (S.filter badTheta).length * M ^ 2 + M * M ≤ 2 * M ^ 2 := by
      have hm := Nat.mul_le_mul_right (M ^ 2) hBadThetaLe1
      have hSq : M * M = M ^ 2 := (Nat.pow_two M).symm
      rw [Nat.one_mul] at hm
      rw [hSq]
      omega
    exact Nat.le_trans hSumTheta (Nat.le_trans hSplitTheta hThCount)
  -- Sum over all `iφ : Fin M`:
  have hPerPhi : ∀ iφ : Fin M,
      qsum M (fun iθ =>
        qsum M (fun iα =>
          qsum M (fun iβ =>
            let φ := S.get iφ
            let θ := S.get iθ
            let α := S.get iα
            let β := S.get iβ
            let k' := List.zipWith (fun a b => CommRingOps.add a (CommRingOps.mul φ b)) kE kO
            if ringDot (affineCombine θ α β cE cO) k' =
                hemBridgeFoldClaim curClaim w₀ w₁ w₂ c_F c_G φ θ α β then 1 else 0))) ≤
      (if badPhi (S.get iφ) = true then 1 else 0) * M ^ 3 + 2 * M ^ 2 := by
    intro iφ
    cases hPh : badPhi (S.get iφ)
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_mul, Nat.zero_add]
      exact hPerGoodPhi iφ hPh
    · simp only [↓reduceIte, Nat.one_mul]
      have hCube :
          qsum M (fun iθ =>
            qsum M (fun iα =>
              qsum M (fun iβ =>
                let φ := S.get iφ
                let θ := S.get iθ
                let α := S.get iα
                let β := S.get iβ
                let k' := List.zipWith (fun a b => CommRingOps.add a (CommRingOps.mul φ b)) kE kO
                if ringDot (affineCombine θ α β cE cO) k' =
                    hemBridgeFoldClaim curClaim w₀ w₁ w₂ c_F c_G φ θ α β then 1 else 0))) ≤
          M ^ 3 := by
        have h1 : ∀ iθ : Fin M,
            qsum M (fun iα =>
              qsum M (fun iβ =>
                let φ := S.get iφ
                let θ := S.get iθ
                let α := S.get iα
                let β := S.get iβ
                let k' := List.zipWith (fun a b => CommRingOps.add a (CommRingOps.mul φ b)) kE kO
                if ringDot (affineCombine θ α β cE cO) k' =
                    hemBridgeFoldClaim curClaim w₀ w₁ w₂ c_F c_G φ θ α β then 1 else 0)) ≤ M ^ 2 := by
          intro iθ
          have h2 : ∀ iα : Fin M,
              qsum M (fun iβ =>
                if ringDot (affineCombine (S.get iθ) (S.get iα) (S.get iβ) cE cO)
                    (List.zipWith (fun a b => CommRingOps.add a (CommRingOps.mul (S.get iφ) b)) kE kO) =
                    hemBridgeFoldClaim curClaim w₀ w₁ w₂ c_F c_G (S.get iφ) (S.get iθ) (S.get iα) (S.get iβ)
                then 1 else 0) ≤ M := by
            intro iα
            have h3 := qsum_le_qsum (n := M)
              (f := fun iβ =>
                if ringDot (affineCombine (S.get iθ) (S.get iα) (S.get iβ) cE cO)
                    (List.zipWith (fun a b => CommRingOps.add a (CommRingOps.mul (S.get iφ) b)) kE kO) =
                    hemBridgeFoldClaim curClaim w₀ w₁ w₂ c_F c_G (S.get iφ) (S.get iθ) (S.get iα) (S.get iβ)
                then 1 else 0)
              (g := fun _ => 1) (fun _ => by split <;> omega)
            rw [qsum_const, Nat.mul_one] at h3
            exact h3
          have h2Sum := qsum_le_qsum h2
          rw [qsum_const, ← Nat.pow_two] at h2Sum
          exact h2Sum
        have h1Sum := qsum_le_qsum h1
        rw [qsum_const] at h1Sum
        have hPow3 : M * M ^ 2 = M ^ 3 := by
          show M * M ^ 2 = M ^ 2 * M
          exact Nat.mul_comm M (M ^ 2)
        rwa [hPow3] at h1Sum
      exact Nat.le_trans hCube (Nat.le_add_right _ _)
  have hAllPhi := qsum_le_qsum hPerPhi
  rw [qsum_add, qsum_mul_right, qsum_const, qsum_get_filter_length] at hAllPhi
  have hFinal : (S.filter badPhi).length * M ^ 3 + M * (2 * M ^ 2) ≤ 3 * M ^ 3 := by
    have hm := Nat.mul_le_mul_right (M ^ 3) hBadPhiLe1
    rw [Nat.one_mul] at hm
    have hPow3 : M * M ^ 2 = M ^ 3 := by
      show M * M ^ 2 = M ^ 2 * M
      exact Nat.mul_comm M (M ^ 2)
    have hTwo : M * (2 * M ^ 2) = 2 * M ^ 3 := by
      rw [Nat.mul_left_comm, hPow3]
    omega
  exact Nat.le_trans hAllPhi hFinal

theorem filter_any_length_le {α β : Type} (items : List α) (pred : α → β → Bool)
    (xs : List β) (B : Nat)
    (hEach : ∀ a ∈ items, (xs.filter (pred a)).length ≤ B) :
    (xs.filter (fun x => items.any (fun a => pred a x))).length ≤ items.length * B := by
  induction items with
  | nil =>
    have hNil : xs.filter (fun _ => false) = [] :=
      filter_eq_nil_of_false (fun _ => false) xs (fun _ _ => rfl)
    simp only [List.any_nil, hNil, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons a rest ih =>
    have hSub : ∀ (ys : List β),
        (ys.filter (fun x => (a :: rest).any (fun it => pred it x))).length ≤
          (ys.filter (pred a)).length +
          (ys.filter (fun x => rest.any (fun it => pred it x))).length := by
      have hAnyCons : (fun x => (a :: rest).any (fun it => pred it x)) =
          (fun x => pred a x || rest.any (fun it => pred it x)) :=
        funext (fun _ => List.any_cons)
      rw [hAnyCons]
      intro ys
      induction ys with
      | nil => exact Nat.le_refl 0
      | cons y yt ihy =>
        simp only [List.filter_cons]
        cases h1 : pred a y <;> cases h2 : rest.any (fun it => pred it y) <;>
          simp only [Bool.true_or, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
            List.length_cons] <;> omega
    have hA := hEach a (.head rest)
    have hR := ih (fun it hit => hEach it (.tail a hit))
    have hTot := hSub xs
    simp only [List.length_cons, Nat.succ_mul]
    omega

/-- Binary claim-carrying fold flip bound from `hDecomp`. The theta-mixing step of the
    equal-degree three-challenge combiner is not included in this theorem:
    Over `[LawfulField F] [DecidableEq F]`, if `(g, e_g)` has NO degree-`≤ d` witness at agreement
    `A` on `D` (`D.Nodup`, `d + 2 ≤ A`), then for ANY word `f`, running claim `e_f`, and absorbed
    shift `s_g`, the number of challenges `ch ∈ prodPool S` (`S.Nodup`) yielding a post-fold
    witness `P` (`deg P ≤ d + 1`, agreement `≥ A + 1` with `f + (α + β X) g`, and
    `ringDot P kernel = e_f + α e_g + β s_g`) is at most
    `badMca + (gsDecodeList (d + 1) A D f).length * (gsDecodeList d A D g).length * S.length`. -/
theorem claimFold_bad_pairs_bound {F : Type} [LawfulField F] [DecidableEq F]
    (D S kernel : List F) (d A badMca : Nat)
    (f g : F → F) (e_f e_g s_g : F)
    (hD : D.Nodup) (hS : S.Nodup) (hdA : d + 2 ≤ A)
    (hDecomp : AffineFoldDecompBound D S (d + 1) (A + 1) badMca)
    (hInvalidG : ∀ G : List F, G.length ≤ d + 1 →
      A ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs G z = g z))).length →
      ringDot G kernel ≠ e_g)
    (L : List (Fin (prodPool S).length)) (hNd : L.Nodup)
    (hFlip : ∀ ch ∈ L, ¬¬ ∃ P : List F,
      affineMcaAccepts D S (d + 1) (A + 1) (f, g) ch.1 P = true ∧
      ringDot P kernel = CommRingOps.add e_f
        (CommRingOps.add
          (CommRingOps.mul ((prodPool S).get ch).1 e_g)
          (CommRingOps.mul ((prodPool S).get ch).2 s_g))) :
    L.length ≤ badMca +
      (gsDecodeList (d + 1) A D f).length * (gsDecodeList d A D g).length * S.length := by
  let candF := gsDecodeList (d + 1) A D f
  let candG := gsDecodeList d A D g
  let pairsFG := candF.flatMap (fun pF => candG.map (fun pG => (pF, pG)))
  have hPairsLen : pairsFG.length = candF.length * candG.length := by
    dsimp only [pairsFG]
    clear hFlip hNd L hDecomp hInvalidG
    induction candF with
    | nil => simp
    | cons _ rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons, ih]
      rw [Nat.succ_mul, Nat.add_comm]
  let matchPair : GsUniPoly F × GsUniPoly F → Fin (prodPool S).length → Bool :=
    fun fg ch =>
      let p := (prodPool S).get ch
      decide (CommRingOps.add (ringDot fg.1.val kernel)
        (CommRingOps.add (CommRingOps.mul p.1 (ringDot fg.2.val kernel))
          (CommRingOps.mul p.2 (ringDot (shiftPoly fg.2.val) kernel))) =
        CommRingOps.add e_f
          (CommRingOps.add (CommRingOps.mul p.1 e_g) (CommRingOps.mul p.2 s_g)))
  let anyMatch : Fin (prodPool S).length → Bool := fun ch => pairsFG.any (fun fg => matchPair fg ch)
  have hSplit := length_filter_add_not anyMatch L
  -- Bound `L.filter anyMatch`: each `(pF, pG) ∈ pairsFG` has `ringDot pG.val kernel ≠ e_g`!
  have hMatchLe : (L.filter anyMatch).length ≤ pairsFG.length * S.length := by
    refine filter_any_length_le pairsFG matchPair L S.length ?_
    intro fg hfg
    rcases List.mem_flatMap.mp hfg with ⟨pF, _, hInG⟩
    rcases List.mem_map.mp hInG with ⟨pG, hpGMem, rfl⟩
    have hpGProps := (mem_gsDecodeList_iff g hD (by omega) pG).mp hpGMem
    have hNeEg : ringDot pG.val kernel ≠ e_g := hInvalidG pG.val hpGProps.1 hpGProps.2
    let Δ₀ := CommRingOps.sub (ringDot pF.val kernel) e_f
    let Δ_α := CommRingOps.sub (ringDot pG.val kernel) e_g
    let Δ_β := CommRingOps.sub (ringDot (shiftPoly pG.val) kernel) s_g
    have hΔαNe : Δ_α ≠ CommRingOps.zero :=
      fun h0 => hNeEg (LawfulCommRing.sub_eq_zero_iff.mp h0)
    have hMapNd : ((L.filter (matchPair (pF, pG))).map (fun ch => (prodPool S).get ch)).Nodup :=
      List.Pairwise.map _ (fun a b hab hEq => hab (nodup_get_inj (prodPool_nodup hS) hEq))
        (List.Pairwise.filter _ hNd)
    have hSubPool : ∀ p ∈ (L.filter (matchPair (pF, pG))).map (fun ch => (prodPool S).get ch),
        p ∈ (prodPool S).filter (fun p =>
          decide (CommRingOps.add Δ₀
            (CommRingOps.add (CommRingOps.mul p.1 Δ_α) (CommRingOps.mul p.2 Δ_β)) =
              CommRingOps.zero)) := by
      intro p hp
      rcases List.mem_map.mp hp with ⟨ch, hchF, rfl⟩
      have hEqCl : CommRingOps.add (ringDot pF.val kernel)
          (CommRingOps.add (CommRingOps.mul ((prodPool S).get ch).1 (ringDot pG.val kernel))
            (CommRingOps.mul ((prodPool S).get ch).2 (ringDot (shiftPoly pG.val) kernel))) =
          CommRingOps.add e_f
            (CommRingOps.add (CommRingOps.mul ((prodPool S).get ch).1 e_g)
              (CommRingOps.mul ((prodPool S).get ch).2 s_g)) :=
        of_decide_eq_true (List.mem_filter.mp hchF).2
      refine List.mem_filter.mpr ⟨list_get_mem (prodPool S) ch, decide_eq_true ?_⟩
      dsimp only [Δ₀, Δ_α, Δ_β]
      have hId : CommRingOps.add (CommRingOps.sub (ringDot pF.val kernel) e_f)
          (CommRingOps.add
            (CommRingOps.mul ((prodPool S).get ch).1 (CommRingOps.sub (ringDot pG.val kernel) e_g))
            (CommRingOps.mul ((prodPool S).get ch).2 (CommRingOps.sub (ringDot (shiftPoly pG.val) kernel) s_g))) =
        CommRingOps.sub
          (CommRingOps.add (ringDot pF.val kernel)
            (CommRingOps.add (CommRingOps.mul ((prodPool S).get ch).1 (ringDot pG.val kernel))
              (CommRingOps.mul ((prodPool S).get ch).2 (ringDot (shiftPoly pG.val) kernel))))
          (CommRingOps.add e_f
            (CommRingOps.add (CommRingOps.mul ((prodPool S).get ch).1 e_g)
              (CommRingOps.mul ((prodPool S).get ch).2 s_g))) := by
        constructive_ring
      rw [hId, hEqCl, LawfulCommRing.sub_self]
    have hLenMap := nodup_length_le_of_subset hMapNd hSubPool
    rw [List.length_map] at hLenMap
    exact Nat.le_trans hLenMap (absorbed_linear_claim_bad_pairs_le_card S hS Δ₀ Δ_α Δ_β (.inr hΔαNe))
  -- Bound `L.filter (!anyMatch ·)` via `hDecomp`:
  have hNonMatchLe : (L.filter (fun ch => !anyMatch ch)).length ≤ badMca := by
    refine hDecomp (f, g) (L.filter (fun ch => !anyMatch ch)) (List.Pairwise.filter _ hNd) ?_
    intro ch hch hNo
    rcases List.mem_filter.mp hch with ⟨hchL, hNotAny⟩
    refine hFlip ch hchL ?_
    rintro ⟨P, hPAcc, hPCl⟩
    refine hNo ⟨P, hPAcc, ?_⟩
    rintro ⟨F_poly, G_poly, ⟨hFLen, hGLen, hJoint⟩, hTrimEq⟩
    let pF : GsUniPoly F := GsUniPoly.ofCoeffs F_poly
    let pG : GsUniPoly F := GsUniPoly.ofCoeffs G_poly
    have hJointF : A ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs pF.val z = f z))).length := by
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
    have hJointG : A ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs pG.val z = g z))).length := by
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
      (mem_gsDecodeList_iff f hD hdA pF).mpr ⟨Nat.le_trans (trimPoly_length_le F_poly) hFLen, hJointF⟩
    have hpGMem : pG ∈ candG :=
      (mem_gsDecodeList_iff g hD (by omega) pG).mpr
        ⟨Nat.le_trans (trimPoly_length_le G_poly) hGLen, hJointG⟩
    have hMemPairs : (pF, pG) ∈ pairsFG :=
      List.mem_flatMap.mpr ⟨pF, hpFMem, List.mem_map.mpr ⟨pG, hpGMem, rfl⟩⟩
    have hMatchTrue : matchPair (pF, pG) ch = true := by
      dsimp only [matchPair]
      apply decide_eq_true
      change CommRingOps.add (ringDot (trimPoly F_poly) kernel)
        (CommRingOps.add
          (CommRingOps.mul ((prodPool S).get ch).1 (ringDot (trimPoly G_poly) kernel))
          (CommRingOps.mul ((prodPool S).get ch).2 (ringDot (shiftPoly (trimPoly G_poly)) kernel))) = _
      rw [ringDot_trimPoly_eq, ringDot_trimPoly_eq, ringDot_shiftPoly_trimPoly_eq]
      have hDotTrim := congrArg (fun u => ringDot u kernel) hTrimEq
      rw [ringDot_trimPoly_eq, ringDot_trimPoly_eq,
          ringDot_polyAddVar, ringDot_polyAddVar,
          ringDot_polyScaleVar, ringDot_polyScaleVar] at hDotTrim
      exact hDotTrim.symm.trans hPCl
    have hAnyTrue : anyMatch ch = true := List.any_eq_true.mpr ⟨(pF, pG), hMemPairs, hMatchTrue⟩
    rw [hAnyTrue] at hNotAny
    exact absurd hNotAny (by decide)
  rw [hPairsLen] at hMatchLe
  dsimp only [candF, candG] at hMatchLe
  omega

/-! ## §2. Sequential RBR State-Machine Engine & `Hem` Affine WHIR `RbrStateFunction` -/

/-- One round specification of a sequential public-coin IOP with a single state-liveness predicate. -/
structure SeqRoundSpec (Stmt State Msg : Type) (stateLive : Stmt → State → Prop) where
  chalCard : Nat
  h_pos : 0 < chalCard
  bad : Nat
  step : Stmt → State → Msg → Nat → State
  flip_bound :
    ∀ (x : Stmt) (st : State) (m : Msg),
      ¬ stateLive x st →
      ∀ (L : List (Fin chalCard)), L.Nodup →
        (∀ ch ∈ L, ¬¬ stateLive x (step x st m ch.1)) →
        L.length ≤ bad

/-- Execute a list of sequential round specifications along a transcript prefix. -/
@[expose] def runSeqSpecs {Stmt State Msg : Type} {stateLive : Stmt → State → Prop} :
    List (SeqRoundSpec Stmt State Msg stateLive) → Stmt → State → List (Msg × Nat) → State
  | [], _, st, _ => st
  | _, _, st, [] => st
  | sp :: restSpecs, x, st, (m, ch) :: restTr =>
    runSeqSpecs restSpecs x (sp.step x st m ch) restTr

private theorem runSeqSpecs_nil_tr {Stmt State Msg : Type} {stateLive : Stmt → State → Prop}
    (specs : List (SeqRoundSpec Stmt State Msg stateLive)) (x : Stmt) (st : State) :
    runSeqSpecs specs x st [] = st := by
  cases specs <;> rfl

/-- Build a `PublicCoinIop` from `specs : List (SeqRoundSpec ...)`. -/
def seqSpecsIop {Stmt State Msg : Type} {stateLive : Stmt → State → Prop}
    (specs : List (SeqRoundSpec Stmt State Msg stateLive))
    (inLang : Stmt → Prop)
    (verify : Stmt → List (Msg × Nat) → Bool) :
    PublicCoinIop Stmt Msg specs.length where
  challengeCard := fun r => (specs.get r).chalCard
  h_chal_pos := fun r => (specs.get r).h_pos
  inLang := inLang
  verify := verify

private theorem seqSpecs_flip_aux {Stmt State Msg : Type} {stateLive : Stmt → State → Prop} :
    ∀ (specs : List (SeqRoundSpec Stmt State Msg stateLive))
      (x : Stmt) (st : State) (r : Fin specs.length) (pref : List (Msg × Nat)) (m : Msg),
      pref.length = r.1 →
      ¬ stateLive x (runSeqSpecs specs x st pref) →
      ∀ (L : List (Fin (specs.get r).chalCard)), L.Nodup →
        (∀ ch ∈ L, ¬¬ stateLive x (runSeqSpecs specs x st (pref ++ [(m, ch.1)]))) →
        L.length ≤ (specs.get r).bad
  | [], _, _, r, _, _, _, _, _, _, _ => Fin.elim0 r
  | sp :: restSpecs, x, st, ⟨0, _⟩, pref, m, hLen, hDoomed, L, hNd, hL => by
    have hNil : pref = [] := List.eq_nil_of_length_eq_zero hLen
    subst hNil
    rw [runSeqSpecs_nil_tr] at hDoomed
    exact sp.flip_bound x st m hDoomed L hNd (fun ch hch => by
      have h := hL ch hch
      simpa only [List.nil_append, runSeqSpecs, runSeqSpecs_nil_tr] using h)
  | sp :: restSpecs, x, st, ⟨r' + 1, hr⟩, pref, m, hLen, hDoomed, L, hNd, hL => by
    cases pref with
    | nil => exact absurd hLen (Nat.succ_ne_zero r').symm
    | cons mc restPref =>
      exact seqSpecs_flip_aux restSpecs x (sp.step x st mc.1 mc.2)
        ⟨r', Nat.lt_of_succ_lt_succ hr⟩ restPref m (Nat.succ.inj hLen) hDoomed L hNd hL

/-- Assemble a genuine `RbrStateFunction` from any `specs : List (SeqRoundSpec ...)`. -/
def seqSpecsRbr {Stmt State Msg : Type} {stateLive : Stmt → State → Prop}
    (specs : List (SeqRoundSpec Stmt State Msg stateLive))
    (initState : Stmt → State)
    (inLang : Stmt → Prop)
    (verify : Stmt → List (Msg × Nat) → Bool)
    (hInit : ∀ x : Stmt, ¬ inLang x → ¬ stateLive x (initState x))
    (hAccept : ∀ (x : Stmt) (tr : List (Msg × Nat)),
      tr.length = specs.length → verify x tr = true →
        stateLive x (runSeqSpecs specs x (initState x) tr)) :
    RbrStateFunction (seqSpecsIop specs inLang verify) where
  Live := fun x tr => stateLive x (runSeqSpecs specs x (initState x) tr)
  badCard := fun r => (specs.get r).bad
  doomed_init := fun x hNot hLive => by
    rw [runSeqSpecs_nil_tr] at hLive
    exact hInit x hNot hLive
  accept_implies_live := hAccept
  round_flip_bound := fun x r pref m hLen hDoomed L hNd hL =>
    seqSpecs_flip_aux specs x (initState x) r pref m hLen hDoomed L hNd hL

/-- A state invariant preserved by every round step holds along every run. -/
theorem runSeqSpecs_inv {Stmt State Msg : Type} {stateLive : Stmt → State → Prop}
    (Inv : State → Prop) :
    ∀ (specs : List (SeqRoundSpec Stmt State Msg stateLive)) (x : Stmt) (st : State)
      (tr : List (Msg × Nat)),
      (∀ sp ∈ specs, ∀ (s : State) (m : Msg) (ch : Nat), Inv s → Inv (sp.step x s m ch)) →
      Inv st → Inv (runSeqSpecs specs x st tr)
  | [], _, _, tr, _, h => by cases tr <;> exact h
  | _ :: _, _, _, [], _, h => h
  | sp :: rest, x, st, (m, ch) :: tr, hStep, h =>
    runSeqSpecs_inv Inv rest x (sp.step x st m ch) tr
      (fun sp' hsp' => hStep sp' (.tail sp hsp')) (hStep sp (.head rest) st m ch h)

/-- **Counting form of the flip bound for a decided liveness.** If `liveB` decides `stateLive x`
    on every state satisfying a step-preserved invariant `Inv`, then from a prefix whose state
    is not live, the number of round-`r` challenges after which the state is live is at most
    the round's `bad`. -/
theorem seqSpecs_bool_flip_count {Stmt State Msg : Type} {stateLive : Stmt → State → Prop}
    (specs : List (SeqRoundSpec Stmt State Msg stateLive)) (x : Stmt)
    (Inv : State → Prop) (liveB : State → Bool)
    (hStep : ∀ sp ∈ specs, ∀ (s : State) (m : Msg) (ch : Nat), Inv s → Inv (sp.step x s m ch))
    (hDec : ∀ s : State, Inv s → (liveB s = true ↔ stateLive x s))
    (st : State) (hInv : Inv st) (r : Fin specs.length) (pref : List (Msg × Nat)) (m : Msg)
    (hLen : pref.length = r.1)
    (hDoomed : liveB (runSeqSpecs specs x st pref) = false) :
    qsum (specs.get r).chalCard (fun ch =>
      if liveB (runSeqSpecs specs x st (pref ++ [(m, ch.1)])) = true then 1 else 0) ≤
      (specs.get r).bad := by
  have hNot : ¬ stateLive x (runSeqSpecs specs x st pref) := fun hLive => by
    have h := (hDec _ (runSeqSpecs_inv Inv specs x st pref hStep hInv)).mpr hLive
    rw [hDoomed] at h
    exact Bool.false_ne_true h
  have hB := seqSpecs_flip_aux specs x st r pref m hLen hNot
    (finFilterList (specs.get r).chalCard
      (fun ch => liveB (runSeqSpecs specs x st (pref ++ [(m, ch.1)]))))
    (finFilterList_nodup _ _)
    (fun ch hch hN => hN ((hDec _ (runSeqSpecs_inv Inv specs x st _ hStep hInv)).mp
      (finFilterList_sound _ _ ch hch)))
  rw [finFilterList_length] at hB
  exact hB

/-- Sum over `Fin (a + b)` of a function of the index value, split at `a`. -/
theorem qsum_val_split (g : Nat → Nat) :
    ∀ (a b n : Nat), n = a + b →
      qsum n (fun i => g i.1) = qsum a (fun i => g i.1) + qsum b (fun i => g (a + i.1))
  | 0, b, n, h => by
    have hn : n = b := h.trans (Nat.zero_add b)
    subst hn
    rw [qsum_zero, Nat.zero_add]
    exact qsum_congr (fun i => by rw [Nat.zero_add])
  | a + 1, b, 0, h => by
    rw [Nat.succ_add] at h
    exact absurd h (Nat.succ_ne_zero _).symm
  | a + 1, b, n + 1, h => by
    have hn : n = a + b := by
      rw [Nat.succ_add] at h
      exact Nat.succ.inj h
    have ih := qsum_val_split (fun j => g (j + 1)) a b n hn
    rw [qsum_succ, qsum_succ]
    show g 0 + qsum n (fun i => g (i.1 + 1)) =
      g 0 + qsum a (fun i => g (i.1 + 1)) + qsum b (fun i => g (a + 1 + i.1))
    rw [ih, Nat.add_assoc]
    refine congrArg (fun t => g 0 + (qsum a (fun i => g (i.1 + 1)) + t)) ?_
    exact qsum_congr (fun i => by rw [Nat.add_right_comm])

/-- Reducing the index modulo `c` over `Fin (c * m)` repeats the sum over `Fin c` `m` times. -/
theorem qsum_val_mod (g : Nat → Nat) (c : Nat) :
    ∀ (m n : Nat), n = c * m →
      qsum n (fun i => g (i.1 % c)) = m * qsum c (fun i => g i.1)
  | 0, n, h => by
    have hn : n = 0 := h
    subst hn
    rw [qsum_zero, Nat.zero_mul]
  | m + 1, n, h => by
    have hSplit := qsum_val_split (fun v => g (v % c)) (c * m) c n (h.trans (Nat.mul_succ c m))
    rw [hSplit, qsum_val_mod g c m (c * m) rfl, Nat.succ_mul]
    refine congrArg (fun t => m * qsum c (fun i => g i.1) + t) ?_
    exact qsum_congr (fun i => by
      rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt i.2])

/-- Decode an outer transcript into a transcript of a sequential IOP: round `i` applies the
    `i`-th message decoder and reduces the challenge modulo the `i`-th challenge count. Rounds
    beyond either list are dropped. -/
def decodeRounds {Msg Msg' : Type} :
    List Nat → List (Msg' → Msg) → List (Msg' × Nat) → List (Msg × Nat)
  | c :: cs, d :: ds, (m, ch) :: tr => (d m, ch % c) :: decodeRounds cs ds tr
  | _, _, _ => []

theorem decodeRounds_nil_tr {Msg Msg' : Type} (cs : List Nat) (ds : List (Msg' → Msg)) :
    decodeRounds cs ds ([] : List (Msg' × Nat)) = [] := by
  cases cs with
  | nil => rfl
  | cons c cs => cases ds <;> rfl

theorem decodeRounds_cons {Msg Msg' : Type} (c : Nat) (cs : List Nat) (d : Msg' → Msg)
    (ds : List (Msg' → Msg)) (m : Msg') (ch : Nat) (tr : List (Msg' × Nat)) :
    decodeRounds (c :: cs) (d :: ds) ((m, ch) :: tr) = (d m, ch % c) :: decodeRounds cs ds tr := by
  rfl

theorem decodeRounds_length {Msg Msg' : Type} :
    ∀ (cs : List Nat) (ds : List (Msg' → Msg)) (tr : List (Msg' × Nat)),
      tr.length ≤ cs.length → cs.length ≤ ds.length → (decodeRounds cs ds tr).length = tr.length
  | cs, ds, [], _, _ => congrArg List.length (decodeRounds_nil_tr cs ds)
  | [], _, _ :: _, h, _ => absurd h (Nat.not_succ_le_zero _)
  | _ :: _, [], _ :: _, _, h => absurd h (Nat.not_succ_le_zero _)
  | c :: cs, d :: ds, (m, ch) :: tr, h1, h2 => by
    rw [decodeRounds_cons]
    exact congrArg Nat.succ (decodeRounds_length cs ds tr (Nat.le_of_succ_le_succ h1)
      (Nat.le_of_succ_le_succ h2))

/-- Appending one round to a transcript prefix appends one decoded round, whose message does
    not depend on the challenge and whose challenge is reduced modulo that round's count. -/
theorem decodeRounds_snoc {Msg Msg' : Type} :
    ∀ (cs : List Nat) (ds : List (Msg' → Msg)) (pref : List (Msg' × Nat)) (m : Msg')
      (hr : pref.length < cs.length), cs.length ≤ ds.length →
      ∃ m' : Msg, ∀ ch : Nat,
        decodeRounds cs ds (pref ++ [(m, ch)]) =
          decodeRounds cs ds pref ++ [(m', ch % cs.get ⟨pref.length, hr⟩)]
  | [], _, _, _, hr, _ => absurd hr (Nat.not_lt_zero _)
  | _ :: _, [], _, _, _, h => absurd h (Nat.not_succ_le_zero _)
  | c :: cs, d :: ds, [], m, _, _ => ⟨d m, fun ch => by
      show decodeRounds (c :: cs) (d :: ds) ((m, ch) :: []) = _
      rw [decodeRounds_cons, decodeRounds_nil_tr, decodeRounds_nil_tr]
      rfl⟩
  | c :: cs, d :: ds, (m₀, ch₀) :: pref, m, hr, h => by
    obtain ⟨m', hm'⟩ := decodeRounds_snoc cs ds pref m (Nat.lt_of_succ_lt_succ hr)
      (Nat.le_of_succ_le_succ h)
    refine ⟨m', fun ch => ?_⟩
    show decodeRounds (c :: cs) (d :: ds) ((m₀, ch₀) :: (pref ++ [(m, ch)])) = _
    rw [decodeRounds_cons, decodeRounds_cons, hm' ch]
    rfl

/-- **Flip count through a decoded transcript with a common challenge space.** Let the round
    `r` of `specs` have `c` challenges and let `N = c * mult`. If the outer transcript is
    decoded by `decodeRounds` with the challenge counts of `specs`, then from an outer prefix
    whose decoded state is not live, the number of outer challenges in `Fin N` after which the
    decoded state is live is at most `bad * mult`. -/
theorem seqSpecs_decoded_flip_count {Stmt State Msg Msg' : Type}
    {stateLive : Stmt → State → Prop}
    (specs : List (SeqRoundSpec Stmt State Msg stateLive)) (x : Stmt)
    (Inv : State → Prop) (liveB : State → Bool)
    (hStep : ∀ sp ∈ specs, ∀ (s : State) (m : Msg) (ch : Nat), Inv s → Inv (sp.step x s m ch))
    (hDec : ∀ s : State, Inv s → (liveB s = true ↔ stateLive x s))
    (st : State) (hInv : Inv st)
    (decs : List (Msg' → Msg)) (hDecs : specs.length ≤ decs.length)
    (r : Fin specs.length) (pref : List (Msg' × Nat)) (m : Msg')
    (hLen : pref.length = r.1) (N mult : Nat) (hN : N = (specs.get r).chalCard * mult)
    (hDoomed : liveB (runSeqSpecs specs x st
      (decodeRounds (specs.map (fun sp => sp.chalCard)) decs pref)) = false) :
    qsum N (fun ch =>
      if liveB (runSeqSpecs specs x st
        (decodeRounds (specs.map (fun sp => sp.chalCard)) decs (pref ++ [(m, ch.1)]))) = true
      then 1 else 0) ≤ (specs.get r).bad * mult := by
  have hCsLen : (specs.map (fun sp => sp.chalCard)).length = specs.length := List.length_map _
  have hr : pref.length < (specs.map (fun sp => sp.chalCard)).length := by
    rw [hCsLen, hLen]; exact r.2
  obtain ⟨m', hm'⟩ := decodeRounds_snoc (specs.map (fun sp => sp.chalCard)) decs pref m hr
    (by rw [hCsLen]; exact hDecs)
  have hCard : (specs.map (fun sp => sp.chalCard)).get ⟨pref.length, hr⟩ =
      (specs.get r).chalCard := by
    have hIdx : (⟨pref.length, hr⟩ : Fin (specs.map (fun sp => sp.chalCard)).length) =
        ⟨r.1, by rw [hCsLen]; exact r.2⟩ := Fin.ext hLen
    rw [hIdx]
    show (specs.map (fun sp => sp.chalCard))[r.1]'_ = (specs[r.1]'r.2).chalCard
    rw [List.getElem_map]
  have hPrefLen : (decodeRounds (specs.map (fun sp => sp.chalCard)) decs pref).length = r.1 := by
    rw [decodeRounds_length _ _ _ (Nat.le_of_lt hr) (by rw [hCsLen]; exact hDecs)]
    exact hLen
  have hBase := seqSpecs_bool_flip_count specs x Inv liveB hStep hDec st hInv r
    (decodeRounds (specs.map (fun sp => sp.chalCard)) decs pref) m' hPrefLen hDoomed
  have hEq : qsum N (fun ch =>
      if liveB (runSeqSpecs specs x st
        (decodeRounds (specs.map (fun sp => sp.chalCard)) decs (pref ++ [(m, ch.1)]))) = true
      then 1 else 0) =
      mult * qsum (specs.get r).chalCard (fun ch =>
        if liveB (runSeqSpecs specs x st
          (decodeRounds (specs.map (fun sp => sp.chalCard)) decs pref ++ [(m', ch.1)])) = true
        then 1 else 0) := by
    rw [← qsum_val_mod (fun v =>
      if liveB (runSeqSpecs specs x st
        (decodeRounds (specs.map (fun sp => sp.chalCard)) decs pref ++ [(m', v)])) = true
      then 1 else 0) (specs.get r).chalCard mult N hN]
    exact qsum_congr (fun ch => by rw [hm' ch.1, hCard])
  rw [hEq, Nat.mul_comm]
  exact Nat.mul_le_mul_right mult hBase

/-! ### §2.1 Concrete `Hem` Affine WHIR IOP Messages, Multi-Stage State & Verifier Bridge -/

/-- Decidable prover message type for the `Hem` Affine WHIR public-coin IOP (`0` function fields,
    so `[DecidableEq F] → DecidableEq (HemIopMsg F)` holds constructively for `SrScheduleTree`). -/
inductive HemIopMsg (F : Type := QuarticGoldilocks) where
  | msgCascade (absorbedShifts : List F)
  | msgStageFold (w₀ w₁ w₂ c_F c_G : F)
  | msgStageTable (stageTable : List F)
  | msgStageOod (ood₀ ood₁ : F)
  | msgFinal (finalCoeffs : List F)
  deriving DecidableEq, Repr

/-- Convert a finite committed oracle vector `tbl : List F` to an indexed oracle `Nat → F`. -/
def tableToOracle {F : Type} [CommRingOps F] (tbl : List F) (idx : Nat) : F :=
  tbl.getD idx CommRingOps.zero

theorem tableToOracle_apply {F : Type} [CommRingOps F] (tbl : List F) (idx : Nat) :
    tableToOracle tbl idx = tbl.getD idx CommRingOps.zero := by unfold tableToOracle; rfl

/-- Decode base-`B` challenge digits of length `m` from a single challenge `ch : Nat`. -/
def decodeBaseDigits (B : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | m + 1, ch => (ch % B) :: decodeBaseDigits B m (ch / B)

theorem decodeBaseDigits_length (B : Nat) : ∀ (m ch : Nat), (decodeBaseDigits B m ch).length = m
  | 0, _ => rfl
  | m + 1, ch => congrArg Nat.succ (decodeBaseDigits_length B m (ch / B))

/-- Map base-`|prodPool S|` challenge `ch` into `m` cascade weight pairs in `S × S`. -/
def decodeCascadeWeights {F : Type} [CommRingOps F] (S : List F) (m ch : Nat) : List (F × F) :=
  (decodeBaseDigits (prodPool S).length m ch).map
    (fun c => (prodPool S).getD c (CommRingOps.zero, CommRingOps.zero))

theorem decodeCascadeWeights_length {F : Type} [CommRingOps F] (S : List F) (m ch : Nat) :
    (decodeCascadeWeights S m ch).length = m := by
  unfold decodeCascadeWeights
  rw [List.length_map, decodeBaseDigits_length]

/-- Decode a 4-tuple `(φ, θ, α, β) ∈ S^4` from `ch : Nat`. -/
def decodeQuadChallenge {F : Type} [CommRingOps F] (S : List F) (ch : Nat) : F × F × F × F :=
  let M := S.length
  let iφ := ch % M
  let r1 := ch / M
  let iθ := r1 % M
  let r2 := r1 / M
  let iα := r2 % M
  let iβ := (r2 / M) % M
  (S.getD iφ CommRingOps.zero, S.getD iθ CommRingOps.zero,
   S.getD iα CommRingOps.zero, S.getD iβ CommRingOps.zero)

/-- Decode a pair `(z₀, z₁) ∈ S^2` from `ch : Nat`. -/
def decodePairChallenge {F : Type} [CommRingOps F] (S : List F) (ch : Nat) : F × F :=
  let M := S.length
  (S.getD (ch % M) CommRingOps.zero, S.getD ((ch / M) % M) CommRingOps.zero)

/-- Coset-folded virtual oracle from `curOracle` (`curDom` of even/odd pairs `(x, -x)`) onto `foldDom`. -/
def hemVirtualFoldOracle {F : Type} [LawfulField F]
    (θ α β : F) (curDom foldDom : List F) (curOracle : Nat → F) (idx : Nat) : F :=
  let two := CommRingOps.add CommRingOps.one CommRingOps.one
  let x := curDom.getD (2 * idx) CommRingOps.one
  let y := foldDom.getD idx CommRingOps.zero
  let a := curOracle (2 * idx)
  let b := curOracle (2 * idx + 1)
  let fE := CommRingOps.mul (LawfulField.inv two) (CommRingOps.add a b)
  let fO := CommRingOps.mul (LawfulField.inv (CommRingOps.mul two x)) (CommRingOps.sub a b)
  let hComb := CommRingOps.add fE (CommRingOps.mul θ fO)
  CommRingOps.add fO (CommRingOps.mul (CommRingOps.add α (CommRingOps.mul β y)) hComb)

/-- Parameter certificate for the single-batch, zero-fold cascade IOP below. -/
structure HemCascadeRbrCert (S : List QuarticGoldilocks)
    (domPts : List QuarticGoldilocks) (d₀ A₀ badMca listG : Nat) : Prop where
  dom_nodup : domPts.Nodup
  pool_nodup : S.Nodup
  deg_le_agree : d₀ + 2 ≤ A₀
  agree_succ_le_dom : A₀ + 1 ≤ domPts.length
  decomp_bound : AffineFoldDecompBound domPts S (d₀ + 1) (A₀ + 1) badMca
  gs_list_bound : ∀ word : QuarticGoldilocks → QuarticGoldilocks,
    (gsDecodeList d₀ A₀ domPts word).length ≤ listG

/-- Sequential state of the Round-0 Cascade + Final Opening `Hem` IOP (the exact 2-round core of
    `honest_cascade_completeness_poly`, restricted here to one batch oracle and no fold stages). -/
inductive HemCoreState where
  | init
  | postCascade (combOracle : Nat → QuarticGoldilocks) (combClaim : QuarticGoldilocks)
  | accepted (combOracle : Nat → QuarticGoldilocks) (combClaim : QuarticGoldilocks)
  | invalid

/-- Geometry of one binary fold stage from the running `(curDom, curDeg, curAgree)` onto the
    stage `st`. `curDom` lists antipodal pairs `(x, -x)` at indices `(2 i, 2 i + 1)` and
    `st.domainPts` lists their squares; a degree-`≤ curDeg` polynomial splits into two halves of
    degree `≤ st.degBound - 1`; and two separate agreements `≥ st.minAgree - 1` of the halves
    intersect in enough points to lift to `curAgree` agreements on `curDom`. -/
@[expose, reducible] def HemFoldStageGeom (curDom : List QuarticGoldilocks) (curDeg curAgree : Nat)
    (st : HemWhirStageSpec QuarticGoldilocks) : Prop :=
  curDom.Nodup ∧ st.domainPts.Nodup ∧
  curDom.length = 2 * st.domainPts.length ∧
  (∀ idx : Nat, idx < st.domainPts.length →
    curDom.getD (2 * idx) CommRingOps.one ≠ CommRingOps.zero ∧
    curDom.getD (2 * idx + 1) CommRingOps.zero =
      CommRingOps.neg (curDom.getD (2 * idx) CommRingOps.one) ∧
    st.domainPts.getD idx CommRingOps.zero =
      CommRingOps.mul (curDom.getD (2 * idx) CommRingOps.one)
        (curDom.getD (2 * idx) CommRingOps.one)) ∧
  1 ≤ st.degBound ∧ 2 * st.degBound ≤ curDeg + 1 ∧
  st.degBound + 2 ≤ st.minAgree ∧ st.minAgree ≤ st.domainPts.length ∧
  curAgree + 2 * st.domainPts.length + 4 ≤ 4 * st.minAgree

/-- Per-stage well-formedness of an arbitrary-length fold-stage list: every stage satisfies
    `HemFoldStageGeom` against the geometry left by its predecessor. -/
@[expose] def HemStageChainWellFormed :
    List QuarticGoldilocks → Nat → Nat → List (HemWhirStageSpec QuarticGoldilocks) → Prop
  | _, _, _, [] => True
  | curDom, curDeg, curAgree, st :: rest =>
    HemFoldStageGeom curDom curDeg curAgree st ∧
      HemStageChainWellFormed st.domainPts st.degBound st.minAgree rest

theorem hemStageChainWellFormed_nil (curDom : List QuarticGoldilocks) (curDeg curAgree : Nat) :
    HemStageChainWellFormed curDom curDeg curAgree [] := True.intro

theorem hemStageChainWellFormed_cons_iff (curDom : List QuarticGoldilocks) (curDeg curAgree : Nat)
    (st : HemWhirStageSpec QuarticGoldilocks) (rest : List (HemWhirStageSpec QuarticGoldilocks)) :
    HemStageChainWellFormed curDom curDeg curAgree (st :: rest) ↔
      (HemFoldStageGeom curDom curDeg curAgree st ∧
        HemStageChainWellFormed st.domainPts st.degBound st.minAgree rest) := Iff.rfl

/-- Well-formedness of a `HemWhirInstance` of batch size `m` with an arbitrary-length list of
    fold stages: the cascade leaves degree `d₀ + 1` and agreement `A₀ + 1` on `domPts`, and the
    stages chain from there (`HemStageChainWellFormed`). With `inst.stages = []` the chain
    condition is `True`, which is the direct cascade-to-final case. -/
@[expose] def WellFormedHemCascadeInstance (m : Nat) (domPts : List QuarticGoldilocks) (d₀ A₀ : Nat)
    (inst : HemWhirInstance QuarticGoldilocks) : Prop :=
  (1 ≤ m ∧ m ≤ 16) ∧
  inst.batchOracles.length = m ∧
  inst.batchClaims.length = m ∧
  inst.initDomainPts = domPts ∧
  inst.initDegBound = d₀ ∧
  inst.initMinAgree = A₀ ∧
  HemStageChainWellFormed domPts (d₀ + 1) (A₀ + 1) inst.stages

/-- State liveness predicate for `HemCoreState`. -/
@[expose] def hemCoreLive (m : Nat) (domPts : List QuarticGoldilocks) (d₀ A₀ : Nat)
    (inst : HemWhirInstance QuarticGoldilocks) : HemCoreState → Prop
  | .init => WellFormedHemCascadeInstance m domPts d₀ A₀ inst ∧ HemStatementValid inst
  | .postCascade combOracle combClaim =>
    ∃ P : List QuarticGoldilocks,
      polyWitnessValid domPts (A₀ + 1) (d₀ + 1) combOracle inst.initKernel combClaim P = true
  | .accepted combOracle combClaim =>
    ∃ P : List QuarticGoldilocks,
      polyWitnessValid domPts (A₀ + 1) (d₀ + 1) combOracle inst.initKernel combClaim P = true
  | .invalid => False

/-- Constructive extractor finding the first invalid batch index `< batchOracles.length` when
    `HemBatchValid` fails (`0` classical choice: uses `gsDecodeList` decidability!). -/
def findInvalidBatchIdx (domPts : List QuarticGoldilocks) (A₀ d₀ : Nat)
    (kernel : List QuarticGoldilocks) :
    List (Nat → QuarticGoldilocks) → List QuarticGoldilocks → Option Nat
  | [], _ => none
  | _, [] => none
  | O :: os, e :: es =>
    let word := lookupDomOracle domPts O
    let hasWit := (gsDecodeList d₀ A₀ domPts word).any (fun P =>
      polyWitnessValid domPts A₀ d₀ O kernel e P.val)
    if hasWit = true then
      (findInvalidBatchIdx domPts A₀ d₀ kernel os es).map Nat.succ
    else
      some 0

private theorem findInvalidBatchIdx_complete
    (domPts : List QuarticGoldilocks) (A₀ d₀ : Nat) (kernel : List QuarticGoldilocks)
    (hDom : domPts.Nodup) (hdA : d₀ + 1 ≤ A₀) :
    ∀ (os : List (Nat → QuarticGoldilocks)) (es : List QuarticGoldilocks),
      os.length = es.length →
      ¬ HemBatchValid domPts A₀ d₀ kernel os es →
      ∃ i₀ : Nat, findInvalidBatchIdx domPts A₀ d₀ kernel os es = some i₀ ∧
        i₀ < os.length ∧
        (∀ G : List QuarticGoldilocks,
          polyWitnessValid domPts A₀ d₀ (os.getD i₀ (fun _ => CommRingOps.zero))
            kernel (es.getD i₀ CommRingOps.zero) G = false)
  | [], [], _, hNot => False.elim (hNot (HemBatchValid_nil_nil domPts A₀ d₀ kernel))
  | [], _ :: _, hLen, _ => absurd hLen (Nat.succ_ne_zero _).symm
  | _ :: _, [], hLen, _ => absurd hLen (Nat.succ_ne_zero _)
  | O :: os, e :: es, hLen, hNot => by
    unfold findInvalidBatchIdx
    dsimp only
    cases hHas : (gsDecodeList d₀ A₀ domPts (lookupDomOracle domPts O)).any
        (fun P => polyWitnessValid domPts A₀ d₀ O kernel e P.val)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨0, rfl, Nat.zero_lt_succ _, ?_⟩
      intro G
      simp only [List.getD, List.getElem?_cons_zero, Option.getD_some]
      cases hG : polyWitnessValid domPts A₀ d₀ O kernel e G
      · rfl
      · exfalso
        let word := lookupDomOracle domPts O
        rw [polyWitnessValid_def] at hG
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hG
        rcases hG with ⟨⟨hGLen, hGAg⟩, hGDot⟩
        rw [hemCosetAgreeCount_eq_filter_lookup domPts O G hDom] at hGAg
        let pG : GsUniPoly QuarticGoldilocks := GsUniPoly.ofCoeffs G
        have hpGAg : A₀ ≤ (domPts.filter (fun z =>
            decide (RoundPoly.evalCoeffs pG.val z = word z))).length := by
          have hEqF : domPts.filter (fun z => decide (RoundPoly.evalCoeffs pG.val z = word z)) =
              domPts.filter (fun z => decide (RoundPoly.evalCoeffs G z = word z)) :=
            congrArg (fun q => List.filter q domPts) (funext fun z => by
              show decide (RoundPoly.evalCoeffs (trimPoly G) z = word z) = _
              rw [evalCoeffs_trimPoly])
          rw [hEqF]; exact hGAg
        have hpGMem : pG ∈ gsDecodeList d₀ A₀ domPts word :=
          (mem_gsDecodeList_iff word hDom hdA pG).mpr
            ⟨Nat.le_trans (trimPoly_length_le G) hGLen, hpGAg⟩
        have hpGVal : polyWitnessValid domPts A₀ d₀ O kernel e pG.val = true := by
          rw [polyWitnessValid_def]
          rw [hemCosetAgreeCount_eq_filter_lookup domPts O pG.val hDom]
          have hpGLen : pG.val.length ≤ d₀ + 1 := Nat.le_trans (trimPoly_length_le G) hGLen
          have hpGDot : ringDot pG.val kernel = e := by
            change ringDot (trimPoly G) kernel = e
            rw [ringDot_trimPoly_eq]; exact hGDot
          dsimp only [word] at hpGAg
          simp only [hpGLen, hpGAg, hpGDot, decide_true, Bool.and_self]
        have hAnyTrue : (gsDecodeList d₀ A₀ domPts (lookupDomOracle domPts O)).any
            (fun P => polyWitnessValid domPts A₀ d₀ O kernel e P.val) = true :=
          List.any_eq_true.mpr ⟨pG, hpGMem, hpGVal⟩
        rw [hAnyTrue] at hHas
        exact Bool.noConfusion hHas
    · simp only [↓reduceIte]
      rcases List.any_eq_true.mp hHas with ⟨pW, _, hpWVal⟩
      have hNotRest : ¬ HemBatchValid domPts A₀ d₀ kernel os es :=
        fun hRest => hNot ((HemBatchValid_cons_cons_iff domPts A₀ d₀ kernel O os e es).mpr
          ⟨⟨pW.val, hpWVal⟩, hRest⟩)
      rcases findInvalidBatchIdx_complete domPts A₀ d₀ kernel hDom hdA os es
          (Nat.succ.inj hLen) hNotRest with ⟨j, hjEq, hjLt, hjInv⟩
      refine ⟨j + 1, by simp only [hjEq, Option.map], Nat.succ_lt_succ hjLt, ?_⟩
      intro G
      simp only [List.getD, List.getElem?_cons_succ] at hjInv ⊢
      exact hjInv G

/-- Single-batch (`m = 1`) cascade `SeqRoundSpec` using `claimFold_bad_pairs_bound` (`f = 0`,
    so `gsDecodeList (d₀ + 1) A₀ domPts 0` has length `1`: only the zero polynomial `[]`!). -/
private theorem gsDecodeList_zero_length_le_one (domPts : List QuarticGoldilocks)
    (d A : Nat) (hDom : domPts.Nodup) (hdA : d + 1 ≤ A) :
    (gsDecodeList d A domPts (fun _ => CommRingOps.zero)).length ≤ 1 := by
  generalize hC : gsDecodeList d A domPts (fun _ => CommRingOps.zero) = cands
  have hNd : cands.Nodup := hC ▸ gsDecodeList_nodup d A domPts (fun _ => CommRingOps.zero)
  rcases cands with _ | ⟨p₁, _ | ⟨p₂, rest⟩⟩
  · exact Nat.zero_le 1
  · exact Nat.le_refl 1
  · exfalso
    have hp₁Mem : p₁ ∈ gsDecodeList d A domPts (fun _ => CommRingOps.zero) := by
      rw [hC]; exact .head _
    have hp₂Mem : p₂ ∈ gsDecodeList d A domPts (fun _ => CommRingOps.zero) := by
      rw [hC]; exact .tail _ (.head _)
    have hp₁ := (mem_gsDecodeList_iff (fun _ => CommRingOps.zero) hDom hdA p₁).mp hp₁Mem
    have hp₂ := (mem_gsDecodeList_iff (fun _ => CommRingOps.zero) hDom hdA p₂).mp hp₂Mem
    -- Any `p` in `cands` agrees with `0` on `≥ A ≥ d + 1` points of `domPts`, so `p.val = trimPoly []`!
    have eqZero : ∀ (p : GsUniPoly QuarticGoldilocks),
        p.val.length ≤ d + 1 →
        A ≤ (domPts.filter (fun z => decide (RoundPoly.evalCoeffs p.val z = CommRingOps.zero))).length →
        p = GsUniPoly.ofCoeffs [] := by
      intro p hpLen hpAg
      have hTrim := trimPoly_eq_of_agree_on_nodup (Q := ([] : List QuarticGoldilocks))
        hpLen (Nat.zero_le (d + 1))
        (List.Pairwise.filter _ hDom) (Nat.le_trans hdA hpAg)
        (fun x hx => of_decide_eq_true (List.mem_filter.mp hx).2)
      apply UPoly.ext
      rw [← p.trimmed, hTrim]
      rfl
    have e1 := eqZero p₁ hp₁.1 hp₁.2
    have e2 := eqZero p₂ hp₂.1 hp₂.2
    exact (List.pairwise_cons.mp hNd).1 p₂ (.head _) (e1.trans e2.symm)

@[expose] def hemSingleCascadeStep (S domPts : List QuarticGoldilocks) (d₀ A₀ : Nat)
    (inst : HemWhirInstance QuarticGoldilocks) (st : HemCoreState)
    (m : HemIopMsg QuarticGoldilocks) (ch : Nat) : HemCoreState :=
  match st, m with
  | .init, .msgCascade [s₀] =>
    if decide (inst.batchOracles.length = 1 ∧ inst.batchClaims.length = 1 ∧
        inst.initDomainPts = domPts ∧ inst.initDegBound = d₀ ∧
        inst.initMinAgree = A₀ ∧ inst.stages = []) = true then
      let pair := (prodPool S).getD ch (CommRingOps.zero, CommRingOps.zero)
      let combClaim := evalCascadeClaim inst.batchClaims [s₀] [pair]
      let combOracle := evalCascadeOracle domPts inst.batchOracles [pair]
      .postCascade combOracle combClaim
    else
      .invalid
  | _, _ => .invalid

theorem hemSingleCascade_flip_bound
    (S domPts : List QuarticGoldilocks) (d₀ A₀ badMca listG : Nat)
    (cert : HemCascadeRbrCert S domPts d₀ A₀ badMca listG)
    (inst : HemWhirInstance QuarticGoldilocks) (st : HemCoreState)
    (m : HemIopMsg QuarticGoldilocks)
    (hDoomed : ¬ hemCoreLive 1 domPts d₀ A₀ inst st)
    (L : List (Fin (prodPool S).length)) (hNd : L.Nodup)
    (hL : ∀ ch ∈ L, ¬¬ hemCoreLive 1 domPts d₀ A₀ inst
      (hemSingleCascadeStep S domPts d₀ A₀ inst st m ch.1)) :
    L.length ≤ badMca + 1 * listG * S.length := by
  cases st with
  | postCascade _ _ =>
    cases L with
    | nil => exact Nat.zero_le _
    | cons ch _ => exact False.elim (hL ch (.head _) id)
  | accepted _ _ =>
    cases L with
    | nil => exact Nat.zero_le _
    | cons ch _ => exact False.elim (hL ch (.head _) id)
  | invalid =>
    cases L with
    | nil => exact Nat.zero_le _
    | cons ch _ => exact False.elim (hL ch (.head _) id)
  | init =>
    rcases m with ⟨_ | ⟨s₀, _ | _⟩⟩ | _ | _ | _ | _
    · cases L with
      | nil => exact Nat.zero_le _
      | cons ch _ => exact False.elim (hL ch (.head _) id)
    · by_cases hWfDec : (inst.batchOracles.length = 1 ∧ inst.batchClaims.length = 1 ∧
          inst.initDomainPts = domPts ∧ inst.initDegBound = d₀ ∧
          inst.initMinAgree = A₀ ∧ inst.stages = [])
      · have hStepEq : ∀ ch : Fin (prodPool S).length,
            hemSingleCascadeStep S domPts d₀ A₀ inst .init (.msgCascade [s₀]) ch.1 =
              .postCascade
                (evalCascadeOracle domPts inst.batchOracles [(prodPool S).get ch])
                (evalCascadeClaim inst.batchClaims [s₀] [(prodPool S).get ch]) := by
          intro ch
          unfold hemSingleCascadeStep
          rw [decide_eq_true hWfDec, list_getD_eq_get (prodPool S) _ ch]
          rfl
        have hL' : ∀ ch ∈ L, ¬¬ hemCoreLive 1 domPts d₀ A₀ inst
            (.postCascade
              (evalCascadeOracle domPts inst.batchOracles [(prodPool S).get ch])
              (evalCascadeClaim inst.batchClaims [s₀] [(prodPool S).get ch])) := by
          intro ch hch
          have h := hL ch hch
          rwa [hStepEq ch] at h
        clear hL hStepEq
        rcases hWfDec with ⟨hOLen, hCLen, hDomEq, hDegEq, hAgEq, hStEq⟩
        have hWf : WellFormedHemCascadeInstance 1 domPts d₀ A₀ inst :=
          ⟨⟨Nat.le_refl 1, Nat.le_add_right 1 15⟩, hOLen, hCLen, hDomEq, hDegEq, hAgEq,
            hStEq ▸ hemStageChainWellFormed_nil domPts (d₀ + 1) (A₀ + 1)⟩
        have hInvalidStmt : ¬ HemStatementValid inst := fun hV => hDoomed ⟨hWf, hV⟩
        rcases inst with ⟨os, es, iDom, iDeg, iAg, kernel, iSt⟩
        dsimp only at hOLen hCLen hDomEq hDegEq hAgEq hStEq hL'
        clear hWf hDoomed
        subst iDom; subst iDeg; subst iAg; subst iSt
        rcases os with _ | ⟨O₀, _ | _⟩
        · cases hOLen
        · rcases es with _ | ⟨e₀, _ | _⟩
          · cases hCLen
          · have hNotBatch : ¬ HemBatchValid domPts A₀ d₀ kernel [O₀] [e₀] :=
              fun hb => hInvalidStmt ((HemStatementValid_iff _).mpr
                ⟨⟨Nat.le_refl 1, Nat.le_add_right 1 15⟩, hb⟩)
            have hdA1 : d₀ + 1 ≤ A₀ := Nat.le_of_succ_le cert.deg_le_agree
            rcases findInvalidBatchIdx_complete domPts A₀ d₀ kernel cert.dom_nodup
                hdA1 [O₀] [e₀] rfl hNotBatch with ⟨i₀, _, hi₀Lt, hi₀Inv⟩
            have hi₀0 : i₀ = 0 := by omega
            subst hi₀0
            simp only [List.getD, List.getElem?_cons_zero, Option.getD_some] at hi₀Inv
            let gWord := lookupDomOracle domPts O₀
            have hInvalidG : ∀ G : List QuarticGoldilocks, G.length ≤ d₀ + 1 →
                A₀ ≤ (domPts.filter (fun z => decide (RoundPoly.evalCoeffs G z = gWord z))).length →
                ringDot G kernel ≠ e₀ := by
              intro G hGLen hGAg hGDot
              have hVal : polyWitnessValid domPts A₀ d₀ O₀ kernel e₀ G = true := by
                rw [polyWitnessValid_def]
                rw [hemCosetAgreeCount_eq_filter_lookup domPts O₀ G cert.dom_nodup]
                dsimp only [gWord] at hGAg
                simp only [hGLen, hGAg, hGDot, decide_true, Bool.and_self]
              rw [hi₀Inv G] at hVal
              exact Bool.noConfusion hVal
            have hBound := claimFold_bad_pairs_bound domPts S kernel d₀ A₀ badMca
              (fun _ => CommRingOps.zero) gWord CommRingOps.zero e₀ s₀
              cert.dom_nodup cert.pool_nodup cert.deg_le_agree cert.decomp_bound hInvalidG L hNd
              (fun ch hch hNo => by
                refine hL' ch hch (fun hLive => hNo ?_)
                rcases hLive with ⟨P, hP⟩
                rw [polyWitnessValid_def] at hP
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
                rcases hP with ⟨⟨hPLen, hPAg⟩, hPDot⟩
                rw [hemCosetAgreeCount_eq_filter_lookup domPts _ P cert.dom_nodup] at hPAg
                refine ⟨P, ?_, ?_⟩
                · unfold affineMcaAccepts
                  rw [list_getD_eq_get (prodPool S) _ ch]
                  simp only [ch.2, hPLen, decide_true, Bool.true_and]
                  have hEqFilt : domPts.filter (fun z =>
                      decide (RoundPoly.evalCoeffs P z =
                        CommRingOps.add CommRingOps.zero
                          (CommRingOps.mul (CommRingOps.add ((prodPool S).get ch).1
                            (CommRingOps.mul ((prodPool S).get ch).2 z)) (gWord z)))) =
                      domPts.filter (fun z =>
                        decide (RoundPoly.evalCoeffs P z =
                          lookupDomOracle domPts
                            (evalCascadeOracle domPts [O₀] [(prodPool S).get ch]) z)) := by
                    have hMemCongr : ∀ (xs : List QuarticGoldilocks),
                        (∀ z ∈ xs, z ∈ domPts) →
                        xs.filter (fun z =>
                          decide (RoundPoly.evalCoeffs P z =
                            CommRingOps.add CommRingOps.zero
                              (CommRingOps.mul (CommRingOps.add ((prodPool S).get ch).1
                                (CommRingOps.mul ((prodPool S).get ch).2 z)) (gWord z)))) =
                        xs.filter (fun z =>
                          decide (RoundPoly.evalCoeffs P z =
                            lookupDomOracle domPts
                              (evalCascadeOracle domPts [O₀] [(prodPool S).get ch]) z)) := by
                      intro xs hSub
                      induction xs with
                      | nil => rfl
                      | cons z zs ih =>
                        rcases List.getElem?_of_mem (hSub z (.head zs)) with ⟨idx, hIdx⟩
                        have hLt : idx < domPts.length := by
                          by_cases h : idx < domPts.length
                          · exact h
                          · rw [List.getElem?_eq_none (Nat.le_of_not_lt h)] at hIdx
                            cases hIdx
                        have hGetEq : domPts.get ⟨idx, hLt⟩ = z := by
                          rw [List.getElem?_eq_getElem hLt] at hIdx
                          exact Option.some.inj hIdx
                        have hValEq :
                            lookupDomOracle domPts
                              (evalCascadeOracle domPts [O₀] [(prodPool S).get ch]) z =
                            CommRingOps.add CommRingOps.zero
                              (CommRingOps.mul (CommRingOps.add ((prodPool S).get ch).1
                                (CommRingOps.mul ((prodPool S).get ch).2 z)) (gWord z)) := by
                          rw [← hGetEq, lookupDomOracle_get domPts _ cert.dom_nodup ⟨idx, hLt⟩]
                          rw [evalCascadeOracle_cons, evalCascadeOracle_nil]
                          dsimp only [gWord]
                          rw [list_getD_eq_get domPts CommRingOps.zero ⟨idx, hLt⟩,
                              lookupDomOracle_get domPts O₀ cert.dom_nodup ⟨idx, hLt⟩,
                              LawfulCommRing.add_zero, LawfulCommRing.zero_add]
                        simp only [List.filter_cons, hValEq,
                          ih (fun y hy => hSub y (.tail z hy))]
                    exact hMemCongr domPts (fun _ h => h)
                  rw [hEqFilt]
                  exact decide_eq_true hPAg
                · rw [evalCascadeClaim_cons, evalCascadeClaim_nil] at hPDot
                  rw [hPDot]
                  constructive_ring)
            have hZLen : (gsDecodeList (d₀ + 1) A₀ domPts (fun _ => CommRingOps.zero)).length ≤ 1 :=
              gsDecodeList_zero_length_le_one domPts (d₀ + 1) A₀ cert.dom_nodup cert.deg_le_agree
            have hGLen : (gsDecodeList d₀ A₀ domPts gWord).length ≤ listG := cert.gs_list_bound gWord
            have hProdLe :
                (gsDecodeList (d₀ + 1) A₀ domPts (fun _ => CommRingOps.zero)).length *
                  (gsDecodeList d₀ A₀ domPts gWord).length * S.length ≤
                1 * listG * S.length :=
              Nat.mul_le_mul_right S.length (Nat.mul_le_mul hZLen hGLen)
            exact Nat.le_trans hBound (Nat.add_le_add_left hProdLe badMca)
          · cases hCLen
        · cases hOLen
      · cases L with
        | nil => exact Nat.zero_le _
        | cons ch _ =>
          exfalso
          refine hL ch (.head _) ?_
          unfold hemSingleCascadeStep
          rw [decide_eq_false hWfDec]
          exact id
    · cases L with
      | nil => exact Nat.zero_le _
      | cons ch _ => exact False.elim (hL ch (.head _) id)
    · cases L with
      | nil => exact Nat.zero_le _
      | cons ch _ => exact False.elim (hL ch (.head _) id)
    · cases L with
      | nil => exact Nat.zero_le _
      | cons ch _ => exact False.elim (hL ch (.head _) id)
    · cases L with
      | nil => exact Nat.zero_le _
      | cons ch _ => exact False.elim (hL ch (.head _) id)
    · cases L with
      | nil => exact Nat.zero_le _
      | cons ch _ => exact False.elim (hL ch (.head _) id)

/-- Round-0 single-batch cascade `SeqRoundSpec`: flips on at most `badMca + listG * |S|` out of `|S|^2`. -/
def hemSingleCascadeRoundSpec (S : List QuarticGoldilocks) (hSpos : 0 < S.length)
    (domPts : List QuarticGoldilocks) (d₀ A₀ badMca listG : Nat)
    (cert : HemCascadeRbrCert S domPts d₀ A₀ badMca listG) :
    SeqRoundSpec (HemWhirInstance QuarticGoldilocks) HemCoreState
      (HemIopMsg QuarticGoldilocks) (hemCoreLive 1 domPts d₀ A₀) where
  chalCard := (prodPool S).length
  h_pos := by rw [prodPool_length]; exact Nat.mul_pos hSpos hSpos
  bad := badMca + 1 * listG * S.length
  step := hemSingleCascadeStep S domPts d₀ A₀
  flip_bound := hemSingleCascade_flip_bound S domPts d₀ A₀ badMca listG cert

/-- Round-1 final polynomial opening `SeqRoundSpec`: deterministic (`bad = 0`, `chalCard = 1`). -/
def hemFinalOpenRoundSpec (domPts : List QuarticGoldilocks) (d₀ A₀ : Nat) :
    SeqRoundSpec (HemWhirInstance QuarticGoldilocks) HemCoreState
      (HemIopMsg QuarticGoldilocks) (hemCoreLive 1 domPts d₀ A₀) where
  chalCard := 1
  h_pos := Nat.zero_lt_one
  bad := 0
  step := fun inst st m _ =>
    match st, m with
    | .postCascade combOracle combClaim, .msgFinal finalCoeffs =>
      if polyWitnessValid domPts (A₀ + 1) (d₀ + 1) combOracle inst.initKernel combClaim finalCoeffs = true then
        .accepted combOracle combClaim
      else
        .invalid
    | _, _ => .invalid
  flip_bound := by
    intro inst st m hDoomed L _ hL
    cases L with
    | nil => exact Nat.le_refl 0
    | cons ch _ =>
      exfalso
      refine hL ch (.head _) ?_
      cases st with
      | init => exact id
      | accepted _ _ => exact id
      | invalid => exact id
      | postCascade combOracle combClaim =>
        cases m with
        | msgCascade _ => exact id
        | msgStageFold _ _ _ _ _ => exact id
        | msgStageTable _ => exact id
        | msgStageOod _ _ => exact id
        | msgFinal finalCoeffs =>
          cases hv : polyWitnessValid domPts (A₀ + 1) (d₀ + 1)
              combOracle inst.initKernel combClaim finalCoeffs
          · simp only [hv, Bool.false_eq_true, ↓reduceIte, hemCoreLive]; exact id
          · simp only [hv, ↓reduceIte, hemCoreLive]
            intro _
            exact hDoomed ⟨finalCoeffs, hv⟩

/-- Assemble a `List (HemTranscriptRound QuarticGoldilocks)` from an IOP transcript `tr`
    (`0` prover candidate hints: `cascadeDecoded` is populated directly from `[finalCoeffs]`). -/
def assembleHemCoreTranscript (S : List QuarticGoldilocks) :
    List (HemIopMsg QuarticGoldilocks × Nat) → List (HemTranscriptRound QuarticGoldilocks)
  | [(.msgCascade shifts, ch₀), (.msgFinal finalCoeffs, _)] =>
    let pair := (prodPool S).getD ch₀ (CommRingOps.zero, CommRingOps.zero)
    [.cascade shifts [pair] [finalCoeffs], .finalQuery finalCoeffs]
  | _ => []

/-- Succinct verifier for the 2-round `Hem` Affine WHIR IOP, checking `finalCoeffs` on the first
    `A₀ + 1` points of `domPts` (`List.range (A₀ + 1)`) and verifying `verifyHemAffineWhir`. -/
def verifyHemCoreIop (S : List QuarticGoldilocks) (domPts : List QuarticGoldilocks)
    (d₀ A₀ : Nat) (inst : HemWhirInstance QuarticGoldilocks)
    (tr : List (HemIopMsg QuarticGoldilocks × Nat)) : Bool :=
  match tr with
  | [(m₀, ch₀), (m₁, _)] =>
    match m₀, m₁ with
    | .msgCascade [s₀], .msgFinal finalCoeffs =>
      decide (inst.batchOracles.length = 1 ∧ inst.batchClaims.length = 1 ∧
        inst.initDomainPts = domPts ∧ inst.initDegBound = d₀ ∧
        inst.initMinAgree = A₀ ∧ inst.stages = []) &&
      decide (ch₀ < (prodPool S).length) &&
      (let pair := (prodPool S).getD ch₀ (CommRingOps.zero, CommRingOps.zero)
       let combClaim := evalCascadeClaim inst.batchClaims [s₀] [pair]
       let combOracle := evalCascadeOracle domPts inst.batchOracles [pair]
       polyWitnessValid domPts (A₀ + 1) (d₀ + 1) combOracle inst.initKernel combClaim finalCoeffs) &&
      verifyHemAffineWhir inst (assembleHemCoreTranscript S tr)
    | _, _ => false
  | _ => false

/-- Public-coin IOP packaging `verifyHemAffineWhir` & `hemAffineWhirStateFunction` over `QuarticGoldilocks`. -/
def hemAffineWhirIop (S : List QuarticGoldilocks) (hSpos : 0 < S.length)
    (domPts : List QuarticGoldilocks) (d₀ A₀ badMca listG : Nat)
    (cert : HemCascadeRbrCert S domPts d₀ A₀ badMca listG) :
    PublicCoinIop (HemWhirInstance QuarticGoldilocks) (HemIopMsg QuarticGoldilocks) 2 :=
  seqSpecsIop
    [hemSingleCascadeRoundSpec S hSpos domPts d₀ A₀ badMca listG cert,
     hemFinalOpenRoundSpec domPts d₀ A₀]
    (fun inst => WellFormedHemCascadeInstance 1 domPts d₀ A₀ inst ∧ HemStatementValid inst)
    (verifyHemCoreIop S domPts d₀ A₀)

/-- **Verifier-Acceptance Bridge (`hemAffineWhirIop_accepts_implies_verifier`)**:
    Every IOP transcript `tr` accepted by `hemAffineWhirIop` yields an explicit `Hem` transcript
    `assembleHemCoreTranscript S tr` accepted by `verifyHemAffineWhir` AND live under
    `hemAffineWhirStateFunction`. -/
theorem hemAffineWhirIop_accepts_implies_verifier
    (S : List QuarticGoldilocks) (hSpos : 0 < S.length)
    (domPts : List QuarticGoldilocks) (d₀ A₀ badMca listG : Nat)
    (cert : HemCascadeRbrCert S domPts d₀ A₀ badMca listG)
    (inst : HemWhirInstance QuarticGoldilocks)
    (tr : List (HemIopMsg QuarticGoldilocks × Nat))
    (hVer : (hemAffineWhirIop S hSpos domPts d₀ A₀ badMca listG cert).verify inst tr = true) :
    verifyHemAffineWhir inst (assembleHemCoreTranscript S tr) = true ∧
    hemAffineWhirStateFunction inst (assembleHemCoreTranscript S tr) := by
  change verifyHemCoreIop S domPts d₀ A₀ inst tr = true at hVer
  rcases tr with _ | ⟨⟨m₀, ch₀⟩, _ | ⟨⟨m₁, ch₁⟩, _ | _⟩⟩
  · exact Bool.noConfusion hVer
  · exact Bool.noConfusion hVer
  · rcases m₀ with ⟨_ | ⟨s₀, _ | _⟩⟩ | _ | _ | _ | _ <;>
      try exact Bool.noConfusion hVer
    rcases m₁ with _ | _ | _ | _ | ⟨finalCoeffs⟩ <;>
      try exact Bool.noConfusion hVer
    unfold verifyHemCoreIop at hVer
    have hAff : verifyHemAffineWhir inst
        (assembleHemCoreTranscript S [(.msgCascade [s₀], ch₀), (.msgFinal finalCoeffs, ch₁)]) =
          true :=
      ((Bool.and_eq_true _ _).mp hVer).2
    exact ⟨hAff, hemAffineWhir_rbr_completeness_and_doomed_init.2.2.1 inst _ hAff⟩
  · exact Bool.noConfusion hVer

private theorem hemCoreAccept_implies_live
    (S : List QuarticGoldilocks) (hSpos : 0 < S.length)
    (domPts : List QuarticGoldilocks) (d₀ A₀ badMca listG : Nat)
    (cert : HemCascadeRbrCert S domPts d₀ A₀ badMca listG)
    (inst : HemWhirInstance QuarticGoldilocks)
    (tr : List (HemIopMsg QuarticGoldilocks × Nat))
    (_hLen : tr.length = 2)
    (hVer : verifyHemCoreIop S domPts d₀ A₀ inst tr = true) :
    hemCoreLive 1 domPts d₀ A₀ inst
      (runSeqSpecs
        [hemSingleCascadeRoundSpec S hSpos domPts d₀ A₀ badMca listG cert,
         hemFinalOpenRoundSpec domPts d₀ A₀]
        inst .init tr) := by
  rcases tr with _ | ⟨⟨m₀, ch₀⟩, _ | ⟨⟨m₁, ch₁⟩, _ | _⟩⟩
  · exact Bool.noConfusion hVer
  · exact Bool.noConfusion hVer
  · rcases m₀ with ⟨_ | ⟨s₀, _ | _⟩⟩ | _ | _ | _ | _ <;>
      try exact Bool.noConfusion hVer
    rcases m₁ with _ | _ | _ | _ | ⟨finalCoeffs⟩ <;>
      try exact Bool.noConfusion hVer
    unfold verifyHemCoreIop at hVer
    have hLeft3 := ((Bool.and_eq_true _ _).mp hVer).1
    have hPW := ((Bool.and_eq_true _ _).mp hLeft3).2
    have hLeft2 := ((Bool.and_eq_true _ _).mp hLeft3).1
    have hWfDec := ((Bool.and_eq_true _ _).mp hLeft2).1
    simp only [runSeqSpecs, hemSingleCascadeRoundSpec, hemSingleCascadeStep,
      hemFinalOpenRoundSpec, hWfDec, hPW, ↓reduceIte, hemCoreLive]
    exact ⟨finalCoeffs, hPW⟩
  · exact Bool.noConfusion hVer

/-- **Genuine `RbrStateFunction` for `hemAffineWhirIop` (`hemAffineWhirRbrOf`)**:
    Packages `Hem` Affine WHIR over `QuarticGoldilocks` as an `RbrStateFunction` parameterized by
    `HemCascadeRbrCert`, with Round-0 flip bound `badMca + listG * |S|` out of `|S|^2` and Round-1
    flip bound `0`. -/
def hemAffineWhirRbrOf (S : List QuarticGoldilocks) (hSpos : 0 < S.length)
    (domPts : List QuarticGoldilocks) (d₀ A₀ badMca listG : Nat)
    (cert : HemCascadeRbrCert S domPts d₀ A₀ badMca listG) :
    RbrStateFunction (hemAffineWhirIop S hSpos domPts d₀ A₀ badMca listG cert) :=
  seqSpecsRbr
    [hemSingleCascadeRoundSpec S hSpos domPts d₀ A₀ badMca listG cert,
     hemFinalOpenRoundSpec domPts d₀ A₀]
    (fun _ => .init)
    (fun inst => WellFormedHemCascadeInstance 1 domPts d₀ A₀ inst ∧ HemStatementValid inst)
    (verifyHemCoreIop S domPts d₀ A₀)
    (fun _ hNot hLive => hNot hLive)
    (hemCoreAccept_implies_live S hSpos domPts d₀ A₀ badMca listG cert)

/-- **Unconditional Welch–Berlekamp `RbrStateFunction` Specialization (`hemAffineWhirRbr_welch_berlekamp`)**:
    Instantiates `hemAffineWhirRbrOf` unconditionally in the Welch–Berlekamp regime (`3 (d₀ + 1) + 1 ≤ |D|`
    and `2 |D| + (d₀ + 1) + 1 < 3 (A₀ + 1)`, where unique decoding gives `listG = 1` via Sudan `m = 1`
    or overlap!). -/
theorem overlap_unique_decode_le_one (domPts : List QuarticGoldilocks) (d₀ A₀ : Nat)
    (hDom : domPts.Nodup) (hdA : d₀ + 1 ≤ A₀) (hOv : domPts.length + d₀ < 2 * A₀)
    (word : QuarticGoldilocks → QuarticGoldilocks) :
    (gsDecodeList d₀ A₀ domPts word).length ≤ 1 := by
  generalize hC : gsDecodeList d₀ A₀ domPts word = cands
  have hNd : cands.Nodup := hC ▸ gsDecodeList_nodup d₀ A₀ domPts word
  rcases cands with _ | ⟨p₁, _ | ⟨p₂, rest⟩⟩
  · exact Nat.zero_le 1
  · exact Nat.le_refl 1
  · exfalso
    have hp₁Mem : p₁ ∈ gsDecodeList d₀ A₀ domPts word := by rw [hC]; exact .head _
    have hp₂Mem : p₂ ∈ gsDecodeList d₀ A₀ domPts word := by rw [hC]; exact .tail _ (.head _)
    have hp₁ := (mem_gsDecodeList_iff word hDom hdA p₁).mp hp₁Mem
    have hp₂ := (mem_gsDecodeList_iff word hDom hdA p₂).mp hp₂Mem
    let q₁ : QuarticGoldilocks → Bool := fun z => decide (RoundPoly.evalCoeffs p₁.val z = word z)
    let q₂ : QuarticGoldilocks → Bool := fun z => decide (RoundPoly.evalCoeffs p₂.val z = word z)
    let U := domPts.filter (fun z => q₁ z && q₂ z)
    have hULen : d₀ + 1 ≤ U.length := by
      have h := filter_overlap_len q₁ q₂ domPts
      change (domPts.filter q₁).length + (domPts.filter q₂).length ≤ domPts.length + U.length at h
      have h1 : A₀ ≤ (domPts.filter q₁).length := hp₁.2
      have h2 : A₀ ≤ (domPts.filter q₂).length := hp₂.2
      omega
    have hTrim := trimPoly_eq_of_agree_on_nodup hp₁.1 hp₂.1 (List.Pairwise.filter _ hDom) hULen
      (fun x hx => by
        rcases (Bool.and_eq_true _ _).mp (List.mem_filter.mp hx).2 with ⟨e1, e2⟩
        exact (of_decide_eq_true e1).trans (of_decide_eq_true e2).symm)
    have hEq : p₁ = p₂ := UPoly.ext (p₁.trimmed.symm.trans (hTrim.trans p₂.trimmed))
    exact (List.pairwise_cons.mp hNd).1 p₂ (.head _) hEq

theorem hemWelchBerlekampCert (S domPts : List QuarticGoldilocks) (d₀ A₀ : Nat)
    (hDom : domPts.Nodup) (hS : S.Nodup)
    (hdA : d₀ + 2 ≤ A₀) (hAgDom : A₀ + 1 ≤ domPts.length)
    (hWB : 2 * domPts.length + (d₀ + 1) + 1 < 3 * (A₀ + 1)) :
    HemCascadeRbrCert S domPts d₀ A₀
      (Nat.max S.length (domPts.length * (domPts.length - 1) / 2)) 1 where
  dom_nodup := hDom
  pool_nodup := hS
  deg_le_agree := hdA
  agree_succ_le_dom := hAgDom
  decomp_bound := affineFoldDecompBound_welch_berlekamp domPts S (d₀ + 1) (A₀ + 1)
    hDom hS hAgDom hWB
  gs_list_bound := overlap_unique_decode_le_one domPts d₀ A₀ hDom (by omega) (by omega)

/-- **`[CWYZ26]` Johnson-Radius `RbrStateFunction` Specialization (`hemCwyz26JohnsonCert`)**:
    Plugs `cwyz26_affineFoldDecompBound_of_nonExcluded` and `gsDecodeList_length_le` directly into
    `HemCascadeRbrCert` at arbitrary list-decoding multiplicity `(m_gs, listG)`. -/
theorem hemCwyz26JohnsonCert (S domPts : List QuarticGoldilocks)
    (d₀ A₀ m Wx Dy rest m_gs listG : Nat)
    (hDom : domPts.Nodup) (hS : S.Nodup)
    (hdA : d₀ + 2 ≤ A₀) (hAgDom : A₀ + 1 ≤ domPts.length)
    (hCount : domPts.length * Poly3.triCount 1 m Dy m < Poly3.triCount (d₀ + 1) Wx Dy (Dy + 1))
    (hWA : Wx + Dy ≤ m * (A₀ + 1))
    (hRest : NonExcludedDecompBound domPts S (d₀ + 1) (A₀ + 1) m Wx Dy rest)
    (hGsDim : domPts.length * (m_gs * (m_gs + 1) / 2) < gsMonomialCount (m_gs * A₀) d₀ listG) :
    HemCascadeRbrCert S domPts d₀ A₀ (Dy + rest) listG where
  dom_nodup := hDom
  pool_nodup := hS
  deg_le_agree := hdA
  agree_succ_le_dom := hAgDom
  decomp_bound := cwyz26_affineFoldDecompBound_of_nonExcluded domPts S (d₀ + 1) (A₀ + 1)
    m Wx Dy rest hRest hDom hS hCount hWA
  gs_list_bound := fun word =>
    gsDecodeList_length_le domPts word d₀ A₀ listG m_gs hDom (by omega) hGsDim

/-- **Adaptive State-Restoration Soundness of the restricted cascade IOP
    (`hemAffineWhir_state_restoration_soundness`)**:
    For ANY well-formed false statement `¬ HemStatementValid inst` and ANY `T`-step adaptive
    rewinding attack tree `tree : SrScheduleTree ... sched`, the acceptance probability of
    `hemAffineWhirIop` is bounded by
    `srScheduleErrorSum (hemAffineWhirRbrOf ... cert) sched`. -/
theorem hemAffineWhir_state_restoration_soundness
    (S : List QuarticGoldilocks) (hSpos : 0 < S.length)
    (domPts : List QuarticGoldilocks) (d₀ A₀ badMca listG : Nat)
    (cert : HemCascadeRbrCert S domPts d₀ A₀ badMca listG)
    (inst : HemWhirInstance QuarticGoldilocks)
    (hInvalid : ¬ HemStatementValid inst)
    (sched : List (Fin 2))
    (tree : SrScheduleTree (hemAffineWhirIop S hSpos domPts d₀ A₀ badMca listG cert) sched) :
    RatBound.le
      (srTreeAcceptProb (hemAffineWhirIop S hSpos domPts d₀ A₀ badMca listG cert) tree inst)
      (srScheduleErrorSum (hemAffineWhirRbrOf S hSpos domPts d₀ A₀ badMca listG cert) sched) :=
  rbr_implies_state_restoration_soundness
    (hemAffineWhirRbrOf S hSpos domPts d₀ A₀ badMca listG cert)
    inst (fun h => hInvalid h.2) sched tree

/-! ## §3. Conditional QROM event accounting -/

/-- Conditional probability accounting for the transcript checker. The supplied RBR/query
    bounds and acceptance cover are obligations, not consequences proved here. In particular,
    `hRbrBound` uses the paper/profile inputs `hemV6FiveRoundRbrBounds`, whose stronger
    incidence constant and equal-degree/multistage lift are not furnished by the larger
    proved sliced binary-fold counts. `outTr` is
    unrestricted and does not encode a Fiat–Shamir transcript derivation. This lemma is useful
    only after an execution-specific reduction establishes all three event bounds and cover. -/
theorem hemAffineWhir_qrom_acceptance_bound_of_event_bounds
    {cardX cardAnc Q : Nat}
    (inst : HemWhirInstance QuarticGoldilocks)
    (A : QuantumAdv cardX 256 cardAnc Q)
    (outTr : (Fin cardX → BitVec 256) → Fin cardX → List (HemTranscriptRound QuarticGoldilocks))
    -- 1. Online Merkle extraction reduction (`QromMerkleOnlineExtraction`):
    (failMerkle : (Fin cardX → BitVec 256) → Fin cardX → Bool)
    (merkleProj : Fin (2 * 5) → Fin cardX → Fin cardX)
    (merkleTargets : Fin (2 * 5) → (Fin cardX → BitVec 256) → Fin cardX → List (BitVec 256))
    (hMerkleLocal : ∀ r O x ch, merkleTargets r (reprogramOracle O x ch) x = merkleTargets r O x)
    (hMerkleCard : ∀ r O x, (merkleTargets r O x).length ≤ (if r.1 % 2 = 0 then 1 else 2 * Q + 1))
    (hMerkleCover : ∀ H, QVec.queryMassOn (failMerkle H) (runQuantumAdv A H) ≤
      qsum (2 * 5) (fun r =>
        qromOrdinaryFlipMass A H (merkleProj r) (fun _ _ => true)
          (fun O x => listHasElem (O x) (merkleTargets r O x))))
    -- 2. RBR Fiat–Shamir challenge-round flips:
    (failRbr : (Fin cardX → BitVec 256) → Fin cardX → Bool)
    (hRbrBound :
      let norm := prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init
      RatBound.le
        ⟨uniformOracleSum 256 cardX (fun H => QVec.queryMassOn (failRbr H) (runQuantumAdv A H)),
          (2 ^ 256) ^ cardX * norm,
          Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos 256))
            (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
        (RatBound.sumList (hemV6FiveRoundRbrBounds.map (dfmRoundScale Q))))
    -- 3. Stage coset-query search bound:
    (failQuery : (Fin cardX → BitVec 256) → Fin cardX → Bool)
    (hQueryBound :
      let norm := prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init
      RatBound.le
        ⟨uniformOracleSum 256 cardX (fun H => QVec.queryMassOn (failQuery H) (runQuantumAdv A H)),
          (2 ^ 256) ^ cardX * norm,
          Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos 256))
            (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
        (RatBound.sumList (hemV6BciksJohnsonQueryBounds.map (quantumGroverGrindingBound Q))))
    -- 4. Supplied transcript-acceptance event cover:
    (hAcceptCover : ∀ H x,
      verifyHemAffineWhir inst (outTr H x) = true →
        failRbr H x = true ∨ failMerkle H x = true ∨ failQuery H x = true) :
    let norm := prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init
    let acceptProb : RatBound :=
      ⟨uniformOracleSum 256 cardX (fun H =>
          QVec.queryMassOn (fun x => verifyHemAffineWhir inst (outTr H x)) (runQuantumAdv A H)),
        (2 ^ 256) ^ cardX * norm,
        Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos 256))
          (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)⟩
    RatBound.le acceptProb
      (multiRoundFsQromCompilerBound Q 5 256
        hemV6FiveRoundRbrBounds hemV6BciksJohnsonQueryBounds) ∧
    (Q + 1 ≤ 2 ^ 40 → strictlyMoreThanBits 128 acceptProb ∧ atLeastBits 128 acceptProb) := by
  let norm := prefixScale A Q (Nat.le_refl Q) * QVec.stateNormSq A.init
  let Den := (2 ^ 256) ^ cardX * norm
  have hDenPos : 0 < Den :=
    Nat.mul_pos (Nat.pow_pos (Nat.two_pow_pos 256))
      (Nat.mul_pos (prefixScale_pos A Q (Nat.le_refl Q)) A.h_init_pos)
  have hMerkleBound :
      RatBound.le
        ⟨uniformOracleSum 256 cardX (fun H => QVec.queryMassOn (failMerkle H) (runQuantumAdv A H)),
          Den, hDenPos⟩
        (qromMerkleOnlineExtractBound 5 256 Q) :=
    qrom_unitary_multiRoot_merkle_extract_bound 5 A failMerkle merkleProj merkleTargets
      hMerkleLocal hMerkleCard hMerkleCover
  have hPointwise : ∀ H,
      QVec.queryMassOn (fun x => verifyHemAffineWhir inst (outTr H x)) (runQuantumAdv A H) ≤
        QVec.queryMassOn (failRbr H) (runQuantumAdv A H) +
        (QVec.queryMassOn (failMerkle H) (runQuantumAdv A H) +
         QVec.queryMassOn (failQuery H) (runQuantumAdv A H)) := by
    intro H
    simp only [QVec.queryMassOn_def]
    rw [← qsum_add, ← qsum_add]
    apply qsum_le_qsum; intro x
    by_cases hv : verifyHemAffineWhir inst (outTr H x) = true
    · have hCov := hAcceptCover H x hv
      simp only [hv, ↓reduceIte]
      cases h1 : failRbr H x <;> cases h2 : failMerkle H x <;> cases h3 : failQuery H x
      · rw [h1, h2, h3] at hCov
        rcases hCov with hc | hc | hc <;> exact Bool.noConfusion hc
      all_goals simp only [Bool.false_eq_true, ↓reduceIte]; omega
    · have hvf : verifyHemAffineWhir inst (outTr H x) = false := Bool.eq_false_iff.mpr hv
      simp only [hvf, Bool.false_eq_true, ↓reduceIte]
      exact Nat.zero_le _
  have hSum := uniformOracleSum_le 256 cardX _ _ hPointwise
  have hSplitSum : ∀ (n : Nat) (f g : (Fin n → BitVec 256) → Nat),
      uniformOracleSum 256 n (fun H => f H + g H) =
        uniformOracleSum 256 n f + uniformOracleSum 256 n g :=
    fun n f g => uniformOracleSum_add 256 n f g
  rw [hSplitSum, hSplitSum] at hSum
  let bR := RatBound.mk (uniformOracleSum 256 cardX (fun H => QVec.queryMassOn (failRbr H) (runQuantumAdv A H))) Den hDenPos
  let bM := RatBound.mk (uniformOracleSum 256 cardX (fun H => QVec.queryMassOn (failMerkle H) (runQuantumAdv A H))) Den hDenPos
  let bQ := RatBound.mk (uniformOracleSum 256 cardX (fun H => QVec.queryMassOn (failQuery H) (runQuantumAdv A H))) Den hDenPos
  have hSameDenAdd : ∀ (n1 n2 : Nat) (d : Nat) (hd : 0 < d),
      RatBound.le ⟨n1 + n2, d, hd⟩ (RatBound.add ⟨n1, d, hd⟩ ⟨n2, d, hd⟩) := by
    intro n1 n2 d hd
    unfold RatBound.le RatBound.add
    dsimp only
    rw [← Nat.add_mul, ← Nat.mul_assoc]
    exact Nat.le_refl _
  have hAccLeSum :
      RatBound.le
        ⟨uniformOracleSum 256 cardX (fun H =>
            QVec.queryMassOn (fun x => verifyHemAffineWhir inst (outTr H x)) (runQuantumAdv A H)),
          Den, hDenPos⟩
        (RatBound.add bR (RatBound.add bM bQ)) := by
    have h1 : RatBound.le
        ⟨uniformOracleSum 256 cardX (fun H =>
            QVec.queryMassOn (fun x => verifyHemAffineWhir inst (outTr H x)) (runQuantumAdv A H)),
          Den, hDenPos⟩
        ⟨bR.num + (bM.num + bQ.num), Den, hDenPos⟩ :=
      Nat.mul_le_mul_right Den hSum
    exact RatBound.le_trans h1
      (RatBound.le_trans (hSameDenAdd bR.num (bM.num + bQ.num) Den hDenPos)
        (RatBound.add_le_add (RatBound.le_refl bR) (hSameDenAdd bM.num bQ.num Den hDenPos)))
  have hCompLe :
      RatBound.le (RatBound.add bR (RatBound.add bM bQ))
        (multiRoundFsQromCompilerBound Q 5 256
          hemV6FiveRoundRbrBounds hemV6BciksJohnsonQueryBounds) :=
    RatBound.add_le_add hRbrBound (RatBound.add_le_add hMerkleBound hQueryBound)
  have hMain := RatBound.le_trans hAccLeSum hCompLe
  refine ⟨hMain, ?_⟩
  intro hQ
  have hBudget := (multiRoundFsQrom_budget_bound.2 Q hQ).1
  let A_num := uniformOracleSum 256 cardX (fun H =>
    QVec.queryMassOn (fun x => verifyHemAffineWhir inst (outTr H x)) (runQuantumAdv A H))
  let cB := multiRoundFsQromCompilerBound Q 5 256 hemV6FiveRoundRbrBounds hemV6BciksJohnsonQueryBounds
  have hMain' : A_num * cB.den ≤ cB.num * Den := hMain
  have hBudget' : cB.num * 2 ^ 128 < cB.den := hBudget
  unfold strictlyMoreThanBits atLeastBits
  dsimp only
  have hStrict : A_num * 2 ^ 128 < Den := by
    have h1 : A_num * 2 ^ 128 * cB.den ≤ cB.num * 2 ^ 128 * Den := by
      calc A_num * 2 ^ 128 * cB.den
          = (A_num * cB.den) * 2 ^ 128 := Nat.mul_right_comm A_num (2 ^ 128) cB.den
        _ ≤ (cB.num * Den) * 2 ^ 128 := Nat.mul_le_mul_right (2 ^ 128) hMain'
        _ = cB.num * 2 ^ 128 * Den := Nat.mul_right_comm cB.num Den (2 ^ 128)
    have h2 : cB.num * 2 ^ 128 * Den < cB.den * Den :=
      Nat.mul_lt_mul_of_pos_right hBudget' hDenPos
    have h3 : A_num * 2 ^ 128 * cB.den < Den * cB.den := by
      rw [Nat.mul_comm Den cB.den]
      exact Nat.lt_of_le_of_lt h1 h2
    if hLt : A_num * 2 ^ 128 < Den then
      exact hLt
    else
      exact False.elim (Nat.not_le_of_gt h3 (Nat.mul_le_mul_right cB.den (Nat.le_of_not_lt hLt)))
  exact ⟨hStrict, Nat.le_of_lt hStrict⟩

/-! ## §4. `#tooth` Mutation Guard, `#verify_inhabited` & `#verify_constructive` Audits -/

/-- `#tooth`: dropping cross-stage fold-coset queries (`verifyHemStages` on an unconstrained
    stage commitment) allows a doomed post-cascade state (`cascadeLive = false`) with a non-zero
    false claim `curClaim = 1` to pass `verifyHemStages` with probability `1` via `[α]`. -/
theorem tooth_unconstrained_stageOracle_accepts_false_claim :
    let st : HemWhirStageSpec QuarticGoldilocks :=
      { domainPts := [CommRingOps.zero]
        degBound := 0
        minAgree := 1
        listBound := 1
        queriedCosets := [] }
    let P_cheat : List QuarticGoldilocks := [CommRingOps.one]
    let stageOracle : Nat → QuarticGoldilocks := fun _ => CommRingOps.one
    verifyHemStages (fun _ => CommRingOps.zero) [CommRingOps.zero, CommRingOps.one] 1 2
      [CommRingOps.one, CommRingOps.zero] CommRingOps.one [st]
      [.stageFold stageOracle CommRingOps.one CommRingOps.zero CommRingOps.zero
          CommRingOps.zero CommRingOps.zero CommRingOps.zero CommRingOps.zero
          CommRingOps.one CommRingOps.zero CommRingOps.zero CommRingOps.zero
          CommRingOps.one CommRingOps.one [P_cheat],
       .finalQuery P_cheat] = true ∧
    ¬ (∃ P : List QuarticGoldilocks,
      polyWitnessValid [CommRingOps.zero, CommRingOps.one] 2 0
        (fun _ => CommRingOps.zero) [CommRingOps.one] CommRingOps.one P = true) := by
  intro st P_cheat stageOracle
  refine ⟨?_, ?_⟩
  · have hOne : ∀ z : QuarticGoldilocks,
        RoundPoly.evalCoeffs [CommRingOps.one] z = CommRingOps.one := by
      intro z
      show CommRingOps.add CommRingOps.one (CommRingOps.mul z CommRingOps.zero) =
        CommRingOps.one
      rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    have hK : hemKernelFold (CommRingOps.zero : QuarticGoldilocks)
        [CommRingOps.one, CommRingOps.zero] = [CommRingOps.one, CommRingOps.zero] := by
      rw [hemKernelFold_cons_cons, hemKernelFold_nil, LawfulCommRing.mul_zero,
        LawfulCommRing.add_zero]
    have hC : hemBridgeFoldClaim (CommRingOps.one : QuarticGoldilocks) CommRingOps.one
        CommRingOps.zero CommRingOps.zero CommRingOps.zero CommRingOps.zero CommRingOps.zero
        CommRingOps.zero CommRingOps.one CommRingOps.zero = CommRingOps.one := by
      rw [hemBridgeFoldClaim_def]
      constructive_ring
    have hDot : ringDot [(CommRingOps.one : QuarticGoldilocks)]
        [CommRingOps.one, CommRingOps.zero] = CommRingOps.one := by
      rw [ringDot_cons_cons, ringDot_zero_left, LawfulCommRing.mul_one, LawfulCommRing.add_zero]
    have hAg : hemCosetAgreeCount [(CommRingOps.zero : QuarticGoldilocks)]
        (fun _ => CommRingOps.one) [CommRingOps.one] = 1 := by
      rw [hemCosetAgreeCount_def]
      show qsum 1 _ = 1
      rw [qsum_succ, qsum_zero]
      simp only [hOne, ↓reduceIte]
    rw [verifyHemStages_cons_stageFold, verifyHemStages_nil_finalQuery, hK, hC]
    simp only [st, P_cheat, stageOracle, List.any_cons, List.any_nil, polyWitnessValid_def, hAg,
      hDot, hOne, checkQueriedCosets_nil, List.length_cons, List.length_nil, Nat.le_refl,
      decide_true, Bool.and_self, Bool.or_false]
    show (true && (true && checkQueriedCosets [(CommRingOps.zero : QuarticGoldilocks)]
      (fun _ => CommRingOps.one) [CommRingOps.one] [0])) = true
    rw [checkQueriedCosets_cons, checkQueriedCosets_nil, hOne]
    simp only [List.length_cons, List.length_nil, Nat.lt_add_one, decide_true, Bool.and_self]
  · rintro ⟨P, hP⟩
    apply hemFalseClaimInstance_invalid
    rw [HemStatementValid_iff, hemFalseClaimInstance_def]
    exact ⟨⟨Nat.le_refl 1, by decide⟩,
      (HemBatchValid_cons_cons_iff _ _ _ _ _ _ _ _).mpr
        ⟨⟨P, hP⟩, HemBatchValid_nil_nil _ _ _ _⟩⟩


private def qgOfNat (n : Nat) : QuarticGoldilocks := CRing.natCast n

private theorem qgOfNat_ne (a d : Nat) (h1 : 1 ≤ d) (hd : d < goldilocksPrime) :
    qgOfNat a ≠ qgOfNat (a + d) := by
  intro h
  unfold qgOfNat at h
  rw [CRing.natCast_add] at h
  apply QuarticGoldilocks.natCast_ne_zero d h1 hd
  have hId : ∀ x y : QuarticGoldilocks,
      y = CommRingOps.sub (CommRingOps.add x y) x := by
    intro x y
    constructive_ring
  rw [hId (CRing.natCast a) (CRing.natCast d), ← h, LawfulCommRing.sub_self]

private theorem qgRange_nodup : ∀ (n a : Nat), a + n ≤ goldilocksPrime →
    ((List.range' a n).map qgOfNat).Nodup
  | 0, _, _ => List.Pairwise.nil
  | n + 1, a, h => by
    rw [List.range'_succ, List.map_cons, List.nodup_cons]
    refine ⟨?_, qgRange_nodup n (a + 1) (by omega)⟩
    intro hMem
    rcases List.mem_map.mp hMem with ⟨b, hb, hEq⟩
    have hb' := List.mem_range'_1.mp hb
    have hd : b = a + (b - a) := by omega
    rw [hd] at hEq
    exact qgOfNat_ne a (b - a) (by omega) (by omega) hEq.symm

private def wbDom5 : List QuarticGoldilocks :=
  [qgOfNat 0, qgOfNat 1, qgOfNat 2, qgOfNat 3, qgOfNat 4]

private def wbPool2 : List QuarticGoldilocks :=
  [qgOfNat 1, qgOfNat 2]

private theorem wbCertWitness : HemCascadeRbrCert wbPool2 wbDom5 0 4 10 1 :=
  hemWelchBerlekampCert wbPool2 wbDom5 0 4
    (qgRange_nodup 5 0 (by decide)) (qgRange_nodup 2 1 (by decide))
    (by decide) (by decide) (by decide)

private def wbFalseInst : HemWhirInstance QuarticGoldilocks :=
  { batchOracles := [fun _ => CommRingOps.zero]
    batchClaims := [CommRingOps.one]
    initDomainPts := wbDom5
    initDegBound := 0
    initMinAgree := 4
    initKernel := [CommRingOps.one]
    stages := [] }

private theorem wbFalseInst_invalid : ¬ HemStatementValid wbFalseInst := by
  intro hValid
  rcases (HemStatementValid_iff wbFalseInst).mp hValid with ⟨_, hBatch⟩
  dsimp only [wbFalseInst] at hBatch
  rcases (HemBatchValid_cons_cons_iff _ _ _ _ _ _ _ _).mp hBatch with ⟨⟨P, hP⟩, _⟩
  rw [polyWitnessValid_def] at hP
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
  rcases hP with ⟨⟨hLen, hAg⟩, hDot⟩
  rcases P with _ | ⟨c, _ | _⟩
  · rw [ringDot_zero_left] at hDot
    exact LawfulField.one_ne_zero hDot.symm
  · have hc0 : c = CommRingOps.zero := by
      apply Decidable.byContradiction
      intro hNe
      have hEval : ∀ z : QuarticGoldilocks, RoundPoly.evalCoeffs [c] z = c := by
        intro z
        show CommRingOps.add c (CommRingOps.mul z CommRingOps.zero) = c
        rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
      have hCount0 : hemCosetAgreeCount wbDom5 (fun _ => CommRingOps.zero) [c] = 0 := by
        rw [hemCosetAgreeCount_def]
        have hEq0 : qsum wbDom5.length (fun idx =>
            if (CommRingOps.zero : QuarticGoldilocks) = RoundPoly.evalCoeffs [c] (wbDom5.get idx)
            then 1 else 0) = qsum wbDom5.length (fun _ => 0) := by
          apply qsum_congr; intro idx
          rw [hEval]
          have hNe' : (CommRingOps.zero : QuarticGoldilocks) ≠ c := fun e => hNe e.symm
          simp only [hNe', ↓reduceIte]
        rw [hEq0, qsum_const, Nat.mul_zero]
      rw [hCount0] at hAg
      exact absurd hAg (by decide)
    subst hc0
    rw [ringDot_cons_cons, ringDot_zero_left, LawfulCommRing.zero_mul,
      LawfulCommRing.add_zero] at hDot
    exact LawfulField.one_ne_zero hDot.symm
  · simp only [List.length_cons] at hLen; omega

private def wbTreeWitness :
    SrScheduleTree (hemAffineWhirIop wbPool2 (by decide) wbDom5 0 4 10 1 wbCertWitness) [] :=
  .done (fun _ => [])

/-- Inhabitedness witness for `hemAffineWhir_state_restoration_soundness`. -/
theorem inhabited_hemAffineWhir_state_restoration :
    ∃ (S : List QuarticGoldilocks) (hSpos : 0 < S.length)
      (domPts : List QuarticGoldilocks) (d₀ A₀ badMca listG : Nat)
      (cert : HemCascadeRbrCert S domPts d₀ A₀ badMca listG)
      (inst : HemWhirInstance QuarticGoldilocks)
      (sched : List (Fin 2))
      (tree : SrScheduleTree (hemAffineWhirIop S hSpos domPts d₀ A₀ badMca listG cert) sched),
      ¬ HemStatementValid inst ∧
      RatBound.le
        (srTreeAcceptProb (hemAffineWhirIop S hSpos domPts d₀ A₀ badMca listG cert) tree inst)
        (srScheduleErrorSum (hemAffineWhirRbrOf S hSpos domPts d₀ A₀ badMca listG cert) sched) :=
  ⟨wbPool2, by decide, wbDom5, 0, 4, 10, 1, wbCertWitness, wbFalseInst, [], wbTreeWitness,
    wbFalseInst_invalid,
    hemAffineWhir_state_restoration_soundness wbPool2 (by decide) wbDom5 0 4 10 1
      wbCertWitness wbFalseInst wbFalseInst_invalid [] wbTreeWitness⟩

#verify_inhabited
  Qsag.hemAffineWhir_state_restoration_soundness
  Qsag.inhabited_hemAffineWhir_state_restoration

#verify_constructive
  Qsag.ringDot_trimPoly_eq
  Qsag.absorbed_linear_claim_bad_pairs_le_card
  Qsag.hemBridge_bad_quads_le_three_cube
  Qsag.claimFold_bad_pairs_bound
  Qsag.hemAffineWhirIop_accepts_implies_verifier
  Qsag.hemAffineWhir_state_restoration_soundness
  Qsag.hemAffineWhir_qrom_acceptance_bound_of_event_bounds
  Qsag.inhabited_hemAffineWhir_state_restoration

end Qsag

/-
# Hem point-reduction sumcheck: wire decoding and bad-challenge counting

The point-reduction verifier in pcs.rs uses two coefficients c0,c2 and reconstructs
c1 = claim - 2*c0 - c2. Its sum equation is therefore a consequence of the wire decoder,
not an independent premise. This module proves that identity and a two-root bound for
agreement with a genuine quadratic having a different hypercube sum.

The polynomial root argument is integrated from the earlier HemStateFunctionRbr draft.
It is a local algebraic result; neither adaptive composition nor a Rust refinement theorem
is claimed here. The separate implementation refinement lives in the WHIR leaf project.
-/

public section
namespace Qsag
set_option autoImplicit false

private theorem cFilter_congr {α : Type} {p q : α → Bool} :
    ∀ (xs : List α), (∀ x ∈ xs, p x = q x) → xs.filter p = xs.filter q
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.filter_cons, h x (.head xs),
      cFilter_congr xs (fun y hy => h y (.tail x hy))]

/-- A checked false sumcheck message can agree with a true bounded-degree polynomial at
    at most `deg` challenges in a duplicate-free pool. -/
theorem hemSumcheck_polynomial_collision_count {F : Type} [LawfulField F] [DecidableEq F]
    (deg : Nat) (G H_sent S : List F) (claim : F)
    (hS : S.Nodup) (hG : G.length ≤ deg + 1) (hH : H_sent.length ≤ deg + 1)
    (hCheck : CommRingOps.add (RoundPoly.evalCoeffs H_sent CommRingOps.zero)
                (RoundPoly.evalCoeffs H_sent CommRingOps.one) = claim)
    (hFalse : claim ≠ CommRingOps.add (RoundPoly.evalCoeffs G CommRingOps.zero)
                        (RoundPoly.evalCoeffs G CommRingOps.one)) :
    (S.filter (fun r => decide (RoundPoly.evalCoeffs H_sent r = RoundPoly.evalCoeffs G r))).length ≤
      deg := by
  let diff := polySubVar H_sent G
  have hNz : ∃ x₀ : F, RoundPoly.evalCoeffs diff x₀ ≠ CommRingOps.zero := by
    by_cases h0 : RoundPoly.evalCoeffs H_sent CommRingOps.zero =
        RoundPoly.evalCoeffs G CommRingOps.zero
    · refine ⟨CommRingOps.one, fun h1 => hFalse ?_⟩
      rw [evalCoeffs_polySubVar] at h1
      rw [← hCheck, h0, LawfulCommRing.sub_eq_zero_iff.mp h1]
    · exact ⟨CommRingOps.zero, fun hz =>
        h0 (LawfulCommRing.sub_eq_zero_iff.mp (by rwa [evalCoeffs_polySubVar] at hz))⟩
  have hEq : S.filter (fun r => decide (RoundPoly.evalCoeffs H_sent r = RoundPoly.evalCoeffs G r)) =
      S.filter (fun r => decide (RoundPoly.evalCoeffs diff r = CommRingOps.zero)) := by
    refine cFilter_congr S (fun r _ => ?_)
    dsimp only [diff]; rw [evalCoeffs_polySubVar]
    by_cases he : RoundPoly.evalCoeffs H_sent r = RoundPoly.evalCoeffs G r
    · simp only [he, LawfulCommRing.sub_self, decide_true]
    · have hSub : CommRingOps.sub (RoundPoly.evalCoeffs H_sent r)
          (RoundPoly.evalCoeffs G r) ≠ CommRingOps.zero :=
        fun h0 => he (LawfulCommRing.sub_eq_zero_iff.mp h0)
      simp only [he, hSub, decide_false]
  rw [hEq]
  exact @RoundPoly.roots_nodup_length_le F _ _ (LawfulField.toNoZeroDivisors F)
    deg diff S hS (polySubVar_length_le H_sent G (deg + 1) hH hG) hNz


/-- Mathematical coefficient list decoded by the PCS point-reduction quadratic wire. -/
def hemPointReductionWirePoly {F : Type} [CommRingOps F]
    (c0 c2 claim : F) : List F :=
  [c0, CommRingOps.sub (CommRingOps.sub claim (CommRingOps.add c0 c0)) c2, c2]

/-- The compact wire enforces the hypercube sum for every pair of transmitted coefficients. -/
theorem hemPointReductionWire_sum {F : Type} [LawfulCommRing F] (c0 c2 claim : F) :
    CommRingOps.add
      (RoundPoly.evalCoeffs (hemPointReductionWirePoly c0 c2 claim) CommRingOps.zero)
      (RoundPoly.evalCoeffs (hemPointReductionWirePoly c0 c2 claim) CommRingOps.one) = claim := by
  simp only [hemPointReductionWirePoly, RoundPoly.evalCoeffs]
  constructive_ring

/-- The PCS point-reduction wire has at most two challenges agreeing with any genuine
    quadratic whose sum differs from `claim`. The message-length and sum-check premises
    of the general root lemma are discharged from the decoder itself. -/
theorem hemPointReductionWire_bad_challenges_le_two {F : Type} [LawfulField F] [DecidableEq F]
    (G S : List F) (c0 c2 claim : F) (hS : S.Nodup) (hG : G.length ≤ 3)
    (hFalse : claim ≠ CommRingOps.add (RoundPoly.evalCoeffs G CommRingOps.zero)
      (RoundPoly.evalCoeffs G CommRingOps.one)) :
    (S.filter (fun r => decide
      (RoundPoly.evalCoeffs (hemPointReductionWirePoly c0 c2 claim) r =
        RoundPoly.evalCoeffs G r))).length ≤ 2 :=
  hemSumcheck_polynomial_collision_count 2 G (hemPointReductionWirePoly c0 c2 claim) S claim
    hS hG (Nat.le_refl 3) (hemPointReductionWire_sum c0 c2 claim) hFalse

/-- The bound is attained by a false claim: over the pool {0,1,2}, the decoded message
    X(X-2) agrees with the zero polynomial at two points and disagrees at the third. -/
theorem hemPointReductionWire_bound_attained :
    let S : List QuarticGoldilocks :=
      [CommRingOps.zero, CommRingOps.one, CommRingOps.add CommRingOps.one CommRingOps.one]
    let claim : QuarticGoldilocks := CommRingOps.neg CommRingOps.one
    claim ≠ CommRingOps.add
      (RoundPoly.evalCoeffs ([] : List QuarticGoldilocks) CommRingOps.zero)
      (RoundPoly.evalCoeffs ([] : List QuarticGoldilocks) CommRingOps.one) ∧
    (S.filter (fun r => decide
      (RoundPoly.evalCoeffs (hemPointReductionWirePoly CommRingOps.zero CommRingOps.one claim) r =
        RoundPoly.evalCoeffs ([] : List QuarticGoldilocks) r))).length = 2 ∧
    2 < S.length := by
  intro S claim
  have hEv : ∀ r : QuarticGoldilocks,
      RoundPoly.evalCoeffs (hemPointReductionWirePoly CommRingOps.zero CommRingOps.one claim) r =
        CommRingOps.mul r (CommRingOps.sub r (CommRingOps.add CommRingOps.one CommRingOps.one)) := by
    intro r
    simp only [hemPointReductionWirePoly, RoundPoly.evalCoeffs, claim]
    constructive_ring
  have hNil : ∀ r : QuarticGoldilocks,
      RoundPoly.evalCoeffs ([] : List QuarticGoldilocks) r = CommRingOps.zero := fun _ => rfl
  have hNeg : CommRingOps.neg (CommRingOps.one : QuarticGoldilocks) ≠ CommRingOps.zero := by
    intro h
    have hId : ∀ x : QuarticGoldilocks, x = CommRingOps.neg (CommRingOps.neg x) := by
      intro x
      constructive_ring
    apply LawfulField.one_ne_zero (F := QuarticGoldilocks)
    rw [hId CommRingOps.one, h]
    constructive_ring
  refine ⟨?_, ?_, by decide⟩
  · intro h
    rw [hNil, hNil, LawfulCommRing.add_zero] at h
    exact hNeg h
  · have e0 : CommRingOps.mul (CommRingOps.zero : QuarticGoldilocks)
        (CommRingOps.sub CommRingOps.zero (CommRingOps.add CommRingOps.one CommRingOps.one)) =
          CommRingOps.zero := LawfulCommRing.zero_mul _
    have e1 : CommRingOps.mul (CommRingOps.one : QuarticGoldilocks)
        (CommRingOps.sub CommRingOps.one (CommRingOps.add CommRingOps.one CommRingOps.one)) =
          CommRingOps.neg CommRingOps.one := by
      constructive_ring
    have e2 : CommRingOps.mul (CommRingOps.add CommRingOps.one (CommRingOps.one : QuarticGoldilocks))
        (CommRingOps.sub (CommRingOps.add CommRingOps.one CommRingOps.one)
          (CommRingOps.add CommRingOps.one CommRingOps.one)) = CommRingOps.zero := by
      constructive_ring
    simp only [S, List.filter_cons, List.filter_nil, hEv, hNil, e0, e1, e2, hNeg, decide_true,
      decide_false, Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_nil]

#verify_constructive
  Qsag.hemSumcheck_polynomial_collision_count
  Qsag.hemPointReductionWire_sum
  Qsag.hemPointReductionWire_bad_challenges_le_two
  Qsag.hemPointReductionWire_bound_attained
/-! ### Exports for lane agg-budget -/

/-- Public form of the one-root count: at most one element of a duplicate-free pool `S` solves
    `a + x * b = 0` when `b ≠ 0`. -/
theorem linear_one_var_bad_count_le_one {F : Type} [LawfulField F] [DecidableEq F]
    (S : List F) (hS : S.Nodup) (a b : F) (hb : b ≠ CommRingOps.zero) :
    (S.filter (fun x =>
      decide (CommRingOps.add a (CommRingOps.mul x b) = CommRingOps.zero))).length ≤ 1 :=
  linear_one_var_bad_le_one S hS a b hb

theorem hemVirtualFoldOracle_def {F : Type} [LawfulField F]
    (θ α β : F) (curDom foldDom : List F) (curOracle : Nat → F) (idx : Nat) :
    hemVirtualFoldOracle θ α β curDom foldDom curOracle idx =
      CommRingOps.add
        (CommRingOps.mul
          (LawfulField.inv (CommRingOps.mul (CommRingOps.add CommRingOps.one CommRingOps.one)
            (curDom.getD (2 * idx) CommRingOps.one)))
          (CommRingOps.sub (curOracle (2 * idx)) (curOracle (2 * idx + 1))))
        (CommRingOps.mul
          (CommRingOps.add α (CommRingOps.mul β (foldDom.getD idx CommRingOps.zero)))
          (CommRingOps.add
            (CommRingOps.mul (LawfulField.inv (CommRingOps.add CommRingOps.one CommRingOps.one))
              (CommRingOps.add (curOracle (2 * idx)) (curOracle (2 * idx + 1))))
            (CommRingOps.mul θ
              (CommRingOps.mul
                (LawfulField.inv (CommRingOps.mul (CommRingOps.add CommRingOps.one CommRingOps.one)
                  (curDom.getD (2 * idx) CommRingOps.one)))
                (CommRingOps.sub (curOracle (2 * idx)) (curOracle (2 * idx + 1))))))) := by
  rfl

theorem seqSpecsIop_inLang {Stmt State Msg : Type} {stateLive : Stmt → State → Prop}
    (specs : List (SeqRoundSpec Stmt State Msg stateLive))
    (inLang : Stmt → Prop) (verify : Stmt → List (Msg × Nat) → Bool) :
    (seqSpecsIop specs inLang verify).inLang = inLang := by rfl

theorem seqSpecsIop_verify {Stmt State Msg : Type} {stateLive : Stmt → State → Prop}
    (specs : List (SeqRoundSpec Stmt State Msg stateLive))
    (inLang : Stmt → Prop) (verify : Stmt → List (Msg × Nat) → Bool) :
    (seqSpecsIop specs inLang verify).verify = verify := by rfl
/-- Public form of the invalid-coordinate search: a batch that is not `HemBatchValid` has a
    coordinate with no accepted polynomial witness. -/
theorem exists_invalid_batch_coordinate
    (domPts : List QuarticGoldilocks) (A₀ d₀ : Nat) (kernel : List QuarticGoldilocks)
    (hDom : domPts.Nodup) (hdA : d₀ + 1 ≤ A₀)
    (os : List (Nat → QuarticGoldilocks)) (es : List QuarticGoldilocks)
    (hLen : os.length = es.length)
    (hNot : ¬ HemBatchValid domPts A₀ d₀ kernel os es) :
    ∃ i₀ : Nat, i₀ < os.length ∧
      (∀ G : List QuarticGoldilocks,
        polyWitnessValid domPts A₀ d₀ (os.getD i₀ (fun _ => CommRingOps.zero))
          kernel (es.getD i₀ CommRingOps.zero) G = false) := by
  obtain ⟨i₀, _, hLt, hBad⟩ :=
    findInvalidBatchIdx_complete domPts A₀ d₀ kernel hDom hdA os es hLen hNot
  exact ⟨i₀, hLt, hBad⟩

-- (end exports for lane agg-budget)

end Qsag
