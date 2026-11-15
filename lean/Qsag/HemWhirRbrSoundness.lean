module
/-
# Hem affine-fold counting and a restricted cascade IOP

The algebraic counting results are constructive. The packaged IOP below has one batch oracle,
no WHIR fold stages, and a final agreement check at A₀ + 1; the transcript checker imported
from MultiRoundFsQrom uses A₀. Thus its acceptance implication goes from this restricted IOP
to the checker, and does not establish soundness of arbitrary checker transcripts.

Johnson-radius claim preservation remains conditional on NonExcludedDecompBound. The final
QROM lemma is only a union bound from supplied event bounds and coverage. It neither derives
Fiat–Shamir challenges from transcript bytes nor constructs quantum Merkle extraction, and
must not be read as deployed verifier soundness.
-/

public import Qsag.MultiRoundFsQrom
public import Qsag.CodingTheory.Cwyz26AffineGap
public import Qsag.CodingTheory.TrivariateGsExplainer
public import Qsag.QromMerkleOnlineExtraction
public import Qsag.Tactic.ConstructiveRing
public import Qsag.Tactic.AssuranceKit
import all Qsag.MultiRoundFsQrom
import all Qsag.AffineProximityGaps
import all Qsag.CodingTheory.PolyMv3
import all Qsag.CodingTheory.TrivariateGsExplainer
import all Qsag.CodingTheory.AffineIncidenceBound
import all Qsag.CodingTheory.Cwyz26AffineGap

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
  unfold hemCosetAgreeCount
  rw [← qsum_get_filter_eq]
  apply qsum_congr; intro idx
  rw [lookupDomOracle_get domPts O hNd idx]
  by_cases h : O idx.1 = RoundPoly.evalCoeffs P (domPts.get idx)
  · simp only [h, decide_true, ↓reduceIte]
  · have h' : RoundPoly.evalCoeffs P (domPts.get idx) ≠ O idx.1 := fun e => h e.symm
    simp only [h, h', decide_false, Bool.false_eq_true, ↓reduceIte]

private theorem ringDot_zero_left {F : Type} [LawfulCommRing F] (v : List F) :
    ringDot ([] : List F) v = CommRingOps.zero := rfl

/-- Canonical trailing-zero trimming `trimPoly` preserves `ringDot` against every kernel `v`. -/
theorem ringDot_trimPoly_eq {F : Type} [LawfulCommRing F] [DecidableEq F] :
    ∀ (p v : List F), ringDot (trimPoly p) v = ringDot p v
  | [], _ => rfl
  | c :: cs, [] => by
    simp only [trimPoly]
    split <;> rfl
  | c :: cs, k :: ks => by
    simp only [trimPoly]
    have ih := ringDot_trimPoly_eq cs ks
    split
    · rename_i hZero
      rcases hZero with ⟨hcsNil, hc0⟩
      rw [hc0]
      change CommRingOps.zero =
        CommRingOps.add (CommRingOps.mul CommRingOps.zero k) (ringDot cs ks)
      rw [← ih, hcsNil, ringDot_zero_left, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
    · simp only [ringDot, ih]

/-- Canonical trailing-zero trimming also preserves shifted functional evaluations `⟨X · P, v⟩`. -/
theorem ringDot_shiftPoly_trimPoly_eq {F : Type} [LawfulCommRing F] [DecidableEq F]
    (p v : List F) :
    ringDot (shiftPoly (trimPoly p)) v = ringDot (shiftPoly p) v := by
  cases v with
  | nil => rfl
  | cons k ks =>
    simp only [shiftPoly, ringDot, LawfulCommRing.zero_mul, LawfulCommRing.zero_add]
    exact ringDot_trimPoly_eq p ks

/-- Two degree-`≤ d` coefficient lists agreeing on `≥ d + 1` points of a `Nodup` set `U`
    have identical canonical trimmed polynomials (`0` classical choice). -/
theorem trimPoly_eq_of_agree_on_nodup {F : Type} [LawfulField F] [DecidableEq F]
    {d : Nat} {P Q : List F} {U : List F}
    (hP : P.length ≤ d + 1) (hQ : Q.length ≤ d + 1)
    (hU : U.Nodup) (hULen : d + 1 ≤ U.length)
    (hAgree : ∀ x ∈ U, RoundPoly.evalCoeffs P x = RoundPoly.evalCoeffs Q x) :
    trimPoly P = trimPoly Q := by
  let pG : GsUniPoly F := GsUniPoly.ofCoeffs P
  let qG : GsUniPoly F := GsUniPoly.ofCoeffs Q
  if hEq : pG = qG then
    exact congrArg Subtype.val hEq
  else
    have hpDeg : pG.val.length ≤ d + 1 := Nat.le_trans (trimPoly_length_le P) hP
    have hqDeg : qG.val.length ≤ d + 1 := Nat.le_trans (trimPoly_length_le Q) hQ
    rcases gsUniPoly_exists_diff_on_domain hEq hpDeg hqDeg hU hULen with ⟨x₀, hx₀U, hDiff⟩
    exfalso
    apply hDiff
    change RoundPoly.evalCoeffs (trimPoly P) x₀ = RoundPoly.evalCoeffs (trimPoly Q) x₀
    rw [evalCoeffs_trimPoly, evalCoeffs_trimPoly]
    exact hAgree x₀ hx₀U

private theorem filter_overlap_len {α : Type} (p q : α → Bool) :
    ∀ (D : List α),
      (D.filter p).length + (D.filter q).length ≤
        D.length + (D.filter (fun z => p z && q z)).length
  | [] => Nat.le_refl 0
  | a :: ds => by
    have ih := filter_overlap_len p q ds
    cases hp : p a <;> cases hq : q a <;>
      simp only [List.filter_cons, hp, hq, Bool.and_self, Bool.and_false, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega

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
            unfold hemBridgeFoldClaim at hEq
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
    rw [qsum_add, qsum_mul_right, qsum_const, qsum_get_filter_eq] at hSplitTheta
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
  rw [qsum_add, qsum_mul_right, qsum_const, qsum_get_filter_eq] at hAllPhi
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

/-- Explicit correlated-agreement pair witness `(F_poly, G_poly)` for `(f, g)` at `(d, B)` on `D`. -/
def HasCorrelatedPairAt {F : Type} [CommRingOps F] [DecidableEq F]
    (d B : Nat) (f g : F → F) (D : List F) (F_poly G_poly : List F) : Prop :=
  F_poly.length ≤ d + 1 ∧
  G_poly.length ≤ d ∧
  B ≤ (D.filter (fun z =>
    decide (RoundPoly.evalCoeffs F_poly z = f z) &&
    decide (RoundPoly.evalCoeffs G_poly z = g z))).length

/-- `P` decomposes as `F_poly + (α + β X) G_poly` (up to trailing zeros) for a `(d, B)`
    correlated-agreement pair `(F_poly, G_poly)` of `(f, g)` on `D`. -/
def DecomposesViaCorrelatedPair {F : Type} [CommRingOps F] [DecidableEq F]
    (d B : Nat) (f g : F → F) (D : List F) (α β : F) (P : List F) : Prop :=
  ∃ F_poly G_poly : List F,
    HasCorrelatedPairAt d B f g D F_poly G_poly ∧
    trimPoly P = trimPoly
      (polyAddVar F_poly
        (polyAddVar (polyScaleVar α G_poly) (polyScaleVar β (shiftPoly G_poly))))

/-- **`[CWYZ26]` Theorem 5.1 Claim-Preserving Fold Decomposition Bound (`AffineFoldDecompBound`)**:
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
          simp only [polyScaleVar, List.length_map]; omega
        have h2 : (polyScaleVar β (shiftPoly G₀)).length ≤ d + 1 := by
          simp only [polyScaleVar, shiftPoly, List.length_map, List.length_cons]; omega
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

/-- **`[CWYZ26]` Lemma 4.1 + 4.2 Non-Excluded Decomposition Hypothesis (`NonExcludedDecompBound`)**:
    At arbitrary Johnson list-decoding radius (`D_list ≥ 1`), bounds the number of non-excluded
    challenges `(α, β) ∈ prodPool S` whose explainer `Q(X, α + β X, Z)` admits a degree-`≤ d`,
    agreement-`≥ A` root `P` that does NOT arise from a `(d, A - 1)` correlated-agreement branch. -/
def NonExcludedDecompBound {F : Type} [LawfulField F] [DecidableEq F]
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

private theorem filter_any_length_le {α β : Type} (items : List α) (pred : α → β → Bool)
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

/-- **`[CWYZ26]` Theorem 5.1 Eq. `(5.7)` Claim-Carrying Fold Flip Bound (`claimFold_bad_pairs_bound`)**:
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
def runSeqSpecs {Stmt State Msg : Type} {stateLive : Stmt → State → Prop} :
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

/-- Well-formedness of a `k = 0` (direct cascade-to-final) `HemWhirInstance` of batch size `m`. -/
def WellFormedHemCascadeInstance (m : Nat) (domPts : List QuarticGoldilocks) (d₀ A₀ : Nat)
    (inst : HemWhirInstance QuarticGoldilocks) : Prop :=
  (1 ≤ m ∧ m ≤ 16) ∧
  inst.batchOracles.length = m ∧
  inst.batchClaims.length = m ∧
  inst.initDomainPts = domPts ∧
  inst.initDegBound = d₀ ∧
  inst.initMinAgree = A₀ ∧
  inst.stages = []

/-- State liveness predicate for `HemCoreState`. -/
def hemCoreLive (m : Nat) (domPts : List QuarticGoldilocks) (d₀ A₀ : Nat)
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
  | [], [], _, hNot => False.elim (hNot trivial)
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
        unfold polyWitnessValid at hG
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
          unfold polyWitnessValid
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
        fun hRest => hNot ⟨⟨pW.val, hpWVal⟩, hRest⟩
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
      apply Subtype.ext
      rw [← p.property, hTrim]
      rfl
    have e1 := eqZero p₁ hp₁.1 hp₁.2
    have e2 := eqZero p₂ hp₂.1 hp₂.2
    exact (List.pairwise_cons.mp hNd).1 p₂ (.head _) (e1.trans e2.symm)

def hemSingleCascadeStep (S domPts : List QuarticGoldilocks) (d₀ A₀ : Nat)
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

private theorem hemSingleCascade_flip_bound
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
          ⟨⟨Nat.le_refl 1, Nat.le_add_right 1 15⟩, hOLen, hCLen, hDomEq, hDegEq, hAgEq, hStEq⟩
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
              fun hb => hInvalidStmt ⟨⟨Nat.le_refl 1, Nat.le_add_right 1 15⟩, hb⟩
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
                unfold polyWitnessValid
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
                unfold polyWitnessValid at hP
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
                          dsimp only [evalCascadeOracle, gWord]
                          rw [list_getD_eq_get domPts CommRingOps.zero ⟨idx, hLt⟩,
                              lookupDomOracle_get domPts O₀ cert.dom_nodup ⟨idx, hLt⟩,
                              LawfulCommRing.add_zero, LawfulCommRing.zero_add]
                        simp only [List.filter_cons, hValEq,
                          ih (fun y hy => hSub y (.tail z hy))]
                    exact hMemCongr domPts (fun _ h => h)
                  rw [hEqFilt]
                  exact decide_eq_true hPAg
                · dsimp only [evalCascadeClaim] at hPDot
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
    have hEq : p₁ = p₂ := Subtype.ext (p₁.property.symm.trans (hTrim.trans p₂.property))
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
    unfold QVec.queryMassOn
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
        uniformOracleSum 256 n f + uniformOracleSum 256 n g := by
    intro n
    induction n with
    | zero => intro _ _; rfl
    | succ m ih =>
      intro f g
      simp only [uniformOracleSum, ih, qsum_add]
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
  refine ⟨by decide, ?_⟩
  rintro ⟨P, hP⟩
  exact hemFalseClaimInstance_invalid ⟨⟨Nat.le_refl 1, by decide⟩, ⟨P, hP⟩, trivial⟩


private def qgOfNat (n : Nat) : QuarticGoldilocks :=
  ⟨⟨Goldilocks.ofNat n, Goldilocks.ofNat 0⟩, ⟨Goldilocks.ofNat 0, Goldilocks.ofNat 0⟩⟩

private def wbDom5 : List QuarticGoldilocks :=
  [qgOfNat 0, qgOfNat 1, qgOfNat 2, qgOfNat 3, qgOfNat 4]

private def wbPool2 : List QuarticGoldilocks :=
  [qgOfNat 1, qgOfNat 2]

private theorem wbCertWitness : HemCascadeRbrCert wbPool2 wbDom5 0 4 10 1 :=
  hemWelchBerlekampCert wbPool2 wbDom5 0 4
    (by decide) (by decide) (by decide) (by decide) (by decide)

private def wbFalseInst : HemWhirInstance QuarticGoldilocks :=
  { batchOracles := [fun _ => CommRingOps.zero]
    batchClaims := [CommRingOps.one]
    initDomainPts := wbDom5
    initDegBound := 0
    initMinAgree := 4
    initKernel := [CommRingOps.one]
    stages := [] }

private theorem wbFalseInst_invalid : ¬ HemStatementValid wbFalseInst := by
  rintro ⟨_, ⟨P, hP⟩, _⟩
  unfold polyWitnessValid at hP
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
  rcases hP with ⟨⟨hLen, hAg⟩, hDot⟩
  dsimp only [wbFalseInst] at hLen hAg hDot
  rcases P with _ | ⟨c, _ | _⟩
  · exact absurd hDot (by decide)
  · have hc0 : c = CommRingOps.zero := by
      apply Decidable.byContradiction
      intro hNe
      have hEval : ∀ z : QuarticGoldilocks, RoundPoly.evalCoeffs [c] z = c := by
        intro z
        show CommRingOps.add c (CommRingOps.mul z CommRingOps.zero) = c
        rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
      have hCount0 : hemCosetAgreeCount wbDom5 (fun _ => CommRingOps.zero) [c] = 0 := by
        unfold hemCosetAgreeCount
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
    exact absurd hDot (by decide)
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
  Qsag.affineFoldDecompBound_of_affineMcaBound
  Qsag.affineFoldDecompBound_welch_berlekamp
  Qsag.cwyz26_affineFoldDecompBound_of_nonExcluded
  Qsag.claimFold_bad_pairs_bound
  Qsag.hemAffineWhirIop_accepts_implies_verifier
  Qsag.hemAffineWhir_state_restoration_soundness
  Qsag.hemAffineWhir_qrom_acceptance_bound_of_event_bounds
  Qsag.inhabited_hemAffineWhir_state_restoration

end Qsag
