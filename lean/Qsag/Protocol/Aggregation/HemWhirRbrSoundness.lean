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

public import Qsag.Oracle.MultiRoundFsQrom
public import Qsag.Coding.Cwyz26AffineGap
public import Qsag.Coding.TrivariateGsExplainer
public import Qsag.Oracle.QromMerkleOnlineExtraction
public import Qsag.Tactic.ConstructiveRing
public import Qsag.Tactic.AssuranceKit
import all Qsag.Oracle.MultiRoundFsQrom
import all Qsag.Coding.AffineProximityGaps
import all Qsag.Coding.PolyMv3
import all Qsag.Coding.TrivariateGsExplainer
import all Qsag.Coding.AffineIncidenceBound
import all Qsag.Coding.Cwyz26AffineGap

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

