module
public import Qsag.Protocol.Aggregation.HemInterpolation
public import Qsag.Protocol.Aggregation.Aggregation
public import Qsag.Math.QuinticExt5
public import Qsag.Math.Tactic.CommRing
public import Qsag.Tactic.AssuranceKit
/-
# Qsag.Protocol.Aggregation.ZkHemV2 — zero-knowledge lemmas of zk-Hem v2

Lean statements of `crates/qsag-agg/SECURITY.md`, section V2.2 (table of V2.6).

§1  `CoinBijectionSimulated`: perfect simulation by a bijection of coins. It has the body of
    `Qsag.ZkHem.PerfectlySimulated`, whose definition is sealed for importing modules.
§2  Lemma V2.4. `v2_mask_line_perfectly_simulated`, `v2_mask_claim_determined`,
    `v2_mask_symbol_determined`, `v2_mask_line_view_perfectly_simulated`.
§3  Weighted moments of distinct points: `momInv_moments`, `moments_momInv`.
§4  Lemma V2.3 (c). `foldScalars` is the linear part of the five scalars of one Stage-0 fold
    as a function of `(F_j)`; `v2_fold_scalar_matrix_bijective`,
    `v2_fold_scalars_perfectly_simulated`.
§5  Newton interpolation on `List.map (evalCoeffs cs) xs` (the sealed `Qsag.ZkHem.interp` and
    `Qsag.ZkHem.evalAll` cannot be unfolded here).
§6  Lemma V2.2 in interpolation form. `v2_blinding_count`, `v2_blinding_count_scaled`,
    `v2_opened_symbols_and_mask_values_perfectly_simulated`.
§6b Lemma V2.2 in quotient-ring form (`E[X] / (X^(2^s) - z_j)`, `SECURITY.md` §§V2.2, V2.6, V2.9).
    `divModBinomial`, `fiberRoots`, `blindPoints_fiberRoots_nodup`,
    `v2_blinding_residue_ring_bijective`, `v2_blinding_residue_ring_perfectly_simulated`.
§7  Profile roster and cell count: `ZkHemV2Profile`, `blindCells`.

The negative statements (`tooth_*`) are paired in `Qsag.Tests.ZkHemV2Teeth`.
-/

public section
namespace Qsag.ZkHemV2

set_option autoImplicit false
open CommRingOps RoundPoly
open Qsag.ZkHem (LinForm vadd vsub vadd_length vsub_length vsub_vadd vadd_vsub)
open QuinticGoldilocks (frob ofBase xBasis)

/-! ## §1. Perfect simulation by a bijection of coins -/

/-- `real w` on uniform prover coins `R` and `sim` on uniform simulator coins `C` are the same
    distribution for every witness `w`. The simulator does not take `w`. -/
@[expose] def CoinBijectionSimulated {W R C V : Type} (real : W → R → V) (sim : C → V) : Prop :=
  ∀ w : W, ∃ Φ : SimpleEquiv R C, ∀ r : R, real w r = sim (Φ.toFun r)

/-- Post-compose a bijection onto a product with a bijection of each factor. -/
def postProd {R A B A' B' : Type} (e : SimpleEquiv R (A × B)) (a : SimpleEquiv A A')
    (b : SimpleEquiv B B') : SimpleEquiv R (A' × B') where
  toFun r := (a.toFun (e.toFun r).1, b.toFun (e.toFun r).2)
  invFun o := e.invFun (a.invFun o.1, b.invFun o.2)
  left_inv r := by
    show e.invFun (a.invFun (a.toFun (e.toFun r).1), b.invFun (b.toFun (e.toFun r).2)) = r
    rw [a.left_inv, b.left_inv]
    exact e.left_inv r
  right_inv o := by
    show (a.toFun (e.toFun (e.invFun (a.invFun o.1, b.invFun o.2))).1,
      b.toFun (e.toFun (e.invFun (a.invFun o.1, b.invFun o.2))).2) = o
    rw [e.right_inv]
    show (a.toFun (a.invFun o.1), b.toFun (b.invFun o.2)) = o
    rw [a.right_inv, b.right_inv]

theorem postProd_apply {R A B A' B' : Type} (e : SimpleEquiv R (A × B))
    (a : SimpleEquiv A A') (b : SimpleEquiv B B') (r : R) :
    (postProd e a b).toFun r = (a.toFun (e.toFun r).1, b.toFun (e.toFun r).2) := by unfold postProd; rfl

section Offsets
variable {F : Type} [LawfulField F]

/-- Translation by a fixed vector of the same length. -/
def offsetEquiv {n : Nat} (d : {l : List F // l.length = n}) :
    SimpleEquiv {l : List F // l.length = n} {l : List F // l.length = n} where
  toFun v := ⟨vadd d.1 v.1, (vadd_length _ _ (d.2.trans v.2.symm)).trans v.2⟩
  invFun o := ⟨vsub o.1 d.1, (vsub_length _ _ (o.2.trans d.2.symm)).trans d.2⟩
  left_inv v := Subtype.ext (vsub_vadd _ _ (d.2.trans v.2.symm))
  right_inv o := Subtype.ext (vadd_vsub _ _ (d.2.trans o.2.symm))

theorem offsetEquiv_apply {n : Nat} (d v : {l : List F // l.length = n}) :
    ((offsetEquiv d).toFun v).val = vadd d.val v.val := by unfold offsetEquiv; rfl

/-- A view that is a witness-dependent offset plus a bijective image of the coins is simulated
    by a uniform vector. -/
theorem offset_simulated {R : Type} {n : Nat} (e : SimpleEquiv R {l : List F // l.length = n}) :
    CoinBijectionSimulated
      (fun (d : {l : List F // l.length = n}) (r : R) => vadd d.1 (e.toFun r).1)
      (fun (o : {l : List F // l.length = n}) => o.1) := by
  intro d
  refine ⟨⟨fun r => (offsetEquiv d).toFun (e.toFun r),
    fun o => e.invFun ((offsetEquiv d).invFun o), fun r => ?_, fun o => ?_⟩, fun _ => rfl⟩
  · show e.invFun ((offsetEquiv d).invFun ((offsetEquiv d).toFun (e.toFun r))) = r
    rw [(offsetEquiv d).left_inv, e.left_inv]
  · show (offsetEquiv d).toFun (e.toFun (e.invFun ((offsetEquiv d).invFun o))) = o
    rw [e.right_inv, (offsetEquiv d).right_inv]

/-- The two-component form of `offset_simulated`, over two fields. -/
theorem offset_pair_simulated {G R : Type} [LawfulField G] {n m : Nat}
    (e : SimpleEquiv R ({l : List F // l.length = n} × {l : List G // l.length = m})) :
    CoinBijectionSimulated
      (fun (d : {l : List F // l.length = n} × {l : List G // l.length = m}) (r : R) =>
        (vadd d.1.1 (e.toFun r).1.1, vadd d.2.1 (e.toFun r).2.1))
      (fun (o : {l : List F // l.length = n} × {l : List G // l.length = m}) => (o.1.1, o.2.1)) :=
  fun d => ⟨postProd e (offsetEquiv d.1) (offsetEquiv d.2), fun _ => rfl⟩

end Offsets

/-! ## §2. Lemma V2.4: the mask line -/

section MaskLine
variable {F : Type} [LawfulField F] {ι : Type}

/-- `g = P + β R`. -/
@[expose] def maskLine (β : F) (P R : ι → F) : ι → F :=
  fun i => add (P i) (mul β (R i))

def unmaskLine (β : F) (P g : ι → F) : ι → F :=
  fun i => mul (sub (g i) (P i)) (LawfulField.inv β)

theorem unmaskLine_maskLine (β : F) (hβ : β ≠ zero) (P R : ι → F) :
    unmaskLine β P (maskLine β P R) = R := by
  funext i
  have hi := LawfulField.mul_inv_cancel hβ
  show mul (sub (add (P i) (mul β (R i))) (P i)) (LawfulField.inv β) = R i
  generalize LawfulField.inv β = j at hi
  have e : mul (sub (add (P i) (mul β (R i))) (P i)) j = mul (R i) (mul β j) := by
    constructive_ring
  rw [e, hi, LawfulCommRing.mul_one]

theorem maskLine_unmaskLine (β : F) (hβ : β ≠ zero) (P g : ι → F) :
    maskLine β P (unmaskLine β P g) = g := by
  funext i
  have hi := LawfulField.mul_inv_cancel hβ
  show add (P i) (mul β (mul (sub (g i) (P i)) (LawfulField.inv β))) = g i
  generalize LawfulField.inv β = j at hi
  have e : add (P i) (mul β (mul (sub (g i) (P i)) j)) =
      add (P i) (mul (sub (g i) (P i)) (mul β j)) := by constructive_ring
  rw [e, hi]
  constructive_ring

/-- **Lemma V2.4.** For `β ≠ 0` and a uniform `R`, the word `P + β R` is uniform whatever `P`
    is. -/
theorem v2_mask_line_perfectly_simulated (β : F) (hβ : β ≠ zero) :
    CoinBijectionSimulated (fun (P : ι → F) (R : ι → F) => maskLine β P R)
      (fun (g : ι → F) => g) :=
  fun P => ⟨⟨maskLine β P, unmaskLine β P, unmaskLine_maskLine β hβ P,
    maskLine_unmaskLine β hβ P⟩, fun _ => rfl⟩

theorem maskLine_claim (ℓ : LinForm ι F) (β : F) (P R : ι → F) :
    ℓ.app (maskLine β P R) = add (ℓ.app P) (mul β (ℓ.app R)) := by
  have e : maskLine β P R = fun i => add (mul one (P i)) (mul β (R i)) := by
    funext i
    show add (P i) (mul β (R i)) = add (mul one (P i)) (mul β (R i))
    constructive_ring
  rw [e, ℓ.lin]
  constructive_ring

/-- The claim `μ = ⟨R, v⟩` is determined by `g`, `β` and the claim on `P`. -/
theorem v2_mask_claim_determined (ℓ : LinForm ι F) (β : F) (hβ : β ≠ zero) (P R : ι → F) :
    ℓ.app R = mul (sub (ℓ.app (maskLine β P R)) (ℓ.app P)) (LawfulField.inv β) := by
  have hi := LawfulField.mul_inv_cancel hβ
  rw [maskLine_claim]
  generalize LawfulField.inv β = j at hi
  have e : mul (sub (add (ℓ.app P) (mul β (ℓ.app R))) (ℓ.app P)) j =
      mul (ℓ.app R) (mul β j) := by constructive_ring
  rw [e, hi, LawfulCommRing.mul_one]

/-- Every symbol of `R` is determined by the same symbols of `g` and `P`. -/
theorem v2_mask_symbol_determined (β : F) (hβ : β ≠ zero) (P R : ι → F) (i : ι) :
    R i = mul (sub (maskLine β P R i) (P i)) (LawfulField.inv β) :=
  (congrFun (unmaskLine_maskLine β hβ P R) i).symm

/-- Real view of the mask-line rounds: the word `g`, the claim `μ = ℓ(R)` and the opened
    values `opened k` of `R` (each a linear functional of `R`). -/
def maskLineReal {κ : Type} (β : F) (ℓ : LinForm ι F) (opened : κ → LinForm ι F)
    (P R : ι → F) : (ι → F) × F × (κ → F) :=
  (maskLine β P R, ℓ.app R, fun k => (opened k).app R)

/-- Simulated view from `g`, the public claim value `σ = ℓ(P)` and the opened values `o` of
    `P`. It takes neither `P` nor `R`. -/
def maskLineSim {κ : Type} (β : F) (ℓ : LinForm ι F) (opened : κ → LinForm ι F) (σ : F)
    (o : κ → F) (g : ι → F) : (ι → F) × F × (κ → F) :=
  (g, mul (sub (ℓ.app g) σ) (LawfulField.inv β),
    fun k => mul (sub ((opened k).app g) (o k)) (LawfulField.inv β))

theorem v2_mask_line_view_eq_sim {κ : Type} (β : F) (hβ : β ≠ zero) (ℓ : LinForm ι F)
    (opened : κ → LinForm ι F) (P R : ι → F) :
    maskLineReal β ℓ opened P R =
      maskLineSim β ℓ opened (ℓ.app P) (fun k => (opened k).app P) (maskLine β P R) := by
  have e : (fun k => (opened k).app R) =
      fun k => mul (sub ((opened k).app (maskLine β P R)) ((opened k).app P))
        (LawfulField.inv β) :=
    funext fun k => v2_mask_claim_determined (opened k) β hβ P R
  show (maskLine β P R, ℓ.app R, fun k => (opened k).app R) =
    (maskLine β P R, mul (sub (ℓ.app (maskLine β P R)) (ℓ.app P)) (LawfulField.inv β),
      fun k => mul (sub ((opened k).app (maskLine β P R)) ((opened k).app P))
        (LawfulField.inv β))
  rw [e, ← v2_mask_claim_determined ℓ β hβ P R]

/-- **Lemma V2.4, composed view.** Among the words `P` with claim value `σ` and opened values
    `o`, the view `(g, μ, opened symbols of R)` on a uniform `R` equals the simulator's view on
    a uniform `g`. -/
theorem v2_mask_line_view_perfectly_simulated {κ : Type} (β : F) (hβ : β ≠ zero)
    (ℓ : LinForm ι F) (opened : κ → LinForm ι F) (σ : F) (o : κ → F) :
    CoinBijectionSimulated
      (fun (P : {P : ι → F // ℓ.app P = σ ∧ ∀ k, (opened k).app P = o k}) (R : ι → F) =>
        maskLineReal β ℓ opened P.1 R)
      (maskLineSim β ℓ opened σ o) := by
  intro P
  refine ⟨⟨maskLine β P.1, unmaskLine β P.1, unmaskLine_maskLine β hβ P.1,
    maskLine_unmaskLine β hβ P.1⟩, fun R => ?_⟩
  have h := v2_mask_line_view_eq_sim β hβ ℓ opened P.1 R
  have ho : (fun k => (opened k).app P.1) = o := funext P.2.2
  rw [P.2.1, ho] at h
  exact h

/-- With `β = 0` the word is `P` itself: different `P` give different views under all coins. -/
theorem tooth_zero_mask_challenge_reveals_word (P P' R R' : ι → F) (h : P ≠ P') :
    ¬ (maskLine zero P R = maskLine zero P' R') := by
  intro hEq
  have e : ∀ (P R : ι → F), maskLine zero P R = P := fun P R => by
    funext i
    show add (P i) (mul zero (R i)) = P i
    constructive_ring
  rw [e, e] at hEq
  exact h hEq

end MaskLine

/-! ## §3. Weighted moments of distinct points -/

section Moments
variable {F : Type} [LawfulField F]

def lsum : List F → F
  | [] => zero
  | a :: as => add a (lsum as)

/-- Pointwise product, truncated to the shorter list. -/
def pmul : List F → List F → List F
  | a :: as, b :: bs => mul a b :: pmul as bs
  | _, _ => []

theorem pmul_length : ∀ (as bs : List F), as.length = bs.length →
    (pmul as bs).length = bs.length
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | _ :: as, _ :: bs, h => by
    show (pmul as bs).length + 1 = bs.length + 1
    rw [pmul_length as bs (Nat.succ.inj h)]

theorem pmul_right_comm : ∀ (as bs cs : List F), pmul (pmul as bs) cs = pmul (pmul as cs) bs
  | [], _, _ => rfl
  | _ :: _, [], [] => rfl
  | _ :: _, [], _ :: _ => rfl
  | _ :: _, _ :: _, [] => rfl
  | a :: as, b :: bs, c :: cs => by
    show mul (mul a b) c :: pmul (pmul as bs) cs = mul (mul a c) b :: pmul (pmul as cs) bs
    rw [pmul_right_comm as bs cs]
    have e : mul (mul a b) c = mul (mul a c) b := by constructive_ring
    rw [e]

theorem pmul_inv_cancel : ∀ (cs ds : List F), (∀ d ∈ ds, d ≠ zero) → cs.length = ds.length →
    pmul (pmul cs ds) (ds.map LawfulField.inv) = cs
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h
  | c :: cs, d :: ds, hd, h => by
    have hi := LawfulField.mul_inv_cancel (hd d List.mem_cons_self)
    show mul (mul c d) (LawfulField.inv d) :: pmul (pmul cs ds) (ds.map LawfulField.inv) =
      c :: cs
    rw [pmul_inv_cancel cs ds (fun t ht => hd t (List.mem_cons_of_mem _ ht)) (Nat.succ.inj h)]
    generalize LawfulField.inv d = j at hi
    have e : mul (mul c d) j = mul c (mul d j) := by constructive_ring
    rw [e, hi, LawfulCommRing.mul_one]

theorem lsum_pmul_shift (x : F) : ∀ (cs xs : List F), cs.length = xs.length →
    lsum (pmul cs (xs.map (fun t => sub t x))) = sub (lsum (pmul cs xs)) (mul x (lsum cs))
  | [], [], _ => by
    show (zero : F) = sub zero (mul x zero)
    constructive_ring
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | c :: cs, t :: xs, h => by
    show add (mul c (sub t x)) (lsum (pmul cs (xs.map (fun t => sub t x)))) =
      sub (add (mul c t) (lsum (pmul cs xs))) (mul x (add c (lsum cs)))
    rw [lsum_pmul_shift x cs xs (Nat.succ.inj h)]
    constructive_ring

/-- `moments n xs cs = [Σ_j c_j x_j^k]` for `k < n`. -/
def moments : Nat → List F → List F → List F
  | 0, _, _ => []
  | n + 1, xs, cs => lsum cs :: moments n xs (pmul cs xs)

theorem moments_length : ∀ (n : Nat) (xs cs : List F), (moments n xs cs).length = n
  | 0, _, _ => rfl
  | n + 1, xs, cs => by
    show (moments n xs (pmul cs xs)).length + 1 = n + 1
    rw [moments_length n xs (pmul cs xs)]

/-- `[m_1 - x m_0, m_2 - x m_1, …]`. -/
def shiftDiff (x : F) : List F → List F
  | a :: b :: r => sub b (mul x a) :: shiftDiff x (b :: r)
  | _ => []

theorem shiftDiff_length (x : F) : ∀ (a : F) (m : List F),
    (shiftDiff x (a :: m)).length = m.length
  | _, [] => rfl
  | _, b :: r => by
    show (shiftDiff x (b :: r)).length + 1 = r.length + 1
    rw [shiftDiff_length x b r]

/-- Removing the first point: the shifted moments are the moments of the other points with
    weights `c_j (x_j - x)`. -/
theorem shiftDiff_moments (x : F) (xs : List F) : ∀ (n : Nat) (c : F) (cs : List F),
    cs.length = xs.length →
    shiftDiff x (moments (n + 1) (x :: xs) (c :: cs)) =
      moments n xs (pmul cs (xs.map (fun t => sub t x)))
  | 0, _, _, _ => rfl
  | n + 1, c, cs, h => by
    have hl : (pmul cs xs).length = xs.length := pmul_length cs xs h
    have ih := shiftDiff_moments x xs n (mul c x) (pmul cs xs) hl
    show sub (lsum (mul c x :: pmul cs xs)) (mul x (lsum (c :: cs))) ::
        shiftDiff x (moments (n + 1) (x :: xs) (mul c x :: pmul cs xs)) =
      lsum (pmul cs (xs.map (fun t => sub t x))) ::
        moments n xs (pmul (pmul cs (xs.map (fun t => sub t x))) xs)
    rw [ih, lsum_pmul_shift x cs xs h, pmul_right_comm cs (xs.map (fun t => sub t x)) xs]
    have e : sub (lsum (mul c x :: pmul cs xs)) (mul x (lsum (c :: cs))) =
        sub (lsum (pmul cs xs)) (mul x (lsum cs)) := by
      show sub (add (mul c x) (lsum (pmul cs xs))) (mul x (add c (lsum cs))) =
        sub (lsum (pmul cs xs)) (mul x (lsum cs))
      constructive_ring
    rw [e]

/-- Weights from moments, one point at a time. -/
def momInv : List F → List F → List F
  | [], _ => []
  | x :: xs, m =>
    sub (m.headD zero)
        (lsum (pmul (momInv xs (shiftDiff x m))
          ((xs.map (fun t => sub t x)).map LawfulField.inv))) ::
      pmul (momInv xs (shiftDiff x m)) ((xs.map (fun t => sub t x)).map LawfulField.inv)

theorem momInv_length : ∀ (xs m : List F), m.length = xs.length →
    (momInv xs m).length = xs.length
  | [], _, _ => rfl
  | _ :: _, [], h => by cases h
  | x :: xs, a :: m, h => by
    have hs : (shiftDiff x (a :: m)).length = xs.length :=
      (shiftDiff_length x a m).trans (Nat.succ.inj h)
    have ih := momInv_length xs (shiftDiff x (a :: m)) hs
    have hB : ((xs.map (fun t => sub t x)).map LawfulField.inv).length = xs.length := by
      rw [List.length_map, List.length_map]
    show (pmul (momInv xs (shiftDiff x (a :: m)))
      ((xs.map (fun t => sub t x)).map LawfulField.inv)).length + 1 = xs.length + 1
    rw [pmul_length _ _ (ih.trans hB.symm), hB]

theorem shifted_points_ne_zero (x : F) (xs : List F) (hx : ¬ x ∈ xs) :
    ∀ d ∈ xs.map (fun t => sub t x), d ≠ zero := by
  intro d hd h0
  obtain ⟨t, ht, hEq⟩ := List.mem_map.mp hd
  rw [← hEq] at h0
  exact hx ((LawfulCommRing.sub_eq_zero_iff.mp h0) ▸ ht)

theorem momInv_moments : ∀ (xs cs : List F), xs.Nodup → cs.length = xs.length →
    momInv xs (moments xs.length xs cs) = cs
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h
  | x :: xs, c :: cs, hnd, h => by
    obtain ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
    have hl : cs.length = xs.length := Nat.succ.inj h
    have hlm : cs.length = (xs.map (fun t => sub t x)).length := hl.trans (List.length_map _).symm
    have hpl : (pmul cs (xs.map (fun t => sub t x))).length = xs.length := by
      rw [pmul_length cs _ hlm, List.length_map]
    have hs := shiftDiff_moments x xs xs.length c cs hl
    have ih := momInv_moments xs (pmul cs (xs.map (fun t => sub t x))) hnd' hpl
    show sub (lsum (c :: cs))
          (lsum (pmul (momInv xs (shiftDiff x (moments (xs.length + 1) (x :: xs) (c :: cs))))
            ((xs.map (fun t => sub t x)).map LawfulField.inv))) ::
        pmul (momInv xs (shiftDiff x (moments (xs.length + 1) (x :: xs) (c :: cs))))
          ((xs.map (fun t => sub t x)).map LawfulField.inv) = c :: cs
    rw [hs, ih, pmul_inv_cancel cs _ (shifted_points_ne_zero x xs hx) hlm]
    have e : sub (lsum (c :: cs)) (lsum cs) = c := by
      show sub (add c (lsum cs)) (lsum cs) = c
      constructive_ring
    rw [e]

theorem eq_of_head_shiftDiff (x : F) : ∀ (a b : F) (m m' : List F), m.length = m'.length →
    a = b → shiftDiff x (a :: m) = shiftDiff x (b :: m') → a :: m = b :: m'
  | _, _, [], [], _, hab, _ => by rw [hab]
  | _, _, [], _ :: _, h, _, _ => by cases h
  | _, _, _ :: _, [], h, _, _ => by cases h
  | a, b, c :: m, d :: m', h, hab, hs => by
    have hs' : sub c (mul x a) :: shiftDiff x (c :: m) =
        sub d (mul x b) :: shiftDiff x (d :: m') := hs
    obtain ⟨h0, hT⟩ := List.cons.inj hs'
    rw [hab] at h0
    have e1 : c = add (sub c (mul x b)) (mul x b) := by constructive_ring
    have e2 : add (sub d (mul x b)) (mul x b) = d := by constructive_ring
    have hcd : c = d := by
      rw [e1, h0]
      exact e2
    rw [hab, eq_of_head_shiftDiff x c d m m' (Nat.succ.inj h) hcd hT]

theorem moments_momInv : ∀ (xs m : List F), xs.Nodup → m.length = xs.length →
    moments xs.length xs (momInv xs m) = m
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h
  | x :: xs, a :: m, hnd, h => by
    obtain ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
    have hs : (shiftDiff x (a :: m)).length = xs.length :=
      (shiftDiff_length x a m).trans (Nat.succ.inj h)
    have ih := moments_momInv xs (shiftDiff x (a :: m)) hnd' hs
    have hA := momInv_length xs (shiftDiff x (a :: m)) hs
    have hB : ((xs.map (fun t => sub t x)).map LawfulField.inv).length = xs.length := by
      rw [List.length_map, List.length_map]
    have hlm : (momInv xs (shiftDiff x (a :: m))).length = (xs.map (fun t => sub t x)).length :=
      hA.trans (List.length_map _).symm
    have hcsl : (pmul (momInv xs (shiftDiff x (a :: m)))
        ((xs.map (fun t => sub t x)).map LawfulField.inv)).length = xs.length := by
      rw [pmul_length _ _ (hA.trans hB.symm), hB]
    have hback : pmul (pmul (momInv xs (shiftDiff x (a :: m)))
        ((xs.map (fun t => sub t x)).map LawfulField.inv)) (xs.map (fun t => sub t x)) =
        momInv xs (shiftDiff x (a :: m)) := by
      rw [pmul_right_comm]
      exact pmul_inv_cancel _ _ (shifted_points_ne_zero x xs hx) hlm
    have hmom : moments xs.length xs (pmul (pmul (momInv xs (shiftDiff x (a :: m)))
        ((xs.map (fun t => sub t x)).map LawfulField.inv)) (xs.map (fun t => sub t x))) =
        shiftDiff x (a :: m) := by
      rw [hback]
      exact ih
    show moments (xs.length + 1) (x :: xs)
      (sub a (lsum (pmul (momInv xs (shiftDiff x (a :: m)))
          ((xs.map (fun t => sub t x)).map LawfulField.inv))) ::
        pmul (momInv xs (shiftDiff x (a :: m)))
          ((xs.map (fun t => sub t x)).map LawfulField.inv)) = a :: m
    revert hcsl hmom
    generalize pmul (momInv xs (shiftDiff x (a :: m)))
      ((xs.map (fun t => sub t x)).map LawfulField.inv) = cs
    intro hcsl hmom
    have key : shiftDiff x (lsum (sub a (lsum cs) :: cs) ::
        moments xs.length (x :: xs) (pmul (sub a (lsum cs) :: cs) (x :: xs))) =
        shiftDiff x (a :: m) := by
      show shiftDiff x (moments (xs.length + 1) (x :: xs) (sub a (lsum cs) :: cs)) =
        shiftDiff x (a :: m)
      rw [shiftDiff_moments x xs xs.length _ cs hcsl]
      exact hmom
    have hhead : lsum (sub a (lsum cs) :: cs) = a := by
      show add (sub a (lsum cs)) (lsum cs) = a
      constructive_ring
    show lsum (sub a (lsum cs) :: cs) ::
      moments xs.length (x :: xs) (pmul (sub a (lsum cs) :: cs) (x :: xs)) = a :: m
    exact eq_of_head_shiftDiff x _ a _ m
      ((moments_length _ _ _).trans (Nat.succ.inj h).symm) hhead key

end Moments

/-! ## §4. Lemma V2.3 (c): the five scalars of one fold -/

section FoldScalars
variable {F : Type} [LawfulField F]

/-- `Σ_j w_j g(x_j) f_j`. -/
@[expose] def rowSum (g : F → F) : List F → List F → List F → F
  | x :: xs, w :: ws, f :: fs => add (mul (mul w (g x)) f) (rowSum g xs ws fs)
  | _, _, _ => zero

/-- Linear part of `(σ_even, τ_01, τ_10, c_F, c_G)` as a function of `(F_j)`: column `j` is
    `w_j (1, x_j, -1/x_j, (1 + φ x_j) x_j², -(1 + φ x_j) x_j)`. -/
@[expose] def foldScalars (φ : F) (xs ws fs : List F) : List F :=
  [rowSum (fun _ => one) xs ws fs,
   rowSum (fun x => x) xs ws fs,
   rowSum (fun x => neg (LawfulField.inv x)) xs ws fs,
   rowSum (fun x => mul (add one (mul φ x)) (mul x x)) xs ws fs,
   rowSum (fun x => neg (mul (add one (mul φ x)) x)) xs ws fs]

def termVec (g : F → F) : List F → List F → List F → List F
  | x :: xs, w :: ws, f :: fs => mul (mul w (g x)) f :: termVec g xs ws fs
  | _, _, _ => []

theorem lsum_termVec (g : F → F) : ∀ (xs ws fs : List F),
    lsum (termVec g xs ws fs) = rowSum g xs ws fs
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
  | x :: xs, w :: ws, f :: fs => by
    show add (mul (mul w (g x)) f) (lsum (termVec g xs ws fs)) =
      add (mul (mul w (g x)) f) (rowSum g xs ws fs)
    rw [lsum_termVec g xs ws fs]

theorem pmul_termVec (g : F → F) : ∀ (xs ws fs : List F),
    pmul (termVec g xs ws fs) xs = termVec (fun x => mul (g x) x) xs ws fs
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
  | x :: xs, w :: ws, f :: fs => by
    show mul (mul (mul w (g x)) f) x :: pmul (termVec g xs ws fs) xs =
      mul (mul w (mul (g x) x)) f :: termVec (fun x => mul (g x) x) xs ws fs
    rw [pmul_termVec g xs ws fs]
    have e : mul (mul (mul w (g x)) f) x = mul (mul w (mul (g x) x)) f := by constructive_ring
    rw [e]

theorem termVec_length (g : F → F) : ∀ (xs ws fs : List F), ws.length = xs.length →
    fs.length = xs.length → (termVec g xs ws fs).length = xs.length
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, h, _ => by cases h
  | _ :: _, _ :: _, [], _, h => by cases h
  | _ :: xs, _ :: ws, _ :: fs, hw, hf => by
    show (termVec g xs ws fs).length + 1 = xs.length + 1
    rw [termVec_length g xs ws fs (Nat.succ.inj hw) (Nat.succ.inj hf)]

theorem moments_termVec (g : F → F) (n : Nat) (xs ws fs : List F) :
    moments (n + 1) xs (termVec g xs ws fs) =
      rowSum g xs ws fs :: moments n xs (termVec (fun x => mul (g x) x) xs ws fs) := by
  show lsum (termVec g xs ws fs) :: moments n xs (pmul (termVec g xs ws fs) xs) = _
  rw [lsum_termVec, pmul_termVec]

theorem rowSum_congr (g k : F → F) : ∀ (xs ws fs : List F), (∀ x ∈ xs, k x = g x) →
    rowSum k xs ws fs = rowSum g xs ws fs
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | _ :: _, _ :: _, [], _ => rfl
  | x :: xs, w :: ws, f :: fs, hk => by
    show add (mul (mul w (k x)) f) (rowSum k xs ws fs) =
      add (mul (mul w (g x)) f) (rowSum g xs ws fs)
    rw [rowSum_congr g k xs ws fs (fun t ht => hk t (List.mem_cons_of_mem _ ht)),
      hk x List.mem_cons_self]

theorem rowSum_combo (a b : F) (g h k : F → F) : ∀ (xs ws fs : List F),
    (∀ x ∈ xs, k x = add (mul a (g x)) (mul b (h x))) →
    rowSum k xs ws fs = add (mul a (rowSum g xs ws fs)) (mul b (rowSum h xs ws fs))
  | [], _, _, _ => by
    show (zero : F) = add (mul a zero) (mul b zero)
    constructive_ring
  | _ :: _, [], _, _ => by
    show (zero : F) = add (mul a zero) (mul b zero)
    constructive_ring
  | _ :: _, _ :: _, [], _ => by
    show (zero : F) = add (mul a zero) (mul b zero)
    constructive_ring
  | x :: xs, w :: ws, f :: fs, hk => by
    show add (mul (mul w (k x)) f) (rowSum k xs ws fs) =
      add (mul a (add (mul (mul w (g x)) f) (rowSum g xs ws fs)))
        (mul b (add (mul (mul w (h x)) f) (rowSum h xs ws fs)))
    rw [rowSum_combo a b g h k xs ws fs (fun t ht => hk t (List.mem_cons_of_mem _ ht)),
      hk x List.mem_cons_self]
    constructive_ring

/-- A linear relation among five row functions on the points is a linear relation among the
    five row sums. -/
theorem rowSum_relation (l0 l1 l2 l3 l4 : F) (g0 g1 g2 g3 g4 : F → F) :
    ∀ (xs ws fs : List F),
    (∀ x ∈ xs, add (add (add (add (mul l0 (g0 x)) (mul l1 (g1 x))) (mul l2 (g2 x)))
      (mul l3 (g3 x))) (mul l4 (g4 x)) = zero) →
    add (add (add (add (mul l0 (rowSum g0 xs ws fs)) (mul l1 (rowSum g1 xs ws fs)))
      (mul l2 (rowSum g2 xs ws fs))) (mul l3 (rowSum g3 xs ws fs)))
      (mul l4 (rowSum g4 xs ws fs)) = zero
  | [], _, _, _ => by
    show add (add (add (add (mul l0 zero) (mul l1 zero)) (mul l2 zero)) (mul l3 zero))
      (mul l4 zero) = (zero : F)
    constructive_ring
  | _ :: _, [], _, _ => by
    show add (add (add (add (mul l0 zero) (mul l1 zero)) (mul l2 zero)) (mul l3 zero))
      (mul l4 zero) = (zero : F)
    constructive_ring
  | _ :: _, _ :: _, [], _ => by
    show add (add (add (add (mul l0 zero) (mul l1 zero)) (mul l2 zero)) (mul l3 zero))
      (mul l4 zero) = (zero : F)
    constructive_ring
  | x :: xs, w :: ws, f :: fs, hk => by
    have ih := rowSum_relation l0 l1 l2 l3 l4 g0 g1 g2 g3 g4 xs ws fs
      (fun t ht => hk t (List.mem_cons_of_mem _ ht))
    have hx := hk x List.mem_cons_self
    show add (add (add (add
        (mul l0 (add (mul (mul w (g0 x)) f) (rowSum g0 xs ws fs)))
        (mul l1 (add (mul (mul w (g1 x)) f) (rowSum g1 xs ws fs))))
        (mul l2 (add (mul (mul w (g2 x)) f) (rowSum g2 xs ws fs))))
        (mul l3 (add (mul (mul w (g3 x)) f) (rowSum g3 xs ws fs))))
        (mul l4 (add (mul (mul w (g4 x)) f) (rowSum g4 xs ws fs))) = zero
    have e : add (add (add (add
        (mul l0 (add (mul (mul w (g0 x)) f) (rowSum g0 xs ws fs)))
        (mul l1 (add (mul (mul w (g1 x)) f) (rowSum g1 xs ws fs))))
        (mul l2 (add (mul (mul w (g2 x)) f) (rowSum g2 xs ws fs))))
        (mul l3 (add (mul (mul w (g3 x)) f) (rowSum g3 xs ws fs))))
        (mul l4 (add (mul (mul w (g4 x)) f) (rowSum g4 xs ws fs))) =
      add (mul (mul w f)
          (add (add (add (add (mul l0 (g0 x)) (mul l1 (g1 x))) (mul l2 (g2 x)))
            (mul l3 (g3 x))) (mul l4 (g4 x))))
        (add (add (add (add (mul l0 (rowSum g0 xs ws fs)) (mul l1 (rowSum g1 xs ws fs)))
          (mul l2 (rowSum g2 xs ws fs))) (mul l3 (rowSum g3 xs ws fs)))
          (mul l4 (rowSum g4 xs ws fs))) := by constructive_ring
    rw [e, hx, ih]
    constructive_ring

/-- `(M_0, …, M_4) ↦ (M_1, M_2, -M_0, M_3 + φ M_4, -(M_2 + φ M_3))`. -/
def foldMix (φ : F) : List F → List F
  | [m0, m1, m2, m3, m4] => [m1, m2, neg m0, add m3 (mul φ m4), neg (add m2 (mul φ m3))]
  | _ => []

def foldUnmix (φ : F) : List F → List F
  | [s0, s1, s2, s3, s4] =>
    [neg s2, s0, s1, neg (mul (add s4 s1) (LawfulField.inv φ)),
      mul (add s3 (mul (add s4 s1) (LawfulField.inv φ))) (LawfulField.inv φ)]
  | _ => []

theorem foldUnmix_foldMix (φ : F) (hφ : φ ≠ zero) (m0 m1 m2 m3 m4 : F) :
    foldUnmix φ (foldMix φ [m0, m1, m2, m3, m4]) = [m0, m1, m2, m3, m4] := by
  have hi := LawfulField.mul_inv_cancel hφ
  show [neg (neg m0), m1, m2,
      neg (mul (add (neg (add m2 (mul φ m3))) m2) (LawfulField.inv φ)),
      mul (add (add m3 (mul φ m4))
        (mul (add (neg (add m2 (mul φ m3))) m2) (LawfulField.inv φ))) (LawfulField.inv φ)] =
    [m0, m1, m2, m3, m4]
  generalize LawfulField.inv φ = j at hi
  have e0 : neg (neg m0) = m0 := by constructive_ring
  have e3 : neg (mul (add (neg (add m2 (mul φ m3))) m2) j) = mul m3 (mul φ j) := by
    constructive_ring
  have e4 : mul (add (add m3 (mul φ m4)) (mul (add (neg (add m2 (mul φ m3))) m2) j)) j =
      add (mul m4 (mul φ j)) (mul (mul m3 j) (sub one (mul φ j))) := by constructive_ring
  have f3 : mul m3 one = m3 := by constructive_ring
  have f4 : add (mul m4 one) (mul (mul m3 j) (sub one one)) = m4 := by constructive_ring
  rw [e0, e3, e4, hi, f3, f4]

theorem foldMix_foldUnmix (φ : F) (hφ : φ ≠ zero) (s0 s1 s2 s3 s4 : F) :
    foldMix φ (foldUnmix φ [s0, s1, s2, s3, s4]) = [s0, s1, s2, s3, s4] := by
  have hi := LawfulField.mul_inv_cancel hφ
  show [s0, s1, neg (neg s2),
      add (neg (mul (add s4 s1) (LawfulField.inv φ)))
        (mul φ (mul (add s3 (mul (add s4 s1) (LawfulField.inv φ))) (LawfulField.inv φ))),
      neg (add s1 (mul φ (neg (mul (add s4 s1) (LawfulField.inv φ)))))] =
    [s0, s1, s2, s3, s4]
  generalize LawfulField.inv φ = j at hi
  have e2 : neg (neg s2) = s2 := by constructive_ring
  have e3 : add (neg (mul (add s4 s1) j)) (mul φ (mul (add s3 (mul (add s4 s1) j)) j)) =
      add (mul (mul φ j) (add s3 (mul (add s4 s1) j))) (neg (mul (add s4 s1) j)) := by
    constructive_ring
  have e4 : neg (add s1 (mul φ (neg (mul (add s4 s1) j)))) =
      neg (sub s1 (mul (mul φ j) (add s4 s1))) := by constructive_ring
  have f3 : add (mul one (add s3 (mul (add s4 s1) j))) (neg (mul (add s4 s1) j)) = s3 := by
    constructive_ring
  have f4 : neg (sub s1 (mul one (add s4 s1))) = s4 := by constructive_ring
  rw [e2, e3, e4, hi, f3, f4]

theorem length_eq_five {α : Type} : ∀ (l : List α), l.length = 5 →
    ∃ a b c d e, l = [a, b, c, d, e]
  | [a, b, c, d, e], _ => ⟨a, b, c, d, e, rfl⟩
  | [], h => by cases h
  | [_], h => by cases h
  | [_, _], h => by cases h
  | [_, _, _], h => by cases h
  | [_, _, _, _], h => by cases h
  | _ :: _ :: _ :: _ :: _ :: _ :: _, h => by cases h

/-- With `x_j ≠ 0` the five scalars are `foldMix` of the moments `Σ_j (w_j f_j / x_j) x_j^k`,
    `k < 5`. -/
theorem foldScalars_eq_mix (φ : F) (xs ws fs : List F) (hx : ∀ x ∈ xs, x ≠ zero) :
    foldScalars φ xs ws fs = foldMix φ (moments 5 xs (termVec LawfulField.inv xs ws fs)) := by
  rw [moments_termVec, moments_termVec, moments_termVec, moments_termVec, moments_termVec]
  have c0 : rowSum (fun _ => one) xs ws fs =
      rowSum (fun x => mul (LawfulField.inv x) x) xs ws fs :=
    rowSum_congr _ _ xs ws fs (fun x hm => (LawfulField.inv_mul_cancel (hx x hm)).symm)
  have c1 : rowSum (fun x => x) xs ws fs =
      rowSum (fun x => mul (mul (LawfulField.inv x) x) x) xs ws fs :=
    rowSum_congr _ _ xs ws fs (fun x hm => by
      show x = mul (mul (LawfulField.inv x) x) x
      rw [LawfulField.inv_mul_cancel (hx x hm), LawfulCommRing.one_mul])
  have c2 : rowSum (fun x => neg (LawfulField.inv x)) xs ws fs =
      neg (rowSum LawfulField.inv xs ws fs) :=
    (rowSum_combo (neg one) zero LawfulField.inv LawfulField.inv
      (fun x => neg (LawfulField.inv x)) xs ws fs (fun x _ => by
        show neg (LawfulField.inv x) =
          add (mul (neg one) (LawfulField.inv x)) (mul zero (LawfulField.inv x))
        constructive_ring)).trans (by constructive_ring)
  have c3 : rowSum (fun x => mul (add one (mul φ x)) (mul x x)) xs ws fs =
      add (rowSum (fun x => mul (mul (mul (LawfulField.inv x) x) x) x) xs ws fs)
        (mul φ (rowSum (fun x => mul (mul (mul (mul (LawfulField.inv x) x) x) x) x) xs ws fs)) :=
    (rowSum_combo one φ (fun x => mul (mul (mul (LawfulField.inv x) x) x) x)
      (fun x => mul (mul (mul (mul (LawfulField.inv x) x) x) x) x)
      (fun x => mul (add one (mul φ x)) (mul x x)) xs ws fs (fun x hm => by
        have hji := LawfulField.inv_mul_cancel (hx x hm)
        show mul (add one (mul φ x)) (mul x x) =
          add (mul one (mul (mul (mul (LawfulField.inv x) x) x) x))
            (mul φ (mul (mul (mul (mul (LawfulField.inv x) x) x) x) x))
        generalize LawfulField.inv x = j at hji
        have e : add (mul one (mul (mul (mul j x) x) x))
            (mul φ (mul (mul (mul (mul j x) x) x) x)) =
            mul (mul j x) (mul (add one (mul φ x)) (mul x x)) := by constructive_ring
        rw [e, hji, LawfulCommRing.one_mul])).trans (by constructive_ring)
  have c4 : rowSum (fun x => neg (mul (add one (mul φ x)) x)) xs ws fs =
      neg (add (rowSum (fun x => mul (mul (LawfulField.inv x) x) x) xs ws fs)
        (mul φ (rowSum (fun x => mul (mul (mul (LawfulField.inv x) x) x) x) xs ws fs))) :=
    (rowSum_combo (neg one) (neg φ) (fun x => mul (mul (LawfulField.inv x) x) x)
      (fun x => mul (mul (mul (LawfulField.inv x) x) x) x)
      (fun x => neg (mul (add one (mul φ x)) x)) xs ws fs (fun x hm => by
        have hji := LawfulField.inv_mul_cancel (hx x hm)
        show neg (mul (add one (mul φ x)) x) =
          add (mul (neg one) (mul (mul (LawfulField.inv x) x) x))
            (mul (neg φ) (mul (mul (mul (LawfulField.inv x) x) x) x))
        generalize LawfulField.inv x = j at hji
        have e : add (mul (neg one) (mul (mul j x) x)) (mul (neg φ) (mul (mul (mul j x) x) x)) =
            mul (mul j x) (neg (mul (add one (mul φ x)) x)) := by constructive_ring
        rw [e, hji, LawfulCommRing.one_mul])).trans (by constructive_ring)
  show [rowSum (fun _ => one) xs ws fs, rowSum (fun x => x) xs ws fs,
      rowSum (fun x => neg (LawfulField.inv x)) xs ws fs,
      rowSum (fun x => mul (add one (mul φ x)) (mul x x)) xs ws fs,
      rowSum (fun x => neg (mul (add one (mul φ x)) x)) xs ws fs] =
    [rowSum (fun x => mul (LawfulField.inv x) x) xs ws fs,
      rowSum (fun x => mul (mul (LawfulField.inv x) x) x) xs ws fs,
      neg (rowSum LawfulField.inv xs ws fs),
      add (rowSum (fun x => mul (mul (mul (LawfulField.inv x) x) x) x) xs ws fs)
        (mul φ (rowSum (fun x => mul (mul (mul (mul (LawfulField.inv x) x) x) x) x) xs ws fs)),
      neg (add (rowSum (fun x => mul (mul (LawfulField.inv x) x) x) xs ws fs)
        (mul φ (rowSum (fun x => mul (mul (mul (LawfulField.inv x) x) x) x) xs ws fs)))]
  rw [c0, c1, c2, c3, c4]

/-- `f_j = c_j x_j / w_j`. -/
def unTerms : List F → List F → List F → List F
  | x :: xs, w :: ws, c :: cs => mul c (mul x (LawfulField.inv w)) :: unTerms xs ws cs
  | _, _, _ => []

theorem unTerms_length : ∀ (xs ws cs : List F), ws.length = xs.length →
    cs.length = xs.length → (unTerms xs ws cs).length = xs.length
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, h, _ => by cases h
  | _ :: _, _ :: _, [], _, h => by cases h
  | _ :: xs, _ :: ws, _ :: cs, hw, hc => by
    show (unTerms xs ws cs).length + 1 = xs.length + 1
    rw [unTerms_length xs ws cs (Nat.succ.inj hw) (Nat.succ.inj hc)]

theorem termVec_unTerms : ∀ (xs ws cs : List F), (∀ x ∈ xs, x ≠ zero) → (∀ w ∈ ws, w ≠ zero) →
    ws.length = xs.length → cs.length = xs.length →
    termVec LawfulField.inv xs ws (unTerms xs ws cs) = cs
  | [], _, [], _, _, _, _ => rfl
  | [], _, _ :: _, _, _, _, h => by cases h
  | _ :: _, [], _, _, _, h, _ => by cases h
  | _ :: _, _ :: _, [], _, _, _, h => by cases h
  | x :: xs, w :: ws, c :: cs, hx, hw, hwl, hcl => by
    have hix := LawfulField.mul_inv_cancel (hx x List.mem_cons_self)
    have hiw := LawfulField.mul_inv_cancel (hw w List.mem_cons_self)
    show mul (mul w (LawfulField.inv x)) (mul c (mul x (LawfulField.inv w))) ::
      termVec LawfulField.inv xs ws (unTerms xs ws cs) = c :: cs
    rw [termVec_unTerms xs ws cs (fun t ht => hx t (List.mem_cons_of_mem _ ht))
      (fun t ht => hw t (List.mem_cons_of_mem _ ht)) (Nat.succ.inj hwl) (Nat.succ.inj hcl)]
    have e : ∀ jx jw : F, mul x jx = one → mul w jw = one →
        mul (mul w jx) (mul c (mul x jw)) = c := by
      intro jx jw h1 h2
      have e1 : mul (mul w jx) (mul c (mul x jw)) = mul c (mul (mul x jx) (mul w jw)) := by
        constructive_ring
      rw [e1, h1, h2]
      constructive_ring
    rw [e _ _ hix hiw]

theorem unTerms_termVec : ∀ (xs ws fs : List F), (∀ x ∈ xs, x ≠ zero) → (∀ w ∈ ws, w ≠ zero) →
    ws.length = xs.length → fs.length = xs.length →
    unTerms xs ws (termVec LawfulField.inv xs ws fs) = fs
  | [], _, [], _, _, _, _ => rfl
  | [], _, _ :: _, _, _, _, h => by cases h
  | _ :: _, [], _, _, _, h, _ => by cases h
  | _ :: _, _ :: _, [], _, _, _, h => by cases h
  | x :: xs, w :: ws, f :: fs, hx, hw, hwl, hfl => by
    have hix := LawfulField.mul_inv_cancel (hx x List.mem_cons_self)
    have hiw := LawfulField.mul_inv_cancel (hw w List.mem_cons_self)
    show mul (mul (mul w (LawfulField.inv x)) f) (mul x (LawfulField.inv w)) ::
      unTerms xs ws (termVec LawfulField.inv xs ws fs) = f :: fs
    rw [unTerms_termVec xs ws fs (fun t ht => hx t (List.mem_cons_of_mem _ ht))
      (fun t ht => hw t (List.mem_cons_of_mem _ ht)) (Nat.succ.inj hwl) (Nat.succ.inj hfl)]
    have e : ∀ jx jw : F, mul x jx = one → mul w jw = one →
        mul (mul (mul w jx) f) (mul x jw) = f := by
      intro jx jw h1 h2
      have e1 : mul (mul (mul w jx) f) (mul x jw) = mul f (mul (mul x jx) (mul w jw)) := by
        constructive_ring
      rw [e1, h1, h2]
      constructive_ring
    rw [e _ _ hix hiw]

/-- Explicit inverse of `foldScalars φ xs ws`. -/
def foldScalarsInv (φ : F) (xs ws ss : List F) : List F :=
  unTerms xs ws (momInv xs (foldUnmix φ ss))

theorem foldScalarsInv_length (φ : F) (xs ws ss : List F) (hxl : xs.length = 5)
    (hwl : ws.length = 5) (hsl : ss.length = 5) : (foldScalarsInv φ xs ws ss).length = 5 := by
  obtain ⟨s0, s1, s2, s3, s4, hs⟩ := length_eq_five ss hsl
  rw [hs]
  have hU : (foldUnmix φ [s0, s1, s2, s3, s4]).length = xs.length := by
    show 5 = xs.length
    exact hxl.symm
  exact (unTerms_length xs ws _ (hwl.trans hxl.symm) (momInv_length xs _ hU)).trans hxl

theorem foldScalarsInv_foldScalars (φ : F) (xs ws fs : List F) (hnd : xs.Nodup)
    (hx : ∀ x ∈ xs, x ≠ zero) (hw : ∀ w ∈ ws, w ≠ zero) (hφ : φ ≠ zero) (hxl : xs.length = 5)
    (hwl : ws.length = 5) (hfl : fs.length = 5) :
    foldScalarsInv φ xs ws (foldScalars φ xs ws fs) = fs := by
  have hT : (termVec LawfulField.inv xs ws fs).length = xs.length :=
    termVec_length _ xs ws fs (hwl.trans hxl.symm) (hfl.trans hxl.symm)
  obtain ⟨m0, m1, m2, m3, m4, hm⟩ :=
    length_eq_five _ (moments_length 5 xs (termVec LawfulField.inv xs ws fs))
  have hinv := momInv_moments xs (termVec LawfulField.inv xs ws fs) hnd hT
  rw [hxl] at hinv
  show unTerms xs ws (momInv xs (foldUnmix φ (foldScalars φ xs ws fs))) = fs
  rw [foldScalars_eq_mix φ xs ws fs hx, hm, foldUnmix_foldMix φ hφ, ← hm, hinv]
  exact unTerms_termVec xs ws fs hx hw (hwl.trans hxl.symm) (hfl.trans hxl.symm)

theorem foldScalars_foldScalarsInv (φ : F) (xs ws ss : List F) (hnd : xs.Nodup)
    (hx : ∀ x ∈ xs, x ≠ zero) (hw : ∀ w ∈ ws, w ≠ zero) (hφ : φ ≠ zero) (hxl : xs.length = 5)
    (hwl : ws.length = 5) (hsl : ss.length = 5) :
    foldScalars φ xs ws (foldScalarsInv φ xs ws ss) = ss := by
  obtain ⟨s0, s1, s2, s3, s4, hs⟩ := length_eq_five ss hsl
  rw [hs]
  have hU : (foldUnmix φ [s0, s1, s2, s3, s4]).length = xs.length := by
    show 5 = xs.length
    exact hxl.symm
  have hC := momInv_length xs _ hU
  have hmm := moments_momInv xs _ hnd hU
  rw [hxl] at hmm
  show foldScalars φ xs ws (unTerms xs ws (momInv xs (foldUnmix φ [s0, s1, s2, s3, s4]))) =
    [s0, s1, s2, s3, s4]
  rw [foldScalars_eq_mix φ xs ws _ hx,
    termVec_unTerms xs ws _ hx hw (hwl.trans hxl.symm) hC, hmm]
  exact foldMix_foldUnmix φ hφ s0 s1 s2 s3 s4

def foldScalarEquiv (φ : F) (xs ws : List F) (hnd : xs.Nodup) (hx : ∀ x ∈ xs, x ≠ zero)
    (hw : ∀ w ∈ ws, w ≠ zero) (hφ : φ ≠ zero) (hxl : xs.length = 5) (hwl : ws.length = 5) :
    SimpleEquiv {fs : List F // fs.length = 5} {ss : List F // ss.length = 5} where
  toFun fs := ⟨foldScalars φ xs ws fs.1, rfl⟩
  invFun ss := ⟨foldScalarsInv φ xs ws ss.1, foldScalarsInv_length φ xs ws ss.1 hxl hwl ss.2⟩
  left_inv fs := Subtype.ext (foldScalarsInv_foldScalars φ xs ws fs.1 hnd hx hw hφ hxl hwl fs.2)
  right_inv ss := Subtype.ext (foldScalars_foldScalarsInv φ xs ws ss.1 hnd hx hw hφ hxl hwl ss.2)

theorem foldScalarEquiv_apply (φ : F) (xs ws : List F) (hnd : xs.Nodup) (hx : ∀ x ∈ xs, x ≠ zero)
    (hw : ∀ w ∈ ws, w ≠ zero) (hφ : φ ≠ zero) (hxl : xs.length = 5) (hwl : ws.length = 5) (v : {l : List F // l.length = 5}) :
    ((foldScalarEquiv φ xs ws hnd hx hw hφ hxl hwl).toFun v).val = foldScalars φ xs ws v.val := by unfold foldScalarEquiv; rfl

/-- **Lemma V2.3 (c), linear part.** For five pairwise distinct nonzero points, five nonzero
    weights and `φ ≠ 0`, `foldScalars φ xs ws` is a bijection of `F^5` with inverse
    `foldScalarsInv φ xs ws`. -/
theorem v2_fold_scalar_matrix_bijective (φ : F) (xs ws : List F) (hnd : xs.Nodup)
    (hx : ∀ x ∈ xs, x ≠ zero) (hw : ∀ w ∈ ws, w ≠ zero) (hφ : φ ≠ zero) (hxl : xs.length = 5)
    (hwl : ws.length = 5) :
    ∃ Φ : SimpleEquiv {fs : List F // fs.length = 5} {ss : List F // ss.length = 5},
      (∀ fs, (Φ.toFun fs).1 = foldScalars φ xs ws fs.1) ∧
      (∀ ss, (Φ.invFun ss).1 = foldScalarsInv φ xs ws ss.1) :=
  ⟨foldScalarEquiv φ xs ws hnd hx hw hφ hxl hwl, fun _ => rfl, fun _ => rfl⟩

/-- **Lemma V2.3 (c).** The five scalars of one fold, an offset `d` (the part that depends on
    the cells below the blinders and on earlier values) plus `foldScalars` of uniform `(F_j)`,
    are five uniform field elements. -/
theorem v2_fold_scalars_perfectly_simulated (φ : F) (xs ws : List F) (hnd : xs.Nodup)
    (hx : ∀ x ∈ xs, x ≠ zero) (hw : ∀ w ∈ ws, w ≠ zero) (hφ : φ ≠ zero) (hxl : xs.length = 5)
    (hwl : ws.length = 5) :
    CoinBijectionSimulated
      (fun (d : {d : List F // d.length = 5}) (f : {fs : List F // fs.length = 5}) =>
        vadd d.1 (foldScalars φ xs ws f.1))
      (fun (s : {ss : List F // ss.length = 5}) => s.1) :=
  offset_simulated (foldScalarEquiv φ xs ws hnd hx hw hφ hxl hwl)

/-- With `φ = 0` the fifth scalar is minus the second, for any points and weights. -/
theorem tooth_zero_fold_challenge_not_surjective (xs ws : List F) :
    ¬ ∃ fs : List F, foldScalars zero xs ws fs = [zero, zero, zero, zero, one] := by
  rintro ⟨fs, h⟩
  have h' : [rowSum (fun _ => one) xs ws fs, rowSum (fun x => x) xs ws fs,
      rowSum (fun x => neg (LawfulField.inv x)) xs ws fs,
      rowSum (fun x => mul (add one (mul zero x)) (mul x x)) xs ws fs,
      rowSum (fun x => neg (mul (add one (mul zero x)) x)) xs ws fs] =
      [zero, zero, zero, zero, one] := h
  obtain ⟨-, t1⟩ := List.cons.inj h'
  obtain ⟨r1, t2⟩ := List.cons.inj t1
  obtain ⟨-, t3⟩ := List.cons.inj t2
  obtain ⟨-, t4⟩ := List.cons.inj t3
  obtain ⟨r4, -⟩ := List.cons.inj t4
  have c := rowSum_combo (neg one) zero (fun x => x) (fun x => x)
    (fun x => neg (mul (add one (mul zero x)) x)) xs ws fs (fun x _ => by
      show neg (mul (add one (mul zero x)) x) = add (mul (neg one) x) (mul zero x)
      constructive_ring)
  rw [r4, r1] at c
  have e : add (mul (neg one) zero) (mul zero zero) = (zero : F) := by constructive_ring
  exact LawfulField.zero_ne_one (c.trans e).symm

/-- With a repeated point the map has a kernel. -/
theorem tooth_repeated_mask_point_not_injective (φ x w1 w2 : F) (hw : w2 ≠ zero)
    (xs ws : List F) :
    ∃ fs fs' : List F, fs.length = xs.length + 2 ∧ fs'.length = xs.length + 2 ∧ ¬ (fs = fs') ∧
      foldScalars φ (x :: x :: xs) (w1 :: w2 :: ws) fs =
        foldScalars φ (x :: x :: xs) (w1 :: w2 :: ws) fs' := by
  have hg : ∀ g : F → F,
      rowSum g (x :: x :: xs) (w1 :: w2 :: ws) (w2 :: neg w1 :: xs.map (fun _ => zero)) =
      rowSum g (x :: x :: xs) (w1 :: w2 :: ws) (zero :: zero :: xs.map (fun _ => zero)) := by
    intro g
    show add (mul (mul w1 (g x)) w2) (add (mul (mul w2 (g x)) (neg w1))
        (rowSum g xs ws (xs.map (fun _ => zero)))) =
      add (mul (mul w1 (g x)) zero) (add (mul (mul w2 (g x)) zero)
        (rowSum g xs ws (xs.map (fun _ => zero))))
    constructive_ring
  have hlen : ∀ a b : F, (a :: b :: xs.map (fun _ => (zero : F))).length = xs.length + 2 := by
    intro a b
    show (xs.map (fun _ => (zero : F))).length + 1 + 1 = xs.length + 2
    rw [List.length_map]
  refine ⟨w2 :: neg w1 :: xs.map (fun _ => zero), zero :: zero :: xs.map (fun _ => zero),
    hlen _ _, hlen _ _, fun h => hw (List.cons.inj h).1, ?_⟩
  show [rowSum _ _ _ _, rowSum _ _ _ _, rowSum _ _ _ _, rowSum _ _ _ _, rowSum _ _ _ _] =
    [rowSum _ _ _ _, rowSum _ _ _ _, rowSum _ _ _ _, rowSum _ _ _ _, rowSum _ _ _ _]
  rw [hg, hg, hg, hg, hg]

/-- The relation behind `tooth_four_mask_points_not_surjective` at one root `x` of
    `X⁴ - e₁ X³ + e₂ X² - e₃ X + e₄`. -/
theorem four_point_row_relation (φ x e1 e2 e3 e4 j : F)
    (hpoly : add (sub (add (sub (mul (mul x x) (mul x x)) (mul e1 (mul x (mul x x))))
      (mul e2 (mul x x))) (mul e3 x)) e4 = zero)
    (hj : mul x j = one) :
    add (add (add (add
      (mul (neg (mul (mul φ φ) e3)) one)
      (mul (add (add one (mul φ e1)) (mul (mul φ φ) e2)) x))
      (mul (neg (mul (mul φ φ) e4)) (neg j)))
      (mul φ (mul (add one (mul φ x)) (mul x x))))
      (mul (add one (mul φ e1)) (neg (mul (add one (mul φ x)) x))) = zero := by
  have e : add (add (add (add
      (mul (neg (mul (mul φ φ) e3)) one)
      (mul (add (add one (mul φ e1)) (mul (mul φ φ) e2)) x))
      (mul (neg (mul (mul φ φ) e4)) (neg j)))
      (mul φ (mul (add one (mul φ x)) (mul x x))))
      (mul (add one (mul φ e1)) (neg (mul (add one (mul φ x)) x))) =
    add (mul (mul (mul φ φ) j)
        (add (sub (add (sub (mul (mul x x) (mul x x)) (mul e1 (mul x (mul x x))))
          (mul e2 (mul x x))) (mul e3 x)) e4))
      (mul (mul (mul φ φ) (sub (add (sub (mul x (mul x x)) (mul e1 (mul x x))) (mul e2 x)) e3))
        (sub one (mul x j))) := by constructive_ring
  rw [e, hpoly, hj]
  constructive_ring

/-- Four points cannot carry five scalars: the image of the `5 × 4` map lies in a hyperplane
    that misses `(0, 0, 0, 1, 0)`. -/
theorem tooth_four_mask_points_not_surjective (φ a b c d : F) (hφ : φ ≠ zero) (ha : a ≠ zero)
    (hb : b ≠ zero) (hc : c ≠ zero) (hd : d ≠ zero) (ws : List F) :
    ¬ ∃ fs : List F, foldScalars φ [a, b, c, d] ws fs = [zero, zero, zero, one, zero] := by
  rintro ⟨fs, h⟩
  obtain ⟨e1, he1⟩ : ∃ e : F, e = add (add (add a b) c) d := ⟨_, rfl⟩
  obtain ⟨e2, he2⟩ : ∃ e : F, e = add (add (add (add (add (mul a b) (mul a c)) (mul a d))
    (mul b c)) (mul b d)) (mul c d) := ⟨_, rfl⟩
  obtain ⟨e3, he3⟩ : ∃ e : F, e = add (add (add (mul (mul a b) c) (mul (mul a b) d))
    (mul (mul a c) d)) (mul (mul b c) d) := ⟨_, rfl⟩
  obtain ⟨e4, he4⟩ : ∃ e : F, e = mul (mul (mul a b) c) d := ⟨_, rfl⟩
  have hroot : ∀ x ∈ [a, b, c, d], x ≠ zero ∧
      add (sub (add (sub (mul (mul x x) (mul x x)) (mul e1 (mul x (mul x x))))
        (mul e2 (mul x x))) (mul e3 x)) e4 = zero := by
    intro x hx
    rw [he1, he2, he3, he4]
    rcases List.mem_cons.mp hx with h1 | hx
    · rw [h1]
      exact ⟨ha, by constructive_ring⟩
    rcases List.mem_cons.mp hx with h1 | hx
    · rw [h1]
      exact ⟨hb, by constructive_ring⟩
    rcases List.mem_cons.mp hx with h1 | hx
    · rw [h1]
      exact ⟨hc, by constructive_ring⟩
    rcases List.mem_cons.mp hx with h1 | hx
    · rw [h1]
      exact ⟨hd, by constructive_ring⟩
    · cases hx
  have hrel := rowSum_relation (neg (mul (mul φ φ) e3))
    (add (add one (mul φ e1)) (mul (mul φ φ) e2)) (neg (mul (mul φ φ) e4)) φ
    (add one (mul φ e1))
    (fun _ => one) (fun x => x) (fun x => neg (LawfulField.inv x))
    (fun x => mul (add one (mul φ x)) (mul x x)) (fun x => neg (mul (add one (mul φ x)) x))
    [a, b, c, d] ws fs (fun x hx =>
      four_point_row_relation φ x e1 e2 e3 e4 (LawfulField.inv x) (hroot x hx).2
        (LawfulField.mul_inv_cancel (hroot x hx).1))
  have h' : [rowSum (fun _ => one) [a, b, c, d] ws fs, rowSum (fun x => x) [a, b, c, d] ws fs,
      rowSum (fun x => neg (LawfulField.inv x)) [a, b, c, d] ws fs,
      rowSum (fun x => mul (add one (mul φ x)) (mul x x)) [a, b, c, d] ws fs,
      rowSum (fun x => neg (mul (add one (mul φ x)) x)) [a, b, c, d] ws fs] =
      [zero, zero, zero, one, zero] := h
  obtain ⟨r0, t1⟩ := List.cons.inj h'
  obtain ⟨r1, t2⟩ := List.cons.inj t1
  obtain ⟨r2, t3⟩ := List.cons.inj t2
  obtain ⟨r3, t4⟩ := List.cons.inj t3
  obtain ⟨r4, -⟩ := List.cons.inj t4
  rw [r0, r1, r2, r3, r4] at hrel
  have e : add (add (add (add (mul (neg (mul (mul φ φ) e3)) zero)
      (mul (add (add one (mul φ e1)) (mul (mul φ φ) e2)) zero))
      (mul (neg (mul (mul φ φ) e4)) zero)) (mul φ one)) (mul (add one (mul φ e1)) zero) = φ := by
    constructive_ring
  rw [e] at hrel
  exact hφ hrel

end FoldScalars

/-! ## §5. Newton interpolation on `List.map (evalCoeffs cs) xs` -/

section Interpolation
variable {F : Type} [LawfulField F]

/-- Coefficients of `y + (X - x) q(X)`. -/
def newtonUnquot (x : F) : F → List F → List F
  | y, [] => [y]
  | y, q0 :: qs => sub y (mul x q0) :: newtonUnquot x q0 qs

theorem newtonUnquot_length (x : F) : ∀ (y : F) (q : List F),
    (newtonUnquot x y q).length = q.length + 1
  | _, [] => rfl
  | _, q0 :: qs => by
    show (newtonUnquot x q0 qs).length + 1 = qs.length + 1 + 1
    rw [newtonUnquot_length x q0 qs]

theorem evalCoeffs_newtonUnquot (x : F) : ∀ (y : F) (q : List F) (t : F),
    evalCoeffs (newtonUnquot x y q) t = add y (mul (sub t x) (evalCoeffs q t))
  | y, [], t => by
    show add y (mul t zero) = add y (mul (sub t x) zero)
    constructive_ring
  | y, q0 :: qs, t => by
    show add (sub y (mul x q0)) (mul t (evalCoeffs (newtonUnquot x q0 qs) t)) =
      add y (mul (sub t x) (add q0 (mul t (evalCoeffs qs t))))
    rw [evalCoeffs_newtonUnquot x q0 qs t]
    constructive_ring

theorem newtonUnquot_quotLinear (x : F) : ∀ (cs : List F), cs ≠ [] →
    newtonUnquot x (evalCoeffs cs x) (quotLinear cs x) = cs
  | [], h => absurd rfl h
  | [c0], _ => by
    show [add c0 (mul x zero)] = [c0]
    have e : add c0 (mul x zero) = c0 := by constructive_ring
    rw [e]
  | c0 :: c1 :: cs, _ => by
    show sub (add c0 (mul x (evalCoeffs (c1 :: cs) x))) (mul x (evalCoeffs (c1 :: cs) x)) ::
      newtonUnquot x (evalCoeffs (c1 :: cs) x) (quotLinear (c1 :: cs) x) = c0 :: c1 :: cs
    rw [newtonUnquot_quotLinear x (c1 :: cs) (List.cons_ne_nil _ _)]
    have e : sub (add c0 (mul x (evalCoeffs (c1 :: cs) x))) (mul x (evalCoeffs (c1 :: cs) x)) =
        c0 := by constructive_ring
    rw [e]

/-- Divided differences against the first point. -/
def newtonDivDiff (x y : F) : List F → List F → List F
  | xi :: xs, yi :: ys =>
    mul (sub yi y) (LawfulField.inv (sub xi x)) :: newtonDivDiff x y xs ys
  | _, _ => []

theorem newtonDivDiff_length (x y : F) : ∀ (xs ys : List F), xs.length = ys.length →
    (newtonDivDiff x y xs ys).length = xs.length
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | _ :: xs, _ :: ys, h => by
    show (newtonDivDiff x y xs ys).length + 1 = xs.length + 1
    rw [newtonDivDiff_length x y xs ys (Nat.succ.inj h)]

/-- The coefficient list of length `|xs|` with values `ys` at `xs`. -/
def newtonInterp : List F → List F → List F
  | x :: xs, y :: ys => newtonUnquot x y (newtonInterp xs (newtonDivDiff x y xs ys))
  | _, _ => []

theorem newtonInterp_length : ∀ (xs ys : List F), xs.length = ys.length →
    (newtonInterp xs ys).length = xs.length
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: xs, y :: ys, h => by
    show (newtonUnquot x y (newtonInterp xs (newtonDivDiff x y xs ys))).length = xs.length + 1
    rw [newtonUnquot_length, newtonInterp_length xs (newtonDivDiff x y xs ys)
      (newtonDivDiff_length x y xs ys (Nat.succ.inj h)).symm]

theorem undo_newtonDivDiff (x y : F) (g : F → F) : ∀ (xs ys : List F), xs.length = ys.length →
    (∀ t ∈ xs, t ≠ x) → xs.map g = newtonDivDiff x y xs ys →
    xs.map (fun t => add y (mul (sub t x) (g t))) = ys
  | [], [], _, _, _ => rfl
  | [], _ :: _, h, _, _ => by cases h
  | _ :: _, [], h, _, _ => by cases h
  | t :: xs, yi :: ys, h, hx, hg => by
    have hg' : g t :: xs.map g =
        mul (sub yi y) (LawfulField.inv (sub t x)) :: newtonDivDiff x y xs ys := hg
    obtain ⟨h0, hTail⟩ := List.cons.inj hg'
    have hne : sub t x ≠ zero := fun h0' =>
      hx t (List.mem_cons_self) (LawfulCommRing.sub_eq_zero_iff.mp h0')
    have hi := LawfulField.mul_inv_cancel hne
    show add y (mul (sub t x) (g t)) :: xs.map (fun t => add y (mul (sub t x) (g t))) = yi :: ys
    rw [undo_newtonDivDiff x y g xs ys (Nat.succ.inj h)
      (fun t' ht' => hx t' (List.mem_cons_of_mem _ ht')) hTail, h0]
    generalize LawfulField.inv (sub t x) = j at hi
    have e : add y (mul (sub t x) (mul (sub yi y) j)) =
        add y (mul (sub yi y) (mul (sub t x) j)) := by constructive_ring
    rw [e, hi]
    have e2 : add y (mul (sub yi y) one) = yi := by constructive_ring
    rw [e2]

theorem eval_newtonInterp : ∀ (xs ys : List F), xs.Nodup → xs.length = ys.length →
    xs.map (evalCoeffs (newtonInterp xs ys)) = ys
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h
  | x :: xs, y :: ys, hnd, h => by
    obtain ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
    have hlen : xs.length = (newtonDivDiff x y xs ys).length :=
      (newtonDivDiff_length x y xs ys (Nat.succ.inj h)).symm
    have ih := eval_newtonInterp xs (newtonDivDiff x y xs ys) hnd' hlen
    have hTail := undo_newtonDivDiff x y
      (evalCoeffs (newtonInterp xs (newtonDivDiff x y xs ys))) xs ys
      (Nat.succ.inj h) (fun t ht hEq => hx (hEq ▸ ht)) ih
    show evalCoeffs (newtonUnquot x y (newtonInterp xs (newtonDivDiff x y xs ys))) x ::
      xs.map (evalCoeffs (newtonUnquot x y (newtonInterp xs (newtonDivDiff x y xs ys)))) =
      y :: ys
    have hFun : evalCoeffs (newtonUnquot x y (newtonInterp xs (newtonDivDiff x y xs ys))) =
        fun t => add y (mul (sub t x)
          (evalCoeffs (newtonInterp xs (newtonDivDiff x y xs ys)) t)) :=
      funext (fun t => evalCoeffs_newtonUnquot x y _ t)
    rw [hFun, hTail]
    have e : add y (mul (sub x x)
        (evalCoeffs (newtonInterp xs (newtonDivDiff x y xs ys)) x)) = y := by
      constructive_ring
    show add y (mul (sub x x) (evalCoeffs (newtonInterp xs (newtonDivDiff x y xs ys)) x)) ::
      ys = y :: ys
    rw [e]

theorem newtonDivDiff_eval (x : F) (cs : List F) : ∀ (xs : List F), (∀ t ∈ xs, t ≠ x) →
    newtonDivDiff x (evalCoeffs cs x) xs (xs.map (evalCoeffs cs)) =
      xs.map (evalCoeffs (quotLinear cs x))
  | [], _ => rfl
  | t :: xs, hx => by
    have hne : sub t x ≠ zero := fun h0 =>
      hx t (List.mem_cons_self) (LawfulCommRing.sub_eq_zero_iff.mp h0)
    have hi := LawfulField.mul_inv_cancel hne
    show mul (sub (evalCoeffs cs t) (evalCoeffs cs x)) (LawfulField.inv (sub t x)) ::
      newtonDivDiff x (evalCoeffs cs x) xs (xs.map (evalCoeffs cs)) =
      evalCoeffs (quotLinear cs x) t :: xs.map (evalCoeffs (quotLinear cs x))
    rw [newtonDivDiff_eval x cs xs (fun t' ht' => hx t' (List.mem_cons_of_mem _ ht')),
      evalCoeffs_eq_mul_quotLinear_add cs x t]
    generalize LawfulField.inv (sub t x) = j at hi
    have e : mul (sub (add (mul (sub t x) (evalCoeffs (quotLinear cs x) t)) (evalCoeffs cs x))
        (evalCoeffs cs x)) j = mul (evalCoeffs (quotLinear cs x) t) (mul (sub t x) j) := by
      constructive_ring
    rw [e, hi, LawfulCommRing.mul_one]

theorem newtonInterp_eval : ∀ (xs cs : List F), xs.Nodup → cs.length = xs.length →
    newtonInterp xs (xs.map (evalCoeffs cs)) = cs
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by cases h
  | x :: xs, cs, hnd, h => by
    obtain ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
    have hcs : cs ≠ [] := fun h0 => by
      rw [h0] at h
      cases h
    have hq : (quotLinear cs x).length = xs.length := by
      rw [quotLinear_length, h]
      rfl
    show newtonUnquot x (evalCoeffs cs x)
      (newtonInterp xs (newtonDivDiff x (evalCoeffs cs x) xs (xs.map (evalCoeffs cs)))) = cs
    rw [newtonDivDiff_eval x cs xs (fun t ht hEq => hx (hEq ▸ ht))]
    have ih := newtonInterp_eval xs (quotLinear cs x) hnd' hq
    rw [ih, newtonUnquot_quotLinear x cs hcs]

end Interpolation

/-! ## §6. Lemma V2.2 in interpolation form -/

section ListMaps

theorem map_map_comm {α β γ δ : Type} (f : α → β) (g : β → δ) (f' : α → γ) (g' : γ → δ)
    (h : ∀ a, g (f a) = g' (f' a)) : ∀ l : List α, (l.map f).map g = (l.map f').map g'
  | [] => rfl
  | a :: l => by
    show g (f a) :: (l.map f).map g = g' (f' a) :: (l.map f').map g'
    rw [h a, map_map_comm f g f' g' h l]

theorem pointwise_of_map_map {α β γ δ : Type} (f : α → β) (g : β → δ) (f' : α → γ)
    (g' : γ → δ) : ∀ l : List α, (l.map f).map g = (l.map f').map g' →
    ∀ a ∈ l, g (f a) = g' (f' a)
  | [], _, _, ha => nomatch ha
  | b :: l, h, a, ha => by
    have h' : g (f b) :: (l.map f).map g = g' (f' b) :: (l.map f').map g' := h
    obtain ⟨h0, hT⟩ := List.cons.inj h'
    rcases List.mem_cons.mp ha with hab | hal
    · rw [hab]
      exact h0
    · exact pointwise_of_map_map f g f' g' l hT a hal

theorem map_congr_mem {α β : Type} (f g : α → β) : ∀ l : List α, (∀ a ∈ l, f a = g a) →
    l.map f = l.map g
  | [], _ => rfl
  | a :: l, h => by
    show f a :: l.map f = g a :: l.map g
    rw [h a List.mem_cons_self, map_congr_mem f g l (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem fixed_of_map_eq_self {α : Type} (f : α → α) : ∀ l : List α, l.map f = l →
    ∀ a ∈ l, f a = a
  | [], _, _, ha => nomatch ha
  | b :: l, h, a, ha => by
    have h' : f b :: l.map f = b :: l := h
    obtain ⟨h0, hT⟩ := List.cons.inj h'
    rcases List.mem_cons.mp ha with hab | hal
    · rw [hab]
      exact h0
    · exact fixed_of_map_eq_self f l hT a hal

theorem append_cancel_of_length {α : Type} : ∀ (a c b d : List α), a.length = c.length →
    a ++ b = c ++ d → a = c ∧ b = d
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | [], _ :: _, _, _, hl, _ => by cases hl
  | _ :: _, [], _, _, hl, _ => by cases hl
  | x :: a, y :: c, b, d, hl, h => by
    have h' : x :: (a ++ b) = y :: (c ++ d) := h
    obtain ⟨h0, hT⟩ := List.cons.inj h'
    obtain ⟨h1, h2⟩ := append_cancel_of_length a c b d (Nat.succ.inj hl) hT
    rw [h0, h1]
    exact ⟨rfl, h2⟩

end ListMaps

section BlindingCount

theorem evalCoeffs_map_ofBase : ∀ (cs : List Goldilocks) (q : Goldilocks),
    evalCoeffs (cs.map ofBase) (ofBase q) = ofBase (evalCoeffs cs q)
  | [], _ => QuinticGoldilocks.ofBase_zero.symm
  | c :: cs, q => by
    show add (ofBase c) (mul (ofBase q) (evalCoeffs (cs.map ofBase) (ofBase q))) =
      ofBase (add c (mul q (evalCoeffs cs q)))
    rw [evalCoeffs_map_ofBase cs q, QuinticGoldilocks.ofBase_add, QuinticGoldilocks.ofBase_mul]

theorem evalCoeffs_map_frob : ∀ (cs : List QuinticGoldilocks) (x : QuinticGoldilocks),
    evalCoeffs (cs.map frob) (frob x) = frob (evalCoeffs cs x)
  | [], _ => QuinticGoldilocks.frob_zero.symm
  | c :: cs, x => by
    show add (frob c) (mul (frob x) (evalCoeffs (cs.map frob) (frob x))) =
      frob (add c (mul x (evalCoeffs cs x)))
    rw [evalCoeffs_map_frob cs x, QuinticGoldilocks.frob_add, QuinticGoldilocks.frob_mul]

theorem map_frob_map_ofBase (cs : List Goldilocks) :
    (cs.map ofBase).map frob = cs.map ofBase :=
  (map_map_comm ofBase frob ofBase (fun z => z) QuinticGoldilocks.frob_ofBase cs).trans
    (map_congr_mem _ _ _ (fun _ _ => rfl)) |>.trans (by
      show (cs.map ofBase).map (fun z => z) = cs.map ofBase
      exact List.map_id' _)

/-- A polynomial with base-field coefficients commutes with the Frobenius map. -/
theorem evalCoeffs_base_frob (cs : List Goldilocks) (x : QuinticGoldilocks) :
    evalCoeffs (cs.map ofBase) (frob x) = frob (evalCoeffs (cs.map ofBase) x) := by
  have h := evalCoeffs_map_frob (cs.map ofBase) x
  rw [map_frob_map_ofBase] at h
  exact h

theorem map_c0_map_ofBase : ∀ cs : List Goldilocks,
    (cs.map ofBase).map QuinticGoldilocks.c0 = cs
  | [] => rfl
  | c :: cs => by
    show (ofBase c).c0 :: (cs.map ofBase).map QuinticGoldilocks.c0 = c :: cs
    rw [map_c0_map_ofBase cs, QuinticGoldilocks.ofBase_c0]

theorem map_ofBase_map_c0 : ∀ C : List QuinticGoldilocks, (∀ c ∈ C, c = ofBase c.c0) →
    (C.map QuinticGoldilocks.c0).map ofBase = C
  | [], _ => rfl
  | c :: C, h => by
    show ofBase c.c0 :: (C.map QuinticGoldilocks.c0).map ofBase = c :: C
    rw [map_ofBase_map_c0 C (fun b hb => h b (List.mem_cons_of_mem _ hb)),
      ← h c List.mem_cons_self]

theorem map_ofBase_injective : ∀ a b : List Goldilocks, a.map ofBase = b.map ofBase → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: a, y :: b, h => by
    have h' : ofBase x :: a.map ofBase = ofBase y :: b.map ofBase := h
    obtain ⟨h0, hT⟩ := List.cons.inj h'
    rw [QuinticGoldilocks.ofBase_injective h0, map_ofBase_injective a b hT]

/-- `bs` followed by `zs` and its four Frobenius conjugates. -/
@[expose] def conjClosure (bs zs : List QuinticGoldilocks) : List QuinticGoldilocks :=
  bs ++ (zs ++ (zs.map frob ++ (zs.map (fun z => frob (frob z)) ++
    (zs.map (fun z => frob (frob (frob z))) ++
      zs.map (fun z => frob (frob (frob (frob z))))))))

/-- The base points `qs`, the points `ys` of `E` and the conjugates of `ys`. That this list
    has no repetition says: the `qs` are distinct, each `y` is outside the base field, and the
    `ys` are pairwise non-conjugate. -/
@[expose] def blindPoints (qs : List Goldilocks) (ys : List QuinticGoldilocks) :
    List QuinticGoldilocks :=
  conjClosure (qs.map ofBase) ys

theorem conjClosure_length (bs zs : List QuinticGoldilocks) :
    (conjClosure bs zs).length = bs.length + 5 * zs.length := by
  show (bs ++ (zs ++ (zs.map frob ++ (zs.map (fun z => frob (frob z)) ++
    (zs.map (fun z => frob (frob (frob z))) ++
      zs.map (fun z => frob (frob (frob (frob z))))))))).length = bs.length + 5 * zs.length
  rw [List.length_append, List.length_append, List.length_append, List.length_append,
    List.length_append, List.length_map, List.length_map, List.length_map, List.length_map]
  omega

/-- What a blinding polynomial with base-field coefficients `cs` shows: its values at the
    base points and at the points of `E`. -/
@[expose] def blindingView (qs : List Goldilocks) (ys : List QuinticGoldilocks)
    (cs : List Goldilocks) : List Goldilocks × List QuinticGoldilocks :=
  (qs.map (evalCoeffs cs), ys.map (evalCoeffs (cs.map ofBase)))

/-- Coefficients from values: interpolate over `E` through the conjugate-closed data and read
    off the base-field coordinate. -/
def blindingInv (qs : List Goldilocks) (ys : List QuinticGoldilocks) (us : List Goldilocks)
    (vs : List QuinticGoldilocks) : List Goldilocks :=
  (newtonInterp (blindPoints qs ys) (conjClosure (us.map ofBase) vs)).map QuinticGoldilocks.c0

theorem blind_lengths (qs : List Goldilocks) (ys : List QuinticGoldilocks) (us : List Goldilocks)
    (vs : List QuinticGoldilocks) (hu : us.length = qs.length) (hv : vs.length = ys.length) :
    (blindPoints qs ys).length = (conjClosure (us.map ofBase) vs).length := by
  show (conjClosure (qs.map ofBase) ys).length = _
  rw [conjClosure_length, conjClosure_length, List.length_map, List.length_map, hu, hv]

theorem blindPoints_length (qs : List Goldilocks) (ys : List QuinticGoldilocks) :
    (blindPoints qs ys).length = qs.length + 5 * ys.length := by
  show (conjClosure (qs.map ofBase) ys).length = _
  rw [conjClosure_length, List.length_map]

theorem blindingInv_length (qs : List Goldilocks) (ys : List QuinticGoldilocks)
    (us : List Goldilocks) (vs : List QuinticGoldilocks) (hu : us.length = qs.length)
    (hv : vs.length = ys.length) :
    (blindingInv qs ys us vs).length = qs.length + 5 * ys.length := by
  show ((newtonInterp (blindPoints qs ys) (conjClosure (us.map ofBase) vs)).map
    QuinticGoldilocks.c0).length = _
  rw [List.length_map, newtonInterp_length _ _ (blind_lengths qs ys us vs hu hv),
    blindPoints_length]

/-- The values of a base-coefficient polynomial on `blindPoints` are the conjugate closure of
    its values on `qs` and `ys`. -/
theorem conjClosure_eval (qs : List Goldilocks) (ys : List QuinticGoldilocks)
    (cs : List Goldilocks) :
    conjClosure ((qs.map (evalCoeffs cs)).map ofBase) (ys.map (evalCoeffs (cs.map ofBase))) =
      (blindPoints qs ys).map (evalCoeffs (cs.map ofBase)) := by
  have h1 := evalCoeffs_base_frob cs
  have h2 : ∀ y, evalCoeffs (cs.map ofBase) (frob (frob y)) =
      frob (frob (evalCoeffs (cs.map ofBase) y)) := fun y => by rw [h1, h1]
  have h3 : ∀ y, evalCoeffs (cs.map ofBase) (frob (frob (frob y))) =
      frob (frob (frob (evalCoeffs (cs.map ofBase) y))) := fun y => by rw [h1, h1, h1]
  have h4 : ∀ y, evalCoeffs (cs.map ofBase) (frob (frob (frob (frob y)))) =
      frob (frob (frob (frob (evalCoeffs (cs.map ofBase) y)))) := fun y => by
    rw [h1, h1, h1, h1]
  have b0 := map_map_comm ofBase (evalCoeffs (cs.map ofBase)) (evalCoeffs cs) ofBase
    (evalCoeffs_map_ofBase cs) qs
  have b1 := map_map_comm frob (evalCoeffs (cs.map ofBase)) (evalCoeffs (cs.map ofBase)) frob
    h1 ys
  have b2 := map_map_comm (fun z => frob (frob z)) (evalCoeffs (cs.map ofBase))
    (evalCoeffs (cs.map ofBase)) (fun z => frob (frob z)) h2 ys
  have b3 := map_map_comm (fun z => frob (frob (frob z))) (evalCoeffs (cs.map ofBase))
    (evalCoeffs (cs.map ofBase)) (fun z => frob (frob (frob z))) h3 ys
  have b4 := map_map_comm (fun z => frob (frob (frob (frob z)))) (evalCoeffs (cs.map ofBase))
    (evalCoeffs (cs.map ofBase)) (fun z => frob (frob (frob (frob z)))) h4 ys
  show _ = List.map (evalCoeffs (cs.map ofBase)) (qs.map ofBase ++ (ys ++ (ys.map frob ++
    (ys.map (fun z => frob (frob z)) ++ (ys.map (fun z => frob (frob (frob z))) ++
      ys.map (fun z => frob (frob (frob (frob z)))))))))
  rw [List.map_append, List.map_append, List.map_append, List.map_append, List.map_append,
    b0, b1, b2, b3, b4]
  rfl

theorem blindingInv_blindingView (qs : List Goldilocks) (ys : List QuinticGoldilocks)
    (hnd : (blindPoints qs ys).Nodup) (cs : List Goldilocks)
    (hc : cs.length = qs.length + 5 * ys.length) :
    blindingInv qs ys (qs.map (evalCoeffs cs)) (ys.map (evalCoeffs (cs.map ofBase))) = cs := by
  show (newtonInterp (blindPoints qs ys)
    (conjClosure ((qs.map (evalCoeffs cs)).map ofBase)
      (ys.map (evalCoeffs (cs.map ofBase))))).map QuinticGoldilocks.c0 = cs
  rw [conjClosure_eval, newtonInterp_eval _ _ hnd
    ((List.length_map _).trans (hc.trans (blindPoints_length qs ys).symm)), map_c0_map_ofBase]

theorem blindingView_blindingInv (qs : List Goldilocks) (ys : List QuinticGoldilocks)
    (hnd : (blindPoints qs ys).Nodup) (us : List Goldilocks) (vs : List QuinticGoldilocks)
    (hu : us.length = qs.length) (hv : vs.length = ys.length) :
    blindingView qs ys (blindingInv qs ys us vs) = (us, vs) := by
  have hlen := blind_lengths qs ys us vs hu hv
  have hC := eval_newtonInterp (blindPoints qs ys) (conjClosure (us.map ofBase) vs) hnd hlen
  have hCl := newtonInterp_length (blindPoints qs ys) (conjClosure (us.map ofBase) vs) hlen
  show (qs.map (evalCoeffs ((newtonInterp (blindPoints qs ys)
      (conjClosure (us.map ofBase) vs)).map QuinticGoldilocks.c0)),
    ys.map (evalCoeffs (((newtonInterp (blindPoints qs ys)
      (conjClosure (us.map ofBase) vs)).map QuinticGoldilocks.c0).map ofBase))) = (us, vs)
  revert hC hCl
  generalize newtonInterp (blindPoints qs ys) (conjClosure (us.map ofBase) vs) = C
  intro hC hCl
  -- the six blocks of `hC`
  have hC' : (qs.map ofBase).map (evalCoeffs C) ++ (ys.map (evalCoeffs C) ++
      ((ys.map frob).map (evalCoeffs C) ++ ((ys.map (fun z => frob (frob z))).map (evalCoeffs C) ++
        ((ys.map (fun z => frob (frob (frob z)))).map (evalCoeffs C) ++
          (ys.map (fun z => frob (frob (frob (frob z))))).map (evalCoeffs C))))) =
      us.map ofBase ++ (vs ++ (vs.map frob ++ (vs.map (fun z => frob (frob z)) ++
        (vs.map (fun z => frob (frob (frob z))) ++
          vs.map (fun z => frob (frob (frob (frob z)))))))) := by
    rw [← List.map_append, ← List.map_append, ← List.map_append, ← List.map_append,
      ← List.map_append]
    exact hC
  have lv : ∀ (f : QuinticGoldilocks → QuinticGoldilocks) (g : QuinticGoldilocks → QuinticGoldilocks),
      ((ys.map f).map (evalCoeffs C)).length = (vs.map g).length := fun f g => by
    rw [List.length_map, List.length_map, List.length_map, hv]
  obtain ⟨B0, r0⟩ := append_cancel_of_length _ _ _ _ (by
    rw [List.length_map, List.length_map, List.length_map, hu]) hC'
  obtain ⟨B1, r1⟩ := append_cancel_of_length _ _ _ _ (by rw [List.length_map, hv]) r0
  obtain ⟨B2, r2⟩ := append_cancel_of_length _ _ _ _ (lv frob frob) r1
  obtain ⟨B3, r3⟩ := append_cancel_of_length _ _ _ _ (lv _ _) r2
  obtain ⟨B4, B5⟩ := append_cancel_of_length _ _ _ _ (lv _ _) r3
  rw [← B1] at B2 B3 B4 B5
  have p1 := pointwise_of_map_map frob (evalCoeffs C) (evalCoeffs C) frob ys B2
  have p2 := pointwise_of_map_map (fun z => frob (frob z)) (evalCoeffs C) (evalCoeffs C)
    (fun z => frob (frob z)) ys B3
  have p3 := pointwise_of_map_map (fun z => frob (frob (frob z))) (evalCoeffs C) (evalCoeffs C)
    (fun z => frob (frob (frob z))) ys B4
  have p4 := pointwise_of_map_map (fun z => frob (frob (frob (frob z)))) (evalCoeffs C)
    (evalCoeffs C) (fun z => frob (frob (frob (frob z)))) ys B5
  have p0 : ∀ q ∈ qs, frob (evalCoeffs C (ofBase q)) = evalCoeffs C (ofBase q) := by
    intro q hq
    have hm : evalCoeffs C (ofBase q) ∈ (qs.map ofBase).map (evalCoeffs C) :=
      List.mem_map.mpr ⟨ofBase q, List.mem_map.mpr ⟨q, hq, rfl⟩, rfl⟩
    rw [B0] at hm
    obtain ⟨u, -, hu'⟩ := List.mem_map.mp hm
    rw [← hu', QuinticGoldilocks.frob_ofBase]
  -- the conjugated coefficient list interpolates the same data
  have hpt : ∀ x ∈ blindPoints qs ys, evalCoeffs (C.map frob) x = evalCoeffs C x := by
    intro x hx
    have hx' : x ∈ qs.map ofBase ++ (ys ++ (ys.map frob ++ (ys.map (fun z => frob (frob z)) ++
        (ys.map (fun z => frob (frob (frob z))) ++
          ys.map (fun z => frob (frob (frob (frob z)))))))) := hx
    rcases List.mem_append.mp hx' with h | h
    · obtain ⟨q, hq, hEq⟩ := List.mem_map.mp h
      have t := evalCoeffs_map_frob C (ofBase q)
      rw [QuinticGoldilocks.frob_ofBase] at t
      rw [← hEq, t, p0 q hq]
    rcases List.mem_append.mp h with h | h
    · have t := evalCoeffs_map_frob C (frob (frob (frob (frob x))))
      rw [QuinticGoldilocks.frob_pow5] at t
      have q4 : evalCoeffs C (frob (frob (frob (frob x)))) =
          frob (frob (frob (frob (evalCoeffs C x)))) := p4 x h
      rw [t, q4, QuinticGoldilocks.frob_pow5]
    rcases List.mem_append.mp h with h | h
    · obtain ⟨y, hy, hEq⟩ := List.mem_map.mp h
      have q1 : evalCoeffs C (frob y) = frob (evalCoeffs C y) := p1 y hy
      rw [← hEq, evalCoeffs_map_frob C y, q1]
    rcases List.mem_append.mp h with h | h
    · obtain ⟨y, hy, hEq⟩ := List.mem_map.mp h
      have hEq' : frob (frob y) = x := hEq
      have q1 : evalCoeffs C (frob y) = frob (evalCoeffs C y) := p1 y hy
      have q2 : evalCoeffs C (frob (frob y)) = frob (frob (evalCoeffs C y)) := p2 y hy
      rw [← hEq', evalCoeffs_map_frob C (frob y), q1, q2]
    rcases List.mem_append.mp h with h | h
    · obtain ⟨y, hy, hEq⟩ := List.mem_map.mp h
      have hEq' : frob (frob (frob y)) = x := hEq
      have q2 : evalCoeffs C (frob (frob y)) = frob (frob (evalCoeffs C y)) := p2 y hy
      have q3 : evalCoeffs C (frob (frob (frob y))) = frob (frob (frob (evalCoeffs C y))) :=
        p3 y hy
      rw [← hEq', evalCoeffs_map_frob C (frob (frob y)), q2, q3]
    · obtain ⟨y, hy, hEq⟩ := List.mem_map.mp h
      have hEq' : frob (frob (frob (frob y))) = x := hEq
      have q3 : evalCoeffs C (frob (frob (frob y))) = frob (frob (frob (evalCoeffs C y))) :=
        p3 y hy
      have q4 : evalCoeffs C (frob (frob (frob (frob y)))) =
          frob (frob (frob (frob (evalCoeffs C y)))) := p4 y hy
      rw [← hEq', evalCoeffs_map_frob C (frob (frob (frob y))), q3, q4]
  have hfix : C.map frob = C := by
    have hD := newtonInterp_eval (blindPoints qs ys) (C.map frob) hnd
      ((List.length_map _).trans hCl)
    have hC2 := newtonInterp_eval (blindPoints qs ys) C hnd hCl
    rw [map_congr_mem _ _ _ hpt, hC2] at hD
    exact hD.symm
  have hbase : (C.map QuinticGoldilocks.c0).map ofBase = C :=
    map_ofBase_map_c0 C (fun c hc =>
      (QuinticGoldilocks.frob_eq_self_iff c).mp (fixed_of_map_eq_self frob C hfix c hc))
  have hfst : qs.map (evalCoeffs (C.map QuinticGoldilocks.c0)) = us := by
    apply map_ofBase_injective
    have t := map_map_comm ofBase (evalCoeffs ((C.map QuinticGoldilocks.c0).map ofBase))
      (evalCoeffs (C.map QuinticGoldilocks.c0)) ofBase
      (evalCoeffs_map_ofBase (C.map QuinticGoldilocks.c0)) qs
    rw [hbase, B0] at t
    exact t.symm
  show (qs.map (evalCoeffs (C.map QuinticGoldilocks.c0)),
    ys.map (evalCoeffs ((C.map QuinticGoldilocks.c0).map ofBase))) = (us, vs)
  rw [hbase, hfst, B1]

def blindingEquiv (qs : List Goldilocks) (ys : List QuinticGoldilocks)
    (hnd : (blindPoints qs ys).Nodup) :
    SimpleEquiv {cs : List Goldilocks // cs.length = qs.length + 5 * ys.length}
      ({us : List Goldilocks // us.length = qs.length} ×
        {vs : List QuinticGoldilocks // vs.length = ys.length}) where
  toFun cs := (⟨qs.map (evalCoeffs cs.1), List.length_map _⟩,
    ⟨ys.map (evalCoeffs (cs.1.map ofBase)), List.length_map _⟩)
  invFun o := ⟨blindingInv qs ys o.1.1 o.2.1, blindingInv_length qs ys o.1.1 o.2.1 o.1.2 o.2.2⟩
  left_inv cs := Subtype.ext (blindingInv_blindingView qs ys hnd cs.1 cs.2)
  right_inv o := by
    have h := blindingView_blindingInv qs ys hnd o.1.1 o.2.1 o.1.2 o.2.2
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)

/-- **Lemma V2.2, interpolation form.** If the base points, the points `ys` of `E` and the
    four conjugates of each `y` are pairwise distinct, then a polynomial with
    `|qs| + 5 |ys|` base-field coefficients is determined by, and can take any, values at
    `qs` (in the base field) and at `ys` (in `E`). -/
theorem v2_blinding_count (qs : List Goldilocks) (ys : List QuinticGoldilocks)
    (hnd : (blindPoints qs ys).Nodup) :
    ∃ Φ : SimpleEquiv {cs : List Goldilocks // cs.length = qs.length + 5 * ys.length}
        ({us : List Goldilocks // us.length = qs.length} ×
          {vs : List QuinticGoldilocks // vs.length = ys.length}),
      (∀ cs, ((Φ.toFun cs).1.1, (Φ.toFun cs).2.1) = blindingView qs ys cs.1) ∧
      (∀ o, (Φ.invFun o).1 = blindingInv qs ys o.1.1 o.2.1) :=
  ⟨blindingEquiv qs ys hnd, fun _ => rfl, fun _ => rfl⟩

/-- Pointwise scaling by nonzero factors. -/
def scaleEquiv {F : Type} [LawfulField F] {n : Nat} (ls : List F) (hn : ls.length = n)
    (hz : ∀ l ∈ ls, l ≠ zero) :
    SimpleEquiv {v : List F // v.length = n} {v : List F // v.length = n} where
  toFun v := ⟨pmul v.1 ls, (pmul_length _ _ (v.2.trans hn.symm)).trans hn⟩
  invFun o := ⟨pmul o.1 (ls.map LawfulField.inv),
    (pmul_length _ _ (o.2.trans (hn.symm.trans (List.length_map _).symm))).trans
      ((List.length_map _).trans hn)⟩
  left_inv v := Subtype.ext (pmul_inv_cancel v.1 ls hz (v.2.trans hn.symm))
  right_inv o := Subtype.ext (by
    show pmul (pmul o.1 (ls.map LawfulField.inv)) ls = o.1
    rw [pmul_right_comm]
    exact pmul_inv_cancel o.1 ls hz (o.2.trans hn.symm))

/-- The view with the factor `x^(N-b)` of the protocol: each value is multiplied by a nonzero
    factor of its own. -/
def blindingViewScaled (qs : List Goldilocks) (ys : List QuinticGoldilocks)
    (ls : List Goldilocks) (ms : List QuinticGoldilocks) (cs : List Goldilocks) :
    List Goldilocks × List QuinticGoldilocks :=
  (pmul (qs.map (evalCoeffs cs)) ls, pmul (ys.map (evalCoeffs (cs.map ofBase))) ms)

/-- **Lemma V2.2 with unit factors.** -/
theorem v2_blinding_count_scaled (qs : List Goldilocks) (ys : List QuinticGoldilocks)
    (ls : List Goldilocks) (ms : List QuinticGoldilocks) (hl : ls.length = qs.length)
    (hm : ms.length = ys.length) (hlz : ∀ l ∈ ls, l ≠ zero) (hmz : ∀ m ∈ ms, m ≠ zero)
    (hnd : (blindPoints qs ys).Nodup) :
    ∃ Φ : SimpleEquiv {cs : List Goldilocks // cs.length = qs.length + 5 * ys.length}
        ({us : List Goldilocks // us.length = qs.length} ×
          {vs : List QuinticGoldilocks // vs.length = ys.length}),
      ∀ cs, ((Φ.toFun cs).1.1, (Φ.toFun cs).2.1) = blindingViewScaled qs ys ls ms cs.1 :=
  ⟨postProd (blindingEquiv qs ys hnd) (scaleEquiv ls hl hlz) (scaleEquiv ms hm hmz),
    fun _ => rfl⟩

/-- **Lemma V2.2 as a simulation.** The opened base-field symbols and the exposed `E`-values,
    each an offset (the part of the table below the blinders) plus the value of a uniform
    blinding polynomial with `|qs| + 5 |ys|` base-field coefficients, are uniform. -/
theorem v2_opened_symbols_and_mask_values_perfectly_simulated (qs : List Goldilocks)
    (ys : List QuinticGoldilocks) (hnd : (blindPoints qs ys).Nodup) :
    CoinBijectionSimulated
      (fun (d : {us : List Goldilocks // us.length = qs.length} ×
          {vs : List QuinticGoldilocks // vs.length = ys.length})
        (cs : {cs : List Goldilocks // cs.length = qs.length + 5 * ys.length}) =>
        (vadd d.1.1 (qs.map (evalCoeffs cs.1)),
          vadd d.2.1 (ys.map (evalCoeffs (cs.1.map ofBase)))))
      (fun (o : {us : List Goldilocks // us.length = qs.length} ×
          {vs : List QuinticGoldilocks // vs.length = ys.length}) => (o.1.1, o.2.1)) :=
  offset_pair_simulated (blindingEquiv qs ys hnd)

/-- The simulation of `v2_opened_symbols_and_mask_values_perfectly_simulated` with unit
    factors on the blinder values. -/
theorem v2_scaled_symbols_and_mask_values_perfectly_simulated (qs : List Goldilocks)
    (ys : List QuinticGoldilocks) (ls : List Goldilocks) (ms : List QuinticGoldilocks)
    (hl : ls.length = qs.length) (hm : ms.length = ys.length) (hlz : ∀ l ∈ ls, l ≠ zero)
    (hmz : ∀ m ∈ ms, m ≠ zero) (hnd : (blindPoints qs ys).Nodup) :
    CoinBijectionSimulated
      (fun (d : {us : List Goldilocks // us.length = qs.length} ×
          {vs : List QuinticGoldilocks // vs.length = ys.length})
        (cs : {cs : List Goldilocks // cs.length = qs.length + 5 * ys.length}) =>
        (vadd d.1.1 (pmul (qs.map (evalCoeffs cs.1)) ls),
          vadd d.2.1 (pmul (ys.map (evalCoeffs (cs.1.map ofBase))) ms)))
      (fun (o : {us : List Goldilocks // us.length = qs.length} ×
          {vs : List QuinticGoldilocks // vs.length = ys.length}) => (o.1.1, o.2.1)) :=
  offset_pair_simulated
    (postProd (blindingEquiv qs ys hnd) (scaleEquiv ls hl hlz) (scaleEquiv ms hm hmz))

/-- A point of the base field among the `ys`: every exposed value there lies in the base
    field, so five base-field coefficients do not buy an `E`-value. -/
theorem tooth_blinding_base_field_point_not_surjective (qs : List Goldilocks) (a : Goldilocks)
    (us : List Goldilocks) :
    ¬ ∃ cs : List Goldilocks, blindingView qs [ofBase a] cs = (us, [xBasis]) := by
  rintro ⟨cs, h⟩
  have h2 : [evalCoeffs (cs.map ofBase) (ofBase a)] = [xBasis] := (Prod.mk.inj h).2
  have h3 := (List.cons.inj h2).1
  rw [evalCoeffs_map_ofBase] at h3
  exact LawfulField.zero_ne_one (F := Goldilocks) (congrArg QuinticGoldilocks.c1 h3)

/-- Two conjugate points among the `ys`: the two exposed values are conjugate. -/
theorem tooth_blinding_conjugate_points_not_surjective (qs : List Goldilocks)
    (y : QuinticGoldilocks) (us : List Goldilocks) :
    ¬ ∃ cs : List Goldilocks, blindingView qs [y, frob y] cs = (us, [zero, one]) := by
  rintro ⟨cs, h⟩
  have h2 : [evalCoeffs (cs.map ofBase) y, evalCoeffs (cs.map ofBase) (frob y)] = [zero, one] :=
    (Prod.mk.inj h).2
  obtain ⟨h0, hT⟩ := List.cons.inj h2
  have h1 := (List.cons.inj hT).1
  have hf := evalCoeffs_base_frob cs y
  rw [h1, h0, QuinticGoldilocks.frob_zero] at hf
  exact LawfulField.zero_ne_one (F := QuinticGoldilocks) hf.symm

end BlindingCount

/-! ## §6b. Lemma V2.2: point-interpolation to residue-ring (`E[X] / (X^(2^s) - z_j)`) bridge -/

section ResidueRingBridge

/-- Natural-number power in any `CommRingOps` carrier. -/
def fpow {F : Type} [CommRingOps F] (x : F) : Nat → F
  | 0 => one
  | n + 1 => mul x (fpow x n)

theorem fpow_zero {F : Type} [CommRingOps F] (x : F) : fpow x 0 = one := by rw [fpow]
theorem fpow_succ {F : Type} [CommRingOps F] (x : F) (n : Nat) :
    fpow x (n + 1) = mul x (fpow x n) := by rw [fpow]

theorem fpow_add {F : Type} [LawfulCommRing F] (x : F) :
    ∀ a b : Nat, fpow x (a + b) = mul (fpow x a) (fpow x b)
  | 0, b => by
    rw [Nat.zero_add]
    show fpow x b = mul one (fpow x b)
    rw [LawfulCommRing.one_mul]
  | a + 1, b => by
    have e : a + 1 + b = (a + b) + 1 := by omega
    rw [e]
    show mul x (fpow x (a + b)) = mul (mul x (fpow x a)) (fpow x b)
    rw [fpow_add x a b, LawfulCommRing.mul_assoc]

theorem fpow_mul_base {F : Type} [LawfulCommRing F] (x y : F) :
    ∀ n : Nat, fpow (mul x y) n = mul (fpow x n) (fpow y n)
  | 0 => by
    show one = mul one one
    constructive_ring
  | n + 1 => by
    show mul (mul x y) (fpow (mul x y) n) = mul (mul x (fpow x n)) (mul y (fpow y n))
    rw [fpow_mul_base x y n]
    constructive_ring

theorem fpow_one {F : Type} [LawfulCommRing F] : ∀ n : Nat, fpow (one : F) n = one
  | 0 => rfl
  | n + 1 => by
    show mul one (fpow one n) = one
    rw [fpow_one n, LawfulCommRing.one_mul]

theorem fpow_ne_zero {F : Type} [LawfulField F] {x : F} (hx : x ≠ zero) :
    ∀ n : Nat, fpow x n ≠ zero
  | 0 => LawfulField.one_ne_zero
  | n + 1 => fun h => by
    have hi := LawfulField.mul_inv_cancel hx
    have h1 : mul (LawfulField.inv x) (mul x (fpow x n)) = mul (LawfulField.inv x) zero :=
      congrArg (mul (LawfulField.inv x)) h
    have e : mul (LawfulField.inv x) (mul x (fpow x n)) =
        mul (mul x (LawfulField.inv x)) (fpow x n) := by constructive_ring
    have e0 : mul (LawfulField.inv x) zero = (zero : F) := by constructive_ring
    rw [e, hi, LawfulCommRing.one_mul, e0] at h1
    exact fpow_ne_zero hx n h1

theorem fpow_ofBase (a : Goldilocks) :
    ∀ n : Nat, fpow (ofBase a) n = ofBase (fpow a n)
  | 0 => QuinticGoldilocks.ofBase_one.symm
  | n + 1 => by
    show mul (ofBase a) (fpow (ofBase a) n) = ofBase (mul a (fpow a n))
    rw [fpow_ofBase a n, QuinticGoldilocks.ofBase_mul]

theorem fpow_frob (z : QuinticGoldilocks) :
    ∀ n : Nat, fpow (frob z) n = frob (fpow z n)
  | 0 => QuinticGoldilocks.frob_one.symm
  | n + 1 => by
    show mul (frob z) (fpow (frob z) n) = frob (mul z (fpow z n))
    rw [fpow_frob z n, QuinticGoldilocks.frob_mul]

/-- Iterated squaring `x^(2^k)`. -/
def pow2Iter {F : Type} [CommRingOps F] : Nat → F → F
  | 0, x => x
  | k + 1, x =>
    let y := pow2Iter k x
    mul y y

theorem pow2Iter_zero {F : Type} [CommRingOps F] (x : F) : pow2Iter 0 x = x := by rw [pow2Iter]
theorem pow2Iter_one {F : Type} [CommRingOps F] (x : F) : pow2Iter 1 x = mul x x := by simp only [pow2Iter]

theorem pow2Iter_add {F : Type} [CommRingOps F] :
    ∀ (a b : Nat) (x : F), pow2Iter (a + b) x = pow2Iter a (pow2Iter b x)
  | 0, b, x => by
    rw [Nat.zero_add]
    rfl
  | a + 1, b, x => by
    have e : a + 1 + b = (a + b) + 1 := by omega
    rw [e]
    show mul (pow2Iter (a + b) x) (pow2Iter (a + b) x) =
      mul (pow2Iter a (pow2Iter b x)) (pow2Iter a (pow2Iter b x))
    rw [pow2Iter_add a b x]

theorem pow2Iter_eq_fpow {F : Type} [LawfulCommRing F] :
    ∀ (k : Nat) (x : F), pow2Iter k x = fpow x (2 ^ k)
  | 0, x => by
    show x = mul x one
    constructive_ring
  | k + 1, x => by
    have e : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by omega
    rw [e, fpow_add]
    show mul (pow2Iter k x) (pow2Iter k x) = mul (fpow x (2 ^ k)) (fpow x (2 ^ k))
    rw [pow2Iter_eq_fpow k x]

/-- Monomial multiplication `X^k · P(X)`. -/
def shiftMonomial {F : Type} [CommRingOps F] : Nat → List F → List F
  | 0, P => P
  | k + 1, P => zero :: shiftMonomial k P

theorem evalCoeffs_shiftMonomial {F : Type} [LawfulCommRing F] :
    ∀ (k : Nat) (P : List F) (x : F),
      evalCoeffs (shiftMonomial k P) x = mul (fpow x k) (evalCoeffs P x)
  | 0, P, x => by
    show evalCoeffs P x = mul one (evalCoeffs P x)
    rw [LawfulCommRing.one_mul]
  | k + 1, P, x => by
    show add zero (mul x (evalCoeffs (shiftMonomial k P) x)) =
      mul (mul x (fpow x k)) (evalCoeffs P x)
    rw [evalCoeffs_shiftMonomial k P x]
    constructive_ring

/-- Euclidean division `(rem, quot)` of `P(X)` by `X^(m + 1) - z`:
    `rem` has exact length `m + 1`, and `P(x) = rem(x) + (x^(m + 1) - z) · quot(x)`. -/
def divModBinomial {F : Type} [CommRingOps F] (m : Nat) (z : F) : List F → List F × List F
  | [] => (List.replicate (m + 1) zero, [])
  | c :: P =>
    let rq := divModBinomial m z P
    let top := rq.1.getD m zero
    (add c (mul z top) :: rq.1.take m, top :: rq.2)

theorem divModBinomial_rem_length {F : Type} [CommRingOps F] (m : Nat) (z : F) :
    ∀ P : List F, (divModBinomial m z P).1.length = m + 1
  | [] => List.length_replicate
  | c :: P => by
    have ih := divModBinomial_rem_length m z P
    show ((divModBinomial m z P).1.take m).length + 1 = m + 1
    rw [List.length_take, ih]
    omega

private theorem evalCoeffs_replicate_zero {F : Type} [LawfulCommRing F] :
    ∀ (n : Nat) (x : F), evalCoeffs (List.replicate n (zero : F)) x = zero
  | 0, _ => rfl
  | n + 1, x => by
    show add zero (mul x (evalCoeffs (List.replicate n zero) x)) = zero
    rw [evalCoeffs_replicate_zero n x]
    constructive_ring

private theorem evalCoeffs_split_last {F : Type} [LawfulCommRing F] :
    ∀ (m : Nat) (R : List F) (x : F), R.length = m + 1 →
      evalCoeffs R x = add (evalCoeffs (R.take m) x) (mul (fpow x m) (R.getD m zero))
  | 0, [], _, h => by cases h
  | 0, r0 :: rs, x, h => by
    have hrs : rs = [] := List.eq_nil_of_length_eq_zero (Nat.succ.inj h)
    subst hrs
    show add r0 (mul x zero) = add zero (mul one r0)
    constructive_ring
  | m + 1, [], _, h => by cases h
  | m + 1, r0 :: rs, x, h => by
    have ih := evalCoeffs_split_last m rs x (Nat.succ.inj h)
    show add r0 (mul x (evalCoeffs rs x)) =
      add (add r0 (mul x (evalCoeffs (rs.take m) x))) (mul (mul x (fpow x m)) (rs.getD m zero))
    rw [ih]
    constructive_ring

/-- **Exact Binomial Division Identity (`evalCoeffs_divModBinomial`)**:
    For every polynomial `P` and point `x`,
    `P(x) = rem(x) + (x^(m + 1) - z) · quot(x)`. -/
theorem evalCoeffs_divModBinomial {F : Type} [LawfulCommRing F] (m : Nat) (z : F) :
    ∀ (P : List F) (x : F),
      evalCoeffs P x =
        add (evalCoeffs (divModBinomial m z P).1 x)
          (mul (sub (fpow x (m + 1)) z) (evalCoeffs (divModBinomial m z P).2 x))
  | [], x => by
    show zero = add (evalCoeffs (List.replicate (m + 1) zero) x) (mul (sub (fpow x (m + 1)) z) zero)
    rw [evalCoeffs_replicate_zero]
    constructive_ring
  | c :: P, x => by
    have ih := evalCoeffs_divModBinomial m z P x
    dsimp only [fpow] at ih
    have hLen := divModBinomial_rem_length m z P
    have hSplit := evalCoeffs_split_last m (divModBinomial m z P).1 x hLen
    dsimp only [divModBinomial]
    generalize (divModBinomial m z P).1 = R at ih hLen hSplit ⊢
    generalize (divModBinomial m z P).2 = Q at ih ⊢
    show add c (mul x (evalCoeffs P x)) =
      add (add (add c (mul z (R.getD m zero))) (mul x (evalCoeffs (R.take m) x)))
        (mul (sub (mul x (fpow x m)) z) (add (R.getD m zero) (mul x (evalCoeffs Q x))))
    rw [ih, hSplit]
    constructive_ring

/-- At any root `r` of `X^(m + 1) - z`, `P(r)` equals the canonical remainder evaluated at `r`. -/
theorem evalCoeffs_divModBinomial_at_root {F : Type} [LawfulCommRing F] (m : Nat) (z : F)
    (P : List F) {r : F} (hr : fpow r (m + 1) = z) :
    evalCoeffs (divModBinomial m z P).1 r = evalCoeffs P r := by
  rw [evalCoeffs_divModBinomial m z P r, hr]
  constructive_ring

/-- Primitive `2^32`-th root of unity in `Goldilocks` (`7^((p - 1) / 2^32) mod p`). -/
def twoAdicGen32 : Goldilocks := Goldilocks.ofNat 1753635133440165772

theorem twoAdicGen32_pow31 : pow2Iter 31 twoAdicGen32 = neg one := by
  decide +kernel

theorem twoAdicGen32_pow32 : pow2Iter 32 twoAdicGen32 = one := by
  decide +kernel

/-- Canonical `2^s`-th root of unity in `Goldilocks` for `s ≤ 32`. -/
def twoAdicElem (s : Nat) : Goldilocks := pow2Iter (32 - s) twoAdicGen32

theorem twoAdicElem_pow2 (s : Nat) (hs : s ≤ 32) :
    fpow (twoAdicElem s) (2 ^ s) = one := by
  rw [← pow2Iter_eq_fpow]
  unfold twoAdicElem
  rw [← pow2Iter_add]
  have e : s + (32 - s) = 32 := by omega
  rw [e]
  exact twoAdicGen32_pow32

theorem twoAdicElem_sq (s : Nat) (hs : s + 1 ≤ 32) :
    mul (twoAdicElem (s + 1)) (twoAdicElem (s + 1)) = twoAdicElem s := by
  unfold twoAdicElem
  have e : 32 - s = (32 - (s + 1)) + 1 := by omega
  rw [e]
  rfl

theorem twoAdicElem_half_pow (s : Nat) (hs : s + 1 ≤ 32) :
    fpow (twoAdicElem (s + 1)) (2 ^ s) = neg one := by
  rw [← pow2Iter_eq_fpow]
  unfold twoAdicElem
  rw [← pow2Iter_add]
  have e : s + (32 - (s + 1)) = 31 := by omega
  rw [e]
  exact twoAdicGen32_pow31

theorem twoAdicElem_ne_zero (s : Nat) (hs : s ≤ 32) : twoAdicElem s ≠ zero := by
  intro h0
  have h1 := twoAdicElem_pow2 s hs
  rw [h0] at h1
  have h2Pos : 2 ^ s = (2 ^ s - 1) + 1 := by
    have hp := Nat.two_pow_pos s
    omega
  rw [h2Pos] at h1
  have hz : mul (zero : Goldilocks) (fpow zero (2 ^ s - 1)) = zero := by constructive_ring
  exact LawfulField.zero_ne_one (hz.symm.trans h1)

private theorem sub_mod_two_pow {s n : Nat} (hn : n < 2 ^ (s + 1)) (hGe : ¬ n < 2 ^ s) :
    n % 2 ^ s = n - 2 ^ s := by
  have hSubLt : n - 2 ^ s < 2 ^ s := by
    have he2 : 2 ^ (s + 1) = 2 ^ s + 2 ^ s := by omega
    omega
  have hEq : n = (n - 2 ^ s) + 2 ^ s := by omega
  conv => lhs; rw [hEq]
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt hSubLt]

private theorem fpow_mod_two_pow {s : Nat} (hs : s ≤ 32) {n : Nat} (hn : n < 2 ^ (s + 1)) :
    fpow (twoAdicElem s) n = fpow (twoAdicElem s) (n % 2 ^ s) := by
  by_cases hLt : n < 2 ^ s
  · rw [Nat.mod_eq_of_lt hLt]
  · have hMod := sub_mod_two_pow hn hLt
    have hEq : n = (n - 2 ^ s) + 2 ^ s := by omega
    rw [hMod]
    conv => lhs; rw [hEq]
    rw [fpow_add, twoAdicElem_pow2 s hs, LawfulCommRing.mul_one]

private theorem twoAdicElem_exp_inj :
    ∀ (s : Nat), s ≤ 32 → ∀ (i j : Nat), i < 2 ^ s → j < 2 ^ s →
      fpow (twoAdicElem s) i = fpow (twoAdicElem s) j → i = j
  | 0, _, i, j, hi, hj, _ => by omega
  | s + 1, hs, i, j, hi, hj, hEq => by
    have hsLe : s ≤ 32 := by omega
    have hSq : mul (fpow (twoAdicElem (s + 1)) i) (fpow (twoAdicElem (s + 1)) i) =
        mul (fpow (twoAdicElem (s + 1)) j) (fpow (twoAdicElem (s + 1)) j) := by
      rw [hEq]
    rw [← fpow_mul_base, ← fpow_mul_base, twoAdicElem_sq s hs,
      fpow_mod_two_pow hsLe hi, fpow_mod_two_pow hsLe hj] at hSq
    have hModEq := twoAdicElem_exp_inj s hsLe (i % 2 ^ s) (j % 2 ^ s)
      (Nat.mod_lt _ (Nat.two_pow_pos s)) (Nat.mod_lt _ (Nat.two_pow_pos s)) hSq
    have hTri : i = j ∨ j = i + 2 ^ s ∨ i = j + 2 ^ s := by
      by_cases hiLt : i < 2 ^ s <;> by_cases hjLt : j < 2 ^ s
      · rw [Nat.mod_eq_of_lt hiLt, Nat.mod_eq_of_lt hjLt] at hModEq
        exact .inl hModEq
      · rw [Nat.mod_eq_of_lt hiLt, sub_mod_two_pow hj hjLt] at hModEq
        exact .inr (.inl (by omega))
      · rw [sub_mod_two_pow hi hiLt, Nat.mod_eq_of_lt hjLt] at hModEq
        exact .inr (.inr (by omega))
      · rw [sub_mod_two_pow hi hiLt, sub_mod_two_pow hj hjLt] at hModEq
        exact .inl (by omega)
    rcases hTri with hSame | hJ | hI
    · exact hSame
    · exfalso
      rw [hJ, fpow_add, twoAdicElem_half_pow s hs] at hEq
      have hTwoZero : mul (add (one : Goldilocks) one) (fpow (twoAdicElem (s + 1)) i) = zero := by
        calc mul (add (one : Goldilocks) one) (fpow (twoAdicElem (s + 1)) i)
            = add (fpow (twoAdicElem (s + 1)) i) (fpow (twoAdicElem (s + 1)) i) := by
                constructive_ring
          _ = add (fpow (twoAdicElem (s + 1)) i)
                (mul (fpow (twoAdicElem (s + 1)) i) (neg one)) := by
                conv => lhs; arg 2; rw [hEq]
          _ = zero := by constructive_ring
      have hTwoNe : add (one : Goldilocks) one ≠ zero := by decide +kernel
      have hWiNe := fpow_ne_zero (twoAdicElem_ne_zero (s + 1) hs) i
      have hInv := LawfulField.mul_inv_cancel hTwoNe
      have h1 := congrArg (mul (LawfulField.inv (add (one : Goldilocks) one))) hTwoZero
      have e1 : mul (LawfulField.inv (add (one : Goldilocks) one))
          (mul (add one one) (fpow (twoAdicElem (s + 1)) i)) =
          mul (mul (add one one) (LawfulField.inv (add one one)))
            (fpow (twoAdicElem (s + 1)) i) := by constructive_ring
      have e0 : mul (LawfulField.inv (add (one : Goldilocks) one)) zero = zero := by
        constructive_ring
      rw [e1, hInv, LawfulCommRing.one_mul, e0] at h1
      exact hWiNe h1
    · exfalso
      have hSymm := hEq.symm
      rw [hI, fpow_add, twoAdicElem_half_pow s hs] at hSymm
      have hTwoZero : mul (add (one : Goldilocks) one) (fpow (twoAdicElem (s + 1)) j) = zero := by
        calc mul (add (one : Goldilocks) one) (fpow (twoAdicElem (s + 1)) j)
            = add (fpow (twoAdicElem (s + 1)) j) (fpow (twoAdicElem (s + 1)) j) := by
                constructive_ring
          _ = add (fpow (twoAdicElem (s + 1)) j)
                (mul (fpow (twoAdicElem (s + 1)) j) (neg one)) := by
                conv => lhs; arg 2; rw [hSymm]
          _ = zero := by constructive_ring
      have hTwoNe : add (one : Goldilocks) one ≠ zero := by decide +kernel
      have hWjNe := fpow_ne_zero (twoAdicElem_ne_zero (s + 1) hs) j
      have hInv := LawfulField.mul_inv_cancel hTwoNe
      have h1 := congrArg (mul (LawfulField.inv (add (one : Goldilocks) one))) hTwoZero
      have e1 : mul (LawfulField.inv (add (one : Goldilocks) one))
          (mul (add one one) (fpow (twoAdicElem (s + 1)) j)) =
          mul (mul (add one one) (LawfulField.inv (add one one)))
            (fpow (twoAdicElem (s + 1)) j) := by constructive_ring
      have e0 : mul (LawfulField.inv (add (one : Goldilocks) one)) zero = zero := by
        constructive_ring
      rw [e1, hInv, LawfulCommRing.one_mul, e0] at h1
      exact hWjNe h1

/-- Subgroup of `2^s`-th roots of unity in `Goldilocks` (`s ≤ 32`). -/
def twoAdicCoset (s : Nat) : List Goldilocks :=
  (List.range (2 ^ s)).map (fpow (twoAdicElem s))

theorem twoAdicCoset_eq_map (s : Nat) :
    twoAdicCoset s = (List.range (2 ^ s)).map (fpow (twoAdicElem s)) := by unfold twoAdicCoset; rfl

theorem twoAdicCoset_length (s : Nat) : (twoAdicCoset s).length = 2 ^ s := by
  unfold twoAdicCoset
  rw [List.length_map, List.length_range]

private theorem nodup_map_on {α β : Type} (f : α → β) :
    ∀ l : List α, l.Nodup → (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) → (l.map f).Nodup
  | [], _, _ => List.Pairwise.nil
  | a :: l, hnd, hinj => by
    obtain ⟨ha, hnd'⟩ := List.nodup_cons.mp hnd
    refine List.nodup_cons.mpr ⟨?_, nodup_map_on f l hnd'
      (fun x hx y hy => hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))⟩
    intro hMem
    obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hMem
    have hab := hinj b (List.mem_cons_of_mem _ hb) a List.mem_cons_self hfb
    exact ha (hab ▸ hb)

private theorem nodup_append_disj {α : Type} {a b : List α}
    (ha : a.Nodup) (hb : b.Nodup) (hDisj : ∀ x ∈ a, ∀ y ∈ b, x ≠ y) :
    (a ++ b).Nodup := by
  induction a with
  | nil => exact hb
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := List.nodup_cons.mp ha
    refine List.nodup_cons.mpr ⟨?_, ih hxs
      (fun u hu v hv => hDisj u (List.mem_cons_of_mem _ hu) v hv)⟩
    intro hMem
    rcases List.mem_append.mp hMem with hInXs | hInB
    · exact hx hInXs
    · exact hDisj x List.mem_cons_self x hInB rfl

private theorem nodup_range_constructive : ∀ n : Nat, (List.range n).Nodup
  | 0 => List.Pairwise.nil
  | n + 1 => by
    rw [List.range_succ]
    refine nodup_append_disj (nodup_range_constructive n)
      (List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil) ?_
    intro x hx y hy
    obtain rfl := List.mem_singleton.mp hy
    have hxLt := List.mem_range.mp hx
    omega

theorem twoAdicCoset_nodup (s : Nat) (hs : s ≤ 32) : (twoAdicCoset s).Nodup :=
  nodup_map_on (fpow (twoAdicElem s)) (List.range (2 ^ s)) (nodup_range_constructive (2 ^ s))
    (fun i hi j hj hEq =>
      twoAdicElem_exp_inj s hs i j (List.mem_range.mp hi) (List.mem_range.mp hj) hEq)

theorem twoAdicCoset_pow_eq_one (s : Nat) (hs : s ≤ 32) {u : Goldilocks}
    (hu : u ∈ twoAdicCoset s) : fpow u (2 ^ s) = one ∧ u ≠ zero := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hu
  refine ⟨?_, fpow_ne_zero (twoAdicElem_ne_zero s hs) i⟩
  rw [← pow2Iter_eq_fpow]
  have hComm : ∀ k : Nat, pow2Iter k (fpow (twoAdicElem s) i) = fpow (pow2Iter k (twoAdicElem s)) i := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      show mul (pow2Iter k (fpow (twoAdicElem s) i)) (pow2Iter k (fpow (twoAdicElem s) i)) =
        fpow (mul (pow2Iter k (twoAdicElem s)) (pow2Iter k (twoAdicElem s))) i
      rw [ih, fpow_mul_base]
  rw [hComm s, pow2Iter_eq_fpow, twoAdicElem_pow2 s hs, fpow_one]

/-- The `2^s` roots of `X^(2^s) - ω^(2^s)` in `QuinticGoldilocks`. -/
def fiberRoots (s : Nat) (ω : QuinticGoldilocks) : List QuinticGoldilocks :=
  (twoAdicCoset s).map (fun u => mul (ofBase u) ω)

theorem fiberRoots_length (s : Nat) (ω : QuinticGoldilocks) :
    (fiberRoots s ω).length = 2 ^ s := by
  unfold fiberRoots
  rw [List.length_map, twoAdicCoset_length]

theorem fiberRoots_pow (s : Nat) (hs : s ≤ 32) (ω : QuinticGoldilocks) {r : QuinticGoldilocks}
    (hr : r ∈ fiberRoots s ω) : fpow r (2 ^ s) = fpow ω (2 ^ s) := by
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
  rw [fpow_mul_base, fpow_ofBase, (twoAdicCoset_pow_eq_one s hs hu).1,
    QuinticGoldilocks.ofBase_one, LawfulCommRing.one_mul]

theorem fiberRoots_nodup (s : Nat) (hs : s ≤ 32) {ω : QuinticGoldilocks} (hω : ω ≠ zero) :
    (fiberRoots s ω).Nodup :=
  nodup_map_on (fun u => mul (ofBase u) ω) (twoAdicCoset s) (twoAdicCoset_nodup s hs)
    (fun u₁ _ u₂ _ hEq => by
      have hInv := LawfulField.mul_inv_cancel hω
      have h1 := congrArg (fun z => mul z (LawfulField.inv ω)) hEq
      have e1 : mul (mul (ofBase u₁) ω) (LawfulField.inv ω) =
          mul (ofBase u₁) (mul ω (LawfulField.inv ω)) := by constructive_ring
      have e2 : mul (mul (ofBase u₂) ω) (LawfulField.inv ω) =
          mul (ofBase u₂) (mul ω (LawfulField.inv ω)) := by constructive_ring
      rw [e1, e2, hInv, LawfulCommRing.mul_one, LawfulCommRing.mul_one] at h1
      exact QuinticGoldilocks.ofBase_injective h1)

/-- Iterated Frobenius `frob^[k]` on `QuinticGoldilocks`. -/
def frobIter : Nat → QuinticGoldilocks → QuinticGoldilocks
  | 0, z => z
  | k + 1, z => frob (frobIter k z)

theorem frobIter_add :
    ∀ (a b : Nat) (z : QuinticGoldilocks), frobIter (a + b) z = frobIter a (frobIter b z)
  | 0, b, z => by
    rw [Nat.zero_add]
    rfl
  | a + 1, b, z => by
    have e : a + 1 + b = (a + b) + 1 := by omega
    rw [e]
    exact congrArg frob (frobIter_add a b z)

theorem frobIter_five (z : QuinticGoldilocks) : frobIter 5 z = z :=
  QuinticGoldilocks.frob_pow5 z

theorem frobIter_mod5 : ∀ (k : Nat) (z : QuinticGoldilocks), frobIter k z = frobIter (k % 5) z
  | k, z => by
    by_cases hk : k < 5
    · rw [Nat.mod_eq_of_lt hk]
    · have hSub : k = (k - 5) + 5 := by omega
      have hMod : k % 5 = (k - 5) % 5 := by
        conv => lhs; rw [hSub]
        exact Nat.add_mod_right (k - 5) 5
      rw [hMod]
      conv => lhs; rw [hSub, frobIter_add (k - 5) 5, frobIter_five]
      exact frobIter_mod5 (k - 5) z
termination_by k => k

theorem frobIter_inj :
    ∀ (k : Nat) {x y : QuinticGoldilocks}, frobIter k x = frobIter k y → x = y
  | 0, _, _, h => h
  | k + 1, x, y, h => by
    have h4 : frobIter 4 (frob (frobIter k x)) = frobIter 4 (frob (frobIter k y)) :=
      congrArg (frobIter 4) h
    have e1 : frobIter 4 (frob (frobIter k x)) = frobIter 5 (frobIter k x) := rfl
    have e2 : frobIter 4 (frob (frobIter k y)) = frobIter 5 (frobIter k y) := rfl
    rw [e1, e2, frobIter_five, frobIter_five] at h4
    exact frobIter_inj k h4

theorem frobIter_fixed_imp_frob {k : Nat} {z : QuinticGoldilocks}
    (hkLt : k < 5) (hkNe : k ≠ 0) (hFix : frobIter k z = z) : frob z = z := by
  rcases k with _ | _ | _ | _ | _ | k
  · exact absurd rfl hkNe
  · exact hFix
  · have h2 : frob (frob z) = z := hFix
    have h4 : frob (frob (frob (frob z))) = z := by
      rw [h2, h2]
    calc frob z = frob (frob (frob (frob (frob z)))) := by
            conv => lhs; arg 1; rw [← h4]
      _ = z := QuinticGoldilocks.frob_pow5 z
  · have h3 : frob (frob (frob z)) = z := hFix
    calc frob z = frob (frob (frob (frob (frob (frob z))))) := by
            rw [QuinticGoldilocks.frob_pow5 z]
      _ = frob (frob (frob z)) := by
            conv => lhs; arg 1; arg 1; arg 1; rw [h3]
      _ = z := h3
  · have h4 : frob (frob (frob (frob z))) = z := hFix
    calc frob z = frob (frob (frob (frob (frob z)))) := by
            conv => lhs; arg 1; rw [← h4]
      _ = z := QuinticGoldilocks.frob_pow5 z
  · omega

theorem fpow_frobIter (z : QuinticGoldilocks) :
    ∀ (k n : Nat), fpow (frobIter k z) n = frobIter k (fpow z n)
  | 0, _ => rfl
  | k + 1, n => by
    show fpow (frob (frobIter k z)) n = frob (frobIter k (fpow z n))
    rw [fpow_frob, fpow_frobIter z k n]

theorem frobIter_ofBase (a : Goldilocks) :
    ∀ k : Nat, frobIter k (ofBase a) = ofBase a
  | 0 => rfl
  | k + 1 => by
    show frob (frobIter k (ofBase a)) = ofBase a
    rw [frobIter_ofBase a k, QuinticGoldilocks.frob_ofBase]

theorem frobIter_mul :
    ∀ (k : Nat) (x y : QuinticGoldilocks), frobIter k (mul x y) = mul (frobIter k x) (frobIter k y)
  | 0, _, _ => rfl
  | k + 1, x, y => by
    show frob (frobIter k (mul x y)) = mul (frob (frobIter k x)) (frob (frobIter k y))
    rw [frobIter_mul k x y, QuinticGoldilocks.frob_mul]

/-- Protocol condition `(G2)` of `SECURITY.md` §V2.1 on the Stage-0 mask fiber generators `ωs`
    (`z_j = ω_j^(2^s)`): `s ≤ 32`, each `z_j ∉ F_p`, and distinct `z_j` lie in distinct
    `Gal(E / F_p)` orbits. -/
def MaskRootsValid (s : Nat) (ωs : List QuinticGoldilocks) : Prop :=
  s ≤ 32 ∧
  (∀ ω ∈ ωs, frob (fpow ω (2 ^ s)) ≠ fpow ω (2 ^ s)) ∧
  ωs.Pairwise (fun ω₁ ω₂ => ∀ k < 5, fpow ω₁ (2 ^ s) ≠ frobIter k (fpow ω₂ (2 ^ s)))

theorem MaskRootsValid.omega_ne_zero {s : Nat} {ωs : List QuinticGoldilocks}
    (hV : MaskRootsValid s ωs) {ω : QuinticGoldilocks} (hω : ω ∈ ωs) :
    ω ≠ zero ∧ fpow ω (2 ^ s) ≠ zero := by
  have hzNe : fpow ω (2 ^ s) ≠ zero := fun hz0 => by
    have hf := hV.2.1 ω hω
    rw [hz0, QuinticGoldilocks.frob_zero] at hf
    exact hf rfl
  refine ⟨fun h0 => ?_, hzNe⟩
  apply hzNe
  rw [h0]
  have h2Pos : 2 ^ s = (2 ^ s - 1) + 1 := by
    have hp := Nat.two_pow_pos s
    omega
  rw [h2Pos]
  show mul (zero : QuinticGoldilocks) (fpow zero (2 ^ s - 1)) = zero
  constructive_ring

private theorem nodup_append_of_disjoint {α : Type} {a b : List α}
    (ha : a.Nodup) (hb : b.Nodup) (hDisj : ∀ x ∈ a, ∀ y ∈ b, x ≠ y) :
    (a ++ b).Nodup := by
  induction a with
  | nil => exact hb
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := List.nodup_cons.mp ha
    refine List.nodup_cons.mpr ⟨?_, ih hxs (fun u hu v hv => hDisj u (List.mem_cons_of_mem _ hu) v hv)⟩
    intro hMem
    rcases List.mem_append.mp hMem with hInXs | hInB
    · exact hx hInXs
    · exact hDisj x List.mem_cons_self x hInB rfl

private theorem flatMap_fiberRoots_nodup (s : Nat) (hs : s ≤ 32) :
    ∀ ωs : List QuinticGoldilocks,
      (∀ ω ∈ ωs, frob (fpow ω (2 ^ s)) ≠ fpow ω (2 ^ s)) →
      ωs.Pairwise (fun ω₁ ω₂ => ∀ k < 5, fpow ω₁ (2 ^ s) ≠ frobIter k (fpow ω₂ (2 ^ s))) →
      (ωs.flatMap (fiberRoots s)).Nodup
  | [], _, _ => List.Pairwise.nil
  | ω :: rest, hNonBase, hPair => by
    rw [List.flatMap_cons]
    obtain ⟨hHeadRel, hTailPair⟩ := List.pairwise_cons.mp hPair
    have hωNz : ω ≠ zero := by
      intro h0
      have hf := hNonBase ω List.mem_cons_self
      rw [h0] at hf
      have h2Pos : 2 ^ s = (2 ^ s - 1) + 1 := by have hp := Nat.two_pow_pos s; omega
      rw [h2Pos] at hf
      dsimp only [fpow] at hf
      have hz : mul (zero : QuinticGoldilocks) (fpow zero (2 ^ s - 1)) = zero := by
        constructive_ring
      rw [hz, QuinticGoldilocks.frob_zero] at hf
      exact hf rfl
    refine nodup_append_of_disjoint (fiberRoots_nodup s hs hωNz)
      (flatMap_fiberRoots_nodup s hs rest
        (fun u hu => hNonBase u (List.mem_cons_of_mem _ hu)) hTailPair) ?_
    intro r₁ hr₁ r₂ hr₂ hEq
    obtain ⟨ω₂, hω₂, hr₂Mem⟩ := List.mem_flatMap.mp hr₂
    have hp₁ := fiberRoots_pow s hs ω hr₁
    have hp₂ := fiberRoots_pow s hs ω₂ hr₂Mem
    have hzEq : fpow ω (2 ^ s) = frobIter 0 (fpow ω₂ (2 ^ s)) :=
      hp₁.symm.trans ((congrArg (fun x => fpow x (2 ^ s)) hEq).trans hp₂)
    exact hHeadRel ω₂ hω₂ 0 (by decide) hzEq

private theorem maskRootsValid_pairSymm {s : Nat} {ωs : List QuinticGoldilocks}
    (hV : MaskRootsValid s ωs) :
    ∀ a ∈ ωs, ∀ b ∈ ωs, a ≠ b →
      ∀ k < 5, fpow a (2 ^ s) ≠ frobIter k (fpow b (2 ^ s)) := by
  induction ωs with
  | nil => intro a ha; nomatch ha
  | cons head tail ih =>
    obtain ⟨hHead, hTail⟩ := List.pairwise_cons.mp hV.2.2
    have hVTail : MaskRootsValid s tail :=
      ⟨hV.1, fun u hu => hV.2.1 u (List.mem_cons_of_mem _ hu), hTail⟩
    intro a ha b hb hab k hk hBad
    rcases List.mem_cons.mp ha with rfl | haT
    · rcases List.mem_cons.mp hb with rfl | hbT
      · exact hab rfl
      · exact hHead b hbT k hk hBad
    · rcases List.mem_cons.mp hb with rfl | hbT
      · let invK := (5 - k) % 5
        have hRev : fpow b (2 ^ s) = frobIter invK (fpow a (2 ^ s)) := by
          have h1 : frobIter invK (fpow a (2 ^ s)) =
              frobIter (invK + k) (fpow b (2 ^ s)) := by
            rw [frobIter_add, ← hBad]
          have hm0 : (invK + k) % 5 = 0 := by omega
          rw [frobIter_mod5 (invK + k), hm0] at h1
          exact h1.symm
        exact hHead a haT invK (Nat.mod_lt _ (by decide)) hRev
      · exact ih hVTail a haT b hbT hab k hk hBad

private theorem frobIter_fiberRoot_ne {s : Nat} (hs : s ≤ 32)
    {ωs : List QuinticGoldilocks} (hV : MaskRootsValid s ωs)
    {r₁ r₂ : QuinticGoldilocks} (hr₁ : r₁ ∈ ωs.flatMap (fiberRoots s))
    (hr₂ : r₂ ∈ ωs.flatMap (fiberRoots s))
    {k₁ k₂ : Nat} (hk₁ : k₁ < 5) (hk₂ : k₂ < 5)
    (hEq : frobIter k₁ r₁ = frobIter k₂ r₂) :
    k₁ = k₂ ∧ r₁ = r₂ := by
  obtain ⟨ω₁, hω₁, hm₁⟩ := List.mem_flatMap.mp hr₁
  obtain ⟨ω₂, hω₂, hm₂⟩ := List.mem_flatMap.mp hr₂
  have hp : fpow (frobIter k₁ r₁) (2 ^ s) = fpow (frobIter k₂ r₂) (2 ^ s) :=
    congrArg (fun x => fpow x (2 ^ s)) hEq
  rw [fpow_frobIter, fpow_frobIter, fiberRoots_pow s hs ω₁ hm₁,
    fiberRoots_pow s hs ω₂ hm₂] at hp
  let sh := (5 - k₁) % 5
  have hpShift : frobIter (sh + k₁) (fpow ω₁ (2 ^ s)) = frobIter (sh + k₂) (fpow ω₂ (2 ^ s)) := by
    rw [frobIter_add, frobIter_add, hp]
  have hMod1 : (sh + k₁) % 5 = 0 := by omega
  rw [frobIter_mod5 (sh + k₁), hMod1, frobIter_mod5 (sh + k₂)] at hpShift
  have hSameOmega : ω₁ = ω₂ := by
    by_cases hEqO : ω₁ = ω₂
    · exact hEqO
    · exact absurd hpShift
        (maskRootsValid_pairSymm hV ω₁ hω₁ ω₂ hω₂ hEqO ((sh + k₂) % 5) (Nat.mod_lt _ (by decide)))
  subst hSameOmega
  have hkEq : k₁ = k₂ := by
    by_cases hMod0 : (sh + k₂) % 5 = 0
    · omega
    · exfalso
      exact hV.2.1 ω₁ hω₁
        (frobIter_fixed_imp_frob (Nat.mod_lt _ (by decide)) hMod0 hpShift.symm)
  subst hkEq
  exact ⟨rfl, frobIter_inj k₁ hEq⟩

/-- **`(G2)` Discharges `blindPoints.Nodup` Across All `t · 2^s` Fiber Roots
    (`blindPoints_fiberRoots_nodup`)**:
    Under `qs.Nodup` and `MaskRootsValid s ωs`, all base-field query points `qs` together with
    all `t · 2^s` roots of `X^(2^s) - z_j` and their four Frobenius conjugates are pairwise
    distinct in `QuinticGoldilocks`. -/
theorem blindPoints_fiberRoots_nodup {s : Nat} {qs : List Goldilocks}
    {ωs : List QuinticGoldilocks} (hqs : qs.Nodup) (hV : MaskRootsValid s ωs) :
    (blindPoints qs (ωs.flatMap (fiberRoots s))).Nodup := by
  let ys := ωs.flatMap (fiberRoots s)
  have hysNd : ys.Nodup := flatMap_fiberRoots_nodup s hV.1 ωs hV.2.1 hV.2.2
  have hOrbNd : ∀ k < 5, (ys.map (frobIter k)).Nodup := fun k _ =>
    nodup_map_on (frobIter k) ys hysNd (fun a _ b _ h => frobIter_inj k h)
  have hOrbDisj : ∀ k₁ k₂ : Nat, k₁ < 5 → k₂ < 5 → k₁ ≠ k₂ →
      ∀ x ∈ ys.map (frobIter k₁), ∀ y ∈ ys.map (frobIter k₂), x ≠ y := by
    intro k₁ k₂ hk₁ hk₂ hNe x hx y hy hEq
    obtain ⟨r₁, hr₁, rfl⟩ := List.mem_map.mp hx
    obtain ⟨r₂, hr₂, rfl⟩ := List.mem_map.mp hy
    exact hNe (frobIter_fiberRoot_ne hV.1 hV hr₁ hr₂ hk₁ hk₂ hEq).1
  have hQsNd : (qs.map ofBase).Nodup :=
    nodup_map_on ofBase qs hqs (fun _ _ _ _ h => QuinticGoldilocks.ofBase_injective h)
  have hBaseDisj : ∀ k < 5, ∀ x ∈ qs.map ofBase, ∀ y ∈ ys.map (frobIter k), x ≠ y := by
    intro k hk x hx y hy hEq
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hy
    obtain ⟨ω, hω, hm⟩ := List.mem_flatMap.mp hr
    have hp := congrArg (fun z => fpow z (2 ^ s)) hEq
    rw [fpow_ofBase, fpow_frobIter, fiberRoots_pow s hV.1 ω hm] at hp
    let invK := (5 - k) % 5
    have hp2 := congrArg (frobIter invK) hp
    have hm0 : (invK + k) % 5 = 0 := by omega
    rw [frobIter_ofBase, ← frobIter_add, frobIter_mod5 (invK + k), hm0] at hp2
    have hp2' : ofBase (fpow q (2 ^ s)) = fpow ω (2 ^ s) := hp2
    have hf : frob (fpow ω (2 ^ s)) = fpow ω (2 ^ s) := by
      rw [← hp2', QuinticGoldilocks.frob_ofBase]
    exact hV.2.1 ω hω hf
  have hMap0 : ys = ys.map (frobIter 0) := (List.map_id' ys).symm
  have hMap1 : ys.map frob = ys.map (frobIter 1) := rfl
  have hMap2 : ys.map (fun z => frob (frob z)) = ys.map (frobIter 2) := rfl
  have hMap3 : ys.map (fun z => frob (frob (frob z))) = ys.map (frobIter 3) := rfl
  have hMap4 : ys.map (fun z => frob (frob (frob (frob z)))) = ys.map (frobIter 4) := rfl
  show (qs.map ofBase ++ (ys ++ (ys.map frob ++ (ys.map (fun z => frob (frob z)) ++
    (ys.map (fun z => frob (frob (frob z))) ++
      ys.map (fun z => frob (frob (frob (frob z))))))))).Nodup
  rw [hMap1, hMap2, hMap3, hMap4]
  conv => arg 1; arg 2; arg 1; rw [hMap0]
  have h34 := nodup_append_of_disjoint (hOrbNd 3 (by decide)) (hOrbNd 4 (by decide))
    (hOrbDisj 3 4 (by decide) (by decide) (by decide))
  have h234 := nodup_append_of_disjoint (hOrbNd 2 (by decide)) h34 (fun x hx y hy => by
    rcases List.mem_append.mp hy with hy3 | hy4
    · exact hOrbDisj 2 3 (by decide) (by decide) (by decide) x hx y hy3
    · exact hOrbDisj 2 4 (by decide) (by decide) (by decide) x hx y hy4)
  have h1234 := nodup_append_of_disjoint (hOrbNd 1 (by decide)) h234 (fun x hx y hy => by
    rcases List.mem_append.mp hy with hy2 | hy34
    · exact hOrbDisj 1 2 (by decide) (by decide) (by decide) x hx y hy2
    · rcases List.mem_append.mp hy34 with hy3 | hy4
      · exact hOrbDisj 1 3 (by decide) (by decide) (by decide) x hx y hy3
      · exact hOrbDisj 1 4 (by decide) (by decide) (by decide) x hx y hy4)
  have h01234 := nodup_append_of_disjoint (hOrbNd 0 (by decide)) h1234 (fun x hx y hy => by
    rcases List.mem_append.mp hy with hy1 | hy234
    · exact hOrbDisj 0 1 (by decide) (by decide) (by decide) x hx y hy1
    · rcases List.mem_append.mp hy234 with hy2 | hy34
      · exact hOrbDisj 0 2 (by decide) (by decide) (by decide) x hx y hy2
      · rcases List.mem_append.mp hy34 with hy3 | hy4
        · exact hOrbDisj 0 3 (by decide) (by decide) (by decide) x hx y hy3
        · exact hOrbDisj 0 4 (by decide) (by decide) (by decide) x hx y hy4)
  refine nodup_append_of_disjoint hQsNd h01234 (fun x hx y hy => ?_)
  rcases List.mem_append.mp hy with hy0 | hy1234
  · exact hBaseDisj 0 (by decide) x hx y hy0
  · rcases List.mem_append.mp hy1234 with hy1 | hy234
    · exact hBaseDisj 1 (by decide) x hx y hy1
    · rcases List.mem_append.mp hy234 with hy2 | hy34
      · exact hBaseDisj 2 (by decide) x hx y hy2
      · rcases List.mem_append.mp hy34 with hy3 | hy4
        · exact hBaseDisj 3 (by decide) x hx y hy3
        · exact hBaseDisj 4 (by decide) x hx y hy4

/-- Evaluate a list of canonical degree-`< 2^s` remainders across the fibers `fiberRoots s ω`. -/
def evalResidues (s : Nat) :
    List QuinticGoldilocks → List (List QuinticGoldilocks) → List QuinticGoldilocks
  | [], _ => []
  | _, [] => []
  | ω :: ωs, rem :: rems => (fiberRoots s ω).map (evalCoeffs rem) ++ evalResidues s ωs rems

/-- Interpolate canonical degree-`< 2^s` remainders from fiber evaluations. -/
def interpResidues (s : Nat) :
    List QuinticGoldilocks → List QuinticGoldilocks → List (List QuinticGoldilocks)
  | [], _ => []
  | ω :: ωs, vs =>
    newtonInterp (fiberRoots s ω) (vs.take (2 ^ s)) :: interpResidues s ωs (vs.drop (2 ^ s))

theorem flatMap_fiberRoots_length (s : Nat) :
    ∀ ωs : List QuinticGoldilocks, (ωs.flatMap (fiberRoots s)).length = ωs.length * 2 ^ s
  | [] => (Nat.zero_mul (2 ^ s)).symm
  | ω :: ωs => by
    rw [List.flatMap_cons, List.length_append, fiberRoots_length, flatMap_fiberRoots_length s ωs]
    show 2 ^ s + ωs.length * 2 ^ s = (ωs.length + 1) * 2 ^ s
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem interpResidues_shape (s : Nat) :
    ∀ (ωs : List QuinticGoldilocks) (vs : List QuinticGoldilocks),
      vs.length = ωs.length * 2 ^ s →
      (interpResidues s ωs vs).length = ωs.length ∧
      ∀ r ∈ interpResidues s ωs vs, r.length = 2 ^ s
  | [], _, _ => ⟨rfl, fun _ h => nomatch h⟩
  | ω :: ωs, vs, hvs => by
    have hGe : 2 ^ s ≤ vs.length := by
      have e : (ω :: ωs).length * 2 ^ s = 2 ^ s + ωs.length * 2 ^ s := by
        show (ωs.length + 1) * 2 ^ s = 2 ^ s + ωs.length * 2 ^ s
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      omega
    have hTakeLen : (vs.take (2 ^ s)).length = 2 ^ s := by
      rw [List.length_take]; omega
    have hDropLen : (vs.drop (2 ^ s)).length = ωs.length * 2 ^ s := by
      rw [List.length_drop]
      have e : (ω :: ωs).length * 2 ^ s = 2 ^ s + ωs.length * 2 ^ s := by
        show (ωs.length + 1) * 2 ^ s = 2 ^ s + ωs.length * 2 ^ s
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      omega
    obtain ⟨ihLen, ihMem⟩ := interpResidues_shape s ωs (vs.drop (2 ^ s)) hDropLen
    refine ⟨congrArg Nat.succ ihLen, fun r hr => ?_⟩
    rcases List.mem_cons.mp hr with rfl | hrTail
    · rw [newtonInterp_length _ _ ((fiberRoots_length s ω).trans hTakeLen.symm),
        fiberRoots_length]
    · exact ihMem r hrTail

theorem evalResidues_length (s : Nat) :
    ∀ (ωs : List QuinticGoldilocks) (rems : List (List QuinticGoldilocks)),
      rems.length = ωs.length →
      (∀ r ∈ rems, r.length = 2 ^ s) →
      (evalResidues s ωs rems).length = ωs.length * 2 ^ s
  | [], [], _, _ => (Nat.zero_mul (2 ^ s)).symm
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | ω :: ωs, rem :: rems, hLen, hRems => by
    show ((fiberRoots s ω).map (evalCoeffs rem) ++ evalResidues s ωs rems).length =
      (ωs.length + 1) * 2 ^ s
    rw [List.length_append, List.length_map, fiberRoots_length,
      evalResidues_length s ωs rems (Nat.succ.inj hLen)
        (fun r hr => hRems r (List.mem_cons_of_mem _ hr)),
      Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem interpResidues_evalResidues (s : Nat) (hs : s ≤ 32) :
    ∀ (ωs : List QuinticGoldilocks) (rems : List (List QuinticGoldilocks)),
      (∀ ω ∈ ωs, ω ≠ zero) →
      rems.length = ωs.length →
      (∀ r ∈ rems, r.length = 2 ^ s) →
      interpResidues s ωs (evalResidues s ωs rems) = rems
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, h, _ => by cases h
  | _ :: _, [], _, h, _ => by cases h
  | ω :: ωs, rem :: rems, hNz, hLen, hRems => by
    have hMapLen : ((fiberRoots s ω).map (evalCoeffs rem)).length = 2 ^ s := by
      rw [List.length_map, fiberRoots_length]
    have hTake : (((fiberRoots s ω).map (evalCoeffs rem)) ++ evalResidues s ωs rems).take (2 ^ s) =
        (fiberRoots s ω).map (evalCoeffs rem) := by
      rw [← hMapLen, List.take_left]
    have hDrop : (((fiberRoots s ω).map (evalCoeffs rem)) ++ evalResidues s ωs rems).drop (2 ^ s) =
        evalResidues s ωs rems := by
      rw [← hMapLen, List.drop_left]
    show newtonInterp (fiberRoots s ω)
        ((((fiberRoots s ω).map (evalCoeffs rem)) ++ evalResidues s ωs rems).take (2 ^ s)) ::
      interpResidues s ωs
        ((((fiberRoots s ω).map (evalCoeffs rem)) ++ evalResidues s ωs rems).drop (2 ^ s)) =
      rem :: rems
    rw [hTake, hDrop,
      newtonInterp_eval (fiberRoots s ω) rem (fiberRoots_nodup s hs (hNz ω List.mem_cons_self))
        ((hRems rem List.mem_cons_self).trans (fiberRoots_length s ω).symm),
      interpResidues_evalResidues s hs ωs rems
        (fun u hu => hNz u (List.mem_cons_of_mem _ hu))
        (Nat.succ.inj hLen) (fun r hr => hRems r (List.mem_cons_of_mem _ hr))]

theorem evalResidues_interpResidues (s : Nat) (hs : s ≤ 32) :
    ∀ (ωs : List QuinticGoldilocks) (vs : List QuinticGoldilocks),
      (∀ ω ∈ ωs, ω ≠ zero) →
      vs.length = ωs.length * 2 ^ s →
      evalResidues s ωs (interpResidues s ωs vs) = vs
  | [], vs, _, hvs => by
    have h0 : vs.length = 0 := hvs.trans (Nat.zero_mul (2 ^ s))
    exact (List.eq_nil_of_length_eq_zero h0).symm
  | ω :: ωs, vs, hNz, hvs => by
    have hGe : 2 ^ s ≤ vs.length := by
      have e : (ω :: ωs).length * 2 ^ s = 2 ^ s + ωs.length * 2 ^ s := by
        show (ωs.length + 1) * 2 ^ s = 2 ^ s + ωs.length * 2 ^ s
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      omega
    have hTakeLen : (vs.take (2 ^ s)).length = 2 ^ s := by rw [List.length_take]; omega
    have hDropLen : (vs.drop (2 ^ s)).length = ωs.length * 2 ^ s := by
      rw [List.length_drop]
      have e : (ω :: ωs).length * 2 ^ s = 2 ^ s + ωs.length * 2 ^ s := by
        show (ωs.length + 1) * 2 ^ s = 2 ^ s + ωs.length * 2 ^ s
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      omega
    show (fiberRoots s ω).map (evalCoeffs (newtonInterp (fiberRoots s ω) (vs.take (2 ^ s)))) ++
        evalResidues s ωs (interpResidues s ωs (vs.drop (2 ^ s))) = vs
    rw [eval_newtonInterp (fiberRoots s ω) (vs.take (2 ^ s))
        (fiberRoots_nodup s hs (hNz ω List.mem_cons_self))
        ((fiberRoots_length s ω).trans hTakeLen.symm),
      evalResidues_interpResidues s hs ωs (vs.drop (2 ^ s))
        (fun u hu => hNz u (List.mem_cons_of_mem _ hu)) hDropLen,
      List.take_append_drop]

/-- Constructive equivalence between fiber evaluation vectors and canonical remainders in
    `∏_{j=1}^t E[X] / (X^(2^s) - z_j)`. -/
def residuesEquiv (s : Nat) (ωs : List QuinticGoldilocks) (hs : s ≤ 32)
    (hNz : ∀ ω ∈ ωs, ω ≠ zero) :
    SimpleEquiv
      {vs : List QuinticGoldilocks // vs.length = (ωs.flatMap (fiberRoots s)).length}
      {rems : List (List QuinticGoldilocks) //
        rems.length = ωs.length ∧ ∀ r ∈ rems, r.length = 2 ^ s} where
  toFun vs :=
    ⟨interpResidues s ωs vs.1,
      interpResidues_shape s ωs vs.1 (vs.2.trans (flatMap_fiberRoots_length s ωs))⟩
  invFun rems :=
    ⟨evalResidues s ωs rems.1,
      (evalResidues_length s ωs rems.1 rems.2.1 rems.2.2).trans
        (flatMap_fiberRoots_length s ωs).symm⟩
  left_inv vs := Subtype.ext
    (evalResidues_interpResidues s hs ωs vs.1 hNz
      (vs.2.trans (flatMap_fiberRoots_length s ωs)))
  right_inv rems := Subtype.ext
    (interpResidues_evalResidues s hs ωs rems.1 hNz rems.2.1 rems.2.2)

/-- Exact quotient-ring view of Lemma V2.2 (`SECURITY.md` §V2.2):
    `B ↦ ((q^(N-b) · B(q))_{q ∈ qs}, (X^(N-b) · B(X) mod (X^(2^s) - ω_j^(2^s)))_{j = 1..t})`. -/
def blindingResidueView (s shiftDeg : Nat) (qs : List Goldilocks)
    (ωs : List QuinticGoldilocks) (cs : List Goldilocks) :
    List Goldilocks × List (List QuinticGoldilocks) :=
  (pmul (qs.map (evalCoeffs cs)) (qs.map (fun q => fpow q shiftDeg)),
   ωs.map (fun ω =>
     (divModBinomial (2 ^ s - 1) (fpow ω (2 ^ s)) (shiftMonomial shiftDeg (cs.map ofBase))).1))

private theorem evalResidues_blindingResidueView (s shiftDeg : Nat) (hs : s ≤ 32)
    (cs : List Goldilocks) :
    ∀ ωs : List QuinticGoldilocks,
      evalResidues s ωs
        (ωs.map (fun ω =>
          (divModBinomial (2 ^ s - 1) (fpow ω (2 ^ s))
            (shiftMonomial shiftDeg (cs.map ofBase))).1)) =
      pmul ((ωs.flatMap (fiberRoots s)).map (evalCoeffs (cs.map ofBase)))
        ((ωs.flatMap (fiberRoots s)).map (fun r => fpow r shiftDeg))
  | [] => rfl
  | ω :: ωs => by
    have h2Pos : (2 ^ s - 1) + 1 = 2 ^ s := by
      have hp := Nat.two_pow_pos s
      omega
    have hHead : (fiberRoots s ω).map
        (evalCoeffs (divModBinomial (2 ^ s - 1) (fpow ω (2 ^ s))
          (shiftMonomial shiftDeg (cs.map ofBase))).1) =
      pmul ((fiberRoots s ω).map (evalCoeffs (cs.map ofBase)))
        ((fiberRoots s ω).map (fun r => fpow r shiftDeg)) := by
      have hPt : ∀ r ∈ fiberRoots s ω,
          evalCoeffs (divModBinomial (2 ^ s - 1) (fpow ω (2 ^ s))
            (shiftMonomial shiftDeg (cs.map ofBase))).1 r =
          mul (evalCoeffs (cs.map ofBase) r) (fpow r shiftDeg) := by
        intro r hr
        have hrPow : fpow r ((2 ^ s - 1) + 1) = fpow ω (2 ^ s) := by
          rw [h2Pos]
          exact fiberRoots_pow s hs ω hr
        rw [evalCoeffs_divModBinomial_at_root (2 ^ s - 1) (fpow ω (2 ^ s)) _ hrPow,
          evalCoeffs_shiftMonomial, LawfulCommRing.mul_comm]
      have hZip : ∀ l : List QuinticGoldilocks,
          pmul (l.map (evalCoeffs (cs.map ofBase))) (l.map (fun r => fpow r shiftDeg)) =
            l.map (fun r => mul (evalCoeffs (cs.map ofBase) r) (fpow r shiftDeg)) := by
        intro l
        induction l with
        | nil => rfl
        | cons a l ih =>
          show mul (evalCoeffs (cs.map ofBase) a) (fpow a shiftDeg) ::
              pmul (l.map (evalCoeffs (cs.map ofBase))) (l.map (fun r => fpow r shiftDeg)) =
            mul (evalCoeffs (cs.map ofBase) a) (fpow a shiftDeg) ::
              l.map (fun r => mul (evalCoeffs (cs.map ofBase) r) (fpow r shiftDeg))
          rw [ih]
      rw [hZip]
      exact map_congr_mem _ _ _ hPt
    have hPmulAppend : ∀ (a₁ b₁ a₂ b₂ : List QuinticGoldilocks), a₁.length = b₁.length →
        pmul (a₁ ++ a₂) (b₁ ++ b₂) = pmul a₁ b₁ ++ pmul a₂ b₂ := by
      intro a₁ b₁ a₂ b₂ hL
      induction a₁ generalizing b₁ with
      | nil =>
        have hb0 := List.eq_nil_of_length_eq_zero hL.symm
        subst hb0
        rfl
      | cons x xs ih =>
        cases b₁ with
        | nil => cases hL
        | cons y ys =>
          show mul x y :: pmul (xs ++ a₂) (ys ++ b₂) = (mul x y :: pmul xs ys) ++ pmul a₂ b₂
          rw [ih ys (Nat.succ.inj hL)]
          rfl
    show (fiberRoots s ω).map
        (evalCoeffs (divModBinomial (2 ^ s - 1) (fpow ω (2 ^ s))
          (shiftMonomial shiftDeg (cs.map ofBase))).1) ++
      evalResidues s ωs
        (ωs.map (fun ω =>
          (divModBinomial (2 ^ s - 1) (fpow ω (2 ^ s))
            (shiftMonomial shiftDeg (cs.map ofBase))).1)) =
      pmul (((fiberRoots s ω) ++ ωs.flatMap (fiberRoots s)).map (evalCoeffs (cs.map ofBase)))
        (((fiberRoots s ω) ++ ωs.flatMap (fiberRoots s)).map (fun r => fpow r shiftDeg))
    rw [List.map_append, List.map_append,
      hPmulAppend _ _ _ _ ((List.length_map _).trans (List.length_map _).symm),
      hHead, evalResidues_blindingResidueView s shiftDeg hs cs ωs]

/-- Constructive `SimpleEquiv` for **Lemma V2.2 in exact quotient-ring form**
    (`F_p^{|qs| + 5 t 2^s} ≃ F_p^{|qs|} × ∏_{j=1}^t E[X] / (X^(2^s) - z_j)`). -/
def blindingResidueEquiv (s shiftDeg : Nat) (qs : List Goldilocks)
    (ωs : List QuinticGoldilocks) (hqs : qs.Nodup) (hqz : ∀ q ∈ qs, q ≠ zero)
    (hV : MaskRootsValid s ωs) :
    SimpleEquiv
      {cs : List Goldilocks // cs.length = qs.length + 5 * (ωs.length * 2 ^ s)}
      ({us : List Goldilocks // us.length = qs.length} ×
        {rems : List (List QuinticGoldilocks) //
          rems.length = ωs.length ∧ ∀ r ∈ rems, r.length = 2 ^ s}) :=
  let ys := ωs.flatMap (fiberRoots s)
  have hysLen : ys.length = ωs.length * 2 ^ s := flatMap_fiberRoots_length s ωs
  have hLsNz : ∀ l ∈ qs.map (fun q => fpow q shiftDeg), l ≠ zero := by
    intro l hl
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
    exact fpow_ne_zero (hqz q hq) shiftDeg
  have hMsNz : ∀ m ∈ ys.map (fun r => fpow r shiftDeg), m ≠ zero := by
    intro m hm
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
    obtain ⟨ω, hω, hmR⟩ := List.mem_flatMap.mp hr
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hmR
    have huNz := (twoAdicCoset_pow_eq_one s hV.1 hu).2
    have hωNz := (hV.omega_ne_zero hω).1
    have hrNz : mul (ofBase u) ω ≠ zero := by
      intro h0
      have h1 := congrArg (fun z => mul z (LawfulField.inv ω)) h0
      have e1 : mul (mul (ofBase u) ω) (LawfulField.inv ω) =
          mul (ofBase u) (mul ω (LawfulField.inv ω)) := by constructive_ring
      have e0 : mul (zero : QuinticGoldilocks) (LawfulField.inv ω) = zero := by constructive_ring
      rw [e1, LawfulField.mul_inv_cancel hωNz, LawfulCommRing.mul_one, e0,
        ← QuinticGoldilocks.ofBase_zero] at h1
      exact huNz (QuinticGoldilocks.ofBase_injective h1)
    exact fpow_ne_zero hrNz shiftDeg
  let lenCast : SimpleEquiv
      {cs : List Goldilocks // cs.length = qs.length + 5 * (ωs.length * 2 ^ s)}
      {cs : List Goldilocks // cs.length = qs.length + 5 * ys.length} :=
    { toFun := fun cs => ⟨cs.1, by rw [hysLen]; exact cs.2⟩
      invFun := fun cs => ⟨cs.1, by rw [← hysLen]; exact cs.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let scaled := postProd
    (blindingEquiv qs ys (blindPoints_fiberRoots_nodup hqs hV))
    (scaleEquiv (qs.map (fun q => fpow q shiftDeg)) (List.length_map _) hLsNz)
    (scaleEquiv (ys.map (fun r => fpow r shiftDeg)) (List.length_map _) hMsNz)
  let resEq := residuesEquiv s ωs hV.1 (fun ω hω => (hV.omega_ne_zero hω).1)
  { toFun := fun cs =>
      let p := scaled.toFun (lenCast.toFun cs)
      (p.1, resEq.toFun p.2)
    invFun := fun o =>
      lenCast.invFun (scaled.invFun (o.1, resEq.invFun o.2))
    left_inv := fun cs => by
      dsimp only
      rw [resEq.left_inv, scaled.left_inv, lenCast.left_inv]
    right_inv := fun o => by
      dsimp only
      rw [lenCast.right_inv, scaled.right_inv]
      exact Prod.ext rfl (resEq.right_inv o.2) }

theorem blindingResidueEquiv_apply (s shiftDeg : Nat) (qs : List Goldilocks)
    (ωs : List QuinticGoldilocks) (hqs : qs.Nodup) (hqz : ∀ q ∈ qs, q ≠ zero)
    (hV : MaskRootsValid s ωs)
    (cs : {cs : List Goldilocks // cs.length = qs.length + 5 * (ωs.length * 2 ^ s)}) :
    (((blindingResidueEquiv s shiftDeg qs ωs hqs hqz hV).toFun cs).1.1,
     ((blindingResidueEquiv s shiftDeg qs ωs hqs hqz hV).toFun cs).2.1) =
      blindingResidueView s shiftDeg qs ωs cs.1 := by
  refine Prod.ext rfl ?_
  show interpResidues s ωs
      (pmul ((ωs.flatMap (fiberRoots s)).map (evalCoeffs (cs.1.map ofBase)))
        ((ωs.flatMap (fiberRoots s)).map (fun r => fpow r shiftDeg))) =
    ωs.map (fun ω =>
      (divModBinomial (2 ^ s - 1) (fpow ω (2 ^ s)) (shiftMonomial shiftDeg (cs.1.map ofBase))).1)
  rw [← evalResidues_blindingResidueView s shiftDeg hV.1 cs.1 ωs]
  refine interpResidues_evalResidues s hV.1 ωs _
    (fun ω hω => (hV.omega_ne_zero hω).1) (List.length_map _) ?_
  intro r hr
  obtain ⟨ω, _, rfl⟩ := List.mem_map.mp hr
  have h2Pos : (2 ^ s - 1) + 1 = 2 ^ s := by
    have hp := Nat.two_pow_pos s
    omega
  rw [divModBinomial_rem_length, h2Pos]

/-- **Lemma V2.2 in Exact Quotient-Ring Form (`v2_blinding_residue_ring_bijective`,
    `SECURITY.md` §§V2.2, V2.6, V2.9)**:
    Under `qs.Nodup`, `0 ∉ qs`, and `(G2)` (`MaskRootsValid s ωs`), the linear map
    `B ↦ ((q^(N-b) · B(q))_{q ∈ qs}, (X^(N-b) · B(X) mod (X^(2^s) - z_j))_{j = 1..t})`
    on polynomials `B ∈ F_p[X]_{< |qs| + 5 t 2^s}` is an explicit constructive bijection onto
    `F_p^{|qs|} × ∏_{j=1}^t E[X] / (X^(2^s) - z_j)`. -/
theorem v2_blinding_residue_ring_bijective (s shiftDeg : Nat) (qs : List Goldilocks)
    (ωs : List QuinticGoldilocks) (hqs : qs.Nodup) (hqz : ∀ q ∈ qs, q ≠ zero)
    (hV : MaskRootsValid s ωs) :
    ∃ Φ : SimpleEquiv
        {cs : List Goldilocks // cs.length = qs.length + 5 * (ωs.length * 2 ^ s)}
        ({us : List Goldilocks // us.length = qs.length} ×
          {rems : List (List QuinticGoldilocks) //
            rems.length = ωs.length ∧ ∀ r ∈ rems, r.length = 2 ^ s}),
      ∀ cs, ((Φ.toFun cs).1.1, (Φ.toFun cs).2.1) = blindingResidueView s shiftDeg qs ωs cs.1 :=
  ⟨blindingResidueEquiv s shiftDeg qs ωs hqs hqz hV,
    blindingResidueEquiv_apply s shiftDeg qs ωs hqs hqz hV⟩

/-- Componentwise vector addition on lists of residue polynomials. -/
def vaddResidues : List (List QuinticGoldilocks) → List (List QuinticGoldilocks) →
    List (List QuinticGoldilocks)
  | r1 :: rs1, r2 :: rs2 => vadd r1 r2 :: vaddResidues rs1 rs2
  | _, _ => []

def vsubResidues : List (List QuinticGoldilocks) → List (List QuinticGoldilocks) →
    List (List QuinticGoldilocks)
  | r1 :: rs1, r2 :: rs2 => vsub r1 r2 :: vsubResidues rs1 rs2
  | _, _ => []

private theorem vaddResidues_shape (s : Nat) :
    ∀ (a b : List (List QuinticGoldilocks)),
      a.length = b.length →
      (∀ r ∈ a, r.length = 2 ^ s) →
      (∀ r ∈ b, r.length = 2 ^ s) →
      (vaddResidues a b).length = b.length ∧ ∀ r ∈ vaddResidues a b, r.length = 2 ^ s
  | [], [], _, _, _ => ⟨rfl, fun _ h => nomatch h⟩
  | [], _ :: _, h, _, _ => by cases h
  | _ :: _, [], h, _, _ => by cases h
  | r1 :: rs1, r2 :: rs2, hL, ha, hb => by
    obtain ⟨ihL, ihM⟩ := vaddResidues_shape s rs1 rs2 (Nat.succ.inj hL)
      (fun r hr => ha r (List.mem_cons_of_mem _ hr))
      (fun r hr => hb r (List.mem_cons_of_mem _ hr))
    refine ⟨congrArg Nat.succ ihL, fun r hr => ?_⟩
    rcases List.mem_cons.mp hr with rfl | hrT
    · exact (vadd_length r1 r2
        ((ha r1 List.mem_cons_self).trans (hb r2 List.mem_cons_self).symm)).trans
        (hb r2 List.mem_cons_self)
    · exact ihM r hrT

private theorem vsubResidues_shape (s : Nat) :
    ∀ (a b : List (List QuinticGoldilocks)),
      a.length = b.length →
      (∀ r ∈ a, r.length = 2 ^ s) →
      (∀ r ∈ b, r.length = 2 ^ s) →
      (vsubResidues a b).length = b.length ∧ ∀ r ∈ vsubResidues a b, r.length = 2 ^ s
  | [], [], _, _, _ => ⟨rfl, fun _ h => nomatch h⟩
  | [], _ :: _, h, _, _ => by cases h
  | _ :: _, [], h, _, _ => by cases h
  | r1 :: rs1, r2 :: rs2, hL, ha, hb => by
    obtain ⟨ihL, ihM⟩ := vsubResidues_shape s rs1 rs2 (Nat.succ.inj hL)
      (fun r hr => ha r (List.mem_cons_of_mem _ hr))
      (fun r hr => hb r (List.mem_cons_of_mem _ hr))
    refine ⟨congrArg Nat.succ ihL, fun r hr => ?_⟩
    rcases List.mem_cons.mp hr with rfl | hrT
    · exact (vsub_length r1 r2
        ((ha r1 List.mem_cons_self).trans (hb r2 List.mem_cons_self).symm)).trans
        (hb r2 List.mem_cons_self)
    · exact ihM r hrT

private theorem vsubResidues_vaddResidues (s : Nat) :
    ∀ (d v : List (List QuinticGoldilocks)),
      d.length = v.length →
      (∀ r ∈ d, r.length = 2 ^ s) →
      (∀ r ∈ v, r.length = 2 ^ s) →
      vsubResidues (vaddResidues d v) d = v
  | [], [], _, _, _ => rfl
  | [], _ :: _, h, _, _ => by cases h
  | _ :: _, [], h, _, _ => by cases h
  | r1 :: rs1, r2 :: rs2, hL, hd, hv => by
    show vsub (vadd r1 r2) r1 :: vsubResidues (vaddResidues rs1 rs2) rs1 = r2 :: rs2
    rw [vsub_vadd r1 r2 ((hd r1 List.mem_cons_self).trans (hv r2 List.mem_cons_self).symm),
      vsubResidues_vaddResidues s rs1 rs2 (Nat.succ.inj hL)
        (fun r hr => hd r (List.mem_cons_of_mem _ hr))
        (fun r hr => hv r (List.mem_cons_of_mem _ hr))]

private theorem vaddResidues_vsubResidues (s : Nat) :
    ∀ (d o : List (List QuinticGoldilocks)),
      d.length = o.length →
      (∀ r ∈ d, r.length = 2 ^ s) →
      (∀ r ∈ o, r.length = 2 ^ s) →
      vaddResidues d (vsubResidues o d) = o
  | [], [], _, _, _ => rfl
  | [], _ :: _, h, _, _ => by cases h
  | _ :: _, [], h, _, _ => by cases h
  | r1 :: rs1, r2 :: rs2, hL, hd, ho => by
    show vadd r1 (vsub r2 r1) :: vaddResidues rs1 (vsubResidues rs2 rs1) = r2 :: rs2
    rw [vadd_vsub r1 r2 ((hd r1 List.mem_cons_self).trans (ho r2 List.mem_cons_self).symm),
      vaddResidues_vsubResidues s rs1 rs2 (Nat.succ.inj hL)
        (fun r hr => hd r (List.mem_cons_of_mem _ hr))
        (fun r hr => ho r (List.mem_cons_of_mem _ hr))]

/-- **Lemma V2.2 Perfect Simulation in Residue-Ring Form
    (`v2_blinding_residue_ring_perfectly_simulated`)**:
    Witness-dependent base-field evaluations and `E[X] / (X^(2^s) - z_j)` quotient-ring coset
    residues masked by `blindingResidueView` on uniform blinder coefficients are perfectly
    simulated (`CoinBijectionSimulated`) by uniform elements of
    `F_p^{|qs|} × ∏_{j=1}^t E[X] / (X^(2^s) - z_j)`. -/
theorem v2_blinding_residue_ring_perfectly_simulated (s shiftDeg : Nat) (qs : List Goldilocks)
    (ωs : List QuinticGoldilocks) (hqs : qs.Nodup) (hqz : ∀ q ∈ qs, q ≠ zero)
    (hV : MaskRootsValid s ωs) :
    CoinBijectionSimulated
      (fun (d : {us : List Goldilocks // us.length = qs.length} ×
            {rems : List (List QuinticGoldilocks) //
              rems.length = ωs.length ∧ ∀ r ∈ rems, r.length = 2 ^ s})
          (cs : {cs : List Goldilocks // cs.length = qs.length + 5 * (ωs.length * 2 ^ s)}) =>
        let bw := blindingResidueView s shiftDeg qs ωs cs.1
        (vadd d.1.1 bw.1, vaddResidues d.2.1 bw.2))
      (fun (o : {us : List Goldilocks // us.length = qs.length} ×
            {rems : List (List QuinticGoldilocks) //
              rems.length = ωs.length ∧ ∀ r ∈ rems, r.length = 2 ^ s}) =>
        (o.1.1, o.2.1)) := by
  intro d
  let baseEq := blindingResidueEquiv s shiftDeg qs ωs hqs hqz hV
  let resOff : SimpleEquiv
      {rems : List (List QuinticGoldilocks) //
        rems.length = ωs.length ∧ ∀ r ∈ rems, r.length = 2 ^ s}
      {rems : List (List QuinticGoldilocks) //
        rems.length = ωs.length ∧ ∀ r ∈ rems, r.length = 2 ^ s} :=
    { toFun := fun v =>
        let sh := vaddResidues_shape s d.2.1 v.1 (d.2.2.1.trans v.2.1.symm) d.2.2.2 v.2.2
        ⟨vaddResidues d.2.1 v.1, sh.1.trans v.2.1, sh.2⟩
      invFun := fun o =>
        let sh := vsubResidues_shape s o.1 d.2.1 (o.2.1.trans d.2.2.1.symm) o.2.2 d.2.2.2
        ⟨vsubResidues o.1 d.2.1, sh.1.trans d.2.2.1, sh.2⟩
      left_inv := fun v => Subtype.ext
        (vsubResidues_vaddResidues s d.2.1 v.1 (d.2.2.1.trans v.2.1.symm) d.2.2.2 v.2.2)
      right_inv := fun o => Subtype.ext
        (vaddResidues_vsubResidues s d.2.1 o.1 (d.2.2.1.trans o.2.1.symm) d.2.2.2 o.2.2) }
  refine ⟨postProd baseEq (offsetEquiv d.1) resOff, fun cs => ?_⟩
  have hApp := blindingResidueEquiv_apply s shiftDeg qs ωs hqs hqz hV cs
  obtain ⟨h1, h2⟩ := Prod.mk.inj hApp
  show (vadd d.1.1 (blindingResidueView s shiftDeg qs ωs cs.1).1,
        vaddResidues d.2.1 (blindingResidueView s shiftDeg qs ωs cs.1).2) =
    (vadd d.1.1 ((baseEq.toFun cs).1).1, vaddResidues d.2.1 ((baseEq.toFun cs).2).1)
  rw [h1, h2]
  rfl

end ResidueRingBridge

#export_eqns MaskRootsValid blindingResidueView divModBinomial shiftMonomial fpow frobIter

/-! ## §7. Profile roster and cell count -/

/-- `zk_hem::v2::params::Profile`. -/
inductive ZkHemV2Profile where
  | cshakeJohnson400
  | turboShakeJohnson400
  deriving DecidableEq, Repr

namespace ZkHemV2Profile

/-- `Profile::ALL`. -/
def all : List ZkHemV2Profile := [.cshakeJohnson400, .turboShakeJohnson400]

theorem mem_all (p : ZkHemV2Profile) : p ∈ all := by
  cases p <;> decide

/-- `Profile::wire_tag`. -/
@[expose] def wireTag : ZkHemV2Profile → UInt8
  | .cshakeJohnson400 => 16
  | .turboShakeJohnson400 => 17

/-- `Profile::from_wire_tag`. -/
@[expose] def ofWireTag (tag : UInt8) : Option ZkHemV2Profile :=
  if tag = 16 then some .cshakeJohnson400
  else if tag = 17 then some .turboShakeJohnson400
  else none

theorem ofWireTag_wireTag (p : ZkHemV2Profile) : ofWireTag p.wireTag = some p := by
  cases p <;> rfl

theorem wireTag_of_ofWireTag {tag : UInt8} {p : ZkHemV2Profile} (h : ofWireTag tag = some p) :
    p.wireTag = tag := by
  unfold ofWireTag at h
  by_cases h16 : tag = 16
  · rw [ite_eq_left h16] at h; cases h; exact h16.symm
  rw [ite_eq_right h16] at h
  by_cases h17 : tag = 17
  · rw [ite_eq_left h17] at h; cases h; exact h17.symm
  rw [ite_eq_right h17] at h
  cases h

theorem wireTag_injective {p q : ZkHemV2Profile} (h : p.wireTag = q.wireTag) : p = q := by
  have h1 := ofWireTag_wireTag p
  rw [h, ofWireTag_wireTag q] at h1
  exact (Option.some.inj h1).symm


end ZkHemV2Profile

/-- `DIGEST_BYTES`. -/
abbrev digestBytes : Nat := 50
/-- `SALT_BYTES`. -/
abbrev saltBytes : Nat := 32
/-- `LIMBS`. -/
abbrev limbs : Nat := 5
/-- `MASK_POINTS`. -/
abbrev maskPoints : Nat := 5

/-- `STAGE0_QUERIES`, indexed by `log_cells` in `16..=24`. -/
@[expose] def stage0Queries (logCells : Nat) : Option Nat :=
  if logCells < 16 then none
  else ([281, 281, 287, 295, 300, 300, 320, 342, 342] : List Nat)[logCells - 16]?

theorem stage0Queries_table :
    [16, 17, 18, 19, 20, 21, 22, 23, 24].map stage0Queries =
      [some 281, some 281, some 287, some 295, some 300, some 300, some 320, some 342,
        some 342] := by
  decide

theorem stage0Queries_below (l : Nat) (h : l < 16) : stage0Queries l = none := by
  unfold stage0Queries
  rw [ite_eq_left h]

theorem stage0Queries_above (l : Nat) (h : 24 < l) : stage0Queries l = none := by
  unfold stage0Queries
  have h16 : ¬ l < 16 := by omega
  rw [ite_eq_right h16]
  exact List.getElem?_eq_none (by
    show 9 ≤ l - 16
    omega)

/-- `blind_cells_for`. -/
@[expose] def blindCells (stepVars openedFibers : Nat) : Nat :=
  (openedFibers + limbs * maskPoints) * 2 ^ stepVars

/-- The opened symbols plus five base-field cells for each of the `maskPoints * 2^s` exposed
    `E`-values. -/
theorem blindCells_eq (s q : Nat) :
    blindCells s q = q * 2 ^ s + limbs * (maskPoints * 2 ^ s) := by
  show (q + limbs * maskPoints) * 2 ^ s = q * 2 ^ s + limbs * (maskPoints * 2 ^ s)
  rw [Nat.add_mul, Nat.mul_assoc]

/-- The blinder count of the layout is the coefficient count of `v2_blinding_count` for
    `q 2^s` opened symbols and `maskPoints * 2^s` exposed values. -/
theorem blindCells_eq_blinding_count (s q : Nat) (qs : List Goldilocks)
    (ys : List QuinticGoldilocks) (hq : qs.length = q * 2 ^ s)
    (hy : ys.length = maskPoints * 2 ^ s) :
    blindCells s q = qs.length + 5 * ys.length := by
  rw [blindCells_eq, hq, hy]

#verify_constructive Qsag.ZkHemV2.v2_mask_line_perfectly_simulated
  Qsag.ZkHemV2.v2_mask_claim_determined
  Qsag.ZkHemV2.v2_mask_symbol_determined
  Qsag.ZkHemV2.v2_mask_line_view_perfectly_simulated
  Qsag.ZkHemV2.tooth_zero_mask_challenge_reveals_word
  Qsag.ZkHemV2.v2_fold_scalar_matrix_bijective
  Qsag.ZkHemV2.v2_fold_scalars_perfectly_simulated
  Qsag.ZkHemV2.tooth_zero_fold_challenge_not_surjective
  Qsag.ZkHemV2.tooth_repeated_mask_point_not_injective
  Qsag.ZkHemV2.tooth_four_mask_points_not_surjective
  Qsag.ZkHemV2.v2_blinding_count
  Qsag.ZkHemV2.v2_blinding_count_scaled
  Qsag.ZkHemV2.v2_opened_symbols_and_mask_values_perfectly_simulated
  Qsag.ZkHemV2.v2_scaled_symbols_and_mask_values_perfectly_simulated
  Qsag.ZkHemV2.tooth_blinding_base_field_point_not_surjective
  Qsag.ZkHemV2.tooth_blinding_conjugate_points_not_surjective
  Qsag.ZkHemV2.evalCoeffs_divModBinomial
  Qsag.ZkHemV2.evalCoeffs_divModBinomial_at_root
  Qsag.ZkHemV2.fpow_zero
  Qsag.ZkHemV2.fpow_succ
  Qsag.ZkHemV2.pow2Iter_zero
  Qsag.ZkHemV2.pow2Iter_one
  Qsag.ZkHemV2.twoAdicCoset_eq_map
  Qsag.ZkHemV2.twoAdicCoset_nodup
  Qsag.ZkHemV2.blindPoints_fiberRoots_nodup
  Qsag.ZkHemV2.v2_blinding_residue_ring_bijective
  Qsag.ZkHemV2.v2_blinding_residue_ring_perfectly_simulated
  Qsag.ZkHemV2.ZkHemV2Profile.ofWireTag_wireTag
  Qsag.ZkHemV2.ZkHemV2Profile.wireTag_of_ofWireTag
  Qsag.ZkHemV2.stage0Queries_table
  Qsag.ZkHemV2.blindCells_eq
  Qsag.ZkHemV2.blindCells_eq_blinding_count

end Qsag.ZkHemV2
end

public section
namespace Qsag.ZkHemV2
#export_eqns unmaskLine vaddResidues
end Qsag.ZkHemV2
end
