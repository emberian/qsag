module
public import Qsag.Protocol.Aggregation.ZkHem
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

section Offsets
variable {F : Type} [LawfulField F]

/-- Translation by a fixed vector of the same length. -/
def offsetEquiv {n : Nat} (d : {l : List F // l.length = n}) :
    SimpleEquiv {l : List F // l.length = n} {l : List F // l.length = n} where
  toFun v := ⟨vadd d.1 v.1, (vadd_length _ _ (d.2.trans v.2.symm)).trans v.2⟩
  invFun o := ⟨vsub o.1 d.1, (vsub_length _ _ (o.2.trans d.2.symm)).trans d.2⟩
  left_inv v := Subtype.ext (vsub_vadd _ _ (d.2.trans v.2.symm))
  right_inv o := Subtype.ext (vadd_vsub _ _ (d.2.trans o.2.symm))

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
