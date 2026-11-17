module
public import Qsag.Spec.Algebra
import Qsag.Tactic.AssuranceKit
public import Qsag.Tactic.Prelude
public import Qsag.Math.Tactic.CommRing
public import Qsag.Math.Counting

/-!
# Qsag.Math.CoeffPoly

Univariate polynomials as coefficient lists over a `LawfulCommRing` / `LawfulField`.

* `RoundPoly`, Horner evaluation `evalCoeffs`, synthetic division `quotLinear` and the
  factor-theorem root bound (also in leading-coefficient form);
* vanishing polynomials of a point list;
* the homogeneous linear solver `gauss_nullspace_witness` over a field;
* canonical (trimmed) coefficient lists: `trimPoly`, `pAdd`, `pMul`, `pScale`, raw convolution
  `rawMul`, Euclidean division and gcd with fuel, divisibility `DvdTrim`, and the
  Welch–Berlekamp interpolation argument;
* formal-root multiplicity bound for the Guruswami–Sudan step, `mulLinear` / `vanishingCoeffs`,
  and the coefficient pairing `ringDot` with Lagrange evaluation at zero.
-/

public section
-- Avoid the choice-based LawfulBEq derived from the Fin order package.
attribute [-instance] Fin.instLinearOrderPackage
namespace Qsag
set_option autoImplicit false
/-! ## 7. Univariate Polynomials (`RoundPoly R`) & Factor-Theorem Root Bound -/

structure RoundPoly (R : Type) where
  coeffs : List R
  deriving DecidableEq, Repr

namespace RoundPoly

@[expose] def evalCoeffs {R : Type} [CommRingOps R] : List R → R → R
  | [], _ => CommRingOps.zero
  | c :: cs, x => CommRingOps.add c (CommRingOps.mul x (evalCoeffs cs x))

@[simp] theorem evalCoeffs_nil {R : Type} [CommRingOps R] (x : R) :
    evalCoeffs ([] : List R) x = CommRingOps.zero := rfl

@[simp] theorem evalCoeffs_cons {R : Type} [CommRingOps R] (c : R) (cs : List R) (x : R) :
    evalCoeffs (c :: cs) x = CommRingOps.add c (CommRingOps.mul x (evalCoeffs cs x)) := rfl

def eval {R : Type} [CommRingOps R] (p : RoundPoly R) (x : R) : R :=
  evalCoeffs p.coeffs x

def subCoeffs {R : Type} [CommRingOps R] : List R → List R → List R
  | [], [] => []
  | c :: cs, [] => c :: subCoeffs cs []
  | [], d :: ds => CommRingOps.neg d :: subCoeffs [] ds
  | c :: cs, d :: ds => CommRingOps.sub c d :: subCoeffs cs ds

theorem subCoeffs_cons_cons {R : Type} [CommRingOps R] (c d : R) (cs ds : List R) :
    subCoeffs (c :: cs) (d :: ds) = CommRingOps.sub c d :: subCoeffs cs ds := by
  conv => lhs; unfold subCoeffs

theorem subCoeffs_length :
    ∀ {R : Type} [CommRingOps R] (cs ds : List R),
      (subCoeffs cs ds).length = Nat.max cs.length ds.length
  | _, _, [], [] => by simp [subCoeffs]
  | _, _, _ :: cs, [] => by simp [subCoeffs, subCoeffs_length cs []]
  | _, _, [], _ :: ds => by simp [subCoeffs, subCoeffs_length [] ds]
  | _, _, _ :: cs, _ :: ds => by
    simp [subCoeffs, subCoeffs_length cs ds, Nat.succ_max_succ]

theorem evalCoeffs_sub {R : Type} [LawfulCommRing R] :
    ∀ (cs ds : List R) (x : R),
      evalCoeffs (subCoeffs cs ds) x = CommRingOps.sub (evalCoeffs cs x) (evalCoeffs ds x)
  | [], [], _ => by
    simp [subCoeffs, evalCoeffs, LawfulCommRing.sub_self]
  | c :: cs, [], x => by
    simp only [subCoeffs, evalCoeffs, evalCoeffs_sub cs [] x]
    rw [LawfulCommRing.sub_zero, LawfulCommRing.sub_zero]
  | [], d :: ds, x => by
    simp only [subCoeffs, evalCoeffs, evalCoeffs_sub [] ds x]
    rw [LawfulCommRing.sub_eq_add_neg CommRingOps.zero (evalCoeffs ds x),
        LawfulCommRing.zero_add, LawfulCommRing.mul_neg,
        LawfulCommRing.sub_eq_add_neg CommRingOps.zero _,
        LawfulCommRing.zero_add]
    apply LawfulCommRing.add_left_cancel
      (a := CommRingOps.add d (CommRingOps.mul x (evalCoeffs ds x)))
    rw [LawfulCommRing.add_right_neg,
        LawfulCommRing.add_add_add_comm,
        LawfulCommRing.add_right_neg,
        LawfulCommRing.add_right_neg,
        LawfulCommRing.add_zero]
  | c :: cs, d :: ds, x => by
    simp only [subCoeffs, evalCoeffs, evalCoeffs_sub cs ds x]
    rw [LawfulCommRing.mul_sub]
    apply LawfulCommRing.add_left_cancel
      (a := CommRingOps.add d (CommRingOps.mul x (evalCoeffs ds x)))
    rw [LawfulCommRing.add_sub_cancel_left]
    rw [LawfulCommRing.add_add_add_comm,
        LawfulCommRing.add_sub_cancel_left,
        LawfulCommRing.add_sub_cancel_left]

/-- Monic synthetic linear division quotient `(p(X) - p(r)) / (X - r)`. -/
@[expose] def quotLinear {R : Type} [CommRingOps R] : List R → R → List R
  | [], _ => []
  | [_], _ => []
  | _ :: c₁ :: cs, r => evalCoeffs (c₁ :: cs) r :: quotLinear (c₁ :: cs) r

theorem quotLinear_length {R : Type} [CommRingOps R] :
    ∀ (cs : List R) (r : R), (quotLinear cs r).length = cs.length - 1
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: c₁ :: cs, r => by
    simp only [quotLinear, List.length_cons, quotLinear_length (c₁ :: cs) r]
    simp

/-- **Factor Theorem Identity (`evalCoeffs_eq_mul_quotLinear_add`)**:
    $p(x) = (x - r) \cdot q(x) + p(r)$ in every `LawfulCommRing R`. -/
theorem evalCoeffs_eq_mul_quotLinear_add {R : Type} [LawfulCommRing R] :
    ∀ (cs : List R) (r x : R),
      evalCoeffs cs x =
        CommRingOps.add
          (CommRingOps.mul (CommRingOps.sub x r) (evalCoeffs (quotLinear cs r) x))
          (evalCoeffs cs r)
  | [], r, x => by
    simp [quotLinear, evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | [c₀], r, x => by
    simp [quotLinear, evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.zero_add]
  | c₀ :: c₁ :: cs, r, x => by
    let tl := c₁ :: cs
    have ih := evalCoeffs_eq_mul_quotLinear_add tl r x
    change CommRingOps.add c₀ (CommRingOps.mul x (evalCoeffs tl x)) =
      CommRingOps.add
        (CommRingOps.mul (CommRingOps.sub x r)
          (CommRingOps.add (evalCoeffs tl r) (CommRingOps.mul x (evalCoeffs (quotLinear tl r) x))))
        (CommRingOps.add c₀ (CommRingOps.mul r (evalCoeffs tl r)))
    rw [ih]
    rw [LawfulCommRing.left_distrib x,
        LawfulCommRing.left_distrib (CommRingOps.sub x r),
        LawfulCommRing.sub_mul x r (evalCoeffs tl r)]
    have hcommX : CommRingOps.mul (CommRingOps.sub x r)
        (CommRingOps.mul x (evalCoeffs (quotLinear tl r) x)) =
        CommRingOps.mul x
          (CommRingOps.mul (CommRingOps.sub x r) (evalCoeffs (quotLinear tl r) x)) := by
      rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm (CommRingOps.sub x r) x,
          LawfulCommRing.mul_assoc]
    rw [hcommX]
    apply LawfulCommRing.add_left_cancel (a := CommRingOps.mul r (evalCoeffs tl r))
    let A := CommRingOps.mul r (evalCoeffs tl r)
    let B := CommRingOps.mul x (evalCoeffs tl r)
    let C := CommRingOps.mul x (CommRingOps.mul (CommRingOps.sub x r) (evalCoeffs (quotLinear tl r) x))
    change CommRingOps.add A (CommRingOps.add c₀ (CommRingOps.add C B)) =
      CommRingOps.add A (CommRingOps.add (CommRingOps.add (CommRingOps.sub B A) C) (CommRingOps.add c₀ A))
    rw [← LawfulCommRing.add_assoc A (CommRingOps.add (CommRingOps.sub B A) C) (CommRingOps.add c₀ A),
        ← LawfulCommRing.add_assoc A (CommRingOps.sub B A) C,
        LawfulCommRing.add_sub_cancel_left A B]
    rw [LawfulCommRing.add_comm C B,
        LawfulCommRing.add_comm c₀ A,
        ← LawfulCommRing.add_assoc A c₀ (CommRingOps.add B C),
        LawfulCommRing.add_comm A c₀,
        LawfulCommRing.add_assoc c₀ A (CommRingOps.add B C),
        ← LawfulCommRing.add_assoc c₀ A (CommRingOps.add B C),
        LawfulCommRing.add_comm (CommRingOps.add c₀ A) (CommRingOps.add B C)]

private theorem mem_of_mem_filter_local {α : Type} {p : α → Bool} {x : α} :
    ∀ {l : List α}, x ∈ l.filter p → x ∈ l
  | [], h => by cases h
  | _ :: _, h => by
    simp only [List.filter] at h
    split at h
    · cases h with
      | head => exact .head _
      | tail _ hm => exact .tail _ (mem_of_mem_filter_local hm)
    · exact .tail _ (mem_of_mem_filter_local h)

private theorem pred_of_mem_filter_local {α : Type} {p : α → Bool} {x : α} :
    ∀ {l : List α}, x ∈ l.filter p → p x = true
  | [], h => by cases h
  | _ :: _, h => by
    simp only [List.filter] at h
    split at h
    · rename_i hpx
      cases h with
      | head => exact hpx
      | tail _ hm => exact pred_of_mem_filter_local hm
    · exact pred_of_mem_filter_local h

private theorem nodup_filter_local {α : Type} (p : α → Bool) :
    ∀ {l : List α}, l.Nodup → (l.filter p).Nodup
  | [], _ => .nil
  | _ :: _, .cons hrel htail => by
    simp only [List.filter]
    split
    · exact .cons (fun b hb => hrel b (mem_of_mem_filter_local hb)) (nodup_filter_local p htail)
    · exact nodup_filter_local p htail

private theorem filter_eq_self_of_forall {α : Type} {p : α → Bool} :
    ∀ {xs : List α}, (∀ x ∈ xs, p x = true) → xs.filter p = xs
  | [], _ => rfl
  | y :: ys, h => by
    have hy := h y (.head _)
    simp only [List.filter, hy]
    exact congrArg (y :: ·) (filter_eq_self_of_forall (fun z hz => h z (.tail _ hz)))

/-- **Lagrange / Factor-Theorem Root-Counting Bound (`roots_nodup_length_le`)**:
    Over every `LawfulCommRing R` without zero divisors, any non-zero polynomial of formal
    degree $\le d$ has at most `d` roots in any duplicate-free list `S : List R`. -/
theorem roots_nodup_length_le
    {R : Type} [LawfulCommRing R] [DecidableEq R] [NoZeroDivisors R] :
    ∀ (d : Nat) (cs : List R) (S : List R),
      S.Nodup →
      cs.length ≤ d + 1 →
      (∃ x₀ : R, evalCoeffs cs x₀ ≠ CommRingOps.zero) →
      (S.filter (fun r => decide (evalCoeffs cs r = CommRingOps.zero))).length ≤ d
  | 0, cs, S, _, hlen, ⟨x₀, hx₀⟩ => by
    have hempty : S.filter (fun r => decide (evalCoeffs cs r = CommRingOps.zero)) = [] := by
      cases hfilt : S.filter (fun r => decide (evalCoeffs cs r = CommRingOps.zero)) with
      | nil => rfl
      | cons r rs =>
        exfalso
        have hpred := pred_of_mem_filter_local (p := fun r => decide (evalCoeffs cs r = CommRingOps.zero))
          (l := S) (x := r) (by rw [hfilt]; exact .head _)
        rw [decide_eq_true_eq] at hpred
        cases cs with
        | nil => exact hx₀ rfl
        | cons c₀ tl =>
          cases tl with
          | nil =>
            simp only [evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero] at hpred hx₀
            exact hx₀ hpred
          | cons _ _ =>
            simp only [List.length_cons] at hlen
            omega
    rw [hempty]
    exact Nat.le_refl 0
  | d + 1, cs, S, hNodup, hlen, ⟨x₀, hx₀⟩ => by
    have hndRoots : (S.filter (fun r => decide (evalCoeffs cs r = CommRingOps.zero))).Nodup :=
      nodup_filter_local _ hNodup
    cases hRoots : S.filter (fun r => decide (evalCoeffs cs r = CommRingOps.zero)) with
    | nil => simp
    | cons r rest =>
      rw [hRoots] at hndRoots
      cases hndRoots with
      | cons hNotMem hndRest =>
        have hrRoot : evalCoeffs cs r = CommRingOps.zero := by
          have hp := pred_of_mem_filter_local
            (p := fun r => decide (evalCoeffs cs r = CommRingOps.zero))
            (l := S) (x := r) (by rw [hRoots]; exact .head _)
          exact of_decide_eq_true hp
        let qcs := quotLinear cs r
        have hqLen : qcs.length ≤ d + 1 := by
          dsimp [qcs]; rw [quotLinear_length]; omega
        have hqNonzero : ∃ x₁ : R, evalCoeffs qcs x₁ ≠ CommRingOps.zero := by
          refine ⟨x₀, fun hq0 => hx₀ ?_⟩
          rw [evalCoeffs_eq_mul_quotLinear_add cs r x₀, hq0, hrRoot,
              LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
        have hSubRest : ∀ y ∈ rest, decide (evalCoeffs qcs y = CommRingOps.zero) = true := by
          intro y hy
          have hyInFilt : y ∈ S.filter (fun r => decide (evalCoeffs cs r = CommRingOps.zero)) := by
            rw [hRoots]; exact .tail _ hy
          have hyRoot : evalCoeffs cs y = CommRingOps.zero :=
            of_decide_eq_true
              (pred_of_mem_filter_local (p := fun r => decide (evalCoeffs cs r = CommRingOps.zero)) hyInFilt)
          have hyNeR : y ≠ r := fun heq => hNotMem y hy heq.symm
          have hSubNe : CommRingOps.sub y r ≠ CommRingOps.zero :=
            fun hsub0 => hyNeR (LawfulCommRing.sub_eq_zero_iff.mp hsub0)
          have hfac := evalCoeffs_eq_mul_quotLinear_add cs r y
          rw [hyRoot, hrRoot, LawfulCommRing.add_zero] at hfac
          rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hfac.symm with hbad | hqy0
          · exact False.elim (hSubNe hbad)
          · exact decide_eq_true hqy0
        have hRestEq : rest.filter (fun y => decide (evalCoeffs qcs y = CommRingOps.zero)) = rest :=
          filter_eq_self_of_forall hSubRest
        have ih := roots_nodup_length_le d qcs rest hndRest hqLen hqNonzero
        rw [hRestEq] at ih
        simp only [List.length_cons]
        omega

end RoundPoly

/-- Monic vanishing polynomial `∏_{c ∈ C} (X - c)` of degree `C.length`. -/
def vanishingPoly {F : Type} [CommRingOps F] : List F → List F
  | [] => [CommRingOps.one]
  | c :: cs =>
    let p := vanishingPoly cs
    RoundPoly.subCoeffs (CommRingOps.zero :: p) (p.map (CommRingOps.mul c))

theorem vanishingPoly_length {F : Type} [CommRingOps F] :
    ∀ (C : List F), (vanishingPoly C).length = C.length + 1
  | [] => rfl
  | c :: cs => by
    simp only [vanishingPoly, RoundPoly.subCoeffs_length, List.length_cons, List.length_map,
               vanishingPoly_length cs]
    exact Nat.max_eq_left (by omega)

private theorem evalCoeffs_map_mul {F : Type} [LawfulCommRing F] (c x : F) :
    ∀ (p : List F), RoundPoly.evalCoeffs (p.map (CommRingOps.mul c)) x =
      CommRingOps.mul c (RoundPoly.evalCoeffs p x)
  | [] => by simp [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero]
  | a :: as => by
    simp only [List.map, RoundPoly.evalCoeffs, evalCoeffs_map_mul c x as]
    rw [LawfulCommRing.left_distrib,
        ← LawfulCommRing.mul_assoc c x _,
        LawfulCommRing.mul_comm c x,
        LawfulCommRing.mul_assoc]

theorem eval_vanishingPoly_eq_zero_of_mem {F : Type} [LawfulCommRing F] :
    ∀ {C : List F} {z : F}, z ∈ C → RoundPoly.evalCoeffs (vanishingPoly C) z = CommRingOps.zero
  | [], _, h => by cases h
  | c :: cs, z, h => by
    simp only [vanishingPoly, RoundPoly.evalCoeffs_sub, RoundPoly.evalCoeffs_cons,
               LawfulCommRing.zero_add, evalCoeffs_map_mul]
    rw [← LawfulCommRing.sub_mul]
    cases h with
    | head =>
      rw [LawfulCommRing.sub_self, LawfulCommRing.zero_mul]
    | tail _ hm =>
      rw [eval_vanishingPoly_eq_zero_of_mem hm, LawfulCommRing.mul_zero]

theorem eval_vanishingPoly_ne_zero_of_not_mem
    {F : Type} [LawfulField F] [DecidableEq F] :
    ∀ {C : List F} {z : F}, z ∉ C → RoundPoly.evalCoeffs (vanishingPoly C) z ≠ CommRingOps.zero
  | [], z, _ => by
    simp only [vanishingPoly, RoundPoly.evalCoeffs_cons, RoundPoly.evalCoeffs_nil,
               LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    exact LawfulField.one_ne_zero
  | c :: cs, z, hnot => by
    simp only [vanishingPoly, RoundPoly.evalCoeffs_sub, RoundPoly.evalCoeffs_cons,
               LawfulCommRing.zero_add, evalCoeffs_map_mul, ← LawfulCommRing.sub_mul]
    have hzc : z ≠ c := fun heq => hnot (heq ▸ .head _)
    have hzNotCs : z ∉ cs := fun hm => hnot (.tail _ hm)
    have hsubNe : CommRingOps.sub z c ≠ CommRingOps.zero :=
      fun h0 => hzc (LawfulCommRing.sub_eq_zero_iff.mp h0)
    have ih := eval_vanishingPoly_ne_zero_of_not_mem hzNotCs
    intro hprod
    rcases LawfulField.mul_eq_zero hprod with h1 | h2
    · exact hsubNe h1
    · exact ih h2

theorem last_subCoeffs_vanishingPoly
    {F : Type} [LawfulField F] :
    ∀ (p G : List F),
      0 < p.length →
      p.getD (p.length - 1) CommRingOps.zero = CommRingOps.one →
      G.length < p.length →
      (RoundPoly.subCoeffs p G).getD (p.length - 1) CommRingOps.zero = CommRingOps.one
  | [], _, hp, _, _ => by cases hp
  | [c], [], _, hlast, _ => by
    simpa [RoundPoly.subCoeffs] using hlast
  | [_], _ :: _, _, _, hlt => by simp at hlt
  | c₀ :: c₁ :: cs, [], _, hlast, _ => by
    have hpos : 0 < (c₁ :: cs).length := by simp
    have ih := last_subCoeffs_vanishingPoly (c₁ :: cs) [] hpos hlast (by simp)
    simpa [RoundPoly.subCoeffs] using ih
  | c₀ :: c₁ :: cs, g₀ :: gs, _, hlast, hlt => by
    have hpos : 0 < (c₁ :: cs).length := by simp
    have hlt' : gs.length < (c₁ :: cs).length := by simp at hlt ⊢; omega
    have ih := last_subCoeffs_vanishingPoly (c₁ :: cs) gs hpos hlast hlt'
    simpa [RoundPoly.subCoeffs] using ih

theorem vanishingPoly_last_one
    {F : Type} [LawfulField F] :
    ∀ (C : List F), (vanishingPoly C).getD C.length CommRingOps.zero = CommRingOps.one
  | [] => rfl
  | c :: cs => by
    have hcsLen : (vanishingPoly cs).length = cs.length + 1 := vanishingPoly_length cs
    have h0Last : (CommRingOps.zero :: vanishingPoly cs).getD
        ((CommRingOps.zero :: vanishingPoly cs).length - 1) CommRingOps.zero =
        CommRingOps.one := by
      simp only [List.length_cons, Nat.add_sub_cancel, hcsLen]
      simpa [List.getD] using vanishingPoly_last_one cs
    have hmapLt : ((vanishingPoly cs).map (CommRingOps.mul c)).length <
        (CommRingOps.zero :: vanishingPoly cs).length := by simp [hcsLen]
    have h := last_subCoeffs_vanishingPoly
      (CommRingOps.zero :: vanishingPoly cs)
      ((vanishingPoly cs).map (CommRingOps.mul c))
      (by simp) h0Last hmapLt
    simpa [vanishingPoly, hcsLen] using h

theorem lt_length_of_getElem?_eq_some {α : Type} :
    ∀ {xs : List α} {i : Nat} {x : α}, xs[i]? = some x → i < xs.length
  | [], _, _, h => by simp at h
  | _ :: _, 0, _, _ => by simp
  | _ :: xs, i + 1, _, h =>
    Nat.succ_lt_succ (lt_length_of_getElem?_eq_some (by simpa using h))

theorem exists_nonroot_of_monic_len
    {F : Type} [LawfulField F] [DecidableEq F] :
    ∀ (k : Nat) (p U : List F),
      p.length = k + 1 →
      p.getD k CommRingOps.zero = CommRingOps.one →
      U.Nodup →
      k + 1 ≤ U.length →
      ∃ x₀ ∈ U, RoundPoly.evalCoeffs p x₀ ≠ CommRingOps.zero
  | 0, [c], u :: _, _, hlast, _, _ => by
    simp only [List.getD, List.getElem?_cons_zero, Option.getD_some] at hlast
    subst hlast
    refine ⟨u, .head _, ?_⟩
    simp [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    exact LawfulField.one_ne_zero
  | 0, [], _, hlen, _, _, _ => by cases hlen
  | 0, _ :: _ :: _, _, hlen, _, _, _ => by cases hlen
  | k + 1, p, [], _, _, _, hU => by cases hU
  | k + 1, p, u :: us, hlen, hlast, .cons hnot hnd, hU => by
    if hev : RoundPoly.evalCoeffs p u = CommRingOps.zero then
      let q := RoundPoly.quotLinear p u
      have hqLen : q.length = k + 1 := by
        dsimp [q]; rw [RoundPoly.quotLinear_length, hlen]; rfl
      have hqLast : q.getD k CommRingOps.zero = CommRingOps.one := by
        have aux : ∀ (m : Nat) (xs : List F),
            xs.length = m + 2 →
            (RoundPoly.quotLinear xs u).getD m CommRingOps.zero =
              xs.getD (m + 1) CommRingOps.zero := by
          intro m xs hxs
          induction m generalizing xs with
          | zero =>
            rcases xs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
            · cases hxs
            · cases hxs
            · simp [RoundPoly.quotLinear, RoundPoly.evalCoeffs,
                    LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
            · cases hxs
          | succ m' ihm =>
            rcases xs with _ | ⟨a, _ | ⟨b, tl⟩⟩
            · cases hxs
            · cases hxs
            · have htl : (b :: tl).length = m' + 2 := Nat.succ.inj hxs
              simpa [RoundPoly.quotLinear] using ihm (b :: tl) htl
        rw [aux k p hlen, hlast]
      have hUsLen : k + 1 ≤ us.length := Nat.le_of_succ_le_succ hU
      rcases exists_nonroot_of_monic_len k q us hqLen hqLast hnd hUsLen with ⟨x₁, hx₁Mem, hx₁Ne⟩
      refine ⟨x₁, .tail _ hx₁Mem, ?_⟩
      rw [RoundPoly.evalCoeffs_eq_mul_quotLinear_add p u x₁, hev, LawfulCommRing.add_zero]
      have hneU : x₁ ≠ u := fun heq => hnot x₁ hx₁Mem heq.symm
      have hsubNe : CommRingOps.sub x₁ u ≠ CommRingOps.zero :=
        fun h0 => hneU (LawfulCommRing.sub_eq_zero_iff.mp h0)
      intro hprod
      rcases LawfulField.mul_eq_zero hprod with h1 | h2
      · exact hsubNe h1
      · exact hx₁Ne h2
    else
      exact ⟨u, .head _, hev⟩
  termination_by structural k => k

/-- Horner recursion for the `k`-th univariate formal Hasse derivative at `b`, valid over every
    commutative ring without binomial or factorial division. -/
@[expose] def gsUniHasse {R : Type} [CommRingOps R] : List R → Nat → R → R
  | [], _, _ => CommRingOps.zero
  | c :: cs, 0, b => CommRingOps.add c (CommRingOps.mul b (gsUniHasse cs 0 b))
  | _ :: cs, k + 1, b =>
    CommRingOps.add (gsUniHasse cs k b) (CommRingOps.mul b (gsUniHasse cs (k + 1) b))


open RoundPoly
/-! ## §3. Constructive Homogeneous Linear Solver (`gauss_nullspace_witness`) -/

/-- Dot product of two `List F` vectors over `CommRingOps F`. -/
@[expose] def dotVec {F : Type} [CommRingOps F] : List F → List F → F
  | [], _ => CommRingOps.zero
  | _, [] => CommRingOps.zero
  | a :: as, b :: bs => CommRingOps.add (CommRingOps.mul a b) (dotVec as bs)

/-- Scalar multiple `c · v` of a vector `v : List F`. -/
def scaleVec {F : Type} [CommRingOps F] (c : F) (v : List F) : List F :=
  v.map (CommRingOps.mul c)

/-- Componentwise difference `a - b` of two vectors of equal length. -/
def subVec {F : Type} [CommRingOps F] : List F → List F → List F
  | [], _ => []
  | _, [] => []
  | a :: as, b :: bs => CommRingOps.sub a b :: subVec as bs

/-- Remove element at index `p` from a list. -/
def dropIdx {α : Type} : Nat → List α → List α
  | _, [] => []
  | 0, _ :: xs => xs
  | p + 1, x :: xs => x :: dropIdx p xs

/-- Insert `val` at index `p` in a list. -/
def insertIdxVal {α : Type} : Nat → α → List α → List α
  | 0, val, xs => val :: xs
  | _ + 1, val, [] => [val]
  | p + 1, val, x :: xs => x :: insertIdxVal p val xs

/-- Constructive search for the first non-zero coordinate index in `r : List F`. -/
def findNonzeroIdx {F : Type} [CommRingOps F] [DecidableEq F] : List F → Option Nat
  | [] => none
  | x :: xs =>
    if x = CommRingOps.zero then
      (findNonzeroIdx xs).map (· + 1)
    else
      some 0

/-- Primitive-recursive homogeneous Gaussian pivot solver over `[LawfulField F] [DecidableEq F]`
    (`0` `WellFounded.fix`, `0` classical choice). Given `N` variables and `rows.length < N` equations
    of length `N`, returns a non-zero vector `v` of length `N` orthogonal to every row in `rows`. -/
def solveHomogeneous {F : Type} [LawfulField F] [DecidableEq F] :
    Nat → List (List F) → List F
  | 0, _ => []
  | n + 1, [] => CommRingOps.one :: List.replicate n CommRingOps.zero
  | n + 1, r :: rs =>
    match findNonzeroIdx r with
    | none =>
      CommRingOps.zero :: solveHomogeneous n (rs.map List.tail)
    | some p =>
      let rp := r.getD p CommRingOps.zero
      let invRp := LawfulField.inv rp
      let rDrop := dropIdx p r
      let rs' := rs.map (fun row =>
        let coef := CommRingOps.mul (row.getD p CommRingOps.zero) invRp
        subVec (dropIdx p row) (scaleVec coef rDrop))
      let v' := solveHomogeneous n rs'
      let vp := CommRingOps.neg (CommRingOps.mul invRp (dotVec rDrop v'))
      insertIdxVal p vp v'

private theorem dropIdx_length {α : Type} :
    ∀ (p : Nat) (xs : List α), p < xs.length → (dropIdx p xs).length + 1 = xs.length
  | _, [], h => by simp at h
  | 0, _ :: xs, _ => by simp [dropIdx]
  | p + 1, _ :: xs, h => by
    simp only [List.length_cons] at h ⊢
    have ih := dropIdx_length p xs (by omega)
    simp only [dropIdx, List.length_cons]
    omega

private theorem subVec_length {F : Type} [CommRingOps F] :
    ∀ (a b : List F), a.length = b.length → (subVec a b).length = a.length
  | [], [], _ => rfl
  | _ :: as, _ :: bs, h => congrArg Nat.succ (subVec_length as bs (Nat.succ.inj h))
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  termination_by structural a => a

private theorem insertIdxVal_length {α : Type} :
    ∀ (p : Nat) (val : α) (xs : List α), p ≤ xs.length →
      (insertIdxVal p val xs).length = xs.length + 1
  | 0, _, _, _ => rfl
  | _ + 1, _, [], h => by cases h
  | p + 1, val, _ :: xs, h =>
    congrArg Nat.succ (insertIdxVal_length p val xs (Nat.le_of_succ_le_succ h))

private theorem mem_insertIdxVal_of_mem {α : Type} :
    ∀ (p : Nat) (val : α) {z : α} {xs : List α}, z ∈ xs → z ∈ insertIdxVal p val xs
  | 0, _, _, _, hz => .tail _ hz
  | _ + 1, _, _, [], hz => by cases hz
  | p + 1, val, _, _ :: xs, hz => by
    simp only [insertIdxVal]
    cases hz with
    | head => exact .head _
    | tail _ hm => exact .tail _ (mem_insertIdxVal_of_mem p val hm)

private theorem findNonzeroIdx_none {F : Type} [CommRingOps F] [DecidableEq F] :
    ∀ {r : List F}, findNonzeroIdx r = none → ∀ x ∈ r, x = CommRingOps.zero
  | [], _, _, hx => by cases hx
  | x :: xs, h, y, hy => by
    simp only [findNonzeroIdx] at h
    if hx0 : x = CommRingOps.zero then
      simp only [hx0, ↓reduceIte, Option.map_eq_none_iff] at h
      cases hy with
      | head => exact hx0
      | tail _ hm => exact findNonzeroIdx_none h y hm
    else
      simp [hx0] at h

private theorem findNonzeroIdx_some {F : Type} [CommRingOps F] [DecidableEq F] :
    ∀ {r : List F} {p : Nat}, findNonzeroIdx r = some p →
      p < r.length ∧ r.getD p CommRingOps.zero ≠ CommRingOps.zero
  | [], _, h => by cases h
  | x :: xs, p, h => by
    simp only [findNonzeroIdx] at h
    if hx0 : x = CommRingOps.zero then
      simp only [hx0, ↓reduceIte, Option.map_eq_some_iff] at h
      rcases h with ⟨q, hq, rfl⟩
      rcases findNonzeroIdx_some hq with ⟨hqLt, hqNe⟩
      refine ⟨by simp; omega, ?_⟩
      simpa [List.getD] using hqNe
    else
      simp only [hx0, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨by simp, by simpa [List.getD] using hx0⟩

private theorem dotVec_all_zero {F : Type} [LawfulCommRing F] :
    ∀ (r v : List F), (∀ x ∈ r, x = CommRingOps.zero) → dotVec r v = CommRingOps.zero
  | [], _, _ => rfl
  | _, [], _ => by cases ‹List F› <;> rfl
  | x :: xs, y :: ys, hall => by
    simp only [dotVec, hall x (.head _), LawfulCommRing.zero_mul, LawfulCommRing.zero_add]
    exact dotVec_all_zero xs ys (fun z hz => hall z (.tail _ hz))

theorem dotVec_scaleVec {F : Type} [LawfulCommRing F] (c : F) :
    ∀ (a v : List F), dotVec (scaleVec c a) v = CommRingOps.mul c (dotVec a v)
  | [], _ => by simp [scaleVec, dotVec, LawfulCommRing.mul_zero]
  | _ :: _, [] => by simp [scaleVec, dotVec, LawfulCommRing.mul_zero]
  | a :: as, b :: bs => by
    change CommRingOps.add (CommRingOps.mul (CommRingOps.mul c a) b) (dotVec (scaleVec c as) bs) =
      CommRingOps.mul c (CommRingOps.add (CommRingOps.mul a b) (dotVec as bs))
    rw [dotVec_scaleVec c as bs, LawfulCommRing.mul_assoc, ← LawfulCommRing.left_distrib]

private theorem dotVec_subVec {F : Type} [LawfulCommRing F] :
    ∀ (a b v : List F), a.length = b.length →
      dotVec (subVec a b) v = CommRingOps.sub (dotVec a v) (dotVec b v)
  | [], [], _ => fun _ => by simp [subVec, dotVec, LawfulCommRing.sub_self]
  | _ :: _, _ :: _, [] => fun _ => by simp [subVec, dotVec, LawfulCommRing.sub_self]
  | a :: as, b :: bs, x :: xs => fun hlen => by
    simp only [subVec, dotVec, dotVec_subVec as bs xs (Nat.succ.inj hlen), LawfulCommRing.sub_mul]
    apply LawfulCommRing.add_left_cancel
      (a := CommRingOps.add (CommRingOps.mul b x) (dotVec bs xs))
    rw [LawfulCommRing.add_sub_cancel_left,
        ← LawfulCommRing.add_assoc,
        LawfulCommRing.add_assoc (CommRingOps.mul b x) (dotVec bs xs) _,
        LawfulCommRing.add_comm (dotVec bs xs) (CommRingOps.sub _ _),
        ← LawfulCommRing.add_assoc (CommRingOps.mul b x),
        LawfulCommRing.add_sub_cancel_left,
        LawfulCommRing.add_assoc,
        LawfulCommRing.add_sub_cancel_left]
  | [], _ :: _, _ => fun h => by cases h
  | _ :: _, [], _ => fun h => by cases h
  termination_by structural a => a

private theorem dotVec_insertIdxVal {F : Type} [LawfulCommRing F] :
    ∀ (p : Nat) (row v : List F) (vp : F),
      row.length = v.length + 1 →
      p < row.length →
      dotVec row (insertIdxVal p vp v) =
        CommRingOps.add (CommRingOps.mul (row.getD p CommRingOps.zero) vp)
          (dotVec (dropIdx p row) v)
  | 0, [], _, _, _, hp => by cases hp
  | 0, r0 :: rs, v, vp, _, _ => by
    simp [insertIdxVal, dropIdx, dotVec, List.getD]
  | _ + 1, [], _, _, _, hp => by cases hp
  | p + 1, _ :: tl, [], _, hlen, hp => by
    cases tl with
    | nil => exact False.elim (Nat.not_lt_zero p (Nat.lt_of_succ_lt_succ hp))
    | cons _ _ => cases hlen
  | p + 1, r0 :: rs, w0 :: ws, vp, hlen, hp => by
    have ih := dotVec_insertIdxVal p rs ws vp (Nat.succ.inj hlen) (Nat.lt_of_succ_lt_succ hp)
    simp only [insertIdxVal, dropIdx, dotVec, ih]
    have hget : (r0 :: rs).getD (p + 1) CommRingOps.zero = rs.getD p CommRingOps.zero := by
      simp [List.getD]
    rw [hget, ← LawfulCommRing.add_assoc,
        LawfulCommRing.add_comm (CommRingOps.mul r0 w0) _,
        LawfulCommRing.add_assoc]
  termination_by structural p => p

private theorem any_true_of_mem {α : Type} {pred : α → Bool} :
    ∀ {xs : List α} {z : α}, z ∈ xs → pred z = true → xs.any pred = true
  | [], _, hz, _ => by cases hz
  | x :: xs, z, hz, hp => by
    simp only [List.any_cons, Bool.or_eq_true]
    cases hz with
    | head => exact .inl hp
    | tail _ hm => exact .inr (any_true_of_mem hm hp)

theorem mem_of_any_true {α : Type} {pred : α → Bool} :
    ∀ {xs : List α}, xs.any pred = true → ∃ z ∈ xs, pred z = true
  | [], h => by simp at h
  | x :: xs, h => by
    simp only [List.any_cons, Bool.or_eq_true] at h
    rcases h with hx | hxs
    · exact ⟨x, .head _, hx⟩
    · rcases mem_of_any_true hxs with ⟨z, hz, hp⟩
      exact ⟨z, .tail _ hz, hp⟩

/-- **Constructive Homogeneous Underdetermined Linear Solver (`gauss_nullspace_witness`)**:
    Over ANY `[LawfulField F] [DecidableEq F]`, for any `N` unknowns and `rows.length < N`
    homogeneous linear equations of length `N`, `solveHomogeneous N rows` produces a vector `v`
    of length `N` that has a strictly non-zero entry (`any ≠ 0`) and annihilates every row (`0` choice). -/
theorem gauss_nullspace_witness
    {F : Type} [LawfulField F] [DecidableEq F] :
    ∀ (N : Nat) (rows : List (List F)),
      rows.length < N →
      (∀ row ∈ rows, row.length = N) →
      let v := solveHomogeneous N rows
      v.length = N ∧
      (v.any (fun x => !(decide (x = CommRingOps.zero)))) = true ∧
      ∀ row ∈ rows, dotVec row v = CommRingOps.zero
  | 0, _, hlt, _ => by cases hlt
  | n + 1, [], _, _ => by
    dsimp [solveHomogeneous]
    refine ⟨by simp, ?_, by intro _ h; cases h⟩
    simp [LawfulField.one_ne_zero]
  | n + 1, r :: rs, hlt, hlen => by
    simp only [List.length_cons] at hlt
    have hrLen : r.length = n + 1 := hlen r (.head _)
    have hrsLen : ∀ row ∈ rs, row.length = n + 1 := fun row h => hlen row (.tail _ h)
    dsimp only [solveHomogeneous]
    cases hFind : findNonzeroIdx r with
    | none =>
      dsimp only
      let rsTail := rs.map List.tail
      have hTailLt : rsTail.length < n := by
        rw [List.length_map]
        exact Nat.lt_of_succ_lt_succ hlt
      have hTailLen : ∀ row' ∈ rsTail, row'.length = n := by
        intro row' hmem
        rw [List.mem_map] at hmem
        rcases hmem with ⟨row, hrow, rfl⟩
        have hl := hrsLen row hrow
        cases row with
        | nil => cases hl
        | cons _ tl => exact Nat.succ.inj hl
      rcases gauss_nullspace_witness n rsTail hTailLt hTailLen with ⟨hvLen, hvAny, hvZero⟩
      dsimp only [rsTail] at hvLen hvAny hvZero
      refine ⟨by simp [hvLen], ?_, ?_⟩
      · simp only [List.any_cons, hvAny, Bool.or_true]
      · intro row hrow
        cases hrow with
        | head =>
          exact dotVec_all_zero r _ (findNonzeroIdx_none hFind)
        | tail _ hm =>
          have hl := hrsLen row hm
          cases row with
          | nil => cases hl
          | cons c cs =>
            simp only [dotVec, LawfulCommRing.mul_zero, LawfulCommRing.zero_add]
            exact hvZero cs (List.mem_map.mpr ⟨c :: cs, hm, rfl⟩)
    | some p =>
      dsimp only
      rcases findNonzeroIdx_some hFind with ⟨hpLt, hrpNe⟩
      let rp := r.getD p CommRingOps.zero
      let invRp := LawfulField.inv rp
      let rDrop := dropIdx p r
      have hrDropLen : rDrop.length = n := by
        dsimp only [rDrop]
        have h := dropIdx_length p r hpLt
        rw [hrLen] at h
        exact Nat.succ.inj h
      let elimRow := fun (row : List F) =>
        subVec (dropIdx p row) (scaleVec (CommRingOps.mul (row.getD p CommRingOps.zero) invRp) rDrop)
      let rs' := rs.map elimRow
      have hrs'Lt : rs'.length < n := by
        rw [List.length_map]
        exact Nat.lt_of_succ_lt_succ hlt
      have hrs'Len : ∀ row' ∈ rs', row'.length = n := by
        intro row' hmem
        rw [List.mem_map] at hmem
        rcases hmem with ⟨row, hrow, rfl⟩
        have hl := hrsLen row hrow
        have hpRow : p < row.length := by rw [hl, ← hrLen]; exact hpLt
        have hd : (dropIdx p row).length = n := by
          have h := dropIdx_length p row hpRow
          rw [hl] at h
          exact Nat.succ.inj h
        dsimp [elimRow]
        rw [subVec_length]
        · exact hd
        · simp [scaleVec, hd, hrDropLen]
      rcases gauss_nullspace_witness n rs' hrs'Lt hrs'Len with ⟨hvLen, hvAny, hvZero⟩
      let v' := solveHomogeneous n rs'
      have hv'Len : v'.length = n := hvLen
      let vp := CommRingOps.neg (CommRingOps.mul invRp (dotVec rDrop v'))
      have hpLe : p ≤ v'.length := by
        have hpSucc : p < n + 1 := by rw [← hrLen]; exact hpLt
        rw [hv'Len]
        exact Nat.le_of_lt_succ hpSucc
      refine ⟨?_, ?_, ?_⟩
      · rw [insertIdxVal_length p vp v' hpLe, hv'Len]
      · rcases mem_of_any_true hvAny with ⟨z, hzMem, hzPred⟩
        exact any_true_of_mem (mem_insertIdxVal_of_mem p vp hzMem) hzPred
      · intro row hrow
        have hrowLen : row.length = n + 1 := hlen row hrow
        have hpRow : p < row.length := by rw [hrowLen, ← hrLen]; exact hpLt
        rw [dotVec_insertIdxVal p row v' vp (by rw [hrowLen, hv'Len]) hpRow]
        cases hrow with
        | head =>
          -- Pivot row `r`: `rp * (-invRp * dot(rDrop, v')) + dot(rDrop, v') = 0`
          change CommRingOps.add (CommRingOps.mul rp vp) (dotVec rDrop v') = CommRingOps.zero
          dsimp [vp]
          rw [LawfulCommRing.mul_neg, ← LawfulCommRing.mul_assoc,
              LawfulField.mul_inv_cancel hrpNe, LawfulCommRing.one_mul,
              LawfulCommRing.add_left_neg]
        | tail _ hm =>
          -- Eliminated row `row ∈ rs`:
          have hElimZero : dotVec (elimRow row) v' = CommRingOps.zero :=
            hvZero (elimRow row) (List.mem_map.mpr ⟨row, hm, rfl⟩)
          have hdLen : (dropIdx p row).length = n := by
            have h := dropIdx_length p row hpRow
            rw [hrowLen] at h
            exact Nat.succ.inj h
          dsimp [elimRow] at hElimZero
          rw [dotVec_subVec _ _ v' (by simp [scaleVec, hdLen, hrDropLen]),
              dotVec_scaleVec] at hElimZero
          have hEqDrop : dotVec (dropIdx p row) v' =
              CommRingOps.mul (CommRingOps.mul (row.getD p CommRingOps.zero) invRp)
                (dotVec rDrop v') :=
            LawfulCommRing.sub_eq_zero_iff.mp hElimZero
          rw [hEqDrop]
          dsimp [vp]
          rw [LawfulCommRing.mul_neg, LawfulCommRing.mul_assoc,
              LawfulCommRing.add_left_neg]
  termination_by structural N => N

/-- Geometric power vector `[1, z, z^2, ..., z^(m-1)]` connecting `dotVec` directly to `evalCoeffs`. -/
def geomVec {F : Type} [CommRingOps F] (z : F) : Nat → List F
  | 0 => []
  | k + 1 => CommRingOps.one :: (geomVec z k).map (CommRingOps.mul z)

theorem geomVec_length {F : Type} [CommRingOps F] (z : F) :
    ∀ (m : Nat), (geomVec z m).length = m
  | 0 => rfl
  | k + 1 => by simp [geomVec, geomVec_length z k]

theorem dotVec_geomVec_eq_evalCoeffs {F : Type} [LawfulCommRing F] (z : F) :
    ∀ (m : Nat) (coeffs : List F),
      coeffs.length = m →
      dotVec (geomVec z m) coeffs = RoundPoly.evalCoeffs coeffs z
  | 0, [], _ => rfl
  | 0, _ :: _, h => by cases h
  | _ + 1, [], h => by cases h
  | k + 1, c :: cs, h => by
    have hcs : cs.length = k := Nat.succ.inj h
    have hscale : dotVec ((geomVec z k).map (CommRingOps.mul z)) cs =
        CommRingOps.mul z (dotVec (geomVec z k) cs) :=
      dotVec_scaleVec z (geomVec z k) cs
    simp only [geomVec, dotVec, LawfulCommRing.one_mul, hscale,
               dotVec_geomVec_eq_evalCoeffs z k cs hcs, RoundPoly.evalCoeffs]
  termination_by structural m => m

theorem dotVec_append_eq {F : Type} [LawfulCommRing F] :
    ∀ (a b x y : List F), a.length = x.length →
      dotVec (a ++ b) (x ++ y) = CommRingOps.add (dotVec a x) (dotVec b y)
  | [], b, [], y, _ => by simp [dotVec, LawfulCommRing.zero_add]
  | a0 :: as, b, x0 :: xs, y, h => by
    simp only [List.cons_append, dotVec, dotVec_append_eq as b xs y (Nat.succ.inj h),
               LawfulCommRing.add_assoc]
  | [], _, _ :: _, _, h => by cases h
  | _ :: _, _, [], _, h => by cases h
  termination_by structural a => a

theorem dotVec_replicate_zero {F : Type} [LawfulCommRing F] :
    ∀ (m : Nat) (v : List F), dotVec (List.replicate m CommRingOps.zero) v = CommRingOps.zero
  | 0, _ => rfl
  | m + 1, [] => rfl
  | m + 1, _ :: vs => by
    simp [List.replicate, dotVec, LawfulCommRing.zero_mul, LawfulCommRing.zero_add,
          dotVec_replicate_zero m vs]


/-! ## §4. Constructive Euclidean Polynomials & Welch–Berlekamp Affine Proximity Gap (`Tier 1B`) -/

/-- Coefficient of `X^k` in `p : List F` (`0` past `p.length`). -/
@[expose] def coeffAt {F : Type} [CommRingOps F] (p : List F) (k : Nat) : F :=
  p.getD k CommRingOps.zero

/-- Strip trailing zeros so every non-empty canonical polynomial has a non-zero leading coefficient. -/
@[expose] def trimPoly {F : Type} [CommRingOps F] [DecidableEq F] : List F → List F
  | [] => []
  | c :: cs =>
    let cs' := trimPoly cs
    if cs' = [] ∧ c = CommRingOps.zero then [] else c :: cs'

/-- Canonical trimmedness predicate. -/
@[expose] def IsTrimmed {F : Type} [CommRingOps F] [DecidableEq F] (p : List F) : Prop :=
  trimPoly p = p

theorem coeffAt_nil {F : Type} [CommRingOps F] (k : Nat) :
    coeffAt ([] : List F) k = CommRingOps.zero := by
  simp [coeffAt]

theorem coeffAt_cons_zero {F : Type} [CommRingOps F] (c : F) (cs : List F) :
    coeffAt (c :: cs) 0 = c := by
  simp [coeffAt]

theorem coeffAt_cons_succ {F : Type} [CommRingOps F] (c : F) (cs : List F) (k : Nat) :
    coeffAt (c :: cs) (k + 1) = coeffAt cs k := by
  simp [coeffAt]

theorem coeffAt_eq_zero_of_ge {F : Type} [CommRingOps F] :
    ∀ (p : List F) (k : Nat), p.length ≤ k → coeffAt p k = CommRingOps.zero
  | [], _, _ => rfl
  | _ :: _, 0, h => by simp at h
  | _ :: cs, k + 1, h => by
    simp only [List.length_cons] at h
    rw [coeffAt_cons_succ]
    exact coeffAt_eq_zero_of_ge cs k (by omega)

theorem trimPoly_length_le {F : Type} [CommRingOps F] [DecidableEq F] :
    ∀ (p : List F), (trimPoly p).length ≤ p.length
  | [] => Nat.le_refl 0
  | c :: cs => by
    simp only [trimPoly]
    split
    · simp
    · simp only [List.length_cons]
      exact Nat.succ_le_succ (trimPoly_length_le cs)

theorem evalCoeffs_trimPoly {F : Type} [LawfulCommRing F] [DecidableEq F] (x : F) :
    ∀ (p : List F), RoundPoly.evalCoeffs (trimPoly p) x = RoundPoly.evalCoeffs p x
  | [] => rfl
  | c :: cs => by
    simp only [trimPoly]
    split
    · next h =>
      rcases h with ⟨hcs, hc⟩
      have ih := evalCoeffs_trimPoly x cs
      rw [hcs, RoundPoly.evalCoeffs_nil] at ih
      simp [RoundPoly.evalCoeffs, hc, ← ih, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    · simp [RoundPoly.evalCoeffs, evalCoeffs_trimPoly x cs]

theorem coeffAt_trimPoly {F : Type} [CommRingOps F] [DecidableEq F] :
    ∀ (p : List F) (k : Nat), coeffAt (trimPoly p) k = coeffAt p k
  | [], _ => rfl
  | c :: cs, k => by
    simp only [trimPoly]
    split
    · next h =>
      rcases h with ⟨hcs, hc⟩
      cases k with
      | zero => simp [coeffAt, hc]
      | succ k' =>
        have ih := coeffAt_trimPoly cs k'
        rw [hcs, coeffAt_nil] at ih
        rw [coeffAt_nil, coeffAt_cons_succ, ← ih]
    · cases k with
      | zero => rfl
      | succ k' => exact coeffAt_trimPoly cs k'

theorem trimPoly_idem {F : Type} [CommRingOps F] [DecidableEq F] :
    ∀ (p : List F), trimPoly (trimPoly p) = trimPoly p
  | [] => rfl
  | c :: cs => by
    simp only [trimPoly]
    split
    · rfl
    · next h =>
      simp only [trimPoly, trimPoly_idem cs, h, ↓reduceIte]

theorem leadCoeff_ne_zero_of_trimPoly_ne_nil {F : Type} [CommRingOps F] [DecidableEq F] :
    ∀ (p : List F), trimPoly p ≠ [] →
      coeffAt (trimPoly p) ((trimPoly p).length - 1) ≠ CommRingOps.zero
  | [], h => False.elim (h rfl)
  | c :: cs, h => by
    simp only [trimPoly] at h ⊢
    if hcond : trimPoly cs = [] ∧ c = CommRingOps.zero then
      simp [hcond] at h
    else
      simp only [hcond, ↓reduceIte]
      if hcs : trimPoly cs = [] then
        have hc : c ≠ CommRingOps.zero := fun hc0 => hcond ⟨hcs, hc0⟩
        simpa [hcs, coeffAt] using hc
      else
        have ih := leadCoeff_ne_zero_of_trimPoly_ne_nil cs hcs
        cases hq : trimPoly cs with
        | nil => exact False.elim (hcs hq)
        | cons d ds =>
          rw [hq] at ih
          simpa [coeffAt] using ih

theorem eq_of_isTrimmed_coeffAt {F : Type} [CommRingOps F] [DecidableEq F] :
    ∀ (a b : List F), IsTrimmed a → IsTrimmed b →
      (∀ k : Nat, coeffAt a k = coeffAt b k) → a = b
  | [], [], _, _, _ => rfl
  | [], y :: ys, _, hb, hcoeff => by
    have hne : trimPoly (y :: ys) ≠ [] := by rw [hb]; simp
    have hlead := leadCoeff_ne_zero_of_trimPoly_ne_nil (y :: ys) hne
    rw [hb, ← hcoeff ((y :: ys).length - 1), coeffAt_nil] at hlead
    exact False.elim (hlead rfl)
  | x :: xs, [], ha, _, hcoeff => by
    have hne : trimPoly (x :: xs) ≠ [] := by rw [ha]; simp
    have hlead := leadCoeff_ne_zero_of_trimPoly_ne_nil (x :: xs) hne
    rw [ha, hcoeff ((x :: xs).length - 1), coeffAt_nil] at hlead
    exact False.elim (hlead rfl)
  | x :: xs, y :: ys, ha, hb, hcoeff => by
    have hxy : x = y := by simpa [coeffAt] using hcoeff 0
    subst hxy
    have hxs : IsTrimmed xs := by
      unfold IsTrimmed at ha ⊢
      simp only [trimPoly] at ha
      split at ha
      · cases ha
      · injection ha with _ htl
    have hys : IsTrimmed ys := by
      unfold IsTrimmed at hb ⊢
      simp only [trimPoly] at hb
      split at hb
      · cases hb
      · injection hb with _ htl
    have htl := eq_of_isTrimmed_coeffAt xs ys hxs hys (fun k => by
      simpa [coeffAt_cons_succ] using hcoeff (k + 1))
    rw [htl]

/-- Canonical polynomial equality criterion: `trimPoly p = trimPoly q` iff all coefficients match. -/
theorem trimPoly_eq_iff_coeffAt {F : Type} [CommRingOps F] [DecidableEq F] (p q : List F) :
    trimPoly p = trimPoly q ↔ ∀ k : Nat, coeffAt p k = coeffAt q k := by
  constructor
  · intro heq k
    rw [← coeffAt_trimPoly p k, ← coeffAt_trimPoly q k, heq]
  · intro h
    apply eq_of_isTrimmed_coeffAt (trimPoly p) (trimPoly q) (trimPoly_idem p) (trimPoly_idem q)
    intro k
    rw [coeffAt_trimPoly, coeffAt_trimPoly, h k]

theorem trimPoly_eq_nil_iff {F : Type} [CommRingOps F] [DecidableEq F] (p : List F) :
    trimPoly p = [] ↔ ∀ k : Nat, coeffAt p k = CommRingOps.zero := by
  simpa [trimPoly, coeffAt_nil] using trimPoly_eq_iff_coeffAt p []

theorem length_trimPoly_le_of_coeffAt_zero {F : Type} [CommRingOps F] [DecidableEq F]
    (p : List F) (B : Nat) (h : ∀ k : Nat, B ≤ k → coeffAt p k = CommRingOps.zero) :
    (trimPoly p).length ≤ B := by
  if hnil : trimPoly p = [] then
    rw [hnil]; exact Nat.zero_le B
  else
    have hlead := leadCoeff_ne_zero_of_trimPoly_ne_nil p hnil
    rw [coeffAt_trimPoly] at hlead
    if hle : (trimPoly p).length ≤ B then
      exact hle
    else
      exact False.elim (hlead (h ((trimPoly p).length - 1) (by omega)))

/-- Constructive non-root existence for ANY non-empty trimmed polynomial on a `Nodup` domain `U`
    with `p.length ≤ U.length` (`0` classical axioms). -/
theorem exists_nonroot_of_trim_ne_nil
    {F : Type} [LawfulField F] [DecidableEq F]
    {p U : List F}
    (hpTrim : IsTrimmed p)
    (hpNe : p ≠ [])
    (hU : U.Nodup)
    (hLen : p.length ≤ U.length) :
    ∃ x₀ ∈ U, RoundPoly.evalCoeffs p x₀ ≠ CommRingOps.zero := by
  let k := p.length - 1
  have hk : p.length = k + 1 := by
    cases p with
    | nil => exact False.elim (hpNe rfl)
    | cons _ _ => simp [k]
  have hlcNe : coeffAt p k ≠ CommRingOps.zero := by
    have h := leadCoeff_ne_zero_of_trimPoly_ne_nil p (by rwa [hpTrim])
    rw [hpTrim] at h
    exact h
  let pMonic := p.map (CommRingOps.mul (LawfulField.inv (coeffAt p k)))
  have hMonicLen : pMonic.length = k + 1 := by simp [pMonic, hk]
  have hMonicLast : pMonic.getD k CommRingOps.zero = CommRingOps.one := by
    have hkLt : k < p.length := by omega
    have hget : pMonic.getD k CommRingOps.zero =
        CommRingOps.mul (LawfulField.inv (coeffAt p k)) (coeffAt p k) := by
      simp [pMonic, coeffAt, List.getD, hkLt]
    rw [hget, LawfulField.inv_mul_cancel hlcNe]
  rcases exists_nonroot_of_monic_len k pMonic U hMonicLen hMonicLast hU (by omega) with
    ⟨x₀, hx₀Mem, hx₀Ne⟩
  refine ⟨x₀, hx₀Mem, ?_⟩
  intro hev0
  apply hx₀Ne
  rw [evalCoeffs_map_mul, hev0, LawfulCommRing.mul_zero]

/-- Componentwise polynomial addition & negation on raw `List F` coefficient vectors. -/
@[expose] def rawAddCoeffs {F : Type} [CommRingOps F] : List F → List F → List F
  | [], b => b
  | a, [] => a
  | c :: cs, d :: ds => CommRingOps.add c d :: rawAddCoeffs cs ds

def rawNegCoeffs {F : Type} [CommRingOps F] (a : List F) : List F :=
  a.map CommRingOps.neg

theorem evalCoeffs_rawAdd {F : Type} [LawfulCommRing F] :
    ∀ (a b : List F) (x : F),
      RoundPoly.evalCoeffs (rawAddCoeffs a b) x =
        CommRingOps.add (RoundPoly.evalCoeffs a x) (RoundPoly.evalCoeffs b x)
  | [], b, x => by simp [rawAddCoeffs, RoundPoly.evalCoeffs, LawfulCommRing.zero_add]
  | a, [], x => by cases a <;> simp [rawAddCoeffs, RoundPoly.evalCoeffs, LawfulCommRing.add_zero]
  | c :: cs, d :: ds, x => by
    simp only [rawAddCoeffs, RoundPoly.evalCoeffs, evalCoeffs_rawAdd cs ds x]
    rw [LawfulCommRing.left_distrib, LawfulCommRing.add_add_add_comm]

/-- Canonical trimmed univariate polynomial operations. -/
def pAdd {F : Type} [CommRingOps F] [DecidableEq F] (a b : List F) : List F :=
  trimPoly (rawAddCoeffs a b)

def pSub {F : Type} [CommRingOps F] [DecidableEq F] (a b : List F) : List F :=
  trimPoly (RoundPoly.subCoeffs a b)

def pNeg {F : Type} [CommRingOps F] [DecidableEq F] (a : List F) : List F :=
  trimPoly (rawNegCoeffs a)

def pScale {F : Type} [CommRingOps F] [DecidableEq F] (c : F) (a : List F) : List F :=
  trimPoly (a.map (CommRingOps.mul c))

@[expose] def rawMul {F : Type} [CommRingOps F] : List F → List F → List F
  | [], _ => []
  | c :: cs, b => rawAddCoeffs (b.map (CommRingOps.mul c)) (CommRingOps.zero :: rawMul cs b)

@[expose] def pMul {F : Type} [CommRingOps F] [DecidableEq F] (a b : List F) : List F :=
  trimPoly (rawMul a b)

def monomial {F : Type} [CommRingOps F] (deg : Nat) (c : F) : List F :=
  List.replicate deg CommRingOps.zero ++ [c]

theorem coeffAt_addCoeffs {F : Type} [LawfulCommRing F] :
    ∀ (a b : List F) (k : Nat),
      coeffAt (rawAddCoeffs a b) k = CommRingOps.add (coeffAt a k) (coeffAt b k)
  | [], b, k => by simp [rawAddCoeffs, coeffAt_nil, LawfulCommRing.zero_add]
  | a, [], k => by
    cases a <;> simp [rawAddCoeffs, coeffAt_nil, LawfulCommRing.add_zero]
  | _ :: _, _ :: _, 0 => by simp [rawAddCoeffs, coeffAt]
  | _ :: as, _ :: bs, k + 1 => by
    simp only [rawAddCoeffs, coeffAt_cons_succ, coeffAt_addCoeffs as bs k]

private theorem coeffAt_negCoeffs {F : Type} [LawfulCommRing F] :
    ∀ (a : List F) (k : Nat),
      coeffAt (rawNegCoeffs a) k = CommRingOps.neg (coeffAt a k)
  | [], _ => by simp [rawNegCoeffs, coeffAt_nil, LawfulCommRing.neg_zero]
  | _ :: _, 0 => by simp [rawNegCoeffs, coeffAt]
  | c :: as, k + 1 => by
    change coeffAt (CommRingOps.neg c :: rawNegCoeffs as) (k + 1) =
      CommRingOps.neg (coeffAt (c :: as) (k + 1))
    rw [coeffAt_cons_succ, coeffAt_cons_succ, coeffAt_negCoeffs as k]

private theorem coeffAt_subCoeffs {F : Type} [LawfulCommRing F] :
    ∀ (a b : List F) (k : Nat),
      coeffAt (RoundPoly.subCoeffs a b) k = CommRingOps.sub (coeffAt a k) (coeffAt b k)
  | [], [], k => by simp [RoundPoly.subCoeffs, coeffAt_nil, LawfulCommRing.sub_self]
  | c :: cs, [], 0 => by simp [RoundPoly.subCoeffs, coeffAt, LawfulCommRing.sub_zero]
  | c :: cs, [], k + 1 => by
    simp only [RoundPoly.subCoeffs, coeffAt_cons_succ, coeffAt_subCoeffs cs [] k, coeffAt_nil]
  | [], d :: ds, 0 => by
    simp [RoundPoly.subCoeffs, coeffAt, LawfulCommRing.sub_eq_add_neg, LawfulCommRing.zero_add]
  | [], d :: ds, k + 1 => by
    simp only [RoundPoly.subCoeffs, coeffAt_cons_succ, coeffAt_subCoeffs [] ds k, coeffAt_nil]
  | _ :: _, _ :: _, 0 => by simp [RoundPoly.subCoeffs, coeffAt]
  | _ :: as, _ :: bs, k + 1 => by
    simp only [RoundPoly.subCoeffs, coeffAt_cons_succ, coeffAt_subCoeffs as bs k]

theorem coeffAt_map_mul {F : Type} [LawfulCommRing F] (c : F) :
    ∀ (a : List F) (k : Nat),
      coeffAt (a.map (CommRingOps.mul c)) k = CommRingOps.mul c (coeffAt a k)
  | [], _ => by simp [coeffAt_nil, LawfulCommRing.mul_zero]
  | _ :: _, 0 => by simp [coeffAt]
  | _ :: as, k + 1 => by simp [coeffAt_cons_succ, coeffAt_map_mul c as k]

theorem coeffAt_pAdd {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) (k : Nat) :
    coeffAt (pAdd a b) k = CommRingOps.add (coeffAt a k) (coeffAt b k) := by
  rw [pAdd, coeffAt_trimPoly, coeffAt_addCoeffs]

theorem coeffAt_pSub {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) (k : Nat) :
    coeffAt (pSub a b) k = CommRingOps.sub (coeffAt a k) (coeffAt b k) := by
  rw [pSub, coeffAt_trimPoly, coeffAt_subCoeffs]

theorem coeffAt_pNeg {F : Type} [LawfulCommRing F] [DecidableEq F] (a : List F) (k : Nat) :
    coeffAt (pNeg a) k = CommRingOps.neg (coeffAt a k) := by
  rw [pNeg, coeffAt_trimPoly, coeffAt_negCoeffs]

theorem coeffAt_pScale {F : Type} [LawfulCommRing F] [DecidableEq F] (c : F) (a : List F) (k : Nat) :
    coeffAt (pScale c a) k = CommRingOps.mul c (coeffAt a k) := by
  rw [pScale, coeffAt_trimPoly, coeffAt_map_mul]

theorem evalCoeffs_rawMul {F : Type} [LawfulCommRing F] (x : F) :
    ∀ (a b : List F), RoundPoly.evalCoeffs (rawMul a b) x =
      CommRingOps.mul (RoundPoly.evalCoeffs a x) (RoundPoly.evalCoeffs b x)
  | [], _ => by simp [rawMul, RoundPoly.evalCoeffs, LawfulCommRing.zero_mul]
  | c :: cs, b => by
    simp only [rawMul, evalCoeffs_rawAdd, evalCoeffs_map_mul, RoundPoly.evalCoeffs_cons,
               LawfulCommRing.zero_add, evalCoeffs_rawMul x cs b]
    rw [LawfulCommRing.right_distrib, LawfulCommRing.mul_assoc]

theorem evalCoeffs_pAdd {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) (x : F) :
    RoundPoly.evalCoeffs (pAdd a b) x =
      CommRingOps.add (RoundPoly.evalCoeffs a x) (RoundPoly.evalCoeffs b x) := by
  rw [pAdd, evalCoeffs_trimPoly, evalCoeffs_rawAdd]

theorem evalCoeffs_pSub {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) (x : F) :
    RoundPoly.evalCoeffs (pSub a b) x =
      CommRingOps.sub (RoundPoly.evalCoeffs a x) (RoundPoly.evalCoeffs b x) := by
  rw [pSub, evalCoeffs_trimPoly, RoundPoly.evalCoeffs_sub]

theorem evalCoeffs_pScale {F : Type} [LawfulCommRing F] [DecidableEq F] (c : F) (a : List F) (x : F) :
    RoundPoly.evalCoeffs (pScale c a) x = CommRingOps.mul c (RoundPoly.evalCoeffs a x) := by
  rw [pScale, evalCoeffs_trimPoly, evalCoeffs_map_mul]

theorem evalCoeffs_pMul {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) (x : F) :
    RoundPoly.evalCoeffs (pMul a b) x =
      CommRingOps.mul (RoundPoly.evalCoeffs a x) (RoundPoly.evalCoeffs b x) := by
  rw [pMul, evalCoeffs_trimPoly, evalCoeffs_rawMul]

private theorem coeffAt_rawMul_zero_left {F : Type} [LawfulCommRing F] (b : List F) :
    ∀ (a : List F), (∀ i, coeffAt a i = CommRingOps.zero) →
      ∀ k, coeffAt (rawMul a b) k = CommRingOps.zero
  | [], _, k => by simp [rawMul, coeffAt_nil]
  | c :: cs, ha, k => by
    have hc : c = CommRingOps.zero := ha 0
    have hcs : ∀ i, coeffAt cs i = CommRingOps.zero := fun i => ha (i + 1)
    simp only [rawMul, coeffAt_addCoeffs, coeffAt_map_mul, hc, LawfulCommRing.zero_mul,
               LawfulCommRing.zero_add]
    cases k with
    | zero => rfl
    | succ k' => exact coeffAt_rawMul_zero_left b cs hcs k'

private theorem coeffAt_rawMul_zero_right {F : Type} [LawfulCommRing F] :
    ∀ (a b : List F), (∀ j, coeffAt b j = CommRingOps.zero) →
      ∀ k, coeffAt (rawMul a b) k = CommRingOps.zero
  | [], _, _, k => by simp [rawMul, coeffAt_nil]
  | c :: cs, b, hb, k => by
    simp only [rawMul, coeffAt_addCoeffs, coeffAt_map_mul, hb k, LawfulCommRing.mul_zero,
               LawfulCommRing.zero_add]
    cases k with
    | zero => rfl
    | succ k' => exact coeffAt_rawMul_zero_right cs b hb k'

private theorem coeffAt_rawMul_high {F : Type} [LawfulCommRing F] (b : List F) (db : Nat)
    (hb : ∀ j, db < j → coeffAt b j = CommRingOps.zero) :
    ∀ (da : Nat) (a : List F),
      (∀ i, da < i → coeffAt a i = CommRingOps.zero) →
      (∀ k, da + db < k → coeffAt (rawMul a b) k = CommRingOps.zero) ∧
      coeffAt (rawMul a b) (da + db) = CommRingOps.mul (coeffAt a da) (coeffAt b db)
  | 0, [], _ => by
    refine ⟨fun k _ => by simp [rawMul, coeffAt_nil], ?_⟩
    simp [rawMul, coeffAt_nil, LawfulCommRing.zero_mul]
  | 0, a0 :: as, ha => by
    have has0 : ∀ i, coeffAt as i = CommRingOps.zero := fun i => by
      simpa [coeffAt_cons_succ] using ha (i + 1) (Nat.zero_lt_succ i)
    have htail : ∀ k, coeffAt (CommRingOps.zero :: rawMul as b) k = CommRingOps.zero := by
      intro k
      cases k with
      | zero => rfl
      | succ k' => exact coeffAt_rawMul_zero_left b as has0 k'
    refine ⟨fun k hk => ?_, ?_⟩
    · simp only [rawMul, coeffAt_addCoeffs, coeffAt_map_mul, htail k, LawfulCommRing.add_zero]
      rw [hb k (by simpa [Nat.zero_add] using hk), LawfulCommRing.mul_zero]
    · simp only [Nat.zero_add, rawMul, coeffAt_addCoeffs, coeffAt_map_mul, htail db,
                 LawfulCommRing.add_zero, coeffAt_cons_zero]
  | da + 1, [], _ => by
    refine ⟨fun k _ => by simp [rawMul, coeffAt_nil], ?_⟩
    simp [rawMul, coeffAt_nil, LawfulCommRing.zero_mul]
  | da + 1, a0 :: as, ha => by
    have has : ∀ i, da < i → coeffAt as i = CommRingOps.zero := fun i hi => by
      simpa [coeffAt_cons_succ] using ha (i + 1) (Nat.succ_lt_succ hi)
    rcases coeffAt_rawMul_high b db hb da as has with ⟨ihHigh, ihTop⟩
    refine ⟨fun k hk => ?_, ?_⟩
    · cases k with
      | zero => cases hk
      | succ k' =>
        simp only [rawMul, coeffAt_addCoeffs, coeffAt_map_mul, coeffAt_cons_succ]
        have hk1 : db < k' + 1 := Nat.lt_of_le_of_lt (Nat.le_add_left db (da + 1)) hk
        have hk2 : da + db < k' := Nat.lt_of_succ_lt_succ (by rwa [Nat.succ_add] at hk)
        rw [hb (k' + 1) hk1, ihHigh k' hk2,
            LawfulCommRing.mul_zero, LawfulCommRing.zero_add]
    · have hidx : da + 1 + db = (da + db) + 1 := Nat.succ_add da db
      rw [hidx]
      simp only [rawMul, coeffAt_addCoeffs, coeffAt_map_mul, coeffAt_cons_succ]
      have htopLt : db < (da + db) + 1 := Nat.lt_succ_of_le (Nat.le_add_left db da)
      rw [hb ((da + db) + 1) htopLt, LawfulCommRing.mul_zero, LawfulCommRing.zero_add, ihTop]
  termination_by structural da => da

private theorem coeffAt_rawMul_add_left {F : Type} [LawfulCommRing F] (b : List F) :
    ∀ (a1 a2 : List F) (k : Nat),
      coeffAt (rawMul (rawAddCoeffs a1 a2) b) k =
        CommRingOps.add (coeffAt (rawMul a1 b) k) (coeffAt (rawMul a2 b) k)
  | [], a2, k => by simp [rawAddCoeffs, rawMul, coeffAt_nil, LawfulCommRing.zero_add]
  | a1, [], k => by
    cases a1 <;> simp [rawAddCoeffs, rawMul, coeffAt_nil, LawfulCommRing.add_zero]
  | x :: xs, y :: ys, k => by
    simp only [rawAddCoeffs, rawMul, coeffAt_addCoeffs, coeffAt_map_mul,
               LawfulCommRing.right_distrib]
    cases k with
    | zero =>
      simp [coeffAt, LawfulCommRing.add_zero]
    | succ k' =>
      simp only [coeffAt_cons_succ, coeffAt_rawMul_add_left b xs ys k']
      rw [← LawfulCommRing.add_assoc,
          LawfulCommRing.add_assoc (CommRingOps.mul x _) (CommRingOps.mul y _) _,
          LawfulCommRing.add_comm (CommRingOps.mul y _) (coeffAt (rawMul xs b) k'),
          ← LawfulCommRing.add_assoc,
          LawfulCommRing.add_assoc]

private theorem coeffAt_rawMul_add_right {F : Type} [LawfulCommRing F] :
    ∀ (a b1 b2 : List F) (k : Nat),
      coeffAt (rawMul a (rawAddCoeffs b1 b2)) k =
        CommRingOps.add (coeffAt (rawMul a b1) k) (coeffAt (rawMul a b2) k)
  | [], _, _, _ => by simp [rawMul, coeffAt_nil, LawfulCommRing.zero_add]
  | c :: cs, b1, b2, k => by
    simp only [rawMul, coeffAt_addCoeffs, coeffAt_map_mul, LawfulCommRing.left_distrib]
    cases k with
    | zero => simp [coeffAt, LawfulCommRing.add_zero]
    | succ k' =>
      simp only [coeffAt_cons_succ, coeffAt_rawMul_add_right cs b1 b2 k']
      rw [← LawfulCommRing.add_assoc,
          LawfulCommRing.add_assoc (CommRingOps.mul c _) (CommRingOps.mul c _) _,
          LawfulCommRing.add_comm (CommRingOps.mul c (coeffAt b2 (k' + 1))) _,
          ← LawfulCommRing.add_assoc,
          LawfulCommRing.add_assoc]

private theorem coeffAt_rawMul_shift_right {F : Type} [LawfulCommRing F] :
    ∀ (a b : List F) (k : Nat),
      coeffAt (rawMul a (CommRingOps.zero :: b)) k =
        coeffAt (CommRingOps.zero :: rawMul a b) k
  | [], _, k => by cases k <;> simp [rawMul, coeffAt]
  | c :: cs, b, 0 => by
    simp only [rawMul, coeffAt_addCoeffs, coeffAt_map_mul, coeffAt_cons_zero,
               LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | c :: cs, b, k + 1 => by
    simp [rawMul, coeffAt_addCoeffs, coeffAt_map_mul, coeffAt_cons_succ,
          coeffAt_rawMul_shift_right cs b k]

private theorem coeffAt_rawMul_scale_left {F : Type} [LawfulCommRing F] (s : F) (b : List F) :
    ∀ (a : List F) (k : Nat),
      coeffAt (rawMul (a.map (CommRingOps.mul s)) b) k =
        CommRingOps.mul s (coeffAt (rawMul a b) k)
  | [], _ => by simp [rawMul, coeffAt_nil, LawfulCommRing.mul_zero]
  | c :: cs, 0 => by
    simp only [List.map, rawMul, coeffAt_addCoeffs, coeffAt_map_mul, coeffAt_cons_zero,
               LawfulCommRing.add_zero, LawfulCommRing.mul_assoc]
  | c :: cs, k + 1 => by
    simp [rawMul, coeffAt_addCoeffs, coeffAt_map_mul, coeffAt_cons_succ,
          coeffAt_rawMul_scale_left s b cs k,
          LawfulCommRing.left_distrib, LawfulCommRing.mul_assoc]

private theorem coeffAt_rawMul_scale_right {F : Type} [LawfulCommRing F] (s : F) :
    ∀ (a b : List F) (k : Nat),
      coeffAt (rawMul a (b.map (CommRingOps.mul s))) k =
        CommRingOps.mul s (coeffAt (rawMul a b) k)
  | [], _, _ => by simp [rawMul, coeffAt_nil, LawfulCommRing.mul_zero]
  | c :: cs, b, k => by
    simp only [rawMul, coeffAt_addCoeffs, coeffAt_map_mul]
    have hcomm : CommRingOps.mul c (CommRingOps.mul s (coeffAt b k)) =
        CommRingOps.mul s (CommRingOps.mul c (coeffAt b k)) := by
      rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm c s, LawfulCommRing.mul_assoc]
    rw [hcomm]
    cases k with
    | zero => simp only [coeffAt_cons_zero, LawfulCommRing.add_zero]
    | succ k' =>
      simp [coeffAt_cons_succ, coeffAt_rawMul_scale_right s cs b k', LawfulCommRing.left_distrib]

private theorem coeffAt_rawMul_congr {F : Type} [LawfulCommRing F] :
    ∀ (a1 a2 b1 b2 : List F),
      (∀ i, coeffAt a1 i = coeffAt a2 i) →
      (∀ j, coeffAt b1 j = coeffAt b2 j) →
      ∀ k, coeffAt (rawMul a1 b1) k = coeffAt (rawMul a2 b2) k
  | [], [], _, _, _, _, _ => rfl
  | [], c :: cs, b1, b2, ha, _, k => by
    have h0 : ∀ i, coeffAt (c :: cs) i = CommRingOps.zero := fun i => by
      simpa [coeffAt_nil] using (ha i).symm
    rw [show rawMul ([] : List F) b1 = [] from rfl, coeffAt_nil,
        coeffAt_rawMul_zero_left b2 (c :: cs) h0 k]
  | c :: cs, [], b1, b2, ha, _, k => by
    have h0 : ∀ i, coeffAt (c :: cs) i = CommRingOps.zero := fun i => by
      simpa [coeffAt_nil] using ha i
    rw [show rawMul ([] : List F) b2 = [] from rfl, coeffAt_nil,
        coeffAt_rawMul_zero_left b1 (c :: cs) h0 k]
  | x :: xs, y :: ys, b1, b2, ha, hb, k => by
    have hxy : x = y := by simpa [coeffAt] using ha 0
    subst hxy
    simp only [rawMul, coeffAt_addCoeffs, coeffAt_map_mul, hb k]
    cases k with
    | zero => rfl
    | succ k' =>
      simp only [coeffAt_cons_succ]
      rw [coeffAt_rawMul_congr xs ys b1 b2
        (fun i => by simpa [coeffAt_cons_succ] using ha (i + 1)) hb k']

theorem pMul_trimPoly_left {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) :
    pMul (trimPoly a) b = pMul a b := by
  unfold pMul
  rw [trimPoly_eq_iff_coeffAt]
  exact coeffAt_rawMul_congr (trimPoly a) a b b (coeffAt_trimPoly a) (fun _ => rfl)

theorem pMul_trimPoly_right {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) :
    pMul a (trimPoly b) = pMul a b := by
  unfold pMul
  rw [trimPoly_eq_iff_coeffAt]
  exact coeffAt_rawMul_congr a a (trimPoly b) b (fun _ => rfl) (coeffAt_trimPoly b)

theorem pAdd_comm {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) :
    pAdd a b = pAdd b a := by
  unfold pAdd; rw [trimPoly_eq_iff_coeffAt]; intro k
  simp [coeffAt_addCoeffs, LawfulCommRing.add_comm]

theorem pAdd_assoc {F : Type} [LawfulCommRing F] [DecidableEq F] (a b c : List F) :
    pAdd (pAdd a b) c = pAdd a (pAdd b c) := by
  unfold pAdd; rw [trimPoly_eq_iff_coeffAt]; intro k
  simp [coeffAt_addCoeffs, coeffAt_trimPoly, LawfulCommRing.add_assoc]

theorem pAdd_nil_right {F : Type} [LawfulCommRing F] [DecidableEq F] (a : List F) :
    pAdd a [] = trimPoly a := by
  unfold pAdd; rw [trimPoly_eq_iff_coeffAt]; intro k
  simp [coeffAt_addCoeffs, coeffAt_nil, LawfulCommRing.add_zero]

theorem pAdd_nil_left {F : Type} [LawfulCommRing F] [DecidableEq F] (a : List F) :
    pAdd [] a = trimPoly a := by
  rw [pAdd_comm, pAdd_nil_right]

theorem pAdd_trimPoly_left {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) :
    pAdd (trimPoly a) b = pAdd a b := by
  unfold pAdd; rw [trimPoly_eq_iff_coeffAt]; intro k
  simp [coeffAt_addCoeffs, coeffAt_trimPoly]

theorem pAdd_trimPoly_right {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) :
    pAdd a (trimPoly b) = pAdd a b := by
  unfold pAdd; rw [trimPoly_eq_iff_coeffAt]; intro k
  simp [coeffAt_addCoeffs, coeffAt_trimPoly]

theorem pSub_eq_pAdd_pNeg {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) :
    pSub a b = pAdd a (pNeg b) := by
  unfold pSub pAdd pNeg; rw [trimPoly_eq_iff_coeffAt]; intro k
  simp [coeffAt_subCoeffs, coeffAt_addCoeffs, coeffAt_trimPoly, coeffAt_negCoeffs,
        LawfulCommRing.sub_eq_add_neg]

theorem pAdd_pSub_cancel {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) :
    pAdd b (pSub a b) = trimPoly a := by
  unfold pAdd pSub; rw [trimPoly_eq_iff_coeffAt]; intro k
  simp [coeffAt_addCoeffs, coeffAt_trimPoly, coeffAt_subCoeffs, LawfulCommRing.add_sub_cancel_left]

theorem pSub_pAdd_cancel_left {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) :
    pSub (pAdd a b) a = trimPoly b := by
  unfold pSub pAdd; rw [trimPoly_eq_iff_coeffAt]; intro k
  rw [coeffAt_subCoeffs, coeffAt_trimPoly, coeffAt_addCoeffs,
      LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_comm (coeffAt a k),
      LawfulCommRing.add_assoc, LawfulCommRing.add_right_neg, LawfulCommRing.add_zero]

theorem pMul_comm {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) :
    pMul a b = pMul b a := by
  unfold pMul
  rw [trimPoly_eq_iff_coeffAt]
  induction a with
  | nil =>
    intro k
    have h0 : ∀ j, coeffAt ([] : List F) j = CommRingOps.zero := coeffAt_nil
    simp [rawMul, coeffAt_nil, coeffAt_rawMul_zero_right b [] h0 k]
  | cons c cs ih =>
    intro k
    have h1 : ∀ j, coeffAt (rawMul b [c]) j = CommRingOps.mul c (coeffAt b j) := by
      clear ih k cs
      induction b with
      | nil => intro j; simp [rawMul, coeffAt_nil, LawfulCommRing.mul_zero]
      | cons d ds ihb =>
        intro j
        cases j with
        | zero =>
          simp only [rawMul, coeffAt_addCoeffs, coeffAt_map_mul, coeffAt_cons_zero,
                     LawfulCommRing.add_zero, LawfulCommRing.mul_comm]
        | succ j' =>
          simp only [rawMul, coeffAt_addCoeffs, List.map, coeffAt_cons_succ, coeffAt_nil,
                     LawfulCommRing.zero_add, ihb j']
    have hsplit : ∀ i, coeffAt (c :: cs) i =
        coeffAt (rawAddCoeffs [c] (CommRingOps.zero :: cs)) i := by
      intro i
      cases i with
      | zero => simp [rawAddCoeffs, coeffAt, LawfulCommRing.add_zero]
      | succ _ => simp [rawAddCoeffs, coeffAt]
    rw [coeffAt_rawMul_congr b b (c :: cs) (rawAddCoeffs [c] (CommRingOps.zero :: cs))
          (fun _ => rfl) hsplit k,
        coeffAt_rawMul_add_right, h1 k, coeffAt_rawMul_shift_right]
    simp only [rawMul, coeffAt_addCoeffs, coeffAt_map_mul]
    cases k with
    | zero => rfl
    | succ k' => simp [coeffAt_cons_succ, ih k']

theorem pMul_assoc {F : Type} [LawfulCommRing F] [DecidableEq F] (a b c : List F) :
    pMul (pMul a b) c = pMul a (pMul b c) := by
  have h1 : pMul (pMul a b) c = pMul (rawMul a b) c := pMul_trimPoly_left (rawMul a b) c
  have h2 : pMul a (pMul b c) = pMul a (rawMul b c) := pMul_trimPoly_right a (rawMul b c)
  rw [h1, h2]
  clear h1 h2
  unfold pMul
  rw [trimPoly_eq_iff_coeffAt]
  have hshiftLeft : ∀ (u v : List F) (k : Nat),
      coeffAt (rawMul (CommRingOps.zero :: u) v) k =
        coeffAt (CommRingOps.zero :: rawMul u v) k := by
    intro u v k
    simp [rawMul, coeffAt_addCoeffs, coeffAt_map_mul, LawfulCommRing.zero_mul, LawfulCommRing.zero_add]
  induction a with
  | nil => intro k; rfl
  | cons x xs ih =>
    intro k
    simp only [rawMul]
    rw [coeffAt_rawMul_add_left, coeffAt_rawMul_scale_left, hshiftLeft,
        coeffAt_addCoeffs, coeffAt_map_mul]
    cases k with
    | zero => simp only [coeffAt_cons_zero, LawfulCommRing.add_zero]
    | succ k' => simp only [coeffAt_cons_succ, ih k']

theorem pMul_pAdd_left {F : Type} [LawfulCommRing F] [DecidableEq F] (a1 a2 b : List F) :
    pMul (pAdd a1 a2) b = pAdd (pMul a1 b) (pMul a2 b) := by
  rw [show pAdd a1 a2 = trimPoly (rawAddCoeffs a1 a2) from rfl, pMul_trimPoly_left,
      show pMul a1 b = trimPoly (rawMul a1 b) from rfl,
      show pMul a2 b = trimPoly (rawMul a2 b) from rfl,
      pAdd_trimPoly_left, pAdd_trimPoly_right]
  unfold pMul pAdd; rw [trimPoly_eq_iff_coeffAt]
  intro k
  rw [coeffAt_rawMul_add_left, coeffAt_addCoeffs]

theorem pMul_pAdd_right {F : Type} [LawfulCommRing F] [DecidableEq F] (a b1 b2 : List F) :
    pMul a (pAdd b1 b2) = pAdd (pMul a b1) (pMul a b2) := by
  rw [pMul_comm a _, pMul_pAdd_left, pMul_comm b1 a, pMul_comm b2 a]

theorem pMul_pNeg_right {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) :
    pMul a (pNeg b) = pNeg (pMul a b) := by
  have heq : pNeg b = pScale (CommRingOps.neg CommRingOps.one) b := by
    unfold pNeg pScale; rw [trimPoly_eq_iff_coeffAt]; intro k
    rw [coeffAt_negCoeffs, coeffAt_map_mul, LawfulCommRing.neg_mul, LawfulCommRing.one_mul]
  have heq2 : pNeg (pMul a b) = pScale (CommRingOps.neg CommRingOps.one) (pMul a b) := by
    unfold pNeg pScale; rw [trimPoly_eq_iff_coeffAt]; intro k
    rw [coeffAt_negCoeffs, coeffAt_map_mul, LawfulCommRing.neg_mul, LawfulCommRing.one_mul]
  rw [heq, heq2]
  unfold pScale
  rw [pMul_trimPoly_right]
  unfold pMul
  rw [trimPoly_eq_iff_coeffAt]
  intro k
  rw [coeffAt_rawMul_scale_right, coeffAt_map_mul, coeffAt_trimPoly]

theorem pMul_pSub_right {F : Type} [LawfulCommRing F] [DecidableEq F] (a b1 b2 : List F) :
    pMul a (pSub b1 b2) = pSub (pMul a b1) (pMul a b2) := by
  rw [pSub_eq_pAdd_pNeg, pSub_eq_pAdd_pNeg, pMul_pAdd_right, pMul_pNeg_right]

theorem pMul_pScale_right {F : Type} [LawfulCommRing F] [DecidableEq F] (c : F) (a b : List F) :
    pMul a (pScale c b) = pScale c (pMul a b) := by
  unfold pScale; rw [pMul_trimPoly_right]
  unfold pMul; rw [trimPoly_eq_iff_coeffAt]; intro k
  rw [coeffAt_rawMul_scale_right, coeffAt_map_mul, coeffAt_trimPoly]

theorem pMul_one_right {F : Type} [LawfulCommRing F] [DecidableEq F] (a : List F) :
    pMul a [CommRingOps.one] = trimPoly a := by
  rw [pMul_comm]
  unfold pMul; rw [trimPoly_eq_iff_coeffAt]; intro k
  simp [rawMul, coeffAt_addCoeffs, coeffAt_map_mul, LawfulCommRing.one_mul]
  cases k <;> simp [coeffAt, LawfulCommRing.add_zero]

/-- Degree-additivity & integral-domain law for canonical polynomials over `[LawfulField F]`:
    for non-empty trimmed `a, b`, `(pMul a b).length = a.length + b.length - 1` and `pMul a b ≠ []`. -/
theorem pMul_length_of_trimmed_ne_nil
    {F : Type} [LawfulField F] [DecidableEq F]
    {a b : List F}
    (haTrim : IsTrimmed a) (hbTrim : IsTrimmed b)
    (haNe : a ≠ []) (hbNe : b ≠ []) :
    (pMul a b).length = a.length + b.length - 1 ∧ pMul a b ≠ [] := by
  let da := a.length - 1
  let db := b.length - 1
  have haLen : a.length = da + 1 := by cases a with | nil => contradiction | cons _ _ => simp [da]
  have hbLen : b.length = db + 1 := by cases b with | nil => contradiction | cons _ _ => simp [db]
  have haHigh : ∀ i, da < i → coeffAt a i = CommRingOps.zero :=
    fun i hi => coeffAt_eq_zero_of_ge a i (by omega)
  have hbHigh : ∀ j, db < j → coeffAt b j = CommRingOps.zero :=
    fun j hj => coeffAt_eq_zero_of_ge b j (by omega)
  rcases coeffAt_rawMul_high b db hbHigh da a haHigh with ⟨hHigh, hTop⟩
  have hlaNe : coeffAt a da ≠ CommRingOps.zero := by
    have h := leadCoeff_ne_zero_of_trimPoly_ne_nil a (by rwa [haTrim])
    rw [haTrim] at h
    exact h
  have hlbNe : coeffAt b db ≠ CommRingOps.zero := by
    have h := leadCoeff_ne_zero_of_trimPoly_ne_nil b (by rwa [hbTrim])
    rw [hbTrim] at h
    exact h
  have hTopNe : coeffAt (rawMul a b) (da + db) ≠ CommRingOps.zero := by
    rw [hTop]
    intro h0
    rcases LawfulField.mul_eq_zero h0 with h1 | h2
    · exact hlaNe h1
    · exact hlbNe h2
  have hpNe : pMul a b ≠ [] := by
    intro hnil
    have h0 := (trimPoly_eq_nil_iff (rawMul a b)).mp hnil (da + db)
    exact hTopNe h0
  have hle : (pMul a b).length ≤ da + db + 1 :=
    length_trimPoly_le_of_coeffAt_zero (rawMul a b) (da + db + 1)
      (fun k hk => hHigh k (by omega))
  have hge : da + db + 1 ≤ (pMul a b).length := by
    if hlt : (pMul a b).length < da + db + 1 then
      have h0 : coeffAt (pMul a b) (da + db) = CommRingOps.zero :=
        coeffAt_eq_zero_of_ge (pMul a b) (da + db) (by omega)
      rw [pMul, coeffAt_trimPoly] at h0
      exact False.elim (hTopNe h0)
    else
      omega
  refine ⟨by omega, hpNe⟩

theorem pMul_eq_nil_iff {F : Type} [LawfulField F] [DecidableEq F] (a b : List F) :
    pMul a b = [] ↔ trimPoly a = [] ∨ trimPoly b = [] := by
  constructor
  · intro h
    if ha : trimPoly a = [] then
      exact .inl ha
    else if hb : trimPoly b = [] then
      exact .inr hb
    else
      rw [← pMul_trimPoly_left, ← pMul_trimPoly_right (trimPoly a) b] at h
      have hne := (pMul_length_of_trimmed_ne_nil (trimPoly_idem a) (trimPoly_idem b) ha hb).2
      exact False.elim (hne h)
  · rintro (ha | hb)
    · rw [← pMul_trimPoly_left, ha]; rfl
    · rw [← pMul_trimPoly_right, hb, pMul_comm]; rfl

theorem pAdd_length_le {F : Type} [LawfulCommRing F] [DecidableEq F] (a b : List F) (B : Nat)
    (ha : a.length ≤ B) (hb : b.length ≤ B) :
    (pAdd a b).length ≤ B := by
  apply length_trimPoly_le_of_coeffAt_zero _ B
  intro k hk
  rw [coeffAt_addCoeffs, coeffAt_eq_zero_of_ge a k (by omega),
      coeffAt_eq_zero_of_ge b k (by omega), LawfulCommRing.add_zero]

theorem pMul_length_le {F : Type} [LawfulField F] [DecidableEq F] (a b : List F) (ka kb : Nat)
    (ha : a.length ≤ ka + 1) (hb : b.length ≤ kb + 1) :
    (pMul a b).length ≤ ka + kb + 1 := by
  if ha0 : trimPoly a = [] then
    rw [(pMul_eq_nil_iff a b).mpr (.inl ha0)]; simp
  else if hb0 : trimPoly b = [] then
    rw [(pMul_eq_nil_iff a b).mpr (.inr hb0)]; simp
  else
    rw [← pMul_trimPoly_left, ← pMul_trimPoly_right (trimPoly a) b]
    have hlen := (pMul_length_of_trimmed_ne_nil (trimPoly_idem a) (trimPoly_idem b) ha0 hb0).1
    have haL := trimPoly_length_le a
    have hbL := trimPoly_length_le b
    omega

theorem coeffAt_monomial {F : Type} [CommRingOps F] :
    ∀ (deg k : Nat) (c : F),
      coeffAt (monomial deg c) k = if k = deg then c else CommRingOps.zero
  | 0, 0, _ => rfl
  | 0, k + 1, _ => by
    have hne : k + 1 ≠ 0 := Nat.succ_ne_zero k
    simp only [hne, ↓reduceIte]; rfl
  | deg + 1, 0, _ => by
    have hne : (0 : Nat) ≠ deg + 1 := (Nat.succ_ne_zero deg).symm
    simp only [hne, ↓reduceIte]; rfl
  | deg + 1, k + 1, c => by
    have hcons : monomial (deg + 1) c = CommRingOps.zero :: monomial deg c := rfl
    have heq : (k + 1 = deg + 1) ↔ (k = deg) := ⟨Nat.succ.inj, congrArg Nat.succ⟩
    rw [hcons, coeffAt_cons_succ, coeffAt_monomial deg k c]
    simp only [heq]
  termination_by structural deg => deg

/-- Fuel-bounded constructive Euclidean polynomial division (`0` `WellFounded.fix`, `0` choice). -/
def polyDivModFuel {F : Type} [LawfulField F] [DecidableEq F] :
    Nat → List F → List F → List F × List F
  | 0, a, _ => ([], trimPoly a)
  | fuel + 1, a, b =>
    let a' := trimPoly a
    let b' := trimPoly b
    if b' = [] ∨ a'.length < b'.length then
      ([], a')
    else
      let da := a'.length - 1
      let db := b'.length - 1
      let coef := CommRingOps.mul (coeffAt a' da) (LawfulField.inv (coeffAt b' db))
      let stepQ := monomial (da - db) coef
      let rem1 := pSub a' (pMul stepQ b')
      let qr := polyDivModFuel fuel rem1 b'
      (pAdd stepQ qr.1, qr.2)

/-- Constructive univariate Euclidean division `polyDivMod a b = (q, r)`. -/
def polyDivMod {F : Type} [LawfulField F] [DecidableEq F] (a b : List F) : List F × List F :=
  polyDivModFuel (trimPoly a).length a b

private theorem polyDivModFuel_spec
    {F : Type} [LawfulField F] [DecidableEq F] :
    ∀ (fuel : Nat) (a b : List F),
      trimPoly b ≠ [] →
      (trimPoly a).length ≤ fuel →
      let (q, r) := polyDivModFuel fuel a b
      IsTrimmed q ∧ IsTrimmed r ∧
      trimPoly a = pAdd (pMul q b) r ∧
      r.length < (trimPoly b).length
  | 0, a, b, hbNe, hfuel => by
    have haNil : trimPoly a = [] := by
      cases h : trimPoly a with
      | nil => rfl
      | cons _ _ => rw [h] at hfuel; simp at hfuel
    have hbPos : 0 < (trimPoly b).length := by
      cases h : trimPoly b with
      | nil => exact False.elim (hbNe h)
      | cons _ _ => simp
    dsimp [polyDivModFuel]
    refine ⟨rfl, trimPoly_idem a, ?_, by rw [haNil]; exact hbPos⟩
    rw [haNil]
    have hmul0 : pMul ([] : List F) b = [] := (pMul_eq_nil_iff [] b).mpr (.inl rfl)
    rw [hmul0, pAdd_nil_left]; rfl
  | fuel + 1, a, b, hbNe, hfuel => by
    dsimp only [polyDivModFuel]
    if hstop : trimPoly b = [] ∨ (trimPoly a).length < (trimPoly b).length then
      simp only [hstop, ↓reduceIte]
      rcases hstop with hb0 | hlt
      · exact False.elim (hbNe hb0)
      · refine ⟨rfl, trimPoly_idem a, ?_, hlt⟩
        have hmul0 : pMul ([] : List F) b = [] := (pMul_eq_nil_iff [] b).mpr (.inl rfl)
        rw [hmul0, pAdd_nil_left, trimPoly_idem]
    else
      simp only [hstop, ↓reduceIte]
      have hge : (trimPoly b).length ≤ (trimPoly a).length := by omega
      let a' := trimPoly a
      let b' := trimPoly b
      have hbPos : 1 ≤ b'.length := by
        cases h : b' with
        | nil => exact False.elim (hbNe h)
        | cons _ _ => simp
      have haPos : 1 ≤ a'.length := by dsimp only [a', b'] at hbPos ⊢; omega
      let da := a'.length - 1
      let db := b'.length - 1
      have hlbNe : coeffAt b' db ≠ CommRingOps.zero := by
        have h := leadCoeff_ne_zero_of_trimPoly_ne_nil b hbNe
        simpa [b', db] using h
      let coef := CommRingOps.mul (coeffAt a' da) (LawfulField.inv (coeffAt b' db))
      let stepQ := monomial (da - db) coef
      let rem1 := pSub a' (pMul stepQ b')
      have hStepHigh : ∀ i, da - db < i → coeffAt stepQ i = CommRingOps.zero := by
        intro i hi
        rw [coeffAt_monomial]
        simp [show i ≠ da - db by omega]
      have hbHigh : ∀ j, db < j → coeffAt b' j = CommRingOps.zero :=
        fun j hj => coeffAt_eq_zero_of_ge b' j (by omega)
      rcases coeffAt_rawMul_high b' db hbHigh (da - db) stepQ hStepHigh with ⟨hMulHigh, hMulTop⟩
      have hdaEq : da - db + db = da := by dsimp only [a', b', da, db]; omega
      rw [hdaEq] at hMulHigh hMulTop
      have hRemLen : rem1.length ≤ da := by
        apply length_trimPoly_le_of_coeffAt_zero _ da
        intro k hk
        rw [coeffAt_subCoeffs, pMul, coeffAt_trimPoly (rawMul stepQ b') k]
        if hkEq : k = da then
          subst hkEq
          rw [hMulTop, coeffAt_monomial]
          simp only [↓reduceIte]
          dsimp [coef]
          rw [LawfulCommRing.mul_assoc, LawfulField.inv_mul_cancel hlbNe,
              LawfulCommRing.mul_one, LawfulCommRing.sub_self]
        else
          rw [coeffAt_eq_zero_of_ge a' k (by dsimp only [da] at hk hkEq; omega),
              hMulHigh k (by omega),
              LawfulCommRing.sub_self]
      have hRemTrim : IsTrimmed rem1 := trimPoly_idem _
      have hRemFuel : (trimPoly rem1).length ≤ fuel := by
        rw [hRemTrim]
        dsimp only [a', da] at hRemLen
        omega
      have hb'Ne : trimPoly b' ≠ [] := by rwa [trimPoly_idem]
      have ih := polyDivModFuel_spec fuel rem1 b' hb'Ne hRemFuel
      let qr := polyDivModFuel fuel rem1 b'
      rcases ih with ⟨hqTrim, hrTrim, hRemDecomp, hrLt⟩
      rw [hRemTrim] at hRemDecomp
      rw [trimPoly_idem] at hrLt
      refine ⟨trimPoly_idem _, hrTrim, ?_, hrLt⟩
      -- `a' = pMul stepQ b' + rem1 = pMul stepQ b + (pMul qr.1 b + qr.2) = pMul (stepQ + qr.1) b + qr.2`
      rw [pMul_pAdd_left, ← pMul_trimPoly_right stepQ b, ← pMul_trimPoly_right qr.1 b,
          pAdd_assoc, ← hRemDecomp]
      have hcancel := pAdd_pSub_cancel a' (pMul stepQ b')
      rw [trimPoly_idem] at hcancel
      exact hcancel.symm
  termination_by structural fuel => fuel

/-- **Constructive Euclidean Division Specification (`polyDivMod_spec`)**:
    For any `a, b : List F` with `trimPoly b ≠ []`, `polyDivMod a b = (q, r)` produces canonical
    trimmed polynomials satisfying `trimPoly a = pAdd (pMul q b) r` and `r.length < (trimPoly b).length`. -/
theorem polyDivMod_spec
    {F : Type} [LawfulField F] [DecidableEq F]
    (a b : List F) (hbNe : trimPoly b ≠ []) :
    let (q, r) := polyDivMod a b
    IsTrimmed q ∧ IsTrimmed r ∧
    trimPoly a = pAdd (pMul q b) r ∧
    r.length < (trimPoly b).length :=
  polyDivModFuel_spec (trimPoly a).length a b hbNe (Nat.le_refl _)

/-- Divisibility relation on canonical trimmed polynomials. -/
def DvdTrim {F : Type} [CommRingOps F] [DecidableEq F] (d a : List F) : Prop :=
  ∃ k : List F, trimPoly a = pMul d k

theorem dvdTrim_refl {F : Type} [LawfulCommRing F] [DecidableEq F] (d : List F) :
    DvdTrim d d :=
  ⟨[CommRingOps.one], (pMul_one_right d).symm⟩

theorem dvdTrim_nil {F : Type} [LawfulField F] [DecidableEq F] (d : List F) :
    DvdTrim d [] :=
  ⟨[], ((pMul_eq_nil_iff d []).mpr (.inr rfl)).symm⟩

theorem dvdTrim_trans {F : Type} [LawfulCommRing F] [DecidableEq F]
    {a b c : List F} (hab : DvdTrim a b) (hbc : DvdTrim b c) : DvdTrim a c := by
  rcases hab with ⟨k1, hk1⟩
  rcases hbc with ⟨k2, hk2⟩
  refine ⟨pMul k1 k2, ?_⟩
  rw [hk2, ← pMul_trimPoly_left b k2, hk1, pMul_assoc]

/-- Constructive exact quotient extraction: if `DvdTrim g a` and `trimPoly g ≠ []`, then
    `polyDivMod a g` has remainder `[]` and its quotient `q = (polyDivMod a g).1` satisfies
    `trimPoly a = pMul g q` (`0` classical choice!). -/
theorem exactDiv_of_dvdTrim
    {F : Type} [LawfulField F] [DecidableEq F]
    (a g : List F) (hgNe : trimPoly g ≠ []) (hdvd : DvdTrim g a) :
    let (q, r) := polyDivMod a g
    IsTrimmed q ∧ r = [] ∧ trimPoly a = pMul g q := by
  have hspec := polyDivMod_spec a g hgNe
  dsimp only at hspec ⊢
  rcases hspec with ⟨hqTrim, hrTrim, hDecomp, hrLt⟩
  rcases hdvd with ⟨k, hk⟩
  have hrEq : trimPoly (polyDivMod a g).2 = pMul (trimPoly g) (pSub k (polyDivMod a g).1) := by
    have h1 := pSub_pAdd_cancel_left (pMul (polyDivMod a g).1 g) (polyDivMod a g).2
    rw [← hDecomp, hk, pMul_comm (polyDivMod a g).1 g, ← pMul_pSub_right,
        ← pMul_trimPoly_left g] at h1
    exact h1.symm
  rw [hrTrim] at hrEq
  have hrNil : (polyDivMod a g).2 = [] := by
    if hrNe : (polyDivMod a g).2 = [] then
      exact hrNe
    else
      have hdiffNe : trimPoly (pSub k (polyDivMod a g).1) ≠ [] := by
        intro h0
        rw [(pMul_eq_nil_iff (trimPoly g) _).mpr (.inr h0)] at hrEq
        exact hrNe hrEq
      rw [← pMul_trimPoly_right (trimPoly g)] at hrEq
      have hlen := (pMul_length_of_trimmed_ne_nil (trimPoly_idem g) (trimPoly_idem _) hgNe hdiffNe).1
      rw [← hrEq] at hlen
      have hpos : 1 ≤ (trimPoly (pSub k (polyDivMod a g).1)).length := by
        cases h : trimPoly (pSub k (polyDivMod a g).1) with
        | nil => exact False.elim (hdiffNe h)
        | cons _ _ => simp
      omega
  refine ⟨hqTrim, hrNil, ?_⟩
  rw [hrNil, pAdd_nil_right, pMul_comm] at hDecomp
  simpa [pMul, trimPoly_idem] using hDecomp

/-- Fuel-bounded constructive Euclidean polynomial GCD (`0` `WellFounded.fix`, `0` choice). -/
def polyGcdFuel {F : Type} [LawfulField F] [DecidableEq F] :
    Nat → List F → List F → List F
  | 0, a, _ => trimPoly a
  | fuel + 1, a, b =>
    let a' := trimPoly a
    let b' := trimPoly b
    if b' = [] then a'
    else
      let r := (polyDivMod a' b').2
      polyGcdFuel fuel b' r

/-- Constructive greatest common divisor `polyGcd a b` on `List F`. -/
def polyGcd {F : Type} [LawfulField F] [DecidableEq F] (a b : List F) : List F :=
  polyGcdFuel ((trimPoly b).length + 1) a b

private theorem polyGcdFuel_spec
    {F : Type} [LawfulField F] [DecidableEq F] :
    ∀ (fuel : Nat) (a b : List F),
      (trimPoly b).length < fuel →
      let g := polyGcdFuel fuel a b
      IsTrimmed g ∧
      DvdTrim g a ∧ DvdTrim g b ∧
      (∀ d : List F, DvdTrim d a → DvdTrim d b → DvdTrim d g)
  | 0, _, _, hlt => by cases hlt
  | fuel + 1, a, b, hlt => by
    dsimp only [polyGcdFuel]
    if hb0 : trimPoly b = [] then
      simp only [hb0, ↓reduceIte]
      refine ⟨trimPoly_idem a, ?_, ?_, ?_⟩
      · refine ⟨[CommRingOps.one], ?_⟩
        rw [pMul_one_right, trimPoly_idem]
      · exact ⟨[], by rw [hb0, (pMul_eq_nil_iff _ []).mpr (.inr rfl)]⟩
      · intro d hda _
        rcases hda with ⟨k, hk⟩
        exact ⟨k, by rwa [trimPoly_idem]⟩
    else
      simp only [hb0, ↓reduceIte]
      have hb'Ne : trimPoly (trimPoly b) ≠ [] := by rwa [trimPoly_idem]
      have hdivSpec := polyDivMod_spec (trimPoly a) (trimPoly b) hb'Ne
      dsimp only at hdivSpec
      rcases hdivSpec with ⟨hqT, hrT, hDecomp, hrLt⟩
      rw [trimPoly_idem] at hDecomp
      rw [trimPoly_idem] at hrLt
      let q := (polyDivMod (trimPoly a) (trimPoly b)).1
      let r := (polyDivMod (trimPoly a) (trimPoly b)).2
      change trimPoly a = pAdd (pMul q (trimPoly b)) r at hDecomp
      have hrFuel : (trimPoly r).length < fuel := by
        rw [hrT]
        exact Nat.lt_of_lt_of_le hrLt (Nat.le_of_lt_succ hlt)
      rcases polyGcdFuel_spec fuel (trimPoly b) r hrFuel with ⟨hgT, hgb, hgr, hgUniv⟩
      let g := polyGcdFuel fuel (trimPoly b) r
      refine ⟨hgT, ?_, ?_, ?_⟩
      · -- `g | b` and `g | r` implies `g | q*b + r = a`
        rcases hgb with ⟨kb, hkb⟩
        rcases hgr with ⟨kr, hkr⟩
        rw [trimPoly_idem] at hkb
        rw [hrT] at hkr
        change trimPoly b = pMul g kb at hkb
        change r = pMul g kr at hkr
        refine ⟨pAdd (pMul kb q) kr, ?_⟩
        calc trimPoly a
            = pAdd (pMul q (trimPoly b)) r := hDecomp
          _ = pAdd (pMul (trimPoly b) q) r := by rw [pMul_comm q (trimPoly b)]
          _ = pAdd (pMul (pMul g kb) q) r := congrArg (fun x => pAdd (pMul x q) r) hkb
          _ = pAdd (pMul (pMul g kb) q) (pMul g kr) := congrArg (pAdd (pMul (pMul g kb) q)) hkr
          _ = pAdd (pMul g (pMul kb q)) (pMul g kr) := by rw [pMul_assoc]
          _ = pMul g (pAdd (pMul kb q) kr) := (pMul_pAdd_right g _ _).symm
      · rcases hgb with ⟨kb, hkb⟩
        rw [trimPoly_idem] at hkb
        exact ⟨kb, hkb⟩
      · intro d hda hdb
        apply hgUniv d
        · rcases hdb with ⟨kb, hkb⟩
          exact ⟨kb, by rwa [trimPoly_idem]⟩
        · -- `d | a` and `d | b` implies `d | a - q*b = r`
          rcases hda with ⟨ka, hka⟩
          rcases hdb with ⟨kb, hkb⟩
          have hrSub := pSub_pAdd_cancel_left (pMul q (trimPoly b)) r
          rw [← hDecomp, hka, pMul_comm q (trimPoly b), hkb,
              pMul_assoc, ← pMul_pSub_right] at hrSub
          exact ⟨pSub ka (pMul kb q), hrSub.symm⟩
  termination_by structural fuel => fuel

/-- **Constructive Polynomial GCD Specification (`polyGcd_spec`)**. -/
theorem polyGcd_spec
    {F : Type} [LawfulField F] [DecidableEq F]
    (a b : List F) :
    let g := polyGcd a b
    IsTrimmed g ∧
    DvdTrim g a ∧ DvdTrim g b ∧
    (∀ d : List F, DvdTrim d a → DvdTrim d b → DvdTrim d g) :=
  polyGcdFuel_spec ((trimPoly b).length + 1) a b (Nat.lt_succ_self _)


end Qsag

namespace Qsag

set_option autoImplicit false

open CommRingOps RoundPoly

/-- Canonical univariate polynomials over `R`: coefficient lists without trailing zeros. -/
structure UPoly (R : Type) [CommRingOps R] [DecidableEq R] where
  coeffs : List R
  trimmed : trimPoly coeffs = coeffs

namespace UPoly

section Ring
variable {R : Type} [LawfulCommRing R] [DecidableEq R]

theorem ext {a b : UPoly R} (h : a.coeffs = b.coeffs) : a = b := by
  cases a; cases b; cases h; rfl

instance : DecidableEq (UPoly R) := fun a b =>
  if h : a.coeffs = b.coeffs then .isTrue (ext h) else .isFalse (fun e => h (e ▸ rfl))

/-- Canonicalize a coefficient list. -/
@[expose] def ofList (l : List R) : UPoly R := ⟨trimPoly l, trimPoly_idem l⟩

theorem coeffs_ofList (l : List R) : (ofList l).coeffs = trimPoly l := by rfl
theorem pAdd_trimmed (a b : List R) : trimPoly (pAdd a b) = pAdd a b := trimPoly_idem _
theorem pMul_trimmed (a b : List R) : trimPoly (pMul a b) = pMul a b := trimPoly_idem _
theorem pNeg_trimmed (a : List R) : trimPoly (pNeg a) = pNeg a := trimPoly_idem _
theorem pSub_trimmed (a b : List R) : trimPoly (pSub a b) = pSub a b := trimPoly_idem _

instance instLawfulCommRing : LawfulCommRing (UPoly R) where
  zero := ofList []
  one := ofList [one]
  add a b := ⟨pAdd a.coeffs b.coeffs, pAdd_trimmed _ _⟩
  mul a b := ⟨pMul a.coeffs b.coeffs, pMul_trimmed _ _⟩
  neg a := ⟨pNeg a.coeffs, pNeg_trimmed _⟩
  sub a b := ⟨pSub a.coeffs b.coeffs, pSub_trimmed _ _⟩
  add_assoc a b c := ext (pAdd_assoc a.coeffs b.coeffs c.coeffs)
  add_comm a b := ext (pAdd_comm a.coeffs b.coeffs)
  zero_add a := by
    apply ext
    show pAdd [] a.coeffs = a.coeffs
    rw [pAdd_nil_left, a.trimmed]
  add_zero a := by
    apply ext
    show pAdd a.coeffs [] = a.coeffs
    rw [pAdd_nil_right, a.trimmed]
  add_left_neg a := by
    apply ext
    show trimPoly (rawAddCoeffs (pNeg a.coeffs) a.coeffs) = trimPoly []
    rw [trimPoly_eq_iff_coeffAt]
    intro k
    rw [coeffAt_addCoeffs, coeffAt_pNeg, LawfulCommRing.add_left_neg, coeffAt_nil]
  sub_eq_add_neg a b := ext (pSub_eq_pAdd_pNeg a.coeffs b.coeffs)
  mul_assoc a b c := ext (pMul_assoc a.coeffs b.coeffs c.coeffs)
  mul_comm a b := ext (pMul_comm a.coeffs b.coeffs)
  one_mul a := by
    apply ext
    show pMul (trimPoly [one]) a.coeffs = a.coeffs
    rw [pMul_trimPoly_left, pMul_comm, pMul_one_right, a.trimmed]
  mul_one a := by
    apply ext
    show pMul a.coeffs (trimPoly [one]) = a.coeffs
    rw [pMul_trimPoly_right, pMul_one_right, a.trimmed]
  left_distrib a b c := ext (pMul_pAdd_right a.coeffs b.coeffs c.coeffs)
  right_distrib a b c := ext (pMul_pAdd_left a.coeffs b.coeffs c.coeffs)

theorem coeffs_zero : (zero : UPoly R).coeffs = [] := by rfl
theorem coeffs_add (a b : UPoly R) : (add a b).coeffs = pAdd a.coeffs b.coeffs := by rfl
theorem coeffs_mul (a b : UPoly R) : (mul a b).coeffs = pMul a.coeffs b.coeffs := by rfl
theorem coeffs_neg (a : UPoly R) : (neg a).coeffs = pNeg a.coeffs := by rfl
theorem coeffs_sub (a b : UPoly R) : (sub a b).coeffs = pSub a.coeffs b.coeffs := by rfl
theorem coeffs_one : (one : UPoly R).coeffs = trimPoly [one] := by rfl
theorem eq_iff_coeffs {a b : UPoly R} : a = b ↔ a.coeffs = b.coeffs := ⟨fun h => h ▸ rfl, ext⟩
theorem eq_zero_iff (a : UPoly R) : a = zero ↔ a.coeffs = [] :=
  ⟨fun h => h ▸ rfl, fun h => ext h⟩

/-- Coefficientwise extensionality. -/
theorem ext_coeffAt {a b : UPoly R} (h : ∀ k, coeffAt a.coeffs k = coeffAt b.coeffs k) :
    a = b := by
  apply ext
  rw [← a.trimmed, ← b.trimmed]
  exact (trimPoly_eq_iff_coeffAt _ _).mpr h

theorem coeffAt_add (a b : UPoly R) (k : Nat) :
    coeffAt (add a b).coeffs k = add (coeffAt a.coeffs k) (coeffAt b.coeffs k) :=
  coeffAt_pAdd _ _ k

theorem coeffAt_neg (a : UPoly R) (k : Nat) :
    coeffAt (neg a).coeffs k = neg (coeffAt a.coeffs k) := coeffAt_pNeg _ k

theorem coeffAt_sub (a b : UPoly R) (k : Nat) :
    coeffAt (sub a b).coeffs k = sub (coeffAt a.coeffs k) (coeffAt b.coeffs k) :=
  coeffAt_pSub _ _ k

theorem coeffAt_ofList (l : List R) (k : Nat) : coeffAt (ofList l).coeffs k = coeffAt l k :=
  coeffAt_trimPoly l k

/-- The degree, with `natDeg 0 = 0`. -/
@[expose] def natDeg (p : UPoly R) : Nat := p.coeffs.length - 1

/-- The leading coefficient (`zero` for the zero polynomial). -/
def lead (p : UPoly R) : R := coeffAt p.coeffs p.natDeg

theorem lead_ne_zero {p : UPoly R} (h : p ≠ zero) : p.lead ≠ zero := by
  have hne : trimPoly p.coeffs ≠ [] := by
    rw [p.trimmed]; exact fun e => h ((eq_zero_iff p).mpr e)
  have := leadCoeff_ne_zero_of_trimPoly_ne_nil p.coeffs hne
  rwa [p.trimmed] at this

theorem coeffAt_eq_zero_of_natDeg_lt (p : UPoly R) {k : Nat} (h : p.natDeg < k) :
    coeffAt p.coeffs k = zero :=
  coeffAt_eq_zero_of_ge p.coeffs k (by unfold natDeg at h; omega)

theorem natDeg_le_of_coeffAt (p : UPoly R) (B : Nat)
    (h : ∀ k, B < k → coeffAt p.coeffs k = zero) : p.natDeg ≤ B := by
  have := length_trimPoly_le_of_coeffAt_zero p.coeffs (B + 1) (fun k hk => h k (by omega))
  rw [p.trimmed] at this
  unfold natDeg; omega

/-- Coefficients of a product above the sum of the degrees vanish, and the top one is the
    product of the leading coefficients. -/
theorem coeffAt_mul_top (a b : UPoly R) :
    (∀ k, a.natDeg + b.natDeg < k → coeffAt (mul a b).coeffs k = zero) ∧
    coeffAt (mul a b).coeffs (a.natDeg + b.natDeg) = mul a.lead b.lead := by
  have h := coeffAt_rawMul_high b.coeffs b.natDeg
    (fun j hj => b.coeffAt_eq_zero_of_natDeg_lt hj) a.natDeg a.coeffs
    (fun i hi => a.coeffAt_eq_zero_of_natDeg_lt hi)
  refine ⟨fun k hk => ?_, ?_⟩
  · show coeffAt (trimPoly (rawMul a.coeffs b.coeffs)) k = zero
    rw [coeffAt_trimPoly]; exact h.1 k hk
  · show coeffAt (trimPoly (rawMul a.coeffs b.coeffs)) _ = _
    rw [coeffAt_trimPoly]; exact h.2

theorem natDeg_mul_le (a b : UPoly R) : (mul a b).natDeg ≤ a.natDeg + b.natDeg :=
  natDeg_le_of_coeffAt _ _ (coeffAt_mul_top a b).1

theorem natDeg_add_le (a b : UPoly R) : (add a b).natDeg ≤ max a.natDeg b.natDeg := by
  apply natDeg_le_of_coeffAt
  intro k hk
  have ha : a.natDeg < k := by omega
  have hb : b.natDeg < k := by omega
  rw [coeffAt_add, a.coeffAt_eq_zero_of_natDeg_lt ha, b.coeffAt_eq_zero_of_natDeg_lt hb,
    LawfulCommRing.add_zero]

instance [NoZeroDivisors R] : NoZeroDivisors (UPoly R) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b h
    if ha : a = zero then exact .inl ha
    else if hb : b = zero then exact .inr hb
    else
      exfalso
      have htop := (coeffAt_mul_top a b).2
      rw [show (CommRingOps.mul a b) = zero from h, coeffs_zero, coeffAt_nil] at htop
      rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero htop.symm with h1 | h1
      · exact lead_ne_zero ha h1
      · exact lead_ne_zero hb h1

/-- Over a domain the degree of a product of nonzero polynomials is the sum of degrees. -/
theorem natDeg_mul [NoZeroDivisors R] {a b : UPoly R} (ha : a ≠ zero) (hb : b ≠ zero) :
    (mul a b).natDeg = a.natDeg + b.natDeg := by
  apply Nat.le_antisymm (natDeg_mul_le a b)
  apply Decidable.byContradiction
  intro hlt
  have hz := (mul a b).coeffAt_eq_zero_of_natDeg_lt (Nat.lt_of_not_le hlt)
  rw [(coeffAt_mul_top a b).2] at hz
  rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hz with h1 | h1
  · exact lead_ne_zero ha h1
  · exact lead_ne_zero hb h1

end Ring

end UPoly
end Qsag

namespace Qsag
open CommRingOps
namespace UPoly
variable {R : Type} [LawfulCommRing R] [DecidableEq R]
 theorem lead_eq (p : UPoly R) : p.lead = coeffAt p.coeffs p.natDeg := by rfl
end UPoly
end Qsag

namespace Qsag
 theorem scaleVec_eq {F : Type} [CommRingOps F] (c : F) (v : List F) :
    scaleVec c v = v.map (CommRingOps.mul c) := by unfold scaleVec; rfl
end Qsag

namespace Qsag
open RoundPoly
abbrev GsUniPoly (F : Type) [CommRingOps F] [DecidableEq F] := UPoly F
namespace GsUniPoly
abbrev val {F : Type} [CommRingOps F] [DecidableEq F] (p : GsUniPoly F) := p.coeffs
theorem property {F : Type} [CommRingOps F] [DecidableEq F] (p : GsUniPoly F) : trimPoly p.coeffs = p.coeffs := p.trimmed
abbrev ofCoeffs {F : Type} [LawfulField F] [DecidableEq F] (p : List F) : GsUniPoly F := UPoly.ofList p
end GsUniPoly
end Qsag

namespace Qsag
/-! ## §1. Constructive Leading-Coefficient Polynomial Root Bound -/

private theorem quotLinear_append_lead {R : Type} [LawfulCommRing R] :
    ∀ (init : List R) (c₀ lead r : R),
      ∃ init' : List R, init'.length = init.length ∧
        RoundPoly.quotLinear (c₀ :: (init ++ [lead])) r = init' ++ [lead]
  | [], c₀, lead, r =>
    ⟨[], rfl, by simp [RoundPoly.quotLinear, RoundPoly.evalCoeffs,
      LawfulCommRing.mul_zero, LawfulCommRing.add_zero]⟩
  | c₁ :: rest, c₀, lead, r => by
    obtain ⟨init', hLen, hEq⟩ := quotLinear_append_lead rest c₁ lead r
    refine ⟨RoundPoly.evalCoeffs (c₁ :: (rest ++ [lead])) r :: init', congrArg Nat.succ hLen, ?_⟩
    simp only [List.cons_append, RoundPoly.quotLinear]
    exact congrArg (RoundPoly.evalCoeffs (c₁ :: (rest ++ [lead])) r :: ·) hEq

private theorem mem_of_mem_filter_spn {α : Type} {p : α → Bool} {x : α} :
    ∀ {l : List α}, x ∈ l.filter p → x ∈ l
  | [], h => by cases h
  | _ :: _, h => by
    simp only [List.filter] at h; split at h
    · cases h with | head => exact .head _ | tail _ hm => exact .tail _ (mem_of_mem_filter_spn hm)
    · exact .tail _ (mem_of_mem_filter_spn h)

private theorem pred_of_mem_filter_spn {α : Type} {p : α → Bool} {x : α} :
    ∀ {l : List α}, x ∈ l.filter p → p x = true
  | [], h => by cases h
  | _ :: _, h => by
    simp only [List.filter] at h; split at h
    · rename_i hpx; cases h with | head => exact hpx | tail _ hm => exact pred_of_mem_filter_spn hm
    · exact pred_of_mem_filter_spn h

private theorem nodup_filter_spn {α : Type} (p : α → Bool) :
    ∀ {l : List α}, l.Nodup → (l.filter p).Nodup
  | [], _ => .nil
  | _ :: _, .cons hrel htail => by
    simp only [List.filter]; split
    · exact .cons (fun b hb => hrel b (mem_of_mem_filter_spn hb)) (nodup_filter_spn p htail)
    · exact nodup_filter_spn p htail

/-- **Leading-Coefficient Root-Counting Bound (`evalCoeffs_roots_le_of_lead_nonzero`)**:
    Over every `LawfulCommRing R` without zero divisors, any polynomial `init ++ [lead]` of exact
    degree `d = init.length` with `lead ≠ 0` has at most `d` roots in any duplicate-free list `S`. -/
theorem evalCoeffs_roots_le_of_lead_nonzero
    {R : Type} [LawfulCommRing R] [DecidableEq R] [NoZeroDivisors R] :
    ∀ (d : Nat) (init : List R) (lead : R) (S : List R),
      init.length = d → lead ≠ CommRingOps.zero → S.Nodup →
      (S.filter (fun r => decide (RoundPoly.evalCoeffs (init ++ [lead]) r = CommRingOps.zero))).length ≤ d
  | 0, init, lead, S, hLen, hLead, _ => by
    cases init with
    | cons _ _ => cases hLen
    | nil =>
      have hEmpty : S.filter (fun r => decide (RoundPoly.evalCoeffs [lead] r = CommRingOps.zero)) = [] := by
        cases hFilt : S.filter (fun r => decide (RoundPoly.evalCoeffs [lead] r = CommRingOps.zero)) with
        | nil => rfl
        | cons r _ =>
          have hp := pred_of_mem_filter_spn (p := fun r => decide (RoundPoly.evalCoeffs [lead] r = CommRingOps.zero))
            (l := S) (x := r) (by rw [hFilt]; exact .head _)
          have hr : RoundPoly.evalCoeffs [lead] r = CommRingOps.zero := of_decide_eq_true hp
          simp only [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero] at hr
          exact False.elim (hLead hr)
      rw [List.nil_append, hEmpty]
      exact Nat.zero_le 0
  | d + 1, init, lead, S, hLen, hLead, hNodup => by
    cases init with
    | nil => cases hLen
    | cons c₀ restInit =>
      let cs := c₀ :: (restInit ++ [lead])
      let p : R → Bool := fun r => decide (RoundPoly.evalCoeffs cs r = CommRingOps.zero)
      have hndRoots := nodup_filter_spn p hNodup
      cases hRoots : S.filter p with
      | nil =>
        change (S.filter p).length ≤ d + 1
        rw [hRoots]
        exact Nat.zero_le (d + 1)
      | cons r rest =>
        rw [hRoots] at hndRoots
        cases hndRoots with
        | cons hNotMem hndRest =>
          have hrRoot : RoundPoly.evalCoeffs cs r = CommRingOps.zero :=
            of_decide_eq_true (pred_of_mem_filter_spn (p := p) (l := S) (x := r) (by rw [hRoots]; exact .head _))
          obtain ⟨init', hLen', hQuotEq⟩ := quotLinear_append_lead restInit c₀ lead r
          have hRestEq : rest.filter (fun y =>
              decide (RoundPoly.evalCoeffs (init' ++ [lead]) y = CommRingOps.zero)) = rest := by
            apply List.filter_eq_self.mpr
            intro y hy
            have hyInFilt : y ∈ S.filter p := by
              rw [hRoots]; exact .tail _ hy
            have hyRoot : RoundPoly.evalCoeffs cs y = CommRingOps.zero :=
              of_decide_eq_true (pred_of_mem_filter_spn (p := p) hyInFilt)
            have hSubNe : CommRingOps.sub y r ≠ CommRingOps.zero :=
              fun hsub0 => hNotMem y hy (LawfulCommRing.sub_eq_zero_iff.mp hsub0).symm
            have hfac := RoundPoly.evalCoeffs_eq_mul_quotLinear_add cs r y
            rw [hyRoot, hrRoot, LawfulCommRing.add_zero, hQuotEq] at hfac
            exact (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hfac.symm).elim
              (fun hb => False.elim (hSubNe hb)) decide_eq_true
          have ih := evalCoeffs_roots_le_of_lead_nonzero d init' lead rest
            (hLen'.trans (Nat.succ.inj hLen)) hLead hndRest
          rw [hRestEq] at ih
          change (S.filter p).length ≤ d + 1
          rw [hRoots]; simp only [List.length_cons]; omega


end Qsag

namespace Qsag
set_option autoImplicit false
open RoundPoly

open RoundPoly

/-- A formally nonzero coefficient list remains nonzero after synthetic division by a root.
    This uses coefficients rather than a nonzero evaluation, so it also works over finite fields. -/
private theorem gs_all_zero_of_quotLinear {R : Type} [LawfulCommRing R] :
    ∀ (cs : List R) (r : R),
    (∀ c ∈ quotLinear cs r, c = CommRingOps.zero) →
    evalCoeffs cs r = CommRingOps.zero → ∀ c ∈ cs, c = CommRingOps.zero
  | [], _, _, _, _, hc => by cases hc
  | [a], r, _, he, c, hc => by
    have ha : a = CommRingOps.zero := by
      simpa only [evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero] using he
    exact (List.mem_singleton.mp hc).trans ha
  | a :: b :: bs, r, hq, he, c, hc => by
    have ht : evalCoeffs (b :: bs) r = CommRingOps.zero := hq _ (.head _)
    have htail := gs_all_zero_of_quotLinear (b :: bs) r
      (fun x hx => hq x (.tail _ hx)) ht
    have ha : a = CommRingOps.zero := by
      change CommRingOps.add a (CommRingOps.mul r (evalCoeffs (b :: bs) r)) = _ at he
      simpa only [ht, LawfulCommRing.mul_zero, LawfulCommRing.add_zero] using he
    cases hc with
    | head => exact ha
    | tail _ h => exact htail c h

/-- Formal root bound over any decidable integral domain. Unlike an evaluation-based nonzero
    premise, the nonzero-coefficient premise covers polynomials such as `X^q-X` over `F_q`. -/
theorem gs_formal_root_bound {R : Type} [LawfulCommRing R] [DecidableEq R] [NoZeroDivisors R] :
    ∀ (d : Nat) (cs : List R) (roots : List R),
    cs.length ≤ d + 1 → (∃ c ∈ cs, c ≠ CommRingOps.zero) →
    roots.Nodup → (∀ r ∈ roots, evalCoeffs cs r = CommRingOps.zero) → roots.length ≤ d
  | _, _, [], _, _, _, _ => Nat.zero_le _
  | 0, cs, r :: rs, hlen, hnz, _, hr => by
    cases cs with
    | nil => obtain ⟨c, hc, _⟩ := hnz; cases hc
    | cons c cs =>
      have ht : cs = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hlen; omega)
      subst cs
      have he := hr r (.head _)
      have hz : c = CommRingOps.zero := by
        simpa only [evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero] using he
      obtain ⟨a, ha, hne⟩ := hnz
      exact False.elim (hne ((List.mem_singleton.mp ha).trans hz))
  | d + 1, cs, r :: rs, hlen, hnz, hnd, hr => by
    have hroot := hr r (.head _)
    have hqnz : ∃ c ∈ quotLinear cs r, c ≠ CommRingOps.zero := by
      cases htest : (quotLinear cs r).any (fun c => decide (c ≠ CommRingOps.zero)) with
      | true =>
        obtain ⟨c, hc, he⟩ := List.any_eq_true.mp htest
        exact ⟨c, hc, of_decide_eq_true he⟩
      | false =>
        have hzero : ∀ c ∈ quotLinear cs r, c = CommRingOps.zero := by
          intro c hc
          have he := List.any_eq_false.mp htest c hc
          simpa only [decide_eq_true_eq, Decidable.not_not] using he
        obtain ⟨c, hc, hne⟩ := hnz
        exact False.elim (hne (gs_all_zero_of_quotLinear cs r hzero hroot c hc))
    have hrest : ∀ x ∈ rs, evalCoeffs (quotLinear cs r) x = CommRingOps.zero := by
      intro x hx
      have hfac := evalCoeffs_eq_mul_quotLinear_add cs r x
      rw [hr x (.tail _ hx), hroot, LawfulCommRing.add_zero] at hfac
      cases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hfac.symm with
      | inl hsub =>
        have heq := LawfulCommRing.sub_eq_zero_iff.mp hsub
        exact False.elim ((List.pairwise_cons.mp hnd).1 x hx heq.symm)
      | inr hq => exact hq
    have ih := gs_formal_root_bound d (quotLinear cs r) rs
      (by rw [quotLinear_length]; omega) hqnz (List.pairwise_cons.mp hnd).2 hrest
    simpa only [List.length_cons] using Nat.succ_le_succ ih


end Qsag

namespace Qsag
open CommRingOps
open RoundPoly
theorem pMul_nil_left_eq {R : Type} [CommRingOps R] [DecidableEq R] (cs : List R) : pMul [] cs = [] := by rfl
end Qsag

namespace Qsag
 theorem isTrimmed_iff {F : Type} [CommRingOps F] [DecidableEq F] (p : List F) : IsTrimmed p ↔ trimPoly p = p := by rfl
 theorem dvdTrim_iff {F : Type} [CommRingOps F] [DecidableEq F] (d a : List F) : DvdTrim d a ↔ ∃ k, trimPoly a = pMul d k := by rfl
 theorem isTrimmed_trimPoly {F : Type} [CommRingOps F] [DecidableEq F] (p : List F) : IsTrimmed (trimPoly p) := trimPoly_idem p
 theorem isTrimmed_pAdd {F : Type} [CommRingOps F] [DecidableEq F] (a b : List F) : IsTrimmed (pAdd a b) := trimPoly_idem _
 theorem isTrimmed_pScale {F : Type} [CommRingOps F] [DecidableEq F] (c : F) (a : List F) : IsTrimmed (pScale c a) := trimPoly_idem _
 theorem trimPoly_zero_singleton {F : Type} [CommRingOps F] [DecidableEq F] : trimPoly [(CommRingOps.zero : F)] = [] := by simp [trimPoly]
end Qsag

namespace Qsag
open CommRingOps
@[simp] theorem dotVec_nil_left {F : Type} [CommRingOps F] (xs : List F) : dotVec [] xs = zero := by cases xs <;> rfl
@[simp] theorem dotVec_nil_right {F : Type} [CommRingOps F] (xs : List F) : dotVec xs [] = zero := by cases xs <;> rfl
@[simp] theorem dotVec_cons {F : Type} [CommRingOps F] (a b : F) (as bs : List F) :
  dotVec (a :: as) (b :: bs) = add (mul a b) (dotVec as bs) := by rfl
end Qsag

namespace Qsag
 theorem trimPoly_nil_eq {F : Type} [CommRingOps F] [DecidableEq F] : trimPoly ([] : List F) = [] := by rfl
 theorem pAdd_eq {F : Type} [CommRingOps F] [DecidableEq F] (a b : List F) : pAdd a b = trimPoly (rawAddCoeffs a b) := by rfl
 theorem pScale_eq {F : Type} [CommRingOps F] [DecidableEq F] (c : F) (a : List F) : pScale c a = trimPoly (a.map (CommRingOps.mul c)) := by rfl
end Qsag

namespace Qsag
namespace RoundPoly

theorem evalCoeffs_map_mul {R : Type} [LawfulCommRing R] (s : R) (cs : List R) (x : R) :
    evalCoeffs (cs.map (CommRingOps.mul s)) x = CommRingOps.mul s (evalCoeffs cs x) :=
  Qsag.evalCoeffs_map_mul s x cs

/-- Coefficients of `(X - s) · cs`. -/
def mulLinear {R : Type} [CommRingOps R] (s : R) (cs : List R) : List R :=
  subCoeffs (CommRingOps.zero :: cs) (cs.map (CommRingOps.mul s))

theorem evalCoeffs_mulLinear {R : Type} [LawfulCommRing R] (s : R) (cs : List R) (x : R) :
    evalCoeffs (mulLinear s cs) x = CommRingOps.mul (CommRingOps.sub x s) (evalCoeffs cs x) := by
  unfold mulLinear
  rw [evalCoeffs_sub, evalCoeffs_cons, evalCoeffs_map_mul, LawfulCommRing.zero_add,
      LawfulCommRing.sub_mul]

theorem mulLinear_length {R : Type} [CommRingOps R] (s : R) (cs : List R) :
    (mulLinear s cs).length = cs.length + 1 := by
  unfold mulLinear
  rw [subCoeffs_length]
  simp only [List.length_cons, List.length_map]
  exact Nat.max_eq_left (Nat.le_succ _)

/-- Coefficients of the vanishing polynomial `∏_{s ∈ S} (X - s)`. -/
def vanishingCoeffs {R : Type} [CommRingOps R] : List R → List R := vanishingPoly

theorem vanishingCoeffs_length {R : Type} [CommRingOps R] (S : List R) :
    (vanishingCoeffs S).length = S.length + 1 := vanishingPoly_length S

theorem evalCoeffs_vanishingCoeffs_of_mem {R : Type} [LawfulCommRing R]
    (S : List R) (x : R) (h : x ∈ S) : evalCoeffs (vanishingCoeffs S) x = CommRingOps.zero :=
  eval_vanishingPoly_eq_zero_of_mem h

theorem evalCoeffs_vanishingCoeffs_ne_zero {R : Type} [LawfulCommRing R] [NoZeroDivisors R]
    (hOne : (CommRingOps.one : R) ≠ CommRingOps.zero) :
    ∀ (S : List R) (x : R), x ∉ S → evalCoeffs (vanishingCoeffs S) x ≠ CommRingOps.zero
  | [], x, _ => by
    simp only [vanishingCoeffs, vanishingPoly, evalCoeffs_cons, evalCoeffs_nil]
    rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    exact hOne
  | s :: rest, x, h => by
    change evalCoeffs (mulLinear s (vanishingCoeffs rest)) x ≠ CommRingOps.zero
    rw [evalCoeffs_mulLinear]
    intro hz
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hz with hx | hv
    · exact h (List.mem_cons.mpr (.inl (LawfulCommRing.sub_eq_zero_iff.mp hx)))
    · exact evalCoeffs_vanishingCoeffs_ne_zero hOne rest x
        (fun hm => h (List.mem_cons.mpr (.inr hm))) hv

end RoundPoly
end Qsag

namespace Qsag
/-- Compatibility spelling for the canonical coefficient pairing. -/
abbrev ringDot {R : Type} [CommRingOps R] : List R → List R → R := dotVec
/-- Compatibility spelling for the canonical natural power. -/
def ringPow {R : Type} [CommRingOps R] (x : R) : Nat → R := CRing.npow x

private def evalShifted {R : Type} [CommRingOps R] : List R → Nat → R → R
  | [], _, _ => CommRingOps.zero
  | c :: cs, shift, x => CommRingOps.add (CommRingOps.mul c (CRing.npow x shift)) (evalShifted cs (shift + 1) x)

private theorem evalShifted_eq_mul_pow {R : Type} [LawfulCommRing R] :
    ∀ (cs : List R) (shift : Nat) (x : R),
      evalShifted cs shift x = CommRingOps.mul (CRing.npow x shift) (RoundPoly.evalCoeffs cs x)
  | [], shift, x => by simp [evalShifted, LawfulCommRing.mul_zero]
  | c :: cs, shift, x => by
    simp only [evalShifted, RoundPoly.evalCoeffs_cons, evalShifted_eq_mul_pow cs (shift + 1) x, CRing.npow]
    rw [LawfulCommRing.mul_comm c (CRing.npow x shift), LawfulCommRing.mul_assoc (CRing.npow x shift) x _,
        ← LawfulCommRing.left_distrib]

private theorem ringDot_map_zero {R : Type} [LawfulCommRing R] :
    ∀ (ls pts : List R), dotVec ls (pts.map (fun _ => CommRingOps.zero)) = CommRingOps.zero
  | [], _ => by simp [dotVec]
  | _ :: _, [] => by simp
  | _ :: ls, _ :: ps => by
    simp only [List.map_cons, dotVec, LawfulCommRing.mul_zero, ringDot_map_zero ls ps, LawfulCommRing.zero_add]

private theorem ringDot_map_add {R : Type} [LawfulCommRing R] (f g : R → R) :
    ∀ (ls pts : List R),
      dotVec ls (pts.map (fun x => CommRingOps.add (f x) (g x))) =
        CommRingOps.add (dotVec ls (pts.map f)) (dotVec ls (pts.map g))
  | [], _ => by simp [dotVec, LawfulCommRing.add_zero]
  | _, [] => by simp [LawfulCommRing.add_zero]
  | _ :: ls, _ :: ps => by
    simp only [List.map_cons, dotVec, ringDot_map_add f g ls ps,
               LawfulCommRing.left_distrib, LawfulCommRing.add_add_add_comm]

private theorem ringDot_map_scale {R : Type} [LawfulCommRing R] (c : R) (f : R → R) :
    ∀ (ls pts : List R),
      dotVec ls (pts.map (fun x => CommRingOps.mul c (f x))) =
        CommRingOps.mul c (dotVec ls (pts.map f))
  | [], _ => by simp [dotVec, LawfulCommRing.mul_zero]
  | _, [] => by simp [LawfulCommRing.mul_zero]
  | l :: ls, p :: ps => by
    simp only [List.map_cons, dotVec, ringDot_map_scale c f ls ps]
    have hSwap : CommRingOps.mul l (CommRingOps.mul c (f p)) = CommRingOps.mul c (CommRingOps.mul l (f p)) := by
      rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm l c, LawfulCommRing.mul_assoc]
    rw [hSwap, ← LawfulCommRing.left_distrib]

private theorem ringDot_evalShifted_tail_zero {R : Type} [LawfulCommRing R]
    (lambdas pts : List R) (t : Nat)
    (hHigher : ∀ d, 1 ≤ d → d < t → dotVec lambdas (pts.map (fun x => CRing.npow x d)) = CommRingOps.zero) :
    ∀ (cs : List R) (shift : Nat),
      1 ≤ shift → shift + cs.length ≤ t →
      dotVec lambdas (pts.map (fun x => evalShifted cs shift x)) = CommRingOps.zero
  | [], _, _, _ => ringDot_map_zero lambdas pts
  | _ :: cs, shift, hGe1, hBound => by
    simp only [List.length_cons] at hBound
    simp only [evalShifted]
    rw [ringDot_map_add, ringDot_map_scale, hHigher shift hGe1 (by omega),
        LawfulCommRing.mul_zero, LawfulCommRing.zero_add]
    exact ringDot_evalShifted_tail_zero lambdas pts t hHigher cs (shift + 1) (by omega) (by omega)

/-- **Polymorphic Vandermonde / Lagrange-at-Zero Reconstruction (`lagrangeAtZero_evalCoeffs`)**. -/
theorem lagrangeAtZero_evalCoeffs {R : Type} [LawfulCommRing R]
    (lambdas pts coeffs : List R) (t : Nat)
    (hLen : coeffs.length ≤ t)
    (hZero : dotVec lambdas (pts.map (fun _ => CommRingOps.one)) = CommRingOps.one)
    (hHigher : ∀ d, 1 ≤ d → d < t → dotVec lambdas (pts.map (fun x => CRing.npow x d)) = CommRingOps.zero) :
    dotVec lambdas (pts.map (fun x => RoundPoly.evalCoeffs coeffs x)) =
      RoundPoly.evalCoeffs coeffs CommRingOps.zero := by
  have hToShift : ∀ x : R, RoundPoly.evalCoeffs coeffs x = evalShifted coeffs 0 x := by
    intro x
    rw [evalShifted_eq_mul_pow coeffs 0 x, CRing.npow, LawfulCommRing.one_mul]
  have hMapEq : pts.map (fun x => RoundPoly.evalCoeffs coeffs x) =
      pts.map (fun x => evalShifted coeffs 0 x) := List.map_congr_left (fun x _ => hToShift x)
  rw [hMapEq]
  cases coeffs with
  | nil => exact ringDot_map_zero lambdas pts
  | cons c0 rest =>
    simp only [List.length_cons] at hLen
    simp only [evalShifted, CRing.npow, RoundPoly.evalCoeffs_cons, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
    rw [ringDot_map_add, ringDot_map_scale, hZero, LawfulCommRing.mul_one,
        ringDot_evalShifted_tail_zero lambdas pts t hHigher rest 1 (by omega) (by omega),
        LawfulCommRing.add_zero]

theorem ringDot_eq {R : Type} [CommRingOps R] (a b : List R) : ringDot a b = dotVec a b := by unfold ringDot; rfl
theorem ringPow_eq {R : Type} [CommRingOps R] (x : R) (n : Nat) : ringPow x n = CRing.npow x n := by unfold ringPow; rfl
end Qsag

namespace Qsag
open RoundPoly
/-- Constructive Newton polynomial interpolation over `[LawfulField F]` (`0` `Classical.choice`).
    On any `Nodup` list `pts`, returns a canonical trimmed polynomial of length `≤ pts.length`
    matching `word` at every `x ∈ pts`. -/
def newtonInterp {F : Type} [LawfulField F] [DecidableEq F] (word : F → F) : List F → List F
  | [] => []
  | x₀ :: xs =>
    let P₀ := newtonInterp word xs
    let V := vanishingPoly xs
    let c := CommRingOps.mul (CommRingOps.sub (word x₀) (RoundPoly.evalCoeffs P₀ x₀))
      (LawfulField.inv (RoundPoly.evalCoeffs V x₀))
    pAdd P₀ (pScale c V)

theorem newtonInterp_trimmed {F : Type} [LawfulField F] [DecidableEq F] (word : F → F) :
    ∀ (pts : List F), IsTrimmed (newtonInterp word pts)
  | [] => rfl
  | _ :: _ => trimPoly_idem _

theorem newtonInterp_length_le {F : Type} [LawfulField F] [DecidableEq F] (word : F → F) :
    ∀ (pts : List F), (newtonInterp word pts).length ≤ pts.length
  | [] => Nat.le_refl 0
  | _ :: xs => by
    unfold newtonInterp
    apply pAdd_length_le
    · exact Nat.le_trans (newtonInterp_length_le word xs) (Nat.le_succ xs.length)
    · unfold pScale
      exact Nat.le_trans (trimPoly_length_le _)
        (by rw [List.length_map, vanishingPoly_length, List.length_cons]; exact Nat.le_refl _)

theorem evalCoeffs_newtonInterp {F : Type} [LawfulField F] [DecidableEq F] (word : F → F) :
    ∀ {pts : List F}, pts.Nodup →
      ∀ x ∈ pts, RoundPoly.evalCoeffs (newtonInterp word pts) x = word x
  | [], _, _, hx => by cases hx
  | x₀ :: xs, hnd, x, hx => by
    rcases hnd with _ | ⟨hnot, hnd'⟩
    unfold newtonInterp
    rw [evalCoeffs_pAdd, evalCoeffs_pScale]
    cases hx with
    | head =>
      have hVne : RoundPoly.evalCoeffs (vanishingPoly xs) x₀ ≠ CommRingOps.zero :=
        eval_vanishingPoly_ne_zero_of_not_mem (fun hm => hnot x₀ hm rfl)
      rw [LawfulCommRing.mul_assoc,
          LawfulCommRing.mul_comm (LawfulField.inv (RoundPoly.evalCoeffs (vanishingPoly xs) x₀)) _,
          LawfulField.mul_inv_cancel hVne,
          LawfulCommRing.mul_one,
          LawfulCommRing.add_sub_cancel_left]
    | tail _ hm =>
      rw [eval_vanishingPoly_eq_zero_of_mem hm, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
      exact evalCoeffs_newtonInterp word hnd' x hm


private theorem pSub_length_le {F : Type} [LawfulCommRing F] [DecidableEq F]
    (a b : List F) (B : Nat) (ha : a.length ≤ B) (hb : b.length ≤ B) :
    (pSub a b).length ≤ B := by
  apply length_trimPoly_le_of_coeffAt_zero _ B
  intro k hk
  rw [coeffAt_subCoeffs, coeffAt_eq_zero_of_ge a k (by omega),
      coeffAt_eq_zero_of_ge b k (by omega), LawfulCommRing.sub_self]

/-- Any two distinct canonical degree-`≤ d` polynomials disagree on at least one point of any
    `Nodup` set `U` of size `≥ d + 1` (`0` `Classical.choice`). -/
theorem gsUniPoly_exists_diff_on_domain {F : Type} [LawfulField F] [DecidableEq F]
    {P₁ P₂ : GsUniPoly F} {d : Nat} {U : List F}
    (hNe : P₁ ≠ P₂) (hDeg₁ : P₁.coeffs.length ≤ d + 1) (hDeg₂ : P₂.coeffs.length ≤ d + 1)
    (hU : U.Nodup) (hULen : d + 1 ≤ U.length) :
    ∃ x₀ ∈ U, RoundPoly.evalCoeffs P₁.coeffs x₀ ≠ RoundPoly.evalCoeffs P₂.coeffs x₀ := by
  have hSubNe : pSub P₁.coeffs P₂.coeffs ≠ [] := by
    intro hNil
    apply hNe
    apply UPoly.ext
    apply eq_of_isTrimmed_coeffAt P₁.coeffs P₂.coeffs P₁.trimmed P₂.trimmed
    intro k
    have hk : coeffAt (pSub P₁.coeffs P₂.coeffs) k = CommRingOps.zero := by
      rw [hNil]; exact coeffAt_nil k
    rw [coeffAt_pSub] at hk
    exact LawfulCommRing.sub_eq_zero_iff.mp hk
  have hSubLen : (pSub P₁.coeffs P₂.coeffs).length ≤ U.length :=
    Nat.le_trans (pSub_length_le P₁.coeffs P₂.coeffs (d + 1) hDeg₁ hDeg₂) hULen
  rcases exists_nonroot_of_trim_ne_nil (trimPoly_idem _) hSubNe hU hSubLen with ⟨x₀, hx₀U, hx₀Ne⟩
  refine ⟨x₀, hx₀U, fun hEq => hx₀Ne ?_⟩
  change RoundPoly.evalCoeffs (pSub P₁.coeffs P₂.coeffs) x₀ = CommRingOps.zero
  rw [evalCoeffs_pSub, hEq, LawfulCommRing.sub_self]


theorem pMul_linear_eq {F : Type} [LawfulCommRing F] [DecidableEq F] : ∀ (α β : F) (w : List F),
    pMul [α, β] w = pAdd (pScale α w) (pScale β (CommRingOps.zero :: w)) := by
  intro α β w
  have hz1 : ∀ m, coeffAt ([CommRingOps.zero] : List F) m = CommRingOps.zero := by
    intro m; cases m <;> rfl
  unfold pMul pAdd pScale
  rw [trimPoly_eq_iff_coeffAt]
  intro k
  rw [coeffAt_addCoeffs, coeffAt_trimPoly, coeffAt_trimPoly, coeffAt_map_mul, coeffAt_map_mul]
  simp only [rawMul, coeffAt_addCoeffs, coeffAt_map_mul]
  cases k with
  | zero => simp only [coeffAt_cons_zero, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | succ k' =>
    simp only [coeffAt_cons_succ, coeffAt_addCoeffs, coeffAt_map_mul, hz1,
               LawfulCommRing.add_zero]

theorem pMul_singleton_eq {F : Type} [LawfulCommRing F] [DecidableEq F] (c : F) : ∀ w, pMul [c] w = pScale c w := by
  intro w; unfold pMul pScale; rw [trimPoly_eq_iff_coeffAt]; intro k
  simp only [rawMul, coeffAt_addCoeffs, coeffAt_map_mul]
  cases k with
  | zero => simp only [coeffAt_cons_zero, LawfulCommRing.add_zero]
  | succ _ => simp only [coeffAt_cons_succ, coeffAt_nil, LawfulCommRing.add_zero]

end Qsag

namespace Qsag
 theorem GsUniPoly.ofCoeffs_coeffs_of_trimmed {F : Type} [LawfulField F] [DecidableEq F] (cs : List F) (h : IsTrimmed cs) : (GsUniPoly.ofCoeffs cs).coeffs = cs := h
end Qsag

namespace Qsag
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
    exact congrArg UPoly.coeffs hEq
  else
    have hpDeg : pG.coeffs.length ≤ d + 1 := Nat.le_trans (trimPoly_length_le P) hP
    have hqDeg : qG.coeffs.length ≤ d + 1 := Nat.le_trans (trimPoly_length_le Q) hQ
    rcases gsUniPoly_exists_diff_on_domain hEq hpDeg hqDeg hU hULen with ⟨x₀, hx₀U, hDiff⟩
    exfalso
    apply hDiff
    change RoundPoly.evalCoeffs (trimPoly P) x₀ = RoundPoly.evalCoeffs (trimPoly Q) x₀
    rw [evalCoeffs_trimPoly, evalCoeffs_trimPoly]
    exact hAgree x₀ hx₀U

theorem filter_overlap_len {α : Type} (p q : α → Bool) :
    ∀ (D : List α),
      (D.filter p).length + (D.filter q).length ≤
        D.length + (D.filter (fun z => p z && q z)).length
  | [] => Nat.le_refl 0
  | a :: ds => by
    have ih := filter_overlap_len p q ds
    cases hp : p a <;> cases hq : q a <;>
      simp only [List.filter_cons, hp, hq, Bool.and_self, Bool.and_false, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega


end Qsag

-- Owning-module audit certificates for theorems audited and paired in `Tests/MathAndCoding`.
#verify_constructive
  Qsag.UPoly.natDeg_mul

-- Kernel-checked defining equations for the executed controls in `Tests/MathAndCoding` (no body is exposed).
#export_eqns Qsag.UPoly.lead
#export_eqns Qsag.RoundPoly.eval
#export_eqns Qsag.monomial
#export_eqns Qsag.solveHomogeneous
#export_eqns Qsag.insertIdxVal
#export_eqns Qsag.subVec
#export_eqns Qsag.dropIdx
#export_eqns Qsag.scaleVec
#export_eqns Qsag.RoundPoly.subCoeffs
#export_eqns Qsag.vanishingPoly

-- Kernel-checked defining equations for the executed controls in `Tests/MathAndCoding` (no body is exposed).
#export_eqns Qsag.pSub
#export_eqns Qsag.pAdd
#export_eqns Qsag.pNeg
#export_eqns Qsag.rawNegCoeffs
#export_eqns Qsag.findNonzeroIdx
