module
public import Qsag.Spec.Algebra
public import Qsag.Tactic.Prelude
public import Qsag.Tactic.CommRing

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
def quotLinear {R : Type} [CommRingOps R] : List R → R → List R
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
def prodPool {α : Type} (S : List α) : List (α × α) :=
  S.flatMap (fun a => S.map (fun b => (a, b)))

theorem prodPool_length {α : Type} (S : List α) :
    (prodPool S).length = S.length * S.length := by
  unfold prodPool
  have hrec : ∀ (xs B : List α),
      (xs.flatMap (fun x => B.map (fun b => (x, b)))).length = xs.length * B.length := by
    intro xs B
    induction xs with
    | nil => simp
    | cons _ rest ihr =>
      simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons]
      rw [ihr, Nat.add_mul, Nat.one_mul, Nat.add_comm]
  exact hrec S S

theorem mem_prodPool_iff {α : Type} {S : List α} {p : α × α} :
    p ∈ prodPool S ↔ p.1 ∈ S ∧ p.2 ∈ S := by
  rcases p with ⟨a, b⟩
  unfold prodPool
  simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨a', ha', b', hb', rfl, rfl⟩
    exact ⟨ha', hb'⟩
  · rintro ⟨ha, hb⟩
    exact ⟨a, ha, b, hb, rfl, rfl⟩

private theorem nodup_map_pair_right {α : Type} (a : α) :
    ∀ {S : List α}, S.Nodup → (S.map (fun b => (a, b))).Nodup
  | [], _ => .nil
  | b :: bs, .cons hnot hnd => by
    simp only [List.map]
    refine .cons ?_ (nodup_map_pair_right a hnd)
    intro p hp heq
    rw [List.mem_map] at hp
    rcases hp with ⟨b', hb', rfl⟩
    cases heq
    exact hnot b hb' rfl

private theorem nodup_flatMap_pairs {α : Type} (B : List α) (hB : B.Nodup) :
    ∀ {A : List α}, A.Nodup → (A.flatMap (fun a => B.map (fun b => (a, b)))).Nodup
  | [], _ => .nil
  | a :: as, .cons hnot hnd => by
    simp only [List.flatMap_cons]
    rw [List.nodup_append]
    refine ⟨nodup_map_pair_right a hB, nodup_flatMap_pairs B hB hnd, ?_⟩
    intro p₁ hp₁ p₂ hp₂ heq
    subst heq
    rw [List.mem_map] at hp₁
    rw [List.mem_flatMap] at hp₂
    rcases hp₁ with ⟨b₁, _, rfl⟩
    rcases hp₂ with ⟨a₂, ha₂, hp₂'⟩
    rw [List.mem_map] at hp₂'
    rcases hp₂' with ⟨b₂, _, heq'⟩
    cases heq'
    exact hnot a ha₂ rfl

theorem prodPool_nodup {α : Type} {S : List α} (hS : S.Nodup) :
    (prodPool S).Nodup :=
  nodup_flatMap_pairs S hS hS

/-- Constructive first-occurrence erasure for proving `Nodup` subset length bounds (`0` choice). -/
def eraseFirst {α : Type} [DecidableEq α] (x : α) : List α → List α
  | [] => []
  | y :: ys => if x = y then ys else y :: eraseFirst x ys

theorem eraseFirst_length_of_mem {α : Type} [DecidableEq α] {x : α} :
    ∀ {M : List α}, x ∈ M → (eraseFirst x M).length + 1 = M.length
  | [], h => by cases h
  | y :: ys, h => by
    unfold eraseFirst
    if hxy : x = y then
      simp [hxy]
    else
      simp only [hxy, ↓reduceIte, List.length_cons]
      cases h with
      | head => exact False.elim (hxy rfl)
      | tail _ hm =>
        have ih := eraseFirst_length_of_mem hm
        omega

theorem mem_eraseFirst_of_ne {α : Type} [DecidableEq α] {x z : α} (hne : z ≠ x) :
    ∀ {M : List α}, z ∈ M → z ∈ eraseFirst x M
  | [], h => by cases h
  | y :: ys, h => by
    unfold eraseFirst
    if hxy : x = y then
      simp only [hxy, ↓reduceIte]
      subst hxy
      cases h with
      | head => exact False.elim (hne rfl)
      | tail _ hm => exact hm
    else
      simp only [hxy, ↓reduceIte]
      cases h with
      | head => exact .head _
      | tail _ hm => exact .tail _ (mem_eraseFirst_of_ne hne hm)

/-- Constructive Pigeonhole / Subset-Length Lemma: any `Nodup` list `L` contained in `M` satisfies
    `L.length ≤ M.length` (`0` classical axioms). -/
theorem nodup_length_le_of_subset {α : Type} [DecidableEq α] :
    ∀ {L M : List α}, L.Nodup → (∀ x ∈ L, x ∈ M) → L.length ≤ M.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, M, .cons hnot hnd, hsub => by
    have hxM : x ∈ M := hsub x (.head _)
    have hlen := eraseFirst_length_of_mem hxM
    have hsub' : ∀ z ∈ xs, z ∈ eraseFirst x M := by
      intro z hz
      have hne : z ≠ x := fun heq => hnot z hz heq.symm
      exact mem_eraseFirst_of_ne hne (hsub z (.tail _ hz))
    have ih := nodup_length_le_of_subset hnd hsub'
    simp only [List.length_cons]
    omega

theorem filter_eq_max_one_of_nodup {α : Type} [DecidableEq α] (target : α) :
    ∀ {S : List α}, S.Nodup → (S.filter (fun x => decide (x = target))).length ≤ 1
  | [], _ => by simp
  | x :: xs, .cons hnot hnd => by
    simp only [List.filter]
    if hx : x = target then
      subst hx
      simp only [decide_true, List.length_cons]
      have hempty : xs.filter (fun y => decide (y = x)) = [] := by
        induction xs with
        | nil => rfl
        | cons y ys ih =>
          have hyne : y ≠ x := fun heq => hnot y (.head _) heq.symm
          have hnd' : ys.Nodup := by
            cases hnd with | cons _ t => exact t
          simp [List.filter, hyne, ih (fun z hz => hnot z (.tail _ hz)) hnd']
      rw [hempty]
      simp
    else
      simp only [hx, decide_false]
      exact filter_eq_max_one_of_nodup target hnd

theorem filter_sub_length_le {α : Type} (p q : α → Bool) (hpq : ∀ x, p x = true → q x = true) :
    ∀ (xs : List α), (xs.filter p).length ≤ (xs.filter q).length
  | [] => Nat.le_refl 0
  | x :: xs => by
    have ih := filter_sub_length_le p q hpq xs
    simp only [List.filter]
    cases hpx : p x
    · cases hqx : q x <;> simp <;> omega
    · rw [hpq x hpx]
      simp only [List.length_cons]
      exact Nat.succ_le_succ ih

theorem flatMap_filter_length_le {α β : Type} (f : α → List β) (p : β → Bool) (B : Nat) :
    ∀ {xs : List α}, (∀ x ∈ xs, ((f x).filter p).length ≤ B) →
      ((xs.flatMap f).filter p).length ≤ xs.length * B
  | [], _ => by simp
  | x :: xs, hB => by
    rw [List.flatMap_cons, List.filter_append, List.length_append, List.length_cons]
    have hx := hB x (.head _)
    have htl := flatMap_filter_length_le f p B (fun y hy => hB y (.tail _ hy))
    have hmul : (xs.length + 1) * B = B + xs.length * B := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    rw [hmul]
    exact Nat.add_le_add hx htl
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
def gsUniHasse {R : Type} [CommRingOps R] : List R → Nat → R → R
  | [], _, _ => CommRingOps.zero
  | c :: cs, 0, b => CommRingOps.add c (CommRingOps.mul b (gsUniHasse cs 0 b))
  | _ :: cs, k + 1, b =>
    CommRingOps.add (gsUniHasse cs k b) (CommRingOps.mul b (gsUniHasse cs (k + 1) b))


open RoundPoly
/-! ## §3. Constructive Homogeneous Linear Solver (`gauss_nullspace_witness`) -/

/-- Dot product of two `List F` vectors over `CommRingOps F`. -/
def dotVec {F : Type} [CommRingOps F] : List F → List F → F
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
def coeffAt {F : Type} [CommRingOps F] (p : List F) (k : Nat) : F :=
  p.getD k CommRingOps.zero

/-- Strip trailing zeros so every non-empty canonical polynomial has a non-zero leading coefficient. -/
def trimPoly {F : Type} [CommRingOps F] [DecidableEq F] : List F → List F
  | [] => []
  | c :: cs =>
    let cs' := trimPoly cs
    if cs' = [] ∧ c = CommRingOps.zero then [] else c :: cs'

/-- Canonical trimmedness predicate. -/
def IsTrimmed {F : Type} [CommRingOps F] [DecidableEq F] (p : List F) : Prop :=
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
def rawAddCoeffs {F : Type} [CommRingOps F] : List F → List F → List F
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

def rawMul {F : Type} [CommRingOps F] : List F → List F → List F
  | [], _ => []
  | c :: cs, b => rawAddCoeffs (b.map (CommRingOps.mul c)) (CommRingOps.zero :: rawMul cs b)

def pMul {F : Type} [CommRingOps F] [DecidableEq F] (a b : List F) : List F :=
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
def ofList (l : List R) : UPoly R := ⟨trimPoly l, trimPoly_idem l⟩

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

/-! ## Ring homomorphisms and evaluation -/

/-- Ring homomorphisms between the project's ring structures. -/
structure RingHom (R S : Type) [CommRingOps R] [CommRingOps S] where
  toFun : R → S
  map_zero : toFun zero = zero
  map_one : toFun one = one
  map_add : ∀ a b, toFun (add a b) = add (toFun a) (toFun b)
  map_mul : ∀ a b, toFun (mul a b) = mul (toFun a) (toFun b)

namespace RingHom
variable {R S T : Type} [LawfulCommRing R] [LawfulCommRing S] [LawfulCommRing T]

theorem map_neg (φ : RingHom R S) (a : R) : φ.toFun (neg a) = neg (φ.toFun a) := by
  apply LawfulCommRing.add_left_cancel (a := φ.toFun a)
  rw [← φ.map_add, LawfulCommRing.add_right_neg, LawfulCommRing.add_right_neg, φ.map_zero]

theorem map_sub (φ : RingHom R S) (a b : R) :
    φ.toFun (sub a b) = sub (φ.toFun a) (φ.toFun b) := by
  rw [LawfulCommRing.sub_eq_add_neg, φ.map_add, φ.map_neg, ← LawfulCommRing.sub_eq_add_neg]

/-- The identity homomorphism. -/
def id (R : Type) [CommRingOps R] : RingHom R R :=
  ⟨fun a => a, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem id_apply (a : R) : (RingHom.id R).toFun a = a := by rfl

/-- Composition `ψ ∘ φ`. -/
def comp (ψ : RingHom S T) (φ : RingHom R S) : RingHom R T where
  toFun a := ψ.toFun (φ.toFun a)
  map_zero := by rw [φ.map_zero, ψ.map_zero]
  map_one := by rw [φ.map_one, ψ.map_one]
  map_add a b := by rw [φ.map_add, ψ.map_add]
  map_mul a b := by rw [φ.map_mul, ψ.map_mul]

theorem comp_apply (ψ : RingHom S T) (φ : RingHom R S) (a : R) :
    (ψ.comp φ).toFun a = ψ.toFun (φ.toFun a) := by rfl

theorem coeffAt_map (φ : RingHom R S) :
    ∀ (l : List R) (k : Nat), coeffAt (l.map φ.toFun) k = φ.toFun (coeffAt l k)
  | [], k => by rw [List.map_nil, coeffAt_nil, coeffAt_nil, φ.map_zero]
  | _ :: _, 0 => by rfl
  | _ :: cs, k + 1 => by
    rw [List.map_cons, coeffAt_cons_succ, coeffAt_cons_succ, coeffAt_map φ cs k]

theorem map_rawAdd (φ : RingHom R S) :
    ∀ a b : List R, (rawAddCoeffs a b).map φ.toFun =
      rawAddCoeffs (a.map φ.toFun) (b.map φ.toFun)
  | [], b => by simp [rawAddCoeffs]
  | c :: cs, [] => by simp [rawAddCoeffs]
  | c :: cs, d :: ds => by simp [rawAddCoeffs, φ.map_add, map_rawAdd φ cs ds]

theorem map_rawMul (φ : RingHom R S) :
    ∀ a b : List R, (rawMul a b).map φ.toFun = rawMul (a.map φ.toFun) (b.map φ.toFun)
  | [], _ => by rfl
  | c :: cs, b => by
    show (rawAddCoeffs (b.map (mul c)) (zero :: rawMul cs b)).map φ.toFun =
      rawAddCoeffs ((b.map φ.toFun).map (mul (φ.toFun c)))
        (zero :: rawMul (cs.map φ.toFun) (b.map φ.toFun))
    rw [map_rawAdd, List.map_cons, φ.map_zero, map_rawMul φ cs b, List.map_map, List.map_map]
    exact congrArg (rawAddCoeffs · _) (List.map_congr_left fun x _ => φ.map_mul c x)

theorem map_evalCoeffs (φ : RingHom R S) (x : R) :
    ∀ l : List R, φ.toFun (evalCoeffs l x) = evalCoeffs (l.map φ.toFun) (φ.toFun x)
  | [] => φ.map_zero
  | c :: cs => by
    show φ.toFun (add c (mul x (evalCoeffs cs x))) =
      add (φ.toFun c) (mul (φ.toFun x) (evalCoeffs (cs.map φ.toFun) (φ.toFun x)))
    rw [φ.map_add, φ.map_mul, map_evalCoeffs φ x cs]

end RingHom

namespace UPoly
section Eval
variable {R S T : Type} [LawfulCommRing R] [DecidableEq R] [LawfulCommRing S] [LawfulCommRing T]

theorem evalCoeffs_map_trimPoly (φ : RingHom R S) (s : S) :
    ∀ l : List R, evalCoeffs ((trimPoly l).map φ.toFun) s = evalCoeffs (l.map φ.toFun) s
  | [] => by rfl
  | c :: cs => by
    have ih := evalCoeffs_map_trimPoly φ s cs
    simp only [trimPoly]
    split
    · next h =>
      rw [h.1] at ih
      show zero = add (φ.toFun c) (mul s (evalCoeffs (cs.map φ.toFun) s))
      rw [← ih, h.2, φ.map_zero]
      show zero = add zero (mul s zero)
      rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    · show add (φ.toFun c) (mul s (evalCoeffs ((trimPoly cs).map φ.toFun) s)) =
        add (φ.toFun c) (mul s (evalCoeffs (cs.map φ.toFun) s))
      rw [ih]

/-- Evaluate at `s : S` after pushing coefficients through `φ`. -/
@[expose] def eval₂ (φ : RingHom R S) (s : S) (p : UPoly R) : S := evalCoeffs (p.coeffs.map φ.toFun) s

theorem eval₂_ofList (φ : RingHom R S) (s : S) (l : List R) :
    eval₂ φ s (ofList l) = evalCoeffs (l.map φ.toFun) s := evalCoeffs_map_trimPoly φ s l

theorem eval₂_zero (φ : RingHom R S) (s : S) : eval₂ φ s zero = zero := by rfl
theorem eval₂_add (φ : RingHom R S) (s : S) (a b : UPoly R) :
    eval₂ φ s (add a b) = add (eval₂ φ s a) (eval₂ φ s b) := by
  show evalCoeffs ((trimPoly (rawAddCoeffs a.coeffs b.coeffs)).map φ.toFun) s = _
  rw [evalCoeffs_map_trimPoly, RingHom.map_rawAdd, evalCoeffs_rawAdd]; rfl

theorem eval₂_mul (φ : RingHom R S) (s : S) (a b : UPoly R) :
    eval₂ φ s (mul a b) = mul (eval₂ φ s a) (eval₂ φ s b) := by
  show evalCoeffs ((trimPoly (rawMul a.coeffs b.coeffs)).map φ.toFun) s = _
  rw [evalCoeffs_map_trimPoly, RingHom.map_rawMul, evalCoeffs_rawMul]; rfl

/-- Constant polynomials. -/
@[expose] def C (c : R) : UPoly R := ofList [c]

/-- The variable. -/
@[expose] def X : UPoly R := ofList [zero, one]

theorem eval₂_C (φ : RingHom R S) (s : S) (c : R) : eval₂ φ s (C c) = φ.toFun c := by
  show eval₂ φ s (ofList [c]) = _; rw [eval₂_ofList]
  show add (φ.toFun c) (mul s zero) = _; rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

theorem eval₂_X (φ : RingHom R S) (s : S) : eval₂ φ s (X : UPoly R) = s := by
  show eval₂ φ s (ofList [zero, one]) = _; rw [eval₂_ofList]
  show add (φ.toFun zero) (mul s (add (φ.toFun one) (mul s zero))) = s
  rw [φ.map_zero, φ.map_one, LawfulCommRing.mul_zero, LawfulCommRing.add_zero,
    LawfulCommRing.mul_one, LawfulCommRing.zero_add]

theorem one_eq_C : (one : UPoly R) = C one := by rfl

/-- `eval₂ φ s` as a ring homomorphism. -/
def eval₂Hom (φ : RingHom R S) (s : S) : RingHom (UPoly R) S where
  toFun := eval₂ φ s
  map_zero := eval₂_zero φ s
  map_one := by rw [one_eq_C, eval₂_C, φ.map_one]
  map_add := eval₂_add φ s
  map_mul := eval₂_mul φ s

theorem eval₂Hom_apply (φ : RingHom R S) (s : S) (p : UPoly R) :
    (eval₂Hom φ s).toFun p = eval₂ φ s p := by rfl

/-- Homomorphisms commute with `eval₂`. -/
theorem hom_eval₂ (ψ : RingHom S T) (φ : RingHom R S) (s : S) (p : UPoly R) :
    ψ.toFun (eval₂ φ s p) = eval₂ (ψ.comp φ) (ψ.toFun s) p := by
  show ψ.toFun (evalCoeffs (p.coeffs.map φ.toFun) s) = _
  rw [RingHom.map_evalCoeffs, List.map_map]; rfl

/-- Plain evaluation at a point of the coefficient ring. -/
@[expose] def eval (p : UPoly R) (x : R) : R := eval₂ (RingHom.id R) x p

theorem eval_eq (p : UPoly R) (x : R) : p.eval x = evalCoeffs p.coeffs x := by
  show evalCoeffs (p.coeffs.map (fun a => a)) x = _; rw [List.map_id']

/-- Evaluation at `x` as a ring homomorphism. -/
def evalHom (x : R) : RingHom (UPoly R) R := eval₂Hom (RingHom.id R) x

theorem evalHom_apply (x : R) (p : UPoly R) : (evalHom x).toFun p = p.eval x := by rfl
theorem eval_C (c x : R) : (C c).eval x = c := eval₂_C _ _ _
theorem eval_X (x : R) : (X : UPoly R).eval x = x := eval₂_X _ _
theorem coeffAt_C_zero (c : R) : coeffAt (C c).coeffs 0 = c := by
  show coeffAt (ofList [c]).coeffs 0 = _; rw [coeffAt_ofList]; rfl
theorem coeffAt_C_succ (c : R) (k : Nat) : coeffAt (C c).coeffs (k + 1) = zero := by
  show coeffAt (ofList [c]).coeffs (k + 1) = _
  rw [coeffAt_ofList, coeffAt_cons_succ, coeffAt_nil]

omit [DecidableEq R] in
private theorem coeffAt_zero_cons_nil (l : List R) : ∀ k : Nat,
    coeffAt (zero :: rawMul ([] : List R) l) k = zero
  | 0 => rfl
  | k + 1 => by rw [coeffAt_cons_succ]; exact coeffAt_nil k

theorem coeffAt_C_mul (c : R) (q : UPoly R) (k : Nat) :
    coeffAt (mul (C c) q).coeffs k = mul c (coeffAt q.coeffs k) := by
  show coeffAt (pMul (trimPoly [c]) q.coeffs) k = _
  rw [pMul_trimPoly_left]
  show coeffAt (trimPoly (rawAddCoeffs (q.coeffs.map (mul c)) (zero :: rawMul [] q.coeffs))) k = _
  rw [coeffAt_trimPoly, coeffAt_addCoeffs, coeffAt_map_mul, coeffAt_zero_cons_nil,
    LawfulCommRing.add_zero]

theorem coeffAt_X_mul_zero (q : UPoly R) : coeffAt (mul X q).coeffs 0 = zero := by
  show coeffAt (pMul (trimPoly [zero, one]) q.coeffs) 0 = _
  rw [pMul_trimPoly_left]
  show coeffAt (trimPoly (rawAddCoeffs (q.coeffs.map (mul zero))
    (zero :: rawMul [one] q.coeffs))) 0 = _
  rw [coeffAt_trimPoly, coeffAt_addCoeffs, coeffAt_map_mul, LawfulCommRing.zero_mul,
    coeffAt_cons_zero, LawfulCommRing.add_zero]

theorem coeffAt_X_mul_succ (q : UPoly R) (k : Nat) :
    coeffAt (mul X q).coeffs (k + 1) = coeffAt q.coeffs k := by
  show coeffAt (pMul (trimPoly [zero, one]) q.coeffs) (k + 1) = _
  rw [pMul_trimPoly_left]
  show coeffAt (trimPoly (rawAddCoeffs (q.coeffs.map (mul zero))
    (zero :: rawAddCoeffs (q.coeffs.map (mul one)) (zero :: rawMul [] q.coeffs)))) (k + 1) = _
  rw [coeffAt_trimPoly, coeffAt_addCoeffs, coeffAt_map_mul, LawfulCommRing.zero_mul,
    coeffAt_cons_succ, coeffAt_addCoeffs, coeffAt_map_mul, LawfulCommRing.one_mul,
    LawfulCommRing.zero_add, coeffAt_zero_cons_nil, LawfulCommRing.add_zero]

/-- Horner decomposition of a coefficient list. -/
theorem ofList_cons (c : R) (l : List R) :
    ofList (c :: l) = add (C c) (mul X (ofList l)) := by
  apply ext_coeffAt; intro k
  rw [coeffAt_ofList, coeffAt_add]
  cases k with
  | zero => rw [coeffAt_X_mul_zero, coeffAt_C_zero, coeffAt_cons_zero, LawfulCommRing.add_zero]
  | succ k =>
    rw [coeffAt_X_mul_succ, coeffAt_C_succ, coeffAt_cons_succ, coeffAt_ofList,
      LawfulCommRing.zero_add]


theorem ofList_coeffs (p : UPoly R) : ofList p.coeffs = p := by apply ext; rw [coeffs_ofList]; exact p.trimmed

/-- `C` as a ring homomorphism. -/
def CHom : RingHom R (UPoly R) where
  toFun := C
  map_zero := ext_coeffAt fun k => by
    rw [coeffs_zero, coeffAt_nil]
    cases k <;> first | exact coeffAt_C_zero _ | exact coeffAt_C_succ _ _
  map_one := by rfl
  map_add a b := ext_coeffAt fun k => by
    rw [coeffAt_add]
    cases k with
    | zero => rw [coeffAt_C_zero, coeffAt_C_zero, coeffAt_C_zero]
    | succ k => rw [coeffAt_C_succ, coeffAt_C_succ, coeffAt_C_succ, LawfulCommRing.add_zero]
  map_mul a b := ext_coeffAt fun k => by
    rw [coeffAt_C_mul]
    cases k with
    | zero => rw [coeffAt_C_zero, coeffAt_C_zero]
    | succ k => rw [coeffAt_C_succ, coeffAt_C_succ, LawfulCommRing.mul_zero]

theorem CHom_apply (c : R) : (CHom (R := R)).toFun c = C c := by rfl

end Eval
end UPoly

/-! ## Weighted degrees -/

section Degree
variable {R S : Type} [LawfulCommRing R] [DecidableEq R] [LawfulCommRing S] [DecidableEq S]

omit [DecidableEq R] in
/-- The filtration lemma for products: if the coefficients of `a` and `b` lie in families
    `M` and `N` with `M i · N j ⊆ L (i + j)`, the coefficients of `a * b` lie in `L`. -/
theorem coeffAt_rawMul_graded (N : Nat → R → Prop) (b : List R) (hN : ∀ j, N j (coeffAt b j)) :
    ∀ (a : List R) (L M : Nat → R → Prop), (∀ k, L k zero) →
      (∀ k x y, L k x → L k y → L k (add x y)) →
      (∀ i j x y, M i x → N j y → L (i + j) (mul x y)) →
      (∀ i, M i (coeffAt a i)) → ∀ k, L k (coeffAt (rawMul a b) k)
  | [], L, _, hz, _, _, _, k => by
    show L k (coeffAt [] k); rw [coeffAt_nil]; exact hz k
  | c :: cs, L, M, hz, hadd, hmul, hM, k => by
    show L k (coeffAt (rawAddCoeffs (b.map (mul c)) (zero :: rawMul cs b)) k)
    rw [coeffAt_addCoeffs, coeffAt_map_mul]
    apply hadd
    · have := hmul 0 k c _ (hM 0) (hN k)
      rwa [Nat.zero_add] at this
    · cases k with
      | zero => exact hz 0
      | succ k =>
        rw [coeffAt_cons_succ]
        exact coeffAt_rawMul_graded N b hN cs (fun k => L (k + 1)) (fun i => M (i + 1))
          (fun k => hz _) (fun k => hadd _)
          (fun i j x y hx hy => by
            have := hmul (i + 1) j x y hx hy
            rwa [Nat.add_right_comm] at this)
          (fun i => hM (i + 1)) k

/-- A degree-like function: zero at zero, ultrametric on sums, subadditive on products. -/
structure DegFn (w : R → Nat) : Prop where
  zero : w zero = 0
  add_le : ∀ x y, w (add x y) ≤ max (w x) (w y)
  mul_le : ∀ x y, w (mul x y) ≤ w x + w y
  neg_le : ∀ x, w (neg x) ≤ w x

namespace UPoly

/-- `max` of `w c + s * k` over the nonzero coefficients `c` at index `k`, from offset `o`. -/
def wdegFrom (w : R → Nat) (s : Nat) : Nat → List R → Nat
  | _, [] => 0
  | o, c :: cs => max (if c = zero then 0 else w c + s * o) (wdegFrom w s (o + 1) cs)

/-- Weighted degree: coefficients are measured by `w`, the variable has weight `s`. -/
@[expose] def wdeg (w : R → Nat) (s : Nat) (p : UPoly R) : Nat := wdegFrom w s 0 p.coeffs

theorem le_wdegFrom (w : R → Nat) (s : Nat) : ∀ (o : Nat) (l : List R) (k : Nat),
    coeffAt l k ≠ zero → w (coeffAt l k) + s * (o + k) ≤ wdegFrom w s o l
  | _, [], k, h => absurd (coeffAt_nil k) h
  | o, c :: cs, 0, h => by
    rw [coeffAt_cons_zero] at h ⊢
    unfold wdegFrom
    simp only [h, ↓reduceIte, Nat.add_zero]
    exact Nat.le_max_left _ _
  | o, c :: cs, k + 1, h => by
    rw [coeffAt_cons_succ] at h ⊢
    have ih := le_wdegFrom w s (o + 1) cs k h
    unfold wdegFrom
    have e : o + (k + 1) = o + 1 + k := by omega
    rw [e]
    exact Nat.le_trans ih (Nat.le_max_right _ _)

theorem wdegFrom_le (w : R → Nat) (s : Nat) : ∀ (o : Nat) (l : List R) (B : Nat),
    (∀ k, coeffAt l k ≠ zero → w (coeffAt l k) + s * (o + k) ≤ B) → wdegFrom w s o l ≤ B
  | _, [], _, _ => Nat.zero_le _
  | o, c :: cs, B, h => by
    unfold wdegFrom
    apply Nat.max_le.mpr
    constructor
    · split
      · exact Nat.zero_le _
      · next hc => exact h 0 hc
    · apply wdegFrom_le w s (o + 1) cs B
      intro k hk
      have := h (k + 1) hk
      rw [coeffAt_cons_succ] at this
      have e : o + (k + 1) = o + 1 + k := by omega
      rwa [e] at this

theorem le_wdeg (w : R → Nat) (s : Nat) (p : UPoly R) (k : Nat)
    (h : coeffAt p.coeffs k ≠ zero) : w (coeffAt p.coeffs k) + s * k ≤ p.wdeg w s := by
  have := le_wdegFrom w s 0 p.coeffs k h
  rwa [Nat.zero_add] at this

theorem wdeg_le (w : R → Nat) (s : Nat) (p : UPoly R) (B : Nat)
    (h : ∀ k, coeffAt p.coeffs k ≠ zero → w (coeffAt p.coeffs k) + s * k ≤ B) :
    p.wdeg w s ≤ B :=
  wdegFrom_le w s 0 p.coeffs B (fun k hk => by rw [Nat.zero_add]; exact h k hk)

theorem bnd_add {w : R → Nat} (hw : DegFn w) {c : Nat} {B : Nat} {x y : R}
    (hx : x ≠ zero → w x + c ≤ B) (hy : y ≠ zero → w y + c ≤ B) (h : add x y ≠ zero) :
    w (add x y) + c ≤ B := by
  if hx0 : x = zero then
    subst hx0; rw [LawfulCommRing.zero_add] at h ⊢; exact hy h
  else if hy0 : y = zero then
    subst hy0; rw [LawfulCommRing.add_zero] at h ⊢; exact hx h
  else
    have := hw.add_le x y; have := hx hx0; have := hy hy0; omega

/-- A degree function on `R` lifts to the weighted degree on `UPoly R`. -/
theorem degFn_wdeg {w : R → Nat} (hw : DegFn w) (s : Nat) :
    DegFn (fun p : UPoly R => p.wdeg w s) where
  zero := by rfl
  add_le a b := by
    apply wdeg_le
    intro k hk
    rw [coeffAt_add] at hk ⊢
    have ha := le_wdeg w s a k
    have hb := le_wdeg w s b k
    exact bnd_add hw (B := max (a.wdeg w s) (b.wdeg w s)) (fun h => by have := ha h; omega)
      (fun h => by have := hb h; omega) hk
  neg_le a := by
    apply wdeg_le
    intro k hk
    rw [coeffAt_neg] at hk ⊢
    have hne : coeffAt a.coeffs k ≠ zero := fun e => hk (by rw [e, LawfulCommRing.neg_zero])
    have := le_wdeg w s a k hne; have := hw.neg_le (coeffAt a.coeffs k); omega
  mul_le a b := by
    apply wdeg_le
    intro k
    have e : coeffAt (mul a b).coeffs k = coeffAt (rawMul a.coeffs b.coeffs) k :=
      coeffAt_trimPoly _ k
    rw [e]
    exact coeffAt_rawMul_graded (fun j y => y ≠ zero → w y + s * j ≤ b.wdeg w s) b.coeffs
      (le_wdeg w s b) a.coeffs (fun k x => x ≠ zero → w x + s * k ≤ a.wdeg w s + b.wdeg w s)
      (fun i x => x ≠ zero → w x + s * i ≤ a.wdeg w s) (fun _ h => absurd rfl h)
      (fun _ _ _ hx hy h => bnd_add hw hx hy h)
      (fun i j x y hx hy h => by
        have hx0 : x ≠ zero := fun e => h (by rw [e, LawfulCommRing.zero_mul])
        have hy0 : y ≠ zero := fun e => h (by rw [e, LawfulCommRing.mul_zero])
        have := hx hx0; have := hy hy0; have := hw.mul_le x y
        rw [Nat.mul_add]; omega)
      (le_wdeg w s a) k

theorem degFn_natDeg : DegFn (natDeg : UPoly R → Nat) where
  zero := by rfl
  add_le := natDeg_add_le
  mul_le := natDeg_mul_le
  neg_le a := natDeg_le_of_coeffAt _ _ (fun k hk => by
    rw [coeffAt_neg, a.coeffAt_eq_zero_of_natDeg_lt hk, LawfulCommRing.neg_zero])

omit [DecidableEq S] in
theorem evalCoeffs_eq_zero_of_coeffAt (s : S) : ∀ l : List S,
    (∀ k, coeffAt l k = zero) → evalCoeffs l s = zero
  | [], _ => rfl
  | c :: cs, h => by
    show add c (mul s (evalCoeffs cs s)) = zero
    rw [evalCoeffs_eq_zero_of_coeffAt s cs (fun k => h (k + 1)), show c = zero from h 0,
      LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

/-- Horner degree bound: evaluating at a point of degree at most `t`. -/
theorem degFn_evalCoeffs_le {δ : S → Nat} (hδ : DegFn δ) (s : S) (t : Nat) (hs : δ s ≤ t) :
    ∀ (l : List S) (B : Nat), (∀ k, coeffAt l k ≠ zero → δ (coeffAt l k) + t * k ≤ B) →
      δ (evalCoeffs l s) ≤ B
  | [], _, _ => by show δ zero ≤ _; rw [hδ.zero]; exact Nat.zero_le _
  | c :: cs, B, h => by
    show δ (add c (mul s (evalCoeffs cs s))) ≤ B
    have hc : δ c ≤ B := by
      if hc0 : c = zero then rw [hc0, hδ.zero]; exact Nat.zero_le _
      else have := h 0 hc0; rw [coeffAt_cons_zero] at this; omega
    have hrest : δ (mul s (evalCoeffs cs s)) ≤ B := by
      if htB : t ≤ B then
        have ih := degFn_evalCoeffs_le hδ s t hs cs (B - t) (fun k hk => by
          have := h (k + 1) hk
          rw [coeffAt_cons_succ, Nat.mul_succ] at this; omega)
        have := hδ.mul_le s (evalCoeffs cs s); omega
      else
        have hall : ∀ k, coeffAt cs k = zero := fun k => Decidable.byContradiction fun hk => by
          have := h (k + 1) hk
          rw [coeffAt_cons_succ, Nat.mul_succ] at this; omega
        rw [evalCoeffs_eq_zero_of_coeffAt s cs hall, LawfulCommRing.mul_zero, hδ.zero]
        exact Nat.zero_le _
    have := hδ.add_le c (mul s (evalCoeffs cs s)); omega

/-- Degree of `eval₂ φ s p` against the weighted degree of `p`. -/
theorem degFn_eval₂_le {δ : S → Nat} (hδ : DegFn δ) (φ : RingHom R S) (w : R → Nat)
    (hw : ∀ c, δ (φ.toFun c) ≤ w c) (s : S) (t : Nat) (hs : δ s ≤ t) (p : UPoly R) :
    δ (eval₂ φ s p) ≤ p.wdeg w t := by
  apply degFn_evalCoeffs_le hδ s t hs
  intro k hk
  rw [RingHom.coeffAt_map] at hk ⊢
  have hne : coeffAt p.coeffs k ≠ zero := fun e => hk (by rw [e, φ.map_zero])
  have := le_wdeg w t p k hne; have := hw (coeffAt p.coeffs k); omega

end UPoly
end Degree

/-! ## Taylor shift and Hasse derivatives -/

namespace RingHom
variable {S T : Type} [LawfulCommRing S] [LawfulCommRing T]

/-- The Horner–Hasse recursion commutes with ring homomorphisms. -/
theorem map_gsUniHasse (ψ : RingHom S T) : ∀ (l : List S) (k : Nat) (s : S),
    ψ.toFun (gsUniHasse l k s) = gsUniHasse (l.map ψ.toFun) k (ψ.toFun s)
  | [], _, _ => ψ.map_zero
  | c :: cs, 0, s => by
    show ψ.toFun (add c (mul s (gsUniHasse cs 0 s))) = add (ψ.toFun c)
      (mul (ψ.toFun s) (gsUniHasse (cs.map ψ.toFun) 0 (ψ.toFun s)))
    rw [ψ.map_add, ψ.map_mul, map_gsUniHasse ψ cs 0 s]
  | c :: cs, k + 1, s => by
    show ψ.toFun (add (gsUniHasse cs k s) (mul s (gsUniHasse cs (k + 1) s))) =
      add (gsUniHasse (cs.map ψ.toFun) k (ψ.toFun s))
        (mul (ψ.toFun s) (gsUniHasse (cs.map ψ.toFun) (k + 1) (ψ.toFun s)))
    rw [ψ.map_add, ψ.map_mul, map_gsUniHasse ψ cs k s, map_gsUniHasse ψ cs (k + 1) s]

end RingHom

namespace UPoly
section Taylor
variable {R : Type} [LawfulCommRing R] [DecidableEq R]

/-- The Taylor shift `p ↦ p(b + W)`. It is a ring homomorphism: multiplicativity is the
    Leibniz rule for Hasse derivatives in generating-function form. -/
def taylorShift (b : R) : RingHom (UPoly R) (UPoly R) := eval₂Hom CHom (add (C b) X)

/-- The `k`-th Hasse derivative as a polynomial: the Horner–Hasse recursion `gsUniHasse`
    run at the generic point `X` of `R[X]`. -/
def hasse (k : Nat) (p : UPoly R) : UPoly R := gsUniHasse (p.coeffs.map C) k X

private theorem map_eval_C (x : R) : ∀ l : List R, l.map (fun c => (C c).eval x) = l
  | [] => rfl
  | c :: cs => by rw [List.map_cons, map_eval_C x cs, eval_C]

/-- Evaluating the Hasse derivative recovers the pointwise recursion; by
    `gsUniHasse_eq_dotVec` this is the binomial formula `Σ C(i, k) pᵢ b^(i-k)`. -/
theorem eval_hasse (k : Nat) (p : UPoly R) (b : R) :
    (hasse k p).eval b = gsUniHasse p.coeffs k b := by
  show (evalHom b).toFun (gsUniHasse (p.coeffs.map C) k X) = _
  rw [RingHom.map_gsUniHasse, List.map_map]
  show gsUniHasse (p.coeffs.map (fun c => (C c).eval b)) k (X.eval b) = _
  rw [map_eval_C, eval_X]

/-- Shift rule: `(taylorShift b p)(w) = p(b + w)`. -/
theorem eval_taylorShift (b w : R) (p : UPoly R) :
    ((taylorShift b).toFun p).eval w = p.eval (add b w) := by
  show (evalHom w).toFun (eval₂ CHom (add (C b) X) p) = _
  rw [hom_eval₂, (evalHom w).map_add]
  show evalCoeffs (p.coeffs.map (fun c => (C c).eval w)) (add ((C b).eval w) (X.eval w)) = _
  rw [map_eval_C, eval_C, eval_X, eval_eq]

theorem coeffAt_shift_list (b : R) : ∀ (l : List R) (k : Nat),
    coeffAt (evalCoeffs (l.map C) (add (C b) X)).coeffs k = gsUniHasse l k b
  | [], k => by show coeffAt (zero : UPoly R).coeffs k = zero; rw [coeffs_zero, coeffAt_nil]
  | c :: cs, k => by
    show coeffAt (add (C c) (mul (add (C b) X) (evalCoeffs (cs.map C) (add (C b) X)))).coeffs k
      = _
    rw [coeffAt_add, LawfulCommRing.right_distrib, coeffAt_add, coeffAt_C_mul]
    cases k with
    | zero =>
      rw [coeffAt_X_mul_zero, coeffAt_C_zero, coeffAt_shift_list b cs 0,
        LawfulCommRing.add_zero]; rfl
    | succ k =>
      rw [coeffAt_X_mul_succ, coeffAt_C_succ, coeffAt_shift_list b cs (k + 1),
        coeffAt_shift_list b cs k]
      show add zero (add (mul b (gsUniHasse cs (k + 1) b)) (gsUniHasse cs k b)) =
        add (gsUniHasse cs k b) (mul b (gsUniHasse cs (k + 1) b))
      rw [LawfulCommRing.zero_add, LawfulCommRing.add_comm]

/-- Taylor's formula: the coefficient of `W^k` in `p(b + W)` is the `k`-th Hasse derivative
    of `p` at `b`. -/
theorem coeffAt_taylorShift (b : R) (p : UPoly R) (k : Nat) :
    coeffAt ((taylorShift b).toFun p).coeffs k = (hasse k p).eval b :=
  (coeffAt_shift_list b p.coeffs k).trans (eval_hasse k p b).symm

end Taylor
end UPoly

/-! ## Trivariate polynomials -/

/-- `F[X][Y][Z]`, with `Z` the outermost variable. -/
abbrev Poly3 (F : Type) [LawfulCommRing F] [DecidableEq F] := UPoly (UPoly (UPoly F))

namespace Poly3
variable {F : Type} [LawfulCommRing F] [DecidableEq F]

/-- Degree in `Z`. -/
def degZ (Q : Poly3 F) : Nat := Q.natDeg

theorem degZ_eq (Q : Poly3 F) : Q.degZ = Q.natDeg := by unfold degZ; rfl

/-- Total degree in `(Y, Z)`. -/
@[expose] def degYZ (Q : Poly3 F) : Nat := Q.wdeg UPoly.natDeg 1

/-- The `(1, 1, d)`-weighted degree in `(X, Y, Z)`. -/
@[expose] def deg11d (d : Nat) (Q : Poly3 F) : Nat := Q.wdeg (fun q => q.wdeg UPoly.natDeg 1) d

/-- The line `α + βX`. -/
@[expose] def line (α β : F) : UPoly F := UPoly.ofList [α, β]

theorem natDeg_line_le (α β : F) : (line α β).natDeg ≤ 1 := by
  have := trimPoly_length_le [α, β]
  show (trimPoly [α, β]).length - 1 ≤ 1
  simp only [List.length_cons, List.length_nil] at this; omega

/-- Specialization to the affine line: `Q(X, α + βX, P(X))`, as a ring homomorphism. -/
def affineLineHom (α β : F) (P : UPoly F) : RingHom (Poly3 F) (UPoly F) :=
  UPoly.eval₂Hom (UPoly.evalHom (line α β)) P

/-- `Q(X, α + βX, P(X))`. -/
def evalAffineLine (Q : Poly3 F) (α β : F) (P : UPoly F) : UPoly F :=
  (affineLineHom α β P).toFun Q

theorem evalAffineLine_mul (Q₁ Q₂ : Poly3 F) (α β : F) (P : UPoly F) :
    evalAffineLine (mul Q₁ Q₂) α β P = mul (evalAffineLine Q₁ α β P) (evalAffineLine Q₂ α β P) :=
  (affineLineHom α β P).map_mul Q₁ Q₂

theorem evalAffineLine_add (Q₁ Q₂ : Poly3 F) (α β : F) (P : UPoly F) :
    evalAffineLine (add Q₁ Q₂) α β P = add (evalAffineLine Q₁ α β P) (evalAffineLine Q₂ α β P) :=
  (affineLineHom α β P).map_add Q₁ Q₂

/-- A polynomial constant in `Z` is evaluated on the line alone. -/
theorem evalAffineLine_C (G : UPoly (UPoly F)) (α β : F) (P : UPoly F) :
    evalAffineLine (UPoly.C G) α β P = G.eval (line α β) := UPoly.eval₂_C _ _ _

/-- Substituting a line for `Y` and a polynomial of degree at most `d` for `Z` produces a
    polynomial of degree at most the `(1, 1, d)`-weighted degree. -/
theorem deg_evalAffineLine_le (Q : Poly3 F) (α β : F) (P : UPoly F) (d : Nat)
    (hP : P.natDeg ≤ d) : (evalAffineLine Q α β P).natDeg ≤ Q.deg11d d :=
  UPoly.degFn_eval₂_le UPoly.degFn_natDeg _ _
    (fun q => UPoly.degFn_eval₂_le UPoly.degFn_natDeg (RingHom.id _) UPoly.natDeg
      (fun _ => Nat.le_refl _) (line α β) 1 (natDeg_line_le α β) q) P d hP Q

/-- Formal derivative in `Z`, of Hasse order `s`. -/
def hasseZ (s : Nat) (Q : Poly3 F) : Poly3 F := UPoly.hasse s Q

/-- Mixed Hasse derivative `∂_X^(r) ∂_Z^(s)`: differentiate the innermost coefficients in
    `X`, then the outer polynomial in `Z`. -/
def hasseXZ (r s : Nat) (Q : Poly3 F) : Poly3 F :=
  UPoly.hasse s (UPoly.ofList (Q.coeffs.map fun q => UPoly.ofList (q.coeffs.map (UPoly.hasse r))))

end Poly3


end Qsag
namespace Qsag

set_option autoImplicit false
open CommRingOps RoundPoly

namespace Mat
section Ring
variable {R : Type} [LawfulCommRing R]

private theorem ite_pos {α : Type} {p : Prop} [Decidable p] (hp : p) {a b : α} :
    (if p then a else b) = a := by
  split
  · rfl
  · next hn => exact absurd hp hn

private theorem ite_neg {α : Type} {p : Prop} [Decidable p] (hnp : ¬ p) {a b : α} :
    (if p then a else b) = b := by
  split
  · next hp => exact absurd hp hnp
  · rfl

/-! ## Structural finite sums `rangeSum` -/

def rangeSum : Nat → (Nat → R) → R
  | 0, _ => zero
  | n + 1, f => add (rangeSum n f) (f n)

theorem rangeSum_congr {n : Nat} {f g : Nat → R} (h : ∀ i, i < n → f i = g i) :
    rangeSum n f = rangeSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show add (rangeSum n f) (f n) = add (rangeSum n g) (g n)
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

theorem rangeSum_eq_zero {n : Nat} {f : Nat → R} (h : ∀ i, i < n → f i = zero) :
    rangeSum n f = zero := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show add (rangeSum n f) (f n) = zero
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n), LawfulCommRing.add_zero]

theorem rangeSum_add (n : Nat) (f g : Nat → R) :
    rangeSum n (fun i => add (f i) (g i)) = add (rangeSum n f) (rangeSum n g) := by
  induction n with
  | zero => show zero = add zero zero; rw [LawfulCommRing.add_zero]
  | succ n ih =>
    show add (rangeSum n _) (add (f n) (g n)) = add (add (rangeSum n f) (f n)) (add (rangeSum n g) (g n))
    rw [ih]; constructive_ring

theorem rangeSum_mul_left (c : R) (n : Nat) (f : Nat → R) :
    rangeSum n (fun i => mul c (f i)) = mul c (rangeSum n f) := by
  induction n with
  | zero => show zero = mul c zero; rw [LawfulCommRing.mul_zero]
  | succ n ih =>
    show add (rangeSum n _) (mul c (f n)) = mul c (add (rangeSum n f) (f n))
    rw [ih, LawfulCommRing.left_distrib]

theorem rangeSum_mul_right (c : R) (n : Nat) (f : Nat → R) :
    rangeSum n (fun i => mul (f i) c) = mul (rangeSum n f) c := by
  induction n with
  | zero => show zero = mul zero c; rw [LawfulCommRing.zero_mul]
  | succ n ih =>
    show add (rangeSum n _) (mul (f n) c) = mul (add (rangeSum n f) (f n)) c
    rw [ih]; constructive_ring

theorem rangeSum_single {n j₀ : Nat} (hj₀ : j₀ < n) (f : Nat → R)
    (hz : ∀ j, j < n → j ≠ j₀ → f j = zero) :
    rangeSum n f = f j₀ := by
  induction n with
  | zero => exact absurd hj₀ (Nat.not_lt_zero _)
  | succ n ih =>
    show add (rangeSum n f) (f n) = f j₀
    if hEq : j₀ = n then
      subst hEq
      rw [rangeSum_eq_zero (fun j hj => hz j (Nat.lt_succ_of_lt hj) (Nat.ne_of_lt hj)), LawfulCommRing.zero_add]
    else
      rw [ih (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj₀) hEq) (fun j hj => hz j (Nat.lt_succ_of_lt hj)),
        hz n (Nat.lt_succ_self n) (Ne.symm hEq), LawfulCommRing.add_zero]

theorem map_rangeSum {S : Type} [LawfulCommRing S] (φ : RingHom R S) (n : Nat) (f : Nat → R) :
    φ.toFun (rangeSum n f) = rangeSum n (fun i => φ.toFun (f i)) := by
  induction n with
  | zero => exact φ.map_zero
  | succ n ih => show φ.toFun (add _ _) = add _ _; rw [φ.map_add, ih]

private theorem rangeSum_antisym_eq_zero :
    ∀ (n : Nat) (g : Nat → Nat → R),
      (∀ i, i < n → g i i = zero) → (∀ i, i < n → ∀ j, j < n → g i j = neg (g j i)) →
      rangeSum n (fun i => rangeSum n (fun j => g i j)) = zero
  | 0, _, _, _ => rfl
  | n + 1, g, hdiag, hanti => by
    show add (rangeSum n (fun i => add (rangeSum n (fun j => g i j)) (g i n)))
        (add (rangeSum n (fun j => g n j)) (g n n)) = zero
    rw [rangeSum_add, rangeSum_antisym_eq_zero n g
        (fun i hi => hdiag i (Nat.lt_succ_of_lt hi))
        (fun i hi j hj => hanti i (Nat.lt_succ_of_lt hi) j (Nat.lt_succ_of_lt hj)),
      hdiag n (Nat.lt_succ_self n), LawfulCommRing.zero_add, LawfulCommRing.add_zero, ← rangeSum_add]
    exact rangeSum_eq_zero fun i hi => by
      rw [hanti i (Nat.lt_succ_of_lt hi) n (Nat.lt_succ_self n)]
      exact LawfulCommRing.add_left_neg (g n i)

/-! ## Determinant via Laplace expansion along row `0` -/

def skipIdx (r i : Nat) : Nat := if i < r then i else i + 1

theorem skipIdx_lt {r i k : Nat} (hi : i < k) : skipIdx r i < k + 1 := by unfold skipIdx; split <;> omega

def minor (M : Nat → Nat → R) (r c : Nat) : Nat → Nat → R :=
  fun i j => M (skipIdx r i) (skipIdx c j)

def signed (j : Nat) (x : R) : R := if j % 2 = 0 then x else neg x

private theorem signed_zero (j : Nat) : signed j (zero : R) = zero := by
  unfold signed; if h : j % 2 = 0 then rw [ite_pos h] else rw [ite_neg h, LawfulCommRing.neg_zero]

private theorem signed_add (j : Nat) (x y : R) :
    signed j (add x y) = add (signed j x) (signed j y) := by
  unfold signed; split
  · rfl
  · constructive_ring

private theorem signed_mul_left (j : Nat) (c x : R) :
    signed j (mul c x) = mul c (signed j x) := by
  unfold signed; split
  · rfl
  · constructive_ring

private theorem signed_rangeSum (j n : Nat) (f : Nat → R) :
    signed j (rangeSum n f) = rangeSum n (fun i => signed j (f i)) := by
  induction n with
  | zero => exact signed_zero j
  | succ n ih => show signed j (add _ _) = add _ _; rw [signed_add, ih]

private theorem signed_signed (j₁ j₂ : Nat) (x : R) :
    signed j₁ (signed j₂ x) = signed (j₁ + j₂) x := by
  unfold signed
  if h1 : j₁ % 2 = 0 then
    if h2 : j₂ % 2 = 0 then rw [ite_pos h2, ite_pos h1, ite_pos (by omega)]
    else rw [ite_neg h2, ite_pos h1, ite_neg (by omega)]
  else
    if h2 : j₂ % 2 = 0 then rw [ite_pos h2, ite_neg h1, ite_neg (by omega)]
    else rw [ite_neg h2, ite_neg h1, ite_pos (by omega)]; constructive_ring

def det : Nat → (Nat → Nat → R) → R
  | 0, _ => one
  | k + 1, M => rangeSum (k + 1) (fun j => signed j (mul (M 0 j) (det k (minor M 0 j))))

theorem det_congr :
    ∀ (k : Nat) {M N : Nat → Nat → R},
      (∀ i, i < k → ∀ j, j < k → M i j = N i j) → det k M = det k N
  | 0, _, _, _ => rfl
  | k + 1, M, N, h =>
    rangeSum_congr fun j hj => by
      have hm : det k (minor M 0 j) = det k (minor N 0 j) :=
        det_congr k fun i hi c hc => h (i + 1) (Nat.succ_lt_succ hi) (skipIdx j c) (skipIdx_lt hc)
      rw [h 0 (Nat.zero_lt_succ k) j hj, hm]

theorem map_det {S : Type} [LawfulCommRing S] (φ : RingHom R S) :
    ∀ (k : Nat) (M : Nat → Nat → R), φ.toFun (det k M) = det k (fun i j => φ.toFun (M i j))
  | 0, _ => φ.map_one
  | k + 1, M => by
    show φ.toFun (rangeSum (k + 1) _) = rangeSum (k + 1) _
    rw [map_rangeSum]
    refine rangeSum_congr fun j _ => ?_
    unfold signed; split
    · rw [φ.map_mul, map_det φ k (minor M 0 j)]; rfl
    · rw [φ.map_neg, φ.map_mul, map_det φ k (minor M 0 j)]; rfl

/-! ## Triangular, column-0, and identity determinants -/

theorem det_col0_zero :
    ∀ (k : Nat) (M : Nat → Nat → R), (∀ i, i < k + 1 → M i 0 = zero) → det (k + 1) M = zero
  | 0, M, h => by
    show add zero (signed 0 (mul (M 0 0) one)) = zero
    rw [h 0 Nat.zero_lt_one, LawfulCommRing.zero_mul, signed_zero, LawfulCommRing.add_zero]
  | k + 1, M, h =>
    rangeSum_eq_zero fun j _ => by
      cases j with
      | zero => rw [h 0 (Nat.zero_lt_succ _), LawfulCommRing.zero_mul, signed_zero]
      | succ j' =>
        rw [det_col0_zero k (minor M 0 (j' + 1)) (fun i hi => h (i + 1) (Nat.succ_lt_succ hi)),
          LawfulCommRing.mul_zero, signed_zero]

theorem det_col0_unit (k : Nat) (M : Nat → Nat → R) (h : ∀ i, i < k → M (i + 1) 0 = zero) :
    det (k + 1) M = mul (M 0 0) (det k (minor M 0 0)) := by
  show rangeSum (k + 1) _ = _
  rw [rangeSum_single (Nat.zero_lt_succ k) _ fun j hj hne => ?_]
  · rfl
  · cases j with
    | zero => exact absurd rfl hne
    | succ j' =>
      cases k with
      | zero => exfalso; omega
      | succ k' =>
        rw [det_col0_zero k' (minor M 0 (j' + 1)) (fun i hi => h i hi), LawfulCommRing.mul_zero, signed_zero]

theorem det_row0_unit (k : Nat) (M : Nat → Nat → R) (h : ∀ j, j < k → M 0 (j + 1) = zero) :
    det (k + 1) M = mul (M 0 0) (det k (minor M 0 0)) := by
  show rangeSum (k + 1) _ = _
  rw [rangeSum_single (Nat.zero_lt_succ k) _ fun j hj hne => ?_]
  · rfl
  · cases j with
    | zero => exact absurd rfl hne
    | succ j' => rw [h j' (Nat.lt_of_succ_lt_succ hj), LawfulCommRing.zero_mul, signed_zero]

theorem det_lower_tri_const (c : R) :
    ∀ (k : Nat) (M : Nat → Nat → R),
      (∀ i j, i < j → j < k → M i j = zero) → (∀ i, i < k → M i i = c) →
      det k M = CRing.npow c k
  | 0, _, _, _ => rfl
  | k + 1, M, hlt, hdiag => by
    rw [det_row0_unit k M (fun j hj => hlt 0 (j + 1) (Nat.zero_lt_succ j) (Nat.succ_lt_succ hj)),
      hdiag 0 (Nat.zero_lt_succ k),
      det_lower_tri_const c k (minor M 0 0)
        (fun i j hij hjk => hlt (i + 1) (j + 1) (Nat.succ_lt_succ hij) (Nat.succ_lt_succ hjk))
        (fun i hi => hdiag (i + 1) (Nat.succ_lt_succ hi))]
    exact LawfulCommRing.mul_comm c (CRing.npow c k)

private theorem npow_one : ∀ k : Nat, CRing.npow (one : R) k = one
  | 0 => rfl
  | k + 1 => by show mul (CRing.npow one k) one = one; rw [npow_one k, LawfulCommRing.one_mul]

theorem det_lower_tri_one (k : Nat) (M : Nat → Nat → R)
    (hlt : ∀ i j, i < j → j < k → M i j = zero) (hdiag : ∀ i, i < k → M i i = one) :
    det k M = one := by
  rw [det_lower_tri_const one k M hlt hdiag, npow_one]

def idMat (i j : Nat) : R := if i = j then one else zero

theorem det_idMat (k : Nat) : det k (idMat (R := R)) = one :=
  det_lower_tri_one k idMat
    (fun i j hij _ => by unfold idMat; rw [ite_neg (Nat.ne_of_lt hij)])
    (fun i _ => by unfold idMat; rw [ite_pos rfl])

/-! ## Weighted `DegFn` bound on `det k M` -/

def natRangeSum : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => natRangeSum n f + f n

private theorem natRangeSum_shift :
    ∀ (k : Nat) (f : Nat → Nat), f 0 + natRangeSum k (fun i => f (i + 1)) = natRangeSum (k + 1) f
  | 0, f => by show f 0 + 0 = 0 + f 0; omega
  | k + 1, f => by
    show f 0 + (natRangeSum k (fun i => f (i + 1)) + f (k + 1)) = natRangeSum (k + 1) f + f (k + 1)
    rw [← Nat.add_assoc, natRangeSum_shift k f]

private theorem natRangeSum_skipIdx :
    ∀ (k j : Nat) (cWt : Nat → Nat),
      j < k + 1 → cWt j + natRangeSum k (fun c => cWt (skipIdx j c)) = natRangeSum (k + 1) cWt
  | 0, j, cWt, hj => by
    have hj0 : j = 0 := by omega
    subst hj0; show cWt 0 + 0 = 0 + cWt 0; omega
  | k + 1, j, cWt, hj => by
    if hEq : j = k + 1 then
      subst hEq
      have aux : ∀ m, m ≤ k + 1 → natRangeSum m (fun c => cWt (skipIdx (k + 1) c)) = natRangeSum m cWt := by
        intro m; induction m with
        | zero => intro _; rfl
        | succ m ihm =>
          intro hm; show natRangeSum m _ + cWt (skipIdx (k + 1) m) = natRangeSum m cWt + cWt m
          rw [ihm (by omega)]; unfold skipIdx; rw [ite_pos (by omega)]
      show cWt (k + 1) + natRangeSum (k + 1) _ = natRangeSum (k + 1) cWt + cWt (k + 1)
      rw [aux (k + 1) (Nat.le_refl _)]; omega
    else
      have ih := natRangeSum_skipIdx k j cWt (by omega)
      have hsk : skipIdx j k = k + 1 := by unfold skipIdx; rw [ite_neg (by omega)]
      show cWt j + (natRangeSum k (fun c => cWt (skipIdx j c)) + cWt (skipIdx j k)) =
        natRangeSum (k + 1) cWt + cWt (k + 1)
      rw [hsk]; omega

section WeightedDeg
variable [DecidableEq R]

theorem degFn_det_weighted_le {w : R → Nat} (hw : DegFn w) (hw1 : w one = 0) :
    ∀ (k : Nat) (M : Nat → Nat → R) (rowWt colWt : Nat → Nat),
      (∀ i, i < k → ∀ j, j < k → M i j ≠ zero → w (M i j) + colWt j ≤ rowWt i) →
      det k M ≠ zero → w (det k M) + natRangeSum k colWt ≤ natRangeSum k rowWt
  | 0, _, _, _, _, _ => by show w one + 0 ≤ 0; rw [hw1]; exact Nat.zero_le 0
  | k + 1, M, rowWt, colWt, hBnd, hNe => by
    let term (j : Nat) : R := signed j (mul (M 0 j) (det k (minor M 0 j)))
    have hTermBnd : ∀ j, j < k + 1 → term j ≠ zero →
        w (term j) + natRangeSum (k + 1) colWt ≤ natRangeSum (k + 1) rowWt := by
      intro j hj htj
      have hMulNe : mul (M 0 j) (det k (minor M 0 j)) ≠ zero := fun e => by
        dsimp [term] at htj; rw [e, signed_zero] at htj; exact htj rfl
      have hM0Ne : M 0 j ≠ zero := fun e => hMulNe (by rw [e, LawfulCommRing.zero_mul])
      have hMinNe : det k (minor M 0 j) ≠ zero := fun e => hMulNe (by rw [e, LawfulCommRing.mul_zero])
      have h0 := hBnd 0 (Nat.zero_lt_succ k) j hj hM0Ne
      have hih := degFn_det_weighted_le hw hw1 k (minor M 0 j)
        (fun i => rowWt (i + 1)) (fun c => colWt (skipIdx j c))
        (fun i hi c hc => hBnd (i + 1) (Nat.succ_lt_succ hi) (skipIdx j c) (skipIdx_lt hc)) hMinNe
      have hSignW : w (term j) ≤ w (M 0 j) + w (det k (minor M 0 j)) := by
        dsimp [term]; unfold signed; split
        · exact hw.mul_le _ _
        · exact Nat.le_trans (hw.neg_le _) (hw.mul_le _ _)
      have hCol := natRangeSum_skipIdx k j colWt hj
      have hRow := natRangeSum_shift k rowWt
      omega
    have hSumBnd : ∀ m, m ≤ k + 1 → rangeSum m term ≠ zero →
        w (rangeSum m term) + natRangeSum (k + 1) colWt ≤ natRangeSum (k + 1) rowWt := by
      intro m; induction m with
      | zero => intro _ h0; exact absurd rfl h0
      | succ m ihm =>
        intro hm hsum
        exact UPoly.bnd_add hw (ihm (Nat.le_of_succ_le hm)) (hTermBnd m (Nat.lt_of_succ_le hm)) hsum
    exact hSumBnd (k + 1) (Nat.le_refl _) hNe

end WeightedDeg

/-! ## Row multilinearity, alternating rows, and `det_matMul` -/

def updRow (M : Nat → Nat → R) (r : Nat) (v : Nat → R) (i j : Nat) : R :=
  if i = r then v j else M i j

private theorem minor_updRow_zero (M : Nat → Nat → R) (v : Nat → R) (k j : Nat) :
    det k (minor (updRow M 0 v) 0 j) = det k (minor M 0 j) :=
  det_congr k fun _ _ _ _ => rfl

private theorem minor_updRow_succ (M : Nat → Nat → R) (r : Nat) (v : Nat → R) (k j : Nat) :
    det k (minor (updRow M (r + 1) v) 0 j) =
      det k (updRow (minor M 0 j) r (fun c => v (skipIdx j c))) :=
  det_congr k fun i _ c _ => by
    show (if i + 1 = r + 1 then v (skipIdx j c) else M (i + 1) (skipIdx j c)) =
      if i = r then v (skipIdx j c) else M (i + 1) (skipIdx j c)
    if h : i = r then rw [h, ite_pos rfl, ite_pos rfl]
    else rw [ite_neg (fun e => h (Nat.succ.inj e)), ite_neg h]

theorem det_updRow_zero :
    ∀ (k r : Nat) (M : Nat → Nat → R), r < k → det k (updRow M r (fun _ => zero)) = zero
  | 0, _, _, hr => absurd hr (Nat.not_lt_zero _)
  | k + 1, 0, _, _ =>
    rangeSum_eq_zero fun j _ => by show signed j (mul zero _) = zero; rw [LawfulCommRing.zero_mul, signed_zero]
  | k + 1, r + 1, M, hr =>
    rangeSum_eq_zero fun j _ => by
      show signed j (mul (M 0 j) (det k (minor (updRow M (r + 1) _) 0 j))) = zero
      rw [minor_updRow_succ, det_updRow_zero k r (minor M 0 j) (Nat.lt_of_succ_lt_succ hr),
        LawfulCommRing.mul_zero, signed_zero]

theorem det_updRow_add :
    ∀ (k r : Nat) (M : Nat → Nat → R) (u v : Nat → R), r < k →
      det k (updRow M r (fun j => add (u j) (v j))) =
        add (det k (updRow M r u)) (det k (updRow M r v))
  | 0, _, _, _, _, hr => absurd hr (Nat.not_lt_zero _)
  | k + 1, 0, M, u, v, _ => by
    show rangeSum (k + 1) _ = add (rangeSum (k + 1) _) (rangeSum (k + 1) _)
    rw [← rangeSum_add]; refine rangeSum_congr fun j _ => ?_
    show signed j (mul (add (u j) (v j)) (det k (minor (updRow M 0 _) 0 j))) =
      add (signed j (mul (u j) (det k (minor (updRow M 0 u) 0 j))))
        (signed j (mul (v j) (det k (minor (updRow M 0 v) 0 j))))
    rw [minor_updRow_zero, minor_updRow_zero, minor_updRow_zero, ← signed_add]
    congr 1; constructive_ring
  | k + 1, r + 1, M, u, v, hr => by
    show rangeSum (k + 1) _ = add (rangeSum (k + 1) _) (rangeSum (k + 1) _)
    rw [← rangeSum_add]; refine rangeSum_congr fun j _ => ?_
    show signed j (mul (M 0 j) (det k (minor (updRow M (r + 1) _) 0 j))) =
      add (signed j (mul (M 0 j) (det k (minor (updRow M (r + 1) u) 0 j))))
        (signed j (mul (M 0 j) (det k (minor (updRow M (r + 1) v) 0 j))))
    rw [minor_updRow_succ, minor_updRow_succ, minor_updRow_succ,
      det_updRow_add k r (minor M 0 j) _ _ (Nat.lt_of_succ_lt_succ hr),
      LawfulCommRing.left_distrib, signed_add]

theorem det_updRow_smul :
    ∀ (k r : Nat) (M : Nat → Nat → R) (c : R) (u : Nat → R), r < k →
      det k (updRow M r (fun j => mul c (u j))) = mul c (det k (updRow M r u))
  | 0, _, _, _, _, hr => absurd hr (Nat.not_lt_zero _)
  | k + 1, 0, M, c, u, _ => by
    show rangeSum (k + 1) _ = mul c (rangeSum (k + 1) _)
    rw [← rangeSum_mul_left]; refine rangeSum_congr fun j _ => ?_
    show signed j (mul (mul c (u j)) (det k (minor (updRow M 0 _) 0 j))) =
      mul c (signed j (mul (u j) (det k (minor (updRow M 0 u) 0 j))))
    rw [minor_updRow_zero, minor_updRow_zero, LawfulCommRing.mul_assoc, signed_mul_left]
  | k + 1, r + 1, M, c, u, hr => by
    show rangeSum (k + 1) _ = mul c (rangeSum (k + 1) _)
    rw [← rangeSum_mul_left]; refine rangeSum_congr fun j _ => ?_
    show signed j (mul (M 0 j) (det k (minor (updRow M (r + 1) _) 0 j))) =
      mul c (signed j (mul (M 0 j) (det k (minor (updRow M (r + 1) u) 0 j))))
    rw [minor_updRow_succ, minor_updRow_succ,
      det_updRow_smul k r (minor M 0 j) c _ (Nat.lt_of_succ_lt_succ hr), ← signed_mul_left]
    congr 1; constructive_ring

private theorem rangeSum_skipIdx :
    ∀ (n j₁ : Nat) (h : Nat → R),
      j₁ < n + 1 → h j₁ = zero → rangeSum n (fun j₂' => h (skipIdx j₁ j₂')) = rangeSum (n + 1) h
  | 0, j₁, h, hj₁, hz => by
    have hj0 : j₁ = 0 := by omega
    subst hj0; show zero = add zero (h 0); rw [hz, LawfulCommRing.add_zero]
  | n + 1, j₁, h, hj₁, hz => by
    if hEq : j₁ = n + 1 then
      subst hEq
      have hSame : rangeSum (n + 1) (fun j₂' => h (skipIdx (n + 1) j₂')) = rangeSum (n + 1) h :=
        rangeSum_congr fun j₂' hj₂' => by unfold skipIdx; rw [ite_pos hj₂']
      show rangeSum (n + 1) _ = add (rangeSum (n + 1) h) (h (n + 1))
      rw [hSame, hz, LawfulCommRing.add_zero]
    else
      show add (rangeSum n (fun j₂' => h (skipIdx j₁ j₂'))) (h (skipIdx j₁ n)) =
        add (rangeSum (n + 1) h) (h (n + 1))
      rw [rangeSum_skipIdx n j₁ h (by omega) hz]
      have hsk : skipIdx j₁ n = n + 1 := by unfold skipIdx; rw [ite_neg (by omega)]
      rw [hsk]

private theorem skipIdx_comm {j₁ j₂ : Nat} (hlt : j₁ < j₂) (c : Nat) :
    skipIdx j₁ (skipIdx (j₂ - 1) c) = skipIdx j₂ (skipIdx j₁ c) := by
  unfold skipIdx
  if h1 : c < j₂ - 1 then
    rw [ite_pos h1]
    if h2 : c < j₁ then rw [ite_pos h2, ite_pos (by omega)] else rw [ite_neg h2, ite_pos (by omega)]
  else
    rw [ite_neg h1, ite_neg (by omega)]
    if h2 : c < j₁ then exfalso; omega else rw [ite_neg h2, ite_neg (by omega)]

private theorem det_row01_eq_zero (k : Nat) (M : Nat → Nat → R)
    (hEq : ∀ j, j < k + 2 → M 0 j = M 1 j) :
    det (k + 2) M = zero := by
  let min2 (a b : Nat) : Nat → Nat → R := fun i c => M (i + 2) (skipIdx b (skipIdx a c))
  let g (j₁ j₂ : Nat) : R :=
    if j₁ = j₂ then zero
    else if j₂ < j₁ then signed (j₁ + j₂) (mul (mul (M 0 j₁) (M 1 j₂)) (det k (min2 j₂ j₁)))
    else signed (j₁ + j₂ - 1) (mul (mul (M 0 j₁) (M 1 j₂)) (det k (min2 j₁ j₂)))
  have hExpand : det (k + 2) M = rangeSum (k + 2) (fun j₁ => rangeSum (k + 2) (fun j₂ => g j₁ j₂)) := by
    show rangeSum (k + 2) _ = _; refine rangeSum_congr fun j₁ hj₁ => ?_
    show signed j₁ (mul (M 0 j₁) (rangeSum (k + 1) _)) = _
    rw [← rangeSum_mul_left, signed_rangeSum, ← rangeSum_skipIdx (k + 1) j₁ (g j₁) hj₁ (by dsimp [g]; rw [ite_pos rfl])]
    refine rangeSum_congr fun j₂' _ => ?_
    rw [← signed_mul_left, signed_signed, ← LawfulCommRing.mul_assoc]
    have hM1 : minor M 0 j₁ 0 j₂' = M 1 (skipIdx j₁ j₂') := rfl
    rw [hM1]
    if hlt : j₂' < j₁ then
      have hsk : skipIdx j₁ j₂' = j₂' := by unfold skipIdx; rw [ite_pos hlt]
      have hMinEq : det k (minor (minor M 0 j₁) 0 j₂') = det k (min2 j₂' j₁) := det_congr k fun _ _ _ _ => rfl
      dsimp only [g]; rw [hsk, ite_neg (Nat.ne_of_gt hlt), ite_pos hlt, hMinEq]
    else
      have hsk : skipIdx j₁ j₂' = j₂' + 1 := by unfold skipIdx; rw [ite_neg hlt]
      have hgt : j₁ < j₂' + 1 := by omega
      have hMinEq : det k (minor (minor M 0 j₁) 0 j₂') = det k (min2 j₁ (j₂' + 1)) :=
        det_congr k fun i _ c _ => congrArg (M (i + 2)) (skipIdx_comm hgt c)
      dsimp only [g]
      rw [hsk, ite_neg (Nat.ne_of_lt hgt), ite_neg (show ¬ j₂' + 1 < j₁ by omega),
        show j₁ + (j₂' + 1) - 1 = j₁ + j₂' by omega, hMinEq]
  rw [hExpand]
  have hFlip (a b : Nat) (hab : 1 ≤ a + b) (x : R) : signed (a + b) x = neg (signed (a + b - 1) x) := by
    unfold signed
    if hp : (a + b) % 2 = 0 then rw [ite_pos hp, ite_neg (by omega)]; constructive_ring
    else rw [ite_neg hp, ite_pos (by omega)]
  refine rangeSum_antisym_eq_zero (k + 2) g (fun i _ => by dsimp [g]; rw [ite_pos rfl]) (fun i hi j hj => ?_)
  if hij : i = j then
    subst hij; dsimp only [g]; rw [ite_pos rfl, LawfulCommRing.neg_zero]
  else if hji : j < i then
    dsimp only [g]
    rw [ite_neg hij, ite_pos hji, ite_neg (Ne.symm hij), ite_neg (show ¬ i < j by omega),
      show mul (M 0 i) (M 1 j) = mul (M 0 j) (M 1 i) by rw [← hEq i hi, ← hEq j hj, LawfulCommRing.mul_comm],
      Nat.add_comm j i, hFlip i j (by omega)]
  else
    have hijLt : i < j := by omega
    dsimp only [g]
    rw [ite_neg hij, ite_neg hji, ite_neg (Ne.symm hij), ite_pos hijLt,
      show mul (M 0 i) (M 1 j) = mul (M 0 j) (M 1 i) by rw [← hEq i hi, ← hEq j hj, LawfulCommRing.mul_comm],
      Nat.add_comm j i, hFlip i j (by omega), LawfulCommRing.neg_neg]

theorem det_adj_eq_zero :
    ∀ (k r : Nat) (M : Nat → Nat → R), r + 1 < k → (∀ j, j < k → M r j = M (r + 1) j) → det k M = zero
  | 0, _, _, hr, _ => absurd hr (Nat.not_lt_zero _)
  | 1, _, _, hr, _ => by exfalso; omega
  | k + 2, 0, M, _, hEq => det_row01_eq_zero k M hEq
  | k + 2, r + 1, M, hr, hEq =>
    rangeSum_eq_zero fun j _ => by
      have hm0 := det_adj_eq_zero (k + 1) r (minor M 0 j) (Nat.lt_of_succ_lt_succ hr)
        fun c hc => hEq (skipIdx j c) (skipIdx_lt hc)
      show signed j (mul (M 0 j) (det (k + 1) (minor M 0 j))) = zero
      rw [hm0, LawfulCommRing.mul_zero, signed_zero]

def swapAdjIdx (r i : Nat) : Nat := if i = r then r + 1 else if i = r + 1 then r else i

theorem det_swap_adj (k r : Nat) (M : Nat → Nat → R) (hr : r + 1 < k) :
    det k (fun i j => M (swapAdjIdx r i) j) = neg (det k M) := by
  let S := updRow (updRow M r (fun j => add (M r j) (M (r + 1) j)))
    (r + 1) (fun j => add (M r j) (M (r + 1) j))
  have hne : r ≠ r + 1 := by omega
  have hS0 : det k S = zero := det_adj_eq_zero k r S hr fun j _ => by
    dsimp only [S]; unfold updRow; rw [ite_neg hne, ite_pos rfl, ite_pos rfl]
  have hrLt : r < k := by omega
  dsimp only [S] at hS0; rw [det_updRow_add k (r + 1) _ _ _ hr] at hS0
  have h11 : det k (updRow (updRow M r (fun j => add (M r j) (M (r + 1) j))) (r + 1) (M r)) =
      det k (updRow (updRow M (r + 1) (M r)) r (fun j => add (M r j) (M (r + 1) j))) :=
    det_congr k fun i _ j _ => by
      unfold updRow
      if h1 : i = r then rw [h1, ite_neg hne, ite_pos rfl, ite_pos rfl]
      else if h2 : i = r + 1 then rw [h2, ite_pos rfl, ite_neg (Ne.symm hne), ite_pos rfl]
      else rw [ite_neg h2, ite_neg h1, ite_neg h1, ite_neg h2]
  have h12 : det k (updRow (updRow M r (fun j => add (M r j) (M (r + 1) j))) (r + 1) (M (r + 1))) =
      det k (updRow M r (fun j => add (M r j) (M (r + 1) j))) :=
    det_congr k fun i _ j _ => by
      unfold updRow
      if h2 : i = r + 1 then rw [h2, ite_pos rfl, ite_neg (Ne.symm hne)] else rw [ite_neg h2]
  rw [h11, h12, det_updRow_add k r _ _ _ hrLt, det_updRow_add k r _ _ _ hrLt] at hS0
  have hrr : det k (updRow (updRow M (r + 1) (M r)) r (M r)) = zero :=
    det_adj_eq_zero k r _ hr fun j _ => by unfold updRow; rw [ite_pos rfl, ite_neg (Ne.symm hne), ite_pos rfl]
  have hss : det k (updRow M r (M (r + 1))) = zero :=
    det_adj_eq_zero k r _ hr fun j _ => by unfold updRow; rw [ite_pos rfl, ite_neg (Ne.symm hne)]
  have hId : det k (updRow M r (M r)) = det k M :=
    det_congr k fun i _ j _ => by unfold updRow; if h1 : i = r then rw [h1, ite_pos rfl] else rw [ite_neg h1]
  have hSw : det k (updRow (updRow M (r + 1) (M r)) r (M (r + 1))) =
      det k (fun i j => M (swapAdjIdx r i) j) :=
    det_congr k fun i _ j _ => by
      unfold updRow swapAdjIdx
      if h1 : i = r then rw [h1, ite_pos rfl, ite_pos rfl]
      else if h2 : i = r + 1 then rw [h2, ite_neg (Ne.symm hne), ite_pos rfl, ite_neg (Ne.symm hne), ite_pos rfl]
      else rw [ite_neg h1, ite_neg h2, ite_neg h1, ite_neg h2]
  rw [hrr, hss, hId, hSw, LawfulCommRing.zero_add, LawfulCommRing.add_zero] at hS0
  apply LawfulCommRing.add_left_cancel (a := det k M)
  rw [LawfulCommRing.add_comm (det k M), hS0, LawfulCommRing.add_right_neg]

theorem det_eq_zero_of_row_eq (k r₁ r₂ : Nat) (M : Nat → Nat → R)
    (hr₁ : r₁ < r₂) (hr₂ : r₂ < k) (hEq : ∀ j, j < k → M r₁ j = M r₂ j) :
    det k M = zero := by
  have aux : ∀ (d r₂ : Nat) (M : Nat → Nat → R),
      r₂ - r₁ = d → r₁ < r₂ → r₂ < k → (∀ j, j < k → M r₁ j = M r₂ j) → det k M = zero := by
    intro d; induction d with
    | zero => intros; exfalso; omega
    | succ d ihd =>
      intro r₂ M hd hlt hk hE
      if hd0 : d = 0 then
        have hr₂Eq : r₂ = r₁ + 1 := by omega
        subst hr₂Eq; exact det_adj_eq_zero k r₁ M hk hE
      else
        let M' := fun i j => M (swapAdjIdx (r₂ - 1) i) j
        have hSw := det_swap_adj k (r₂ - 1) M (by omega)
        have hM'0 : det k M' = zero :=
          ihd (r₂ - 1) M' (by omega) (by omega) (by omega) fun j hj => by
            dsimp only [M']; unfold swapAdjIdx
            rw [ite_neg (show r₁ ≠ r₂ - 1 by omega), ite_neg (show r₁ ≠ r₂ - 1 + 1 by omega),
              ite_pos rfl, show r₂ - 1 + 1 = r₂ by omega]
            exact hE j hj
        rw [hM'0] at hSw; have h0 := congrArg neg hSw
        rw [LawfulCommRing.neg_zero, LawfulCommRing.neg_neg] at h0; exact h0.symm
  exact aux (r₂ - r₁) r₂ M rfl hr₁ hr₂ hEq

/-! ### Row-permutation factoring `det_perm_rows` and `det_matMul` -/

private def phiPot : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, σ => phiPot n σ + n * σ n

private theorem phiPot_le_cube :
    ∀ (n k : Nat) (σ : Nat → Nat), n ≤ k → (∀ i, i < k → σ i < k) → phiPot n σ ≤ n * k * k
  | 0, _, _, _, _ => Nat.zero_le _
  | n + 1, k, σ, hnk, hσ => by
    show phiPot n σ + n * σ n ≤ (n + 1) * k * k
    have ih := phiPot_le_cube n k σ (by omega) hσ
    have hsn : σ n < k := hσ n (by omega)
    have hmul : n * σ n ≤ k * k := Nat.mul_le_mul (by omega) (by omega)
    rw [Nat.succ_mul, Nat.add_mul]; omega

private theorem phiPot_swapAdj :
    ∀ (n r : Nat) (σ : Nat → Nat), r + 1 < n →
      phiPot n σ + σ r = phiPot n (fun i => σ (swapAdjIdx r i)) + σ (r + 1)
  | 0, _, _, hr => absurd hr (Nat.not_lt_zero _)
  | 1, _, _, hr => by omega
  | n + 2, r, σ, hr => by
    if hTop : r = n then
      subst r
      have aux : ∀ m, m ≤ n → phiPot m (fun i => σ (swapAdjIdx n i)) = phiPot m σ := by
        intro m; induction m with
        | zero => intro _; rfl
        | succ m ihm =>
          intro hm; show phiPot m _ + m * σ (swapAdjIdx n m) = phiPot m σ + m * σ m
          rw [ihm (by omega)]; unfold swapAdjIdx; rw [ite_neg (by omega), ite_neg (by omega)]
      show phiPot n σ + n * σ n + (n + 1) * σ (n + 1) + σ n =
        phiPot n (fun i => σ (swapAdjIdx n i)) + n * σ (swapAdjIdx n n) +
          (n + 1) * σ (swapAdjIdx n (n + 1)) + σ (n + 1)
      rw [aux n (Nat.le_refl _)]; unfold swapAdjIdx
      rw [ite_pos rfl, ite_neg (show n + 1 ≠ n by omega), ite_pos rfl, Nat.succ_mul, Nat.succ_mul]; omega
    else
      have ih := phiPot_swapAdj (n + 1) r σ (by omega)
      have hsk : swapAdjIdx r (n + 1) = n + 1 := by unfold swapAdjIdx; rw [ite_neg (by omega), ite_neg (by omega)]
      show phiPot (n + 1) σ + (n + 1) * σ (n + 1) + σ r =
        phiPot (n + 1) (fun i => σ (swapAdjIdx r i)) + (n + 1) * σ (swapAdjIdx r (n + 1)) + σ (r + 1)
      rw [hsk]; omega

private theorem find_dup_or_inv_or_inc (k : Nat) (σ : Nat → Nat) :
    (∃ i₁ i₂, i₁ < i₂ ∧ i₂ < k ∧ σ i₁ = σ i₂) ∨
    (∃ r, r + 1 < k ∧ σ (r + 1) < σ r) ∨ (∀ r, r + 1 < k → σ r < σ (r + 1)) := by
  have hAdj : ∀ m, m ≤ k →
      (∃ r, r + 1 < m ∧ σ (r + 1) ≤ σ r) ∨ (∀ r, r + 1 < m → σ r < σ (r + 1)) := by
    intro m; induction m with
    | zero => intro _; exact .inr fun _ h => absurd h (Nat.not_lt_zero _)
    | succ m ihm =>
      intro hm
      rcases ihm (Nat.le_of_succ_le hm) with ⟨r, hr, hle⟩ | hinc
      · exact .inl ⟨r, Nat.lt_succ_of_lt hr, hle⟩
      · if hm0 : m = 0 then exact .inr fun _ hr => by omega
        else if hle : σ m ≤ σ (m - 1) then
          exact .inl ⟨m - 1, by omega, by rwa [show m - 1 + 1 = m by omega]⟩
        else
          refine .inr fun r hr => ?_
          if hrEq : r = m - 1 then subst hrEq; rw [show m - 1 + 1 = m by omega]; omega
          else exact hinc r (by omega)
  rcases hAdj k (Nat.le_refl _) with ⟨r, hr, hle⟩ | hinc
  · if hEq : σ r = σ (r + 1) then exact .inl ⟨r, r + 1, Nat.lt_succ_self r, hr, hEq⟩
    else exact .inr (.inl ⟨r, hr, by omega⟩)
  · exact .inr (.inr hinc)

private theorem inc_endo_eq_id (k : Nat) (σ : Nat → Nat)
    (hBound : ∀ i, i < k → σ i < k) (hInc : ∀ r, r + 1 < k → σ r < σ (r + 1)) :
    ∀ i, i < k → σ i = i := by
  have hLo : ∀ i, i < k → i ≤ σ i := by
    intro i; induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ i ihi => intro hi; have := ihi (Nat.lt_of_succ_lt hi); have := hInc i hi; omega
  have hHi : ∀ d i, k - 1 - i = d → i < k → σ i ≤ i := by
    intro d; induction d with
    | zero =>
      intro i hd hi; have hiEq : i = k - 1 := by omega
      subst hiEq; have := hBound _ hi; omega
    | succ d ihd =>
      intro i hd hi; have hi1 : i + 1 < k := by omega
      have := ihd (i + 1) (by omega) hi1; have := hInc i hi1; omega
  intro i hi; exact Nat.le_antisymm (hHi (k - 1 - i) i rfl hi) (hLo i hi)

private theorem swapAdjIdx_lt {r i k : Nat} (hr : r + 1 < k) (hi : i < k) : swapAdjIdx r i < k := by
  unfold swapAdjIdx
  if h1 : i = r then rw [ite_pos h1]; exact hr
  else if h2 : i = r + 1 then rw [ite_neg h1, ite_pos h2]; omega
  else rw [ite_neg h1, ite_neg h2]; exact hi

theorem det_perm_rows (k : Nat) (B : Nat → Nat → R) (σ : Nat → Nat)
    (hBound : ∀ i, i < k → σ i < k) :
    det k (fun i j => B (σ i) j) = mul (det k (fun i j => idMat (σ i) j)) (det k B) := by
  have aux : ∀ (fuel : Nat) (σ : Nat → Nat),
      (∀ i, i < k → σ i < k) → k * k * k - phiPot k σ ≤ fuel →
      det k (fun i j => B (σ i) j) = mul (det k (fun i j => idMat (σ i) j)) (det k B) := by
    intro fuel; induction fuel with
    | zero =>
      intro σ hB hF
      rcases find_dup_or_inv_or_inc k σ with ⟨i₁, i₂, hi₁₂, hi₂k, hEq⟩ | ⟨r, hr, hinv⟩ | hinc
      · rw [det_eq_zero_of_row_eq k i₁ i₂ (fun i j => B (σ i) j) hi₁₂ hi₂k (fun j _ => congrArg (fun x => B x j) hEq),
          det_eq_zero_of_row_eq k i₁ i₂ (fun i j => idMat (σ i) j) hi₁₂ hi₂k (fun j _ => congrArg (fun x => idMat x j) hEq),
          LawfulCommRing.zero_mul]
      · exfalso
        let σ' := fun i => σ (swapAdjIdx r i)
        have hB' : ∀ i, i < k → σ' i < k := fun i hi => hB _ (swapAdjIdx_lt hr hi)
        have hCube := phiPot_le_cube k k σ' (Nat.le_refl k) hB'
        have hSw := phiPot_swapAdj k r σ hr
        dsimp only [σ'] at hCube; clear hB hB'; omega
      · have hId := inc_endo_eq_id k σ hB hinc
        rw [det_congr k (N := B) (fun i hi j _ => congrArg (fun x => B x j) (hId i hi)),
          det_congr k (N := idMat) (fun i hi j _ => congrArg (fun x => idMat x j) (hId i hi)),
          det_idMat, LawfulCommRing.one_mul]
    | succ fuel ih =>
      intro σ hB hF
      rcases find_dup_or_inv_or_inc k σ with ⟨i₁, i₂, hi₁₂, hi₂k, hEq⟩ | ⟨r, hr, hinv⟩ | hinc
      · rw [det_eq_zero_of_row_eq k i₁ i₂ (fun i j => B (σ i) j) hi₁₂ hi₂k (fun j _ => congrArg (fun x => B x j) hEq),
          det_eq_zero_of_row_eq k i₁ i₂ (fun i j => idMat (σ i) j) hi₁₂ hi₂k (fun j _ => congrArg (fun x => idMat x j) hEq),
          LawfulCommRing.zero_mul]
      · let σ' := fun i => σ (swapAdjIdx r i)
        have hB' : ∀ i, i < k → σ' i < k := fun i hi => hB _ (swapAdjIdx_lt hr hi)
        have hCube := phiPot_le_cube k k σ' (Nat.le_refl k) hB'
        have hSw := phiPot_swapAdj k r σ hr
        have hFuel' : k * k * k - phiPot k σ' ≤ fuel := by dsimp only [σ'] at hCube ⊢; clear ih hB hB'; omega
        have hStep := ih σ' hB' hFuel'
        have hNegB := det_swap_adj k r (fun i j => B (σ i) j) hr
        have hNegI := det_swap_adj k r (fun i j => idMat (R := R) (σ i) j) hr
        dsimp only [σ'] at hStep; rw [hNegB, hNegI] at hStep
        have h0 := congrArg neg hStep; rw [LawfulCommRing.neg_neg] at h0; rw [h0]; constructive_ring
      · have hId := inc_endo_eq_id k σ hB hinc
        rw [det_congr k (N := B) (fun i hi j _ => congrArg (fun x => B x j) (hId i hi)),
          det_congr k (N := idMat) (fun i hi j _ => congrArg (fun x => idMat x j) (hId i hi)),
          det_idMat, LawfulCommRing.one_mul]
  exact aux (k * k * k - phiPot k σ) σ hBound (Nat.le_refl _)

private theorem det_updRow_rangeSum (k r : Nat) (M : Nat → Nat → R) (hr : r < k) :
    ∀ (m : Nat) (c : Nat → R) (v : Nat → Nat → R),
      det k (updRow M r (fun j => rangeSum m (fun l => mul (c l) (v l j)))) =
        rangeSum m (fun l => mul (c l) (det k (updRow M r (v l))))
  | 0, _, _ => det_updRow_zero k r M hr
  | m + 1, c, v => by
    show det k (updRow M r (fun j => add _ _)) = add (rangeSum m _) _
    rw [det_updRow_add k r M _ _ hr, det_updRow_rangeSum k r M hr m c v,
      det_updRow_smul k r M (c m) (v m) hr]

def matMul (k : Nat) (A B : Nat → Nat → R) (i j : Nat) : R :=
  rangeSum k (fun l => mul (A i l) (B l j))

/-- **Multiplicativity of the determinant (`det_matMul`)**: over any `[LawfulCommRing R]`,
    `det k (matMul k A B) = mul (det k A) (det k B)`. -/
theorem det_matMul (k : Nat) (A B : Nat → Nat → R) :
    det k (matMul k A B) = mul (det k A) (det k B) := by
  let mix (m : Nat) (σ : Nat → Nat) (C : Nat → Nat → R) (i j : Nat) : R :=
    if i < m then matMul k A C i j else C (σ i) j
  have hStage : ∀ (m : Nat) (σ : Nat → Nat),
      m ≤ k → (∀ i, m ≤ i → i < k → σ i < k) →
      det k (mix m σ B) = mul (det k (mix m σ idMat)) (det k B) := by
    intro m; induction m with
    | zero => intro σ _ hσ; exact det_perm_rows k B σ (fun i hi => hσ i (Nat.zero_le i) hi)
    | succ m ihm =>
      intro σ hmk hσ
      have hmLt : m < k := hmk
      have hUpd (C : Nat → Nat → R) :
          det k (mix (m + 1) σ C) =
            det k (updRow (mix m σ C) m (fun j => rangeSum k (fun l => mul (A m l) (C l j)))) :=
        det_congr k fun i _ j _ => by
          show (if i < m + 1 then matMul k A C i j else C (σ i) j) =
            if i = m then rangeSum k (fun l => mul (A m l) (C l j))
            else if i < m then matMul k A C i j else C (σ i) j
          if hEq : i = m then rw [hEq, ite_pos (Nat.lt_succ_self m), ite_pos rfl]; rfl
          else if hLt : i < m then rw [ite_pos (Nat.lt_succ_of_lt hLt), ite_neg hEq, ite_pos hLt]
          else rw [ite_neg (by omega), ite_neg hEq, ite_neg hLt]
      rw [hUpd B, hUpd idMat, det_updRow_rangeSum k m (mix m σ B) hmLt k (A m) B,
        det_updRow_rangeSum k m (mix m σ idMat) hmLt k (A m) idMat, ← rangeSum_mul_right]
      refine rangeSum_congr fun l hl => ?_
      let σ' := fun i => if i = m then l else σ i
      have hMixEq (C : Nat → Nat → R) : det k (updRow (mix m σ C) m (C l)) = det k (mix m σ' C) :=
        det_congr k fun i _ j _ => by
          show (if i = m then C l j else if i < m then matMul k A C i j else C (σ i) j) =
            if i < m then matMul k A C i j else C (if i = m then l else σ i) j
          if hEq : i = m then rw [hEq, ite_pos rfl, ite_neg (Nat.lt_irrefl m), ite_pos rfl]
          else if hLt : i < m then rw [ite_neg hEq, ite_pos hLt, ite_pos hLt]
          else rw [ite_neg hEq, ite_neg hLt, ite_neg hLt, ite_neg hEq]
      rw [hMixEq B, hMixEq idMat,
        ihm σ' (Nat.le_of_succ_le hmk) (fun i hmi hik => by
          dsimp only [σ']; split
          · exact hl
          · next hne => exact hσ i (by omega) hik),
        LawfulCommRing.mul_assoc]
  have hAllB : det k (matMul k A B) = det k (mix k (fun i => i) B) :=
    det_congr k fun i hi _ _ => by dsimp only [mix]; rw [ite_pos hi]
  have hAllI : det k (mix k (fun i => i) idMat) = det k A :=
    det_congr k fun i hi j hj => by
      dsimp only [mix]; rw [ite_pos hi]; unfold matMul idMat
      rw [rangeSum_single hj _ fun l _ hne => by rw [ite_neg hne, LawfulCommRing.mul_zero]]
      rw [ite_pos rfl, LawfulCommRing.mul_one]
  rw [hAllB, hStage k (fun i => i) (Nat.le_refl k)
      (fun _ hle hlt => absurd hlt (Nat.not_lt_of_ge hle)), hAllI]

end Ring
end Mat


end Qsag

namespace Qsag.Math
/-! ## 2. Constructive Ring and Field Isomorphisms (`RingIso`, `FieldIso`) -/

/-- Constructive two-sided commutative ring isomorphism (`R ≃+* S`) preserving `0, 1, +, -, sub, *`. -/
structure RingIso (R S : Type) [CommRingOps R] [CommRingOps S] where
  toFun : R → S
  invFun : S → R
  left_inv : ∀ x : R, invFun (toFun x) = x
  right_inv : ∀ y : S, toFun (invFun y) = y
  map_zero : toFun CommRingOps.zero = CommRingOps.zero
  map_one : toFun CommRingOps.one = CommRingOps.one
  map_add : ∀ x y : R, toFun (CommRingOps.add x y) = CommRingOps.add (toFun x) (toFun y)
  map_neg : ∀ x : R, toFun (CommRingOps.neg x) = CommRingOps.neg (toFun x)
  map_sub : ∀ x y : R, toFun (CommRingOps.sub x y) = CommRingOps.sub (toFun x) (toFun y)
  map_mul : ∀ x y : R, toFun (CommRingOps.mul x y) = CommRingOps.mul (toFun x) (toFun y)

/-- Constructive two-sided field isomorphism extending `RingIso F G` with total `LawfulField.inv` preservation. -/
structure FieldIso (F G : Type) [LawfulField F] [LawfulField G] extends RingIso F G where
  map_inv : ∀ x : F, toFun (LawfulField.inv x) = LawfulField.inv (toFun x)

theorem RingIso.toFun_injective {R S : Type} [CommRingOps R] [CommRingOps S]
    (φ : RingIso R S) {x y : R} (h : φ.toFun x = φ.toFun y) : x = y := by
  have hInv := congrArg φ.invFun h
  rw [φ.left_inv, φ.left_inv] at hInv
  exact hInv

theorem RingIso.map_eq_zero_iff {R S : Type} [CommRingOps R] [CommRingOps S]
    (φ : RingIso R S) (x : R) :
    φ.toFun x = CommRingOps.zero ↔ x = CommRingOps.zero := by
  constructor
  · intro h
    apply φ.toFun_injective
    rw [h, φ.map_zero]
  · rintro rfl
    exact φ.map_zero

def RingIso.refl (R : Type) [CommRingOps R] : RingIso R R where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_zero := rfl
  map_one := rfl
  map_add _ _ := rfl
  map_neg _ := rfl
  map_sub _ _ := rfl
  map_mul _ _ := rfl

def RingIso.symm {R S : Type} [CommRingOps R] [CommRingOps S]
    (φ : RingIso R S) : RingIso S R where
  toFun := φ.invFun
  invFun := φ.toFun
  left_inv := φ.right_inv
  right_inv := φ.left_inv
  map_zero := by
    have h := congrArg φ.invFun φ.map_zero
    rw [φ.left_inv] at h
    exact h.symm
  map_one := by
    have h := congrArg φ.invFun φ.map_one
    rw [φ.left_inv] at h
    exact h.symm
  map_add x y := by
    apply φ.toFun_injective
    rw [φ.right_inv, φ.map_add, φ.right_inv, φ.right_inv]
  map_neg x := by
    apply φ.toFun_injective
    rw [φ.right_inv, φ.map_neg, φ.right_inv]
  map_sub x y := by
    apply φ.toFun_injective
    rw [φ.right_inv, φ.map_sub, φ.right_inv, φ.right_inv]
  map_mul x y := by
    apply φ.toFun_injective
    rw [φ.right_inv, φ.map_mul, φ.right_inv, φ.right_inv]

def RingIso.trans {R S T : Type} [CommRingOps R] [CommRingOps S] [CommRingOps T]
    (φ : RingIso R S) (ψ : RingIso S T) : RingIso R T where
  toFun x := ψ.toFun (φ.toFun x)
  invFun z := φ.invFun (ψ.invFun z)
  left_inv x := by rw [ψ.left_inv, φ.left_inv]
  right_inv z := by rw [φ.right_inv, ψ.right_inv]
  map_zero := by rw [φ.map_zero, ψ.map_zero]
  map_one := by rw [φ.map_one, ψ.map_one]
  map_add x y := by rw [φ.map_add, ψ.map_add]
  map_neg x := by rw [φ.map_neg, ψ.map_neg]
  map_sub x y := by rw [φ.map_sub, ψ.map_sub]
  map_mul x y := by rw [φ.map_mul, ψ.map_mul]

/-- **Automatic Inverse Preservation (`RingIso.toFieldIso`)**:
    Every `RingIso F G` between two `LawfulField`s satisfying `inv 0 = 0` automatically preserves
    `LawfulField.inv` for all `x : F` by uniqueness of multiplicative inverses (`0 Classical.choice`). -/
def RingIso.toFieldIso {F G : Type} [LawfulField F] [LawfulField G] [DecidableEq F]
    (φ : RingIso F G)
    (hInvZeroF : LawfulField.inv (CommRingOps.zero : F) = CommRingOps.zero)
    (hInvZeroG : LawfulField.inv (CommRingOps.zero : G) = CommRingOps.zero) :
    FieldIso F G where
  toRingIso := φ
  map_inv x := by
    by_cases hx : x = CommRingOps.zero
    · rw [hx, hInvZeroF, φ.map_zero, hInvZeroG]
    · have hFxNe : φ.toFun x ≠ CommRingOps.zero := fun h0 => hx ((φ.map_eq_zero_iff x).mp h0)
      have hProd : CommRingOps.mul (φ.toFun x) (φ.toFun (LawfulField.inv x)) = CommRingOps.one := by
        rw [← φ.map_mul, LawfulField.mul_inv_cancel hx, φ.map_one]
      have hLeft := congrArg (CommRingOps.mul (LawfulField.inv (φ.toFun x))) hProd
      rw [← LawfulCommRing.mul_assoc,
          LawfulCommRing.mul_comm (LawfulField.inv (φ.toFun x)) (φ.toFun x),
          LawfulField.mul_inv_cancel hFxNe,
          LawfulCommRing.one_mul,
          LawfulCommRing.mul_one] at hLeft
      exact hLeft

def FieldIso.refl (F : Type) [LawfulField F] : FieldIso F F where
  toRingIso := RingIso.refl F
  map_inv _ := rfl

def FieldIso.symm {F G : Type} [LawfulField F] [LawfulField G]
    (φ : FieldIso F G) : FieldIso G F where
  toRingIso := φ.toRingIso.symm
  map_inv y := by
    apply φ.toRingIso.toFun_injective
    dsimp only [RingIso.symm]
    rw [φ.right_inv, φ.map_inv, φ.right_inv]

def FieldIso.trans {F G H : Type} [LawfulField F] [LawfulField G] [LawfulField H]
    (φ : FieldIso F G) (ψ : FieldIso G H) : FieldIso F H where
  toRingIso := φ.toRingIso.trans ψ.toRingIso
  map_inv x := by
    dsimp only [RingIso.trans]
    rw [φ.map_inv, ψ.map_inv]


end Qsag.Math

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
set_option autoImplicit false
theorem nodup_filter_bool {α : Type} (p : α → Bool) {l : List α} (h : l.Nodup) : (l.filter p).Nodup := List.Pairwise.filter p h
open CommRingOps RoundPoly UPoly

/-- A ring in which `1 ≠ 0`. -/
class NontrivialRing (D : Type) [CommRingOps D] : Prop where
  one_ne_zero : (one : D) ≠ zero

instance (F : Type) [LawfulField F] : NontrivialRing F := ⟨LawfulField.one_ne_zero⟩

/-- A numerator and a nonzero denominator. -/
structure PreFrac (D : Type) [CommRingOps D] where
  num : D
  den : D
  den_ne : den ≠ zero

section Domain
variable {D : Type} [LawfulCommRing D] [NoZeroDivisors D]

theorem mul_ne_zero' {a b : D} (ha : a ≠ zero) (hb : b ≠ zero) : mul a b ≠ zero := fun h =>
  (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h).elim ha hb

theorem mul_right_cancel' {x y d : D} (hd : d ≠ zero) (h : mul x d = mul y d) : x = y := by
  have h0 : mul (sub x y) d = zero := by
    rw [LawfulCommRing.sub_mul, h, LawfulCommRing.sub_self]
  rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h0 with h1 | h1
  · exact LawfulCommRing.sub_eq_zero_iff.mp h1
  · exact absurd h1 hd

end Domain

namespace PreFrac
variable {D : Type} [LawfulCommRing D] [NoZeroDivisors D]

/-- Equality of fractions by cross-multiplication. -/
def Rel (a b : PreFrac D) : Prop := mul a.num b.den = mul b.num a.den

theorem Rel.trans' {a b c : PreFrac D} (hab : Rel a b) (hbc : Rel b c) : Rel a c := by
  unfold Rel at *
  apply mul_right_cancel' b.den_ne
  have e1 : mul (mul a.num c.den) b.den = mul (mul a.num b.den) c.den := by constructive_ring
  have e2 : mul (mul b.num a.den) c.den = mul (mul b.num c.den) a.den := by constructive_ring
  have e3 : mul (mul c.num b.den) a.den = mul (mul c.num a.den) b.den := by constructive_ring
  rw [e1, hab, e2, hbc, e3]

instance setoid : Setoid (PreFrac D) where
  r := Rel
  iseqv := ⟨fun _ => by unfold Rel; rfl, fun h => by unfold Rel at *; exact h.symm, Rel.trans'⟩

def padd (a b : PreFrac D) : PreFrac D :=
  ⟨add (mul a.num b.den) (mul b.num a.den), mul a.den b.den, mul_ne_zero' a.den_ne b.den_ne⟩

def pmul (a b : PreFrac D) : PreFrac D :=
  ⟨mul a.num b.num, mul a.den b.den, mul_ne_zero' a.den_ne b.den_ne⟩

def pneg (a : PreFrac D) : PreFrac D := ⟨neg a.num, a.den, a.den_ne⟩

def pinv [DecidableEq D] [NontrivialRing D] (a : PreFrac D) : PreFrac D :=
  if h : a.num = zero then ⟨zero, one, NontrivialRing.one_ne_zero⟩ else ⟨a.den, a.num, h⟩

theorem padd_rel {a a' b b' : PreFrac D} (ha : Rel a a') (hb : Rel b b') :
    Rel (padd a b) (padd a' b') := by
  unfold Rel at *
  show mul (add (mul a.num b.den) (mul b.num a.den)) (mul a'.den b'.den) =
    mul (add (mul a'.num b'.den) (mul b'.num a'.den)) (mul a.den b.den)
  have e1 : mul (add (mul a.num b.den) (mul b.num a.den)) (mul a'.den b'.den) =
      add (mul (mul a.num a'.den) (mul b.den b'.den))
        (mul (mul b.num b'.den) (mul a.den a'.den)) := by constructive_ring
  rw [e1, ha, hb]; constructive_ring

theorem pmul_rel {a a' b b' : PreFrac D} (ha : Rel a a') (hb : Rel b b') :
    Rel (pmul a b) (pmul a' b') := by
  unfold Rel at *
  show mul (mul a.num b.num) (mul a'.den b'.den) = mul (mul a'.num b'.num) (mul a.den b.den)
  have e1 : mul (mul a.num b.num) (mul a'.den b'.den) =
      mul (mul a.num a'.den) (mul b.num b'.den) := by constructive_ring
  rw [e1, ha, hb]; constructive_ring

omit [NoZeroDivisors D] in
theorem pneg_rel {a a' : PreFrac D} (ha : Rel a a') : Rel (pneg a) (pneg a') := by
  unfold Rel at *
  show mul (neg a.num) a'.den = mul (neg a'.num) a.den
  rw [LawfulCommRing.neg_mul, ha, LawfulCommRing.neg_mul]

theorem pinv_rel [DecidableEq D] [NontrivialRing D] {a a' : PreFrac D} (ha : Rel a a') :
    Rel (pinv a) (pinv a') := by
  unfold Rel at ha
  have hiff : a.num = zero ↔ a'.num = zero := by
    constructor
    · intro h
      rw [h, LawfulCommRing.zero_mul] at ha
      exact (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero ha.symm).elim id
        (fun e => absurd e a.den_ne)
    · intro h
      rw [h, LawfulCommRing.zero_mul] at ha
      exact (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero ha).elim id
        (fun e => absurd e a'.den_ne)
  unfold pinv
  split
  · next h =>
    split
    · rfl
    · next h' => exact absurd (hiff.mp h) h'
  · next h =>
    split
    · next h' => exact absurd (hiff.mpr h') h
    · show mul a.den a'.num = mul a'.den a.num
      rw [LawfulCommRing.mul_comm, ← ha, LawfulCommRing.mul_comm]

end PreFrac

/-- The fraction field of the integral domain `D`. -/
abbrev Frac (D : Type) [LawfulCommRing D] [NoZeroDivisors D] : Type :=
  Quotient (PreFrac.setoid (D := D))

namespace Frac
variable {D : Type} [LawfulCommRing D] [NoZeroDivisors D] [DecidableEq D] [NontrivialRing D]
open PreFrac

/-- The class of `n/d`. -/
def mk (a : PreFrac D) : Frac D := Quotient.mk _ a

omit [DecidableEq D] [NontrivialRing D] in
theorem sound {a b : PreFrac D} (h : Rel a b) : mk a = mk b := Quotient.sound h

omit [DecidableEq D] [NontrivialRing D] in
theorem exact {a b : PreFrac D} (h : mk a = mk b) : Rel a b := Quotient.exact h

instance : DecidableEq (Frac D) := fun x y =>
  Quotient.recOnSubsingleton₂ x y fun a b =>
    if h : mul a.num b.den = mul b.num a.den then .isTrue (Quotient.sound (by change Rel a b; unfold Rel; exact h))
    else .isFalse (fun e => h (by have hr : Rel a b := Quotient.exact e; unfold Rel at hr; exact hr))

def fadd (x y : Frac D) : Frac D :=
  Quotient.liftOn₂ x y (fun a b => mk (padd a b)) (fun _ _ _ _ ha hb => sound (padd_rel ha hb))

def fmul (x y : Frac D) : Frac D :=
  Quotient.liftOn₂ x y (fun a b => mk (pmul a b)) (fun _ _ _ _ ha hb => sound (pmul_rel ha hb))

def fneg (x : Frac D) : Frac D :=
  Quotient.liftOn x (fun a => mk (pneg a)) (fun _ _ ha => sound (pneg_rel ha))

def finv (x : Frac D) : Frac D :=
  Quotient.liftOn x (fun a => mk (pinv a)) (fun _ _ ha => sound (pinv_rel ha))

/-- The class of `c/1`. -/
def ofD (c : D) : Frac D := mk ⟨c, one, NontrivialRing.one_ne_zero⟩

omit [DecidableEq D] [NontrivialRing D] in
theorem ind₁ {p : Frac D → Prop} (h : ∀ a, p (mk a)) : ∀ x, p x := Quotient.ind h

omit [DecidableEq D] [NontrivialRing D] in
theorem ind₂ {p : Frac D → Frac D → Prop} (h : ∀ a b, p (mk a) (mk b)) : ∀ x y, p x y :=
  fun x y => Quotient.inductionOn₂ x y h

omit [DecidableEq D] [NontrivialRing D] in
theorem ind₃ {p : Frac D → Frac D → Frac D → Prop}
    (h : ∀ a b c, p (mk a) (mk b) (mk c)) : ∀ x y z, p x y z :=
  fun x y z => Quotient.inductionOn₃ x y z h

instance instLawfulField : LawfulField (Frac D) where
  zero := ofD zero
  one := ofD one
  add := fadd
  mul := fmul
  neg := fneg
  sub x y := fadd x (fneg y)
  inv := finv
  add_assoc := ind₃ fun a b c => by
    exact sound (by unfold Rel padd; dsimp only; constructive_ring)
  add_comm := ind₂ fun a b => by exact sound (by unfold Rel padd; dsimp only; constructive_ring)
  zero_add := ind₁ fun a => by exact sound (by unfold Rel padd; dsimp only; constructive_ring)
  add_zero := ind₁ fun a => by exact sound (by unfold Rel padd; dsimp only; constructive_ring)
  add_left_neg := ind₁ fun a => by
    exact sound (by unfold Rel padd pneg; dsimp only; constructive_ring)
  sub_eq_add_neg _ _ := by rfl
  mul_assoc := ind₃ fun a b c => by
    exact sound (by unfold Rel pmul; dsimp only; constructive_ring)
  mul_comm := ind₂ fun a b => by exact sound (by unfold Rel pmul; dsimp only; constructive_ring)
  one_mul := ind₁ fun a => by exact sound (by unfold Rel pmul; dsimp only; constructive_ring)
  mul_one := ind₁ fun a => by exact sound (by unfold Rel pmul; dsimp only; constructive_ring)
  left_distrib := ind₃ fun a b c => by
    exact sound (by unfold Rel pmul padd; dsimp only; constructive_ring)
  right_distrib := ind₃ fun a b c => by
    exact sound (by unfold Rel pmul padd; dsimp only; constructive_ring)
  zero_ne_one := by
    intro h
    have h' : mul (zero : D) one = mul one one := exact h
    rw [LawfulCommRing.zero_mul, LawfulCommRing.mul_one] at h'
    exact NontrivialRing.one_ne_zero h'.symm
  mul_inv_cancel := by
    intro x
    induction x using ind₁ with | h a =>
    intro hx
    have hn : a.num ≠ zero := fun e => hx (sound (by
      show mul a.num one = mul zero a.den
      rw [e, LawfulCommRing.zero_mul, LawfulCommRing.zero_mul]))
    exact sound (by
      unfold pinv; split
      · next h => exact absurd h hn
      · show mul (mul a.num a.den) one = mul one (mul a.den a.num)
        constructive_ring)

/-- The embedding `D → Frac D`. -/
def of : RingHom D (Frac D) where
  toFun := ofD
  map_zero := by rfl
  map_one := by rfl
  map_add a b := sound (by
    show mul (add a b) (mul one one) = mul (add (mul a one) (mul b one)) one
    constructive_ring)
  map_mul a b := sound (by
    show mul (mul a b) (mul one one) = mul (mul a b) one
    constructive_ring)

theorem of_injective {a b : D} (h : (of (D := D)).toFun a = (of (D := D)).toFun b) : a = b := by
  have h' : mul a one = mul b one := exact h
  rwa [LawfulCommRing.mul_one, LawfulCommRing.mul_one] at h'

end Frac

/-! ## Base change of coefficients -/

namespace UPoly

section Map
variable {R S T : Type} [LawfulCommRing R] [DecidableEq R] [LawfulCommRing S] [DecidableEq S]
  [LawfulCommRing T]

/-- Coefficientwise base change `R[X] → S[X]`. -/
def mapHom (φ : RingHom R S) : RingHom (UPoly R) (UPoly S) := eval₂Hom (CHom.comp φ) X

theorem mapHom_apply (φ : RingHom R S) (p : UPoly R) :
    (mapHom φ).toFun p = ofList (p.coeffs.map φ.toFun) := by
  show evalCoeffs (p.coeffs.map (CHom.comp φ).toFun) X = _
  generalize p.coeffs = l
  induction l with
  | nil => rfl
  | cons c cs ih =>
    show add (C (φ.toFun c)) (mul X (evalCoeffs (cs.map (CHom.comp φ).toFun) X)) =
      ofList (φ.toFun c :: cs.map φ.toFun)
    rw [ih, ofList_cons]

theorem coeffAt_mapHom (φ : RingHom R S) (p : UPoly R) (k : Nat) :
    coeffAt ((mapHom φ).toFun p).coeffs k = φ.toFun (coeffAt p.coeffs k) := by
  rw [mapHom_apply, coeffAt_ofList, RingHom.coeffAt_map]

theorem mapHom_C (φ : RingHom R S) (c : R) : (mapHom φ).toFun (C c) = C (φ.toFun c) :=
  eval₂_C _ _ _

theorem mapHom_inj (φ : RingHom R S) (hinj : ∀ x, φ.toFun x = zero → x = zero)
    (p : UPoly R) (h : (mapHom φ).toFun p = zero) : p = zero :=
  ext_coeffAt fun k => by
    have := congrArg (fun q : UPoly S => coeffAt q.coeffs k) h
    simp only [coeffAt_mapHom, coeffs_zero, coeffAt_nil] at this
    rw [coeffs_zero, coeffAt_nil]; exact hinj _ this

theorem natDeg_mapHom_le (φ : RingHom R S) (p : UPoly R) :
    ((mapHom φ).toFun p).natDeg ≤ p.natDeg :=
  natDeg_le_of_coeffAt _ _ (fun k hk => by
    rw [coeffAt_mapHom, p.coeffAt_eq_zero_of_natDeg_lt hk, φ.map_zero])

theorem natDeg_mapHom (φ : RingHom R S) (hinj : ∀ x, φ.toFun x = zero → x = zero)
    (p : UPoly R) : ((mapHom φ).toFun p).natDeg = p.natDeg := by
  apply Nat.le_antisymm (natDeg_mapHom_le φ p)
  apply Decidable.byContradiction
  intro hlt
  have hz := ((mapHom φ).toFun p).coeffAt_eq_zero_of_natDeg_lt (Nat.lt_of_not_le hlt)
  rw [coeffAt_mapHom] at hz
  have hp : p ≠ zero := fun e => by
    rw [e] at hlt; exact hlt (Nat.zero_le _)
  exact lead_ne_zero hp (hinj _ hz)

theorem eval₂_mapHom (ψ : RingHom S T) (s : T) (φ : RingHom R S) (p : UPoly R) :
    eval₂ ψ s ((mapHom φ).toFun p) = eval₂ (ψ.comp φ) s p := by
  rw [mapHom_apply, eval₂_ofList, List.map_map]; rfl

theorem eval_mapHom (φ : RingHom R S) (p : UPoly R) (y : R) :
    ((mapHom φ).toFun p).eval (φ.toFun y) = φ.toFun (p.eval y) := by
  show eval₂ (RingHom.id S) (φ.toFun y) ((mapHom φ).toFun p) = φ.toFun (eval₂ (RingHom.id R) y p)
  rw [eval₂_mapHom, hom_eval₂]; rfl

/-- Evaluating a doubly base-changed polynomial at the image of a point. -/
theorem eval₂_mapHom_mapHom (φ : RingHom R S) (Q : UPoly (UPoly R)) (y z : R) :
    eval₂ (evalHom (φ.toFun y)) (φ.toFun z) ((mapHom (mapHom φ)).toFun Q) =
      φ.toFun (eval₂ (evalHom y) z Q) := by
  rw [eval₂_mapHom, hom_eval₂]
  show evalCoeffs (Q.coeffs.map _) _ = evalCoeffs (Q.coeffs.map _) _
  congr 1
  apply List.map_congr_left
  intro q _
  exact eval_mapHom φ q y

/-- Base change does not raise the total degree. -/
theorem wdeg_mapHom_mapHom_le (φ : RingHom R S) (Q : UPoly (UPoly R)) :
    ((mapHom (mapHom φ)).toFun Q).wdeg natDeg 1 ≤ Q.wdeg natDeg 1 := by
  apply wdeg_le
  intro k hk
  rw [coeffAt_mapHom] at hk ⊢
  have hne : coeffAt Q.coeffs k ≠ zero := fun e => hk (by rw [e, (mapHom φ).map_zero])
  have := le_wdeg natDeg 1 Q k hne
  have := natDeg_mapHom_le φ (coeffAt Q.coeffs k)
  omega

end Map

section Hasse
variable {R : Type} [LawfulCommRing R] [DecidableEq R]

/-- Hasse derivatives respect coefficient filtrations: the `i`-th coefficient of the `k`-th
    derivative is an integer combination of the coefficient of index `i + k`. -/
theorem coeffAt_hasse_graded : ∀ (l : List R) (L : Nat → R → Prop), (∀ j, L j zero) →
    (∀ j x y, L j x → L j y → L j (add x y)) → (∀ j, L j (coeffAt l j)) →
    ∀ k i, L (i + k) (coeffAt (gsUniHasse (l.map C) k (X : UPoly R)).coeffs i)
  | [], L, hz, _, _, k, i => by
    show L (i + k) (coeffAt (zero : UPoly R).coeffs i); rw [coeffs_zero, coeffAt_nil]; exact hz _
  | c :: cs, L, hz, hadd, hl, k, i => by
    have ih := coeffAt_hasse_graded cs (fun j => L (j + 1)) (fun _ => hz _) (fun _ => hadd _)
      (fun j => hl (j + 1))
    cases k with
    | zero =>
      show L (i + 0) (coeffAt (add (C c) (mul X (gsUniHasse (cs.map C) 0 X))).coeffs i)
      rw [coeffAt_add]
      cases i with
      | zero => rw [coeffAt_X_mul_zero, coeffAt_C_zero, LawfulCommRing.add_zero]; exact hl 0
      | succ i => rw [coeffAt_X_mul_succ, coeffAt_C_succ, LawfulCommRing.zero_add]; exact ih 0 i
    | succ k =>
      show L (i + (k + 1)) (coeffAt (add (gsUniHasse (cs.map C) k X)
        (mul X (gsUniHasse (cs.map C) (k + 1) X))).coeffs i)
      rw [coeffAt_add]
      apply hadd
      · exact ih k i
      · cases i with
        | zero => rw [coeffAt_X_mul_zero]; exact hz _
        | succ i =>
          rw [coeffAt_X_mul_succ]
          have := ih (k + 1) i
          rwa [show i + (k + 1) + 1 = i + 1 + (k + 1) by omega] at this

/-- Differentiating `k` times lowers the weighted degree by `k` times the variable weight. -/
theorem wdeg_hasse_le (w : R → Nat) (hw : DegFn w) (s k : Nat) (p : UPoly R) :
    (hasse k p).wdeg w s ≤ p.wdeg w s - s * k := by
  apply wdeg_le
  intro i h
  have key : coeffAt (hasse k p).coeffs i ≠ zero →
      w (coeffAt (hasse k p).coeffs i) + s * (i + k) ≤ p.wdeg w s :=
    coeffAt_hasse_graded p.coeffs (fun j x => x ≠ zero → w x + s * j ≤ p.wdeg w s)
      (fun _ h => absurd rfl h) (fun _ _ _ hx hy h => bnd_add hw hx hy h) (le_wdeg w s p) k i
  have := key h
  rw [Nat.mul_add] at this; omega
end Hasse

/-- The product of a list of polynomials. -/
def prodList {R : Type} [LawfulCommRing R] [DecidableEq R] : List (UPoly R) → UPoly R
  | [] => one
  | p :: ps => mul p (prodList ps)

end UPoly

instance (F : Type) [LawfulField F] [DecidableEq F] : NoZeroDivisors (UPoly F) :=
  letI : NoZeroDivisors F := LawfulField.toNoZeroDivisors F
  inferInstance

instance (R : Type) [LawfulCommRing R] [DecidableEq R] [NontrivialRing R] :
    NontrivialRing (UPoly R) where
  one_ne_zero := fun e => NontrivialRing.one_ne_zero (D := R) (by
    have := congrArg (fun p : UPoly R => coeffAt p.coeffs 0) e
    simp only [UPoly.one_eq_C, UPoly.coeffAt_C_zero, UPoly.coeffs_zero, coeffAt_nil] at this
    exact this)

/-- Rational functions `F(X)`. -/
abbrev RatFunc (F : Type) [LawfulField F] [DecidableEq F] := Frac (UPoly F)

namespace UPoly
variable {R : Type} [LawfulCommRing R] [DecidableEq R]

theorem natDeg_one : (one : UPoly R).natDeg = 0 := by
  have := trimPoly_length_le [(one : R)]
  show (ofList [one]).coeffs.length - 1 = 0
  rw [coeffs_ofList]
  simp only [List.length_cons, List.length_nil] at this; omega

theorem prodList_ne_zero [NoZeroDivisors R] [NontrivialRing R] :
    ∀ ps : List (UPoly R), (∀ p ∈ ps, p ≠ zero) → prodList ps ≠ zero
  | [], _ => NontrivialRing.one_ne_zero
  | p :: ps, h => mul_ne_zero' (h p (.head _))
      (prodList_ne_zero ps (fun q hq => h q (.tail _ hq)))

theorem eval_prodList_eq_zero (y : R) : ∀ ps : List (UPoly R),
    (∃ p ∈ ps, p.eval y = zero) → (prodList ps).eval y = zero
  | [], h => by obtain ⟨_, hp, _⟩ := h; cases hp
  | p :: ps, h => by
    show (evalHom y).toFun (mul p (prodList ps)) = zero
    rw [(evalHom y).map_mul]
    obtain ⟨q, hq, hz⟩ := h
    cases hq with
    | head => rw [evalHom_apply, hz, LawfulCommRing.zero_mul]
    | tail _ hq' =>
      rw [evalHom_apply, evalHom_apply, eval_prodList_eq_zero y ps ⟨q, hq', hz⟩,
        LawfulCommRing.mul_zero]

end UPoly

/-! ## Squarefree factors and `[CWYZ26]` Lemma 4.3 -/

/-! ## Dynamic GCD splitting over a field -/

namespace UPoly
variable {K : Type} [LawfulField K] [DecidableEq K]

local instance : NoZeroDivisors K := LawfulField.toNoZeroDivisors K

/-- Euclidean division in `K[Z]`. -/
def divMod (a b : UPoly K) : UPoly K × UPoly K :=
  (ofList (polyDivMod a.coeffs b.coeffs).1, ofList (polyDivMod a.coeffs b.coeffs).2)

theorem divMod_spec (a b : UPoly K) (hb : b ≠ zero) :
    a = add (mul (divMod a b).1 b) (divMod a b).2 ∧
      (divMod a b).2.coeffs.length < b.coeffs.length := by
  have hb' : trimPoly b.coeffs ≠ [] := by
    rw [b.trimmed]; exact fun e => hb ((eq_zero_iff b).mpr e)
  have h := polyDivMod_spec a.coeffs b.coeffs hb'
  unfold divMod
  generalize polyDivMod a.coeffs b.coeffs = qr at h
  obtain ⟨q, r⟩ := qr
  obtain ⟨hq, hr, heq, hlen⟩ := h
  have hq' : trimPoly q = q := hq
  have hr' : trimPoly r = r := hr
  refine ⟨ext ?_, ?_⟩
  · show a.coeffs = pAdd (pMul (trimPoly q) b.coeffs) (trimPoly r)
    rw [hq', hr', ← heq, a.trimmed]
  · show (trimPoly r).length < b.coeffs.length
    rw [hr']; rwa [b.trimmed] at hlen

/-- Extended Euclid: `(g, u, v)` with `u·a + v·b = g` and `g` dividing both. -/
def xgcdAux : Nat → UPoly K → UPoly K → UPoly K × UPoly K × UPoly K
  | 0, a, _ => (a, one, zero)
  | fuel + 1, a, b =>
    if b = zero then (a, one, zero)
    else
      let r := xgcdAux fuel b (divMod a b).2
      (r.1, r.2.2, sub r.2.1 (mul r.2.2 (divMod a b).1))

theorem xgcdAux_spec : ∀ (fuel : Nat) (a b : UPoly K), b.coeffs.length ≤ fuel →
    add (mul (xgcdAux fuel a b).2.1 a) (mul (xgcdAux fuel a b).2.2 b) = (xgcdAux fuel a b).1 ∧
      (∃ s, a = mul (xgcdAux fuel a b).1 s) ∧ (∃ t, b = mul (xgcdAux fuel a b).1 t)
  | 0, a, b, h => by
    have hb : b = zero := (eq_zero_iff b).mpr (List.eq_nil_of_length_eq_zero (by omega))
    subst hb
    exact ⟨by show add (mul one a) (mul zero zero) = a; constructive_ring,
      ⟨one, (LawfulCommRing.mul_one a).symm⟩, ⟨zero, (LawfulCommRing.mul_zero a).symm⟩⟩
  | fuel + 1, a, b, h => by
    unfold xgcdAux
    split
    · next hb =>
      subst hb
      exact ⟨by show add (mul one a) (mul zero zero) = a; constructive_ring,
        ⟨one, (LawfulCommRing.mul_one a).symm⟩, ⟨zero, (LawfulCommRing.mul_zero a).symm⟩⟩
    · next hb =>
      obtain ⟨hdiv, hlen⟩ := divMod_spec a b hb
      obtain ⟨hbez, ⟨s, hs⟩, ⟨t, ht⟩⟩ := xgcdAux_spec fuel b (divMod a b).2 (by omega)
      generalize xgcdAux fuel b (divMod a b).2 = res at hbez hs ht
      generalize (divMod a b).1 = q at hdiv
      generalize (divMod a b).2 = r at hdiv hbez ht
      refine ⟨?_, ⟨add (mul q s) t, ?_⟩, ⟨s, hs⟩⟩
      · show add (mul res.2.2 a) (mul (sub res.2.1 (mul res.2.2 q)) b) = res.1
        rw [← hbez, hdiv]; constructive_ring
      · rw [hdiv, hs, ht]; constructive_ring

/-- A gcd of `R` and `G` with its Bézout cofactors. -/
def xgcd (R G : UPoly K) : UPoly K × UPoly K × UPoly K := xgcdAux G.coeffs.length R G

/-- **D5 splitting step.** Testing `G` against a modulus `R ≠ 0` has three outcomes: `G` is
    invertible modulo `R`; or `R` divides `G`; or `R = g·q` splits into two factors of
    positive degree, with `deg g + deg q = deg R`, so the degree sum of a factor list is
    preserved and its length strictly grows. -/
theorem d5_split (R G : UPoly K) (hR : R ≠ zero) :
    (∃ u v, add (mul u R) (mul v G) = one) ∨ (∃ t, G = mul R t) ∨
      (∃ g q, R = mul g q ∧ 0 < g.natDeg ∧ 0 < q.natDeg ∧ g.natDeg + q.natDeg = R.natDeg ∧
        ∃ t, G = mul g t) := by
  obtain ⟨hbez, ⟨s, hs⟩, ⟨t, ht⟩⟩ := xgcdAux_spec G.coeffs.length R G (Nat.le_refl _)
  generalize (xgcdAux G.coeffs.length R G).1 = g at hbez hs ht
  generalize (xgcdAux G.coeffs.length R G).2.1 = u at hbez
  generalize (xgcdAux G.coeffs.length R G).2.2 = v at hbez
  have hg : g ≠ zero := fun e => hR (by rw [hs, e, LawfulCommRing.zero_mul])
  have hs0 : s ≠ zero := fun e => hR (by rw [hs, e, LawfulCommRing.mul_zero])
  have hdeg : R.natDeg = g.natDeg + s.natDeg := by rw [hs]; exact natDeg_mul hg hs0
  have unit : ∀ p : UPoly K, p ≠ zero → p.natDeg = 0 → mul p (C (LawfulField.inv p.lead)) = one := by
    intro p hp hd
    have hpC : p = C p.lead := ext_coeffAt fun k => by
      cases k with
      | zero => rw [coeffAt_C_zero]; show _ = coeffAt p.coeffs p.natDeg; rw [hd]
      | succ k => rw [coeffAt_C_succ]; exact p.coeffAt_eq_zero_of_natDeg_lt (by omega)
    have h1 : mul (C p.lead) (C (LawfulField.inv p.lead)) = C (mul p.lead (LawfulField.inv p.lead)) :=
      (CHom.map_mul _ _).symm
    rw [LawfulField.mul_inv_cancel (lead_ne_zero hp)] at h1
    exact (congrArg (fun x => mul x (C (LawfulField.inv p.lead))) hpC).trans h1
  if h0 : g.natDeg = 0 then
    refine .inl ⟨mul (C (LawfulField.inv g.lead)) u, mul (C (LawfulField.inv g.lead)) v, ?_⟩
    rw [← unit g hg h0, ← hbez]; constructive_ring
  else if h1 : s.natDeg = 0 then
    refine .inr (.inl ⟨mul (C (LawfulField.inv s.lead)) t, ?_⟩)
    have hu := unit s hs0 h1
    have : mul R (mul (C (LawfulField.inv s.lead)) t) =
        mul g (mul (mul s (C (LawfulField.inv s.lead))) t) := by rw [hs]; constructive_ring
    rw [this, hu, ht]; constructive_ring
  else
    exact .inr (.inr ⟨g, s, hs, by omega, by omega, hdeg.symm, t, ht⟩)

end UPoly

/-! ## Witnesses -/

end Qsag

section
namespace Qsag

set_option autoImplicit false

namespace JohnsonBound

/-- Sum of a list of natural numbers. -/
def sumNat : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumNat xs

theorem sumNat_map_add {α : Type} (f g : α → Nat) :
    ∀ xs : List α, sumNat (xs.map (fun z => f z + g z)) = sumNat (xs.map f) + sumNat (xs.map g)
  | [] => rfl
  | x :: xs => by
    show f x + g x + sumNat _ = (f x + sumNat _) + (g x + sumNat _)
    rw [sumNat_map_add f g xs]
    omega

theorem sumNat_map_le {α : Type} (f g : α → Nat) :
    ∀ (xs : List α), (∀ z ∈ xs, f z ≤ g z) → sumNat (xs.map f) ≤ sumNat (xs.map g)
  | [], _ => Nat.le_refl 0
  | x :: xs, h =>
    Nat.add_le_add (h x (.head _)) (sumNat_map_le f g xs (fun z hz => h z (.tail _ hz)))

theorem sumNat_map_const {α : Type} (c : Nat) :
    ∀ xs : List α, sumNat (xs.map (fun _ => c)) = xs.length * c
  | [] => by simp [sumNat]
  | _ :: xs => by
    show c + sumNat _ = (xs.length + 1) * c
    rw [sumNat_map_const c xs, Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem two_mul_le_add_sq (a b : Nat) : 2 * (a * b) ≤ a * a + b * b := by
  if h : a ≤ b then
    obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
    have hexp : (a + d) * (a + d) = a * a + 2 * (a * d) + d * d := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm d a]
      omega
    have hmul : a * (a + d) = a * a + a * d := Nat.mul_add a a d
    omega
  else
    obtain ⟨d, rfl⟩ : ∃ d, a = b + d := ⟨a - b, by omega⟩
    have hexp : (b + d) * (b + d) = b * b + 2 * (b * d) + d * d := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm d b]
      omega
    have hmul : (b + d) * b = b * b + b * d := by rw [Nat.add_mul, Nat.mul_comm d b]
    omega

theorem two_mul_sumNat_le (a : Nat) :
    ∀ xs : List Nat, 2 * (a * sumNat xs) ≤ xs.length * (a * a) + sumNat (xs.map (fun x => x * x))
  | [] => by simp [sumNat]
  | x :: xs => by
    have ih := two_mul_sumNat_le a xs
    have hxy := two_mul_le_add_sq a x
    show 2 * (a * (x + sumNat xs)) ≤
      (xs.length + 1) * (a * a) + (x * x + sumNat (xs.map (fun y => y * y)))
    rw [Nat.mul_add a x (sumNat xs), Nat.mul_add 2, Nat.add_mul xs.length 1 (a * a), Nat.one_mul]
    omega

/-- **Constructive Integer Cauchy–Schwarz Inequality (`nat_cauchy_schwarz`)**:
    `(∑ x_i)^2 ≤ n · ∑ x_i^2` over any `xs : List Nat`, proved purely in `Nat`. -/
theorem nat_cauchy_schwarz :
    ∀ xs : List Nat, sumNat xs * sumNat xs ≤ xs.length * sumNat (xs.map (fun x => x * x))
  | [] => by simp [sumNat]
  | a :: xs => by
    have ih := nat_cauchy_schwarz xs
    have hcross := two_mul_sumNat_le a xs
    show (a + sumNat xs) * (a + sumNat xs) ≤
      (xs.length + 1) * (a * a + sumNat (xs.map (fun x => x * x)))
    have hL : (a + sumNat xs) * (a + sumNat xs) =
        a * a + 2 * (a * sumNat xs) + sumNat xs * sumNat xs := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm (sumNat xs) a]
      omega
    have hR : (xs.length + 1) * (a * a + sumNat (xs.map (fun x => x * x))) =
        a * a + xs.length * (a * a) + sumNat (xs.map (fun x => x * x)) +
          xs.length * sumNat (xs.map (fun x => x * x)) := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_add]
      omega
    omega

/-- Indicator `0/1` of a boolean. -/
def indBool (b : Bool) : Nat := if b then 1 else 0

theorem indBool_sq (b : Bool) : indBool b * indBool b = indBool b := by
  cases b <;> rfl

theorem sumNat_indBool {α : Type} (p : α → Bool) :
    ∀ D : List α, sumNat (D.map (fun z => indBool (p z))) = (D.filter p).length
  | [] => rfl
  | z :: zs => by
    have ih := sumNat_indBool p zs
    cases hp : p z with
    | true =>
      rw [List.filter_cons_of_pos hp]
      show indBool (p z) + sumNat (zs.map (fun w => indBool (p w))) = (zs.filter p).length + 1
      rw [hp]; show 1 + _ = _; omega
    | false =>
      rw [List.filter_cons_of_neg (by rw [hp]; decide)]
      show indBool (p z) + sumNat (zs.map (fun w => indBool (p w))) = (zs.filter p).length
      rw [hp]; show 0 + _ = _; omega

/-- Point degree `|{i ∈ fam : mem i z = true}|`. -/
def ptDeg {α β : Type} (mem : β → α → Bool) (fam : List β) (z : α) : Nat :=
  (fam.filter (fun i => mem i z)).length

theorem ptDeg_cons {α β : Type} (mem : β → α → Bool) (i : β) (fam : List β) (z : α) :
    ptDeg mem (i :: fam) z = indBool (mem i z) + ptDeg mem fam z := by
  unfold ptDeg indBool
  cases hm : mem i z with
  | true =>
    rw [List.filter_cons_of_pos (p := fun j => mem j z) hm]
    show (fam.filter (fun j => mem j z)).length + 1 = 1 + (fam.filter (fun j => mem j z)).length
    omega
  | false =>
    rw [List.filter_cons_of_neg (p := fun j => mem j z) (by rw [hm]; decide)]
    show (fam.filter (fun j => mem j z)).length = 0 + (fam.filter (fun j => mem j z)).length
    omega

/-- Double-counting first moment: `∑_{z ∈ D} ptDeg(z) = ∑_{i ∈ fam} |I_i|`. -/
theorem sum_ptDeg_eq {α β : Type} (mem : β → α → Bool) (D : List α) :
    ∀ fam : List β,
      sumNat (D.map (ptDeg mem fam)) =
        sumNat (fam.map (fun i => (D.filter (fun z => mem i z)).length))
  | [] => by
    show sumNat (D.map (fun _ => 0)) = 0
    rw [sumNat_map_const, Nat.mul_zero]
  | i :: fam => by
    have hcongr : D.map (ptDeg mem (i :: fam)) =
        D.map (fun z => indBool (mem i z) + ptDeg mem fam z) :=
      List.map_congr_left (fun z _ => ptDeg_cons mem i fam z)
    rw [hcongr, sumNat_map_add, sumNat_indBool, sum_ptDeg_eq mem D fam]
    rfl

theorem sum_ind_mul_ptDeg_eq {α β : Type} (mem : β → α → Bool) (D : List α) (i : β) :
    ∀ fam : List β,
      sumNat (D.map (fun z => indBool (mem i z) * ptDeg mem fam z)) =
        sumNat (fam.map (fun j => (D.filter (fun z => mem i z && mem j z)).length))
  | [] => by
    show sumNat (D.map (fun z => indBool (mem i z) * 0)) = 0
    have h0 : D.map (fun z => indBool (mem i z) * 0) = D.map (fun _ => 0) :=
      List.map_congr_left (fun _ _ => Nat.mul_zero _)
    rw [h0, sumNat_map_const, Nat.mul_zero]
  | j :: fam => by
    have hstep : D.map (fun z => indBool (mem i z) * ptDeg mem (j :: fam) z) =
        D.map (fun z => indBool (mem i z && mem j z) + indBool (mem i z) * ptDeg mem fam z) := by
      refine List.map_congr_left (fun z _ => ?_)
      rw [ptDeg_cons, Nat.mul_add]
      have hind : indBool (mem i z) * indBool (mem j z) = indBool (mem i z && mem j z) := by
        cases mem i z <;> cases mem j z <;> rfl
      rw [hind]
    rw [hstep, sumNat_map_add, sumNat_indBool, sum_ind_mul_ptDeg_eq mem D i fam]
    rfl

/-- Double-counting second moment: `∑_{z ∈ D} ptDeg(z)^2 ≤ ∑_i |I_i| + k(k - 1)t`. -/
theorem sum_ptDeg_sq_le {α β : Type} (mem : β → α → Bool) (D : List α) (t : Nat) :
    ∀ fam : List β,
      fam.Pairwise (fun i j => (D.filter (fun z => mem i z && mem j z)).length ≤ t) →
      sumNat (D.map (fun z => ptDeg mem fam z * ptDeg mem fam z)) ≤
        sumNat (fam.map (fun i => (D.filter (fun z => mem i z)).length)) +
          fam.length * (fam.length - 1) * t
  | [], _ => by
    have h0 : D.map (fun z => ptDeg mem ([] : List β) z * ptDeg mem ([] : List β) z) =
        D.map (fun _ => 0) := List.map_congr_left (fun _ _ => rfl)
    rw [h0, sumNat_map_const, Nat.mul_zero]
    exact Nat.zero_le _
  | i :: fam, hp => by
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hp
    have ih := sum_ptDeg_sq_le mem D t fam htail
    have hexpand : D.map (fun z => ptDeg mem (i :: fam) z * ptDeg mem (i :: fam) z) =
        D.map (fun z =>
          (indBool (mem i z) + 2 * (indBool (mem i z) * ptDeg mem fam z)) +
            ptDeg mem fam z * ptDeg mem fam z) := by
      refine List.map_congr_left (fun z _ => ?_)
      rw [ptDeg_cons]
      have hsq := indBool_sq (mem i z)
      have hmul : (indBool (mem i z) + ptDeg mem fam z) * (indBool (mem i z) + ptDeg mem fam z) =
          indBool (mem i z) * indBool (mem i z) + 2 * (indBool (mem i z) * ptDeg mem fam z) +
            ptDeg mem fam z * ptDeg mem fam z := by
        rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm (ptDeg mem fam z) (indBool (mem i z))]
        omega
      omega
    have h2 : sumNat (D.map (fun z => 2 * (indBool (mem i z) * ptDeg mem fam z))) =
        2 * sumNat (D.map (fun z => indBool (mem i z) * ptDeg mem fam z)) := by
      have heq : D.map (fun z => 2 * (indBool (mem i z) * ptDeg mem fam z)) =
          D.map (fun z => indBool (mem i z) * ptDeg mem fam z +
            indBool (mem i z) * ptDeg mem fam z) :=
        List.map_congr_left (fun _ _ => by omega)
      rw [heq, sumNat_map_add]; omega
    have hinter : sumNat (fam.map (fun j => (D.filter (fun z => mem i z && mem j z)).length)) ≤
        fam.length * t := by
      rw [← sumNat_map_const t fam]
      exact sumNat_map_le _ _ fam hhead
    rw [hexpand, sumNat_map_add, sumNat_map_add, sumNat_indBool (fun z => mem i z) D,
      h2, sum_ind_mul_ptDeg_eq]
    have halg : 2 * (fam.length * t) + fam.length * (fam.length - 1) * t =
        (fam.length + 1) * fam.length * t := by
      cases fam with
      | nil => simp
      | cons _ tl =>
        calc 2 * ((tl.length + 1) * t) + (tl.length + 1) * tl.length * t
            = (2 * (tl.length + 1)) * t + ((tl.length + 1) * tl.length) * t := by
              rw [Nat.mul_assoc 2 (tl.length + 1) t]
          _ = (2 * (tl.length + 1) + (tl.length + 1) * tl.length) * t := (Nat.add_mul _ _ t).symm
          _ = ((tl.length + 2) * (tl.length + 1)) * t := by
              rw [Nat.add_comm tl.length 2, Nat.add_mul 2 tl.length (tl.length + 1),
                Nat.mul_comm tl.length (tl.length + 1)]
    have hstep1 : 2 * sumNat (fam.map (fun j => (D.filter (fun z => mem i z && mem j z)).length)) ≤
        2 * (fam.length * t) := Nat.mul_le_mul_left 2 hinter
    show (D.filter (fun z => mem i z)).length +
        2 * sumNat (fam.map (fun j => (D.filter (fun z => mem i z && mem j z)).length)) +
        sumNat (D.map (fun z => ptDeg mem fam z * ptDeg mem fam z)) ≤
      (D.filter (fun z => mem i z)).length +
        sumNat (fam.map (fun j => (D.filter (fun z => mem j z)).length)) +
        (fam.length + 1) * fam.length * t
    omega

/-- Boolean membership in a list. -/
def elemBool {α : Type} [DecidableEq α] (x : α) : List α → Bool
  | [] => false
  | y :: ys => decide (x = y) || elemBool x ys

theorem elemBool_iff {α : Type} [DecidableEq α] (x : α) :
    ∀ ys : List α, elemBool x ys = true ↔ x ∈ ys
  | [] => ⟨fun h => Bool.noConfusion h, fun h => by cases h⟩
  | y :: ys => by
    show (decide (x = y) || elemBool x ys) = true ↔ x ∈ y :: ys
    rw [Bool.or_eq_true, decide_eq_true_eq, elemBool_iff x ys, List.mem_cons]

def eraseFirstLocal {α : Type} [DecidableEq α] (x : α) : List α → List α
  | [] => []
  | y :: ys => if x = y then ys else y :: eraseFirstLocal x ys

private theorem mem_eraseFirstLocal_of_ne {α : Type} [DecidableEq α] {x z : α} (hne : z ≠ x) :
    ∀ {ys : List α}, z ∈ ys → z ∈ eraseFirstLocal x ys
  | [], h => by cases h
  | y :: ys, h => by
    unfold eraseFirstLocal
    if hxy : x = y then
      simp only [hxy, ↓reduceIte]
      cases h with
      | head => exact absurd hxy.symm hne
      | tail _ hm => exact hm
    else
      simp only [hxy, ↓reduceIte]
      cases h with
      | head => exact .head _
      | tail _ hm => exact .tail _ (mem_eraseFirstLocal_of_ne hne hm)

theorem eraseFirstLocal_length_lt {α : Type} [DecidableEq α] {x : α} :
    ∀ {ys : List α}, x ∈ ys → (eraseFirstLocal x ys).length < ys.length
  | [], h => by cases h
  | y :: ys, h => by
    unfold eraseFirstLocal
    if hxy : x = y then
      simp only [hxy, ↓reduceIte, List.length_cons]
      omega
    else
      simp only [hxy, ↓reduceIte, List.length_cons]
      cases h with
      | head => exact absurd rfl hxy
      | tail _ hm => exact Nat.succ_lt_succ (eraseFirstLocal_length_lt hm)

private theorem nodup_length_le_subset {α : Type} [DecidableEq α] :
    ∀ {A B : List α}, A.Nodup → (∀ z ∈ A, z ∈ B) → A.length ≤ B.length
  | [], _, _, _ => Nat.zero_le _
  | a :: as, B, hnd, hsub => by
    obtain ⟨hnot, hnd'⟩ := List.pairwise_cons.mp hnd
    have haB : a ∈ B := hsub a (.head _)
    have hlt := eraseFirstLocal_length_lt haB
    have ih := nodup_length_le_subset (B := eraseFirstLocal a B) hnd'
      (fun z hz => mem_eraseFirstLocal_of_ne (fun e => hnot z hz e.symm) (hsub z (.tail _ hz)))
    show as.length + 1 ≤ B.length
    omega

