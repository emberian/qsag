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

theorem filter_elemBool_take_length {α : Type} [DecidableEq α] (B : Nat) :
    ∀ {D : List α} (p : α → Bool), D.Nodup → B ≤ (D.filter p).length →
      (D.filter (fun z => elemBool z ((D.filter p).take B))).length = B := by
  intro D p hD hB
  let S := (D.filter p).take B
  have hSsub : ∀ z ∈ S, z ∈ D := fun z hz => (List.mem_filter.mp (List.mem_of_mem_take hz)).1
  have hSNd : S.Nodup := by
    have hFNd : (D.filter p).Nodup := List.Pairwise.filter _ hD
    have hsplit : (D.filter p).take B ++ (D.filter p).drop B = D.filter p := List.take_append_drop B _
    rw [← hsplit, List.nodup_append] at hFNd
    exact hFNd.1
  have hFNd2 : (D.filter (fun z => elemBool z S)).Nodup := List.Pairwise.filter _ hD
  have h1 : (D.filter (fun z => elemBool z S)).length ≤ S.length :=
    nodup_length_le_subset hFNd2 (fun z hz => (elemBool_iff z S).mp (List.mem_filter.mp hz).2)
  have h2 : S.length ≤ (D.filter (fun z => elemBool z S)).length :=
    nodup_length_le_subset hSNd (fun z hz => List.mem_filter.mpr ⟨hSsub z hz, (elemBool_iff z S).mpr hz⟩)
  have hEq : (D.filter (fun z => elemBool z S)).length = S.length := by omega
  rw [hEq, List.length_take]
  omega

theorem filter_and_mono {α : Type} (p q p' q' : α → Bool)
    (hp : ∀ z, p' z = true → p z = true) (hq : ∀ z, q' z = true → q z = true) :
    ∀ D : List α, (D.filter (fun z => p' z && q' z)).length ≤ (D.filter (fun z => p z && q z)).length
  | [] => Nat.le_refl 0
  | z :: zs => by
    let f1 : α → Bool := fun w => p' w && q' w
    let f2 : α → Bool := fun w => p w && q w
    have ih : (zs.filter f1).length ≤ (zs.filter f2).length :=
      filter_and_mono p q p' q' hp hq zs
    show ((z :: zs).filter f1).length ≤ ((z :: zs).filter f2).length
    cases h1 : f1 z with
    | false =>
      rw [List.filter_cons_of_neg (by rw [h1]; decide)]
      cases h2 : f2 z with
      | false => rw [List.filter_cons_of_neg (by rw [h2]; decide)]; exact ih
      | true => rw [List.filter_cons_of_pos h2]; exact Nat.le_succ_of_le ih
    | true =>
      obtain ⟨hp', hq'⟩ := Bool.and_eq_true_iff.mp h1
      have h2 : f2 z = true := Bool.and_eq_true_iff.mpr ⟨hp z hp', hq z hq'⟩
      rw [List.filter_cons_of_pos h1, List.filter_cons_of_pos h2]
      exact Nat.succ_le_succ ih

/-- **`[CWYZ26]` Lemma 3.2 (Cleared-Denominator Integer Johnson Set-System Bound)**:
    On an `n`-element duplicate-free domain `D`, any family `fam` of subsets of size `≥ B`
    whose distinct members intersect in `≤ t` points with `n * t < B * B` satisfies
    `(B * B - n * t) * fam.length ≤ n * (B - t)`. -/
theorem johnson_set_system_mul_le {α β : Type} [DecidableEq α]
    (D : List α) (fam : List β) (mem : β → α → Bool) (B t : Nat)
    (hD : D.Nodup)
    (hSize : ∀ i ∈ fam, B ≤ (D.filter (fun z => mem i z)).length)
    (hInter : fam.Pairwise (fun i j => (D.filter (fun z => mem i z && mem j z)).length ≤ t))
    (hDen : D.length * t < B * B) :
    (B * B - D.length * t) * fam.length ≤ D.length * (B - t) := by
  cases fam with
  | nil => simp
  | cons i₀ rest =>
    let fam' := i₀ :: rest
    let k := fam'.length
    have hk : 1 ≤ k := Nat.succ_pos _
    have hBn : B ≤ D.length := Nat.le_trans (hSize i₀ (.head _)) (List.length_filter_le _ D)
    have htB : t < B := Decidable.byContradiction (fun hnot => by
      have hBt : B ≤ t := by omega
      have hBBle : B * B ≤ D.length * t := Nat.mul_le_mul hBn hBt
      omega)
    let mem' : β → α → Bool := fun i z => elemBool z ((D.filter (fun w => mem i w)).take B)
    have hExact : ∀ i ∈ fam', (D.filter (fun z => mem' i z)).length = B :=
      fun i hi => filter_elemBool_take_length B (fun w => mem i w) hD (hSize i hi)
    have hSub : ∀ i z, mem' i z = true → mem i z = true := fun i z hz =>
      (List.mem_filter.mp (List.mem_of_mem_take ((elemBool_iff z _).mp hz))).2
    have hInter' : fam'.Pairwise (fun i j => (D.filter (fun z => mem' i z && mem' j z)).length ≤ t) :=
      List.Pairwise.imp (fun {i j} hij =>
        Nat.le_trans (filter_and_mono _ _ _ _ (hSub i) (hSub j) D) hij) hInter
    have hS1 : sumNat (D.map (ptDeg mem' fam')) = k * B := by
      rw [sum_ptDeg_eq]
      have heq : fam'.map (fun i => (D.filter (fun z => mem' i z)).length) =
          fam'.map (fun _ => B) := List.map_congr_left hExact
      rw [heq, sumNat_map_const]
    have hCS := nat_cauchy_schwarz (D.map (ptDeg mem' fam'))
    rw [List.length_map, List.map_map, hS1] at hCS
    have hS2 := sum_ptDeg_sq_le mem' D t fam' hInter'
    have hS1' : sumNat (fam'.map (fun i => (D.filter (fun z => mem' i z)).length)) = k * B := by
      rw [← sum_ptDeg_eq]; exact hS1
    rw [hS1'] at hS2
    have hComb : (k * B) * (k * B) ≤ D.length * (k * B + k * (k - 1) * t) :=
      Nat.le_trans hCS (Nat.mul_le_mul_left D.length hS2)
    have hL : (k * B) * (k * B) = k * (k * (B * B)) := by
      rw [Nat.mul_mul_mul_comm k B k B, Nat.mul_assoc k k (B * B)]
    have hR : D.length * (k * B + k * (k - 1) * t) =
        k * (D.length * B + (k - 1) * (D.length * t)) := by
      rw [Nat.mul_add]
      have e1 : D.length * (k * B) = k * (D.length * B) := by
        rw [← Nat.mul_assoc, Nat.mul_comm D.length k, Nat.mul_assoc]
      have e2 : D.length * (k * (k - 1) * t) = k * ((k - 1) * (D.length * t)) := by
        rw [Nat.mul_assoc k (k - 1) t, ← Nat.mul_assoc D.length k, Nat.mul_comm D.length k,
          Nat.mul_assoc k D.length, ← Nat.mul_assoc D.length (k - 1) t,
          Nat.mul_comm D.length (k - 1), Nat.mul_assoc (k - 1) D.length t]
      rw [e1, e2, ← Nat.mul_add]
    rw [hL, hR] at hComb
    have hCancel : k * (B * B) ≤ D.length * B + (k - 1) * (D.length * t) :=
      Nat.le_of_mul_le_mul_left hComb hk
    have hSplitK : k * (D.length * t) = D.length * t + (k - 1) * (D.length * t) := by
      have hk1 : k = 1 + (k - 1) := by omega
      conv => lhs; rw [hk1]
      rw [Nat.add_mul, Nat.one_mul]
    have hSub1 : (B * B - D.length * t) * k = k * (B * B) - k * (D.length * t) := by
      rw [Nat.mul_comm _ k, Nat.mul_sub]
    have hSub2 : D.length * (B - t) = D.length * B - D.length * t := Nat.mul_sub D.length B t
    show (B * B - D.length * t) * k ≤ D.length * (B - t)
    omega

/-- The integer Johnson set-system upper bound `⌊n(B - t) / (B² - nt)⌋` (`[CWYZ26]` Lemma 3.2). -/
def johnsonBound (n B t : Nat) : Nat :=
  (n * (B - t)) / (B * B - n * t)

/-- **`[CWYZ26]` Lemma 3.2 (Division Form)**:
    Under `D.length * t < B * B`, `fam.length ≤ johnsonBound D.length B t`. -/
theorem johnson_set_system_card_le {α β : Type} [DecidableEq α]
    (D : List α) (fam : List β) (mem : β → α → Bool) (B t : Nat)
    (hD : D.Nodup)
    (hSize : ∀ i ∈ fam, B ≤ (D.filter (fun z => mem i z)).length)
    (hInter : fam.Pairwise (fun i j => (D.filter (fun z => mem i z && mem j z)).length ≤ t))
    (hDen : D.length * t < B * B) :
    fam.length ≤ johnsonBound D.length B t := by
  have hmul := johnson_set_system_mul_le D fam mem B t hD hSize hInter hDen
  rw [Nat.mul_comm] at hmul
  exact (Nat.le_div_iff_mul_le (by omega)).mpr hmul

private theorem nodup_filter_bool {α : Type} (p : α → Bool) :
    ∀ {l : List α}, l.Nodup → (l.filter p).Nodup
  | [], _ => .nil
  | a :: l, h => by
    obtain ⟨ha, hl⟩ := List.pairwise_cons.mp h
    cases hpa : p a with
    | false =>
      rw [List.filter_cons_of_neg (by rw [hpa]; decide)]
      exact nodup_filter_bool p hl
    | true =>
      rw [List.filter_cons_of_pos hpa]
      exact List.pairwise_cons.mpr ⟨fun b hb => ha b (List.mem_filter.mp hb).1,
        nodup_filter_bool p hl⟩

/-- Subadditivity of list filter lengths under pointwise disjunction. -/
theorem filter_length_le_add {α : Type} (p q r : α → Bool) :
    ∀ (xs : List α), (∀ x ∈ xs, p x = true → q x = true ∨ r x = true) →
      (xs.filter p).length ≤ (xs.filter q).length + (xs.filter r).length
  | [], _ => Nat.le_refl 0
  | x :: xs, h => by
    have ih := filter_length_le_add p q r xs (fun y hy => h y (.tail _ hy))
    cases hp : p x with
    | false =>
      simp only [List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte]
      cases q x <;> cases r x <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega
    | true =>
      rcases h x (.head _) hp with hq | hr
      · simp only [List.filter_cons, hp, hq, ↓reduceIte, List.length_cons]
        cases r x <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega
      · simp only [List.filter_cons, hp, hr, ↓reduceIte, List.length_cons]
        cases q x <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons] <;> omega

/-- First-occurrence deduplication of a decidable list. -/
def dedupFirst {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: l => a :: (dedupFirst l).filter (fun b => decide (b ≠ a))

theorem dedupFirst_nodup {α : Type} [DecidableEq α] :
    ∀ l : List α, (dedupFirst l).Nodup
  | [] => .nil
  | _ :: l => List.pairwise_cons.mpr ⟨fun _ hb =>
      (of_decide_eq_true (List.mem_filter.mp hb).2).symm,
      nodup_filter_bool _ (dedupFirst_nodup l)⟩

theorem mem_dedupFirst_iff {α : Type} [DecidableEq α] (x : α) :
    ∀ l : List α, x ∈ dedupFirst l ↔ x ∈ l
  | [] => Iff.rfl
  | a :: l => by
    show x ∈ a :: (dedupFirst l).filter (fun b => decide (b ≠ a)) ↔ x ∈ a :: l
    rw [List.mem_cons, List.mem_cons, List.mem_filter, mem_dedupFirst_iff x l]
    constructor
    · rintro (rfl | ⟨hx, _⟩)
      · exact .inl rfl
      · exact .inr hx
    · rintro (rfl | hx)
      · exact .inl rfl
      · if hxa : x = a then exact .inl hxa
        else exact .inr ⟨hx, decide_eq_true hxa⟩

theorem pairwise_of_nodup {α : Type} {R : α → α → Prop} {l : List α}
    (hNd : l.Nodup) (h : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b) : l.Pairwise R := by
  induction l with
  | nil => exact .nil
  | cons a tl ih =>
    obtain ⟨hnot, htl⟩ := List.pairwise_cons.mp hNd
    exact List.pairwise_cons.mpr ⟨fun b hb => h a (.head _) b (.tail _ hb) (fun e => hnot b hb e),
      ih htl (fun x hx y hy hne => h x (.tail _ hx) y (.tail _ hy) hne)⟩

/-- Fiber-partition bound: if `f` maps `L` into `fam` and every fiber in `L` has size `≤ M`,
    then `L.length ≤ fam.length * M`. -/
theorem count_partition_le {α β : Type} [DecidableEq β] (f : α → β) (M : Nat) :
    ∀ (L : List α) (fam : List β),
      (∀ x ∈ L, f x ∈ fam) →
      (∀ b ∈ fam, (L.filter (fun x => decide (f x = b))).length ≤ M) →
      L.length ≤ fam.length * M := by
  intro L fam hCov hFib
  have hSum : ∀ bs : List β, (∀ b ∈ bs, b ∈ fam) →
      (L.filter (fun x => elemBool (f x) bs)).length ≤ bs.length * M := by
    intro bs; induction bs with
    | nil =>
      intro _
      have hNil : ∀ xs : List α, xs.filter (fun x => elemBool (f x) []) = [] := by
        intro xs; induction xs with
        | nil => rfl
        | cons _ _ ihL => exact ihL
      rw [hNil L]; exact Nat.zero_le _
    | cons b tl ih =>
      intro hSubFam
      have hSub := filter_length_le_add (fun x => elemBool (f x) (b :: tl))
        (fun x => decide (f x = b)) (fun x => elemBool (f x) tl) L
        (fun x _ hx => Bool.or_eq_true_iff.mp hx)
      refine Nat.le_trans hSub ?_
      have hb : (L.filter (fun x => decide (f x = b))).length ≤ M :=
        hFib b (hSubFam b (.head _))
      show _ ≤ (tl.length + 1) * M
      rw [Nat.add_comm tl.length 1, Nat.add_mul, Nat.one_mul]
      exact Nat.add_le_add hb (ih (fun y hy => hSubFam y (.tail _ hy)))
  have hAll : ∀ xs : List α, (∀ x ∈ xs, f x ∈ fam) →
      xs.filter (fun x => elemBool (f x) fam) = xs := by
    intro xs; induction xs with
    | nil => intro _; rfl
    | cons x tl ih =>
      intro hc
      have hx : elemBool (f x) fam = true := (elemBool_iff (f x) fam).mpr (hc x (.head _))
      simp only [List.filter_cons, hx, ↓reduceIte]
      exact congrArg (x :: ·) (ih (fun y hy => hc y (.tail _ hy)))
  have key := hSum fam (fun _ h => h)
  rwa [hAll L hCov] at key

end JohnsonBound

/-! ## Assurance Witnesses -/

end Qsag

end

namespace Qsag
open CommRingOps RoundPoly UPoly
namespace SylElim
theorem natRangeSum_const_add :
    ∀ (n c : Nat), Mat.natRangeSum n (fun i => c + i) = n * c + Mat.natRangeSum n (fun i => i)
  | 0, c => by show 0 = 0 * c + 0; omega
  | n + 1, c => by
    show Mat.natRangeSum n (fun i => c + i) + (c + n) = (n + 1) * c + (Mat.natRangeSum n (fun i => i) + n)
    rw [natRangeSum_const_add n c, Nat.succ_mul]; omega

theorem natRangeSum_split :
    ∀ (m N : Nat) (f : Nat → Nat),
      Mat.natRangeSum (m + N) f = Mat.natRangeSum m f + Mat.natRangeSum N (fun r => f (m + r))
  | m, 0, _ => by show Mat.natRangeSum m _ = Mat.natRangeSum m _ + 0; omega
  | m, N + 1, f => by
    show Mat.natRangeSum (m + N) f + f (m + N) =
      Mat.natRangeSum m f + (Mat.natRangeSum N (fun r => f (m + r)) + f (m + N))
    rw [natRangeSum_split m N f]; omega

theorem natRangeSum_split_id (m N : Nat) :
    Mat.natRangeSum (m + N) (fun i => i) =
      Mat.natRangeSum m (fun i => i) + Mat.natRangeSum N (fun i => i) + m * N := by
  rw [natRangeSum_split m N (fun i => i), natRangeSum_const_add N m, Nat.mul_comm N m]; omega

theorem rangeSum_split {R : Type} [LawfulCommRing R] (m : Nat) :
    ∀ (N : Nat) (f : Nat → R),
      Mat.rangeSum (m + N) f = add (Mat.rangeSum m f) (Mat.rangeSum N (fun r => f (m + r)))
  | 0, f => by show Mat.rangeSum m f = add (Mat.rangeSum m f) zero; rw [LawfulCommRing.add_zero]
  | N + 1, f => by
    show add (Mat.rangeSum (m + N) f) (f (m + N)) =
      add (Mat.rangeSum m f) (add (Mat.rangeSum N (fun r => f (m + r))) (f (m + N)))
    rw [rangeSum_split m N f, LawfulCommRing.add_assoc]

end SylElim
namespace RingHom

theorem map_npow {R S : Type} [LawfulCommRing R] [LawfulCommRing S] (φ : RingHom R S) (a : R) :
    ∀ k : Nat, φ.toFun (CRing.npow a k) = CRing.npow (φ.toFun a) k
  | 0 => φ.map_one
  | k + 1 => by
    show φ.toFun (mul (CRing.npow a k) a) = mul (CRing.npow (φ.toFun a) k) (φ.toFun a)
    rw [φ.map_mul, map_npow φ a k]

end RingHom

theorem npow_mul_self {R : Type} [LawfulCommRing R] (s : R) :
    ∀ j : Nat, CRing.npow (mul s s) j = CRing.npow s (2 * j)
  | 0 => rfl
  | j + 1 => by
    show mul (CRing.npow (mul s s) j) (mul s s) = mul (mul (CRing.npow s (2 * j)) s) s
    rw [npow_mul_self s j, LawfulCommRing.mul_assoc]

theorem degFn_npow_le {R : Type} [LawfulCommRing R] {δ : R → Nat} (hδ : DegFn δ)
    (h1 : δ one = 0) (a : R) (B : Nat) (ha : δ a ≤ B) : ∀ k : Nat, δ (CRing.npow a k) ≤ k * B
  | 0 => by show δ one ≤ 0 * B; rw [h1]; exact Nat.zero_le _
  | k + 1 => by
    have h := hδ.mul_le (CRing.npow a k) a
    have ih := degFn_npow_le hδ h1 a B ha k
    show δ (mul (CRing.npow a k) a) ≤ (k + 1) * B
    rw [Nat.succ_mul]; omega

namespace UPoly
variable {R : Type} [LawfulCommRing R] [DecidableEq R]
theorem mapHom_X {S : Type} [LawfulCommRing S] [DecidableEq S] (φ : RingHom R S) :
    (mapHom φ).toFun X = X := eval₂_X _ _

end UPoly

@[simp] theorem dotVec_nil_left {F : Type} [CommRingOps F] (xs : List F) : dotVec [] xs = zero := by cases xs <;> rfl
@[simp] theorem dotVec_nil_right {F : Type} [CommRingOps F] (xs : List F) : dotVec xs [] = zero := by cases xs <;> rfl
@[simp] theorem dotVec_cons {F : Type} [CommRingOps F] (a b : F) (as bs : List F) :
  dotVec (a :: as) (b :: bs) = add (mul a b) (dotVec as bs) := by rfl
namespace Mat
@[simp] theorem natRangeSum_zero (f : Nat → Nat) : natRangeSum 0 f = 0 := by rfl
@[simp] theorem natRangeSum_succ (n : Nat) (f : Nat → Nat) : natRangeSum (n+1) f = natRangeSum n f + f n := by rfl
end Mat

namespace UPoly
variable {R : Type} [LawfulCommRing R] [DecidableEq R]
@[simp] theorem natDeg_zero : (zero : UPoly R).natDeg = 0 := by rfl
@[simp] theorem C_add_eq (a b : R) : C (add a b) = add (C a) (C b) := CHom.map_add a b
@[simp] theorem C_mul_eq (a b : R) : C (mul a b) = mul (C a) (C b) := CHom.map_mul a b
end UPoly
end Qsag

namespace Qsag
open CommRingOps RoundPoly UPoly
namespace Poly2
variable {E : Type} [LawfulField E] [DecidableEq E]
local instance : NoZeroDivisors E := LawfulField.toNoZeroDivisors E
theorem xgcd_spec (a b : UPoly E) :
    add (mul (UPoly.xgcd a b).2.1 a) (mul (UPoly.xgcd a b).2.2 b) = (UPoly.xgcd a b).1 ∧
      (∃ s, a = mul (UPoly.xgcd a b).1 s) ∧ (∃ t, b = mul (UPoly.xgcd a b).1 t) :=
  UPoly.xgcdAux_spec b.coeffs.length a b (Nat.le_refl _)

theorem eq_C_lead_of_natDeg_zero {u : UPoly E} (hd : u.natDeg = 0) : u = C u.lead :=
  ext_coeffAt fun k => by
    cases k with
    | zero => rw [coeffAt_C_zero]; show _ = coeffAt u.coeffs u.natDeg; rw [hd]
    | succ k => rw [coeffAt_C_succ]; exact u.coeffAt_eq_zero_of_natDeg_lt (by omega)

theorem divMod_exact_of_mul (g q : UPoly E) (hg : g ≠ zero) :
    (UPoly.divMod (mul g q) g).1 = q := by
  obtain ⟨hdiv, hlen⟩ := UPoly.divMod_spec (mul g q) g hg
  generalize (UPoly.divMod (mul g q) g).1 = q' at hdiv
  generalize (UPoly.divMod (mul g q) g).2 = r at hdiv hlen
  have hrEq : r = mul g (sub q q') := by
    apply LawfulCommRing.add_left_cancel (a := mul q' g)
    rw [← hdiv]; constructive_ring
  if hsub : sub q q' = zero then
    exact (LawfulCommRing.sub_eq_zero_iff.mp hsub).symm
  else
    exfalso
    have hr0 : r ≠ zero := fun e => mul_ne_zero' hg hsub (hrEq.symm.trans e)
    have hdeg := UPoly.natDeg_mul hg hsub
    rw [← hrEq] at hdeg
    have hgPos : 1 ≤ g.coeffs.length := by
      cases hc : g.coeffs with
      | nil => exact absurd (UPoly.ext hc) hg
      | cons _ _ => exact Nat.succ_pos _
    have hrPos : 1 ≤ r.coeffs.length := by
      cases hc : r.coeffs with
      | nil => exact absurd (UPoly.ext hc) hr0
      | cons _ _ => exact Nat.succ_pos _
    unfold UPoly.natDeg at hdeg
    omega

theorem coeffAt_map_zero_fn {α β : Type} [CommRingOps α] [CommRingOps β]
    (f : α → β) (hf0 : f zero = zero) :
    ∀ (l : List α) (k : Nat), coeffAt (l.map f) k = f (coeffAt l k)
  | [], k => by rw [List.map_nil, coeffAt_nil, coeffAt_nil, hf0]
  | _ :: _, 0 => rfl
  | _ :: tl, k + 1 => coeffAt_map_zero_fn f hf0 tl k

theorem coeffAt_map_mul_left (c : UPoly E) :
    ∀ (bs : List (UPoly E)) (k : Nat), coeffAt (bs.map (mul c)) k = mul c (coeffAt bs k) :=
  coeffAt_map_zero_fn (mul c) (LawfulCommRing.mul_zero c)

abbrev DvdU (g x : UPoly E) : Prop := ∃ q, x = mul g q

theorem dvdU_zero (g : UPoly E) : DvdU g zero :=
  ⟨zero, (LawfulCommRing.mul_zero g).symm⟩

theorem dvdU_add {g x y : UPoly E} (hx : DvdU g x) (hy : DvdU g y) : DvdU g (add x y) := by
  obtain ⟨qx, rfl⟩ := hx; obtain ⟨qy, rfl⟩ := hy
  exact ⟨add qx qy, (LawfulCommRing.left_distrib g qx qy).symm⟩

theorem dvdU_mul_right {g x : UPoly E} (hx : DvdU g x) (y : UPoly E) : DvdU g (mul x y) := by
  obtain ⟨q, rfl⟩ := hx; exact ⟨mul q y, LawfulCommRing.mul_assoc g q y⟩

theorem dvdU_trans {g' g x : UPoly E} (hg : DvdU g' g) (hx : DvdU g x) : DvdU g' x := by
  obtain ⟨t, rfl⟩ := hg; obtain ⟨q, rfl⟩ := hx
  exact ⟨mul t q, LawfulCommRing.mul_assoc g' t q⟩

theorem coeffAt_rawAddCoeffs (as bs : List (UPoly E)) (k : Nat) :
    coeffAt (rawAddCoeffs as bs) k = add (coeffAt as k) (coeffAt bs k) := by
  induction as generalizing bs k with
  | nil => cases bs <;> simp [rawAddCoeffs, coeffAt_nil, LawfulCommRing.zero_add]
  | cons a tl ih =>
    cases bs with
    | nil => cases k <;> simp [rawAddCoeffs, coeffAt_nil, LawfulCommRing.add_zero]
    | cons _ btl =>
      cases k with
      | zero => rfl
      | succ k => exact ih btl k

theorem dvdU_rawMul_lt (g : UPoly E) (bs : List (UPoly E)) (k : Nat)
    (hbs : ∀ j, j < k → DvdU g (coeffAt bs j)) :
    ∀ (as : List (UPoly E)) (m : Nat), m < k → DvdU g (coeffAt (rawMul as bs) m)
  | [], m, _ => by show DvdU g (coeffAt [] m); rw [coeffAt_nil]; exact dvdU_zero g
  | a :: tl, m, hm => by
    show DvdU g (coeffAt (rawAddCoeffs (bs.map (mul a)) (zero :: rawMul tl bs)) m)
    rw [coeffAt_rawAddCoeffs, coeffAt_map_mul_left]
    refine dvdU_add ?_ ?_
    · obtain ⟨q, hq⟩ := hbs m hm
      exact ⟨mul a q, by rw [hq]; constructive_ring⟩
    · cases m with
      | zero => exact dvdU_zero g
      | succ m' => exact dvdU_rawMul_lt g bs k hbs tl m' (by omega)

theorem rawMul_pivot_congr (g : UPoly E) (bs : List (UPoly E)) (j₀ : Nat)
    (hbs : ∀ j, j < j₀ → DvdU g (coeffAt bs j)) :
    ∀ (i₀ : Nat) (as : List (UPoly E)),
      (∀ i, i < i₀ → DvdU g (coeffAt as i)) →
      ∃ q, coeffAt (rawMul as bs) (i₀ + j₀) =
        add (mul (coeffAt as i₀) (coeffAt bs j₀)) (mul g q)
  | 0, [], _ =>
    ⟨zero, by
      show zero = add (mul zero (coeffAt bs j₀)) (mul g zero)
      rw [LawfulCommRing.zero_mul, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]⟩
  | 0, a :: tl, _ => by
    rw [Nat.zero_add]
    show ∃ q, coeffAt (rawAddCoeffs (bs.map (mul a)) (zero :: rawMul tl bs)) j₀ =
      add (mul a (coeffAt bs j₀)) (mul g q)
    rw [coeffAt_rawAddCoeffs, coeffAt_map_mul_left]
    cases j₀ with
    | zero => exact ⟨zero, by show add _ zero = _; rw [LawfulCommRing.mul_zero]⟩
    | succ j' =>
      obtain ⟨q, hq⟩ := dvdU_rawMul_lt g bs (j' + 1) hbs tl j' (Nat.lt_succ_self j')
      exact ⟨q, by show add _ (coeffAt (rawMul tl bs) j') = _; rw [hq]⟩
  | i' + 1, [], _ =>
    ⟨zero, by
      show zero = add (mul zero (coeffAt bs j₀)) (mul g zero)
      rw [LawfulCommRing.zero_mul, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]⟩
  | i' + 1, a :: tl, has => by
    rw [Nat.succ_add]
    show ∃ q, coeffAt (rawAddCoeffs (bs.map (mul a)) (zero :: rawMul tl bs)) (i' + j₀ + 1) =
      add (mul (coeffAt tl i') (coeffAt bs j₀)) (mul g q)
    rw [coeffAt_rawAddCoeffs, coeffAt_map_mul_left]
    have ha0 : DvdU g a := has 0 (Nat.zero_lt_succ i')
    obtain ⟨qa, hqa⟩ := dvdU_mul_right ha0 (coeffAt bs (i' + j₀ + 1))
    obtain ⟨qtl, hqtl⟩ := rawMul_pivot_congr g bs j₀ hbs i' tl
      (fun i hi => has (i + 1) (Nat.succ_lt_succ hi))
    refine ⟨add qa qtl, ?_⟩
    show add (mul a (coeffAt bs (i' + j₀ + 1))) (coeffAt (rawMul tl bs) (i' + j₀)) = _
    rw [hqa, hqtl]; constructive_ring

theorem refine_against_list :
    ∀ (cs : List (UPoly E)) (g : UPoly E), 1 ≤ g.natDeg →
      ∃ g' : UPoly E, 1 ≤ g'.natDeg ∧ DvdU g' g ∧
        ∀ c ∈ cs, DvdU g' c ∨ ∃ u v, add (mul u g') (mul v c) = one
  | [], g, hg => ⟨g, hg, ⟨one, (LawfulCommRing.mul_one g).symm⟩, fun _ hc => nomatch hc⟩
  | c :: tl, g, hg => by
    have hgNe : g ≠ zero := fun e => by rw [e] at hg; exact Nat.not_succ_le_zero 0 hg
    rcases UPoly.d5_split g c hgNe with ⟨u, v, hbez⟩ | ⟨t, ht⟩ | ⟨g₁, q₁, hsplit, hg₁pos, _, _, t, ht⟩
    · obtain ⟨g', hg'deg, hg'dvd, htl⟩ := refine_against_list tl g hg
      refine ⟨g', hg'deg, hg'dvd, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hxtl
      · obtain ⟨s, rfl⟩ := hg'dvd
        exact .inr ⟨mul u s, v, by rw [← hbez]; constructive_ring⟩
      · exact htl x hxtl
    · obtain ⟨g', hg'deg, hg'dvd, htl⟩ := refine_against_list tl g hg
      refine ⟨g', hg'deg, hg'dvd, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hxtl
      · exact .inl (dvdU_trans hg'dvd ⟨t, ht⟩)
      · exact htl x hxtl
    · obtain ⟨g', hg'deg, hg'dvd, htl⟩ := refine_against_list tl g₁ hg₁pos
      have hg'g : DvdU g' g := dvdU_trans hg'dvd ⟨q₁, hsplit⟩
      refine ⟨g', hg'deg, hg'g, fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hxtl
      · exact .inl (dvdU_trans hg'dvd ⟨t, ht⟩)
      · exact htl x hxtl

theorem coeffAt_mem_or_zero :
    ∀ (cs : List (UPoly E)) (k : Nat), coeffAt cs k ∈ cs ∨ coeffAt cs k = zero
  | [], k => .inr (coeffAt_nil k)
  | _ :: _, 0 => .inl (.head _)
  | _ :: tl, k + 1 => (coeffAt_mem_or_zero tl k).elim (fun h => .inl (.tail _ h)) .inr

end Poly2
end Qsag

namespace Qsag
open CommRingOps RoundPoly
 theorem coeffAt_eq_getD {F : Type} [CommRingOps F] (cs : List F) (k : Nat) : coeffAt cs k = cs.getD k zero := by rfl
namespace Mat
variable {R : Type} [LawfulCommRing R]
@[simp] theorem rangeSum_zero (f : Nat → R) : rangeSum 0 f = zero := by rfl
@[simp] theorem rangeSum_succ (n : Nat) (f : Nat → R) : rangeSum (n+1) f = add (rangeSum n f) (f n) := by rfl
 theorem matMul_apply (k : Nat) (A B : Nat → Nat → R) (i j : Nat) : matMul k A B i j = rangeSum k (fun l => mul (A i l) (B l j)) := by rfl
omit [LawfulCommRing R] in
 theorem minor_zero_zero (M : Nat → Nat → R) (i j : Nat) : minor M 0 0 i j = M (i+1) (j+1) := by simp [minor, skipIdx]
 theorem idMat_eq (i j : Nat) : (idMat i j : R) = if i = j then one else zero := by rfl
end Mat
namespace UPoly
variable {R : Type} [LawfulCommRing R] [DecidableEq R]
 theorem lead_eq (p : UPoly R) : p.lead = coeffAt p.coeffs p.natDeg := by rfl
 theorem eval_mul (a b : UPoly R) (x : R) : (mul a b).eval x = mul (a.eval x) (b.eval x) := (evalHom x).map_mul a b
 theorem eval_add (a b : UPoly R) (x : R) : (add a b).eval x = add (a.eval x) (b.eval x) := (evalHom x).map_add a b
 theorem C_zero_eq : (C zero : UPoly R) = zero := CHom.map_zero
end UPoly
end Qsag

namespace Qsag
open CommRingOps RoundPoly UPoly
namespace SylElim
variable {R : Type} [LawfulCommRing R] [DecidableEq R]
theorem ite_pos {α : Type} {p : Prop} [Decidable p] (hp : p) {a b : α} :
    (if p then a else b) = a := by
  split
  · rfl
  · next hn => exact absurd hp hn

theorem ite_neg {α : Type} {p : Prop} [Decidable p] (hnp : ¬ p) {a b : α} :
    (if p then a else b) = b := by
  split
  · next hp => exact absurd hp hnp
  · rfl

def divXSubList (ζ : R) : List R → List R
  | [] => []
  | [_] => []
  | _ :: c₁ :: cs => evalCoeffs (c₁ :: cs) ζ :: divXSubList ζ (c₁ :: cs)

def divXSub (p : UPoly R) (ζ : R) : UPoly R :=
  ofList (divXSubList ζ p.coeffs)

omit [DecidableEq R] in
theorem length_divXSubList (ζ : R) :
    ∀ l : List R, (divXSubList ζ l).length = l.length - 1
  | [] => rfl
  | [_] => rfl
  | _ :: c₁ :: cs => by
    show (divXSubList ζ (c₁ :: cs)).length + 1 = (c₁ :: cs).length
    rw [length_divXSubList ζ (c₁ :: cs)]; rfl

theorem divXSubList_spec (ζ : R) :
    ∀ l : List R, ofList l = add (C (evalCoeffs l ζ)) (mul (sub X (C ζ)) (ofList (divXSubList ζ l)))
  | [] => by
    show zero = add (C zero) (mul (sub X (C ζ)) zero)
    rw [UPoly.C_zero_eq, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | [c] => by
    show ofList [c] = add (C (add c (mul ζ zero))) (mul (sub X (C ζ)) zero)
    rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    rfl
  | c₀ :: c₁ :: cs => by
    rw [ofList_cons c₀ (c₁ :: cs), divXSubList_spec ζ (c₁ :: cs)]
    show add (C c₀) (mul X (add (C (evalCoeffs (c₁ :: cs) ζ))
        (mul (sub X (C ζ)) (ofList (divXSubList ζ (c₁ :: cs)))))) =
      add (C (add c₀ (mul ζ (evalCoeffs (c₁ :: cs) ζ))))
        (mul (sub X (C ζ)) (ofList (evalCoeffs (c₁ :: cs) ζ :: divXSubList ζ (c₁ :: cs))))
    rw [ofList_cons, UPoly.C_add_eq, UPoly.C_mul_eq]; constructive_ring

theorem divXSub_spec (p : UPoly R) (ζ : R) :
    p = add (C (p.eval ζ)) (mul (sub X (C ζ)) (divXSub p ζ)) ∧
      (divXSub p ζ).natDeg ≤ p.natDeg - 1 := by
  refine ⟨?_, ?_⟩
  · have h := divXSubList_spec ζ p.coeffs
    rwa [ofList_coeffs, ← eval_eq] at h
  · unfold divXSub natDeg
    have htr := trimPoly_length_le (divXSubList ζ p.coeffs)
    have hlen := length_divXSubList ζ p.coeffs
    rw [coeffs_ofList]; omega

/-! ## Monomials & Coefficient Extraction -/

def monom : Nat → UPoly R
  | 0 => one
  | k + 1 => mul X (monom k)

theorem coeffAt_monom :
    ∀ (k j : Nat), coeffAt (monom (R := R) k).coeffs j = if j = k then one else zero
  | 0, 0 => coeffAt_C_zero one
  | 0, j + 1 => coeffAt_C_succ one j
  | k + 1, 0 => coeffAt_X_mul_zero (monom k)
  | k + 1, j + 1 => by
    rw [monom, coeffAt_X_mul_succ, coeffAt_monom k j]
    if h : j = k then rw [h, ite_pos rfl, ite_pos rfl]
    else rw [ite_neg (fun e => h (Nat.succ.inj e)), ite_neg h]

theorem coeffAt_monom_mul :
    ∀ (d : Nat) (G : UPoly R) (j : Nat),
      coeffAt (mul (monom d) G).coeffs j = if d ≤ j then coeffAt G.coeffs (j - d) else zero
  | 0, G, j => by
    show coeffAt (mul one G).coeffs j = _
    rw [LawfulCommRing.one_mul, ite_pos (Nat.zero_le j), Nat.sub_zero]
  | d + 1, G, 0 => by
    show coeffAt (mul (mul X (monom d)) G).coeffs 0 = _
    rw [LawfulCommRing.mul_assoc, coeffAt_X_mul_zero, ite_neg (Nat.not_succ_le_zero d)]
  | d + 1, G, j + 1 => by
    show coeffAt (mul (mul X (monom d)) G).coeffs (j + 1) = _
    rw [LawfulCommRing.mul_assoc, coeffAt_X_mul_succ, coeffAt_monom_mul d G j]
    if h : d ≤ j then rw [ite_pos h, ite_pos (Nat.succ_le_succ h), Nat.succ_sub_succ]
    else rw [ite_neg h, ite_neg (fun hs => h (Nat.le_of_succ_le_succ hs))]

/-! ## Master Linear-Factor Identity `sylRes_mul_X_sub` -/

theorem coeffAt_sub_X_C_mul (ζ : R) (G : UPoly R) :
    (coeffAt (mul (sub X (C ζ)) G).coeffs 0 = neg (mul ζ (coeffAt G.coeffs 0))) ∧
      ∀ s : Nat, coeffAt (mul (sub X (C ζ)) G).coeffs (s + 1) =
        sub (coeffAt G.coeffs s) (mul ζ (coeffAt G.coeffs (s + 1))) := by
  have hExpand : mul (sub X (C ζ)) G = sub (mul X G) (mul (C ζ) G) := by constructive_ring
  refine ⟨?_, fun s => ?_⟩
  · rw [hExpand, coeffAt_sub, coeffAt_X_mul_zero, coeffAt_C_mul]; constructive_ring
  · rw [hExpand, coeffAt_sub, coeffAt_X_mul_succ, coeffAt_C_mul]

omit [DecidableEq R] in
theorem rangeSum_eval_eq (ζ : R) :
    ∀ (l : List R) (K : Nat),
      l.length ≤ K → Mat.rangeSum K (fun j => mul (coeffAt l j) (CRing.npow ζ j)) = evalCoeffs l ζ
  | [], K, _ => Mat.rangeSum_eq_zero fun j _ => by rw [coeffAt_nil, LawfulCommRing.zero_mul]
  | _ :: _, 0, h => by simp only [List.length_cons] at h; exfalso; omega
  | c :: cs, K + 1, h => by
    have hShift : ∀ m, Mat.rangeSum (m + 1) (fun j => mul (coeffAt (c :: cs) j) (CRing.npow ζ j)) =
        add c (mul ζ (Mat.rangeSum m (fun j => mul (coeffAt cs j) (CRing.npow ζ j)))) := by
      intro m; induction m with
      | zero =>
        show add zero (mul c one) = add c (mul ζ zero)
        rw [LawfulCommRing.zero_add, LawfulCommRing.mul_one, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
      | succ m ihm =>
        show add (Mat.rangeSum (m + 1) _) (mul (coeffAt cs m) (mul (CRing.npow ζ m) ζ)) =
          add c (mul ζ (add (Mat.rangeSum m _) (mul (coeffAt cs m) (CRing.npow ζ m))))
        rw [ihm]; constructive_ring
    rw [hShift K, rangeSum_eval_eq ζ cs K (by simp only [List.length_cons] at h; omega)]; rfl

theorem telescope_col0 (ζ : R) (G : UPoly R) :
    ∀ s : Nat,
      Mat.rangeSum (s + 1) (fun j => mul (coeffAt (mul (sub X (C ζ)) G).coeffs j) (CRing.npow ζ j)) =
        neg (mul (coeffAt G.coeffs s) (CRing.npow ζ (s + 1)))
  | 0 => by
    show add zero (mul (coeffAt (mul (sub X (C ζ)) G).coeffs 0) one) = neg (mul (coeffAt G.coeffs 0) (mul one ζ))
    rw [(coeffAt_sub_X_C_mul ζ G).1]; constructive_ring
  | s + 1 => by
    show add (Mat.rangeSum (s + 1) _)
        (mul (coeffAt (mul (sub X (C ζ)) G).coeffs (s + 1)) (CRing.npow ζ (s + 1))) =
      neg (mul (coeffAt G.coeffs (s + 1)) (mul (CRing.npow ζ (s + 1)) ζ))
    rw [telescope_col0 ζ G s, (coeffAt_sub_X_C_mul ζ G).2 s]; constructive_ring

theorem telescope_col_succ (ζ : R) (G : UPoly R) (c : Nat) :
    ∀ d : Nat,
      Mat.rangeSum (c + 1 + (d + 1))
        (fun j => mul (coeffAt (mul (sub X (C ζ)) G).coeffs j)
          (if c + 1 ≤ j then CRing.npow ζ (j - (c + 1)) else zero)) =
        sub (coeffAt G.coeffs c) (mul (coeffAt G.coeffs (c + 1 + d)) (CRing.npow ζ (d + 1)))
  | 0 => by
    have hz : Mat.rangeSum (c + 1)
        (fun j => mul (coeffAt (mul (sub X (C ζ)) G).coeffs j)
          (if c + 1 ≤ j then CRing.npow ζ (j - (c + 1)) else zero)) = zero :=
      Mat.rangeSum_eq_zero fun j hj => by rw [ite_neg (by omega), LawfulCommRing.mul_zero]
    show add (Mat.rangeSum (c + 1) _) _ = sub (coeffAt G.coeffs c) (mul (coeffAt G.coeffs (c + 1 + 0)) (mul one ζ))
    rw [hz, LawfulCommRing.zero_add]
    dsimp only
    rw [ite_pos (Nat.le_refl (c + 1)), Nat.sub_self, (coeffAt_sub_X_C_mul ζ G).2 c]
    show mul _ one = _; constructive_ring
  | d + 1 => by
    show add (Mat.rangeSum (c + 1 + (d + 1)) _)
        (mul (coeffAt (mul (sub X (C ζ)) G).coeffs (c + 1 + (d + 1)))
          (if c + 1 ≤ c + 1 + (d + 1) then CRing.npow ζ (c + 1 + (d + 1) - (c + 1)) else zero)) =
      sub (coeffAt G.coeffs c) (mul (coeffAt G.coeffs (c + 1 + (d + 1))) (mul (CRing.npow ζ (d + 1)) ζ))
    rw [telescope_col_succ ζ G c d, ite_pos (by omega), show c + 1 + (d + 1) - (c + 1) = d + 1 by omega,
      show c + 1 + (d + 1) = (c + 1 + d) + 1 by omega, (coeffAt_sub_X_C_mul ζ G).2 (c + 1 + d)]
    constructive_ring

def polyOfRange : Nat → (Nat → R) → UPoly R
  | 0, _ => zero
  | n + 1, f => add (polyOfRange n f) (mul (C (f n)) (monom n))

theorem coeffAt_polyOfRange :
    ∀ (n : Nat) (f : Nat → R) (i : Nat),
      coeffAt (polyOfRange n f).coeffs i = if i < n then f i else zero
  | 0, _, i => by show coeffAt (zero : UPoly R).coeffs i = zero; rw [coeffs_zero, coeffAt_nil]
  | n + 1, f, i => by
    show coeffAt (add (polyOfRange n f) (mul (C (f n)) (monom n))).coeffs i = _
    rw [coeffAt_add, coeffAt_polyOfRange n f i, coeffAt_C_mul, coeffAt_monom]
    if hEq : i = n then
      subst hEq; rw [ite_neg (Nat.lt_irrefl i), ite_pos rfl, ite_pos (Nat.lt_succ_self i)]; constructive_ring
    else if hLt : i < n then
      rw [ite_pos hLt, ite_neg hEq, ite_pos (Nat.lt_succ_of_lt hLt)]; constructive_ring
    else
      rw [ite_neg hLt, ite_neg hEq, ite_neg (by omega)]; constructive_ring

theorem coeffAt_mul_polyOfRange (B : UPoly R) :
    ∀ (n : Nat) (f : Nat → R) (j : Nat),
      coeffAt (mul (polyOfRange n f) B).coeffs j =
        Mat.rangeSum n (fun i => mul (f i) (if i ≤ j then coeffAt B.coeffs (j - i) else zero))
  | 0, _, _ => by show coeffAt (mul zero B).coeffs _ = zero; rw [LawfulCommRing.zero_mul, coeffs_zero, coeffAt_nil]
  | n + 1, f, j => by
    show coeffAt (mul (add (polyOfRange n f) (mul (C (f n)) (monom n))) B).coeffs j = add _ _
    have hDist : mul (add (polyOfRange n f) (mul (C (f n)) (monom n))) B =
        add (mul (polyOfRange n f) B) (mul (C (f n)) (mul (monom n) B)) := by constructive_ring
    rw [hDist, coeffAt_add, coeffAt_mul_polyOfRange B n f j, coeffAt_C_mul, coeffAt_monom_mul]

theorem bezout_step (mK U0 A V0 B q r : UPoly R)
    (h1 : mul mK (add (mul U0 A) (mul V0 B)) = mK)
    (h2 : mul mK V0 = add (mul q A) r) :
    add (mul (add (mul mK U0) (mul q B)) A) (mul r B) = mK := by
  have hRhs : mK = add (mul (mul mK U0) A) (mul (add (mul q A) r) B) := by
    conv => lhs; rw [← h1]
    rw [LawfulCommRing.left_distrib, ← LawfulCommRing.mul_assoc mK V0 B, h2]
    constructive_ring
  conv => rhs; rw [hRhs]
  constructive_ring

end SylElim
theorem exists_mem_ne_zero_of_coeffAt {R : Type} [CommRingOps R] : ∀ (l : List R) (k : Nat),
    coeffAt l k ≠ zero → ∃ c ∈ l, c ≠ zero
  | [], k, h => absurd (coeffAt_nil k) h
  | c :: _, 0, h => ⟨c, .head _, by rwa [coeffAt_cons_zero] at h⟩
  | _ :: cs, k + 1, h => by
    rw [coeffAt_cons_succ] at h
    obtain ⟨c', hc', hne⟩ := exists_mem_ne_zero_of_coeffAt cs k h
    exact ⟨c', .tail _ hc', hne⟩

namespace Frac
variable {D : Type} [LawfulCommRing D] [NoZeroDivisors D] [DecidableEq D] [NontrivialRing D]
theorem exists_mul_denominator (c : Frac D) : ∃ n d : D, d ≠ zero ∧ mul (of.toFun d) c = of.toFun n := by
  induction c using ind₁ with | h a =>
  refine ⟨a.num, a.den, a.den_ne, sound ?_⟩
  show mul (mul a.den a.num) one = mul a.num (mul one a.den)
  constructive_ring
end Frac
namespace UPoly
variable {R : Type} [LawfulCommRing R] [DecidableEq R]
theorem prodList_nil : prodList ([] : List (UPoly R)) = one := by rfl
theorem prodList_cons (p : UPoly R) (ps : List (UPoly R)) : prodList (p :: ps) = mul p (prodList ps) := by rfl
end UPoly
end Qsag

namespace Qsag.UPoly
open Qsag CommRingOps
 theorem coeffAt_mul_raw {R : Type} [LawfulCommRing R] [DecidableEq R] (A B : UPoly R) (k : Nat) :
   coeffAt (mul A B).coeffs k = coeffAt (rawMul A.coeffs B.coeffs) k := coeffAt_trimPoly _ _
end Qsag.UPoly

namespace Qsag.RingHom
theorem comp_toFun {R S T : Type} [LawfulCommRing R] [LawfulCommRing S] [LawfulCommRing T]
 (ψ : RingHom S T) (φ : RingHom R S) : (ψ.comp φ).toFun = fun x => ψ.toFun (φ.toFun x) := by rfl
theorem id_toFun {R : Type} [CommRingOps R] : (id R).toFun = fun x => x := by rfl
end Qsag.RingHom

namespace Qsag
/-- Module-local constructive finite sum `∑_{i : Fin n} f i`, keeping full definitional reduction
    available inside proofs and decidable evaluations without exposing internal `UcGames` bodies. -/
def qsum : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => f ⟨0, Nat.zero_lt_succ n⟩ + qsum n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

theorem qsum_const : ∀ (n c : Nat), qsum n (fun _ => c) = n * c
  | 0, _ => by simp [qsum]
  | n + 1, c => by
    simp only [qsum, qsum_const n c, Nat.succ_mul]
    omega

theorem qsum_congr {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i = g i) :
    qsum n f = qsum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [qsum, h ⟨0, Nat.zero_lt_succ n⟩]
    rw [ih (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)]

theorem qsum_le_qsum {n : Nat} {f g : Fin n → Nat} (h : ∀ i, f i ≤ g i) :
    qsum n f ≤ qsum n g := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    simp only [qsum]
    have h0 := h ⟨0, Nat.zero_lt_succ n⟩
    have hRest := ih (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
    omega

theorem qsum_add {n : Nat} (f g : Fin n → Nat) :
    qsum n (fun i => f i + g i) = qsum n f + qsum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [qsum, ih]
    omega

theorem qsum_eq_indicator : ∀ (n : Nat) (a : Fin n),
    qsum n (fun i => if i = a then 1 else 0) = 1
  | 0, a => Fin.elim0 a
  | n + 1, ⟨0, _⟩ => by
    simp only [qsum, ↓reduceIte]
    have hZero : qsum n (fun i => if (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1)) = ⟨0, Nat.zero_lt_succ n⟩ then 1 else 0) =
        qsum n (fun _ => 0) := by
      apply qsum_congr
      intro i
      have hNe : (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1)) ≠ ⟨0, Nat.zero_lt_succ n⟩ :=
        fun he => Nat.noConfusion (congrArg Fin.val he)
      simp only [hNe, ↓reduceIte]
    rw [hZero, qsum_const]
    omega
  | n + 1, ⟨k + 1, hk⟩ => by
    simp only [qsum]
    have h0 : (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) ≠ ⟨k + 1, hk⟩ :=
      fun heq => Nat.noConfusion (congrArg Fin.val heq)
    simp only [h0, ↓reduceIte, Nat.zero_add]
    have hShift :
        qsum n (fun i => if (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1)) = ⟨k + 1, hk⟩ then 1 else 0) =
        qsum n (fun i => if i = ⟨k, Nat.lt_of_succ_lt_succ hk⟩ then 1 else 0) := by
      apply qsum_congr
      intro i
      by_cases hik : i.1 = k
      · have h2 : i = ⟨k, Nat.lt_of_succ_lt_succ hk⟩ := Fin.ext hik
        have h1 : (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1)) = ⟨k + 1, hk⟩ :=
          Fin.ext (congrArg Nat.succ hik)
        simp only [h1, ↓reduceIte]
        simp only [h2, ↓reduceIte]
      · have h2 : i ≠ ⟨k, Nat.lt_of_succ_lt_succ hk⟩ := fun heq => hik (congrArg Fin.val heq)
        have h1 : (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1)) ≠ ⟨k + 1, hk⟩ :=
          fun heq => hik (Nat.succ.inj (congrArg Fin.val heq))
        simp only [h1, ↓reduceIte]
        simp only [h2, ↓reduceIte]
    rw [hShift]
    exact qsum_eq_indicator n ⟨k, Nat.lt_of_succ_lt_succ hk⟩

theorem qsum_mul_left (c : Nat) :
    ∀ {n : Nat} (f : Fin n → Nat), qsum n (fun i => c * f i) = c * qsum n f
  | 0, _ => by simp [qsum]
  | n + 1, f => by
    simp only [qsum, Nat.left_distrib]
    rw [qsum_mul_left c (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)]

theorem qsum_mul_right (c : Nat) :
    ∀ {n : Nat} (f : Fin n → Nat), qsum n (fun i => f i * c) = qsum n f * c
  | 0, _ => by simp [qsum]
  | n + 1, f => by
    simp only [qsum, Nat.right_distrib]
    rw [qsum_mul_right c (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)]

theorem qsum_comm :
    ∀ (A B : Nat) (f : Fin A → Fin B → Nat),
      qsum A (fun a => qsum B (fun b => f a b)) =
        qsum B (fun b => qsum A (fun a => f a b))
  | 0, B, _ => by
    simp only [qsum]
    exact (qsum_const B 0).symm
  | A + 1, B, f => by
    simp only [qsum]
    rw [qsum_comm A B (fun a b => f ⟨a.1 + 1, Nat.succ_lt_succ a.2⟩ b), ← qsum_add]

theorem qsum_ite_eq (n : Nat) (a : Fin n) (v : Nat) :
    qsum n (fun i => if i = a then v else 0) = v := by
  have hFactor : qsum n (fun i => if i = a then v else 0) =
      qsum n (fun i => v * (if i = a then 1 else 0)) := by
    apply qsum_congr
    intro i
    by_cases h : i = a <;> simp [h]
  rw [hFactor, qsum_mul_left, qsum_eq_indicator, Nat.mul_one]

/-- Constructive bijection-invariance of `qsum` proved via `qsum_comm` + `qsum_ite_eq`
    with zero list-permutation or pigeonhole machinery. -/
theorem qsum_bijection {n : Nat} (π ρ : Fin n → Fin n)
    (hLeft : ∀ i, ρ (π i) = i) (hRight : ∀ k, π (ρ k) = k) (g : Fin n → Nat) :
    qsum n (fun i => g (π i)) = qsum n g := by
  have hExpand : qsum n (fun i => g (π i)) =
      qsum n (fun i => qsum n (fun k => if k = π i then g k else 0)) := by
    apply qsum_congr
    intro i
    have hCongrK : qsum n (fun k => if k = π i then g k else 0) =
        qsum n (fun k => if k = π i then g (π i) else 0) := by
      apply qsum_congr; intro k
      by_cases hk : k = π i
      · rw [hk]
      · simp only [hk, ↓reduceIte]
    rw [hCongrK, qsum_ite_eq]
  rw [hExpand, qsum_comm]
  apply qsum_congr
  intro k
  have hSwap : qsum n (fun i => if k = π i then g k else 0) =
      qsum n (fun i => if i = ρ k then g k else 0) := by
    apply qsum_congr
    intro i
    by_cases h : i = ρ k
    · have hk : k = π i := by rw [h, hRight]
      have s1 : (if k = π i then g k else 0) = g k := by simp only [hk, ↓reduceIte]
      have s2 : (if i = ρ k then g k else 0) = g k := by simp only [h, ↓reduceIte]
      rw [s1, s2]
    · have hk : k ≠ π i := fun heq => h (by rw [heq, hLeft])
      have s1 : (if k = π i then g k else 0) = 0 := by simp only [hk, ↓reduceIte]
      have s2 : (if i = ρ k then g k else 0) = 0 := by simp only [h, ↓reduceIte]
      rw [s1, s2]
  rw [hSwap, qsum_ite_eq]

theorem qsum_involutive {n : Nat} (π : Fin n → Fin n)
    (hInv : ∀ i, π (π i) = i) (g : Fin n → Nat) :
    qsum n (fun i => g (π i)) = qsum n g :=
  qsum_bijection π π hInv hInv g

/-- Constructive uniqueness-to-`≤ 1` sum bound without existential case splitting. -/
theorem qsum_le_one_of_subsingleton :
    ∀ {n : Nat} (p : Fin n → Bool),
      (∀ i j : Fin n, p i = true → p j = true → i = j) →
      qsum n (fun i => if p i = true then 1 else 0) ≤ 1
  | 0, _, _ => Nat.zero_le 1
  | n + 1, p, hUnique => by
    simp only [qsum]
    cases hp0 : p ⟨0, Nat.zero_lt_succ n⟩
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      exact qsum_le_one_of_subsingleton (fun i => p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
        (fun i j hi hj => Fin.ext (Nat.succ.inj (congrArg Fin.val (hUnique _ _ hi hj))))
    · simp only [↓reduceIte]
      have hTailZero : qsum n (fun i => if p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ = true then 1 else 0) =
          qsum n (fun _ => 0) := by
        apply qsum_congr
        intro i
        cases hpi : p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
        · rfl
        · exfalso
          have hEq := congrArg Fin.val (hUnique ⟨0, Nat.zero_lt_succ n⟩ ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ hp0 hpi)
          exact Nat.noConfusion hEq
      rw [hTailZero, qsum_const]
      omega


@[simp] theorem qsum_zero (f : Fin 0 → Nat) : qsum 0 f = 0 := by rfl
@[simp] theorem qsum_succ (n : Nat) (f : Fin (n+1) → Nat) : qsum (n+1) f = f ⟨0, Nat.zero_lt_succ n⟩ + qsum n (fun i => f ⟨i.val+1, Nat.succ_lt_succ i.isLt⟩) := by rfl
end Qsag

namespace Qsag
open RoundPoly
abbrev GsUniPoly (F : Type) [CommRingOps F] [DecidableEq F] := UPoly F
namespace GsUniPoly
abbrev val {F : Type} [CommRingOps F] [DecidableEq F] (p : GsUniPoly F) := p.coeffs
theorem property {F : Type} [CommRingOps F] [DecidableEq F] (p : GsUniPoly F) : trimPoly p.coeffs = p.coeffs := p.trimmed
abbrev ofCoeffs {F : Type} [LawfulField F] [DecidableEq F] (p : List F) : GsUniPoly F := UPoly.ofList p
end GsUniPoly
/-- Natural scalar in the supplied constructive ring. -/
def gsNat {F : Type} [CommRingOps F] : Nat → F
  | 0 => CommRingOps.zero
  | n + 1 => CommRingOps.add (gsNat n) CommRingOps.one

/-- Powers in the supplied constructive ring. -/
def gsPow {F : Type} [CommRingOps F] (x : F) : Nat → F
  | 0 => CommRingOps.one
  | n + 1 => CommRingOps.mul x (gsPow x n)

/-- Pascal recursion for binomial coefficients. -/
def gsChoose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => gsChoose n k + gsChoose n (k + 1)

/-- Formal `(r,s)` Hasse derivative of the monomial `X^i Y^j`, evaluated at `(x,y)`.
    Binomial coefficients, rather than factorial division, make this valid in every characteristic. -/
def gsHasseMonomial {F : Type} [CommRingOps F]
    (e order : Nat × Nat) (point : F × F) : F :=
  CommRingOps.mul (gsNat (gsChoose e.1 order.1 * gsChoose e.2 order.2))
    (CommRingOps.mul (gsPow point.1 (e.1 - order.1)) (gsPow point.2 (e.2 - order.2)))

/-- Taylor coefficients of `cs` at `b` by repeated synthetic division:
    `cs(Y) = ∑ₛ (gsTaylor n cs b)[s] · (Y - b)^s` whenever `cs.length ≤ n`. Entry `s` is the
    `s`-th Hasse derivative of `cs` at `b`. No binomial or factorial division occurs, so the
    expansion holds over every commutative ring and in every characteristic. -/
def gsTaylor {R : Type} [CommRingOps R] : Nat → List R → R → List R
  | 0, _, _ => []
  | n + 1, cs, b => evalCoeffs cs b :: gsTaylor n (quotLinear cs b) b

/-- Taylor re-expansion preserves evaluation at every point of the ring. Over `R = F[X]` this
    quantifies over all substituted polynomials, so it is a formal identity in `Y`. -/
theorem gsTaylor_eval {R : Type} [LawfulCommRing R] (b y : R) :
    ∀ (n : Nat) (cs : List R), cs.length ≤ n →
      evalCoeffs cs y = evalCoeffs (gsTaylor n cs b) (CommRingOps.sub y b)
  | 0, cs, h => by
    have hcs : cs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero h)
    subst hcs
    rfl
  | n + 1, cs, h => by
    have ih := gsTaylor_eval b y n (quotLinear cs b) (by rw [quotLinear_length]; omega)
    show evalCoeffs cs y = CommRingOps.add (evalCoeffs cs b)
      (CommRingOps.mul (CommRingOps.sub y b)
        (evalCoeffs (gsTaylor n (quotLinear cs b) b) (CommRingOps.sub y b)))
    rw [← ih]
    exact (evalCoeffs_eq_mul_quotLinear_add cs b y).trans (LawfulCommRing.add_comm _ _)

theorem gsPow_zero_mul {R : Type} [LawfulCommRing R] (t w : R) :
    CommRingOps.mul (gsPow t 0) w = w :=
  LawfulCommRing.one_mul w

theorem gsPow_succ_mul {R : Type} [LawfulCommRing R] (t : R) (k : Nat) (w : R) :
    CommRingOps.mul (gsPow t (k + 1)) w = CommRingOps.mul t (CommRingOps.mul (gsPow t k) w) :=
  LawfulCommRing.mul_assoc t (gsPow t k) w

theorem gs_mul_mul_mul_comm {R : Type} [LawfulCommRing R] (a b c d : R) :
    CommRingOps.mul (CommRingOps.mul a b) (CommRingOps.mul c d) =
      CommRingOps.mul (CommRingOps.mul a c) (CommRingOps.mul b d) := by
  rw [LawfulCommRing.mul_assoc a b, ← LawfulCommRing.mul_assoc b c d,
    LawfulCommRing.mul_comm b c, LawfulCommRing.mul_assoc c b d, ← LawfulCommRing.mul_assoc a c]

/-- If the coefficient of `Y^s` is divisible by `t^(m - s)` for every `s < m`, then substituting
    `Y := t * u` gives a value divisible by `t^m`. -/
theorem gs_low_order_divisible {R : Type} [LawfulCommRing R] (t u : R) :
    ∀ (cs : List R) (m : Nat),
      (∀ s : Nat, s < m → ∃ h : R, coeffAt cs s = CommRingOps.mul (gsPow t (m - s)) h) →
      ∃ k : R, evalCoeffs cs (CommRingOps.mul t u) = CommRingOps.mul (gsPow t m) k
  | [], _, _ => ⟨CommRingOps.zero, (LawfulCommRing.mul_zero _).symm⟩
  | c :: cs, 0, _ =>
    ⟨evalCoeffs (c :: cs) (CommRingOps.mul t u), (LawfulCommRing.one_mul _).symm⟩
  | c :: cs, m + 1, h => by
    obtain ⟨h0, hh0⟩ := h 0 (Nat.succ_pos m)
    rw [coeffAt_cons_zero, Nat.sub_zero] at hh0
    have htail : ∀ s : Nat, s < m →
        ∃ h' : R, coeffAt cs s = CommRingOps.mul (gsPow t (m - s)) h' := by
      intro s hs
      obtain ⟨h', hh'⟩ := h (s + 1) (Nat.succ_lt_succ hs)
      rw [coeffAt_cons_succ, Nat.add_sub_add_right] at hh'
      exact ⟨h', hh'⟩
    obtain ⟨k, hk⟩ := gs_low_order_divisible t u cs m htail
    refine ⟨CommRingOps.add h0 (CommRingOps.mul u k), ?_⟩
    show CommRingOps.add c
        (CommRingOps.mul (CommRingOps.mul t u) (evalCoeffs cs (CommRingOps.mul t u))) =
      CommRingOps.mul (gsPow t (m + 1)) (CommRingOps.add h0 (CommRingOps.mul u k))
    rw [hk, hh0, LawfulCommRing.left_distrib]
    exact congrArg (CommRingOps.add (CommRingOps.mul (gsPow t (m + 1)) h0))
      (gs_mul_mul_mul_comm t u (gsPow t m) k)

theorem gsLinear_trimmed {F : Type} [LawfulField F] [DecidableEq F] (a : F) :
    trimPoly [CommRingOps.neg a, CommRingOps.one] = [CommRingOps.neg a, CommRingOps.one] := by
  simp [trimPoly, LawfulField.one_ne_zero]

/-- The monic linear polynomial `X - a` as a canonical element of `F[X]`. -/
def gsLinear {F : Type} [LawfulField F] [DecidableEq F] (a : F) : GsUniPoly F :=
  ⟨[CommRingOps.neg a, CommRingOps.one], gsLinear_trimmed a⟩

/-- The constant polynomial `b` as a canonical element of `F[X]`. -/
def gsConst {F : Type} [LawfulField F] [DecidableEq F] (b : F) : GsUniPoly F :=
  GsUniPoly.ofCoeffs [b]

theorem gsLinear_eval {F : Type} [LawfulField F] [DecidableEq F] (a c : F) :
    evalCoeffs (gsLinear a).coeffs c = CommRingOps.sub c a := by
  show evalCoeffs [CommRingOps.neg a, CommRingOps.one] c = CommRingOps.sub c a
  rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_comm c (CommRingOps.neg a)]
  simp only [evalCoeffs_cons, evalCoeffs_nil, LawfulCommRing.mul_zero, LawfulCommRing.add_zero,
    LawfulCommRing.mul_one]

/-- Formal factor theorem in `F[X]`: a polynomial vanishing at `a` is `(X - a)` times a
    polynomial, with the quotient produced by `polyDivMod`. -/
theorem gsLinear_factor {F : Type} [LawfulField F] [DecidableEq F] (a : F)
    (c : GsUniPoly F) (hroot : evalCoeffs c.coeffs a = CommRingOps.zero) :
    ∃ u : GsUniPoly F, c = CommRingOps.mul (gsLinear a) u := by
  have hLne : trimPoly [CommRingOps.neg a, CommRingOps.one] ≠ [] := by
    rw [gsLinear_trimmed]
    exact List.cons_ne_nil _ _
  have hspec := polyDivMod_spec c.coeffs [CommRingOps.neg a, CommRingOps.one] hLne
  dsimp only at hspec
  rcases hspec with ⟨hqTrim, hrTrim, hDecomp, hrLt⟩
  rw [gsLinear_trimmed] at hrLt
  have hLeval : evalCoeffs [CommRingOps.neg a, CommRingOps.one] a = CommRingOps.zero :=
    (gsLinear_eval a a).trans (LawfulCommRing.sub_self a)
  have hEv : evalCoeffs (polyDivMod c.coeffs [CommRingOps.neg a, CommRingOps.one]).2 a =
      CommRingOps.zero := by
    have h1 : evalCoeffs (trimPoly c.coeffs) a = evalCoeffs _ a :=
      congrArg (fun p => evalCoeffs p a) hDecomp
    rw [evalCoeffs_trimPoly, hroot, evalCoeffs_pAdd, evalCoeffs_pMul, hLeval,
      LawfulCommRing.mul_zero, LawfulCommRing.zero_add] at h1
    exact h1.symm
  have hrNil : (polyDivMod c.coeffs [CommRingOps.neg a, CommRingOps.one]).2 = [] := by
    cases hr : (polyDivMod c.coeffs [CommRingOps.neg a, CommRingOps.one]).2 with
    | nil => rfl
    | cons r0 rs =>
      rw [hr] at hrLt hrTrim hEv
      cases rs with
      | cons r1 rs' =>
        have h2 : 2 ≤ (r0 :: r1 :: rs').length :=
          Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))
        have h3 : ([CommRingOps.neg a, CommRingOps.one] : List F).length = 2 := rfl
        exfalso
        omega
      | nil =>
        have hr0 : r0 = CommRingOps.zero := by
          simpa only [evalCoeffs_cons, evalCoeffs_nil, LawfulCommRing.mul_zero,
            LawfulCommRing.add_zero] using hEv
        have hz : trimPoly [(CommRingOps.zero : F)] = [] := by simp [trimPoly]
        rw [hr0] at hrTrim
        exact absurd (hz.symm.trans hrTrim) (List.cons_ne_nil _ _).symm
  rw [hrNil, pAdd_nil_right] at hDecomp
  exact ⟨⟨(polyDivMod c.coeffs [CommRingOps.neg a, CommRingOps.one]).1, hqTrim⟩,
    UPoly.ext (c.trimmed.symm.trans (hDecomp.trans
      ((trimPoly_idem (rawMul (polyDivMod c.coeffs [CommRingOps.neg a, CommRingOps.one]).1
          [CommRingOps.neg a, CommRingOps.one])).trans
        (pMul_comm (polyDivMod c.coeffs [CommRingOps.neg a, CommRingOps.one]).1
          [CommRingOps.neg a, CommRingOps.one]))))⟩

theorem gsLinear_mul_cancel {F : Type} [LawfulField F] [DecidableEq F] (c : F)
    (x y : GsUniPoly F)
    (h : CommRingOps.mul (gsLinear c) x = CommRingOps.mul (gsLinear c) y) : x = y := by
  have hz : CommRingOps.mul (gsLinear c) (CommRingOps.sub x y) = CommRingOps.zero := by
    rw [LawfulCommRing.mul_sub, h, LawfulCommRing.sub_self]
  cases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hz with
  | inl hT =>
    exact absurd (show ([CommRingOps.neg c, CommRingOps.one] : List F) = [] from
      congrArg UPoly.coeffs hT) (List.cons_ne_nil _ _)
  | inr hs => exact LawfulCommRing.sub_eq_zero_iff.mp hs

/-- Distinct linear factors are coprime: `(X - c)^k ∣ (X - a) · v` with `c ≠ a` forces
    `(X - c)^k ∣ v`. Evaluation at `c` and the formal factor theorem replace Bézout. -/
theorem gsLinear_coprime_cancel_one {F : Type} [LawfulField F] [DecidableEq F]
    (c a : F) (hne : c ≠ a) :
    ∀ (k : Nat) (w v : GsUniPoly F),
      CommRingOps.mul (gsPow (gsLinear c) k) w = CommRingOps.mul (gsLinear a) v →
      ∃ w' : GsUniPoly F, v = CommRingOps.mul (gsPow (gsLinear c) k) w'
  | 0, _, v, _ => ⟨v, (gsPow_zero_mul (gsLinear c) v).symm⟩
  | k + 1, w, v, h => by
    letI : NoZeroDivisors F := LawfulField.toNoZeroDivisors F
    have hstep := gsPow_succ_mul (gsLinear c) k w
    have hL : evalCoeffs (CommRingOps.mul (gsPow (gsLinear c) (k + 1)) w).coeffs c =
        CommRingOps.zero := by
      rw [hstep]
      show evalCoeffs (pMul (gsLinear c).coeffs
        (CommRingOps.mul (gsPow (gsLinear c) k) w).coeffs) c = CommRingOps.zero
      rw [evalCoeffs_pMul, gsLinear_eval, LawfulCommRing.sub_self, LawfulCommRing.zero_mul]
    have hR : evalCoeffs (CommRingOps.mul (gsLinear a) v).coeffs c =
        CommRingOps.mul (CommRingOps.sub c a) (evalCoeffs v.coeffs c) := by
      show evalCoeffs (pMul (gsLinear a).coeffs v.coeffs) c =
        CommRingOps.mul (CommRingOps.sub c a) (evalCoeffs v.coeffs c)
      rw [evalCoeffs_pMul, gsLinear_eval]
    have hev : evalCoeffs (CommRingOps.mul (gsPow (gsLinear c) (k + 1)) w).coeffs c =
        evalCoeffs (CommRingOps.mul (gsLinear a) v).coeffs c := by rw [h]
    have hv0 : evalCoeffs v.coeffs c = CommRingOps.zero := by
      cases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero
          (hR.symm.trans (hev.symm.trans hL)) with
      | inl hs => exact absurd (LawfulCommRing.sub_eq_zero_iff.mp hs) hne
      | inr hv => exact hv
    obtain ⟨v1, hv1⟩ := gsLinear_factor c v hv0
    have h2 : CommRingOps.mul (gsLinear c) (CommRingOps.mul (gsPow (gsLinear c) k) w) =
        CommRingOps.mul (gsLinear c) (CommRingOps.mul (gsLinear a) v1) := by
      rw [← hstep, h, hv1, ← LawfulCommRing.mul_assoc, ← LawfulCommRing.mul_assoc,
        LawfulCommRing.mul_comm (gsLinear a) (gsLinear c)]
    obtain ⟨w1, hw1⟩ :=
      gsLinear_coprime_cancel_one c a hne k w v1 (gsLinear_mul_cancel c _ _ h2)
    exact ⟨w1, by rw [hv1, hw1]; exact (gsPow_succ_mul (gsLinear c) k w1).symm⟩

theorem gsLinear_pow_coprime_cancel {F : Type} [LawfulField F] [DecidableEq F]
    (c a : F) (hne : c ≠ a) (k : Nat) :
    ∀ (e : Nat) (w v : GsUniPoly F),
      CommRingOps.mul (gsPow (gsLinear c) k) w = CommRingOps.mul (gsPow (gsLinear a) e) v →
      ∃ w' : GsUniPoly F, v = CommRingOps.mul (gsPow (gsLinear c) k) w'
  | 0, w, v, h => ⟨w, (gsPow_zero_mul (gsLinear a) v).symm.trans h.symm⟩
  | e + 1, w, v, h => by
    obtain ⟨w1, hw1⟩ := gsLinear_coprime_cancel_one c a hne k w
      (CommRingOps.mul (gsPow (gsLinear a) e) v) (h.trans (gsPow_succ_mul (gsLinear a) e v))
    exact gsLinear_pow_coprime_cancel c a hne k e w1 v hw1.symm

theorem gsLinear_mul_length {F : Type} [LawfulField F] [DecidableEq F] (x : F)
    (h : GsUniPoly F) (hh : h.coeffs ≠ []) :
    (CommRingOps.mul (gsLinear x) h).coeffs.length = h.coeffs.length + 1 ∧
      (CommRingOps.mul (gsLinear x) h).coeffs ≠ [] := by
  have hl := pMul_length_of_trimmed_ne_nil (a := [CommRingOps.neg x, CommRingOps.one])
    (b := h.coeffs) (gsLinear_trimmed x) h.trimmed (List.cons_ne_nil _ _) hh
  have h2 : ([CommRingOps.neg x, CommRingOps.one] : List F).length = 2 := rfl
  rw [h2] at hl
  refine ⟨?_, hl.2⟩
  have h1 := hl.1
  show (pMul [CommRingOps.neg x, CommRingOps.one] h.coeffs).length = h.coeffs.length + 1
  omega

theorem gsLinear_pow_mul_length {F : Type} [LawfulField F] [DecidableEq F] (x : F) :
    ∀ (m : Nat) (h : GsUniPoly F), h.coeffs ≠ [] →
      (CommRingOps.mul (gsPow (gsLinear x) m) h).coeffs.length = m + h.coeffs.length ∧
        (CommRingOps.mul (gsPow (gsLinear x) m) h).coeffs ≠ []
  | 0, h, hh => by
    rw [gsPow_zero_mul]
    exact ⟨(Nat.zero_add _).symm, hh⟩
  | m + 1, h, hh => by
    have ih := gsLinear_pow_mul_length x m h hh
    have hl := gsLinear_mul_length x _ ih.2
    rw [gsPow_succ_mul]
    exact ⟨by rw [hl.1, ih.1]; omega, hl.2⟩

/-- A nonzero polynomial divisible by `(X - x)^m` at each of `A` distinct points has more than
    `m * A` coefficients. -/
theorem gs_multiplicity_length {F : Type} [LawfulField F] [DecidableEq F] (m : Nat) :
    ∀ (xs : List F) (g : GsUniPoly F), xs.Nodup → g.coeffs ≠ [] →
      (∀ x ∈ xs, ∃ k : GsUniPoly F, g = CommRingOps.mul (gsPow (gsLinear x) m) k) →
      m * xs.length + 1 ≤ g.coeffs.length
  | [], g, _, hg, _ => by
    cases hv : g.coeffs with
    | nil => exact absurd hv hg
    | cons _ _ => simp
  | x :: xs, g, hnd, hg, hdiv => by
    obtain ⟨h, hh⟩ := hdiv x (.head _)
    have hhne : h.coeffs ≠ [] := by
      intro h0
      have hzero : h = CommRingOps.zero := UPoly.ext h0
      have hg0 : g = CommRingOps.zero := by
        rw [hh, hzero]
        exact LawfulCommRing.mul_zero _
      exact hg (congrArg UPoly.coeffs hg0)
    have hrest : ∀ y ∈ xs, ∃ k : GsUniPoly F,
        h = CommRingOps.mul (gsPow (gsLinear y) m) k := by
      intro y hy
      obtain ⟨k, hk⟩ := hdiv y (.tail _ hy)
      have hne : y ≠ x := fun e => (List.pairwise_cons.mp hnd).1 y hy e.symm
      exact gsLinear_pow_coprime_cancel y x hne m m k h (hk.symm.trans hh)
    have ih := gs_multiplicity_length m xs h (List.pairwise_cons.mp hnd).2 hhne hrest
    have hl := (gsLinear_pow_mul_length x m h hhne).1
    have e : m * (x :: xs).length = m * xs.length + m := Nat.mul_succ m xs.length
    rw [hh, hl, e]
    omega

theorem gsUniHasse_zero_eq_evalCoeffs {R : Type} [CommRingOps R] :
    ∀ (cs : List R) (b : R), gsUniHasse cs 0 b = evalCoeffs cs b
  | [], _ => rfl
  | c :: cs, b => by
    show CommRingOps.add c (CommRingOps.mul b (gsUniHasse cs 0 b)) =
      CommRingOps.add c (CommRingOps.mul b (evalCoeffs cs b))
    rw [gsUniHasse_zero_eq_evalCoeffs cs b]

theorem gsUniHasse_quotLinear {R : Type} [LawfulCommRing R] :
    ∀ (cs : List R) (k : Nat) (b : R),
      gsUniHasse (quotLinear cs b) k b = gsUniHasse cs (k + 1) b
  | [], _, _ => rfl
  | [c₀], k, b => by
    show CommRingOps.zero =
      CommRingOps.add (gsUniHasse ([] : List R) k b)
        (CommRingOps.mul b (gsUniHasse ([] : List R) (k + 1) b))
    change CommRingOps.zero =
      CommRingOps.add CommRingOps.zero (CommRingOps.mul b CommRingOps.zero)
    rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | c₀ :: c₁ :: tl, 0, b => by
    have ih := gsUniHasse_quotLinear (c₁ :: tl) 0 b
    show CommRingOps.add (evalCoeffs (c₁ :: tl) b)
        (CommRingOps.mul b (gsUniHasse (quotLinear (c₁ :: tl) b) 0 b)) =
      CommRingOps.add (gsUniHasse (c₁ :: tl) 0 b)
        (CommRingOps.mul b (gsUniHasse (c₁ :: tl) 1 b))
    rw [ih, gsUniHasse_zero_eq_evalCoeffs (c₁ :: tl) b]
  | c₀ :: c₁ :: tl, k + 1, b => by
    have ih0 := gsUniHasse_quotLinear (c₁ :: tl) k b
    have ih1 := gsUniHasse_quotLinear (c₁ :: tl) (k + 1) b
    show CommRingOps.add (gsUniHasse (quotLinear (c₁ :: tl) b) k b)
        (CommRingOps.mul b (gsUniHasse (quotLinear (c₁ :: tl) b) (k + 1) b)) =
      CommRingOps.add (gsUniHasse (c₁ :: tl) (k + 1) b)
        (CommRingOps.mul b (gsUniHasse (c₁ :: tl) (k + 2) b))
    rw [ih0, ih1]

/-- Every synthetic-division Taylor coefficient `(gsTaylor n cs b)[k]` equals `gsUniHasse cs k b`. -/
theorem coeffAt_gsTaylor_eq_gsUniHasse {R : Type} [LawfulCommRing R] :
    ∀ (n : Nat) (cs : List R) (k : Nat) (b : R),
      cs.length ≤ n → coeffAt (gsTaylor n cs b) k = gsUniHasse cs k b
  | 0, cs, k, b, h => by
    have hcs : cs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero h)
    subst hcs
    rfl
  | n + 1, cs, 0, b, _ => by
    show coeffAt (evalCoeffs cs b :: gsTaylor n (quotLinear cs b) b) 0 = gsUniHasse cs 0 b
    rw [coeffAt_cons_zero, gsUniHasse_zero_eq_evalCoeffs]
  | n + 1, cs, k + 1, b, h => by
    show coeffAt (evalCoeffs cs b :: gsTaylor n (quotLinear cs b) b) (k + 1) =
      gsUniHasse cs (k + 1) b
    rw [coeffAt_cons_succ,
        coeffAt_gsTaylor_eq_gsUniHasse n (quotLinear cs b) k b (by rw [quotLinear_length]; omega),
        gsUniHasse_quotLinear]

theorem gsNat_add {R : Type} [LawfulCommRing R] (u : Nat) :
    ∀ (v : Nat), (gsNat (u + v) : R) = CommRingOps.add (gsNat u) (gsNat v)
  | 0 => (LawfulCommRing.add_zero _).symm
  | v + 1 => by
    show CommRingOps.add (gsNat (u + v)) CommRingOps.one =
      CommRingOps.add (gsNat u) (CommRingOps.add (gsNat v) CommRingOps.one)
    rw [gsNat_add u v, LawfulCommRing.add_assoc]

theorem gsNat_mul {R : Type} [LawfulCommRing R] (u : Nat) :
    ∀ (v : Nat), (gsNat (u * v) : R) = CommRingOps.mul (gsNat u) (gsNat v)
  | 0 => (LawfulCommRing.mul_zero _).symm
  | v + 1 => by
    rw [Nat.mul_succ, gsNat_add]
    show CommRingOps.add (gsNat (u * v)) (gsNat u) =
      CommRingOps.mul (gsNat u) (CommRingOps.add (gsNat v) CommRingOps.one)
    rw [gsNat_mul u v, LawfulCommRing.left_distrib, LawfulCommRing.mul_one]

theorem gsChoose_eq_zero_of_lt :
    ∀ (i r : Nat), i < r → gsChoose i r = 0
  | 0, _ + 1, _ => rfl
  | i + 1, r + 1, h => by
    have hlt := Nat.lt_of_succ_lt_succ h
    show gsChoose i r + gsChoose i (r + 1) = 0
    rw [gsChoose_eq_zero_of_lt i r hlt,
        gsChoose_eq_zero_of_lt i (r + 1) (Nat.lt_succ_of_lt hlt)]

/-- Univariate binomial-Hasse basis element `(i choose r) * a^(i - r)`. -/
def gsUniHasseBasis {R : Type} [CommRingOps R] (r : Nat) (a : R) (i : Nat) : R :=
  CommRingOps.mul (gsNat (gsChoose i r)) (gsPow a (i - r))

theorem gsUniHasseBasis_zero_succ {R : Type} [LawfulCommRing R] (a : R) (i : Nat) :
    gsUniHasseBasis 0 a (i + 1) = CommRingOps.mul a (gsUniHasseBasis 0 a i) := by
  unfold gsUniHasseBasis
  have h1 : (gsNat (gsChoose (i + 1) 0) : R) = CommRingOps.one :=
    LawfulCommRing.zero_add CommRingOps.one
  have h2 : (gsNat (gsChoose i 0) : R) = CommRingOps.one := by
    cases i <;> exact LawfulCommRing.zero_add CommRingOps.one
  have hsub1 : i + 1 - 0 = i + 1 := rfl
  have hsub2 : i - 0 = i := rfl
  rw [h1, h2, hsub1, hsub2, LawfulCommRing.one_mul, LawfulCommRing.one_mul]
  rfl

theorem gsUniHasseBasis_succ_succ {R : Type} [LawfulCommRing R] (r : Nat) (a : R) (i : Nat) :
    gsUniHasseBasis (r + 1) a (i + 1) =
      CommRingOps.add (gsUniHasseBasis r a i)
        (CommRingOps.mul a (gsUniHasseBasis (r + 1) a i)) := by
  unfold gsUniHasseBasis
  have hsub : (i + 1) - (r + 1) = i - r := Nat.add_sub_add_right i 1 r
  show CommRingOps.mul (gsNat (gsChoose i r + gsChoose i (r + 1))) (gsPow a ((i + 1) - (r + 1))) = _
  rw [hsub, gsNat_add, LawfulCommRing.right_distrib]
  apply congrArg (CommRingOps.add _)
  if hle : i ≤ r then
    have hc0 : gsChoose i (r + 1) = 0 := gsChoose_eq_zero_of_lt i (r + 1) (Nat.lt_succ_of_le hle)
    rw [hc0]
    change CommRingOps.mul CommRingOps.zero _ =
      CommRingOps.mul a (CommRingOps.mul CommRingOps.zero _)
    rw [LawfulCommRing.zero_mul, LawfulCommRing.zero_mul, LawfulCommRing.mul_zero]
  else
    have hstep : i - r = (i - (r + 1)) + 1 := by omega
    rw [hstep]
    show CommRingOps.mul (gsNat (gsChoose i (r + 1)))
        (CommRingOps.mul a (gsPow a (i - (r + 1)))) =
      CommRingOps.mul a (CommRingOps.mul (gsNat (gsChoose i (r + 1))) (gsPow a (i - (r + 1))))
    rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm _ a, LawfulCommRing.mul_assoc]

theorem gs_range_succ_map :
    ∀ (n : Nat), List.range (n + 1) = 0 :: (List.range n).map (· + 1)
  | 0 => rfl
  | n + 1 => by
    conv => lhs; rw [List.range_succ, gs_range_succ_map n]
    conv => rhs; rw [List.range_succ]
    simp [List.map_append]

theorem dotVec_map_add {R : Type} [LawfulCommRing R] {α : Type} (f g : α → R) :
    ∀ (xs : List α) (cs : List R),
      dotVec (xs.map (fun x => CommRingOps.add (f x) (g x))) cs =
        CommRingOps.add (dotVec (xs.map f) cs) (dotVec (xs.map g) cs)
  | [], _ => (LawfulCommRing.add_zero _).symm
  | _ :: _, [] => (LawfulCommRing.add_zero _).symm
  | x :: xs, c :: cs => by
    show CommRingOps.add (CommRingOps.mul (CommRingOps.add (f x) (g x)) c)
        (dotVec (xs.map (fun y => CommRingOps.add (f y) (g y))) cs) =
      CommRingOps.add
        (CommRingOps.add (CommRingOps.mul (f x) c) (dotVec (xs.map f) cs))
        (CommRingOps.add (CommRingOps.mul (g x) c) (dotVec (xs.map g) cs))
    rw [dotVec_map_add f g xs cs, LawfulCommRing.right_distrib, LawfulCommRing.add_add_add_comm]

/-- Equivalence between Horner-Hasse evaluation and binomial dot-product evaluation. -/
theorem gsUniHasse_eq_dotVec {R : Type} [LawfulCommRing R] :
    ∀ (cs : List R) (r : Nat) (a : R),
      gsUniHasse cs r a = dotVec ((List.range cs.length).map (gsUniHasseBasis r a)) cs
  | [], _, _ => rfl
  | c :: cs, 0, a => by
    rw [List.length_cons, gs_range_succ_map, List.map_cons, List.map_map]
    have h0 : gsUniHasseBasis 0 a 0 = (CommRingOps.one : R) := by
      unfold gsUniHasseBasis
      change CommRingOps.mul (CommRingOps.add CommRingOps.zero CommRingOps.one) CommRingOps.one = _
      rw [LawfulCommRing.zero_add, LawfulCommRing.mul_one]
    have hmap : (List.range cs.length).map (gsUniHasseBasis 0 a ∘ (· + 1)) =
        scaleVec a ((List.range cs.length).map (gsUniHasseBasis 0 a)) := by
      unfold scaleVec
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      exact gsUniHasseBasis_zero_succ a i
    show CommRingOps.add c (CommRingOps.mul a (gsUniHasse cs 0 a)) =
      CommRingOps.add (CommRingOps.mul (gsUniHasseBasis 0 a 0) c)
        (dotVec ((List.range cs.length).map (gsUniHasseBasis 0 a ∘ (· + 1))) cs)
    rw [h0, LawfulCommRing.one_mul, hmap, dotVec_scaleVec, gsUniHasse_eq_dotVec cs 0 a]
  | c :: cs, r + 1, a => by
    rw [List.length_cons, gs_range_succ_map, List.map_cons, List.map_map]
    have h0 : gsUniHasseBasis (r + 1) a 0 = (CommRingOps.zero : R) := by
      unfold gsUniHasseBasis
      change CommRingOps.mul CommRingOps.zero _ = _
      exact LawfulCommRing.zero_mul _
    have hmap : (List.range cs.length).map (gsUniHasseBasis (r + 1) a ∘ (· + 1)) =
        (List.range cs.length).map (fun i =>
          CommRingOps.add (gsUniHasseBasis r a i)
            (CommRingOps.mul a (gsUniHasseBasis (r + 1) a i))) := by
      apply List.map_congr_left
      intro i _
      exact gsUniHasseBasis_succ_succ r a i
    have hscale : (List.range cs.length).map (fun i =>
        CommRingOps.mul a (gsUniHasseBasis (r + 1) a i)) =
        scaleVec a ((List.range cs.length).map (gsUniHasseBasis (r + 1) a)) := by
      unfold scaleVec
      rw [List.map_map]
      rfl
    show CommRingOps.add (gsUniHasse cs r a) (CommRingOps.mul a (gsUniHasse cs (r + 1) a)) =
      CommRingOps.add (CommRingOps.mul (gsUniHasseBasis (r + 1) a 0) c)
        (dotVec ((List.range cs.length).map (gsUniHasseBasis (r + 1) a ∘ (· + 1))) cs)
    rw [h0, LawfulCommRing.zero_mul, LawfulCommRing.zero_add, hmap, dotVec_map_add,
        hscale, dotVec_scaleVec, gsUniHasse_eq_dotVec cs r a, gsUniHasse_eq_dotVec cs (r + 1) a]

theorem gsUniHasse_trimPoly {F : Type} [LawfulCommRing F] [DecidableEq F] :
    ∀ (cs : List F) (r : Nat) (a : F),
      gsUniHasse (trimPoly cs) r a = gsUniHasse cs r a
  | [], _, _ => rfl
  | c :: cs, r, a => by
    simp only [trimPoly]
    split
    · next h =>
      rcases h with ⟨hcs, hc⟩
      have ih0 := gsUniHasse_trimPoly cs 0 a
      rw [hcs] at ih0
      cases r with
      | zero =>
        show CommRingOps.zero = CommRingOps.add c (CommRingOps.mul a (gsUniHasse cs 0 a))
        rw [hc, ← ih0]
        change CommRingOps.zero = CommRingOps.add CommRingOps.zero (CommRingOps.mul a CommRingOps.zero)
        rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
      | succ r' =>
        have ihr := gsUniHasse_trimPoly cs r' a
        have ihr1 := gsUniHasse_trimPoly cs (r' + 1) a
        rw [hcs] at ihr ihr1
        show CommRingOps.zero =
          CommRingOps.add (gsUniHasse cs r' a) (CommRingOps.mul a (gsUniHasse cs (r' + 1) a))
        rw [← ihr, ← ihr1]
        change CommRingOps.zero = CommRingOps.add CommRingOps.zero (CommRingOps.mul a CommRingOps.zero)
        rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    · cases r with
      | zero =>
        show CommRingOps.add c (CommRingOps.mul a (gsUniHasse (trimPoly cs) 0 a)) =
          CommRingOps.add c (CommRingOps.mul a (gsUniHasse cs 0 a))
        rw [gsUniHasse_trimPoly cs 0 a]
      | succ r' =>
        show CommRingOps.add (gsUniHasse (trimPoly cs) r' a)
            (CommRingOps.mul a (gsUniHasse (trimPoly cs) (r' + 1) a)) =
          CommRingOps.add (gsUniHasse cs r' a) (CommRingOps.mul a (gsUniHasse cs (r' + 1) a))
        rw [gsUniHasse_trimPoly cs r' a, gsUniHasse_trimPoly cs (r' + 1) a]

theorem gsUniHasse_rawAdd {F : Type} [LawfulCommRing F] :
    ∀ (u v : List F) (r : Nat) (a : F),
      gsUniHasse (rawAddCoeffs u v) r a =
        CommRingOps.add (gsUniHasse u r a) (gsUniHasse v r a)
  | [], v, r, a => by
    show gsUniHasse v r a = CommRingOps.add CommRingOps.zero (gsUniHasse v r a)
    exact (LawfulCommRing.zero_add _).symm
  | u, [], r, a => by
    cases u <;> exact (LawfulCommRing.add_zero _).symm
  | c :: cs, d :: ds, 0, a => by
    show CommRingOps.add (CommRingOps.add c d)
        (CommRingOps.mul a (gsUniHasse (rawAddCoeffs cs ds) 0 a)) =
      CommRingOps.add
        (CommRingOps.add c (CommRingOps.mul a (gsUniHasse cs 0 a)))
        (CommRingOps.add d (CommRingOps.mul a (gsUniHasse ds 0 a)))
    rw [gsUniHasse_rawAdd cs ds 0 a, LawfulCommRing.left_distrib, LawfulCommRing.add_add_add_comm]
  | _ :: cs, _ :: ds, r + 1, a => by
    show CommRingOps.add (gsUniHasse (rawAddCoeffs cs ds) r a)
        (CommRingOps.mul a (gsUniHasse (rawAddCoeffs cs ds) (r + 1) a)) =
      CommRingOps.add
        (CommRingOps.add (gsUniHasse cs r a) (CommRingOps.mul a (gsUniHasse cs (r + 1) a)))
        (CommRingOps.add (gsUniHasse ds r a) (CommRingOps.mul a (gsUniHasse ds (r + 1) a)))
    rw [gsUniHasse_rawAdd cs ds r a, gsUniHasse_rawAdd cs ds (r + 1) a,
        LawfulCommRing.left_distrib, LawfulCommRing.add_add_add_comm]

theorem gsUniHasse_map_mul {F : Type} [LawfulCommRing F] (c : F) :
    ∀ (u : List F) (r : Nat) (a : F),
      gsUniHasse (u.map (CommRingOps.mul c)) r a =
        CommRingOps.mul c (gsUniHasse u r a)
  | [], _, _ => (LawfulCommRing.mul_zero c).symm
  | x :: xs, 0, a => by
    show CommRingOps.add (CommRingOps.mul c x)
        (CommRingOps.mul a (gsUniHasse (xs.map (CommRingOps.mul c)) 0 a)) =
      CommRingOps.mul c (CommRingOps.add x (CommRingOps.mul a (gsUniHasse xs 0 a)))
    rw [gsUniHasse_map_mul c xs 0 a, LawfulCommRing.left_distrib,
        ← LawfulCommRing.mul_assoc a c _, LawfulCommRing.mul_comm a c, LawfulCommRing.mul_assoc]
  | _ :: xs, r + 1, a => by
    show CommRingOps.add (gsUniHasse (xs.map (CommRingOps.mul c)) r a)
        (CommRingOps.mul a (gsUniHasse (xs.map (CommRingOps.mul c)) (r + 1) a)) =
      CommRingOps.mul c
        (CommRingOps.add (gsUniHasse xs r a) (CommRingOps.mul a (gsUniHasse xs (r + 1) a)))
    rw [gsUniHasse_map_mul c xs r a, gsUniHasse_map_mul c xs (r + 1) a,
        LawfulCommRing.left_distrib,
        ← LawfulCommRing.mul_assoc a c _, LawfulCommRing.mul_comm a c, LawfulCommRing.mul_assoc]

theorem gsConst_mul_val {F : Type} [LawfulField F] [DecidableEq F]
    (c : F) (p : GsUniPoly F) :
    (CommRingOps.mul (gsConst c) p).coeffs = pScale c p.coeffs := by
  show pMul (trimPoly [c]) p.coeffs = pScale c p.coeffs
  rw [pMul_trimPoly_left]
  unfold pMul pScale
  rw [trimPoly_eq_iff_coeffAt]
  intro k
  simp only [rawMul, coeffAt_addCoeffs]
  cases k with
  | zero => rw [coeffAt_cons_zero, LawfulCommRing.add_zero]
  | succ k' => rw [coeffAt_cons_succ, coeffAt_nil, LawfulCommRing.add_zero]

theorem gsUniHasse_bivariate_comm {F : Type} [LawfulField F] [DecidableEq F]
    (r : Nat) (a b : F) :
    ∀ (Q : List (GsUniPoly F)) (s : Nat),
      gsUniHasse (gsUniHasse Q s (gsConst b)).coeffs r a =
        gsUniHasse (Q.map (fun p => gsUniHasse p.coeffs r a)) s b
  | [], _ => rfl
  | q₀ :: qs, 0 => by
    show gsUniHasse (CommRingOps.add q₀ (CommRingOps.mul (gsConst b) (gsUniHasse qs 0 (gsConst b)))).coeffs r a =
      CommRingOps.add (gsUniHasse q₀.coeffs r a)
        (CommRingOps.mul b (gsUniHasse (qs.map (fun p => gsUniHasse p.coeffs r a)) 0 b))
    change gsUniHasse (pAdd q₀.coeffs (CommRingOps.mul (gsConst b) (gsUniHasse qs 0 (gsConst b))).coeffs) r a = _
    rw [pAdd, gsUniHasse_trimPoly, gsUniHasse_rawAdd, gsConst_mul_val,
        pScale, gsUniHasse_trimPoly, gsUniHasse_map_mul, gsUniHasse_bivariate_comm r a b qs 0]
  | _ :: qs, s + 1 => by
    show gsUniHasse (CommRingOps.add (gsUniHasse qs s (gsConst b))
        (CommRingOps.mul (gsConst b) (gsUniHasse qs (s + 1) (gsConst b)))).coeffs r a =
      CommRingOps.add (gsUniHasse (qs.map (fun p => gsUniHasse p.coeffs r a)) s b)
        (CommRingOps.mul b (gsUniHasse (qs.map (fun p => gsUniHasse p.coeffs r a)) (s + 1) b))
    change gsUniHasse (pAdd (gsUniHasse qs s (gsConst b)).coeffs
        (CommRingOps.mul (gsConst b) (gsUniHasse qs (s + 1) (gsConst b))).coeffs) r a = _
    rw [pAdd, gsUniHasse_trimPoly, gsUniHasse_rawAdd, gsConst_mul_val,
        pScale, gsUniHasse_trimPoly, gsUniHasse_map_mul,
        gsUniHasse_bivariate_comm r a b qs s, gsUniHasse_bivariate_comm r a b qs (s + 1)]

/-- Slice a flat vector into consecutive blocks of prescribed widths. -/
def gsVarX {F : Type} [LawfulField F] [DecidableEq F] : GsUniPoly F :=
  ⟨[CommRingOps.zero, CommRingOps.one], by simp [trimPoly, LawfulField.one_ne_zero]⟩

theorem gsConst_zero {F : Type} [LawfulField F] [DecidableEq F] :
    (gsConst CommRingOps.zero : GsUniPoly F) = CommRingOps.zero := by
  apply UPoly.ext
  show trimPoly [CommRingOps.zero] = []
  simp [trimPoly]

theorem gsVarX_sub_gsConst {F : Type} [LawfulField F] [DecidableEq F] (a : F) :
    CommRingOps.sub gsVarX (gsConst a) = gsLinear a := by
  apply UPoly.ext
  apply eq_of_isTrimmed_coeffAt _ _ (CommRingOps.sub gsVarX (gsConst a)).trimmed (gsLinear_trimmed a)
  intro k
  change coeffAt (pSub [CommRingOps.zero, CommRingOps.one] (trimPoly [a])) k =
    coeffAt [CommRingOps.neg a, CommRingOps.one] k
  rw [coeffAt_pSub, coeffAt_trimPoly]
  cases k with
  | zero =>
    simp [coeffAt, LawfulCommRing.sub_eq_add_neg, LawfulCommRing.zero_add]
  | succ k' =>
    cases k' <;> simp [coeffAt, LawfulCommRing.sub_zero]

theorem evalCoeffs_map_gsConst_gsVarX {F : Type} [LawfulField F] [DecidableEq F] :
    ∀ (cs : List F), evalCoeffs (cs.map gsConst) gsVarX = GsUniPoly.ofCoeffs cs
  | [] => rfl
  | c :: cs => by
    show CommRingOps.add (gsConst c) (CommRingOps.mul gsVarX (evalCoeffs (cs.map gsConst) gsVarX)) =
      GsUniPoly.ofCoeffs (c :: cs)
    rw [evalCoeffs_map_gsConst_gsVarX cs]
    apply UPoly.ext
    apply eq_of_isTrimmed_coeffAt _ _
      (CommRingOps.add (gsConst c) (CommRingOps.mul gsVarX (GsUniPoly.ofCoeffs cs))).trimmed
      (trimPoly_idem (c :: cs))
    intro k
    change coeffAt (pAdd (trimPoly [c]) (pMul [CommRingOps.zero, CommRingOps.one] (trimPoly cs))) k =
      coeffAt (trimPoly (c :: cs)) k
    rw [coeffAt_pAdd, coeffAt_trimPoly, pMul, coeffAt_trimPoly, coeffAt_trimPoly,
        rawMul, coeffAt_addCoeffs, coeffAt_map_mul, LawfulCommRing.zero_mul,
        LawfulCommRing.zero_add]
    cases k with
    | zero =>
      rw [coeffAt_cons_zero, coeffAt_cons_zero, coeffAt_cons_zero, LawfulCommRing.add_zero]
    | succ k' =>
      rw [coeffAt_cons_succ, coeffAt_nil, LawfulCommRing.zero_add,
          coeffAt_cons_succ, coeffAt_cons_succ,
          rawMul, coeffAt_addCoeffs, coeffAt_map_mul, LawfulCommRing.one_mul, coeffAt_trimPoly]
      cases k' with
      | zero => rw [coeffAt_cons_zero, LawfulCommRing.add_zero]
      | succ k'' => rw [coeffAt_cons_succ, rawMul, coeffAt_nil, LawfulCommRing.add_zero]

theorem gsConst_add {F : Type} [LawfulField F] [DecidableEq F] (x y : F) :
    gsConst (CommRingOps.add x y) = CommRingOps.add (gsConst x) (gsConst y) := by
  apply UPoly.ext
  apply eq_of_isTrimmed_coeffAt _ _ (trimPoly_idem _) (CommRingOps.add (gsConst x) (gsConst y)).trimmed
  intro k
  change coeffAt (trimPoly [CommRingOps.add x y]) k =
    coeffAt (pAdd (trimPoly [x]) (trimPoly [y])) k
  rw [coeffAt_pAdd, coeffAt_trimPoly, coeffAt_trimPoly, coeffAt_trimPoly]
  cases k <;> simp [coeffAt, LawfulCommRing.add_zero]

theorem gsConst_mul {F : Type} [LawfulField F] [DecidableEq F] (x y : F) :
    gsConst (CommRingOps.mul x y) = CommRingOps.mul (gsConst x) (gsConst y) := by
  apply UPoly.ext
  show trimPoly [CommRingOps.mul x y] = (CommRingOps.mul (gsConst x) (gsConst y)).coeffs
  rw [gsConst_mul_val]
  unfold pScale
  rw [trimPoly_eq_iff_coeffAt]
  intro k
  change coeffAt [CommRingOps.mul x y] k = coeffAt (List.map (CommRingOps.mul x) (trimPoly [y])) k
  rw [coeffAt_map_mul, coeffAt_trimPoly]
  cases k <;> simp [coeffAt, LawfulCommRing.mul_zero]

theorem evalCoeffs_map_gsConst {F : Type} [LawfulField F] [DecidableEq F] (a : F) :
    ∀ (cs : List F), evalCoeffs (cs.map gsConst) (gsConst a) = gsConst (evalCoeffs cs a)
  | [] => gsConst_zero.symm
  | c :: cs => by
    show CommRingOps.add (gsConst c) (CommRingOps.mul (gsConst a) (evalCoeffs (cs.map gsConst) (gsConst a))) =
      gsConst (CommRingOps.add c (CommRingOps.mul a (evalCoeffs cs a)))
    rw [evalCoeffs_map_gsConst a cs, ← gsConst_mul, ← gsConst_add]

theorem quotLinear_map_gsConst {F : Type} [LawfulField F] [DecidableEq F] (a : F) :
    ∀ (cs : List F), quotLinear (cs.map gsConst) (gsConst a) = (quotLinear cs a).map gsConst
  | [] => rfl
  | [_] => rfl
  | _ :: c₁ :: tl => by
    show evalCoeffs ((c₁ :: tl).map gsConst) (gsConst a) ::
        quotLinear ((c₁ :: tl).map gsConst) (gsConst a) =
      gsConst (evalCoeffs (c₁ :: tl) a) :: (quotLinear (c₁ :: tl) a).map gsConst
    rw [evalCoeffs_map_gsConst, quotLinear_map_gsConst a (c₁ :: tl)]

theorem gsTaylor_map_gsConst {F : Type} [LawfulField F] [DecidableEq F] (a : F) :
    ∀ (n : Nat) (cs : List F),
      gsTaylor n (cs.map gsConst) (gsConst a) = (gsTaylor n cs a).map gsConst
  | 0, _ => rfl
  | n + 1, cs => by
    show evalCoeffs (cs.map gsConst) (gsConst a) ::
        gsTaylor n (quotLinear (cs.map gsConst) (gsConst a)) (gsConst a) =
      gsConst (evalCoeffs cs a) :: (gsTaylor n (quotLinear cs a) a).map gsConst
    rw [evalCoeffs_map_gsConst, quotLinear_map_gsConst, gsTaylor_map_gsConst a n]

theorem coeffAt_map_gsConst {F : Type} [LawfulField F] [DecidableEq F] :
    ∀ (cs : List F) (r : Nat), coeffAt (cs.map gsConst) r = gsConst (coeffAt cs r)
  | [], _ => gsConst_zero.symm
  | _ :: _, 0 => rfl
  | _ :: cs, r + 1 => coeffAt_map_gsConst cs r


end Qsag

namespace Qsag
open CommRingOps RoundPoly
theorem pMul_nil_left_eq {R : Type} [CommRingOps R] [DecidableEq R] (cs : List R) : pMul [] cs = [] := by rfl
theorem gsTaylor_zero {R : Type} [CommRingOps R] (cs : List R) (b : R) : gsTaylor 0 cs b = [] := by rfl
theorem gsTaylor_succ {R : Type} [CommRingOps R] (n : Nat) (cs : List R) (b : R) : gsTaylor (n+1) cs b = evalCoeffs cs b :: gsTaylor n (quotLinear cs b) b := by rfl
theorem gsConst_coeffs {F : Type} [LawfulField F] [DecidableEq F] (b : F) : (gsConst b).coeffs = trimPoly [b] := by rfl
end Qsag

namespace Qsag
open CommRingOps RoundPoly UPoly
/-! ## Polynomial lemmas -/

namespace UPoly

theorem coeffAt_tail {R : Type} [LawfulCommRing R] :
    ∀ (l : List R) (k : Nat), coeffAt l.tail k = coeffAt l (k + 1)
  | [], k => by rw [List.tail_nil, coeffAt_nil, coeffAt_nil]
  | _ :: _, k => by rw [List.tail_cons, coeffAt_cons_succ]

section Ring
variable {R : Type} [LawfulCommRing R] [DecidableEq R]

theorem eval_zero_eq (p : UPoly R) : p.eval zero = coeffAt p.coeffs 0 := by
  rw [eval_eq]
  generalize p.coeffs = l
  cases l with
  | nil => rfl
  | cons c cs =>
    show add c (mul zero (evalCoeffs cs zero)) = c
    rw [LawfulCommRing.zero_mul, LawfulCommRing.add_zero]

/-- Drop the constant term and divide by the variable. -/
def shiftDown (p : UPoly R) : UPoly R := ofList p.coeffs.tail

theorem coeffAt_shiftDown (p : UPoly R) (k : Nat) :
    coeffAt (shiftDown p).coeffs k = coeffAt p.coeffs (k + 1) := by
  show coeffAt (ofList p.coeffs.tail).coeffs k = _
  rw [coeffAt_ofList, coeffAt_tail]

/-- Split off the constant term: `a = a₀ + X · a'`. -/
theorem eq_C_add_X_mul (a : UPoly R) :
    a = add (C (coeffAt a.coeffs 0)) (mul X (shiftDown a)) :=
  ext_coeffAt fun k => by
    rw [coeffAt_add]
    cases k with
    | zero => rw [coeffAt_C_zero, coeffAt_X_mul_zero, LawfulCommRing.add_zero]
    | succ k =>
      rw [coeffAt_C_succ, coeffAt_X_mul_succ, coeffAt_shiftDown, LawfulCommRing.zero_add]

theorem hom_split {S : Type} [LawfulCommRing S] (ψ : RingHom (UPoly R) S) (p : UPoly R) :
    ψ.toFun p = add (ψ.toFun (C (coeffAt p.coeffs 0))) (mul (ψ.toFun X) (ψ.toFun (shiftDown p))) :=
  (congrArg ψ.toFun (eq_C_add_X_mul p)).trans (by rw [ψ.map_add, ψ.map_mul])

/-- Homomorphisms out of `R[X]` are determined on constants and the variable. -/
theorem hom_ext {S : Type} [LawfulCommRing S]
    (φ ψ : RingHom (UPoly R) S) (hC : ∀ c, φ.toFun (C c) = ψ.toFun (C c))
    (hX : φ.toFun X = ψ.toFun X) (p : UPoly R) : φ.toFun p = ψ.toFun p := by
  have key : ∀ l : List R, φ.toFun (ofList l) = ψ.toFun (ofList l) := by
    intro l
    induction l with
    | nil => exact φ.map_zero.trans ψ.map_zero.symm
    | cons c cs ih => rw [ofList_cons, φ.map_add, φ.map_mul, ψ.map_add, ψ.map_mul, hC, hX, ih]
  have := key p.coeffs
  rwa [ofList_coeffs] at this

theorem eval₂_congr {S : Type} [LawfulCommRing S] (φ ψ : RingHom R S)
    (h : ∀ c, φ.toFun c = ψ.toFun c) (s : S) (p : UPoly R) : eval₂ φ s p = eval₂ ψ s p := by
  show evalCoeffs (p.coeffs.map φ.toFun) s = evalCoeffs (p.coeffs.map ψ.toFun) s
  rw [List.map_congr_left (fun c _ => h c)]

theorem taylorShift_C (b c : R) : (taylorShift b).toFun (C c) = C c := eval₂_C _ _ _

theorem taylorShift_X (b : R) : (taylorShift b).toFun X = add (C b) X := eval₂_X _ _

/-- A polynomial is the evaluation of its constant-lifted coefficients at the variable. -/
theorem evalCoeffs_C_X (p : UPoly R) : evalCoeffs (p.coeffs.map (CHom (R := R)).toFun) X = p := by
  have h := mapHom_apply (RingHom.id R) p
  have e : (mapHom (RingHom.id R)).toFun p = evalCoeffs (p.coeffs.map (CHom (R := R)).toFun) X :=
    rfl
  rw [← e, h]
  show ofList (p.coeffs.map (fun a => a)) = p
  rw [List.map_id', ofList_coeffs]

theorem natDeg_C_eq (c : R) : (C c).natDeg = 0 :=
  Nat.le_zero.mp (natDeg_le_of_coeffAt _ 0 (fun k hk => by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact coeffAt_C_succ c j))

theorem wdeg_C_le (w : R → Nat) (s : Nat) (c : R) : (C c).wdeg w s ≤ w c := by
  apply wdeg_le
  intro k hk
  cases k with
  | zero => rw [coeffAt_C_zero]; exact Nat.le_refl _
  | succ k => exact absurd (coeffAt_C_succ c k) hk

theorem wdeg_X_le (w : R → Nat) (s : Nat) : (X : UPoly R).wdeg w s ≤ w one + s := by
  apply wdeg_le
  intro k hk
  have e : coeffAt (X : UPoly R).coeffs k = coeffAt [zero, one] k := coeffAt_ofList _ k
  rw [e] at hk ⊢
  cases k with
  | zero => exact absurd rfl hk
  | succ k =>
    cases k with
    | zero => show w one + s * 1 ≤ w one + s; rw [Nat.mul_one]; exact Nat.le_refl _
    | succ k => exact absurd rfl hk

/-- Coefficients after the scaling `X ↦ c·X`. -/
theorem coeffAt_scale (c : R) : ∀ (l : List R) (j : Nat),
    coeffAt (evalCoeffs (l.map (CHom (R := R)).toFun) (mul (C c) X)).coeffs j =
      mul (CRing.npow c j) (coeffAt l j)
  | [], j => by
    show coeffAt (zero : UPoly R).coeffs j = _
    rw [coeffs_zero, coeffAt_nil, LawfulCommRing.mul_zero]
  | a :: l, 0 => by
    show coeffAt (add (C a) (mul (mul (C c) X)
      (evalCoeffs (l.map (CHom (R := R)).toFun) (mul (C c) X)))).coeffs 0 = mul one a
    rw [coeffAt_add, coeffAt_C_zero, LawfulCommRing.mul_assoc, coeffAt_C_mul, coeffAt_X_mul_zero,
      LawfulCommRing.mul_zero, LawfulCommRing.add_zero, LawfulCommRing.one_mul]
  | a :: l, j + 1 => by
    show coeffAt (add (C a) (mul (mul (C c) X)
      (evalCoeffs (l.map (CHom (R := R)).toFun) (mul (C c) X)))).coeffs (j + 1) =
        mul (mul (CRing.npow c j) c) (coeffAt (a :: l) (j + 1))
    rw [coeffAt_add, coeffAt_C_succ, LawfulCommRing.zero_add, LawfulCommRing.mul_assoc,
      coeffAt_C_mul, coeffAt_X_mul_succ, coeffAt_scale c l j, coeffAt_cons_succ]
    generalize CRing.npow c j = p
    constructive_ring

end Ring
end UPoly

/-! ## Powers of a principal ideal -/

/-- `x ∈ u^k · S`. -/
def InPow {S : Type} [CommRingOps S] (u : S) (k : Nat) (x : S) : Prop :=
  ∃ q, x = mul (CRing.npow u k) q

namespace InPow
variable {S : Type} [LawfulCommRing S]

theorem base (u x : S) : InPow u 0 x := ⟨x, (LawfulCommRing.one_mul x).symm⟩

theorem zero_mem (u : S) (k : Nat) : InPow u k zero := ⟨zero, (LawfulCommRing.mul_zero _).symm⟩

theorem add_mem {u : S} {k : Nat} {x y : S} (hx : InPow u k x) (hy : InPow u k y) :
    InPow u k (add x y) := by
  obtain ⟨q, rfl⟩ := hx
  obtain ⟨q', rfl⟩ := hy
  exact ⟨add q q', (LawfulCommRing.left_distrib _ _ _).symm⟩

theorem mul_mem {u : S} {k : Nat} {x : S} (a : S) (hx : InPow u k x) : InPow u k (mul a x) := by
  obtain ⟨q, rfl⟩ := hx
  refine ⟨mul a q, ?_⟩
  generalize CRing.npow u k = p
  constructive_ring

theorem step {u : S} {k : Nat} {x : S} (w : S) (hx : InPow u k x) :
    InPow u (k + 1) (mul (mul u w) x) := by
  obtain ⟨q, rfl⟩ := hx
  refine ⟨mul w q, ?_⟩
  show _ = mul (mul (CRing.npow u k) u) (mul w q)
  generalize CRing.npow u k = p
  constructive_ring

theorem of_one {u x : S} (h : InPow u 1 x) : ∃ a, x = mul u a := by
  obtain ⟨q, hq⟩ := h
  exact ⟨q, hq.trans (by show mul (mul one u) q = mul u q; rw [LawfulCommRing.one_mul])⟩

theorem to_one (u a : S) : InPow u 1 (mul u a) :=
  ⟨a, by show mul u a = mul (mul one u) a; rw [LawfulCommRing.one_mul]⟩

theorem mono {u : S} {j k : Nat} {x : S} (hjk : j ≤ k) (hx : InPow u k x) : InPow u j x := by
  obtain ⟨q, rfl⟩ := hx
  obtain ⟨i, rfl⟩ : ∃ i, k = j + i := ⟨k - j, by omega⟩
  exact ⟨mul (CRing.npow u i) q, by rw [CRing.npow_add, LawfulCommRing.mul_assoc]⟩

/-- A polynomial with vanishing coefficients below `k`, evaluated at `u`, lies in `u^k`. -/
theorem evalCoeffs_low {R : Type} [LawfulCommRing R] (φ : RingHom R S) (u : S) :
    ∀ (k : Nat) (l : List R), (∀ r, r < k → coeffAt l r = zero) →
      InPow u k (evalCoeffs (l.map φ.toFun) u)
  | 0, _, _ => base u _
  | _ + 1, [], _ => zero_mem u _
  | k + 1, c :: cs, h => by
    have hc : c = zero := h 0 (Nat.succ_pos k)
    obtain ⟨q, hq⟩ := evalCoeffs_low φ u k cs (fun r hr => by
      have := h (r + 1) (Nat.succ_lt_succ hr)
      rwa [coeffAt_cons_succ] at this)
    refine ⟨q, ?_⟩
    show add (φ.toFun c) (mul u (evalCoeffs (cs.map φ.toFun) u)) =
      mul (mul (CRing.npow u k) u) q
    rw [hq, hc, φ.map_zero]
    generalize CRing.npow u k = p
    constructive_ring

/-- Evaluating a polynomial whose coefficients all lie in `u^k`. -/
theorem evalCoeffs_all (u y : S) (k : Nat) : ∀ l : List S, (∀ t, InPow u k (coeffAt l t)) →
    InPow u k (evalCoeffs l y)
  | [], _ => zero_mem u k
  | c :: cs, h =>
    add_mem (h 0) (mul_mem y (evalCoeffs_all u y k cs (fun t => by
      have := h (t + 1)
      rwa [coeffAt_cons_succ] at this)))

/-- If the coefficient of `Z^s` lies in `u^(m - s)`, evaluating at `Z = u·w` lands in `u^m`. -/
theorem evalCoeffs_graded (u w : S) : ∀ (l : List S) (m : Nat),
    (∀ s, InPow u (m - s) (coeffAt l s)) → InPow u m (evalCoeffs l (mul u w))
  | [], m, _ => zero_mem u m
  | _ :: _, 0, _ => base u _
  | c :: cs, m + 1, h => by
    have hc := h 0
    rw [Nat.sub_zero, coeffAt_cons_zero] at hc
    have ih := evalCoeffs_graded u w cs m (fun s => by
      have := h (s + 1)
      rwa [coeffAt_cons_succ, Nat.add_sub_add_right] at this)
    exact add_mem hc (step w ih)

end InPow

namespace UPoly
variable {R : Type} [LawfulCommRing R] [DecidableEq R]

/-- `X^k ∣ p` when the coefficients of `p` below `k` vanish. -/
theorem inPow_of_coeff_zero (p : UPoly R) (k : Nat)
    (h : ∀ j, j < k → coeffAt p.coeffs j = zero) : InPow X k p := by
  have := InPow.evalCoeffs_low (CHom (R := R)) X k p.coeffs h
  rwa [evalCoeffs_C_X] at this

/-- The coefficients of a multiple of `X^k` below `k` vanish. -/
theorem coeff_zero_of_inPow : ∀ (k : Nat) (p : UPoly R), InPow X k p →
    ∀ j, j < k → coeffAt p.coeffs j = zero
  | 0, _, _, j, hj => absurd hj (Nat.not_lt_zero j)
  | k + 1, p, ⟨q, hq⟩, j, hj => by
    have e : p = mul X (mul (CRing.npow X k) q) := by
      rw [hq]
      show mul (mul (CRing.npow X k) X) q = _
      generalize CRing.npow (X : UPoly R) k = P
      constructive_ring
    rw [e]
    cases j with
    | zero => exact coeffAt_X_mul_zero _
    | succ j =>
      rw [coeffAt_X_mul_succ]
      exact coeff_zero_of_inPow k _ ⟨q, rfl⟩ j (Nat.lt_of_succ_lt_succ hj)

end UPoly

/-! ## The fixed-point operator -/

namespace RingHom
variable {R S : Type} [LawfulCommRing R] [LawfulCommRing S]

/-- Synthetic division by `X - r` commutes with ring homomorphisms. -/
theorem map_quotLinear (φ : RingHom R S) (r : R) : ∀ l : List R,
    (quotLinear l r).map φ.toFun = quotLinear (l.map φ.toFun) (φ.toFun r)
  | [] => rfl
  | [_] => rfl
  | _ :: c₁ :: cs => by
    show φ.toFun (evalCoeffs (c₁ :: cs) r) :: (quotLinear (c₁ :: cs) r).map φ.toFun =
      evalCoeffs ((c₁ :: cs).map φ.toFun) (φ.toFun r) ::
        quotLinear ((c₁ :: cs).map φ.toFun) (φ.toFun r)
    rw [map_quotLinear φ r (c₁ :: cs), RingHom.map_evalCoeffs]

end RingHom

namespace UPoly

section Ring
variable {R S : Type} [LawfulCommRing R] [DecidableEq R] [LawfulCommRing S]

/-- The derivative at `z` by synthetic division: `(p(U) - p(z))/(U - z)` at `U = z`. -/
theorem evalCoeffs_quotLinear_self (g : List S) (z : S) :
    evalCoeffs (quotLinear g z) z = gsUniHasse g 1 z :=
  (gsUniHasse_zero_eq_evalCoeffs _ _).symm.trans (gsUniHasse_quotLinear g 0 z)

/-- The image of a Hasse derivative under `eval₂`. -/
theorem eval₂_hasse (χ : RingHom R S) (z : S) (k : Nat) (Q : UPoly R) :
    eval₂ χ z (hasse k Q) = gsUniHasse (Q.coeffs.map χ.toFun) k z := by
  show (eval₂Hom χ z).toFun (gsUniHasse (Q.coeffs.map C) k X) = _
  rw [RingHom.map_gsUniHasse, List.map_map]
  show gsUniHasse (Q.coeffs.map (fun c => eval₂ χ z (C c))) k (eval₂ χ z X) = _
  rw [eval₂_X]
  congr 1
  exact List.map_congr_left (fun c _ => eval₂_C χ z c)

/-- Shifting by `t` and then by `-t` is the identity. -/
theorem taylorShift_neg_cancel (t : R) (p : UPoly R) :
    (taylorShift (neg t)).toFun ((taylorShift t).toFun p) = p := by
  show (taylorShift (neg t)).toFun (eval₂ CHom (add (C t) X) p) = p
  rw [hom_eval₂, RingHom.map_add]
  have h1 : (taylorShift (neg t)).toFun (C t) = C t := eval₂_C _ _ _
  have h2 : (taylorShift (neg t)).toFun X = add (C (neg t)) X := eval₂_X _ _
  have h3 : add (C t) (add (C (neg t)) X) = (X : UPoly R) := by
    rw [← LawfulCommRing.add_assoc, ← CHom_apply t, ← CHom_apply (neg t), ← CHom.map_add,
      LawfulCommRing.add_right_neg, CHom.map_zero, LawfulCommRing.zero_add]
  rw [h1, h2, h3]
  have h4 : eval₂ ((taylorShift (neg t)).comp CHom) X p =
      (mapHom (RingHom.id R)).toFun p := by
    show evalCoeffs (p.coeffs.map _) X = evalCoeffs (p.coeffs.map _) X
    congr 1
    exact List.map_congr_left (fun c _ => eval₂_C _ _ c)
  rw [h4, mapHom_apply]
  show ofList (p.coeffs.map (fun a => a)) = p
  rw [List.map_id', ofList_coeffs]

end Ring

section Field
variable {K : Type} [LawfulField K] [DecidableEq K]

/-- In `K[W]`, a factor with nonzero constant term cancels modulo `W^n`. -/
theorem trunc_cancel : ∀ (n : Nat) (a b : UPoly K), coeffAt b.coeffs 0 ≠ zero →
    (∀ k, k < n → coeffAt (mul a b).coeffs k = zero) → ∀ k, k < n → coeffAt a.coeffs k = zero
  | 0, _, _, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, a, b, hb, h, k, hk => by
    have ha := eq_C_add_X_mul a
    have hmul : mul a b = add (mul (C (coeffAt a.coeffs 0)) b)
        (mul X (mul (shiftDown a) b)) := by
      have e : mul (add (C (coeffAt a.coeffs 0)) (mul X (shiftDown a))) b =
          add (mul (C (coeffAt a.coeffs 0)) b) (mul X (mul (shiftDown a) b)) := by
        constructive_ring
      rw [← ha] at e; exact e
    have h0 := h 0 (by omega)
    rw [hmul, coeffAt_add, coeffAt_C_mul, coeffAt_X_mul_zero, LawfulCommRing.add_zero] at h0
    have hc : coeffAt a.coeffs 0 = zero :=
      (LawfulField.mul_eq_zero h0).elim id (fun e => absurd e hb)
    have htail : ∀ j, j < n → coeffAt (mul (shiftDown a) b).coeffs j = zero := by
      intro j hj
      have := h (j + 1) (by omega)
      rw [hmul, coeffAt_add, coeffAt_C_mul, coeffAt_X_mul_succ, hc, LawfulCommRing.zero_mul,
        LawfulCommRing.zero_add] at this
      exact this
    have ih := trunc_cancel n (shiftDown a) b hb htail
    cases k with
    | zero => exact hc
    | succ k =>
      have := ih k (by omega)
      rwa [coeffAt_shiftDown] at this

/-- **Hensel uniqueness** (`[CWYZ26]` Lemma 3.11, uniqueness). Let `Q` have coefficients in
    a ring mapping to `K[W]` by `ψ`, so that `e ↦ eval₂ ψ e Q` is `E ↦ G(W, E)`. If `e₁` and
    `e₂` have the same constant term `z₀`, both solve `G(W, E) ≡ 0 (mod W^n)`, and
    `∂_U G(0, z₀) ≠ 0`, then `e₁ ≡ e₂ (mod W^n)`. -/
theorem hensel_unique {B : Type} [LawfulCommRing B] [DecidableEq B] (Q : UPoly B)
    (ψ : RingHom B (UPoly K)) (e₁ e₂ : UPoly K) (z₀ : K) (h₁ : e₁.eval zero = z₀)
    (h₂ : e₂.eval zero = z₀)
    (hS : eval₂ ((evalHom zero).comp ψ) z₀ (hasse 1 Q) ≠ zero) (n : Nat)
    (hr₁ : ∀ k, k < n → coeffAt (eval₂ ψ e₁ Q).coeffs k = zero)
    (hr₂ : ∀ k, k < n → coeffAt (eval₂ ψ e₂ Q).coeffs k = zero) :
    ∀ k, k < n → coeffAt e₁.coeffs k = coeffAt e₂.coeffs k := by
  have hfac := evalCoeffs_eq_mul_quotLinear_add (Q.coeffs.map ψ.toFun) e₂ e₁
  have hH : coeffAt (evalCoeffs (quotLinear (Q.coeffs.map ψ.toFun) e₂) e₁).coeffs 0 ≠ zero := by
    rw [← eval_zero_eq]
    show (evalHom (zero : K)).toFun (evalCoeffs (quotLinear (Q.coeffs.map ψ.toFun) e₂) e₁) ≠ zero
    rw [RingHom.map_evalCoeffs, RingHom.map_quotLinear, List.map_map, evalHom_apply,
      evalHom_apply, h₁, h₂, evalCoeffs_quotLinear_self]
    rw [eval₂_hasse] at hS
    exact hS
  have hdiff : ∀ k, k < n → coeffAt (mul (sub e₁ e₂)
      (evalCoeffs (quotLinear (Q.coeffs.map ψ.toFun) e₂) e₁)).coeffs k = zero := by
    intro k hk
    have e : mul (sub e₁ e₂) (evalCoeffs (quotLinear (Q.coeffs.map ψ.toFun) e₂) e₁) =
        sub (eval₂ ψ e₁ Q) (eval₂ ψ e₂ Q) := by
      show _ = sub (evalCoeffs (Q.coeffs.map ψ.toFun) e₁) (evalCoeffs (Q.coeffs.map ψ.toFun) e₂)
      rw [hfac]; constructive_ring
    rw [e, coeffAt_sub, hr₁ k hk, hr₂ k hk, LawfulCommRing.sub_self]
  intro k hk
  have := trunc_cancel n _ _ hH hdiff k hk
  rw [coeffAt_sub] at this
  exact LawfulCommRing.sub_eq_zero_iff.mp this

end Field
end UPoly

/-- A decidable predicate fails throughout `0..n`, or has a first point where it holds. -/
theorem first_or_none (p : Nat → Prop) [DecidablePred p] : ∀ n,
    (∀ k, k ≤ n → ¬ p k) ∨ ∃ μ, μ ≤ n ∧ p μ ∧ ∀ k, k < μ → ¬ p k
  | 0 =>
    if h : p 0 then .inr ⟨0, Nat.le_refl 0, h, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
    else .inl (fun k hk => by
      obtain rfl : k = 0 := Nat.le_zero.mp hk
      exact h)
  | n + 1 => by
    rcases first_or_none p n with hall | ⟨μ, hμ, hp, hlt⟩
    · if h : p (n + 1) then
        exact .inr ⟨n + 1, Nat.le_refl _, h, fun k hk => hall k (Nat.le_of_lt_succ hk)⟩
      else
        refine .inl (fun k hk => ?_)
        if hk' : k ≤ n then exact hall k hk'
        else
          obtain rfl : k = n + 1 := by omega
          exact h
    · exact .inr ⟨μ, Nat.le_succ_of_le hμ, hp, hlt⟩

namespace RingHom

theorem map_natCast {R S : Type} [LawfulCommRing R] [LawfulCommRing S] (φ : RingHom R S) :
    ∀ n : Nat, φ.toFun (CRing.natCast n) = CRing.natCast n
  | 0 => φ.map_zero
  | n + 1 => by
    rw [CRing.natCast_succ, CRing.natCast_succ, φ.map_add, map_natCast φ n, φ.map_one]

end RingHom

/-! ## Composition of Hasse derivatives -/

namespace UPoly

theorem gsUniHasse_eq_zero_of_length_le {S : Type} [LawfulCommRing S] (s : S) :
    ∀ (l : List S) (k : Nat), l.length ≤ k → gsUniHasse l k s = zero
  | [], _, _ => rfl
  | _ :: _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | _ :: cs, k + 1, h => by
    show add (gsUniHasse cs k s) (mul s (gsUniHasse cs (k + 1) s)) = zero
    rw [gsUniHasse_eq_zero_of_length_le s cs k (Nat.le_of_succ_le_succ h),
      gsUniHasse_eq_zero_of_length_le s cs (k + 1)
        (Nat.le_succ_of_le (Nat.le_of_succ_le_succ h)),
      LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

section
variable {R : Type} [LawfulCommRing R] [DecidableEq R]

/-- A coefficient list all of whose Hasse derivatives vanish at one point is zero. -/
theorem coeffs_zero_of_hasse_zero (l : List R) (s : R) (h : ∀ k, gsUniHasse l k s = zero) :
    ∀ j, coeffAt l j = zero := by
  have hT : (taylorShift s).toFun (ofList l) = zero := ext_coeffAt fun k => by
    show coeffAt (eval₂ CHom (add (C s) X) (ofList l)).coeffs k = _
    rw [eval₂_ofList, coeffs_zero, coeffAt_nil]
    exact (coeffAt_shift_list s l k).trans (h k)
  have h2 := congrArg (taylorShift (neg s)).toFun hT
  rw [taylorShift_neg_cancel, RingHom.map_zero] at h2
  intro j
  rw [← coeffAt_ofList, h2, coeffs_zero, coeffAt_nil]

/-- `p(X) ↦ p(X + T) ∈ R[X][T]`. -/
def shift2 : RingHom (UPoly R) (UPoly (UPoly R)) := eval₂Hom (CHom.comp CHom) (add (C X) X)

/-- The `k`-th Hasse derivative is the coefficient of `T^k` in `p(X + T)`. -/
theorem hasse_eq_coeff (k : Nat) (p : UPoly R) :
    hasse k p = coeffAt ((shift2 (R := R)).toFun p).coeffs k := by
  have h := coeffAt_shift_list (X : UPoly R) (p.coeffs.map C) k
  rw [List.map_map] at h
  exact h.symm

theorem hasse_add (k : Nat) (p q : UPoly R) :
    hasse k (add p q) = add (hasse k p) (hasse k q) := by
  rw [hasse_eq_coeff, hasse_eq_coeff, hasse_eq_coeff, RingHom.map_add, coeffAt_add]

theorem hasse_one_zero : hasse 1 (zero : UPoly R) = zero := by
  rw [hasse_eq_coeff, RingHom.map_zero, coeffs_zero, coeffAt_nil]

theorem hasse_one_C (c : R) : hasse 1 (C c) = zero := by
  rw [hasse_eq_coeff]
  show coeffAt (eval₂ (CHom.comp CHom) (add (C X) X) (C c)).coeffs 1 = zero
  rw [eval₂_C]
  exact coeffAt_C_succ (C c) 0

theorem _root_.Qsag.Poly3.hasse_zero {R : Type} [LawfulCommRing R] [DecidableEq R] (p : UPoly R) :
    hasse 0 p = p := by
  show gsUniHasse (p.coeffs.map C) 0 X = p
  rw [gsUniHasse_zero_eq_evalCoeffs]
  exact evalCoeffs_C_X p

/-- The product rule against the variable. -/
theorem hasse_one_X_mul (p : UPoly R) : hasse 1 (mul X p) = add p (mul X (hasse 1 p)) := by
  have hX : (shift2 (R := R)).toFun X = add (C X) X := eval₂_X _ _
  have h0 : coeffAt ((shift2 (R := R)).toFun p).coeffs 0 = p :=
    (hasse_eq_coeff 0 p).symm.trans (Poly3.hasse_zero p)
  rw [hasse_eq_coeff, hasse_eq_coeff 1 p, RingHom.map_mul, hX, LawfulCommRing.right_distrib,
    coeffAt_add, coeffAt_C_mul, coeffAt_X_mul_succ, h0]
  exact LawfulCommRing.add_comm _ _

theorem hasse_one_hasse_list : ∀ (l : List R) (k : Nat),
    hasse 1 (gsUniHasse (l.map C) k (X : UPoly R)) =
      mul (CRing.natCast (k + 1)) (gsUniHasse (l.map C) (k + 1) X)
  | [], k => by
    show hasse 1 (zero : UPoly R) = mul _ zero
    rw [hasse_one_zero, LawfulCommRing.mul_zero]
  | c :: cs, 0 => by
    show hasse 1 (add (C c) (mul X (gsUniHasse (cs.map C) 0 X))) =
      mul one (add (gsUniHasse (cs.map C) 0 X) (mul X (gsUniHasse (cs.map C) 1 X)))
    rw [hasse_add, hasse_one_C, hasse_one_X_mul, hasse_one_hasse_list cs 0]
    show add zero (add _ (mul X (mul one _))) = _
    constructive_ring
  | c :: cs, k + 1 => by
    show hasse 1 (add (gsUniHasse (cs.map C) k X) (mul X (gsUniHasse (cs.map C) (k + 1) X))) =
      mul (CRing.natCast (k + 1 + 1)) (add (gsUniHasse (cs.map C) (k + 1) X)
        (mul X (gsUniHasse (cs.map C) (k + 1 + 1) X)))
    rw [hasse_add, hasse_one_X_mul, hasse_one_hasse_list cs k, hasse_one_hasse_list cs (k + 1),
      CRing.natCast_succ (k + 1)]
    generalize (CRing.natCast (k + 1) : UPoly R) = n
    constructive_ring

/-- **Composition of Hasse derivatives**: `∂^{(1)} ∂^{(k)} = (k + 1)·∂^{(k+1)}`. -/
theorem hasse_one_hasse (k : Nat) (p : UPoly R) :
    hasse 1 (hasse k p) = mul (CRing.natCast (k + 1)) (hasse (k + 1) p) :=
  hasse_one_hasse_list p.coeffs k

theorem natCast_ne_zero (n : Nat) (h : (CRing.natCast n : R) ≠ zero) :
    (CRing.natCast n : UPoly R) ≠ zero := fun e => h (by
  have h1 : (CRing.natCast n : UPoly R) = C (CRing.natCast n) :=
    ((CHom (R := R)).map_natCast n).symm
  have h2 := congrArg (fun p : UPoly R => coeffAt p.coeffs 0) (h1.symm.trans e)
  simp only [coeffAt_C_zero, coeffs_zero, coeffAt_nil] at h2
  exact h2)

end
end UPoly

/-! ## Excluded lines and multiplicities -/

end Qsag

namespace Qsag
theorem qsum_mem_list_le (n : Nat) : ∀ (S : List (Fin n)),
    qsum n (fun i => if i ∈ S then 1 else 0) ≤ S.length
  | [] => by
    have h0 : qsum n (fun i => if i ∈ ([] : List (Fin n)) then 1 else 0) = qsum n (fun _ => 0) :=
      qsum_congr (fun _ => rfl)
    rw [h0, qsum_const]
    omega
  | a :: S => by
    have hPoint : ∀ i : Fin n,
        (if i ∈ a :: S then 1 else 0) ≤ (if i = a then 1 else 0) + (if i ∈ S then 1 else 0) := by
      intro i
      by_cases hia : i = a
      · subst hia; simp
      · by_cases his : i ∈ S <;> simp [hia, his]
    have hLe := qsum_le_qsum hPoint
    rw [qsum_add, qsum_eq_indicator] at hLe
    have ih := qsum_mem_list_le n S
    simp only [List.length_cons]
    omega

def natAbsDiff (a b : Nat) : Nat :=
  if a ≤ b then b - a else a - b

theorem natAbsDiff_triangle (a b c : Nat) :
    natAbsDiff a c ≤ natAbsDiff a b + natAbsDiff b c := by
  unfold natAbsDiff
  split <;> split <;> split <;> omega

private theorem natAbsDiff_step (p0 q0 sp sq sb : Nat)
    (hp0 : p0 ≤ 1) (hq0 : q0 ≤ 1) (hih : natAbsDiff sp sq ≤ sb) :
    natAbsDiff (p0 + sp) (q0 + sq) ≤ 1 + sb := by
  unfold natAbsDiff at hih ⊢
  split at hih <;> split <;> omega

private theorem natAbsDiff_same_add (v sp sq : Nat) :
    natAbsDiff (v + sp) (v + sq) = natAbsDiff sp sq := by
  unfold natAbsDiff
  split <;> split <;> omega

theorem qsum_indicator_diff_le {n : Nat} (p q : Fin n → Bool) (bad : Fin n → Bool)
    (hAgree : ∀ i : Fin n, bad i = false → p i = q i) :
    natAbsDiff (qsum n (fun i => if p i then 1 else 0))
               (qsum n (fun i => if q i then 1 else 0)) ≤
      qsum n (fun i => if bad i then 1 else 0) := by
  induction n with
  | zero => simp [qsum, natAbsDiff]
  | succ n ih =>
    simp only [qsum_succ]
    let p' : Fin n → Bool := fun i => p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
    let q' : Fin n → Bool := fun i => q ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
    let b' : Fin n → Bool := fun i => bad ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
    have ih' := ih p' q' b' (fun i hi => hAgree ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ hi)
    cases hb0 : bad ⟨0, Nat.zero_lt_succ n⟩
    · have hpq0 := hAgree ⟨0, Nat.zero_lt_succ n⟩ hb0
      rw [hpq0]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, natAbsDiff_same_add]
      exact ih'
    · simp only [↓reduceIte]
      exact natAbsDiff_step _ _ _ _ _
        (by split <;> omega) (by split <;> omega) ih'


end Qsag

namespace Qsag
 theorem scaleVec_eq {F : Type} [CommRingOps F] (c : F) (v : List F) :
    scaleVec c v = v.map (CommRingOps.mul c) := by unfold scaleVec; rfl
namespace Poly3
variable {F : Type} [LawfulCommRing F] [DecidableEq F]
theorem hasseZ_eq (s : Nat) (Q : Poly3 F) : hasseZ s Q = UPoly.hasse s Q := by unfold hasseZ; rfl
theorem evalAffineLine_eq (Q : Poly3 F) (α β : F) (P : UPoly F) :
    evalAffineLine Q α β P = (affineLineHom α β P).toFun Q := by unfold evalAffineLine; rfl
theorem evalAffineLine_eq_eval₂ (Q : Poly3 F) (α β : F) (P : UPoly F) :
    evalAffineLine Q α β P = UPoly.eval₂ (UPoly.evalHom (line α β)) P Q := by
  unfold evalAffineLine affineLineHom; rfl
theorem evalAffineLine_one (α β : F) (P : UPoly F) :
    evalAffineLine CommRingOps.one α β P = CommRingOps.one := by
  rw [evalAffineLine_eq]; exact (affineLineHom α β P).map_one
end Poly3
end Qsag

section
namespace Qsag

set_option autoImplicit false

open CommRingOps RoundPoly

namespace Hensel
open UPoly

section Generic
variable {Λ : Type} [LawfulCommRing Λ] [DecidableEq Λ]

/-- The separant `[W⁰U¹] G`. -/
def sep (G : UPoly (UPoly Λ)) : Λ := coeffAt (coeffAt G.coeffs 1).coeffs 0

/-- The residue `[W⁰U⁰] G`. -/
def res (G : UPoly (UPoly Λ)) : Λ := coeffAt (coeffAt G.coeffs 0).coeffs 0

/-- `W ↦ S²·W`. -/
def evW (G : UPoly (UPoly Λ)) : RingHom (UPoly Λ) (UPoly Λ) :=
  eval₂Hom CHom (mul (C (mul (sep G) (sep G))) X)

/-- `W ↦ S²·W`, `U ↦ S·N`. -/
def evG (G : UPoly (UPoly Λ)) (N : UPoly Λ) : RingHom (UPoly (UPoly Λ)) (UPoly Λ) :=
  eval₂Hom (evW G) (mul (C (sep G)) N)

@[simp] theorem evW_apply (G : UPoly (UPoly Λ)) (q : UPoly Λ) :
    (evW G).toFun q = eval₂ CHom (mul (C (mul (sep G) (sep G))) X) q := by
  unfold evW; rw [eval₂Hom_apply]
@[simp] theorem evG_apply (G : UPoly (UPoly Λ)) (N : UPoly Λ) (p : UPoly (UPoly Λ)) :
    (evG G N).toFun p = eval₂ (evW G) (mul (C (sep G)) N) p := by
  unfold evG; rw [eval₂Hom_apply]

def e12 (G : UPoly (UPoly Λ)) : UPoly Λ := (evW G).toFun (shiftDown (coeffAt G.coeffs 1))
def e2 (G : UPoly (UPoly Λ)) : UPoly Λ := (evW G).toFun (shiftDown (coeffAt G.coeffs 0))
def e11 (G : UPoly (UPoly Λ)) (N : UPoly Λ) : UPoly Λ :=
  (evG G N).toFun (shiftDown (shiftDown G))

/-- `Φ(N) = -(S·N·W·G₁₂(S²W) + N²·G₁₁(S²W, S·N) + W·G₂(S²W))`. -/
def phi (G : UPoly (UPoly Λ)) (N : UPoly Λ) : UPoly Λ :=
  neg (add (add (mul (mul (mul (C (sep G)) N) X) (e12 G)) (mul (mul N N) (e11 G N)))
    (mul X (e2 G)))

/-- `G(S²W, S·N) = [W⁰U⁰]G + S²·(N - Φ(N))`, for every `N`. -/
theorem evG_eq (G : UPoly (UPoly Λ)) (N : UPoly Λ) :
    (evG G N).toFun G = add (C (res G)) (mul (C (mul (sep G) (sep G))) (sub N (phi G N))) := by
  have hC : ∀ q, (evG G N).toFun (C q) = (evW G).toFun q := fun q => by rw [evG_apply, eval₂_C]
  have hX : (evG G N).toFun X = mul (C (sep G)) N := by rw [evG_apply, eval₂_X]
  have hWC : ∀ a, (evW G).toFun (C a) = C a := fun a => by rw [evW_apply, eval₂_C, CHom_apply]
  have hWX : (evW G).toFun X = mul (C (mul (sep G) (sep G))) X := by rw [evW_apply, eval₂_X]
  have h1 : coeffAt (shiftDown G).coeffs 0 = coeffAt G.coeffs 1 := coeffAt_shiftDown G 0
  have hSS : C (mul (sep G) (sep G)) = mul (C (sep G)) (C (sep G)) := C_mul_eq _ _
  rw [hom_split (evG G N) G, hom_split (evG G N) (shiftDown G), hC, hC, hX, h1,
    hom_split (evW G) (coeffAt G.coeffs 0), hom_split (evW G) (coeffAt G.coeffs 1), hWC, hWC, hWX]
  show add (add (C (res G)) (mul _ (e2 G))) (mul _ (add (add (C (sep G)) (mul _ (e12 G)))
    (mul _ (e11 G N)))) = add (C (res G)) (mul _ (sub N (neg (add (add
      (mul (mul (mul (C (sep G)) N) X) (e12 G)) (mul (mul N N) (e11 G N))) (mul X (e2 G))))))
  rw [hSS]
  constructive_ring

/-- `Φ` preserves the ideal `(W)`. -/
theorem phi_mem (G : UPoly (UPoly Λ)) (N : UPoly Λ) (hN : InPow X 1 N) :
    InPow X 1 (phi G N) := by
  obtain ⟨a, rfl⟩ := InPow.of_one hN
  refine ⟨neg (add (add (mul (mul (mul (C (sep G)) a) X) (e12 G))
    (mul (mul a (mul X a)) (e11 G (mul X a)))) (e2 G)), ?_⟩
  show neg (add (add (mul (mul (mul (C (sep G)) (mul X a)) X) (e12 G))
    (mul (mul (mul X a) (mul X a)) (e11 G (mul X a)))) (mul X (e2 G))) = mul (mul one X) _
  constructive_ring

/-- **`Φ` is a contraction**: `N ≡ N' (mod W^k)` gives `Φ(N) ≡ Φ(N') (mod W^(k+1))` for
    `N, N'` without constant term. -/
