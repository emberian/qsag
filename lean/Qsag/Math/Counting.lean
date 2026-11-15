module
public import Qsag.Tactic.Prelude

/-!
# Qsag.Math.Counting

Constructive list and finite-sum combinatorics used by the algebra and coding layers; nothing here
mentions a ring.

* product pools `prodPool`, `eraseFirst`, `Nodup`/`filter` length bounds;
* the Johnson set-system bound (`JohnsonBound`): double counting of point degrees and pairwise
  intersections of a family of sets;
* finite sums `qsum n f = ∑_{i : Fin n} f i`: congruence, monotonicity, indicator sums, reindexing
  along bijections (`SimpleEquiv`), and absolute-difference bounds (`natAbsDiff`);
* falling factorials and duplicate-free tuples (`affineFallingFactorial`, `affineDistinctTuples`).
-/

public section
-- Avoid the choice-based LawfulBEq derived from the Fin order package.
attribute [-instance] Fin.instLinearOrderPackage
namespace Qsag
set_option autoImplicit false
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

