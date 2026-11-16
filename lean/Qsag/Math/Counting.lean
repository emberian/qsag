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
/-- Module-local constructive finite sum `∑_{i : Fin n} f i`, keeping full definitional reduction
    available inside proofs and decidable evaluations without exposing internal `UcGames` bodies. -/
@[expose] def qsum : (n : Nat) → (Fin n → Nat) → Nat
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
theorem flatMap_const_length {α β : Type} (c : Nat) (f : α → List β) :
    ∀ (xs : List α), (∀ x ∈ xs, (f x).length = c) → (xs.flatMap f).length = xs.length * c
  | [], _ => by simp
  | x :: xs, h => by
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [h x (.head _), flatMap_const_length c f xs (fun y hy => h y (.tail _ hy)),
        Nat.add_mul, Nat.one_mul, Nat.add_comm]
end Qsag

namespace Qsag
/-- Exact falling factorial `a (a - 1) ⋯ (a - k + 1)`: `affineFallingFactorial A q / affineFallingFactorial n q`
    is the exact probability that `q` DISTINCT uniformly sampled fibers (the `BTreeSet` sampling of
    `pcs.rs::sample_stage_queries`) all land inside a fixed set of `A` out of `n` fibers. -/
@[expose] def affineFallingFactorial (a : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => (a - k) * affineFallingFactorial a k

theorem affineFallingFactorial_pos (a : Nat) : ∀ k : Nat, k ≤ a → 0 < affineFallingFactorial a k
  | 0, _ => Nat.zero_lt_one
  | k + 1, h => by
    show 0 < (a - k) * affineFallingFactorial a k
    exact Nat.mul_pos (by omega) (affineFallingFactorial_pos a k (by omega))

/-- Sampling without replacement never hits a fixed set more often than sampling with replacement:
    `affineFallingFactorial a k * n^k ≤ a^k * affineFallingFactorial n k` whenever `a ≤ n`. -/
theorem affineFallingFactorial_mul_pow_le (a n : Nat) (han : a ≤ n) :
    ∀ k : Nat, affineFallingFactorial a k * n ^ k ≤ a ^ k * affineFallingFactorial n k
  | 0 => Nat.le_refl _
  | k + 1 => by
    show (a - k) * affineFallingFactorial a k * n ^ (k + 1) ≤ a ^ (k + 1) * ((n - k) * affineFallingFactorial n k)
    have ih := affineFallingFactorial_mul_pow_le a n han k
    have hCross : (a - k) * n ≤ a * (n - k) := by
      if hk : k ≤ a then
        have e1 : (a - k) * n = a * n - k * n := Nat.sub_mul a k n
        have e2 : a * (n - k) = a * n - a * k := Nat.mul_sub a n k
        have h3 : a * k ≤ k * n := by
          rw [Nat.mul_comm a k]; exact Nat.mul_le_mul_left k han
        rw [e1, e2]
        exact Nat.sub_le_sub_left h3 (a * n)
      else
        have h0 : a - k = 0 := by omega
        rw [h0, Nat.zero_mul]
        exact Nat.zero_le _
    have hL : (a - k) * affineFallingFactorial a k * n ^ (k + 1) =
        ((a - k) * n) * (affineFallingFactorial a k * n ^ k) := by
      rw [Nat.pow_succ, Nat.mul_comm (n ^ k) n, Nat.mul_mul_mul_comm]
    have hR : a ^ (k + 1) * ((n - k) * affineFallingFactorial n k) =
        (a * (n - k)) * (a ^ k * affineFallingFactorial n k) := by
      rw [Nat.pow_succ, Nat.mul_comm (a ^ k) a, Nat.mul_mul_mul_comm]
    rw [hL, hR]
    exact Nat.mul_le_mul hCross ih

theorem affineFallingFactorial_mono {a b : Nat} (hab : a ≤ b) :
    ∀ k : Nat, affineFallingFactorial a k ≤ affineFallingFactorial b k
  | 0 => Nat.le_refl 1
  | k + 1 => Nat.mul_le_mul (Nat.sub_le_sub_right hab k) (affineFallingFactorial_mono hab k)

private theorem mul_affineFallingFactorial_pred (a : Nat) :
    ∀ k : Nat, a * affineFallingFactorial (a - 1) k = affineFallingFactorial a (k + 1)
  | 0 => by simp [affineFallingFactorial]
  | k + 1 => by
    have ih := mul_affineFallingFactorial_pred a k
    show a * ((a - 1 - k) * affineFallingFactorial (a - 1) k) =
      (a - (k + 1)) * affineFallingFactorial a (k + 1)
    have hsub : a - 1 - k = a - (k + 1) := by omega
    rw [hsub, ← Nat.mul_assoc, Nat.mul_comm a (a - (k + 1)), Nat.mul_assoc, ih]

private theorem mem_of_mem_eraseFirst {α : Type} [DecidableEq α] {x z : α} :
    ∀ {M : List α}, z ∈ eraseFirst x M → z ∈ M
  | [], h => by cases h
  | y :: ys, h => by
    unfold eraseFirst at h
    if hxy : x = y then
      simp only [hxy, ↓reduceIte] at h
      exact .tail _ h
    else
      simp only [hxy, ↓reduceIte] at h
      cases h with
      | head => exact .head _
      | tail _ hm => exact .tail _ (mem_of_mem_eraseFirst hm)

private theorem eraseFirst_nodup {α : Type} [DecidableEq α] (x : α) :
    ∀ {M : List α}, M.Nodup → (eraseFirst x M).Nodup
  | [], _ => .nil
  | y :: ys, .cons hnot hnd => by
    unfold eraseFirst
    if hxy : x = y then
      simp only [hxy, ↓reduceIte]
      exact hnd
    else
      simp only [hxy, ↓reduceIte]
      refine .cons ?_ (eraseFirst_nodup x hnd)
      intro z hz heq
      subst heq
      exact hnot y (mem_of_mem_eraseFirst hz) rfl

/-- Ordered `k`-tuples of pairwise-distinct elements drawn without replacement from `U`. -/
def affineDistinctTuples {α : Type} [DecidableEq α] : Nat → List α → List (List α)
  | 0, _ => [[]]
  | k + 1, U => U.flatMap (fun x => (affineDistinctTuples k (eraseFirst x U)).map (x :: ·))


/-- For duplicate-free `U`, `affineDistinctTuples k U` has exact size `affineFallingFactorial U.length k`. -/
theorem affineDistinctTuples_length {α : Type} [DecidableEq α] :
    ∀ (k : Nat) {U : List α}, U.Nodup →
      (affineDistinctTuples k U).length = affineFallingFactorial U.length k
  | 0, _, _ => rfl
  | k + 1, U, hU => by
    unfold affineDistinctTuples
    rw [flatMap_const_length (affineFallingFactorial (U.length - 1) k)]
    · exact mul_affineFallingFactorial_pred U.length k
    · intro x hx
      rw [List.length_map, affineDistinctTuples_length k (eraseFirst_nodup x hU)]
      have hlen := eraseFirst_length_of_mem hx
      have heq : (eraseFirst x U).length = U.length - 1 := by omega
      rw [heq]

theorem mem_affineDistinctTuples_props {α : Type} [DecidableEq α] :
    ∀ (k : Nat) {U : List α} {t : List α},
      U.Nodup → t ∈ affineDistinctTuples k U →
      t.length = k ∧ t.Nodup ∧ ∀ x ∈ t, x ∈ U
  | 0, _, t, _, ht => by
    simp only [affineDistinctTuples, List.mem_singleton] at ht
    subst ht
    exact ⟨rfl, .nil, fun _ h => by cases h⟩
  | k + 1, U, t, hU, ht => by
    unfold affineDistinctTuples at ht
    rw [List.mem_flatMap] at ht
    rcases ht with ⟨x, hxU, htMap⟩
    rw [List.mem_map] at htMap
    rcases htMap with ⟨ts, htsMem, rfl⟩
    rcases mem_affineDistinctTuples_props k (eraseFirst_nodup x hU) htsMem with ⟨hlen, hnd, hsub⟩
    refine ⟨congrArg Nat.succ hlen, .cons ?_ hnd, ?_⟩
    · intro y hy heq
      subst heq
      have hyEr := hsub x hy
      have hnotEr : ∀ {M : List α}, M.Nodup → x ∉ eraseFirst x M := by
        intro M hM
        induction M with
        | nil => simp [eraseFirst]
        | cons z zs ih =>
          rcases hM with _ | ⟨hnotZ, hndZ⟩
          unfold eraseFirst
          if hxz : x = z then
            simp only [hxz, ↓reduceIte]
            subst hxz
            exact fun hm => hnotZ x hm rfl
          else
            simp only [hxz, ↓reduceIte, List.mem_cons]
            rintro (heq | hm)
            · exact False.elim heq
            · exact ih hndZ hm
      exact hnotEr hU hyEr
    · intro y hy
      cases hy with
      | head => exact hxU
      | tail _ hm => exact mem_of_mem_eraseFirst (hsub y hm)

theorem mem_affineDistinctTuples_of_subset {α : Type} [DecidableEq α] :
    ∀ (k : Nat) {U t : List α},
      t.length = k → t.Nodup → (∀ x ∈ t, x ∈ U) → t ∈ affineDistinctTuples k U
  | 0, _, t, hlen, _, _ => by
    have ht : t = [] := List.eq_nil_of_length_eq_zero hlen
    subst ht
    exact .head _
  | k + 1, U, [], hlen, _, _ => by cases hlen
  | k + 1, U, x :: ts, hlen, .cons hnot hnd, hsub => by
    unfold affineDistinctTuples
    rw [List.mem_flatMap]
    refine ⟨x, hsub x (.head _), List.mem_map.mpr ⟨ts, ?_, rfl⟩⟩
    refine mem_affineDistinctTuples_of_subset k (Nat.succ.inj hlen) hnd ?_
    intro y hy
    exact mem_eraseFirst_of_ne (fun heq => hnot y hy heq.symm) (hsub y (.tail _ hy))

theorem affineDistinctTuples_nodup {α : Type} [DecidableEq α] :
    ∀ (k : Nat) {U : List α}, U.Nodup → (affineDistinctTuples k U).Nodup
  | 0, _, _ => .cons (by simp) .nil
  | k + 1, U, hU => by
    unfold affineDistinctTuples
    apply List.pairwise_flatMap.mpr
    refine ⟨?_, ?_⟩
    · intro x _
      apply List.pairwise_map.mpr
      exact (affineDistinctTuples_nodup k (eraseFirst_nodup x hU)).imp
        (fun hne heq => hne (List.cons.inj heq).2)
    · refine hU.imp ?_
      intro x y hxy t₁ ht₁ t₂ ht₂ heq
      rcases List.mem_map.mp ht₁ with ⟨_, _, rfl⟩
      rcases List.mem_map.mp ht₂ with ⟨_, _, rfl⟩
      exact hxy (List.cons.inj heq).1

/-- **Constructive Hypergeometric Distinct-Fiber Sampling Bound (`affineDistinctTuples_all_good_le`)**:
    For ANY duplicate-free fiber domain `U` and ANY predicate `good : α → Bool` satisfied by at most
    `B` elements of `U`, at most `affineFallingFactorial B k` out of all
    `affineFallingFactorial U.length k` distinct `k`-tuples in `affineDistinctTuples k U` satisfy
    `t.all good = true`! -/
theorem affineDistinctTuples_all_good_le {α : Type} [DecidableEq α]
    (k B : Nat) (U : List α) (good : α → Bool)
    (hU : U.Nodup) (hGoodLe : (U.filter good).length ≤ B) :
    ((affineDistinctTuples k U).filter (fun t => t.all good)).length ≤
      affineFallingFactorial B k := by
  let G := U.filter good
  have hGNd : G.Nodup := List.Pairwise.filter _ hU
  have hFiltNd : ((affineDistinctTuples k U).filter (fun t => t.all good)).Nodup :=
    List.Pairwise.filter _ (affineDistinctTuples_nodup k hU)
  have hSub : ∀ t ∈ (affineDistinctTuples k U).filter (fun t => t.all good),
      t ∈ affineDistinctTuples k G := by
    intro t ht
    rcases List.mem_filter.mp ht with ⟨htMem, htGood⟩
    rcases mem_affineDistinctTuples_props k hU htMem with ⟨hlen, hnd, hsubU⟩
    exact mem_affineDistinctTuples_of_subset k hlen hnd
      (fun x hx => List.mem_filter.mpr ⟨hsubU x hx, List.all_eq_true.mp htGood x hx⟩)
  calc ((affineDistinctTuples k U).filter (fun t => t.all good)).length
      ≤ (affineDistinctTuples k G).length := nodup_length_le_of_subset hFiltNd hSub
    _ = affineFallingFactorial G.length k := affineDistinctTuples_length k hGNd
    _ ≤ affineFallingFactorial B k := affineFallingFactorial_mono hGoodLe k


end Qsag

namespace Qsag
structure SimpleEquiv (α β : Type) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a : α, invFun (toFun a) = a
  right_inv : ∀ b : β, toFun (invFun b) = b


end Qsag

namespace Qsag
abbrev SimpleEquiv.refl (α : Type) : SimpleEquiv α α where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl


end Qsag

namespace Qsag
theorem qsum_perm_invariant {n : Nat} (π πinv : Fin n → Fin n)
    (hLeft : ∀ i, πinv (π i) = i) (hRight : ∀ j, π (πinv j) = j) (g : Fin n → Nat) :
    qsum n (fun i => g (π i)) = qsum n g := qsum_bijection π πinv hLeft hRight g

/-- **Uniform-Distribution Bijection Invariance (`qsum_bijection_invariant`)**: over a sample
    space `Ω` enumerated by `enum`, pre-composing any weight `g` with a bijection `e` of `Ω`
    leaves the total weight unchanged. -/
theorem qsum_bijection_invariant {Ω : Type} {C : Nat}
    (enum : SimpleEquiv (Fin C) Ω) (e : SimpleEquiv Ω Ω) (g : Ω → Nat) :
    qsum C (fun i => g (e.toFun (enum.toFun i))) = qsum C (fun i => g (enum.toFun i)) := by
  have h := qsum_perm_invariant
    (fun i => enum.invFun (e.toFun (enum.toFun i)))
    (fun j => enum.invFun (e.invFun (enum.toFun j)))
    (fun i => by simp only [enum.right_inv, e.left_inv, enum.left_inv])
    (fun j => by simp only [enum.right_inv, e.right_inv, enum.left_inv])
    (fun i => g (enum.toFun i))
  simp only [enum.right_inv] at h
  exact h

theorem qsum_indicator_or_le {n : Nat} (p q : Fin n → Bool) :
    qsum n (fun i => if (p i || q i) then 1 else 0) ≤
      qsum n (fun i => if p i then 1 else 0) + qsum n (fun i => if q i then 1 else 0) := by
  have h : ∀ i : Fin n, (if (p i || q i) then 1 else 0) ≤
      (if p i then 1 else 0) + (if q i then 1 else 0) := by
    intro i
    cases p i <;> cases q i <;> decide
  exact Nat.le_trans (qsum_le_qsum h)
    (Nat.le_of_eq (qsum_add (fun i => if p i then 1 else 0) (fun i => if q i then 1 else 0)))

/-- At most one index satisfies a predicate whose satisfying indices all coincide. -/
theorem qsum_indicator_le_one_of_unique : ∀ (n : Nat) (p : Fin n → Bool),
    (∀ i j : Fin n, p i = true → p j = true → i = j) →
    qsum n (fun i => if p i then 1 else 0) ≤ 1
  | 0, _, _ => Nat.zero_le 1
  | n + 1, p, hUniq => by
    simp only [qsum]
    cases hp0 : p ⟨0, Nat.zero_lt_succ n⟩ with
    | true =>
      have hRest : qsum n (fun i => if p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ then 1 else 0) =
          qsum n (fun _ => 0) := by
        apply qsum_congr
        intro i
        have hpi : p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ = false := by
          cases hpi : p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ with
          | false => rfl
          | true =>
            exact absurd (congrArg Fin.val (hUniq _ _ hp0 hpi)) (Nat.succ_ne_zero i.1).symm
        simp only [hpi, Bool.false_eq_true, ↓reduceIte]
      rw [hRest, qsum_const]
      simp
    | false =>
      have ih := qsum_indicator_le_one_of_unique n (fun i => p ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
        (fun i j hi hj => Fin.ext (Nat.succ.inj (congrArg Fin.val (hUniq _ _ hi hj))))
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      exact ih

theorem natAbsDiff_add_le (a b c d : Nat) :
    natAbsDiff (a + b) (c + d) ≤ natAbsDiff a c + natAbsDiff b d := by
  unfold natAbsDiff
  split <;> split <;> split <;> omega

theorem natAbsDiff_qsum_le {n : Nat} (f g : Fin n → Nat) :
    natAbsDiff (qsum n f) (qsum n g) ≤ qsum n (fun i => natAbsDiff (f i) (g i)) := by
  induction n with
  | zero => exact Nat.le_of_eq rfl
  | succ n ih =>
    simp only [qsum]
    exact Nat.le_trans (natAbsDiff_add_le _ _ _ _) (Nat.add_le_add_left (ih _ _) _)

theorem natAbsDiff_mul_left (c a b : Nat) : natAbsDiff (c * a) (c * b) = c * natAbsDiff a b := by
  unfold natAbsDiff
  by_cases h : a ≤ b
  · rw [ite_eq_left h, ite_eq_left (Nat.mul_le_mul_left c h), Nat.mul_sub]
  · have hba : b ≤ a := Nat.le_of_lt (Nat.gt_of_not_le h)
    have h' : c * b ≤ c * a := Nat.mul_le_mul_left c hba
    rw [ite_eq_right h, Nat.mul_sub]
    split
    · omega
    · rfl


end Qsag

namespace Qsag
theorem natAbsDiff_eq (a b : Nat) : natAbsDiff a b = if a ≤ b then b - a else a - b := by
  unfold natAbsDiff; rfl
end Qsag

namespace Qsag
namespace JohnsonBound
theorem johnsonBound_eq (n B t : Nat) : johnsonBound n B t = (n * (B - t)) / (B * B - n * t) := by unfold johnsonBound; rfl
theorem ptDeg_eq {α β : Type} (mem : β → α → Bool) (fam : List β) (z : α) : ptDeg mem fam z = (fam.filter (fun i => mem i z)).length := by unfold ptDeg; rfl
end JohnsonBound
end Qsag

namespace Qsag
 theorem prodPool_eq {α : Type} (S : List α) : prodPool S = S.flatMap (fun x => S.map (fun y => (x,y))) := by rfl

/-! ### Exports for lane agg-budget -/

/-- A filter whose predicate is false on every element is empty. -/
theorem filter_eq_nil_of_all_false {α : Type} (p : α → Bool) :
    ∀ (xs : List α), (∀ a ∈ xs, p a = false) → xs.filter p = []
  | [], _ => rfl
  | a :: rest, h => by
    simp only [List.filter_cons, h a (.head rest), Bool.false_eq_true, ↓reduceIte]
    exact filter_eq_nil_of_all_false p rest (fun x hx => h x (.tail a hx))

/-- Union bound over a list of events: if each `pred a` selects at most `B` elements of `xs`,
    the elements selected by some `a ∈ items` number at most `items.length * B`. -/
theorem filter_any_length_le_mul {α β : Type} (items : List α) (pred : α → β → Bool)
    (xs : List β) (B : Nat)
    (hEach : ∀ a ∈ items, (xs.filter (pred a)).length ≤ B) :
    (xs.filter (fun x => items.any (fun a => pred a x))).length ≤ items.length * B := by
  induction items with
  | nil =>
    have hNil : xs.filter (fun _ => false) = [] :=
      filter_eq_nil_of_all_false (fun _ => false) xs (fun _ _ => rfl)
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
-- (end exports for lane agg-budget)

end Qsag

/-! ### Exports for lane math -/
public section

#verify_constructive Qsag.JohnsonBound.nat_cauchy_schwarz
#verify_constructive Qsag.JohnsonBound.count_partition_le
#verify_constructive Qsag.JohnsonBound.johnson_set_system_mul_le
#verify_constructive Qsag.JohnsonBound.johnson_set_system_card_le

namespace Qsag

theorem JohnsonBound.elemBool_nil {α : Type} [DecidableEq α] (x : α) :
    JohnsonBound.elemBool x [] = false := by rfl

theorem JohnsonBound.elemBool_cons {α : Type} [DecidableEq α] (x y : α) (ys : List α) :
    JohnsonBound.elemBool x (y :: ys) = (decide (x = y) || JohnsonBound.elemBool x ys) := by rfl

end Qsag

end

/-! ### Exports for lane sig -/
public section
namespace Qsag

theorem natAbsDiff_def (a b : Nat) : natAbsDiff a b = if a ≤ b then b - a else a - b := by rfl

end Qsag
end
