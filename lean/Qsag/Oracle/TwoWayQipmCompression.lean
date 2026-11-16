module
/-
# Qsag.Oracle.TwoWayQipmCompression — two-way ideal permutation model `(π, π⁻¹)` for the
# width-12 Goldilocks `Poseidon2` compression and sponge

`poseidon2Perm12` is a public, efficiently invertible permutation (`poseidon2Perm12Inv`), so an
attacker queries both directions. This module contains:

1. The lazily sampled two-way ideal permutation game over a finite `D` with an explicit
   duplicate-free complete enumeration (`QipmEnum`). The adversary is an adaptive decision tree
   (`TwoWayQipmAdv`). Success is an exact integer weight with the uniform total
   `qipmFall N i k = (N - i) (N - i - 1) ⋯ (N - i - k + 1)` (`qipmWeight_total`).
   The game IS the lazy table experiment; its equivalence with sampling a uniform element of
   `Sym(D)` is not proved here.
2. The bad-event bound `Q * B / (N - Q + 1)` (`qipm_two_way_bad_event_bound`) and its two
   instances: preimage / CICO (`qipm_two_way_preimage_bound`) and collision
   (`qipm_two_way_collision_bound`) of a compression `x ↦ comp x (π x)` with validity predicate.
3. The 1-inverse-query attack with probability one when there is neither feed-forward nor a
   capacity constraint (`qipm_unweighted_inverse_attack_total`), and the same attack on the real
   `poseidon2Perm12` (`poseidon2_unweighted_truncation_inverted`).
4. Instantiation at the Goldilocks state space (`N = p^12`, digest `p^4`): fiber counts `p^8`
   for the weighted feed-forward compression and for the capacity-4 sponge CICO, and 128-bit
   margins for every `Q ≤ 2^56` classical two-way queries.
5. Quantum two-way access as one XOR oracle on `Fin (n + n)`, the 4-point transposition
   difference, and the resulting O2H disturbance bounds. No quantum CICO or collision bound for
   two-way access is proved or claimed.

The real compression takes all 12 limbs as input (two rate lanes and the tweak lane) and outputs
one 4-limb lane; the sponge has rate 8 and capacity 4 limbs.
-/
public import Qsag.Oracle.Qrom
public import Qsag.Oracle.Poseidon2
public import Qsag.Tactic.AssuranceKit

public section
namespace Qsag
set_option autoImplicit false
set_option exponentiation.threshold 2048

/-! ## §1. Finite sums and counts over explicit enumerations -/

def qipmSum {α : Type} : List α → (α → Nat) → Nat
  | [], _ => 0
  | a :: l, f => f a + qipmSum l f

theorem qipmSum_congr {α : Type} (l : List α) {f g : α → Nat} (h : ∀ a, f a = g a) :
    qipmSum l f = qipmSum l g := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [qipmSum, qipmSum, h a, ih]

theorem qipmSum_le {α : Type} (l : List α) {f g : α → Nat} (h : ∀ a, f a ≤ g a) :
    qipmSum l f ≤ qipmSum l g := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons a l ih => rw [qipmSum, qipmSum]; exact Nat.add_le_add (h a) ih

theorem qipmSum_add {α : Type} (l : List α) (f g : α → Nat) :
    qipmSum l (fun a => f a + g a) = qipmSum l f + qipmSum l g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [qipmSum, ih]; omega

theorem qipmSum_mul_right {α : Type} (l : List α) (f : α → Nat) (c : Nat) :
    qipmSum l (fun a => f a * c) = qipmSum l f * c := by
  induction l with
  | nil => rw [qipmSum, qipmSum, Nat.zero_mul]
  | cons a l ih => rw [qipmSum, qipmSum, Nat.add_mul, ih]

theorem qipmSum_const {α : Type} (l : List α) (c : Nat) :
    qipmSum l (fun _ => c) = l.length * c := by
  induction l with
  | nil => rw [qipmSum, List.length_nil, Nat.zero_mul]
  | cons a l ih => rw [qipmSum, ih, List.length_cons, Nat.succ_mul, Nat.add_comm]

theorem qipmSum_append {α : Type} (l₁ l₂ : List α) (f : α → Nat) :
    qipmSum (l₁ ++ l₂) f = qipmSum l₁ f + qipmSum l₂ f := by
  induction l₁ with
  | nil => rw [List.nil_append, qipmSum, Nat.zero_add]
  | cons a l ih => rw [List.cons_append, qipmSum, qipmSum, ih, Nat.add_assoc]

theorem qipmSum_map {α β : Type} (l : List α) (h : α → β) (f : β → Nat) :
    qipmSum (l.map h) f = qipmSum l (fun a => f (h a)) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.map_cons, qipmSum, qipmSum, ih]

/-- Number of list entries satisfying `p`. -/
def qipmCount {α : Type} (l : List α) (p : α → Bool) : Nat :=
  qipmSum l (fun a => if p a = true then 1 else 0)

theorem qipmSum_ite_const {α : Type} (l : List α) (p : α → Bool) (c : Nat) :
    qipmSum l (fun a => if p a = true then c else 0) = qipmCount l p * c := by
  unfold qipmCount
  rw [← qipmSum_mul_right]
  apply qipmSum_congr
  intro a
  cases p a
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_mul]
  · simp only [↓reduceIte, Nat.one_mul]

theorem qipmCount_mono {α : Type} (l : List α) {p q : α → Bool}
    (h : ∀ a, p a = true → q a = true) : qipmCount l p ≤ qipmCount l q := by
  unfold qipmCount
  apply qipmSum_le
  intro a
  cases hp : p a
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_le]
  · simp only [h a hp, ↓reduceIte, Nat.le_refl]

theorem qipmCount_or_le {α : Type} (l : List α) (p q : α → Bool) :
    qipmCount l (fun a => p a || q a) ≤ qipmCount l p + qipmCount l q := by
  unfold qipmCount
  rw [← qipmSum_add]
  apply qipmSum_le
  intro a
  show (if (p a || q a) = true then 1 else 0) ≤
    (if p a = true then 1 else 0) + (if q a = true then 1 else 0)
  cases p a <;> cases q a <;> decide

theorem qipmCount_add_not {α : Type} (l : List α) (p : α → Bool) :
    qipmCount l p + qipmCount l (fun a => !p a) = l.length := by
  unfold qipmCount
  rw [← qipmSum_add]
  have h : ∀ a, (if p a = true then 1 else 0) + (if (!p a) = true then 1 else 0) = 1 := by
    intro a; cases p a <;> rfl
  rw [qipmSum_congr l h, qipmSum_const, Nat.mul_one]

theorem qipmCount_le_length {α : Type} (l : List α) (p : α → Bool) :
    qipmCount l p ≤ l.length := by
  have h := qipmCount_add_not l p
  omega

theorem qipmCount_true {α : Type} (l : List α) : qipmCount l (fun _ => true) = l.length := by
  unfold qipmCount
  simp only [↓reduceIte]
  rw [qipmSum_const, Nat.mul_one]

/-- Either no entry satisfies `p`, or some value does. -/
theorem qipmCount_zero_or_witness {α : Type} (l : List α) (p : α → Bool) :
    qipmCount l p = 0 ∨ ∃ a, p a = true := by
  induction l with
  | nil => exact Or.inl rfl
  | cons a l ih =>
    cases hp : p a
    · cases ih with
      | inl h0 =>
        left
        unfold qipmCount at h0 ⊢
        rw [qipmSum, h0]
        simp only [hp, Bool.false_eq_true, ↓reduceIte]
      | inr hw => exact Or.inr hw
    · exact Or.inr ⟨a, hp⟩

/-- `elems` lists every value of `D` exactly once. -/
def QipmEnum {D : Type} [DecidableEq D] (elems : List D) : Prop :=
  ∀ a : D, qipmCount elems (fun z => decide (z = a)) = 1

/-- A predicate with at most one solution is counted at most once by an enumeration. -/
theorem qipmCount_le_one_of_unique {D : Type} [DecidableEq D] (elems : List D)
    (hE : QipmEnum elems) (p : D → Bool)
    (hU : ∀ a b : D, p a = true → p b = true → a = b) : qipmCount elems p ≤ 1 := by
  cases qipmCount_zero_or_witness elems p with
  | inl h0 => rw [h0]; exact Nat.zero_le 1
  | inr hw =>
    obtain ⟨a0, ha0⟩ := hw
    rw [← hE a0]
    apply qipmCount_mono
    intro a ha
    exact decide_eq_true (hU a a0 ha ha0)

/-! ## §2. Lazy two-way permutation table and adaptive adversaries -/

/-- Adaptive two-way adversary: a decision tree issuing forward queries `π(x)` and inverse
    queries `π⁻¹(y)`, ending with an output. -/
inductive TwoWayQipmAdv (D Out : Type) where
  | done (out : Out)
  | fwd (x : D) (k : D → TwoWayQipmAdv D Out)
  | inv (y : D) (k : D → TwoWayQipmAdv D Out)

/-- Query table, newest entry first. An entry `(d, x, z)` records `π x = z`; `d = true` when it
    was created by an inverse query. -/
abbrev QipmTable (D : Type) := List (Bool × D × D)

def qipmFwd? {D : Type} [DecidableEq D] : QipmTable D → D → Option D
  | [], _ => none
  | e :: τ, x => if e.2.1 = x then some e.2.2 else qipmFwd? τ x

def qipmInv? {D : Type} [DecidableEq D] : QipmTable D → D → Option D
  | [], _ => none
  | e :: τ, y => if e.2.2 = y then some e.2.1 else qipmInv? τ y

theorem qipmFwd?_cons {D : Type} [DecidableEq D] (e : Bool × D × D) (τ : QipmTable D) (x : D) :
    qipmFwd? (e :: τ) x = if e.2.1 = x then some e.2.2 else qipmFwd? τ x := by rfl

theorem qipmInv?_cons {D : Type} [DecidableEq D] (e : Bool × D × D) (τ : QipmTable D) (y : D) :
    qipmInv? (e :: τ) y = if e.2.2 = y then some e.2.1 else qipmInv? τ y := by rfl

/-- The table is a partial injection: no input and no output occurs twice. -/
def QipmTableOk {D : Type} [DecidableEq D] : QipmTable D → Prop
  | [] => True
  | e :: τ => qipmFwd? τ e.2.1 = none ∧ qipmInv? τ e.2.2 = none ∧ QipmTableOk τ

theorem qipmCount_usedOut {D : Type} [DecidableEq D] (elems : List D) (hE : QipmEnum elems) :
    ∀ τ : QipmTable D, QipmTableOk τ →
      qipmCount elems (fun z => (qipmInv? τ z).isSome) = τ.length := by
  intro τ
  induction τ with
  | nil =>
    intro _
    unfold qipmCount
    simp only [qipmInv?, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    rw [qipmSum_const, Nat.mul_zero, List.length_nil]
  | cons e τ ih =>
    intro hOk
    have hpt : ∀ z, (if (qipmInv? (e :: τ) z).isSome = true then 1 else 0) =
        (if decide (z = e.2.2) = true then 1 else 0) +
          (if (qipmInv? τ z).isSome = true then 1 else 0) := by
      intro z
      rw [qipmInv?_cons]
      by_cases hz : e.2.2 = z
      · have hn : qipmInv? τ z = none := by rw [← hz]; exact hOk.2.1
        simp only [hz, ↓reduceIte, hn, Option.isSome_some, Option.isSome_none, decide_true,
          Bool.false_eq_true]
      · have hz' : ¬ z = e.2.2 := fun h => hz h.symm
        simp only [hz, hz', ↓reduceIte, decide_false, Bool.false_eq_true, Nat.zero_add]
    have h1 := hE e.2.2
    have h2 := ih hOk.2.2
    unfold qipmCount at h1 h2 ⊢
    rw [qipmSum_congr elems hpt, qipmSum_add, h1, h2, List.length_cons, Nat.add_comm]

theorem qipmCount_usedIn {D : Type} [DecidableEq D] (elems : List D) (hE : QipmEnum elems) :
    ∀ τ : QipmTable D, QipmTableOk τ →
      qipmCount elems (fun x => (qipmFwd? τ x).isSome) = τ.length := by
  intro τ
  induction τ with
  | nil =>
    intro _
    unfold qipmCount
    simp only [qipmFwd?, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    rw [qipmSum_const, Nat.mul_zero, List.length_nil]
  | cons e τ ih =>
    intro hOk
    have hpt : ∀ x, (if (qipmFwd? (e :: τ) x).isSome = true then 1 else 0) =
        (if decide (x = e.2.1) = true then 1 else 0) +
          (if (qipmFwd? τ x).isSome = true then 1 else 0) := by
      intro x
      rw [qipmFwd?_cons]
      by_cases hx : e.2.1 = x
      · have hn : qipmFwd? τ x = none := by rw [← hx]; exact hOk.1
        simp only [hx, ↓reduceIte, hn, Option.isSome_some, Option.isSome_none, decide_true,
          Bool.false_eq_true]
      · have hx' : ¬ x = e.2.1 := fun h => hx h.symm
        simp only [hx, hx', ↓reduceIte, decide_false, Bool.false_eq_true, Nat.zero_add]
    have h1 := hE e.2.1
    have h2 := ih hOk.2.2
    unfold qipmCount at h1 h2 ⊢
    rw [qipmSum_congr elems hpt, qipmSum_add, h1, h2, List.length_cons, Nat.add_comm]

theorem qipmCount_freshOut {D : Type} [DecidableEq D] (elems : List D) (hE : QipmEnum elems)
    (τ : QipmTable D) (hOk : QipmTableOk τ) :
    qipmCount elems (fun z => (qipmInv? τ z).isNone) = elems.length - τ.length := by
  have h := qipmCount_add_not elems (fun z => (qipmInv? τ z).isSome)
  rw [qipmCount_usedOut elems hE τ hOk] at h
  have hEq : qipmCount elems (fun z => (qipmInv? τ z).isNone) =
      qipmCount elems (fun z => !(qipmInv? τ z).isSome) := by
    unfold qipmCount
    apply qipmSum_congr
    intro z
    show (if (qipmInv? τ z).isNone = true then 1 else 0) =
      (if (!(qipmInv? τ z).isSome) = true then 1 else 0)
    cases qipmInv? τ z <;> rfl
  rw [hEq]
  omega

theorem qipmCount_freshIn {D : Type} [DecidableEq D] (elems : List D) (hE : QipmEnum elems)
    (τ : QipmTable D) (hOk : QipmTableOk τ) :
    qipmCount elems (fun x => (qipmFwd? τ x).isNone) = elems.length - τ.length := by
  have h := qipmCount_add_not elems (fun x => (qipmFwd? τ x).isSome)
  rw [qipmCount_usedIn elems hE τ hOk] at h
  have hEq : qipmCount elems (fun x => (qipmFwd? τ x).isNone) =
      qipmCount elems (fun x => !(qipmFwd? τ x).isSome) := by
    unfold qipmCount
    apply qipmSum_congr
    intro x
    show (if (qipmFwd? τ x).isNone = true then 1 else 0) =
      (if (!(qipmFwd? τ x).isSome) = true then 1 else 0)
    cases qipmFwd? τ x <;> rfl
  rw [hEq]
  omega

/-- Falling factorial `(N - i) (N - i - 1) ⋯ (N - i - k + 1)`: the number of equally likely
    lazy-sampling coin sequences for `k` further fresh queries from a table of size `i`. -/
def qipmFall (N : Nat) : Nat → Nat → Nat
  | _, 0 => 1
  | i, k + 1 => (N - i) * qipmFall N (i + 1) k

theorem qipmFall_succ_right (N : Nat) : ∀ (k i : Nat),
    qipmFall N i (k + 1) = qipmFall N i k * (N - i - k)
  | 0, i => by simp only [qipmFall, Nat.mul_one, Nat.one_mul, Nat.sub_zero]
  | k + 1, i => by
    have hs : N - (i + 1) - k = N - i - (k + 1) := by omega
    show (N - i) * qipmFall N (i + 1) (k + 1) = ((N - i) * qipmFall N (i + 1) k) * (N - i - (k + 1))
    rw [qipmFall_succ_right N k (i + 1), hs, Nat.mul_assoc]

theorem qipmFall_mono_index (N : Nat) : ∀ (k i : Nat), qipmFall N (i + 1) k ≤ qipmFall N i k
  | 0, _ => Nat.le_refl 1
  | k + 1, i => Nat.mul_le_mul (by omega) (qipmFall_mono_index N k (i + 1))

theorem qipmFall_pos (N : Nat) : ∀ (k i : Nat), i + k ≤ N → 0 < qipmFall N i k
  | 0, _, _ => Nat.zero_lt_one
  | k + 1, i, h => Nat.mul_pos (by omega) (qipmFall_pos N k (i + 1) (by omega))

/-- Exact success weight of the lazy two-way game with `k` remaining queries from table `τ`.
    A fresh query ranges over all unused answers. A repeated query gets the recorded answer and
    is padded by the factor `N - |τ| - (k - 1)`, so that every node has total `qipmFall N |τ| k`.
    An adversary that exceeds its budget gets weight zero. -/
def qipmWeight {D Out : Type} [DecidableEq D] (elems : List D)
    (ev : QipmTable D → Out → Bool) : TwoWayQipmAdv D Out → Nat → QipmTable D → Nat
  | .done out, k, τ => if ev τ out = true then qipmFall elems.length τ.length k else 0
  | .fwd _ _, 0, _ => 0
  | .fwd x cont, k + 1, τ =>
    match qipmFwd? τ x with
    | some z => (elems.length - τ.length - k) * qipmWeight elems ev (cont z) k τ
    | none => qipmSum elems (fun z =>
        if (qipmInv? τ z).isNone = true then
          qipmWeight elems ev (cont z) k ((false, x, z) :: τ) else 0)
  | .inv _ _, 0, _ => 0
  | .inv y cont, k + 1, τ =>
    match qipmInv? τ y with
    | some x => (elems.length - τ.length - k) * qipmWeight elems ev (cont x) k τ
    | none => qipmSum elems (fun x =>
        if (qipmFwd? τ x).isNone = true then
          qipmWeight elems ev (cont x) k ((true, x, y) :: τ) else 0)

/-- The adversary makes at most `k` queries on every path. -/
def QipmWithin {D Out : Type} : TwoWayQipmAdv D Out → Nat → Prop
  | .done _, _ => True
  | .fwd _ _, 0 => False
  | .fwd _ cont, k + 1 => ∀ z, QipmWithin (cont z) k
  | .inv _ _, 0 => False
  | .inv _ cont, k + 1 => ∀ x, QipmWithin (cont x) k

theorem qipmWeight_le_fall {D Out : Type} [DecidableEq D] (elems : List D) (hE : QipmEnum elems)
    (ev : QipmTable D → Out → Bool) (A : TwoWayQipmAdv D Out) :
    ∀ (k : Nat) (τ : QipmTable D), QipmTableOk τ →
      qipmWeight elems ev A k τ ≤ qipmFall elems.length τ.length k := by
  induction A with
  | done out =>
    intro k τ _
    rw [qipmWeight]
    split
    · exact Nat.le_refl _
    · exact Nat.zero_le _
  | fwd x cont ih =>
    intro k τ hOk
    cases k with
    | zero => rw [qipmWeight]; exact Nat.zero_le _
    | succ k =>
      rw [qipmWeight]
      split
      · next z _ =>
        rw [qipmFall_succ_right, Nat.mul_comm]
        exact Nat.mul_le_mul_right _ (ih z k τ hOk)
      · next hx =>
        refine Nat.le_trans (qipmSum_le elems (g := fun z =>
          if (qipmInv? τ z).isNone = true then qipmFall elems.length (τ.length + 1) k else 0) ?_) ?_
        · intro z
          split
          · next hf => exact ih z k _ ⟨hx, Option.isNone_iff_eq_none.mp hf, hOk⟩
          · exact Nat.le_refl 0
        · rw [qipmSum_ite_const, qipmCount_freshOut elems hE τ hOk]
          exact Nat.le_refl _
  | inv y cont ih =>
    intro k τ hOk
    cases k with
    | zero => rw [qipmWeight]; exact Nat.zero_le _
    | succ k =>
      rw [qipmWeight]
      split
      · next x _ =>
        rw [qipmFall_succ_right, Nat.mul_comm]
        exact Nat.mul_le_mul_right _ (ih x k τ hOk)
      · next hy =>
        refine Nat.le_trans (qipmSum_le elems (g := fun x =>
          if (qipmFwd? τ x).isNone = true then qipmFall elems.length (τ.length + 1) k else 0) ?_) ?_
        · intro x
          split
          · next hf => exact ih x k _ ⟨Option.isNone_iff_eq_none.mp hf, hy, hOk⟩
          · exact Nat.le_refl 0
        · rw [qipmSum_ite_const, qipmCount_freshIn elems hE τ hOk]
          exact Nat.le_refl _

/-- Normalization: the certain event has weight exactly `qipmFall N |τ| k`, for every adversary
    that stays within its budget. Hence `qipmWeight / qipmFall` is a probability. -/
theorem qipmWeight_total {D Out : Type} [DecidableEq D] (elems : List D) (hE : QipmEnum elems)
    (A : TwoWayQipmAdv D Out) :
    ∀ (k : Nat) (τ : QipmTable D), QipmTableOk τ → QipmWithin A k →
      qipmWeight elems (fun _ _ => true) A k τ = qipmFall elems.length τ.length k := by
  induction A with
  | done out =>
    intro k τ _ _
    rw [qipmWeight]
    simp only [↓reduceIte]
  | fwd x cont ih =>
    intro k τ hOk hW
    cases k with
    | zero => exact absurd hW (fun h => h)
    | succ k =>
      rw [qipmWeight]
      split
      · next z _ =>
        rw [qipmFall_succ_right, Nat.mul_comm, ih z k τ hOk (hW z)]
      · next hx =>
        have hpt : ∀ z, (if (qipmInv? τ z).isNone = true then
            qipmWeight elems (fun _ _ => true) (cont z) k ((false, x, z) :: τ) else 0) =
            (if (qipmInv? τ z).isNone = true then qipmFall elems.length (τ.length + 1) k else 0) := by
          intro z
          split
          · next hf => exact ih z k _ ⟨hx, Option.isNone_iff_eq_none.mp hf, hOk⟩ (hW z)
          · rfl
        rw [qipmSum_congr elems hpt, qipmSum_ite_const, qipmCount_freshOut elems hE τ hOk]
        rfl
  | inv y cont ih =>
    intro k τ hOk hW
    cases k with
    | zero => exact absurd hW (fun h => h)
    | succ k =>
      rw [qipmWeight]
      split
      · next x _ =>
        rw [qipmFall_succ_right, Nat.mul_comm, ih x k τ hOk (hW x)]
      · next hy =>
        have hpt : ∀ x, (if (qipmFwd? τ x).isNone = true then
            qipmWeight elems (fun _ _ => true) (cont x) k ((true, x, y) :: τ) else 0) =
            (if (qipmFwd? τ x).isNone = true then qipmFall elems.length (τ.length + 1) k else 0) := by
          intro x
          split
          · next hf => exact ih x k _ ⟨Option.isNone_iff_eq_none.mp hf, hy, hOk⟩ (hW x)
          · rfl
        rw [qipmSum_congr elems hpt, qipmSum_ite_const, qipmCount_freshIn elems hE τ hOk]
        rfl

theorem qipmWeight_mono {D Out : Type} [DecidableEq D] (elems : List D)
    (ev ev' : QipmTable D → Out → Bool)
    (h : ∀ τ o, ev τ o = true → ev' τ o = true) (A : TwoWayQipmAdv D Out) :
    ∀ (k : Nat) (τ : QipmTable D), qipmWeight elems ev A k τ ≤ qipmWeight elems ev' A k τ := by
  induction A with
  | done out =>
    intro k τ
    rw [qipmWeight, qipmWeight]
    cases hev : ev τ out
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_le]
    · simp only [h τ out hev, ↓reduceIte, Nat.le_refl]
  | fwd x cont ih =>
    intro k τ
    cases k with
    | zero => rw [qipmWeight]; exact Nat.zero_le _
    | succ k =>
      rw [qipmWeight, qipmWeight]
      split
      · next z _ => exact Nat.mul_le_mul_left _ (ih z k τ)
      · apply qipmSum_le
        intro z
        split
        · exact ih z k _
        · exact Nat.le_refl 0
  | inv y cont ih =>
    intro k τ
    cases k with
    | zero => rw [qipmWeight]; exact Nat.zero_le _
    | succ k =>
      rw [qipmWeight, qipmWeight]
      split
      · next x _ => exact Nat.mul_le_mul_left _ (ih x k τ)
      · apply qipmSum_le
        intro x
        split
        · exact ih x k _
        · exact Nat.le_refl 0

/-! ## §3. Bad-event bound for two-way queries -/

/-- Some entry of the table was bad at the moment it was created. -/
def qipmAnyBad {D : Type} (bad : QipmTable D → Bool × D × D → Bool) : QipmTable D → Bool
  | [] => false
  | e :: τ => bad τ e || qipmAnyBad bad τ

/-- Weight budget `k * B * qipmFall N i (k - 1)` of the bad event. -/
def qipmBadBudget (N B : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | i, k + 1 => (k + 1) * B * qipmFall N i k

theorem qipmBadBudget_redundant (N B i : Nat) : ∀ k : Nat,
    (N - i - k) * qipmBadBudget N B i k ≤ qipmBadBudget N B i (k + 1)
  | 0 => by
    show (N - i - 0) * 0 ≤ _
    rw [Nat.mul_zero]; exact Nat.zero_le _
  | k + 1 => by
    show (N - i - (k + 1)) * ((k + 1) * B * qipmFall N i k) ≤
      (k + 1 + 1) * B * qipmFall N i (k + 1)
    rw [qipmFall_succ_right, Nat.mul_comm (N - i - (k + 1)), Nat.mul_assoc ((k + 1) * B)]
    refine Nat.le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
      (show N - i - (k + 1) ≤ N - i - k by omega))) ?_
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_succ _))

theorem qipmBadBudget_fresh (N B i c : Nat) (hc : c ≤ B) : ∀ k : Nat,
    c * qipmFall N (i + 1) k + (N - i) * qipmBadBudget N B (i + 1) k ≤
      qipmBadBudget N B i (k + 1) := by
  intro k
  have h1 : c * qipmFall N (i + 1) k ≤ B * qipmFall N i k :=
    Nat.mul_le_mul hc (qipmFall_mono_index N k i)
  have h2 : (N - i) * qipmBadBudget N B (i + 1) k ≤ k * B * qipmFall N i k := by
    cases k with
    | zero =>
      show (N - i) * 0 ≤ _
      rw [Nat.mul_zero]; exact Nat.zero_le _
    | succ k =>
      show (N - i) * ((k + 1) * B * qipmFall N (i + 1) k) ≤
        (k + 1) * B * ((N - i) * qipmFall N (i + 1) k)
      exact Nat.le_of_eq (Nat.mul_left_comm _ _ _)
  show _ ≤ (k + 1) * B * qipmFall N i k
  rw [Nat.succ_mul k B, Nat.add_mul, Nat.add_comm (k * B * qipmFall N i k)]
  exact Nat.add_le_add h1 h2

/-- **Two-way bad-event weight bound.** If every table of size below `Qmax` admits at most `B`
    bad fresh answers for each forward and each inverse query, then the weight of "some query
    was bad" with `k` remaining queries is at most `k * B * qipmFall N |τ| (k - 1)`. -/
theorem qipm_bad_weight_le {D Out : Type} [DecidableEq D] (elems : List D) (hE : QipmEnum elems)
    (bad : QipmTable D → Bool × D × D → Bool) (B Qmax : Nat)
    (hF : ∀ (τ : QipmTable D) (x : D), τ.length < Qmax →
      qipmCount elems (fun z => (qipmInv? τ z).isNone && bad τ (false, x, z)) ≤ B)
    (hI : ∀ (τ : QipmTable D) (y : D), τ.length < Qmax →
      qipmCount elems (fun x => (qipmFwd? τ x).isNone && bad τ (true, x, y)) ≤ B)
    (A : TwoWayQipmAdv D Out) :
    ∀ (k : Nat) (τ : QipmTable D), QipmTableOk τ → τ.length + k ≤ Qmax →
      qipmAnyBad bad τ = false →
      qipmWeight elems (fun τ' (_ : Out) => qipmAnyBad bad τ') A k τ ≤
        qipmBadBudget elems.length B τ.length k := by
  induction A with
  | done out =>
    intro k τ _ _ hNo
    rw [qipmWeight]
    simp only [hNo, Bool.false_eq_true, ↓reduceIte, Nat.zero_le]
  | fwd x cont ih =>
    intro k τ hOk hLen hNo
    cases k with
    | zero => rw [qipmWeight]; exact Nat.zero_le _
    | succ k =>
      rw [qipmWeight]
      split
      · next z _ =>
        exact Nat.le_trans (Nat.mul_le_mul_left _ (ih z k τ hOk (by omega) hNo))
          (qipmBadBudget_redundant _ _ _ k)
      · next hx =>
        have hstep : ∀ z, (if (qipmInv? τ z).isNone = true then
            qipmWeight elems (fun τ' (_ : Out) => qipmAnyBad bad τ') (cont z) k
              ((false, x, z) :: τ) else 0) ≤
            (if ((qipmInv? τ z).isNone && bad τ (false, x, z)) = true then
              qipmFall elems.length (τ.length + 1) k else 0) +
            (if (qipmInv? τ z).isNone = true then
              qipmBadBudget elems.length B (τ.length + 1) k else 0) := by
          intro z
          cases hfz : (qipmInv? τ z).isNone
          · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and, Nat.le_refl]
          · have hOk' : QipmTableOk ((false, x, z) :: τ) :=
              ⟨hx, Option.isNone_iff_eq_none.mp hfz, hOk⟩
            cases hb : bad τ (false, x, z)
            · simp only [↓reduceIte, Bool.true_and, Bool.false_eq_true, Nat.zero_add]
              refine ih z k _ hOk' ?_ ?_
              · rw [List.length_cons]; omega
              · show (bad τ (false, x, z) || qipmAnyBad bad τ) = false
                rw [hb, hNo]; rfl
            · simp only [↓reduceIte, Bool.true_and]
              exact Nat.le_trans (qipmWeight_le_fall elems hE _ (cont z) k _ hOk')
                (Nat.le_add_right _ _)
        refine Nat.le_trans (qipmSum_le elems hstep) ?_
        rw [qipmSum_add, qipmSum_ite_const, qipmSum_ite_const,
          qipmCount_freshOut elems hE τ hOk]
        exact qipmBadBudget_fresh _ _ _ _ (hF τ x (by omega)) k
  | inv y cont ih =>
    intro k τ hOk hLen hNo
    cases k with
    | zero => rw [qipmWeight]; exact Nat.zero_le _
    | succ k =>
      rw [qipmWeight]
      split
      · next x _ =>
        exact Nat.le_trans (Nat.mul_le_mul_left _ (ih x k τ hOk (by omega) hNo))
          (qipmBadBudget_redundant _ _ _ k)
      · next hy =>
        have hstep : ∀ x, (if (qipmFwd? τ x).isNone = true then
            qipmWeight elems (fun τ' (_ : Out) => qipmAnyBad bad τ') (cont x) k
              ((true, x, y) :: τ) else 0) ≤
            (if ((qipmFwd? τ x).isNone && bad τ (true, x, y)) = true then
              qipmFall elems.length (τ.length + 1) k else 0) +
            (if (qipmFwd? τ x).isNone = true then
              qipmBadBudget elems.length B (τ.length + 1) k else 0) := by
          intro x
          cases hfx : (qipmFwd? τ x).isNone
          · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and, Nat.le_refl]
          · have hOk' : QipmTableOk ((true, x, y) :: τ) :=
              ⟨Option.isNone_iff_eq_none.mp hfx, hy, hOk⟩
            cases hb : bad τ (true, x, y)
            · simp only [↓reduceIte, Bool.true_and, Bool.false_eq_true, Nat.zero_add]
              refine ih x k _ hOk' ?_ ?_
              · rw [List.length_cons]; omega
              · show (bad τ (true, x, y) || qipmAnyBad bad τ) = false
                rw [hb, hNo]; rfl
            · simp only [↓reduceIte, Bool.true_and]
              exact Nat.le_trans (qipmWeight_le_fall elems hE _ (cont x) k _ hOk')
                (Nat.le_add_right _ _)
        refine Nat.le_trans (qipmSum_le elems hstep) ?_
        rw [qipmSum_add, qipmSum_ite_const, qipmSum_ite_const,
          qipmCount_freshIn elems hE τ hOk]
        exact qipmBadBudget_fresh _ _ _ _ (hI τ y (by omega)) k

/-- Success probability of event `ev` for adversary `A` with query budget `Q`, starting from the
    empty table: `qipmWeight / qipmFall N 0 Q`. -/
def qipmProb {D Out : Type} [DecidableEq D] (elems : List D) (ev : QipmTable D → Out → Bool)
    (A : TwoWayQipmAdv D Out) (Q : Nat) (hQ : Q ≤ elems.length) : RatBound :=
  ⟨qipmWeight elems ev A Q [], qipmFall elems.length 0 Q,
    qipmFall_pos elems.length Q 0 (by rw [Nat.zero_add]; exact hQ)⟩

/-- **Two-way bad-event probability bound `Q * B / (N - Q + 1)`.** Every event that implies a
    bad query has probability at most `Q * B / (N - Q + 1)` against any adaptive adversary with
    `Q` forward-plus-inverse queries to a lazily sampled permutation of an `N`-element set. -/
theorem qipm_two_way_bad_event_bound {D Out : Type} [DecidableEq D] (elems : List D)
    (hE : QipmEnum elems) (bad : QipmTable D → Bool × D × D → Bool) (B : Nat)
    (ev : QipmTable D → Out → Bool)
    (hImp : ∀ τ o, ev τ o = true → qipmAnyBad bad τ = true)
    (A : TwoWayQipmAdv D Out) (Q : Nat) (hQ : Q ≤ elems.length)
    (hF : ∀ (τ : QipmTable D) (x : D), τ.length < Q →
      qipmCount elems (fun z => (qipmInv? τ z).isNone && bad τ (false, x, z)) ≤ B)
    (hI : ∀ (τ : QipmTable D) (y : D), τ.length < Q →
      qipmCount elems (fun x => (qipmFwd? τ x).isNone && bad τ (true, x, y)) ≤ B) :
    RatBound.le (qipmProb elems ev A Q hQ)
      ⟨Q * B, elems.length - Q + 1, Nat.succ_pos _⟩ := by
  have hW := Nat.le_trans (qipmWeight_mono elems ev _ hImp A Q [])
    (qipm_bad_weight_le elems hE bad B Q hF hI A Q [] True.intro
      (by rw [List.length_nil, Nat.zero_add]; exact Nat.le_refl Q) rfl)
  show qipmWeight elems ev A Q [] * (elems.length - Q + 1) ≤ Q * B * qipmFall elems.length 0 Q
  cases Q with
  | zero =>
    have h0 : qipmWeight elems ev A 0 [] = 0 := Nat.le_zero.mp hW
    rw [h0, Nat.zero_mul]; exact Nat.zero_le _
  | succ q =>
    have hden : elems.length - (q + 1) + 1 = elems.length - 0 - q := by omega
    rw [hden, qipmFall_succ_right, ← Nat.mul_assoc]
    exact Nat.mul_le_mul_right _ hW

/-! ## §4. Preimage / CICO and collision games for a compression `x ↦ comp x (π x)` -/

private theorem qipm_and_left {a b : Bool} (h : (a && b) = true) : a = true := by
  revert h; cases a <;> cases b <;> decide

private theorem qipm_and_right {a b : Bool} (h : (a && b) = true) : b = true := by
  revert h; cases a <;> cases b <;> decide

private theorem qipm_and_intro {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  rw [ha, hb]; rfl

theorem qipmCount_false {α : Type} (l : List α) : qipmCount l (fun _ => false) = 0 := by
  unfold qipmCount
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [qipmSum_const, Nat.mul_zero]

/-- The claimed preimage is evaluated by a final forward query, so the win condition is always
    checked against the permutation table. This costs one query of the budget. -/
def qipmFinalizeFwd {D : Type} : TwoWayQipmAdv D D → TwoWayQipmAdv D D
  | .done x => .fwd x (fun _ => .done x)
  | .fwd x k => .fwd x (fun z => qipmFinalizeFwd (k z))
  | .inv y k => .inv y (fun x => qipmFinalizeFwd (k x))

/-- `x` is a valid input whose recorded permutation output compresses to `y`. `valid` carries the
    capacity / domain constraint (CICO); `comp x z` is the digest computed from the input `x` and
    the permutation output `z`. -/
def qipmPreimageWin {D G : Type} [DecidableEq D] [DecidableEq G] (valid : D → Bool)
    (comp : D → D → G) (y : G) (τ : QipmTable D) (x : D) : Bool :=
  match qipmFwd? τ x with
  | some z => valid x && decide (comp x z = y)
  | none => false

def qipmPreimageBad {D G : Type} [DecidableEq G] (valid : D → Bool) (comp : D → D → G) (y : G) :
    QipmTable D → Bool × D × D → Bool :=
  fun _ e => valid e.2.1 && decide (comp e.2.1 e.2.2 = y)

theorem qipmPreimageWin_anyBad {D G : Type} [DecidableEq D] [DecidableEq G] (valid : D → Bool)
    (comp : D → D → G) (y : G) : ∀ (τ : QipmTable D) (x : D),
      qipmPreimageWin valid comp y τ x = true →
        qipmAnyBad (qipmPreimageBad valid comp y) τ = true := by
  intro τ
  induction τ with
  | nil => intro x h; exact Bool.noConfusion h
  | cons e τ ih =>
    intro x h
    unfold qipmPreimageWin at h
    rw [qipmFwd?_cons] at h
    show (qipmPreimageBad valid comp y τ e || qipmAnyBad (qipmPreimageBad valid comp y) τ) = true
    by_cases he : e.2.1 = x
    · simp only [he, ↓reduceIte] at h
      have hb : qipmPreimageBad valid comp y τ e = true := by
        show (valid e.2.1 && decide (comp e.2.1 e.2.2 = y)) = true
        rw [he]; exact h
      rw [hb]; rfl
    · simp only [he, ↓reduceIte] at h
      rw [ih x h, Bool.or_true]

/-- Probability that a `Q`-query two-way adversary outputs a valid preimage of `y`. -/
def qipmPreimageProb {D G : Type} [DecidableEq D] [DecidableEq G] (elems : List D)
    (valid : D → Bool) (comp : D → D → G) (y : G) (A : TwoWayQipmAdv D D) (Q : Nat)
    (hQ : Q + 1 ≤ elems.length) : RatBound :=
  qipmProb elems (qipmPreimageWin valid comp y) (qipmFinalizeFwd A) (Q + 1) hQ

/-- **Two-way preimage / CICO bound.** If at most `B` permutation outputs `z` complete any fixed
    input to digest `y`, and at most `B` valid inputs `x` complete any fixed output to digest `y`,
    then `Q` forward-plus-inverse queries find a valid preimage of `y` with probability at most
    `(Q + 1) * B / (N - Q)`. -/
theorem qipm_two_way_preimage_bound {D G : Type} [DecidableEq D] [DecidableEq G]
    (elems : List D) (hE : QipmEnum elems) (valid : D → Bool) (comp : D → D → G) (y : G) (B : Nat)
    (hF : ∀ x : D, qipmCount elems (fun z => decide (comp x z = y)) ≤ B)
    (hI : ∀ z : D, qipmCount elems (fun x => valid x && decide (comp x z = y)) ≤ B)
    (A : TwoWayQipmAdv D D) (Q : Nat) (hQ : Q + 1 ≤ elems.length) :
    RatBound.le (qipmPreimageProb elems valid comp y A Q hQ)
      ⟨(Q + 1) * B, elems.length - (Q + 1) + 1, Nat.succ_pos _⟩ :=
  qipm_two_way_bad_event_bound elems hE (qipmPreimageBad valid comp y) B _
    (qipmPreimageWin_anyBad valid comp y) _ (Q + 1) hQ
    (fun _ x _ => Nat.le_trans
      (qipmCount_mono elems (fun _ h => qipm_and_right (qipm_and_right h))) (hF x))
    (fun _ z _ => Nat.le_trans (qipmCount_mono elems (fun _ h => qipm_and_right h)) (hI z))

/-- The claimed colliding pair is evaluated by two final forward queries. -/
def qipmFinalizeFwd2 {D : Type} : TwoWayQipmAdv D (D × D) → TwoWayQipmAdv D (D × D)
  | .done p => .fwd p.1 (fun _ => .fwd p.2 (fun _ => .done p))
  | .fwd x k => .fwd x (fun z => qipmFinalizeFwd2 (k z))
  | .inv y k => .inv y (fun x => qipmFinalizeFwd2 (k x))

/-- Two distinct valid inputs whose recorded outputs give the same digest. -/
def qipmCollisionWin {D G : Type} [DecidableEq D] [DecidableEq G] (valid : D → Bool)
    (comp : D → D → G) (τ : QipmTable D) (p : D × D) : Bool :=
  match qipmFwd? τ p.1, qipmFwd? τ p.2 with
  | some z, some z' =>
    !decide (p.1 = p.2) && (valid p.1 && (valid p.2 && decide (comp p.1 z = comp p.2 z')))
  | _, _ => false

/-- Some recorded valid input already has digest `g`. -/
def qipmHit {D G : Type} [DecidableEq G] (valid : D → Bool) (comp : D → D → G) (g : G) :
    QipmTable D → Bool
  | [] => false
  | e :: τ => (valid e.2.1 && decide (g = comp e.2.1 e.2.2)) || qipmHit valid comp g τ

def qipmCollisionBad {D G : Type} [DecidableEq G] (valid : D → Bool) (comp : D → D → G) :
    QipmTable D → Bool × D × D → Bool :=
  fun τ e => valid e.2.1 && qipmHit valid comp (comp e.2.1 e.2.2) τ

private theorem qipmFwd?_some_hit {D G : Type} [DecidableEq D] [DecidableEq G] (valid : D → Bool)
    (comp : D → D → G) (x z : D) (hv : valid x = true) : ∀ τ : QipmTable D,
      qipmFwd? τ x = some z → qipmHit valid comp (comp x z) τ = true := by
  intro τ
  induction τ with
  | nil => intro h; have h' : (none : Option D) = some z := h; cases h'
  | cons e τ ih =>
    intro h
    rw [qipmFwd?_cons] at h
    show ((valid e.2.1 && decide (comp x z = comp e.2.1 e.2.2)) ||
      qipmHit valid comp (comp x z) τ) = true
    by_cases he : e.2.1 = x
    · simp only [he, ↓reduceIte] at h
      have hz : e.2.2 = z := Option.some.inj h
      rw [he, hz, hv, decide_eq_true rfl]; rfl
    · simp only [he, ↓reduceIte] at h
      rw [ih h, Bool.or_true]

private theorem qipm_collision_entries_anyBad {D G : Type} [DecidableEq D] [DecidableEq G]
    (valid : D → Bool) (comp : D → D → G) : ∀ (τ : QipmTable D) (x x' z z' : D),
      qipmFwd? τ x = some z → qipmFwd? τ x' = some z' → ¬ x = x' → valid x = true →
      valid x' = true → comp x z = comp x' z' →
        qipmAnyBad (qipmCollisionBad valid comp) τ = true := by
  intro τ
  induction τ with
  | nil => intro x x' z z' h; have h' : (none : Option D) = some z := h; cases h'
  | cons e τ ih =>
    intro x x' z z' h1 h2 hne hv hv' hc
    rw [qipmFwd?_cons] at h1 h2
    show (qipmCollisionBad valid comp τ e || qipmAnyBad (qipmCollisionBad valid comp) τ) = true
    by_cases he : e.2.1 = x
    · by_cases he' : e.2.1 = x'
      · exact absurd (he.symm.trans he') hne
      · simp only [he, ↓reduceIte] at h1
        simp only [he', ↓reduceIte] at h2
        have hz : e.2.2 = z := Option.some.inj h1
        have hb : qipmCollisionBad valid comp τ e = true := by
          show (valid e.2.1 && qipmHit valid comp (comp e.2.1 e.2.2) τ) = true
          rw [he, hz, hv, hc, qipmFwd?_some_hit valid comp x' z' hv' τ h2]; rfl
        rw [hb]; rfl
    · by_cases he' : e.2.1 = x'
      · simp only [he, ↓reduceIte] at h1
        simp only [he', ↓reduceIte] at h2
        have hz : e.2.2 = z' := Option.some.inj h2
        have hb : qipmCollisionBad valid comp τ e = true := by
          show (valid e.2.1 && qipmHit valid comp (comp e.2.1 e.2.2) τ) = true
          rw [he', hz, hv', ← hc, qipmFwd?_some_hit valid comp x z hv τ h1]; rfl
        rw [hb]; rfl
      · simp only [he, ↓reduceIte] at h1
        simp only [he', ↓reduceIte] at h2
        rw [ih x x' z z' h1 h2 hne hv hv' hc, Bool.or_true]

