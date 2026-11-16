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

theorem qipmCollisionWin_anyBad {D G : Type} [DecidableEq D] [DecidableEq G] (valid : D → Bool)
    (comp : D → D → G) (τ : QipmTable D) (p : D × D)
    (h : qipmCollisionWin valid comp τ p = true) :
    qipmAnyBad (qipmCollisionBad valid comp) τ = true := by
  unfold qipmCollisionWin at h
  cases h1 : qipmFwd? τ p.1 with
  | none => simp only [h1] at h; exact Bool.noConfusion h
  | some z =>
    cases h2 : qipmFwd? τ p.2 with
    | none => simp only [h1, h2] at h; exact Bool.noConfusion h
    | some z' =>
      simp only [h1, h2] at h
      have hne : ¬ p.1 = p.2 := by
        intro heq
        have hd := qipm_and_left h
        rw [decide_eq_true heq] at hd
        exact Bool.noConfusion hd
      have hr := qipm_and_right h
      exact qipm_collision_entries_anyBad valid comp τ p.1 p.2 z z' h1 h2 hne
        (qipm_and_left hr) (qipm_and_left (qipm_and_right hr))
        (of_decide_eq_true (qipm_and_right (qipm_and_right hr)))

private theorem qipmCount_hit_fwd {D G : Type} [DecidableEq G] (elems : List D)
    (valid : D → Bool) (comp : D → D → G) (B : Nat)
    (hF : ∀ (x : D) (g : G), qipmCount elems (fun z => decide (comp x z = g)) ≤ B) (x : D) :
    ∀ τ : QipmTable D,
      qipmCount elems (fun z => qipmHit valid comp (comp x z) τ) ≤ τ.length * B := by
  intro τ
  induction τ with
  | nil =>
    show qipmCount elems (fun _ => false) ≤ _
    rw [qipmCount_false]; exact Nat.zero_le _
  | cons e τ ih =>
    show qipmCount elems (fun z => (valid e.2.1 && decide (comp x z = comp e.2.1 e.2.2)) ||
      qipmHit valid comp (comp x z) τ) ≤ _
    refine Nat.le_trans (qipmCount_or_le elems _ _) ?_
    rw [List.length_cons, Nat.succ_mul, Nat.add_comm (τ.length * B) B]
    exact Nat.add_le_add
      (Nat.le_trans (qipmCount_mono elems (fun _ h => qipm_and_right h)) (hF x _)) ih

private theorem qipmCount_hit_inv {D G : Type} [DecidableEq G] (elems : List D)
    (valid : D → Bool) (comp : D → D → G) (B : Nat)
    (hI : ∀ (z : D) (g : G), qipmCount elems (fun x => valid x && decide (comp x z = g)) ≤ B)
    (z : D) : ∀ τ : QipmTable D,
      qipmCount elems (fun x => valid x && qipmHit valid comp (comp x z) τ) ≤ τ.length * B := by
  intro τ
  induction τ with
  | nil =>
    refine Nat.le_trans (qipmCount_mono elems (q := fun _ => false) ?_) ?_
    · intro x h; exact qipm_and_right h
    · rw [qipmCount_false]; exact Nat.zero_le _
  | cons e τ ih =>
    refine Nat.le_trans (qipmCount_mono elems (q := fun x =>
      (valid x && decide (comp x z = comp e.2.1 e.2.2)) ||
        (valid x && qipmHit valid comp (comp x z) τ)) ?_) ?_
    · intro x h
      have hv := qipm_and_left h
      have hh : ((valid e.2.1 && decide (comp x z = comp e.2.1 e.2.2)) ||
          qipmHit valid comp (comp x z) τ) = true := qipm_and_right h
      show ((valid x && decide (comp x z = comp e.2.1 e.2.2)) ||
        (valid x && qipmHit valid comp (comp x z) τ)) = true
      rw [hv]
      revert hh
      cases valid e.2.1 <;> cases decide (comp x z = comp e.2.1 e.2.2) <;>
        cases qipmHit valid comp (comp x z) τ <;> decide
    · refine Nat.le_trans (qipmCount_or_le elems _ _) ?_
      rw [List.length_cons, Nat.succ_mul, Nat.add_comm (τ.length * B) B]
      exact Nat.add_le_add (hI z _) ih

/-- Probability that a `Q`-query two-way adversary outputs a collision of valid inputs. -/
def qipmCollisionProb {D G : Type} [DecidableEq D] [DecidableEq G] (elems : List D)
    (valid : D → Bool) (comp : D → D → G) (A : TwoWayQipmAdv D (D × D)) (Q : Nat)
    (hQ : Q + 2 ≤ elems.length) : RatBound :=
  qipmProb elems (qipmCollisionWin valid comp) (qipmFinalizeFwd2 A) (Q + 2) hQ

/-- **Two-way collision bound.** With fiber counts at most `B` in both directions for every
    digest, `Q` forward-plus-inverse queries find a collision of valid inputs with probability
    at most `(Q + 2)^2 * B / (N - Q - 1)`. -/
theorem qipm_two_way_collision_bound {D G : Type} [DecidableEq D] [DecidableEq G]
    (elems : List D) (hE : QipmEnum elems) (valid : D → Bool) (comp : D → D → G) (B : Nat)
    (hF : ∀ (x : D) (g : G), qipmCount elems (fun z => decide (comp x z = g)) ≤ B)
    (hI : ∀ (z : D) (g : G), qipmCount elems (fun x => valid x && decide (comp x z = g)) ≤ B)
    (A : TwoWayQipmAdv D (D × D)) (Q : Nat) (hQ : Q + 2 ≤ elems.length) :
    RatBound.le (qipmCollisionProb elems valid comp A Q hQ)
      ⟨(Q + 2) * ((Q + 2) * B), elems.length - (Q + 2) + 1, Nat.succ_pos _⟩ :=
  qipm_two_way_bad_event_bound elems hE (qipmCollisionBad valid comp) ((Q + 2) * B) _
    (qipmCollisionWin_anyBad valid comp) _ (Q + 2) hQ
    (fun τ x hlen => Nat.le_trans
      (qipmCount_mono elems (q := fun z => qipmHit valid comp (comp x z) τ)
        (by intro z h; exact qipm_and_right (qipm_and_right h)))
      (Nat.le_trans (qipmCount_hit_fwd elems valid comp B hF x τ)
        (Nat.mul_le_mul_right B (Nat.le_of_lt hlen))))
    (fun τ z hlen => Nat.le_trans
      (qipmCount_mono elems (q := fun x => valid x && qipmHit valid comp (comp x z) τ)
        (by intro x h; exact qipm_and_right h))
      (Nat.le_trans (qipmCount_hit_inv elems valid comp B hI z τ)
        (Nat.mul_le_mul_right B (Nat.le_of_lt hlen))))

/-! ## §5. Inversion collapse without feed-forward and without capacity -/

/-- **One inverse query inverts an unweighted, unconstrained truncation with probability one.**
    If the digest reads only the permutation output (`comp x z = out z`) and every input is valid,
    the adversary asks `π⁻¹(z*)` for any `z*` with `out z* = y` and outputs the answer. Its
    success weight equals the total weight `qipmFall N 0 2` of the two-query game. -/
theorem qipm_unweighted_inverse_attack_total {D G : Type} [DecidableEq D] [DecidableEq G]
    (elems : List D) (out : D → G) (y : G) (zs : D) (hz : out zs = y) :
    qipmWeight elems (qipmPreimageWin (fun _ => true) (fun _ z => out z) y)
      (qipmFinalizeFwd (TwoWayQipmAdv.inv zs TwoWayQipmAdv.done)) (1 + 1) [] =
      qipmFall elems.length 0 (1 + 1) := by
  have hpt : ∀ x : D, (if (qipmFwd? ([] : QipmTable D) x).isNone = true then
      qipmWeight elems (qipmPreimageWin (fun _ => true) (fun _ z => out z) y)
        (TwoWayQipmAdv.fwd x (fun _ => TwoWayQipmAdv.done x)) (0 + 1) [(true, x, zs)] else 0) =
      elems.length - 1 := by
    intro x
    have hl : qipmFwd? [(true, x, zs)] x = some zs := by
      rw [qipmFwd?_cons]; simp only [↓reduceIte]
    have hw : qipmPreimageWin (fun _ => true) (fun _ z => out z) y [(true, x, zs)] x = true := by
      unfold qipmPreimageWin
      rw [hl]
      show (true && decide (out zs = y)) = true
      rw [decide_eq_true hz]; rfl
    have hn : (qipmFwd? ([] : QipmTable D) x).isNone = true := rfl
    rw [hn]
    simp only [↓reduceIte]
    rw [qipmWeight]
    simp only [hl]
    rw [qipmWeight]
    simp only [hw, ↓reduceIte, qipmFall, List.length_cons, List.length_nil, Nat.zero_add, Nat.mul_one,
      Nat.sub_zero]
  show qipmSum elems (fun x => if (qipmFwd? ([] : QipmTable D) x).isNone = true then
      qipmWeight elems (qipmPreimageWin (fun _ => true) (fun _ z => out z) y)
        (TwoWayQipmAdv.fwd x (fun _ => TwoWayQipmAdv.done x)) (0 + 1) [(true, x, zs)] else 0) =
    (elems.length - 0) * ((elems.length - 1) * 1)
  rw [qipmSum_congr elems hpt, qipmSum_const, Nat.mul_one, Nat.sub_zero]

/-- Weighted feed-forward of the canonical compression: `in0 + 2 * in1 + 4 * tweak`. -/
def qipmFeedForward (s : Poseidon2State12) : Lane4 :=
  lane4Add (lane4Add s.b0 (lane4Scale (Goldilocks.ofNat 2) s.b1))
    (lane4Scale (Goldilocks.ofNat 4) s.b2)

/-- Digest of the weighted compression from the input `x` and the permutation output `z`. -/
def qipmWeightedComp (x z : Poseidon2State12) : Lane4 :=
  lane4Add z.b0 (qipmFeedForward x)

/-- Digest that only truncates the permutation output: no feed-forward. This is also the squeeze
    of a single-block rate-8 sponge. -/
def qipmTruncComp (_x z : Poseidon2State12) : Lane4 := z.b0

/-- The canonical `poseidon2CompressWeighted` shape, for an arbitrary permutation `π` in place of
    `poseidon2Perm12`: all 12 limbs are input, the digest is one 4-limb lane. -/
def qipmWeightedCompress (π : Poseidon2State12 → Poseidon2State12) (s : Poseidon2State12) :
    Lane4 :=
  qipmWeightedComp s (π s)

theorem qipmWeightedCompress_eq (π : Poseidon2State12 → Poseidon2State12)
    (s : Poseidon2State12) :
    qipmWeightedCompress π s =
      lane4Add (π s).b0 (lane4Add (lane4Add s.b0 (lane4Scale (Goldilocks.ofNat 2) s.b1))
        (lane4Scale (Goldilocks.ofNat 4) s.b2)) := by rfl

theorem qipmWeightedCompress_def (π : Poseidon2State12 → Poseidon2State12)
    (s : Poseidon2State12) : qipmWeightedCompress π s = qipmWeightedComp s (π s) := by rfl

/-- At the deployed permutation, the generic weighted compression is the canonical
    `poseidon2CompressWeighted` of `Qsag.Oracle.Poseidon2`. -/
theorem qipmWeightedCompress_poseidon2Perm12 :
    qipmWeightedCompress poseidon2Perm12 = poseidon2CompressWeighted := by
  funext s
  rw [qipmWeightedCompress_eq, poseidon2CompressWeighted_eq, poseidon2WeightedFeedForward_eq]

/-- The feed-forward term of the lazy game is the one of `poseidon2CompressWeighted`. -/
theorem qipmFeedForward_eq_poseidon2WeightedFeedForward (s : Poseidon2State12) :
    qipmFeedForward s = poseidon2WeightedFeedForward s := by
  rw [poseidon2WeightedFeedForward_eq]; rfl

/-- **Inversion of the real permutation without feed-forward.** For every target digest `y` and
    every choice of the other two lanes, one evaluation of `poseidon2Perm12Inv` gives an input
    whose truncated permutation output is `y`. -/
theorem poseidon2_unweighted_truncation_inverted (y b1 b2 : Lane4) :
    qipmTruncComp (poseidon2Perm12Inv ⟨y, b1, b2⟩)
      (poseidon2Perm12 (poseidon2Perm12Inv ⟨y, b1, b2⟩)) = y := by
  show (poseidon2Perm12 (poseidon2Perm12Inv ⟨y, b1, b2⟩)).b0 = y
  rw [poseidon2Perm12Inv_right_inv]

/-- Two such inverse evaluations with different middle lanes are distinct inputs with the same
    truncated digest: an explicit collision of the real permutation's unweighted truncation. -/
theorem poseidon2_unweighted_truncation_collides (y b1 b1' b2 : Lane4) (hne : ¬ b1 = b1') :
    ¬ poseidon2Perm12Inv ⟨y, b1, b2⟩ = poseidon2Perm12Inv ⟨y, b1', b2⟩ ∧
    qipmTruncComp (poseidon2Perm12Inv ⟨y, b1, b2⟩)
        (poseidon2Perm12 (poseidon2Perm12Inv ⟨y, b1, b2⟩)) =
      qipmTruncComp (poseidon2Perm12Inv ⟨y, b1', b2⟩)
        (poseidon2Perm12 (poseidon2Perm12Inv ⟨y, b1', b2⟩)) := by
  refine ⟨fun h => hne ?_, ?_⟩
  · have h2 := congrArg poseidon2Perm12 h
    rw [poseidon2Perm12Inv_right_inv, poseidon2Perm12Inv_right_inv] at h2
    exact congrArg Poseidon2State12.b1 h2
  · rw [poseidon2_unweighted_truncation_inverted, poseidon2_unweighted_truncation_inverted]

/-! ## §6. Enumeration of the Goldilocks state space and fiber counts -/

def qipmGoldUpTo : (k : Nat) → k ≤ goldilocksPrime → List Goldilocks
  | 0, _ => []
  | k + 1, h => ⟨k, h⟩ :: qipmGoldUpTo k (Nat.le_of_succ_le h)

theorem qipmGoldUpTo_length : ∀ (k : Nat) (h : k ≤ goldilocksPrime),
    (qipmGoldUpTo k h).length = k
  | 0, _ => rfl
  | k + 1, h => by rw [qipmGoldUpTo, List.length_cons, qipmGoldUpTo_length k]

theorem qipmGoldUpTo_count (a : Goldilocks) : ∀ (k : Nat) (h : k ≤ goldilocksPrime),
    qipmCount (qipmGoldUpTo k h) (fun z => decide (z = a)) = if a.val < k then 1 else 0
  | 0, _ => by
    unfold qipmCount
    rw [qipmGoldUpTo, qipmSum]
    simp only [Nat.not_lt_zero, ↓reduceIte]
  | k + 1, h => by
    have ih := qipmGoldUpTo_count a k (Nat.le_of_succ_le h)
    unfold qipmCount at ih ⊢
    rw [qipmGoldUpTo, qipmSum, ih]
    by_cases hk : a.val = k
    · have he : (⟨k, h⟩ : Goldilocks) = a := Goldilocks.ext hk.symm
      have h1 : ¬ a.val < k := by omega
      have h2 : a.val < k + 1 := by omega
      simp only [he, decide_true, ↓reduceIte, h1, h2]
    · have he : ¬ (⟨k, h⟩ : Goldilocks) = a := fun e => hk (by rw [← e])
      simp only [he, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      by_cases hlt : a.val < k
      · have h2 : a.val < k + 1 := by omega
        simp only [hlt, h2, ↓reduceIte]
      · have h2 : ¬ a.val < k + 1 := by omega
        simp only [hlt, h2, ↓reduceIte]

/-- All Goldilocks field elements. -/
def qipmGoldAll : List Goldilocks := qipmGoldUpTo goldilocksPrime (Nat.le_refl _)

theorem qipmGoldAll_enum : QipmEnum qipmGoldAll := by
  intro a
  unfold qipmGoldAll
  rw [qipmGoldUpTo_count]
  simp only [a.isLt, ↓reduceIte]

theorem qipmGoldAll_length : qipmGoldAll.length = goldilocksPrime := by
  unfold qipmGoldAll
  rw [qipmGoldUpTo_length]

attribute [irreducible] qipmGoldAll

/-- Row-major product enumeration. -/
def qipmProd2 {A B C : Type} (mk : A → B → C) : List A → List B → List C
  | [], _ => []
  | a :: la, lb => lb.map (mk a) ++ qipmProd2 mk la lb

theorem qipmSum_prod2 {A B C : Type} (mk : A → B → C) (la : List A) (lb : List B)
    (f : C → Nat) :
    qipmSum (qipmProd2 mk la lb) f = qipmSum la (fun a => qipmSum lb (fun b => f (mk a b))) := by
  induction la with
  | nil => rfl
  | cons a la ih => rw [qipmProd2, qipmSum_append, qipmSum_map, ih, qipmSum]

theorem qipmProd2_length {A B C : Type} (mk : A → B → C) (la : List A) (lb : List B) :
    (qipmProd2 mk la lb).length = la.length * lb.length := by
  have key := qipmSum_prod2 mk la lb (fun _ => 1)
  rw [qipmSum_const, Nat.mul_one] at key
  rw [key]
  have hin : ∀ a : A, qipmSum lb (fun _ => 1) = lb.length := by
    intro _; rw [qipmSum_const, Nat.mul_one]
  rw [qipmSum_congr la hin, qipmSum_const]

theorem qipmEnum_prod2 {A B C : Type} [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (mk : A → B → C) (pa : C → A) (pb : C → B)
    (hmk : ∀ c, mk (pa c) (pb c) = c) (hpa : ∀ a b, pa (mk a b) = a)
    (hpb : ∀ a b, pb (mk a b) = b)
    (la : List A) (lb : List B) (hA : QipmEnum la) (hB : QipmEnum lb) :
    QipmEnum (qipmProd2 mk la lb) := by
  intro c
  have hin : ∀ a : A, qipmSum lb (fun b => if decide (mk a b = c) = true then 1 else 0) =
      if decide (a = pa c) = true then 1 else 0 := by
    intro a
    by_cases ha : a = pa c
    · have hb := hB (pb c)
      unfold qipmCount at hb
      simp only [ha, decide_true, ↓reduceIte]
      refine Eq.trans ?_ hb
      apply qipmSum_congr
      intro b
      by_cases hbb : b = pb c
      · have hm : mk (pa c) b = c := by rw [hbb]; exact hmk c
        rw [hbb]
        simp only [hmk c, decide_true]
      · have hm : ¬ mk (pa c) b = c := fun e => hbb (by rw [← e, hpb])
        simp only [hbb, hm, decide_false]
    · have hm : ∀ b, ¬ mk a b = c := fun b e => ha (by rw [← e, hpa])
      simp only [ha, hm, decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [qipmSum_const, Nat.mul_zero]
  have hA' := hA (pa c)
  unfold qipmCount at hA' ⊢
  rw [qipmSum_prod2, qipmSum_congr la hin]
  exact hA'

def qipmGoldPairs : List (Goldilocks × Goldilocks) := qipmProd2 Prod.mk qipmGoldAll qipmGoldAll

/-- All 4-limb lanes. -/
def qipmLaneAll : List Lane4 :=
  qipmProd2 (fun p q => Lane4.mk p.1 p.2 q.1 q.2) qipmGoldPairs qipmGoldPairs

/-- All 12-limb states over a lane enumeration; the digest lane `b0` varies fastest. -/
def qipmStatesOf (l4 : List Lane4) : List Poseidon2State12 :=
  qipmProd2 (fun (p : Lane4 × Lane4) (b0 : Lane4) => Poseidon2State12.mk b0 p.1 p.2)
    (qipmProd2 Prod.mk l4 l4) l4

theorem qipmGoldPairs_enum : QipmEnum qipmGoldPairs := by
  unfold qipmGoldPairs
  exact qipmEnum_prod2 Prod.mk Prod.fst Prod.snd (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) qipmGoldAll qipmGoldAll qipmGoldAll_enum qipmGoldAll_enum

theorem qipmLaneAll_enum : QipmEnum qipmLaneAll := by
  unfold qipmLaneAll
  exact qipmEnum_prod2 (fun p q => Lane4.mk p.1 p.2 q.1 q.2) (fun c => (c.x0, c.x1))
    (fun c => (c.x2, c.x3)) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    qipmGoldPairs qipmGoldPairs qipmGoldPairs_enum qipmGoldPairs_enum

theorem qipmStatesOf_enum (l4 : List Lane4) (hL : QipmEnum l4) : QipmEnum (qipmStatesOf l4) := by
  unfold qipmStatesOf
  exact qipmEnum_prod2 (fun (p : Lane4 × Lane4) (b0 : Lane4) => Poseidon2State12.mk b0 p.1 p.2)
    (fun s => (s.b1, s.b2)) (fun s => s.b0) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (qipmProd2 Prod.mk l4 l4) l4 (qipmEnum_prod2 Prod.mk Prod.fst Prod.snd (fun _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) l4 l4 hL hL) hL

theorem qipmStatesOf_length (l4 : List Lane4) :
    (qipmStatesOf l4).length = l4.length * l4.length * l4.length := by
  unfold qipmStatesOf
  rw [qipmProd2_length, qipmProd2_length]

private theorem qipm_pow_four (p : Nat) : p * p * (p * p) = p ^ 4 := by
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_assoc]

theorem qipmLaneAll_length : qipmLaneAll.length = goldilocksPrime ^ 4 := by
  unfold qipmLaneAll qipmGoldPairs
  rw [qipmProd2_length, qipmProd2_length, qipmGoldAll_length, qipm_pow_four]

/-- Goldilocks `Poseidon2-12` state space: all `p^12` states. -/
def qipmGoldStates : List Poseidon2State12 := qipmStatesOf qipmLaneAll

theorem qipmGoldStates_enum : QipmEnum qipmGoldStates := qipmStatesOf_enum _ qipmLaneAll_enum

theorem qipmGoldStates_length : qipmGoldStates.length = goldilocksPrime ^ 12 := by
  unfold qipmGoldStates
  rw [qipmStatesOf_length, qipmLaneAll_length, ← Nat.pow_add, ← Nat.pow_add]

/-- A predicate that fixes the digest lane `b0` once the other two lanes are given has at most
    `|lane|^2` solutions among the `|lane|^3` states. -/
theorem qipmCount_states_le_of_b0_unique (l4 : List Lane4) (hL : QipmEnum l4)
    (P : Poseidon2State12 → Bool)
    (hU : ∀ (b1 b2 a a' : Lane4), P ⟨a, b1, b2⟩ = true → P ⟨a', b1, b2⟩ = true → a = a') :
    qipmCount (qipmStatesOf l4) P ≤ l4.length * l4.length := by
  unfold qipmCount qipmStatesOf
  rw [qipmSum_prod2]
  refine Nat.le_trans (qipmSum_le _ (g := fun _ => 1) ?_) ?_
  · intro p
    exact qipmCount_le_one_of_unique l4 hL (fun a => P ⟨a, p.1, p.2⟩) (hU p.1 p.2)
  · rw [qipmSum_const, Nat.mul_one, qipmProd2_length]
    exact Nat.le_refl _

private theorem qipm_gold_add_left_cancel {a b c : Goldilocks}
    (h : Goldilocks.add c a = Goldilocks.add c b) : a = b :=
  LawfulCommRing.add_left_cancel (R := Goldilocks) (a := c) h

private theorem qipm_gold_add_right_cancel {a b c : Goldilocks}
    (h : Goldilocks.add a c = Goldilocks.add b c) : a = b := by
  apply qipm_gold_add_left_cancel (c := c)
  have h1 : Goldilocks.add c a = Goldilocks.add a c := LawfulCommRing.add_comm (R := Goldilocks) c a
  have h2 : Goldilocks.add c b = Goldilocks.add b c := LawfulCommRing.add_comm (R := Goldilocks) c b
  rw [h1, h2]; exact h

theorem qipm_lane4Add_left_cancel {a b c : Lane4} (h : lane4Add c a = lane4Add c b) : a = b := by
  rw [lane4Add_eq, lane4Add_eq] at h
  injection h with h0 h1 h2 h3
  exact Lane4.ext (qipm_gold_add_left_cancel h0) (qipm_gold_add_left_cancel h1)
    (qipm_gold_add_left_cancel h2) (qipm_gold_add_left_cancel h3)

theorem qipm_lane4Add_right_cancel {a b c : Lane4} (h : lane4Add a c = lane4Add b c) : a = b := by
  rw [lane4Add_eq, lane4Add_eq] at h
  injection h with h0 h1 h2 h3
  exact Lane4.ext (qipm_gold_add_right_cancel h0) (qipm_gold_add_right_cancel h1)
    (qipm_gold_add_right_cancel h2) (qipm_gold_add_right_cancel h3)

/-- Forward fiber of the weighted compression: for a fixed input, at most `|lane|^2` of the
    `|lane|^3` permutation outputs give digest `g`. -/
theorem qipm_weighted_forward_fiber (l4 : List Lane4) (hL : QipmEnum l4)
    (x : Poseidon2State12) (g : Lane4) :
    qipmCount (qipmStatesOf l4) (fun z => decide (qipmWeightedComp x z = g)) ≤
      l4.length * l4.length := by
  apply qipmCount_states_le_of_b0_unique l4 hL
  intro b1 b2 a a' h h'
  have e : lane4Add a (qipmFeedForward x) = lane4Add a' (qipmFeedForward x) :=
    (of_decide_eq_true h).trans (of_decide_eq_true h').symm
  exact qipm_lane4Add_right_cancel e

/-- Inverse fiber of the weighted compression with NO capacity constraint: for a fixed
    permutation output, the feed-forward alone leaves at most `|lane|^2` inputs with digest `g`. -/
theorem qipm_weighted_inverse_fiber (l4 : List Lane4) (hL : QipmEnum l4)
    (z : Poseidon2State12) (g : Lane4) :
    qipmCount (qipmStatesOf l4) (fun x => true && decide (qipmWeightedComp x z = g)) ≤
      l4.length * l4.length := by
  apply qipmCount_states_le_of_b0_unique l4 hL
  intro b1 b2 a a' h h'
  have e : lane4Add z.b0 (lane4Add (lane4Add a (lane4Scale (Goldilocks.ofNat 2) b1))
        (lane4Scale (Goldilocks.ofNat 4) b2)) =
      lane4Add z.b0 (lane4Add (lane4Add a' (lane4Scale (Goldilocks.ofNat 2) b1))
        (lane4Scale (Goldilocks.ofNat 4) b2)) :=
    (of_decide_eq_true (qipm_and_right h)).trans (of_decide_eq_true (qipm_and_right h')).symm
  exact qipm_lane4Add_right_cancel (qipm_lane4Add_right_cancel (qipm_lane4Add_left_cancel e))

/-- Forward fiber of the truncation digest. -/
theorem qipm_trunc_forward_fiber (l4 : List Lane4) (hL : QipmEnum l4)
    (x : Poseidon2State12) (g : Lane4) :
    qipmCount (qipmStatesOf l4) (fun z => decide (qipmTruncComp x z = g)) ≤
      l4.length * l4.length := by
  apply qipmCount_states_le_of_b0_unique l4 hL
  intro b1 b2 a a' h h'
  exact (of_decide_eq_true h : a = g).trans (of_decide_eq_true h' : a' = g).symm

/-- Exactly `|lane|^2` states have capacity lane `b2 = cap`. -/
theorem qipm_capacity_fiber (l4 : List Lane4) (hL : QipmEnum l4) (cap : Lane4) :
    qipmCount (qipmStatesOf l4) (fun x => decide (x.b2 = cap)) = l4.length * l4.length := by
  unfold qipmCount qipmStatesOf
  rw [qipmSum_prod2, qipmSum_prod2]
  have hin : ∀ b1 : Lane4, qipmSum l4 (fun b2 => qipmSum l4 (fun (_ : Lane4) =>
      if decide (b2 = cap) = true then 1 else 0)) = l4.length := by
    intro _
    have hc : ∀ b2 : Lane4, qipmSum l4 (fun (_ : Lane4) =>
        if decide (b2 = cap) = true then 1 else 0) =
        (if decide (b2 = cap) = true then 1 else 0) * l4.length := by
      intro b2; rw [qipmSum_const, Nat.mul_comm]
    have hcap := hL cap
    unfold qipmCount at hcap
    rw [qipmSum_congr l4 hc, qipmSum_mul_right, hcap, Nat.one_mul]
  rw [qipmSum_congr l4 hin, qipmSum_const]

/-- Inverse fiber of the sponge-style CICO with NO feed-forward: the capacity constraint alone
    leaves at most `|lane|^2` valid inputs, whatever the queried output. -/
theorem qipm_sponge_inverse_fiber (l4 : List Lane4) (hL : QipmEnum l4) (cap : Lane4)
    (z : Poseidon2State12) (g : Lane4) :
    qipmCount (qipmStatesOf l4)
        (fun x => decide (x.b2 = cap) && decide (qipmTruncComp x z = g)) ≤
      l4.length * l4.length := by
  rw [← qipm_capacity_fiber l4 hL cap]
  exact qipmCount_mono _ (fun _ h => qipm_and_left h)

/-- With neither feed-forward nor capacity, EVERY input completes a suitable inverse query:
    the inverse fiber is the whole state space. -/
theorem qipm_unprotected_inverse_fiber_full (l4 : List Lane4) (z : Poseidon2State12) :
    qipmCount (qipmStatesOf l4) (fun x => true && decide (qipmTruncComp x z = z.b0)) =
      l4.length * l4.length * l4.length := by
  have hp : ∀ x : Poseidon2State12, (true && decide (qipmTruncComp x z = z.b0)) = true := by
    intro x; exact qipm_and_intro rfl (decide_eq_true rfl)
  unfold qipmCount
  simp only [hp, ↓reduceIte]
  rw [qipmSum_const, Nat.mul_one, qipmStatesOf_length]

/-! ## §7. Goldilocks `Poseidon2-12` parameters at `Q ≤ 2^56` classical two-way queries -/

theorem qipmGoldStates_budget_ok (Q : Nat) (hQ : Q ≤ 2 ^ 56) : Q + 2 ≤ qipmGoldStates.length := by
  rw [qipmGoldStates_length]
  have hlit : 2 ^ 56 + 2 ≤ goldilocksPrime ^ 12 := by decide +kernel
  exact Nat.le_trans (Nat.add_le_add_right hQ 2) hlit

private theorem qipm_sub_antitone (P a b : Nat) (h : a ≤ b) : P - b + 1 ≤ P - a + 1 := by omega

private theorem qipm_goldilocks_preimage_arith (Q : Nat) (hQ : Q ≤ 2 ^ 56) :
    (Q + 1) * (goldilocksPrime ^ 4 * goldilocksPrime ^ 4) * 2 ^ 128 ≤
      goldilocksPrime ^ 12 - (Q + 1) + 1 := by
  have hlit : (2 ^ 56 + 1) * (goldilocksPrime ^ 4 * goldilocksPrime ^ 4) * 2 ^ 128 ≤
      goldilocksPrime ^ 12 - (2 ^ 56 + 1) + 1 := by decide +kernel
  exact Nat.le_trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.add_le_add_right hQ 1)))
    (Nat.le_trans hlit (qipm_sub_antitone _ _ _ (Nat.add_le_add_right hQ 1)))

private theorem qipm_goldilocks_collision_arith (Q : Nat) (hQ : Q ≤ 2 ^ 56) :
    (Q + 2) * ((Q + 2) * (goldilocksPrime ^ 4 * goldilocksPrime ^ 4)) * 2 ^ 128 ≤
      goldilocksPrime ^ 12 - (Q + 2) + 1 := by
  have hlit : (2 ^ 56 + 2) * ((2 ^ 56 + 2) * (goldilocksPrime ^ 4 * goldilocksPrime ^ 4)) *
      2 ^ 128 ≤ goldilocksPrime ^ 12 - (2 ^ 56 + 2) + 1 := by decide +kernel
  have h2 : Q + 2 ≤ 2 ^ 56 + 2 := Nat.add_le_add_right hQ 2
  exact Nat.le_trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul h2 (Nat.mul_le_mul_right _ h2)))
    (Nat.le_trans hlit (qipm_sub_antitone _ _ _ h2))

/-- **Weighted feed-forward compression over an ideal permutation, preimage, classical two-way
    queries.** Against a lazily sampled permutation of the `p^12` Goldilocks states (NOT
    `poseidon2Perm12`), any adversary with `Q ≤ 2^56` forward-plus-inverse queries finds a
    preimage of any digest under the weighted feed-forward compression with probability at most
    `2^-128`. -/
theorem qipm_lazy_ideal_perm_weighted_feedforward_preimage_128_at_2pow56
    (A : TwoWayQipmAdv Poseidon2State12 Poseidon2State12) (y : Lane4) (Q : Nat)
    (hQ : Q ≤ 2 ^ 56) :
    atLeastBits 128 (qipmPreimageProb qipmGoldStates (fun _ => true) qipmWeightedComp y A Q
      (Nat.le_of_succ_le (qipmGoldStates_budget_ok Q hQ))) := by
  refine atLeastBits_of_le (qipm_two_way_preimage_bound qipmGoldStates qipmGoldStates_enum
    (fun _ => true) qipmWeightedComp y (qipmLaneAll.length * qipmLaneAll.length)
    (fun x => qipm_weighted_forward_fiber _ qipmLaneAll_enum x y)
    (fun z => qipm_weighted_inverse_fiber _ qipmLaneAll_enum z y) A Q _) ?_
  show (Q + 1) * (qipmLaneAll.length * qipmLaneAll.length) * 2 ^ 128 ≤
    qipmGoldStates.length - (Q + 1) + 1
  rw [qipmLaneAll_length, qipmGoldStates_length]
  exact qipm_goldilocks_preimage_arith Q hQ

/-- **Weighted feed-forward compression over an ideal permutation, collision, classical two-way
    queries, `Q ≤ 2^56`.** The permutation is lazily sampled, not `poseidon2Perm12`. -/
theorem qipm_lazy_ideal_perm_weighted_feedforward_collision_128_at_2pow56
    (A : TwoWayQipmAdv Poseidon2State12 (Poseidon2State12 × Poseidon2State12)) (Q : Nat)
    (hQ : Q ≤ 2 ^ 56) :
    atLeastBits 128 (qipmCollisionProb qipmGoldStates (fun _ => true) qipmWeightedComp A Q
      (qipmGoldStates_budget_ok Q hQ)) := by
  refine atLeastBits_of_le (qipm_two_way_collision_bound qipmGoldStates qipmGoldStates_enum
    (fun _ => true) qipmWeightedComp (qipmLaneAll.length * qipmLaneAll.length)
    (fun x g => qipm_weighted_forward_fiber _ qipmLaneAll_enum x g)
    (fun z g => qipm_weighted_inverse_fiber _ qipmLaneAll_enum z g) A Q _) ?_
  show (Q + 2) * ((Q + 2) * (qipmLaneAll.length * qipmLaneAll.length)) * 2 ^ 128 ≤
    qipmGoldStates.length - (Q + 2) + 1
  rw [qipmLaneAll_length, qipmGoldStates_length]
  exact qipm_goldilocks_collision_arith Q hQ

/-- **Rate-8 / capacity-4 truncation CICO over an ideal permutation, classical two-way queries,
    `Q ≤ 2^56`.** The permutation is lazily sampled. Inputs must carry the
    capacity lane `b2 = cap`; the digest is the truncation `b0` of the permutation output, with no
    feed-forward. -/
theorem qipm_lazy_ideal_perm_capacity4_truncation_cico_128_at_2pow56
    (A : TwoWayQipmAdv Poseidon2State12 Poseidon2State12) (cap y : Lane4) (Q : Nat)
    (hQ : Q ≤ 2 ^ 56) :
    atLeastBits 128 (qipmPreimageProb qipmGoldStates (fun x => decide (x.b2 = cap))
      qipmTruncComp y A Q (Nat.le_of_succ_le (qipmGoldStates_budget_ok Q hQ))) := by
  refine atLeastBits_of_le (qipm_two_way_preimage_bound qipmGoldStates qipmGoldStates_enum
    (fun x => decide (x.b2 = cap)) qipmTruncComp y (qipmLaneAll.length * qipmLaneAll.length)
    (fun x => qipm_trunc_forward_fiber _ qipmLaneAll_enum x y)
    (fun z => qipm_sponge_inverse_fiber _ qipmLaneAll_enum cap z y) A Q _) ?_
  show (Q + 1) * (qipmLaneAll.length * qipmLaneAll.length) * 2 ^ 128 ≤
    qipmGoldStates.length - (Q + 1) + 1
  rw [qipmLaneAll_length, qipmGoldStates_length]
  exact qipm_goldilocks_preimage_arith Q hQ

/-- Collisions of the capacity-constrained truncation (single-block sponge) over a lazily
    sampled permutation, `Q ≤ 2^56`. -/
theorem qipm_lazy_ideal_perm_capacity4_truncation_collision_128_at_2pow56
    (A : TwoWayQipmAdv Poseidon2State12 (Poseidon2State12 × Poseidon2State12)) (cap : Lane4)
    (Q : Nat) (hQ : Q ≤ 2 ^ 56) :
    atLeastBits 128 (qipmCollisionProb qipmGoldStates (fun x => decide (x.b2 = cap))
      qipmTruncComp A Q (qipmGoldStates_budget_ok Q hQ)) := by
  refine atLeastBits_of_le (qipm_two_way_collision_bound qipmGoldStates qipmGoldStates_enum
    (fun x => decide (x.b2 = cap)) qipmTruncComp (qipmLaneAll.length * qipmLaneAll.length)
    (fun x g => qipm_trunc_forward_fiber _ qipmLaneAll_enum x g)
    (fun z g => qipm_sponge_inverse_fiber _ qipmLaneAll_enum cap z g) A Q _) ?_
  show (Q + 2) * ((Q + 2) * (qipmLaneAll.length * qipmLaneAll.length)) * 2 ^ 128 ≤
    qipmGoldStates.length - (Q + 2) + 1
  rw [qipmLaneAll_length, qipmGoldStates_length]
  exact qipm_goldilocks_collision_arith Q hQ

/-! ## §8. Quantum two-way access as one XOR oracle, and the transposition O2H bound

A superposition query to `(π, π⁻¹)` with a direction qubit is one query to the function oracle
`qipmTwoWayOracle` on `Fin (n + n)`: index `i < n` is the forward query `π(i)`, index `n + j` is
the inverse query `π⁻¹(j)`. Every statement of the one-way QROM development about a FIXED oracle
therefore applies. What does not transfer is the resampling step: reprogramming one point of
this oracle leaves the set of permutations. The correct local move is a transposition, which
changes four points. No quantum CICO or collision bound for two-way access follows from this
section. -/

def qipmTwoWayOracle {n w : Nat} (f g : Fin n → BitVec w) : Fin (n + n) → BitVec w :=
  fun i => if h : i.val < n then f ⟨i.val, h⟩
    else g ⟨i.val - n, by have := i.isLt; omega⟩

/-- Two-way oracle of the permutation `π` with inverse `ρ`, answers encoded by `enc`. -/
def qipmPermOracle {n w : Nat} (π ρ : Fin n → Fin n) (enc : Fin n → BitVec w) :
    Fin (n + n) → BitVec w :=
  qipmTwoWayOracle (fun x => enc (π x)) (fun y => enc (ρ y))

/-- Transposition `(a b)`. -/
def qipmFinSwap {n : Nat} (a b x : Fin n) : Fin n :=
  if x = a then b else if x = b then a else x

theorem qipmFinSwap_of_ne {n : Nat} (a b x : Fin n) (h1 : ¬ x = a) (h2 : ¬ x = b) :
    qipmFinSwap a b x = x := by
  unfold qipmFinSwap
  simp only [h1, h2, ↓reduceIte]

theorem qipmFinSwap_involutive {n : Nat} (a b x : Fin n) :
    qipmFinSwap a b (qipmFinSwap a b x) = x := by
  by_cases h1 : x = a
  · have e1 : qipmFinSwap a b x = b := by unfold qipmFinSwap; simp only [h1, ↓reduceIte]
    rw [e1, h1]
    unfold qipmFinSwap
    by_cases hba : b = a
    · simp only [hba, ↓reduceIte]
    · simp only [hba, ↓reduceIte]
  · by_cases h2 : x = b
    · have hba : ¬ b = a := fun e => h1 (h2.trans e)
      have e1 : qipmFinSwap a b x = a := by
        unfold qipmFinSwap; rw [h2]; simp only [hba, ↓reduceIte]
      rw [e1, h2]
      unfold qipmFinSwap
      simp only [↓reduceIte]
    · rw [qipmFinSwap_of_ne a b x h1 h2, qipmFinSwap_of_ne a b x h1 h2]

/-- `π ∘ (a b)` is again a permutation, with inverse `(a b) ∘ ρ`. -/
theorem qipm_swapped_perm_inverse {n : Nat} (π ρ : Fin n → Fin n)
    (hL : ∀ x, ρ (π x) = x) (hR : ∀ y, π (ρ y) = y) (a b : Fin n) :
    (∀ x, qipmFinSwap a b (ρ (π (qipmFinSwap a b x))) = x) ∧
    (∀ y, π (qipmFinSwap a b (qipmFinSwap a b (ρ y))) = y) := by
  refine ⟨fun x => ?_, fun y => ?_⟩
  · rw [hL, qipmFinSwap_involutive]
  · rw [qipmFinSwap_involutive, hR]

/-- The four oracle points touched by the transposition `(a b)`: forward `a`, forward `b`,
    inverse `π a`, inverse `π b`. -/
def qipmSwapMark {n : Nat} (π : Fin n → Fin n) (a b : Fin n) : Fin (n + n) → Bool :=
  fun i => if h : i.val < n then
      decide ((⟨i.val, h⟩ : Fin n) = a) || decide ((⟨i.val, h⟩ : Fin n) = b)
    else
      decide ((⟨i.val - n, by have := i.isLt; omega⟩ : Fin n) = π a) ||
        decide ((⟨i.val - n, by have := i.isLt; omega⟩ : Fin n) = π b)

@[expose] def qipmFwdIdx {n : Nat} (a : Fin n) : Fin (n + n) :=
  ⟨a.val, Nat.lt_of_lt_of_le a.isLt (Nat.le_add_left n n)⟩

@[expose] def qipmInvIdx {n : Nat} (y : Fin n) : Fin (n + n) :=
  ⟨n + y.val, by have := y.isLt; omega⟩

private theorem qipm_or_false {p q : Bool} (h : (p || q) = false) : p = false ∧ q = false := by
  revert h; cases p <;> cases q <;> decide

private theorem qipm_or_true {p q : Bool} (h : (p || q) = true) : p = true ∨ q = true := by
  revert h; cases p <;> cases q <;> decide

/-- The two-way oracles of `π` and of `π ∘ (a b)` agree outside the four marked points. -/
theorem qipmPermOracle_swap_agree {n w : Nat} (π ρ : Fin n → Fin n)
    (hR : ∀ y, π (ρ y) = y) (enc : Fin n → BitVec w) (a b : Fin n) (i : Fin (n + n))
    (hm : qipmSwapMark π a b i = false) :
    qipmPermOracle (fun x => π (qipmFinSwap a b x)) (fun y => qipmFinSwap a b (ρ y)) enc i =
      qipmPermOracle π ρ enc i := by
  unfold qipmPermOracle qipmTwoWayOracle
  unfold qipmSwapMark at hm
  by_cases h : i.val < n
  · simp only [h, ↓reduceDIte] at hm ⊢
    have hh := qipm_or_false hm
    rw [qipmFinSwap_of_ne a b _ (of_decide_eq_false hh.1) (of_decide_eq_false hh.2)]
  · simp only [h, ↓reduceDIte] at hm ⊢
    have hh := qipm_or_false hm
    have h1 : ¬ ρ ⟨i.val - n, by have := i.isLt; omega⟩ = a := by
      intro e
      apply of_decide_eq_false hh.1
      rw [← e, hR]
    have h2 : ¬ ρ ⟨i.val - n, by have := i.isLt; omega⟩ = b := by
      intro e
      apply of_decide_eq_false hh.2
      rw [← e, hR]
    rw [qipmFinSwap_of_ne a b _ h1 h2]

theorem qipmSwapMark_cases {n : Nat} (π : Fin n → Fin n) (a b : Fin n) (i : Fin (n + n))
    (h : qipmSwapMark π a b i = true) :
    i = qipmFwdIdx a ∨ i = qipmFwdIdx b ∨ i = qipmInvIdx (π a) ∨ i = qipmInvIdx (π b) := by
  unfold qipmSwapMark at h
  by_cases hlt : i.val < n
  · simp only [hlt, ↓reduceDIte] at h
    cases qipm_or_true h with
    | inl e =>
      have hv : i.val = a.val := congrArg Fin.val (of_decide_eq_true e)
      exact Or.inl (Fin.ext hv)
    | inr e =>
      have hv : i.val = b.val := congrArg Fin.val (of_decide_eq_true e)
      exact Or.inr (Or.inl (Fin.ext hv))
  · simp only [hlt, ↓reduceDIte] at h
    cases qipm_or_true h with
    | inl e =>
      have hv : i.val - n = (π a).val := congrArg Fin.val (of_decide_eq_true e)
      exact Or.inr (Or.inr (Or.inl (Fin.ext (by show i.val = n + (π a).val; omega))))
    | inr e =>
      have hv : i.val - n = (π b).val := congrArg Fin.val (of_decide_eq_true e)
      exact Or.inr (Or.inr (Or.inr (Fin.ext (by show i.val = n + (π b).val; omega))))

/-- At most four of the `2 n` oracle points are marked. -/
theorem qipmSwapMark_card_le_four {n : Nat} (π : Fin n → Fin n) (a b : Fin n) :
    qsum (n + n) (fun i => if qipmSwapMark π a b i = true then 1 else 0) ≤ 4 := by
  have hpt : ∀ i : Fin (n + n), (if qipmSwapMark π a b i = true then 1 else 0) ≤
      (if i = qipmFwdIdx a then 1 else 0) + (if i = qipmFwdIdx b then 1 else 0) +
        (if i = qipmInvIdx (π a) then 1 else 0) + (if i = qipmInvIdx (π b) then 1 else 0) := by
    intro i
    cases hm : qipmSwapMark π a b i
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_le]
    · simp only [↓reduceIte]
      rcases qipmSwapMark_cases π a b i hm with e | e | e | e
      · have h1 : (if i = qipmFwdIdx a then 1 else 0) = 1 := by simp only [e, ↓reduceIte]
        omega
      · have h1 : (if i = qipmFwdIdx b then 1 else 0) = 1 := by simp only [e, ↓reduceIte]
        omega
      · have h1 : (if i = qipmInvIdx (π a) then 1 else 0) = 1 := by simp only [e, ↓reduceIte]
        omega
      · have h1 : (if i = qipmInvIdx (π b) then 1 else 0) = 1 := by simp only [e, ↓reduceIte]
        omega
  refine Nat.le_trans (qsum_le_qsum hpt) ?_
  rw [qsum_add, qsum_add, qsum_add, qsum_eq_indicator, qsum_eq_indicator, qsum_eq_indicator,
    qsum_eq_indicator]
  exact Nat.le_refl 4

/-- **Two-way transposition O2H.** For any `q`-query quantum adversary with superposition access
    to both directions, replacing `π` by `π ∘ (a b)` disturbs the final state by at most
    `4 q ∑_t suffixScale(t) * (query mass of step t on the four touched points)`, the masses
    being those of the run against the unmodified `π`. -/
theorem qipm_two_way_swap_o2h {n w cardAnc q : Nat} (A : QuantumAdv (n + n) w cardAnc q)
    (π ρ : Fin n → Fin n) (hR : ∀ y, π (ρ y) = y) (enc : Fin n → BitVec w) (a b : Fin n) :
    QVec.stateNormSq
        ((runQuantumAdv A (qipmPermOracle (fun x => π (qipmFinSwap a b x))
          (fun y => qipmFinSwap a b (ρ y)) enc)).sub
          (runQuantumAdv A (qipmPermOracle π ρ enc))) ≤
      4 * q * qsum q (fun t =>
        suffixScale A t.1 (Nat.le_of_lt t.2) *
          QVec.queryMassOn (qipmSwapMark π a b)
            (advStateAt A (qipmPermOracle π ρ enc) t.1 (Nat.le_of_lt t.2))) :=
  qrom_o2h_telescoping_disturbance_le A _ _ (qipmSwapMark π a b)
    (fun i hm => qipmPermOracle_swap_agree π ρ hR enc a b i hm)

/-! ## §9. Arithmetic on quantum bound SHAPES for a 256-bit digest

These are not security theorems for two-way quantum adversaries. They record which generic
quantum query-complexity shapes can meet a `2^-128` budget at all. -/

/-- Grover / preimage shape `(Q + 1)^2 / 2^digestBits`. -/
@[expose] def qipmGroverShape (Q digestBits : Nat) : RatBound :=
  ⟨(Q + 1) ^ 2, 2 ^ digestBits, Nat.two_pow_pos digestBits⟩

/-- BHT / collision shape `(Q + 1)^3 / 2^digestBits`. -/
@[expose] def qipmBhtShape (Q digestBits : Nat) : RatBound :=
  ⟨(Q + 1) ^ 3, 2 ^ digestBits, Nat.two_pow_pos digestBits⟩

theorem qipm_grover_shape_256_at_2pow56 (Q : Nat) (hQ : Q ≤ 2 ^ 56) :
    atLeastBits 128 (qipmGroverShape Q 256) := by
  show (Q + 1) ^ 2 * 2 ^ 128 ≤ 2 ^ 256
  have hlit : (2 ^ 56 + 1) ^ 2 * 2 ^ 128 ≤ 2 ^ 256 := by decide +kernel
  exact Nat.le_trans
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.add_le_add_right hQ 1) 2)) hlit

theorem qipm_bht_shape_256_up_to_2pow42 (Q : Nat) (hQ : Q + 1 ≤ 2 ^ 42) :
    atLeastBits 128 (qipmBhtShape Q 256) := by
  show (Q + 1) ^ 3 * 2 ^ 128 ≤ 2 ^ 256
  have hlit : (2 ^ 42) ^ 3 * 2 ^ 128 ≤ 2 ^ 256 := by decide +kernel
  exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hQ 3)) hlit

#verify_constructive
  Qsag.qipmWeightedCompress_poseidon2Perm12
  Qsag.qipmFeedForward_eq_poseidon2WeightedFeedForward
  Qsag.qipmWeight_total
  Qsag.qipmWeight_le_fall
  Qsag.qipm_bad_weight_le
  Qsag.qipm_two_way_bad_event_bound
  Qsag.qipm_two_way_preimage_bound
  Qsag.qipm_two_way_collision_bound
  Qsag.qipm_unweighted_inverse_attack_total
  Qsag.poseidon2_unweighted_truncation_inverted
  Qsag.poseidon2_unweighted_truncation_collides
  Qsag.qipmGoldStates_enum
  Qsag.qipmGoldStates_length
  Qsag.qipm_weighted_forward_fiber
  Qsag.qipm_weighted_inverse_fiber
  Qsag.qipm_trunc_forward_fiber
  Qsag.qipm_capacity_fiber
  Qsag.qipm_sponge_inverse_fiber
  Qsag.qipm_unprotected_inverse_fiber_full
  Qsag.qipm_lazy_ideal_perm_weighted_feedforward_preimage_128_at_2pow56
  Qsag.qipm_lazy_ideal_perm_weighted_feedforward_collision_128_at_2pow56
  Qsag.qipm_lazy_ideal_perm_capacity4_truncation_cico_128_at_2pow56
  Qsag.qipm_lazy_ideal_perm_capacity4_truncation_collision_128_at_2pow56
  Qsag.qipm_swapped_perm_inverse
  Qsag.qipmPermOracle_swap_agree
  Qsag.qipmSwapMark_card_le_four
  Qsag.qipm_two_way_swap_o2h
  Qsag.qipm_grover_shape_256_at_2pow56
  Qsag.qipm_bht_shape_256_up_to_2pow42

end Qsag
end
