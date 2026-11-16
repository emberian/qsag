module
/-
# Qsag.Oracle.FrozenChallengeGame — freeze, then sample, then check

A public-coin check is only as strong as the order in which things are fixed. This module
models that order as a transition system and counts, over the whole challenge space, the
challenge vectors on which a frozen commitment is accepted.

1. Counting (`countIf`, `sumOver`, `vectors`, `extendAll`, `enumBelow`): the sample space of
   `t` independent uniform draws from a list `xs` is the list `vectors xs t` of length
   `xs.length ^ t`; probabilities are counts over that list. Draws are uniform over list
   positions, so a duplicate-free `xs` is a uniform draw from its elements.
2. The machine (`Phase`, `State`, `Move`, `step`, `run`): `freeze c`, then `sample chis`, then
   `check`. `step` refuses a sample before the freeze, a second freeze, a challenge vector whose
   length is not `cfg.reps`, and every challenge vector when `cfg.reps = 0` (so `chis = []` is
   never accepted). `run_verdict_shape` shows that a run that reaches a verdict is exactly
   `[freeze c, sample chis, check]`.
3. `frozen_win_count_eq` / `frozen_win_count_le`: the adversary is a function from the
   challenges revealed so far to a commitment; in this machine it is called on the empty view.
   The number of accepted challenge vectors is the product over repetitions of the per-repetition
   pass counts, hence at most `k ^ reps` when each is at most `k`.
4. `grinding_win_count_le`: an adaptive adversary that tries `Q` commitments, each against a
   fresh independent challenge vector (a lazily sampled classical random oracle queried at `Q`
   distinct points), wins on at most `Q * k ^ reps * M ^ Q / M` of the `M ^ Q` oracle tables,
   `M = xs.length ^ reps`. This is a classical union bound; nothing here is a QROM statement.
5. `swapped_win_count_all`: in the machine with the first two phases exchanged
   (`stepSwapped`: sample, then freeze, then check) an adversary that can fit a commitment to a
   known challenge vector is accepted on every challenge vector.

The per-repetition check `cfg.check c j x` is a parameter. Nothing is assumed about how the
commitment is bound: `freeze c` hands the machine the value itself, so a hiding or binding
commitment scheme and its failure probability are outside this model.
-/
public import Qsag.Tactic.Prelude

public section
namespace Qsag.FrozenChallenge
set_option autoImplicit false

/-! ## 1. Counting over finite sample spaces -/

/-- Number of entries of the list, with multiplicity, on which `p` holds. -/
@[expose] def countIf {α : Type} (p : α → Bool) : List α → Nat
  | [] => 0
  | x :: xs => (if p x then 1 else 0) + countIf p xs

@[expose] def sumOver {α : Type} (f : α → Nat) : List α → Nat
  | [] => 0
  | x :: xs => f x + sumOver f xs

/-- Every `x :: v` with `x` from the first list and `v` from the second. -/
@[expose] def extendAll {α : Type} : List α → List (List α) → List (List α)
  | [], _ => []
  | x :: xs, vs => vs.map (fun v => x :: v) ++ extendAll xs vs

/-- All vectors of `t` draws from `xs`. -/
@[expose] def vectors {α : Type} (xs : List α) : Nat → List (List α)
  | 0 => [[]]
  | t + 1 => extendAll xs (vectors xs t)

/-- `[f (n-1), …, f 0]`. -/
@[expose] def enumBelow {α : Type} (f : Nat → α) : Nat → List α
  | 0 => []
  | n + 1 => f n :: enumBelow f n

theorem countIf_append {α : Type} (p : α → Bool) :
    ∀ xs ys : List α, countIf p (xs ++ ys) = countIf p xs + countIf p ys
  | [], ys => by rw [List.nil_append]; exact (Nat.zero_add _).symm
  | x :: xs, ys => by
    rw [List.cons_append]
    show _ + countIf p (xs ++ ys) = _ + countIf p xs + countIf p ys
    rw [countIf_append p xs ys, Nat.add_assoc]

theorem countIf_map {α β : Type} (p : β → Bool) (f : α → β) :
    ∀ xs : List α, countIf p (xs.map f) = countIf (fun x => p (f x)) xs
  | [] => by rfl
  | x :: xs => by
    rw [List.map_cons]
    show _ + countIf p (xs.map f) = _ + countIf (fun x => p (f x)) xs
    rw [countIf_map p f xs]

theorem countIf_false {α : Type} : ∀ xs : List α, countIf (fun _ => false) xs = 0
  | [] => by rfl
  | _ :: xs => by
    show 0 + countIf (fun _ => false) xs = 0
    rw [countIf_false xs]

theorem countIf_true {α : Type} : ∀ xs : List α, countIf (fun _ => true) xs = xs.length
  | [] => by rfl
  | _ :: xs => by
    show 1 + countIf (fun _ => true) xs = xs.length + 1
    rw [countIf_true xs, Nat.add_comm]

theorem countIf_le_length {α : Type} (p : α → Bool) : ∀ xs : List α, countIf p xs ≤ xs.length
  | [] => Nat.le_refl 0
  | x :: xs => by
    show (if p x then 1 else 0) + countIf p xs ≤ xs.length + 1
    have ih := countIf_le_length p xs
    cases p x
    · show 0 + countIf p xs ≤ xs.length + 1
      rw [Nat.zero_add]; exact Nat.le_succ_of_le ih
    · show 1 + countIf p xs ≤ xs.length + 1
      rw [Nat.add_comm]; exact Nat.succ_le_succ ih

theorem countIf_and_const {α : Type} (b : Bool) (q : α → Bool) (xs : List α) :
    countIf (fun x => b && q x) xs = if b then countIf q xs else 0 := by
  cases b
  · show countIf (fun _ => false) xs = 0
    exact countIf_false xs
  · rfl

theorem countIf_or_const_le {α : Type} (b : Bool) (q : α → Bool) (xs : List α) :
    countIf (fun x => b || q x) xs ≤ (if b then xs.length else 0) + countIf q xs := by
  cases b
  · show countIf q xs ≤ 0 + countIf q xs
    rw [Nat.zero_add]; exact Nat.le_refl _
  · show countIf (fun _ => true) xs ≤ xs.length + countIf q xs
    rw [countIf_true]; exact Nat.le_add_right _ _

theorem countIf_eq_zero_of_forall {α : Type} {p : α → Bool} :
    ∀ {xs : List α}, (∀ x ∈ xs, p x = false) → countIf p xs = 0
  | [], _ => by rfl
  | x :: xs, h => by
    have hx : p x = false := h x (.head xs)
    have ih : countIf p xs = 0 := countIf_eq_zero_of_forall (fun y hy => h y (.tail x hy))
    show (if p x then 1 else 0) + countIf p xs = 0
    rw [hx, ih]; rfl

/-- A predicate with at most one satisfying value holds on at most one entry of a
duplicate-free list. -/
theorem countIf_le_one_of_unique {α : Type} {p : α → Bool} :
    ∀ {xs : List α}, xs.Nodup → (∀ x y, p x = true → p y = true → x = y) → countIf p xs ≤ 1
  | [], _, _ => Nat.zero_le 1
  | x :: xs, hnd, hu => by
    have hnd' := List.nodup_cons.mp hnd
    show (if p x then 1 else 0) + countIf p xs ≤ 1
    cases hpx : p x with
    | false =>
      show 0 + countIf p xs ≤ 1
      rw [Nat.zero_add]; exact countIf_le_one_of_unique hnd'.2 hu
    | true =>
      have hz : countIf p xs = 0 := countIf_eq_zero_of_forall (fun y hy => by
        cases hpy : p y with
        | false => rfl
        | true =>
          have e : x = y := hu x y hpx hpy
          exact absurd (e ▸ hy) hnd'.1)
      show 1 + countIf p xs ≤ 1
      rw [hz]; exact Nat.le_refl 1

theorem sumOver_append {α : Type} (f : α → Nat) :
    ∀ xs ys : List α, sumOver f (xs ++ ys) = sumOver f xs + sumOver f ys
  | [], ys => by rw [List.nil_append]; exact (Nat.zero_add _).symm
  | x :: xs, ys => by
    rw [List.cons_append]
    show f x + sumOver f (xs ++ ys) = f x + sumOver f xs + sumOver f ys
    rw [sumOver_append f xs ys, Nat.add_assoc]

theorem sumOver_map {α β : Type} (g : β → Nat) (f : α → β) :
    ∀ xs : List α, sumOver g (xs.map f) = sumOver (fun x => g (f x)) xs
  | [] => by rfl
  | x :: xs => by
    rw [List.map_cons]
    show g (f x) + sumOver g (xs.map f) = g (f x) + sumOver (fun x => g (f x)) xs
    rw [sumOver_map g f xs]

theorem sumOver_le {α : Type} {f g : α → Nat} (h : ∀ x, f x ≤ g x) :
    ∀ xs : List α, sumOver f xs ≤ sumOver g xs
  | [] => Nat.le_refl 0
  | x :: xs => Nat.add_le_add (h x) (sumOver_le h xs)

theorem sumOver_add {α : Type} (f g : α → Nat) :
    ∀ xs : List α, sumOver (fun x => f x + g x) xs = sumOver f xs + sumOver g xs
  | [] => by rfl
  | x :: xs => by
    show f x + g x + sumOver (fun x => f x + g x) xs = f x + sumOver f xs + (g x + sumOver g xs)
    rw [sumOver_add f g xs, Nat.add_assoc, Nat.add_assoc, Nat.add_left_comm (g x)]

theorem sumOver_mul_right {α : Type} (f : α → Nat) (c : Nat) :
    ∀ xs : List α, sumOver (fun x => f x * c) xs = sumOver f xs * c
  | [] => by show 0 = 0 * c; rw [Nat.zero_mul]
  | x :: xs => by
    show f x * c + sumOver (fun x => f x * c) xs = (f x + sumOver f xs) * c
    rw [sumOver_mul_right f c xs, Nat.add_mul]

theorem sumOver_mul_left {α : Type} (c : Nat) (f : α → Nat) :
    ∀ xs : List α, sumOver (fun x => c * f x) xs = c * sumOver f xs
  | [] => by rfl
  | x :: xs => by
    show c * f x + sumOver (fun x => c * f x) xs = c * (f x + sumOver f xs)
    rw [sumOver_mul_left c f xs, Nat.mul_add]

theorem sumOver_const {α : Type} (c : Nat) : ∀ xs : List α, sumOver (fun _ => c) xs = xs.length * c
  | [] => by show 0 = 0 * c; rw [Nat.zero_mul]
  | _ :: xs => by
    show c + sumOver (fun _ => c) xs = (xs.length + 1) * c
    rw [sumOver_const c xs, Nat.add_mul, Nat.one_mul, Nat.add_comm]

theorem sumOver_ite_const {α : Type} (p : α → Bool) (c : Nat) :
    ∀ xs : List α, sumOver (fun x => if p x then c else 0) xs = countIf p xs * c
  | [] => by show 0 = 0 * c; rw [Nat.zero_mul]
  | x :: xs => by
    show (if p x then c else 0) + sumOver (fun x => if p x then c else 0) xs =
      ((if p x then 1 else 0) + countIf p xs) * c
    rw [sumOver_ite_const p c xs, Nat.add_mul]
    cases p x
    · show 0 + _ = 0 * c + _
      rw [Nat.zero_mul]
    · show c + _ = 1 * c + _
      rw [Nat.one_mul]

theorem countIf_extendAll {α : Type} (p : List α → Bool) (vs : List (List α)) :
    ∀ ys : List α,
      countIf p (extendAll ys vs) = sumOver (fun x => countIf (fun v => p (x :: v)) vs) ys
  | [] => by rfl
  | y :: ys => by
    show countIf p (vs.map (fun v => y :: v) ++ extendAll ys vs) =
      countIf (fun v => p (y :: v)) vs + sumOver (fun x => countIf (fun v => p (x :: v)) vs) ys
    rw [countIf_append, countIf_map, countIf_extendAll p vs ys]

theorem sumOver_extendAll {α : Type} (g : List α → Nat) (vs : List (List α)) :
    ∀ ys : List α,
      sumOver g (extendAll ys vs) = sumOver (fun x => sumOver (fun v => g (x :: v)) vs) ys
  | [] => by rfl
  | y :: ys => by
    show sumOver g (vs.map (fun v => y :: v) ++ extendAll ys vs) =
      sumOver (fun v => g (y :: v)) vs + sumOver (fun x => sumOver (fun v => g (x :: v)) vs) ys
    rw [sumOver_append, sumOver_map, sumOver_extendAll g vs ys]

theorem length_extendAll {α : Type} (vs : List (List α)) :
    ∀ ys : List α, (extendAll ys vs).length = ys.length * vs.length
  | [] => by show 0 = 0 * vs.length; rw [Nat.zero_mul]
  | y :: ys => by
    show (vs.map (fun v => y :: v) ++ extendAll ys vs).length = (ys.length + 1) * vs.length
    rw [List.length_append, List.length_map, length_extendAll vs ys, Nat.add_mul, Nat.one_mul,
      Nat.add_comm]

theorem length_vectors {α : Type} (xs : List α) : ∀ t : Nat, (vectors xs t).length = xs.length ^ t
  | 0 => by rfl
  | t + 1 => by
    show (extendAll xs (vectors xs t)).length = xs.length ^ (t + 1)
    rw [length_extendAll, length_vectors xs t, Nat.pow_succ, Nat.mul_comm]

/-- Predicates that agree on vectors of the right length have the same count. -/
theorem countIf_vectors_congr {α : Type} (xs : List α) :
    ∀ (t : Nat) (p q : List α → Bool), (∀ v, v.length = t → p v = q v) →
      countIf p (vectors xs t) = countIf q (vectors xs t)
  | 0, p, q, h => by
    show (if p [] then 1 else 0) + 0 = (if q [] then 1 else 0) + 0
    rw [h [] rfl]
  | t + 1, p, q, h => by
    show countIf p (extendAll xs (vectors xs t)) = countIf q (extendAll xs (vectors xs t))
    rw [countIf_extendAll, countIf_extendAll]
    have e : (fun x => countIf (fun v => p (x :: v)) (vectors xs t)) =
        (fun x => countIf (fun v => q (x :: v)) (vectors xs t)) := by
      funext x
      exact countIf_vectors_congr xs t _ _ (fun v hv => h (x :: v) (by rw [List.length_cons, hv]))
    rw [e]

theorem length_enumBelow {α : Type} (f : Nat → α) : ∀ n : Nat, (enumBelow f n).length = n
  | 0 => by rfl
  | n + 1 => by
    show (enumBelow f n).length + 1 = n + 1
    rw [length_enumBelow f n]

theorem mem_enumBelow {α : Type} {f : Nat → α} :
    ∀ {n : Nat} {y : α}, y ∈ enumBelow f n → ∃ i, i < n ∧ y = f i
  | 0, _, h => nomatch h
  | n + 1, y, h => by
    have h' : y ∈ f n :: enumBelow f n := h
    cases h' with
    | head => exact ⟨n, Nat.lt_succ_self n, rfl⟩
    | tail _ ht =>
      obtain ⟨i, hi, e⟩ := mem_enumBelow ht
      exact ⟨i, Nat.lt_succ_of_lt hi, e⟩

theorem enumBelow_nodup {α : Type} {f : Nat → α} :
    ∀ {n : Nat}, (∀ i j, i < n → j < n → f i = f j → i = j) → (enumBelow f n).Nodup
  | 0, _ => List.nodup_nil
  | n + 1, h => by
    show (f n :: enumBelow f n).Nodup
    refine List.nodup_cons.mpr ⟨fun hm => ?_, enumBelow_nodup (fun i j hi hj =>
      h i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj))⟩
    obtain ⟨i, hi, e⟩ := mem_enumBelow hm
    have hEq : n = i := h n i (Nat.lt_succ_self n) (Nat.lt_succ_of_lt hi) e
    exact Nat.lt_irrefl i (hEq ▸ hi)

/-! ## 2. Repetitions -/

/-- Repetition `j, j+1, …` of the check, one challenge each. -/
def allReps {α : Type} (check : Nat → α → Bool) : Nat → List α → Bool
  | _, [] => true
  | j, x :: v => check j x && allReps check (j + 1) v

/-- Product over repetitions `j, …, j+t-1` of the number of passing challenges. -/
def repProduct {α : Type} (xs : List α) (check : Nat → α → Bool) : Nat → Nat → Nat
  | _, 0 => 1
  | j, t + 1 => countIf (check j) xs * repProduct xs check (j + 1) t

theorem allReps_nil {α : Type} (check : Nat → α → Bool) (j : Nat) : allReps check j [] = true := by
  rfl

theorem allReps_cons {α : Type} (check : Nat → α → Bool) (j : Nat) (x : α) (v : List α) :
    allReps check j (x :: v) = (check j x && allReps check (j + 1) v) := by rfl

/-- A challenge vector passes when its `j`-th entry passes repetition `i + j` for every `j`. -/
theorem allReps_of_getElem {α : Type} (check : Nat → α → Bool) :
    ∀ (v : List α) (i : Nat), (∀ j x, v[j]? = some x → check (i + j) x = true) →
      allReps check i v = true
  | [], _, _ => by rfl
  | x :: v, i, h => by
    have h0 : check i x = true := h 0 x (by rfl)
    have ih : allReps check (i + 1) v = true :=
      allReps_of_getElem check v (i + 1) (fun j y hy => by
        have hj := h (j + 1) y (by rw [List.getElem?_cons_succ]; exact hy)
        rw [show i + (j + 1) = i + 1 + j from Nat.add_right_comm i j 1] at hj
        exact hj)
    show (check i x && allReps check (i + 1) v) = true
    rw [h0, ih]; rfl

/-- The number of accepted challenge vectors is the product of the per-repetition counts. -/
theorem countIf_allReps_vectors {α : Type} (xs : List α) (check : Nat → α → Bool) :
    ∀ (t j : Nat), countIf (allReps check j) (vectors xs t) = repProduct xs check j t
  | 0, _ => by rfl
  | t + 1, j => by
    show countIf (allReps check j) (extendAll xs (vectors xs t)) =
      countIf (check j) xs * repProduct xs check (j + 1) t
    rw [countIf_extendAll]
    have e : (fun x => countIf (fun v => allReps check j (x :: v)) (vectors xs t)) =
        (fun x => if check j x then repProduct xs check (j + 1) t else 0) := by
      funext x
      show countIf (fun v => check j x && allReps check (j + 1) v) (vectors xs t) = _
      rw [countIf_and_const, countIf_allReps_vectors xs check t (j + 1)]
    rw [e, sumOver_ite_const]

theorem repProduct_le_pow {α : Type} (xs : List α) (check : Nat → α → Bool) (k : Nat)
    (hk : ∀ j, countIf (check j) xs ≤ k) : ∀ (t j : Nat), repProduct xs check j t ≤ k ^ t
  | 0, _ => Nat.le_refl 1
  | t + 1, j => by
    show countIf (check j) xs * repProduct xs check (j + 1) t ≤ k ^ (t + 1)
    rw [Nat.pow_succ, Nat.mul_comm (k ^ t) k]
    exact Nat.mul_le_mul (hk j) (repProduct_le_pow xs check k hk t (j + 1))

/-! ## 3. The freeze / sample / check machine -/

inductive Phase where
  | awaitFreeze
  | awaitSample
  | awaitCheck
  | done
  deriving DecidableEq, Repr

structure Config (C X : Type) where
  /-- Number of independent challenges; the machine refuses to sample when this is zero. -/
  reps : Nat
  /-- `check c j x`: repetition `j` of commitment `c` passes under challenge `x`. -/
  check : C → Nat → X → Bool

structure State (C X : Type) where
  phase : Phase
  frozen : Option C
  chis : List X
  verdict : Option Bool

inductive Move (C X : Type) where
  | freeze (c : C)
  | sample (chis : List X)
  | check

def State.init {C X : Type} : State C X := ⟨.awaitFreeze, none, [], none⟩

/-- Initial state of the machine with the first two phases exchanged. -/
def State.initSwapped {C X : Type} : State C X := ⟨.awaitSample, none, [], none⟩

/-- Freeze, then sample, then check. -/
def step {C X : Type} (cfg : Config C X) (s : State C X) : Move C X → Option (State C X)
  | .freeze c =>
    match s.phase with
    | .awaitFreeze => some ⟨.awaitSample, some c, [], none⟩
    | _ => none
  | .sample chis =>
    match s.phase with
    | .awaitSample =>
      if 1 ≤ cfg.reps ∧ chis.length = cfg.reps then some ⟨.awaitCheck, s.frozen, chis, none⟩
      else none
    | _ => none
  | .check =>
    match s.phase, s.frozen with
    | .awaitCheck, some c => some ⟨.done, some c, s.chis, some (allReps (cfg.check c) 0 s.chis)⟩
    | _, _ => none

def run {C X : Type} (cfg : Config C X) : State C X → List (Move C X) → Option (State C X)
  | s, [] => some s
  | s, m :: ms =>
    match step cfg s m with
    | none => none
    | some s' => run cfg s' ms

/-- The same machine with the order of the first two phases exchanged: sample, then freeze. -/
def stepSwapped {C X : Type} (cfg : Config C X) (s : State C X) : Move C X → Option (State C X)
  | .sample chis =>
    match s.phase, s.frozen with
    | .awaitSample, none =>
      if 1 ≤ cfg.reps ∧ chis.length = cfg.reps then some ⟨.awaitFreeze, none, chis, none⟩
      else none
    | _, _ => none
  | .freeze c =>
    match s.phase with
    | .awaitFreeze => some ⟨.awaitCheck, some c, s.chis, none⟩
    | _ => none
  | .check =>
    match s.phase, s.frozen with
    | .awaitCheck, some c => some ⟨.done, some c, s.chis, some (allReps (cfg.check c) 0 s.chis)⟩
    | _, _ => none

/-- An adversary chooses its commitment from the challenges that are public when it commits. -/
structure Adversary (C X : Type) where
  commit : List X → C

def accepted {C X : Type} : Option (State C X) → Bool
  | some s => match s.verdict with
    | some true => true
    | _ => false
  | none => false

/-- One execution in the freeze-first order: the adversary commits on the initial (empty)
view, the challenges are then sampled, then the check runs. -/
def playFrozen {C X : Type} (cfg : Config C X) (A : Adversary C X) (chis : List X) :
    Option (State C X) :=
  run cfg State.init [.freeze (A.commit (State.init (C := C) (X := X)).chis), .sample chis, .check]

def frozenWins {C X : Type} (cfg : Config C X) (A : Adversary C X) (chis : List X) : Bool :=
  accepted (playFrozen cfg A chis)

/-- One execution in the exchanged order: the adversary commits after seeing the challenges. -/
def playSwapped {C X : Type} (cfg : Config C X) (A : Adversary C X) (chis : List X) :
    Option (State C X) :=
  match stepSwapped cfg State.initSwapped (.sample chis) with
  | none => none
  | some s1 =>
    match stepSwapped cfg s1 (.freeze (A.commit s1.chis)) with
    | none => none
    | some s2 => stepSwapped cfg s2 .check

def swappedWins {C X : Type} (cfg : Config C X) (A : Adversary C X) (chis : List X) : Bool :=
  accepted (playSwapped cfg A chis)

/-! ### Order enforcement -/

theorem step_sample_before_freeze_rejected {C X : Type} (cfg : Config C X) (chis : List X) :
    step cfg State.init (.sample chis) = none := by rfl

theorem step_check_before_sample_rejected {C X : Type} (cfg : Config C X) (c : C) :
    run cfg State.init [.freeze c, .check] = none := by rfl

theorem step_refreeze_rejected {C X : Type} (cfg : Config C X) (c c' : C) :
    run cfg State.init [.freeze c, .freeze c'] = none := by rfl

/-- The empty challenge vector is refused in every state and for every configuration. -/
theorem step_empty_sample_rejected {C X : Type} (cfg : Config C X) (s : State C X) :
    step cfg s (.sample []) = none := by
  rcases s with ⟨ph, fr, ch, vd⟩
  cases ph
  · rfl
  · show (if 1 ≤ cfg.reps ∧ ([] : List X).length = cfg.reps then _ else none) = none
    split
    · rename_i h
      have h0 : 0 = cfg.reps := h.2
      exact absurd h.1 (by rw [← h0]; exact Nat.not_succ_le_zero 0)
    · rfl
  · rfl
  · rfl

theorem step_wrong_length_rejected {C X : Type} (cfg : Config C X) (s : State C X) (chis : List X)
    (h : chis.length ≠ cfg.reps) : step cfg s (.sample chis) = none := by
  rcases s with ⟨ph, fr, ch, vd⟩
  cases ph
  · rfl
  · show (if 1 ≤ cfg.reps ∧ chis.length = cfg.reps then _ else none) = none
    split
    · rename_i hc
      exact absurd hc.2 h
    · rfl
  · rfl
  · rfl

/-- What a challenge vector must satisfy to be sampled. -/
def sampleOk {C X : Type} (cfg : Config C X) (chis : List X) : Bool :=
  decide (1 ≤ cfg.reps ∧ chis.length = cfg.reps)

theorem frozenWins_eq {C X : Type} (cfg : Config C X) (A : Adversary C X) (chis : List X) :
    frozenWins cfg A chis = (sampleOk cfg chis && allReps (cfg.check (A.commit [])) 0 chis) := by
  unfold frozenWins playFrozen sampleOk
  by_cases h : 1 ≤ cfg.reps ∧ chis.length = cfg.reps
  · cases hb : allReps (cfg.check (A.commit [])) 0 chis <;>
      simp [run, step, State.init, accepted, h, hb]
  · simp [run, step, State.init, accepted, h]

theorem swappedWins_eq {C X : Type} (cfg : Config C X) (A : Adversary C X) (chis : List X) :
    swappedWins cfg A chis =
      (sampleOk cfg chis && allReps (cfg.check (A.commit chis)) 0 chis) := by
  unfold swappedWins playSwapped sampleOk
  by_cases h : 1 ≤ cfg.reps ∧ chis.length = cfg.reps
  · cases hb : allReps (cfg.check (A.commit chis)) 0 chis <;>
      simp [stepSwapped, State.initSwapped, accepted, h, hb]
  · simp [stepSwapped, State.initSwapped, accepted, h]

theorem frozenWins_of_allReps {C X : Type} (cfg : Config C X) (A : Adversary C X) (chis : List X)
    (h1 : 1 ≤ cfg.reps) (hLen : chis.length = cfg.reps)
    (hAll : allReps (cfg.check (A.commit [])) 0 chis = true) : frozenWins cfg A chis = true := by
  rw [frozenWins_eq, hAll]
  have hs : sampleOk cfg chis = true := decide_eq_true ⟨h1, hLen⟩
  rw [hs]; rfl

/-- A configuration with no repetition accepts nothing. -/
theorem frozenWins_zero_reps {C X : Type} (cfg : Config C X) (A : Adversary C X) (chis : List X)
    (h0 : cfg.reps = 0) : frozenWins cfg A chis = false := by
  rw [frozenWins_eq]
  have hs : sampleOk cfg chis = false :=
    decide_eq_false (fun hc => Nat.not_succ_le_zero 0 (by have h := hc.1; rw [h0] at h; exact h))
  rw [hs]; rfl

/-- A run from the initial state that carries a verdict is `freeze`, `sample`, `check` in that
order, with a challenge vector of the configured nonzero length, and the verdict is the check
of the commitment that was frozen first. -/
theorem run_verdict_shape {C X : Type} (cfg : Config C X) (ms : List (Move C X)) (s : State C X)
    (b : Bool) (hRun : run cfg State.init ms = some s) (hV : s.verdict = some b) :
    ∃ (c : C) (chis : List X), ms = [.freeze c, .sample chis, .check] ∧ 1 ≤ cfg.reps ∧
      chis.length = cfg.reps ∧ b = allReps (cfg.check c) 0 chis := by
  match ms, hRun with
  | [], hRun =>
    simp [run, State.init] at hRun
    subst hRun
    simp at hV
  | .sample _ :: _, hRun => simp [run, step, State.init] at hRun
  | .check :: _, hRun => simp [run, step, State.init] at hRun
  | [.freeze c], hRun =>
    simp [run, step, State.init] at hRun
    subst hRun
    simp at hV
  | .freeze c :: .freeze _ :: _, hRun => simp [run, step, State.init] at hRun
  | .freeze c :: .check :: _, hRun => simp [run, step, State.init] at hRun
  | .freeze c :: .sample chis :: rest, hRun =>
    by_cases h : 1 ≤ cfg.reps ∧ chis.length = cfg.reps
    · match rest, hRun with
      | [], hRun =>
        simp [run, step, State.init, h] at hRun
        subst hRun
        simp at hV
      | .freeze _ :: _, hRun => simp [run, step, State.init, h] at hRun
      | .sample _ :: _, hRun => simp [run, step, State.init, h] at hRun
      | [.check], hRun =>
        simp [run, step, State.init, h] at hRun
        subst hRun
        simp at hV
        exact ⟨c, chis, rfl, h.1, h.2, hV.symm⟩
      | .check :: .freeze _ :: _, hRun => simp [run, step, State.init, h] at hRun
      | .check :: .sample _ :: _, hRun => simp [run, step, State.init, h] at hRun
      | .check :: .check :: _, hRun => simp [run, step, State.init, h] at hRun
    · simp [run, step, State.init, h] at hRun

/-! ## 4. Counting accepted challenge vectors -/

/-- **Freeze-then-sample count.** For every adversary the number of challenge vectors on which
the frozen commitment is accepted is the product of the per-repetition pass counts, and it is
zero when the configuration asks for no repetition. -/
theorem frozen_win_count_eq {C X : Type} (cfg : Config C X) (A : Adversary C X) (xs : List X) :
    countIf (frozenWins cfg A) (vectors xs cfg.reps) =
      if 1 ≤ cfg.reps then repProduct xs (cfg.check (A.commit [])) 0 cfg.reps else 0 := by
  have hc : countIf (frozenWins cfg A) (vectors xs cfg.reps) =
      countIf (fun v => decide (1 ≤ cfg.reps) && allReps (cfg.check (A.commit [])) 0 v)
        (vectors xs cfg.reps) := by
    apply countIf_vectors_congr
    intro v hv
    rw [frozenWins_eq]; unfold sampleOk
    by_cases h1 : 1 ≤ cfg.reps
    · simp [h1, hv]
    · simp [h1]
  rw [hc, countIf_and_const, countIf_allReps_vectors]
  by_cases h1 : 1 ≤ cfg.reps
  · simp [h1]
  · simp [h1]

/-- **Freeze-then-sample bound.** If every repetition of the frozen commitment passes on at
most `k` of the challenges in `xs`, the commitment is accepted on at most `k ^ reps` of the
`xs.length ^ reps` challenge vectors. -/
theorem frozen_win_count_le {C X : Type} (cfg : Config C X) (A : Adversary C X) (xs : List X)
    (k : Nat) (hk : ∀ j, countIf (cfg.check (A.commit []) j) xs ≤ k) :
    countIf (frozenWins cfg A) (vectors xs cfg.reps) ≤ k ^ cfg.reps ∧
      (vectors xs cfg.reps).length = xs.length ^ cfg.reps := by
  refine ⟨?_, length_vectors xs cfg.reps⟩
  rw [frozen_win_count_eq]
  split
  · exact repProduct_le_pow xs _ k hk cfg.reps 0
  · exact Nat.zero_le _

/-- **Exchanged order.** If the adversary can fit a commitment to any challenge vector it has
seen, the sample-then-freeze machine accepts on every challenge vector. -/
theorem swapped_win_count_all {C X : Type} (cfg : Config C X) (A : Adversary C X) (xs : List X)
    (h1 : 1 ≤ cfg.reps)
    (hFit : ∀ chis : List X, chis.length = cfg.reps →
      allReps (cfg.check (A.commit chis)) 0 chis = true) :
    countIf (swappedWins cfg A) (vectors xs cfg.reps) = xs.length ^ cfg.reps := by
  have hc : countIf (swappedWins cfg A) (vectors xs cfg.reps) =
      countIf (fun _ => true) (vectors xs cfg.reps) := by
    apply countIf_vectors_congr
    intro v hv
    rw [swappedWins_eq, hFit v hv]; unfold sampleOk
    simp [h1, hv]
  rw [hc, countIf_true, length_vectors]

/-! ## 5. Grinding against a lazily sampled oracle -/

/-- `Q` attempts. Attempt `i` commits as a function of the challenge vectors answered to the
earlier attempts and is checked against its own fresh challenge vector. -/
def grindWins {C X : Type} (cfg : Config C X) (A : Adversary C (List X)) :
    List (List X) → List (List X) → Bool
  | _, [] => false
  | hist, v :: rest =>
    (sampleOk cfg v && allReps (cfg.check (A.commit hist)) 0 v) ||
      grindWins cfg A (hist ++ [v]) rest

/-- **Grinding bound.** If every commitment the adversary can produce passes each repetition on
at most `k` challenges, then among the `M ^ Q` assignments of independent challenge vectors to
`Q` adaptive attempts (`M = xs.length ^ reps`) at most a `Q * k ^ reps / M` fraction contains an
accepted attempt. Stated cross-multiplied by `M`. -/
theorem grinding_win_count_le {C X : Type} (cfg : Config C X) (A : Adversary C (List X))
    (xs : List X) (k : Nat) (hk : ∀ hist j, countIf (cfg.check (A.commit hist) j) xs ≤ k) :
    ∀ (Q : Nat) (hist : List (List X)),
      countIf (grindWins cfg A hist) (vectors (vectors xs cfg.reps) Q) * xs.length ^ cfg.reps ≤
        Q * k ^ cfg.reps * (xs.length ^ cfg.reps) ^ Q
  | 0, hist => by
    show ((if grindWins cfg A hist [] then 1 else 0) + 0) * xs.length ^ cfg.reps ≤ _
    show (0 + 0) * xs.length ^ cfg.reps ≤ _
    rw [Nat.zero_mul]; exact Nat.zero_le _
  | Q + 1, hist => by
    have hM : (vectors xs cfg.reps).length = xs.length ^ cfg.reps := length_vectors xs cfg.reps
    have hLenQ : (vectors (vectors xs cfg.reps) Q).length = (xs.length ^ cfg.reps) ^ Q := by
      rw [length_vectors, hM]
    generalize hMdef : xs.length ^ cfg.reps = M at hM hLenQ ⊢
    generalize hKdef : k ^ cfg.reps = K
    have hOne : countIf (fun v => sampleOk cfg v && allReps (cfg.check (A.commit hist)) 0 v)
        (vectors xs cfg.reps) ≤ K := by
      have hEq : countIf (fun v => sampleOk cfg v && allReps (cfg.check (A.commit hist)) 0 v)
          (vectors xs cfg.reps) =
          countIf (frozenWins cfg ⟨fun _ => A.commit hist⟩) (vectors xs cfg.reps) := by
        apply countIf_vectors_congr
        intro v _
        rw [frozenWins_eq]
      rw [hEq, ← hKdef]
      exact (frozen_win_count_le cfg ⟨fun _ => A.commit hist⟩ xs k (hk hist)).1
    show countIf (grindWins cfg A hist) (extendAll (vectors xs cfg.reps)
      (vectors (vectors xs cfg.reps) Q)) * M ≤ (Q + 1) * K * M ^ (Q + 1)
    rw [countIf_extendAll]
    have hStep : sumOver (fun v => countIf (fun rest => grindWins cfg A hist (v :: rest))
        (vectors (vectors xs cfg.reps) Q)) (vectors xs cfg.reps) ≤
        sumOver (fun v =>
          (if sampleOk cfg v && allReps (cfg.check (A.commit hist)) 0 v then M ^ Q else 0) +
          countIf (grindWins cfg A (hist ++ [v])) (vectors (vectors xs cfg.reps) Q))
          (vectors xs cfg.reps) := by
      apply sumOver_le
      intro v
      have hb := countIf_or_const_le
        (sampleOk cfg v && allReps (cfg.check (A.commit hist)) 0 v)
        (grindWins cfg A (hist ++ [v])) (vectors (vectors xs cfg.reps) Q)
      rw [hLenQ] at hb
      exact hb
    rw [sumOver_add, sumOver_ite_const] at hStep
    have hTail : sumOver (fun v => countIf (grindWins cfg A (hist ++ [v]))
        (vectors (vectors xs cfg.reps) Q)) (vectors xs cfg.reps) * M ≤ M * (Q * K * M ^ Q) := by
      rw [← sumOver_mul_right]
      have hLe := sumOver_le (f := fun v => countIf (grindWins cfg A (hist ++ [v]))
          (vectors (vectors xs cfg.reps) Q) * M) (g := fun _ => Q * K * M ^ Q)
        (fun v => by
          have ih := grinding_win_count_le cfg A xs k hk Q (hist ++ [v])
          rw [hMdef, hKdef] at ih
          exact ih) (vectors xs cfg.reps)
      rw [sumOver_const, hM] at hLe
      exact hLe
    have hHead := Nat.mul_le_mul_right (M ^ Q * M) hOne
    have hTot := Nat.mul_le_mul_right M hStep
    rw [Nat.add_mul] at hTot
    refine Nat.le_trans hTot ?_
    have hSum := Nat.add_le_add
      (show countIf (fun v => sampleOk cfg v && allReps (cfg.check (A.commit hist)) 0 v)
          (vectors xs cfg.reps) * M ^ Q * M ≤ K * (M ^ Q * M) from by
        rw [Nat.mul_assoc]; exact hHead) hTail
    refine Nat.le_trans hSum (Nat.le_of_eq ?_)
    rw [Nat.pow_succ, Nat.add_mul Q 1 K, Nat.one_mul, Nat.add_mul, Nat.add_comm]
    congr 1
    rw [Nat.mul_comm M (Q * K * M ^ Q), Nat.mul_assoc (Q * K)]

/-! ## 6. Small instances -/

/-- A commitment is a list of bits; repetition `j` passes when the challenge equals bit `j`. -/
def echoConfig (reps : Nat) : Config (List Bool) Bool :=
  ⟨reps, fun c j x => decide (c.getD j false = x)⟩

theorem echoConfig_pass_count_le_one (reps : Nat) (c : List Bool) (j : Nat) :
    countIf ((echoConfig reps).check c j) [true, false] ≤ 1 :=
  countIf_le_one_of_unique (by decide) (fun _ _ hx hy =>
    (of_decide_eq_true hx).symm.trans (of_decide_eq_true hy))

theorem inhabited_frozen_win_count_le :
    ∃ (cfg : Config (List Bool) Bool) (A : Adversary (List Bool) Bool) (xs : List Bool) (k : Nat),
      ∀ j, countIf (cfg.check (A.commit []) j) xs ≤ k :=
  ⟨echoConfig 2, ⟨fun v => v⟩, [true, false], 1, fun j => echoConfig_pass_count_le_one 2 [] j⟩

theorem inhabited_grinding_win_count_le :
    ∃ (cfg : Config (List Bool) Bool) (A : Adversary (List Bool) (List Bool)) (xs : List Bool)
      (k : Nat), ∀ hist j, countIf (cfg.check (A.commit hist) j) xs ≤ k :=
  ⟨echoConfig 1, ⟨fun _ => [true]⟩, [true, false], 1,
    fun _ j => echoConfig_pass_count_le_one 1 [true] j⟩

theorem inhabited_run_verdict_shape :
    ∃ (cfg : Config Unit Bool) (ms : List (Move Unit Bool)) (s : State Unit Bool) (b : Bool),
      run cfg State.init ms = some s ∧ s.verdict = some b :=
  ⟨⟨1, fun _ _ x => x⟩, [.freeze (), .sample [true], .check],
    ⟨.done, some (), [true], some true⟩, true, by rfl, by rfl⟩

/-- In the exchanged order the adversary that commits the challenge vector it has just seen is
accepted on all four challenge vectors, although every commitment passes each repetition on at
most one challenge, so that the frozen order accepts at most one of the four. -/
theorem tooth_swapped_order_echo_wins_everywhere :
    ∃ A : Adversary (List Bool) Bool,
      (∀ c j, countIf ((echoConfig 2).check c j) [true, false] ≤ 1) ∧
      countIf (swappedWins (echoConfig 2) A) (vectors [true, false] 2) = 4 :=
  ⟨⟨fun v => v⟩, echoConfig_pass_count_le_one 2, by decide⟩

/-- The factor `Q` of the grinding bound is needed: two attempts at a one-bit challenge are
accepted on three of the four challenge assignments, more than the single-attempt bound. -/
theorem tooth_grinding_factor_needed :
    ∃ A : Adversary (List Bool) (List Bool),
      (∀ hist j, countIf ((echoConfig 1).check (A.commit hist) j) [true, false] ≤ 1) ∧
      ¬ (countIf (grindWins (echoConfig 1) A []) (vectors (vectors [true, false] 1) 2) * 2 ^ 1 ≤
        1 * 1 ^ 1 * (2 ^ 1) ^ 2) :=
  ⟨⟨fun _ => [true]⟩, fun _ j => echoConfig_pass_count_le_one 1 [true] j, by decide⟩

/-! ## Audits

The audit commands read proof bodies, which a module does not export, so they run here. -/

#verify_constructive frozen_win_count_eq
#verify_constructive frozen_win_count_le
#verify_constructive grinding_win_count_le
#verify_constructive swapped_win_count_all
#verify_constructive run_verdict_shape
#verify_constructive step_empty_sample_rejected
#verify_constructive step_wrong_length_rejected
#verify_constructive step_sample_before_freeze_rejected
#verify_constructive tooth_swapped_order_echo_wins_everywhere
#verify_constructive tooth_grinding_factor_needed

#verify_inhabited frozen_win_count_le inhabited_frozen_win_count_le
#verify_inhabited grinding_win_count_le inhabited_grinding_win_count_le
#verify_inhabited run_verdict_shape inhabited_run_verdict_shape

#tooth_pair frozen_win_count_le vs tooth_swapped_order_echo_wins_everywhere
#tooth_pair grinding_win_count_le vs tooth_grinding_factor_needed
#tooth_pair run_verdict_shape vs step_empty_sample_rejected

end Qsag.FrozenChallenge
