module
/-
Cross-construction boundaries, audited against the Rust sources.

The permutation results are classical transcript/counting results, not QROM bounds.
Fresh verification queries must be charged: an unqueried output can guess a preimage.
Sampling a permutation is without replacement; the denominator is N - t, not N.
The actual outer WHIR primitive is cSHAKE256 (sponge.rs, pcs.rs), not BLAKE3.
compute_message_mu uses Poseidon2; its Digest5 codec is little endian, whereas the
variable-length bytesToLimbs56 codec uses marked big-endian seven-byte chunks.
Distinct cSHAKE customizations separate inputs, not outputs or entire protocols.
FIPS-205 raw SHAKE roles and reused labels prevent an unconditional global partition.
-/
public import Qsag.Aggregation
public import Qsag.Poseidon2
public import Qsag.Fips205
public import Qsag.SpongeFramingAndDomainSep
import all Qsag.Aggregation
import all Qsag.Poseidon2
import all Qsag.Fips205
import all Qsag.SpongeFramingAndDomainSep
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.CrossProtocol
set_option autoImplicit false
open CommRingOps LawfulCommRing

/-- Three blocks of four field elements represent width twelve and rate eight. -/
abbrev State (D : Type) := D × D × D
abbrev Block4 := Fin 4 → Goldilocks

/-- Componentwise field addition is the Rust four-limb feed-forward operation. -/
instance : LawfulCommRing Block4 where
  zero := fun _ => zero; one := fun _ => one
  add := fun a b i => add (a i) (b i); mul := fun a b i => mul (a i) (b i)
  neg := fun a i => neg (a i); sub := fun a b i => sub (a i) (b i)
  add_assoc := fun _ _ _ => funext (fun _ => add_assoc _ _ _)
  add_comm := fun _ _ => funext (fun _ => add_comm _ _)
  zero_add := fun _ => funext (fun _ => zero_add _)
  add_zero := fun _ => funext (fun _ => add_zero _)
  add_left_neg := fun _ => funext (fun _ => add_left_neg _)
  sub_eq_add_neg := fun _ _ => funext (fun _ => sub_eq_add_neg _ _)
  mul_assoc := fun _ _ _ => funext (fun _ => mul_assoc _ _ _)
  mul_comm := fun _ _ => funext (fun _ => mul_comm _ _)
  one_mul := fun _ => funext (fun _ => one_mul _)
  mul_one := fun _ => funext (fun _ => mul_one _)
  left_distrib := fun _ _ _ => funext (fun _ => left_distrib _ _ _)
  right_distrib := fun _ _ _ => funext (fun _ => right_distrib _ _ _)

def rawTrunc {D : Type} (p : SimpleEquiv (State D) (State D)) (x : State D) : D :=
  (p.toFun x).1

/-- `extra = 0` matches agg/sponge.rs; `extra x = x.2.1 + seed` matches accel. -/
def relation {D : Type} [LawfulCommRing D] (extra : State D → D)
    (x y : State D) : D := add y.1 (add x.1 (extra x))

def jiveCompress {D : Type} [LawfulCommRing D] (extra : State D → D)
    (p : SimpleEquiv (State D) (State D)) (x : State D) : D :=
  relation extra x (p.toFun x)

/-- One inverse call suffices only when the recovered capacity is admissible. -/
theorem raw_inverse {D : Type} (p : SimpleEquiv (State D) (State D))
    (target b c : D) : rawTrunc p (p.invFun (target, b, c)) = target := by
  unfold rawTrunc
  rw [p.right_inv]

theorem raw_inverse_fixed_capacity {D : Type} (p : SimpleEquiv (State D) (State D))
    (target b c cap : D) (h : (p.invFun (target, b, c)).2.2 = cap) :
    ∃ a r, rawTrunc p (a, r, cap) = target := by
  have e := raw_inverse p target b c
  exact ⟨(p.invFun (target, b, c)).1, (p.invFun (target, b, c)).2.1, h ▸ e⟩

theorem inverse_feedforward_relation {D : Type} [LawfulCommRing D]
    (extra : State D → D) (p : SimpleEquiv (State D) (State D)) (y : State D) :
    jiveCompress extra p (p.invFun y) =
      add y.1 (add (p.invFun y).1 (extra (p.invFun y))) := by
  unfold jiveCompress
  rw [p.right_inv]
  rfl

/-- Explicit permutation: raw inversion succeeds, adding the recovered input fails. -/
theorem raw_vs_feedforward_tooth :
    ∃ p : SimpleEquiv (State Goldilocks) (State Goldilocks),
      rawTrunc p (p.invFun (one, zero, zero)) = one ∧
      jiveCompress (fun _ => zero) p (p.invFun (one, zero, zero)) ≠ one := by
  refine ⟨SimpleEquiv.refl _, rfl, ?_⟩
  decide

/-- Feed-forward does not guarantee security for every fixed permutation. -/
theorem identity_collision_tooth :
    ∃ x y : State Goldilocks, x ≠ y ∧
      jiveCompress (fun _ => zero) (SimpleEquiv.refl _) x =
      jiveCompress (fun _ => zero) (SimpleEquiv.refl _) y := by
  exact ⟨(zero, zero, zero), (zero, one, zero), by decide, rfl⟩

def Consistent {S : Type} (p : SimpleEquiv S S) (t : List (S × S)) : Prop :=
  ∀ x y, (x, y) ∈ t → p.toFun x = y

theorem forward_extension {S : Type} (p : SimpleEquiv S S) (t : List (S × S))
    (h : Consistent p t) (x : S) : Consistent p ((x, p.toFun x) :: t) := by
  intro a b hab
  rcases List.mem_cons.mp hab with he | he
  · cases he; rfl
  · exact h a b he

theorem inverse_extension {S : Type} (p : SimpleEquiv S S) (t : List (S × S))
    (h : Consistent p t) (y : S) : Consistent p ((p.invFun y, y) :: t) := by
  intro a b hab
  rcases List.mem_cons.mp hab with he | he
  · cases he; exact p.right_inv y
  · exact h a b he

theorem checked_preimage_is_transcript_hit {D : Type} [LawfulCommRing D]
    (extra : State D → D) (p : SimpleEquiv (State D) (State D))
    (t : List (State D × State D)) (target : D) (x y : State D)
    (hc : Consistent p t) (hm : (x, y) ∈ t) (hs : jiveCompress extra p x = target) :
    relation extra x y = target := by
  unfold jiveCompress at hs
  rwa [hc x y hm] at hs

def transcriptOutputs {S D : Type} (f : S → S → D) (t : List (S × S)) : List D :=
  t.map (fun xy => f xy.1 xy.2)

theorem preimage_target_count {S D : Type} (f : S → S → D)
    (t : List (S × S)) (q : Nat) (hq : t.length ≤ q) :
    (transcriptOutputs f t).length ≤ q := by
  simpa [transcriptOutputs] using hq

def unorderedPairs {D : Type} : List D → List (D × D)
  | [] => []
  | x :: xs => xs.map (fun y => (x, y)) ++ unorderedPairs xs

theorem unorderedPairs_count {D : Type} (xs : List D) :
    2 * (unorderedPairs xs).length = xs.length * (xs.length - 1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [unorderedPairs, List.length_append, List.length_map, List.length_cons]
    cases hn : xs.length with
    | zero => simp_all
    | succ n =>
      rw [hn] at ih
      simp only [Nat.succ_sub_one] at *
      rw [Nat.mul_add, ih]
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega

/-- Candidate counts, not a probability claim for an arbitrary permutation. -/
theorem collision_candidate_count {D : Type} (xs : List D) :
    (unorderedPairs xs).length + xs.length =
      xs.length * (xs.length - 1) / 2 + xs.length := by
  rw [← unorderedPairs_count xs, Nat.mul_div_right _ (by decide : 0 < 2)]

private theorem sum_constant {A : Type} (xs : List A) (f : A → Nat) (k : Nat)
    (h : ∀ x ∈ xs, f x = k) : (xs.map f).sum = xs.length * k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [h x (by simp), ih (fun a ha => h a (by simp [ha])), Nat.add_mul]
    omega

private theorem erase_length {S : Type} [DecidableEq S] (ys : List S) (y : S)
    (hy : y ∈ ys) : (ys.erase y).length = ys.length - 1 := by
  induction ys with
  | nil => cases hy
  | cons a ys ih =>
    by_cases he : a = y
    · subst a; simp only [List.erase_cons_head, List.length_cons, Nat.add_sub_cancel]
    · have ht : y ∈ ys := (List.mem_cons.mp hy).resolve_left (Ne.symm he)
      have hp := List.length_pos_of_mem ht
      rw [List.erase_cons_tail (by simpa only [beq_iff_eq] using he)]
      simp only [List.length_cons, ih ht]
      omega

private theorem erase_survives {S : Type} [DecidableEq S] (ys : List S) (x y : S)
    (hne : x ≠ y) (hx : x ∈ ys) : x ∈ ys.erase y := by
  induction ys with
  | nil => cases hx
  | cons a ys ih =>
    by_cases he : a = y
    · subst a; rw [List.erase_cons_head]
      exact (List.mem_cons.mp hx).resolve_left hne
    · rw [List.erase_cons_tail (by simpa only [beq_iff_eq] using he)]
      rcases List.mem_cons.mp hx with h | h
      · exact List.mem_cons.mpr (Or.inl h)
      · exact List.mem_cons.mpr (Or.inr (ih h))

private theorem nodup_length_bound {S : Type} [DecidableEq S] (xs ys : List S)
    (hn : xs.Nodup) (hs : xs ⊆ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => exact Nat.zero_le _
  | cons a xs ih =>
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hn
    have hay := hs (List.mem_cons_self ..)
    have hsub : xs ⊆ ys.erase a := fun x hx =>
      erase_survives ys x a (fun he => ha (he ▸ hx)) (hs (List.mem_cons_of_mem a hx))
    have hb := ih (ys.erase a) ht hsub
    rw [erase_length ys a hay] at hb
    have hp := List.length_pos_of_mem hay
    simp only [List.length_cons]
    omega

private theorem erase_perm {S : Type} [DecidableEq S] (ys : List S) (y : S)
    (hy : y ∈ ys) : ys.Perm (y :: ys.erase y) := by
  induction ys with
  | nil => cases hy
  | cons a ys ih =>
    by_cases he : a = y
    · subst a; rw [List.erase_cons_head]
    · have ht : y ∈ ys := (List.mem_cons.mp hy).resolve_left (Ne.symm he)
      rw [List.erase_cons_tail (by simpa only [beq_iff_eq] using he)]
      exact (List.Perm.cons a (ih ht)).trans (List.Perm.swap y a _)

/-- All ways to complete the unused output table, in fixed unused-input order. -/
def extensions {S : Type} [DecidableEq S] : Nat → List S → List (List S)
  | 0, _ => [[]]
  | n + 1, ys => ys.flatMap (fun y => (extensions n (ys.erase y)).map (y :: ·))

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

theorem extensions_count {S : Type} [DecidableEq S] (n : Nat) (ys : List S)
    (h : ys.length = n) : (extensions n ys).length = factorial n := by
  induction n generalizing ys with
  | zero => rfl
  | succ n ih =>
    rw [extensions, List.length_flatMap]
    have he : ∀ y ∈ ys, ((extensions n (ys.erase y)).map (y :: ·)).length = factorial n := by
      intro y hy
      rw [List.length_map, ih _ (by rw [erase_length ys y hy, h]; omega)]
    rw [sum_constant ys _ _ he, h]
    rfl

theorem extensions_are_permutations {S : Type} [DecidableEq S] (n : Nat)
    (ys zs : List S) (h : ys.length = n) (hm : zs ∈ extensions n ys) : zs.Perm ys := by
  induction n generalizing ys zs with
  | zero =>
    have hy : ys = [] := List.length_eq_zero_iff.mp h
    have hz : zs = [] := List.mem_singleton.mp hm
    subst ys; subst zs; exact List.Perm.refl _
  | succ n ih =>
    obtain ⟨y, hy, hzs⟩ := List.mem_flatMap.mp hm
    obtain ⟨rest, hr, rfl⟩ := List.mem_map.mp hzs
    exact (List.Perm.cons y (ih _ _ (by rw [erase_length ys y hy, h]; omega) hr)).trans
      (erase_perm ys y hy).symm

theorem extensions_complete {S : Type} [DecidableEq S] (n : Nat) (ys zs : List S)
    (hl : ys.length = n) (hp : zs.Perm ys) : zs ∈ extensions n ys := by
  induction n generalizing ys zs with
  | zero =>
    have hz := hp.length_eq.trans hl
    have he := List.length_eq_zero_iff.mp hz
    subst zs; exact List.mem_singleton.mpr rfl
  | succ n ih =>
    cases zs with
    | nil => have h := hp.length_eq; simp only [List.length_nil] at h; omega
    | cons y zs =>
      have hy := hp.mem_iff.mp (by simp : y ∈ y :: zs)
      apply List.mem_flatMap.mpr
      refine ⟨y, hy, List.mem_map.mpr ⟨zs, ?_, rfl⟩⟩
      exact ih _ _ (by rw [erase_length ys y hy, hl]; omega)
        (List.Perm.cons_inv (hp.trans (erase_perm ys y hy)))

private theorem flatMap_nodup {A B : Type} (xs : List A) (f : A → List B)
    (hn : xs.Nodup) (hf : ∀ a ∈ xs, (f a).Nodup)
    (sep : ∀ a ∈ xs, ∀ b ∈ xs, a ≠ b → ∀ u ∈ f a, ∀ v ∈ f b, u ≠ v) :
    (xs.flatMap f).Nodup := by
  induction xs with
  | nil => exact .nil
  | cons a xs ih =>
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hn
    apply List.nodup_append.mpr
    refine ⟨hf a (by simp), ih ht (fun x hx => hf x (by simp [hx]))
      (fun x hx y hy => sep x (by simp [hx]) y (by simp [hy])), ?_⟩
    intro u hu v hv
    obtain ⟨b, hb, hv⟩ := List.mem_flatMap.mp hv
    exact sep a (by simp) b (by simp [hb]) (fun h => ha (h ▸ hb)) u hu v hv

theorem extensions_nodup {S : Type} [DecidableEq S] (n : Nat) (ys : List S)
    (hn : ys.Nodup) : (extensions n ys).Nodup := by
  induction n generalizing ys with
  | zero => exact .cons (by intro _ h; cases h) .nil
  | succ n ih =>
    apply flatMap_nodup ys _ hn
    · intro y _
      exact (ih _ (hn.erase y)).map (y :: ·) (fun _ _ h e => h (List.cons.inj e).2)
    · intro a _ b _ hab u hu v hv
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hu
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp hv
      exact fun e => hab (List.cons.inj e).1

/-- Each possible fresh answer has exactly the same number of completions. -/
theorem fresh_answer_weight {S : Type} [DecidableEq S] (ys : List S) (y : S)
    (hy : y ∈ ys) :
    (extensions (ys.length - 1) (ys.erase y)).length = factorial (ys.length - 1) :=
  extensions_count _ _ (erase_length ys y hy)

def forwardFiber {D : Type} [LawfulCommRing D] (ds : List D)
    (extra : State D → D) (x : State D) (target : D) : List (State D) :=
  ds.flatMap (fun b => ds.map (fun c => (sub target (add x.1 (extra x)), b, c)))

/-- `extra` may depend on the second/third block, but not on the unknown first block. -/
def inverseFiber {D : Type} [LawfulCommRing D] (ds : List D)
    (extra : D → D → D) (y : State D) (target : D) : List (State D) :=
  ds.flatMap (fun b => ds.map (fun c => (sub (sub target y.1) (extra b c), b, c)))

private theorem solve_add {D : Type} [LawfulCommRing D] {a b t : D}
    (h : add a b = t) : a = sub t b := by
  rw [← h, sub_eq_add_neg, add_assoc, add_right_neg, add_zero]

theorem forward_fiber_complete {D : Type} [LawfulCommRing D] (ds : List D)
    (allD : ∀ d, d ∈ ds) (extra : State D → D) (x y : State D) (target : D)
    (h : relation extra x y = target) : y ∈ forwardFiber ds extra x target := by
  have e := solve_add h
  exact List.mem_flatMap.mpr ⟨y.2.1, allD _, List.mem_map.mpr ⟨y.2.2, allD _,
    by cases y; simp_all⟩⟩

theorem inverse_fiber_complete {D : Type} [LawfulCommRing D] (ds : List D)
    (allD : ∀ d, d ∈ ds) (extra : D → D → D) (x y : State D) (target : D)
    (h : relation (fun z => extra z.2.1 z.2.2) x y = target) :
    x ∈ inverseFiber ds extra y target := by
  have he : add (add x.1 (extra x.2.1 x.2.2)) y.1 = target :=
    (add_comm _ _).trans h
  have e := solve_add (solve_add he)
  exact List.mem_flatMap.mpr ⟨x.2.1, allD _, List.mem_map.mpr ⟨x.2.2, allD _,
    by cases x; simp_all⟩⟩

theorem fiber_counts {D : Type} [LawfulCommRing D] (ds : List D)
    (f : State D → D) (g : D → D → D) (x y : State D) (target : D) :
    (forwardFiber ds f x target).length = ds.length * ds.length ∧
    (inverseFiber ds g y target).length = ds.length * ds.length := by
  constructor <;> simp only [forwardFiber, inverseFiber, List.length_flatMap]
  all_goals exact sum_constant ds _ _ (fun _ _ => List.length_map _)

/-- Finite counting form: at most B favorable fresh responses, each of weight (N-t-1)!.
    With D = F^4, fibers have B = |D|^2 = p^8 and the full state space has N = p^12.
    The conditional ratio is at most B/(N-t), in either query direction. -/
theorem fresh_bad_extensions_bound {S : Type} [DecidableEq S]
    (available fiber : List S) (bad : S → Bool) (hn : available.Nodup)
    (cover : ∀ x ∈ available, bad x = true → x ∈ fiber) :
    ((available.filter bad).flatMap (fun y =>
      (extensions (available.length - 1) (available.erase y)).map (y :: ·))).length ≤
      fiber.length * factorial (available.length - 1) := by
  rw [List.length_flatMap]
  have hw : ∀ y ∈ available.filter bad,
      ((extensions (available.length - 1) (available.erase y)).map (y :: ·)).length =
      factorial (available.length - 1) := by
    intro y hy
    rw [List.length_map, fresh_answer_weight available y (List.mem_filter.mp hy).1]
  rw [sum_constant _ _ _ hw]
  apply Nat.mul_le_mul_right
  exact nodup_length_bound _ _ (hn.filter bad) (fun x hx =>
    cover x (List.mem_filter.mp hx).1 (List.mem_filter.mp hx).2)

def queryValue {D : Type} [LawfulCommRing D] (inverse : Bool)
    (extra : D → D → D) (chosen answer : State D) : D :=
  if inverse then relation (fun z => extra z.2.1 z.2.2) answer chosen
  else relation (fun z => extra z.2.1 z.2.2) chosen answer

def queryFiber {D : Type} [LawfulCommRing D] (inverse : Bool) (ds : List D)
    (extra : D → D → D) (chosen : State D) (target : D) : List (State D) :=
  if inverse then inverseFiber ds extra chosen target
  else forwardFiber ds (fun z => extra z.2.1 z.2.2) chosen target

/-- One theorem covers forward/inverse preimages (one target) and collisions
    (all prior transcript outputs). Each target contributes at most |D|² completions
    per residual permutation, with the exact without-replacement denominator. -/
theorem bidirectional_bad_count {D : Type} [LawfulCommRing D] [DecidableEq D]
    (inverse : Bool) (ds : List D) (allD : ∀ d, d ∈ ds) (extra : D → D → D)
    (chosen : State D) (targets : List D) (available : List (State D))
    (hn : available.Nodup) :
    ((available.filter (fun x => decide (queryValue inverse extra chosen x ∈ targets))).flatMap
      (fun y => (extensions (available.length - 1) (available.erase y)).map (y :: ·))).length ≤
      (targets.length * (ds.length * ds.length)) * factorial (available.length - 1) := by
  let fibers := targets.flatMap (queryFiber inverse ds extra chosen)
  have hc : ∀ x ∈ available,
      decide (queryValue inverse extra chosen x ∈ targets) = true → x ∈ fibers := by
    intro x _ hx
    apply List.mem_flatMap.mpr
    refine ⟨queryValue inverse extra chosen x, of_decide_eq_true hx, ?_⟩
    cases inverse
    · exact forward_fiber_complete ds allD (fun z => extra z.2.1 z.2.2) chosen x _ rfl
    · exact inverse_fiber_complete ds allD extra x chosen _ rfl
  have hl : fibers.length = targets.length * (ds.length * ds.length) := by
    rw [List.length_flatMap]
    apply sum_constant
    intro t _
    cases inverse
    · exact (fiber_counts ds (fun z => extra z.2.1 z.2.2) extra chosen chosen t).1
    · exact (fiber_counts ds (fun z => extra z.2.1 z.2.2) extra chosen chosen t).2
  have hb := fresh_bad_extensions_bound available fibers _ hn hc
  rwa [hl] at hb

/-- Uniform completions give an exact finite denominator: available.length factorial.
    Deleting prior responses affects the denominator even when the bad fiber is unchanged. -/
theorem conditional_extension_density {S : Type} [DecidableEq S]
    (available : List S) (bad : S → Bool) :
    ((available.filter bad).flatMap (fun y =>
      (extensions (available.length - 1) (available.erase y)).map (y :: ·))).length =
      (available.filter bad).length * factorial (available.length - 1) := by
  rw [List.length_flatMap]
  exact sum_constant _ _ _ (fun y hy => by
    rw [List.length_map, fresh_answer_weight available y (List.mem_filter.mp hy).1])

theorem width12_fiber_cardinality (ds : List Block4)
    (hc : ds.length = goldilocksPrime ^ 4) (x y : State Block4) (target : Block4) :
    (forwardFiber ds (fun _ => zero) x target).length = goldilocksPrime ^ 8 ∧
    (inverseFiber ds (fun _ _ => zero) y target).length = goldilocksPrime ^ 8 := by
  obtain ⟨hf, hi⟩ := fiber_counts ds (fun _ => zero) (fun _ _ => zero) x y target
  have he : ds.length * ds.length = goldilocksPrime ^ 8 := by
    rw [hc, ← Nat.pow_add]
  exact ⟨hf.trans he, hi.trans he⟩

/-- A zero-query guess can succeed; verification must extend the charged transcript. -/
theorem unchecked_preimage_tooth : ∃ x : State Goldilocks,
    jiveCompress (fun _ => zero) (SimpleEquiv.refl _) x = zero ∧
    ¬ ∃ y, (x, y) ∈ ([] : List (State Goldilocks × State Goldilocks)) := by
  exact ⟨(zero, zero, zero), by decide, by intro ⟨_, h⟩; cases h⟩

/-- Product-oracle independence is a hypothesis of the model, not inferred from tags. -/
structure OraclePair (Q R S : Type) where
  outer : Q → R
  inner : SimpleEquiv S S

def reprogram {Q R S : Type} (sim : (Q → R) → Q → R)
    (o : OraclePair Q R S) : OraclePair Q R S := ⟨sim o.outer, o.inner⟩

inductive InnerQuery (S : Type) where
  | forward : S → InnerQuery S
  | inverse : S → InnerQuery S

def innerAnswer {Q R S : Type} (o : OraclePair Q R S) : InnerQuery S → S
  | .forward x => o.inner.toFun x
  | .inverse y => o.inner.invFun y

/-- Adaptive inner-only algorithms have identical views under outer-only updates. -/
inductive InnerProgram (S A : Type) where
  | done : A → InnerProgram S A
  | ask : InnerQuery S → (S → InnerProgram S A) → InnerProgram S A

def runInner {Q R S A : Type} (o : OraclePair Q R S) : InnerProgram S A → A
  | .done a => a
  | .ask q k => runInner o (k (innerAnswer o q))

theorem outer_reprogram_zero_drift {Q R S A : Type} (sim : (Q → R) → Q → R)
    (o : OraclePair Q R S) (game : InnerProgram S A) :
    runInner (reprogram sim o) game = runInner o game := by
  induction game with
  | done a => rfl
  | ask q k ih => exact ih (innerAnswer o q)

theorem digest5_collision_iff {M : Type} (hash : M → BitVec 256) (a b : M) :
    digest5FromBitVec256 (hash a) = digest5FromBitVec256 (hash b) ↔ hash a = hash b :=
  ⟨digest5FromBitVec256_injective, congrArg digest5FromBitVec256⟩

theorem marked_bytes_collision_iff {M : Type} (hash : M → List UInt8) (a b : M) :
    bytesToLimbs56 (hash a) = bytesToLimbs56 (hash b) ↔ hash a = hash b :=
  ⟨bytesToLimbs56_injective, congrArg bytesToLimbs56⟩

def naiveLimb (n : Nat) : Nat := n % goldilocksPrime

/-- There are 2^32-1 distinct colliding PAIRS, not that many preimages per residue. -/
theorem naive_limb_collision_family (i : Fin (2 ^ 32 - 1)) :
    i.val < goldilocksPrime ∧ goldilocksPrime + i.val < 2 ^ 64 ∧
    i.val ≠ goldilocksPrime + i.val ∧
    naiveLimb i.val = naiveLimb (goldilocksPrime + i.val) := by
  have hi := i.isLt
  refine ⟨by unfold goldilocksPrime; omega, by unfold goldilocksPrime; omega,
    by unfold goldilocksPrime; omega, ?_⟩
  simp [naiveLimb]

theorem naive_family_distinct (i j : Fin (2 ^ 32 - 1))
    (h : goldilocksPrime + i.val = goldilocksPrime + j.val) : i = j :=
  Fin.ext (Nat.add_left_cancel h)

theorem digest5_vs_modular_tooth :
    digest5FromBitVec256 0 ≠ digest5FromBitVec256 (BitVec.ofNat 256 goldilocksPrime) ∧
    naiveLimb 0 = naiveLimb goldilocksPrime := by
  constructor
  · intro h
    have e := digest5FromBitVec256_injective h
    exact (by decide : (0 : BitVec 256) ≠ BitVec.ofNat 256 goldilocksPrime) e
  · simp [naiveLimb]

/-- Exact UTF-8 bytes; all audited Rust byte literals below are ASCII. -/
def bytes (s : String) : List UInt8 := s.toUTF8.data.toList

/-- Twelve agg/sig.rs IVs, in source order (including all four FORS roles). -/
def aggTags : List Nat :=
  [0x5153414757505246, 0x5153414757535450, 0x5153414757504B31, 0x515341474D524B4C,
   0x51534147484D5331, 0x5153414748445452, 0x515341474853544C, 0x515341475052464D,
   0x5153414746505246, 0x51534147464C4546, 0x51534147464E4F44, 0x5153414746525453]

/-- Address, migration-nullifier, permutation, accelerated-Merkle and node IVs. -/
def otherIVs : List Nat :=
  [0x5153414741445232, 0x4D49475F4E554C31, 0x504F53325F474C31,
   0x4D524B4C5F503231, 0x4C525F4E4F444531]

theorem iv_tags_canonical_distinct :
    (aggTags ++ otherIVs).Nodup ∧
      ∀ n ∈ aggTags ++ otherIVs, n < goldilocksPrime := by decide

/-- Canonical literal IVs remain distinct when put in a dedicated field lane. -/
theorem canonical_iv_separation (a b : Nat) (ha : a < goldilocksPrime)
    (hb : b < goldilocksPrime) (hne : a ≠ b) : naiveLimb a ≠ naiveLimb b := by
  simpa only [naiveLimb, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hne

/-- An IV added to an adversarial seed is not a disjoint literal prefix. -/
theorem additive_iv_tooth : ∃ a b s t : Goldilocks,
    a ≠ b ∧ add a s = add b t := by
  exact ⟨zero, one, one, zero, by decide, by decide⟩

/-- Nonempty cSHAKE customization input, before padding; empty tags select raw SHAKE in Rust. -/
def formatted (tag payload : List UInt8) : List UInt8 := cshakePrefix [] tag ++ payload

theorem universal_customization_partition (a b x y : List UInt8)
    (hne : a ≠ b) (ha : 8 * a.length < 256 ^ 255)
    (hb : 8 * b.length < 256 ^ 255) : formatted a x ≠ formatted b y := by
  intro h
  exact hne (cshakePrefix_prefix_free (by decide) ha (by decide) hb h).2.1

def reprogramAt {R : Type} (h : List UInt8 → R) (query : List UInt8) (v : R)
    (x : List UInt8) : R := if x = query then v else h x

/-- Zero cross-domain query aliasing; hash OUTPUT collisions are still possible. -/
theorem foreign_reprogram_unchanged {R : Type} (h : List UInt8 → R) (v : R)
    (a b x y : List UInt8) (ha : 8 * a.length < 256 ^ 255)
    (hb : 8 * b.length < 256 ^ 255) (hne : a ≠ b) :
    reprogramAt h (formatted b y) v (formatted a x) = h (formatted a x) := by
  exact ite_eq_right (universal_customization_partition a b x y hne ha hb)

inductive OracleProgram (Q R A : Type) where
  | done : A → OracleProgram Q R A
  | ask : Q → (R → OracleProgram Q R A) → OracleProgram Q R A

def runOracle {Q R A : Type} (h : Q → R) : OracleProgram Q R A → A
  | .done a => a
  | .ask q k => runOracle h (k (h q))

theorem runOracle_ext {Q R A : Type} (h g : Q → R) (eqv : ∀ q, h q = g q)
    (p : OracleProgram Q R A) : runOracle h p = runOracle g p := by
  induction p with
  | done a => rfl
  | ask q k ih => simp only [runOracle, eqv q]; exact ih (g q)

/-- Pointwise game equality for a target-domain program, hence equal indicators
    on any common distribution of seeds. Does not assert arbitrary protocol composition. -/
theorem isolated_game_zero_drift {R A : Type} (h : List UInt8 → R) (v : R)
    (a b y : List UInt8) (ha : 8 * a.length < 256 ^ 255)
    (hb : 8 * b.length < 256 ^ 255) (hne : a ≠ b)
    (p : OracleProgram (List UInt8) R A) :
    runOracle (fun x => reprogramAt h (formatted b y) v (formatted a x)) p =
      runOracle (fun x => h (formatted a x)) p :=
  runOracle_ext _ _ (fun x => foreign_reprogram_unchanged h v a b x y ha hb hne) p

theorem fips_adrs_type_partition (a b : Fips205Adrs) (hne : a.adrsType ≠ b.adrsType) :
    encodeFips205Adrs a ≠ encodeFips205Adrs b := by
  intro h
  exact hne (congrArg Fips205Adrs.adrsType (encodeFips205Adrs_injective h))

/-- FIPS-205 §11.2.1: exact raw SHAKE inputs, with no synthetic role byte. -/
def fipsPrfMsgInput (sk rand msg : List UInt8) := sk ++ rand ++ msg
def fipsHMsgInput (rand seed root msg : List UInt8) := rand ++ seed ++ root ++ msg

/-- Valid n=16 lengths and pure-message leading bytes can still overlap across roles.
    This is an input-domain counterexample, not a FIPS-205 signature forgery. -/
theorem fips_universal_partition_tooth :
    ∃ sk rand root m m' : List UInt8,
      sk.length = 16 ∧ rand.length = 16 ∧ root.length = 16 ∧ m ≠ m' ∧
      fipsPrfMsgInput sk rand m' = fipsHMsgInput sk rand root m := by
  refine ⟨List.replicate 16 0, List.replicate 16 0, List.replicate 16 0,
    [0, 0], List.replicate 16 0 ++ [0, 0], rfl, rfl, rfl, ?_, ?_⟩
  · intro h
    have e := congrArg List.length h
    simp at e
  · simp only [fipsPrfMsgInput, fipsHMsgInput, List.append_assoc]

/-- Any verifier that accepts a signature on an unprefixed digest accepts it in
    another role when the same message and verification key are used. -/
def digestAccepts {D Sig : Type} (verify : D → Sig → Bool) (hash : List UInt8 → D)
    (_role : Bool) (msg : List UInt8) (sig : Sig) : Bool := verify (hash msg) sig

theorem unprefixed_chosen_message_tooth : ∃ msg : List UInt8,
    true ≠ false ∧ digestAccepts (fun d s => d == s) id true msg msg = true ∧
      digestAccepts (fun d s => d == s) id false msg msg = true := by
  exact ⟨[42], by decide, by decide, by decide⟩

/-- Concrete nonempty witnesses for the three assurance boundaries. -/
theorem permutation_witness :
    ∃ p : SimpleEquiv (State Goldilocks) (State Goldilocks),
      rawTrunc p (p.invFun (one, zero, zero)) = one := ⟨SimpleEquiv.refl _, rfl⟩

theorem digest_witness : ∃ h : Bool → BitVec 256,
    digest5FromBitVec256 (h false) = digest5FromBitVec256 (h false) := ⟨fun _ => 0, rfl⟩

theorem partition_witness : ∃ a b x y : List UInt8,
    8 * a.length < 256 ^ 255 ∧ 8 * b.length < 256 ^ 255 ∧ a ≠ b ∧
      formatted a x ≠ formatted b y := by
  refine ⟨[1], [2], [], [], by decide, by decide, by decide, ?_⟩
  exact universal_customization_partition _ _ _ _ (by decide) (by decide) (by decide)

/-- Omitting framing aliases a chosen message across distinct domains. -/
theorem unframed_partition_tooth : ∃ a b x y : List UInt8,
    a ≠ b ∧ a ++ x = b ++ y ∧ formatted a x ≠ formatted b y := by
  refine ⟨[1], [1, 2], [2], [], by decide, rfl, ?_⟩
  exact universal_customization_partition _ _ _ _ (by decide) (by decide) (by decide)


/-- Source literal inventory across all twelve crates (production source before test modules).
    Includes wire magics and transcript labels; membership alone does not imply that a label
    is a cSHAKE customization. Shared labels retain both owning crates. -/
def auditedByteLabels : List (String × List String) := [
  ("qsag-accel", [
    "QSAG.ACCEL.ALG.BDOZ_GF2_128_DOT.V1", "QSAG.ACCEL.ALG.COSET_LDE_EXT2.V1", "QSAG.ACCEL.ALG.GOLDILOCKS_NTT.V1", "QSAG.ACCEL.ALG.KECCAK_F1600.V1", "QSAG.ACCEL.ALG.MERKLE_POSEIDON2.V1", "QSAG.ACCEL.ALG.POSEIDON2_PERM12.V1", "QSAG.ACCEL.BACKEND_ATTESTATION_KEY.V1", "QSAG.ACCEL.BACKEND_ID.V1",
    "QSAG.ACCEL.BDOZ_IN.V1", "QSAG.ACCEL.BDOZ_OUT.V1", "QSAG.ACCEL.KECCAK_IN.V1", "QSAG.ACCEL.KECCAK_OUT.V1", "QSAG.ACCEL.KERNEL.P2.V1", "QSAG.ACCEL.KERNEL.SHA256.V1", "QSAG.ACCEL.KEYED_RECEIPT.V5", "QSAG.ACCEL.LDE_IN.V1",
    "QSAG.ACCEL.LDE_OUT.V1", "QSAG.ACCEL.MERKLE_IN.V1", "QSAG.ACCEL.MERKLE_OUT.V1", "QSAG.ACCEL.MERKLE_SAMPLE.V1", "QSAG.ACCEL.NTT_IN.V2", "QSAG.ACCEL.NTT_OUT.V1", "QSAG.ACCEL.P2_PERM_IN.V1", "QSAG.ACCEL.P2_PERM_OUT.V1",
    "QSAG.ACCEL.PROVER.AIR_ROW_GROUP_A.V1", "QSAG.ACCEL.PROVER.AIR_ROW_GROUP_B.V1", "QSAG.ACCEL.PROVER.WHIR_FOLD_SUMCHECK.V1", "QSAG.ACCEL.PROVER.WHIR_LDE_COMMIT.V1", "QSAG.ACCEL.PROVER_KERNEL.P2.V1", "QSAG.ACCEL.PROVER_KERNEL.SHA256.V1", "QSAG.ACCEL.VULKAN_AUDIT_EVIDENCE.V1", "QSAG.COMMIT.V1",
    "QSAG.CPU_REF.BDOZ_GF2_128_DOT.V1", "QSAG.CPU_REF.COSET_LDE_EXT2.V1", "QSAG.CPU_REF.GOLDILOCKS_NTT.V1", "QSAG.CPU_REF.KECCAK_F1600.V1", "QSAG.CPU_REF.MERKLE_POSEIDON2.V1", "QSAG.CPU_REF.POSEIDON2_PERM12.V1", "QSAG.FS.ABSORB.V1", "QSAG.FS.INIT.V1",
    "QSAG.FS.RATCHET.V1", "QSAG.FS.SQUEEZE.V1"]),
  ("qsag-addr", [
    "QSAG.ADDR.CSHAKE256.V1", "QSAG.HYBRID.ENV.V1", "QSAG.HYBRID.ID_COMMIT.V1", "QSAG.HYBRID.ID_COMMIT.V2", "QSAG.HYBRID.PK_CLASSICAL.V2", "QSAG.HYBRID.PK_PQ.V2", "QSAG.HYBRID.V2"]),
  ("qsag-agg", [
    "QSAG.AGG.FS_TRANSCRIPT/v1", "QSAG.AGG.WAL.MAC/v4", "QSAG.BATCH.BLIND/v4", "QSAG.COMMITTEE.ROOT/v2", "QSAG.HEM.BLIND/v2", "QSAG.HEM.HIERARCHY.ROOT/v3", "QSAG.HEM.HIERARCHY.SHARD/v3", "QSAG.HEM.MSG/v2",
    "QSAG.HEM.NTT.INPUT/v2", "QSAG.HEM.NTT.OUTPUT/v2", "QSAG.HEM.NTT.WORDS.LEAF/v1", "QSAG.HEM.NTT.WORDS.ROOT/v1", "QSAG.HEM.POLICY.REGISTRY/v2", "QSAG.HEM.POLICY.ROW/v2", "QSAG.HEM.PROVER.STAGE.IN/v1", "QSAG.HEM.PROVER.STAGE.OUT/v1",
    "QSAG.HEM.REGION.BOUND/v2", "QSAG.KEYGEN.PKSEED/v2", "QSAG.KEYGEN.PRF/v2", "QSAG.KEYGEN.SK/v2", "QSAG.LEAF.PCS_SALT/v4", "QSAG.MU/v2", "QSAG.PCS.CANOPY/v2", "QSAG.PCS.POW2/v1",
    "QSAG.SHARD.BATCH/v5", "QSAG.SHARD.BLIND/v4", "QSAG.SHM.OUTER.IDLE.BLIND/v1", "QSAG.SHM.OUTER.SALT/v1", "QSAG.SHM.SUMMARY.HDR/v1", "QSAG.SIGNING.MODE/v2", "QSAG.STATELESS.BUDGET/v1", "QSAG.SUCCINCT.OUTER.HEM/v1",
    "QSAGWAA4", "QSAGWAL4"]),
  ("qsag-asm", [
    "QSAGLCK1", "QSAGREC1"]),
  ("qsag-cli", [
    "QSAG.CLI.AGG.BINDING.V1", "QSAG.CLI.AGG.CEREMONY.V1", "QSAG.CLI.ANCHOR.DOMAIN.V1", "QSAG.CLI.ANCHOR.FLOOR.V1", "QSAG.CLI.ANCHOR.SLOT.V1", "QSAG.CLI.DERIVE.V1", "QSAG.CLI.DKG.BEAVER.CORR.V1", "QSAG.CLI.ENROLL.V1",
    "QSAG.CLI.EXTERNAL_ANCHOR.MAC.V1", "QSAG.CLI.FRONTIER.CEREMONY.V1", "QSAG.CLI.FRONTIER.HEDGE.V1", "QSAG.CLI.FRONTIER.USE_SEED.V1", "QSAG.CLI.FTS.DKG.BEAVER_CORR.V1", "QSAG.CLI.FTS.DKG.PARTY_ENTROPY.V1", "QSAG.CLI.FTS.DKG.SESSION.V1", "QSAG.CLI.FTS.LEAF_PREP.V1",
    "QSAG.CLI.HEM.DIR_DIGEST.V1", "QSAG.CLI.HEM.QUORUM.LATCH_SEED.V1", "QSAG.CLI.HEM.QUORUM.SEED_FILE.V1", "QSAG.CLI.HEM.REFRESH.DET.V1", "QSAG.CLI.HEM.RESHARE.DET.V1", "QSAG.CLI.HEM.RESHARE.NEW_LATCH.V1", "QSAG.CLI.POLICY.COMMITTEE_CHECKPOINT.V1", "QSAG.CLI.POLICY.DKG.PARTY_ENTROPY.V1",
    "QSAG.CLI.POLICY.DKG.SETUP.V1", "QSAG.CLI.POLICY.EPHEMERAL.KEY.V1", "QSAG.CLI.POLICY.INTENT_RECORD.V1", "QSAG.CLI.POLICY.KEY_ID.V1", "QSAG.CLI.POLICY.LEDGER.KDF.V1", "QSAG.CLI.POLICY.LEDGER_ID.SEED.V1", "QSAG.CLI.POLICY.LEDGER_ID.V1", "QSAG.CLI.POLICY.WINDOW_STATE.V1",
    "QSAG.CLI.PUBLIC_AGG.BLINDING.V1", "QSAG.CLI.PUBLIC_AGG.SIG_ACC.V1", "QSAG.CLI.QUORUM.CEREMONY_ID.V1", "QSAG.CLI.QUORUM.DKG.RNG.V1", "QSAG.CLI.QUORUM.KEYGEN.RNG.V1", "QSAG.CLI.QUORUM.ONLINE_RNG.V1", "QSAG.CLI.QUORUM.ONLINE_RNG_STREAM.V1", "QSAG.CLI.QUORUM.ONLINE_SID.V1",
    "QSAG.CLI.QUORUM.PARTY_KDF.V1", "QSAG.CLI.QUORUM.PARTY_KEY_ID.V1", "QSAG.CLI.QUORUM.TREE_DIGEST.V1", "QSAG.CLI.SESSION.HEDGE.V1", "QSAG.CLI.SESSION.V1", "QSAG.CLI.SLH.HEDGE.V1", "QSAG.CLI.THRESHOLD.CEREMONY.V1", "QSAG.CLI.THRESHOLD.EPOCH_SEED.V1",
    "QSAG.CLI.VAULT.MAC.V1", "QSAG.ENVELOPE.ENC.V1", "QSAG.ENVELOPE.ITER.V1", "QSAG.ENVELOPE.KDF.V1", "QSAG.ENVELOPE.MAC.V1", "QSAG.ENVELOPE.STREAM.V1", "QSAG.ENVELOPE.TAG.V1", "QSAG.KAT.v1",
    "QSAG.POLICY.CTX.V1", "QSAG.POLICY.KEY.V1", "QSAGANC1", "QSAGLCK1", "QSAGPLB1"]),
  ("qsag-core", [
    "QSAG-JORTS-RETRY-SALT-v1", ("QSAG-WA" ++ "VE-CHECK-COIN-v1"), ("QSAG-WA" ++ "VE-CHECK-v1"), ("QSAG-WA" ++ "VE-HORNER-v1"), ("QSAG-WA" ++ "VE-PRODUCT-CHALLENGE-v1"), ("QSAG-WA" ++ "VE-PRODUCT-COIN-v1"), ("QSAG-WA" ++ "VE-PRODUCT-ROUND-v2"), ("QSAG-WA" ++ "VE-PRODUCT-WEIGHTS-v1"),
    ("QSAG-WA" ++ "VE-STREAM-v1"), ("QSAG-WA" ++ "VE-TRANSCRIPT-v1"), "QSAG.ABIT.CHI/v1", "QSAG.ABIT.COL/v1", "QSAG.BAGGY.DIGEST/v1", "QSAG.BAGGY.HMSG/v1", "QSAG.BAGGY.KEYID/v1", "QSAG.BAGGY.OPTRAND/v1",
    "QSAG.BAGGY.PARAMS/v1", "QSAG.BAGGY.PRECOMPUTE.RELEASE/v1", "QSAG.BAGGY.R/v1", "QSAG.BAGGY.WAISTBAND.CODEWORD_TAG/v1", "QSAG.BAGGY.WAISTBAND.PK_TAG/v1", "QSAG.BASE_OT.PROOF/v2", "QSAG.BDOZ.GF256.LHL_H/v1", "QSAG.BELT.ECHO.KEY/v1",
    "QSAG.BELT.ECHO.MAC/v1", "QSAG.BELT.LATCH.BINDING/v1", "QSAG.BELT.LATCH.WAL.MAC/v2", "QSAG.BELT.LATCH.WAL/v1", "QSAG.CEREMONY.JOURNAL.MAC/v3", "QSAG.COIN.COMMIT/v1", "QSAG.COIN.DERIVE/v1", "QSAG.COIN.PERMUTATION/v1",
    "QSAG.CRH", "QSAG.CRYPTO.FS.ABSORB/v1", "QSAG.CRYPTO.FS.BIND/v1", "QSAG.CRYPTO.FS.INSTANCE/v1", "QSAG.CRYPTO.FS.RATCHET/v1", "QSAG.CRYPTO.FS.SEED/v1", "QSAG.CRYPTO.FS.SQUEEZE/v1", "QSAG.DKG.FELDMAN.V2",
    "QSAG.DKG.GF256.BOOL.AUTH/v1", "QSAG.DKG.GF256.BOOL.MASK/v1", "QSAG.DKG.GL.BOOL.AUTH/v1", "QSAG.DKG.SCHNORR.CHAL/v1", "QSAG.DPCG.ACTIVE.PRODUCT/v1", "QSAG.DPCG.BVRCRH", "QSAG.DPCG.GGM.N2", "QSAG.DPCG.LPNTAP",
    "QSAG.DPCG.ROOTS/v2", "QSAG.DPCG.SEED.ID/v2", "QSAG.DPCG.SILENT.OT/v1", "QSAG.DPCG.SPCOT.CHAL/v1", "QSAG.DPCG.SPCOT.COIN/v1", "QSAG.DPCG.SPCOT.LHL.BIND/v2", "QSAG.DPCG.SPCOT.LHL.COIN/v1", "QSAG.DPCG.SPCOT.LHL.MAT/v1",
    "QSAG.DPCG.SPCOT.TAG/v1", "QSAG.DPCG.SPCOT.TR/v1", "QSAG.EPOCH.CUSTODIAN.ACK/v1", "QSAG.FIPS205.PROFILE.V1", "QSAG.FIRST_SIGNED.V1", "QSAG.GILBOA.GL.LHL_G/v1", "QSAG.HEDGED_RNG.V1", "QSAG.JORTS.BIND/v1",
    "QSAG.JORTS.DIGEST/v1", "QSAG.LEDGER.MAC/v2", "QSAG.MASCOT.AUTH.CHI/v1", "QSAG.MASCOT.COMBINE/v1", "QSAG.MASCOT.COPE.PRG/v1", "QSAG.MASCOT.DCOT.DIAG/v1", "QSAG.MASCOT.SAC.THETA/v1", "QSAG.MU/v2",
    "QSAG.OT.", "QSAG.OT.COMBINER.COIN.COM/v1", "QSAG.OT.COMBINER.COMMIT/v1", "QSAG.OT.COMBINER.EXT/v1", "QSAG.OT.CRS.COIN.COM/v1", "QSAG.OT.CRS.COMMIT/v1", "QSAG.OT.EXT.COL/v2", "QSAG.OT.KOS.BIND/v2",
    "QSAG.OT.KOS.ICHAL/v2", "QSAG.OT.KOS.UCOLS/v2", "QSAG.OT.MESH.RECEIVER/v1", "QSAG.OT.MESH.SENDER/v1", "QSAG.OT.PARCOMB.RNG/v1", "QSAG.OT.RLWE.CRS.COIN/v1", "QSAG.OT.RLWE.CRS/v1", "QSAG.OT.RLWE.CRS/v2",
    "QSAG.OT.RLWE.FO.STREAM/v2", "QSAG.OT.RLWE.FO/v2", "QSAG.OT.RLWE.ZKPOK/v3", "QSAG.PARTY.RNG.INIT/v1", "QSAG.PCG.GGM.LEVEL/v1", "QSAG.PCG.LEAF.EXPAND/v1", "QSAG.PCG.SILENT.CHOSEN.OT/v1", "QSAG.PCG.SILENT.OT.PAD/v1",
    "QSAG.PCG.SPCOT.BIND/v1", "QSAG.PCG.SPCOT.FS_CHAL/v1", "QSAG.POS2.KEY.AUTH/v1", "QSAG.POS2.UNIFIED.ALPHA/v1", "QSAG.POS2.VAULT.POW7/v1", "QSAG.PQ.BAGGYSIG.DET/v1", "QSAG.PQ.DKG.CHAL/v2", "QSAG.PQ.DKG.COMMIT/v1",
    "QSAG.PQ.DKG.R1.TRANS/v2", "QSAG.PQ.EPOCH_LATCH.BIND/v1", "QSAG.PQ.EPOCH_LATCH/v1", "QSAG.PQ.FS_WAL_LATCH/v1", "QSAG.PQ.HINT/v1", "QSAG.PQ.HMSG/v1", "QSAG.PQ.HXOF/v1", "QSAG.PQ.HYBRID.ID/v1",
    "QSAG.PQ.HYBRID.MSG/v1", "QSAG.PQ.PRE/v1", "QSAG.PQ.PRF/v1", "QSAG.PQ.PRFMSG/v1", "QSAG.PQ.STATELESS.DET/v1", "QSAG.PQ.SUITE.CSHAKE256/v1", "QSAG.PQ.SUITE.POSEIDON2/v1", "QSAG.PQ.TH_F/v1",
    "QSAG.PQ.TH_H/v1", "QSAG.PQ.TH_TL/v1", "QSAG.PRG", "QSAG.PUBLIC.COIN.COM/v1", "QSAG.PUBLIC.COIN.OUT/v1", "QSAG.PUBLIC.PERM/v1", "QSAG.RSS.CHI.MASK/v2", "QSAG.RSS.CHI.MASK/v3",
    "QSAG.RSS.DKG.PK.COM/v1", "QSAG.RSS.DZK.RHOS.POLY/v2", "QSAG.RSS.DZK.WEIGHTS.POLY/v3", "QSAG.RSS.DZK.ZPRG.POLY/v2", "QSAG.RSS.DZK.ZPRG.POLY/v3", "QSAG.RSS.MASK.HEDGE/v1", "QSAG.RSS.TRIPLE.PRG/v1", "QSAG.RSS.U64.OPEN.COM/v1",
    "QSAG.R_COMMIT/v1", "QSAG.SEED_BURN.V1", "QSAG.SPDZ.BS64.BATCH.CHIS/v1", "QSAG.SPDZ.BS64.BATCH.DIG/v1", "QSAG.SPDZ.BS64.BATCH.MAC.CHI/v1", "QSAG.SPDZ.BS64.BATCH.MAC.COM/v1", "QSAG.SPDZ.BS64.BATCH.OPEN.COM/v1", "QSAG.SPDZ.BS64.CHIS/v1",
    "QSAG.SPDZ.BS64.DEG.COM/v1", "QSAG.SPDZ.BS64.DIG/v1", "QSAG.SPDZ.BS64.LHL_H/v1", "QSAG.SPDZ.BS64.LHL_H/v2", "QSAG.SPDZ.BS64.MAC.COM/v1", "QSAG.SPDZ.BS64.OPEN.COM/v1", "QSAG.SPDZ.BS64.PIMAC_W/v1", "QSAG.SPDZ.BS64.PIMAC_W_BLK/v1",
    "QSAG.SPDZ.EXT2.DEG.COM/v1", "QSAG.SPDZ.EXT2.MAC.COM/v1", "QSAG.SPDZ.EXT2.OPEN.COM/v1", "QSAG.SPDZ.GF256.DEG.COM/v1", "QSAG.SPDZ.GF256.MAC.COM/v1", "QSAG.SPDZ.GF256.OPEN.COM/v1", "QSAG.SPDZ.GL.BATCH.CHIS/v1", "QSAG.SPDZ.GL.BATCH.DIG/v1",
    "QSAG.SPDZ.GL.BATCH.MAC.CHI/v1", "QSAG.SPDZ.GL.BATCH.MAC.COM/v1", "QSAG.SPDZ.GL.BATCH.OPEN.COM/v1", "QSAG.SPDZ.GL.LHL_H/v2", "QSAG.SPDZ.GL.MAC.COM/v1", "QSAG.SPDZ.GL.OPEN.COM/v1", "QSAG.SPDZ.GL.PIMAC_W/v1", "QSAG.SPDZ.KECCAK.DE.COM/v1",
    "QSAG.SPDZ.KECCAK.PEND.CHIS/v1", "QSAG.SPDZ.KECCAK.PEND.DIG/v1", "QSAG.SPDZ.KECCAK.PEND.MAC.COM/v1", "QSAG.SPDZ.T128.DEG.COM/v1", "QSAG.SPDZ.T128.OPEN.COM/v1", "QSAG.TH.PRF/v1", "QSAG.TH.TWEAK/v1", "QSAG.TPM2.ANCHOR.MAC/v1",
    "QSAG.TRIPLE.F2.CHI/v1", "QSAG.TRIPLE.F2.DEAL/v1", "QSAG.TRIPLE.F2.LOCK.COMMIT/v1", "QSAG.TRIPLE.F2.LOCK.DIGEST/v1", "QSAG.TRIPLE.F2.OPEN.COM/v1", "QSAG.TRIPLE.F2.SAC/v1", "QSAG.TRIPLE.F2.TRANSCRIPT/v1", "QSAG.TSW.FAULT.CACHE/v1",
    "QSAG.TSW.FAULT.KEY/v1", "QSAG.TSW.RSS.OPT_RAND/v1", "QSAG.TSW.RSS.PARAMS.DIGEST/v1", "QSAG.VMGENID.ANCHOR.MAC/v1", "QSAGBLT1", "QSAGCRJ3", "QSAGDPC1", "QSAGDPC2",
    "QSAGDPC3", "QSAGLDG2", "QSAGLTC1", "QSAGWAL1", "QSAGWAL2"]),
  ("qsag-cred", [
    "QSAG.BLIND_VC.ISSUE_ZK.V1", "QSAG.BLIND_VC.SCOPE.V1", "QSAG.BLIND_VC.SCOPE_GL.V1", "QSAG.BLIND_VC.SD_ZK.V1", "QSAG.MLDSA.NONCE_BURN.V2", "QSAG.MLDSA.PENDING_CIPHER.V1", "QSAG.MLDSA.PENDING_CT_TAG.V1", "QSAG.MLDSA.SEAL_KEY.V1",
    "QSAG.POLICY.KEY.V1", "QSAG.RSS.KEY.V1", "QSAG.RSS.KEYCONFIRM.V1", "QSAG.RSS.KEYSHARE.V1", "QSAG.RSS.OPEN.BIN.V1", "QSAG.RSS.OPEN.V1", "QSAG.RSS.PRSS.V1", "QSAG.RSS.VIEW.BIN.V1",
    "QSAG.RSS.VIEW.DIGEST.V1", "QSAG.RSS.VIEW.INIT.V1", "QSAG.RSS.VIEW.V1", "QSAG.TMLDSA.CUSTODY.V1", "QSAG.TMLDSA.DKG.CONFIRM.V1", "QSAG.TMLDSA.DKG.CTX.V1", "QSAG.TMLDSA.DKG.RHO.V1", "QSAG.TMLDSA.SEAL_ENTROPY.V1",
    "QSAG.TMLDSA.SIGN.CTX.V1", "QSAG.TMLDSA.SIGN.ENTROPY.V1", "QSAG.TOPRF.CLIENT.SALT.V1", "QSAG.TOPRF.CLIENT.SHARE.V1", "QSAG.TOPRF.DKG.COMMIT.V1", "QSAG.TOPRF.DKG.COMMITS.V1", "QSAG.TOPRF.DKG.DELIVER.V1", "QSAG.TOPRF.DKG.JOINT.V1",
    "QSAG.TOPRF.DKG.SEED.V1", "QSAG.TOPRF.EVAL.V1", "QSAG.TOPRF.INPUT.BIND.V1", "QSAG.TOPRF.INPUT.CHECK.V1", "QSAG.TOPRF.INPUT.COMMIT.V1", "QSAG.TOPRF.INPUT.FIELD.V1", "QSAG.TOPRF.INPUT.V1", "QSAG.TOPRF.ISSUANCE.RECEIPT.V2",
    "QSAG.TOPRF.KEY.COMPONENT.V1", "QSAG.TOPRF.KEY.V1", "QSAG.TOPRF.LAYER.V2", "QSAG.TOPRF.OUTPUT.V1", "QSAG.TOPRF.REQUEST.CONTEXT.V1", "QSAG.TOPRF.REQUEST.V1", "QSAG.TOPRF.RESHARE.DIGEST.V2", "QSAG.TOPRF.RESHARE.V2",
    "QSAG.TOPRF.START.V1", "QSAG.TRANSPORT.V1", "QSAG.VC.ACC_ROOT_TAG.V1", "QSAG.VC.FRESH.V1", "QSAG.VC.HOLDER_BLIND.V1", "QSAG.VC.ISSUER_PK.V1", "QSAG.VC.ISS_IN_SH.V1", "QSAG.VC.ISS_SALT.V1",
    "QSAG.VC.ISS_STMT_DIGEST.V1", "QSAG.VC.ISS_TAPE.V1", "QSAG.VC.ISS_ZK_SEED.V1", "QSAG.VC.PRES_BLIND.V1", "QSAG.VC.PRES_NONCE.V1", "QSAG.VC.PROFILE.Quantum128:438", "QSAG.VC.ROOT_ATTEST.CTX.V1", "QSAG.VC.ROOT_ATTEST.V1",
    "QSAG.VC.SCOPED.V1", "QSAG.VC.SD_IN_SH.V1", "QSAG.VC.SD_SALT.V1", "QSAG.VC.SD_STMT_DIGEST.V1", "QSAG.VC.SD_TAPE.V1", "QSAG.VC.SD_ZK_SEED.V1", "QSAG.VC.VIEW_COM.V1", "QSAG.VC.ZKBOO_R.V1"]),
  ("qsag-fts", [
    "QSAG.BURN.GENESIS.ID.V2", "QSAG.BURN.GENESIS.V4", "QSAG.BURN.HWM.V4", "QSAG.BURN.RECORD.V2", "QSAG.CUSTODY.KOS.V1", "QSAG.CUSTODY.OT.CHUNK.V1", "QSAG.CUSTODY.OT.PAD.V1", "QSAG.DKG.CHECK.COIN.V1",
    "QSAG.DKG.CHECK.COIN_COMMIT.V1", "QSAG.DKG.CHECK.CONTEXT.V1", "QSAG.DKG.CHECK.FOLD_WEIGHTS.V1", "QSAG.DKG.CHECK.JOINT_COIN.V1", "QSAG.DKG.CHECK.MAC_WEIGHTS.V1", "QSAG.DKG.CHECK.SACRIFICE_T.V1", "QSAG.DKG.CHECK.SHARES.V1", "QSAG.DKG.CHECK.TAG_COMMIT.V1",
    "QSAG.DKG.CHECK.TAG_SALT.V1", "QSAG.DKG.COIN.V1", "QSAG.DKG.COMMIT.V1", "QSAG.DKG.CONTEXT.V1", "QSAG.DKG.CORRELATIONS.V1", "QSAG.DKG.FROZEN.V1", "QSAG.DKG.OT.BATCH.V1", "QSAG.DKG.OT.PADS.V1",
    "QSAG.DKG.PAIR.V1", "QSAG.DKG.PRIVATE.V1", "QSAG.DKG.PRODUCT.V1", "QSAG.DKG.PUBLIC_SEED.V1", "QSAG.DKG.SALT.V1", "QSAG.FRONTIER.WAL.V1", "QSAG.FTS.CANDIDATE_BINDING.V1", "QSAG.FTS.CHAIN.V1",
    "QSAG.FTS.EPOCH.MESSAGE.V1", "QSAG.FTS.EPOCH.VOTE.V1", "QSAG.FTS.HMSG.V1", "QSAG.FTS.LEAF.V1", "QSAG.FTS.MERGE.V1", "QSAG.FTS.MSG256.V1", "QSAG.FTS.RAND.V1", "QSAG.PSFTS.ALPHA.V2",
    "QSAG.PSFTS.BAR_SALT.V2", "QSAG.PSFTS.BATCH_VALUES.V4", "QSAG.PSFTS.BATCH_WEIGHT.V4", "QSAG.PSFTS.BATCH_ZERO.V4", "QSAG.PSFTS.BEAVER_AB.V2", "QSAG.PSFTS.CHAIN_TWK.V2", "QSAG.PSFTS.DEAL_P0.V2", "QSAG.PSFTS.DEAL_P1.V2",
    "QSAG.PSFTS.DEAL_S0.V2", "QSAG.PSFTS.DEAL_S1.V2", "QSAG.PSFTS.DISTRIBUTED.V4", "QSAG.PSFTS.HMSG.V2", "QSAG.PSFTS.INTERMEDIATE.V5", "QSAG.PSFTS.INTERMEDIATE.ZERO.V5", "QSAG.PSFTS.KG.SK_PRF.V2", "QSAG.PSFTS.KG.SK_SEED.V2",
    "QSAG.PSFTS.MAC_W.V2", "QSAG.PSFTS.PAIR_ZERO_PRF.V2", "QSAG.PSFTS.PAIR_ZSEED.V2", "QSAG.PSFTS.POW7_ROUND.V4", "QSAG.PSFTS.POWER.V4", "QSAG.PSFTS.RAND_TWK.V2", "QSAG.PSFTS.ROUND_SALT.V4", "QSAG.PSFTS.SALT_SEED.V2",
    "QSAG.PSFTS.SEED_TWK.V2", "QSAG.PSFTS.SIGN_CONTEXT.V3", "QSAG.PSFTS.TILDE_DIGEST.V2"]),
  ("qsag-hd", [
    "QSAG.HD.CC.KEY.V1", "QSAG.HD.CHAIN_CODE.COMMIT.V1", "QSAG.HD.DEALERLESS.ROOT.V1", "QSAG.HD.DEALERLESS.ROOT_CC.V2", "QSAG.HD.DEALERLESS.SEED_A.V1", "QSAG.HD.EVAL.CONTEXT.V1", "QSAG.HD.EVAL.MAC_SALT.V1", "QSAG.HD.EVAL.VALUE_SALT.V1",
    "QSAG.HD.HARDENED_CC.V2", "QSAG.HD.INV.SLH128F.ROOT32.V2", "QSAG.HD.INV.TPRF.CHILD.V1", "QSAG.HD.LMOD.ALPHA.V2", "QSAG.HD.LMOD.MAC.V2", "QSAG.HD.LMOD.MAT_A.V1", "QSAG.HD.LMOD.NEXT_CC.V1", "QSAG.HD.LMOD.PK_HASH.V1",
    "QSAG.HD.LMOD.ROOT_CC.V2", "QSAG.HD.LMOD.ROOT_S.V2", "QSAG.HD.LMOD.R_POLY.V2", "QSAG.HD.LMOD.SEED_A.V2", "QSAG.HD.LMOD.SHAMIR.V2", "QSAG.HD.LMOD.TWEAK_SEED.V1", "QSAG.HD.OPENING_ZERO.CONTEXT.V1", "QSAG.HD.OPENING_ZERO.DEALERLESS.V1",
    "QSAG.HD.OPENING_ZERO.PAIR.V1", "QSAG.HD.OPENING_ZERO.V1", "QSAG.HD.POISON.V2", "QSAG.HD.QUERY_BUDGET.HWM.V3", "QSAG.HD.QUERY_BUDGET.V2", "QSAG.HD.REKEY.CHALLENGE.V1", "QSAG.HD.REKEY.COIN.V1", "QSAG.HD.REKEY.COIN_SALT.V1",
    "QSAG.HD.REKEY.LOCAL.V1", "QSAG.HD.REKEY.NONCE.V1", "QSAG.HD.REKEY.PRODUCTS.V1", "QSAG.HD.REKEY.PRSS.KEYS.V1", "QSAG.HD.REKEY.PRSS.MASKS.V1", "QSAG.HD.REKEY.REQUEST.V1", "QSAG.HD.REKEY.SESSION.V1", "QSAG.HD.REKEY.STATE.V1",
    "QSAG.HD.REKEY.ZERO_SALT.V1", "QSAG.HD.SEEDS.CEREMONY.V1", "QSAG.HD.SEEDS.COMMIT.V1", "QSAG.HD.SEEDS.CONFIG.V1", "QSAG.HD.SEEDS.CONFIRM.V1", "QSAG.HD.SEEDS.CONTRIBUTION.V1", "QSAG.HD.SEEDS.KEY.V1", "QSAG.HD.SEEDS.SALT.V1",
    "QSAG.HD.SEEDS.STREAM.V1", "QSAG.HD.SEEDS.TRANSCRIPT.V1", "QSAG.HD.TPRF.DERIVATION.V1", "QSAG.HD.TPRF.R_POLY.V1", "QSAG.HD.TPRF.TWEAK.V1", "QSAG.HD.ZERO_TEST.PEER_TRANSCRIPT.V1", "QSAGREC1"]),
  ("qsag-migrate", [
    "QSAG.BLS12_381.CAMPAIGN.V1", "QSAG.BLS12_381.HEDGE.V1", "QSAG.BLS12_381.MIGRATE.STMT.V1", "QSAG.BLS12_381.MIGRATE.V1", "QSAG.BLS12_381.SEEDS.V1", "QSAG.MIGRATE.CAMPAIGN.V3", "QSAG.MIGRATE.CHALLENGES.V3", "QSAG.MIGRATE.HEDGE.V4",
    "QSAG.MIGRATE.REPETITION.V3", "QSAG.MIGRATE.ROOT.V3", "QSAG.MIGRATE.SEEDS.V3", "QSAG.MIGRATE.TAPE.V3", "QSAG.MIGRATE.V3", "QSAG.MIGRATE.VIEW.V3", "QSAG.OUTER.BATCH.ENTROPY.V1", "QSAG.OUTER.BATCH.V1",
    "QSAG.OUTER.COIN.COMMIT.V1", "QSAG.OUTER.COIN.DERIVE.V1", "QSAG.OUTER.COIN.HEDGE.V1", "QSAG.OUTER.COIN.RNG.V1", "QSAG.OUTER.COMPLETE.V1", "QSAG.OUTER.FREEZE.V1", "QSAG.OUTER.MESSAGE.V1", "QSAG.OUTER.MULCHECK.BITS.BASE.V1",
    "QSAG.OUTER.MULCHECK.BITS.FOLD.V1", "QSAG.OUTER.MULCHECK.BITS.INIT.V1", "QSAG.OUTER.MULCHECK.BITS.SUMCHECK.V1", "QSAG.OUTER.MULCHECK.FP.BASE.V1", "QSAG.OUTER.MULCHECK.FP.FOLD.V1", "QSAG.OUTER.MULCHECK.FP.INIT.V1", "QSAG.OUTER.MULCHECK.GOLD.BASE.V1", "QSAG.OUTER.MULCHECK.GOLD.FOLD.V1",
    "QSAG.OUTER.MULCHECK.GOLD.INIT.V1", "QSAG.OUTER.PADS.V1", "QSAG.OUTER.PRECOMMIT.V1", "QSAG.OUTER.SEED.V1", "QSAG.OUTER.STATEMENT.V1", "QSAG.PALLAS.CAMPAIGN.V1", "QSAG.PALLAS.HEDGE.V1", "QSAG.PALLAS.MIGRATE.STMT.V1",
    "QSAG.PALLAS.MIGRATE.V1", "QSAG.PALLAS.SEEDS.V1", "QSAG.TEST.PROOF.PARITY"]),
  ("qsag-policy", [
    "QSAG.POLICY.ALPHA_SH.V2", "QSAG.POLICY.AUTO_NONCE.V1", "QSAG.POLICY.BARRIER_W.V3", "QSAG.POLICY.BDOZ_KEY.V2", "QSAG.POLICY.COMMIT_SALT.V2", "QSAG.POLICY.CTX.V1", "QSAG.POLICY.DELTA_SALT.V1", "QSAG.POLICY.DKG.ALPHA.V1",
    "QSAG.POLICY.DKG.LOCAL.V1", "QSAG.POLICY.DKG.OT_PAD.V1", "QSAG.POLICY.DKG.PAIR.V1", "QSAG.POLICY.DKG.R.V1", "QSAG.POLICY.DKG.SEED.V1", "QSAG.POLICY.DKG.SEED_COMMIT.V1", "QSAG.POLICY.DKG.V1", "QSAG.POLICY.DKG.ZERO.V1",
    "QSAG.POLICY.DURABLE_KEY.V2", "QSAG.POLICY.DURABLE_LEDGER.V5", "QSAG.POLICY.FS.SEAL.V2", "QSAG.POLICY.GEN.FENCE.V2", "QSAG.POLICY.GUARD_BINDING.V1", "QSAG.POLICY.INITIATOR_AUTH_MAC.V1", "QSAG.POLICY.INITIATOR_AUTH_PREIMAGE.V1", "QSAG.POLICY.INITIATOR_SELF_MAC.V1",
    "QSAG.POLICY.INTENT.V2", "QSAG.POLICY.LOCAL_SALT.V2", "QSAG.POLICY.MSG.V1", "QSAG.POLICY.PAIR_WEIGHT.V1", "QSAG.POLICY.PAIR_WEIGHT.V3", "QSAG.POLICY.PAIR_ZERO_PRF.V2", "QSAG.POLICY.PAIR_ZSEED.V2", "QSAG.POLICY.PAYLOAD.V2",
    "QSAG.POLICY.PEER_SLOT_ALPHA.V1", "QSAG.POLICY.PREPROC_R.V2", "QSAG.POLICY.QUORUM_SET.V2", "QSAG.POLICY.SHARED_LEDGER.V1", "QSAG.POLICY.SIGMA_SALT.V1", "QSAG.POLICY.SIGNED_INTENT.V2", "QSAG.POLICY.SPEC.V1", "QSAG.POLICY.VERIFIED_DELTAS.V2",
    "QSAG.POLICY.WINDOW_ADVANCE/v1", "QSAG.POLICY.WINDOW_KEY/v1", "QSAG.POLICY.WIRE_META.V1"]),
  ("qsag-quorum", [
    "QSAG.DIRECTORY.ANCHOR.V1", "QSAG.FIRST_SIGNED.V1", "QSAG.HEM.EPOCH.ACK/v1", "QSAG.HEM.LATCH.KEY/v1", "QSAG.HEM.QSA.ECHO/v1", "QSAG.HEM.QSA.PKSEED/v1", "QSAG.HEM.QSA.RNG.STREAM/v1", "QSAG.HEM.QSA.RNG/v1",
    "QSAG.HEM.QSA.SKPRF/v1", "QSAG.HEM.QSA.SKSEED/v1", "QSAG.HEM.QSB.CHAL.STREAM/v1", "QSAG.HEM.QSB.CHAL/v1", "QSAG.HEM.QSB.COMMIT/v1", "QSAG.HEM.QSB.DEALER.RNG/v1", "QSAG.HEM.QSB.DEALER.STREAM/v1", "QSAG.HEM.QSB.LATCH.RESTORE.STREAM/v1",
    "QSAG.HEM.QSB.LATCH.RESTORE/v1", "QSAG.HEM.QSB.MACCHK.AUTH/v1", "QSAG.HEM.QSB.MACCHK.OT/v1", "QSAG.HEM.QSB.MACCHK.RNG/v1", "QSAG.HEM.QSB.MACCHK.STREAM/v1", "QSAG.HEM.QSB.NEW.LATCH.STREAM/v1", "QSAG.HEM.QSB.NEW.LATCH/v1", "QSAG.HEM.QSB.PKSEED/v1",
    "QSAG.HEM.QSB.RNG.STREAM/v1", "QSAG.HEM.QSB.RNG/v1", "QSAG.HEM.QSB.SKPRF/v1", "QSAG.HEM.QSB.SKSEED/v1", "QSAG.HEM.SPDZ.DKG.PRF/v1", "QSAG.HEM.SPDZ.DKG.SEED/v1", "QSAG.HEM.SPDZ.KEYGEN.ONLINE/v1", "QSAG.HEM.SPDZ.KEYGEN.PREP/v1",
    "QSAG.HEM.SPDZ.OT/v1", "QSAG.HEM.SPDZ.REF.PRF/v1", "QSAG.HEM.SPDZ.REF.RNG/v1", "QSAG.HEM.SPDZ.REF.SEED/v1", "QSAG.HEM.SPDZ.REF.STREAM/v1", "QSAG.HEM.SPDZ.RESHARE.NEW.STREAM/v1", "QSAG.HEM.SPDZ.RESHARE.NEW/v1", "QSAG.HEM.SPDZ.RESHARE.OLD.STREAM/v1",
    "QSAG.HEM.SPDZ.RESHARE.OLD/v1", "QSAG.HEM.SPDZ.RESHARE.OT/v1", "QSAG.HEM.SPDZ.RESHARE.P/v1", "QSAG.HEM.SPDZ.RESHARE.S/v1", "QSAG.HEM.SPDZ.RESHARE.VCHK/v1", "QSAG.HEM.SPDZ.RESHARE.VOT/v1", "QSAG.HEM.SPDZ.RESHARE.VPREP/v1", "QSAG.HEM.SPDZ.RESHARE.VRNG.STREAM/v1",
    "QSAG.HEM.SPDZ.RESHARE.VRNG/v1", "QSAG.HEM.SPDZ.RNG.STREAM/v1", "QSAG.HEM.SPDZ.RNG/v1", "QSAG.HEM.SPDZ.SIGN.ONLINE/v1", "QSAG.HEM.SPDZ.SIGN.OT/v1", "QSAG.HEM.SPDZ.SIGN.PREP/v1", "QSAG.HEM.SPDZ.SIGN.RNG/v1", "QSAG.HEM.SPDZ.SIGN.STREAM/v1",
    "QSAG.POISON.JOURNAL/v2", "QSAG.POISON.LOCK_NONCE/v2", "QSAG.QUORUM.ACK.MAC/v1", "QSAG.QUORUM.ANCHORED_CUSTODY.KEY.V1", "QSAG.QUORUM.BELT_GUARD/v1", "QSAG.QUORUM.BELT_WAL_KEY/v1", "QSAG.QUORUM.BINDING/v1", "QSAG.QUORUM.CHAIN/v1",
    "QSAG.QUORUM.CHECKPOINT.ANCHOR.V1", "QSAG.QUORUM.DIGEST/v1", "QSAG.QUORUM.DZK.POINTS/v1", "QSAG.QUORUM.DZK.WEIGHTS/v1", "QSAG.QUORUM.ECHO.MAC/v1", "QSAG.QUORUM.LEAF.UNASSIGNED/v1", "QSAG.QUORUM.LEAF/v1", "QSAG.QUORUM.MSG/v1",
    "QSAG.QUORUM.NODE/v1", "QSAG.QUORUM.PAIR.KEY/v1", "QSAG.QUORUM.RNG.BLOCK/v1", "QSAG.QUORUM.RNG.KEY/v1", "QSAG.QUORUM.RSS.COIN.COMMIT/v1", "QSAG.QUORUM.RSS.COIN.ECHO.MAC/v1", "QSAG.QUORUM.RSS.COIN.ECHO/v1", "QSAG.QUORUM.RSS.DEAL/v1",
    "QSAG.QUORUM.RSS.DZK.PRG/v1", "QSAG.QUORUM.RSS.SEED.A/v1", "QSAG.QUORUM.RSS.SEED.B/v1", "QSAG.QUORUM.RSS.VERDICT/v1", "QSAG.QUORUM.STAGE.PKSEED/v1", "QSAG.QUORUM.STAGE.SK/v1", "QSAG.QUORUM.WAL_RECEIPT/v1", "QSAG.QUORUM.WIRE_DIRECTION/v1",
    "QSAG.QUORUM.WIRE_ENC_KEY/v1", "QSAG.QUORUM.WIRE_MAC/v1", "QSAG.QUORUM.WIRE_MAC_KEY/v1", "QSAG.QUORUM.WIRE_RATCHET/v1", "QSAG.QUORUM.WIRE_STREAM/v1", "QSAG.RSS.OPEN.BINDING/v1", "QSAG.RSS.OPEN.COPY/v1", "QSAG.RSS.SESSION.MAC/v1",
    "QSAG.SEED_BURN.V1", "QSAGCKP1", "QSAGHDIR", "QSAGHSHR"])
]

theorem digest5_modular_pair_tooth : ∃ a b : BitVec 256,
    digest5FromBitVec256 a ≠ digest5FromBitVec256 b ∧
    naiveLimb a.toNat = naiveLimb b.toNat :=
  ⟨0, BitVec.ofNat 256 goldilocksPrime, digest5_vs_modular_tooth⟩

theorem transcript_witness : ∃ p : SimpleEquiv (State Goldilocks) (State Goldilocks),
    ∃ t : List (State Goldilocks × State Goldilocks), ∃ x y : State Goldilocks,
    ∃ target : Goldilocks, Consistent p t ∧ (x, y) ∈ t ∧
      jiveCompress (fun _ => zero) p x = target := by
  let x : State Goldilocks := (zero, zero, zero)
  refine ⟨SimpleEquiv.refl _, [(x, x)], x, x, zero, ?_, by simp, ?_⟩
  · intro a b h; have e := List.mem_singleton.mp h; cases e; rfl
  · decide

theorem digest5_collision_reduction (a b : BitVec 256)
    (h : digest5FromBitVec256 a = digest5FromBitVec256 b) : a = b :=
  digest5FromBitVec256_injective h

theorem digest_reduction_witness : ∃ a b : BitVec 256,
    digest5FromBitVec256 a = digest5FromBitVec256 b := ⟨0, 0, rfl⟩

#verify_constructive bidirectional_bad_count
#verify_constructive extensions_complete extensions_nodup conditional_extension_density
  width12_fiber_cardinality unchecked_preimage_tooth
#verify_constructive transcript_witness digest5_collision_reduction digest_reduction_witness
#verify_constructive raw_inverse raw_inverse_fixed_capacity inverse_feedforward_relation
  raw_vs_feedforward_tooth identity_collision_tooth forward_extension inverse_extension
  checked_preimage_is_transcript_hit preimage_target_count unorderedPairs_count
  collision_candidate_count extensions_count extensions_are_permutations fresh_answer_weight
  forward_fiber_complete inverse_fiber_complete fiber_counts fresh_bad_extensions_bound
  outer_reprogram_zero_drift digest5_collision_iff marked_bytes_collision_iff
  naive_limb_collision_family naive_family_distinct digest5_vs_modular_tooth
  iv_tags_canonical_distinct canonical_iv_separation additive_iv_tooth
  universal_customization_partition foreign_reprogram_unchanged runOracle_ext
  isolated_game_zero_drift fips_adrs_type_partition fips_universal_partition_tooth
  unprefixed_chosen_message_tooth permutation_witness digest_witness partition_witness
  unframed_partition_tooth digest5_modular_pair_tooth
#verify_inhabited checked_preimage_is_transcript_hit transcript_witness
#verify_inhabited digest5_collision_reduction digest_reduction_witness
#verify_inhabited universal_customization_partition partition_witness
#tooth_pair inverse_feedforward_relation vs raw_vs_feedforward_tooth
#tooth_pair digest5_collision_iff vs digest5_modular_pair_tooth
#tooth_pair universal_customization_partition vs unframed_partition_tooth
end Qsag.CrossProtocol
end
