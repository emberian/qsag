module
/-
# Qsag.Oracle.SpnRoundConstantExperiment — who is random in the 48-round x^7 SPN experiments

`ParallelSeededSpnSecurity` proves component facts (x^7 root count, branch number, active-box
count) and `HashTrailSampling` shows that the product of root fractions is a probability only
for fresh gate inputs, never for a trail of one fixed permutation. This module supplies the
experiment in which the product IS a probability for the actual round function, and the
statements that survive for the other choices of randomness. The sample space is always an
explicit list; a probability is `count / length`.

Roles. `s`, `s'` are the two 256-bit inputs; `ks` is the list of 48 round-constant pairs
(Rust `round_constants`, public cSHAKE output); `keys` is the duplicate-free list a lane
constant is drawn from (`2^128` elements in deployment).

* **Committed experiment (§3 here; differentials and Davies–Meyer in
  `Qsag.SpnCommittedDifferential`).** The adversary fixes `s ≠ s'` (and a trail or an output
  difference) first; the 48 constant pairs are then drawn uniformly and independently.
  - `spnTrailCount_le`: a committed S-box trail is followed by at most the product of the
    per-lane root counts (the Markov-cipher product, proved by peeling one round at a time).
  - `spn48_committed_trail_count_le`, `spn48_committed_trail_atLeast_256_bits`: with
    `spn48_active_sboxes_ge_72` this is `(6/N)^72`; it is the first statement in which
    `spn48_differential_trail_security_bounds` bounds an event.
  - `spn_differential_count_le`: a committed differential (all trails summed, i.e. the hull)
    has probability at most `(6/N)^2` over any number `≥ 2` of rounds. The trail product does
    NOT bound the differential; `36/N^2` is what the two-lane branch number gives.
  - `spn48_davies_meyer_committed_pair_collision_count_le`: a committed pair collides under
    the actual `spnDaviesMeyer48` with probability at most `36/N^2` (`> 250` bits).
* **Adaptive control (§3).** `spn_adaptive_trail_always_realized`: a trail chosen after the
  constants are published is followed with probability one. Deployment publishes the
  constants, so the committed bounds above do not cover an attacker who reads them first.
* **Davies–Meyer control (`Qsag.SpnCommittedDifferential`).** `tooth_xor_constant_permutation_davies_meyer_collapses`:
  a bijective permutation whose feed-forward is constant. Invertibility implies nothing.

Not proved here: independence of the cSHAKE-derived constants (a random-oracle idealisation),
any bound for an adversary who picks inputs after seeing the constants (collision, preimage
or one-wayness of the fixed public permutation), and the polynomial-basis representation.
-/
public import Qsag.Oracle.HashTrailSampling
import all Qsag.Oracle.HashTrailSampling
import all Qsag.Oracle.ParallelSeededSpnSecurity

public section
namespace Qsag
set_option autoImplicit false

/-! ## §1. Finite sums over explicit sample lists -/

/-- Sum of a `Nat`-valued function over a list. -/
def rcSum {α : Type} (f : α → Nat) : List α → Nat
  | [] => 0
  | x :: xs => f x + rcSum f xs

theorem rcSum_le_of_le {α : Type} (f g : α → Nat) (l : List α)
    (h : ∀ x ∈ l, f x ≤ g x) : rcSum f l ≤ rcSum g l := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    exact Nat.add_le_add (h x List.mem_cons_self)
      (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem rcSum_const {α : Type} (c : Nat) (l : List α) :
    rcSum (fun _ => c) l = l.length * c := by
  induction l with
  | nil => exact (Nat.zero_mul c).symm
  | cons x xs ih =>
    show c + rcSum (fun _ => c) xs = (xs.length + 1) * c
    rw [ih, Nat.succ_mul, Nat.add_comm]

theorem rcSum_le_const {α : Type} (f : α → Nat) (c : Nat) (l : List α)
    (h : ∀ x ∈ l, f x ≤ c) : rcSum f l ≤ l.length * c := by
  rw [← rcSum_const c l]
  exact rcSum_le_of_le f _ l h

theorem rcSum_ite {α : Type} (p : α → Bool) (c : Nat) (l : List α) :
    rcSum (fun x => if p x then c else 0) l = (l.filter p).length * c := by
  induction l with
  | nil => exact (Nat.zero_mul c).symm
  | cons x xs ih =>
    show (if p x then c else 0) + rcSum (fun x => if p x then c else 0) xs = _
    rw [ih]
    cases hp : p x
    · rw [List.filter_cons_of_neg (by rw [hp]; exact Bool.false_ne_true)]
      exact Nat.zero_add _
    · rw [List.filter_cons_of_pos hp, List.length_cons, Nat.succ_mul, Nat.add_comm]
      rfl

/-- Counting inside a Cartesian prefix: sum over the head of the count over the tails. -/
theorem filter_prefixAssignments_length {α : Type} (p : List α → Bool)
    (choices : List α) (tails : List (List α)) :
    ((prefixAssignments choices tails).filter p).length =
      rcSum (fun x => (tails.filter fun t => p (x :: t)).length) choices := by
  induction choices with
  | nil => rfl
  | cons x xs ih =>
    have hSplit : prefixAssignments (x :: xs) tails =
        tails.map (x :: ·) ++ prefixAssignments xs tails := by
      simp only [prefixAssignments, List.flatMap_cons]
    rw [hSplit, List.filter_append, List.length_append, ih, List.filter_map, List.length_map]
    rfl

theorem mem_freshInputAssignments_length {α : Type} (inputs : List α) :
    ∀ (n : Nat) (l : List α), l ∈ freshInputAssignments inputs n → l.length = n
  | 0, l, h => by
    have hl : l = [] := by simpa [freshInputAssignments] using h
    rw [hl]; rfl
  | n + 1, l, h => by
    simp only [freshInputAssignments, prefixAssignments, List.mem_flatMap, List.mem_map] at h
    obtain ⟨x, _, t, ht, rfl⟩ := h
    rw [List.length_cons, mem_freshInputAssignments_length inputs n t ht]

/-- All ordered pairs of lane constants: the sample list for one round. -/
def rcPairs {α : Type} (keys : List α) : List (α × α) :=
  keys.flatMap fun a => keys.map fun b => (a, b)

theorem filter_pairList_length {α : Type} (p : α × α → Bool) (l1 l2 : List α) :
    ((l1.flatMap fun a => l2.map fun b => (a, b)).filter p).length =
      rcSum (fun a => (l2.filter fun b => p (a, b)).length) l1 := by
  induction l1 with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons, List.filter_append, List.length_append, ih, List.filter_map,
      List.length_map]
    rfl

theorem filter_rcPairs_length {α : Type} (p : α × α → Bool) (keys : List α) :
    ((rcPairs keys).filter p).length =
      rcSum (fun a => (keys.filter fun b => p (a, b)).length) keys :=
  filter_pairList_length p keys keys

theorem pairList_length {α : Type} (l1 l2 : List α) :
    (l1.flatMap fun a => l2.map fun b => (a, b)).length = l1.length * l2.length := by
  induction l1 with
  | nil => exact (Nat.zero_mul _).symm
  | cons x xs ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_map, List.length_cons,
      Nat.succ_mul, Nat.add_comm]

theorem rcPairs_length {α : Type} (keys : List α) :
    (rcPairs keys).length = keys.length * keys.length := pairList_length keys keys

theorem filter_length_eq_zero {α : Type} (p : α → Bool) :
    ∀ l : List α, (∀ x ∈ l, ¬ p x = true) → (l.filter p).length = 0
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.filter_cons_of_neg (h x List.mem_cons_self)]
    exact filter_length_eq_zero p xs fun y hy => h y (List.mem_cons_of_mem _ hy)

theorem filter_singleton_length {α : Type} (p : α → Bool) (a : α) :
    ([a].filter p).length = if p a = true then 1 else 0 := by
  by_cases h : p a = true
  · rw [ite_eq_left h, List.filter_cons_of_pos h]; rfl
  · rw [ite_eq_right h, List.filter_cons_of_neg h]; rfl

theorem rcNodup_map_of_injective {α β : Type} (f : α → β)
    (hInj : ∀ a b, f a = f b → a = b) :
    ∀ l : List α, l.Nodup → (l.map f).Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    have hx := List.nodup_cons.mp h
    rw [List.map_cons]
    refine List.nodup_cons.mpr ⟨fun hm => ?_, rcNodup_map_of_injective f hInj xs hx.2⟩
    obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hm
    have hEq := hInj _ _ hfy
    rw [hEq] at hy
    exact hx.1 hy

/-! ## §2. One lane and one round -/

theorem tadd_eq_zero_iff (a b : Tower128) : towerAdd 7 a b = towerZero 7 ↔ a = b := by
  refine ⟨fun h => ?_, fun h => by rw [h, towerAdd_self_zero]⟩
  have h2 := congrArg (fun z => towerAdd 7 z b) h
  simpa only [towerZero_add, towerAdd_assoc, towerAdd_self_zero, towerAdd_zero] using h2

theorem tadd_shift (t t' k : Tower128) :
    towerAdd 7 (towerAdd 7 t' k) (towerAdd 7 t t') = towerAdd 7 t k := by
  rw [towerAdd_comm 7 t t', towerAdd_comm 7 t' k, towerAdd_assoc, ← towerAdd_assoc 7 t' t' t,
    towerAdd_self_zero, towerZero_add, towerAdd_comm]

theorem tadd_swap (a b c d : Tower128) :
    towerAdd 7 (towerAdd 7 a b) (towerAdd 7 c d) =
      towerAdd 7 (towerAdd 7 a c) (towerAdd 7 b d) := by
  rw [towerAdd_assoc, towerAdd_left_comm 7 b c d, ← towerAdd_assoc]

/-- `a ⊕ b = c ⊕ d` exactly when `a ⊕ c = b ⊕ d`. -/
theorem tadd_cross_iff (a b c d : Tower128) :
    towerAdd 7 a b = towerAdd 7 c d ↔ towerAdd 7 a c = towerAdd 7 b d := by
  rw [← tadd_eq_zero_iff (towerAdd 7 a b), ← tadd_eq_zero_iff (towerAdd 7 a c), tadd_swap]

/-- Output difference of one x^7 gate whose two inputs `t`, `t'` receive the same constant. -/
def sboxLaneDiff (k t t' : Tower128) : Tower128 :=
  towerAdd 7 (towerSbox7 7 (towerAdd 7 t k)) (towerSbox7 7 (towerAdd 7 t' k))

theorem sboxLaneDiff_eq_zero_iff (k t t' : Tower128) :
    sboxLaneDiff k t t' = towerZero 7 ↔ t = t' := by
  rw [sboxLaneDiff, ← tadd_shift t t' k, towerSbox7_diff_zero_iff, tadd_eq_zero_iff]

/-- Number of lane constants producing gate output difference `γ`. -/
def laneCount (keys : List Tower128) (t t' γ : Tower128) : Nat :=
  (keys.filter fun k => decide (sboxLaneDiff k t t' = γ)).length

/-- `6` for an active lane, the whole constant list for an inactive one. -/
def laneBound (N : Nat) (δ : Tower128) : Nat := if δ = towerZero 7 then N else 6

theorem laneCount_le_length (keys : List Tower128) (t t' γ : Tower128) :
    laneCount keys t t' γ ≤ keys.length := List.length_filter_le _ _

/-- The root bound applied to the lane constant: `k ↦ t' ⊕ k` is injective, so the gate
    inputs form a duplicate-free list and `towerSbox7_differential_uniformity_le_six` applies. -/
theorem laneCount_le_laneBound (keys : List Tower128) (hNd : keys.Nodup) (t t' γ : Tower128) :
    laneCount keys t t' γ ≤ laneBound keys.length (towerAdd 7 t t') := by
  unfold laneBound
  by_cases h : towerAdd 7 t t' = towerZero 7
  · rw [ite_eq_left h]; exact laneCount_le_length keys t t' γ
  · rw [ite_eq_right h]
    have hMapNd : (keys.map (towerAdd 7 t')).Nodup :=
      rcNodup_map_of_injective _ (fun a b hab => by
        have h2 := congrArg (towerAdd 7 t') hab
        simpa only [towerAdd_cancel] using h2) keys hNd
    have hU := towerSbox7_differential_uniformity_le_six 7 (towerAdd 7 t t') γ h
      (keys.map (towerAdd 7 t')) hMapNd
    rw [List.filter_map, List.length_map] at hU
    refine Nat.le_trans (Nat.le_of_eq ?_) hU
    unfold laneCount
    apply congrArg List.length
    apply List.filter_congr
    intro k _
    exact decide_eq_decide.mpr (by simp only [sboxLaneDiff, tadd_shift])

theorem laneCount_eq_zero_of_ne (keys : List Tower128) (t t' γ : Tower128)
    (h : ∀ k, sboxLaneDiff k t t' ≠ γ) : laneCount keys t t' γ = 0 := by
  exact filter_length_eq_zero _ keys fun k _ hk => h k (of_decide_eq_true hk)

/-- An inactive lane never produces a zero-to-nonzero or nonzero-to-zero transition, so a
    lane is bounded by six whenever its target or its input difference is nonzero. -/
theorem laneCount_le_six (keys : List Tower128) (hNd : keys.Nodup) (t t' γ : Tower128)
    (h : γ ≠ towerZero 7 ∨ t ≠ t') : laneCount keys t t' γ ≤ 6 := by
  by_cases hT : t = t'
  · have hγ : γ ≠ towerZero 7 := h.elim id (fun hne => absurd hT hne)
    rw [laneCount_eq_zero_of_ne keys t t' γ (fun k hk =>
      hγ (hk ▸ (sboxLaneDiff_eq_zero_iff k t t').mpr hT))]
    exact Nat.zero_le 6
  · have hB := laneCount_le_laneBound keys hNd t t' γ
    unfold laneBound at hB
    rwa [ite_eq_right (fun h0 => hT ((tadd_eq_zero_iff t t').mp h0))] at hB

theorem laneCount_zero_target (keys : List Tower128) (t t' : Tower128) (hT : t ≠ t') :
    laneCount keys t t' (towerZero 7) = 0 :=
  laneCount_eq_zero_of_ne keys t t' _ fun k hk => hT ((sboxLaneDiff_eq_zero_iff k t t').mp hk)

/-- Lanewise xor of two states. -/
def pairXor (a b : Tower128 × Tower128) : Tower128 × Tower128 :=
  (towerAdd 7 a.1 b.1, towerAdd 7 a.2 b.2)

theorem pairXor_ne_zero {s s' : Tower128 × Tower128} (h : s ≠ s') :
    pairXor s s' ≠ (towerZero 7, towerZero 7) := fun h0 =>
  h (Prod.ext ((tadd_eq_zero_iff _ _).mp (congrArg Prod.fst h0))
    ((tadd_eq_zero_iff _ _).mp (congrArg Prod.snd h0)))

/-- Difference of the two states after the constant addition and the x^7 layer. -/
def sboxPairDiff (rc s s' : Tower128 × Tower128) : Tower128 × Tower128 :=
  (sboxLaneDiff rc.1 s.1 s'.1, sboxLaneDiff rc.2 s.2 s'.2)

theorem spnLinearMix_xor (mdsA mdsB : Tower128) (a b : Tower128 × Tower128) :
    pairXor (spnLinearMix 7 mdsA mdsB a) (spnLinearMix 7 mdsA mdsB b) =
      spnLinearMix 7 mdsA mdsB (pairXor a b) := by
  unfold spnLinearMix pairXor
  apply Prod.ext <;> simp only [towerMul_add_distrib, towerAdd_assoc, towerAdd_left_comm]

/-- The state difference after one actual round is the linear layer applied to the S-box
    output difference. The round constant enters only through `sboxPairDiff`. -/
theorem spnRound128_diff (mdsA mdsB : Tower128) (rc s s' : Tower128 × Tower128) :
    pairXor (spnRound128 mdsA mdsB rc s) (spnRound128 mdsA mdsB rc s') =
      spnLinearMix 7 mdsA mdsB (sboxPairDiff rc s s') := by
  unfold spnRound128
  rw [spnLinearMix_xor]
  rfl

theorem spnLinearMix_injective (mds : ValidSpnMdsPair 7) (a b : Tower128 × Tower128)
    (h : spnLinearMix 7 mds.mdsA mds.mdsB a = spnLinearMix 7 mds.mdsA mds.mdsB b) : a = b := by
  if hab : a = b then exact hab else
    have hNe := (spnLinearMix_branch_number_three mds (pairXor a b) (pairXor_ne_zero hab)).1
    rw [← spnLinearMix_xor, h] at hNe
    exact absurd (by unfold pairXor; rw [towerAdd_self_zero, towerAdd_self_zero]) hNe

theorem spnRound128_ne (mds : ValidSpnMdsPair 7) (rc s s' : Tower128 × Tower128)
    (h : s ≠ s') : spnRound128 mds.mdsA mds.mdsB rc s ≠ spnRound128 mds.mdsA mds.mdsB rc s' := by
  intro hEq
  have hD := spnRound128_diff mds.mdsA mds.mdsB rc s s'
  rw [hEq] at hD
  have hZero : spnLinearMix 7 mds.mdsA mds.mdsB (sboxPairDiff rc s s') =
      spnLinearMix 7 mds.mdsA mds.mdsB (towerZero 7, towerZero 7) := by
    rw [← hD]; unfold pairXor spnLinearMix
    simp only [towerAdd_self_zero, towerMul_zero]
  have hS := spnLinearMix_injective mds _ _ hZero
  exact h (Prod.ext ((sboxLaneDiff_eq_zero_iff _ _ _).mp (congrArg Prod.fst hS))
    ((sboxLaneDiff_eq_zero_iff _ _ _).mp (congrArg Prod.snd hS)))

/-- One round, exact: the constants producing S-box output difference `γ` form a rectangle,
    because the two lane constants are separate coordinates of the sample. -/
theorem sboxPairDiff_count (keys : List Tower128) (s s' γ : Tower128 × Tower128) :
    ((rcPairs keys).filter fun rc => decide (sboxPairDiff rc s s' = γ)).length =
      laneCount keys s.1 s'.1 γ.1 * laneCount keys s.2 s'.2 γ.2 := by
  rcases γ with ⟨g1, g2⟩
  rw [filter_rcPairs_length]
  have hTerm : (fun a => (keys.filter fun b =>
      decide (sboxPairDiff (a, b) s s' = (g1, g2))).length) =
      fun a => if decide (sboxLaneDiff a s.1 s'.1 = g1) then laneCount keys s.2 s'.2 g2 else 0 := by
    funext a
    by_cases ha : sboxLaneDiff a s.1 s'.1 = g1
    · rw [ite_eq_left (decide_eq_true ha)]
      unfold laneCount
      apply congrArg List.length
      apply List.filter_congr
      intro b _
      simp only [sboxPairDiff, Prod.mk.injEq, ha, true_and]
    · rw [ite_eq_right (fun hd => ha (of_decide_eq_true hd))]
      exact filter_length_eq_zero _ keys fun b _ hb =>
        ha (congrArg Prod.fst (of_decide_eq_true hb))
  rw [hTerm, rcSum_ite]
  rfl

/-! ## §3. Committed trails: the product over rounds, and the adaptive control -/

/-- S-box output differences of the two trajectories, round by round, for the constant list
    `ks` (head = first round). -/
def spnSboxTrail (mdsA mdsB : Tower128) :
    List (Tower128 × Tower128) → Tower128 × Tower128 → Tower128 × Tower128 →
      List (Tower128 × Tower128)
  | [], _, _ => []
  | rc :: rest, s, s' =>
    sboxPairDiff rc s s' ::
      spnSboxTrail mdsA mdsB rest (spnRound128 mdsA mdsB rc s) (spnRound128 mdsA mdsB rc s')

/-- Number of constant lists, out of `(N·N)^trail.length`, under which the committed pair
    `s`, `s'` follows the committed trail. -/
def spnTrailCount (keys : List Tower128) (mdsA mdsB : Tower128)
    (s s' : Tower128 × Tower128) (trail : List (Tower128 × Tower128)) : Nat :=
  ((freshInputAssignments (rcPairs keys) trail.length).filter fun ks =>
    decide (spnSboxTrail mdsA mdsB ks s s' = trail)).length

/-- Product of lane bounds along a trail: the input difference of each round is the linear
    layer applied to the previous S-box output difference. -/
def spnTrailBound (N : Nat) (mdsA mdsB : Tower128) :
    Tower128 × Tower128 → List (Tower128 × Tower128) → Nat
  | _, [] => 1
  | δ, γ :: rest =>
    laneBound N δ.1 * laneBound N δ.2 * spnTrailBound N mdsA mdsB (spnLinearMix 7 mdsA mdsB γ) rest

/-- **Markov product for the actual round function.** For every committed pair and trail, the
    number of independent uniform constant lists that realize the trail is at most the product
    of the per-lane root bounds. Proof: the first round's constants are a separate coordinate
    of the sample, and the bound for the remaining rounds is uniform in the reached states. -/
theorem spnTrailCount_le (keys : List Tower128) (hNd : keys.Nodup) (mdsA mdsB : Tower128) :
    ∀ (trail : List (Tower128 × Tower128)) (s s' : Tower128 × Tower128),
      spnTrailCount keys mdsA mdsB s s' trail ≤
        spnTrailBound keys.length mdsA mdsB (pairXor s s') trail
  | [], s, s' => List.length_filter_le _ [[]]
  | γ :: rest, s, s' => by
    unfold spnTrailCount
    rw [List.length_cons, freshInputAssignments, filter_prefixAssignments_length]
    have hTerm : ∀ rc ∈ rcPairs keys,
        ((freshInputAssignments (rcPairs keys) rest.length).filter fun t =>
          decide (spnSboxTrail mdsA mdsB (rc :: t) s s' = γ :: rest)).length ≤
        if decide (sboxPairDiff rc s s' = γ) then
          spnTrailBound keys.length mdsA mdsB (spnLinearMix 7 mdsA mdsB γ) rest else 0 := by
      intro rc _
      by_cases h : sboxPairDiff rc s s' = γ
      · rw [ite_eq_left (decide_eq_true h)]
        have ih := spnTrailCount_le keys hNd mdsA mdsB rest
          (spnRound128 mdsA mdsB rc s) (spnRound128 mdsA mdsB rc s')
        rw [spnRound128_diff, h] at ih
        refine Nat.le_trans (Nat.le_of_eq ?_) ih
        unfold spnTrailCount
        apply congrArg List.length
        apply List.filter_congr
        intro t _
        simp only [spnSboxTrail, h, List.cons.injEq, true_and]
      · rw [ite_eq_right (fun hd => h (of_decide_eq_true hd))]
        exact Nat.le_of_eq (filter_length_eq_zero _ _ fun t _ ht =>
          h (List.head_eq_of_cons_eq (of_decide_eq_true ht)))
    refine Nat.le_trans (rcSum_le_of_le _ _ _ hTerm) ?_
    rw [rcSum_ite, sboxPairDiff_count]
    exact Nat.mul_le_mul
      (Nat.mul_le_mul (laneCount_le_laneBound keys hNd s.1 s'.1 γ.1)
        (laneCount_le_laneBound keys hNd s.2 s'.2 γ.2)) (Nat.le_refl _)

/-- Round-constant schedule read from a list (zero past its end). -/
def rcSchedule : List (Tower128 × Tower128) → Nat → Tower128 × Tower128
  | [], _ => (towerZero 7, towerZero 7)
  | rc :: _, 0 => rc
  | _ :: rest, i + 1 => rcSchedule rest i

theorem spnIterRounds128_succ_head (mdsA mdsB : Tower128) (rcs : Nat → Tower128 × Tower128) :
    ∀ (r : Nat) (st : Tower128 × Tower128),
      spnIterRounds128 mdsA mdsB rcs (r + 1) st =
        spnIterRounds128 mdsA mdsB (fun i => rcs (i + 1)) r (spnRound128 mdsA mdsB (rcs 0) st)
  | 0, _ => rfl
  | r + 1, st => by
    show spnRound128 mdsA mdsB (rcs (r + 1)) (spnIterRounds128 mdsA mdsB rcs (r + 1) st) =
      spnRound128 mdsA mdsB (rcs (r + 1))
        (spnIterRounds128 mdsA mdsB (fun i => rcs (i + 1)) r (spnRound128 mdsA mdsB (rcs 0) st))
    rw [spnIterRounds128_succ_head mdsA mdsB rcs r st]

/-- The permutation with the constant list applied head first. -/
def spnRunList (mdsA mdsB : Tower128) :
    List (Tower128 × Tower128) → Tower128 × Tower128 → Tower128 × Tower128
  | [], st => st
  | rc :: rest, st => spnRunList mdsA mdsB rest (spnRound128 mdsA mdsB rc st)

/-- `spnRunList` is the actual `spnIterRounds128` under the list's schedule. -/
theorem spnRunList_eq_iter (mdsA mdsB : Tower128) :
    ∀ (ks : List (Tower128 × Tower128)) (st : Tower128 × Tower128),
      spnRunList mdsA mdsB ks st = spnIterRounds128 mdsA mdsB (rcSchedule ks) ks.length st
  | [], _ => rfl
  | rc :: rest, st => by
    rw [List.length_cons, spnIterRounds128_succ_head]
    exact spnRunList_eq_iter mdsA mdsB rest (spnRound128 mdsA mdsB rc st)

theorem spnTrailActiveSboxes_succ_head (mdsA mdsB : Tower128)
    (rcs : Nat → Tower128 × Tower128) :
    ∀ (r : Nat) (s s' : Tower128 × Tower128),
      spnTrailActiveSboxes mdsA mdsB rcs (r + 1) s s' =
        laneActiveWeight 7 (pairXor s s') +
          spnTrailActiveSboxes mdsA mdsB (fun i => rcs (i + 1)) r
            (spnRound128 mdsA mdsB (rcs 0) s) (spnRound128 mdsA mdsB (rcs 0) s')
  | 0, s, s' => (Nat.zero_add _).trans (Nat.add_zero _).symm
  | r + 1, s, s' => by
    have ih := spnTrailActiveSboxes_succ_head mdsA mdsB rcs r s s'
    show spnTrailActiveSboxes mdsA mdsB rcs (r + 1) s s' +
        laneActiveWeight 7 (pairXor (spnIterRounds128 mdsA mdsB rcs (r + 1) s)
          (spnIterRounds128 mdsA mdsB rcs (r + 1) s')) =
      laneActiveWeight 7 (pairXor s s') +
        (spnTrailActiveSboxes mdsA mdsB (fun i => rcs (i + 1)) r
            (spnRound128 mdsA mdsB (rcs 0) s) (spnRound128 mdsA mdsB (rcs 0) s') +
          laneActiveWeight 7 (pairXor
            (spnIterRounds128 mdsA mdsB (fun i => rcs (i + 1)) r (spnRound128 mdsA mdsB (rcs 0) s))
            (spnIterRounds128 mdsA mdsB (fun i => rcs (i + 1)) r
              (spnRound128 mdsA mdsB (rcs 0) s'))))
    rw [ih, spnIterRounds128_succ_head, spnIterRounds128_succ_head, Nat.add_assoc]

/-- Active S-boxes of the two trajectories, counted head first. -/
def spnListActive (mdsA mdsB : Tower128) :
    List (Tower128 × Tower128) → Tower128 × Tower128 → Tower128 × Tower128 → Nat
  | [], _, _ => 0
  | rc :: rest, s, s' =>
    laneActiveWeight 7 (pairXor s s') +
      spnListActive mdsA mdsB rest (spnRound128 mdsA mdsB rc s) (spnRound128 mdsA mdsB rc s')

/-- `spnListActive` is the existing `spnTrailActiveSboxes` under the list's schedule. -/
theorem spnListActive_eq (mdsA mdsB : Tower128) :
    ∀ (ks : List (Tower128 × Tower128)) (s s' : Tower128 × Tower128),
      spnListActive mdsA mdsB ks s s' =
        spnTrailActiveSboxes mdsA mdsB (rcSchedule ks) ks.length s s'
  | [], _, _ => rfl
  | rc :: rest, s, s' => by
    rw [List.length_cons, spnTrailActiveSboxes_succ_head]
    show _ + spnListActive mdsA mdsB rest _ _ =
      _ + spnTrailActiveSboxes mdsA mdsB (rcSchedule rest) rest.length _ _
    rw [spnListActive_eq mdsA mdsB rest]
    rfl

theorem laneBound_weight (N : Nat) (δ : Tower128 × Tower128) :
    laneBound N δ.1 * laneBound N δ.2 * N ^ laneActiveWeight 7 δ =
      6 ^ laneActiveWeight 7 δ * (N * N) := by
  unfold laneBound laneActiveWeight
  by_cases h1 : δ.1 = towerZero 7 <;> by_cases h2 : δ.2 = towerZero 7
  · rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left h1, ite_eq_left h2]
    show N * N * 1 = 1 * (N * N)
    rw [Nat.mul_one, Nat.one_mul]
  · rw [ite_eq_left h1, ite_eq_right h2, ite_eq_left h1, ite_eq_right h2]
    show N * 6 * (1 * N) = 1 * 6 * (N * N)
    rw [Nat.one_mul, Nat.one_mul, Nat.mul_comm N 6, Nat.mul_assoc]
  · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_right h1, ite_eq_left h2]
    show 6 * N * (1 * N) = 1 * 6 * (N * N)
    rw [Nat.one_mul, Nat.one_mul, Nat.mul_assoc]
  · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h1, ite_eq_right h2]
    show 6 * 6 * (1 * N * N) = 1 * 6 * 6 * (N * N)
    rw [Nat.one_mul, Nat.one_mul]

theorem trailBound_step_arith (lb tb N w a n : Nat)
    (hw : lb * N ^ w = 6 ^ w * (N * N)) (ih : tb * N ^ a = 6 ^ a * (N * N) ^ n) :
    lb * tb * N ^ (w + a) = 6 ^ (w + a) * (N * N) ^ (n + 1) := by
  rw [Nat.pow_add N, Nat.pow_add 6, Nat.mul_mul_mul_comm, hw, ih, Nat.pow_succ,
    Nat.mul_mul_mul_comm, Nat.mul_comm (N * N) ((N * N) ^ n)]

/-- On a realized trail the bound is exactly `6^a · N^(2n - a)` for the existing active count. -/
theorem spnTrailBound_realized (N : Nat) (mdsA mdsB : Tower128) :
    ∀ (ks : List (Tower128 × Tower128)) (s s' : Tower128 × Tower128),
      spnTrailBound N mdsA mdsB (pairXor s s') (spnSboxTrail mdsA mdsB ks s s') *
          N ^ spnListActive mdsA mdsB ks s s' =
        6 ^ spnListActive mdsA mdsB ks s s' * (N * N) ^ ks.length
  | [], _, _ => rfl
  | rc :: rest, s, s' => by
    have ih := spnTrailBound_realized N mdsA mdsB rest
      (spnRound128 mdsA mdsB rc s) (spnRound128 mdsA mdsB rc s')
    rw [spnRound128_diff] at ih
    exact trailBound_step_arith _ _ N _ _ _ (laneBound_weight N (pairXor s s')) ih

theorem committed_trail_arith (c tb N a M : Nat) (hc : c ≤ tb)
    (hR : tb * N ^ a = 6 ^ a * M) (ha : 72 ≤ a) (h6 : 6 ≤ N) :
    c * N ^ 72 ≤ 6 ^ 72 * M := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le ha
  have hNpos : 0 < N ^ e := Nat.pow_pos (Nat.lt_of_lt_of_le (by decide) h6)
  apply Nat.le_of_mul_le_mul_right _ hNpos
  calc c * N ^ 72 * N ^ e ≤ tb * N ^ 72 * N ^ e :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc)
    _ = tb * N ^ (72 + e) := by rw [Nat.mul_assoc, ← Nat.pow_add]
    _ = 6 ^ (72 + e) * M := hR
    _ = 6 ^ 72 * M * 6 ^ e := by rw [Nat.pow_add, Nat.mul_right_comm]
    _ ≤ 6 ^ 72 * M * N ^ e := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h6 e)

/-- **48 rounds, committed trail.** With the deployed-shape mixing layer, any committed pair
    `s ≠ s'` and committed 48-round trail are realized by at most a `(6/N)^72` fraction of
    the `(N·N)^48` constant lists. This consumes `spn48_active_sboxes_ge_72`: a realized trail
    has at least 72 active lanes, and each active lane costs a factor `6/N`. -/
theorem spn48_committed_trail_count_le (mds : ValidSpnMdsPair 7) (keys : List Tower128)
    (hNd : keys.Nodup) (hSix : 6 ≤ keys.length) (s s' : Tower128 × Tower128) (hNe : s ≠ s')
    (trail : List (Tower128 × Tower128)) (hLen : trail.length = spnRounds) :
    spnTrailCount keys mds.mdsA mds.mdsB s s' trail * keys.length ^ 72 ≤
      6 ^ 72 * (keys.length * keys.length) ^ 48 := by
  cases hF : (freshInputAssignments (rcPairs keys) trail.length).filter fun ks =>
      decide (spnSboxTrail mds.mdsA mds.mdsB ks s s' = trail) with
  | nil =>
    unfold spnTrailCount
    rw [hF]
    exact (Nat.zero_mul _).symm ▸ Nat.zero_le _
  | cons ks more =>
    have hMem : ks ∈ (freshInputAssignments (rcPairs keys) trail.length).filter fun ks =>
        decide (spnSboxTrail mds.mdsA mds.mdsB ks s s' = trail) := by
      rw [hF]; exact List.mem_cons_self
    obtain ⟨hIn, hDec⟩ := List.mem_filter.mp hMem
    have hEq : spnSboxTrail mds.mdsA mds.mdsB ks s s' = trail := of_decide_eq_true hDec
    have hLenKs : ks.length = spnRounds :=
      (mem_freshInputAssignments_length _ _ _ hIn).trans hLen
    have hAct : 72 ≤ spnListActive mds.mdsA mds.mdsB ks s s' := by
      rw [spnListActive_eq, hLenKs]
      exact (spn48_active_sboxes_ge_72 mds (rcSchedule ks) s s' hNe).1
    have hR := spnTrailBound_realized keys.length mds.mdsA mds.mdsB ks s s'
    rw [hEq, hLenKs] at hR
    exact committed_trail_arith _ _ _ _ _
      (spnTrailCount_le keys hNd mds.mdsA mds.mdsB trail s s') hR hAct hSix

/-- The committed-trail probability, as a `RatBound` over the `2^128`-element lane constant
    list, is at most `sbox7MaxDiffProb128.pow 72`. This is the event that the arithmetic in
    `spn48_differential_trail_security_bounds` was missing; its third conjunct now applies. -/
theorem spn48_committed_trail_atLeast_256_bits (mds : ValidSpnMdsPair 7)
    (keys : List Tower128) (hNd : keys.Nodup) (hN : keys.length = 2 ^ 128)
    (s s' : Tower128 × Tower128) (hNe : s ≠ s')
    (trail : List (Tower128 × Tower128)) (hLen : trail.length = spnRounds) :
    let prob : RatBound := ⟨spnTrailCount keys mds.mdsA mds.mdsB s s' trail,
      (2 ^ 128 * 2 ^ 128) ^ 48, Nat.pow_pos (Nat.mul_pos (Nat.two_pow_pos 128) (Nat.two_pow_pos 128))⟩
    RatBound.le prob (sbox7MaxDiffProb128.pow 72) ∧ atLeastBits 256 prob := by
  have hLe : RatBound.le
      (⟨spnTrailCount keys mds.mdsA mds.mdsB s s' trail, (2 ^ 128 * 2 ^ 128) ^ 48,
        Nat.pow_pos (Nat.mul_pos (Nat.two_pow_pos 128) (Nat.two_pow_pos 128))⟩ : RatBound)
      (sbox7MaxDiffProb128.pow 72) := by
    have h := spn48_committed_trail_count_le mds keys hNd
      (by rw [hN]; exact Nat.le_of_lt_succ (by decide)) s s' hNe trail hLen
    rw [hN] at h
    exact h
  exact ⟨hLe, atLeastBits_of_le hLe
    (atLeastBits_of_strictlyMoreThanBits spn48_differential_trail_security_bounds.2.2)⟩

/-- **Adaptive control.** A trail selected after the constants are published (here: the trail
    the committed pair actually follows) is realized by every constant list. The committed
    bound therefore says nothing about an attacker who reads the public constants first. -/
theorem spn_adaptive_trail_always_realized (keys : List Tower128) (mdsA mdsB : Tower128)
    (s s' : Tower128 × Tower128) (n : Nat) :
    ((freshInputAssignments (rcPairs keys) n).filter fun ks =>
      decide (spnSboxTrail mdsA mdsB ks s s' =
        (fun seen => spnSboxTrail mdsA mdsB seen s s') ks)).length =
      (keys.length * keys.length) ^ n := by
  have hAll : ((freshInputAssignments (rcPairs keys) n).filter fun ks =>
      decide (spnSboxTrail mdsA mdsB ks s s' =
        (fun seen => spnSboxTrail mdsA mdsB seen s s') ks)) =
      freshInputAssignments (rcPairs keys) n :=
    List.filter_eq_self.mpr fun ks _ => decide_eq_true rfl
  rw [hAll, freshInputAssignments_length, rcPairs_length]

/-- The adaptive count violates the committed 48-round bound for every list of more than six
    lane constants. -/
theorem spn48_adaptive_trail_exceeds_committed_bound (N : Nat) (hN : 6 < N) :
    ¬ (N * N) ^ 48 * N ^ 72 ≤ 6 ^ 72 * (N * N) ^ 48 := by
  intro h
  rw [Nat.mul_comm (6 ^ 72)] at h
  have hPos : 0 < (N * N) ^ 48 :=
    Nat.pow_pos (Nat.mul_pos (Nat.lt_trans (by decide) hN) (Nat.lt_trans (by decide) hN))
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le
    (Nat.pow_lt_pow_left hN (by decide)) (Nat.le_of_mul_le_mul_left h hPos))

end Qsag
end

#verify_constructive
  Qsag.spnTrailCount_le
  Qsag.spnRunList_eq_iter
  Qsag.spnListActive_eq
  Qsag.spn48_committed_trail_count_le
  Qsag.spn48_committed_trail_atLeast_256_bits
  Qsag.spn_adaptive_trail_always_realized
  Qsag.spn48_adaptive_trail_exceeds_committed_bound
