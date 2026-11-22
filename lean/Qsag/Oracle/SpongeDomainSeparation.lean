module
/-
# Qsag.Oracle.SpongeDomainSeparation — permutation-query disjointness of the multi-block sponge
# and indistinguishability from a random function on block paths

`Qsag.Oracle.Sponge` separates ENCODINGS (padded block sequences). This module is about the
permutation queries made while absorbing and squeezing them.

**Model.** A state type `σ` with a capacity projection `capOf : σ → κ` and an absorption map
`xorBlk : σ → β → σ` that leaves the capacity alone and is injective in the block
(`SpongeCapLaws`). The zero block `z` is absorbed as the identity, so the state from which output
block `j` of a block sequence `w` is read is the state after absorbing `w ++ replicate j z`.
Instances: the product state `BitVec n × κ` with `xorBlk (r, c) b = (r ^^^ b, c)`
(`rateCapXor_laws`) and `Keccak-f[1600]` at rate 136 with the eight capacity lanes
`a17 … a24`, 512 bits (`keccakRate136_laws`).

**§1–§3, a fixed transformation `π`.**
* `spongeTrace π xorBlk s w` is the list of `π`-inputs of `spongeAbsorbBlocks π xorBlk s w`, and
  `evalSponge` depends on `π` only at the absorb trace and the iterated squeeze states
  (`evalSponge_congr_on_queries`).
* `sponge_distinct_inputs_terminal_disjoint_or_cap_collision`: two different non-empty sequences
  of valid blocks either end in different `π`-inputs, or the queries BEFORE the terminal ones
  contain a capacity event (`SpongeCapEvent`): some earlier output has the capacity of the
  initial state, or two different earlier inputs have outputs of equal capacity. The statement
  is for every function `π`, with an explicit witness in either branch.
* The same for every pair of output blocks (`sponge_output_queries_disjoint_or_cap_collision`),
  for `absorbPayload` under valid domain bytes
  (`absorbPayload_output_queries_disjoint_or_cap_collision`), for `cSHAKE256` `(N, S)` pairs
  (`cshake256_output_queries_disjoint_or_cap_collision`) and for the `QSAG.*` tags
  (`qsag_tags_output_queries_disjoint_or_cap_collision`).

**§4–§6, a lazily sampled random transformation.** The sample space is `K` independent uniform
draws from the state space (`Fin (Spec.roCoinPow cardD K)`). An adversary is an adaptive
`Spec.Code` program that asks for the rate part of the state at any block path. In the real
world a path is answered by walking it through a lazily sampled function on states
(`spongeRealWorld`); in the ideal world by a lazily sampled function on paths
(`spongeIdealWorld`), which gives every distinct path its own independent draw. Then
* on every coin on which no capacity event is recorded the two worlds return the same result
  (`spongeReal_eq_ideal_of_no_cap_bad`);
* the capacity event has probability at most `K (K + 1) · R / (2 · cardD)` when every capacity
  value has at most `R` preimages (`sponge_cap_bad_bound`);
* hence `AdvDist real ideal ≤ K (K + 1) / (2 C)` for `cardD = R * C`
  (`sponge_multi_domain_ro_indistinguishability_bound`), which is below `2^-430` for
  `C = 2^512` and `K ≤ 2^40` (`sponge_ro_bound_430_bits_at_c512_q2pow40`);
* at the Keccak state (`KState`, coded by `keccakDec`, rate-136 absorption `xorRate136`,
  read-out `rateBlockBytes`, capacity `keccakCap512`) and for adversaries that query `cSHAKE256`
  by `(customization, message, output block)`, the advantage is at most `K (K + 1) / 2^513`
  with no hypothesis left (`keccak_cshake_tags_ro_indistinguishability_bound`,
  `keccak_cshake_tags_ro_bound_430_bits_at_q2pow40`).
Distinct `(domain byte, message, output block)` triples and distinct
`(N, S, message, output block)` triples address distinct paths
(`absorbPayload_output_path_injective`, `cshake256_output_path_injective`,
`cshakeTagPath_injective_on_qsag_tags`), so in the ideal world no two domains or tags read the
same draw; `qsag_tags_sponge_ro_indistinguishability_bound` is the bound for adversaries that
query `cSHAKE256` by `(customization, message, output block)`.

**Scope.** The adversary of §4–§6 has no direct access to `π`: this is indistinguishability of
the keyless sponge over a hidden random transformation from a random function on paths, not
indifferentiability, and no simulator is constructed. The transformation is sampled as a
function, not as a permutation, and there is no inverse oracle; the two-way lazy permutation
game of `Qsag.Oracle.TwoWayQipmCompression` is not connected to this module. The ideal world
keeps the coin positions of the real one (it also draws at the proper prefixes of a queried
path); its equality in distribution with a random function sampled only at the queried paths
is not proved. `K` bounds the number of permutation calls, not of sponge queries: a program
that needs more calls is stopped and loses in both worlds. `keccakDec` reads a draw as
base-`2^64` digits; that it is a bijection onto `KState` is not proved (the bounds use only the
capacity fibre count `keccak_capacity_fiber_count`).

**Teeth.** `tooth_zero_capacity_state_collision`: with no capacity, for every `π` and every
target block sequence there is a different sequence with the same terminal query.
`tooth_unpadded_length_extension_shares_output_query`: without the padding property
(last block non-zero), two different `(blocks, output index)` pairs make the same terminal
query in a model with no capacity event. `tooth_zero_capacity_bad_event_certain`: at one
capacity value the bad event is recorded on every coin.
`tooth_zero_capacity_distinguisher_advantage_half`: at one capacity value an explicit adaptive
adversary has advantage `1/2`, so the real and ideal games are not the same game.
-/

public import Qsag.Oracle.Sponge
public import Qsag.Spec.GameBound
public import Qsag.Spec.Assumptions
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

/-! ## §1. Capacity-split sponge model and the query trace -/

/-- Absorption acts on the rate only: it preserves the capacity and is injective in the block. -/
structure SpongeCapLaws {σ κ β : Type} (capOf : σ → κ) (xorBlk : σ → β → σ)
    (valid : β → Prop) : Prop where
  cap_xor : ∀ (s : σ) (b : β), valid b → capOf (xorBlk s b) = capOf s
  xor_inj : ∀ (s : σ) (b₁ b₂ : β), valid b₁ → valid b₂ → xorBlk s b₁ = xorBlk s b₂ → b₁ = b₂

/-- Multi-block absorption over an arbitrary block type (`spongeAbsorbBlocks` at `List UInt8`). -/
@[expose] def spongeFold {σ β : Type} (π : σ → σ) (xorBlk : σ → β → σ) : σ → List β → σ
  | s, [] => s
  | s, b :: rest => spongeFold π xorBlk (π (xorBlk s b)) rest

/-- The `π`-inputs of `spongeFold π xorBlk s w`, in order. -/
@[expose] def spongeTrace {σ β : Type} (π : σ → σ) (xorBlk : σ → β → σ) : σ → List β → List σ
  | _, [] => []
  | s, b :: rest => xorBlk s b :: spongeTrace π xorBlk (π (xorBlk s b)) rest

/-- `j`-fold iteration of `π` (the squeeze states). -/
@[expose] def spongeIter {σ : Type} (π : σ → σ) : Nat → σ → σ
  | 0, s => s
  | j + 1, s => spongeIter π j (π s)

/-- State at the node addressed by a reversed block path (last block first). -/
@[expose] def spongeNodeState {σ β : Type} (π : σ → σ) (xorBlk : σ → β → σ) (s0 : σ) :
    List β → σ
  | [] => s0
  | b :: r => π (xorBlk (spongeNodeState π xorBlk s0 r) b)

/-- `π`-inputs along a reversed block path, newest first. -/
@[expose] def spongeNodeQueries {σ β : Type} (π : σ → σ) (xorBlk : σ → β → σ) (s0 : σ) :
    List β → List σ
  | [] => []
  | b :: r => xorBlk (spongeNodeState π xorBlk s0 r) b :: spongeNodeQueries π xorBlk s0 r

/-- The last `π`-input made while absorbing `w` (`s0` when `w` is empty and nothing is asked). -/
@[expose] def spongeTerminalQuery {σ β : Type} (π : σ → σ) (xorBlk : σ → β → σ) (s0 : σ)
    (w : List β) : σ :=
  match w.reverse with
  | [] => s0
  | b :: r => xorBlk (spongeNodeState π xorBlk s0 r) b

/-- Capacity event on a list of queries: an output with the initial capacity, or two different
    queries with outputs of equal capacity. -/
@[expose] def SpongeCapEvent {σ κ : Type} (π : σ → σ) (capOf : σ → κ) (s0 : σ)
    (queries : List σ) : Prop :=
  (∃ x, x ∈ queries ∧ capOf (π x) = capOf s0) ∨
  (∃ x y, x ∈ queries ∧ y ∈ queries ∧ x ≠ y ∧ capOf (π x) = capOf (π y))

theorem SpongeCapEvent.mono {σ κ : Type} {π : σ → σ} {capOf : σ → κ} {s0 : σ}
    {q₁ q₂ : List σ} (hSub : ∀ x, x ∈ q₁ → x ∈ q₂) (h : SpongeCapEvent π capOf s0 q₁) :
    SpongeCapEvent π capOf s0 q₂ := by
  rcases h with ⟨x, hx, hc⟩ | ⟨x, y, hx, hy, hne, hc⟩
  · exact .inl ⟨x, hSub x hx, hc⟩
  · exact .inr ⟨x, y, hSub x hx, hSub y hy, hne, hc⟩

theorem spongeAbsorbBlocks_eq_spongeFold {σ : Type} (π : σ → σ)
    (xorBlk : σ → List UInt8 → σ) (s : σ) (w : List (List UInt8)) :
    spongeAbsorbBlocks π xorBlk s w = spongeFold π xorBlk s w := by
  induction w generalizing s with
  | nil => rfl
  | cons b rest ih => exact ih (π (xorBlk s b))

theorem spongeFold_append {σ β : Type} (π : σ → σ) (xorBlk : σ → β → σ) (s : σ)
    (xs ys : List β) :
    spongeFold π xorBlk s (xs ++ ys) = spongeFold π xorBlk (spongeFold π xorBlk s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons b rest ih => exact ih (π (xorBlk s b))

theorem spongeTrace_append {σ β : Type} (π : σ → σ) (xorBlk : σ → β → σ) (s : σ)
    (xs ys : List β) :
    spongeTrace π xorBlk s (xs ++ ys) =
      spongeTrace π xorBlk s xs ++ spongeTrace π xorBlk (spongeFold π xorBlk s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons b rest ih =>
    show xorBlk s b :: spongeTrace π xorBlk (π (xorBlk s b)) (rest ++ ys) = _
    rw [ih (π (xorBlk s b))]
    rfl

private theorem spongeFold_nodeState {σ β : Type} (π : σ → σ) (xorBlk : σ → β → σ) (s0 : σ) :
    ∀ (w p : List β),
      spongeFold π xorBlk (spongeNodeState π xorBlk s0 p) w =
        spongeNodeState π xorBlk s0 (w.reverse ++ p)
  | [], _ => rfl
  | b :: rest, p => by
    have h := spongeFold_nodeState π xorBlk s0 rest (b :: p)
    rw [List.reverse_cons, List.append_assoc]
    exact h

private theorem spongeTrace_nodeQueries {σ β : Type} (π : σ → σ) (xorBlk : σ → β → σ) (s0 : σ) :
    ∀ (w p : List β),
      (spongeTrace π xorBlk (spongeNodeState π xorBlk s0 p) w).reverse ++
          spongeNodeQueries π xorBlk s0 p =
        spongeNodeQueries π xorBlk s0 (w.reverse ++ p)
  | [], _ => rfl
  | b :: rest, p => by
    have h := spongeTrace_nodeQueries π xorBlk s0 rest (b :: p)
    rw [List.reverse_cons, List.append_assoc, List.singleton_append, ← h]
    show (xorBlk (spongeNodeState π xorBlk s0 p) b ::
        spongeTrace π xorBlk (π (xorBlk (spongeNodeState π xorBlk s0 p) b)) rest).reverse ++ _ = _
    rw [List.reverse_cons, List.append_assoc]
    rfl

/-- The state after absorbing `w` is the node state of the reversed path. -/
theorem spongeNodeState_reverse {σ β : Type} (π : σ → σ) (xorBlk : σ → β → σ) (s0 : σ)
    (w : List β) :
    spongeNodeState π xorBlk s0 w.reverse = spongeFold π xorBlk s0 w := by
  have h := spongeFold_nodeState π xorBlk s0 w []
  rw [List.append_nil] at h
  exact h.symm

/-- The node queries of the reversed path are the absorb trace, reversed. -/
theorem spongeNodeQueries_reverse {σ β : Type} (π : σ → σ) (xorBlk : σ → β → σ) (s0 : σ)
    (w : List β) :
    spongeNodeQueries π xorBlk s0 w.reverse = (spongeTrace π xorBlk s0 w).reverse := by
  have h : (spongeTrace π xorBlk s0 w).reverse ++ [] =
      spongeNodeQueries π xorBlk s0 (w.reverse ++ []) := spongeTrace_nodeQueries π xorBlk s0 w []
  rw [List.append_nil, List.append_nil] at h
  exact h.symm

/-- The terminal query of `init ++ [b]` absorbs `b` into the state after `init`. -/
theorem spongeTerminalQuery_snoc {σ β : Type} (π : σ → σ) (xorBlk : σ → β → σ) (s0 : σ)
    (init : List β) (b : β) :
    spongeTerminalQuery π xorBlk s0 (init ++ [b]) = xorBlk (spongeFold π xorBlk s0 init) b := by
  unfold spongeTerminalQuery
  rw [List.reverse_append, List.reverse_singleton, List.singleton_append]
  show xorBlk (spongeNodeState π xorBlk s0 init.reverse) b = _
  rw [spongeNodeState_reverse]

/-- The terminal query is the last element of the trace. -/
theorem spongeTrace_snoc {σ β : Type} (π : σ → σ) (xorBlk : σ → β → σ) (s0 : σ)
    (init : List β) (b : β) :
    spongeTrace π xorBlk s0 (init ++ [b]) =
      spongeTrace π xorBlk s0 init ++ [spongeTerminalQuery π xorBlk s0 (init ++ [b])] := by
  rw [spongeTrace_append, spongeTerminalQuery_snoc]
  rfl

/-! ## §2. Distinct block sequences end in distinct queries, or a capacity event occurred -/

/-- Path form of the main theorem: reversed paths `b₁ :: r₁ ≠ b₂ :: r₂` of valid blocks have
    different node queries, or the queries of the two parents contain a capacity event. -/
theorem sponge_node_query_injective_or_cap_event {σ κ β : Type} [DecidableEq σ]
    {capOf : σ → κ} {xorBlk : σ → β → σ} {valid : β → Prop}
    (hL : SpongeCapLaws capOf xorBlk valid) (π : σ → σ) (s0 : σ) :
    ∀ (r₁ r₂ : List β) (b₁ b₂ : β),
      (∀ b, b ∈ b₁ :: r₁ → valid b) → (∀ b, b ∈ b₂ :: r₂ → valid b) →
      b₁ :: r₁ ≠ b₂ :: r₂ →
      xorBlk (spongeNodeState π xorBlk s0 r₁) b₁ ≠ xorBlk (spongeNodeState π xorBlk s0 r₂) b₂ ∨
      SpongeCapEvent π capOf s0
        (spongeNodeQueries π xorBlk s0 r₁ ++ spongeNodeQueries π xorBlk s0 r₂) := by
  intro r₁
  induction r₁ with
  | nil =>
    intro r₂ b₁ b₂ hV₁ hV₂ hNe
    by_cases hq : xorBlk (spongeNodeState π xorBlk s0 []) b₁ =
        xorBlk (spongeNodeState π xorBlk s0 r₂) b₂
    · have hCap : capOf (spongeNodeState π xorBlk s0 []) =
          capOf (spongeNodeState π xorBlk s0 r₂) := by
        rw [← hL.cap_xor _ b₁ (hV₁ b₁ List.mem_cons_self),
          ← hL.cap_xor (spongeNodeState π xorBlk s0 r₂) b₂ (hV₂ b₂ List.mem_cons_self), hq]
      cases r₂ with
      | nil =>
        exact absurd (congrArg (· :: ([] : List β))
          (hL.xor_inj s0 b₁ b₂ (hV₁ b₁ List.mem_cons_self) (hV₂ b₂ List.mem_cons_self) hq)) hNe
      | cons c t =>
        exact .inr (.inl ⟨xorBlk (spongeNodeState π xorBlk s0 t) c,
          List.mem_append_right _ List.mem_cons_self, hCap.symm⟩)
    · exact .inl hq
  | cons c₁ t₁ ih =>
    intro r₂ b₁ b₂ hV₁ hV₂ hNe
    by_cases hq : xorBlk (spongeNodeState π xorBlk s0 (c₁ :: t₁)) b₁ =
        xorBlk (spongeNodeState π xorBlk s0 r₂) b₂
    · have hCap : capOf (spongeNodeState π xorBlk s0 (c₁ :: t₁)) =
          capOf (spongeNodeState π xorBlk s0 r₂) := by
        rw [← hL.cap_xor _ b₁ (hV₁ b₁ List.mem_cons_self),
          ← hL.cap_xor (spongeNodeState π xorBlk s0 r₂) b₂ (hV₂ b₂ List.mem_cons_self), hq]
      cases r₂ with
      | nil =>
        exact .inr (.inl ⟨xorBlk (spongeNodeState π xorBlk s0 t₁) c₁,
          List.mem_append_left _ List.mem_cons_self, hCap⟩)
      | cons c₂ t₂ =>
        by_cases hp : xorBlk (spongeNodeState π xorBlk s0 t₁) c₁ =
            xorBlk (spongeNodeState π xorBlk s0 t₂) c₂
        · have hState : spongeNodeState π xorBlk s0 (c₁ :: t₁) =
              spongeNodeState π xorBlk s0 (c₂ :: t₂) := congrArg π hp
          rw [hState] at hq
          have hb : b₁ = b₂ := hL.xor_inj _ b₁ b₂ (hV₁ b₁ List.mem_cons_self)
            (hV₂ b₂ List.mem_cons_self) hq
          have hNe' : c₁ :: t₁ ≠ c₂ :: t₂ := fun hEq => hNe (by rw [hb, hEq])
          rcases ih t₂ c₁ c₂
              (fun b hb' => hV₁ b (List.mem_cons_of_mem _ hb'))
              (fun b hb' => hV₂ b (List.mem_cons_of_mem _ hb')) hNe' with hDiff | hEv
          · exact absurd hp hDiff
          · exact .inr (SpongeCapEvent.mono (fun x hx => by
              rcases List.mem_append.mp hx with h | h
              · exact List.mem_append_left _ (List.mem_cons_of_mem _ h)
              · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)) hEv)
        · exact .inr (.inr ⟨xorBlk (spongeNodeState π xorBlk s0 t₁) c₁,
            xorBlk (spongeNodeState π xorBlk s0 t₂) c₂,
            List.mem_append_left _ List.mem_cons_self,
            List.mem_append_right _ List.mem_cons_self, hp, hCap⟩)
    · exact .inl hq

/-- **Terminal-query disjointness up to capacity events.** For every transformation `π`, two
    different sequences `init₁ ++ [b₁] ≠ init₂ ++ [b₂]` of valid blocks either end in different
    `π`-inputs, or the queries made BEFORE the terminal ones (the traces of `init₁` and `init₂`)
    contain a capacity event. -/
theorem sponge_distinct_inputs_terminal_disjoint_or_cap_collision {σ κ β : Type} [DecidableEq σ]
    {capOf : σ → κ} {xorBlk : σ → β → σ} {valid : β → Prop}
    (hL : SpongeCapLaws capOf xorBlk valid) (π : σ → σ) (s0 : σ)
    (init₁ init₂ : List β) (b₁ b₂ : β)
    (hV₁ : ∀ b, b ∈ init₁ ++ [b₁] → valid b) (hV₂ : ∀ b, b ∈ init₂ ++ [b₂] → valid b)
    (hNe : init₁ ++ [b₁] ≠ init₂ ++ [b₂]) :
    xorBlk (spongeFold π xorBlk s0 init₁) b₁ ≠ xorBlk (spongeFold π xorBlk s0 init₂) b₂ ∨
    SpongeCapEvent π capOf s0
      (spongeTrace π xorBlk s0 init₁ ++ spongeTrace π xorBlk s0 init₂) := by
  have hMem : ∀ (init : List β) (b c : β), c ∈ b :: init.reverse → c ∈ init ++ [b] := by
    intro init b c hc
    rcases List.mem_cons.mp hc with rfl | h
    · exact List.mem_append_right _ List.mem_cons_self
    · exact List.mem_append_left _ (List.mem_reverse.mp h)
  have hNeRev : b₁ :: init₁.reverse ≠ b₂ :: init₂.reverse := by
    intro hEq
    apply hNe
    have h := congrArg List.reverse hEq
    rw [List.reverse_cons, List.reverse_cons, List.reverse_reverse, List.reverse_reverse] at h
    exact h
  rcases sponge_node_query_injective_or_cap_event hL π s0 init₁.reverse init₂.reverse b₁ b₂
      (fun c hc => hV₁ c (hMem init₁ b₁ c hc)) (fun c hc => hV₂ c (hMem init₂ b₂ c hc))
      hNeRev with hDiff | hEv
  · rw [spongeNodeState_reverse, spongeNodeState_reverse] at hDiff
    exact .inl hDiff
  · rw [spongeNodeQueries_reverse, spongeNodeQueries_reverse] at hEv
    exact .inr (SpongeCapEvent.mono (fun x hx => by
      rcases List.mem_append.mp hx with h | h
      · exact List.mem_append_left _ (List.mem_reverse.mp h)
      · exact List.mem_append_right _ (List.mem_reverse.mp h)) hEv)

/-- The `π`-inputs made while absorbing `w`, except the terminal one (newest first). -/
@[expose] def spongeInnerQueries {σ β : Type} (π : σ → σ) (xorBlk : σ → β → σ) (s0 : σ)
    (w : List β) : List σ :=
  (spongeNodeQueries π xorBlk s0 w.reverse).tail

theorem mem_spongeInnerQueries_snoc {σ β : Type} (π : σ → σ) (xorBlk : σ → β → σ) (s0 : σ)
    (init : List β) (b : β) (x : σ) :
    x ∈ spongeInnerQueries π xorBlk s0 (init ++ [b]) ↔ x ∈ spongeTrace π xorBlk s0 init := by
  unfold spongeInnerQueries
  rw [List.reverse_append, List.reverse_singleton, List.singleton_append]
  show x ∈ spongeNodeQueries π xorBlk s0 init.reverse ↔ _
  rw [spongeNodeQueries_reverse]
  exact List.mem_reverse

/-- Total-function form of `sponge_distinct_inputs_terminal_disjoint_or_cap_collision`. -/
theorem sponge_terminal_query_ne_or_cap_event {σ κ β : Type} [DecidableEq σ]
    {capOf : σ → κ} {xorBlk : σ → β → σ} {valid : β → Prop}
    (hL : SpongeCapLaws capOf xorBlk valid) (π : σ → σ) (s0 : σ) (w₁ w₂ : List β)
    (hV₁ : ∀ b, b ∈ w₁ → valid b) (hV₂ : ∀ b, b ∈ w₂ → valid b)
    (hne₁ : w₁ ≠ []) (hne₂ : w₂ ≠ []) (hNe : w₁ ≠ w₂) :
    spongeTerminalQuery π xorBlk s0 w₁ ≠ spongeTerminalQuery π xorBlk s0 w₂ ∨
    SpongeCapEvent π capOf s0
      (spongeInnerQueries π xorBlk s0 w₁ ++ spongeInnerQueries π xorBlk s0 w₂) := by
  cases h₁ : w₁.reverse with
  | nil => exact absurd (List.reverse_eq_nil_iff.mp h₁) hne₁
  | cons b₁ r₁ =>
    cases h₂ : w₂.reverse with
    | nil => exact absurd (List.reverse_eq_nil_iff.mp h₂) hne₂
    | cons b₂ r₂ =>
      unfold spongeTerminalQuery spongeInnerQueries
      rw [h₁, h₂]
      refine sponge_node_query_injective_or_cap_event hL π s0 r₁ r₂ b₁ b₂
        (fun b hb => hV₁ b (List.mem_reverse.mp (h₁ ▸ hb)))
        (fun b hb => hV₂ b (List.mem_reverse.mp (h₂ ▸ hb))) ?_
      intro hEq
      apply hNe
      have h := h₁.trans (hEq.trans h₂.symm)
      exact List.reverse_inj.mp h

/-- Padded block sequences followed by zero blocks address distinct paths: if neither sequence
    ends in the zero block `z`, then `w ++ replicate j z` determines `w` and `j`. -/
theorem sponge_output_path_injective {β : Type} (z : β) :
    ∀ (j₁ j₂ : Nat) (w₁ w₂ : List β),
      (∀ init, w₁ ≠ init ++ [z]) → (∀ init, w₂ ≠ init ++ [z]) →
      w₁ ++ List.replicate j₁ z = w₂ ++ List.replicate j₂ z → w₁ = w₂ ∧ j₁ = j₂
  | 0, 0, w₁, w₂, _, _, h => by
    rw [List.replicate_zero, List.append_nil, List.append_nil] at h
    exact ⟨h, rfl⟩
  | 0, j₂ + 1, w₁, w₂, hL₁, _, h => by
    rw [List.replicate_zero, List.append_nil, List.replicate_succ', ← List.append_assoc] at h
    exact absurd h (hL₁ _)
  | j₁ + 1, 0, w₁, w₂, _, hL₂, h => by
    rw [List.replicate_zero, List.append_nil, List.replicate_succ', ← List.append_assoc] at h
    exact absurd h.symm (hL₂ _)
  | j₁ + 1, j₂ + 1, w₁, w₂, hL₁, hL₂, h => by
    rw [List.replicate_succ', List.replicate_succ', ← List.append_assoc, ← List.append_assoc] at h
    obtain ⟨hw, hj⟩ := sponge_output_path_injective z j₁ j₂ w₁ w₂ hL₁ hL₂
      (List.append_cancel_right h)
    exact ⟨hw, congrArg (· + 1) hj⟩

/-- **Output-block query disjointness.** Block sequences `w₁, w₂` that do not end in the zero
    block `z`, read at output blocks `j₁, j₂` with `(w₁, j₁) ≠ (w₂, j₂)`: the two terminal
    queries differ, or the earlier queries of the two runs contain a capacity event. -/
theorem sponge_output_queries_disjoint_or_cap_collision {σ κ β : Type} [DecidableEq σ]
    {capOf : σ → κ} {xorBlk : σ → β → σ} {valid : β → Prop}
    (hL : SpongeCapLaws capOf xorBlk valid) (π : σ → σ) (s0 : σ) (z : β) (hz : valid z)
    (w₁ w₂ : List β) (j₁ j₂ : Nat)
    (hV₁ : ∀ b, b ∈ w₁ → valid b) (hV₂ : ∀ b, b ∈ w₂ → valid b)
    (hne₁ : w₁ ≠ []) (hne₂ : w₂ ≠ [])
    (hLast₁ : ∀ init, w₁ ≠ init ++ [z]) (hLast₂ : ∀ init, w₂ ≠ init ++ [z])
    (hNe : (w₁, j₁) ≠ (w₂, j₂)) :
    spongeTerminalQuery π xorBlk s0 (w₁ ++ List.replicate j₁ z) ≠
      spongeTerminalQuery π xorBlk s0 (w₂ ++ List.replicate j₂ z) ∨
    SpongeCapEvent π capOf s0
      (spongeInnerQueries π xorBlk s0 (w₁ ++ List.replicate j₁ z) ++
        spongeInnerQueries π xorBlk s0 (w₂ ++ List.replicate j₂ z)) := by
  have hVal : ∀ (w : List β) (j : Nat), (∀ b, b ∈ w → valid b) →
      ∀ b, b ∈ w ++ List.replicate j z → valid b := by
    intro w j hV b hb
    rcases List.mem_append.mp hb with h | h
    · exact hV b h
    · rw [List.eq_of_mem_replicate h]; exact hz
  refine sponge_terminal_query_ne_or_cap_event hL π s0 _ _ (hVal w₁ j₁ hV₁) (hVal w₂ j₂ hV₂)
    (fun h => hne₁ (List.append_eq_nil_iff.mp h).1)
    (fun h => hne₂ (List.append_eq_nil_iff.mp h).1) ?_
  intro hEq
  obtain ⟨hw, hj⟩ := sponge_output_path_injective z j₁ j₂ w₁ w₂ hLast₁ hLast₂ hEq
  exact hNe (by rw [hw, hj])

/-! ### Squeeze states are terminal queries of zero-extended paths -/

theorem spongeFold_replicate_zero {σ β : Type} (π : σ → σ) (xorBlk : σ → β → σ) (z : β)
    (hzId : ∀ s, xorBlk s z = s) :
    ∀ (j : Nat) (s : σ), spongeFold π xorBlk s (List.replicate j z) = spongeIter π j s
  | 0, _ => rfl
  | j + 1, s => by
    show spongeFold π xorBlk (π (xorBlk s z)) (List.replicate j z) = spongeIter π j (π s)
    rw [hzId]
    exact spongeFold_replicate_zero π xorBlk z hzId j (π s)

/-- The `π`-input that produces output block `j + 1` of `w` is the `j`-th iterate of the
    absorbed state, and it is the terminal query of `w ++ replicate (j + 1) z`. -/
theorem spongeTerminalQuery_squeeze {σ β : Type} (π : σ → σ) (xorBlk : σ → β → σ) (s0 : σ)
    (z : β) (hzId : ∀ s, xorBlk s z = s) (w : List β) (j : Nat) :
    spongeTerminalQuery π xorBlk s0 (w ++ List.replicate (j + 1) z) =
      spongeIter π j (spongeFold π xorBlk s0 w) := by
  rw [List.replicate_succ', ← List.append_assoc, spongeTerminalQuery_snoc, hzId,
    spongeFold_append, spongeFold_replicate_zero π xorBlk z hzId]

/-! ## §3. `evalSponge` reads `π` only at the absorb trace and the squeeze iterates -/

theorem spongeFold_congr {σ β : Type} {π π' : σ → σ} (xorBlk : σ → β → σ) :
    ∀ (w : List β) (s : σ), (∀ x, x ∈ spongeTrace π xorBlk s w → π x = π' x) →
      spongeFold π xorBlk s w = spongeFold π' xorBlk s w
  | [], _, _ => rfl
  | b :: rest, s, h => by
    have h0 : π (xorBlk s b) = π' (xorBlk s b) := h _ List.mem_cons_self
    show spongeFold π xorBlk (π (xorBlk s b)) rest = spongeFold π' xorBlk (π' (xorBlk s b)) rest
    rw [← h0]
    exact spongeFold_congr xorBlk rest _ (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem spongeSqueezeFuel_congr {σ : Type} {π π' : σ → σ} (r : Nat)
    (extractRate : σ → List UInt8) :
    ∀ (fuel outLen : Nat) (s : σ),
      (∀ j, j < fuel → π (spongeIter π j s) = π' (spongeIter π j s)) →
      spongeSqueezeFuel r π extractRate fuel outLen s =
        spongeSqueezeFuel r π' extractRate fuel outLen s
  | 0, _, _, _ => rfl
  | _ + 1, 0, _, _ => rfl
  | fuel + 1, outLen + 1, s, h => by
    have h0 : π s = π' s := h 0 (Nat.zero_lt_succ fuel)
    simp only [spongeSqueezeFuel]
    split
    · rfl
    · rw [← h0]
      exact congrArg (extractRate s ++ ·)
        (spongeSqueezeFuel_congr r extractRate fuel _ (π s)
          (fun j hj => h (j + 1) (Nat.succ_lt_succ hj)))

/-- **The query set of `evalSponge`.** Two transformations that agree on the absorb trace of the
    padded message and on the first `outLen` squeeze iterates give the same sponge output. -/
theorem evalSponge_congr_on_queries {σ : Type} (r : Nat) (domByte : UInt8) (π π' : σ → σ)
    (s0 : σ) (xorBlk : σ → List UInt8 → σ) (extractRate : σ → List UInt8)
    (msg : List UInt8) (outLen : Nat)
    (hAbs : ∀ x, x ∈ spongeTrace π xorBlk s0 (absorbPayload r domByte msg) → π x = π' x)
    (hSq : ∀ j, j < outLen →
      π (spongeIter π j (spongeFold π xorBlk s0 (absorbPayload r domByte msg))) =
        π' (spongeIter π j (spongeFold π xorBlk s0 (absorbPayload r domByte msg)))) :
    evalSponge r domByte π s0 xorBlk extractRate msg outLen =
      evalSponge r domByte π' s0 xorBlk extractRate msg outLen := by
  unfold evalSponge spongeSqueeze
  dsimp only
  rw [spongeAbsorbBlocks_eq_spongeFold, spongeAbsorbBlocks_eq_spongeFold,
    ← spongeFold_congr xorBlk _ s0 hAbs]
  exact spongeSqueezeFuel_congr r extractRate outLen outLen _ hSq

/-! ### `absorbPayload`, `cSHAKE256` and the `QSAG.*` tags -/

private theorem u8_xor_80_ne_zero {d : UInt8} (hd : d.toNat < 128) :
    d ^^^ (0x80 : UInt8) ≠ 0 := by
  intro h
  have h2 : d = (0x80 : UInt8) := by
    have h3 := u8_xor_cancel_right d 0x80
    rw [h, u8_zero_xor] at h3
    exact h3.symm
  rw [h2] at hd
  exact absurd hd (by decide)

private theorem pad10star1_ends_nonzero {r : Nat} (hr : 0 < r) {d : UInt8}
    (hd : ValidDomByte d) (m : List UInt8) :
    ∃ (q : List UInt8) (x : UInt8), pad10star1 r d m = q ++ [x] ∧ x ≠ 0 := by
  have hrNe : r ≠ 0 := by omega
  unfold pad10star1
  simp only [hrNe, ↓reduceIte]
  split
  · exact ⟨m, d ^^^ 0x80, rfl, u8_xor_80_ne_zero hd.2⟩
  · exact ⟨m ++ [d] ++ List.replicate (r - m.length % r - 2) 0, 0x80, rfl, by decide⟩

theorem absorbPayload_ne_nil {r : Nat} (hr : 0 < r) (d : UInt8) (m : List UInt8) :
    absorbPayload r d m ≠ [] := by
  intro h
  have hFlat := (absorbPayload_flatten hr d m).1
  have hLen := (pad10star1_length hr d m).2.2
  rw [← hFlat, h] at hLen
  simp only [List.flatten_nil, List.length_nil] at hLen
  omega

/-- The last padded block is never the zero block: it carries the `0x80` padding bit. -/
theorem absorbPayload_last_block_ne_zero {r : Nat} (hr : 0 < r) {d : UInt8}
    (hd : ValidDomByte d) (m : List UInt8) (init : List (List UInt8)) :
    absorbPayload r d m ≠ init ++ [List.replicate r 0] := by
  intro h
  obtain ⟨q, x, hq, hx⟩ := pad10star1_ends_nonzero hr hd m
  have hFlat := (absorbPayload_flatten hr d m).1
  obtain ⟨k, hk⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  rw [h, hq, hk] at hFlat
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.replicate_succ'] at hFlat
  have hRev := congrArg List.reverse hFlat
  simp only [List.reverse_append, List.reverse_singleton, List.cons_append,
    List.nil_append] at hRev
  exact hx (List.cons.inj hRev).1.symm

private theorem absorbPayload_extended_valid {r : Nat} (hr : 0 < r) (d : UInt8)
    (m : List UInt8) (j : Nat) :
    ∀ b, b ∈ absorbPayload r d m ++ List.replicate j (List.replicate r (0 : UInt8)) →
      b.length = r := by
  intro b hb
  rcases List.mem_append.mp hb with h | h
  · exact (absorbPayload_flatten hr d m).2 b h
  · rw [List.eq_of_mem_replicate h, List.length_replicate]

/-- Distinct `(domain byte, message, output block)` triples address distinct block paths. -/
theorem absorbPayload_output_path_injective {r : Nat} (hr : 0 < r) {d₁ d₂ : UInt8}
    (hd₁ : ValidDomByte d₁) (hd₂ : ValidDomByte d₂) {m₁ m₂ : List UInt8} {j₁ j₂ : Nat}
    (h : absorbPayload r d₁ m₁ ++ List.replicate j₁ (List.replicate r 0) =
      absorbPayload r d₂ m₂ ++ List.replicate j₂ (List.replicate r 0)) :
    d₁ = d₂ ∧ m₁ = m₂ ∧ j₁ = j₂ := by
  obtain ⟨hw, hj⟩ := sponge_output_path_injective (List.replicate r (0 : UInt8)) j₁ j₂ _ _
    (absorbPayload_last_block_ne_zero hr hd₁ m₁) (absorbPayload_last_block_ne_zero hr hd₂ m₂) h
  have hFlat : pad10star1 r d₁ m₁ = pad10star1 r d₂ m₂ := by
    rw [← (absorbPayload_flatten hr d₁ m₁).1, ← (absorbPayload_flatten hr d₂ m₂).1, hw]
  obtain ⟨hd, hm⟩ := pad10star1_joint_injective hr hd₁ hd₂ hFlat
  exact ⟨hd, hm, hj⟩

/-- **Permutation-query disjointness across domain bytes and messages.** For valid domain bytes
    and `(d₁, m₁, j₁) ≠ (d₂, m₂, j₂)`, the `π`-input that produces output block `j₁` of
    `(d₁, m₁)` differs from the one that produces output block `j₂` of `(d₂, m₂)`, or the
    earlier queries of the two runs contain a capacity event. -/
theorem absorbPayload_output_queries_disjoint_or_cap_collision {σ κ : Type} [DecidableEq σ]
    {capOf : σ → κ} {xorBlk : σ → List UInt8 → σ} {r : Nat} (hr : 0 < r)
    (hL : SpongeCapLaws capOf xorBlk (fun b => b.length = r)) (π : σ → σ) (s0 : σ)
    {d₁ d₂ : UInt8} (hd₁ : ValidDomByte d₁) (hd₂ : ValidDomByte d₂)
    (m₁ m₂ : List UInt8) (j₁ j₂ : Nat) (hNe : (d₁, m₁, j₁) ≠ (d₂, m₂, j₂)) :
    spongeTerminalQuery π xorBlk s0
        (absorbPayload r d₁ m₁ ++ List.replicate j₁ (List.replicate r 0)) ≠
      spongeTerminalQuery π xorBlk s0
        (absorbPayload r d₂ m₂ ++ List.replicate j₂ (List.replicate r 0)) ∨
    SpongeCapEvent π capOf s0
      (spongeInnerQueries π xorBlk s0
          (absorbPayload r d₁ m₁ ++ List.replicate j₁ (List.replicate r 0)) ++
        spongeInnerQueries π xorBlk s0
          (absorbPayload r d₂ m₂ ++ List.replicate j₂ (List.replicate r 0))) := by
  refine sponge_terminal_query_ne_or_cap_event hL π s0 _ _
    (absorbPayload_extended_valid hr d₁ m₁ j₁) (absorbPayload_extended_valid hr d₂ m₂ j₂)
    (fun h => absorbPayload_ne_nil hr d₁ m₁ (List.append_eq_nil_iff.mp h).1)
    (fun h => absorbPayload_ne_nil hr d₂ m₂ (List.append_eq_nil_iff.mp h).1) ?_
  intro hEq
  obtain ⟨hd, hm, hj⟩ := absorbPayload_output_path_injective hr hd₁ hd₂ hEq
  exact hNe (by rw [hd, hm, hj])

/-- The padded 136-byte block sequence absorbed by `evalCshake256Sponge` for `(N, S, m)`. -/
@[expose] def cshake256PaddedBlocks (N S m : List UInt8) : List (List UInt8) :=
  if N = [] ∧ S = [] then absorbPayload 136 domShake256 m
  else absorbPayload 136 domCshake256 (cshakePrefix N S ++ m)

theorem evalCshake256Sponge_eq_paddedBlocks {σ : Type} (π : σ → σ) (zeroState : σ)
    (xorBlock : σ → List UInt8 → σ) (extractRate : σ → List UInt8)
    (N S msg : List UInt8) (outLen : Nat) :
    evalCshake256Sponge π zeroState xorBlock extractRate N S msg outLen =
      spongeSqueeze 136 π extractRate outLen
        (spongeFold π xorBlock zeroState (cshake256PaddedBlocks N S msg)) := by
  unfold evalCshake256Sponge cshake256PaddedBlocks evalSponge
  split <;> exact congrArg _ (spongeAbsorbBlocks_eq_spongeFold π xorBlock zeroState _)

private theorem validDom_shake : ValidDomByte domShake256 := by
  rw [domShake256.public_eqs]; exact ⟨by decide, by decide⟩

private theorem validDom_cshake : ValidDomByte domCshake256 := by
  rw [domCshake256.public_eqs]; exact ⟨by decide, by decide⟩

/-- Distinct `(N, S, message, output block)` quadruples address distinct block paths. -/
theorem cshake256_output_path_injective {N₁ S₁ N₂ S₂ m₁ m₂ : List UInt8} {j₁ j₂ : Nat}
    (hN₁ : 8 * N₁.length < 256 ^ 255) (hS₁ : 8 * S₁.length < 256 ^ 255)
    (hN₂ : 8 * N₂.length < 256 ^ 255) (hS₂ : 8 * S₂.length < 256 ^ 255)
    (h : cshake256PaddedBlocks N₁ S₁ m₁ ++ List.replicate j₁ (List.replicate 136 0) =
      cshake256PaddedBlocks N₂ S₂ m₂ ++ List.replicate j₂ (List.replicate 136 0)) :
    N₁ = N₂ ∧ S₁ = S₂ ∧ m₁ = m₂ ∧ j₁ = j₂ := by
  have hLast : ∀ (N S m : List UInt8) (init : List (List UInt8)),
      cshake256PaddedBlocks N S m ≠ init ++ [List.replicate 136 0] := by
    intro N S m init
    unfold cshake256PaddedBlocks
    split
    · exact absorbPayload_last_block_ne_zero (by decide) validDom_shake m init
    · exact absorbPayload_last_block_ne_zero (by decide) validDom_cshake _ init
  obtain ⟨hw, hj⟩ := sponge_output_path_injective (List.replicate 136 (0 : UInt8)) j₁ j₂ _ _
    (hLast N₁ S₁ m₁) (hLast N₂ S₂ m₂) h
  by_cases hNS : (N₁, S₁) = (N₂, S₂)
  · obtain ⟨hN, hS⟩ := Prod.mk.inj hNS
    subst hN; subst hS
    refine ⟨rfl, rfl, ?_, hj⟩
    unfold cshake256PaddedBlocks at hw
    split at hw
    · exact pad10star1_injective (by decide) validDom_shake hw
    · exact List.append_cancel_left
        (pad10star1_injective (by decide) validDom_cshake hw)
  · exact absurd hw (cshake256_padded_blocks_ne m₁ m₂ hN₁ hS₁ hN₂ hS₂ hNS)

/-- **Permutation-query disjointness across `cSHAKE256` customizations.** For
    `(N₁, S₁, m₁, j₁) ≠ (N₂, S₂, m₂, j₂)` the `π`-inputs producing the two output blocks differ,
    or the earlier queries of the two runs contain a capacity event. -/
theorem cshake256_output_queries_disjoint_or_cap_collision {σ κ : Type} [DecidableEq σ]
    {capOf : σ → κ} {xorBlk : σ → List UInt8 → σ}
    (hL : SpongeCapLaws capOf xorBlk (fun b => b.length = 136)) (π : σ → σ) (s0 : σ)
    {N₁ S₁ N₂ S₂ : List UInt8} (m₁ m₂ : List UInt8) (j₁ j₂ : Nat)
    (hN₁ : 8 * N₁.length < 256 ^ 255) (hS₁ : 8 * S₁.length < 256 ^ 255)
    (hN₂ : 8 * N₂.length < 256 ^ 255) (hS₂ : 8 * S₂.length < 256 ^ 255)
    (hNe : (N₁, S₁, m₁, j₁) ≠ (N₂, S₂, m₂, j₂)) :
    spongeTerminalQuery π xorBlk s0
        (cshake256PaddedBlocks N₁ S₁ m₁ ++ List.replicate j₁ (List.replicate 136 0)) ≠
      spongeTerminalQuery π xorBlk s0
        (cshake256PaddedBlocks N₂ S₂ m₂ ++ List.replicate j₂ (List.replicate 136 0)) ∨
    SpongeCapEvent π capOf s0
      (spongeInnerQueries π xorBlk s0
          (cshake256PaddedBlocks N₁ S₁ m₁ ++ List.replicate j₁ (List.replicate 136 0)) ++
        spongeInnerQueries π xorBlk s0
          (cshake256PaddedBlocks N₂ S₂ m₂ ++ List.replicate j₂ (List.replicate 136 0))) := by
  have hVal : ∀ (N S m : List UInt8) (j : Nat) (b : List UInt8),
      b ∈ cshake256PaddedBlocks N S m ++ List.replicate j (List.replicate 136 (0 : UInt8)) →
        b.length = 136 := by
    intro N S m j
    unfold cshake256PaddedBlocks
    split
    · exact absorbPayload_extended_valid (by decide) _ m j
    · exact absorbPayload_extended_valid (by decide) _ _ j
  have hNil : ∀ (N S m : List UInt8), cshake256PaddedBlocks N S m ≠ [] := by
    intro N S m
    unfold cshake256PaddedBlocks
    split
    · exact absorbPayload_ne_nil (by decide) _ m
    · exact absorbPayload_ne_nil (by decide) _ _
  refine sponge_terminal_query_ne_or_cap_event hL π s0 _ _ (hVal N₁ S₁ m₁ j₁)
    (hVal N₂ S₂ m₂ j₂)
    (fun h => hNil N₁ S₁ m₁ (List.append_eq_nil_iff.mp h).1)
    (fun h => hNil N₂ S₂ m₂ (List.append_eq_nil_iff.mp h).1) ?_
  intro hEq
  obtain ⟨hN, hS, hm, hj⟩ := cshake256_output_path_injective hN₁ hS₁ hN₂ hS₂ hEq
  exact hNe (by rw [hN, hS, hm, hj])

/-- The four `QSAG.*` `cSHAKE256` customization tags of `Qsag.Oracle.Sponge`. -/
def qsagSpongeTags : List (List UInt8) :=
  [qsagTagCanopyLeaf, qsagTagCanopyNode, qsagTagFiatShamir, qsagTagFtsOtPad]

theorem qsagSpongeTags_eq :
    qsagSpongeTags = [qsagTagCanopyLeaf, qsagTagCanopyNode, qsagTagFiatShamir, qsagTagFtsOtPad] := by
  rfl

theorem qsagSpongeTags_pairwise_distinct : qsagSpongeTags.Nodup := by
  unfold qsagSpongeTags
  rw [qsagTagCanopyLeaf.public_eqs, qsagTagCanopyNode.public_eqs, qsagTagFiatShamir.public_eqs,
    qsagTagFtsOtPad.public_eqs]
  decide

private theorem qsagSpongeTags_short {S : List UInt8} (hS : S ∈ qsagSpongeTags) :
    8 * S.length < 256 ^ 255 := by
  apply bitlen_lt_sp800_bound
  unfold qsagSpongeTags at hS
  rw [qsagTagCanopyLeaf.public_eqs, qsagTagCanopyNode.public_eqs, qsagTagFiatShamir.public_eqs,
    qsagTagFtsOtPad.public_eqs] at hS
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl <;> decide

/-- **`QSAG.*` tag separation at the permutation.** For tags `S₁, S₂` of `qsagSpongeTags` and
    `(S₁, m₁, j₁) ≠ (S₂, m₂, j₂)`, the two `cSHAKE256` runs end in different `π`-inputs for the
    requested output blocks, or their earlier queries contain a capacity event. -/
theorem qsag_tags_output_queries_disjoint_or_cap_collision {σ κ : Type} [DecidableEq σ]
    {capOf : σ → κ} {xorBlk : σ → List UInt8 → σ}
    (hL : SpongeCapLaws capOf xorBlk (fun b => b.length = 136)) (π : σ → σ) (s0 : σ)
    {S₁ S₂ : List UInt8} (hS₁ : S₁ ∈ qsagSpongeTags) (hS₂ : S₂ ∈ qsagSpongeTags)
    (m₁ m₂ : List UInt8) (j₁ j₂ : Nat) (hNe : (S₁, m₁, j₁) ≠ (S₂, m₂, j₂)) :
    spongeTerminalQuery π xorBlk s0
        (cshake256PaddedBlocks [] S₁ m₁ ++ List.replicate j₁ (List.replicate 136 0)) ≠
      spongeTerminalQuery π xorBlk s0
        (cshake256PaddedBlocks [] S₂ m₂ ++ List.replicate j₂ (List.replicate 136 0)) ∨
    SpongeCapEvent π capOf s0
      (spongeInnerQueries π xorBlk s0
          (cshake256PaddedBlocks [] S₁ m₁ ++ List.replicate j₁ (List.replicate 136 0)) ++
        spongeInnerQueries π xorBlk s0
          (cshake256PaddedBlocks [] S₂ m₂ ++ List.replicate j₂ (List.replicate 136 0))) :=
  cshake256_output_queries_disjoint_or_cap_collision hL π s0 m₁ m₂ j₁ j₂
    (bitlen_lt_sp800_bound (by decide)) (qsagSpongeTags_short hS₁)
    (bitlen_lt_sp800_bound (by decide)) (qsagSpongeTags_short hS₂)
    (fun h => hNe (by
      have h1 := (Prod.mk.inj h).2
      rw [(Prod.mk.inj h1).1, (Prod.mk.inj (Prod.mk.inj h1).2).1, (Prod.mk.inj (Prod.mk.inj h1).2).2]))

/-! ### Instances of `SpongeCapLaws` -/

/-- Product state `Rate × Cap` with XOR absorption on the rate. -/
@[expose] def rateCapXor {n : Nat} {κ : Type} (s : BitVec n × κ) (b : BitVec n) : BitVec n × κ :=
  (s.1 ^^^ b, s.2)

theorem rateCapXor_laws {n : Nat} {κ : Type} :
    SpongeCapLaws (σ := BitVec n × κ) (β := BitVec n) Prod.snd rateCapXor (fun _ => True) where
  cap_xor _ _ _ := rfl
  xor_inj s b₁ b₂ _ _ h := by
    have h1 : s.1 ^^^ b₁ = s.1 ^^^ b₂ := congrArg Prod.fst h
    have h2 : s.1 ^^^ (s.1 ^^^ b₁) = s.1 ^^^ (s.1 ^^^ b₂) := congrArg (s.1 ^^^ ·) h1
    rw [bv_xor_cancel_left, bv_xor_cancel_left] at h2
    exact h2

theorem rateCapXor_zero {n : Nat} {κ : Type} (s : BitVec n × κ) : rateCapXor s 0#n = s := by
  unfold rateCapXor
  rw [bv_xor_zero]

/-- The 512-bit capacity of `Keccak-f[1600]` at rate 136: lanes `a17 … a24`. -/
def keccakCap512 (s : KState) : List UInt64 :=
  [s.a17, s.a18, s.a19, s.a20, s.a21, s.a22, s.a23, s.a24]

theorem keccakRate136_cap_xor (s : KState) (b : List UInt8) :
    keccakCap512 (xorRate136 s b) = keccakCap512 s := by
  rw [xorRate136_eq]
  rfl

theorem keccakRate136_zero (s : KState) : xorRate136 s (List.replicate 136 0) = s := by
  rw [xorRate136_eq]
  simp only [loadLe64_replicate_zero, u64_xor_zero]

private theorem or_mul_pow (x b k : Nat) (hx : x < 2 ^ k) : x ||| b * 2 ^ k = b * 2 ^ k + x := by
  rw [Nat.or_comm, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt hx b]

private theorem le64_toNat (a0 a1 a2 a3 a4 a5 a6 a7 : UInt8) :
    (a0.toUInt64 ||| a1.toUInt64 <<< 8 ||| a2.toUInt64 <<< 16 ||| a3.toUInt64 <<< 24 |||
      a4.toUInt64 <<< 32 ||| a5.toUInt64 <<< 40 ||| a6.toUInt64 <<< 48 |||
      a7.toUInt64 <<< 56).toNat =
    a7.toNat * 2 ^ 56 + (a6.toNat * 2 ^ 48 + (a5.toNat * 2 ^ 40 + (a4.toNat * 2 ^ 32 +
      (a3.toNat * 2 ^ 24 + (a2.toNat * 2 ^ 16 + (a1.toNat * 2 ^ 8 + a0.toNat)))))) := by
  have h0 := a0.toNat_lt
  have h1 := a1.toNat_lt
  have h2 := a2.toNat_lt
  have h3 := a3.toNat_lt
  have h4 := a4.toNat_lt
  have h5 := a5.toNat_lt
  have h6 := a6.toNat_lt
  have h7 := a7.toNat_lt
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64]
  have m1 : a1.toNat <<< ((8 : UInt64).toNat % 64) % 2 ^ 64 = a1.toNat * 2 ^ 8 := by
    rw [show (8 : UInt64).toNat % 64 = 8 from rfl, Nat.shiftLeft_eq]; omega
  have m2 : a2.toNat <<< ((16 : UInt64).toNat % 64) % 2 ^ 64 = a2.toNat * 2 ^ 16 := by
    rw [show (16 : UInt64).toNat % 64 = 16 from rfl, Nat.shiftLeft_eq]; omega
  have m3 : a3.toNat <<< ((24 : UInt64).toNat % 64) % 2 ^ 64 = a3.toNat * 2 ^ 24 := by
    rw [show (24 : UInt64).toNat % 64 = 24 from rfl, Nat.shiftLeft_eq]; omega
  have m4 : a4.toNat <<< ((32 : UInt64).toNat % 64) % 2 ^ 64 = a4.toNat * 2 ^ 32 := by
    rw [show (32 : UInt64).toNat % 64 = 32 from rfl, Nat.shiftLeft_eq]; omega
  have m5 : a5.toNat <<< ((40 : UInt64).toNat % 64) % 2 ^ 64 = a5.toNat * 2 ^ 40 := by
    rw [show (40 : UInt64).toNat % 64 = 40 from rfl, Nat.shiftLeft_eq]; omega
  have m6 : a6.toNat <<< ((48 : UInt64).toNat % 64) % 2 ^ 64 = a6.toNat * 2 ^ 48 := by
    rw [show (48 : UInt64).toNat % 64 = 48 from rfl, Nat.shiftLeft_eq]; omega
  have m7 : a7.toNat <<< ((56 : UInt64).toNat % 64) % 2 ^ 64 = a7.toNat * 2 ^ 56 := by
    rw [show (56 : UInt64).toNat % 64 = 56 from rfl, Nat.shiftLeft_eq]; omega
  rw [m1, m2, m3, m4, m5, m6, m7]
  rw [or_mul_pow a0.toNat a1.toNat 8 h0,
    or_mul_pow _ a2.toNat 16 (by omega), or_mul_pow _ a3.toNat 24 (by omega),
    or_mul_pow _ a4.toNat 32 (by omega), or_mul_pow _ a5.toNat 40 (by omega),
    or_mul_pow _ a6.toNat 48 (by omega), or_mul_pow _ a7.toNat 56 (by omega)]

private theorem le64_inj (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : UInt8)
    (h : (a0.toUInt64 ||| a1.toUInt64 <<< 8 ||| a2.toUInt64 <<< 16 ||| a3.toUInt64 <<< 24 |||
        a4.toUInt64 <<< 32 ||| a5.toUInt64 <<< 40 ||| a6.toUInt64 <<< 48 |||
        a7.toUInt64 <<< 56) =
      (b0.toUInt64 ||| b1.toUInt64 <<< 8 ||| b2.toUInt64 <<< 16 ||| b3.toUInt64 <<< 24 |||
        b4.toUInt64 <<< 32 ||| b5.toUInt64 <<< 40 ||| b6.toUInt64 <<< 48 |||
        b7.toUInt64 <<< 56)) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4 ∧ a5 = b5 ∧ a6 = b6 ∧ a7 = b7 := by
  have hN := congrArg UInt64.toNat h
  rw [le64_toNat, le64_toNat] at hN
  have h0 := a0.toNat_lt
  have h1 := a1.toNat_lt
  have h2 := a2.toNat_lt
  have h3 := a3.toNat_lt
  have h4 := a4.toNat_lt
  have h5 := a5.toNat_lt
  have h6 := a6.toNat_lt
  have h7 := a7.toNat_lt
  have g0 := b0.toNat_lt
  have g1 := b1.toNat_lt
  have g2 := b2.toNat_lt
  have g3 := b3.toNat_lt
  have g4 := b4.toNat_lt
  have g5 := b5.toNat_lt
  have g6 := b6.toNat_lt
  have g7 := b7.toNat_lt
  exact ⟨UInt8.toNat_inj.mp (by omega), UInt8.toNat_inj.mp (by omega),
    UInt8.toNat_inj.mp (by omega), UInt8.toNat_inj.mp (by omega),
    UInt8.toNat_inj.mp (by omega), UInt8.toNat_inj.mp (by omega),
    UInt8.toNat_inj.mp (by omega), UInt8.toNat_inj.mp (by omega)⟩

private theorem loadLe64_bytes_inj (b₁ b₂ : List UInt8) (i : Nat)
    (h : loadLe64 b₁ i = loadLe64 b₂ i) :
    ∀ k, k < 8 → b₁.getD (8 * i + k) 0 = b₂.getD (8 * i + k) 0 := by
  rw [loadLe64_eq, loadLe64_eq] at h
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := le64_inj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
  intro k hk
  match k, hk with
  | 0, _ => exact e0
  | 1, _ => exact e1
  | 2, _ => exact e2
  | 3, _ => exact e3
  | 4, _ => exact e4
  | 5, _ => exact e5
  | 6, _ => exact e6
  | 7, _ => exact e7

private theorem block136_ext (b₁ b₂ : List UInt8) (h₁ : b₁.length = 136) (h₂ : b₂.length = 136)
    (H : ∀ i, i < 17 → loadLe64 b₁ i = loadLe64 b₂ i) : b₁ = b₂ := by
  apply List.ext_getElem (h₁.trans h₂.symm)
  intro n hn₁ hn₂
  have hD := loadLe64_bytes_inj b₁ b₂ (n / 8) (H (n / 8) (by omega)) (n % 8)
    (Nat.mod_lt _ (by decide))
  rw [Nat.div_add_mod n 8] at hD
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn₁,
    List.getElem?_eq_getElem hn₂] at hD
  exact hD

private theorem u64_xor_left_cancel {x y z : UInt64} (h : x ^^^ y = x ^^^ z) : y = z := by
  have h2 : x ^^^ (x ^^^ y) = x ^^^ (x ^^^ z) := congrArg (x ^^^ ·) h
  rw [u64_xor_cancel_left, u64_xor_cancel_left] at h2
  exact h2

/-- Rate-136 absorption into `Keccak-f[1600]` is injective in a 136-byte block. -/
theorem keccakRate136_xor_inj (s : KState) (b₁ b₂ : List UInt8) (h₁ : b₁.length = 136)
    (h₂ : b₂.length = 136) (h : xorRate136 s b₁ = xorRate136 s b₂) : b₁ = b₂ := by
  rw [xorRate136_eq, xorRate136_eq] at h
  refine block136_ext b₁ b₂ h₁ h₂ ?_
  intro i hi
  match i, hi with
  | 0, _ => exact u64_xor_left_cancel (congrArg KState.a0 h)
  | 1, _ => exact u64_xor_left_cancel (congrArg KState.a1 h)
  | 2, _ => exact u64_xor_left_cancel (congrArg KState.a2 h)
  | 3, _ => exact u64_xor_left_cancel (congrArg KState.a3 h)
  | 4, _ => exact u64_xor_left_cancel (congrArg KState.a4 h)
  | 5, _ => exact u64_xor_left_cancel (congrArg KState.a5 h)
  | 6, _ => exact u64_xor_left_cancel (congrArg KState.a6 h)
  | 7, _ => exact u64_xor_left_cancel (congrArg KState.a7 h)
  | 8, _ => exact u64_xor_left_cancel (congrArg KState.a8 h)
  | 9, _ => exact u64_xor_left_cancel (congrArg KState.a9 h)
  | 10, _ => exact u64_xor_left_cancel (congrArg KState.a10 h)
  | 11, _ => exact u64_xor_left_cancel (congrArg KState.a11 h)
  | 12, _ => exact u64_xor_left_cancel (congrArg KState.a12 h)
  | 13, _ => exact u64_xor_left_cancel (congrArg KState.a13 h)
  | 14, _ => exact u64_xor_left_cancel (congrArg KState.a14 h)
  | 15, _ => exact u64_xor_left_cancel (congrArg KState.a15 h)
  | 16, _ => exact u64_xor_left_cancel (congrArg KState.a16 h)
  | i + 17, h => exact absurd h (by omega)

/-- `Keccak-f[1600]` at rate 136 satisfies the capacity-split laws with the 512-bit capacity
    `keccakCap512`. -/
theorem keccakRate136_laws :
    SpongeCapLaws keccakCap512 xorRate136 (fun b => b.length = 136) where
  cap_xor s b _ := keccakRate136_cap_xor s b
  xor_inj s b₁ b₂ h₁ h₂ h := keccakRate136_xor_inj s b₁ b₂ h₁ h₂ h

/-- **`QSAG.*` tag separation at `Keccak-f[1600]`.** For every transformation `π` on the Keccak
    state (the real permutation included) and tags `S₁, S₂` of `qsagSpongeTags` with
    `(S₁, m₁, j₁) ≠ (S₂, m₂, j₂)`: the two `cSHAKE256` runs feed different inputs to `π` for the
    requested output blocks, or their earlier queries contain a 512-bit capacity event. -/
theorem keccak_qsag_tags_output_queries_disjoint_or_cap_collision (π : KState → KState)
    {S₁ S₂ : List UInt8} (hS₁ : S₁ ∈ qsagSpongeTags) (hS₂ : S₂ ∈ qsagSpongeTags)
    (m₁ m₂ : List UInt8) (j₁ j₂ : Nat) (hNe : (S₁, m₁, j₁) ≠ (S₂, m₂, j₂)) :
    spongeTerminalQuery π xorRate136 zeroKState
        (cshake256PaddedBlocks [] S₁ m₁ ++ List.replicate j₁ (List.replicate 136 0)) ≠
      spongeTerminalQuery π xorRate136 zeroKState
        (cshake256PaddedBlocks [] S₂ m₂ ++ List.replicate j₂ (List.replicate 136 0)) ∨
    SpongeCapEvent π keccakCap512 zeroKState
      (spongeInnerQueries π xorRate136 zeroKState
          (cshake256PaddedBlocks [] S₁ m₁ ++ List.replicate j₁ (List.replicate 136 0)) ++
        spongeInnerQueries π xorRate136 zeroKState
          (cshake256PaddedBlocks [] S₂ m₂ ++ List.replicate j₂ (List.replicate 136 0))) :=
  qsag_tags_output_queries_disjoint_or_cap_collision keccakRate136_laws π zeroKState hS₁ hS₂
    m₁ m₂ j₁ j₂ hNe

/-! ## §4. A lazily sampled transformation: coins, tables and the capacity event -/

/-- Newest-first table lookup. -/
def spongeLookup {Dom V : Type} [DecidableEq Dom] : List (Dom × V) → Dom → Option V
  | [], _ => none
  | e :: rest, q => if q = e.1 then some e.2 else spongeLookup rest q

/-- Quotient coordinate of a coin of `Fin (a * b)`: the draw used now. -/
def spongeCoinHead {a b : Nat} (ω : Fin (a * b)) : Fin a :=
  ⟨ω.val / b, Spec.prodCoin_quot_lt ω⟩

/-- Remainder coordinate of a coin of `Fin (a * b)`: the draws kept for later. -/
def spongeCoinTail {a b : Nat} (ω : Fin (a * b)) : Fin b :=
  ⟨ω.val % b, Nat.mod_lt _ (Spec.prodCoin_right_pos ω)⟩

private theorem spongeCoinHead_pair {a b : Nat} (c : Fin a) (x : Fin b) :
    spongeCoinHead (⟨c.1 * b + x.1, Spec.prodCoin_pair_lt c x⟩ : Fin (a * b)) = c :=
  Fin.ext (Spec.prodCoin_pair_quot c x)

private theorem spongeCoinTail_pair {a b : Nat} (c : Fin a) (x : Fin b) :
    spongeCoinTail (⟨c.1 * b + x.1, Spec.prodCoin_pair_lt c x⟩ : Fin (a * b)) = x :=
  Fin.ext (Spec.prodCoin_pair_rem c x)

/-- Run an adaptive program against a lazily sampled function `Dom → Fin cardD` with `K` uniform
    draws. Every call uses one coin position; a repeated query is answered from the table. A
    call with no coin left stops the run with result `none`. -/
def spongeLazyRun {Dom R : Type} [DecidableEq Dom] {cardD : Nat} :
    Spec.Code (Spec.roOracleIface Dom cardD) R → (K : Nat) → List (Dom × Fin cardD) →
      Fin (Spec.roCoinPow cardD K) → Option R × List (Dom × Fin cardD)
  | .ret v, _, st, _ => (some v, st)
  | .call _ _, 0, st, _ => (none, st)
  | .call q next, K + 1, st, ω =>
    match spongeLookup st q with
    | some y => spongeLazyRun (next y) K st (spongeCoinTail (a := cardD) ω)
    | none =>
      spongeLazyRun (next (spongeCoinHead (b := Spec.roCoinPow cardD K) ω)) K
        ((q, spongeCoinHead (b := Spec.roCoinPow cardD K) ω) :: st)
        (spongeCoinTail (a := cardD) ω)

theorem spongeLazyRun_ret {Dom R : Type} [DecidableEq Dom] {cardD : Nat} (v : R) (K : Nat)
    (st : List (Dom × Fin cardD)) (ω : Fin (Spec.roCoinPow cardD K)) :
    spongeLazyRun (Spec.Code.ret v) K st ω = (some v, st) := by
  unfold spongeLazyRun; rfl

theorem spongeLazyRun_call_zero {Dom R : Type} [DecidableEq Dom] {cardD : Nat} (q : Dom)
    (next : Fin cardD → Spec.Code (Spec.roOracleIface Dom cardD) R)
    (st : List (Dom × Fin cardD)) (ω : Fin (Spec.roCoinPow cardD 0)) :
    spongeLazyRun (Spec.Code.call q next) 0 st ω = (none, st) := by
  unfold spongeLazyRun; rfl

theorem spongeLazyRun_call_hit {Dom R : Type} [DecidableEq Dom] {cardD : Nat} (q : Dom)
    (next : Fin cardD → Spec.Code (Spec.roOracleIface Dom cardD) R) (K : Nat)
    (st : List (Dom × Fin cardD)) (ω : Fin (Spec.roCoinPow cardD (K + 1))) (y : Fin cardD)
    (h : spongeLookup st q = some y) :
    spongeLazyRun (Spec.Code.call q next) (K + 1) st ω =
      spongeLazyRun (next y) K st (spongeCoinTail (a := cardD) ω) := by
  conv => lhs; unfold spongeLazyRun
  simp only [h]

theorem spongeLazyRun_call_miss {Dom R : Type} [DecidableEq Dom] {cardD : Nat} (q : Dom)
    (next : Fin cardD → Spec.Code (Spec.roOracleIface Dom cardD) R) (K : Nat)
    (st : List (Dom × Fin cardD)) (ω : Fin (Spec.roCoinPow cardD (K + 1)))
    (h : spongeLookup st q = none) :
    spongeLazyRun (Spec.Code.call q next) (K + 1) st ω =
      spongeLazyRun (next (spongeCoinHead (b := Spec.roCoinPow cardD K) ω)) K
        ((q, spongeCoinHead (b := Spec.roCoinPow cardD K) ω) :: st)
        (spongeCoinTail (a := cardD) ω) := by
  conv => lhs; unfold spongeLazyRun
  simp only [h]

/-- A fresh draw `d` is bad against the earlier outputs `outs`: its capacity is the initial one
    or the capacity of an earlier output. -/
def capOutBad {σ κ : Type} [DecidableEq κ] {cardD : Nat} (capOf : σ → κ) (dec : Fin cardD → σ)
    (s0 : σ) (outs : List (Fin cardD)) (d : Fin cardD) : Bool :=
  decide (capOf (dec d) = capOf s0) ||
    outs.any (fun e => decide (capOf (dec d) = capOf (dec e)))

/-- Some output was bad at the moment it was drawn (outputs newest first). -/
def capOutsBad {σ κ : Type} [DecidableEq κ] {cardD : Nat} (capOf : σ → κ) (dec : Fin cardD → σ)
    (s0 : σ) : List (Fin cardD) → Bool
  | [] => false
  | d :: outs => capOutBad capOf dec s0 outs d || capOutsBad capOf dec s0 outs

/-- The capacity event of a table: some recorded draw was bad when it was made. -/
def capTableBad {Dom σ κ : Type} [DecidableEq κ] {cardD : Nat} (capOf : σ → κ)
    (dec : Fin cardD → σ) (s0 : σ) (st : List (Dom × Fin cardD)) : Bool :=
  capOutsBad capOf dec s0 (st.map Prod.snd)

/-! ### Finite sums (the `Spec.sampleSum` lemmas of `Spec.Assumptions` are module-private) -/

private theorem sds_sum_ext {m : Nat} {f g : Fin m → Nat} (h : ∀ i, f i = g i) :
    Spec.sampleSum m f = Spec.sampleSum m g :=
  congrArg (Spec.sampleSum m) (funext h)

private theorem sds_sum_le :
    ∀ (m : Nat) (f g : Fin m → Nat), (∀ i, f i ≤ g i) → Spec.sampleSum m f ≤ Spec.sampleSum m g
  | 0, _, _, _ => Nat.le_refl 0
  | m + 1, _, _, h =>
    Nat.add_le_add (h ⟨0, Nat.zero_lt_succ m⟩)
      (sds_sum_le m _ _ (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩))

private theorem sds_sum_add :
    ∀ (m : Nat) (f g : Fin m → Nat),
      Spec.sampleSum m (fun i => f i + g i) = Spec.sampleSum m f + Spec.sampleSum m g
  | 0, _, _ => rfl
  | m + 1, f, g => by
    rw [Spec.sampleSum_succ, Spec.sampleSum_succ, Spec.sampleSum_succ, sds_sum_add m]
    omega

private theorem sds_sum_mul_right :
    ∀ (m : Nat) (f : Fin m → Nat) (c : Nat),
      Spec.sampleSum m (fun i => f i * c) = Spec.sampleSum m f * c
  | 0, _, _ => (Nat.zero_mul _).symm
  | m + 1, f, c => by
    rw [Spec.sampleSum_succ, Spec.sampleSum_succ, sds_sum_mul_right m, Nat.add_mul]

private theorem sds_sum_const :
    ∀ (m c : Nat), Spec.sampleSum m (fun _ => c) = m * c
  | 0, c => (Nat.zero_mul c).symm
  | m + 1, c => by
    rw [Spec.sampleSum_succ, sds_sum_const m, Nat.succ_mul, Nat.add_comm]

private theorem sds_sum_cast {m m' : Nat} (h : m = m') (f : Fin m' → Nat) :
    Spec.sampleSum m (fun i => f ⟨i.1, h ▸ i.2⟩) = Spec.sampleSum m' f := by
  subst h; rfl

private theorem sds_sum_split :
    ∀ (a b : Nat) (f : Fin (a + b) → Nat),
      Spec.sampleSum (a + b) f =
        Spec.sampleSum a (fun i => f ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.le_add_right a b)⟩) +
        Spec.sampleSum b (fun j => f ⟨a + j.1, Nat.add_lt_add_left j.2 a⟩)
  | 0, b, f => by
    simp only [Spec.sampleSum_zero, Nat.zero_add]
    exact sds_sum_cast (Nat.zero_add b) (fun j => f ⟨j.1, by omega⟩)
  | a + 1, b, f => by
    have hCast : Spec.sampleSum ((a + 1) + b) f =
        Spec.sampleSum ((a + b) + 1) (fun i => f ⟨i.1, (Nat.succ_add a b).symm ▸ i.2⟩) := by
      have h := sds_sum_cast (Nat.succ_add a b)
        (fun i : Fin ((a + b) + 1) => f ⟨i.1, (Nat.succ_add a b).symm ▸ i.2⟩)
      exact (sds_sum_ext (fun i => rfl)).trans h
    rw [hCast, Spec.sampleSum_succ, sds_sum_split a b, Spec.sampleSum_succ]
    have hMid : Spec.sampleSum a (fun i : Fin a =>
        f ⟨i.1 + 1, (Nat.succ_add a b).symm ▸ Nat.succ_lt_succ
          (Nat.lt_of_lt_of_le i.2 (Nat.le_add_right a b))⟩) =
        Spec.sampleSum a (fun i : Fin a =>
          f ⟨i.1 + 1, Nat.lt_of_lt_of_le (Nat.succ_lt_succ i.2) (Nat.le_add_right (a + 1) b)⟩) :=
      sds_sum_ext (fun _ => rfl)
    have hRight : Spec.sampleSum b (fun j : Fin b =>
        f ⟨(a + j.1) + 1,
          (Nat.succ_add a b).symm ▸ Nat.succ_lt_succ (Nat.add_lt_add_left j.2 a)⟩) =
        Spec.sampleSum b (fun j : Fin b => f ⟨(a + 1) + j.1, Nat.add_lt_add_left j.2 (a + 1)⟩) :=
      sds_sum_ext (fun j => congrArg f (Fin.ext (by dsimp only; omega)))
    rw [hMid, hRight]
    exact (Nat.add_assoc _ _ _).symm

private theorem sds_sum_prod :
    ∀ (m n : Nat) (f : Fin (m * n) → Nat),
      Spec.sampleSum (m * n) f =
        Spec.sampleSum m (fun i => Spec.sampleSum n (fun j =>
          f ⟨i.1 * n + j.1, Spec.prodCoin_pair_lt i j⟩))
  | 0, n, f => by
    rw [Spec.sampleSum_zero]
    have h := sds_sum_cast (Nat.zero_mul n)
      (fun i : Fin 0 => f ⟨i.1, (Nat.zero_mul n).symm ▸ i.2⟩)
    exact h
  | m + 1, n, f => by
    have hEq : (m + 1) * n = n + m * n := (Nat.succ_mul m n).trans (Nat.add_comm (m * n) n)
    have hCast : Spec.sampleSum ((m + 1) * n) f =
        Spec.sampleSum (n + m * n) (fun k => f ⟨k.1, hEq.symm ▸ k.2⟩) :=
      sds_sum_cast hEq (fun k : Fin (n + m * n) => f ⟨k.1, hEq.symm ▸ k.2⟩)
    rw [hCast, sds_sum_split n (m * n), sds_sum_prod m n, Spec.sampleSum_succ]
    have hHead : Spec.sampleSum n (fun i : Fin n =>
        f ⟨i.1, hEq.symm ▸ Nat.lt_of_lt_of_le i.2 (Nat.le_add_right n (m * n))⟩) =
        Spec.sampleSum n (fun j : Fin n =>
          f ⟨(⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)).1 * n + j.1,
            Spec.prodCoin_pair_lt ⟨0, Nat.zero_lt_succ m⟩ j⟩) :=
      sds_sum_ext (fun j => congrArg f (Fin.ext (by simp)))
    have hTail : Spec.sampleSum m (fun i : Fin m => Spec.sampleSum n (fun j : Fin n =>
        f ⟨n + (i.1 * n + j.1),
          hEq.symm ▸ Nat.add_lt_add_left (Spec.prodCoin_pair_lt i j) n⟩)) =
        Spec.sampleSum m (fun i : Fin m => Spec.sampleSum n (fun j : Fin n =>
          f ⟨(i.1 + 1) * n + j.1, Spec.prodCoin_pair_lt ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ j⟩)) :=
      sds_sum_ext (fun i => sds_sum_ext (fun j => congrArg f (Fin.ext (by
        dsimp only
        rw [Nat.add_mul, Nat.one_mul]
        omega))))
    rw [hHead, hTail]

private theorem sds_sum_le_card (m : Nat) (p : Fin m → Bool) :
    Spec.sampleSum m (fun i => if p i then 1 else 0) ≤ m := by
  have h := sds_sum_le m (fun i => if p i then 1 else 0) (fun _ => 1)
    (fun i => by cases p i <;> decide)
  rw [sds_sum_const m 1, Nat.mul_one] at h
  exact h

/-! ## §5. The capacity event has probability at most `K (K + 1) R / (2 cardD)` -/

private theorem bool_or3_indicator_le (A B C : Bool) :
    (if (A || (B || C)) = true then 1 else 0) ≤
      (if B = true then 1 else 0) + (if (A || C) = true then 1 else 0) := by
  cases A <;> cases B <;> cases C <;> decide

/-- At most `(|outs| + 1) · R` draws are bad against `outs`, when every capacity value has at
    most `R` preimages under `dec`. -/
private theorem capOutBad_count {σ κ : Type} [DecidableEq κ] {cardD Rfib : Nat} (capOf : σ → κ)
    (dec : Fin cardD → σ) (s0 : σ)
    (hFib : ∀ c : κ, Spec.sampleSum cardD (fun d => if capOf (dec d) = c then 1 else 0) ≤ Rfib) :
    ∀ outs : List (Fin cardD),
      Spec.sampleSum cardD (fun d => if capOutBad capOf dec s0 outs d = true then 1 else 0) ≤
        (outs.length + 1) * Rfib
  | [] => by
    have hEq : (fun d : Fin cardD => if capOutBad capOf dec s0 [] d = true then 1 else 0) =
        (fun d => if capOf (dec d) = capOf s0 then 1 else 0) := by
      funext d
      unfold capOutBad
      simp only [List.any_nil, Bool.or_false, decide_eq_true_eq]
    rw [hEq, List.length_nil, Nat.zero_add, Nat.one_mul]
    exact hFib (capOf s0)
  | e :: outs => by
    have ih := capOutBad_count capOf dec s0 hFib outs
    have hPt : ∀ d : Fin cardD,
        (if capOutBad capOf dec s0 (e :: outs) d = true then 1 else 0) ≤
          (if capOf (dec d) = capOf (dec e) then 1 else 0) +
            (if capOutBad capOf dec s0 outs d = true then 1 else 0) := by
      intro d
      have h := bool_or3_indicator_le (decide (capOf (dec d) = capOf s0))
        (decide (capOf (dec d) = capOf (dec e)))
        (outs.any (fun e' => decide (capOf (dec d) = capOf (dec e'))))
      simp only [decide_eq_true_eq] at h
      unfold capOutBad
      simp only [List.any_cons]
      exact h
    have hSum := sds_sum_le cardD _ _ hPt
    rw [sds_sum_add] at hSum
    have hF := hFib (capOf (dec e))
    rw [List.length_cons, Nat.succ_mul]
    omega

/-- Twice the number of permutation-call index pairs: `K (2 L + K + 1)` bounds
    `2 · Σ_{i < K} (L + i + 1)`. -/
def capBudget (L K : Nat) : Nat := K * (2 * L + K + 1)

private theorem capBudget_mono (L K : Nat) : capBudget L K ≤ capBudget L (K + 1) :=
  Nat.mul_le_mul (Nat.le_succ K) (by omega)

private theorem capBudget_step (L K : Nat) :
    2 * (L + 1) + capBudget (L + 1) K = capBudget L (K + 1) := by
  have h1 : K * (2 * (L + 1) + K + 1) = K * (2 * L + K + 2) + K := by
    rw [show 2 * (L + 1) + K + 1 = (2 * L + K + 2) + 1 by omega, Nat.mul_succ]
  have h2 : (K + 1) * (2 * L + (K + 1) + 1) = K * (2 * L + K + 2) + (2 * L + K + 2) := by
    rw [show 2 * L + (K + 1) + 1 = 2 * L + K + 2 by omega, Nat.succ_mul]
  unfold capBudget
  rw [h1, h2]
  omega

/-- **Capacity-event weight bound for the lazy sampler.** From a table of `L` entries with no
    bad draw, a program run with `K` coins records a bad draw on at most
    `K (2 L + K + 1) · R · cardD^K / (2 · cardD)` coins. -/
theorem spongeLazyRun_cap_bad_bound {Dom R σ κ : Type} [DecidableEq Dom] [DecidableEq κ]
    {cardD Rfib : Nat} (capOf : σ → κ) (dec : Fin cardD → σ) (s0 : σ)
    (hFib : ∀ c : κ, Spec.sampleSum cardD (fun d => if capOf (dec d) = c then 1 else 0) ≤ Rfib) :
    ∀ (c : Spec.Code (Spec.roOracleIface Dom cardD) R) (K : Nat) (st : List (Dom × Fin cardD)),
      capTableBad capOf dec s0 st = false →
      Spec.sampleSum (Spec.roCoinPow cardD K)
          (fun ω => if capTableBad capOf dec s0 (spongeLazyRun c K st ω).2 = true then 1 else 0) *
          (2 * cardD) ≤
        capBudget st.length K * (Rfib * Spec.roCoinPow cardD K)
  | .ret v, K, st, hClean => by
    have hZero : (fun ω : Fin (Spec.roCoinPow cardD K) =>
        if capTableBad capOf dec s0 (spongeLazyRun (Spec.Code.ret v) K st ω).2 = true
          then 1 else 0) = (fun _ => 0) := by
      funext ω; rw [spongeLazyRun_ret, hClean]; rfl
    rw [hZero, sds_sum_const, Nat.mul_zero, Nat.zero_mul]
    exact Nat.zero_le _
  | .call q next, 0, st, hClean => by
    have hZero : (fun ω : Fin (Spec.roCoinPow cardD 0) =>
        if capTableBad capOf dec s0 (spongeLazyRun (Spec.Code.call q next) 0 st ω).2 = true
          then 1 else 0) = (fun _ => 0) := by
      funext ω; rw [spongeLazyRun_call_zero, hClean]; rfl
    rw [hZero, sds_sum_const, Nat.mul_zero, Nat.zero_mul]
    exact Nat.zero_le _
  | .call q next, K + 1, st, hClean => by
    change Spec.sampleSum (cardD * Spec.roCoinPow cardD K) _ * (2 * cardD) ≤
      capBudget st.length (K + 1) * (Rfib * (cardD * Spec.roCoinPow cardD K))
    rw [sds_sum_prod cardD (Spec.roCoinPow cardD K)]
    cases hLook : spongeLookup st q with
    | some y =>
      have hInner : ∀ (d : Fin cardD) (τ : Fin (Spec.roCoinPow cardD K)),
          (if capTableBad capOf dec s0 (spongeLazyRun (Spec.Code.call q next) (K + 1) st
              ⟨d.1 * Spec.roCoinPow cardD K + τ.1, Spec.prodCoin_pair_lt d τ⟩).2 = true
            then 1 else 0) =
          (if capTableBad capOf dec s0 (spongeLazyRun (next y) K st τ).2 = true
            then 1 else 0) := by
        intro d τ
        rw [spongeLazyRun_call_hit q next K st _ y hLook, spongeCoinTail_pair]
      rw [sds_sum_ext (fun d => sds_sum_ext (fun τ => hInner d τ)), sds_sum_const]
      have ih := spongeLazyRun_cap_bad_bound capOf dec s0 hFib (next y) K st hClean
      have h1 := Nat.mul_le_mul_left cardD ih
      have h2 := Nat.mul_le_mul_right (Rfib * (cardD * Spec.roCoinPow cardD K))
        (capBudget_mono st.length K)
      refine Nat.le_trans (Nat.le_of_eq ?_) (Nat.le_trans h1 (Nat.le_trans (Nat.le_of_eq ?_) h2))
      · ac_rfl
      · ac_rfl
    | none =>
      have hInner : ∀ (d : Fin cardD) (τ : Fin (Spec.roCoinPow cardD K)),
          (if capTableBad capOf dec s0 (spongeLazyRun (Spec.Code.call q next) (K + 1) st
              ⟨d.1 * Spec.roCoinPow cardD K + τ.1, Spec.prodCoin_pair_lt d τ⟩).2 = true
            then 1 else 0) =
          (if capTableBad capOf dec s0
              (spongeLazyRun (next d) K ((q, d) :: st) τ).2 = true then 1 else 0) := by
        intro d τ
        rw [spongeLazyRun_call_miss q next K st _ hLook, spongeCoinTail_pair,
          spongeCoinHead_pair]
      rw [sds_sum_ext (fun d => sds_sum_ext (fun τ => hInner d τ))]
      have hPt : ∀ d : Fin cardD,
          Spec.sampleSum (Spec.roCoinPow cardD K) (fun τ =>
              if capTableBad capOf dec s0
                (spongeLazyRun (next d) K ((q, d) :: st) τ).2 = true then 1 else 0) *
              (2 * cardD) ≤
            (if capOutBad capOf dec s0 (st.map Prod.snd) d = true then 1 else 0) *
                (2 * (cardD * Spec.roCoinPow cardD K)) +
              capBudget (st.length + 1) K * (Rfib * Spec.roCoinPow cardD K) := by
        intro d
        cases hBad : capOutBad capOf dec s0 (st.map Prod.snd) d with
        | true =>
          have hTriv := sds_sum_le_card (Spec.roCoinPow cardD K) (fun τ =>
            capTableBad capOf dec s0 (spongeLazyRun (next d) K ((q, d) :: st) τ).2)
          have h1 := Nat.mul_le_mul_right (2 * cardD) hTriv
          refine Nat.le_trans h1 (Nat.le_trans (Nat.le_of_eq ?_) (Nat.le_add_right _ _))
          simp only [↓reduceIte, Nat.one_mul]
          ac_rfl
        | false =>
          have hClean' : capTableBad capOf dec s0 ((q, d) :: st) = false := by
            show capOutsBad capOf dec s0 (d :: st.map Prod.snd) = false
            show (capOutBad capOf dec s0 (st.map Prod.snd) d ||
              capOutsBad capOf dec s0 (st.map Prod.snd)) = false
            rw [hBad, Bool.false_or]
            exact hClean
          have ih := spongeLazyRun_cap_bad_bound capOf dec s0 hFib (next d) K ((q, d) :: st)
            hClean'
          rw [List.length_cons] at ih
          exact Nat.le_trans ih (Nat.le_add_left _ _)
      have hSum := sds_sum_le cardD _ _ hPt
      rw [sds_sum_mul_right, sds_sum_add, sds_sum_mul_right, sds_sum_const] at hSum
      have hCount := capOutBad_count capOf dec s0 hFib (st.map Prod.snd)
      rw [List.length_map] at hCount
      have hC2 := Nat.mul_le_mul_right (2 * (cardD * Spec.roCoinPow cardD K)) hCount
      refine Nat.le_trans hSum (Nat.le_trans (Nat.add_le_add_right hC2 _) (Nat.le_of_eq ?_))
      have e1 : (st.length + 1) * Rfib * (2 * (cardD * Spec.roCoinPow cardD K)) =
          2 * (st.length + 1) * (Rfib * (cardD * Spec.roCoinPow cardD K)) := by
        simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      have e2 : cardD * (capBudget (st.length + 1) K * (Rfib * Spec.roCoinPow cardD K)) =
          capBudget (st.length + 1) K * (Rfib * (cardD * Spec.roCoinPow cardD K)) := by
        simp only [Nat.mul_left_comm]
      rw [e1, e2, ← capBudget_step st.length K,
        Nat.add_mul (2 * (st.length + 1)) (capBudget (st.length + 1) K)]

/-- The game whose winning coins are those on which a capacity event is recorded. -/
def spongeCapBadGame {Dom R σ κ : Type} [DecidableEq Dom] [DecidableEq κ] {cardD : Nat}
    (hCard : 0 < cardD) (capOf : σ → κ) (dec : Fin cardD → σ) (s0 : σ)
    (c : Spec.Code (Spec.roOracleIface Dom cardD) R) (K : Nat) :
    Spec.FinGame (Spec.roCoinPow cardD K) where
  samplePos := Spec.roCoinPow_pos hCard K
  win ω := capTableBad capOf dec s0 (spongeLazyRun c K [] ω).2

/-- **`Pr[capacity event] ≤ K (K + 1) · R / (2 · cardD)`** for every adaptive program making at
    most `K` calls to a lazily sampled function, when every capacity value has at most `R`
    preimages among the `cardD` states. -/
theorem sponge_cap_bad_bound {Dom R σ κ : Type} [DecidableEq Dom] [DecidableEq κ]
    {cardD Rfib : Nat} (hCard : 0 < cardD) (capOf : σ → κ) (dec : Fin cardD → σ) (s0 : σ)
    (hFib : ∀ c : κ, Spec.sampleSum cardD (fun d => if capOf (dec d) = c then 1 else 0) ≤ Rfib)
    (c : Spec.Code (Spec.roOracleIface Dom cardD) R) (K : Nat) :
    Spec.GameBound (spongeCapBadGame hCard capOf dec s0 c K).winProb
      ⟨K * (K + 1) * Rfib, 2 * cardD, Nat.mul_pos (by decide) hCard⟩ := by
  have h := spongeLazyRun_cap_bad_bound capOf dec s0 hFib c K [] rfl
  show Spec.sampleSum (Spec.roCoinPow cardD K)
      (fun ω => if capTableBad capOf dec s0 (spongeLazyRun c K [] ω).2 = true then 1 else 0) *
      (2 * cardD) ≤ K * (K + 1) * Rfib * Spec.roCoinPow cardD K
  refine Nat.le_trans h (Nat.le_of_eq ?_)
  show K * (2 * 0 + K + 1) * (Rfib * Spec.roCoinPow cardD K) =
    K * (K + 1) * Rfib * Spec.roCoinPow cardD K
  rw [Nat.mul_zero, Nat.zero_add]
  simp only [Nat.mul_assoc]

/-! ## §6. Real and ideal worlds agree until a capacity event -/

/-- Sponge-level interface: a block path is answered by the rate part of the state at its node. -/
@[expose, reducible] def spongeNodeIface (β ρ : Type) : Spec.Iface where
  Query := List β
  Resp _ := ρ

/-- Real world: walk the remaining blocks through the transformation, one call per block. -/
def spongeWalkReal {σ β R : Type} {cardD : Nat} (dec : Fin cardD → σ) (xorBlk : σ → β → σ) :
    σ → List β → (σ → Spec.Code (Spec.roOracleIface σ cardD) R) →
      Spec.Code (Spec.roOracleIface σ cardD) R
  | s, [], k => k s
  | s, b :: rest, k =>
    Spec.Code.call (E := Spec.roOracleIface σ cardD) (xorBlk s b)
      (fun d => spongeWalkReal dec xorBlk (dec d) rest k)

/-- Ideal world: one call per node of the path, keyed by the reversed path itself. -/
def spongeWalkIdeal {σ β R : Type} {cardD : Nat} (dec : Fin cardD → σ) :
    List β → σ → List β → (σ → Spec.Code (Spec.roOracleIface (List β) cardD) R) →
      Spec.Code (Spec.roOracleIface (List β) cardD) R
  | _, s, [], k => k s
  | p, _, b :: rest, k =>
    Spec.Code.call (E := Spec.roOracleIface (List β) cardD) (b :: p)
      (fun d => spongeWalkIdeal dec (b :: p) (dec d) rest k)

/-- The sponge over a lazily sampled transformation: a path of valid blocks is answered by the
    rate part of the state reached by absorbing it from `s0`; any other path by `rate s0`. -/
def spongeRealWorld {σ β ρ R : Type} {cardD : Nat} (dec : Fin cardD → σ) (xorBlk : σ → β → σ)
    (rate : σ → ρ) (s0 : σ) (validB : β → Bool) :
    Spec.Code (spongeNodeIface β ρ) R → Spec.Code (Spec.roOracleIface σ cardD) R
  | .ret v => .ret v
  | .call w k =>
    if w.all validB = true then
      spongeWalkReal dec xorBlk s0 w
        (fun s => spongeRealWorld dec xorBlk rate s0 validB (k (rate s)))
    else spongeRealWorld dec xorBlk rate s0 validB (k (rate s0))

/-- A lazily sampled function on block paths: a path of valid blocks is answered by the rate
    part of the draw recorded for that path (its proper prefixes are drawn too, keeping the coin
    positions of the real world); any other path by `rate s0`. -/
def spongeIdealWorld {σ β ρ R : Type} {cardD : Nat} (dec : Fin cardD → σ)
    (rate : σ → ρ) (s0 : σ) (validB : β → Bool) :
    Spec.Code (spongeNodeIface β ρ) R → Spec.Code (Spec.roOracleIface (List β) cardD) R
  | .ret v => .ret v
  | .call w k =>
    if w.all validB = true then
      spongeWalkIdeal dec [] s0 w
        (fun s => spongeIdealWorld dec rate s0 validB (k (rate s)))
    else spongeIdealWorld dec rate s0 validB (k (rate s0))

/-- State the ideal table assigns to a reversed path. -/
def idealStateOf {σ β : Type} [DecidableEq β] {cardD : Nat} (dec : Fin cardD → σ) (s0 : σ)
    (tI : List (List β × Fin cardD)) : List β → σ
  | [] => s0
  | b :: r =>
    match spongeLookup tI (b :: r) with
    | some d => dec d
    | none => s0

/-- The transformation input the real world uses at the node of a reversed path. -/
def idealNodeIn {σ β : Type} [DecidableEq β] {cardD : Nat} (dec : Fin cardD → σ)
    (xorBlk : σ → β → σ) (s0 : σ) (tI : List (List β × Fin cardD)) : List β → σ
  | [] => s0
  | b :: r => xorBlk (idealStateOf dec s0 tI r) b

/-- The reversed path is the root or has a recorded draw. -/
def idealHas {β : Type} [DecidableEq β] {cardD : Nat} (tI : List (List β × Fin cardD))
    (p : List β) : Prop :=
  p = [] ∨ ∃ d, spongeLookup tI p = some d

/-- Coupling invariant: the real table is the ideal table with every path replaced by its
    transformation input, and the ideal table is closed under parents. -/
structure SpongeCoupled {σ β : Type} [DecidableEq β] {cardD : Nat} (dec : Fin cardD → σ)
    (xorBlk : σ → β → σ) (s0 : σ) (validB : β → Bool) (tR : List (σ × Fin cardD))
    (tI : List (List β × Fin cardD)) : Prop where
  map_eq : tR = tI.map (fun e => (idealNodeIn dec xorBlk s0 tI e.1, e.2))
  keys : ∀ e, e ∈ tI → ∃ b r, e.1 = b :: r ∧ validB b = true ∧ idealHas tI r

private theorem sds_if_pos.{u} {α : Sort u} {p : Prop} [Decidable p] (hp : p) {a b : α} :
    (if p then a else b) = a := by
  cases ‹Decidable p› with
  | isTrue _ => rfl
  | isFalse hn => exact False.elim (hn hp)

private theorem sds_if_neg.{u} {α : Sort u} {p : Prop} [Decidable p] (hnp : ¬ p) {a b : α} :
    (if p then a else b) = b := by
  cases ‹Decidable p› with
  | isTrue hp => exact False.elim (hnp hp)
  | isFalse _ => rfl

private theorem spongeLookup_mem {Dom V : Type} [DecidableEq Dom] :
    ∀ (t : List (Dom × V)) (q : Dom) (v : V), spongeLookup t q = some v → (q, v) ∈ t
  | [], _, _, h => by cases h
  | e :: rest, q, v, h => by
    unfold spongeLookup at h
    by_cases hq : q = e.1
    · rw [sds_if_pos hq] at h
      have hv : e.2 = v := Option.some.inj h
      have he : e = (q, v) := by rw [hq, ← hv]
      rw [he]
      exact List.mem_cons_self
    · rw [sds_if_neg hq] at h
      exact List.mem_cons_of_mem _ (spongeLookup_mem rest q v h)

private theorem spongeLookup_map_inj {A B V : Type} [DecidableEq A] [DecidableEq B] (g : A → B)
    (q : A) :
    ∀ (t : List (A × V)), (∀ e, e ∈ t → g e.1 = g q → e.1 = q) →
      spongeLookup (t.map (fun e => (g e.1, e.2))) (g q) = spongeLookup t q
  | [], _ => rfl
  | e :: rest, h => by
    have ih := spongeLookup_map_inj g q rest (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    show (if g q = g e.1 then some e.2 else
        spongeLookup (rest.map (fun e => (g e.1, e.2))) (g q)) =
      (if q = e.1 then some e.2 else spongeLookup rest q)
    by_cases hq : q = e.1
    · rw [sds_if_pos hq, sds_if_pos (congrArg g hq)]
    · have hg : ¬ g q = g e.1 := fun hEq => hq (h e List.mem_cons_self hEq.symm).symm
      rw [sds_if_neg hq, sds_if_neg hg, ih]

private theorem any_false_of_mem {α : Type} {l : List α} {p : α → Bool} (h : l.any p = false)
    {x : α} (hx : x ∈ l) : p x = false := by
  cases hp : p x with
  | false => rfl
  | true =>
    have hT : l.any p = true := List.any_eq_true.mpr ⟨x, hx, hp⟩
    rw [h] at hT
    cases hT

private theorem bool_or_false_split {a b : Bool} (h : (a || b) = false) :
    a = false ∧ b = false := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | cases h

section CouplingLemmas

variable {σ κ β : Type} [DecidableEq κ] {cardD : Nat}
  (capOf : σ → κ) (dec : Fin cardD → σ) (s0 : σ)

/-- With no capacity event recorded, a recorded draw never has the initial capacity. -/
private theorem capTable_ne_init {Dom : Type} [DecidableEq Dom] :
    ∀ (t : List (Dom × Fin cardD)), capTableBad capOf dec s0 t = false →
      ∀ (p : Dom) (d : Fin cardD), spongeLookup t p = some d → capOf (dec d) ≠ capOf s0
  | [], _, _, _, h => by cases h
  | e :: rest, hBad, p, d, h => by
    have hSplit := bool_or_false_split (a := capOutBad capOf dec s0 (rest.map Prod.snd) e.2)
      (b := capOutsBad capOf dec s0 (rest.map Prod.snd)) hBad
    unfold spongeLookup at h
    by_cases hq : p = e.1
    · rw [sds_if_pos hq] at h
      have hd : e.2 = d := Option.some.inj h
      have h1 := (bool_or_false_split (a := decide (capOf (dec e.2) = capOf s0)) hSplit.1).1
      rw [hd] at h1
      exact of_decide_eq_false h1
    · rw [sds_if_neg hq] at h
      exact capTable_ne_init rest hSplit.2 p d h

/-- With no capacity event recorded, the capacity of a recorded draw determines its key. -/
private theorem capTable_key_inj {Dom : Type} [DecidableEq Dom] :
    ∀ (t : List (Dom × Fin cardD)), capTableBad capOf dec s0 t = false →
      ∀ (p p' : Dom) (d d' : Fin cardD), spongeLookup t p = some d →
        spongeLookup t p' = some d' → capOf (dec d) = capOf (dec d') → p = p'
  | [], _, _, _, _, _, h, _, _ => by cases h
  | e :: rest, hBad, p, p', d, d', h, h', hCap => by
    have hSplit := bool_or_false_split (a := capOutBad capOf dec s0 (rest.map Prod.snd) e.2)
      (b := capOutsBad capOf dec s0 (rest.map Prod.snd)) hBad
    have hAny := (bool_or_false_split (a := decide (capOf (dec e.2) = capOf s0)) hSplit.1).2
    have hOld : ∀ (q : Dom) (x : Fin cardD), spongeLookup rest q = some x →
        capOf (dec e.2) ≠ capOf (dec x) := by
      intro q x hx
      have hMem : x ∈ rest.map Prod.snd :=
        List.mem_map.mpr ⟨(q, x), spongeLookup_mem rest q x hx, rfl⟩
      exact of_decide_eq_false (any_false_of_mem hAny hMem)
    unfold spongeLookup at h h'
    by_cases hq : p = e.1
    · by_cases hq' : p' = e.1
      · rw [hq, hq']
      · rw [sds_if_pos hq] at h
        rw [sds_if_neg hq'] at h'
        have hd : e.2 = d := Option.some.inj h
        rw [← hd] at hCap
        exact absurd hCap (hOld p' d' h')
    · by_cases hq' : p' = e.1
      · rw [sds_if_neg hq] at h
        rw [sds_if_pos hq'] at h'
        have hd : e.2 = d' := Option.some.inj h'
        rw [← hd] at hCap
        exact absurd hCap.symm (hOld p d h)
      · rw [sds_if_neg hq] at h
        rw [sds_if_neg hq'] at h'
        exact capTable_key_inj rest hSplit.2 p p' d d' h h' hCap

variable [DecidableEq β]

private theorem idealStateOf_of_lookup (tI : List (List β × Fin cardD)) (b : β) (r : List β)
    (d : Fin cardD) (h : spongeLookup tI (b :: r) = some d) :
    idealStateOf dec s0 tI (b :: r) = dec d := by
  show (match spongeLookup tI (b :: r) with | some d => dec d | none => s0) = dec d
  rw [h]

/-- With no capacity event recorded, the capacity of the state at a recorded node determines
    the node. -/
private theorem idealState_cap_inj (tI : List (List β × Fin cardD))
    (hBad : capTableBad capOf dec s0 tI = false) :
    ∀ (r r' : List β), idealHas tI r → idealHas tI r' →
      capOf (idealStateOf dec s0 tI r) = capOf (idealStateOf dec s0 tI r') → r = r'
  | [], [], _, _, _ => rfl
  | [], c :: t, _, h', hCap => by
    rcases h' with hNil | ⟨d, hd⟩
    · cases hNil
    · rw [idealStateOf_of_lookup dec s0 tI c t d hd] at hCap
      exact absurd hCap.symm (capTable_ne_init capOf dec s0 tI hBad (c :: t) d hd)
  | c :: t, [], h, _, hCap => by
    rcases h with hNil | ⟨d, hd⟩
    · cases hNil
    · rw [idealStateOf_of_lookup dec s0 tI c t d hd] at hCap
      exact absurd hCap (capTable_ne_init capOf dec s0 tI hBad (c :: t) d hd)
  | c :: t, c' :: t', h, h', hCap => by
    rcases h with hNil | ⟨d, hd⟩
    · cases hNil
    · rcases h' with hNil' | ⟨d', hd'⟩
      · cases hNil'
      · rw [idealStateOf_of_lookup dec s0 tI c t d hd,
          idealStateOf_of_lookup dec s0 tI c' t' d' hd'] at hCap
        exact capTable_key_inj capOf dec s0 tI hBad (c :: t) (c' :: t') d d' hd hd' hCap

end CouplingLemmas

section Coupling

variable {σ κ β : Type} [DecidableEq σ] [DecidableEq κ] [DecidableEq β] {cardD : Nat}
  {capOf : σ → κ} {xorBlk : σ → β → σ} {validB : β → Bool}

omit [DecidableEq σ] in
private theorem capTableBad_coupled (dec : Fin cardD → σ) (s0 : σ)
    {tR : List (σ × Fin cardD)} {tI : List (List β × Fin cardD)}
    (hC : SpongeCoupled dec xorBlk s0 validB tR tI) :
    capTableBad capOf dec s0 tR = capTableBad capOf dec s0 tI := by
  unfold capTableBad
  rw [hC.map_eq, List.map_map]
  rfl

private theorem coupled_lookup_eq (hL : SpongeCapLaws capOf xorBlk (fun b => validB b = true))
    (dec : Fin cardD → σ) (s0 : σ)
    {tR : List (σ × Fin cardD)} {tI : List (List β × Fin cardD)}
    (hC : SpongeCoupled dec xorBlk s0 validB tR tI)
    (hBad : capTableBad capOf dec s0 tI = false) (p : List β) (hp : idealHas tI p) (b : β)
    (hb : validB b = true) :
    spongeLookup tR (xorBlk (idealStateOf dec s0 tI p) b) = spongeLookup tI (b :: p) := by
  rw [hC.map_eq]
  refine spongeLookup_map_inj (idealNodeIn dec xorBlk s0 tI) (b :: p) tI ?_
  intro e he hEq
  obtain ⟨b', r', hKey, hb', hr'⟩ := hC.keys e he
  rw [hKey] at hEq ⊢
  have hEq' : xorBlk (idealStateOf dec s0 tI r') b' = xorBlk (idealStateOf dec s0 tI p) b := hEq
  have hCap : capOf (idealStateOf dec s0 tI r') = capOf (idealStateOf dec s0 tI p) := by
    rw [← hL.cap_xor _ b' hb', ← hL.cap_xor (idealStateOf dec s0 tI p) b hb, hEq']
  have hr : r' = p := idealState_cap_inj capOf dec s0 tI hBad r' p hr' hp hCap
  subst hr
  rw [hL.xor_inj _ b' b hb' hb hEq']

omit [DecidableEq σ] in
private theorem idealStateOf_cons_table (dec : Fin cardD → σ) (s0 : σ)
    (tI : List (List β × Fin cardD)) (b : β) (p : List β) (d : Fin cardD)
    (hNone : spongeLookup tI (b :: p) = none) (r : List β) (hr : idealHas tI r) :
    idealStateOf dec s0 ((b :: p, d) :: tI) r = idealStateOf dec s0 tI r := by
  cases r with
  | nil => rfl
  | cons c t =>
    rcases hr with hNil | ⟨x, hx⟩
    · cases hNil
    · have hNe : ¬ (c :: t = b :: p) := fun hEq => by
        rw [hEq, hNone] at hx; cases hx
      have hLk : spongeLookup ((b :: p, d) :: tI) (c :: t) = spongeLookup tI (c :: t) := by
        show (if c :: t = b :: p then some d else spongeLookup tI (c :: t)) = _
        rw [sds_if_neg hNe]
      show (match spongeLookup ((b :: p, d) :: tI) (c :: t) with
        | some d => dec d | none => s0) = _
      rw [hLk]
      rfl

private theorem idealHas_cons_table (tI : List (List β × Fin cardD)) (key : List β)
    (d : Fin cardD) (r : List β) (hr : idealHas tI r) : idealHas ((key, d) :: tI) r := by
  rcases hr with hNil | ⟨x, hx⟩
  · exact .inl hNil
  · refine .inr ?_
    show ∃ d', (if r = key then some d else spongeLookup tI r) = some d'
    by_cases h : r = key
    · exact ⟨d, by rw [sds_if_pos h]⟩
    · exact ⟨x, by rw [sds_if_neg h]; exact hx⟩

omit [DecidableEq σ] in
private theorem coupled_extend (dec : Fin cardD → σ) (s0 : σ)
    {tR : List (σ × Fin cardD)} {tI : List (List β × Fin cardD)}
    (hC : SpongeCoupled dec xorBlk s0 validB tR tI) (p : List β) (hp : idealHas tI p) (b : β)
    (hb : validB b = true) (d : Fin cardD) (hNone : spongeLookup tI (b :: p) = none) :
    SpongeCoupled dec xorBlk s0 validB ((xorBlk (idealStateOf dec s0 tI p) b, d) :: tR)
      ((b :: p, d) :: tI) where
  map_eq := by
    have hHead : idealNodeIn dec xorBlk s0 ((b :: p, d) :: tI) (b :: p) =
        xorBlk (idealStateOf dec s0 tI p) b := by
      show xorBlk (idealStateOf dec s0 ((b :: p, d) :: tI) p) b = _
      rw [idealStateOf_cons_table dec s0 tI b p d hNone p hp]
    have hTail : tI.map (fun e => (idealNodeIn dec xorBlk s0 ((b :: p, d) :: tI) e.1, e.2)) =
        tI.map (fun e => (idealNodeIn dec xorBlk s0 tI e.1, e.2)) := by
      apply List.map_congr_left
      intro e he
      obtain ⟨b', r', hKey, _, hr'⟩ := hC.keys e he
      rw [hKey]
      show (xorBlk (idealStateOf dec s0 ((b :: p, d) :: tI) r') b', e.2) =
        (xorBlk (idealStateOf dec s0 tI r') b', e.2)
      rw [idealStateOf_cons_table dec s0 tI b p d hNone r' hr']
    show _ = (idealNodeIn dec xorBlk s0 ((b :: p, d) :: tI) (b :: p), d) ::
      tI.map (fun e => (idealNodeIn dec xorBlk s0 ((b :: p, d) :: tI) e.1, e.2))
    rw [hHead, hTail, ← hC.map_eq]
  keys := by
    intro e he
    rcases List.mem_cons.mp he with hNew | hOld
    · rw [hNew]
      exact ⟨b, p, rfl, hb, idealHas_cons_table tI (b :: p) d p hp⟩
    · obtain ⟨b', r', hKey, hb', hr'⟩ := hC.keys e hOld
      exact ⟨b', r', hKey, hb', idealHas_cons_table tI (b :: p) d r' hr'⟩

omit [DecidableEq σ] in
/-- A recorded capacity event stays recorded: tables only grow. -/
theorem capTableBad_run_mono {Dom R : Type} [DecidableEq Dom] (capOf : σ → κ)
    (dec : Fin cardD → σ) (s0 : σ) :
    ∀ (c : Spec.Code (Spec.roOracleIface Dom cardD) R) (K : Nat) (st : List (Dom × Fin cardD))
      (ω : Fin (Spec.roCoinPow cardD K)), capTableBad capOf dec s0 st = true →
      capTableBad capOf dec s0 (spongeLazyRun c K st ω).2 = true
  | .ret v, K, st, ω, h => by rw [spongeLazyRun_ret]; exact h
  | .call q next, 0, st, ω, h => by rw [spongeLazyRun_call_zero]; exact h
  | .call q next, K + 1, st, ω, h => by
    cases hLook : spongeLookup st q with
    | some y =>
      rw [spongeLazyRun_call_hit q next K st ω y hLook]
      exact capTableBad_run_mono capOf dec s0 (next y) K st _ h
    | none =>
      rw [spongeLazyRun_call_miss q next K st ω hLook]
      refine capTableBad_run_mono capOf dec s0 (next _) K _ _ ?_
      show (capOutBad capOf dec s0 (st.map Prod.snd) _ ||
        capOutsBad capOf dec s0 (st.map Prod.snd)) = true
      rw [show capOutsBad capOf dec s0 (st.map Prod.snd) = true from h, Bool.or_true]

private theorem spongeWalk_coupled (hL : SpongeCapLaws capOf xorBlk (fun b => validB b = true))
    (dec : Fin cardD → σ) (s0 : σ) {R : Type}
    (kR : σ → Spec.Code (Spec.roOracleIface σ cardD) R)
    (kI : σ → Spec.Code (Spec.roOracleIface (List β) cardD) R)
    (hCont : ∀ (s : σ) (K : Nat) (tR : List (σ × Fin cardD)) (tI : List (List β × Fin cardD))
        (ω : Fin (Spec.roCoinPow cardD K)), SpongeCoupled dec xorBlk s0 validB tR tI →
        capTableBad capOf dec s0 (spongeLazyRun (kR s) K tR ω).2 = false →
        (spongeLazyRun (kR s) K tR ω).1 = (spongeLazyRun (kI s) K tI ω).1) :
    ∀ (rest p : List β) (K : Nat) (tR : List (σ × Fin cardD)) (tI : List (List β × Fin cardD))
      (ω : Fin (Spec.roCoinPow cardD K)),
      SpongeCoupled dec xorBlk s0 validB tR tI → idealHas tI p →
      (∀ b, b ∈ rest → validB b = true) →
      capTableBad capOf dec s0
        (spongeLazyRun (spongeWalkReal dec xorBlk (idealStateOf dec s0 tI p) rest kR)
          K tR ω).2 = false →
      (spongeLazyRun (spongeWalkReal dec xorBlk (idealStateOf dec s0 tI p) rest kR) K tR ω).1 =
        (spongeLazyRun (spongeWalkIdeal dec p (idealStateOf dec s0 tI p) rest kI) K tI ω).1
  | [], _, K, tR, tI, ω, hC, _, _, hF => hCont _ K tR tI ω hC hF
  | b :: rest, p, 0, tR, tI, ω, _, _, _, _ => by
    show (spongeLazyRun (Spec.Code.call _ _) 0 tR ω).1 =
      (spongeLazyRun (Spec.Code.call _ _) 0 tI ω).1
    rw [spongeLazyRun_call_zero, spongeLazyRun_call_zero]
  | b :: rest, p, K + 1, tR, tI, ω, hC, hp, hV, hF => by
    have hb : validB b = true := hV b List.mem_cons_self
    have hVrest : ∀ c, c ∈ rest → validB c = true :=
      fun c hc => hV c (List.mem_cons_of_mem _ hc)
    have hBadR : capTableBad capOf dec s0 tR = false := by
      cases hB : capTableBad capOf dec s0 tR with
      | false => rfl
      | true =>
        have hT := capTableBad_run_mono capOf dec s0
          (spongeWalkReal dec xorBlk (idealStateOf dec s0 tI p) (b :: rest) kR) (K + 1) tR ω hB
        rw [hF] at hT
        cases hT
    have hBadI : capTableBad capOf dec s0 tI = false := by
      rw [← capTableBad_coupled dec s0 hC]; exact hBadR
    have hLk := coupled_lookup_eq hL dec s0 hC hBadI p hp b hb
    cases hI : spongeLookup tI (b :: p) with
    | some y =>
      have hRunR : spongeLazyRun
            (spongeWalkReal dec xorBlk (idealStateOf dec s0 tI p) (b :: rest) kR) (K + 1) tR ω =
          spongeLazyRun (spongeWalkReal dec xorBlk (dec y) rest kR) K tR
            (spongeCoinTail (a := cardD) ω) :=
        spongeLazyRun_call_hit _ _ K tR ω y (hLk.trans hI)
      have hRunI : spongeLazyRun
            (spongeWalkIdeal dec p (idealStateOf dec s0 tI p) (b :: rest) kI) (K + 1) tI ω =
          spongeLazyRun (spongeWalkIdeal dec (b :: p) (dec y) rest kI) K tI
            (spongeCoinTail (a := cardD) ω) :=
        spongeLazyRun_call_hit _ _ K tI ω y hI
      have hState : dec y = idealStateOf dec s0 tI (b :: p) :=
        (idealStateOf_of_lookup dec s0 tI b p y hI).symm
      rw [hRunR] at hF ⊢
      rw [hRunI]
      rw [hState] at hF ⊢
      exact spongeWalk_coupled hL dec s0 kR kI hCont rest (b :: p) K tR tI _ hC
        (.inr ⟨y, hI⟩) hVrest hF
    | none =>
      have hRunR : spongeLazyRun
            (spongeWalkReal dec xorBlk (idealStateOf dec s0 tI p) (b :: rest) kR) (K + 1) tR ω =
          spongeLazyRun
            (spongeWalkReal dec xorBlk (dec (spongeCoinHead (b := Spec.roCoinPow cardD K) ω))
              rest kR) K
            ((xorBlk (idealStateOf dec s0 tI p) b,
              spongeCoinHead (b := Spec.roCoinPow cardD K) ω) :: tR)
            (spongeCoinTail (a := cardD) ω) :=
        spongeLazyRun_call_miss _ _ K tR ω (hLk.trans hI)
      have hRunI : spongeLazyRun
            (spongeWalkIdeal dec p (idealStateOf dec s0 tI p) (b :: rest) kI) (K + 1) tI ω =
          spongeLazyRun
            (spongeWalkIdeal dec (b :: p)
              (dec (spongeCoinHead (b := Spec.roCoinPow cardD K) ω)) rest kI) K
            ((b :: p, spongeCoinHead (b := Spec.roCoinPow cardD K) ω) :: tI)
            (spongeCoinTail (a := cardD) ω) :=
        spongeLazyRun_call_miss _ _ K tI ω hI
      have hC' := coupled_extend dec s0 hC p hp b hb
        (spongeCoinHead (b := Spec.roCoinPow cardD K) ω) hI
      have hLkNew : spongeLookup
          ((b :: p, spongeCoinHead (b := Spec.roCoinPow cardD K) ω) :: tI) (b :: p) =
          some (spongeCoinHead (b := Spec.roCoinPow cardD K) ω) := by
        show (if b :: p = b :: p then some _ else spongeLookup tI (b :: p)) = _
        rw [sds_if_pos rfl]
      have hState : dec (spongeCoinHead (b := Spec.roCoinPow cardD K) ω) =
          idealStateOf dec s0
            ((b :: p, spongeCoinHead (b := Spec.roCoinPow cardD K) ω) :: tI) (b :: p) :=
        (idealStateOf_of_lookup dec s0 _ b p _ hLkNew).symm
      rw [hRunR] at hF ⊢
      rw [hRunI]
      rw [hState] at hF ⊢
      exact spongeWalk_coupled hL dec s0 kR kI hCont rest (b :: p) K _ _ _ hC'
        (.inr ⟨_, hLkNew⟩) hVrest hF

/-- **Identical until a capacity event.** From coupled tables, on every coin on which the real
    run records no capacity event, the real and ideal worlds return the same result. -/
theorem spongeWorlds_agree_until_cap_bad
    (hL : SpongeCapLaws capOf xorBlk (fun b => validB b = true))
    (dec : Fin cardD → σ) (s0 : σ) {ρ R : Type} (rate : σ → ρ) :
    ∀ (A : Spec.Code (spongeNodeIface β ρ) R) (K : Nat) (tR : List (σ × Fin cardD))
      (tI : List (List β × Fin cardD)) (ω : Fin (Spec.roCoinPow cardD K)),
      SpongeCoupled dec xorBlk s0 validB tR tI →
      capTableBad capOf dec s0
        (spongeLazyRun (spongeRealWorld dec xorBlk rate s0 validB A) K tR ω).2 = false →
      (spongeLazyRun (spongeRealWorld dec xorBlk rate s0 validB A) K tR ω).1 =
        (spongeLazyRun (spongeIdealWorld dec rate s0 validB A) K tI ω).1 := by
  intro A
  induction A with
  | ret v =>
    intro K tR tI ω _ _
    show (spongeLazyRun (Spec.Code.ret v) K tR ω).1 = (spongeLazyRun (Spec.Code.ret v) K tI ω).1
    rw [spongeLazyRun_ret, spongeLazyRun_ret]
  | call w k ih =>
    intro K tR tI ω hC hF
    by_cases hv : List.all w validB = true
    · have hRW : spongeRealWorld dec xorBlk rate s0 validB (Spec.Code.call w k) =
          spongeWalkReal dec xorBlk s0 w
            (fun s => spongeRealWorld dec xorBlk rate s0 validB (k (rate s))) := by
        show (if List.all w validB = true then _ else _) = _
        rw [sds_if_pos hv]
      have hIW : spongeIdealWorld dec rate s0 validB (Spec.Code.call w k) =
          spongeWalkIdeal dec [] s0 w
            (fun s => spongeIdealWorld dec rate s0 validB (k (rate s))) := by
        show (if List.all w validB = true then _ else _) = _
        rw [sds_if_pos hv]
      rw [hRW] at hF ⊢
      rw [hIW]
      exact spongeWalk_coupled hL dec s0 _ _
        (fun s K tR tI ω hC hF => ih (rate s) K tR tI ω hC hF) w [] K tR tI ω hC (.inl rfl)
        (fun b hb => List.all_eq_true.mp hv b hb) hF
    · have hRW : spongeRealWorld dec xorBlk rate s0 validB (Spec.Code.call w k) =
          spongeRealWorld dec xorBlk rate s0 validB (k (rate s0)) := by
        show (if List.all w validB = true then _ else _) = _
        rw [sds_if_neg hv]
      have hIW : spongeIdealWorld dec rate s0 validB (Spec.Code.call w k) =
          spongeIdealWorld dec rate s0 validB (k (rate s0)) := by
        show (if List.all w validB = true then _ else _) = _
        rw [sds_if_neg hv]
      rw [hRW] at hF ⊢
      rw [hIW]
      exact ih (rate s0) K tR tI ω hC hF

end Coupling

/-! ### The two games and the advantage bound -/

/-- Real game: the adversary's verdict against the sponge over a lazily sampled transformation. -/
def spongeRealGame {σ β ρ : Type} [DecidableEq σ] {cardD : Nat} (hCard : 0 < cardD)
    (dec : Fin cardD → σ) (xorBlk : σ → β → σ) (rate : σ → ρ) (s0 : σ) (validB : β → Bool)
    (A : Spec.Code (spongeNodeIface β ρ) Bool) (K : Nat) :
    Spec.FinGame (Spec.roCoinPow cardD K) where
  samplePos := Spec.roCoinPow_pos hCard K
  win ω := (spongeLazyRun (spongeRealWorld dec xorBlk rate s0 validB A) K [] ω).1 == some true

/-- Ideal game: the adversary's verdict against a lazily sampled function on block paths. -/
def spongeIdealGame {σ β ρ : Type} [DecidableEq β] {cardD : Nat} (hCard : 0 < cardD)
    (dec : Fin cardD → σ) (rate : σ → ρ) (s0 : σ) (validB : β → Bool)
    (A : Spec.Code (spongeNodeIface β ρ) Bool) (K : Nat) :
    Spec.FinGame (Spec.roCoinPow cardD K) where
  samplePos := Spec.roCoinPow_pos hCard K
  win ω := (spongeLazyRun (spongeIdealWorld dec rate s0 validB A) K [] ω).1 == some true

section Games

variable {σ κ β ρ : Type} [DecidableEq σ] [DecidableEq κ] [DecidableEq β] {cardD : Nat}
  {capOf : σ → κ} {xorBlk : σ → β → σ} {validB : β → Bool}

/-- **Run-level equality.** On every coin on which the real run records no capacity event, the
    sponge over the lazily sampled transformation and the lazily sampled function on paths
    return the same result to the adversary. -/
theorem spongeReal_eq_ideal_of_no_cap_bad
    (hL : SpongeCapLaws capOf xorBlk (fun b => validB b = true))
    (dec : Fin cardD → σ) (s0 : σ) {R : Type} (rate : σ → ρ)
    (A : Spec.Code (spongeNodeIface β ρ) R) (K : Nat) (ω : Fin (Spec.roCoinPow cardD K))
    (hNoBad : capTableBad capOf dec s0
      (spongeLazyRun (spongeRealWorld dec xorBlk rate s0 validB A) K [] ω).2 = false) :
    (spongeLazyRun (spongeRealWorld dec xorBlk rate s0 validB A) K [] ω).1 =
      (spongeLazyRun (spongeIdealWorld dec rate s0 validB A) K [] ω).1 :=
  spongeWorlds_agree_until_cap_bad hL dec s0 rate A K [] [] ω
    ⟨rfl, fun _ he => by cases he⟩ hNoBad

/-- `AdvDist real ideal ≤ Pr[capacity event in the real run]`. -/
theorem sponge_real_ideal_adv_le_cap_bad (hCard : 0 < cardD)
    (hL : SpongeCapLaws capOf xorBlk (fun b => validB b = true))
    (dec : Fin cardD → σ) (s0 : σ) (rate : σ → ρ)
    (A : Spec.Code (spongeNodeIface β ρ) Bool) (K : Nat) :
    Spec.GameBound
      (Spec.AdvDist (spongeRealGame hCard dec xorBlk rate s0 validB A K)
        (spongeIdealGame hCard dec rate s0 validB A K))
      (spongeCapBadGame hCard capOf dec s0
        (spongeRealWorld dec xorBlk rate s0 validB A) K).winProb :=
  Spec.adv_until_bad (spongeRealGame hCard dec xorBlk rate s0 validB A K)
    (spongeIdealGame hCard dec rate s0 validB A K)
    (fun ω => capTableBad capOf dec s0
      (spongeLazyRun (spongeRealWorld dec xorBlk rate s0 validB A) K [] ω).2)
    (fun ω hBad => by
      show ((spongeLazyRun (spongeRealWorld dec xorBlk rate s0 validB A) K [] ω).1 == some true) =
        ((spongeLazyRun (spongeIdealWorld dec rate s0 validB A) K [] ω).1 == some true)
      rw [spongeReal_eq_ideal_of_no_cap_bad hL dec s0 rate A K ω hBad])

/-- **Sponge indistinguishability from a random function on block paths.** Every adaptive
    adversary whose run makes at most `K` calls to a lazily sampled transformation on `cardD`
    states distinguishes the sponge from a lazily sampled function on paths with advantage at
    most `K (K + 1) · R / (2 · cardD)`, where every capacity value has at most `R` preimages. -/
theorem sponge_multi_domain_ro_indistinguishability_bound {Rfib : Nat} (hCard : 0 < cardD)
    (hL : SpongeCapLaws capOf xorBlk (fun b => validB b = true))
    (dec : Fin cardD → σ) (s0 : σ)
    (hFib : ∀ c : κ, Spec.sampleSum cardD (fun d => if capOf (dec d) = c then 1 else 0) ≤ Rfib)
    (rate : σ → ρ) (A : Spec.Code (spongeNodeIface β ρ) Bool) (K : Nat) :
    Spec.GameBound
      (Spec.AdvDist (spongeRealGame hCard dec xorBlk rate s0 validB A K)
        (spongeIdealGame hCard dec rate s0 validB A K))
      ⟨K * (K + 1) * Rfib, 2 * cardD, Nat.mul_pos (by decide) hCard⟩ :=
  Spec.GameBound.trans (sponge_real_ideal_adv_le_cap_bad hCard hL dec s0 rate A K)
    (sponge_cap_bad_bound hCard capOf dec s0 hFib _ K)

end Games

/-! ### Tag-level adversaries: `cSHAKE256` customizations as domains -/

/-- Tag-level interface: `(S, m, j)` asks for output block `j` of `cSHAKE256` with empty
    function name and customization `S` on message `m`. -/
@[expose, reducible] def cshakeTagIface (ρ : Type) : Spec.Iface where
  Query := List UInt8 × List UInt8 × Nat
  Resp _ := ρ

/-- The block path addressed by a tag-level query. -/
def cshakeTagPath (q : List UInt8 × List UInt8 × Nat) : List (List UInt8) :=
  cshake256PaddedBlocks [] q.1 q.2.1 ++ List.replicate q.2.2 (List.replicate 136 0)

/-- A tag-level adversary as a block-path adversary. -/
def cshakeTagAdversary {ρ R : Type} :
    Spec.Code (cshakeTagIface ρ) R → Spec.Code (spongeNodeIface (List UInt8) ρ) R
  | .ret v => .ret v
  | .call q k =>
    Spec.Code.call (E := spongeNodeIface (List UInt8) ρ) (cshakeTagPath q)
      (fun r => cshakeTagAdversary (k r))

/-- Tag-level queries with customizations of `qsagSpongeTags` address pairwise different block
    paths: in the ideal world no two of them read the same draw. -/
theorem cshakeTagPath_injective_on_qsag_tags {q₁ q₂ : List UInt8 × List UInt8 × Nat}
    (h₁ : q₁.1 ∈ qsagSpongeTags) (h₂ : q₂.1 ∈ qsagSpongeTags)
    (h : cshakeTagPath q₁ = cshakeTagPath q₂) : q₁ = q₂ := by
  obtain ⟨_, hS, hm, hj⟩ := cshake256_output_path_injective
    (bitlen_lt_sp800_bound (by decide)) (qsagSpongeTags_short h₁)
    (bitlen_lt_sp800_bound (by decide)) (qsagSpongeTags_short h₂) h
  exact Prod.ext hS (Prod.ext hm hj)

/-- **Multi-tag form of the bound.** Every adaptive adversary that asks for output blocks of
    `cSHAKE256` under arbitrary customizations (the `QSAG.*` tags among them) distinguishes the
    sponge over a lazily sampled transformation from a lazily sampled function on block paths
    with advantage at most `K (K + 1) · R / (2 · cardD)`. -/
theorem qsag_tags_sponge_ro_indistinguishability_bound {σ κ ρ : Type} [DecidableEq σ]
    [DecidableEq κ] {cardD Rfib : Nat} {capOf : σ → κ} {xorBlk : σ → List UInt8 → σ}
    (hCard : 0 < cardD)
    (hL : SpongeCapLaws capOf xorBlk (fun b => (b.length == 136) = true))
    (dec : Fin cardD → σ) (s0 : σ)
    (hFib : ∀ c : κ, Spec.sampleSum cardD (fun d => if capOf (dec d) = c then 1 else 0) ≤ Rfib)
    (rate : σ → ρ) (A : Spec.Code (cshakeTagIface ρ) Bool) (K : Nat) :
    Spec.GameBound
      (Spec.AdvDist
        (spongeRealGame hCard dec xorBlk rate s0 (fun b => b.length == 136)
          (cshakeTagAdversary A) K)
        (spongeIdealGame hCard dec rate s0 (fun b => b.length == 136)
          (cshakeTagAdversary A) K))
      ⟨K * (K + 1) * Rfib, 2 * cardD, Nat.mul_pos (by decide) hCard⟩ :=
  sponge_multi_domain_ro_indistinguishability_bound hCard hL dec s0 hFib rate
    (cshakeTagAdversary A) K

/-! ### Product-coded state spaces: `cardD = R · C`, bound `K (K + 1) / (2 C)` -/

private theorem sds_sum_indicator_le_one :
    ∀ (m : Nat) (P : Fin m → Prop) [DecidablePred P], (∀ i j, P i → P j → i = j) →
      Spec.sampleSum m (fun i => if P i then 1 else 0) ≤ 1
  | 0, _, _, _ => Nat.zero_le 1
  | m + 1, P, _, hU => by
    rw [Spec.sampleSum_succ]
    by_cases h0 : P ⟨0, Nat.zero_lt_succ m⟩
    · have hRest : (fun i : Fin m => if P ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ then 1 else 0) =
          (fun _ => 0) := by
        funext i
        have hNot : ¬ P ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ := fun hi =>
          absurd (congrArg Fin.val (hU _ _ hi h0)) (Nat.succ_ne_zero i.1)
        rw [sds_if_neg hNot]
      rw [hRest, sds_sum_const, Nat.mul_zero, sds_if_pos h0]
      exact Nat.le_refl 1
    · rw [sds_if_neg h0, Nat.zero_add]
      exact sds_sum_indicator_le_one m (fun i => P ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
        (fun i j hi hj => Fin.ext (Nat.succ.inj (congrArg Fin.val (hU _ _ hi hj))))

/-- If the capacity of the state coded by `i * C + j` is an injective function of `j`, every
    capacity value has at most `R` preimages among the `R * C` codes. -/
theorem sponge_fiber_count_of_product_coding {σ κ : Type} [DecidableEq κ] {R C : Nat}
    (capOf : σ → κ) (dec : Fin (R * C) → σ) (capIdx : Fin C → κ)
    (hInj : ∀ i j, capIdx i = capIdx j → i = j)
    (hDec : ∀ (i : Fin R) (j : Fin C),
      capOf (dec ⟨i.1 * C + j.1, Spec.prodCoin_pair_lt i j⟩) = capIdx j) (c : κ) :
    Spec.sampleSum (R * C) (fun d => if capOf (dec d) = c then 1 else 0) ≤ R := by
  rw [sds_sum_prod R C]
  have hPt : ∀ i : Fin R, Spec.sampleSum C (fun j =>
      if capOf (dec ⟨i.1 * C + j.1, Spec.prodCoin_pair_lt i j⟩) = c then 1 else 0) ≤ 1 := by
    intro i
    have hEq : (fun j : Fin C =>
        if capOf (dec ⟨i.1 * C + j.1, Spec.prodCoin_pair_lt i j⟩) = c then 1 else 0) =
        (fun j => if capIdx j = c then 1 else 0) := by
      funext j; rw [hDec i j]
    rw [hEq]
    exact sds_sum_indicator_le_one C (fun j => capIdx j = c)
      (fun i j hi hj => hInj i j (hi.trans hj.symm))
  have h := sds_sum_le R _ (fun _ => 1) hPt
  rw [sds_sum_const, Nat.mul_one] at h
  exact h

private theorem sds_bound_rescale (a R C : Nat) : a * R * (2 * C) = a * (2 * (R * C)) := by
  simp only [Nat.mul_assoc, Nat.mul_left_comm]

/-- Product state space `BitVec n × Fin C` coded by `Fin (2 ^ n * C)`. -/
def rateCapDec (n C : Nat) (ω : Fin (2 ^ n * C)) : BitVec n × Fin C :=
  (BitVec.ofFin (spongeCoinHead ω), spongeCoinTail ω)

private theorem rateCapXor_laws_bool {n : Nat} {κ : Type} :
    SpongeCapLaws (σ := BitVec n × κ) (β := BitVec n) Prod.snd rateCapXor
      (fun b => (fun _ : BitVec n => true) b = true) where
  cap_xor _ _ _ := rfl
  xor_inj s b₁ b₂ _ _ h := rateCapXor_laws.xor_inj s b₁ b₂ True.intro True.intro h

/-- **`AdvDist ≤ K (K + 1) / (2 C)` for the rate/capacity product sponge.** State space
    `BitVec n × Fin C`, XOR absorption on the rate, any rate read-out, any initial state, any
    adaptive adversary, at most `K` transformation calls. No hypothesis is left. -/
theorem rateCap_sponge_ro_indistinguishability_bound (n C : Nat) (hC : 0 < C) {ρ : Type}
    (rate : BitVec n × Fin C → ρ) (s0 : BitVec n × Fin C)
    (A : Spec.Code (spongeNodeIface (BitVec n) ρ) Bool) (K : Nat) :
    Spec.GameBound
      (Spec.AdvDist
        (spongeRealGame (Nat.mul_pos (Nat.two_pow_pos n) hC) (rateCapDec n C) rateCapXor rate s0
          (fun _ => true) A K)
        (spongeIdealGame (Nat.mul_pos (Nat.two_pow_pos n) hC) (rateCapDec n C) rate s0
          (fun _ => true) A K))
      ⟨K * (K + 1), 2 * C, Nat.mul_pos (by decide) hC⟩ := by
  have hFib := sponge_fiber_count_of_product_coding (R := 2 ^ n) (C := C)
    (Prod.snd : BitVec n × Fin C → Fin C) (rateCapDec n C) id (fun _ _ h => h)
    (fun i j => by
      show spongeCoinTail (⟨i.1 * C + j.1, Spec.prodCoin_pair_lt i j⟩ : Fin (2 ^ n * C)) = j
      exact spongeCoinTail_pair i j)
  have h := sponge_multi_domain_ro_indistinguishability_bound
    (Nat.mul_pos (Nat.two_pow_pos n) hC) rateCapXor_laws_bool (rateCapDec n C) s0 hFib rate A K
  refine Spec.GameBound.trans h ?_
  show K * (K + 1) * 2 ^ n * (2 * C) ≤ K * (K + 1) * (2 * (2 ^ n * C))
  exact Nat.le_of_eq (sds_bound_rescale _ _ _)

set_option exponentiation.threshold 2048 in
/-- At a 512-bit capacity and at most `2^40` transformation calls the bound is below
    `2^-430`. -/
theorem sponge_ro_bound_430_bits_at_c512_q2pow40 (n : Nat) {ρ : Type}
    (rate : BitVec n × Fin (2 ^ 512) → ρ) (s0 : BitVec n × Fin (2 ^ 512))
    (A : Spec.Code (spongeNodeIface (BitVec n) ρ) Bool) (K : Nat) (hK : K ≤ 2 ^ 40) :
    (Spec.AdvDist
      (spongeRealGame (Nat.mul_pos (Nat.two_pow_pos n) (Nat.two_pow_pos 512))
        (rateCapDec n (2 ^ 512)) rateCapXor rate s0 (fun _ => true) A K)
      (spongeIdealGame (Nat.mul_pos (Nat.two_pow_pos n) (Nat.two_pow_pos 512))
        (rateCapDec n (2 ^ 512)) rate s0 (fun _ => true) A K)).atLeastBits 430 := by
  refine Spec.GameBound.atLeastBits
    (rateCap_sponge_ro_indistinguishability_bound n (2 ^ 512) (Nat.two_pow_pos 512) rate s0 A K)
    ?_
  show K * (K + 1) * 2 ^ 430 ≤ 2 * 2 ^ 512
  have h1 : K * (K + 1) ≤ 2 ^ 40 * (2 ^ 40 + 1) := Nat.mul_le_mul hK (Nat.succ_le_succ hK)
  exact Nat.le_trans (Nat.mul_le_mul_right _ h1) (by decide +kernel)

/-! ### The `Keccak-f[1600]` state space: `2^1088 · 2^512` codes, 512-bit capacity -/

/-- Number of rate values of the Keccak state at rate 136: `2^1088`. -/
def keccakRateCard : Nat := 2 ^ 1088

/-- Number of capacity values of the Keccak state at rate 136: `2^512`. -/
def keccakCapCard : Nat := 2 ^ 512

set_option exponentiation.threshold 2048 in
theorem keccakRateCard_eq : keccakRateCard = 2 ^ 1088 := by rfl

set_option exponentiation.threshold 2048 in
theorem keccakCapCard_eq : keccakCapCard = 2 ^ 512 := by rfl

set_option exponentiation.threshold 2048 in
theorem keccakStateCard_pos : 0 < keccakRateCard * keccakCapCard := by
  rw [keccakRateCard_eq, keccakCapCard_eq]
  exact Nat.mul_pos (Nat.two_pow_pos 1088) (Nat.two_pow_pos 512)

/-- The 64-bit lane of `x` at bit offset `e`. -/
def keccakLaneOf (x e : Nat) : UInt64 := UInt64.ofNat (x / 2 ^ e)

/-- Decode a draw of `Fin (keccakRateCard * keccakCapCard)` to a Keccak state by base-`2^64` digits: the
    quotient gives the 17 rate lanes `a0 … a16`, the remainder the 8 capacity lanes
    `a17 … a24`. -/
def keccakDec (ω : Fin (keccakRateCard * keccakCapCard)) : KState :=
  ⟨keccakLaneOf (spongeCoinHead ω).val 0, keccakLaneOf (spongeCoinHead ω).val 64, keccakLaneOf (spongeCoinHead ω).val 128, keccakLaneOf (spongeCoinHead ω).val 192, keccakLaneOf (spongeCoinHead ω).val 256, keccakLaneOf (spongeCoinHead ω).val 320, keccakLaneOf (spongeCoinHead ω).val 384, keccakLaneOf (spongeCoinHead ω).val 448,
    keccakLaneOf (spongeCoinHead ω).val 512, keccakLaneOf (spongeCoinHead ω).val 576, keccakLaneOf (spongeCoinHead ω).val 640, keccakLaneOf (spongeCoinHead ω).val 704, keccakLaneOf (spongeCoinHead ω).val 768, keccakLaneOf (spongeCoinHead ω).val 832, keccakLaneOf (spongeCoinHead ω).val 896, keccakLaneOf (spongeCoinHead ω).val 960, keccakLaneOf (spongeCoinHead ω).val 1024,
    keccakLaneOf (spongeCoinTail ω).val 0, keccakLaneOf (spongeCoinTail ω).val 64, keccakLaneOf (spongeCoinTail ω).val 128, keccakLaneOf (spongeCoinTail ω).val 192, keccakLaneOf (spongeCoinTail ω).val 256, keccakLaneOf (spongeCoinTail ω).val 320, keccakLaneOf (spongeCoinTail ω).val 384, keccakLaneOf (spongeCoinTail ω).val 448⟩

/-- The capacity lanes coded by a remainder `j < keccakCapCard`. -/
def keccakCapIdx (j : Fin keccakCapCard) : List UInt64 :=
  [keccakLaneOf j.val 0, keccakLaneOf j.val 64, keccakLaneOf j.val 128, keccakLaneOf j.val 192, keccakLaneOf j.val 256, keccakLaneOf j.val 320, keccakLaneOf j.val 384, keccakLaneOf j.val 448]

private theorem keccakLaneOf_toNat_eq {x y e : Nat} (h : keccakLaneOf x e = keccakLaneOf y e) :
    (x / 2 ^ e) % 2 ^ 64 = (y / 2 ^ e) % 2 ^ 64 := by
  have h2 : (UInt64.ofNat (x / 2 ^ e)).toNat = (UInt64.ofNat (y / 2 ^ e)).toNat :=
    congrArg UInt64.toNat h
  rw [UInt64.toNat_ofNat', UInt64.toNat_ofNat'] at h2
  exact h2

set_option exponentiation.threshold 2048 in
private theorem digits8_inj (i j : Nat) (hi : i < 2 ^ 512) (hj : j < 2 ^ 512)
    (h0 : (i / 2 ^ 0) % 2 ^ 64 = (j / 2 ^ 0) % 2 ^ 64)
    (h1 : (i / 2 ^ 64) % 2 ^ 64 = (j / 2 ^ 64) % 2 ^ 64)
    (h2 : (i / 2 ^ 128) % 2 ^ 64 = (j / 2 ^ 128) % 2 ^ 64)
    (h3 : (i / 2 ^ 192) % 2 ^ 64 = (j / 2 ^ 192) % 2 ^ 64)
    (h4 : (i / 2 ^ 256) % 2 ^ 64 = (j / 2 ^ 256) % 2 ^ 64)
    (h5 : (i / 2 ^ 320) % 2 ^ 64 = (j / 2 ^ 320) % 2 ^ 64)
    (h6 : (i / 2 ^ 384) % 2 ^ 64 = (j / 2 ^ 384) % 2 ^ 64)
    (h7 : (i / 2 ^ 448) % 2 ^ 64 = (j / 2 ^ 448) % 2 ^ 64) : i = j := by
  omega

set_option exponentiation.threshold 2048 in
private theorem keccakCapIdx_injective (i j : Fin keccakCapCard)
    (h : keccakCapIdx i = keccakCapIdx j) : i = j := by
  obtain ⟨e0, h⟩ := List.cons.inj h
  obtain ⟨e1, h⟩ := List.cons.inj h
  obtain ⟨e2, h⟩ := List.cons.inj h
  obtain ⟨e3, h⟩ := List.cons.inj h
  obtain ⟨e4, h⟩ := List.cons.inj h
  obtain ⟨e5, h⟩ := List.cons.inj h
  obtain ⟨e6, h⟩ := List.cons.inj h
  obtain ⟨e7, _⟩ := List.cons.inj h
  exact Fin.ext (digits8_inj i.val j.val (keccakCapCard_eq ▸ i.isLt)
    (keccakCapCard_eq ▸ j.isLt) (keccakLaneOf_toNat_eq e0)
    (keccakLaneOf_toNat_eq e1) (keccakLaneOf_toNat_eq e2) (keccakLaneOf_toNat_eq e3)
    (keccakLaneOf_toNat_eq e4) (keccakLaneOf_toNat_eq e5) (keccakLaneOf_toNat_eq e6)
    (keccakLaneOf_toNat_eq e7))

set_option exponentiation.threshold 2048 in
/-- Every 512-bit capacity value has at most `keccakRateCard = 2^1088` preimages among the
    `2^1600` codes. -/
theorem keccak_capacity_fiber_count (c : List UInt64) :
    Spec.sampleSum (keccakRateCard * keccakCapCard)
      (fun d => if keccakCap512 (keccakDec d) = c then 1 else 0) ≤ keccakRateCard :=
  sponge_fiber_count_of_product_coding keccakCap512 keccakDec keccakCapIdx
    keccakCapIdx_injective
    (fun i j => by
      show keccakCapIdx (spongeCoinTail
        (⟨i.1 * keccakCapCard + j.1, Spec.prodCoin_pair_lt i j⟩ :
          Fin (keccakRateCard * keccakCapCard))) = _
      rw [spongeCoinTail_pair]) c

private theorem keccakRate136_laws_bool :
    SpongeCapLaws keccakCap512 xorRate136 (fun b => (b.length == 136) = true) where
  cap_xor s b _ := keccakRate136_cap_xor s b
  xor_inj s b₁ b₂ h₁ h₂ h :=
    keccakRate136_xor_inj s b₁ b₂ (beq_iff_eq.mp h₁) (beq_iff_eq.mp h₂) h

set_option exponentiation.threshold 2048 in
/-- **`cSHAKE256` over a hidden random transformation of the Keccak state.** State space
    `KState` (1600 bits, coded by `keccakDec`), rate-136 absorption `xorRate136`, read-out
    `rateBlockBytes`, initial state `zeroKState`. Every adaptive adversary that asks for output
    blocks of `cSHAKE256` under arbitrary customizations, with at most `K` transformation calls
    in the run, distinguishes it from a lazily sampled function on block paths with advantage
    at most `K (K + 1) / 2^513`. No hypothesis is left. -/
theorem keccak_cshake_tags_ro_indistinguishability_bound
    (A : Spec.Code (cshakeTagIface (List UInt8)) Bool) (K : Nat) :
    Spec.GameBound
      (Spec.AdvDist
        (spongeRealGame keccakStateCard_pos keccakDec
          xorRate136 rateBlockBytes zeroKState (fun b => b.length == 136)
          (cshakeTagAdversary A) K)
        (spongeIdealGame keccakStateCard_pos keccakDec
          rateBlockBytes zeroKState (fun b => b.length == 136) (cshakeTagAdversary A) K))
      ⟨K * (K + 1), 2 * 2 ^ 512, Nat.mul_pos (by decide) (Nat.two_pow_pos 512)⟩ := by
  refine Spec.GameBound.trans
    (qsag_tags_sponge_ro_indistinguishability_bound
      keccakStateCard_pos keccakRate136_laws_bool
      keccakDec zeroKState keccak_capacity_fiber_count rateBlockBytes A K) ?_
  show K * (K + 1) * keccakRateCard * (2 * 2 ^ 512) ≤
    K * (K + 1) * (2 * (keccakRateCard * keccakCapCard))
  rw [keccakCapCard_eq]
  exact Nat.le_of_eq (sds_bound_rescale _ _ _)

set_option exponentiation.threshold 2048 in
/-- At most `2^40` transformation calls: the `cSHAKE256` bound is below `2^-430`. -/
theorem keccak_cshake_tags_ro_bound_430_bits_at_q2pow40
    (A : Spec.Code (cshakeTagIface (List UInt8)) Bool) (K : Nat) (hK : K ≤ 2 ^ 40) :
    (Spec.AdvDist
      (spongeRealGame keccakStateCard_pos keccakDec
        xorRate136 rateBlockBytes zeroKState (fun b => b.length == 136)
        (cshakeTagAdversary A) K)
      (spongeIdealGame keccakStateCard_pos keccakDec
        rateBlockBytes zeroKState (fun b => b.length == 136)
        (cshakeTagAdversary A) K)).atLeastBits 430 := by
  refine Spec.GameBound.atLeastBits (keccak_cshake_tags_ro_indistinguishability_bound A K) ?_
  show K * (K + 1) * 2 ^ 430 ≤ 2 * 2 ^ 512
  have h1 : K * (K + 1) ≤ 2 ^ 40 * (2 ^ 40 + 1) := Nat.mul_le_mul hK (Nat.succ_le_succ hK)
  exact Nat.le_trans (Nat.mul_le_mul_right _ h1) (by decide +kernel)

/-! ## §7. Teeth -/

/-- **No capacity, no separation.** When the whole state is rate (`xorBlk = XOR` on the full
    state), for every transformation `π`, every initial state and every one-block input there
    is a different two-block input with the same terminal query. -/
theorem tooth_zero_capacity_state_collision {n : Nat} (π : BitVec n → BitVec n)
    (s0 b₁ b₂ : BitVec n) :
    ∃ b₃ : BitVec n, [b₁] ≠ [b₂, b₃] ∧
      spongeTerminalQuery π (fun s b => s ^^^ b) s0 [b₂, b₃] =
        spongeTerminalQuery π (fun s b => s ^^^ b) s0 [b₁] := by
  refine ⟨π (s0 ^^^ b₂) ^^^ (s0 ^^^ b₁), fun h => ?_, ?_⟩
  · have hLen : (1 : Nat) = 2 := congrArg List.length h
    exact absurd hLen (by decide)
  · show π (s0 ^^^ b₂) ^^^ (π (s0 ^^^ b₂) ^^^ (s0 ^^^ b₁)) = s0 ^^^ b₁
    rw [bv_xor_cancel_left]

/-- Toy transformation on `BitVec 1 × BitVec 1`: flip the capacity bit. -/
def toyCapFlip (s : BitVec 1 × BitVec 1) : BitVec 1 × BitVec 1 := (s.1, s.2 ^^^ 1#1)

/-- **Padding is load-bearing.** Without the property that the last block is not the zero
    block, the pairs `([1], output block 1)` and `([1, 0], output block 0)` are different but
    make the same terminal query, and the earlier queries contain no capacity event. -/
theorem tooth_unpadded_length_extension_shares_output_query :
    ∃ (w₁ w₂ : List (BitVec 1)) (j₁ j₂ : Nat), (w₁, j₁) ≠ (w₂, j₂) ∧
      spongeTerminalQuery toyCapFlip rateCapXor (0#1, 0#1) (w₁ ++ List.replicate j₁ 0#1) =
        spongeTerminalQuery toyCapFlip rateCapXor (0#1, 0#1) (w₂ ++ List.replicate j₂ 0#1) ∧
      ¬ SpongeCapEvent toyCapFlip Prod.snd (0#1, 0#1)
        (spongeInnerQueries toyCapFlip rateCapXor (0#1, 0#1) (w₁ ++ List.replicate j₁ 0#1) ++
          spongeInnerQueries toyCapFlip rateCapXor (0#1, 0#1)
            (w₂ ++ List.replicate j₂ 0#1)) := by
  refine ⟨[1#1], [1#1, 0#1], 1, 0, by decide, rfl, ?_⟩
  have hQ : spongeInnerQueries toyCapFlip rateCapXor (0#1, 0#1) ([1#1] ++ List.replicate 1 0#1) ++
      spongeInnerQueries toyCapFlip rateCapXor (0#1, 0#1) ([1#1, 0#1] ++ List.replicate 0 0#1) =
      [(1#1, 0#1), (1#1, 0#1)] := by decide
  rw [hQ]
  intro hEv
  rcases hEv with ⟨x, hx, hc⟩ | ⟨x, y, hx, hy, hne, _⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hx
    rw [hx] at hc
    exact absurd hc (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hx hy
    exact hne (hx.trans hy.symm)

/-- **One capacity value, certain bad event.** With a single capacity value every first draw
    is bad, so the capacity event has probability one and `sponge_cap_bad_bound` gives nothing:
    here it is not below `1/2`. -/
theorem tooth_zero_capacity_bad_event_certain {Dom σ : Type} [DecidableEq Dom] {cardD : Nat}
    (hCard : 0 < cardD) (dec : Fin cardD → σ) (s0 : σ) (q : Dom) :
    ¬ Spec.GameBound
      (spongeCapBadGame hCard (fun _ : σ => ()) dec s0
        (Spec.Code.call (E := Spec.roOracleIface Dom cardD) q
          (fun _ => Spec.Code.ret true)) 1).winProb
      ⟨1, 2, by decide⟩ := by
  intro h
  have hWin : (spongeCapBadGame hCard (fun _ : σ => ()) dec s0
      (Spec.Code.call (E := Spec.roOracleIface Dom cardD) q
        (fun _ => Spec.Code.ret true)) 1).winCount = Spec.roCoinPow cardD 1 := by
    apply Spec.FinGame.winCount_of_forall_win
    intro ω
    show capTableBad (fun _ : σ => ()) dec s0 (spongeLazyRun _ 1 [] ω).2 = true
    rw [spongeLazyRun_call_miss q _ 0 [] ω rfl, spongeLazyRun_ret]
    rfl
  have h2 : (spongeCapBadGame hCard (fun _ : σ => ()) dec s0
      (Spec.Code.call (E := Spec.roOracleIface Dom cardD) q
        (fun _ => Spec.Code.ret true)) 1).winCount * 2 ≤ 1 * Spec.roCoinPow cardD 1 := h
  rw [hWin] at h2
  have hPos := Spec.roCoinPow_pos hCard 1
  omega

/-- State-collision adversary against a sponge with no capacity: read the state after block
    `0`, read the answer for block `1`, then ask for the two-block path `[0, b₃]` with `b₃`
    chosen so that its second transformation input is the one of `[1]`, and compare. -/
def zeroCapacityDistinguisher : Spec.Code (spongeNodeIface (BitVec 1) (BitVec 1)) Bool :=
  Spec.Code.call (E := spongeNodeIface (BitVec 1) (BitVec 1)) [0#1] (fun s₂ =>
    Spec.Code.call (E := spongeNodeIface (BitVec 1) (BitVec 1)) [1#1] (fun t₁ =>
      Spec.Code.call (E := spongeNodeIface (BitVec 1) (BitVec 1)) [0#1, s₂ ^^^ 1#1] (fun t₂ =>
        Spec.Code.ret (t₁ == t₂))))

/-- **The games are different when there is no capacity.** On the one-bit state with full-state
    XOR absorption (one capacity value), `zeroCapacityDistinguisher` wins the real game on all
    16 coins and the ideal game on 8: its advantage is `1/2`, in particular not below `1/4`.
    The indistinguishability bound is therefore not a statement about two equal games. -/
theorem tooth_zero_capacity_distinguisher_advantage_half :
    ¬ Spec.GameBound
      (Spec.AdvDist
        (spongeRealGame (cardD := 2) (by decide) (fun d => BitVec.ofFin d)
          (fun (s b : BitVec 1) => s ^^^ b) (fun s => s) 0#1 (fun _ => true)
          zeroCapacityDistinguisher 4)
        (spongeIdealGame (cardD := 2) (by decide) (fun d => BitVec.ofFin d)
          (fun (s : BitVec 1) => s) 0#1 (fun _ => true) zeroCapacityDistinguisher 4))
      ⟨1, 4, by decide⟩ :=
  fun h => absurd (show Spec.RatBound.le _ _ from h) (by decide +kernel)

/-- The hypotheses of `keccak_qsag_tags_output_queries_disjoint_or_cap_collision` are jointly
    satisfiable (one tag of the list, two different messages), in a model that satisfies the
    capacity laws. -/
theorem witness_keccak_qsag_tags_distinct :
    ∃ (S₁ S₂ m₁ m₂ : List UInt8) (j₁ j₂ : Nat),
      S₁ ∈ qsagSpongeTags ∧ S₂ ∈ qsagSpongeTags ∧ (S₁, m₁, j₁) ≠ (S₂, m₂, j₂) ∧
      SpongeCapLaws keccakCap512 xorRate136 (fun b => b.length = 136) := by
  refine ⟨qsagTagCanopyLeaf, qsagTagCanopyLeaf, [0x01], [0x02], 0, 0, ?_, ?_, ?_,
    keccakRate136_laws⟩
  · rw [qsagSpongeTags_eq]; exact List.mem_cons_self
  · rw [qsagSpongeTags_eq]; exact List.mem_cons_self
  · intro h
    exact absurd (congrArg (fun t => t.2.1) h) (by decide)

#verify_constructive
  Qsag.qsagSpongeTags_eq
  Qsag.witness_keccak_qsag_tags_distinct
  Qsag.SpongeCapEvent.mono
  Qsag.spongeAbsorbBlocks_eq_spongeFold
  Qsag.spongeFold_append
  Qsag.spongeTrace_append
  Qsag.spongeNodeState_reverse
  Qsag.spongeNodeQueries_reverse
  Qsag.spongeTerminalQuery_snoc
  Qsag.spongeTrace_snoc
  Qsag.sponge_node_query_injective_or_cap_event
  Qsag.sponge_distinct_inputs_terminal_disjoint_or_cap_collision
  Qsag.mem_spongeInnerQueries_snoc
  Qsag.sponge_terminal_query_ne_or_cap_event
  Qsag.sponge_output_path_injective
  Qsag.sponge_output_queries_disjoint_or_cap_collision
  Qsag.spongeFold_replicate_zero
  Qsag.spongeTerminalQuery_squeeze
  Qsag.spongeFold_congr
  Qsag.spongeSqueezeFuel_congr
  Qsag.evalSponge_congr_on_queries
  Qsag.absorbPayload_ne_nil
  Qsag.absorbPayload_last_block_ne_zero
  Qsag.absorbPayload_output_path_injective
  Qsag.absorbPayload_output_queries_disjoint_or_cap_collision
  Qsag.evalCshake256Sponge_eq_paddedBlocks
  Qsag.cshake256_output_path_injective
  Qsag.cshake256_output_queries_disjoint_or_cap_collision
  Qsag.qsagSpongeTags_pairwise_distinct
  Qsag.qsag_tags_output_queries_disjoint_or_cap_collision
  Qsag.rateCapXor_laws
  Qsag.rateCapXor_zero
  Qsag.keccakRate136_cap_xor
  Qsag.keccakRate136_zero
  Qsag.keccakRate136_xor_inj
  Qsag.keccakRate136_laws
  Qsag.keccak_qsag_tags_output_queries_disjoint_or_cap_collision
  Qsag.spongeLazyRun_ret
  Qsag.spongeLazyRun_call_zero
  Qsag.spongeLazyRun_call_hit
  Qsag.spongeLazyRun_call_miss
  Qsag.spongeLazyRun_cap_bad_bound
  Qsag.sponge_cap_bad_bound
  Qsag.capTableBad_run_mono
  Qsag.spongeWorlds_agree_until_cap_bad
  Qsag.spongeReal_eq_ideal_of_no_cap_bad
  Qsag.sponge_real_ideal_adv_le_cap_bad
  Qsag.sponge_multi_domain_ro_indistinguishability_bound
  Qsag.cshakeTagPath_injective_on_qsag_tags
  Qsag.qsag_tags_sponge_ro_indistinguishability_bound
  Qsag.sponge_fiber_count_of_product_coding
  Qsag.keccakRateCard_eq
  Qsag.keccakCapCard_eq
  Qsag.keccakStateCard_pos
  Qsag.keccak_capacity_fiber_count
  Qsag.keccak_cshake_tags_ro_indistinguishability_bound
  Qsag.keccak_cshake_tags_ro_bound_430_bits_at_q2pow40
  Qsag.rateCap_sponge_ro_indistinguishability_bound
  Qsag.sponge_ro_bound_430_bits_at_c512_q2pow40
  Qsag.tooth_zero_capacity_state_collision
  Qsag.tooth_unpadded_length_extension_shares_output_query
  Qsag.tooth_zero_capacity_bad_event_certain
  Qsag.tooth_zero_capacity_distinguisher_advantage_half

#tooth_pair Qsag.sponge_terminal_query_ne_or_cap_event vs
  Qsag.tooth_zero_capacity_state_collision
#tooth_pair Qsag.sponge_output_queries_disjoint_or_cap_collision vs
  Qsag.tooth_unpadded_length_extension_shares_output_query
#tooth_pair Qsag.sponge_cap_bad_bound vs Qsag.tooth_zero_capacity_bad_event_certain
#tooth_pair Qsag.sponge_multi_domain_ro_indistinguishability_bound vs
  Qsag.tooth_zero_capacity_distinguisher_advantage_half
#verify_inhabited Qsag.keccak_qsag_tags_output_queries_disjoint_or_cap_collision
  Qsag.witness_keccak_qsag_tags_distinct

end Qsag
end
