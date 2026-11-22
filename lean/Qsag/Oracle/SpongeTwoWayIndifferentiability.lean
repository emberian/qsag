module
/-
# Qsag.Oracle.SpongeTwoWayIndifferentiability — the sponge with direct `π` / `π⁻¹` access

`Qsag.Oracle.SpongeDomainSeparation` bounds a distinguisher that sees the sponge only. Here the
distinguisher also queries the permutation and its inverse directly, and the sponge is compared
with a random oracle plus a simulator of the permutation (the indifferentiability setting of
Bertoni, Daemen, Peeters and Van Assche).

**Model.** A state is a pair (rate part in `Fin R`, capacity part in `Fin C`). `AbsorbOps`
absorbs a block into the rate part (`xorB`), invertibly in the block. The distinguisher
`SpAdv` is a strategy tree with three oracles: `node m`, the rate part of the sponge state
after absorbing the block list `m` from the initial state `s0` (the node oracle of
`SpongeDomainSeparation`: the hash output of a padded message is read from such nodes);
`fwd x = π x`; `inv y = π⁻¹ y`. Coins are a list of states.

* Real world `realRun`: `π` is a lazily sampled two-way permutation (`realFwd`, `realInv`, with
  rejection sampling of fresh points), and `node m` walks `m` through it (`realWalk`).
* Ideal world `idealRun`: `node` is a random oracle on block paths (`roWalk`, sampling every
  prefix), and `fwd`, `inv` are answered by `spongeSimulator`. The simulator keeps the rooted
  path graph: on `fwd x`, if the capacity of `x` is that of a rooted node with path `p`, then
  `x` absorbs a block `b` into it, and the answer has the oracle value at `p ++ [b]` as its
  rate part and a fresh capacity (the node becomes rooted); otherwise, and on every new `inv`
  query, the answer is a fresh uniform state. The capacity of an oracle node that the simulator
  has not rooted is sampled with the node and kept from the simulator (`SimSt.tH`); the
  simulator reads it only when it roots that node.
* Bad events, flagged by the ideal world: a freshly sampled capacity is already in use
  (`capsOf`: capacity collision, and capacity equal to that of `s0`), or a `fwd`/`inv` query
  that the simulator answers freshly carries the capacity of an oracle node the simulator has
  not rooted (`hidCaps`: a guessed hidden capacity, which is how an inverse query can hit an
  existing node).

**Results.**
1. `sponge_two_way_views_eq`: on every coin list with no bad event, the real world on the SAME
   coins gives the distinguisher the same answers, hence the same output. The proof is a
   coupling invariant (`SInv`) between the real permutation table and the simulator state.
2. `idealRun_bad_count`, `sponge_two_way_bad_bound`: the bad event has probability at most
   `K (K + 1) / C` over `K` uniform coins, for every adaptive distinguisher.
3. `sponge_two_way_indifferentiability_bound`: advantage at most `K (K + 1) / C`.
   `bitSponge_two_way_indifferentiability_bound` is the instance with `n`-bit blocks and XOR
   absorption, `keccak_two_way_indifferentiability_431_bits_at_q2pow40` the margin `2^-431`
   at rate 1088, capacity 512 and `K ≤ 2^40`.
4. Teeth, at ONE capacity value (the sponge output is then the whole state after `π`): the
   distinguisher that inverts an output has advantage `1/2`
   (`tooth_no_capacity_inverse_distinguisher_advantage_half`), the two worlds give different
   views on an explicit coin list (`tooth_views_differ_on_bad_coin`), and the bad event is
   certain (`tooth_no_capacity_bad_event_certain`).

**The budget `K`.** `K` is the number of coins: one per fresh permutation point (each block of
a `node` query beyond a known prefix, each new `fwd`/`inv` query), plus the draws the real
world rejects. A run that needs more coins than it has outputs nothing and does not win, in
both worlds, and outside the bad event both worlds run out at the same query. So `K` bounds
the total permutation cost of the distinguisher, in blocks, not its number of oracle calls.

**Oracle audit.** `idealRun_eq_private_oracle` identifies the public output on every tape
with `labelRun`. Its simulator chooses a request using only its graph and the direct query.
The path oracle keeps each product label permanently, exposes its rate to a node query and
exposes the full label only when rooting that path. `readRates_product_law` gives the exact
product distribution on any finite list of fresh distinct paths. The empty path is the IV.
`BlockCost` bounds path lengths plus direct calls on each adaptive branch and guarantees the
ideal run finishes. At that cost the bound allows any real verdict on exhaustion.

**Byte interface.** `ByteAdv` interleaves encoded byte inputs and indexed squeeze reads with
both directions of the same ideal permutation. `named_output_path_injective` separates
customized cSHAKE256 and the repository's 0x1f TurboSHAKE256 domain. Empty-name,
empty-customization cSHAKE uses the same suffix as that Turbo domain.
The 431-bit result is in the rate-1088, capacity-512 ideal-permutation model. Concrete
Keccak round functions and sampling a whole permutation up front are separate models.
-/

public import Qsag.Oracle.SpongeDomainSeparation
public import Qsag.Oracle.Spn
public import Qsag.Spec.GameBound
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.SpongeIndiff

set_option autoImplicit false

/-! ## §1. States, absorption, adversaries -/

/-- A sponge state: a rate part in `Fin R` and a capacity part in `Fin C`. -/
abbrev SpSt (R C : Nat) : Type := Fin R × Fin C

/-- Absorption of a block into the rate part, with the block recovered from the two rate values:
    for every rate value `r`, `xorB r` is a bijection from blocks to rate values. -/
structure AbsorbOps (β : Type) (R : Nat) where
  xorB : Fin R → β → Fin R
  diffB : Fin R → Fin R → β
  xor_diff : ∀ r r' : Fin R, xorB r (diffB r r') = r'
  diff_xor : ∀ (r : Fin R) (b : β), diffB r (xorB r b) = b

/-- Adaptive distinguisher with three oracles: the rate part of the sponge state at a block
    path (`node`), the permutation (`fwd`) and its inverse (`inv`). -/
inductive SpAdv (β : Type) (R C : Nat) (Out : Type) where
  | done (o : Out)
  | node (m : List β) (k : Fin R → SpAdv β R C Out)
  | fwd (x : SpSt R C) (k : SpSt R C → SpAdv β R C Out)
  | inv (y : SpSt R C) (k : SpSt R C → SpAdv β R C Out)

/-! ## §2. Real world: a lazily sampled two-way permutation and the sponge walking through it -/

/-- Table of a partial permutation: entries `(x, π x)`, newest first. -/
abbrev PermTable (R C : Nat) : Type := List (SpSt R C × SpSt R C)

def permFwd? {R C : Nat} (τ : PermTable R C) (x : SpSt R C) : Option (SpSt R C) :=
  (τ.find? (fun e => decide (e.1 = x))).map (fun e => e.2)

def permInv? {R C : Nat} (τ : PermTable R C) (y : SpSt R C) : Option (SpSt R C) :=
  (τ.find? (fun e => decide (e.2 = y))).map (fun e => e.1)

/-- Rejection sampling of a fresh output: the first coin that is not yet an output. -/
def drawFreshOut {R C : Nat} (τ : PermTable R C) :
    List (SpSt R C) → Option (SpSt R C × List (SpSt R C))
  | [] => none
  | d :: ω => if (permInv? τ d).isSome = true then drawFreshOut τ ω else some (d, ω)

/-- Rejection sampling of a fresh input: the first coin that is not yet an input. -/
def drawFreshIn {R C : Nat} (τ : PermTable R C) :
    List (SpSt R C) → Option (SpSt R C × List (SpSt R C))
  | [] => none
  | d :: ω => if (permFwd? τ d).isSome = true then drawFreshIn τ ω else some (d, ω)

/-- `π x` in the lazily sampled permutation. `none`: the coins ran out. -/
def realFwd {R C : Nat} (τ : PermTable R C) (ω : List (SpSt R C)) (x : SpSt R C) :
    Option (SpSt R C × PermTable R C × List (SpSt R C)) :=
  match permFwd? τ x with
  | some z => some (z, τ, ω)
  | none =>
    match drawFreshOut τ ω with
    | none => none
    | some (z, ω') => some (z, (x, z) :: τ, ω')

/-- `π⁻¹ y` in the lazily sampled permutation. -/
def realInv {R C : Nat} (τ : PermTable R C) (ω : List (SpSt R C)) (y : SpSt R C) :
    Option (SpSt R C × PermTable R C × List (SpSt R C)) :=
  match permInv? τ y with
  | some x => some (x, τ, ω)
  | none =>
    match drawFreshIn τ ω with
    | none => none
    | some (x, ω') => some (x, (x, y) :: τ, ω')

/-- The sponge: absorb the blocks one by one, applying `π` after each. -/
def realWalk {β : Type} {R C : Nat} (ops : AbsorbOps β R) :
    PermTable R C → List (SpSt R C) → SpSt R C → List β →
      Option (SpSt R C × PermTable R C × List (SpSt R C))
  | τ, ω, s, [] => some (s, τ, ω)
  | τ, ω, s, b :: m =>
    match realFwd τ ω (ops.xorB s.1 b, s.2) with
    | none => none
    | some (z, τ', ω') => realWalk ops τ' ω' z m

/-- Real world `(sponge^π, π, π⁻¹)`. -/
def realRun {β : Type} {R C : Nat} {Out : Type} (ops : AbsorbOps β R) (s0 : SpSt R C) :
    SpAdv β R C Out → PermTable R C → List (SpSt R C) → Option Out
  | .done o, _, _ => some o
  | .node m k, τ, ω =>
    match realWalk ops τ ω s0 m with
    | none => none
    | some (s, τ', ω') => realRun ops s0 (k s.1) τ' ω'
  | .fwd x k, τ, ω =>
    match realFwd τ ω x with
    | none => none
    | some (z, τ', ω') => realRun ops s0 (k z) τ' ω'
  | .inv y k, τ, ω =>
    match realInv τ ω y with
    | none => none
    | some (x, τ', ω') => realRun ops s0 (k x) τ' ω'

/-! ## §3. Ideal world: a random oracle on block paths and the simulator -/

/-- State of the ideal world.
    * `rt`: the simulator's rooted nodes `(path, x, z)`: it answered `π x = z`, `x` absorbs the
      last block of `path` into the node of the parent path, and `z.1` is the oracle value at
      `path`.
    * `tH`: oracle values `(path, r, c)` sampled by a distinguisher query and not yet used by
      the simulator; `c` is the value at `path` of the simulator's private random function,
      sampled together with `r` and read only when the simulator roots `path`.
    * `tF`: the simulator's other answers `π x = z`. -/
structure SimSt (β : Type) (R C : Nat) where
  rt : List (List β × SpSt R C × SpSt R C)
  tH : List (List β × Fin R × Fin C)
  tF : List (SpSt R C × SpSt R C)

def SimSt.init (β : Type) (R C : Nat) : SimSt β R C := ⟨[], [], []⟩

/-- The random oracle's memo: the value at `p`, if sampled. -/
def roLookup {β : Type} [DecidableEq β] {R C : Nat} (S : SimSt β R C) (p : List β) :
    Option (Fin R) :=
  match S.rt.find? (fun e => decide (e.1 = p)) with
  | some e => some e.2.2.1
  | none => (S.tH.find? (fun e => decide (e.1 = p))).map (fun e => e.2.1)

/-- Capacity values in use: of the initial state, of every sampled node, and of both ends of
    the simulator's unrooted answers. -/
def capsOf {β : Type} {R C : Nat} (s0 : SpSt R C) (S : SimSt β R C) : List (Fin C) :=
  s0.2 :: (S.tH.map (fun e => e.2.2) ++ (S.rt.map (fun e => e.2.2.2) ++
    (S.tF.map (fun e => e.1.2) ++ S.tF.map (fun e => e.2.2))))

/-- Capacity values the simulator has not seen. -/
def hidCaps {β : Type} {R C : Nat} (S : SimSt β R C) : List (Fin C) :=
  S.tH.map (fun e => e.2.2)

/-- Membership test for capacity values. (`decide (c ∈ l)` on `Fin` resolves `BEq` through
    `Fin.instLinearOrderPackage`, whose lawfulness proof is classical in this toolchain.) -/
def capIn {C : Nat} (c : Fin C) (l : List (Fin C)) : Bool := l.any (fun y => decide (y = c))

theorem capIn_eq_true {C : Nat} {c : Fin C} {l : List (Fin C)} : capIn c l = true ↔ c ∈ l := by
  unfold capIn
  rw [List.any_eq_true]
  constructor
  · intro h
    obtain ⟨y, hy, hd⟩ := h
    have hyc : y = c := of_decide_eq_true hd
    rw [← hyc]
    exact hy
  · intro h
    exact ⟨c, h, decide_eq_true rfl⟩

theorem capIn_eq_false {C : Nat} {c : Fin C} {l : List (Fin C)} (h : capIn c l = false) :
    c ∉ l := by
  intro hm
  rw [capIn_eq_true.mpr hm] at h
  exact absurd h (by decide)

/-- Result of one oracle call of the ideal world: the answer with the new state and the unused
    coins (`none`: the coins ran out), and whether a bad event happened in the call. -/
abbrev StepRes (β : Type) (R C : Nat) (A : Type) : Type :=
  Option (A × SimSt β R C × List (SpSt R C)) × Bool

/-- Sample the oracle at `p` unless it has a value there. Bad: the fresh capacity is in use. -/
def roStep {β : Type} [DecidableEq β] {R C : Nat} (s0 : SpSt R C) (S : SimSt β R C)
    (ω : List (SpSt R C)) (p : List β) : StepRes β R C (Fin R) :=
  match roLookup S p with
  | some r => (some (r, S, ω), false)
  | none =>
    match ω with
    | [] => (none, false)
    | d :: ω' => (some (d.1, { S with tH := (p, d.1, d.2) :: S.tH }, ω'),
        capIn d.2 (capsOf s0 S))

/-- The random oracle at the path `p ++ m`, sampling at every prefix beyond `p` on the way;
    `r` is the value at `p`, `bad` the flag so far. -/
def roWalk {β : Type} [DecidableEq β] {R C : Nat} (s0 : SpSt R C) :
    SimSt β R C → List (SpSt R C) → List β → Fin R → Bool → List β → StepRes β R C (Fin R)
  | S, ω, _, r, bad, [] => (some (r, S, ω), bad)
  | S, ω, p, _, bad, b :: m =>
    match roStep s0 S ω (p ++ [b]) with
    | (none, bd) => (none, bad || bd)
    | (some (r', S', ω'), bd) => roWalk s0 S' ω' (p ++ [b]) r' (bad || bd) m

def simFwdKnown {β : Type} {R C : Nat} (S : SimSt β R C) (x : SpSt R C) : Option (SpSt R C) :=
  match S.rt.find? (fun e => decide (e.2.1 = x)) with
  | some e => some e.2.2
  | none => (S.tF.find? (fun e => decide (e.1 = x))).map (fun e => e.2)

def simInvKnown {β : Type} {R C : Nat} (S : SimSt β R C) (y : SpSt R C) : Option (SpSt R C) :=
  match S.rt.find? (fun e => decide (e.2.2 = y)) with
  | some e => some e.2.1
  | none => (S.tF.find? (fun e => decide (e.2 = y))).map (fun e => e.1)

/-- A rooted node with capacity `c`: the initial state, or a node the simulator rooted. -/
def simFindRoot {β : Type} {R C : Nat} (s0 : SpSt R C) (S : SimSt β R C) (c : Fin C) :
    Option (List β × SpSt R C) :=
  if c = s0.2 then some ([], s0)
  else (S.rt.find? (fun e => decide (e.2.2.2 = c))).map (fun e => (e.1, e.2.2))

/-- **Simulator, forward query.** A repeated query gets the recorded answer. If the capacity of
    `x` is that of a rooted node with path `p`, then `x` absorbs the block `b = diffB t.1 x.1`
    into it: the answer's rate part is the oracle value at `p ++ [b]` and its capacity part is
    the simulator's private random value there. Otherwise the answer is a fresh uniform state.
    Bad: a fresh capacity is in use, or the capacity of an unrooted `x` is one the simulator
    has not seen. -/
def spongeSimFwd {β : Type} [DecidableEq β] {R C : Nat} (ops : AbsorbOps β R) (s0 : SpSt R C)
    (S : SimSt β R C) (ω : List (SpSt R C)) (x : SpSt R C) : StepRes β R C (SpSt R C) :=
  match simFwdKnown S x with
  | some z => (some (z, S, ω), false)
  | none =>
    match simFindRoot s0 S x.2 with
    | some (p, t) =>
      match S.tH.find? (fun e => decide (e.1 = p ++ [ops.diffB t.1 x.1])) with
      | some e =>
        (some ((e.2.1, e.2.2),
          { S with rt := (p ++ [ops.diffB t.1 x.1], x, (e.2.1, e.2.2)) :: S.rt,
                   tH := S.tH.eraseP (fun e => decide (e.1 = p ++ [ops.diffB t.1 x.1])) }, ω),
          false)
      | none =>
        match ω with
        | [] => (none, false)
        | d :: ω' =>
          (some (d, { S with rt := (p ++ [ops.diffB t.1 x.1], x, d) :: S.rt }, ω'),
            capIn d.2 (capsOf s0 S))
    | none =>
      match ω with
      | [] => (none, capIn x.2 (hidCaps S))
      | d :: ω' =>
        (some (d, { S with tF := (x, d) :: S.tF }, ω'),
          capIn x.2 (hidCaps S) || capIn d.2 (capsOf s0 S))

/-- **Simulator, inverse query.** A repeated query gets the recorded answer; otherwise the
    preimage is a fresh uniform state. Bad: the fresh capacity is in use, or the capacity of
    `y` is one the simulator has not seen. -/
def spongeSimInv {β : Type} {R C : Nat} (s0 : SpSt R C)
    (S : SimSt β R C) (ω : List (SpSt R C)) (y : SpSt R C) : StepRes β R C (SpSt R C) :=
  match simInvKnown S y with
  | some x => (some (x, S, ω), false)
  | none =>
    match ω with
    | [] => (none, capIn y.2 (hidCaps S))
    | d :: ω' =>
      (some (d, { S with tF := (d, y) :: S.tF }, ω'),
        capIn y.2 (hidCaps S) || capIn d.2 (capsOf s0 S))

/-- The simulator `(sim_π, sim_π⁻¹)`: `inverse = false` is a forward query. -/
def spongeSimulator {β : Type} [DecidableEq β] {R C : Nat} (ops : AbsorbOps β R) (s0 : SpSt R C)
    (S : SimSt β R C) (ω : List (SpSt R C)) (inverse : Bool) (q : SpSt R C) :
    StepRes β R C (SpSt R C) :=
  if inverse = true then spongeSimInv s0 S ω q else spongeSimFwd ops s0 S ω q

/-- Ideal world `(RO, sim_π, sim_π⁻¹)`: the distinguisher's output, and whether a bad event
    happened. -/
def idealRun {β : Type} [DecidableEq β] {R C : Nat} {Out : Type} (ops : AbsorbOps β R)
    (s0 : SpSt R C) : SpAdv β R C Out → SimSt β R C → List (SpSt R C) → Option Out × Bool
  | .done o, _, _ => (some o, false)
  | .node m k, S, ω =>
    match roWalk s0 S ω [] s0.1 false m with
    | (none, bd) => (none, bd)
    | (some (r, S', ω'), bd) =>
      ((idealRun ops s0 (k r) S' ω').1, bd || (idealRun ops s0 (k r) S' ω').2)
  | .fwd x k, S, ω =>
    match spongeSimulator ops s0 S ω false x with
    | (none, bd) => (none, bd)
    | (some (z, S', ω'), bd) =>
      ((idealRun ops s0 (k z) S' ω').1, bd || (idealRun ops s0 (k z) S' ω').2)
  | .inv y k, S, ω =>
    match spongeSimulator ops s0 S ω true y with
    | (none, bd) => (none, bd)
    | (some (x, S', ω'), bd) =>
      ((idealRun ops s0 (k x) S' ω').1, bd || (idealRun ops s0 (k x) S' ω').2)

/-! ## §4. Coins -/

/-- Sum over all coin lists of length `K`. -/
def sumC (R C : Nat) : Nat → (List (SpSt R C) → Nat) → Nat
  | 0, f => f []
  | K + 1, f => Spec.sampleSum R (fun r => Spec.sampleSum C (fun c =>
      sumC R C K (fun ω => f ((r, c) :: ω))))

def decodeSt {R C : Nat} (d : Fin (R * C)) : SpSt R C :=
  (⟨d.1 / C, (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero (fun h => by
      subst h; exact Nat.not_lt_zero _ d.2))).mpr d.2⟩,
   ⟨d.1 % C, Nat.mod_lt _ (Nat.pos_of_ne_zero (fun h => by
      subst h; exact Nat.not_lt_zero _ d.2))⟩)

/-- A coin of `Fin ((R C)^K)` read as `K` states, most significant digit first. -/
def coinList {R C : Nat} : (K : Nat) → Fin (Spec.roCoinPow (R * C) K) → List (SpSt R C)
  | 0, _ => []
  | K + 1, ω =>
    decodeSt (⟨ω.1 / Spec.roCoinPow (R * C) K,
        (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero (fun h => by
          have h2 : ω.1 < (R * C) * Spec.roCoinPow (R * C) K := ω.2
          rw [h, Nat.mul_zero] at h2
          exact Nat.not_lt_zero _ h2))).mpr ω.2⟩ : Fin (R * C)) ::
      coinList K ⟨ω.1 % Spec.roCoinPow (R * C) K, Nat.mod_lt _ (Nat.pos_of_ne_zero (fun h => by
          have h2 : ω.1 < (R * C) * Spec.roCoinPow (R * C) K := ω.2
          rw [h, Nat.mul_zero] at h2
          exact Nat.not_lt_zero _ h2))⟩

/-! ## §5. Per-coin view equality outside the bad event -/

/-- The sponge state at a block path: the initial state at the empty path, a rooted node, or a
    node sampled by the oracle that the simulator has not seen. -/
private def nodeAt {β : Type} {R C : Nat} (s0 : SpSt R C) (S : SimSt β R C) (p : List β)
    (s : SpSt R C) : Prop :=
  (p = [] ∧ s = s0) ∨ (∃ x, (p, x, s) ∈ S.rt) ∨ (p, s.1, s.2) ∈ S.tH

/-- The coupling invariant between the real permutation table and the ideal state: the table
    is a partial injection whose entries are exactly the simulator's unrooted answers and the
    parent-to-child edges of the path tree; nodes have pairwise distinct capacities, and no
    unrooted query has the capacity of a node. -/
private structure SInv {β : Type} {R C : Nat} (ops : AbsorbOps β R) (s0 : SpSt R C)
    (τ : PermTable R C) (S : SimSt β R C) : Prop where
  fn : ∀ x z z', (x, z) ∈ τ → (x, z') ∈ τ → z = z'
  inj : ∀ x x' z, (x, z) ∈ τ → (x', z) ∈ τ → x = x'
  nfn : ∀ p s s', nodeAt s0 S p s → nodeAt s0 S p s' → s = s'
  ncap : ∀ p p' s s', nodeAt s0 S p s → nodeAt s0 S p' s' → s.2 = s'.2 → p = p'
  edge : ∀ x z, (x, z) ∈ τ ↔ ((x, z) ∈ S.tF ∨
    ∃ p b s, nodeAt s0 S p s ∧ nodeAt s0 S (p ++ [b]) z ∧ x = (ops.xorB s.1 b, s.2))
  par : ∀ p b z, nodeAt s0 S (p ++ [b]) z → ∃ s, nodeAt s0 S p s
  rtx : ∀ q x z, (q, x, z) ∈ S.rt →
    ∃ p b s, q = p ++ [b] ∧ nodeAt s0 S p s ∧ x = (ops.xorB s.1 b, s.2)
  tfc : ∀ x z p s, (x, z) ∈ S.tF → nodeAt s0 S p s → x.2 ≠ s.2

/-- One oracle call of the two worlds agrees: both run out of coins, or both answer with
    related values, the same unused coins, and the invariant again. -/
@[reducible] private def Coupled {β : Type} {R C : Nat} {A B : Type} (ops : AbsorbOps β R)
    (s0 : SpSt R C) (rel : A → B → SimSt β R C → Prop)
    (res : Option (A × SimSt β R C × List (SpSt R C)))
    (real : Option (B × PermTable R C × List (SpSt R C))) : Prop :=
  (res = none → real = none) ∧
  ∀ a S' ω', res = some (a, S', ω') →
    ∃ b τ', real = some (b, τ', ω') ∧ rel a b S' ∧ SInv ops s0 τ' S'

/-! ### Lists -/

private theorem snoc_ne_nil {α : Type} (p : List α) (b : α) : p ++ [b] ≠ [] :=
  fun h => nomatch (List.append_eq_nil_iff.mp h).2

private theorem snoc_ne_self {α : Type} (p : List α) (b : α) : p ++ [b] ≠ p := by
  intro h
  have h1 := congrArg List.length h
  rw [List.length_append] at h1
  simp only [List.length_cons, List.length_nil] at h1
  omega

private theorem mem_or_eraseP {α : Type} (q : α → Bool) :
    ∀ (l : List α) (e a : α), l.find? q = some e → a ∈ l → a = e ∨ a ∈ l.eraseP q
  | [], _, _, h, _ => nomatch h
  | y :: l, e, a, h, ha => by
    rw [List.find?_cons] at h
    rw [List.eraseP_cons]
    cases hq : q y
    · rw [hq] at h
      show a = e ∨ a ∈ y :: l.eraseP q
      rcases List.mem_cons.mp ha with h1 | hm
      · exact Or.inr (by rw [h1]; exact List.mem_cons_self)
      · rcases mem_or_eraseP q l e a h hm with h2 | h2
        · exact Or.inl h2
        · exact Or.inr (List.mem_cons_of_mem _ h2)
    · rw [hq] at h
      have hy : y = e := Option.some.inj h
      show a = e ∨ a ∈ l
      rcases List.mem_cons.mp ha with h1 | hm
      · exact Or.inl (h1.trans hy)
      · exact Or.inr hm

/-! ### The real permutation table -/

private theorem permFwd_of_mem {R C : Nat} {τ : PermTable R C}
    (hfn : ∀ x z z', (x, z) ∈ τ → (x, z') ∈ τ → z = z') {x z : SpSt R C} (h : (x, z) ∈ τ) :
    permFwd? τ x = some z := by
  unfold permFwd?
  cases hf : τ.find? (fun e => decide (e.1 = x)) with
  | none => exact absurd (decide_eq_true rfl) (List.find?_eq_none.mp hf (x, z) h)
  | some e =>
    have h10 := List.find?_some hf
    have h1 : e.1 = x := of_decide_eq_true h10
    have h2 := List.mem_of_find?_eq_some hf
    obtain ⟨a, b⟩ := e
    have h1' : a = x := h1
    subst h1'
    have h3 : b = z := hfn a b z h2 h
    subst h3
    rfl

private theorem permInv_of_mem {R C : Nat} {τ : PermTable R C}
    (hinj : ∀ x x' z, (x, z) ∈ τ → (x', z) ∈ τ → x = x') {x z : SpSt R C} (h : (x, z) ∈ τ) :
    permInv? τ z = some x := by
  unfold permInv?
  cases hf : τ.find? (fun e => decide (e.2 = z)) with
  | none => exact absurd (decide_eq_true rfl) (List.find?_eq_none.mp hf (x, z) h)
  | some e =>
    have h10 := List.find?_some hf
    have h1 : e.2 = z := of_decide_eq_true h10
    have h2 := List.mem_of_find?_eq_some hf
    obtain ⟨a, b⟩ := e
    have h1' : b = z := h1
    subst h1'
    have h3 : a = x := hinj a x b h2 h
    subst h3
    rfl

private theorem permFwd_none {R C : Nat} {τ : PermTable R C} {x : SpSt R C}
    (h : ∀ z, (x, z) ∉ τ) : permFwd? τ x = none := by
  unfold permFwd?
  cases hf : τ.find? (fun e => decide (e.1 = x)) with
  | none => rfl
  | some e =>
    have h10 := List.find?_some hf
    have h1 : e.1 = x := of_decide_eq_true h10
    have h2 := List.mem_of_find?_eq_some hf
    obtain ⟨a, b⟩ := e
    have h1' : a = x := h1
    subst h1'
    exact absurd h2 (h b)

private theorem permInv_none {R C : Nat} {τ : PermTable R C} {z : SpSt R C}
    (h : ∀ x, (x, z) ∉ τ) : permInv? τ z = none := by
  unfold permInv?
  cases hf : τ.find? (fun e => decide (e.2 = z)) with
  | none => rfl
  | some e =>
    have h10 := List.find?_some hf
    have h1 : e.2 = z := of_decide_eq_true h10
    have h2 := List.mem_of_find?_eq_some hf
    obtain ⟨a, b⟩ := e
    have h1' : b = z := h1
    subst h1'
    exact absurd h2 (h a)

theorem realFwd_known {R C : Nat} {τ : PermTable R C}
    (hfn : ∀ x z z', (x, z) ∈ τ → (x, z') ∈ τ → z = z') {x z : SpSt R C} (h : (x, z) ∈ τ)
    (ω : List (SpSt R C)) : realFwd τ ω x = some (z, τ, ω) := by
  unfold realFwd
  rw [permFwd_of_mem hfn h]

theorem realInv_known {R C : Nat} {τ : PermTable R C}
    (hinj : ∀ x x' z, (x, z) ∈ τ → (x', z) ∈ τ → x = x') {x z : SpSt R C} (h : (x, z) ∈ τ)
    (ω : List (SpSt R C)) : realInv τ ω z = some (x, τ, ω) := by
  unfold realInv
  rw [permInv_of_mem hinj h]

private theorem realFwd_nil {R C : Nat} {τ : PermTable R C} {x : SpSt R C}
    (hx : ∀ z, (x, z) ∉ τ) : realFwd τ [] x = none := by
  unfold realFwd
  rw [permFwd_none hx]
  rfl

private theorem realInv_nil {R C : Nat} {τ : PermTable R C} {y : SpSt R C}
    (hy : ∀ x, (x, y) ∉ τ) : realInv τ [] y = none := by
  unfold realInv
  rw [permInv_none hy]
  rfl

theorem realFwd_fresh {R C : Nat} {τ : PermTable R C} {x d : SpSt R C}
    (hx : ∀ z, (x, z) ∉ τ) (hd : ∀ x', (x', d) ∉ τ) (ω : List (SpSt R C)) :
    realFwd τ (d :: ω) x = some (d, (x, d) :: τ, ω) := by
  have hdraw : drawFreshOut τ (d :: ω) = some (d, ω) := by
    show (if (permInv? τ d).isSome = true then drawFreshOut τ ω else some (d, ω)) = some (d, ω)
    rw [permInv_none hd]
    rfl
  unfold realFwd
  rw [permFwd_none hx, hdraw]

theorem realInv_fresh {R C : Nat} {τ : PermTable R C} {y d : SpSt R C}
    (hy : ∀ x, (x, y) ∉ τ) (hd : ∀ z, (d, z) ∉ τ) (ω : List (SpSt R C)) :
    realInv τ (d :: ω) y = some (d, (d, y) :: τ, ω) := by
  have hdraw : drawFreshIn τ (d :: ω) = some (d, ω) := by
    show (if (permFwd? τ d).isSome = true then drawFreshIn τ ω else some (d, ω)) = some (d, ω)
    rw [permFwd_none hd]
    rfl
  unfold realInv
  rw [permInv_none hy, hdraw]

/-! ### Nodes and capacities -/

private theorem node_cap {β : Type} {R C : Nat} {s0 : SpSt R C} {S : SimSt β R C} {p : List β}
    {s : SpSt R C} (h : nodeAt s0 S p s) : s.2 ∈ capsOf s0 S := by
  unfold capsOf
  rcases h with ⟨_, h0⟩ | ⟨x, hx⟩ | ht
  · rw [h0]; exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_left _
      (List.mem_map.mpr ⟨_, hx, rfl⟩)))
  · exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨_, ht, rfl⟩))

private theorem tF_cap_in {β : Type} {R C : Nat} {s0 : SpSt R C} {S : SimSt β R C}
    {x z : SpSt R C} (h : (x, z) ∈ S.tF) : x.2 ∈ capsOf s0 S := by
  unfold capsOf
  exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_left _ (List.mem_map.mpr ⟨_, h, rfl⟩))))

private theorem tF_cap_out {β : Type} {R C : Nat} {s0 : SpSt R C} {S : SimSt β R C}
    {x z : SpSt R C} (h : (x, z) ∈ S.tF) : z.2 ∈ capsOf s0 S := by
  unfold capsOf
  exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_append_right _
    (List.mem_append_right _ (List.mem_map.mpr ⟨_, h, rfl⟩))))

private theorem out_cap {β : Type} {R C : Nat} {ops : AbsorbOps β R} {s0 : SpSt R C}
    {τ : PermTable R C} {S : SimSt β R C} (hI : SInv ops s0 τ S) {x z : SpSt R C}
    (h : (x, z) ∈ τ) : z.2 ∈ capsOf s0 S := by
  rcases (hI.edge x z).mp h with ht | ⟨p, b, s, _, hq, _⟩
  · exact tF_cap_out ht
  · exact node_cap hq

private theorem in_cap {β : Type} {R C : Nat} {ops : AbsorbOps β R} {s0 : SpSt R C}
    {τ : PermTable R C} {S : SimSt β R C} (hI : SInv ops s0 τ S) {x z : SpSt R C}
    (h : (x, z) ∈ τ) : x.2 ∈ capsOf s0 S := by
  rcases (hI.edge x z).mp h with ht | ⟨p, b, s, hp, _, hx⟩
  · exact tF_cap_in ht
  · rw [hx]
    show s.2 ∈ capsOf s0 S
    exact node_cap hp

private theorem fresh_in {β : Type} {R C : Nat} {ops : AbsorbOps β R} {s0 : SpSt R C}
    {τ : PermTable R C} {S : SimSt β R C} (hI : SInv ops s0 τ S) {p : List β} {b : β}
    {s x : SpSt R C} (hp : nodeAt s0 S p s) (hx : x = (ops.xorB s.1 b, s.2))
    (hf : ∀ s', ¬ nodeAt s0 S (p ++ [b]) s') : ∀ z, (x, z) ∉ τ := by
  intro z hz
  rcases (hI.edge x z).mp hz with ht | ⟨p', b', s', hp', hq', hx'⟩
  · exact hI.tfc x z p s ht hp (by rw [hx])
  · have hxx : (ops.xorB s.1 b, s.2) = (ops.xorB s'.1 b', s'.2) := hx.symm.trans hx'
    have hc : s.2 = s'.2 := (Prod.mk.inj hxx).2
    have hpp := hI.ncap p p' s s' hp hp' hc
    subst hpp
    have hss := hI.nfn p s s' hp hp'
    subst hss
    have h1 : ops.xorB s.1 b = ops.xorB s.1 b' := (Prod.mk.inj hxx).1
    have h2 := congrArg (ops.diffB s.1) h1
    rw [ops.diff_xor, ops.diff_xor] at h2
    subst h2
    exact hf z hq'

/-! ### Preservation of the invariant -/

private theorem inv_add_node {β : Type} {R C : Nat} {ops : AbsorbOps β R} {s0 : SpSt R C}
    {τ : PermTable R C} {S S' : SimSt β R C} (hI : SInv ops s0 τ S) {p : List β} {b : β}
    {s x d : SpSt R C} (hp : nodeAt s0 S p s) (hx : x = (ops.xorB s.1 b, s.2))
    (hf : ∀ s', ¬ nodeAt s0 S (p ++ [b]) s') (hd : d.2 ∉ capsOf s0 S)
    (hN : ∀ p' s', nodeAt s0 S' p' s' ↔ (nodeAt s0 S p' s' ∨ (p' = p ++ [b] ∧ s' = d)))
    (htF : S'.tF = S.tF)
    (hrt : ∀ q x' z, (q, x', z) ∈ S'.rt → (q, x', z) ∈ S.rt ∨ (q = p ++ [b] ∧ x' = x)) :
    SInv ops s0 ((x, d) :: τ) S' := by
  have hxin := fresh_in hI hp hx hf
  have hdout : ∀ x', (x', d) ∉ τ := fun x' h => hd (out_cap hI h)
  have lift : ∀ p' s', nodeAt s0 S p' s' → nodeAt s0 S' p' s' :=
    fun p' s' h => (hN p' s').mpr (Or.inl h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a z z' h1 h2
    rcases List.mem_cons.mp h1 with e1 | m1
    · rcases List.mem_cons.mp h2 with e2 | m2
      · exact ((Prod.mk.inj e1).2).trans ((Prod.mk.inj e2).2).symm
      · have ha : a = x := (Prod.mk.inj e1).1
        rw [ha] at m2
        exact absurd m2 (hxin z')
    · rcases List.mem_cons.mp h2 with e2 | m2
      · have ha : a = x := (Prod.mk.inj e2).1
        rw [ha] at m1
        exact absurd m1 (hxin z)
      · exact hI.fn a z z' m1 m2
  · intro a a' z h1 h2
    rcases List.mem_cons.mp h1 with e1 | m1
    · rcases List.mem_cons.mp h2 with e2 | m2
      · exact ((Prod.mk.inj e1).1).trans ((Prod.mk.inj e2).1).symm
      · have hz : z = d := (Prod.mk.inj e1).2
        rw [hz] at m2
        exact absurd m2 (hdout a')
    · rcases List.mem_cons.mp h2 with e2 | m2
      · have hz : z = d := (Prod.mk.inj e2).2
        rw [hz] at m1
        exact absurd m1 (hdout a)
      · exact hI.inj a a' z m1 m2
  · intro p' s1 s2 h1 h2
    rcases (hN p' s1).mp h1 with o1 | ⟨q1, d1⟩
    · rcases (hN p' s2).mp h2 with o2 | ⟨q2, _⟩
      · exact hI.nfn p' s1 s2 o1 o2
      · rw [q2] at o1
        exact absurd o1 (hf s1)
    · rcases (hN p' s2).mp h2 with o2 | ⟨_, d2⟩
      · rw [q1] at o2
        exact absurd o2 (hf s2)
      · exact d1.trans d2.symm
  · intro p1 p2 s1 s2 h1 h2 hc
    rcases (hN p1 s1).mp h1 with o1 | ⟨q1, d1⟩
    · rcases (hN p2 s2).mp h2 with o2 | ⟨_, d2⟩
      · exact hI.ncap p1 p2 s1 s2 o1 o2 hc
      · rw [d2] at hc
        exact absurd (by rw [← hc]; exact node_cap o1) hd
    · rcases (hN p2 s2).mp h2 with o2 | ⟨q2, _⟩
      · rw [d1] at hc
        exact absurd (by rw [hc]; exact node_cap o2) hd
      · exact q1.trans q2.symm
  · intro a z
    constructor
    · intro h
      rcases List.mem_cons.mp h with e | m
      · obtain ⟨ea, ez⟩ := Prod.mk.inj e
        exact Or.inr ⟨p, b, s, lift p s hp, (hN _ _).mpr (Or.inr ⟨rfl, ez⟩), ea.trans hx⟩
      · rcases (hI.edge a z).mp m with ht | ⟨p', b', s', hp', hq', hx'⟩
        · exact Or.inl (by rw [htF]; exact ht)
        · exact Or.inr ⟨p', b', s', lift _ _ hp', lift _ _ hq', hx'⟩
    · intro h
      rcases h with ht | ⟨p', b', s', hp', hq', hx'⟩
      · exact List.mem_cons_of_mem _ ((hI.edge a z).mpr (Or.inl (by rw [← htF]; exact ht)))
      · rcases (hN p' s').mp hp' with o1 | ⟨q1, _⟩
        · rcases (hN _ z).mp hq' with o2 | ⟨q2, d2⟩
          · exact List.mem_cons_of_mem _ ((hI.edge a z).mpr (Or.inr ⟨p', b', s', o1, o2, hx'⟩))
          · obtain ⟨e1, e2⟩ := List.append_inj' q2 rfl
            have e3 : b' = b := (List.cons.inj e2).1
            rw [e1] at o1
            have e4 : s' = s := hI.nfn p s' s o1 hp
            have e5 : (a, z) = (x, d) := by rw [hx', d2, hx, e3, e4]
            rw [e5]
            exact List.mem_cons_self
        · rcases (hN _ z).mp hq' with o2 | ⟨q2, _⟩
          · rw [q1] at o2
            obtain ⟨s'', hs''⟩ := hI.par _ _ _ o2
            exact absurd hs'' (hf s'')
          · rw [q1] at q2
            exact absurd q2 (snoc_ne_self _ _)
  · intro p' b' z h
    rcases (hN _ z).mp h with o | ⟨q, _⟩
    · obtain ⟨s', hs'⟩ := hI.par p' b' z o
      exact ⟨s', lift _ _ hs'⟩
    · obtain ⟨e1, _⟩ := List.append_inj' q rfl
      rw [e1]
      exact ⟨s, lift _ _ hp⟩
  · intro q a z h
    rcases hrt q a z h with o | ⟨e1, e2⟩
    · obtain ⟨p', b', s', hq, hp', hx'⟩ := hI.rtx q a z o
      exact ⟨p', b', s', hq, lift _ _ hp', hx'⟩
    · exact ⟨p, b, s, e1, lift _ _ hp, e2.trans hx⟩
  · intro a z p' s' ht hn
    have ht' : (a, z) ∈ S.tF := by rw [← htF]; exact ht
    rcases (hN p' s').mp hn with o | ⟨_, d1⟩
    · exact hI.tfc a z p' s' ht' o
    · intro hc
      rw [d1] at hc
      exact hd (by rw [← hc]; exact tF_cap_in ht')

private theorem inv_move {β : Type} {R C : Nat} {ops : AbsorbOps β R} {s0 : SpSt R C}
    {τ : PermTable R C} {S S' : SimSt β R C} (hI : SInv ops s0 τ S)
    (hN : ∀ p s, nodeAt s0 S' p s ↔ nodeAt s0 S p s) (htF : S'.tF = S.tF)
    (hrt : ∀ q x z, (q, x, z) ∈ S'.rt →
      ∃ p b s, q = p ++ [b] ∧ nodeAt s0 S p s ∧ x = (ops.xorB s.1 b, s.2)) :
    SInv ops s0 τ S' := by
  refine ⟨hI.fn, hI.inj, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p s s' h1 h2
    exact hI.nfn p s s' ((hN _ _).mp h1) ((hN _ _).mp h2)
  · intro p p' s s' h1 h2
    exact hI.ncap p p' s s' ((hN _ _).mp h1) ((hN _ _).mp h2)
  · intro a z
    constructor
    · intro h
      rcases (hI.edge a z).mp h with ht | ⟨p, b, s, hp, hq, hx⟩
      · exact Or.inl (by rw [htF]; exact ht)
      · exact Or.inr ⟨p, b, s, (hN _ _).mpr hp, (hN _ _).mpr hq, hx⟩
    · intro h
      rcases h with ht | ⟨p, b, s, hp, hq, hx⟩
      · exact (hI.edge a z).mpr (Or.inl (by rw [← htF]; exact ht))
      · exact (hI.edge a z).mpr (Or.inr ⟨p, b, s, (hN _ _).mp hp, (hN _ _).mp hq, hx⟩)
  · intro p b z h
    obtain ⟨s, hs⟩ := hI.par p b z ((hN _ _).mp h)
    exact ⟨s, (hN _ _).mpr hs⟩
  · intro q x z h
    obtain ⟨p, b, s, hq, hp, hx⟩ := hrt q x z h
    exact ⟨p, b, s, hq, (hN _ _).mpr hp, hx⟩
  · intro a z p s ht hn
    exact hI.tfc a z p s (by rw [← htF]; exact ht) ((hN _ _).mp hn)

private theorem inv_add_tF {β : Type} {R C : Nat} {ops : AbsorbOps β R} {s0 : SpSt R C}
    {τ : PermTable R C} {S : SimSt β R C} (hI : SInv ops s0 τ S) {x z : SpSt R C}
    (hx : ∀ z', (x, z') ∉ τ) (hz : ∀ x', (x', z) ∉ τ)
    (hc : ∀ p s, nodeAt s0 S p s → x.2 ≠ s.2) :
    SInv ops s0 ((x, z) :: τ) { S with tF := (x, z) :: S.tF } := by
  refine ⟨?_, ?_, hI.nfn, hI.ncap, ?_, hI.par, hI.rtx, ?_⟩
  · intro a w w' h1 h2
    rcases List.mem_cons.mp h1 with e1 | m1
    · rcases List.mem_cons.mp h2 with e2 | m2
      · exact ((Prod.mk.inj e1).2).trans ((Prod.mk.inj e2).2).symm
      · have ha : a = x := (Prod.mk.inj e1).1
        rw [ha] at m2
        exact absurd m2 (hx w')
    · rcases List.mem_cons.mp h2 with e2 | m2
      · have ha : a = x := (Prod.mk.inj e2).1
        rw [ha] at m1
        exact absurd m1 (hx w)
      · exact hI.fn a w w' m1 m2
  · intro a a' w h1 h2
    rcases List.mem_cons.mp h1 with e1 | m1
    · rcases List.mem_cons.mp h2 with e2 | m2
      · exact ((Prod.mk.inj e1).1).trans ((Prod.mk.inj e2).1).symm
      · have hw : w = z := (Prod.mk.inj e1).2
        rw [hw] at m2
        exact absurd m2 (hz a')
    · rcases List.mem_cons.mp h2 with e2 | m2
      · have hw : w = z := (Prod.mk.inj e2).2
        rw [hw] at m1
        exact absurd m1 (hz a)
      · exact hI.inj a a' w m1 m2
  · intro a w
    constructor
    · intro h
      rcases List.mem_cons.mp h with e | m
      · exact Or.inl (by rw [e]; exact List.mem_cons_self)
      · rcases (hI.edge a w).mp m with ht | hn
        · exact Or.inl (List.mem_cons_of_mem _ ht)
        · exact Or.inr hn
    · intro h
      rcases h with ht | hn
      · rcases List.mem_cons.mp ht with e | m
        · rw [e]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ ((hI.edge a w).mpr (Or.inl m))
      · exact List.mem_cons_of_mem _ ((hI.edge a w).mpr (Or.inr hn))
  · intro a w p s ht hn
    rcases List.mem_cons.mp ht with e | m
    · have ha : a = x := (Prod.mk.inj e).1
      rw [ha]
      exact hc p s hn
    · exact hI.tfc a w p s m hn

private theorem node_add_tH {β : Type} {R C : Nat} (s0 : SpSt R C) (S : SimSt β R C)
    (q : List β) (d : SpSt R C) (p : List β) (s : SpSt R C) :
    nodeAt s0 { S with tH := (q, d.1, d.2) :: S.tH } p s ↔
      (nodeAt s0 S p s ∨ (p = q ∧ s = d)) := by
  constructor
  · intro h
    rcases h with h0 | ⟨x, hx⟩ | ht
    · exact Or.inl (Or.inl h0)
    · exact Or.inl (Or.inr (Or.inl ⟨x, hx⟩))
    · rcases List.mem_cons.mp ht with e | m
      · have e1 : p = q := (Prod.mk.inj e).1
        have e2 : s.1 = d.1 := (Prod.mk.inj (Prod.mk.inj e).2).1
        have e3 : s.2 = d.2 := (Prod.mk.inj (Prod.mk.inj e).2).2
        exact Or.inr ⟨e1, Prod.ext e2 e3⟩
      · exact Or.inl (Or.inr (Or.inr m))
  · intro h
    rcases h with (h0 | ⟨x, hx⟩ | ht) | ⟨e1, e2⟩
    · exact Or.inl h0
    · exact Or.inr (Or.inl ⟨x, hx⟩)
    · exact Or.inr (Or.inr (List.mem_cons_of_mem _ ht))
    · rw [e1, e2]
      exact Or.inr (Or.inr List.mem_cons_self)

private theorem node_add_rt {β : Type} {R C : Nat} (s0 : SpSt R C) (S : SimSt β R C)
    (q : List β) (x d : SpSt R C) (p : List β) (s : SpSt R C) :
    nodeAt s0 { S with rt := (q, x, d) :: S.rt } p s ↔
      (nodeAt s0 S p s ∨ (p = q ∧ s = d)) := by
  constructor
  · intro h
    rcases h with h0 | ⟨x', hx'⟩ | ht
    · exact Or.inl (Or.inl h0)
    · rcases List.mem_cons.mp hx' with e | m
      · exact Or.inr ⟨(Prod.mk.inj e).1, (Prod.mk.inj (Prod.mk.inj e).2).2⟩
      · exact Or.inl (Or.inr (Or.inl ⟨x', m⟩))
    · exact Or.inl (Or.inr (Or.inr ht))
  · intro h
    rcases h with (h0 | ⟨x', hx'⟩ | ht) | ⟨e1, e2⟩
    · exact Or.inl h0
    · exact Or.inr (Or.inl ⟨x', List.mem_cons_of_mem _ hx'⟩)
    · exact Or.inr (Or.inr ht)
    · rw [e1, e2]
      exact Or.inr (Or.inl ⟨x, List.mem_cons_self⟩)

private theorem node_move {β : Type} [DecidableEq β] {R C : Nat} (s0 : SpSt R C)
    {S : SimSt β R C} {q : List β} (x : SpSt R C) {e : List β × Fin R × Fin C}
    (hfind : S.tH.find? (fun e => decide (e.1 = q)) = some e) (p : List β) (s : SpSt R C) :
    nodeAt s0 { S with rt := (q, x, (e.2.1, e.2.2)) :: S.rt,
                       tH := S.tH.eraseP (fun e => decide (e.1 = q)) } p s ↔
      nodeAt s0 S p s := by
  have hm := List.mem_of_find?_eq_some hfind
  have h10 := List.find?_some hfind
  have h1 : e.1 = q := of_decide_eq_true h10
  constructor
  · intro h
    rcases h with h0 | ⟨x', hx'⟩ | ht
    · exact Or.inl h0
    · rcases List.mem_cons.mp hx' with e1 | m
      · have ep : p = q := (Prod.mk.inj e1).1
        have es : s = (e.2.1, e.2.2) := (Prod.mk.inj (Prod.mk.inj e1).2).2
        refine Or.inr (Or.inr ?_)
        rw [ep, es, ← h1]
        exact hm
      · exact Or.inr (Or.inl ⟨x', m⟩)
    · exact Or.inr (Or.inr (List.mem_of_mem_eraseP ht))
  · intro h
    rcases h with h0 | ⟨x', hx'⟩ | ht
    · exact Or.inl h0
    · exact Or.inr (Or.inl ⟨x', List.mem_cons_of_mem _ hx'⟩)
    · rcases mem_or_eraseP _ _ _ _ hfind ht with e1 | m
      · have ep0 := congrArg Prod.fst e1
        have ep : p = q := ep0.trans h1
        have es0 := congrArg (fun t : List β × Fin R × Fin C => (t.2.1, t.2.2)) e1
        have es : s = (e.2.1, e.2.2) := es0
        refine Or.inr (Or.inl ⟨x, ?_⟩)
        rw [ep, es]
        exact List.mem_cons_self
      · exact Or.inr (Or.inr m)

/-! ### Reading the ideal state -/

private theorem node_of_lookup {β : Type} [DecidableEq β] {R C : Nat} (s0 : SpSt R C)
    {S : SimSt β R C} {q : List β} {r : Fin R} (h : roLookup S q = some r) :
    ∃ s, nodeAt s0 S q s ∧ s.1 = r := by
  unfold roLookup at h
  split at h
  · rename_i e he
    have hm := List.mem_of_find?_eq_some he
    have h10 := List.find?_some he
    have h1 : e.1 = q := of_decide_eq_true h10
    refine ⟨e.2.2, Or.inr (Or.inl ⟨e.2.1, ?_⟩), Option.some.inj h⟩
    rw [← h1]
    exact hm
  · cases hf : S.tH.find? (fun e => decide (e.1 = q)) with
    | none => rw [hf] at h; cases h
    | some e =>
      rw [hf] at h
      have hm := List.mem_of_find?_eq_some hf
      have h10 := List.find?_some hf
      have h1 : e.1 = q := of_decide_eq_true h10
      refine ⟨(e.2.1, e.2.2), Or.inr (Or.inr ?_), Option.some.inj h⟩
      rw [← h1]
      exact hm

private theorem no_node_of_lookup {β : Type} [DecidableEq β] {R C : Nat} (s0 : SpSt R C)
    {S : SimSt β R C} {q : List β} (hq : q ≠ []) (h : roLookup S q = none) :
    ∀ s, ¬ nodeAt s0 S q s := by
  unfold roLookup at h
  split at h
  · cases h
  · rename_i hr
    intro s hn
    rcases hn with ⟨h0, _⟩ | ⟨x, hx⟩ | ht
    · exact hq h0
    · exact List.find?_eq_none.mp hr _ hx (decide_eq_true rfl)
    · cases hf : S.tH.find? (fun e => decide (e.1 = q)) with
      | none => exact List.find?_eq_none.mp hf _ ht (decide_eq_true rfl)
      | some e => rw [hf] at h; cases h

private theorem known_fwd_mem {β : Type} {R C : Nat} {ops : AbsorbOps β R} {s0 : SpSt R C}
    {τ : PermTable R C} {S : SimSt β R C} (hI : SInv ops s0 τ S) {x z : SpSt R C}
    (h : simFwdKnown S x = some z) : (x, z) ∈ τ := by
  unfold simFwdKnown at h
  split at h
  · rename_i e he
    have hm := List.mem_of_find?_eq_some he
    have h10 := List.find?_some he
    have h1 : e.2.1 = x := of_decide_eq_true h10
    have h2 : e.2.2 = z := Option.some.inj h
    obtain ⟨p, b, s, hq, hp, hx⟩ := hI.rtx e.1 e.2.1 e.2.2 hm
    refine (hI.edge x z).mpr (Or.inr ⟨p, b, s, hp, ?_, h1.symm.trans hx⟩)
    rw [← hq, ← h2]
    exact Or.inr (Or.inl ⟨e.2.1, hm⟩)
  · cases hf : S.tF.find? (fun e => decide (e.1 = x)) with
    | none => rw [hf] at h; cases h
    | some e =>
      rw [hf] at h
      have h2 : e.2 = z := Option.some.inj h
      have h10 := List.find?_some hf
      have h1 : e.1 = x := of_decide_eq_true h10
      have hm := List.mem_of_find?_eq_some hf
      refine (hI.edge x z).mpr (Or.inl ?_)
      rw [← h1, ← h2]
      exact hm

private theorem known_inv_mem {β : Type} {R C : Nat} {ops : AbsorbOps β R} {s0 : SpSt R C}
    {τ : PermTable R C} {S : SimSt β R C} (hI : SInv ops s0 τ S) {x y : SpSt R C}
    (h : simInvKnown S y = some x) : (x, y) ∈ τ := by
  unfold simInvKnown at h
  split at h
  · rename_i e he
    have hm := List.mem_of_find?_eq_some he
    have h10 := List.find?_some he
    have h1 : e.2.2 = y := of_decide_eq_true h10
    have h2 : e.2.1 = x := Option.some.inj h
    obtain ⟨p, b, s, hq, hp, hx⟩ := hI.rtx e.1 e.2.1 e.2.2 hm
    refine (hI.edge x y).mpr (Or.inr ⟨p, b, s, hp, ?_, h2.symm.trans hx⟩)
    rw [← hq, ← h1]
    exact Or.inr (Or.inl ⟨e.2.1, hm⟩)
  · cases hf : S.tF.find? (fun e => decide (e.2 = y)) with
    | none => rw [hf] at h; cases h
    | some e =>
      rw [hf] at h
      have h2 : e.1 = x := Option.some.inj h
      have h10 := List.find?_some hf
      have h1 : e.2 = y := of_decide_eq_true h10
      have hm := List.mem_of_find?_eq_some hf
      refine (hI.edge x y).mpr (Or.inl ?_)
      rw [← h1, ← h2]
      exact hm

private theorem fwd_known_of_rt {β : Type} {R C : Nat} {S : SimSt β R C} {q : List β}
    {x z : SpSt R C} (hm : (q, x, z) ∈ S.rt) (hk : simFwdKnown S x = none) : False := by
  unfold simFwdKnown at hk
  split at hk
  · cases hk
  · rename_i he
    exact List.find?_eq_none.mp he _ hm (decide_eq_true rfl)

private theorem fwd_known_of_tF {β : Type} {R C : Nat} {S : SimSt β R C}
    {x z : SpSt R C} (hm : (x, z) ∈ S.tF) (hk : simFwdKnown S x = none) : False := by
  unfold simFwdKnown at hk
  split at hk
  · cases hk
  · cases hf : S.tF.find? (fun e => decide (e.1 = x)) with
    | none => exact List.find?_eq_none.mp hf _ hm (decide_eq_true rfl)
    | some e => rw [hf] at hk; cases hk

private theorem inv_known_of_rt {β : Type} {R C : Nat} {S : SimSt β R C} {q : List β}
    {x y : SpSt R C} (hm : (q, x, y) ∈ S.rt) (hk : simInvKnown S y = none) : False := by
  unfold simInvKnown at hk
  split at hk
  · cases hk
  · rename_i he
    exact List.find?_eq_none.mp he _ hm (decide_eq_true rfl)

private theorem inv_known_of_tF {β : Type} {R C : Nat} {S : SimSt β R C}
    {x y : SpSt R C} (hm : (x, y) ∈ S.tF) (hk : simInvKnown S y = none) : False := by
  unfold simInvKnown at hk
  split at hk
  · cases hk
  · cases hf : S.tF.find? (fun e => decide (e.2 = y)) with
    | none => exact List.find?_eq_none.mp hf _ hm (decide_eq_true rfl)
    | some e => rw [hf] at hk; cases hk

private theorem root_spec {β : Type} {R C : Nat} {s0 : SpSt R C} {S : SimSt β R C}
    {c : Fin C} {p : List β} {t : SpSt R C} (h : simFindRoot s0 S c = some (p, t)) :
    nodeAt s0 S p t ∧ t.2 = c := by
  unfold simFindRoot at h
  split at h
  · rename_i hc
    cases h
    exact ⟨Or.inl ⟨rfl, rfl⟩, hc.symm⟩
  · cases hf : S.rt.find? (fun e => decide (e.2.2.2 = c)) with
    | none => rw [hf] at h; cases h
    | some e =>
      rw [hf] at h
      have h' : some (e.1, e.2.2) = some (p, t) := h
      cases h'
      have hd0 := List.find?_some hf
      exact ⟨Or.inr (Or.inl ⟨e.2.1, List.mem_of_find?_eq_some hf⟩), of_decide_eq_true hd0⟩

private theorem root_none {β : Type} {R C : Nat} {s0 : SpSt R C} {S : SimSt β R C}
    {c : Fin C} (h : simFindRoot s0 S c = none) :
    c ≠ s0.2 ∧ ∀ p x z, (p, x, z) ∈ S.rt → z.2 ≠ c := by
  unfold simFindRoot at h
  split at h
  · cases h
  · rename_i hc
    refine ⟨hc, ?_⟩
    cases hf : S.rt.find? (fun e => decide (e.2.2.2 = c)) with
    | none =>
      intro p x z hm hz
      exact List.find?_eq_none.mp hf _ hm (decide_eq_true hz)
    | some e => rw [hf] at h; cases h

private theorem unrooted_caps {β : Type} {R C : Nat} {s0 : SpSt R C} {S : SimSt β R C}
    {c : Fin C} (hne : c ≠ s0.2) (hrt : ∀ p x z, (p, x, z) ∈ S.rt → z.2 ≠ c)
    (hh : c ∉ hidCaps S) : ∀ p s, nodeAt s0 S p s → c ≠ s.2 := by
  intro p s hn hc
  rcases hn with ⟨_, h0⟩ | ⟨x', hx'⟩ | ht
  · rw [h0] at hc
    exact hne hc
  · exact hrt _ _ _ hx' hc.symm
  · exact hh (by rw [hc]; exact List.mem_map.mpr ⟨_, ht, rfl⟩)

/-! ### One oracle call -/

private theorem roStep_sim {β : Type} [DecidableEq β] {R C : Nat} {ops : AbsorbOps β R}
    {s0 : SpSt R C} {τ : PermTable R C} {S : SimSt β R C} (hI : SInv ops s0 τ S) {p : List β}
    {s : SpSt R C} (hp : nodeAt s0 S p s) (b : β) {ω : List (SpSt R C)}
    {res : Option (Fin R × SimSt β R C × List (SpSt R C))}
    (h : roStep s0 S ω (p ++ [b]) = (res, false)) :
    Coupled ops s0 (fun r s' S' => s'.1 = r ∧ nodeAt s0 S' (p ++ [b]) s') res
      (realFwd τ ω (ops.xorB s.1 b, s.2)) := by
  unfold roStep at h
  split at h
  · rename_i r hl
    obtain ⟨h1, _⟩ := Prod.mk.inj h
    subst h1
    obtain ⟨s', hs', hr⟩ := node_of_lookup s0 hl
    have hmem : ((ops.xorB s.1 b, s.2), s') ∈ τ :=
      (hI.edge _ _).mpr (Or.inr ⟨p, b, s, hp, hs', rfl⟩)
    refine ⟨(fun h => nomatch h), fun a S' ω' h => ?_⟩
    cases h
    exact ⟨s', τ, realFwd_known hI.fn hmem ω, ⟨hr, hs'⟩, hI⟩
  · rename_i hl
    have hf := no_node_of_lookup s0 (snoc_ne_nil p b) hl
    have hxin := fresh_in hI hp rfl hf
    split at h
    · obtain ⟨h1, _⟩ := Prod.mk.inj h
      subst h1
      exact ⟨fun _ => realFwd_nil hxin, fun a S' ω' h => nomatch h⟩
    · rename_i d ω'
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      subst h1
      have hd : d.2 ∉ capsOf s0 S := capIn_eq_false h2
      refine ⟨(fun h => nomatch h), fun a S' ω'' h => ?_⟩
      cases h
      exact ⟨d, _, realFwd_fresh hxin (fun x' hx' => hd (out_cap hI hx')) ω',
        ⟨rfl, Or.inr (Or.inr List.mem_cons_self)⟩,
        inv_add_node hI hp rfl hf hd (node_add_tH s0 S _ d) rfl (fun q x' z hq => Or.inl hq)⟩

private theorem roWalk_true {β : Type} [DecidableEq β] {R C : Nat} (s0 : SpSt R C) :
    ∀ (m : List β) (S : SimSt β R C) (ω : List (SpSt R C)) (p : List β) (r : Fin R),
      (roWalk s0 S ω p r true m).2 = true := by
  intro m
  induction m with
  | nil => intro S ω p r; rfl
  | cons b m ih =>
    intro S ω p r
    simp only [roWalk]
    rcases roStep s0 S ω (p ++ [b]) with ⟨_ | ⟨r', S', ω'⟩, bd⟩
    · rfl
    · exact ih S' ω' (p ++ [b]) r'

private theorem walk_sim {β : Type} [DecidableEq β] {R C : Nat} (ops : AbsorbOps β R)
    (s0 : SpSt R C) : ∀ (m : List β) (τ : PermTable R C) (S : SimSt β R C)
      (ω : List (SpSt R C)) (p : List β) (s : SpSt R C)
      (res : Option (Fin R × SimSt β R C × List (SpSt R C))),
      SInv ops s0 τ S → nodeAt s0 S p s → roWalk s0 S ω p s.1 false m = (res, false) →
      Coupled ops s0 (fun r s' _ => s'.1 = r) res (realWalk ops τ ω s m) := by
  intro m
  induction m with
  | nil =>
    intro τ S ω p s res hI _ h
    simp only [roWalk] at h
    obtain ⟨h1, _⟩ := Prod.mk.inj h
    subst h1
    refine ⟨(fun h => nomatch h), fun a S' ω' h => ?_⟩
    cases h
    exact ⟨s, τ, rfl, rfl, hI⟩
  | cons b m ih =>
    intro τ S ω p s res hI hp h
    simp only [roWalk] at h
    rcases hst : roStep s0 S ω (p ++ [b]) with ⟨_ | ⟨r', S', ω'⟩, bd⟩
    · rw [hst] at h
      cases bd with
      | true =>
        have h' : ((none : Option (Fin R × SimSt β R C × List (SpSt R C))), true) =
            (res, false) := h
        have h3 : true = false := (Prod.mk.inj h').2
        exact absurd h3 (by decide)
      | false =>
        have h' : ((none : Option (Fin R × SimSt β R C × List (SpSt R C))), false) =
            (res, false) := h
        obtain ⟨h1, _⟩ := Prod.mk.inj h'
        subst h1
        have hc := roStep_sim hI hp b hst
        refine ⟨fun _ => ?_, fun a S' ω' h => nomatch h⟩
        simp only [realWalk, hc.1 rfl]
    · rw [hst] at h
      cases bd with
      | true =>
        have h' : roWalk s0 S' ω' (p ++ [b]) r' true m = (res, false) := h
        have h2 := roWalk_true s0 m S' ω' (p ++ [b]) r'
        rw [h'] at h2
        have h3 : false = true := h2
        exact absurd h3 (by decide)
      | false =>
        have h' : roWalk s0 S' ω' (p ++ [b]) r' false m = (res, false) := h
        obtain ⟨s', τ', hreal, ⟨hr, hn⟩, hI'⟩ := (roStep_sim hI hp b hst).2 r' S' ω' rfl
        subst hr
        have hrec := ih τ' S' ω' (p ++ [b]) s' res hI' hn h'
        simp only [realWalk, hreal]
        exact hrec

private theorem fwd_sim {β : Type} [DecidableEq β] {R C : Nat} {ops : AbsorbOps β R}
    {s0 : SpSt R C} {τ : PermTable R C} {S : SimSt β R C} (hI : SInv ops s0 τ S)
    {ω : List (SpSt R C)} {x : SpSt R C}
    {res : Option (SpSt R C × SimSt β R C × List (SpSt R C))}
    (h : spongeSimFwd ops s0 S ω x = (res, false)) :
    Coupled ops s0 (fun z z' _ => z' = z) res (realFwd τ ω x) := by
  unfold spongeSimFwd at h
  split at h
  · rename_i z hk
    obtain ⟨h1, _⟩ := Prod.mk.inj h
    subst h1
    refine ⟨(fun h => nomatch h), fun a S' ω' h => ?_⟩
    cases h
    exact ⟨z, τ, realFwd_known hI.fn (known_fwd_mem hI hk) ω, rfl, hI⟩
  · rename_i hk
    split at h
    · rename_i p t hroot
      obtain ⟨hp, hcap⟩ := root_spec hroot
      have hx : x = (ops.xorB t.1 (ops.diffB t.1 x.1), t.2) := by
        rw [ops.xor_diff, hcap]
      split at h
      · rename_i e he
        obtain ⟨h1, _⟩ := Prod.mk.inj h
        subst h1
        have hm := List.mem_of_find?_eq_some he
        have h10 := List.find?_some he
        have h1 : e.1 = p ++ [ops.diffB t.1 x.1] := of_decide_eq_true h10
        have hq : nodeAt s0 S (p ++ [ops.diffB t.1 x.1]) (e.2.1, e.2.2) :=
          Or.inr (Or.inr (by rw [← h1]; exact hm))
        have hmem : (x, (e.2.1, e.2.2)) ∈ τ :=
          (hI.edge _ _).mpr (Or.inr ⟨p, _, t, hp, hq, hx⟩)
        refine ⟨(fun h => nomatch h), fun a S' ω' h => ?_⟩
        cases h
        refine ⟨_, τ, realFwd_known hI.fn hmem ω, rfl,
          inv_move hI (node_move s0 x he) rfl (fun q x' z hq' => ?_)⟩
        rcases List.mem_cons.mp hq' with e1 | m
        · exact ⟨p, _, t, (Prod.mk.inj e1).1, hp,
            ((Prod.mk.inj (Prod.mk.inj e1).2).1).trans hx⟩
        · exact hI.rtx q x' z m
      · rename_i he
        have hf : ∀ s', ¬ nodeAt s0 S (p ++ [ops.diffB t.1 x.1]) s' := by
          intro s' hn
          rcases hn with ⟨h0, _⟩ | ⟨x', hx'⟩ | ht
          · exact snoc_ne_nil _ _ h0
          · obtain ⟨p', b', s'', hq, hp', hxx⟩ := hI.rtx _ _ _ hx'
            obtain ⟨e1, e2⟩ := List.append_inj' hq rfl
            have e3 : ops.diffB t.1 x.1 = b' := (List.cons.inj e2).1
            rw [← e1] at hp'
            have e4 : t = s'' := hI.nfn p t s'' hp hp'
            have e5 : x' = x := by rw [hxx, ← e3, ← e4]; exact hx.symm
            rw [e5] at hx'
            exact fwd_known_of_rt hx' hk
          · exact List.find?_eq_none.mp he _ ht (decide_eq_true rfl)
        split at h
        · obtain ⟨h1, _⟩ := Prod.mk.inj h
          subst h1
          exact ⟨fun _ => realFwd_nil (fresh_in hI hp hx hf), fun a S' ω' h => nomatch h⟩
        · rename_i d ω'
          obtain ⟨h1, h2⟩ := Prod.mk.inj h
          subst h1
          have hd : d.2 ∉ capsOf s0 S := capIn_eq_false h2
          refine ⟨(fun h => nomatch h), fun a S' ω'' h => ?_⟩
          cases h
          refine ⟨d, _, realFwd_fresh (fresh_in hI hp hx hf)
            (fun x' hx' => hd (out_cap hI hx')) ω', rfl,
            inv_add_node hI hp hx hf hd (node_add_rt s0 S _ x d) rfl (fun q x' z hq => ?_)⟩
          rcases List.mem_cons.mp hq with e1 | m
          · exact Or.inr ⟨(Prod.mk.inj e1).1, (Prod.mk.inj (Prod.mk.inj e1).2).1⟩
          · exact Or.inl m
    · rename_i hroot
      obtain ⟨hne, hrt⟩ := root_none hroot
      have hxin_of : x.2 ∉ hidCaps S → ∀ z, (x, z) ∉ τ := by
        intro hh z hz
        rcases (hI.edge x z).mp hz with ht | ⟨p, b, s, hp, _, hx⟩
        · exact fwd_known_of_tF ht hk
        · exact unrooted_caps hne hrt hh p s hp (by rw [hx])
      split at h
      · obtain ⟨h1, h2⟩ := Prod.mk.inj h
        subst h1
        exact ⟨fun _ => realFwd_nil (hxin_of (capIn_eq_false h2)),
          fun a S' ω' h => nomatch h⟩
      · rename_i d ω'
        obtain ⟨h1, h2⟩ := Prod.mk.inj h
        subst h1
        obtain ⟨h3, h4⟩ := Bool.or_eq_false_iff.mp h2
        have hh : x.2 ∉ hidCaps S := capIn_eq_false h3
        have hd : d.2 ∉ capsOf s0 S := capIn_eq_false h4
        refine ⟨(fun h => nomatch h), fun a S' ω'' h => ?_⟩
        cases h
        exact ⟨d, _, realFwd_fresh (hxin_of hh) (fun x' hx' => hd (out_cap hI hx')) ω', rfl,
          inv_add_tF hI (hxin_of hh) (fun x' hx' => hd (out_cap hI hx'))
            (unrooted_caps hne hrt hh)⟩

private theorem inv_sim {β : Type} {R C : Nat} {ops : AbsorbOps β R}
    {s0 : SpSt R C} {τ : PermTable R C} {S : SimSt β R C} (hI : SInv ops s0 τ S)
    {ω : List (SpSt R C)} {y : SpSt R C}
    {res : Option (SpSt R C × SimSt β R C × List (SpSt R C))}
    (h : spongeSimInv s0 S ω y = (res, false)) :
    Coupled ops s0 (fun x x' _ => x' = x) res (realInv τ ω y) := by
  unfold spongeSimInv at h
  split at h
  · rename_i x hk
    obtain ⟨h1, _⟩ := Prod.mk.inj h
    subst h1
    refine ⟨(fun h => nomatch h), fun a S' ω' h => ?_⟩
    cases h
    exact ⟨x, τ, realInv_known hI.inj (known_inv_mem hI hk) ω, rfl, hI⟩
  · rename_i hk
    have hyout_of : y.2 ∉ hidCaps S → ∀ x', (x', y) ∉ τ := by
      intro hh x' hx'
      rcases (hI.edge x' y).mp hx' with ht | ⟨p, b, s, _, hq, _⟩
      · exact inv_known_of_tF ht hk
      · rcases hq with ⟨h0, _⟩ | ⟨x'', hx''⟩ | ht
        · exact snoc_ne_nil _ _ h0
        · exact inv_known_of_rt hx'' hk
        · exact hh (List.mem_map.mpr ⟨_, ht, rfl⟩)
    split at h
    · obtain ⟨h1, h2⟩ := Prod.mk.inj h
      subst h1
      exact ⟨fun _ => realInv_nil (hyout_of (capIn_eq_false h2)),
        fun a S' ω' h => nomatch h⟩
    · rename_i d ω'
      obtain ⟨h1, h2⟩ := Prod.mk.inj h
      subst h1
      obtain ⟨h3, h4⟩ := Bool.or_eq_false_iff.mp h2
      have hh : y.2 ∉ hidCaps S := capIn_eq_false h3
      have hd : d.2 ∉ capsOf s0 S := capIn_eq_false h4
      have hdin : ∀ z, (d, z) ∉ τ := fun z hz => hd (in_cap hI hz)
      refine ⟨(fun h => nomatch h), fun a S' ω'' h => ?_⟩
      cases h
      exact ⟨d, _, realInv_fresh (hyout_of hh) hdin ω', rfl,
        inv_add_tF hI hdin (hyout_of hh)
          (fun p s hn hc => hd (by rw [hc]; exact node_cap hn))⟩

/-! ### The whole interaction -/

private theorem inv_init {β : Type} {R C : Nat} (ops : AbsorbOps β R) (s0 : SpSt R C) :
    SInv ops s0 [] (SimSt.init β R C) := by
  have hnode : ∀ (p : List β) (s : SpSt R C), nodeAt s0 (SimSt.init β R C) p s →
      p = [] ∧ s = s0 := by
    intro p s h
    rcases h with h0 | ⟨x, hx⟩ | ht
    · exact h0
    · exact absurd hx List.not_mem_nil
    · exact absurd ht List.not_mem_nil
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x z z' h _
    exact absurd h List.not_mem_nil
  · intro x x' z h _
    exact absurd h List.not_mem_nil
  · intro p s s' h1 h2
    exact (hnode p s h1).2.trans (hnode p s' h2).2.symm
  · intro p p' s s' h1 h2 _
    exact (hnode p s h1).1.trans (hnode p' s' h2).1.symm
  · intro x z
    constructor
    · intro h
      exact absurd h List.not_mem_nil
    · intro h
      rcases h with ht | ⟨p, b, s, _, hq, _⟩
      · exact absurd ht List.not_mem_nil
      · exact absurd (hnode _ _ hq).1 (snoc_ne_nil p b)
  · intro p b z h
    exact absurd (hnode _ _ h).1 (snoc_ne_nil p b)
  · intro q x z h
    exact absurd h List.not_mem_nil
  · intro x z p s h _
    exact absurd h List.not_mem_nil

private theorem views_gen {β : Type} [DecidableEq β] {R C : Nat} {Out : Type}
    (ops : AbsorbOps β R) (s0 : SpSt R C) : ∀ (A : SpAdv β R C Out) (τ : PermTable R C)
      (S : SimSt β R C) (ω : List (SpSt R C)), SInv ops s0 τ S →
      (idealRun ops s0 A S ω).2 = false →
      realRun ops s0 A τ ω = (idealRun ops s0 A S ω).1 := by
  intro A
  induction A with
  | done o => intro τ S ω _ _; rfl
  | node m k ih =>
    intro τ S ω hI h
    rcases hw : roWalk s0 S ω [] s0.1 false m with ⟨_ | ⟨r, S', ω'⟩, bd⟩
    · simp only [idealRun, hw] at h ⊢
      subst h
      have hc := walk_sim ops s0 m τ S ω [] s0 none hI (Or.inl ⟨rfl, rfl⟩) hw
      simp only [realRun, hc.1 rfl]
    · simp only [idealRun, hw] at h ⊢
      obtain ⟨h1, h2⟩ := Bool.or_eq_false_iff.mp h
      subst h1
      obtain ⟨s', τ', hreal, hr, hI'⟩ :=
        (walk_sim ops s0 m τ S ω [] s0 _ hI (Or.inl ⟨rfl, rfl⟩) hw).2 r S' ω' rfl
      subst hr
      simp only [realRun, hreal]
      exact ih s'.1 τ' S' ω' hI' h2
  | fwd x k ih =>
    intro τ S ω hI h
    have hsim : spongeSimulator ops s0 S ω false x = spongeSimFwd ops s0 S ω x := rfl
    rcases hw : spongeSimFwd ops s0 S ω x with ⟨_ | ⟨z, S', ω'⟩, bd⟩
    · simp only [idealRun, hsim, hw] at h ⊢
      subst h
      have hc := fwd_sim (τ := τ) hI hw
      simp only [realRun, hc.1 rfl]
    · simp only [idealRun, hsim, hw] at h ⊢
      obtain ⟨h1, h2⟩ := Bool.or_eq_false_iff.mp h
      subst h1
      obtain ⟨z', τ', hreal, hr, hI'⟩ := (fwd_sim (τ := τ) hI hw).2 z S' ω' rfl
      subst hr
      simp only [realRun, hreal]
      exact ih z' τ' S' ω' hI' h2
  | inv y k ih =>
    intro τ S ω hI h
    have hsim : spongeSimulator ops s0 S ω true y = spongeSimInv s0 S ω y := rfl
    rcases hw : spongeSimInv s0 S ω y with ⟨_ | ⟨x, S', ω'⟩, bd⟩
    · simp only [idealRun, hsim, hw] at h ⊢
      subst h
      have hc := inv_sim (ops := ops) (τ := τ) hI hw
      simp only [realRun, hc.1 rfl]
    · simp only [idealRun, hsim, hw] at h ⊢
      obtain ⟨h1, h2⟩ := Bool.or_eq_false_iff.mp h
      subst h1
      obtain ⟨x', τ', hreal, hr, hI'⟩ := (inv_sim (ops := ops) (τ := τ) hI hw).2 x S' ω' rfl
      subst hr
      simp only [realRun, hreal]
      exact ih x' τ' S' ω' hI' h2

/-- **Identical views outside the bad event.** On every coin list on which the ideal world
    `(RO, sim_π, sim_π⁻¹)` raises no capacity bad event, the real world
    `(sponge^π, π, π⁻¹)` run on the same coins gives the distinguisher the same answers and
    hence the same output (including running out of coins at the same query). -/
theorem sponge_two_way_views_eq {β : Type} [DecidableEq β] {R C : Nat} {Out : Type}
    (ops : AbsorbOps β R) (s0 : SpSt R C) (A : SpAdv β R C Out) (ω : List (SpSt R C))
    (h : (idealRun ops s0 A (SimSt.init β R C) ω).2 = false) :
    realRun ops s0 A [] ω = (idealRun ops s0 A (SimSt.init β R C) ω).1 :=
  views_gen ops s0 A [] (SimSt.init β R C) ω (inv_init ops s0) h


/-! ## §6. The bad event is rare: counting the bad coin lists

The count is taken over the coin list together with the capacity values stored in `tH`
(`sti_sumG` sums over them for a fixed skeleton of paths and rate values): a capacity sampled
by an oracle query is uniform until the simulator roots its path, so hitting it is charged
as a guess. -/

/-! ### Finite sums -/

private theorem sti_sum_ext {m : Nat} {f g : Fin m → Nat} (h : ∀ i, f i = g i) :
    Spec.sampleSum m f = Spec.sampleSum m g :=
  congrArg (Spec.sampleSum m) (funext h)

private theorem sti_sum_le :
    ∀ (m : Nat) (f g : Fin m → Nat), (∀ i, f i ≤ g i) → Spec.sampleSum m f ≤ Spec.sampleSum m g
  | 0, _, _, _ => Nat.le_refl 0
  | m + 1, _, _, h =>
    Nat.add_le_add (h ⟨0, Nat.zero_lt_succ m⟩)
      (sti_sum_le m _ _ (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩))

private theorem sti_sum_add :
    ∀ (m : Nat) (f g : Fin m → Nat),
      Spec.sampleSum m (fun i => f i + g i) = Spec.sampleSum m f + Spec.sampleSum m g
  | 0, _, _ => rfl
  | m + 1, f, g => by
    rw [Spec.sampleSum_succ, Spec.sampleSum_succ, Spec.sampleSum_succ, sti_sum_add m]
    omega

private theorem sti_sum_mul_right :
    ∀ (m : Nat) (f : Fin m → Nat) (c : Nat),
      Spec.sampleSum m (fun i => f i * c) = Spec.sampleSum m f * c
  | 0, _, _ => (Nat.zero_mul _).symm
  | m + 1, f, c => by
    rw [Spec.sampleSum_succ, Spec.sampleSum_succ, sti_sum_mul_right m, Nat.add_mul]

private theorem sti_sum_const :
    ∀ (m c : Nat), Spec.sampleSum m (fun _ => c) = m * c
  | 0, c => (Nat.zero_mul c).symm
  | m + 1, c => by
    rw [Spec.sampleSum_succ, sti_sum_const m, Nat.succ_mul, Nat.add_comm]

private theorem sti_sum_cast {m m' : Nat} (h : m = m') (f : Fin m' → Nat) :
    Spec.sampleSum m (fun i => f ⟨i.1, h ▸ i.2⟩) = Spec.sampleSum m' f := by
  subst h; rfl

private theorem sti_sum_split :
    ∀ (a b : Nat) (f : Fin (a + b) → Nat),
      Spec.sampleSum (a + b) f =
        Spec.sampleSum a (fun i => f ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.le_add_right a b)⟩) +
        Spec.sampleSum b (fun j => f ⟨a + j.1, Nat.add_lt_add_left j.2 a⟩)
  | 0, b, f => by
    simp only [Spec.sampleSum_zero, Nat.zero_add]
    exact sti_sum_cast (Nat.zero_add b) (fun j => f ⟨j.1, by omega⟩)
  | a + 1, b, f => by
    have hCast : Spec.sampleSum ((a + 1) + b) f =
        Spec.sampleSum ((a + b) + 1) (fun i => f ⟨i.1, (Nat.succ_add a b).symm ▸ i.2⟩) := by
      have h := sti_sum_cast (Nat.succ_add a b)
        (fun i : Fin ((a + b) + 1) => f ⟨i.1, (Nat.succ_add a b).symm ▸ i.2⟩)
      exact (sti_sum_ext (fun i => rfl)).trans h
    rw [hCast, Spec.sampleSum_succ, sti_sum_split a b, Spec.sampleSum_succ]
    have hMid : Spec.sampleSum a (fun i : Fin a =>
        f ⟨i.1 + 1, (Nat.succ_add a b).symm ▸ Nat.succ_lt_succ
          (Nat.lt_of_lt_of_le i.2 (Nat.le_add_right a b))⟩) =
        Spec.sampleSum a (fun i : Fin a =>
          f ⟨i.1 + 1, Nat.lt_of_lt_of_le (Nat.succ_lt_succ i.2) (Nat.le_add_right (a + 1) b)⟩) :=
      sti_sum_ext (fun _ => rfl)
    have hRight : Spec.sampleSum b (fun j : Fin b =>
        f ⟨(a + j.1) + 1,
          (Nat.succ_add a b).symm ▸ Nat.succ_lt_succ (Nat.add_lt_add_left j.2 a)⟩) =
        Spec.sampleSum b (fun j : Fin b => f ⟨(a + 1) + j.1, Nat.add_lt_add_left j.2 (a + 1)⟩) :=
      sti_sum_ext (fun j => congrArg f (Fin.ext (by dsimp only; omega)))
    rw [hMid, hRight]
    exact (Nat.add_assoc _ _ _).symm

private theorem sti_pair_lt {a b : Nat} (i : Fin a) (j : Fin b) : i.1 * b + j.1 < a * b :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.2 _)
    (Nat.succ_mul i.1 b ▸ Nat.mul_le_mul_right b i.2)

private theorem sti_pair_div {a b : Nat} (i : Fin a) (j : Fin b) :
    (i.1 * b + j.1) / b = i.1 := by
  rw [Nat.mul_comm i.1 b, Nat.mul_add_div (Nat.lt_of_le_of_lt (Nat.zero_le _) j.2),
    Nat.div_eq_of_lt j.2]
  rfl

private theorem sti_pair_mod {a b : Nat} (i : Fin a) (j : Fin b) :
    (i.1 * b + j.1) % b = j.1 := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.2]

private theorem sti_sum_prod :
    ∀ (m n : Nat) (f : Fin (m * n) → Nat),
      Spec.sampleSum (m * n) f =
        Spec.sampleSum m (fun i => Spec.sampleSum n (fun j =>
          f ⟨i.1 * n + j.1, sti_pair_lt i j⟩))
  | 0, n, f => by
    rw [Spec.sampleSum_zero]
    have h := sti_sum_cast (Nat.zero_mul n)
      (fun i : Fin 0 => f ⟨i.1, (Nat.zero_mul n).symm ▸ i.2⟩)
    exact h
  | m + 1, n, f => by
    have hEq : (m + 1) * n = n + m * n := (Nat.succ_mul m n).trans (Nat.add_comm (m * n) n)
    have hCast : Spec.sampleSum ((m + 1) * n) f =
        Spec.sampleSum (n + m * n) (fun k => f ⟨k.1, hEq.symm ▸ k.2⟩) :=
      sti_sum_cast hEq (fun k : Fin (n + m * n) => f ⟨k.1, hEq.symm ▸ k.2⟩)
    rw [hCast, sti_sum_split n (m * n), sti_sum_prod m n, Spec.sampleSum_succ]
    have hHead : Spec.sampleSum n (fun i : Fin n =>
        f ⟨i.1, hEq.symm ▸ Nat.lt_of_lt_of_le i.2 (Nat.le_add_right n (m * n))⟩) =
        Spec.sampleSum n (fun j : Fin n =>
          f ⟨(⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)).1 * n + j.1,
            sti_pair_lt ⟨0, Nat.zero_lt_succ m⟩ j⟩) :=
      sti_sum_ext (fun j => congrArg f (Fin.ext (by dsimp only; omega)))
    have hTail : Spec.sampleSum m (fun i : Fin m => Spec.sampleSum n (fun j : Fin n =>
        f ⟨n + (i.1 * n + j.1),
          hEq.symm ▸ Nat.add_lt_add_left (sti_pair_lt i j) n⟩)) =
        Spec.sampleSum m (fun i : Fin m => Spec.sampleSum n (fun j : Fin n =>
          f ⟨(i.1 + 1) * n + j.1, sti_pair_lt ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ j⟩)) :=
      sti_sum_ext (fun i => sti_sum_ext (fun j => congrArg f (Fin.ext (by
        dsimp only
        rw [Nat.add_mul, Nat.one_mul]
        omega))))
    rw [hHead, hTail]

private theorem sti_sum_comm :
    ∀ (m n : Nat) (f : Fin m → Fin n → Nat),
      Spec.sampleSum m (fun i => Spec.sampleSum n (fun j => f i j)) =
        Spec.sampleSum n (fun j => Spec.sampleSum m (fun i => f i j))
  | 0, n, f => by
    show 0 = Spec.sampleSum n (fun _ => 0)
    rw [sti_sum_const, Nat.mul_zero]
  | m + 1, n, f => by
    show Spec.sampleSum n (fun j => f ⟨0, Nat.zero_lt_succ m⟩ j) +
        Spec.sampleSum m (fun i => Spec.sampleSum n (fun j => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ j)) =
      Spec.sampleSum n (fun j => f ⟨0, Nat.zero_lt_succ m⟩ j +
        Spec.sampleSum m (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ j))
    rw [sti_sum_comm m n (fun i j => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ j)]
    exact (sti_sum_add n _ _).symm

private theorem sti_sum1_scale (m : Nat) (f : Fin m → Nat) (E D : Nat)
    (h : ∀ i, f i * E ≤ D) : Spec.sampleSum m f * E ≤ m * D :=
  Nat.le_trans (Nat.le_of_eq (sti_sum_mul_right m f E).symm)
    (Nat.le_trans (sti_sum_le m _ _ h) (Nat.le_of_eq (sti_sum_const m D)))

private theorem sti_sum2_scale (R C : Nat) (f : Fin R → Fin C → Nat) (E D : Nat)
    (h : ∀ r c, f r c * E ≤ D) :
    Spec.sampleSum R (fun r => Spec.sampleSum C (fun c => f r c)) * E ≤ R * (C * D) :=
  sti_sum1_scale R _ E (C * D) (fun r => sti_sum1_scale C (fun c => f r c) E D (h r))

private theorem sti_add3_mul (a b c d : Nat) : (a + b + c) * d = a * d + b * d + c * d := by
  rw [Nat.add_mul, Nat.add_mul]

/-! ### Indicators -/

private def sti_ind (b : Bool) : Nat := if b = true then 1 else 0

private theorem sti_ind_le_one (b : Bool) : sti_ind b ≤ 1 := by
  cases b <;> decide

private theorem sti_ind_or2 (a b : Bool) : sti_ind (a || b) ≤ 0 + sti_ind a + sti_ind b := by
  cases a <;> cases b <;> decide

private theorem sti_ind_or3 (a b c : Bool) :
    sti_ind ((a || b) || c) ≤ sti_ind a + sti_ind b + sti_ind c := by
  cases a <;> cases b <;> cases c <;> decide

private theorem sti_eq_count :
    ∀ (n a : Nat), Spec.sampleSum n (fun i => sti_ind (decide (i.1 = a))) ≤ 1
  | 0, _ => Nat.zero_le 1
  | n + 1, 0 => by
    have h : Spec.sampleSum n (fun i : Fin n => sti_ind (decide (i.1 + 1 = 0))) ≤
        Spec.sampleSum n (fun _ => 0) :=
      sti_sum_le n _ _ (fun i => by
        rw [decide_eq_false (Nat.succ_ne_zero i.1)]; exact Nat.le_refl 0)
    rw [sti_sum_const, Nat.mul_zero] at h
    exact Nat.add_le_add (sti_ind_le_one (decide ((0 : Nat) = 0))) h
  | n + 1, a + 1 => by
    have h : Spec.sampleSum n (fun i : Fin n => sti_ind (decide (i.1 + 1 = a + 1))) ≤
        Spec.sampleSum n (fun i => sti_ind (decide (i.1 = a))) :=
      sti_sum_le n _ _ (fun i => by
        by_cases hi : i.1 = a
        · rw [decide_eq_true hi]; exact sti_ind_le_one _
        · rw [decide_eq_false (fun h' => hi (Nat.succ.inj h'))]; exact Nat.zero_le _)
    have h0 : sti_ind (decide ((0 : Nat) = a + 1)) = 0 := by
      rw [decide_eq_false (fun h' => Nat.succ_ne_zero a h'.symm)]; rfl
    have h1 := Nat.add_le_add (Nat.le_of_eq h0) (Nat.le_trans h (sti_eq_count n a))
    exact h1

private theorem sti_ind_deceq {C : Nat} (c v : Fin C) :
    sti_ind (decide (c = v)) ≤ sti_ind (decide (c.1 = v.1)) := by
  by_cases h : c.1 = v.1
  · have e : sti_ind (decide (c.1 = v.1)) = 1 := by rw [decide_eq_true h]; rfl
    rw [e]; exact sti_ind_le_one _
  · have e : decide (c = v) = false := decide_eq_false (fun e => h (congrArg Fin.val e))
    rw [e]; exact Nat.zero_le _

private theorem sti_ind_or (a b : Bool) : sti_ind (a || b) ≤ sti_ind a + sti_ind b := by
  cases a <;> cases b <;> decide

private theorem sti_ind_mem_cons {C : Nat} (v c : Fin C) (l : List (Fin C)) :
    sti_ind (capIn v (c :: l)) ≤ sti_ind (decide (c.1 = v.1)) + sti_ind (capIn v l) :=
  Nat.le_trans (sti_ind_or (decide (c = v)) (capIn v l))
    (Nat.add_le_add_right (sti_ind_deceq c v) _)

private theorem sti_ind_mem_cons' {C : Nat} (v c : Fin C) (l : List (Fin C)) :
    sti_ind (capIn v (c :: l)) ≤ sti_ind (decide (v.1 = c.1)) + sti_ind (capIn v l) := by
  refine Nat.le_trans (sti_ind_mem_cons v c l) (Nat.add_le_add_right ?_ _)
  by_cases h : c.1 = v.1
  · have e : sti_ind (decide (v.1 = c.1)) = 1 := by rw [decide_eq_true h.symm]; rfl
    rw [e]; exact sti_ind_le_one _
  · rw [decide_eq_false h]; exact Nat.zero_le _

/-- A list of capacity values is hit by at most its length many values. -/
private theorem sti_mem_count {C : Nat} :
    ∀ l : List (Fin C), Spec.sampleSum C (fun c => sti_ind (capIn c l)) ≤ l.length
  | [] =>
    Nat.le_trans (sti_sum_le C _ (fun _ => 0) (fun _ => Nat.le_refl 0))
      (Nat.le_of_eq ((sti_sum_const C 0).trans (Nat.mul_zero C)))
  | a :: l => by
    refine Nat.le_trans (sti_sum_le C _
      (fun c => sti_ind (decide (c.1 = a.1)) + sti_ind (capIn c l))
      (fun c => sti_ind_mem_cons' c a l)) ?_
    rw [sti_sum_add]
    show _ ≤ l.length + 1
    rw [Nat.add_comm]
    exact Nat.add_le_add (sti_mem_count l) (sti_eq_count C a.1)

/-! ### Sums over coin lists -/

private theorem sti_sumC_le {R C : Nat} : ∀ (K : Nat) (f g : List (SpSt R C) → Nat),
    (∀ ω, f ω ≤ g ω) → sumC R C K f ≤ sumC R C K g
  | 0, _, _, h => h []
  | K + 1, _, _, h => sti_sum_le R _ _ (fun r => sti_sum_le C _ _ (fun c =>
      sti_sumC_le K _ _ (fun ω => h ((r, c) :: ω))))

private theorem sti_sumC_add {R C : Nat} : ∀ (K : Nat) (f g : List (SpSt R C) → Nat),
    sumC R C K (fun ω => f ω + g ω) = sumC R C K f + sumC R C K g
  | 0, _, _ => rfl
  | K + 1, f, g => by
    show Spec.sampleSum R (fun r => Spec.sampleSum C (fun c =>
        sumC R C K (fun ω => f ((r, c) :: ω) + g ((r, c) :: ω)))) =
      Spec.sampleSum R (fun r => Spec.sampleSum C (fun c =>
        sumC R C K (fun ω => f ((r, c) :: ω)))) +
      Spec.sampleSum R (fun r => Spec.sampleSum C (fun c =>
        sumC R C K (fun ω => g ((r, c) :: ω))))
    rw [← sti_sum_add]
    refine sti_sum_ext (fun r => ?_)
    rw [← sti_sum_add]
    exact sti_sum_ext (fun c => sti_sumC_add K _ _)

private theorem sti_sumC_const {R C : Nat} : ∀ (K a : Nat),
    sumC R C K (fun _ => a) = a * Spec.roCoinPow (R * C) K
  | 0, a => (Nat.mul_one a).symm
  | K + 1, a => by
    show Spec.sampleSum R (fun _ => Spec.sampleSum C (fun _ => sumC R C K (fun _ => a))) =
      a * (R * C * Spec.roCoinPow (R * C) K)
    rw [sti_sumC_const K a, sti_sum_const, sti_sum_const]
    ac_rfl

private theorem sti_sumC_three {R C : Nat} (K N a b : Nat)
    (hN : Spec.roCoinPow (R * C) K = N) (f h : List (SpSt R C) → Nat)
    (hf : ∀ ω, f ω ≤ a + b + h ω) :
    sumC R C K f ≤ a * N + b * N + sumC R C K h := by
  refine Nat.le_trans (sti_sumC_le K f (fun ω => a + b + h ω) hf) ?_
  rw [sti_sumC_add K (fun _ => a + b) h, sti_sumC_add K (fun _ => a) (fun _ => b),
    sti_sumC_const, sti_sumC_const, hN]
  exact Nat.le_refl _

/-! ### Sums over the hidden capacities -/

/-- The paths and rate values of a table of unused oracle values. -/
private def sti_sk {β : Type} {R C : Nat} (t : List (List β × Fin R × Fin C)) :
    List (List β × Fin R) :=
  t.map (fun e => (e.1, e.2.1))

/-- Sum over all tables of unused oracle values with the given paths and rate values. -/
private def sti_sumG {β : Type} {R : Nat} (C : Nat) :
    List (List β × Fin R) → (List (List β × Fin R × Fin C) → Nat) → Nat
  | [], f => f []
  | e :: ps, f => Spec.sampleSum C (fun c => sti_sumG C ps (fun t => f ((e.1, e.2, c) :: t)))

private theorem sti_sumG_le {β : Type} {R C : Nat} : ∀ (ps : List (List β × Fin R))
    (f g : List (List β × Fin R × Fin C) → Nat),
    (∀ t, sti_sk t = ps → f t ≤ g t) → sti_sumG C ps f ≤ sti_sumG C ps g
  | [], _, _, h => h [] rfl
  | e :: ps, _, _, h => sti_sum_le C _ _ (fun c => sti_sumG_le ps _ _
      (fun t ht => h ((e.1, e.2, c) :: t) (by rw [← ht]; rfl)))

private theorem sti_sumG_congr {β : Type} {R C : Nat} (ps : List (List β × Fin R))
    (f g : List (List β × Fin R × Fin C) → Nat) (h : ∀ t, sti_sk t = ps → f t = g t) :
    sti_sumG C ps f = sti_sumG C ps g :=
  Nat.le_antisymm (sti_sumG_le ps f g (fun t ht => Nat.le_of_eq (h t ht)))
    (sti_sumG_le ps g f (fun t ht => Nat.le_of_eq (h t ht).symm))

private theorem sti_sumG_add {β : Type} {R C : Nat} : ∀ (ps : List (List β × Fin R))
    (f g : List (List β × Fin R × Fin C) → Nat),
    sti_sumG C ps (fun t => f t + g t) = sti_sumG C ps f + sti_sumG C ps g
  | [], _, _ => rfl
  | e :: ps, f, g => by
    show Spec.sampleSum C (fun c => sti_sumG C ps (fun t =>
        f ((e.1, e.2, c) :: t) + g ((e.1, e.2, c) :: t))) =
      Spec.sampleSum C (fun c => sti_sumG C ps (fun t => f ((e.1, e.2, c) :: t))) +
      Spec.sampleSum C (fun c => sti_sumG C ps (fun t => g ((e.1, e.2, c) :: t)))
    rw [← sti_sum_add]
    exact sti_sum_ext (fun c => sti_sumG_add ps _ _)

private theorem sti_sumG_const {β : Type} {R C : Nat} : ∀ (ps : List (List β × Fin R)) (a : Nat),
    sti_sumG C ps (fun _ => a) = a * C ^ ps.length
  | [], a => (Nat.mul_one a).symm
  | e :: ps, a => by
    show Spec.sampleSum C (fun _ => sti_sumG C ps (fun _ => a)) = a * C ^ (ps.length + 1)
    rw [sti_sumG_const ps a, sti_sum_const, Nat.pow_succ]
    ac_rfl

private theorem sti_sumG_mul_right {β : Type} {R C : Nat} : ∀ (ps : List (List β × Fin R))
    (f : List (List β × Fin R × Fin C) → Nat) (a : Nat),
    sti_sumG C ps (fun t => f t * a) = sti_sumG C ps f * a
  | [], _, _ => rfl
  | e :: ps, f, a => by
    show Spec.sampleSum C (fun c => sti_sumG C ps (fun t => f ((e.1, e.2, c) :: t) * a)) =
      Spec.sampleSum C (fun c => sti_sumG C ps (fun t => f ((e.1, e.2, c) :: t))) * a
    rw [← sti_sum_mul_right]
    exact sti_sum_ext (fun c => sti_sumG_mul_right ps _ a)

private theorem sti_sumG_sum {β : Type} {R C : Nat} : ∀ (ps : List (List β × Fin R)) (n : Nat)
    (f : List (List β × Fin R × Fin C) → Fin n → Nat),
    sti_sumG C ps (fun t => Spec.sampleSum n (fun i => f t i)) =
      Spec.sampleSum n (fun i => sti_sumG C ps (fun t => f t i))
  | [], _, _ => rfl
  | e :: ps, n, f =>
    (sti_sum_ext (fun c => sti_sumG_sum ps n (fun t i => f ((e.1, e.2, c) :: t) i))).trans
      (sti_sum_comm C n (fun c i => sti_sumG C ps (fun t => f ((e.1, e.2, c) :: t) i)))

private theorem sti_zero {β : Type} {R C : Nat} (ps : List (List β × Fin R))
    (f : List (List β × Fin R × Fin C) → Nat) (D : Nat) (h : ∀ t, sti_sk t = ps → f t = 0) :
    sti_sumG C ps f * C ≤ D := by
  have e : sti_sumG C ps f = 0 :=
    (sti_sumG_congr ps f (fun _ => 0) h).trans ((sti_sumG_const ps 0).trans (Nat.zero_mul _))
  rw [e, Nat.zero_mul]
  exact Nat.zero_le _

private theorem sti_g0 {β : Type} {R C : Nat} (ps : List (List β × Fin R)) :
    sti_sumG C ps (fun (_ : List (List β × Fin R × Fin C)) => 0) * C ≤
      ps.length * C ^ ps.length :=
  sti_zero ps _ _ (fun _ _ => rfl)

private theorem sti_Phi_congr {β : Type} {R C : Nat} (ps : List (List β × Fin R)) (K : Nat)
    (F F' : List (List β × Fin R × Fin C) → List (SpSt R C) → Nat)
    (h : ∀ t, sti_sk t = ps → ∀ ω, F t ω = F' t ω) :
    sti_sumG C ps (fun t => sumC R C K (F t)) = sti_sumG C ps (fun t => sumC R C K (F' t)) :=
  sti_sumG_congr ps _ _ (fun t ht => congrArg (sumC R C K) (funext (h t ht)))

/-- A fixed capacity value is among the hidden ones for at most a `|ps| / C` fraction of the
    tables. -/
private theorem sti_guess {β : Type} {R C : Nat} (v : Fin C) :
    ∀ ps : List (List β × Fin R),
      sti_sumG C ps (fun (t : List (List β × Fin R × Fin C)) =>
        sti_ind (capIn v (t.map (fun e => e.2.2)))) * C ≤ ps.length * C ^ ps.length
  | [] => by
    show 0 * C ≤ 0 * C ^ 0
    rw [Nat.zero_mul]
    exact Nat.zero_le _
  | e :: ps => by
    have ih := sti_guess v ps
    have hA : Spec.sampleSum C (fun c => sti_ind (decide (c.1 = v.1))) ≤ 1 := sti_eq_count C v.1
    have h1 : sti_sumG C (e :: ps) (fun (t : List (List β × Fin R × Fin C)) =>
          sti_ind (capIn v (t.map (fun e => e.2.2)))) ≤
        Spec.sampleSum C (fun c => sti_ind (decide (c.1 = v.1))) * C ^ ps.length +
          C * sti_sumG C ps (fun (t : List (List β × Fin R × Fin C)) =>
            sti_ind (capIn v (t.map (fun e => e.2.2)))) := by
      refine Nat.le_trans (sti_sum_le C _
        (fun c => sti_ind (decide (c.1 = v.1)) * C ^ ps.length +
          sti_sumG C ps (fun (t : List (List β × Fin R × Fin C)) =>
            sti_ind (capIn v (t.map (fun e => e.2.2))))) (fun c => ?_)) ?_
      · refine Nat.le_trans (sti_sumG_le ps _
          (fun t => sti_ind (decide (c.1 = v.1)) +
            sti_ind (capIn v (t.map (fun e => e.2.2)))) (fun t _ => ?_)) ?_
        · exact sti_ind_mem_cons v c _
        · rw [sti_sumG_add, sti_sumG_const]; exact Nat.le_refl _
      · rw [sti_sum_add, sti_sum_mul_right, sti_sum_const]; exact Nat.le_refl _
    generalize sti_sumG C ps (fun (t : List (List β × Fin R × Fin C)) =>
      sti_ind (capIn v (t.map (fun e => e.2.2)))) = G at ih h1
    generalize Spec.sampleSum C (fun c => sti_ind (decide (c.1 = v.1))) = A at hA h1
    show _ * C ≤ (ps.length + 1) * C ^ (ps.length + 1)
    refine Nat.le_trans (Nat.mul_le_mul_right C h1) ?_
    rw [Nat.pow_succ, Nat.add_mul, Nat.succ_mul, Nat.add_comm (ps.length * _)]
    refine Nat.add_le_add ?_ ?_
    · rw [Nat.mul_assoc]
      exact Nat.le_trans (Nat.mul_le_mul_right _ hA) (Nat.le_of_eq (Nat.one_mul _))
    · calc C * G * C = C * (G * C) := Nat.mul_assoc _ _ _
        _ ≤ C * (ps.length * C ^ ps.length) := Nat.mul_le_mul_left _ ih
        _ = ps.length * (C ^ ps.length * C) := by ac_rfl

private theorem sti_find_pos {α : Type} (p : α → Bool) (a : α) (l : List α) (h : p a = true) :
    (a :: l).find? p = some a := by
  simp only [List.find?_cons, h]

private theorem sti_find_neg {α : Type} (p : α → Bool) (a : α) (l : List α) (h : p a = false) :
    (a :: l).find? p = l.find? p := by
  simp only [List.find?_cons, h]

private theorem sti_erase_pos {α : Type} (p : α → Bool) (a : α) (l : List α) (h : p a = true) :
    (a :: l).eraseP p = l := by
  simp only [List.eraseP_cons, h, ↓reduceIte]

private theorem sti_erase_neg {α : Type} (p : α → Bool) (a : α) (l : List α) (h : p a = false) :
    (a :: l).eraseP p = a :: l.eraseP p := by
  simp only [List.eraseP_cons, h, Bool.false_eq_true, ↓reduceIte]

private theorem sti_sk_find {β : Type} [DecidableEq β] {R C : Nat} (q : List β) :
    ∀ t : List (List β × Fin R × Fin C),
      (sti_sk t).find? (fun e => decide (e.1 = q)) =
        (t.find? (fun e => decide (e.1 = q))).map (fun e => (e.1, e.2.1))
  | [] => rfl
  | a :: t => by
    show ((a.1, a.2.1) :: sti_sk t).find? (fun e => decide (e.1 = q)) = _
    by_cases ha : a.1 = q
    · have hd : decide (a.1 = q) = true := decide_eq_true ha
      rw [sti_find_pos (fun e : List β × Fin R => decide (e.1 = q)) (a.1, a.2.1) (sti_sk t) hd,
        sti_find_pos (fun e : List β × Fin R × Fin C => decide (e.1 = q)) a t hd]
      rfl
    · have hd : decide (a.1 = q) = false := decide_eq_false ha
      rw [sti_find_neg (fun e : List β × Fin R => decide (e.1 = q)) (a.1, a.2.1) (sti_sk t) hd,
        sti_find_neg (fun e : List β × Fin R × Fin C => decide (e.1 = q)) a t hd]
      exact sti_sk_find q t

private theorem sti_sk_find_none {β : Type} [DecidableEq β] {R C : Nat} (q : List β)
    (t : List (List β × Fin R × Fin C)) (ps : List (List β × Fin R)) (ht : sti_sk t = ps)
    (h : ps.find? (fun e => decide (e.1 = q)) = none) :
    t.find? (fun e => decide (e.1 = q)) = none := by
  have e := sti_sk_find q t
  rw [ht, h] at e
  cases hf : t.find? (fun e => decide (e.1 = q)) with
  | none => rfl
  | some a => rw [hf] at e; cases e

private theorem sti_sk_find_some {β : Type} [DecidableEq β] {R C : Nat} (q : List β)
    (t : List (List β × Fin R × Fin C)) (ps : List (List β × Fin R)) (e0 : List β × Fin R)
    (ht : sti_sk t = ps) (h : ps.find? (fun e => decide (e.1 = q)) = some e0) :
    ∃ c : Fin C, t.find? (fun e => decide (e.1 = q)) = some (e0.1, e0.2, c) := by
  have e := sti_sk_find q t
  rw [ht, h] at e
  cases hf : t.find? (fun e => decide (e.1 = q)) with
  | none => rw [hf] at e; cases e
  | some a =>
    rw [hf] at e
    have h0 : e0 = (a.1, a.2.1) := Option.some.inj e
    rw [h0]
    exact ⟨a.2.2, rfl⟩

private theorem sti_sk_len {β : Type} {R C : Nat} (t : List (List β × Fin R × Fin C))
    (ps : List (List β × Fin R)) (ht : sti_sk t = ps) : t.length = ps.length := by
  rw [← ht]; exact (List.length_map _).symm

private theorem sti_erase_len {α : Type} (p : α → Bool) :
    ∀ (l : List α) (a0 : α), l.find? p = some a0 → l.length = (l.eraseP p).length + 1
  | [], _, h => by cases h
  | a :: l, a0, h => by
    cases hp : p a with
    | true => rw [sti_erase_pos p a l hp]; rfl
    | false =>
      rw [sti_find_neg p a l hp] at h
      rw [sti_erase_neg p a l hp]
      exact congrArg (· + 1) (sti_erase_len p l a0 h)

/-- Exposure: reading the entry at path `q` of the table and removing it is the same as
    summing its capacity value separately. -/
private theorem sti_sumG_expose {β : Type} [DecidableEq β] {R C : Nat} (q : List β) :
    ∀ (ps : List (List β × Fin R)) (e0 : List β × Fin R)
      (G : Option (List β × Fin R × Fin C) → List (List β × Fin R × Fin C) → Nat),
      ps.find? (fun e => decide (e.1 = q)) = some e0 →
      sti_sumG C ps (fun t => G (t.find? (fun e => decide (e.1 = q)))
          (t.eraseP (fun e => decide (e.1 = q)))) =
        Spec.sampleSum C (fun c => sti_sumG C (ps.eraseP (fun e => decide (e.1 = q)))
          (fun t' => G (some (e0.1, e0.2, c)) t'))
  | [], _, _, h => by cases h
  | a :: ps, e0, G, h => by
    by_cases ha : a.1 = q
    · have hd : decide (a.1 = q) = true := decide_eq_true ha
      rw [sti_find_pos (fun e : List β × Fin R => decide (e.1 = q)) a ps hd] at h
      have h0 : e0 = a := (Option.some.inj h).symm
      rw [h0, sti_erase_pos (fun e : List β × Fin R => decide (e.1 = q)) a ps hd]
      refine sti_sum_ext (fun c => congrArg (sti_sumG C ps) (funext (fun t => ?_)))
      show G (List.find? _ ((a.1, a.2, c) :: t)) (List.eraseP _ ((a.1, a.2, c) :: t)) = _
      rw [sti_find_pos (fun e : List β × Fin R × Fin C => decide (e.1 = q)) (a.1, a.2, c) t hd,
        sti_erase_pos (fun e : List β × Fin R × Fin C => decide (e.1 = q)) (a.1, a.2, c) t hd]
    · have hd : decide (a.1 = q) = false := decide_eq_false ha
      rw [sti_find_neg (fun e : List β × Fin R => decide (e.1 = q)) a ps hd] at h
      rw [sti_erase_neg (fun e : List β × Fin R => decide (e.1 = q)) a ps hd]
      refine Eq.trans (sti_sum_ext (fun c => ?_))
        (sti_sum_comm C C (fun c c' =>
          sti_sumG C (ps.eraseP (fun e => decide (e.1 = q)))
            (fun t => G (some (e0.1, e0.2, c')) ((a.1, a.2, c) :: t))))
      refine Eq.trans (congrArg (sti_sumG C ps) (funext (fun t => ?_)))
        (sti_sumG_expose q ps e0 (fun o t' => G o ((a.1, a.2, c) :: t')) h)
      show G (List.find? _ ((a.1, a.2, c) :: t)) (List.eraseP _ ((a.1, a.2, c) :: t)) = _
      rw [sti_find_neg (fun e : List β × Fin R × Fin C => decide (e.1 = q)) (a.1, a.2, c) t hd,
        sti_erase_neg (fun e : List β × Fin R × Fin C => decide (e.1 = q)) (a.1, a.2, c) t hd]

/-! ### The coin space `Fin ((R C)^K)` -/

private theorem sti_decode_pair {R C : Nat} (r : Fin R) (c : Fin C) :
    decodeSt (⟨r.1 * C + c.1, sti_pair_lt r c⟩ : Fin (R * C)) = (r, c) :=
  Prod.ext (Fin.ext (sti_pair_div r c)) (Fin.ext (sti_pair_mod r c))

private theorem sti_cons_congr {R C : Nat} (K : Nat) (a a' : Fin (R * C))
    (b b' : Fin (Spec.roCoinPow (R * C) K)) (ha : a = a') (hb : b = b') :
    (decodeSt a :: coinList K b : List (SpSt R C)) = decodeSt a' :: coinList K b' := by
  rw [ha, hb]

private theorem sti_coinList_pair {R C : Nat} (K : Nat) (i : Fin (R * C))
    (j : Fin (Spec.roCoinPow (R * C) K)) :
    coinList (K + 1) (⟨i.1 * Spec.roCoinPow (R * C) K + j.1, sti_pair_lt i j⟩ :
      Fin (Spec.roCoinPow (R * C) (K + 1))) = decodeSt i :: coinList K j :=
  sti_cons_congr K _ i _ j (Fin.ext (sti_pair_div i j)) (Fin.ext (sti_pair_mod i j))

/-- Summing over the coin space `Fin ((R C)^K)` through `coinList` is summing over the coin
    lists of length `K`. -/
theorem sampleSum_coinList {R C : Nat} : ∀ (K : Nat) (f : List (SpSt R C) → Nat),
    Spec.sampleSum (Spec.roCoinPow (R * C) K) (fun ω => f (coinList K ω)) = sumC R C K f
  | 0, _ => rfl
  | K + 1, f => by
    show Spec.sampleSum (R * C * Spec.roCoinPow (R * C) K) (fun ω => f (coinList (K + 1) ω)) =
      Spec.sampleSum R (fun r => Spec.sampleSum C (fun c => sumC R C K (fun ω => f ((r, c) :: ω))))
    rw [sti_sum_prod (R * C) (Spec.roCoinPow (R * C) K)]
    refine (sti_sum_ext (fun i => (sti_sum_ext (fun j =>
      congrArg f (sti_coinList_pair K i j))).trans
        (sampleSum_coinList K (fun ω => f (decodeSt i :: ω))))).trans ?_
    rw [sti_sum_prod R C]
    exact sti_sum_ext (fun r => sti_sum_ext (fun c => by rw [sti_decode_pair]))

/-! ### One oracle call that consumes a coin -/

private theorem sti_caps_len {β : Type} {R C : Nat} (s0 : SpSt R C)
    (rt : List (List β × SpSt R C × SpSt R C)) (tF : List (SpSt R C × SpSt R C))
    (t : List (List β × Fin R × Fin C)) (ps : List (List β × Fin R)) (ht : sti_sk t = ps) :
    (capsOf s0 (SimSt.mk rt t tF)).length = 1 + ps.length + rt.length + 2 * tF.length := by
  have hl := sti_sk_len t ps ht
  simp only [capsOf, List.length_cons, List.length_append, List.length_map]
  omega

/-- The budget: `K` coins left, `L` table entries, `h` of them hidden. -/
private def sti_Bd (K L h : Nat) : Nat := K * (2 * L + K + 1) + h

private theorem sti_Bd_step (K h rt tF L' h' : Nat) (hL : L' = h + rt + tF + 1)
    (hh : h' ≤ h + 1) :
    h + (1 + h + rt + 2 * tF) + sti_Bd K L' h' ≤ sti_Bd (K + 1) (h + rt + tF) h := by
  subst hL
  unfold sti_Bd
  have e1 : 2 * (h + rt + tF + 1) + K + 1 = (2 * (h + rt + tF) + K + 1) + 2 := by omega
  have e2 : 2 * (h + rt + tF) + (K + 1) + 1 = (2 * (h + rt + tF) + K + 1) + 1 := by omega
  rw [e1, e2]
  generalize hX : 2 * (h + rt + tF) + K + 1 = X
  have a1 : K * (X + 2) = K * X + 2 * K := by rw [Nat.mul_add]; omega
  have a2 : (K + 1) * (X + 1) = K * X + K + X + 1 := by rw [Nat.add_mul, Nat.mul_add]; omega
  rw [a1, a2]
  omega

private theorem sti_hG_pair (R C Cn N B' : Nat) (f : Fin R → Fin C → Nat)
    (h : ∀ r c, f r c * C ≤ B' * (Cn * N)) :
    Spec.sampleSum R (fun r => Spec.sampleSum C (fun c => f r c)) * C ≤
      B' * (Cn * (R * C * N)) :=
  Nat.le_trans (sti_sum2_scale R C f C _ h) (Nat.le_of_eq (by ac_rfl))

private theorem sti_hG_row (R C n N B' : Nat) (f : Fin R → Nat)
    (h : ∀ r, f r * C ≤ B' * (C ^ (n + 1) * N)) :
    Spec.sampleSum R f * C ≤ B' * (C ^ n * (R * C * N)) := by
  refine Nat.le_trans (sti_sum1_scale R f C _ h) (Nat.le_of_eq ?_)
  rw [Nat.pow_succ]
  ac_rfl

/-- A call that consumes the coin `(r, c)`: it is charged the guess `g`, the collision of `c`
    with a capacity value in use, and the rest of the run. -/
private theorem sti_step {β : Type} {R C : Nat} (s0 : SpSt R C)
    (rt : List (List β × SpSt R C × SpSt R C)) (tF : List (SpSt R C × SpSt R C))
    (ps : List (List β × Fin R)) (K N cl : Nat) (hN : Spec.roCoinPow (R * C) K = N)
    (hcl : ∀ t, sti_sk t = ps → (capsOf s0 (SimSt.mk rt t tF)).length ≤ cl)
    (X : List (List β × Fin R × Fin C) → List (SpSt R C) → Nat)
    (g : List (List β × Fin R × Fin C) → Nat)
    (Gr : Fin R → Fin C → List (List β × Fin R × Fin C) → List (SpSt R C) → Nat) (B' : Nat)
    (hX : ∀ t, sti_sk t = ps → ∀ r c ω, X t ((r, c) :: ω) ≤
      g t + sti_ind (capIn c (capsOf s0 (SimSt.mk rt t tF))) + Gr r c t ω)
    (hg : sti_sumG C ps g * C ≤ ps.length * C ^ ps.length)
    (hG : Spec.sampleSum R (fun r => Spec.sampleSum C (fun c =>
        sti_sumG C ps (fun t => sumC R C K (Gr r c t)))) * C ≤
      B' * (C ^ ps.length * (R * C * N))) :
    sti_sumG C ps (fun t => sumC R C (K + 1) (X t)) * C ≤
      (ps.length + cl + B') * (C ^ ps.length * (R * C * N)) := by
  have hpt : ∀ t, sti_sk t = ps → sumC R C (K + 1) (X t) ≤
      g t * (R * C * N) + cl * (R * N) +
        Spec.sampleSum R (fun r => Spec.sampleSum C (fun c => sumC R C K (Gr r c t))) := by
    intro t ht
    have hr : ∀ r : Fin R, Spec.sampleSum C (fun c => sumC R C K (fun ω => X t ((r, c) :: ω))) ≤
        C * (g t * N) + cl * N + Spec.sampleSum C (fun c => sumC R C K (Gr r c t)) := by
      intro r
      refine Nat.le_trans (sti_sum_le C _ _ (fun c =>
        sti_sumC_three K N (g t) (sti_ind (capIn c (capsOf s0 (SimSt.mk rt t tF)))) hN _
          (Gr r c t) (fun ω => hX t ht r c ω))) ?_
      rw [sti_sum_add, sti_sum_add, sti_sum_const, sti_sum_mul_right]
      exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_right N
        (Nat.le_trans (sti_mem_count _) (hcl t ht))) _) _
    refine Nat.le_trans (sti_sum_le R _ _ hr) ?_
    rw [sti_sum_add, sti_sum_add, sti_sum_const, sti_sum_const]
    refine Nat.add_le_add_right (Nat.le_of_eq ?_) _
    have e1 : R * (C * (g t * N)) = g t * (R * C * N) := by ac_rfl
    have e2 : R * (cl * N) = cl * (R * N) := by ac_rfl
    rw [e1, e2]
  have hsum := sti_sumG_le ps _ _ hpt
  rw [sti_sumG_add, sti_sumG_add, sti_sumG_mul_right, sti_sumG_const] at hsum
  have hex : sti_sumG C ps (fun t => Spec.sampleSum R (fun r => Spec.sampleSum C (fun c =>
        sumC R C K (Gr r c t)))) =
      Spec.sampleSum R (fun r => Spec.sampleSum C (fun c =>
        sti_sumG C ps (fun t => sumC R C K (Gr r c t)))) :=
    (sti_sumG_sum ps R (fun t r => Spec.sampleSum C (fun c => sumC R C K (Gr r c t)))).trans
      (sti_sum_ext (fun r => sti_sumG_sum ps C (fun t c => sumC R C K (Gr r c t))))
  rw [hex] at hsum
  have h1 : sti_sumG C ps g * (R * C * N) * C ≤ ps.length * (C ^ ps.length * (R * C * N)) :=
    calc sti_sumG C ps g * (R * C * N) * C = sti_sumG C ps g * C * (R * C * N) := by ac_rfl
      _ ≤ ps.length * C ^ ps.length * (R * C * N) := Nat.mul_le_mul_right _ hg
      _ = ps.length * (C ^ ps.length * (R * C * N)) := Nat.mul_assoc _ _ _
  have h2 : cl * (R * N) * C ^ ps.length * C = cl * (C ^ ps.length * (R * C * N)) := by ac_rfl
  refine Nat.le_trans (Nat.mul_le_mul_right C hsum) ?_
  rw [sti_add3_mul, sti_add3_mul]
  exact Nat.add_le_add (Nat.add_le_add h1 (Nat.le_of_eq h2)) hG

/-! ### The flag of one call of the ideal world -/

private theorem sti_inv_known {β : Type} [DecidableEq β] {R C : Nat} {Out : Type}
    (ops : AbsorbOps β R) (s0 : SpSt R C) (y : SpSt R C) (k : SpSt R C → SpAdv β R C Out)
    (S : SimSt β R C) (ω : List (SpSt R C)) (x : SpSt R C) (h : simInvKnown S y = some x) :
    (idealRun ops s0 (SpAdv.inv y k) S ω).2 = (idealRun ops s0 (k x) S ω).2 := by
  simp only [idealRun, spongeSimulator, spongeSimInv, h, ↓reduceIte, Bool.false_or]

private theorem sti_inv_nil {β : Type} [DecidableEq β] {R C : Nat} {Out : Type}
    (ops : AbsorbOps β R) (s0 : SpSt R C) (y : SpSt R C) (k : SpSt R C → SpAdv β R C Out)
    (S : SimSt β R C) (h : simInvKnown S y = none) :
    (idealRun ops s0 (SpAdv.inv y k) S []).2 = capIn y.2 (hidCaps S) := by
  simp only [idealRun, spongeSimulator, spongeSimInv, h, ↓reduceIte]

private theorem sti_inv_cons {β : Type} [DecidableEq β] {R C : Nat} {Out : Type}
    (ops : AbsorbOps β R) (s0 : SpSt R C) (y : SpSt R C) (k : SpSt R C → SpAdv β R C Out)
    (S : SimSt β R C) (d : SpSt R C) (ω : List (SpSt R C)) (h : simInvKnown S y = none) :
    (idealRun ops s0 (SpAdv.inv y k) S (d :: ω)).2 =
      ((capIn y.2 (hidCaps S) || capIn d.2 (capsOf s0 S)) ||
        (idealRun ops s0 (k d) { S with tF := (d, y) :: S.tF } ω).2) := by
  simp only [idealRun, spongeSimulator, spongeSimInv, h, ↓reduceIte]

private theorem sti_fwd_known {β : Type} [DecidableEq β] {R C : Nat} {Out : Type}
    (ops : AbsorbOps β R) (s0 : SpSt R C) (x : SpSt R C) (k : SpSt R C → SpAdv β R C Out)
    (S : SimSt β R C) (ω : List (SpSt R C)) (z : SpSt R C) (h : simFwdKnown S x = some z) :
    (idealRun ops s0 (SpAdv.fwd x k) S ω).2 = (idealRun ops s0 (k z) S ω).2 := by
  simp only [idealRun, spongeSimulator, spongeSimFwd, h, Bool.false_eq_true, ↓reduceIte,
    Bool.false_or]

private theorem sti_fwd_un_nil {β : Type} [DecidableEq β] {R C : Nat} {Out : Type}
    (ops : AbsorbOps β R) (s0 : SpSt R C) (x : SpSt R C) (k : SpSt R C → SpAdv β R C Out)
    (S : SimSt β R C) (hk : simFwdKnown S x = none) (hr : simFindRoot s0 S x.2 = none) :
    (idealRun ops s0 (SpAdv.fwd x k) S []).2 = capIn x.2 (hidCaps S) := by
  simp only [idealRun, spongeSimulator, spongeSimFwd, hk, hr, Bool.false_eq_true, ↓reduceIte]

private theorem sti_fwd_un_cons {β : Type} [DecidableEq β] {R C : Nat} {Out : Type}
    (ops : AbsorbOps β R) (s0 : SpSt R C) (x : SpSt R C) (k : SpSt R C → SpAdv β R C Out)
    (S : SimSt β R C) (d : SpSt R C) (ω : List (SpSt R C))
    (hk : simFwdKnown S x = none) (hr : simFindRoot s0 S x.2 = none) :
    (idealRun ops s0 (SpAdv.fwd x k) S (d :: ω)).2 =
      ((capIn x.2 (hidCaps S) || capIn d.2 (capsOf s0 S)) ||
        (idealRun ops s0 (k d) { S with tF := (x, d) :: S.tF } ω).2) := by
  simp only [idealRun, spongeSimulator, spongeSimFwd, hk, hr, Bool.false_eq_true, ↓reduceIte]

private theorem sti_fwd_expose {β : Type} [DecidableEq β] {R C : Nat} {Out : Type}
    (ops : AbsorbOps β R) (s0 : SpSt R C) (x : SpSt R C) (k : SpSt R C → SpAdv β R C Out)
    (S : SimSt β R C) (ω : List (SpSt R C)) (p : List β) (tt : SpSt R C)
    (e : List β × Fin R × Fin C)
    (hk : simFwdKnown S x = none) (hr : simFindRoot s0 S x.2 = some (p, tt))
    (hf : S.tH.find? (fun e => decide (e.1 = p ++ [ops.diffB tt.1 x.1])) = some e) :
    (idealRun ops s0 (SpAdv.fwd x k) S ω).2 =
      (idealRun ops s0 (k (e.2.1, e.2.2))
        { S with rt := (p ++ [ops.diffB tt.1 x.1], x, (e.2.1, e.2.2)) :: S.rt,
                 tH := S.tH.eraseP (fun e => decide (e.1 = p ++ [ops.diffB tt.1 x.1])) } ω).2 := by
  simp only [idealRun, spongeSimulator, spongeSimFwd, hk, hr, hf, Bool.false_eq_true, ↓reduceIte,
    Bool.false_or]

private theorem sti_fwd_root_nil {β : Type} [DecidableEq β] {R C : Nat} {Out : Type}
    (ops : AbsorbOps β R) (s0 : SpSt R C) (x : SpSt R C) (k : SpSt R C → SpAdv β R C Out)
    (S : SimSt β R C) (p : List β) (tt : SpSt R C)
    (hk : simFwdKnown S x = none) (hr : simFindRoot s0 S x.2 = some (p, tt))
    (hf : S.tH.find? (fun e => decide (e.1 = p ++ [ops.diffB tt.1 x.1])) = none) :
    (idealRun ops s0 (SpAdv.fwd x k) S []).2 = false := by
  simp only [idealRun, spongeSimulator, spongeSimFwd, hk, hr, hf, Bool.false_eq_true, ↓reduceIte]

private theorem sti_fwd_root_cons {β : Type} [DecidableEq β] {R C : Nat} {Out : Type}
    (ops : AbsorbOps β R) (s0 : SpSt R C) (x : SpSt R C) (k : SpSt R C → SpAdv β R C Out)
    (S : SimSt β R C) (d : SpSt R C) (ω : List (SpSt R C)) (p : List β) (tt : SpSt R C)
    (hk : simFwdKnown S x = none) (hr : simFindRoot s0 S x.2 = some (p, tt))
    (hf : S.tH.find? (fun e => decide (e.1 = p ++ [ops.diffB tt.1 x.1])) = none) :
    (idealRun ops s0 (SpAdv.fwd x k) S (d :: ω)).2 =
      (capIn d.2 (capsOf s0 S) ||
        (idealRun ops s0 (k d)
          { S with rt := (p ++ [ops.diffB tt.1 x.1], x, d) :: S.rt } ω).2) := by
  simp only [idealRun, spongeSimulator, spongeSimFwd, hk, hr, hf, Bool.false_eq_true, ↓reduceIte]

/-! ### The oracle walk -/

private theorem sti_roStep_some {β : Type} [DecidableEq β] {R C : Nat} (s0 : SpSt R C)
    (S : SimSt β R C) (ω : List (SpSt R C)) (q : List β) (r : Fin R)
    (h : roLookup S q = some r) : roStep s0 S ω q = (some (r, S, ω), false) := by
  simp only [roStep, h]

private theorem sti_roStep_nil {β : Type} [DecidableEq β] {R C : Nat} (s0 : SpSt R C)
    (S : SimSt β R C) (q : List β) (h : roLookup S q = none) :
    roStep s0 S [] q = (none, false) := by
  simp only [roStep, h]

private theorem sti_roStep_cons {β : Type} [DecidableEq β] {R C : Nat} (s0 : SpSt R C)
    (S : SimSt β R C) (d : SpSt R C) (ω : List (SpSt R C)) (q : List β)
    (h : roLookup S q = none) :
    roStep s0 S (d :: ω) q =
      (some (d.1, { S with tH := (q, d.1, d.2) :: S.tH }, ω), capIn d.2 (capsOf s0 S)) := by
  simp only [roStep, h]

/-- The oracle's memo read off the paths and rate values of `tH`. -/
private def sti_look {β : Type} [DecidableEq β] {R C : Nat}
    (rt : List (List β × SpSt R C × SpSt R C)) (ps : List (List β × Fin R)) (q : List β) :
    Option (Fin R) :=
  match rt.find? (fun e => decide (e.1 = q)) with
  | some e => some e.2.2.1
  | none => (ps.find? (fun e => decide (e.1 = q))).map (fun e => e.2)

private theorem sti_look_eq {β : Type} [DecidableEq β] {R C : Nat}
    (rt : List (List β × SpSt R C × SpSt R C)) (tF : List (SpSt R C × SpSt R C))
    (t : List (List β × Fin R × Fin C)) (ps : List (List β × Fin R)) (q : List β)
    (ht : sti_sk t = ps) : roLookup (SimSt.mk rt t tF) q = sti_look rt ps q := by
  subst ht
  cases hrt : rt.find? (fun e => decide (e.1 = q)) with
  | some e => simp only [roLookup, sti_look, hrt]
  | none =>
    simp only [roLookup, sti_look, hrt, sti_sk_find]
    cases t.find? (fun e => decide (e.1 = q)) <;> rfl

/-- The flag of an oracle walk followed by a continuation. -/
private def sti_walkFlag {β : Type} [DecidableEq β] {R C : Nat} (s0 : SpSt R C)
    (cont : Fin R → SimSt β R C → List (SpSt R C) → Bool) (S : SimSt β R C)
    (ω : List (SpSt R C)) (p : List β) (r : Fin R) (bad : Bool) (m : List β) : Bool :=
  match roWalk s0 S ω p r bad m with
  | (none, bd) => bd
  | (some (r', S', ω'), bd) => bd || cont r' S' ω'

private theorem sti_walk_cons_some {β : Type} [DecidableEq β] {R C : Nat} (s0 : SpSt R C)
    (cont : Fin R → SimSt β R C → List (SpSt R C) → Bool) (S : SimSt β R C)
    (ω : List (SpSt R C)) (p : List β) (r : Fin R) (bad : Bool) (b : β) (m : List β)
    (r' : Fin R) (S' : SimSt β R C) (ω' : List (SpSt R C)) (bd : Bool)
    (h : roStep s0 S ω (p ++ [b]) = (some (r', S', ω'), bd)) :
    sti_walkFlag s0 cont S ω p r bad (b :: m) =
      sti_walkFlag s0 cont S' ω' (p ++ [b]) r' (bad || bd) m := by
  simp only [sti_walkFlag, roWalk, h]

private theorem sti_walk_cons_none {β : Type} [DecidableEq β] {R C : Nat} (s0 : SpSt R C)
    (cont : Fin R → SimSt β R C → List (SpSt R C) → Bool) (S : SimSt β R C)
    (ω : List (SpSt R C)) (p : List β) (r : Fin R) (bad : Bool) (b : β) (m : List β)
    (bd : Bool) (h : roStep s0 S ω (p ++ [b]) = (none, bd)) :
    sti_walkFlag s0 cont S ω p r bad (b :: m) = (bad || bd) := by
  simp only [sti_walkFlag, roWalk, h]

private theorem sti_walk_bad {β : Type} [DecidableEq β] {R C : Nat} (s0 : SpSt R C)
    (cont : Fin R → SimSt β R C → List (SpSt R C) → Bool) :
    ∀ (m : List β) (S : SimSt β R C) (ω : List (SpSt R C)) (p : List β) (r : Fin R)
      (bad : Bool),
      sti_walkFlag s0 cont S ω p r bad m = (bad || sti_walkFlag s0 cont S ω p r false m)
  | [], S, ω, p, r, bad => by
    show (bad || cont r S ω) = (bad || (false || cont r S ω))
    rw [Bool.false_or]
  | b :: m, S, ω, p, r, bad => by
    cases hs : roStep s0 S ω (p ++ [b]) with
    | mk o bd =>
      cases o with
      | none =>
        rw [sti_walk_cons_none s0 cont S ω p r bad b m bd hs,
          sti_walk_cons_none s0 cont S ω p r false b m bd hs, Bool.false_or]
      | some v =>
        obtain ⟨r', S', ω'⟩ := v
        rw [sti_walk_cons_some s0 cont S ω p r bad b m r' S' ω' bd hs,
          sti_walk_cons_some s0 cont S ω p r false b m r' S' ω' bd hs,
          sti_walk_bad s0 cont m S' ω' (p ++ [b]) r' (bad || bd),
          sti_walk_bad s0 cont m S' ω' (p ++ [b]) r' (false || bd), Bool.false_or]
        generalize sti_walkFlag s0 cont S' ω' (p ++ [b]) r' false m = w
        cases bad <;> cases bd <;> cases w <;> rfl

private theorem sti_run_node {β : Type} [DecidableEq β] {R C : Nat} {Out : Type}
    (ops : AbsorbOps β R) (s0 : SpSt R C) (m : List β) (k : Fin R → SpAdv β R C Out)
    (S : SimSt β R C) (ω : List (SpSt R C)) :
    (idealRun ops s0 (SpAdv.node m k) S ω).2 =
      sti_walkFlag s0 (fun r S' ω' => (idealRun ops s0 (k r) S' ω').2) S ω [] s0.1 false m := by
  simp only [idealRun, sti_walkFlag]
  generalize roWalk s0 S ω [] s0.1 false m = res
  obtain ⟨o, bd⟩ := res
  cases o with
  | none => rfl
  | some v => obtain ⟨r, S', ω'⟩ := v; rfl

private theorem sti_walk {β : Type} [DecidableEq β] {R C : Nat} (s0 : SpSt R C)
    (rt : List (List β × SpSt R C × SpSt R C)) (tF : List (SpSt R C × SpSt R C))
    (cont : Fin R → SimSt β R C → List (SpSt R C) → Bool)
    (hc : ∀ (r : Fin R) (ps : List (List β × Fin R)) (K : Nat),
      sti_sumG C ps (fun t => sumC R C K (fun ω =>
        sti_ind (cont r (SimSt.mk rt t tF) ω))) * C ≤
      sti_Bd K (ps.length + rt.length + tF.length) ps.length *
        (C ^ ps.length * Spec.roCoinPow (R * C) K)) :
    ∀ (m : List β) (p : List β) (r : Fin R) (ps : List (List β × Fin R)) (K : Nat),
      sti_sumG C ps (fun t => sumC R C K (fun ω =>
        sti_ind (sti_walkFlag s0 cont (SimSt.mk rt t tF) ω p r false m))) * C ≤
      sti_Bd K (ps.length + rt.length + tF.length) ps.length *
        (C ^ ps.length * Spec.roCoinPow (R * C) K)
  | [], p, r, ps, K => hc r ps K
  | b :: m, p, r, ps, K => by
    cases hl : sti_look rt ps (p ++ [b]) with
    | some r' =>
      rw [sti_Phi_congr ps K
        (fun t ω => sti_ind (sti_walkFlag s0 cont (SimSt.mk rt t tF) ω p r false (b :: m)))
        (fun t ω => sti_ind (sti_walkFlag s0 cont (SimSt.mk rt t tF) ω (p ++ [b]) r' false m))
        (fun t ht ω => congrArg sti_ind
          (sti_walk_cons_some s0 cont _ ω p r false b m r' _ ω false
            (sti_roStep_some s0 _ ω _ r' ((sti_look_eq rt tF t ps _ ht).trans hl))))]
      exact sti_walk s0 rt tF cont hc m (p ++ [b]) r' ps K
    | none =>
      have hno : ∀ t, sti_sk t = ps → roLookup (SimSt.mk rt t tF) (p ++ [b]) = none :=
        fun t ht => (sti_look_eq rt tF t ps _ ht).trans hl
      cases K with
      | zero =>
        exact sti_zero ps _ _ (fun t ht => congrArg sti_ind
          (sti_walk_cons_none s0 cont _ [] p r false b m false
            (sti_roStep_nil s0 _ _ (hno t ht))))
      | succ K =>
        refine Nat.le_trans (sti_step s0 rt tF ps K _ _ rfl
          (fun t ht => Nat.le_of_eq (sti_caps_len s0 rt tF t ps ht))
          (fun t ω => sti_ind (sti_walkFlag s0 cont (SimSt.mk rt t tF) ω p r false (b :: m)))
          (fun _ => 0)
          (fun r' c t ω => sti_ind (sti_walkFlag s0 cont
            (SimSt.mk rt ((p ++ [b], r', c) :: t) tF) ω (p ++ [b]) r' false m))
          (sti_Bd K ((ps.length + 1) + rt.length + tF.length) (ps.length + 1))
          ?_ (sti_g0 ps) ?_) ?_
        · intro t ht r' c ω
          show sti_ind (sti_walkFlag s0 cont (SimSt.mk rt t tF) ((r', c) :: ω) p r false
            (b :: m)) ≤ _
          rw [sti_walk_cons_some s0 cont _ _ p r false b m r' _ ω _
            (sti_roStep_cons s0 _ (r', c) ω _ (hno t ht)), sti_walk_bad]
          exact sti_ind_or2 _ _
        · exact sti_hG_row R C ps.length _ _
            (fun r' => sti_sumG C ((p ++ [b], r') :: ps) (fun t => sumC R C K (fun ω =>
              sti_ind (sti_walkFlag s0 cont (SimSt.mk rt t tF) ω (p ++ [b]) r' false m))))
            (fun r' => sti_walk s0 rt tF cont hc m (p ++ [b]) r' ((p ++ [b], r') :: ps) K)
        · exact Nat.mul_le_mul_right _
            (sti_Bd_step K ps.length rt.length tF.length _ _ (by omega) (Nat.le_refl _))

