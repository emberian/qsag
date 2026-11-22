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

