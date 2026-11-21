module
/-
# Qsag.Spec.Assumptions — Cryptographic Experiments, Hardness Propositions, and Platform Contracts

Experiments, hardness propositions and platform contracts referenced by top-level security
theorems (zero `axiom` declarations).

* An experiment is a game constructed from the primitive, the challenger's samplers, the
  adversary and the enforced resource bound (`smDtTcrGame`, `smDtPreGame`, `itsrGame`,
  `prfRealGame` / `prfIdealGame`, the Ring-LWE, Module-SIS and dual-LPN games).
* Hardness of a primitive against a class `𝒜` of adversaries is a proposition that quantifies
  over every adversary with programs in `𝒜` and every uniform challenger sampler, with challenger
  coins and adversary coins as independent coordinates of the coin space (`CoinSplit`,
  `UniformOn`; `SmDtTcrHard`, `SmDtPreHard`, `ItsrHard`, `PrfHard`, `DecisionRlweHard`,
  `ModuleSisHard`, `DualLpnHard`, and `RegularDualLpnHard` for the regular noise and fixed
  code of the dense PCG). The class is a parameter because this development has no
  running-time model. `…Hard 𝒜` is meaningful only for a class that excludes exhaustive search:
  against the unrestricted class `SM-DT-PRE` hardness is false for every tweakable hash
  (`smDtPreHard_unrestricted_refuted`). That a class excludes such adversaries and that a
  deployed primitive is hard against it is an assumption outside this logic.
* Degenerate primitives are refuted for every class containing one explicit short program
  (`smDtTcrHard_constHash_refuted` and its siblings).
* A platform contract is a set of laws over the event traces of an environment model
  (`PosixFsyncContract`, `AuthenticatedChannelContract`, `KeyErasureContract`,
  `DitHardwareContract`, `SimtWorkgroupContract` / `WellFormedSimtContract`).
-/

public import Qsag.Spec.Primitives
public import Qsag.Spec.Refines
public import Qsag.Spec.GameBound
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Spec

set_option autoImplicit false

-- Avoid the choice-based order-package fallback when simplifying finite-domain equalities.
attribute [-instance] Fin.instLinearOrderPackage

/-! ## 1. Constructive Hash-Break Witness Types (`Type`, Zero Bare Existential `Prop`) -/

/-- Constructive collision witness for a byte-to-byte hash function `H`. -/
structure HashCollision (H : Bytes → Bytes) where
  m₁ : Bytes
  m₂ : Bytes
  distinct : m₁ ≠ m₂
  collides : H m₁ = H m₂

/-- Constructive second-preimage witness against a fixed `target` input under `H`. -/
structure SecondPreimage (H : Bytes → Bytes) (target : Bytes) where
  candidate : Bytes
  distinct : candidate ≠ target
  sameDigest : H candidate = H target

/-- Any `SecondPreimage H target` immediately furnishes a `HashCollision H`. -/
@[expose] def SecondPreimage.toCollision {H : Bytes → Bytes} {target : Bytes}
    (w : SecondPreimage H target) : HashCollision H where
  m₁ := w.candidate
  m₂ := target
  distinct := w.distinct
  collides := w.sameDigest

theorem SecondPreimage.toCollision_collides {H : Bytes → Bytes} {target : Bytes}
    (w : SecondPreimage H target) :
    H w.toCollision.m₁ = H w.toCollision.m₂ ∧ w.toCollision.m₁ ≠ w.toCollision.m₂ :=
  ⟨w.toCollision.collides, w.toCollision.distinct⟩

/-- Prefix-free codec collision extractor: if `H (c.encode x)` collides on distinct inputs `x ≠ y`,
    we constructively obtain a concrete `HashCollision H` (`0 Classical.choice`). -/
def FramedCodec.collisionOfDigestEq {α : Type} [DecidableEq α]
    (c : FramedCodec α) (H : Bytes → Bytes) {x y : α}
    (hDigest : H (c.encode x) = H (c.encode y)) :
    PSum (x = y) (HashCollision H) :=
  match decEq x y with
  | .isTrue hEq => .inl hEq
  | .isFalse hNe =>
    .inr
      { m₁ := c.encode x
        m₂ := c.encode y
        distinct := fun hEnc => hNe (c.encode_injective hEnc)
        collides := hDigest }

theorem FramedCodec.collisionOfDigestEq_sound {α : Type} [DecidableEq α]
    (c : FramedCodec α) (H : Bytes → Bytes) {x y : α}
    (hDigest : H (c.encode x) = H (c.encode y)) :
    match c.collisionOfDigestEq H hDigest with
    | .inl _ => x = y
    | .inr col => x ≠ y ∧ H col.m₁ = H col.m₂ ∧ col.m₁ ≠ col.m₂ := by
  unfold FramedCodec.collisionOfDigestEq
  cases decEq x y with
  | isTrue hEq => exact hEq
  | isFalse hNe => exact ⟨hNe, hDigest, fun hEnc => hNe (c.encode_injective hEnc)⟩

/-! ## 2. Experiments Against a Primitive

Every experiment below is the function of the primitive, the challenger's coin-indexed samplers,
the adversary and the resource bound the challenger enforces. The game constructors take the
samplers and the adversary as functions of one coin `ω : Fin n`; the hardness propositions of
section 2e instantiate them only with samplers that read the challenger coordinate of `ω` and
adversaries that read the adversary coordinate. -/

private theorem iteOfPos {α : Type} {p : Prop} [Decidable p] (hp : p) (a b : α) :
    (if p then a else b) = a := by
  cases ‹Decidable p› with
  | isTrue _ => rfl
  | isFalse hn => exact False.elim (hn hp)

private theorem iteOfNeg {α : Type} {p : Prop} [Decidable p] (hnp : ¬ p) (a b : α) :
    (if p then a else b) = b := by
  cases ‹Decidable p› with
  | isTrue hp => exact False.elim (hnp hp)
  | isFalse _ => rfl

private theorem andTrueSplit {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | cases h

/-- Two games with the same win predicate are the same game. -/
theorem FinGame.ext_win {n : Nat} {G G' : FinGame n} (h : ∀ ω : Fin n, G.win ω = G'.win ω) :
    G = G' := by
  cases G with
  | mk p w =>
    cases G' with
    | mk p' w' =>
      have hw : w = w' := funext h
      subst hw
      rfl

/-- Run an oracle program against a deterministic stateful challenger oracle, returning the
    program's output and the challenger's final state. -/
def Code.play {E : Iface} {R σ : Type} (oracle : σ → (q : E.Query) → E.Resp q × σ) :
    Code E R → σ → R × σ
  | .ret v, st => (v, st)
  | .call q k, st => Code.play oracle (k (oracle st q).1) (oracle st q).2

theorem Code.play_ret {E : Iface} {R σ : Type} (oracle : σ → (q : E.Query) → E.Resp q × σ)
    (v : R) (st : σ) : Code.play oracle (.ret v) st = (v, st) := by
  rfl

theorem Code.play_call {E : Iface} {R σ : Type} (oracle : σ → (q : E.Query) → E.Resp q × σ)
    (q : E.Query) (k : E.Resp q → Code E R) (st : σ) :
    Code.play oracle (.call q k) st = Code.play oracle (k (oracle st q).1) (oracle st q).2 := by
  rfl

/-- A property of the challenger state preserved by every oracle answer holds at the end of
    every run. -/
theorem Code.play_invariant {E : Iface} {R σ : Type}
    (oracle : σ → (q : E.Query) → E.Resp q × σ) (P : σ → Prop)
    (hStep : ∀ (st : σ) (q : E.Query), P st → P (oracle st q).2) :
    ∀ (c : Code E R) (st : σ), P st → P (Code.play oracle c st).2
  | .ret _, _, h => h
  | .call q k, st, h =>
    Code.play_invariant oracle P hStep (k (oracle st q).1) (oracle st q).2 (hStep st q h)

/-- Oracle interface with byte-string queries and byte-string answers. -/
@[expose, reducible] def byteOracleIface : Iface where
  Query := Bytes
  Resp _ := Bytes


/-! ### 2.0 Counting facts, independent coin coordinates and uniform samplers

An experiment separates the challenger's coins from the adversary's. `CoinSplit n nC nA` presents
the coin space `Fin n` as the product of a challenger coordinate `Fin nC` and an adversary
coordinate `Fin nA`: every pair of coordinates is hit by exactly one coin, so under the uniform
measure on `Fin n` the two coordinates are independent and each is uniform. The challenger's
samples are functions of the first coordinate; an adversary is a function of the second
coordinate and of the oracle answers. `UniformOn support sample` says that a sampler is a
bijection from its coin space onto `support`, i.e. the sample is uniform on that set. -/

/-- A game won on every coin has probability `1`: it is not bounded by any `ε < 1`. -/
theorem FinGame.not_bound_of_forall_win {n : Nat} (G : FinGame n)
    (hWin : ∀ ω : Fin n, G.win ω = true) {ε : RatBound} (hε : ε.num < ε.den) :
    ¬ GameBound G.winProb ε := by
  intro h
  have h' : G.winCount * ε.den ≤ ε.num * n := h
  rw [G.winCount_of_forall_win hWin, Nat.mul_comm ε.num n] at h'
  exact Nat.not_le_of_lt hε (Nat.le_of_mul_le_mul_left h' G.samplePos)

/-- A game lost on every coin has probability `0`. -/
theorem FinGame.bound_zero_of_forall_lose {n : Nat} (G : FinGame n)
    (hLose : ∀ ω : Fin n, G.win ω = false) : GameBound G.winProb RatBound.zero := by
  show G.winCount * 1 ≤ 0 * n
  rw [G.winCount_of_forall_lose hLose, Nat.zero_mul, Nat.zero_mul]
  exact Nat.le_refl 0

/-- Every game has probability at most `1`. -/
theorem FinGame.winProb_le_one {n : Nat} (G : FinGame n) : GameBound G.winProb RatBound.one := by
  have hMono := event_le_reduction_win G (FinGame.mk G.samplePos (fun _ => true)) (fun _ _ => rfl)
  have hAll : (FinGame.mk G.samplePos (fun _ => true)).winCount = n :=
    FinGame.winCount_of_forall_win _ (fun _ => rfl)
  have h' : G.winCount * n ≤ (FinGame.mk G.samplePos (fun _ => true)).winCount * n := hMono
  rw [hAll] at h'
  show G.winCount * 1 ≤ 1 * n
  rw [Nat.mul_one, Nat.one_mul]
  exact Nat.le_of_mul_le_mul_right h' G.samplePos

/-- A distinguisher that outputs `true` on every coin of `G₀` and `false` on every coin of `G₁`
    has advantage `1`: it is not bounded by any `ε < 1`. -/
theorem advDist_not_bound_of_always_never {n : Nat} (G₀ G₁ : FinGame n)
    (h₀ : ∀ ω : Fin n, G₀.win ω = true) (h₁ : ∀ ω : Fin n, G₁.win ω = false)
    {ε : RatBound} (hε : ε.num < ε.den) : ¬ GameBound (AdvDist G₀ G₁) ε := by
  intro h
  have h' : natAbsDiff G₀.winCount G₁.winCount * ε.den ≤ ε.num * n := h
  have hAbs : natAbsDiff n 0 = n := by
    unfold natAbsDiff
    rw [iteOfNeg (Nat.not_le_of_lt G₀.samplePos)]
    rfl
  rw [G₀.winCount_of_forall_win h₀, G₁.winCount_of_forall_lose h₁, hAbs,
    Nat.mul_comm ε.num n] at h'
  exact Nat.not_le_of_lt hε (Nat.le_of_mul_le_mul_left h' G₀.samplePos)

/-- Presentation of the coin space `Fin n` as the product of a challenger coordinate and an
    adversary coordinate. -/
structure CoinSplit (n nC nA : Nat) where
  /-- The challenger's coordinate of a coin. -/
  chal : Fin n → Fin nC
  /-- The adversary's coordinate of a coin. -/
  advc : Fin n → Fin nA
  /-- The coin with the given coordinates. -/
  pair : Fin nC → Fin nA → Fin n
  chal_pair : ∀ (c : Fin nC) (a : Fin nA), chal (pair c a) = c
  advc_pair : ∀ (c : Fin nC) (a : Fin nA), advc (pair c a) = a
  pair_eta : ∀ ω : Fin n, pair (chal ω) (advc ω) = ω

/-- The adversary's coordinate does not determine the challenger's: for a fixed adversary coin
    every challenger coin occurs. -/
theorem CoinSplit.chal_free {n nC nA : Nat} (π : CoinSplit n nC nA) (a : Fin nA) (c : Fin nC) :
    ∃ ω : Fin n, π.advc ω = a ∧ π.chal ω = c :=
  ⟨π.pair c a, π.advc_pair c a, π.chal_pair c a⟩

/-- The split with a single adversary coin (a deterministic adversary). -/
def CoinSplit.challengerOnly (n : Nat) : CoinSplit n n 1 where
  chal ω := ω
  advc _ := ⟨0, Nat.one_pos⟩
  pair c _ := c
  chal_pair _ _ := rfl
  advc_pair _ a := Fin.ext (Nat.lt_one_iff.mp a.2).symm
  pair_eta _ := rfl

theorem prodCoin_right_pos {nC nA : Nat} (ω : Fin (nC * nA)) : 0 < nA :=
  Nat.pos_of_ne_zero (fun h => by
    subst h
    exact Nat.not_lt_zero _ ω.2)

theorem prodCoin_quot_lt {nC nA : Nat} (ω : Fin (nC * nA)) : ω.val / nA < nC :=
  (Nat.div_lt_iff_lt_mul (prodCoin_right_pos ω)).mpr ω.2

theorem prodCoin_pair_lt {nC nA : Nat} (c : Fin nC) (a : Fin nA) :
    c.val * nA + a.val < nC * nA :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left a.2 _)
    (Nat.succ_mul c.val nA ▸ Nat.mul_le_mul_right nA c.2)

theorem prodCoin_pair_quot {nC nA : Nat} (c : Fin nC) (a : Fin nA) :
    (c.val * nA + a.val) / nA = c.val := by
  rw [Nat.mul_comm c.val nA, Nat.mul_add_div (Nat.lt_of_le_of_lt (Nat.zero_le _) a.2),
    Nat.div_eq_of_lt a.2]
  rfl

theorem prodCoin_pair_rem {nC nA : Nat} (c : Fin nC) (a : Fin nA) :
    (c.val * nA + a.val) % nA = a.val := by
  rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt a.2]

/-- The split of `Fin (nC * nA)` by quotient and remainder. -/
def CoinSplit.prod (nC nA : Nat) : CoinSplit (nC * nA) nC nA where
  chal ω := ⟨ω.val / nA, prodCoin_quot_lt ω⟩
  advc ω := ⟨ω.val % nA, Nat.mod_lt _ (prodCoin_right_pos ω)⟩
  pair c a := ⟨c.val * nA + a.val, prodCoin_pair_lt c a⟩
  chal_pair c a := Fin.ext (prodCoin_pair_quot c a)
  advc_pair c a := Fin.ext (prodCoin_pair_rem c a)
  pair_eta ω := Fin.ext (Nat.div_add_mod' ω.val nA)

/-- `sample` is a uniform sampler on `support`: a bijection from its coin space onto that set. -/
structure UniformOn {n : Nat} {α : Type} (support : α → Prop) (sample : Fin n → α) : Prop where
  mem : ∀ c : Fin n, support (sample c)
  injective : ∀ c c' : Fin n, sample c = sample c' → c = c'
  surjective : ∀ x : α, support x → ∃ c : Fin n, sample c = x

/-- The one-coin sampler is uniform on a one-element set. -/
theorem uniformOn_unique {α : Type} (support : α → Prop) (x : α) (hx : support x)
    (hUnique : ∀ y : α, support y → y = x) : UniformOn support (fun _ : Fin 1 => x) where
  mem _ := hx
  injective c c' _ :=
    Fin.ext ((Nat.lt_one_iff.mp c.2).trans (Nat.lt_one_iff.mp c'.2).symm)
  surjective y hy := ⟨⟨0, Nat.one_pos⟩, (hUnique y hy).symm⟩

/-- A sampler that ignores a coin is not uniform: the constant sampler on two coins has no
    `UniformOn` law, whatever the support. -/
theorem constant_sampler_not_uniform {α : Type} (support : α → Prop) (x : α) :
    ¬ UniformOn support (fun _ : Fin 2 => x) := by
  intro h
  have hEq := h.injective ⟨0, by decide⟩ ⟨1, by decide⟩ rfl
  exact absurd (congrArg Fin.val hEq) (by decide)

/-- A challenger sample that is uniform on a set with two different elements is not determined
    by the adversary's coordinate: whatever function of the adversary coin is used as a guess,
    some coin with that adversary coordinate carries a different sample. -/
theorem CoinSplit.sample_not_adversary_determined {n nC nA : Nat} {α : Type} [DecidableEq α]
    (π : CoinSplit n nC nA) {support : α → Prop} {sample : Fin nC → α}
    (hU : UniformOn support sample) {x y : α} (hx : support x) (hy : support y) (hxy : x ≠ y)
    (guess : Fin nA → α) (a : Fin nA) :
    ∃ ω : Fin n, π.advc ω = a ∧ sample (π.chal ω) ≠ guess (π.advc ω) := by
  obtain ⟨cx, hcx⟩ := hU.surjective x hx
  obtain ⟨cy, hcy⟩ := hU.surjective y hy
  if hg : guess a = x then
    refine ⟨π.pair cy a, π.advc_pair cy a, ?_⟩
    rw [π.chal_pair, π.advc_pair, hcy, hg]
    exact fun h => hxy h.symm
  else
    refine ⟨π.pair cx a, π.advc_pair cx a, ?_⟩
    rw [π.chal_pair, π.advc_pair, hcx]
    exact fun h => hg h.symm

/-! ### 2a. `SM-DT-TCR` and `SM-DT-PRE` for a tweakable hash `th seed tweak message` -/

/-- Query of the target-commitment phase of the multi-target, distinct-tweak experiments. -/
inductive TargetQuery where
  /-- Commit to a target under `tweak`. `SM-DT-TCR` uses `msg` as the target message;
      `SM-DT-PRE` ignores it and uses a hidden challenger sample. -/
  | target (tweak : Bytes) (msg : Bytes)
  /-- End the commitment phase and receive the public seed. -/
  | reveal
  deriving DecidableEq, Repr

/-- Interface of the target experiments: a refused query is answered `none`. -/
@[expose, reducible] def targetIface : Iface where
  Query := TargetQuery
  Resp _ := Option Bytes

/-- Challenger state of the target experiments. `targets` lists `(tweak, input)` in order. -/
structure TargetState where
  seed : Bytes
  targets : List (Bytes × Bytes)
  revealed : Bool

/-- `SM-DT-TCR` challenger. A target is admitted only before `reveal`, under a tweak not used
    before, and while fewer than `q` targets are committed. -/
def smDtTcrOracle (th : Bytes → Bytes → Bytes → Bytes) (q : Nat) (st : TargetState) :
    (qr : targetIface.Query) → targetIface.Resp qr × TargetState
  | .target t m =>
    if st.revealed = false ∧ st.targets.length < q ∧ t ∉ st.targets.map Prod.fst then
      (some (th st.seed t m), { st with targets := st.targets ++ [(t, m)] })
    else (none, st)
  | .reveal => (some st.seed, { st with revealed := true })

/-- `SM-DT-PRE` challenger. The `i`-th admitted target is the hidden sample `hidden i`; the
    adversary learns `th seed tweak (hidden i)`. -/
def smDtPreOracle (th : Bytes → Bytes → Bytes → Bytes) (q : Nat) (hidden : Nat → Bytes)
    (st : TargetState) : (qr : targetIface.Query) → targetIface.Resp qr × TargetState
  | .target t _ =>
    if st.revealed = false ∧ st.targets.length < q ∧ t ∉ st.targets.map Prod.fst then
      (some (th st.seed t (hidden st.targets.length)),
        { st with targets := st.targets ++ [(t, hidden st.targets.length)] })
    else (none, st)
  | .reveal => (some st.seed, { st with revealed := true })

/-- Adversary output of the target experiments: the tweak of the attacked target, the input the
    adversary claims was committed under it (unused by `SM-DT-PRE`), and its own input. -/
structure TargetBreak where
  tweak : Bytes
  committed : Bytes
  candidate : Bytes
  deriving DecidableEq, Repr

/-- `SM-DT-TCR` win: `(tweak, committed)` is a committed target and `candidate` is a different
    input with the same digest under the challenger's seed. -/
def smDtTcrWin (th : Bytes → Bytes → Bytes → Bytes) (st : TargetState) (out : TargetBreak) :
    Bool :=
  decide ((out.tweak, out.committed) ∈ st.targets) &&
    (decide (out.candidate ≠ out.committed) &&
      decide (th st.seed out.tweak out.candidate = th st.seed out.tweak out.committed))

/-- `SM-DT-PRE` win: `candidate` has the digest of the hidden sample committed under `tweak`. -/
def smDtPreWin (th : Bytes → Bytes → Bytes → Bytes) (st : TargetState) (out : TargetBreak) :
    Bool :=
  st.targets.any (fun e =>
    decide (e.1 = out.tweak) && decide (th st.seed e.1 out.candidate = th st.seed e.1 e.2))

/-- Invariant of the target challengers: the seed is the sampled one, committed tweaks are
    pairwise distinct, and at most `q` targets are committed. -/
def TargetState.Inv (q : Nat) (seed₀ : Bytes) (st : TargetState) : Prop :=
  st.seed = seed₀ ∧ (st.targets.map Prod.fst).Nodup ∧ st.targets.length ≤ q

private theorem targetInv_extend {q : Nat} {seed₀ : Bytes} {st : TargetState} {t x : Bytes}
    (h : st.Inv q seed₀)
    (hc : st.revealed = false ∧ st.targets.length < q ∧ t ∉ st.targets.map Prod.fst) :
    TargetState.Inv q seed₀ { st with targets := st.targets ++ [(t, x)] } := by
  obtain ⟨hSeed, hNd, _⟩ := h
  refine ⟨hSeed, ?_, ?_⟩
  · show ((st.targets ++ [(t, x)]).map Prod.fst).Nodup
    rw [List.map_append]
    refine List.nodup_append.mpr ⟨hNd, List.Pairwise.cons (fun _ h => nomatch h) .nil, ?_⟩
    intro a ha b hb hab
    have hb' : b = t := by
      rcases List.mem_cons.mp hb with h | h
      · exact h
      · exact nomatch h
    exact hc.2.2 (hb' ▸ hab ▸ ha)
  · show (st.targets ++ [(t, x)]).length ≤ q
    rw [List.length_append]
    exact hc.2.1

theorem smDtTcrOracle_inv (th : Bytes → Bytes → Bytes → Bytes) (q : Nat) (seed₀ : Bytes)
    (st : TargetState) (qr : TargetQuery) (h : st.Inv q seed₀) :
    (smDtTcrOracle th q st qr).2.Inv q seed₀ := by
  cases qr with
  | reveal => exact h
  | target t m =>
    if hc : st.revealed = false ∧ st.targets.length < q ∧ t ∉ st.targets.map Prod.fst then
      have hEq : smDtTcrOracle th q st (.target t m) =
          (some (th st.seed t m), { st with targets := st.targets ++ [(t, m)] }) :=
        iteOfPos hc _ _
      rw [hEq]
      exact targetInv_extend h hc
    else
      have hEq : smDtTcrOracle th q st (.target t m) = (none, st) := iteOfNeg hc _ _
      rw [hEq]
      exact h

theorem smDtPreOracle_inv (th : Bytes → Bytes → Bytes → Bytes) (q : Nat) (hidden : Nat → Bytes)
    (seed₀ : Bytes) (st : TargetState) (qr : TargetQuery) (h : st.Inv q seed₀) :
    (smDtPreOracle th q hidden st qr).2.Inv q seed₀ := by
  cases qr with
  | reveal => exact h
  | target t m =>
    if hc : st.revealed = false ∧ st.targets.length < q ∧ t ∉ st.targets.map Prod.fst then
      have hEq : smDtPreOracle th q hidden st (.target t m) =
          (some (th st.seed t (hidden st.targets.length)),
            { st with targets := st.targets ++ [(t, hidden st.targets.length)] }) :=
        iteOfPos hc _ _
      rw [hEq]
      exact targetInv_extend h hc
    else
      have hEq : smDtPreOracle th q hidden st (.target t m) = (none, st) := iteOfNeg hc _ _
      rw [hEq]
      exact h

/-- One run of the `SM-DT-TCR` experiment on coin `ω`. -/
def smDtTcrRun {n : Nat} (th : Bytes → Bytes → Bytes → Bytes) (q : Nat) (seed : Fin n → Bytes)
    (adv : Fin n → Code targetIface TargetBreak) (ω : Fin n) : TargetBreak × TargetState :=
  Code.play (smDtTcrOracle th q) (adv ω) ⟨seed ω, [], false⟩

/-- **`SM-DT-TCR` game** of the tweakable hash `th` with seed sampler `seed`, target budget `q`
    and adversary `adv`. -/
def smDtTcrGame {n : Nat} (hPos : 0 < n) (th : Bytes → Bytes → Bytes → Bytes) (q : Nat)
    (seed : Fin n → Bytes) (adv : Fin n → Code targetIface TargetBreak) : FinGame n :=
  ⟨hPos, fun ω => smDtTcrWin th (smDtTcrRun th q seed adv ω).2 (smDtTcrRun th q seed adv ω).1⟩

/-- One run of the `SM-DT-PRE` experiment on coin `ω`. -/
def smDtPreRun {n : Nat} (th : Bytes → Bytes → Bytes → Bytes) (q : Nat) (seed : Fin n → Bytes)
    (hidden : Fin n → Nat → Bytes) (adv : Fin n → Code targetIface TargetBreak) (ω : Fin n) :
    TargetBreak × TargetState :=
  Code.play (smDtPreOracle th q (hidden ω)) (adv ω) ⟨seed ω, [], false⟩

/-- **`SM-DT-PRE` game** of `th` with seed sampler `seed`, hidden-input sampler `hidden`,
    target budget `q` and adversary `adv`. -/
def smDtPreGame {n : Nat} (hPos : 0 < n) (th : Bytes → Bytes → Bytes → Bytes) (q : Nat)
    (seed : Fin n → Bytes) (hidden : Fin n → Nat → Bytes)
    (adv : Fin n → Code targetIface TargetBreak) : FinGame n :=
  ⟨hPos, fun ω =>
    smDtPreWin th (smDtPreRun th q seed hidden adv ω).2 (smDtPreRun th q seed hidden adv ω).1⟩

/-- The `SM-DT-TCR` challenger ends every run with the sampled seed, pairwise distinct target
    tweaks and at most `q` targets. -/
theorem smDtTcrRun_inv {n : Nat} (th : Bytes → Bytes → Bytes → Bytes) (q : Nat)
    (seed : Fin n → Bytes) (adv : Fin n → Code targetIface TargetBreak) (ω : Fin n) :
    (smDtTcrRun th q seed adv ω).2.Inv q (seed ω) :=
  Code.play_invariant (smDtTcrOracle th q) (TargetState.Inv q (seed ω))
    (fun st qr h => smDtTcrOracle_inv th q (seed ω) st qr h) (adv ω) ⟨seed ω, [], false⟩
    ⟨rfl, .nil, Nat.zero_le q⟩

theorem smDtPreRun_inv {n : Nat} (th : Bytes → Bytes → Bytes → Bytes) (q : Nat)
    (seed : Fin n → Bytes) (hidden : Fin n → Nat → Bytes)
    (adv : Fin n → Code targetIface TargetBreak) (ω : Fin n) :
    (smDtPreRun th q seed hidden adv ω).2.Inv q (seed ω) :=
  Code.play_invariant (smDtPreOracle th q (hidden ω)) (TargetState.Inv q (seed ω))
    (fun st qr h => smDtPreOracle_inv th q (hidden ω) (seed ω) st qr h) (adv ω)
    ⟨seed ω, [], false⟩ ⟨rfl, .nil, Nat.zero_le q⟩

/-- A winning coin of the `SM-DT-TCR` game yields a second preimage of `th (seed ω) tweak` at
    a target the challenger admitted. -/
theorem smDtTcrGame_win_sound {n : Nat} (hPos : 0 < n) (th : Bytes → Bytes → Bytes → Bytes)
    (q : Nat) (seed : Fin n → Bytes) (adv : Fin n → Code targetIface TargetBreak) (ω : Fin n)
    (hWin : (smDtTcrGame hPos th q seed adv).win ω = true) :
    ∃ (t m m' : Bytes), (t, m) ∈ (smDtTcrRun th q seed adv ω).2.targets ∧ m' ≠ m ∧
      th (seed ω) t m' = th (seed ω) t m := by
  have hSeed := (smDtTcrRun_inv th q seed adv ω).1
  have hG : (smDtTcrGame hPos th q seed adv).win ω = true := hWin
  have hW : smDtTcrWin th (smDtTcrRun th q seed adv ω).2 (smDtTcrRun th q seed adv ω).1 = true :=
    hG
  unfold smDtTcrWin at hW
  obtain ⟨hMem, hRest⟩ := andTrueSplit hW
  obtain ⟨hNe, hCol⟩ := andTrueSplit hRest
  rw [hSeed] at hCol
  exact ⟨_, _, _, of_decide_eq_true hMem, of_decide_eq_true hNe, of_decide_eq_true hCol⟩

/-- A winning coin of the `SM-DT-PRE` game yields a preimage of the digest of a hidden target
    the challenger admitted. -/
theorem smDtPreGame_win_sound {n : Nat} (hPos : 0 < n) (th : Bytes → Bytes → Bytes → Bytes)
    (q : Nat) (seed : Fin n → Bytes) (hidden : Fin n → Nat → Bytes)
    (adv : Fin n → Code targetIface TargetBreak) (ω : Fin n)
    (hWin : (smDtPreGame hPos th q seed hidden adv).win ω = true) :
    ∃ (t x m' : Bytes), (t, x) ∈ (smDtPreRun th q seed hidden adv ω).2.targets ∧
      th (seed ω) t m' = th (seed ω) t x := by
  have hSeed := (smDtPreRun_inv th q seed hidden adv ω).1
  have hG : (smDtPreGame hPos th q seed hidden adv).win ω = true := hWin
  have hW : smDtPreWin th (smDtPreRun th q seed hidden adv ω).2
      (smDtPreRun th q seed hidden adv ω).1 = true := hG
  unfold smDtPreWin at hW
  obtain ⟨e, hMem, hE⟩ := List.any_eq_true.mp hW
  obtain ⟨_, hCol⟩ := andTrueSplit hE
  rw [hSeed] at hCol
  exact ⟨e.1, e.2, _, hMem, of_decide_eq_true hCol⟩

/-! ### 2b. Interleaved target subset resilience for a keyed subset hash `hmsg rand message` -/

/-- `ITSR` challenger. The `i`-th admitted message is answered with the randomizer `rand i`
    and logged with it; beyond `q` messages the answer is `[]` and nothing is logged. -/
def itsrOracle (q : Nat) (rand : Nat → Bytes) (log : List (Bytes × Bytes)) :
    (msg : byteOracleIface.Query) → byteOracleIface.Resp msg × List (Bytes × Bytes) :=
  fun (msg : Bytes) =>
    if log.length < q then (rand log.length, log ++ [(rand log.length, msg)]) else ([], log)

/-- `ITSR` win: `(randomizer, message)` was not answered by the challenger and every position
    selected by `hmsg` on it is selected on some answered pair. -/
def itsrWin (hmsg : Bytes → Bytes → List Nat) (log : List (Bytes × Bytes))
    (out : Bytes × Bytes) : Bool :=
  !decide (out ∈ log) &&
    (hmsg out.1 out.2).all (fun x => log.any (fun e => decide (x ∈ hmsg e.1 e.2)))

/-- One run of the `ITSR` experiment on coin `ω`. -/
def itsrRun {n : Nat} (q : Nat) (rand : Fin n → Nat → Bytes)
    (adv : Fin n → Code byteOracleIface (Bytes × Bytes)) (ω : Fin n) :
    (Bytes × Bytes) × List (Bytes × Bytes) :=
  Code.play (itsrOracle q (rand ω)) (adv ω) []

/-- **`ITSR` game** of the subset hash `hmsg` with randomizer sampler `rand`, signing budget `q`
    and adversary `adv`. -/
def itsrGame {n : Nat} (hPos : 0 < n) (hmsg : Bytes → Bytes → List Nat) (q : Nat)
    (rand : Fin n → Nat → Bytes) (adv : Fin n → Code byteOracleIface (Bytes × Bytes)) :
    FinGame n :=
  ⟨hPos, fun ω => itsrWin hmsg (itsrRun q rand adv ω).2 (itsrRun q rand adv ω).1⟩

/-- A winning coin of the `ITSR` game is a fresh pair covered by the answered pairs. -/
theorem itsrGame_win_sound {n : Nat} (hPos : 0 < n) (hmsg : Bytes → Bytes → List Nat) (q : Nat)
    (rand : Fin n → Nat → Bytes) (adv : Fin n → Code byteOracleIface (Bytes × Bytes)) (ω : Fin n)
    (hWin : (itsrGame hPos hmsg q rand adv).win ω = true) :
    (itsrRun q rand adv ω).1 ∉ (itsrRun q rand adv ω).2 ∧
    ∀ x ∈ hmsg (itsrRun q rand adv ω).1.1 (itsrRun q rand adv ω).1.2,
      ∃ e ∈ (itsrRun q rand adv ω).2, x ∈ hmsg e.1 e.2 := by
  have hG : (itsrGame hPos hmsg q rand adv).win ω = true := hWin
  have hW : itsrWin hmsg (itsrRun q rand adv ω).2 (itsrRun q rand adv ω).1 = true := hG
  unfold itsrWin at hW
  obtain ⟨hFresh, hCover⟩ := andTrueSplit hW
  refine ⟨fun hMem => ?_, fun x hx => ?_⟩
  · rw [decide_eq_true hMem] at hFresh
    cases hFresh
  · obtain ⟨e, he, hxe⟩ := List.any_eq_true.mp (List.all_eq_true.mp hCover x hx)
    exact ⟨e, he, of_decide_eq_true hxe⟩

/-- The `ITSR` challenger answers at most `q` messages. -/
theorem itsrRun_log_length_le {n : Nat} (q : Nat) (rand : Fin n → Nat → Bytes)
    (adv : Fin n → Code byteOracleIface (Bytes × Bytes)) (ω : Fin n) :
    (itsrRun q rand adv ω).2.length ≤ q :=
  Code.play_invariant (itsrOracle q (rand ω)) (fun log => log.length ≤ q)
    (fun log (msg : Bytes) h => by
      if hc : log.length < q then
        have hEq : itsrOracle q (rand ω) log msg =
            (rand ω log.length, log ++ [(rand ω log.length, msg)]) := iteOfPos hc _ _
        rw [hEq]
        show (log ++ [(rand ω log.length, msg)]).length ≤ q
        rw [List.length_append]
        exact hc
      else
        have hEq : itsrOracle q (rand ω) log msg = ([], log) := iteOfNeg hc _ _
        rw [hEq]
        exact h)
    (adv ω) [] (Nat.zero_le q)

/-! ### 2c. Keyed PRF distinguishing for `prf key input` -/

/-- Function oracle with a query budget: the first `q` queries are answered by `f`, later ones
    by `[]`. The state is the number of queries answered so far. -/
def budgetedFunOracle (f : Bytes → Bytes) (q : Nat) (used : Nat) :
    (x : byteOracleIface.Query) → byteOracleIface.Resp x × Nat :=
  fun x => if used < q then (f x, used + 1) else ([], used)

/-- **Real PRF game**: the distinguisher `adv` queries `prf (key ω)` at most `q` times and
    wins when it outputs `true`. -/
def prfRealGame {n : Nat} (hPos : 0 < n) (prf : Bytes → Bytes → Bytes) (q : Nat)
    (key : Fin n → Bytes) (adv : Fin n → Code byteOracleIface Bool) : FinGame n :=
  ⟨hPos, fun ω => (Code.play (budgetedFunOracle (prf (key ω)) q) (adv ω) 0).1⟩

/-- **Ideal PRF game**: the same distinguisher against the sampled function `rf ω`. -/
def prfIdealGame {n : Nat} (hPos : 0 < n) (q : Nat) (rf : Fin n → Bytes → Bytes)
    (adv : Fin n → Code byteOracleIface Bool) : FinGame n :=
  ⟨hPos, fun ω => (Code.play (budgetedFunOracle (rf ω) q) (adv ω) 0).1⟩

/-- On a coin where the keyed function and the sampled function are the same function, the
    two PRF games give the same verdict. -/
theorem prfGames_agree_of_fun_eq {n : Nat} (hPos : 0 < n) (prf : Bytes → Bytes → Bytes)
    (q : Nat) (key : Fin n → Bytes) (rf : Fin n → Bytes → Bytes)
    (adv : Fin n → Code byteOracleIface Bool) (ω : Fin n) (hEq : prf (key ω) = rf ω) :
    (prfRealGame hPos prf q key adv).win ω = (prfIdealGame hPos q rf adv).win ω := by
  show (Code.play (budgetedFunOracle (prf (key ω)) q) (adv ω) 0).1 =
    (Code.play (budgetedFunOracle (rf ω) q) (adv ω) 0).1
  rw [hEq]

/-! ### 2d. Lattice experiments over `R_q = ℤ_q[X]/(X^N + 1)` and dual-LPN over `𝔽₂` -/

/-- Product in `ℤ_q[X]/(X^N + 1)` on coefficient lists (little-endian, missing coefficients
    read as `0`). -/
def rqMul (N q : Nat) (a s : List Nat) : List Nat :=
  (List.range N).map (fun k =>
    ((List.range N).foldl (fun acc i =>
      if i ≤ k then acc + a.getD i 0 * s.getD (k - i) 0
      else acc + (q - (a.getD i 0 * s.getD (N + k - i) 0) % q)) 0) % q)

/-- Coefficient-wise sum modulo `q`. -/
def rqAdd (q : Nat) (a b : List Nat) : List Nat :=
  List.zipWith (fun x y => (x + y) % q) a b

/-- `c` is a residue modulo `q` whose centered representative has absolute value at most `β`. -/
def centeredLe (q β c : Nat) : Bool :=
  decide (c < q) && (decide (c ≤ β) || decide (q - β ≤ c))

/-- `p` has `N` coefficients, all residues modulo `q`. -/
def rqPolyOk (N q : Nat) (p : List Nat) : Bool :=
  decide (p.length = N) && p.all (fun c => decide (c < q))

/-- `p` has `N` coefficients, all of centered absolute value at most `β`. -/
def rqShortOk (N q β : Nat) (p : List Nat) : Bool :=
  decide (p.length = N) && p.all (centeredLe q β)

/-- The `m` real Ring-LWE samples `(aᵢ, aᵢ · s + eᵢ)`. -/
def rlweRealSamples (N q m : Nat) (a : Nat → List Nat) (s : List Nat) (e : Nat → List Nat) :
    List (List Nat × List Nat) :=
  (List.range m).map (fun i => (a i, rqAdd q (rqMul N q (a i) s) (e i)))

/-- The `m` samples `(aᵢ, uᵢ)` with independent second components. -/
def rlweUniformSamples (m : Nat) (a u : Nat → List Nat) : List (List Nat × List Nat) :=
  (List.range m).map (fun i => (a i, u i))

/-- **Module-SIS win**: `z` has `cols` polynomials of `N` coefficients, each of centered
    absolute value at most `β`, is not zero, and `A · z = 0` in `R_q^{rows}`. -/
def moduleSisWin (N q cols β : Nat) (A : List (List (List Nat))) (z : List (List Nat)) : Bool :=
  decide (z.length = cols) &&
    (z.all (rqShortOk N q β) &&
      (z.any (fun p => p.any (fun c => decide (c ≠ 0))) &&
        A.all (fun row =>
          decide ((List.zipWith (rqMul N q) row z).foldl (rqAdd q) (List.replicate N 0) =
            List.replicate N 0))))

/-- **Module-SIS game**: the adversary receives the matrix `matrix ω` and wins with a short
    nonzero kernel vector. -/
def moduleSisGame {n : Nat} (hPos : 0 < n) (N q cols β : Nat)
    (matrix : Fin n → List (List (List Nat)))
    (adv : Fin n → List (List (List Nat)) → List (List Nat)) : FinGame n :=
  ⟨hPos, fun ω => moduleSisWin N q cols β (matrix ω) (adv ω (matrix ω))⟩

/-- A winning coin of the Module-SIS game carries a short nonzero vector annihilated by every
    row of the sampled matrix. -/
theorem moduleSisGame_win_sound {n : Nat} (hPos : 0 < n) (N q cols β : Nat)
    (matrix : Fin n → List (List (List Nat)))
    (adv : Fin n → List (List (List Nat)) → List (List Nat)) (ω : Fin n)
    (hWin : (moduleSisGame hPos N q cols β matrix adv).win ω = true) :
    (adv ω (matrix ω)).length = cols ∧
    (∀ p ∈ adv ω (matrix ω), rqShortOk N q β p = true) ∧
    (∃ p ∈ adv ω (matrix ω), ∃ c ∈ p, c ≠ 0) ∧
    (∀ row ∈ matrix ω,
      (List.zipWith (rqMul N q) row (adv ω (matrix ω))).foldl (rqAdd q) (List.replicate N 0) =
        List.replicate N 0) := by
  have hG : (moduleSisGame hPos N q cols β matrix adv).win ω = true := hWin
  have hW : moduleSisWin N q cols β (matrix ω) (adv ω (matrix ω)) = true := hG
  unfold moduleSisWin at hW
  obtain ⟨hLen, h1⟩ := andTrueSplit hW
  obtain ⟨hShort, h2⟩ := andTrueSplit h1
  obtain ⟨hNz, hKer⟩ := andTrueSplit h2
  refine ⟨of_decide_eq_true hLen, fun p hp => List.all_eq_true.mp hShort p hp, ?_,
    fun row hr => of_decide_eq_true (List.all_eq_true.mp hKer row hr)⟩
  obtain ⟨p, hp, hpNz⟩ := List.any_eq_true.mp hNz
  obtain ⟨c, hc, hcNz⟩ := List.any_eq_true.mp hpNz
  exact ⟨p, hp, c, hc, of_decide_eq_true hcNz⟩

/-- Syndrome `H · e` over `𝔽₂`, one bit per row of `H`. -/
def lpnSyndrome (H : List (List Bool)) (e : List Bool) : List Bool :=
  H.map (fun row => (List.zipWith (fun a b => a && b) row e).foldl Bool.xor false)

/-- Shape of a dual-LPN instance: `H` has `rows` rows of `N` bits, the noise `e` has `N` bits
    of which exactly `weight` are set, and `u` has `rows` bits. -/
def dualLpnShapeOk (N rows weight : Nat) (H : List (List Bool)) (e u : List Bool) : Bool :=
  decide (H.length = rows) && (H.all (fun row => decide (row.length = N)) &&
    (decide (e.length = N) && (decide (e.count true = weight) && decide (u.length = rows))))

/-! ### 2e. Hardness of a primitive against a class of adversaries

Hardness is a proposition about the primitive and a class `𝒜` of adversaries, indexed by the
sample-space sizes of the experiment, the challenger's query budget and the bound `ε`. It
quantifies over every coin space split into a challenger coordinate and an adversary coordinate
(`CoinSplit`), every challenger sampler that is uniform on the stated sample set (`UniformOn`),
and every randomized adversary whose program on each adversary coin belongs to `𝒜`. Nothing in
the index is chosen by an adversary.

The class `𝒜` is where a resource bound on adversaries lives. This development has no
running-time model, so it cannot define the class of efficient adversaries; `𝒜` is a parameter,
and a theorem that uses `…Hard 𝒜` also needs its reduction adversaries to belong to `𝒜`, as
explicit hypotheses.

For the unrestricted class `fun _ => True` the hash propositions are false, not merely strong:
`smDtPreHard_unrestricted_refuted` shows `SmDtPreHard (fun _ => True) th …` fails for every
tweakable hash `th`, every budget `q ≥ 1` and every `ε < 1` (commit one target, take the seed
from `reveal`, search the `inputLen`-byte strings for a preimage). The analogous facts, that
`SmDtTcrHard` and `ItsrHard` fail on the unrestricted class for every primitive with bounded
output and `PrfHard` once `q · outLen > keyLen`, are not proved here. A proposition `…Hard 𝒜`
is therefore meaningful only for a class `𝒜` that excludes such search adversaries; that `𝒜`
is such a class and that a deployed primitive is hard against it is an assumption outside this
logic. What this layer proves is the other direction: degenerate primitives are refuted for
every class containing one explicit short program (section 2g). -/

/-- **`SM-DT-TCR` hardness** of the tweakable hash `th` against the adversary class `𝒜`, with
    uniform `seedLen`-byte seeds: every adversary with programs in `𝒜` wins the `q`-target
    experiment with probability at most `ε`. -/
@[expose] def SmDtTcrHard (𝒜 : Code targetIface TargetBreak → Prop)
    (th : Bytes → Bytes → Bytes → Bytes) (seedLen q : Nat) (ε : RatBound) : Prop :=
  ∀ (n nC nA : Nat) (hPos : 0 < n) (π : CoinSplit n nC nA) (seed : Fin nC → Bytes),
    UniformOn (fun s : Bytes => s.length = seedLen) seed →
    ∀ adv : Fin nA → Code targetIface TargetBreak, (∀ a : Fin nA, 𝒜 (adv a)) →
      GameBound (smDtTcrGame hPos th q (fun ω => seed (π.chal ω))
        (fun ω => adv (π.advc ω))).winProb ε

/-- Sample set of the `SM-DT-PRE` challenger: a `seedLen`-byte seed and `q` hidden inputs of
    `inputLen` bytes. -/
def SmDtPreSampleOk (seedLen inputLen q : Nat) (x : Bytes × List Bytes) : Prop :=
  x.1.length = seedLen ∧ x.2.length = q ∧ ∀ h ∈ x.2, h.length = inputLen

/-- **`SM-DT-PRE` hardness** of `th` against the adversary class `𝒜`: with a uniform seed and
    `q` independent uniform hidden inputs, every adversary with programs in `𝒜` wins with
    probability at most `ε`. False for the unrestricted class
    (`smDtPreHard_unrestricted_refuted`). -/
@[expose] def SmDtPreHard (𝒜 : Code targetIface TargetBreak → Prop)
    (th : Bytes → Bytes → Bytes → Bytes) (seedLen inputLen q : Nat) (ε : RatBound) : Prop :=
  ∀ (n nC nA : Nat) (hPos : 0 < n) (π : CoinSplit n nC nA) (sample : Fin nC → Bytes × List Bytes),
    UniformOn (SmDtPreSampleOk seedLen inputLen q) sample →
    ∀ adv : Fin nA → Code targetIface TargetBreak, (∀ a : Fin nA, 𝒜 (adv a)) →
      GameBound (smDtPreGame hPos th q (fun ω => (sample (π.chal ω)).1)
        (fun ω i => (sample (π.chal ω)).2.getD i []) (fun ω => adv (π.advc ω))).winProb ε

/-- Sample set of the `ITSR` challenger: `q` randomizers of `randLen` bytes. -/
def ItsrSampleOk (randLen q : Nat) (x : List Bytes) : Prop :=
  x.length = q ∧ ∀ r ∈ x, r.length = randLen

/-- **`ITSR` hardness** of the keyed subset hash `hmsg` against the adversary class `𝒜`: with
    `q` independent uniform randomizers, every adversary with programs in `𝒜` wins with
    probability at most `ε`. -/
@[expose] def ItsrHard (𝒜 : Code byteOracleIface (Bytes × Bytes) → Prop)
    (hmsg : Bytes → Bytes → List Nat) (randLen q : Nat) (ε : RatBound) : Prop :=
  ∀ (n nC nA : Nat) (hPos : 0 < n) (π : CoinSplit n nC nA) (rand : Fin nC → List Bytes),
    UniformOn (ItsrSampleOk randLen q) rand →
    ∀ adv : Fin nA → Code byteOracleIface (Bytes × Bytes), (∀ a : Fin nA, 𝒜 (adv a)) →
      GameBound (itsrGame hPos hmsg q (fun ω i => (rand (π.chal ω)).getD i [])
        (fun ω => adv (π.advc ω))).winProb ε

/-- Sample set of the PRF challenger: a `keyLen`-byte key and a function that maps
    `inLen`-byte inputs to `outLen`-byte outputs and every other input to `[]`. -/
def PrfSampleOk (keyLen inLen outLen : Nat) (x : Bytes × (Bytes → Bytes)) : Prop :=
  x.1.length = keyLen ∧
  ∀ inp : Bytes, (inp.length = inLen → (x.2 inp).length = outLen) ∧
    (inp.length ≠ inLen → x.2 inp = [])

/-- **PRF hardness** of `prf` against the distinguisher class `𝒜`: with a uniform key and an
    independent uniform function, every `q`-query distinguisher with programs in `𝒜` has
    advantage at most `ε`. -/
@[expose] def PrfHard (𝒜 : Code byteOracleIface Bool → Prop)
    (prf : Bytes → Bytes → Bytes) (keyLen inLen outLen q : Nat) (ε : RatBound) : Prop :=
  ∀ (n nC nA : Nat) (hPos : 0 < n) (π : CoinSplit n nC nA)
    (sample : Fin nC → Bytes × (Bytes → Bytes)),
    UniformOn (PrfSampleOk keyLen inLen outLen) sample →
    ∀ adv : Fin nA → Code byteOracleIface Bool, (∀ a : Fin nA, 𝒜 (adv a)) →
      GameBound
        (AdvDist
          (prfRealGame hPos prf q (fun ω => (sample (π.chal ω)).1) (fun ω => adv (π.advc ω)))
          (prfIdealGame hPos q (fun ω => (sample (π.chal ω)).2) (fun ω => adv (π.advc ω)))) ε

/-- Challenger sample of the decision Ring-LWE experiment. -/
structure RlweSample where
  a : List (List Nat)
  s : List Nat
  e : List (List Nat)
  u : List (List Nat)

/-- Sample set of the decision Ring-LWE challenger over `ℤ_q[X]/(X^N + 1)`: `m` ring elements
    `aᵢ`, a secret and `m` errors of centered absolute value at most `β`, and `m` ring elements
    `uᵢ`. -/
def RlweSampleOk (N q m β : Nat) (x : RlweSample) : Prop :=
  (x.a.length = m ∧ ∀ p ∈ x.a, rqPolyOk N q p = true) ∧
  rqShortOk N q β x.s = true ∧
  (x.e.length = m ∧ ∀ p ∈ x.e, rqShortOk N q β p = true) ∧
  (x.u.length = m ∧ ∀ p ∈ x.u, rqPolyOk N q p = true)

/-- The real game of the Ring-LWE experiment: the distinguisher sees `(aᵢ, aᵢ · s + eᵢ)`. -/
def rlweRealGame {n nC nA : Nat} (hPos : 0 < n) (π : CoinSplit n nC nA) (N q m : Nat)
    (sample : Fin nC → RlweSample) (dist : Fin nA → List (List Nat × List Nat) → Bool) :
    FinGame n :=
  ⟨hPos, fun ω => dist (π.advc ω)
    (rlweRealSamples N q m (fun i => (sample (π.chal ω)).a.getD i []) (sample (π.chal ω)).s
      (fun i => (sample (π.chal ω)).e.getD i []))⟩

/-- The ideal game of the Ring-LWE experiment: the distinguisher sees `(aᵢ, uᵢ)`. -/
def rlweUniformGame {n nC nA : Nat} (hPos : 0 < n) (π : CoinSplit n nC nA) (m : Nat)
    (sample : Fin nC → RlweSample) (dist : Fin nA → List (List Nat × List Nat) → Bool) :
    FinGame n :=
  ⟨hPos, fun ω => dist (π.advc ω)
    (rlweUniformSamples m (fun i => (sample (π.chal ω)).a.getD i [])
      (fun i => (sample (π.chal ω)).u.getD i []))⟩

/-- **Decision Ring-LWE hardness** over `ℤ_q[X]/(X^N + 1)` with `m` samples and secret and
    errors uniform among the elements of centered absolute value at most `β`: every
    distinguisher with decision functions in the class `𝒜` has advantage at most `ε`. -/
def DecisionRlweHard (𝒜 : (List (List Nat × List Nat) → Bool) → Prop) (N q m β : Nat)
    (ε : RatBound) : Prop :=
  ∀ (n nC nA : Nat) (hPos : 0 < n) (π : CoinSplit n nC nA) (sample : Fin nC → RlweSample),
    UniformOn (RlweSampleOk N q m β) sample →
    ∀ dist : Fin nA → List (List Nat × List Nat) → Bool, (∀ a : Fin nA, 𝒜 (dist a)) →
      GameBound (AdvDist (rlweRealGame hPos π N q m sample dist)
        (rlweUniformGame hPos π m sample dist)) ε

/-- Sample set of the Module-SIS challenger: a `rows × cols` matrix over `ℤ_q[X]/(X^N + 1)`. -/
def SisMatrixOk (N q rows cols : Nat) (A : List (List (List Nat))) : Prop :=
  A.length = rows ∧ ∀ row ∈ A, row.length = cols ∧ ∀ p ∈ row, rqPolyOk N q p = true

/-- **Module-SIS hardness** for a uniform `rows × cols` matrix and infinity-norm bound `β`:
    every adversary with solvers in the class `𝒜` outputs a short nonzero kernel vector with
    probability at most `ε`. -/
def ModuleSisHard (𝒜 : (List (List (List Nat)) → List (List Nat)) → Prop)
    (N q rows cols β : Nat) (ε : RatBound) : Prop :=
  ∀ (n nC nA : Nat) (hPos : 0 < n) (π : CoinSplit n nC nA)
    (matrix : Fin nC → List (List (List Nat))),
    UniformOn (SisMatrixOk N q rows cols) matrix →
    ∀ adv : Fin nA → List (List (List Nat)) → List (List Nat), (∀ a : Fin nA, 𝒜 (adv a)) →
      GameBound (moduleSisGame hPos N q cols β (fun ω => matrix (π.chal ω))
        (fun ω => adv (π.advc ω))).winProb ε

/-- Challenger sample of the dual-LPN experiment. -/
structure DualLpnSample where
  parity : List (List Bool)
  noise : List Bool
  uniform : List Bool

/-- **Dual-LPN hardness** for a uniform parity-check matrix with `rows` rows over `𝔽₂^N`, noise
    uniform among the vectors of Hamming weight `weight`, and a uniform `rows`-bit string:
    every distinguisher of `(H, H · e)` from `(H, u)` with decision functions in the class `𝒜`
    has advantage at most `ε`. -/
def DualLpnHard (𝒜 : (List (List Bool) × List Bool → Bool) → Prop) (N rows weight : Nat)
    (ε : RatBound) : Prop :=
  ∀ (n nC nA : Nat) (hPos : 0 < n) (π : CoinSplit n nC nA) (sample : Fin nC → DualLpnSample),
    UniformOn (fun x : DualLpnSample =>
      dualLpnShapeOk N rows weight x.parity x.noise x.uniform = true) sample →
    ∀ dist : Fin nA → List (List Bool) × List Bool → Bool, (∀ a : Fin nA, 𝒜 (dist a)) →
      GameBound
        (AdvDist
          (FinGame.mk hPos (fun ω => dist (π.advc ω)
            ((sample (π.chal ω)).parity,
              lpnSyndrome (sample (π.chal ω)).parity (sample (π.chal ω)).noise)))
          (FinGame.mk hPos (fun ω => dist (π.advc ω)
            ((sample (π.chal ω)).parity, (sample (π.chal ω)).uniform)))) ε

/-- Regular noise: `blocks` consecutive blocks of `blockLen` bits with exactly one set bit in
    each. This is the noise of a PCG that punctures one leaf per GGM tree
    (`densePcgV3Profile`: `treesPerBundle` blocks of `leavesPerTree` bits). -/
def regularNoiseOk (blocks blockLen : Nat) (e : List Bool) : Bool :=
  decide (e.length = blocks * blockLen) &&
    (List.range blocks).all
      (fun b => decide (((e.drop (b * blockLen)).take blockLen).count true = 1))

/-- Challenger sample of the regular dual-LPN experiment for a fixed code. -/
structure RegularDualLpnSample where
  noise : List Bool
  uniform : List Bool

/-- **Regular dual-LPN hardness for a fixed public code.** `H` is one fixed parity-check
    matrix (the deployed generator uses a fixed quasi-cyclic tap matrix, not a sampled one);
    the noise is uniform among the regular vectors of `blocks` blocks of `blockLen` bits; the
    comparison string is uniform among the strings of `H.length` bits. Every distinguisher of
    `H · e` from the uniform string with decision functions in the class `𝒜` has advantage at
    most `ε`.

    `DualLpnHard` above is the textbook variant (uniform matrix, noise uniform among all
    vectors of a given Hamming weight). The two are different assumptions: a regular vector
    has weight `blocks`, but a vector of weight `blocks` need not be regular
    (`regularNoise_not_implied_by_weight`), and a fixed code has no matrix coins. -/
def RegularDualLpnHard (𝒜 : (List Bool → Bool) → Prop) (H : List (List Bool))
    (blocks blockLen : Nat) (ε : RatBound) : Prop :=
  ∀ (n nC nA : Nat) (hPos : 0 < n) (π : CoinSplit n nC nA)
    (sample : Fin nC → RegularDualLpnSample),
    UniformOn (fun x : RegularDualLpnSample =>
      regularNoiseOk blocks blockLen x.noise = true ∧ x.uniform.length = H.length) sample →
    ∀ dist : Fin nA → List Bool → Bool, (∀ a : Fin nA, 𝒜 (dist a)) →
      GameBound
        (AdvDist
          (FinGame.mk hPos (fun ω => dist (π.advc ω)
            (lpnSyndrome H (sample (π.chal ω)).noise)))
          (FinGame.mk hPos (fun ω => dist (π.advc ω) (sample (π.chal ω)).uniform))) ε

/-- A vector with one set bit in each of two blocks of two bits is regular. -/
theorem regularNoise_example : regularNoiseOk 2 2 [true, false, false, true] = true := by decide

/-- Hamming weight `blocks` does not make a vector regular: `1100` has weight two and both set
    bits in the first block. -/
theorem regularNoise_not_implied_by_weight :
    ¬ (([true, true, false, false].count true = 2) →
      regularNoiseOk 2 2 [true, true, false, false] = true) := by decide

/-- For the code with no parity checks the syndrome and the comparison string are both empty:
    the two games coincide and the advantage is `0`, whatever the class. The proposition
    carries information only for a code with rows. -/
theorem regularDualLpnHard_noRows (𝒜 : (List Bool → Bool) → Prop) (blocks blockLen : Nat) :
    RegularDualLpnHard 𝒜 [] blocks blockLen RatBound.zero := by
  intro n nC nA hPos π sample hU dist _
  have hEq : FinGame.mk hPos (fun ω => dist (π.advc ω)
        (lpnSyndrome [] (sample (π.chal ω)).noise)) =
      FinGame.mk hPos (fun ω => dist (π.advc ω) (sample (π.chal ω)).uniform) := by
    refine FinGame.ext_win (fun ω => ?_)
    have hLen : (sample (π.chal ω)).uniform.length = 0 := (hU.mem (π.chal ω)).2
    have hNil : (sample (π.chal ω)).uniform = [] := List.eq_nil_of_length_eq_zero hLen
    show dist (π.advc ω) (lpnSyndrome [] (sample (π.chal ω)).noise) =
      dist (π.advc ω) (sample (π.chal ω)).uniform
    rw [hNil]
    rfl
  rw [hEq]
  exact adv_refl _

/-- Hardness weakens along the bound. -/
theorem SmDtTcrHard.mono {𝒜 : Code targetIface TargetBreak → Prop}
    {th : Bytes → Bytes → Bytes → Bytes} {seedLen q : Nat}
    {ε ε' : RatBound} (h : SmDtTcrHard 𝒜 th seedLen q ε) (hLe : ε.le ε') :
    SmDtTcrHard 𝒜 th seedLen q ε' :=
  fun n nC nA hPos π seed hU adv hA => GameBound.trans (h n nC nA hPos π seed hU adv hA) hLe

theorem DecisionRlweHard.bound {𝒜 : (List (List Nat × List Nat) → Bool) → Prop}
    {N q m β : Nat} {ε : RatBound} (h : DecisionRlweHard 𝒜 N q m β ε)
    (n nC nA : Nat) (hPos : 0 < n) (π : CoinSplit n nC nA) (sample : Fin nC → RlweSample)
    (hU : UniformOn (RlweSampleOk N q m β) sample)
    (dist : Fin nA → List (List Nat × List Nat) → Bool) (hD : ∀ a : Fin nA, 𝒜 (dist a)) :
    GameBound (AdvDist (rlweRealGame hPos π N q m sample dist)
      (rlweUniformGame hPos π m sample dist)) ε :=
  h n nC nA hPos π sample hU dist hD

theorem ModuleSisHard.bound {𝒜 : (List (List (List Nat)) → List (List Nat)) → Prop}
    {N q rows cols β : Nat} {ε : RatBound} (h : ModuleSisHard 𝒜 N q rows cols β ε)
    (n nC nA : Nat) (hPos : 0 < n) (π : CoinSplit n nC nA)
    (matrix : Fin nC → List (List (List Nat)))
    (hU : UniformOn (SisMatrixOk N q rows cols) matrix)
    (adv : Fin nA → List (List (List Nat)) → List (List Nat)) (hA : ∀ a : Fin nA, 𝒜 (adv a)) :
    GameBound (moduleSisGame hPos N q cols β (fun ω => matrix (π.chal ω))
      (fun ω => adv (π.advc ω))).winProb ε :=
  h n nC nA hPos π matrix hU adv hA

theorem RegularDualLpnHard.bound {𝒜 : (List Bool → Bool) → Prop}
    {H : List (List Bool)} {blocks blockLen : Nat} {ε : RatBound}
    (h : RegularDualLpnHard 𝒜 H blocks blockLen ε)
    (n nC nA : Nat) (hPos : 0 < n) (π : CoinSplit n nC nA)
    (sample : Fin nC → RegularDualLpnSample)
    (hU : UniformOn (fun x : RegularDualLpnSample =>
      regularNoiseOk blocks blockLen x.noise = true ∧ x.uniform.length = H.length) sample)
    (dist : Fin nA → List Bool → Bool) (hD : ∀ a : Fin nA, 𝒜 (dist a)) :
    GameBound
      (AdvDist
        (FinGame.mk hPos (fun ω => dist (π.advc ω)
          (lpnSyndrome H (sample (π.chal ω)).noise)))
        (FinGame.mk hPos (fun ω => dist (π.advc ω) (sample (π.chal ω)).uniform))) ε :=
  h n nC nA hPos π sample hU dist hD

theorem SmDtPreHard.mono {𝒜 : Code targetIface TargetBreak → Prop}
    {th : Bytes → Bytes → Bytes → Bytes} {seedLen inputLen q : Nat}
    {ε ε' : RatBound} (h : SmDtPreHard 𝒜 th seedLen inputLen q ε) (hLe : ε.le ε') :
    SmDtPreHard 𝒜 th seedLen inputLen q ε' :=
  fun n nC nA hPos π sample hU adv hA => GameBound.trans (h n nC nA hPos π sample hU adv hA) hLe

theorem ItsrHard.mono {𝒜 : Code byteOracleIface (Bytes × Bytes) → Prop}
    {hmsg : Bytes → Bytes → List Nat} {randLen q : Nat}
    {ε ε' : RatBound} (h : ItsrHard 𝒜 hmsg randLen q ε) (hLe : ε.le ε') :
    ItsrHard 𝒜 hmsg randLen q ε' :=
  fun n nC nA hPos π rand hU adv hA => GameBound.trans (h n nC nA hPos π rand hU adv hA) hLe

/-- Hardness against a class gives hardness against every smaller class. -/
theorem SmDtTcrHard.anti {𝒜 ℬ : Code targetIface TargetBreak → Prop}
    {th : Bytes → Bytes → Bytes → Bytes} {seedLen q : Nat} {ε : RatBound}
    (h : SmDtTcrHard 𝒜 th seedLen q ε) (hSub : ∀ c, ℬ c → 𝒜 c) : SmDtTcrHard ℬ th seedLen q ε :=
  fun n nC nA hPos π seed hU adv hA => h n nC nA hPos π seed hU adv (fun a => hSub _ (hA a))

theorem SmDtPreHard.anti {𝒜 ℬ : Code targetIface TargetBreak → Prop}
    {th : Bytes → Bytes → Bytes → Bytes} {seedLen inputLen q : Nat} {ε : RatBound}
    (h : SmDtPreHard 𝒜 th seedLen inputLen q ε) (hSub : ∀ c, ℬ c → 𝒜 c) :
    SmDtPreHard ℬ th seedLen inputLen q ε :=
  fun n nC nA hPos π sample hU adv hA => h n nC nA hPos π sample hU adv (fun a => hSub _ (hA a))

/-- With bound `1` the proposition holds for every hash and every class:
    `SmDtTcrHard 𝒜 th seedLen q 1` carries no information about `th`. -/
theorem smDtTcrHard_one (𝒜 : Code targetIface TargetBreak → Prop)
    (th : Bytes → Bytes → Bytes → Bytes) (seedLen q : Nat) :
    SmDtTcrHard 𝒜 th seedLen q RatBound.one :=
  fun _ _ _ _ _ _ _ _ _ => FinGame.winProb_le_one _

/-- Against the empty class every bound holds: `SmDtPreHard (fun _ => False) th … 0` carries no
    information about `th`. A hardness hypothesis is only as strong as the class it is stated
    for, and that class must contain the reduction adversaries of the theorem that uses it. -/
theorem smDtPreHard_emptyClass (th : Bytes → Bytes → Bytes → Bytes) (seedLen inputLen q : Nat) :
    SmDtPreHard (fun _ => False) th seedLen inputLen q RatBound.zero :=
  fun _ _ _ hPos π _ _ _ hA => (hA (π.advc ⟨0, hPos⟩)).elim

/-- With zero samples the two Ring-LWE games are the same game, so the advantage is `0`. -/
theorem decisionRlweHard_zero_samples (𝒜 : (List (List Nat × List Nat) → Bool) → Prop)
    (N q β : Nat) : DecisionRlweHard 𝒜 N q 0 β RatBound.zero := by
  intro n nC nA hPos π sample _ dist _
  have hEq : rlweRealGame hPos π N q 0 sample dist = rlweUniformGame hPos π 0 sample dist :=
    FinGame.ext_win (fun _ => rfl)
  rw [hEq]
  exact adv_refl _

/-- **Three-way union bound for hash-based signatures.** If every winning coin of `G` is a
    winning coin of an `ITSR`, an `SM-DT-TCR` or an `SM-DT-PRE` experiment whose challengers are
    uniform and whose adversaries read only their adversary coordinate and run programs of the
    classes the hardness hypotheses are stated for, then `Pr[G] ≤ εItsr + εTcr + εPre`. Each
    experiment may split the coin space differently. -/
theorem hashSig_forger_bound {n : Nat} (G : FinGame n)
    {𝒜I : Code byteOracleIface (Bytes × Bytes) → Prop}
    {𝒜T 𝒜P : Code targetIface TargetBreak → Prop}
    {hmsg : Bytes → Bytes → List Nat} {th : Bytes → Bytes → Bytes → Bytes}
    {randLen seedLen inputLen qItsr qTcr qPre : Nat} {εItsr εTcr εPre : RatBound}
    (hItsr : ItsrHard 𝒜I hmsg randLen qItsr εItsr)
    (hTcr : SmDtTcrHard 𝒜T th seedLen qTcr εTcr)
    (hPre : SmDtPreHard 𝒜P th seedLen inputLen qPre εPre)
    {nCi nAi nCt nAt nCp nAp : Nat}
    (πi : CoinSplit n nCi nAi) (πt : CoinSplit n nCt nAt) (πp : CoinSplit n nCp nAp)
    (rand : Fin nCi → List Bytes) (hRand : UniformOn (ItsrSampleOk randLen qItsr) rand)
    (seed : Fin nCt → Bytes) (hSeed : UniformOn (fun s : Bytes => s.length = seedLen) seed)
    (sample : Fin nCp → Bytes × List Bytes)
    (hSample : UniformOn (SmDtPreSampleOk seedLen inputLen qPre) sample)
    (advI : Fin nAi → Code byteOracleIface (Bytes × Bytes)) (hAdvI : ∀ a, 𝒜I (advI a))
    (advT : Fin nAt → Code targetIface TargetBreak) (hAdvT : ∀ a, 𝒜T (advT a))
    (advP : Fin nAp → Code targetIface TargetBreak) (hAdvP : ∀ a, 𝒜P (advP a))
    (hExtract : ∀ ω : Fin n, G.win ω = true →
      (itsrGame G.samplePos hmsg qItsr (fun ω i => (rand (πi.chal ω)).getD i [])
        (fun ω => advI (πi.advc ω))).win ω = true ∨
      (smDtTcrGame G.samplePos th qTcr (fun ω => seed (πt.chal ω))
        (fun ω => advT (πt.advc ω))).win ω = true ∨
      (smDtPreGame G.samplePos th qPre (fun ω => (sample (πp.chal ω)).1)
        (fun ω i => (sample (πp.chal ω)).2.getD i []) (fun ω => advP (πp.advc ω))).win ω = true) :
    GameBound G.winProb ((εItsr.add εTcr).add εPre) :=
  event_le_three_reductions G _ _ _ hExtract
    (hItsr n nCi nAi G.samplePos πi rand hRand advI hAdvI)
    (hTcr n nCt nAt G.samplePos πt seed hSeed advT hAdvT)
    (hPre n nCp nAp G.samplePos πp sample hSample advP hAdvP)

/-! ### 2f. The games are determined by their indices -/

/-- Adversary against the constant tweakable hash: commit `[]` under tweak `[]`, then present
    `[0]` as a second preimage. -/
def constHashTcrAdv : Code targetIface TargetBreak :=
  .call (.target [] []) (fun _ => .ret ⟨[], [], [0]⟩)

/-- Against the constant hash the collision adversary wins on the single coin: the game of a
    locale indexed by this hash and this adversary is not an always-losing game. -/
theorem smDtTcr_constHash_adversary_wins :
    ¬ ((smDtTcrGame Nat.one_pos (fun _ _ _ => []) 1 (fun _ => []) (fun _ => constHashTcrAdv)).win
        ⟨0, Nat.one_pos⟩ = false) := by
  decide

/-- Presenting the committed message itself never wins `SM-DT-TCR`. -/
theorem smDtTcr_committed_message_loses (th : Bytes → Bytes → Bytes → Bytes) (st : TargetState)
    (t m : Bytes) : ¬ (smDtTcrWin th st ⟨t, m, m⟩ = true) := by
  intro h
  unfold smDtTcrWin at h
  obtain ⟨_, hRest⟩ := andTrueSplit h
  exact of_decide_eq_true (andTrueSplit hRest).1 rfl

/-- An output naming a pair the challenger answered never wins `ITSR`. -/
theorem itsr_answered_pair_loses (hmsg : Bytes → Bytes → List Nat) (log : List (Bytes × Bytes))
    (out : Bytes × Bytes) (hMem : out ∈ log) : ¬ (itsrWin hmsg log out = true) := by
  intro h
  unfold itsrWin at h
  have hFresh := (andTrueSplit h).1
  rw [decide_eq_true hMem] at hFresh
  cases hFresh

/-- Distinguisher that queries `[]` and outputs whether the answer is `[]`. -/
def emptyAnswerDistinguisher : Code byteOracleIface Bool :=
  .call ([] : Bytes) (fun (r : Bytes) => .ret (decide (r = [])))

/-- The real and ideal PRF games are different games: the distinguisher separates the
    constant-`[]` function from the constant-`[0]` function. -/
theorem prf_real_ideal_games_differ :
    ¬ ((prfRealGame Nat.one_pos (fun _ _ => []) 1 (fun _ => []) (fun _ => emptyAnswerDistinguisher)).win
        ⟨0, Nat.one_pos⟩ =
      (prfIdealGame Nat.one_pos 1 (fun _ _ => [0]) (fun _ => emptyAnswerDistinguisher)).win
        ⟨0, Nat.one_pos⟩) := by
  decide

/-- `X · X = -1` in `ℤ₅[X]/(X² + 1)`: the product is negacyclic, not cyclic. -/
theorem rqMul_negacyclic_wraparound :
    rqMul 2 5 [0, 1] [0, 1] = [4, 0] ∧ ¬ (rqMul 2 5 [0, 1] [0, 1] = [1, 0]) := by
  decide

/-- The zero vector never wins Module-SIS. -/
theorem moduleSis_zero_vector_loses (N q cols β : Nat) (A : List (List (List Nat))) :
    ¬ (moduleSisWin N q cols β A (List.replicate cols (List.replicate N 0)) = true) := by
  intro h
  unfold moduleSisWin at h
  obtain ⟨_, h1⟩ := andTrueSplit h
  obtain ⟨_, h2⟩ := andTrueSplit h1
  obtain ⟨hNz, _⟩ := andTrueSplit h2
  obtain ⟨p, hp, hpNz⟩ := List.any_eq_true.mp hNz
  obtain ⟨c, hc, hcNz⟩ := List.any_eq_true.mp hpNz
  have hpEq : p = List.replicate N 0 := (List.mem_replicate.mp hp).2
  rw [hpEq] at hc
  exact of_decide_eq_true hcNz (List.mem_replicate.mp hc).2

#tooth_pair smDtTcrGame_win_sound vs smDtTcr_constHash_adversary_wins
#tooth_pair smDtTcrGame_win_sound vs smDtTcr_committed_message_loses
#tooth_pair itsrGame_win_sound vs itsr_answered_pair_loses
#tooth_pair prfGames_agree_of_fun_eq vs prf_real_ideal_games_differ
#tooth_pair moduleSisGame_win_sound vs moduleSis_zero_vector_loses

/-! ### 2g. Degenerate primitives are refuted

For each search experiment, a primitive that carries no hardness is shown not to satisfy the
hardness proposition for any `ε < 1` and any class containing one explicit program: that
program wins on every coin whatever the uniform challenger samples are. Section 2h refutes
`SM-DT-PRE` hardness of every primitive against the unrestricted class. -/

private theorem constHashTcr_play (q : Nat) (hq : 0 < q) (s : Bytes) :
    Code.play (smDtTcrOracle (fun _ _ _ => []) q) constHashTcrAdv ⟨s, [], false⟩ =
      (⟨[], [], [0]⟩, ⟨s, [([], [])], false⟩) := by
  have hc : (false = false ∧ ([] : List (Bytes × Bytes)).length < q ∧
      ([] : Bytes) ∉ ([] : List (Bytes × Bytes)).map Prod.fst) :=
    ⟨rfl, hq, fun h => nomatch h⟩
  have hEq : smDtTcrOracle (fun _ _ _ => []) q ⟨s, [], false⟩ (.target [] []) =
      (some [], ⟨s, [([], [])], false⟩) := iteOfPos hc _ _
  show Code.play (smDtTcrOracle (fun _ _ _ => []) q)
    (TargetBreak.mk [] [] [0] |> Code.ret)
    (smDtTcrOracle (fun _ _ _ => []) q ⟨s, [], false⟩ (.target [] [])).2 = _
  rw [hEq]
  rfl

/-- **The constant tweakable hash is not `SM-DT-TCR` hard** against any class containing the
    two-line program `constHashTcrAdv`. For every seed length for which a uniform seed sampler
    is given, every budget `q ≥ 1` and every `ε < 1`. -/
theorem smDtTcrHard_constHash_refuted {nC : Nat} (hPos : 0 < nC) (seedLen q : Nat)
    (seed : Fin nC → Bytes) (hU : UniformOn (fun s : Bytes => s.length = seedLen) seed)
    (𝒜 : Code targetIface TargetBreak → Prop) (h𝒜 : 𝒜 constHashTcrAdv)
    (hq : 0 < q) {ε : RatBound} (hε : ε.num < ε.den) :
    ¬ SmDtTcrHard 𝒜 (fun _ _ _ => []) seedLen q ε := by
  intro h
  refine FinGame.not_bound_of_forall_win _ (fun ω => ?_) hε
    (h nC nC 1 hPos (CoinSplit.challengerOnly nC) seed hU (fun _ => constHashTcrAdv)
      (fun _ => h𝒜))
  show smDtTcrWin (fun _ _ _ => [])
    (Code.play (smDtTcrOracle (fun _ _ _ => []) q) constHashTcrAdv ⟨seed ω, [], false⟩).2
    (Code.play (smDtTcrOracle (fun _ _ _ => []) q) constHashTcrAdv ⟨seed ω, [], false⟩).1 = true
  rw [constHashTcr_play q hq]
  rfl

/-- The empty byte string is the uniform sample of the zero-length seed space. -/
theorem uniformOn_emptyBytes : UniformOn (fun s : Bytes => s.length = 0) (fun _ : Fin 1 => []) :=
  uniformOn_unique _ [] rfl (fun _ hy => List.eq_nil_of_length_eq_zero hy)

/-- Unconditional instance of the refutation: with seedless hashing, the constant hash is not
    `SM-DT-TCR` hard for any `ε < 1`. -/
theorem smDtTcrHard_constHash_refuted_seedless (𝒜 : Code targetIface TargetBreak → Prop)
    (h𝒜 : 𝒜 constHashTcrAdv) (q : Nat) (hq : 0 < q) {ε : RatBound}
    (hε : ε.num < ε.den) : ¬ SmDtTcrHard 𝒜 (fun _ _ _ => []) 0 q ε :=
  smDtTcrHard_constHash_refuted Nat.one_pos 0 q _ uniformOn_emptyBytes 𝒜 h𝒜 hq hε

private theorem constHashPre_play (q : Nat) (hq : 0 < q) (hidden : Nat → Bytes) (s : Bytes) :
    Code.play (smDtPreOracle (fun _ _ _ => []) q hidden) constHashTcrAdv ⟨s, [], false⟩ =
      (⟨[], [], [0]⟩, ⟨s, [([], hidden 0)], false⟩) := by
  have hc : (false = false ∧ ([] : List (Bytes × Bytes)).length < q ∧
      ([] : Bytes) ∉ ([] : List (Bytes × Bytes)).map Prod.fst) :=
    ⟨rfl, hq, fun h => nomatch h⟩
  have hEq : smDtPreOracle (fun _ _ _ => []) q hidden ⟨s, [], false⟩ (.target [] []) =
      (some [], ⟨s, [([], hidden 0)], false⟩) := iteOfPos hc _ _
  show Code.play (smDtPreOracle (fun _ _ _ => []) q hidden)
    (TargetBreak.mk [] [] [0] |> Code.ret)
    (smDtPreOracle (fun _ _ _ => []) q hidden ⟨s, [], false⟩ (.target [] [])).2 = _
  rw [hEq]
  rfl

/-- **The constant tweakable hash is not `SM-DT-PRE` hard**: any input is a preimage. -/
theorem smDtPreHard_constHash_refuted {nC : Nat} (hPos : 0 < nC) (seedLen inputLen q : Nat)
    (sample : Fin nC → Bytes × List Bytes)
    (hU : UniformOn (SmDtPreSampleOk seedLen inputLen q) sample)
    (𝒜 : Code targetIface TargetBreak → Prop) (h𝒜 : 𝒜 constHashTcrAdv)
    (hq : 0 < q) {ε : RatBound} (hε : ε.num < ε.den) :
    ¬ SmDtPreHard 𝒜 (fun _ _ _ => []) seedLen inputLen q ε := by
  intro h
  refine FinGame.not_bound_of_forall_win _ (fun ω => ?_) hε
    (h nC nC 1 hPos (CoinSplit.challengerOnly nC) sample hU (fun _ => constHashTcrAdv)
      (fun _ => h𝒜))
  show smDtPreWin (fun _ _ _ => [])
    (Code.play (smDtPreOracle (fun _ _ _ => []) q (fun i => (sample ω).2.getD i []))
      constHashTcrAdv ⟨(sample ω).1, [], false⟩).2
    (Code.play (smDtPreOracle (fun _ _ _ => []) q (fun i => (sample ω).2.getD i []))
      constHashTcrAdv ⟨(sample ω).1, [], false⟩).1 = true
  rw [constHashPre_play q hq]
  rfl

/-- **A subset hash that selects no position is not `ITSR` hard**: the adversary that asks
    nothing and outputs `([], [])` is covered by the empty log. -/
theorem itsrHard_emptySelector_refuted {nC : Nat} (hPos : 0 < nC) (randLen q : Nat)
    (rand : Fin nC → List Bytes) (hU : UniformOn (ItsrSampleOk randLen q) rand)
    (𝒜 : Code byteOracleIface (Bytes × Bytes) → Prop) (h𝒜 : 𝒜 (.ret ([], [])))
    {ε : RatBound} (hε : ε.num < ε.den) :
    ¬ ItsrHard 𝒜 (fun _ _ => []) randLen q ε := by
  intro h
  exact FinGame.not_bound_of_forall_win _ (fun _ => rfl) hε
    (h nC nC 1 hPos (CoinSplit.challengerOnly nC) rand hU (fun _ => .ret ([], []))
      (fun _ => h𝒜))

/-- Distinguisher that queries the all-zero `inLen`-byte input and outputs whether the answer
    is empty. -/
def emptyOutputDistinguisher (inLen : Nat) : Code byteOracleIface Bool :=
  .call (List.replicate inLen (0 : UInt8) : Bytes) (fun (r : Bytes) => .ret (decide (r = [])))

private theorem emptyOutputDistinguisher_play (f : Bytes → Bytes) (q inLen : Nat) (hq : 0 < q) :
    (Code.play (budgetedFunOracle f q) (emptyOutputDistinguisher inLen) 0).1 =
      decide (f (List.replicate inLen (0 : UInt8)) = []) := by
  have hEq : budgetedFunOracle f q 0 (List.replicate inLen (0 : UInt8)) =
      (f (List.replicate inLen (0 : UInt8)), 0 + 1) := iteOfPos hq _ _
  show (Code.play (budgetedFunOracle f q)
    ((fun (r : Bytes) => (Code.ret (decide (r = [])) : Code byteOracleIface Bool))
      (budgetedFunOracle f q 0 (List.replicate inLen (0 : UInt8))).1)
    (budgetedFunOracle f q 0 (List.replicate inLen (0 : UInt8))).2).1 = _
  rw [hEq]
  rfl

/-- **A keyed function with empty outputs is not a PRF** onto `outLen ≥ 1` bytes: one query
    separates it from every function of the ideal sample set with advantage `1`. -/
theorem prfHard_emptyOutput_refuted {nC : Nat} (hPos : 0 < nC) (keyLen inLen outLen q : Nat)
    (sample : Fin nC → Bytes × (Bytes → Bytes))
    (hU : UniformOn (PrfSampleOk keyLen inLen outLen) sample)
    (𝒜 : Code byteOracleIface Bool → Prop) (h𝒜 : 𝒜 (emptyOutputDistinguisher inLen))
    (hOut : 0 < outLen) (hq : 0 < q) {ε : RatBound} (hε : ε.num < ε.den) :
    ¬ PrfHard 𝒜 (fun _ _ => []) keyLen inLen outLen q ε := by
  intro h
  refine advDist_not_bound_of_always_never _ _ (fun ω => ?_) (fun ω => ?_) hε
    (h nC nC 1 hPos (CoinSplit.challengerOnly nC) sample hU
      (fun _ => emptyOutputDistinguisher inLen) (fun _ => h𝒜))
  · exact (emptyOutputDistinguisher_play (fun _ => []) q inLen hq).trans (decide_eq_true rfl)
  · have hLen : ((sample ω).2 (List.replicate inLen (0 : UInt8))).length = outLen :=
      ((hU.mem ω).2 (List.replicate inLen (0 : UInt8))).1 List.length_replicate
    have hNe : ¬ ((sample ω).2 (List.replicate inLen (0 : UInt8)) = []) := fun hNil => by
      rw [hNil] at hLen
      exact Nat.ne_of_lt hOut hLen
    exact (emptyOutputDistinguisher_play (sample ω).2 q inLen hq).trans (decide_eq_false hNe)

/-- **Module-SIS with no equations is not hard**: over `ℤ₂[X]/(X + 1)` with a `0 × 1` matrix
    the vector `[[1]]` is a short nonzero kernel vector on every coin. -/
theorem moduleSisHard_noRows_refuted (𝒜 : (List (List (List Nat)) → List (List Nat)) → Prop)
    (h𝒜 : 𝒜 (fun _ => [[1]])) {ε : RatBound} (hε : ε.num < ε.den) :
    ¬ ModuleSisHard 𝒜 1 2 0 1 1 ε := by
  intro h
  have hU : UniformOn (SisMatrixOk 1 2 0 1) (fun _ : Fin 1 => []) :=
    uniformOn_unique _ [] ⟨rfl, fun _ hr => nomatch hr⟩
      (fun _ hy => List.eq_nil_of_length_eq_zero hy.1)
  refine FinGame.not_bound_of_forall_win _ (fun _ => ?_) hε
    (h 1 1 1 Nat.one_pos (CoinSplit.challengerOnly 1) _ hU (fun _ _ => [[1]]) (fun _ => h𝒜))
  show moduleSisWin 1 2 1 1 [] [[1]] = true
  decide

#tooth_pair smDtTcrHard_one vs smDtTcrHard_constHash_refuted
#tooth_pair regularNoise_example vs regularNoise_not_implied_by_weight
#tooth_pair SmDtTcrHard.mono vs smDtTcrHard_constHash_refuted_seedless
#tooth_pair SmDtPreHard.mono vs smDtPreHard_constHash_refuted
#tooth_pair ItsrHard.mono vs itsrHard_emptySelector_refuted
#tooth_pair hashSig_forger_bound vs smDtTcrHard_constHash_refuted
#tooth_pair uniformOn_unique vs constant_sampler_not_uniform

/-! ### 2h. `SM-DT-PRE` hardness is false for the unrestricted adversary class

The experiment gives the adversary the digest of the hidden input and, after `reveal`, the seed.
An adversary that is an arbitrary function then finds a preimage by searching the finitely many
`inputLen`-byte strings: the hidden input is one of them. So `SmDtPreHard 𝒜 th …` fails for
every tweakable hash `th` as soon as `𝒜` contains that search program. -/

/-- All byte strings of a given length. -/
def allByteStrings : Nat → List Bytes
  | 0 => [[]]
  | len + 1 =>
    (allByteStrings len).flatMap (fun t => (List.range 256).map (fun b => UInt8.ofNat b :: t))

theorem mem_allByteStrings : ∀ m : Bytes, m ∈ allByteStrings m.length
  | [] => List.Mem.head _
  | b :: t =>
    List.mem_flatMap.mpr ⟨t, mem_allByteStrings t,
      List.mem_map.mpr ⟨b.toNat, List.mem_range.mpr b.toNat_lt,
        congrArg (· :: t) UInt8.ofNat_toNat⟩⟩

/-- The first element of a list satisfying `p`, and `[]` if there is none. -/
def firstByteString (p : Bytes → Bool) : List Bytes → Bytes
  | [] => []
  | x :: xs => cond (p x) x (firstByteString p xs)

theorem firstByteString_spec (p : Bytes → Bool) :
    ∀ (l : List Bytes) (x : Bytes), x ∈ l → p x = true → p (firstByteString p l) = true
  | [], _, hx, _ => nomatch hx
  | y :: ys, x, hx, hp => by
    show p (cond (p y) y (firstByteString p ys)) = true
    cases hy : p y with
    | true => exact hy
    | false =>
      rcases List.mem_cons.mp hx with hEq | hTail
      · rw [hEq, hy] at hp
        cases hp
      · exact firstByteString_spec p ys x hTail hp

/-- Second phase of preimage search: given the target digest `y`, take the seed from `reveal`
    and return the first `inputLen`-byte string whose digest equals `y`. -/
def preimageSearchCont (th : Bytes → Bytes → Bytes → Bytes) (inputLen : Nat) (y : Option Bytes) :
    Code targetIface TargetBreak :=
  .call .reveal (fun (s : Option Bytes) =>
    .ret ⟨[], [], firstByteString (fun m => decide (some (th (s.getD []) [] m) = y))
      (allByteStrings inputLen)⟩)

/-- **Preimage search**: commit one target under the empty tweak, take the seed from `reveal`,
    and return the first `inputLen`-byte string whose digest equals the target digest. -/
def preimageSearchAdv (th : Bytes → Bytes → Bytes → Bytes) (inputLen : Nat) :
    Code targetIface TargetBreak :=
  .call (.target [] []) (preimageSearchCont th inputLen)

private theorem preimageSearch_play (th : Bytes → Bytes → Bytes → Bytes) (inputLen q : Nat)
    (hq : 0 < q) (hidden : Nat → Bytes) (s : Bytes) :
    Code.play (smDtPreOracle th q hidden) (preimageSearchAdv th inputLen) ⟨s, [], false⟩ =
      (⟨[], [], firstByteString
          (fun m => decide (some (th s [] m) = some (th s [] (hidden 0))))
          (allByteStrings inputLen)⟩,
        ⟨s, [([], hidden 0)], true⟩) := by
  have hc : (false = false ∧ ([] : List (Bytes × Bytes)).length < q ∧
      ([] : Bytes) ∉ ([] : List (Bytes × Bytes)).map Prod.fst) :=
    ⟨rfl, hq, fun h => nomatch h⟩
  have hEq : smDtPreOracle th q hidden ⟨s, [], false⟩ (.target [] []) =
      (some (th s [] (hidden 0)), ⟨s, [([], hidden 0)], false⟩) := iteOfPos hc _ _
  show Code.play (smDtPreOracle th q hidden)
    (preimageSearchCont th inputLen
      (smDtPreOracle th q hidden ⟨s, [], false⟩ (.target [] [])).1)
    (smDtPreOracle th q hidden ⟨s, [], false⟩ (.target [] [])).2 = _
  rw [hEq]
  rfl

private theorem getD_zero_mem : ∀ (l : List Bytes), 0 < l.length → l.getD 0 [] ∈ l
  | [], h => absurd h (Nat.lt_irrefl 0)
  | _ :: xs, _ => List.Mem.head xs

/-- **No tweakable hash is `SM-DT-PRE` hard against a class containing preimage search.** For
    every `th`, every size for which a uniform challenger sampler is given, every budget
    `q ≥ 1` and every `ε < 1`: the search adversary wins on every coin. -/
theorem smDtPreHard_preimageSearch_refuted {nC : Nat} (hPos : 0 < nC)
    (th : Bytes → Bytes → Bytes → Bytes) (seedLen inputLen q : Nat)
    (sample : Fin nC → Bytes × List Bytes)
    (hU : UniformOn (SmDtPreSampleOk seedLen inputLen q) sample)
    (𝒜 : Code targetIface TargetBreak → Prop) (h𝒜 : 𝒜 (preimageSearchAdv th inputLen))
    (hq : 0 < q) {ε : RatBound} (hε : ε.num < ε.den) :
    ¬ SmDtPreHard 𝒜 th seedLen inputLen q ε := by
  intro h
  refine FinGame.not_bound_of_forall_win _ (fun ω => ?_) hε
    (h nC nC 1 hPos (CoinSplit.challengerOnly nC) sample hU
      (fun _ => preimageSearchAdv th inputLen) (fun _ => h𝒜))
  have hOk := hU.mem ω
  have hLen : ((sample ω).2.getD 0 []).length = inputLen :=
    hOk.2.2 _ (getD_zero_mem _ (hOk.2.1 ▸ hq))
  have hFound := firstByteString_spec
    (fun m => decide (some (th (sample ω).1 [] m) =
      some (th (sample ω).1 [] ((sample ω).2.getD 0 []))))
    (allByteStrings inputLen) ((sample ω).2.getD 0 [])
    (hLen ▸ mem_allByteStrings ((sample ω).2.getD 0 [])) (decide_eq_true rfl)
  have hCol := Option.some.inj (of_decide_eq_true hFound)
  show smDtPreWin th
    (Code.play (smDtPreOracle th q (fun i => (sample ω).2.getD i []))
      (preimageSearchAdv th inputLen) ⟨(sample ω).1, [], false⟩).2
    (Code.play (smDtPreOracle th q (fun i => (sample ω).2.getD i []))
      (preimageSearchAdv th inputLen) ⟨(sample ω).1, [], false⟩).1 = true
  rw [preimageSearch_play th inputLen q hq]
  show ((decide (([] : Bytes) = []) && decide (th (sample ω).1 [] _ =
    th (sample ω).1 [] ((sample ω).2.getD 0 []))) || false) = true
  rw [decide_eq_true hCol]
  rfl

/-- **`SM-DT-PRE` hardness against all adversaries is false for every primitive.** -/
theorem smDtPreHard_unrestricted_refuted {nC : Nat} (hPos : 0 < nC)
    (th : Bytes → Bytes → Bytes → Bytes) (seedLen inputLen q : Nat)
    (sample : Fin nC → Bytes × List Bytes)
    (hU : UniformOn (SmDtPreSampleOk seedLen inputLen q) sample)
    (hq : 0 < q) {ε : RatBound} (hε : ε.num < ε.den) :
    ¬ SmDtPreHard (fun _ => True) th seedLen inputLen q ε :=
  smDtPreHard_preimageSearch_refuted hPos th seedLen inputLen q sample hU _ trivial hq hε

/-- Unconditional instance: with empty seeds, empty inputs and one target, no tweakable hash is
    `SM-DT-PRE` hard against all adversaries for any `ε < 1`. -/
theorem smDtPreHard_unrestricted_refuted_trivialSizes (th : Bytes → Bytes → Bytes → Bytes)
    {ε : RatBound} (hε : ε.num < ε.den) : ¬ SmDtPreHard (fun _ => True) th 0 0 1 ε :=
  smDtPreHard_unrestricted_refuted Nat.one_pos th 0 0 1 (fun _ => ([], [[]]))
    (uniformOn_unique _ ([], [[]])
      ⟨rfl, rfl, fun h hh => by
        rcases List.mem_cons.mp hh with hEq | hNil
        · rw [hEq]
          rfl
        · exact nomatch hNil⟩
      (fun y hy => by
        obtain ⟨y1, y2⟩ := y
        obtain ⟨h1, h2, h3⟩ := hy
        have hy1 : y1 = [] := List.eq_nil_of_length_eq_zero h1
        match y2, h2, h3 with
        | [z], _, h3 =>
          have hz : z = [] := List.eq_nil_of_length_eq_zero (h3 z (List.Mem.head _))
          rw [hy1, hz]))
    Nat.one_pos hε

#tooth_pair SmDtPreHard.anti vs smDtPreHard_unrestricted_refuted
#tooth_pair smDtPreHard_emptyClass vs smDtPreHard_unrestricted_refuted_trivialSizes
#tooth_pair SmDtTcrHard.anti vs smDtPreHard_preimageSearch_refuted

/-! ### 2i. Query-Bounded (`Within`) Coin-Sampled ROM Hardness and Inhabited `…Hard` Classes

Sections 2g–2h establish the two trivial extremes: the empty class `fun _ => False` satisfies every
bound vacuously, while the unrestricted class `fun _ => True` fails because pure continuations can
exhaustively search all inputs offline. This section bridges the gap constructively in two ways:

1. **Lazy coin-sampled Random Oracle (`lazyRomRun`, `romSmDtTcrGame`, `romSmDtPreGame`,
   `romItsrGame`)**: over a finite coin space of uniform digest draws (`roCoinPow cardD K`), every
   adaptive oracle adversary satisfying `Within qH` achieves:
   - `SM-DT-TCR` win probability at most `(qH + 1) / cardD` (`romSmDtTcr_within_bound`, with zero
     factor in the number of committed targets thanks to pairwise-distinct tweaks),
   - `SM-DT-PRE` win probability at most `(qH + 1) / cardX + (qH + 1) / cardD`
     (`romSmDtPre_within_bound`), and
   - `ITSR` win probability at most `(qH + 1) * maxCovered / cardSub` (`romItsr_within_bound`),
     specializing to `(qH + 1) * (qS * k)^k / M^k` on `k`-index subset selection
     (`romItsrTuple_within_bound`).
   Dropping `Within qH` refutes each bound on the same game (`tooth_romSmDtTcr_without_within`,
   `tooth_romSmDtPre_without_within`, `tooth_romItsr_without_within`).

2. **Non-empty query-bounded adversary classes inhabiting `SmDtTcrHard`, `SmDtPreHard`, and
   `ItsrHard`** (`WithinTcrQueries`, `WithinPreQueries`, `WithinItsrQueries`): each class requires
   `Within qOracle` on the challenger interface together with a `qEval`-bounded offline candidate
   budget, contains explicit oracle-querying programs with strictly positive win probability, and
   satisfies `SmDtTcrHard`, `SmDtPreHard`, and `ItsrHard` with strict `< 1` bounds `(qEval + 1) / 256`
   whenever `qEval + 1 < 256` (`poly257Hash_smDtTcrHard_within`, `byteXorHash_smDtPreHard_within`,
   `byteIdxHmsg_itsrHard_within`), while failing at `qEval ≥ 256` (`poly257Hash_smDtTcrHard_refuted`,
   `byteIdxHmsg_itsrHard_refuted`). -/

theorem sampleSum_ext {m : Nat} {f g : Fin m → Nat} (h : ∀ i, f i = g i) :
    sampleSum m f = sampleSum m g :=
  congrArg (sampleSum m) (funext h)

theorem sampleSum_le :
    ∀ (m : Nat) (f g : Fin m → Nat), (∀ i, f i ≤ g i) → sampleSum m f ≤ sampleSum m g
  | 0, _, _, _ => Nat.le_refl 0
  | m + 1, _f, _g, h =>
    Nat.add_le_add (h ⟨0, Nat.zero_lt_succ m⟩)
      (sampleSum_le m _ _ (fun i => h ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩))

theorem sampleSum_add_fn :
    ∀ (m : Nat) (f g : Fin m → Nat),
      sampleSum m (fun i => f i + g i) = sampleSum m f + sampleSum m g
  | 0, _, _ => rfl
  | m + 1, f, g => by
    rw [sampleSum_succ, sampleSum_succ, sampleSum_succ, sampleSum_add_fn m]
    omega

theorem sampleSum_mul_right :
    ∀ (m : Nat) (f : Fin m → Nat) (c : Nat),
      sampleSum m (fun i => f i * c) = sampleSum m f * c
  | 0, _, _ => (Nat.zero_mul _).symm
  | m + 1, f, c => by
    rw [sampleSum_succ, sampleSum_succ, sampleSum_mul_right m, Nat.add_mul]

theorem sampleSum_const :
    ∀ (m c : Nat), sampleSum m (fun _ => c) = m * c
  | 0, c => (Nat.zero_mul c).symm
  | m + 1, c => by
    rw [sampleSum_succ, sampleSum_const m, Nat.succ_mul, Nat.add_comm]

private theorem sampleSum_le_card_of_le_one :
    ∀ (m : Nat) (f : Fin m → Nat), (∀ i, f i ≤ 1) → sampleSum m f ≤ m
  | m, f, h => by
    have h1 := sampleSum_le m f (fun _ => 1) h
    rw [sampleSum_const m 1, Nat.mul_one] at h1
    exact h1

private theorem sampleSum_indicator_le_one :
    ∀ (m : Nat) (x : Fin m), sampleSum m (fun i => if i = x then 1 else 0) ≤ 1
  | 0, x => nomatch x
  | m + 1, ⟨0, _⟩ => by
    rw [sampleSum_succ]
    simp only [↓reduceIte]
    have hTail : sampleSum m (fun i : Fin m =>
        if (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (m + 1)) = ⟨0, Nat.zero_lt_succ m⟩ then 1 else 0) = 0 := by
      have hZero : (fun i : Fin m =>
          if (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (m + 1)) = ⟨0, Nat.zero_lt_succ m⟩ then 1 else 0) =
          (fun _ => 0) := by
        funext i
        exact iteOfNeg (fun h => Nat.succ_ne_zero i.1 (congrArg Fin.val h)) 1 0
      rw [hZero, sampleSum_const m 0, Nat.mul_zero]
    rw [hTail]
    exact Nat.le_refl 1
  | m + 1, ⟨k + 1, hk⟩ => by
    rw [sampleSum_succ]
    have hHead : (if (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)) = ⟨k + 1, hk⟩ then 1 else 0) = 0 :=
      iteOfNeg (fun h => Nat.succ_ne_zero k (congrArg Fin.val h).symm) 1 0
    have hTail : (fun i : Fin m =>
        if (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (m + 1)) = ⟨k + 1, hk⟩ then 1 else 0) =
        (fun i : Fin m => if i = ⟨k, Nat.lt_of_succ_lt_succ hk⟩ then 1 else 0) := by
      funext i
      by_cases hi : i = ⟨k, Nat.lt_of_succ_lt_succ hk⟩
      · subst hi; simp only [↓reduceIte]
      · exact iteOfNeg (fun h => hi (Fin.ext (Nat.succ.inj (congrArg Fin.val h)))) 1 0 |>.trans
          (iteOfNeg hi 1 0).symm
    rw [hHead, Nat.zero_add, hTail]
    exact sampleSum_indicator_le_one m ⟨k, Nat.lt_of_succ_lt_succ hk⟩

private theorem sampleSum_bool_le_one_of_subsingleton {m : Nat} (p : Fin m → Bool)
    (hSub : ∀ i j : Fin m, p i = true → p j = true → i = j) :
    sampleSum m (fun i => if p i then 1 else 0) ≤ 1 := by
  suffices ∀ (k : Nat) (q : Fin k → Bool),
      (∀ i j : Fin k, q i = true → q j = true → i = j) →
      sampleSum k (fun i => if q i then 1 else 0) ≤ 1 from this m p hSub
  intro k
  induction k with
  | zero => intro _ _; exact Nat.zero_le 1
  | succ k ih =>
    intro q hq
    rw [sampleSum_succ]
    cases h0 : q ⟨0, Nat.zero_lt_succ k⟩
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      exact ih (fun i => q ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) (fun i j hi hj =>
        Fin.ext (Nat.succ.inj (congrArg Fin.val (hq _ _ hi hj))))
    · simp only [↓reduceIte]
      have hRest : sampleSum k (fun i => if q ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ then 1 else 0) = 0 := by
        have hZ : (fun i : Fin k => if q ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ then 1 else 0) =
            (fun _ => 0) := by
          funext i
          cases hi : q ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩
          · rfl
          · exact False.elim (Nat.succ_ne_zero i.1 (congrArg Fin.val (hq _ _ hi h0)))
        rw [hZ, sampleSum_const, Nat.mul_zero]
      rw [hRest]
      exact Nat.le_refl 1

private theorem sampleSum_cast {m m' : Nat} (h : m = m') (f : Fin m' → Nat) :
    sampleSum m (fun i => f ⟨i.1, h ▸ i.2⟩) = sampleSum m' f := by
  subst h; rfl

private theorem sampleSum_split_add :
    ∀ (a b : Nat) (f : Fin (a + b) → Nat),
      sampleSum (a + b) f =
        sampleSum a (fun i => f ⟨i.1, Nat.lt_of_lt_of_le i.2 (Nat.le_add_right a b)⟩) +
        sampleSum b (fun j => f ⟨a + j.1, Nat.add_lt_add_left j.2 a⟩)
  | 0, b, f => by
    simp only [sampleSum_zero, Nat.zero_add]
    exact sampleSum_cast (Nat.zero_add b) (fun j => f ⟨j.1, by omega⟩)
  | a + 1, b, f => by
    have hCast : sampleSum ((a + 1) + b) f =
        sampleSum ((a + b) + 1) (fun i => f ⟨i.1, (Nat.succ_add a b).symm ▸ i.2⟩) := by
      have h := sampleSum_cast (Nat.succ_add a b)
        (fun i : Fin ((a + b) + 1) => f ⟨i.1, (Nat.succ_add a b).symm ▸ i.2⟩)
      exact (sampleSum_ext (fun i => rfl)).trans h
    rw [hCast, sampleSum_succ, sampleSum_split_add a b, sampleSum_succ]
    have hMid : sampleSum a (fun i : Fin a =>
        f ⟨i.1 + 1, (Nat.succ_add a b).symm ▸ Nat.succ_lt_succ
          (Nat.lt_of_lt_of_le i.2 (Nat.le_add_right a b))⟩) =
        sampleSum a (fun i : Fin a =>
          f ⟨i.1 + 1, Nat.lt_of_lt_of_le (Nat.succ_lt_succ i.2) (Nat.le_add_right (a + 1) b)⟩) :=
      sampleSum_ext (fun _ => rfl)
    have hRight : sampleSum b (fun j : Fin b =>
        f ⟨(a + j.1) + 1, (Nat.succ_add a b).symm ▸ Nat.succ_lt_succ (Nat.add_lt_add_left j.2 a)⟩) =
        sampleSum b (fun j : Fin b => f ⟨(a + 1) + j.1, Nat.add_lt_add_left j.2 (a + 1)⟩) :=
      sampleSum_ext (fun j => congrArg f (Fin.ext (by dsimp only; omega)))
    rw [hMid, hRight]
    exact (Nat.add_assoc _ _ _).symm

private theorem sampleSum_prod :
    ∀ (m n : Nat) (f : Fin (m * n) → Nat),
      sampleSum (m * n) f =
        sampleSum m (fun i => sampleSum n (fun j => f ⟨i.1 * n + j.1, prodCoin_pair_lt i j⟩))
  | 0, n, f => by
    rw [sampleSum_zero]
    have h := sampleSum_cast (Nat.zero_mul n)
      (fun i : Fin 0 => f ⟨i.1, (Nat.zero_mul n).symm ▸ i.2⟩)
    exact h
  | m + 1, n, f => by
    have hEq : (m + 1) * n = n + m * n := (Nat.succ_mul m n).trans (Nat.add_comm (m * n) n)
    have hCast : sampleSum ((m + 1) * n) f =
        sampleSum (n + m * n) (fun k => f ⟨k.1, hEq.symm ▸ k.2⟩) :=
      sampleSum_cast hEq (fun k : Fin (n + m * n) => f ⟨k.1, hEq.symm ▸ k.2⟩)
    rw [hCast, sampleSum_split_add n (m * n), sampleSum_prod m n, sampleSum_succ]
    have hHead : sampleSum n (fun i : Fin n =>
        f ⟨i.1, hEq.symm ▸ Nat.lt_of_lt_of_le i.2 (Nat.le_add_right n (m * n))⟩) =
        sampleSum n (fun j : Fin n =>
          f ⟨(⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)).1 * n + j.1,
            prodCoin_pair_lt ⟨0, Nat.zero_lt_succ m⟩ j⟩) :=
      sampleSum_ext (fun j => congrArg f (Fin.ext (by simp)))
    have hTail : sampleSum m (fun i : Fin m => sampleSum n (fun j : Fin n =>
        f ⟨n + (i.1 * n + j.1), hEq.symm ▸ Nat.add_lt_add_left (prodCoin_pair_lt i j) n⟩)) =
        sampleSum m (fun i : Fin m => sampleSum n (fun j : Fin n =>
          f ⟨(i.1 + 1) * n + j.1, prodCoin_pair_lt ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ j⟩)) :=
      sampleSum_ext (fun i => sampleSum_ext (fun j => congrArg f (Fin.ext (by
        dsimp only
        rw [Nat.add_mul, Nat.one_mul]
        omega))))
    rw [hHead, hTail]

private theorem sampleSum_point_update :
    ∀ (m : Nat) (p : Fin m) (v : Nat) (u : Fin m → Nat),
      u p + sampleSum m (fun i => if i = p then v else u i) = v + sampleSum m u
  | 0, p, _, _ => nomatch p
  | m + 1, ⟨0, _⟩, v, u => by
    rw [sampleSum_succ, sampleSum_succ]
    simp only [↓reduceIte]
    have hRest : sampleSum m (fun i : Fin m =>
        if (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (m + 1)) = ⟨0, Nat.zero_lt_succ m⟩ then v
        else u ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) =
        sampleSum m (fun i : Fin m => u ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) :=
      sampleSum_ext (fun i =>
        iteOfNeg (fun h => Nat.succ_ne_zero i.1 (congrArg Fin.val h)) v _)
    rw [hRest]
    omega
  | m + 1, ⟨p + 1, hp⟩, v, u => by
    rw [sampleSum_succ, sampleSum_succ]
    have hHead : (if (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)) = ⟨p + 1, hp⟩ then v
        else u ⟨0, Nat.zero_lt_succ m⟩) = u ⟨0, Nat.zero_lt_succ m⟩ :=
      iteOfNeg (fun h => Nat.succ_ne_zero p (congrArg Fin.val h).symm) v _
    have hRest : sampleSum m (fun i : Fin m =>
        if (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (m + 1)) = ⟨p + 1, hp⟩ then v
        else u ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) =
        sampleSum m (fun i : Fin m =>
          if i = ⟨p, Nat.lt_of_succ_lt_succ hp⟩ then v else u ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) := by
      refine sampleSum_ext (fun i => ?_)
      by_cases hi : i = ⟨p, Nat.lt_of_succ_lt_succ hp⟩
      · subst hi; simp only [↓reduceIte]
      · exact (iteOfNeg (fun h => hi (Fin.ext (Nat.succ.inj (congrArg Fin.val h)))) v _).trans
          (iteOfNeg hi v _).symm
    rw [hHead, hRest]
    have ih := sampleSum_point_update m ⟨p, Nat.lt_of_succ_lt_succ hp⟩ v
      (fun i => u ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
    dsimp only at ih
    omega

private def finSwapZero {k : Nat} (j₀ j : Fin (k + 1)) : Fin (k + 1) :=
  if j = ⟨0, Nat.zero_lt_succ k⟩ then j₀
  else if j = j₀ then ⟨0, Nat.zero_lt_succ k⟩
  else j

private theorem finSwapZero_involutive {k : Nat} (j₀ j : Fin (k + 1)) :
    finSwapZero j₀ (finSwapZero j₀ j) = j := by
  unfold finSwapZero
  by_cases hj0 : j = ⟨0, Nat.zero_lt_succ k⟩
  · subst hj0
    by_cases h0 : j₀ = ⟨0, Nat.zero_lt_succ k⟩
    · subst h0; rfl
    · rw [iteOfPos rfl, iteOfNeg h0, iteOfPos rfl]
  · rw [iteOfNeg hj0]
    by_cases hjj : j = j₀
    · subst hjj; rw [iteOfPos rfl, iteOfPos rfl]
    · rw [iteOfNeg hjj, iteOfNeg hj0, iteOfNeg hjj]

private theorem sampleSum_swapZero {k : Nat} (j₀ : Fin (k + 1)) (w : Fin (k + 1) → Nat) :
    sampleSum (k + 1) (fun j => w (finSwapZero j₀ j)) = sampleSum (k + 1) w := by
  cases j₀ with
  | mk v hv =>
    cases v with
    | zero =>
      refine sampleSum_ext (fun j => congrArg w ?_)
      unfold finSwapZero
      by_cases hj : j = ⟨0, Nat.zero_lt_succ k⟩
      · subst hj; rfl
      · rw [iteOfNeg hj, iteOfNeg hj]
    | succ j₁ =>
      cases k with
      | zero => omega
      | succ k' =>
        conv => lhs; rw [sampleSum_succ]
        conv => rhs; rw [sampleSum_succ]
        have hHead : w (finSwapZero ⟨j₁ + 1, hv⟩ ⟨0, Nat.zero_lt_succ (k' + 1)⟩) =
            w ⟨j₁ + 1, hv⟩ := rfl
        have hTail : sampleSum (k' + 1) (fun i : Fin (k' + 1) =>
            w (finSwapZero ⟨j₁ + 1, hv⟩ ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)) =
            sampleSum (k' + 1) (fun i : Fin (k' + 1) =>
              if i = ⟨j₁, Nat.lt_of_succ_lt_succ hv⟩ then w ⟨0, Nat.zero_lt_succ (k' + 1)⟩
              else w ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) := by
          refine sampleSum_ext (fun i => ?_)
          unfold finSwapZero
          rw [iteOfNeg (fun h => Nat.succ_ne_zero i.1 (congrArg Fin.val h))]
          by_cases hi : i = ⟨j₁, Nat.lt_of_succ_lt_succ hv⟩
          · subst hi; rw [iteOfPos rfl, iteOfPos rfl]
          · rw [iteOfNeg (fun h => hi (Fin.ext (Nat.succ.inj (congrArg Fin.val h)))),
              iteOfNeg hi]
        rw [hHead, hTail]
        exact sampleSum_point_update (k' + 1) ⟨j₁, Nat.lt_of_succ_lt_succ hv⟩
          (w ⟨0, Nat.zero_lt_succ (k' + 1)⟩) (fun i => w ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)

private theorem bij_sampleSum :
    ∀ (m n : Nat) (f : Fin m → Fin n) (g : Fin n → Fin m),
      (∀ i, g (f i) = i) → (∀ j, f (g j) = j) →
      ∀ (w : Fin n → Nat), sampleSum m (fun i => w (f i)) = sampleSum n w
  | 0, 0, _, _, _, _, _ => rfl
  | 0, k + 1, _, g, _, _, _ => nomatch (g ⟨0, Nat.zero_lt_succ k⟩)
  | m + 1, 0, f, _, _, _, _ => nomatch (f ⟨0, Nat.zero_lt_succ m⟩)
  | m + 1, k + 1, f, g, hgf, hfg, w => by
    let j₀ := f ⟨0, Nat.zero_lt_succ m⟩
    let f₁ : Fin (m + 1) → Fin (k + 1) := fun i => finSwapZero j₀ (f i)
    let g₁ : Fin (k + 1) → Fin (m + 1) := fun j => g (finSwapZero j₀ j)
    have hgf₁ : ∀ i, g₁ (f₁ i) = i := fun i => by
      dsimp only [f₁, g₁]; rw [finSwapZero_involutive, hgf]
    have hfg₁ : ∀ j, f₁ (g₁ j) = j := fun j => by
      dsimp only [f₁, g₁]; rw [hfg, finSwapZero_involutive]
    have hf₁_pos : ∀ i : Fin m, 0 < (f₁ ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩).1 := by
      intro i
      refine Nat.pos_of_ne_zero (fun hZ => ?_)
      have hEq0 : f₁ ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ = ⟨0, Nat.zero_lt_succ k⟩ := Fin.ext hZ
      have hG := congrArg g₁ hEq0
      rw [hgf₁] at hG
      have hG0 : g₁ ⟨0, Nat.zero_lt_succ k⟩ = ⟨0, Nat.zero_lt_succ m⟩ := by
        dsimp only [g₁, finSwapZero]; rw [iteOfPos rfl]; exact hgf ⟨0, Nat.zero_lt_succ m⟩
      rw [hG0] at hG
      exact Nat.succ_ne_zero i.1 (congrArg Fin.val hG)
    have hg₁_pos : ∀ j : Fin k, 0 < (g₁ ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩).1 := by
      intro j
      refine Nat.pos_of_ne_zero (fun hZ => ?_)
      have hEq0 : g₁ ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩ = ⟨0, Nat.zero_lt_succ m⟩ := Fin.ext hZ
      have hF := congrArg f₁ hEq0
      rw [hfg₁] at hF
      have hF0 : f₁ ⟨0, Nat.zero_lt_succ m⟩ = ⟨0, Nat.zero_lt_succ k⟩ := by
        dsimp only [f₁, finSwapZero, j₀]
        by_cases h : f ⟨0, Nat.zero_lt_succ m⟩ = ⟨0, Nat.zero_lt_succ k⟩
        · rw [iteOfPos h]; exact h
        · rw [iteOfNeg h, iteOfPos rfl]
      rw [hF0] at hF
      exact Nat.succ_ne_zero j.1 (congrArg Fin.val hF)
    let f' : Fin m → Fin k := fun i =>
      ⟨(f₁ ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩).1 - 1,
        by have h1 := (f₁ ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩).2; have h2 := hf₁_pos i; omega⟩
    let g' : Fin k → Fin m := fun j =>
      ⟨(g₁ ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩).1 - 1,
        by have h1 := (g₁ ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩).2; have h2 := hg₁_pos j; omega⟩
    have hgf' : ∀ i, g' (f' i) = i := fun i => by
      apply Fin.ext
      dsimp only [f', g']
      have h1 : (⟨(f₁ ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩).1 - 1 + 1,
          Nat.succ_lt_succ (f' i).2⟩ : Fin (k + 1)) = f₁ ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ :=
        Fin.ext (by dsimp only; have := hf₁_pos i; omega)
      rw [h1, hgf₁]
      rfl
    have hfg' : ∀ j, f' (g' j) = j := fun j => by
      apply Fin.ext
      dsimp only [f', g']
      have h1 : (⟨(g₁ ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩).1 - 1 + 1,
          Nat.succ_lt_succ (g' j).2⟩ : Fin (m + 1)) = g₁ ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩ :=
        Fin.ext (by dsimp only; have := hg₁_pos j; omega)
      rw [h1, hfg₁]
      rfl
    have hStep : sampleSum (m + 1) (fun i => w (f i)) =
        sampleSum (m + 1) (fun i => w (finSwapZero j₀ (f₁ i))) :=
      sampleSum_ext (fun i => congrArg w (finSwapZero_involutive j₀ (f i)).symm)
    rw [hStep, sampleSum_succ]
    have hHead : w (finSwapZero j₀ (f₁ ⟨0, Nat.zero_lt_succ m⟩)) = w j₀ := by
      have hF0 : f₁ ⟨0, Nat.zero_lt_succ m⟩ = ⟨0, Nat.zero_lt_succ k⟩ := by
        dsimp only [f₁, finSwapZero, j₀]
        by_cases h : f ⟨0, Nat.zero_lt_succ m⟩ = ⟨0, Nat.zero_lt_succ k⟩
        · rw [iteOfPos h]; exact h
        · rw [iteOfNeg h, iteOfPos rfl]
      rw [hF0]; rfl
    have hTail : sampleSum m (fun i : Fin m =>
        w (finSwapZero j₀ (f₁ ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩))) =
        sampleSum m (fun i : Fin m =>
          w (finSwapZero j₀ ⟨(f' i).1 + 1, Nat.succ_lt_succ (f' i).2⟩)) :=
      sampleSum_ext (fun i => congrArg (fun x => w (finSwapZero j₀ x))
        (Fin.ext (by dsimp only [f']; have := hf₁_pos i; omega)))
    rw [hHead, hTail,
      bij_sampleSum m k f' g' hgf' hfg' (fun j => w (finSwapZero j₀ ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)),
      ← sampleSum_swapZero j₀ w, sampleSum_succ]
    rfl

private theorem bij_card_eq {m n : Nat} (f : Fin m → Fin n) (g : Fin n → Fin m)
    (hgf : ∀ i, g (f i) = i) (hfg : ∀ j, f (g j) = j) : m = n := by
  have h := bij_sampleSum m n f g hgf hfg (fun _ => 1)
  rw [sampleSum_const m 1, sampleSum_const n 1, Nat.mul_one, Nat.mul_one] at h
  exact h

theorem CoinSplit.card_eq {n nC nA : Nat} (π : CoinSplit n nC nA) : n = nC * nA := by
  let p := CoinSplit.prod nC nA
  exact bij_card_eq
    (fun ω => p.pair (π.chal ω) (π.advc ω))
    (fun z => π.pair (p.chal z) (p.advc z))
    (fun ω => by rw [p.chal_pair, p.advc_pair, π.pair_eta])
    (fun z => by rw [π.chal_pair, π.advc_pair, p.pair_eta])

theorem CoinSplit.sampleSum_eq {n nC nA : Nat} (π : CoinSplit n nC nA) (w : Fin n → Nat) :
    sampleSum n w = sampleSum nC (fun c => sampleSum nA (fun a => w (π.pair c a))) := by
  let p := CoinSplit.prod nC nA
  have hBij := bij_sampleSum n (nC * nA)
    (fun ω => p.pair (π.chal ω) (π.advc ω))
    (fun z => π.pair (p.chal z) (p.advc z))
    (fun ω => by rw [p.chal_pair, p.advc_pair, π.pair_eta])
    (fun z => by rw [π.chal_pair, π.advc_pair, p.pair_eta])
    (fun z => w (π.pair (p.chal z) (p.advc z)))
  have hLhs : sampleSum n (fun ω => w (π.pair (p.chal (p.pair (π.chal ω) (π.advc ω)))
      (p.advc (p.pair (π.chal ω) (π.advc ω))))) = sampleSum n w :=
    sampleSum_ext (fun ω => by rw [p.chal_pair, p.advc_pair, π.pair_eta])
  rw [← hLhs, hBij, sampleSum_prod nC nA]
  exact sampleSum_ext (fun c => sampleSum_ext (fun a => by
    have hPair : (⟨c.1 * nA + a.1, prodCoin_pair_lt c a⟩ : Fin (nC * nA)) = p.pair c a := rfl
    rw [hPair, p.chal_pair, p.advc_pair]))

private def finFind {α : Type} [DecidableEq α] :
    (k : Nat) → (Fin k → α) → α → Option (Fin k)
  | 0, _, _ => none
  | k + 1, s, x =>
    if s ⟨0, Nat.zero_lt_succ k⟩ = x then some ⟨0, Nat.zero_lt_succ k⟩
    else (finFind k (fun j => s ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩) x).map
      (fun j => ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)

private theorem finFind_complete {α : Type} [DecidableEq α] :
    ∀ (k : Nat) (s : Fin k → α) (x : α),
      (∃ j : Fin k, s j = x) → ∃ j : Fin k, finFind k s x = some j ∧ s j = x
  | 0, _, _, ⟨j, _⟩ => nomatch j
  | k + 1, s, x, ⟨j, hj⟩ => by
    unfold finFind
    by_cases h0 : s ⟨0, Nat.zero_lt_succ k⟩ = x
    · exact ⟨⟨0, Nat.zero_lt_succ k⟩, iteOfPos h0 _ _, h0⟩
    · rw [iteOfNeg h0]
      cases j with
      | mk v hv =>
        cases v with
        | zero => exact False.elim (h0 hj)
        | succ v' =>
          obtain ⟨j', hj'1, hj'2⟩ := finFind_complete k
            (fun i => s ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩) x
            ⟨⟨v', Nat.lt_of_succ_lt_succ hv⟩, hj⟩
          exact ⟨⟨j'.1 + 1, Nat.succ_lt_succ j'.2⟩, by rw [hj'1]; rfl, hj'2⟩

theorem UniformOn.card_and_sampleSum_eq {m k : Nat} {α : Type} [DecidableEq α]
    {support : α → Prop} {s₁ : Fin m → α} {s₂ : Fin k → α}
    (h₁ : UniformOn support s₁) (h₂ : UniformOn support s₂) (u : α → Nat) :
    m = k ∧ sampleSum m (fun i => u (s₁ i)) = sampleSum k (fun j => u (s₂ j)) := by
  cases m with
  | zero =>
    cases k with
    | zero => exact ⟨rfl, rfl⟩
    | succ k' =>
      obtain ⟨i, _⟩ := h₁.surjective (s₂ ⟨0, Nat.zero_lt_succ k'⟩) (h₂.mem _)
      exact nomatch i
  | succ m' =>
    cases k with
    | zero =>
      obtain ⟨j, _⟩ := h₂.surjective (s₁ ⟨0, Nat.zero_lt_succ m'⟩) (h₁.mem _)
      exact nomatch j
    | succ k' =>
      let f : Fin (m' + 1) → Fin (k' + 1) := fun i =>
        (finFind (k' + 1) s₂ (s₁ i)).getD ⟨0, Nat.zero_lt_succ k'⟩
      let g : Fin (k' + 1) → Fin (m' + 1) := fun j =>
        (finFind (m' + 1) s₁ (s₂ j)).getD ⟨0, Nat.zero_lt_succ m'⟩
      have hf : ∀ i, s₂ (f i) = s₁ i := fun i => by
        obtain ⟨j, hj1, hj2⟩ := finFind_complete (k' + 1) s₂ (s₁ i)
          (h₂.surjective (s₁ i) (h₁.mem i))
        dsimp only [f]; rw [hj1]; exact hj2
      have hg : ∀ j, s₁ (g j) = s₂ j := fun j => by
        obtain ⟨i, hi1, hi2⟩ := finFind_complete (m' + 1) s₁ (s₂ j)
          (h₁.surjective (s₂ j) (h₂.mem j))
        dsimp only [g]; rw [hi1]; exact hi2
      have hgf : ∀ i, g (f i) = i := fun i => h₁.injective _ _ ((hg (f i)).trans (hf i))
      have hfg : ∀ j, f (g j) = j := fun j => h₂.injective _ _ ((hf (g j)).trans (hg j))
      refine ⟨bij_card_eq f g hgf hfg, ?_⟩
      exact (sampleSum_ext (fun i => congrArg u (hf i).symm)).trans
        (bij_sampleSum (m' + 1) (k' + 1) f g hgf hfg (fun j => u (s₂ j)))

/-! #### 2i.1 Lazy Coin-Sampled Random Oracle (`lazyRomRun`) and `O(q / 2^n)` `GameBound`s -/

/-- Consistent lookup in a lazy random-oracle transcript table. -/
def roLookup {Dom : Type} [DecidableEq Dom] {cardD : Nat} :
    List (Dom × Fin cardD) → Dom → Option (Fin cardD)
  | [], _ => none
  | (x, y) :: rest, q => if q = x then some y else roLookup rest q

/-- Single consistent lazy-sampling step: returns the recorded digest if `q` was already queried,
    and otherwise records `(q, draw)` using the fresh coin draw `draw : Fin cardD`. -/
def lazyRomStep {Dom : Type} [DecidableEq Dom] {cardD : Nat}
    (st : List (Dom × Fin cardD)) (q : Dom) (draw : Fin cardD) :
    Fin cardD × List (Dom × Fin cardD) :=
  match roLookup st q with
  | some y => (y, st)
  | none => (draw, (q, draw) :: st)

theorem lazyRomStep_mem {Dom : Type} [DecidableEq Dom] {cardD : Nat} :
    ∀ (st : List (Dom × Fin cardD)) (q : Dom) (draw : Fin cardD),
      (q, (lazyRomStep st q draw).1) ∈ (lazyRomStep st q draw).2 := by
  intro st q draw
  unfold lazyRomStep
  cases hL : roLookup st q with
  | none => exact List.Mem.head _
  | some y =>
    suffices ∀ l : List (Dom × Fin cardD), roLookup l q = some y → (q, y) ∈ l from this st hL
    intro l hl
    induction l with
    | nil => cases hl
    | cons hd tl ih =>
      unfold roLookup at hl
      by_cases hq : q = hd.1
      · rw [iteOfPos hq] at hl
        cases hl
        cases hd
        dsimp only at hq
        subst hq
        exact List.Mem.head _
      · rw [iteOfNeg hq] at hl
        exact List.Mem.tail _ (ih hl)

theorem lazyRomStep_preserves_mem {Dom : Type} [DecidableEq Dom] {cardD : Nat}
    (st : List (Dom × Fin cardD)) (q : Dom) (draw : Fin cardD) {e : Dom × Fin cardD}
    (he : e ∈ st) : e ∈ (lazyRomStep st q draw).2 := by
  unfold lazyRomStep
  cases roLookup st q with
  | some _ => exact he
  | none => exact List.Mem.tail _ he

/-- Execute an adaptive random-oracle program `c` against a lazy random oracle over `K` coin draws. -/
def lazyRomRun {Dom R : Type} [DecidableEq Dom] {cardD : Nat} (hCard : 0 < cardD) :
    Code (roOracleIface Dom cardD) R → (K : Nat) → List (Dom × Fin cardD) →
      Fin (roCoinPow cardD K) → R × List (Dom × Fin cardD)
  | .ret v, _, st, _ => (v, st)
  | .call q next, 0, st, ω =>
    let step := lazyRomStep st q ⟨0, hCard⟩
    lazyRomRun hCard (next step.1) 0 step.2 ω
  | .call q next, K + 1, st, ω =>
    let split := CoinSplit.prod cardD (roCoinPow cardD K)
    let step := lazyRomStep st q (split.chal ω)
    lazyRomRun hCard (next step.1) K step.2 (split.advc ω)

theorem lazyRomRun_ret {Dom R : Type} [DecidableEq Dom] {cardD : Nat} (hCard : 0 < cardD)
    (v : R) (K : Nat) (st : List (Dom × Fin cardD)) (ω : Fin (roCoinPow cardD K)) :
    lazyRomRun hCard (.ret v) K st ω = (v, st) := by conv => lhs; unfold lazyRomRun

theorem lazyRomRun_call_succ {Dom R : Type} [DecidableEq Dom] {cardD : Nat} (hCard : 0 < cardD)
    (q : Dom) (next : Fin cardD → Code (roOracleIface Dom cardD) R) (K : Nat)
    (st : List (Dom × Fin cardD)) (ω : Fin (roCoinPow cardD (K + 1))) :
    lazyRomRun hCard (.call q next) (K + 1) st ω =
      lazyRomRun hCard (next (lazyRomStep st q ((CoinSplit.prod cardD (roCoinPow cardD K)).chal ω)).1)
        K (lazyRomStep st q ((CoinSplit.prod cardD (roCoinPow cardD K)).chal ω)).2
        ((CoinSplit.prod cardD (roCoinPow cardD K)).advc ω) := by conv => lhs; unfold lazyRomRun

/-- Whether any recorded `(query, digest)` entry in `st` triggers `stepBad`. -/
def tableHasBad {Dom : Type} {cardD : Nat} (stepBad : Dom → Fin cardD → Bool)
    (st : List (Dom × Fin cardD)) : Bool :=
  st.any (fun e => stepBad e.1 e.2)

/-- **Master `Within` Lazy-ROM Bad-Event Bound.** If every fresh query `x : Dom` has at most `B`
    bad draws in `Fin cardD`, then for every adaptive program `c` satisfying `Within qH c` (`qH ≤ K`)
    starting from a bad-free initial table `st`, the probability of recording a bad entry is at most
    `(qH * B) / cardD`. -/
theorem lazyRomRun_bad_bound {Dom R : Type} [DecidableEq Dom] {cardD : Nat} (hCard : 0 < cardD)
    (stepBad : Dom → Fin cardD → Bool) (B : Nat)
    (hStepBound : ∀ x : Dom, sampleSum cardD (fun d => if stepBad x d then 1 else 0) ≤ B) :
    ∀ (c : Code (roOracleIface Dom cardD) R) {qH K : Nat},
      qH ≤ K → Within qH c → ∀ (st : List (Dom × Fin cardD)),
      tableHasBad stepBad st = false →
      sampleSum (roCoinPow cardD K)
        (fun ω => if tableHasBad stepBad (lazyRomRun hCard c K st ω).2 then 1 else 0) * cardD ≤
        (qH * B) * roCoinPow cardD K
  | .ret v, _, K, _, _, st, hClean => by
    have hZero : (fun ω : Fin (roCoinPow cardD K) =>
        if tableHasBad stepBad (lazyRomRun hCard (.ret v) K st ω).2 then 1 else 0) =
        (fun _ => 0) := by
      funext ω; rw [lazyRomRun_ret, hClean]; rfl
    rw [hZero, sampleSum_const, Nat.mul_zero, Nat.zero_mul]
    exact Nat.zero_le _
  | .call q next, 0, _, _, hW, _, _ => nomatch hW
  | .call _ _, _ + 1, 0, hqK, _, _, _ => absurd hqK (Nat.not_succ_le_zero _)
  | .call q next, qH + 1, K + 1, hqK, .call _ _ hk, st, hClean => by
    have hqK' : qH ≤ K := Nat.le_of_succ_le_succ hqK
    change sampleSum (cardD * roCoinPow cardD K) _ * cardD ≤ _
    rw [sampleSum_prod cardD (roCoinPow cardD K)]
    let p := CoinSplit.prod cardD (roCoinPow cardD K)
    let inner : Fin cardD → Nat := fun d =>
      sampleSum (roCoinPow cardD K) (fun τ =>
        if tableHasBad stepBad
            (lazyRomRun hCard (next (lazyRomStep st q d).1) K (lazyRomStep st q d).2 τ).2
        then 1 else 0)
    have hInnerEq : sampleSum cardD (fun d => sampleSum (roCoinPow cardD K) (fun τ =>
        if tableHasBad stepBad
            (lazyRomRun hCard (.call q next) (K + 1) st ⟨d.1 * roCoinPow cardD K + τ.1,
              prodCoin_pair_lt d τ⟩).2
        then 1 else 0)) = sampleSum cardD inner := by
      refine sampleSum_ext (fun d => sampleSum_ext (fun τ => ?_))
      have hPair : (⟨d.1 * roCoinPow cardD K + τ.1, prodCoin_pair_lt d τ⟩ :
          Fin (cardD * roCoinPow cardD K)) = p.pair d τ := rfl
      rw [hPair, lazyRomRun_call_succ, p.chal_pair, p.advc_pair]
    rw [hInnerEq, ← sampleSum_mul_right cardD inner cardD]
    cases hLook : roLookup st q with
    | some y =>
      have hStepEq : ∀ d, lazyRomStep st q d = (y, st) := fun d => by
        unfold lazyRomStep; rw [hLook]
      have hPt : ∀ d : Fin cardD, inner d * cardD ≤ (qH * B) * roCoinPow cardD K := fun d => by
        dsimp only [inner]
        rw [hStepEq d]
        exact lazyRomRun_bad_bound hCard stepBad B hStepBound (next y) hqK' (hk y) st hClean
      have hSum := sampleSum_le cardD (fun d => inner d * cardD)
        (fun _ => (qH * B) * roCoinPow cardD K) hPt
      rw [sampleSum_const] at hSum
      refine Nat.le_trans hSum ?_
      have h1 : cardD * ((qH * B) * roCoinPow cardD K) = (qH * B) * (cardD * roCoinPow cardD K) := by
        simp only [Nat.mul_left_comm, Nat.mul_comm]
      rw [h1]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right B (Nat.le_succ qH))
    | none =>
      have hStepEq : ∀ d, lazyRomStep st q d = (d, (q, d) :: st) := fun d => by
        unfold lazyRomStep; rw [hLook]
      have hPt : ∀ d : Fin cardD,
          inner d * cardD ≤
            (if stepBad q d then 1 else 0) * (cardD * roCoinPow cardD K) +
              (qH * B) * roCoinPow cardD K := fun d => by
        dsimp only [inner]
        rw [hStepEq d]
        cases hBadD : stepBad q d
        · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_mul, Nat.zero_add]
          have hClean' : tableHasBad stepBad ((q, d) :: st) = false := by
            unfold tableHasBad
            rw [List.any_cons, hBadD, Bool.false_or]
            exact hClean
          exact lazyRomRun_bad_bound hCard stepBad B hStepBound (next d) hqK' (hk d)
            ((q, d) :: st) hClean'
        · simp only [↓reduceIte, Nat.one_mul]
          have hTriv : sampleSum (roCoinPow cardD K) (fun τ =>
              if tableHasBad stepBad (lazyRomRun hCard (next d) K ((q, d) :: st) τ).2
              then 1 else 0) ≤ roCoinPow cardD K :=
            sampleSum_le_card_of_le_one _ _ (fun τ => by
              cases tableHasBad stepBad (lazyRomRun hCard (next d) K ((q, d) :: st) τ).2 <;> decide)
          have hMul := Nat.mul_le_mul_right cardD hTriv
          rw [Nat.mul_comm (roCoinPow cardD K) cardD] at hMul
          exact Nat.le_trans hMul (Nat.le_add_right _ _)
      have hSum := sampleSum_le cardD (fun d => inner d * cardD) _ hPt
      simp only [sampleSum_add_fn, sampleSum_mul_right, sampleSum_const] at hSum
      rw [sampleSum_mul_right]
      refine Nat.le_trans hSum ?_
      have hB := Nat.mul_le_mul_right (cardD * roCoinPow cardD K) (hStepBound q)
      have hRearr : B * (cardD * roCoinPow cardD K) + cardD * (qH * B * roCoinPow cardD K) =
          (qH + 1) * B * (cardD * roCoinPow cardD K) := by
        rw [Nat.succ_mul, Nat.add_mul]
        have hMid : cardD * (qH * B * roCoinPow cardD K) = qH * B * (cardD * roCoinPow cardD K) := by
          simp only [Nat.mul_left_comm, Nat.mul_comm]
        rw [hMid, Nat.add_comm]
      exact Nat.le_trans (Nat.add_le_add_right hB _) (Nat.le_of_eq (by simpa only [Nat.mul_assoc] using hRearr))

/-- Verify a final query after running `adv`, consuming one additional RO evaluation. -/
def withFinalRoCheck {Dom R : Type} {cardD : Nat} (finalQuery : R → Dom)
    (adv : Code (roOracleIface Dom cardD) R) : Code (roOracleIface Dom cardD) (R × Fin cardD) :=
  Code.bind adv (fun out => .call (finalQuery out) (fun y => .ret (out, y)))

theorem withFinalRoCheck_within {Dom R : Type} {cardD qH : Nat} (finalQuery : R → Dom)
    {adv : Code (roOracleIface Dom cardD) R} (hW : Within qH adv) :
    Within (qH + 1) (withFinalRoCheck finalQuery adv) :=
  Within.bind hW (fun out => Within.call (E := roOracleIface Dom cardD) (b := 0)
    (finalQuery out) _ (fun y => Within.ret 0 (out, y)))

theorem withFinalRoCheck_mem {Dom R : Type} [DecidableEq Dom] {cardD : Nat} (hCard : 0 < cardD)
    (finalQuery : R → Dom) :
    ∀ (adv : Code (roOracleIface Dom cardD) R) (K : Nat) (st : List (Dom × Fin cardD))
      (ω : Fin (roCoinPow cardD K)),
      let res := lazyRomRun hCard (withFinalRoCheck finalQuery adv) K st ω
      (finalQuery res.1.1, res.1.2) ∈ res.2
  | .ret out, 0, st, _ => lazyRomStep_mem st (finalQuery out) ⟨0, hCard⟩
  | .ret out, K + 1, st, ω =>
    lazyRomStep_mem st (finalQuery out) ((CoinSplit.prod cardD (roCoinPow cardD K)).chal ω)
  | .call q next, 0, st, ω =>
    withFinalRoCheck_mem hCard finalQuery (next (lazyRomStep st q ⟨0, hCard⟩).1) 0
      (lazyRomStep st q ⟨0, hCard⟩).2 ω
  | .call q next, K + 1, st, ω =>
    withFinalRoCheck_mem hCard finalQuery
      (next (lazyRomStep st q ((CoinSplit.prod cardD (roCoinPow cardD K)).chal ω)).1) K
      (lazyRomStep st q ((CoinSplit.prod cardD (roCoinPow cardD K)).chal ω)).2
      ((CoinSplit.prod cardD (roCoinPow cardD K)).advc ω)

/-- Committed distinct-tweak target entry `(tweak, msg, digest)` for coin-sampled ROM `SM-DT-TCR`. -/
structure RomTcrTarget (cardD : Nat) where
  tweak : Bytes
  msg : Bytes
  digest : Fin cardD
  deriving DecidableEq, Repr

/-- Bad step predicate for `SM-DT-TCR`: `(t, m')` collides with the committed target under tweak `t`
    on a distinct message `m' ≠ m`. -/
def romTcrStepBad {cardD : Nat} (targets : List (RomTcrTarget cardD))
    (q : Bytes × Bytes) (d : Fin cardD) : Bool :=
  targets.any (fun e => decide (q.1 = e.tweak ∧ q.2 ≠ e.msg ∧ d = e.digest))

private theorem nodup_map_member_injective {α β : Type} (f : α → β) :
    ∀ (xs : List α), (xs.map f).Nodup → ∀ a b,
      a ∈ xs → b ∈ xs → f a = f b → a = b
  | [], _, _, _, ha, _, _ => nomatch ha
  | x :: xs, hn, a, b, ha, hb, he => by
    have hn' := List.nodup_cons.mp hn
    rcases List.mem_cons.mp ha with hax | hat
    · rcases List.mem_cons.mp hb with hbx | hbt
      · exact hax.trans hbx.symm
      · exact False.elim (hn'.1 (by rw [← hax, he]; exact List.mem_map_of_mem hbt))
    · rcases List.mem_cons.mp hb with hbx | hbt
      · exact False.elim (hn'.1 (by rw [← hbx, ← he]; exact List.mem_map_of_mem hat))
      · exact nodup_map_member_injective f xs hn'.2 a b hat hbt he

private theorem romTcrStepBad_initial_clean {cardD : Nat} (targets : List (RomTcrTarget cardD))
    (hNodup : (targets.map RomTcrTarget.tweak).Nodup) :
    tableHasBad (romTcrStepBad targets)
      (targets.map (fun e => ((e.tweak, e.msg), e.digest))) = false := by
  apply Bool.eq_false_iff.mpr
  intro hBad
  unfold tableHasBad at hBad
  obtain ⟨pair, hMemPair, hStep⟩ := List.any_eq_true.mp hBad
  obtain ⟨e₁, hMem₁, rfl⟩ := List.mem_map.mp hMemPair
  unfold romTcrStepBad at hStep
  obtain ⟨e₂, hMem₂, hDec⟩ := List.any_eq_true.mp hStep
  obtain ⟨hTw, hNeMsg, _⟩ := of_decide_eq_true hDec
  have hSame : e₁ = e₂ := nodup_map_member_injective RomTcrTarget.tweak targets
    hNodup e₁ e₂ hMem₁ hMem₂ hTw
  subst hSame
  exact hNeMsg rfl

private theorem romTcrStepBad_le_one {cardD : Nat} (targets : List (RomTcrTarget cardD))
    (hNodup : (targets.map RomTcrTarget.tweak).Nodup) (q : Bytes × Bytes) :
    sampleSum cardD (fun d => if romTcrStepBad targets q d then 1 else 0) ≤ 1 := by
  refine sampleSum_bool_le_one_of_subsingleton _ (fun d₁ d₂ h₁ h₂ => ?_)
  obtain ⟨e₁, hMem₁, hDec₁⟩ := List.any_eq_true.mp h₁
  obtain ⟨e₂, hMem₂, hDec₂⟩ := List.any_eq_true.mp h₂
  obtain ⟨hTw₁, _, hd₁⟩ := of_decide_eq_true hDec₁
  obtain ⟨hTw₂, _, hd₂⟩ := of_decide_eq_true hDec₂
  have hSame : e₁ = e₂ := nodup_map_member_injective RomTcrTarget.tweak targets
    hNodup e₁ e₂ hMem₁ hMem₂ (hTw₁.symm.trans hTw₂)
  subst hSame
  exact hd₁.trans hd₂.symm

/-- **Coin-Sampled Lazy-ROM `SM-DT-TCR` Game.** Given committed distinct-tweak targets `targets`,
    the adversary `adv` queries the random oracle `(tweak, msg) ↦ Fin cardD` over a tape of `K + 1`
    independent draws and wins if it outputs `(tweak, committed, candidate)` colliding with a
    committed target on `candidate ≠ committed`. -/
def romSmDtTcrGame {cardD : Nat} (hCard : 0 < cardD) (targets : List (RomTcrTarget cardD))
    (K : Nat) (adv : Code (roOracleIface (Bytes × Bytes) cardD) TargetBreak) :
    FinGame (roCoinPow cardD (K + 1)) where
  samplePos := roCoinPow_pos hCard (K + 1)
  win ω :=
    let st₀ := targets.map (fun e => ((e.tweak, e.msg), e.digest))
    let res := lazyRomRun hCard
      (withFinalRoCheck (fun out : TargetBreak => (out.tweak, out.candidate)) adv) (K + 1) st₀ ω
    let out := res.1.1
    let yCand := res.1.2
    targets.any (fun e =>
      decide (out.tweak = e.tweak ∧ out.committed = e.msg ∧
        out.candidate ≠ e.msg ∧ yCand = e.digest))

theorem romSmDtTcrGame_win_eq {cardD : Nat} (hCard : 0 < cardD)
    (targets : List (RomTcrTarget cardD)) (K : Nat)
    (adv : Code (roOracleIface (Bytes × Bytes) cardD) TargetBreak)
    (ω : Fin (roCoinPow cardD (K + 1))) :
    (romSmDtTcrGame hCard targets K adv).win ω =
      let st₀ := targets.map (fun e => ((e.tweak, e.msg), e.digest))
      let res := lazyRomRun hCard
        (withFinalRoCheck (fun out : TargetBreak => (out.tweak, out.candidate)) adv) (K + 1) st₀ ω
      targets.any (fun e =>
        decide (res.1.1.tweak = e.tweak ∧ res.1.1.committed = e.msg ∧
          res.1.1.candidate ≠ e.msg ∧ res.1.2 = e.digest)) := by unfold romSmDtTcrGame; rfl

/-- **Query-Bounded ROM `SM-DT-TCR` Hardness (`(qH + 1) / cardD`).** Under pairwise-distinct target
    tweaks, every `Within qH` random-oracle adversary (`qH ≤ K`) wins `romSmDtTcrGame` with
    probability at most `(qH + 1) / cardD`, independent of the number of committed targets. -/
theorem romSmDtTcr_within_bound {cardD : Nat} (hCard : 0 < cardD)
    (targets : List (RomTcrTarget cardD)) (hNodup : (targets.map RomTcrTarget.tweak).Nodup)
    {qH K : Nat} (hqK : qH ≤ K)
    (adv : Code (roOracleIface (Bytes × Bytes) cardD) TargetBreak) (hW : Within qH adv) :
    GameBound (romSmDtTcrGame hCard targets K adv).winProb ⟨qH + 1, cardD, hCard⟩ := by
  let st₀ := targets.map (fun e => ((e.tweak, e.msg), e.digest))
  let prog := withFinalRoCheck (fun out : TargetBreak => (out.tweak, out.candidate)) adv
  have hImp : ∀ ω : Fin (roCoinPow cardD (K + 1)),
      (romSmDtTcrGame hCard targets K adv).win ω = true →
      tableHasBad (romTcrStepBad targets) (lazyRomRun hCard prog (K + 1) st₀ ω).2 = true := by
    intro ω hWin
    obtain ⟨e, hMemE, hDec⟩ := List.any_eq_true.mp hWin
    obtain ⟨hTw, _, hNe, hDig⟩ := of_decide_eq_true hDec
    have hInTable := withFinalRoCheck_mem hCard
      (fun out : TargetBreak => (out.tweak, out.candidate)) adv (K + 1) st₀ ω
    unfold tableHasBad
    exact List.any_eq_true.mpr ⟨_, hInTable,
      List.any_eq_true.mpr ⟨e, hMemE, decide_eq_true ⟨hTw, hNe, hDig⟩⟩⟩
  have hRed := sampleSum_le (roCoinPow cardD (K + 1))
    (fun ω => if (romSmDtTcrGame hCard targets K adv).win ω then 1 else 0)
    (fun ω => if tableHasBad (romTcrStepBad targets) (lazyRomRun hCard prog (K + 1) st₀ ω).2
      then 1 else 0)
    (fun ω => by
      cases hw : (romSmDtTcrGame hCard targets K adv).win ω
      · exact Nat.zero_le _
      · rw [hImp ω hw]; exact Nat.le_refl 1)
  have hMaster := lazyRomRun_bad_bound hCard (romTcrStepBad targets) 1
    (romTcrStepBad_le_one targets hNodup) prog (Nat.succ_le_succ hqK)
    (withFinalRoCheck_within _ hW) st₀ (romTcrStepBad_initial_clean targets hNodup)
  rw [Nat.mul_one] at hMaster
  unfold GameBound RatBound.le FinGame.winProb FinGame.winCount
  dsimp only
  exact Nat.le_trans (Nat.mul_le_mul_right cardD hRed) hMaster

/-- **Coin-Sampled Lazy-ROM `SM-DT-PRE` Game.** Given distinct tweaks `tweaks` (`tweaks.length = qT`),
    a coin in `roCoinPow cardX qT * (roCoinPow cardD qT * roCoinPow cardD (K + 1))` samples `qT`
    independent uniform hidden inputs in `Fin cardX`, `qT` uniform target digests in `Fin cardD`,
    and `K + 1` lazy RO draws; the adversary receives `[(t_i, y_i)]` and wins if its candidate
    `(tweak, idx)` hashes to `y_i` under `tweak = t_i`. -/
def romPreDecodeVec {base : Nat} (hBase : 0 < base) :
    (m : Nat) → Fin (roCoinPow base m) → List (Fin base)
  | 0, _ => []
  | m + 1, ω =>
    let p := CoinSplit.prod base (roCoinPow base m)
    p.chal ω :: romPreDecodeVec hBase m (p.advc ω)

theorem romPreDecodeVec_length {base : Nat} (hBase : 0 < base) :
    ∀ (m : Nat) (ω : Fin (roCoinPow base m)), (romPreDecodeVec hBase m ω).length = m
  | 0, _ => rfl
  | m + 1, _ω => congrArg Nat.succ (romPreDecodeVec_length hBase m _)

private theorem romPreDecodeVec_hit_bound {cardX : Nat} (hX : 0 < cardX) :
    ∀ (m idx : Nat) (target : Fin cardX),
      sampleSum (roCoinPow cardX m)
        (fun xVec =>
          match (romPreDecodeVec hX m xVec)[idx]? with
          | some x => if x = target then 1 else 0
          | none => 0) * cardX ≤ roCoinPow cardX m
  | 0, idx, target => by
    have hZ : (fun xVec : Fin (roCoinPow cardX 0) =>
        match (romPreDecodeVec hX 0 xVec)[idx]? with
        | some x => if x = target then 1 else 0
        | none => 0) = (fun _ => 0) := rfl
    rw [hZ, sampleSum_const, Nat.mul_zero, Nat.zero_mul]
    exact Nat.zero_le _
  | m + 1, 0, target => by
    change sampleSum (cardX * roCoinPow cardX m) _ * cardX ≤ _
    rw [sampleSum_prod cardX (roCoinPow cardX m)]
    let p := CoinSplit.prod cardX (roCoinPow cardX m)
    have hSimpl : sampleSum cardX (fun d => sampleSum (roCoinPow cardX m) (fun τ =>
        match (romPreDecodeVec hX (m + 1) ⟨d.1 * roCoinPow cardX m + τ.1,
          prodCoin_pair_lt d τ⟩)[0]? with
        | some x => if x = target then 1 else 0
        | none => 0)) =
        sampleSum cardX (fun d => (if d = target then 1 else 0) * roCoinPow cardX m) := by
      refine sampleSum_ext (fun d => ?_)
      have hInner : (fun τ : Fin (roCoinPow cardX m) =>
          match (romPreDecodeVec hX (m + 1) ⟨d.1 * roCoinPow cardX m + τ.1,
            prodCoin_pair_lt d τ⟩)[0]? with
          | some x => if x = target then 1 else 0
          | none => 0) = (fun _ => if d = target then 1 else 0) := by
        funext τ
        have hPair : (⟨d.1 * roCoinPow cardX m + τ.1, prodCoin_pair_lt d τ⟩ :
            Fin (cardX * roCoinPow cardX m)) = p.pair d τ := rfl
        rw [hPair]
        show (if p.chal (p.pair d τ) = target then 1 else 0) = _
        rw [p.chal_pair]
      rw [hInner, sampleSum_const, Nat.mul_comm]
    rw [hSimpl, sampleSum_mul_right]
    have hLe := Nat.mul_le_mul_right (roCoinPow cardX m * cardX)
      (sampleSum_indicator_le_one cardX target)
    rw [Nat.one_mul, ← Nat.mul_assoc] at hLe
    refine Nat.le_trans hLe ?_
    rw [Nat.mul_comm (roCoinPow cardX m) cardX]
    exact Nat.le_refl _
  | m + 1, idx + 1, target => by
    change sampleSum (cardX * roCoinPow cardX m) _ * cardX ≤ _
    rw [sampleSum_prod cardX (roCoinPow cardX m)]
    let p := CoinSplit.prod cardX (roCoinPow cardX m)
    have hSimpl : sampleSum cardX (fun d => sampleSum (roCoinPow cardX m) (fun τ =>
        match (romPreDecodeVec hX (m + 1) ⟨d.1 * roCoinPow cardX m + τ.1,
          prodCoin_pair_lt d τ⟩)[idx + 1]? with
        | some x => if x = target then 1 else 0
        | none => 0)) =
        sampleSum cardX (fun _ => sampleSum (roCoinPow cardX m) (fun τ =>
          match (romPreDecodeVec hX m τ)[idx]? with
          | some x => if x = target then 1 else 0
          | none => 0)) := by
      refine sampleSum_ext (fun d => sampleSum_ext (fun τ => ?_))
      have hPair : (⟨d.1 * roCoinPow cardX m + τ.1, prodCoin_pair_lt d τ⟩ :
          Fin (cardX * roCoinPow cardX m)) = p.pair d τ := rfl
      rw [hPair]
      show (match (p.chal (p.pair d τ) :: romPreDecodeVec hX m (p.advc (p.pair d τ)))[idx + 1]? with
        | some x => if x = target then 1 else 0
        | none => 0) = _
      rw [p.advc_pair]
      rfl
    rw [hSimpl, sampleSum_const, Nat.mul_assoc]
    exact Nat.mul_le_mul_left cardX (romPreDecodeVec_hit_bound hX m idx target)

/-- Coin-sampled ROM `SM-DT-PRE` game over `(xVec, yVec, τ)`. -/
def romSmDtPreGame {cardX cardD : Nat} (hX : 0 < cardX) (hD : 0 < cardD)
    (tweaks : List Bytes) (K : Nat)
    (adv : List (Bytes × Fin cardD) → Code (roOracleIface (Bytes × Fin cardX) cardD) (Bytes × Fin cardX)) :
    FinGame (roCoinPow cardX tweaks.length *
      (roCoinPow cardD tweaks.length * roCoinPow cardD (K + 1))) where
  samplePos := Nat.mul_pos (roCoinPow_pos hX _)
    (Nat.mul_pos (roCoinPow_pos hD _) (roCoinPow_pos hD (K + 1)))
  win ω :=
    let s1 := CoinSplit.prod (roCoinPow cardX tweaks.length)
      (roCoinPow cardD tweaks.length * roCoinPow cardD (K + 1))
    let s2 := CoinSplit.prod (roCoinPow cardD tweaks.length) (roCoinPow cardD (K + 1))
    let xs := romPreDecodeVec hX tweaks.length (s1.chal ω)
    let ys := romPreDecodeVec hD tweaks.length (s2.chal (s1.advc ω))
    let τ := s2.advc (s1.advc ω)
    let pubTargets := List.zip tweaks ys
    let st₀ := List.zip (List.zip tweaks xs) ys
    let res := lazyRomRun hD (withFinalRoCheck id (adv pubTargets)) (K + 1) st₀ τ
    pubTargets.any (fun ty => decide (res.1.1.1 = ty.1 ∧ res.1.2 = ty.2))

theorem romSmDtPreGame_win_eq {cardX cardD : Nat} (hX : 0 < cardX) (hD : 0 < cardD)
    (tweaks : List Bytes) (K : Nat)
    (adv : List (Bytes × Fin cardD) → Code (roOracleIface (Bytes × Fin cardX) cardD) (Bytes × Fin cardX))
    (ω : Fin (roCoinPow cardX tweaks.length *
      (roCoinPow cardD tweaks.length * roCoinPow cardD (K + 1)))) :
    (romSmDtPreGame hX hD tweaks K adv).win ω =
      let s1 := CoinSplit.prod (roCoinPow cardX tweaks.length)
        (roCoinPow cardD tweaks.length * roCoinPow cardD (K + 1))
      let s2 := CoinSplit.prod (roCoinPow cardD tweaks.length) (roCoinPow cardD (K + 1))
      let xs := romPreDecodeVec hX tweaks.length (s1.chal ω)
      let ys := romPreDecodeVec hD tweaks.length (s2.chal (s1.advc ω))
      let τ := s2.advc (s1.advc ω)
      let pubTargets := List.zip tweaks ys
      let st₀ := List.zip (List.zip tweaks xs) ys
      let res := lazyRomRun hD (withFinalRoCheck id (adv pubTargets)) (K + 1) st₀ τ
      pubTargets.any (fun ty => decide (res.1.1.1 = ty.1 ∧ res.1.2 = ty.2)) := by unfold romSmDtPreGame; rfl

private def romPreIdealQueries {Dom R : Type} [DecidableEq Dom] {cardD : Nat} (hD : 0 < cardD) :
    Code (roOracleIface Dom cardD) R → (K : Nat) → List (Dom × Fin cardD) →
      Fin (roCoinPow cardD K) → List Dom
  | .ret _, _, _, _ => []
  | .call q next, 0, st, ω =>
    let step := lazyRomStep st q ⟨0, hD⟩
    q :: romPreIdealQueries hD (next step.1) 0 step.2 ω
  | .call q next, K + 1, st, ω =>
    let p := CoinSplit.prod cardD (roCoinPow cardD K)
    let step := lazyRomStep st q (p.chal ω)
    q :: romPreIdealQueries hD (next step.1) K step.2 (p.advc ω)

private theorem romPreIdealQueries_length {Dom R : Type} [DecidableEq Dom] {cardD : Nat}
    (hD : 0 < cardD) :
    ∀ (c : Code (roOracleIface Dom cardD) R) {qH K : Nat},
      Within qH c → ∀ (st : List (Dom × Fin cardD)) (ω : Fin (roCoinPow cardD K)),
      (romPreIdealQueries hD c K st ω).length ≤ qH
  | .ret _, _, _, _, _, _ => Nat.zero_le _
  | .call _ _, 0, _, hW, _, _ => nomatch hW
  | .call _q _next, _ + 1, 0, .call _ _ hk, _st, ω =>
    Nat.succ_le_succ (romPreIdealQueries_length hD _ (hk _) _ ω)
  | .call _q _next, _ + 1, _K + 1, .call _ _ hk, _st, _ω =>
    Nat.succ_le_succ (romPreIdealQueries_length hD _ (hk _) _ _)

private theorem roLookup_append_of_absent {Dom : Type} [DecidableEq Dom] {cardD : Nat}
    (base : List (Dom × Fin cardD)) (q : Dom) (hn : q ∉ base.map Prod.fst)
    (extra : List (Dom × Fin cardD)) : roLookup (extra ++ base) q = roLookup extra q := by
  have hb : roLookup base q = none := by
    induction base with
    | nil => rfl
    | cons hd tl ih =>
      rcases hd with ⟨x, y⟩
      have hx : q ≠ x := fun h => hn (by simp [h])
      simp only [roLookup, iteOfNeg hx]
      exact ih (fun h => hn (List.Mem.tail _ h))
  induction extra with
  | nil => exact hb
  | cons hd tl ih =>
    rcases hd with ⟨x, y⟩
    simp only [List.cons_append, roLookup]
    split <;> simp_all

theorem sampleSum_comm (a b : Nat) (g : Fin a → Fin b → Nat) :
    sampleSum a (fun i => sampleSum b (fun j => g i j)) =
      sampleSum b (fun j => sampleSum a (fun i => g i j)) := by
  induction a with
  | zero => simp only [sampleSum_zero, sampleSum_const, Nat.mul_zero]
  | succ a ih =>
    conv => lhs; rw [sampleSum_succ]
    rw [ih]
    have hr : sampleSum b (fun j => sampleSum (a + 1) (fun i => g i j)) =
        sampleSum b (fun j => g ⟨0, Nat.zero_lt_succ a⟩ j +
          sampleSum a (fun i => g ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ j)) := rfl
    rw [hr, sampleSum_add_fn]

theorem sampleSum_bool_mono {n : Nat} (p q : Fin n → Bool)
    (h : ∀ i, p i = true → q i = true) :
    sampleSum n (fun i => if p i then 1 else 0) ≤
      sampleSum n (fun i => if q i then 1 else 0) := by
  apply sampleSum_le
  intro i
  cases hp : p i
  · exact Nat.zero_le _
  · simp only [h i hp, ↓reduceIte, Nat.le_refl]

private theorem lazyRomRun_agree_unless_queried {Dom R : Type} [DecidableEq Dom] {cardD : Nat}
    (hD : 0 < cardD) (stBase : List (Dom × Fin cardD)) :
    ∀ (c : Code (roOracleIface Dom cardD) R) (K : Nat) (stExtra : List (Dom × Fin cardD))
      (ω : Fin (roCoinPow cardD K)),
      (∀ q ∈ romPreIdealQueries hD c K stExtra ω, q ∉ stBase.map Prod.fst) →
      (lazyRomRun hD c K (stExtra ++ stBase) ω).1 = (lazyRomRun hD c K stExtra ω).1
  | .ret _, _, _, _, _ => rfl
  | .call q next, 0, stExtra, ω, hDisj => by
    have hNotBase : q ∉ stBase.map Prod.fst := hDisj q (List.Mem.head _)
    have hLookEq := roLookup_append_of_absent stBase q hNotBase stExtra
    have hStep : lazyRomStep (stExtra ++ stBase) q ⟨0, hD⟩ =
        ((lazyRomStep stExtra q ⟨0, hD⟩).1, (lazyRomStep stExtra q ⟨0, hD⟩).2 ++ stBase) := by
      unfold lazyRomStep; rw [hLookEq]
      cases roLookup stExtra q <;> rfl
    show (lazyRomRun hD (next (lazyRomStep (stExtra ++ stBase) q ⟨0, hD⟩).1) 0
      (lazyRomStep (stExtra ++ stBase) q ⟨0, hD⟩).2 ω).1 = _
    rw [hStep]
    exact lazyRomRun_agree_unless_queried hD stBase _ 0 _ ω
      (fun q' hq' => hDisj q' (List.Mem.tail _ hq'))
  | .call q next, K + 1, stExtra, ω, hDisj => by
    let p := CoinSplit.prod cardD (roCoinPow cardD K)
    have hNotBase : q ∉ stBase.map Prod.fst := hDisj q (List.Mem.head _)
    have hLookEq := roLookup_append_of_absent stBase q hNotBase stExtra
    have hStep : lazyRomStep (stExtra ++ stBase) q (p.chal ω) =
        ((lazyRomStep stExtra q (p.chal ω)).1, (lazyRomStep stExtra q (p.chal ω)).2 ++ stBase) := by
      unfold lazyRomStep; rw [hLookEq]
      cases roLookup stExtra q <;> rfl
    show (lazyRomRun hD (next (lazyRomStep (stExtra ++ stBase) q (p.chal ω)).1) K
      (lazyRomStep (stExtra ++ stBase) q (p.chal ω)).2 (p.advc ω)).1 = _
    rw [hStep]
    exact lazyRomRun_agree_unless_queried hD stBase _ K _ (p.advc ω)
      (fun q' hq' => hDisj q' (List.Mem.tail _ hq'))

private def findTweakIdx (tweaks : List Bytes) (t : Bytes) : Option Nat :=
  (tweaks.zipIdx).find? (fun e => decide (e.1 = t)) |>.map Prod.snd

private theorem mem_zip_tweaks_implies_find {cardX : Nat} :
    ∀ (tweaks : List Bytes) (xs : List (Fin cardX)) (q : Bytes × Fin cardX),
      tweaks.Nodup → q ∈ List.zip tweaks xs →
      ∃ idx : Nat, findTweakIdx tweaks q.1 = some idx ∧ xs[idx]? = some q.2 := by
  suffices ∀ (tweaks : List Bytes) (xs : List (Fin cardX)) (q : Bytes × Fin cardX) (k : Nat),
      tweaks.Nodup → q ∈ List.zip tweaks xs →
      ∃ idx : Nat,
        ((tweaks.zipIdx k).find? (fun e => decide (e.1 = q.1)) |>.map Prod.snd) = some (k + idx) ∧
        xs[idx]? = some q.2 from
    fun tweaks xs q hNd hMem => by
      obtain ⟨idx, h1, h2⟩ := this tweaks xs q 0 hNd hMem
      rw [Nat.zero_add] at h1
      exact ⟨idx, h1, h2⟩
  intro tweaks
  induction tweaks with
  | nil => intro _ _ _ _ h; nomatch h
  | cons t ts ih =>
    intro xs q k hNd hMem
    cases xs with
    | nil => nomatch hMem
    | cons x xs' =>
      obtain ⟨hHead, hTail⟩ := List.nodup_cons.mp hNd
      rcases List.mem_cons.mp hMem with rfl | hRest
      · refine ⟨0, ?_, rfl⟩
        simp [Nat.add_zero]
      · have hNe : ¬ (t = q.1) := fun hEq => by
          have hIn : q.1 ∈ ts := (List.of_mem_zip hRest).1
          exact hHead (hEq.symm ▸ hIn)
        obtain ⟨idx, h1, h2⟩ := ih xs' q (k + 1) hTail hRest
        refine ⟨idx + 1, ?_, h2⟩
        simp only [List.zipIdx_cons, List.find?_cons, decide_eq_false hNe]
        rw [h1]
        exact congrArg some (by omega)

private theorem romPre_queryList_hit_bound {cardX : Nat} (hX : 0 < cardX)
    (tweaks : List Bytes) (hNodup : tweaks.Nodup) :
    ∀ (qs : List (Bytes × Fin cardX)),
      sampleSum (roCoinPow cardX tweaks.length)
        (fun xVec =>
          let xs := romPreDecodeVec hX tweaks.length xVec
          if qs.any (fun q => decide (q ∈ List.zip tweaks xs)) then 1 else 0) * cardX ≤
        qs.length * roCoinPow cardX tweaks.length
  | [] => by
    simp only [List.any_nil, Bool.false_eq_true, ↓reduceIte, sampleSum_const,
      Nat.mul_zero, Nat.zero_mul, List.length_nil, Nat.le_refl]
  | q :: qs => by
    have hSplit : ∀ xVec : Fin (roCoinPow cardX tweaks.length),
        (let xs := romPreDecodeVec hX tweaks.length xVec
         if (q :: qs).any (fun q' => decide (q' ∈ List.zip tweaks xs)) then 1 else 0) ≤
        (match findTweakIdx tweaks q.1 with
         | some idx =>
           match (romPreDecodeVec hX tweaks.length xVec)[idx]? with
           | some x => if x = q.2 then 1 else 0
           | none => 0
         | none => 0) +
        (let xs := romPreDecodeVec hX tweaks.length xVec
         if qs.any (fun q' => decide (q' ∈ List.zip tweaks xs)) then 1 else 0) := by
      intro xVec
      dsimp only
      rw [List.any_cons]
      by_cases hq : q ∈ List.zip tweaks (romPreDecodeVec hX tweaks.length xVec)
      · rw [decide_eq_true hq, Bool.true_or]
        obtain ⟨idx, hFind, hGet⟩ := mem_zip_tweaks_implies_find tweaks _ q hNodup hq
        simp only [hFind, hGet, ↓reduceIte]
        exact Nat.le_add_right 1 _
      · rw [decide_eq_false hq, Bool.false_or]
        exact Nat.le_add_left _ _
    have hSum := sampleSum_le _ _ _ hSplit
    rw [sampleSum_add_fn] at hSum
    have hMul := Nat.mul_le_mul_right cardX hSum
    rw [Nat.add_mul] at hMul
    have hHead : sampleSum (roCoinPow cardX tweaks.length) (fun xVec =>
        match findTweakIdx tweaks q.1 with
        | some idx =>
          match (romPreDecodeVec hX tweaks.length xVec)[idx]? with
          | some x => if x = q.2 then 1 else 0
          | none => 0
        | none => 0) * cardX ≤ roCoinPow cardX tweaks.length := by
      cases findTweakIdx tweaks q.1 with
      | none =>
        rw [sampleSum_const, Nat.mul_zero, Nat.zero_mul]; exact Nat.zero_le _
      | some idx => exact romPreDecodeVec_hit_bound hX tweaks.length idx q.2
    have hTail := romPre_queryList_hit_bound hX tweaks hNodup qs
    refine Nat.le_trans hMul ?_
    rw [List.length_cons, Nat.succ_mul, Nat.add_comm (qs.length * _)]
    exact Nat.add_le_add hHead hTail

/-- **Query-Bounded ROM `SM-DT-PRE` Hardness (`(qH + 1) / cardX + (qH + 1) / cardD`).** Under
    pairwise-distinct tweaks, every family of `Within qH` random-oracle adversaries (`qH ≤ K`) wins
    `romSmDtPreGame` with probability at most `(qH + 1) / cardX + (qH + 1) / cardD`. -/
theorem romSmDtPre_within_bound {cardX cardD : Nat} (hX : 0 < cardX) (hD : 0 < cardD)
    (tweaks : List Bytes) (hNodup : tweaks.Nodup) {qH K : Nat} (hqK : qH ≤ K)
    (adv : List (Bytes × Fin cardD) → Code (roOracleIface (Bytes × Fin cardX) cardD) (Bytes × Fin cardX))
    (hW : ∀ pub, Within qH (adv pub)) :
    GameBound (romSmDtPreGame hX hD tweaks K adv).winProb
      ((⟨qH + 1, cardX, hX⟩ : RatBound).add ⟨qH + 1, cardD, hD⟩) := by
  let N_X := roCoinPow cardX tweaks.length
  let N_Y := roCoinPow cardD tweaks.length
  let N_T := roCoinPow cardD (K + 1)
  let s1 := CoinSplit.prod N_X (N_Y * N_T)
  let s2 := CoinSplit.prod N_Y N_T
  have hPosTotal : 0 < N_X * (N_Y * N_T) := (romSmDtPreGame hX hD tweaks K adv).samplePos
  let hitHidden : Fin (N_X * (N_Y * N_T)) → Bool := fun ω =>
    let xs := romPreDecodeVec hX tweaks.length (s1.chal ω)
    let ys := romPreDecodeVec hD tweaks.length (s2.chal (s1.advc ω))
    let τ := s2.advc (s1.advc ω)
    let prog := withFinalRoCheck id (adv (List.zip tweaks ys))
    (romPreIdealQueries hD prog (K + 1) [] τ).any (fun q => decide (q ∈ List.zip tweaks xs))
  let hitDigestIdeal : Fin (N_X * (N_Y * N_T)) → Bool := fun ω =>
    let ys := romPreDecodeVec hD tweaks.length (s2.chal (s1.advc ω))
    let τ := s2.advc (s1.advc ω)
    let pub := List.zip tweaks ys
    let prog := withFinalRoCheck id (adv pub)
    let res := lazyRomRun hD prog (K + 1) [] τ
    pub.any (fun ty => decide (res.1.1.1 = ty.1 ∧ res.1.2 = ty.2))
  let G₁ : FinGame (N_X * (N_Y * N_T)) := ⟨hPosTotal, hitHidden⟩
  let G₂ : FinGame (N_X * (N_Y * N_T)) := ⟨hPosTotal, hitDigestIdeal⟩
  have hCover : ∀ ω, (romSmDtPreGame hX hD tweaks K adv).win ω = true →
      G₁.win ω = true ∨ G₂.win ω = true := by
    intro ω hWin
    cases hH : G₁.win ω
    · refine .inr ?_
      dsimp only [G₁, hitHidden] at hH
      have hDisj : ∀ q ∈ romPreIdealQueries hD
          (withFinalRoCheck id (adv (List.zip tweaks (romPreDecodeVec hD tweaks.length (s2.chal (s1.advc ω))))))
          (K + 1) [] (s2.advc (s1.advc ω)),
          q ∉ (List.zip (List.zip tweaks (romPreDecodeVec hX tweaks.length (s1.chal ω)))
            (romPreDecodeVec hD tweaks.length (s2.chal (s1.advc ω)))).map Prod.fst := by
        intro q hq hInMap
        obtain ⟨pair, hInZip, rfl⟩ := List.mem_map.mp hInMap
        have hInZX : pair.1 ∈ List.zip tweaks (romPreDecodeVec hX tweaks.length (s1.chal ω)) := by
          clear hH hq hWin
          generalize List.zip tweaks (romPreDecodeVec hX tweaks.length (s1.chal ω)) = zx at hInZip
          generalize romPreDecodeVec hD tweaks.length (s2.chal (s1.advc ω)) = zy at hInZip
          induction zx generalizing zy with
          | nil => nomatch hInZip
          | cons a as ih =>
            cases zy with
            | nil => nomatch hInZip
            | cons b bs =>
              rcases List.mem_cons.mp hInZip with rfl | hR
              · exact List.Mem.head _
              · exact List.Mem.tail _ (ih bs hR)
        have hAny : (romPreIdealQueries hD
            (withFinalRoCheck id (adv (List.zip tweaks (romPreDecodeVec hD tweaks.length (s2.chal (s1.advc ω))))))
            (K + 1) [] (s2.advc (s1.advc ω))).any
            (fun q' => decide (q' ∈ List.zip tweaks (romPreDecodeVec hX tweaks.length (s1.chal ω)))) = true :=
          List.any_eq_true.mpr ⟨pair.1, hq, decide_eq_true hInZX⟩
        rw [hAny] at hH
        cases hH
      have hAgree := lazyRomRun_agree_unless_queried hD
        (List.zip (List.zip tweaks (romPreDecodeVec hX tweaks.length (s1.chal ω)))
          (romPreDecodeVec hD tweaks.length (s2.chal (s1.advc ω))))
        (withFinalRoCheck id (adv (List.zip tweaks (romPreDecodeVec hD tweaks.length (s2.chal (s1.advc ω))))))
        (K + 1) [] (s2.advc (s1.advc ω)) hDisj
      rw [List.nil_append] at hAgree
      dsimp only [G₂, hitDigestIdeal]
      rw [romSmDtPreGame_win_eq] at hWin
      dsimp only at hWin
      rw [hAgree] at hWin
      exact hWin
    · exact .inl rfl
  have hB1 : GameBound G₁.winProb ⟨qH + 1, cardX, hX⟩ := by
    unfold GameBound RatBound.le FinGame.winProb FinGame.winCount
    dsimp only [G₁, hitHidden]
    rw [s1.sampleSum_eq]
    have hSwap : sampleSum N_X (fun xVec => sampleSum (N_Y * N_T) (fun yτ =>
        if (romPreIdealQueries hD
            (withFinalRoCheck id (adv (List.zip tweaks
              (romPreDecodeVec hD tweaks.length (s2.chal (s1.advc (s1.pair xVec yτ)))))))
            (K + 1) [] (s2.advc (s1.advc (s1.pair xVec yτ)))).any
            (fun q => decide (q ∈ List.zip tweaks
              (romPreDecodeVec hX tweaks.length (s1.chal (s1.pair xVec yτ)))))
        then 1 else 0)) =
        sampleSum (N_Y * N_T) (fun yτ => sampleSum N_X (fun xVec =>
          let xs := romPreDecodeVec hX tweaks.length xVec
          if (romPreIdealQueries hD
              (withFinalRoCheck id (adv (List.zip tweaks (romPreDecodeVec hD tweaks.length (s2.chal yτ)))))
              (K + 1) [] (s2.advc yτ)).any (fun q => decide (q ∈ List.zip tweaks xs))
          then 1 else 0)) := by
      have hClean1 : sampleSum N_X (fun xVec => sampleSum (N_Y * N_T) (fun yτ =>
          if (romPreIdealQueries hD
              (withFinalRoCheck id (adv (List.zip tweaks
                (romPreDecodeVec hD tweaks.length (s2.chal (s1.advc (s1.pair xVec yτ)))))))
              (K + 1) [] (s2.advc (s1.advc (s1.pair xVec yτ)))).any
              (fun q => decide (q ∈ List.zip tweaks
                (romPreDecodeVec hX tweaks.length (s1.chal (s1.pair xVec yτ)))))
          then 1 else 0)) =
          sampleSum N_X (fun xVec => sampleSum (N_Y * N_T) (fun yτ =>
            let xs := romPreDecodeVec hX tweaks.length xVec
            if (romPreIdealQueries hD
                (withFinalRoCheck id (adv (List.zip tweaks (romPreDecodeVec hD tweaks.length (s2.chal yτ)))))
                (K + 1) [] (s2.advc yτ)).any (fun q => decide (q ∈ List.zip tweaks xs))
            then 1 else 0)) :=
        sampleSum_ext (fun xVec => sampleSum_ext (fun yτ => by rw [s1.chal_pair, s1.advc_pair]))
      rw [hClean1]
      exact sampleSum_comm _ _ _
    rw [hSwap, ← sampleSum_mul_right]
    have hPt : ∀ yτ : Fin (N_Y * N_T),
        sampleSum N_X (fun xVec =>
          let xs := romPreDecodeVec hX tweaks.length xVec
          if (romPreIdealQueries hD
              (withFinalRoCheck id (adv (List.zip tweaks (romPreDecodeVec hD tweaks.length (s2.chal yτ)))))
              (K + 1) [] (s2.advc yτ)).any (fun q => decide (q ∈ List.zip tweaks xs))
          then 1 else 0) * cardX ≤ (qH + 1) * N_X := fun yτ => by
      have hLen := romPreIdealQueries_length hD _
        (withFinalRoCheck_within id (hW (List.zip tweaks (romPreDecodeVec hD tweaks.length (s2.chal yτ))))) [] (s2.advc yτ)
      exact Nat.le_trans (romPre_queryList_hit_bound hX tweaks hNodup _)
        (Nat.mul_le_mul_right N_X hLen)
    have hSum := sampleSum_le (N_Y * N_T) _ _ hPt
    rw [sampleSum_const] at hSum
    refine Nat.le_trans hSum ?_
    simp only [Nat.mul_assoc, Nat.mul_comm]
    exact Nat.le_refl _
  have hB2 : GameBound G₂.winProb ⟨qH + 1, cardD, hD⟩ := by
    unfold GameBound RatBound.le FinGame.winProb FinGame.winCount
    dsimp only [G₂, hitDigestIdeal]
    rw [s1.sampleSum_eq]
    have hInnerConst : ∀ xVec : Fin N_X,
        sampleSum (N_Y * N_T) (fun yτ =>
          let ys := romPreDecodeVec hD tweaks.length (s2.chal (s1.advc (s1.pair xVec yτ)))
          let τ := s2.advc (s1.advc (s1.pair xVec yτ))
          let pub := List.zip tweaks ys
          let res := lazyRomRun hD (withFinalRoCheck id (adv pub)) (K + 1) [] τ
          if pub.any (fun ty => decide (res.1.1.1 = ty.1 ∧ res.1.2 = ty.2)) then 1 else 0) * cardD ≤
        (qH + 1) * (N_Y * N_T) := fun xVec => by
      have hS2 : sampleSum (N_Y * N_T) (fun yτ =>
          let ys := romPreDecodeVec hD tweaks.length (s2.chal (s1.advc (s1.pair xVec yτ)))
          let τ := s2.advc (s1.advc (s1.pair xVec yτ))
          let pub := List.zip tweaks ys
          let res := lazyRomRun hD (withFinalRoCheck id (adv pub)) (K + 1) [] τ
          if pub.any (fun ty => decide (res.1.1.1 = ty.1 ∧ res.1.2 = ty.2)) then 1 else 0) =
          sampleSum N_Y (fun yVec => sampleSum N_T (fun τ =>
            let pub := List.zip tweaks (romPreDecodeVec hD tweaks.length yVec)
            let res := lazyRomRun hD (withFinalRoCheck id (adv pub)) (K + 1) [] τ
            if pub.any (fun ty => decide (res.1.1.1 = ty.1 ∧ res.1.2 = ty.2)) then 1 else 0)) := by
        rw [s2.sampleSum_eq]
        exact sampleSum_ext (fun yVec => sampleSum_ext (fun τ => by
          rw [s1.advc_pair, s2.chal_pair, s2.advc_pair]))
      rw [hS2, ← sampleSum_mul_right]
      have hPerY : ∀ yVec : Fin N_Y,
          sampleSum N_T (fun τ =>
            let pub := List.zip tweaks (romPreDecodeVec hD tweaks.length yVec)
            let res := lazyRomRun hD (withFinalRoCheck id (adv pub)) (K + 1) [] τ
            if pub.any (fun ty => decide (res.1.1.1 = ty.1 ∧ res.1.2 = ty.2)) then 1 else 0) * cardD ≤
          (qH + 1) * N_T := fun yVec => by
        let pub := List.zip tweaks (romPreDecodeVec hD tweaks.length yVec)
        let stepBad : (Bytes × Fin cardX) → Fin cardD → Bool := fun q d =>
          pub.any (fun ty => decide (q.1 = ty.1 ∧ d = ty.2))
        have hSub : ∀ q : Bytes × Fin cardX,
            sampleSum cardD (fun d => if stepBad q d then 1 else 0) ≤ 1 := fun q => by
          refine sampleSum_bool_le_one_of_subsingleton _ (fun d₁ d₂ h₁ h₂ => ?_)
          obtain ⟨ty₁, hm₁, hd₁⟩ := List.any_eq_true.mp h₁
          obtain ⟨ty₂, hm₂, hd₂⟩ := List.any_eq_true.mp h₂
          obtain ⟨ht₁, hv₁⟩ := of_decide_eq_true hd₁
          obtain ⟨ht₂, hv₂⟩ := of_decide_eq_true hd₂
          have hSame : ty₁ = ty₂ := by
            have hn : (pub.map Prod.fst).Nodup := by
              dsimp only [pub]
              rw [List.map_fst_zip (by rw [romPreDecodeVec_length]; exact Nat.le_refl _)]
              exact hNodup
            exact nodup_map_member_injective Prod.fst pub hn ty₁ ty₂ hm₁ hm₂ (ht₁.symm.trans ht₂)
          subst hSame
          exact hv₁.trans hv₂.symm
        have hImp : ∀ τ : Fin N_T,
            (let res := lazyRomRun hD (withFinalRoCheck id (adv pub)) (K + 1) [] τ
             pub.any (fun ty => decide (res.1.1.1 = ty.1 ∧ res.1.2 = ty.2))) = true →
            tableHasBad stepBad
              (lazyRomRun hD (withFinalRoCheck id (adv pub)) (K + 1) [] τ).2 = true := by
          intro τ hWτ
          have hIn := withFinalRoCheck_mem hD id (adv pub) (K + 1) [] τ
          exact List.any_eq_true.mpr ⟨_, hIn, hWτ⟩
        have hLe := sampleSum_bool_mono _ _ hImp
        have hM := lazyRomRun_bad_bound hD stepBad 1 hSub (withFinalRoCheck id (adv pub))
          (Nat.succ_le_succ hqK) (withFinalRoCheck_within id (hW pub)) [] rfl
        rw [Nat.mul_one] at hM
        exact Nat.le_trans (Nat.mul_le_mul_right cardD hLe) hM
      have hSum := sampleSum_le N_Y _ _ hPerY
      rw [sampleSum_const] at hSum
      refine Nat.le_trans hSum ?_
      simp only [Nat.mul_left_comm]
      exact Nat.le_refl _
    rw [← sampleSum_mul_right]
    have hSum := sampleSum_le N_X _ _ hInnerConst
    rw [sampleSum_const] at hSum
    refine Nat.le_trans hSum ?_
    simp only [Nat.mul_left_comm]
    exact Nat.le_refl _
  exact RatBound.le_trans
    (event_le_two_reductions (romSmDtPreGame hX hD tweaks K adv) G₁ G₂ hCover)
    (RatBound.add_le_add hB1 hB2)

/-- **Coin-Sampled Lazy-ROM `ITSR` Game.** Given a signed transcript `signedPairs : List (Bytes × Bytes)`
    and its opened subset-codeword outputs `opened : List (Fin cardSub)` (`st₀ = zip signedPairs opened`),
    the adversary queries the subset random oracle `(rand, msg) ↦ Fin cardSub` over `K + 1` draws
    and outputs `(r*, m*)`, winning if `(r*, m*) ∉ signedPairs` and its subset codeword is covered
    by `opened` (`coveredBy opened yStar = true`). -/
def romItsrGame {cardSub : Nat} (hCard : 0 < cardSub)
    (coveredBy : List (Fin cardSub) → Fin cardSub → Bool)
    (signedPairs : List (Bytes × Bytes)) (opened : List (Fin cardSub))
    (K : Nat) (adv : Code (roOracleIface (Bytes × Bytes) cardSub) (Bytes × Bytes)) :
    FinGame (roCoinPow cardSub (K + 1)) where
  samplePos := roCoinPow_pos hCard (K + 1)
  win ω :=
    let st₀ := List.zip signedPairs opened
    let res := lazyRomRun hCard (withFinalRoCheck id adv) (K + 1) st₀ ω
    !decide (res.1.1 ∈ signedPairs) && coveredBy opened res.1.2

theorem romItsrGame_win_eq {cardSub : Nat} (hCard : 0 < cardSub)
    (coveredBy : List (Fin cardSub) → Fin cardSub → Bool)
    (signedPairs : List (Bytes × Bytes)) (opened : List (Fin cardSub))
    (K : Nat) (adv : Code (roOracleIface (Bytes × Bytes) cardSub) (Bytes × Bytes))
    (ω : Fin (roCoinPow cardSub (K + 1))) :
    (romItsrGame hCard coveredBy signedPairs opened K adv).win ω =
      let st₀ := List.zip signedPairs opened
      let res := lazyRomRun hCard (withFinalRoCheck id adv) (K + 1) st₀ ω
      (!decide (res.1.1 ∈ signedPairs) && coveredBy opened res.1.2) := by unfold romItsrGame; rfl

/-- **Query-Bounded ROM `ITSR` Hardness (`(qH + 1) * maxCovered / cardSub`).** Whenever at most
    `maxCovered` subset codewords in `Fin cardSub` are covered by `opened`, every `Within qH`
    random-oracle adversary (`qH ≤ K`) wins `romItsrGame` with probability at most
    `((qH + 1) * maxCovered) / cardSub`. -/
theorem romItsr_within_bound {cardSub : Nat} (hCard : 0 < cardSub)
    (coveredBy : List (Fin cardSub) → Fin cardSub → Bool)
    (signedPairs : List (Bytes × Bytes)) (opened : List (Fin cardSub))
    (maxCovered : Nat)
    (hCover : sampleSum cardSub (fun s => if coveredBy opened s then 1 else 0) ≤ maxCovered)
    {qH K : Nat} (hqK : qH ≤ K)
    (adv : Code (roOracleIface (Bytes × Bytes) cardSub) (Bytes × Bytes)) (hW : Within qH adv) :
    GameBound (romItsrGame hCard coveredBy signedPairs opened K adv).winProb
      ⟨(qH + 1) * maxCovered, cardSub, hCard⟩ := by
  let st₀ := List.zip signedPairs opened
  let stepBad : (Bytes × Bytes) → Fin cardSub → Bool := fun q s =>
    !decide (q ∈ signedPairs) && coveredBy opened s
  have hInitClean : tableHasBad stepBad st₀ = false := by
    apply Bool.eq_false_iff.mpr
    intro hBad
    obtain ⟨e, hMem, hStep⟩ := List.any_eq_true.mp hBad
    obtain ⟨hNotIn, _⟩ := andTrueSplit hStep
    have hIn : e.1 ∈ signedPairs := (List.of_mem_zip hMem).1
    rw [decide_eq_true hIn] at hNotIn
    cases hNotIn
  have hStepB : ∀ q : Bytes × Bytes,
      sampleSum cardSub (fun s => if stepBad q s then 1 else 0) ≤ maxCovered := fun q => by
    refine Nat.le_trans (sampleSum_le cardSub _ _ (fun s => ?_)) hCover
    dsimp only [stepBad]
    by_cases hq : q ∈ signedPairs
    · simp only [decide_eq_true hq, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Nat.zero_le]
    · simp only [decide_eq_false hq, Bool.not_false, Bool.true_and, Nat.le_refl]
  let prog := withFinalRoCheck id adv
  have hImp : ∀ ω : Fin (roCoinPow cardSub (K + 1)),
      (romItsrGame hCard coveredBy signedPairs opened K adv).win ω = true →
      tableHasBad stepBad (lazyRomRun hCard prog (K + 1) st₀ ω).2 = true := fun ω hWin =>
    List.any_eq_true.mpr ⟨_, withFinalRoCheck_mem hCard id adv (K + 1) st₀ ω, hWin⟩
  have hRed := sampleSum_bool_mono _ _ hImp
  have hM := lazyRomRun_bad_bound hCard stepBad maxCovered hStepB prog
    (Nat.succ_le_succ hqK) (withFinalRoCheck_within id hW) st₀ hInitClean
  exact Nat.le_trans (Nat.mul_le_mul_right cardSub hRed) hM

/-- Subset-cover predicate for `k`-tuples in `Fin (roCoinPow M k)`: every selected leaf in `Fin M`
    was already revealed among the `opened` `k`-tuples. -/
def tupleSubsetCovered {M k : Nat} (hM : 0 < M)
    (opened : List (Fin (roCoinPow M k))) (cand : Fin (roCoinPow M k)) : Bool :=
  let revLeaves := opened.flatMap (romPreDecodeVec hM k)
  (romPreDecodeVec hM k cand).all (fun x => decide (x ∈ revLeaves))

private theorem list_mem_indicator_sum_le {M : Nat} :
    ∀ (rev : List (Fin M)),
      sampleSum M (fun d => if decide (d ∈ rev) then 1 else 0) ≤ rev.length
  | [] => by
    have hZ : (fun d : Fin M => if decide (d ∈ ([] : List (Fin M))) then 1 else 0) = (fun _ => 0) :=
      rfl
    rw [hZ, sampleSum_const, Nat.mul_zero]
    exact Nat.le_refl 0
  | x :: xs => by
    have hSplit : ∀ d : Fin M,
        (if decide (d ∈ x :: xs) then 1 else 0) ≤
        (if d = x then 1 else 0) + (if decide (d ∈ xs) then 1 else 0) := fun d => by
      by_cases hd : d ∈ x :: xs
      · simp only [decide_eq_true hd, ↓reduceIte]
        rcases List.mem_cons.mp hd with rfl | hTail
        · rw [iteOfPos rfl]; omega
        · simp only [decide_eq_true hTail, ↓reduceIte]; omega
      · rw [decide_eq_false hd]; exact Nat.zero_le _
    have hSum := sampleSum_le M _ _ hSplit
    rw [sampleSum_add_fn] at hSum
    exact Nat.le_trans hSum
      (Nat.le_trans (Nat.add_le_add (sampleSum_indicator_le_one M x) (list_mem_indicator_sum_le xs))
        (by rw [List.length_cons, Nat.add_comm]; exact Nat.le_refl _))

private theorem tupleSubsetCovered_count_le {M : Nat} (hM : 0 < M) (rev : List (Fin M)) :
    ∀ k : Nat,
      sampleSum (roCoinPow M k)
        (fun s => if (romPreDecodeVec hM k s).all (fun x => decide (x ∈ rev)) then 1 else 0) ≤
      rev.length ^ k
  | 0 => by
    change 1 ≤ 1
    exact Nat.le_refl _
  | k + 1 => by
    rw [sampleSum_prod M (roCoinPow M k)]
    let p := CoinSplit.prod M (roCoinPow M k)
    have hFactor : sampleSum M (fun d => sampleSum (roCoinPow M k) (fun τ =>
        if (romPreDecodeVec hM (k + 1) ⟨d.1 * roCoinPow M k + τ.1, prodCoin_pair_lt d τ⟩).all
            (fun x => decide (x ∈ rev))
        then 1 else 0)) =
        sampleSum M (fun d =>
          (if decide (d ∈ rev) then 1 else 0) *
          sampleSum (roCoinPow M k) (fun τ =>
            if (romPreDecodeVec hM k τ).all (fun x => decide (x ∈ rev)) then 1 else 0)) := by
      refine sampleSum_ext (fun d => ?_)
      cases hd : decide (d ∈ rev)
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_mul]
        have hZ : (fun τ : Fin (roCoinPow M k) =>
            if (romPreDecodeVec hM (k + 1) ⟨d.1 * roCoinPow M k + τ.1, prodCoin_pair_lt d τ⟩).all
                (fun x => decide (x ∈ rev))
            then 1 else 0) = (fun _ => 0) := by
          funext τ
          have hPair : (⟨d.1 * roCoinPow M k + τ.1, prodCoin_pair_lt d τ⟩ :
              Fin (M * roCoinPow M k)) = p.pair d τ := rfl
          rw [hPair]
          show (if (p.chal (p.pair d τ) :: romPreDecodeVec hM k (p.advc (p.pair d τ))).all
              (fun x => decide (x ∈ rev)) then 1 else 0) = 0
          rw [p.chal_pair, List.all_cons, hd, Bool.false_and]
          rfl
        rw [hZ, sampleSum_const, Nat.mul_zero]
      · simp only [↓reduceIte, Nat.one_mul]
        refine sampleSum_ext (fun τ => ?_)
        have hPair : (⟨d.1 * roCoinPow M k + τ.1, prodCoin_pair_lt d τ⟩ :
            Fin (M * roCoinPow M k)) = p.pair d τ := rfl
        rw [hPair]
        show (if (p.chal (p.pair d τ) :: romPreDecodeVec hM k (p.advc (p.pair d τ))).all
            (fun x => decide (x ∈ rev)) then 1 else 0) = _
        rw [p.chal_pair, p.advc_pair, List.all_cons, hd, Bool.true_and]
    rw [hFactor, sampleSum_mul_right, Nat.pow_succ, Nat.mul_comm (rev.length ^ k)]
    exact Nat.mul_le_mul (list_mem_indicator_sum_le rev) (tupleSubsetCovered_count_le hM rev k)

private theorem flatMap_decodeVec_length_le {M k : Nat} (hM : 0 < M) :
    ∀ (opened : List (Fin (roCoinPow M k))),
      (opened.flatMap (romPreDecodeVec hM k)).length ≤ opened.length * k
  | [] => Nat.zero_le _
  | x :: xs => by
    rw [List.flatMap_cons, List.length_append, romPreDecodeVec_length, List.length_cons,
      Nat.succ_mul, Nat.add_comm _ k]
    exact Nat.add_le_add_left (flatMap_decodeVec_length_le hM xs) k

private theorem pow_le_pow_of_le {a b : Nat} (h : a ≤ b) : ∀ k : Nat, a ^ k ≤ b ^ k
  | 0 => Nat.le_refl 1
  | k + 1 => Nat.mul_le_mul (pow_le_pow_of_le h k) h

/-- **Query-Bounded ROM `k`-Tuple Subset-Cover Hardness (`(qH + 1) * (qS * k)^k / M^k`).** After
    `opened.length ≤ qS` signatures each opening `k` leaves in `Fin M`, every `Within qH`
    random-oracle adversary (`qH ≤ K`) wins `romItsrGame` with probability at most
    `((qH + 1) * (qS * k)^k) / M^k`. -/
theorem romItsrTuple_within_bound {M k : Nat} (hM : 0 < M)
    (signedPairs : List (Bytes × Bytes)) (opened : List (Fin (roCoinPow M k)))
    {qS qH K : Nat} (hOpened : opened.length ≤ qS) (hqK : qH ≤ K)
    (adv : Code (roOracleIface (Bytes × Bytes) (roCoinPow M k)) (Bytes × Bytes))
    (hW : Within qH adv) :
    GameBound (romItsrGame (roCoinPow_pos hM k) (tupleSubsetCovered hM) signedPairs opened K adv).winProb
      ⟨(qH + 1) * (qS * k) ^ k, roCoinPow M k, roCoinPow_pos hM k⟩ := by
  have hLen : (opened.flatMap (romPreDecodeVec hM k)).length ≤ qS * k :=
    Nat.le_trans (flatMap_decodeVec_length_le hM opened) (Nat.mul_le_mul_right k hOpened)
  have hCov : sampleSum (roCoinPow M k)
      (fun s => if tupleSubsetCovered hM opened s then 1 else 0) ≤ (qS * k) ^ k :=
    Nat.le_trans (tupleSubsetCovered_count_le hM _ k) (pow_le_pow_of_le hLen k)
  exact romItsr_within_bound (roCoinPow_pos hM k) (tupleSubsetCovered hM) signedPairs opened
    ((qS * k) ^ k) hCov hqK adv hW

/-- `#tooth`: Dropping `Within 0` on `romSmDtTcrGame` breaks the `(0 + 1) / 4` bound — a 2-query
    adversary testing `[1]` and `[2]` against committed target `([], [0], 0)` over `cardD = 4`
    wins with probability `7 / 16 > 1 / 4`. -/
def twoQueryRomTcrAdv : Code (roOracleIface (Bytes × Bytes) 4) TargetBreak :=
  .call ([], [1]) (fun d₁ =>
    if d₁.1 = 0 then .ret ⟨[], [0], [1]⟩
    else .call ([], [2]) (fun _ => .ret ⟨[], [0], [2]⟩))

theorem tooth_romSmDtTcr_without_within :
    ¬ GameBound
        (romSmDtTcrGame (by decide : 0 < 4) [⟨[], [0], ⟨0, by decide⟩⟩] 2 twoQueryRomTcrAdv).winProb
        ⟨0 + 1, 4, by decide⟩ := by
  unfold GameBound RatBound.le
  decide +kernel

/-- `#tooth`: Dropping `Within 0` on `romSmDtPreGame` breaks the `1/2 + 1/4 = 3/4` bound — a
    1-query adversary checking `([], 0)` and falling back to `([], 1)` over `cardX = 2, cardD = 4`
    wins on every coin (`1 > 3 / 4`). -/
def allSearchRomPreAdv :
    List (Bytes × Fin 4) → Code (roOracleIface (Bytes × Fin 2) 4) (Bytes × Fin 2) :=
  fun pub =>
    .call ([], ⟨0, by decide⟩) (fun d₀ =>
      match pub with
      | (_, y) :: _ =>
        if d₀ = y then .ret ([], ⟨0, by decide⟩) else .ret ([], ⟨1, by decide⟩)
      | [] => .ret ([], ⟨0, by decide⟩))

theorem tooth_romSmDtPre_without_within :
    ¬ GameBound
        (romSmDtPreGame (by decide : 0 < 2) (by decide : 0 < 4) [[]] 1 allSearchRomPreAdv).winProb
        ((⟨0 + 1, 2, by decide⟩ : RatBound).add ⟨0 + 1, 4, by decide⟩) := by
  unfold GameBound RatBound.le
  decide +kernel

/-- `#tooth`: Dropping `Within 0` on `romItsrGame` breaks the `1 / 4` bound — a 2-query grinding
    adversary over `cardSub = 4` wins with probability `7 / 16 > 1 / 4`. -/
def twoQueryRomItsrAdv : Code (roOracleIface (Bytes × Bytes) 4) (Bytes × Bytes) :=
  .call ([1], [1]) (fun s₁ =>
    if s₁.1 = 0 then .ret ([1], [1])
    else .call ([2], [1]) (fun _ => .ret ([2], [1])))

theorem tooth_romItsr_without_within :
    ¬ GameBound
        (romItsrGame (by decide : 0 < 4)
          (fun opened s => opened.any (fun o => decide (s = o)))
          [([0], [0])] [⟨0, by decide⟩] 2 twoQueryRomItsrAdv).winProb
        ⟨(0 + 1) * 1, 4, by decide⟩ := by
  unfold GameBound RatBound.le
  decide +kernel

/-! #### 2i.2 Non-Empty Query-Bounded Classes Inhabiting `SmDtTcrHard`, `SmDtPreHard`, and `ItsrHard` -/

/-- Canonical uniform 1-byte seed sampler (`256` seeds). -/
def byte1SeedSampler (i : Fin 256) : Bytes := [UInt8.ofNat i.1]

theorem uniformOn_byte1Seed : UniformOn (fun s : Bytes => s.length = 1) byte1SeedSampler where
  mem _ := rfl
  injective i j h := by
    injection h with hHd _
    have hNat := congrArg UInt8.toNat hHd
    rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat',
      Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt j.2] at hNat
    exact Fin.ext hNat
  surjective s hs := by
    match s, hs with
    | [b], _ => exact ⟨⟨b.toNat, b.toNat_lt⟩, congrArg (· :: []) UInt8.ofNat_toNat⟩

/-- Canonical uniform 1-byte hidden-input `SM-DT-PRE` sampler (`seedLen = 0, inputLen = 1, q = 1`). -/
def byte1PreSampler (i : Fin 256) : Bytes × List Bytes := ([], [[UInt8.ofNat i.1]])

theorem uniformOn_byte1Pre : UniformOn (SmDtPreSampleOk 0 1 1) byte1PreSampler where
  mem _ := ⟨rfl, rfl, fun h hh => by
    rcases List.mem_cons.mp hh with rfl | hNil
    · rfl
    · nomatch hNil⟩
  injective i j h := by
    injection h with _ h2
    injection h2 with hHead _
    injection hHead with hB _
    have hNat := congrArg UInt8.toNat hB
    rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat',
      Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt j.2] at hNat
    exact Fin.ext hNat
  surjective x hx := by
    obtain ⟨s, hs⟩ := x
    obtain ⟨h1, h2, h3⟩ := hx
    have hsNil : s = [] := List.eq_nil_of_length_eq_zero h1
    match hs, h2, h3 with
    | [h], _, h3 =>
      have hLen1 : h.length = 1 := h3 h (List.Mem.head _)
      match h, hLen1 with
      | [b], _ =>
        refine ⟨⟨b.toNat, b.toNat_lt⟩, ?_⟩
        rw [hsNil]
        exact congrArg (fun u => ([], [[u]])) UInt8.ofNat_toNat

/-- Canonical uniform 1-byte randomizer `ITSR` sampler (`randLen = 1, q = 1`). -/
def byte1ItsrSampler (i : Fin 256) : List Bytes := [[UInt8.ofNat i.1]]

theorem uniformOn_byte1Itsr : UniformOn (ItsrSampleOk 1 1) byte1ItsrSampler where
  mem _ := ⟨rfl, fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hNil
    · rfl
    · nomatch hNil⟩
  injective i j h := by
    injection h with hHead _
    injection hHead with hB _
    have hNat := congrArg UInt8.toNat hB
    rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat',
      Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt j.2] at hNat
    exact Fin.ext hNat
  surjective x hx := by
    obtain ⟨h1, h2⟩ := hx
    match x, h1, h2 with
    | [r], _, h2 =>
      have hrLen : r.length = 1 := h2 r (List.Mem.head _)
      match r, hrLen with
      | [b], _ => exact ⟨⟨b.toNat, b.toNat_lt⟩, congrArg (fun u => [[u]]) UInt8.ofNat_toNat⟩

private theorem firstByteString_mem_cons (p : Bytes → Bool) :
    ∀ (l : List Bytes), firstByteString p l ∈ ([] : Bytes) :: l
  | [] => List.Mem.head _
  | x :: xs => by
    unfold firstByteString
    cases p x
    · rcases List.mem_cons.mp (firstByteString_mem_cons p xs) with hNil | hIn
      · rw [hNil]; exact List.Mem.head _
      · exact List.Mem.tail _ (List.Mem.tail _ hIn)
    · exact List.Mem.tail _ (List.Mem.head _)

private theorem byteList_hit_sum_le :
    ∀ (L : List UInt8),
      sampleSum 256 (fun i => if decide (UInt8.ofNat i.1 ∈ L) then 1 else 0) ≤ L.length
  | [] => by
    have hZ : (fun i : Fin 256 => if decide (UInt8.ofNat i.1 ∈ ([] : List UInt8)) then 1 else 0) = (fun _ => 0) :=
      rfl
    rw [hZ, sampleSum_const, Nat.mul_zero]
    exact Nat.le_refl 0
  | b :: bs => by
    have hSplit : ∀ i : Fin 256,
        (if decide (UInt8.ofNat i.1 ∈ b :: bs) then 1 else 0) ≤
        (if i = ⟨b.toNat, b.toNat_lt⟩ then 1 else 0) +
        (if decide (UInt8.ofNat i.1 ∈ bs) then 1 else 0) := fun i => by
      by_cases hi : UInt8.ofNat i.1 ∈ b :: bs
      · simp only [decide_eq_true hi, ↓reduceIte]
        rcases List.mem_cons.mp hi with hEq | hTl
        · have hiEq : i = ⟨b.toNat, b.toNat_lt⟩ := by
            have hN := congrArg UInt8.toNat hEq
            rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt i.2] at hN
            exact Fin.ext hN
          rw [iteOfPos hiEq]; omega
        · simp only [decide_eq_true hTl, ↓reduceIte]; omega
      · rw [decide_eq_false hi]; exact Nat.zero_le _
    have hSum := sampleSum_le 256 _ _ hSplit
    rw [sampleSum_add_fn] at hSum
    exact Nat.le_trans hSum
      (Nat.le_trans (Nat.add_le_add (sampleSum_indicator_le_one 256 ⟨b.toNat, b.toNat_lt⟩)
          (byteList_hit_sum_le bs))
        (by rw [List.length_cons, Nat.add_comm]; exact Nat.le_refl _))

/-- **Query-bounded `SM-DT-PRE` adversary class (`WithinPreQueries`).** Requires `Within qTarget`
    oracle calls on `targetIface` and restricts offline preimage candidates to a dictionary of
    size at most `qEval`. -/
def WithinPreQueries (qTarget qEval : Nat) (c : Code targetIface TargetBreak) : Prop :=
  Within qTarget c ∧
  ∃ dict : List Bytes, dict.length ≤ qEval ∧
    ∀ (oracle : TargetState → (qr : targetIface.Query) → targetIface.Resp qr × TargetState)
      (st : TargetState),
      (Code.play oracle c st).1.candidate ∈ ([] : Bytes) :: dict

/-- Explicit 2-call `SM-DT-PRE` dictionary-search adversary generalizing `preimageSearchAdv`. -/
def boundedPreAdv (th : Bytes → Bytes → Bytes → Bytes) (tweak : Bytes)
    (dict : List Bytes) : Code targetIface TargetBreak :=
  .call (.target tweak []) (fun y =>
    .call .reveal (fun s =>
      .ret ⟨tweak, [], firstByteString
        (fun m => decide (some (th (s.getD []) tweak m) = y)) dict⟩))

theorem boundedPreAdv_mem_within (th : Bytes → Bytes → Bytes → Bytes) (tweak : Bytes)
    {qEval : Nat} (dict : List Bytes) (hLen : dict.length ≤ qEval) :
    WithinPreQueries 2 qEval (boundedPreAdv th tweak dict) :=
  ⟨.call _ _ (fun _ => .call _ _ (fun _ => .ret 0 _)),
   dict, hLen, fun oracle st => by
     show firstByteString _ dict ∈ ([] : Bytes) :: dict
     exact firstByteString_mem_cons _ dict⟩

/-- Concrete 1-byte XOR tweakable hash `byteXorHash` (bijective on 1-byte hidden inputs). -/
def byteXorHash (seed tweak msg : Bytes) : Bytes :=
  [((seed.headD 0) ^^^ (tweak.headD 0)) ^^^ (msg.headD 0)]

theorem byteXorHash_eq (seed tweak msg : Bytes) :
    byteXorHash seed tweak msg = [((seed.headD 0) ^^^ (tweak.headD 0)) ^^^ (msg.headD 0)] := by unfold byteXorHash; rfl

private theorem uint8_xor_left_inj : ∀ a x y : UInt8, (a ^^^ x) = (a ^^^ y) → x = y :=
  fun a _ _ h => (UInt8.xor_right_inj a).mp h

/-- **Inhabited `SmDtPreHard` Theorem (`(qEval + 1) / 256`).** Against `WithinPreQueries qTarget qEval`,
    `byteXorHash` satisfies `SmDtPreHard` with exact rational bound `(qEval + 1) / 256` (strictly `< 1`
    for every `qEval < 255`, while `boundedPreAdv` is in the class and wins with positive probability). -/
theorem byteXorHash_smDtPreHard_within (qTarget qEval : Nat) :
    SmDtPreHard (WithinPreQueries qTarget qEval) byteXorHash 0 1 1 ⟨qEval + 1, 256, by decide⟩ := by
  intro n nC nA hPos π sample hU adv hA
  unfold GameBound RatBound.le FinGame.winProb FinGame.winCount
  dsimp only
  rw [π.sampleSum_eq]
  conv => rhs; rw [π.card_eq]
  obtain ⟨hnC, _⟩ := hU.card_and_sampleSum_eq uniformOn_byte1Pre (fun _ => 0)
  have hSwap : sampleSum nC (fun c => sampleSum nA (fun a =>
      if (smDtPreGame hPos byteXorHash 1 (fun ω => (sample (π.chal ω)).1)
          (fun ω i => (sample (π.chal ω)).2.getD i []) (fun ω => adv (π.advc ω))).win (π.pair c a)
      then 1 else 0)) =
      sampleSum nA (fun a => sampleSum nC (fun c =>
        if smDtPreWin byteXorHash
            (Code.play (smDtPreOracle byteXorHash 1 (fun i => (sample c).2.getD i []))
              (adv a) ⟨(sample c).1, [], false⟩).2
            (Code.play (smDtPreOracle byteXorHash 1 (fun i => (sample c).2.getD i []))
              (adv a) ⟨(sample c).1, [], false⟩).1
        then 1 else 0)) := by
    have hSimpl : sampleSum nC (fun c => sampleSum nA (fun a =>
        if (smDtPreGame hPos byteXorHash 1 (fun ω => (sample (π.chal ω)).1)
            (fun ω i => (sample (π.chal ω)).2.getD i []) (fun ω => adv (π.advc ω))).win (π.pair c a)
        then 1 else 0)) =
        sampleSum nC (fun c => sampleSum nA (fun a =>
          if smDtPreWin byteXorHash
              (Code.play (smDtPreOracle byteXorHash 1 (fun i => (sample c).2.getD i []))
                (adv a) ⟨(sample c).1, [], false⟩).2
              (Code.play (smDtPreOracle byteXorHash 1 (fun i => (sample c).2.getD i []))
                (adv a) ⟨(sample c).1, [], false⟩).1
          then 1 else 0)) :=
      sampleSum_ext (fun c => sampleSum_ext (fun a => by
        show (if smDtPreWin byteXorHash
            (Code.play (smDtPreOracle byteXorHash 1 (fun i => (sample (π.chal (π.pair c a))).2.getD i []))
              (adv (π.advc (π.pair c a))) ⟨(sample (π.chal (π.pair c a))).1, [], false⟩).2
            (Code.play (smDtPreOracle byteXorHash 1 (fun i => (sample (π.chal (π.pair c a))).2.getD i []))
              (adv (π.advc (π.pair c a))) ⟨(sample (π.chal (π.pair c a))).1, [], false⟩).1
          then 1 else 0) = _
        rw [π.chal_pair, π.advc_pair]))
    rw [hSimpl]
    exact sampleSum_comm _ _ _
  rw [hSwap]
  have hPerA : ∀ a : Fin nA,
      sampleSum nC (fun c =>
        if smDtPreWin byteXorHash
            (Code.play (smDtPreOracle byteXorHash 1 (fun i => (sample c).2.getD i []))
              (adv a) ⟨(sample c).1, [], false⟩).2
            (Code.play (smDtPreOracle byteXorHash 1 (fun i => (sample c).2.getD i []))
              (adv a) ⟨(sample c).1, [], false⟩).1
        then 1 else 0) ≤ qEval + 1 := fun a => by
    obtain ⟨_, dict, hDictLen, hDictMem⟩ := hA a
    obtain ⟨_, hSampleSum⟩ := hU.card_and_sampleSum_eq uniformOn_byte1Pre (fun s =>
      if smDtPreWin byteXorHash
          (Code.play (smDtPreOracle byteXorHash 1 (fun i => s.2.getD i [])) (adv a) ⟨s.1, [], false⟩).2
          (Code.play (smDtPreOracle byteXorHash 1 (fun i => s.2.getD i [])) (adv a) ⟨s.1, [], false⟩).1
      then 1 else 0)
    rw [hSampleSum]
    let bytesL : List UInt8 := (([] : Bytes) :: dict).map (fun m => m.headD 0)
    have hImp : ∀ i : Fin 256,
        (if smDtPreWin byteXorHash
            (Code.play (smDtPreOracle byteXorHash 1 (fun j => (byte1PreSampler i).2.getD j []))
              (adv a) ⟨(byte1PreSampler i).1, [], false⟩).2
            (Code.play (smDtPreOracle byteXorHash 1 (fun j => (byte1PreSampler i).2.getD j []))
              (adv a) ⟨(byte1PreSampler i).1, [], false⟩).1
        then 1 else 0) ≤ (if decide (UInt8.ofNat i.1 ∈ bytesL) then 1 else 0) := fun i => by
      cases hW : smDtPreWin byteXorHash
          (Code.play (smDtPreOracle byteXorHash 1 (fun j => (byte1PreSampler i).2.getD j []))
            (adv a) ⟨(byte1PreSampler i).1, [], false⟩).2
          (Code.play (smDtPreOracle byteXorHash 1 (fun j => (byte1PreSampler i).2.getD j []))
            (adv a) ⟨(byte1PreSampler i).1, [], false⟩).1
      · exact Nat.zero_le _
      · obtain ⟨e, hMemE, hAnd⟩ := List.any_eq_true.mp hW
        obtain ⟨_, hDig⟩ := andTrueSplit hAnd
        have hCol := of_decide_eq_true hDig
        have hSndEq : e.2 = [UInt8.ofNat i.1] := by
          have hAllHidden : ∀ (c : Code targetIface TargetBreak) (st : TargetState),
              (∀ p ∈ st.targets, p.2 = [UInt8.ofNat i.1]) → st.targets.length ≤ 1 →
              ∀ p ∈ (Code.play (smDtPreOracle byteXorHash 1
                (fun j => (byte1PreSampler i).2.getD j [])) c st).2.targets,
                p.2 = [UInt8.ofNat i.1] := by
            intro c
            induction c with
            | ret _ => intro st hP _ p hp; exact hP p hp
            | call qr k ihC =>
              intro st hP hLen p hp
              cases qr with
              | reveal => exact ihC (some st.seed) { st with revealed := true } hP hLen p hp
              | target t m =>
                if hc : st.revealed = false ∧ st.targets.length < 1 ∧ t ∉ st.targets.map Prod.fst then
                  have hStep : smDtPreOracle byteXorHash 1
                      (fun j => (byte1PreSampler i).2.getD j []) st (.target t m) =
                      (some _, { st with targets := st.targets ++
                        [(t, (byte1PreSampler i).2.getD st.targets.length [])] }) :=
                    iteOfPos hc _ _
                  show p.2 = [UInt8.ofNat i.1]
                  rw [Code.play_call, hStep] at hp
                  refine ihC _ _ (fun q hq => ?_) (by rw [List.length_append]; exact hc.2.1) p hp
                  rcases List.mem_append.mp hq with hOld | hNew
                  · exact hP q hOld
                  · rcases List.mem_cons.mp hNew with rfl | hN
                    · have hZ : st.targets.length = 0 := Nat.lt_one_iff.mp hc.2.1
                      rw [hZ]; rfl
                    · nomatch hN
                else
                  have hStep : smDtPreOracle byteXorHash 1
                      (fun j => (byte1PreSampler i).2.getD j []) st (.target t m) = (none, st) :=
                    iteOfNeg hc _ _
                  rw [Code.play_call, hStep] at hp
                  exact ihC _ _ hP hLen p hp
          exact hAllHidden (adv a) ⟨[], [], false⟩ (fun _ h => nomatch h) (Nat.zero_le 1) e hMemE
        rw [hSndEq] at hCol
        injection hCol with hByteEq _
        have hHeadEq := uint8_xor_left_inj _ _ _ hByteEq
        have hCandMem := hDictMem
          (smDtPreOracle byteXorHash 1 (fun j => (byte1PreSampler i).2.getD j [])) ⟨[], [], false⟩
        have hInL : UInt8.ofNat i.1 ∈ bytesL :=
          List.mem_map.mpr ⟨_, hCandMem, hHeadEq⟩
        rw [decide_eq_true hInL]
        exact Nat.le_refl 1
    exact Nat.le_trans (sampleSum_le 256 _ _ hImp)
      (Nat.le_trans (byteList_hit_sum_le bytesL) (by
        dsimp only [bytesL]
        rw [List.length_map, List.length_cons]
        exact Nat.succ_le_succ hDictLen))
  have hSum := sampleSum_le nA _ _ hPerA
  rw [sampleSum_const] at hSum
  conv => rhs; rw [hnC]
  refine Nat.le_trans (Nat.mul_le_mul_right 256 hSum) ?_
  simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  exact Nat.le_refl _

/-- **Query-bounded `ITSR` adversary class (`WithinItsrQueries`).** Requires `Within qSign` signing
    queries and restricts output pairs to a candidate pool of size at most `qEval`. -/
def WithinItsrQueries (qSign qEval : Nat) (c : Code byteOracleIface (Bytes × Bytes)) : Prop :=
  Within qSign c ∧
  ∃ pool : List (Bytes × Bytes), pool.length ≤ qEval ∧
    ∀ (oracle : List (Bytes × Bytes) → (msg : Bytes) → Bytes × List (Bytes × Bytes))
      (st : List (Bytes × Bytes)),
      (Code.play oracle c st).1 ∈ (([], []) : Bytes × Bytes) :: pool

/-- First candidate pair in `pool` satisfying `p`, or `([], [])`. -/
def firstBytePair (p : Bytes × Bytes → Bool) : List (Bytes × Bytes) → Bytes × Bytes
  | [] => ([], [])
  | x :: xs => cond (p x) x (firstBytePair p xs)

private theorem firstBytePair_mem_cons (p : Bytes × Bytes → Bool) :
    ∀ l : List (Bytes × Bytes), firstBytePair p l ∈ (([], []) : Bytes × Bytes) :: l
  | [] => List.Mem.head _
  | x :: xs => by
    unfold firstBytePair
    cases p x
    · rcases List.mem_cons.mp (firstBytePair_mem_cons p xs) with hNil | hIn
      · rw [hNil]; exact List.Mem.head _
      · exact List.Mem.tail _ (List.Mem.tail _ hIn)
    · exact List.Mem.tail _ (List.Mem.head _)

private theorem firstBytePair_spec (p : Bytes × Bytes → Bool) :
    ∀ (l : List (Bytes × Bytes)) (x : Bytes × Bytes),
      x ∈ l → p x = true → p (firstBytePair p l) = true
  | [], _, hx, _ => nomatch hx
  | y :: ys, x, hx, hp => by
    unfold firstBytePair
    cases hy : p y
    · rcases List.mem_cons.mp hx with rfl | hTl
      · rw [hy] at hp; cases hp
      · exact firstBytePair_spec p ys x hTl hp
    · exact hy

/-- Explicit 1-query `ITSR` pool-search adversary. -/
def boundedItsrAdv (hmsg : Bytes → Bytes → List Nat) (queryMsg : Bytes)
    (pool : List (Bytes × Bytes)) : Code byteOracleIface (Bytes × Bytes) :=
  .call queryMsg (fun r₀ =>
    .ret (firstBytePair
      (fun pm => !decide (pm = (r₀, queryMsg)) &&
        (hmsg pm.1 pm.2).all (fun x => decide (x ∈ hmsg r₀ queryMsg)))
      pool))

theorem boundedItsrAdv_mem_within (hmsg : Bytes → Bytes → List Nat) (queryMsg : Bytes)
    {qEval : Nat} (pool : List (Bytes × Bytes)) (hLen : pool.length ≤ qEval) :
    WithinItsrQueries 1 qEval (boundedItsrAdv hmsg queryMsg pool) :=
  ⟨Within.call (E := byteOracleIface) (b := 0) queryMsg _ (fun _ => .ret 0 _), pool, hLen, fun _ _ => firstBytePair_mem_cons _ pool⟩

/-- Concrete 1-leaf 256-domain subset selector `byteIdxHmsg`. -/
def byteIdxHmsg (rand msg : Bytes) : List Nat :=
  [((rand.headD 0) ^^^ (msg.headD 0)).toNat]

theorem byteIdxHmsg_eq (rand msg : Bytes) :
    byteIdxHmsg rand msg = [((rand.headD 0) ^^^ (msg.headD 0)).toNat] := by unfold byteIdxHmsg; rfl

private theorem uint8_xor_solve : ∀ a b c : UInt8, (a ^^^ b) = c → a = (c ^^^ b) := by
  intro a b c h
  rw [← h, UInt8.xor_assoc, UInt8.xor_self, UInt8.xor_zero]

private theorem itsr_fixed_log_once (rand₀ : Bytes) (msg₀ : Bytes) :
    ∀ (c : Code byteOracleIface (Bytes × Bytes)) (st : List (Bytes × Bytes)),
      st = [(rand₀, msg₀)] →
      (Code.play (itsrOracle 1 (fun i => if i = 0 then rand₀ else [])) c st).2 = [(rand₀, msg₀)]
  | .ret _, st, hSt => hSt
  | .call m k, st, hSt => by
    subst hSt
    have hStep : itsrOracle 1 (fun i => if i = 0 then rand₀ else []) [(rand₀, msg₀)] m =
        ([], [(rand₀, msg₀)]) := iteOfNeg (by simp) _ _
    rw [Code.play_call, hStep]
    exact itsr_fixed_log_once rand₀ msg₀ (k []) [(rand₀, msg₀)] rfl

/-- **Inhabited `ItsrHard` Theorem (`(qEval + 1) / 256`).** Against `WithinItsrQueries qSign qEval`,
    `byteIdxHmsg` satisfies `ItsrHard` at `randLen = 1, q = 1` with exact rational bound
    `(qEval + 1) / 256` (strictly `< 1` for every `qEval < 255`). -/
theorem byteIdxHmsg_itsrHard_within (qSign qEval : Nat) :
    ItsrHard (WithinItsrQueries qSign qEval) byteIdxHmsg 1 1 ⟨qEval + 1, 256, by decide⟩ := by
  intro n nC nA hPos π rand hU adv hA
  unfold GameBound RatBound.le FinGame.winProb FinGame.winCount
  dsimp only
  rw [π.sampleSum_eq]
  conv => rhs; rw [π.card_eq]
  obtain ⟨hnC, _⟩ := hU.card_and_sampleSum_eq uniformOn_byte1Itsr (fun _ => 0)
  have hSwap : sampleSum nC (fun c => sampleSum nA (fun a =>
      if (itsrGame hPos byteIdxHmsg 1 (fun ω i => (rand (π.chal ω)).getD i [])
          (fun ω => adv (π.advc ω))).win (π.pair c a)
      then 1 else 0)) =
      sampleSum nA (fun a => sampleSum nC (fun c =>
        if itsrWin byteIdxHmsg
            (Code.play (itsrOracle 1 (fun i => (rand c).getD i [])) (adv a) []).2
            (Code.play (itsrOracle 1 (fun i => (rand c).getD i [])) (adv a) []).1
        then 1 else 0)) := by
    have hS : sampleSum nC (fun c => sampleSum nA (fun a =>
        if (itsrGame hPos byteIdxHmsg 1 (fun ω i => (rand (π.chal ω)).getD i [])
            (fun ω => adv (π.advc ω))).win (π.pair c a)
        then 1 else 0)) =
        sampleSum nC (fun c => sampleSum nA (fun a =>
          if itsrWin byteIdxHmsg
              (Code.play (itsrOracle 1 (fun i => (rand c).getD i [])) (adv a) []).2
              (Code.play (itsrOracle 1 (fun i => (rand c).getD i [])) (adv a) []).1
          then 1 else 0)) :=
      sampleSum_ext (fun c => sampleSum_ext (fun a => by
        show (if itsrWin byteIdxHmsg
            (Code.play (itsrOracle 1 (fun i => (rand (π.chal (π.pair c a))).getD i []))
              (adv (π.advc (π.pair c a))) []).2
            (Code.play (itsrOracle 1 (fun i => (rand (π.chal (π.pair c a))).getD i []))
              (adv (π.advc (π.pair c a))) []).1
          then 1 else 0) = _
        rw [π.chal_pair, π.advc_pair]))
    rw [hS]
    exact sampleSum_comm _ _ _
  rw [hSwap]
  have hPerA : ∀ a : Fin nA,
      sampleSum nC (fun c =>
        if itsrWin byteIdxHmsg
            (Code.play (itsrOracle 1 (fun i => (rand c).getD i [])) (adv a) []).2
            (Code.play (itsrOracle 1 (fun i => (rand c).getD i [])) (adv a) []).1
        then 1 else 0) ≤ qEval + 1 := fun a => by
    obtain ⟨_, pool, hPoolLen, hPoolMem⟩ := hA a
    obtain ⟨_, hSampleSum⟩ := hU.card_and_sampleSum_eq uniformOn_byte1Itsr (fun rList =>
      if itsrWin byteIdxHmsg
          (Code.play (itsrOracle 1 (fun i => rList.getD i [])) (adv a) []).2
          (Code.play (itsrOracle 1 (fun i => rList.getD i [])) (adv a) []).1
      then 1 else 0)
    rw [hSampleSum]
    cases hAdv : adv a with
    | ret out =>
      have hZ : (fun i : Fin 256 =>
          if itsrWin byteIdxHmsg
              (Code.play (itsrOracle 1 (fun j => (byte1ItsrSampler i).getD j [])) (.ret out) []).2
              (Code.play (itsrOracle 1 (fun j => (byte1ItsrSampler i).getD j [])) (.ret out) []).1
          then 1 else 0) = (fun _ => 0) := by
        funext i
        have hF : itsrWin byteIdxHmsg [] out = false := by
          unfold itsrWin byteIdxHmsg
          simp
        rw [Code.play_ret, hF]
        rfl
      rw [hZ, sampleSum_const, Nat.mul_zero]
      exact Nat.zero_le _
    | call msg₀ kNext =>
      let bytesL : List UInt8 := ((([], []) : Bytes × Bytes) :: pool).map
        (fun pm => ((pm.1.headD 0) ^^^ (pm.2.headD 0)) ^^^ (msg₀.headD 0))
      have hImp : ∀ i : Fin 256,
          (if itsrWin byteIdxHmsg
              (Code.play (itsrOracle 1 (fun j => (byte1ItsrSampler i).getD j []))
                (.call msg₀ kNext) []).2
              (Code.play (itsrOracle 1 (fun j => (byte1ItsrSampler i).getD j []))
                (.call msg₀ kNext) []).1
          then 1 else 0) ≤ (if decide (UInt8.ofNat i.1 ∈ bytesL) then 1 else 0) := fun i => by
        cases hW : itsrWin byteIdxHmsg
            (Code.play (itsrOracle 1 (fun j => (byte1ItsrSampler i).getD j []))
              (.call msg₀ kNext) []).2
            (Code.play (itsrOracle 1 (fun j => (byte1ItsrSampler i).getD j []))
              (.call msg₀ kNext) []).1
        · exact Nat.zero_le _
        · have hFunEq : (fun j => (byte1ItsrSampler i).getD j []) =
              (fun j => if j = 0 then [UInt8.ofNat i.1] else []) := by
            funext j; cases j <;> rfl
          have hLog : (Code.play (itsrOracle 1 (fun j => (byte1ItsrSampler i).getD j []))
              (.call msg₀ kNext) []).2 = [([UInt8.ofNat i.1], msg₀)] := by
            rw [hFunEq, Code.play_call]
            have hStep0 : itsrOracle 1 (fun j => if j = 0 then [UInt8.ofNat i.1] else []) [] msg₀ =
                ([UInt8.ofNat i.1], [([UInt8.ofNat i.1], msg₀)]) := rfl
            rw [hStep0]
            exact itsr_fixed_log_once [UInt8.ofNat i.1] msg₀ (kNext [UInt8.ofNat i.1]) _ rfl
          rw [hLog] at hW
          obtain ⟨_, hCov⟩ := andTrueSplit hW
          let out := (Code.play (itsrOracle 1 (fun j => (byte1ItsrSampler i).getD j []))
            (.call msg₀ kNext) []).1
          have hAll := List.all_eq_true.mp hCov
            (((out.1.headD 0) ^^^ (out.2.headD 0)).toNat) (List.Mem.head _)
          obtain ⟨e, he, hxe⟩ := List.any_eq_true.mp hAll
          rcases List.mem_cons.mp he with rfl | hNil
          · have hInIdx := of_decide_eq_true hxe
            rcases List.mem_cons.mp hInIdx with hNatEq | hNil2
            · have hByteEq : (UInt8.ofNat i.1) ^^^ (msg₀.headD 0) =
                  (out.1.headD 0) ^^^ (out.2.headD 0) :=
                UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hNatEq.symm)
              have hSolved := uint8_xor_solve _ _ _ hByteEq
              have hOutMem : out ∈ (([], []) : Bytes × Bytes) :: pool := by
                have hM := hPoolMem (itsrOracle 1 (fun j => (byte1ItsrSampler i).getD j [])) []
                rw [hAdv] at hM
                exact hM
              have hInL : UInt8.ofNat i.1 ∈ bytesL :=
                List.mem_map.mpr ⟨out, hOutMem, hSolved.symm⟩
              rw [decide_eq_true hInL]
              exact Nat.le_refl 1
            · nomatch hNil2
          · nomatch hNil
      exact Nat.le_trans (sampleSum_le 256 _ _ hImp)
        (Nat.le_trans (byteList_hit_sum_le bytesL) (by
          dsimp only [bytesL]
          rw [List.length_map, List.length_cons]
          exact Nat.succ_le_succ hPoolLen))
  have hSum := sampleSum_le nA _ _ hPerA
  rw [sampleSum_const] at hSum
  conv => rhs; rw [hnC]
  refine Nat.le_trans (Nat.mul_le_mul_right 256 hSum) ?_
  simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  exact Nat.le_refl _

/-- `#tooth`: At `qEval = 256`, `boundedItsrAdv` searches all 256 candidate randomizers on fresh
    message `[1]`, winning on every coin and refuting `ItsrHard` for every `ε < 1`. -/
def fullItsrSearchPool : List (Bytes × Bytes) :=
  (List.range 256).map (fun b => ([UInt8.ofNat b], [1]))

theorem byteIdxHmsg_itsrHard_refuted {ε : RatBound} (hε : ε.num < ε.den) :
    ¬ ItsrHard (fun _ => True) byteIdxHmsg 1 1 ε := by
  intro h
  refine FinGame.not_bound_of_forall_win _ (fun ω => ?_) hε
    (h 256 256 1 (by decide) (CoinSplit.challengerOnly 256) byte1ItsrSampler uniformOn_byte1Itsr
      (fun _ => boundedItsrAdv byteIdxHmsg [0] fullItsrSearchPool) (fun _ => trivial))
  let targetB := UInt8.ofNat ω.1 ^^^ (0 : UInt8) ^^^ (1 : UInt8)
  have hInPool : ([targetB], [1]) ∈ fullItsrSearchPool :=
    List.mem_map.mpr ⟨targetB.toNat, List.mem_range.mpr targetB.toNat_lt,
      congrArg (fun u => ([u], [1])) UInt8.ofNat_toNat⟩
  have hPredTrue : (!decide (([targetB], ([1] : Bytes)) = ([UInt8.ofNat ω.1], [0])) &&
      (byteIdxHmsg [targetB] [1]).all
        (fun x => decide (x ∈ byteIdxHmsg [UInt8.ofNat ω.1] [0]))) = true := by
    have hXor : ∀ b : UInt8, ((b ^^^ (0 : UInt8) ^^^ (1 : UInt8)) ^^^ (1 : UInt8)) = (b ^^^ (0 : UInt8)) := by
      intro b
      simp only [UInt8.xor_assoc, UInt8.xor_self, UInt8.xor_zero]
    unfold byteIdxHmsg
    dsimp only [targetB, List.headD]
    rw [hXor]
    simp
  have hFound := firstBytePair_spec
    (fun pm => !decide (pm = ([UInt8.ofNat ω.1], [0])) &&
      (byteIdxHmsg pm.1 pm.2).all (fun x => decide (x ∈ byteIdxHmsg [UInt8.ofNat ω.1] [0])))
    fullItsrSearchPool ([targetB], [1]) hInPool hPredTrue
  obtain ⟨hNeq, hAll⟩ := andTrueSplit hFound
  show itsrWin byteIdxHmsg [([UInt8.ofNat ω.1], [0])]
    (firstBytePair _ fullItsrSearchPool) = true
  change itsrWin byteIdxHmsg [([UInt8.ofNat ω.1], [0])]
    (firstBytePair (fun pm => !decide (pm = ([UInt8.ofNat ω.1], [0])) &&
      (byteIdxHmsg pm.1 pm.2).all (fun x => decide (x ∈ byteIdxHmsg [UInt8.ofNat ω.1] [0]))) fullItsrSearchPool) = true
  unfold itsrWin
  apply (Bool.and_eq_true _ _).mpr
  refine ⟨?_, ?_⟩
  · cases hMem : decide (firstBytePair
      (fun pm => !decide (pm = ([UInt8.ofNat ω.1], [0])) &&
        (byteIdxHmsg pm.1 pm.2).all (fun x => decide (x ∈ byteIdxHmsg [UInt8.ofNat ω.1] [0])))
      fullItsrSearchPool ∈ [([UInt8.ofNat ω.1], ([0] : Bytes))])
    · rfl
    · rcases List.mem_cons.mp (of_decide_eq_true hMem) with hEq | hNil
      · rw [decide_eq_true hEq] at hNeq; cases hNeq
      · nomatch hNil
  · refine List.all_eq_true.mpr (fun x hx => List.any_eq_true.mpr
      ⟨([UInt8.ofNat ω.1], [0]), List.Mem.head _, List.all_eq_true.mp hAll x hx⟩)

/-- **Query-bounded `SM-DT-TCR` adversary class (`WithinTcrQueries`).** Requires `Within qTarget`
    calls on `targetIface` and restricts candidate second preimages to a pool of size `≤ qEval`. -/
def WithinTcrQueries (qTarget qEval : Nat) (c : Code targetIface TargetBreak) : Prop :=
  Within qTarget c ∧
  ∃ cands : List Bytes, cands.length ≤ qEval ∧
    ∀ (oracle : TargetState → (qr : targetIface.Query) → targetIface.Resp qr × TargetState)
      (st : TargetState),
      (Code.play oracle c st).1.candidate ∈ ([] : Bytes) :: cands

/-- Explicit 2-call `SM-DT-TCR` pool-search adversary. -/
def boundedTcrAdv (th : Bytes → Bytes → Bytes → Bytes) (tweak msg : Bytes)
    (cands : List Bytes) : Code targetIface TargetBreak :=
  .call (.target tweak msg) (fun y =>
    .call .reveal (fun s =>
      .ret ⟨tweak, msg, firstByteString
        (fun m' => decide (m' ≠ msg ∧ some (th (s.getD []) tweak m') = y)) cands⟩))

theorem boundedTcrAdv_mem_within (th : Bytes → Bytes → Bytes → Bytes) (tweak msg : Bytes)
    {qEval : Nat} (cands : List Bytes) (hLen : cands.length ≤ qEval) :
    WithinTcrQueries 2 qEval (boundedTcrAdv th tweak msg cands) :=
  ⟨.call _ _ (fun _ => .call _ _ (fun _ => .ret 0 _)),
   cands, hLen, fun _ _ => firstByteString_mem_cons _ cands⟩

/-- Polynomial universal hash modulo prime `257` compressing 2-byte messages (`65,536` inputs)
    into `257` field values with 1-byte seeds (`seedLen = 1`). -/
def poly257Coeff0 : Bytes → Nat
  | [] => 0
  | b :: _ => b.toNat + 1

def poly257Coeff1 : Bytes → Nat
  | _ :: b :: _ => b.toNat + 1
  | _ => 0

def poly257Eval (s : Nat) (m : Bytes) : Nat :=
  (poly257Coeff0 m + s * poly257Coeff1 m) % 257

def poly257Hash (seed tweak msg : Bytes) : Bytes :=
  if msg.length ≤ 2 then
    let v := poly257Eval (seed.headD 0).toNat msg
    0x00 :: UInt8.ofNat (v / 256) :: UInt8.ofNat (v % 256) :: tweak
  else
    0x01 :: msg

theorem poly257Hash_eq (seed tweak msg : Bytes) :
    poly257Hash seed tweak msg =
      if msg.length ≤ 2 then
        let v := poly257Eval (seed.headD 0).toNat msg
        0x00 :: UInt8.ofNat (v / 256) :: UInt8.ofNat (v % 256) :: tweak
      else
        0x01 :: msg := by unfold poly257Hash; rfl

private def inv257 (d : Nat) : Nat :=
  ((List.range 257).find? (fun x => decide ((x * d) % 257 = 1))).getD 0

set_option maxRecDepth 4096 in
private theorem inv257_spec : ∀ d : Fin 257, d.1 ≠ 0 → (inv257 d.1 * d.1) % 257 = 1 := by
  decide

private theorem add_mod_cancel_left257 {c x y : Nat} (h : (c + x) % 257 = (c + y) % 257) :
    x % 257 = y % 257 := by
  have h1 := congrArg (fun z => ((257 - c % 257) + z) % 257) h
  have hL : ((257 - c % 257) + (c + x) % 257) % 257 = x % 257 := by
    rw [Nat.add_mod (257 - c % 257), Nat.mod_mod, ← Nat.add_mod]
    have hcLt : c % 257 < 257 := Nat.mod_lt c (by decide)
    have hSplit : (257 - c % 257) + (c + x) = 257 * (c / 257 + 1) + x := by
      have hDiv := Nat.div_add_mod c 257
      omega
    rw [hSplit, Nat.mul_add_mod_self_left]
  have hR : ((257 - c % 257) + (c + y) % 257) % 257 = y % 257 := by
    rw [Nat.add_mod (257 - c % 257), Nat.mod_mod, ← Nat.add_mod]
    have hcLt : c % 257 < 257 := Nat.mod_lt c (by decide)
    have hSplit : (257 - c % 257) + (c + y) = 257 * (c / 257 + 1) + y := by
      have hDiv := Nat.div_add_mod c 257
      omega
    rw [hSplit, Nat.mul_add_mod_self_left]
  exact hL.symm.trans (h1.trans hR)

private theorem poly257_coeffs_inj :
    ∀ {m m' : Bytes}, m.length ≤ 2 → m'.length ≤ 2 →
      poly257Coeff0 m = poly257Coeff0 m' → poly257Coeff1 m = poly257Coeff1 m' → m = m'
  | [], [], _, _, _, _ => rfl
  | [], b :: _, _, _, h0, _ => by dsimp only [poly257Coeff0] at h0; omega
  | b :: _, [], _, _, h0, _ => by dsimp only [poly257Coeff0] at h0; omega
  | [b], [b'], _, _, h0, _ => by
    dsimp only [poly257Coeff0] at h0
    have hb : b.toNat = b'.toNat := by omega
    exact congrArg (· :: []) (UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hb))
  | [_], _ :: c' :: _, _, _, _, h1 => by dsimp only [poly257Coeff1] at h1; omega
  | _ :: c :: _, [_], _, _, _, h1 => by dsimp only [poly257Coeff1] at h1; omega
  | [b₀, b₁], [b₀', b₁'], _, _, h0, h1 => by
    dsimp only [poly257Coeff0, poly257Coeff1] at h0 h1
    have hbn0 : b₀.toNat = b₀'.toNat := by omega
    have hb0 : b₀ = b₀' := UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hbn0)
    have hbn1 : b₁.toNat = b₁'.toNat := by omega
    have hb1 : b₁ = b₁' := UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq hbn1)
    rw [hb0, hb1]
  | _ :: _ :: _ :: _, _, hL, _, _, _ => by simp at hL
  | _, _ :: _ :: _ :: _, _, hL', _, _ => by simp at hL'

private theorem poly257Hash_unique_seed (t m m' : Bytes) (hNe : m' ≠ m)
    (s₁ s₂ : Fin 256)
    (h₁ : poly257Hash [UInt8.ofNat s₁.1] t m' = poly257Hash [UInt8.ofNat s₁.1] t m)
    (h₂ : poly257Hash [UInt8.ofNat s₂.1] t m' = poly257Hash [UInt8.ofNat s₂.1] t m) :
    s₁ = s₂ := by
  unfold poly257Hash at h₁ h₂
  by_cases hm : m.length ≤ 2
  · by_cases hm' : m'.length ≤ 2
    · rw [iteOfPos hm', iteOfPos hm] at h₁ h₂
      have decodeEq : ∀ {u w : Nat}, u < 257 → w < 257 →
          (0x00 :: UInt8.ofNat (u / 256) :: UInt8.ofNat (u % 256) :: t) =
          (0x00 :: UInt8.ofNat (w / 256) :: UInt8.ofNat (w % 256) :: t) → u = w := by
        intro u w hu hw hEq
        injection hEq with _ hTl1
        injection hTl1 with hHi hTl2
        injection hTl2 with hLo _
        have hHiN := congrArg UInt8.toNat hHi
        have hLoN := congrArg UInt8.toNat hLo
        rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat',
          Nat.mod_eq_of_lt (by omega : u / 256 < 256),
          Nat.mod_eq_of_lt (by omega : w / 256 < 256)] at hHiN
        rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat',
          Nat.mod_eq_of_lt (Nat.mod_lt u (by decide)),
          Nat.mod_eq_of_lt (Nat.mod_lt w (by decide))] at hLoN
        have huDiv := Nat.div_add_mod u 256
        have hwDiv := Nat.div_add_mod w 256
        omega
      have hs1Nat : (([UInt8.ofNat s₁.1] : Bytes).headD 0).toNat = s₁.1 := by
        dsimp only [List.headD]; rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt s₁.2]
      have hs2Nat : (([UInt8.ofNat s₂.1] : Bytes).headD 0).toNat = s₂.1 := by
        dsimp only [List.headD]; rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt s₂.2]
      rw [hs1Nat] at h₁
      rw [hs2Nat] at h₂
      have he1 := decodeEq (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) h₁
      have he2 := decodeEq (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) h₂
      unfold poly257Eval at he1 he2
      let a₀ := poly257Coeff0 m
      let a₁ := poly257Coeff1 m
      let b₀ := poly257Coeff0 m'
      let b₁ := poly257Coeff1 m'
      have ha₀ : a₀ < 257 := by
        dsimp only [a₀]; cases m with | nil => exact Nat.zero_lt_succ _ | cons b _ => change b.toNat + 1 < 257; have := b.toNat_lt; omega
      have hb₀ : b₀ < 257 := by
        dsimp only [b₀]; cases m' with | nil => exact Nat.zero_lt_succ _ | cons b _ => change b.toNat + 1 < 257; have := b.toNat_lt; omega
      have ha₁ : a₁ < 257 := by
        dsimp only [a₁]
        match m with | _ :: b :: _ => change b.toNat + 1 < 257; have := b.toNat_lt; omega | [] => exact Nat.zero_lt_succ _ | [_] => exact Nat.zero_lt_succ _
      have hb₁ : b₁ < 257 := by
        dsimp only [b₁]
        match m' with | _ :: b :: _ => change b.toNat + 1 < 257; have := b.toNat_lt; omega | [] => exact Nat.zero_lt_succ _ | [_] => exact Nat.zero_lt_succ _
      have hCross : ((b₀ + s₁.1 * b₁) + (a₀ + s₂.1 * a₁)) % 257 =
          ((a₀ + s₁.1 * a₁) + (b₀ + s₂.1 * b₁)) % 257 := by
        rw [Nat.add_mod, Nat.add_mod (a₀ + s₁.1 * a₁)]
        dsimp only [a₀, a₁, b₀, b₁]
        rw [he1, he2]
      by_cases hEq1 : a₁ = b₁
      · have hMod0 : b₀ % 257 = a₀ % 257 := by
          have hC : (s₁.1 * a₁ + b₀) % 257 = (s₁.1 * a₁ + a₀) % 257 := by
            have hh := he1
            change (b₀ + s₁.1 * b₁) % 257 = (a₀ + s₁.1 * a₁) % 257 at hh
            rw [← hEq1] at hh
            simpa only [Nat.add_comm] using hh
          exact add_mod_cancel_left257 hC
        rw [Nat.mod_eq_of_lt hb₀, Nat.mod_eq_of_lt ha₀] at hMod0
        exact False.elim (hNe (poly257_coeffs_inj hm' hm hMod0 hEq1.symm))
      · have cancelMul : ∀ {k d : Nat}, k < 257 → 0 < d → d < 257 → (k * d) % 257 = 0 → k = 0 := by
          intro k d hk hdPos hdLt hZero
          have hInv := inv257_spec ⟨d, hdLt⟩ (Nat.ne_of_gt hdPos)
          have hCalc : k % 257 = 0 := by
            calc k % 257
              _ = (k * 1) % 257 := by rw [Nat.mul_one]
              _ = (k * ((inv257 d * d) % 257)) % 257 := by rw [hInv]
              _ = (k * (inv257 d * d)) % 257 := by simp only [Nat.mul_mod, Nat.mod_mod]
              _ = (inv257 d * (k * d)) % 257 := by
                exact congrArg (· % 257) (by simp only [Nat.mul_assoc, Nat.mul_comm])
              _ = (inv257 d * ((k * d) % 257)) % 257 := by simp only [Nat.mul_mod, Nat.mod_mod]
              _ = 0 := by rw [hZero, Nat.mul_zero, Nat.zero_mod]
          rwa [Nat.mod_eq_of_lt hk] at hCalc
        by_cases hsLe : s₁.1 ≤ s₂.1
        · by_cases hab : a₁ < b₁
          · let d := b₁ - a₁
            let k := s₂.1 - s₁.1
            have hRearr : (a₀ + b₀ + (s₁.1 + s₂.1) * a₁ + s₁.1 * d + 0) % 257 =
                (a₀ + b₀ + (s₁.1 + s₂.1) * a₁ + s₁.1 * d + k * d) % 257 := by
              have hL : (b₀ + s₁.1 * b₁) + (a₀ + s₂.1 * a₁) =
                  a₀ + b₀ + (s₁.1 + s₂.1) * a₁ + s₁.1 * d + 0 := by
                have hb1Eq : b₁ = a₁ + d := by omega
                rw [hb1Eq, Nat.mul_add, Nat.add_mul]; omega
              have hR : (a₀ + s₁.1 * a₁) + (b₀ + s₂.1 * b₁) =
                  a₀ + b₀ + (s₁.1 + s₂.1) * a₁ + s₁.1 * d + k * d := by
                have hb1Eq : b₁ = a₁ + d := by omega
                have hs2Eq : s₂.1 = s₁.1 + k := by omega
                rw [hb1Eq, hs2Eq]
                simp only [Nat.mul_add, Nat.add_mul]
                omega
              rw [← hL, ← hR]; exact hCross
            have hkd0 := (add_mod_cancel_left257 hRearr).symm
            have hk0 := cancelMul (by omega) (by omega) (by omega) hkd0
            exact Fin.ext (by omega)
          · have hba : b₁ < a₁ := by omega
            let d := a₁ - b₁
            let k := s₂.1 - s₁.1
            have hRearr : (a₀ + b₀ + (s₁.1 + s₂.1) * b₁ + s₁.1 * d + k * d) % 257 =
                (a₀ + b₀ + (s₁.1 + s₂.1) * b₁ + s₁.1 * d + 0) % 257 := by
              have hL : (b₀ + s₁.1 * b₁) + (a₀ + s₂.1 * a₁) =
                  a₀ + b₀ + (s₁.1 + s₂.1) * b₁ + s₁.1 * d + k * d := by
                have ha1Eq : a₁ = b₁ + d := by omega
                have hs2Eq : s₂.1 = s₁.1 + k := by omega
                rw [ha1Eq, hs2Eq]
                simp only [Nat.mul_add, Nat.add_mul]
                omega
              have hR : (a₀ + s₁.1 * a₁) + (b₀ + s₂.1 * b₁) =
                  a₀ + b₀ + (s₁.1 + s₂.1) * b₁ + s₁.1 * d + 0 := by
                have ha1Eq : a₁ = b₁ + d := by omega
                rw [ha1Eq, Nat.mul_add, Nat.add_mul]; omega
              rw [← hL, ← hR]; exact hCross
            have hkd0 := add_mod_cancel_left257 hRearr
            have hk0 := cancelMul (by omega) (by omega) (by omega) hkd0
            exact Fin.ext (by omega)
        · have hs2Le : s₂.1 ≤ s₁.1 := by omega
          by_cases hab : a₁ < b₁
          · let d := b₁ - a₁
            let k := s₁.1 - s₂.1
            have hRearr : (a₀ + b₀ + (s₁.1 + s₂.1) * a₁ + s₂.1 * d + k * d) % 257 =
                (a₀ + b₀ + (s₁.1 + s₂.1) * a₁ + s₂.1 * d + 0) % 257 := by
              have hL : (b₀ + s₁.1 * b₁) + (a₀ + s₂.1 * a₁) =
                  a₀ + b₀ + (s₁.1 + s₂.1) * a₁ + s₂.1 * d + k * d := by
                have hb1Eq : b₁ = a₁ + d := by omega
                have hs1Eq : s₁.1 = s₂.1 + k := by omega
                rw [hb1Eq, hs1Eq]
                simp only [Nat.mul_add, Nat.add_mul]
                omega
              have hR : (a₀ + s₁.1 * a₁) + (b₀ + s₂.1 * b₁) =
                  a₀ + b₀ + (s₁.1 + s₂.1) * a₁ + s₂.1 * d + 0 := by
                have hb1Eq : b₁ = a₁ + d := by omega
                rw [hb1Eq, Nat.mul_add, Nat.add_mul]; omega
              rw [← hL, ← hR]; exact hCross
            have hkd0 := add_mod_cancel_left257 hRearr
            have hk0 := cancelMul (by omega) (by omega) (by omega) hkd0
            exact Fin.ext (by omega)
          · have hba : b₁ < a₁ := by omega
            let d := a₁ - b₁
            let k := s₁.1 - s₂.1
            have hRearr : (a₀ + b₀ + (s₁.1 + s₂.1) * b₁ + s₂.1 * d + 0) % 257 =
                (a₀ + b₀ + (s₁.1 + s₂.1) * b₁ + s₂.1 * d + k * d) % 257 := by
              have hL : (b₀ + s₁.1 * b₁) + (a₀ + s₂.1 * a₁) =
                  a₀ + b₀ + (s₁.1 + s₂.1) * b₁ + s₂.1 * d + 0 := by
                have ha1Eq : a₁ = b₁ + d := by omega
                rw [ha1Eq, Nat.mul_add, Nat.add_mul]; omega
              have hR : (a₀ + s₁.1 * a₁) + (b₀ + s₂.1 * b₁) =
                  a₀ + b₀ + (s₁.1 + s₂.1) * b₁ + s₂.1 * d + k * d := by
                have ha1Eq : a₁ = b₁ + d := by omega
                have hs1Eq : s₁.1 = s₂.1 + k := by omega
                rw [ha1Eq, hs1Eq]
                simp only [Nat.mul_add, Nat.add_mul]
                omega
              rw [← hL, ← hR]; exact hCross
            have hkd0 := (add_mod_cancel_left257 hRearr).symm
            have hk0 := cancelMul (by omega) (by omega) (by omega) hkd0
            exact Fin.ext (by omega)
    · rw [iteOfNeg hm', iteOfPos hm] at h₁
      cases h₁
  · by_cases hm' : m'.length ≤ 2
    · rw [iteOfPos hm', iteOfNeg hm] at h₁
      cases h₁
    · rw [iteOfNeg hm', iteOfNeg hm] at h₁
      injection h₁ with _ hEqM
      exact False.elim (hNe hEqM)

private theorem poly257_candList_hit_le (t m : Bytes) :
    ∀ (cands : List Bytes),
      sampleSum 256 (fun s =>
        if cands.any (fun m' => decide (m' ≠ m ∧
            poly257Hash [UInt8.ofNat s.1] t m' = poly257Hash [UInt8.ofNat s.1] t m))
        then 1 else 0) ≤ cands.length
  | [] => by
    simp only [List.any_nil, Bool.false_eq_true, ↓reduceIte, sampleSum_const,
      Nat.mul_zero, List.length_nil, Nat.le_refl]
  | m' :: ms => by
    have hSplit : ∀ s : Fin 256,
        (if (m' :: ms).any (fun x => decide (x ≠ m ∧
            poly257Hash [UInt8.ofNat s.1] t x = poly257Hash [UInt8.ofNat s.1] t m))
         then 1 else 0) ≤
        (if decide (m' ≠ m ∧
            poly257Hash [UInt8.ofNat s.1] t m' = poly257Hash [UInt8.ofNat s.1] t m)
         then 1 else 0) +
        (if ms.any (fun x => decide (x ≠ m ∧
            poly257Hash [UInt8.ofNat s.1] t x = poly257Hash [UInt8.ofNat s.1] t m))
         then 1 else 0) := fun s => by
      rw [List.any_cons]
      cases decide (m' ≠ m ∧ poly257Hash [UInt8.ofNat s.1] t m' = poly257Hash [UInt8.ofNat s.1] t m) <;>
        cases ms.any (fun x => decide (x ≠ m ∧
          poly257Hash [UInt8.ofNat s.1] t x = poly257Hash [UInt8.ofNat s.1] t m)) <;>
        decide
    have hHead : sampleSum 256 (fun s =>
        if decide (m' ≠ m ∧
            poly257Hash [UInt8.ofNat s.1] t m' = poly257Hash [UInt8.ofNat s.1] t m)
        then 1 else 0) ≤ 1 :=
      sampleSum_bool_le_one_of_subsingleton _ (fun s₁ s₂ h₁ h₂ => by
        obtain ⟨hNe, he₁⟩ := of_decide_eq_true h₁
        obtain ⟨_, he₂⟩ := of_decide_eq_true h₂
        exact poly257Hash_unique_seed t m m' hNe s₁ s₂ he₁ he₂)
    have hSum := sampleSum_le 256 _ _ hSplit
    rw [sampleSum_add_fn] at hSum
    exact Nat.le_trans hSum
      (Nat.le_trans (Nat.add_le_add hHead (poly257_candList_hit_le t m ms))
        (by rw [List.length_cons, Nat.add_comm]; exact Nat.le_refl _))

private theorem tcr_targets_after_revealed (th : Bytes → Bytes → Bytes → Bytes) :
    ∀ (c : Code targetIface TargetBreak) (st : TargetState),
      st.revealed = true →
      (Code.play (smDtTcrOracle th 1) c st).2.targets = st.targets
  | .ret _, _, _ => rfl
  | .call .reveal k, st, _ => tcr_targets_after_revealed th (k (some st.seed)) { st with revealed := true } rfl
  | .call (.target t m) k, st, hRev => by
    have hStep : smDtTcrOracle th 1 st (.target t m) = (none, st) :=
      iteOfNeg (fun h => by rw [hRev] at h; exact Bool.noConfusion h.1) _ _
    rw [Code.play_call, hStep]
    exact tcr_targets_after_revealed th (k none) st hRev

private theorem tcr_targets_after_one (th : Bytes → Bytes → Bytes → Bytes) (t₀ m₀ : Bytes) :
    ∀ (c : Code targetIface TargetBreak) (st : TargetState),
      st.targets = [(t₀, m₀)] →
      (Code.play (smDtTcrOracle th 1) c st).2.targets = [(t₀, m₀)]
  | .ret _, st, hT => hT
  | .call .reveal k, st, hT => tcr_targets_after_one th t₀ m₀ (k (some st.seed)) { st with revealed := true } hT
  | .call (.target t m) k, st, hT => by
    have hStep : smDtTcrOracle th 1 st (.target t m) = (none, st) :=
      iteOfNeg (fun h => by rw [hT] at h; exact Nat.lt_irrefl 1 h.2.1) _ _
    rw [Code.play_call, hStep]
    exact tcr_targets_after_one th t₀ m₀ (k none) st hT

/-- **Inhabited `SmDtTcrHard` Theorem (`(qEval + 1) / 256`).** Against `WithinTcrQueries qTarget qEval`,
    the compressing polynomial universal hash `poly257Hash` satisfies `SmDtTcrHard` at
    `seedLen = 1, q = 1` with exact rational bound `(qEval + 1) / 256` (strictly `< 1` for every
    `qEval < 255`). -/
theorem poly257Hash_smDtTcrHard_within (qTarget qEval : Nat) :
    SmDtTcrHard (WithinTcrQueries qTarget qEval) poly257Hash 1 1 ⟨qEval + 1, 256, by decide⟩ := by
  intro n nC nA hPos π seed hU adv hA
  unfold GameBound RatBound.le FinGame.winProb FinGame.winCount
  dsimp only
  rw [π.sampleSum_eq]
  conv => rhs; rw [π.card_eq]
  obtain ⟨hnC, _⟩ := hU.card_and_sampleSum_eq uniformOn_byte1Seed (fun _ => 0)
  have hSwap : sampleSum nC (fun c => sampleSum nA (fun a =>
      if (smDtTcrGame hPos poly257Hash 1 (fun ω => seed (π.chal ω))
          (fun ω => adv (π.advc ω))).win (π.pair c a)
      then 1 else 0)) =
      sampleSum nA (fun a => sampleSum nC (fun c =>
        if smDtTcrWin poly257Hash
            (Code.play (smDtTcrOracle poly257Hash 1) (adv a) ⟨seed c, [], false⟩).2
            (Code.play (smDtTcrOracle poly257Hash 1) (adv a) ⟨seed c, [], false⟩).1
        then 1 else 0)) := by
    have hS : sampleSum nC (fun c => sampleSum nA (fun a =>
        if (smDtTcrGame hPos poly257Hash 1 (fun ω => seed (π.chal ω))
            (fun ω => adv (π.advc ω))).win (π.pair c a)
        then 1 else 0)) =
        sampleSum nC (fun c => sampleSum nA (fun a =>
          if smDtTcrWin poly257Hash
              (Code.play (smDtTcrOracle poly257Hash 1) (adv a) ⟨seed c, [], false⟩).2
              (Code.play (smDtTcrOracle poly257Hash 1) (adv a) ⟨seed c, [], false⟩).1
          then 1 else 0)) :=
      sampleSum_ext (fun c => sampleSum_ext (fun a => by
        show (if smDtTcrWin poly257Hash
            (Code.play (smDtTcrOracle poly257Hash 1) (adv (π.advc (π.pair c a)))
              ⟨seed (π.chal (π.pair c a)), [], false⟩).2
            (Code.play (smDtTcrOracle poly257Hash 1) (adv (π.advc (π.pair c a)))
              ⟨seed (π.chal (π.pair c a)), [], false⟩).1
          then 1 else 0) = _
        rw [π.chal_pair, π.advc_pair]))
    rw [hS]
    exact sampleSum_comm _ _ _
  rw [hSwap]
  have hPerA : ∀ a : Fin nA,
      sampleSum nC (fun c =>
        if smDtTcrWin poly257Hash
            (Code.play (smDtTcrOracle poly257Hash 1) (adv a) ⟨seed c, [], false⟩).2
            (Code.play (smDtTcrOracle poly257Hash 1) (adv a) ⟨seed c, [], false⟩).1
        then 1 else 0) ≤ qEval + 1 := fun a => by
    obtain ⟨_, cands, hCandsLen, hCandsMem⟩ := hA a
    obtain ⟨_, hSampleSum⟩ := hU.card_and_sampleSum_eq uniformOn_byte1Seed (fun s =>
      if smDtTcrWin poly257Hash
          (Code.play (smDtTcrOracle poly257Hash 1) (adv a) ⟨s, [], false⟩).2
          (Code.play (smDtTcrOracle poly257Hash 1) (adv a) ⟨s, [], false⟩).1
      then 1 else 0)
    rw [hSampleSum]
    cases hAdv : adv a with
    | ret out =>
      have hZ : (fun i : Fin 256 =>
          if smDtTcrWin poly257Hash
              (Code.play (smDtTcrOracle poly257Hash 1) (.ret out) ⟨byte1SeedSampler i, [], false⟩).2
              (Code.play (smDtTcrOracle poly257Hash 1) (.ret out) ⟨byte1SeedSampler i, [], false⟩).1
          then 1 else 0) = (fun _ => 0) := by
        funext i; rfl
      rw [hZ, sampleSum_const, Nat.mul_zero]
      exact Nat.zero_le _
    | call qr kNext =>
      cases qr with
      | reveal =>
        have hZ : (fun i : Fin 256 =>
            if smDtTcrWin poly257Hash
                (Code.play (smDtTcrOracle poly257Hash 1) (.call .reveal kNext)
                  ⟨byte1SeedSampler i, [], false⟩).2
                (Code.play (smDtTcrOracle poly257Hash 1) (.call .reveal kNext)
                  ⟨byte1SeedSampler i, [], false⟩).1
            then 1 else 0) = (fun _ => 0) := by
          funext i
          have hEmpty : (Code.play (smDtTcrOracle poly257Hash 1) (.call .reveal kNext)
              ⟨byte1SeedSampler i, [], false⟩).2.targets = [] :=
            tcr_targets_after_revealed poly257Hash (kNext (some (byte1SeedSampler i)))
              ⟨byte1SeedSampler i, [], true⟩ rfl
          cases hW : smDtTcrWin poly257Hash
              (Code.play (smDtTcrOracle poly257Hash 1) (.call .reveal kNext)
                ⟨byte1SeedSampler i, [], false⟩).2
              (Code.play (smDtTcrOracle poly257Hash 1) (.call .reveal kNext)
                ⟨byte1SeedSampler i, [], false⟩).1
          · rfl
          · obtain ⟨hMem, _⟩ := andTrueSplit hW
            rw [hEmpty] at hMem
            nomatch (of_decide_eq_true hMem)
        rw [hZ, sampleSum_const, Nat.mul_zero]
        exact Nat.zero_le _
      | target t₀ m₀ =>
        have hImp : ∀ i : Fin 256,
            (if smDtTcrWin poly257Hash
                (Code.play (smDtTcrOracle poly257Hash 1) (.call (.target t₀ m₀) kNext)
                  ⟨byte1SeedSampler i, [], false⟩).2
                (Code.play (smDtTcrOracle poly257Hash 1) (.call (.target t₀ m₀) kNext)
                  ⟨byte1SeedSampler i, [], false⟩).1
            then 1 else 0) ≤
            (if (([] : Bytes) :: cands).any (fun m' => decide (m' ≠ m₀ ∧
                poly257Hash [UInt8.ofNat i.1] t₀ m' = poly257Hash [UInt8.ofNat i.1] t₀ m₀))
             then 1 else 0) := fun i => by
          cases hW : smDtTcrWin poly257Hash
              (Code.play (smDtTcrOracle poly257Hash 1) (.call (.target t₀ m₀) kNext)
                ⟨byte1SeedSampler i, [], false⟩).2
              (Code.play (smDtTcrOracle poly257Hash 1) (.call (.target t₀ m₀) kNext)
                ⟨byte1SeedSampler i, [], false⟩).1
          · exact Nat.zero_le _
          · have hStep0 : smDtTcrOracle poly257Hash 1 ⟨byte1SeedSampler i, [], false⟩ (.target t₀ m₀) =
                (some (poly257Hash (byte1SeedSampler i) t₀ m₀),
                  ⟨byte1SeedSampler i, [(t₀, m₀)], false⟩) := rfl
            have hTgt : (Code.play (smDtTcrOracle poly257Hash 1) (.call (.target t₀ m₀) kNext)
                ⟨byte1SeedSampler i, [], false⟩).2.targets = [(t₀, m₀)] := by
              rw [Code.play_call, hStep0]
              exact tcr_targets_after_one poly257Hash t₀ m₀ _ _ rfl
            have hSeedInv := (smDtTcrRun_inv poly257Hash 1 (fun _ : Fin 1 => byte1SeedSampler i)
              (fun _ => .call (.target t₀ m₀) kNext) ⟨0, Nat.one_pos⟩).1
            obtain ⟨hMem, hRest⟩ := andTrueSplit hW
            obtain ⟨hNe, hCol⟩ := andTrueSplit hRest
            rw [hTgt] at hMem
            rcases List.mem_cons.mp (of_decide_eq_true hMem) with hPairEq | hNil
            · injection hPairEq with hTwEq hMsgEq
              have hCandMem : (Code.play (smDtTcrOracle poly257Hash 1) (.call (.target t₀ m₀) kNext)
                  ⟨byte1SeedSampler i, [], false⟩).1.candidate ∈ ([] : Bytes) :: cands := by
                have hM := hCandsMem (smDtTcrOracle poly257Hash 1) ⟨byte1SeedSampler i, [], false⟩
                rw [hAdv] at hM
                exact hM
              have hColProp := of_decide_eq_true hCol
              have hNeProp := of_decide_eq_true hNe
              rw [hTwEq, hMsgEq] at hColProp
              rw [hMsgEq] at hNeProp
              have hSeedEq : (Code.play (smDtTcrOracle poly257Hash 1) (.call (.target t₀ m₀) kNext)
                  ⟨byte1SeedSampler i, [], false⟩).2.seed = [UInt8.ofNat i.1] := hSeedInv
              rw [hSeedEq] at hColProp
              have hAny : (([] : Bytes) :: cands).any (fun m' => decide (m' ≠ m₀ ∧
                  poly257Hash [UInt8.ofNat i.1] t₀ m' = poly257Hash [UInt8.ofNat i.1] t₀ m₀)) = true :=
                List.any_eq_true.mpr ⟨_, hCandMem, decide_eq_true ⟨hNeProp, hColProp⟩⟩
              rw [hAny]
              exact Nat.le_refl 1
            · nomatch hNil
        exact Nat.le_trans (sampleSum_le 256 _ _ hImp)
          (Nat.le_trans (poly257_candList_hit_le t₀ m₀ (([] : Bytes) :: cands))
            (by rw [List.length_cons]; exact Nat.succ_le_succ hCandsLen))
  have hSum := sampleSum_le nA _ _ hPerA
  rw [sampleSum_const] at hSum
  conv => rhs; rw [hnC]
  refine Nat.le_trans (Nat.mul_le_mul_right 256 hSum) ?_
  simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  exact Nat.le_refl _

/-- `#tooth`: Post-reveal unrestricted computation refutes `SmDtTcrHard (fun _ => True) poly257Hash`
    for every `ε < 1`, even though the adversary makes only 2 `targetIface` calls (`Within 2`). -/
def poly257PostRevealBreakAdv : Code targetIface TargetBreak :=
  .call (.target [] [0, 0]) (fun _ =>
    .call .reveal (fun sOpt =>
      let s := ((sOpt.getD []).headD 0).toNat
      let cand : Bytes :=
        if s = 0 then [0, 1]
        else if s = 1 then [1]
        else [UInt8.ofNat (257 - s), 1]
      .ret ⟨[], [0, 0], cand⟩))

set_option maxRecDepth 4096 in
private theorem poly257PostRevealBreak_collides :
    ∀ i : Fin 256,
      let s := i.1
      let cand : Bytes :=
        if s = 0 then [0, 1]
        else if s = 1 then [1]
        else [UInt8.ofNat (257 - s), 1]
      cand ≠ [0, 0] ∧
        poly257Hash [UInt8.ofNat i.1] [] cand = poly257Hash [UInt8.ofNat i.1] [] [0, 0] := by
  decide

theorem poly257Hash_smDtTcrHard_refuted {ε : RatBound} (hε : ε.num < ε.den) :
    ¬ SmDtTcrHard (fun _ => True) poly257Hash 1 1 ε := by
  intro h
  refine FinGame.not_bound_of_forall_win _ (fun ω => ?_) hε
    (h 256 256 1 (by decide) (CoinSplit.challengerOnly 256) byte1SeedSampler uniformOn_byte1Seed
      (fun _ => poly257PostRevealBreakAdv) (fun _ => trivial))
  have hCol := poly257PostRevealBreak_collides ω
  have hsNat : (([UInt8.ofNat ω.1] : Bytes).headD 0).toNat = ω.1 := by
    dsimp only [List.headD]; rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt ω.2]
  show smDtTcrWin poly257Hash ⟨[UInt8.ofNat ω.1], [([], [0, 0])], true⟩
    ⟨[], [0, 0],
      if (([UInt8.ofNat ω.1] : Bytes).headD 0).toNat = 0 then [0, 1]
      else if (([UInt8.ofNat ω.1] : Bytes).headD 0).toNat = 1 then [1]
      else [UInt8.ofNat (257 - (([UInt8.ofNat ω.1] : Bytes).headD 0).toNat), 1]⟩ = true
  rw [hsNat]
  unfold smDtTcrWin
  simp only [decide_eq_true (show ([], [0, 0]) ∈ [(([] : Bytes), ([0, 0] : Bytes))] from List.Mem.head _), decide_eq_true hCol.1, decide_eq_true hCol.2, Bool.true_and]

private theorem pre_targets_after_revealed (th : Bytes → Bytes → Bytes → Bytes)
    (hid : Nat → Bytes) : ∀ (c : Code targetIface TargetBreak) (st : TargetState),
      st.revealed = true → (Code.play (smDtPreOracle th 1 hid) c st).2.targets = st.targets
  | .ret _, _, _ => rfl
  | .call .reveal k, st, _ => pre_targets_after_revealed th hid (k (some st.seed)) { st with revealed := true } rfl
  | .call (.target t m) k, st, hRev => by
    have hStep : smDtPreOracle th 1 hid st (.target t m) = (none, st) :=
      iteOfNeg (fun h => by rw [hRev] at h; exact Bool.noConfusion h.1) _ _
    rw [Code.play_call, hStep]
    exact pre_targets_after_revealed th hid (k none) st hRev

private theorem pre_targets_after_one (th : Bytes → Bytes → Bytes → Bytes)
    (hid : Nat → Bytes) (t₀ : Bytes) : ∀ (c : Code targetIface TargetBreak) (st : TargetState),
      st.targets = [(t₀, hid 0)] →
      (Code.play (smDtPreOracle th 1 hid) c st).2.targets = [(t₀, hid 0)]
  | .ret _, _, hT => hT
  | .call .reveal k, st, hT => pre_targets_after_one th hid t₀ (k (some st.seed)) { st with revealed := true } hT
  | .call (.target t m) k, st, hT => by
    have hStep : smDtPreOracle th 1 hid st (.target t m) = (none, st) :=
      iteOfNeg (fun h => by rw [hT] at h; exact Nat.lt_irrefl 1 h.2.1) _ _
    rw [Code.play_call, hStep]
    exact pre_targets_after_one th hid t₀ (k none) st hT

/-- Canonical uniform sampler on `SmDtPreSampleOk 1 1 1` (`256 * 256` `(seed, [hidden])` pairs). -/
def byte1SeedAndPreSampler (z : Fin (256 * 256)) : Bytes × List Bytes :=
  let p := CoinSplit.prod 256 256
  ([UInt8.ofNat (p.chal z).1], [[UInt8.ofNat (p.advc z).1]])

theorem byte1SeedAndPreSampler_eq (z : Fin (256 * 256)) :
    byte1SeedAndPreSampler z =
      ([UInt8.ofNat ((CoinSplit.prod 256 256).chal z).1],
       [[UInt8.ofNat ((CoinSplit.prod 256 256).advc z).1]]) := by unfold byte1SeedAndPreSampler; rfl

theorem uniformOn_byte1SeedAndPre : UniformOn (SmDtPreSampleOk 1 1 1) byte1SeedAndPreSampler where
  mem _ := ⟨rfl, rfl, fun h hh => by
    rcases List.mem_cons.mp hh with rfl | hNil
    · rfl
    · nomatch hNil⟩
  injective z₁ z₂ h := by
    let p := CoinSplit.prod 256 256
    injection h with hS hH
    injection hH with hHd _
    have hc := uniformOn_byte1Seed.injective (p.chal z₁) (p.chal z₂) hS
    have ha := uniformOn_byte1Seed.injective (p.advc z₁) (p.advc z₂) hHd
    rw [← p.pair_eta z₁, ← p.pair_eta z₂, hc, ha]
  surjective x hx := by
    let p := CoinSplit.prod 256 256
    obtain ⟨s, hs⟩ := x
    obtain ⟨h1, h2, h3⟩ := hx
    obtain ⟨cs, hcs⟩ := uniformOn_byte1Seed.surjective s h1
    match hs, h2, h3 with
    | [h], _, h3 =>
      obtain ⟨ch, hch⟩ := uniformOn_byte1Seed.surjective h (h3 h (List.Mem.head _))
      refine ⟨p.pair cs ch, ?_⟩
      unfold byte1SeedAndPreSampler
      dsimp only
      rw [p.chal_pair, p.advc_pair]
      exact Prod.ext hcs (congrArg (· :: []) hch)

private theorem poly257Hash_oneByte_unique (seed tweak m' : Bytes)
    (x₁ x₂ : Fin 256)
    (h₁ : poly257Hash seed tweak m' = poly257Hash seed tweak [UInt8.ofNat x₁.1])
    (h₂ : poly257Hash seed tweak m' = poly257Hash seed tweak [UInt8.ofNat x₂.1]) :
    x₁ = x₂ := by
  have hEq := h₁.symm.trans h₂
  unfold poly257Hash at hEq
  rw [iteOfPos (by simp : ([UInt8.ofNat x₁.1] : Bytes).length ≤ 2),
    iteOfPos (by simp : ([UInt8.ofNat x₂.1] : Bytes).length ≤ 2)] at hEq
  injection hEq with _ h1
  injection h1 with hHi h2
  injection h2 with hLo _
  have hHiN := congrArg UInt8.toNat hHi
  have hLoN := congrArg UInt8.toNat hLo
  have hv1 : poly257Eval (seed.headD 0).toNat [UInt8.ofNat x₁.1] = x₁.1 + 1 := by
    unfold poly257Eval poly257Coeff0 poly257Coeff1
    simp only [Nat.mul_zero, Nat.add_zero]
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt x₁.2,
      Nat.mod_eq_of_lt (by omega : x₁.1 + 1 < 257)]
  have hv2 : poly257Eval (seed.headD 0).toNat [UInt8.ofNat x₂.1] = x₂.1 + 1 := by
    unfold poly257Eval poly257Coeff0 poly257Coeff1
    simp only [Nat.mul_zero, Nat.add_zero]
    rw [UInt8.toNat_ofNat', Nat.mod_eq_of_lt x₂.2,
      Nat.mod_eq_of_lt (by omega : x₂.1 + 1 < 257)]
  rw [hv1, hv2] at hHiN hLoN
  rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat',
    Nat.mod_eq_of_lt (by omega : (x₁.1 + 1) / 256 < 256),
    Nat.mod_eq_of_lt (by omega : (x₂.1 + 1) / 256 < 256)] at hHiN
  rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat',
    Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide)),
    Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))] at hLoN
  have hd1 := Nat.div_add_mod (x₁.1 + 1) 256
  have hd2 := Nat.div_add_mod (x₂.1 + 1) 256
  exact Fin.ext (by omega)

private theorem poly257_preCandList_hit_le (seed tweak : Bytes) :
    ∀ (dict : List Bytes),
      sampleSum 256 (fun x =>
        if dict.any (fun m' =>
            decide (poly257Hash seed tweak m' = poly257Hash seed tweak [UInt8.ofNat x.1]))
        then 1 else 0) ≤ dict.length
  | [] => by
    simp only [List.any_nil, Bool.false_eq_true, ↓reduceIte, sampleSum_const,
      Nat.mul_zero, List.length_nil, Nat.le_refl]
  | m' :: ms => by
    have hSplit : ∀ x : Fin 256,
        (if (m' :: ms).any (fun c =>
            decide (poly257Hash seed tweak c = poly257Hash seed tweak [UInt8.ofNat x.1]))
         then 1 else 0) ≤
        (if decide (poly257Hash seed tweak m' = poly257Hash seed tweak [UInt8.ofNat x.1])
         then 1 else 0) +
        (if ms.any (fun c =>
            decide (poly257Hash seed tweak c = poly257Hash seed tweak [UInt8.ofNat x.1]))
         then 1 else 0) := fun x => by
      rw [List.any_cons]
      cases decide (poly257Hash seed tweak m' = poly257Hash seed tweak [UInt8.ofNat x.1]) <;>
        cases ms.any (fun c =>
          decide (poly257Hash seed tweak c = poly257Hash seed tweak [UInt8.ofNat x.1])) <;>
        decide
    have hHead : sampleSum 256 (fun x =>
        if decide (poly257Hash seed tweak m' = poly257Hash seed tweak [UInt8.ofNat x.1])
        then 1 else 0) ≤ 1 :=
      sampleSum_bool_le_one_of_subsingleton _ (fun x₁ x₂ h₁ h₂ =>
        poly257Hash_oneByte_unique seed tweak m' x₁ x₂
          (of_decide_eq_true h₁) (of_decide_eq_true h₂))
    have hSum := sampleSum_le 256 _ _ hSplit
    rw [sampleSum_add_fn] at hSum
    exact Nat.le_trans hSum
      (Nat.le_trans (Nat.add_le_add hHead (poly257_preCandList_hit_le seed tweak ms))
        (by rw [List.length_cons, Nat.add_comm]; exact Nat.le_refl _))

/-- **Simultaneous `SmDtPreHard` Theorem for `poly257Hash` (`(qEval + 1) / 256`).** Together with
    `poly257Hash_smDtTcrHard_within`, the single compressing hash `poly257Hash` simultaneously
    satisfies both `SmDtTcrHard` and `SmDtPreHard` at `seedLen = 1, inputLen = 1, q = 1`. -/
theorem poly257Hash_smDtPreHard_within (qTarget qEval : Nat) :
    SmDtPreHard (WithinPreQueries qTarget qEval) poly257Hash 1 1 1 ⟨qEval + 1, 256, by decide⟩ := by
  intro n nC nA hPos π sample hU adv hA
  unfold GameBound RatBound.le FinGame.winProb FinGame.winCount
  dsimp only
  rw [π.sampleSum_eq]
  conv => rhs; rw [π.card_eq]
  obtain ⟨hnC, _⟩ := hU.card_and_sampleSum_eq uniformOn_byte1SeedAndPre (fun _ => 0)
  have hSwap : sampleSum nC (fun c => sampleSum nA (fun a =>
      if (smDtPreGame hPos poly257Hash 1 (fun ω => (sample (π.chal ω)).1)
          (fun ω i => (sample (π.chal ω)).2.getD i []) (fun ω => adv (π.advc ω))).win (π.pair c a)
      then 1 else 0)) =
      sampleSum nA (fun a => sampleSum nC (fun c =>
        if smDtPreWin poly257Hash
            (Code.play (smDtPreOracle poly257Hash 1 (fun i => (sample c).2.getD i []))
              (adv a) ⟨(sample c).1, [], false⟩).2
            (Code.play (smDtPreOracle poly257Hash 1 (fun i => (sample c).2.getD i []))
              (adv a) ⟨(sample c).1, [], false⟩).1
        then 1 else 0)) := by
    have hS : sampleSum nC (fun c => sampleSum nA (fun a =>
        if (smDtPreGame hPos poly257Hash 1 (fun ω => (sample (π.chal ω)).1)
            (fun ω i => (sample (π.chal ω)).2.getD i []) (fun ω => adv (π.advc ω))).win (π.pair c a)
        then 1 else 0)) =
        sampleSum nC (fun c => sampleSum nA (fun a =>
          if smDtPreWin poly257Hash
              (Code.play (smDtPreOracle poly257Hash 1 (fun i => (sample c).2.getD i []))
                (adv a) ⟨(sample c).1, [], false⟩).2
              (Code.play (smDtPreOracle poly257Hash 1 (fun i => (sample c).2.getD i []))
                (adv a) ⟨(sample c).1, [], false⟩).1
          then 1 else 0)) :=
      sampleSum_ext (fun c => sampleSum_ext (fun a => by
        show (if smDtPreWin poly257Hash
            (Code.play (smDtPreOracle poly257Hash 1 (fun i => (sample (π.chal (π.pair c a))).2.getD i []))
              (adv (π.advc (π.pair c a))) ⟨(sample (π.chal (π.pair c a))).1, [], false⟩).2
            (Code.play (smDtPreOracle poly257Hash 1 (fun i => (sample (π.chal (π.pair c a))).2.getD i []))
              (adv (π.advc (π.pair c a))) ⟨(sample (π.chal (π.pair c a))).1, [], false⟩).1
          then 1 else 0) = _
        rw [π.chal_pair, π.advc_pair]))
    rw [hS]
    exact sampleSum_comm _ _ _
  rw [hSwap]
  have hPerA : ∀ a : Fin nA,
      sampleSum nC (fun c =>
        if smDtPreWin poly257Hash
            (Code.play (smDtPreOracle poly257Hash 1 (fun i => (sample c).2.getD i []))
              (adv a) ⟨(sample c).1, [], false⟩).2
            (Code.play (smDtPreOracle poly257Hash 1 (fun i => (sample c).2.getD i []))
              (adv a) ⟨(sample c).1, [], false⟩).1
        then 1 else 0) ≤ 256 * (qEval + 1) := fun a => by
    obtain ⟨_, dict, hDictLen, hDictMem⟩ := hA a
    obtain ⟨_, hSampleSum⟩ := hU.card_and_sampleSum_eq uniformOn_byte1SeedAndPre (fun sx =>
      if smDtPreWin poly257Hash
          (Code.play (smDtPreOracle poly257Hash 1 (fun i => sx.2.getD i []))
            (adv a) ⟨sx.1, [], false⟩).2
          (Code.play (smDtPreOracle poly257Hash 1 (fun i => sx.2.getD i []))
            (adv a) ⟨sx.1, [], false⟩).1
      then 1 else 0)
    rw [hSampleSum, (CoinSplit.prod 256 256).sampleSum_eq]
    have hPerSeed : ∀ s : Fin 256,
        sampleSum 256 (fun x =>
          let z := (CoinSplit.prod 256 256).pair s x
          if smDtPreWin poly257Hash
              (Code.play (smDtPreOracle poly257Hash 1 (fun i => (byte1SeedAndPreSampler z).2.getD i []))
                (adv a) ⟨(byte1SeedAndPreSampler z).1, [], false⟩).2
              (Code.play (smDtPreOracle poly257Hash 1 (fun i => (byte1SeedAndPreSampler z).2.getD i []))
                (adv a) ⟨(byte1SeedAndPreSampler z).1, [], false⟩).1
          then 1 else 0) ≤ qEval + 1 := fun s => by
      cases hAdv : adv a with
      | ret out =>
        have hZ : (fun x : Fin 256 =>
            let z := (CoinSplit.prod 256 256).pair s x
            if smDtPreWin poly257Hash
                (Code.play (smDtPreOracle poly257Hash 1 (fun i => (byte1SeedAndPreSampler z).2.getD i []))
                  (.ret out) ⟨(byte1SeedAndPreSampler z).1, [], false⟩).2
                (Code.play (smDtPreOracle poly257Hash 1 (fun i => (byte1SeedAndPreSampler z).2.getD i []))
                  (.ret out) ⟨(byte1SeedAndPreSampler z).1, [], false⟩).1
            then 1 else 0) = (fun _ => 0) := by
          funext x; rfl
        rw [hZ, sampleSum_const, Nat.mul_zero]
        exact Nat.zero_le _
      | call qr kNext =>
        let firstTweak : Bytes :=
          match qr with
          | .reveal => []
          | .target t₀ _ => t₀
        have hImp : ∀ x : Fin 256,
            (let z := (CoinSplit.prod 256 256).pair s x
             if smDtPreWin poly257Hash
                 (Code.play (smDtPreOracle poly257Hash 1 (fun i => (byte1SeedAndPreSampler z).2.getD i []))
                   (.call qr kNext) ⟨(byte1SeedAndPreSampler z).1, [], false⟩).2
                 (Code.play (smDtPreOracle poly257Hash 1 (fun i => (byte1SeedAndPreSampler z).2.getD i []))
                   (.call qr kNext) ⟨(byte1SeedAndPreSampler z).1, [], false⟩).1
             then 1 else 0) ≤
            (if (([] : Bytes) :: dict).any (fun m' =>
                decide (poly257Hash [UInt8.ofNat s.1] firstTweak m' =
                  poly257Hash [UInt8.ofNat s.1] firstTweak [UInt8.ofNat x.1]))
             then 1 else 0) := fun x => by
          let z := (CoinSplit.prod 256 256).pair s x
          have hz : byte1SeedAndPreSampler z = ([UInt8.ofNat s.1], [[UInt8.ofNat x.1]]) := by
            unfold byte1SeedAndPreSampler
            dsimp only [z]
            rw [(CoinSplit.prod 256 256).chal_pair, (CoinSplit.prod 256 256).advc_pair]
          dsimp only
          cases hW : smDtPreWin poly257Hash
              (Code.play (smDtPreOracle poly257Hash 1 (fun i => (byte1SeedAndPreSampler z).2.getD i []))
                (.call qr kNext) ⟨(byte1SeedAndPreSampler z).1, [], false⟩).2
              (Code.play (smDtPreOracle poly257Hash 1 (fun i => (byte1SeedAndPreSampler z).2.getD i []))
                (.call qr kNext) ⟨(byte1SeedAndPreSampler z).1, [], false⟩).1
          · simpa only [z, hW, Bool.false_eq_true, ↓reduceIte] using (Nat.zero_le (if (([] : Bytes) :: dict).any (fun m' => decide (poly257Hash [UInt8.ofNat s.1] firstTweak m' = poly257Hash [UInt8.ofNat s.1] firstTweak [UInt8.ofNat x.1])) then 1 else 0))
          · cases qr with
            | reveal =>
              have hTNil := pre_targets_after_revealed poly257Hash
                (fun i => (byte1SeedAndPreSampler z).2.getD i [])
                (kNext (some (byte1SeedAndPreSampler z).1))
                ⟨(byte1SeedAndPreSampler z).1, [], true⟩ rfl
              unfold smDtPreWin at hW
              rw [Code.play_call] at hW
              dsimp only [smDtPreOracle] at hW
              rw [hTNil] at hW
              cases hW
            | target t₀ m₀ =>
              have hTgt : (Code.play (smDtPreOracle poly257Hash 1
                  (fun i => (byte1SeedAndPreSampler z).2.getD i []))
                  (.call (.target t₀ m₀) kNext) ⟨(byte1SeedAndPreSampler z).1, [], false⟩).2.targets =
                  [(t₀, [UInt8.ofNat x.1])] := by
                rw [hz]
                rw [Code.play_call]
                change (Code.play (smDtPreOracle poly257Hash 1 (fun i => [[UInt8.ofNat x.1]].getD i []))
                  (kNext (some (poly257Hash [UInt8.ofNat s.1] t₀ [UInt8.ofNat x.1])))
                  ⟨[UInt8.ofNat s.1], [(t₀, [UInt8.ofNat x.1])], false⟩).2.targets = _
                exact pre_targets_after_one poly257Hash _ t₀ _ _ rfl
              have hSeedInv := (smDtPreRun_inv poly257Hash 1
                (fun _ : Fin 1 => (byte1SeedAndPreSampler z).1)
                (fun _ i => (byte1SeedAndPreSampler z).2.getD i [])
                (fun _ => .call (.target t₀ m₀) kNext) ⟨0, Nat.one_pos⟩).1
              obtain ⟨e, hMemE, hAnd⟩ := List.any_eq_true.mp hW
              rw [hTgt] at hMemE
              rcases List.mem_cons.mp hMemE with rfl | hNil
              · obtain ⟨_, hCol⟩ := andTrueSplit hAnd
                have hColP := of_decide_eq_true hCol
                have hSd : (Code.play (smDtPreOracle poly257Hash 1
                    (fun i => (byte1SeedAndPreSampler z).2.getD i []))
                    (.call (.target t₀ m₀) kNext) ⟨(byte1SeedAndPreSampler z).1, [], false⟩).2.seed =
                    [UInt8.ofNat s.1] := hSeedInv.trans (congrArg Prod.fst hz)
                rw [hSd] at hColP
                have hCandMem : (Code.play (smDtPreOracle poly257Hash 1
                    (fun i => (byte1SeedAndPreSampler z).2.getD i []))
                    (.call (.target t₀ m₀) kNext) ⟨(byte1SeedAndPreSampler z).1, [], false⟩).1.candidate ∈
                    ([] : Bytes) :: dict := by
                  have hM := hDictMem (smDtPreOracle poly257Hash 1
                    (fun i => (byte1SeedAndPreSampler z).2.getD i []))
                    ⟨(byte1SeedAndPreSampler z).1, [], false⟩
                  rw [hAdv] at hM
                  exact hM
                have hAny : (([] : Bytes) :: dict).any (fun m' =>
                    decide (poly257Hash [UInt8.ofNat s.1] t₀ m' =
                      poly257Hash [UInt8.ofNat s.1] t₀ [UInt8.ofNat x.1])) = true :=
                  List.any_eq_true.mpr ⟨_, hCandMem, decide_eq_true hColP⟩
                dsimp only [firstTweak]
                rw [hAny]
                simpa only [z, hW, ↓reduceIte] using (Nat.le_refl 1)
              · nomatch hNil
        exact Nat.le_trans (sampleSum_le 256 _ _ hImp)
          (Nat.le_trans (poly257_preCandList_hit_le [UInt8.ofNat s.1] firstTweak (([] : Bytes) :: dict))
            (by rw [List.length_cons]; exact Nat.succ_le_succ hDictLen))
    exact Nat.le_trans (sampleSum_le 256 _ _ hPerSeed) (by rw [sampleSum_const]; exact Nat.le_refl _)
  have hSum := sampleSum_le nA _ _ hPerA
  rw [sampleSum_const] at hSum
  conv => rhs; rw [hnC]
  refine Nat.le_trans (Nat.mul_le_mul_right 256 hSum) ?_
  simp only [Nat.mul_left_comm, Nat.mul_comm]
  exact Nat.le_refl _

#verify_constructive roLookup_append_of_absent
#verify_constructive mem_zip_tweaks_implies_find
#verify_constructive romPreDecodeVec_hit_bound
#verify_constructive romPre_queryList_hit_bound
#verify_constructive lazyRomRun_agree_unless_queried
#verify_constructive romSmDtPre_within_bound
#tooth_pair romSmDtTcr_within_bound vs tooth_romSmDtTcr_without_within
#tooth_pair romSmDtPre_within_bound vs tooth_romSmDtPre_without_within
#tooth_pair romItsr_within_bound vs tooth_romItsr_without_within
#tooth_pair byteXorHash_smDtPreHard_within vs smDtPreHard_unrestricted_refuted
#tooth_pair byteIdxHmsg_itsrHard_within vs byteIdxHmsg_itsrHard_refuted
#tooth_pair poly257Hash_smDtTcrHard_within vs poly257Hash_smDtTcrHard_refuted

/-- A singleton dictionary containing the hidden input wins after target and seed reveal. -/
theorem boundedPreAdv_singleton_wins (th : Bytes → Bytes → Bytes → Bytes) (seed tweak m : Bytes) :
    smDtPreWin th
      (Code.play (smDtPreOracle th 1 (fun _ => m)) (boundedPreAdv th tweak [m]) ⟨seed, [], false⟩).2
      (Code.play (smDtPreOracle th 1 (fun _ => m)) (boundedPreAdv th tweak [m]) ⟨seed, [], false⟩).1 = true := by
  simp [boundedPreAdv, Code.play, smDtPreOracle, firstByteString, smDtPreWin]

/-- Only index zero is read by the singleton PRE distinguisher. -/
theorem boundedPreAdv_singleton_hidden_wins (th : Bytes → Bytes → Bytes → Bytes)
    (seed tweak m : Bytes) (hidden : Nat → Bytes) (h0 : hidden 0 = m) :
    smDtPreWin th
      (Code.play (smDtPreOracle th 1 hidden) (boundedPreAdv th tweak [m]) ⟨seed, [], false⟩).2
      (Code.play (smDtPreOracle th 1 hidden) (boundedPreAdv th tweak [m]) ⟨seed, [], false⟩).1 = true := by
  simp [boundedPreAdv, Code.play, smDtPreOracle, firstByteString, smDtPreWin, h0]

theorem CoinSplit.challengerOnly_chal (n : Nat) (z : Fin n) :
    (challengerOnly n).chal z = z := by unfold challengerOnly; rfl

theorem CoinSplit.prod_advc_val (nC nA : Nat) (z : Fin (nC * nA)) :
    ((prod nC nA).advc z).val = z.val % nA := by unfold prod; rfl
#verify_constructive boundedPreAdv_singleton_hidden_wins

theorem smDtTcrOracle_target (th : Bytes → Bytes → Bytes → Bytes) (q : Nat)
    (st : TargetState) (t m : Bytes) :
    smDtTcrOracle th q st (.target t m) =
      if st.revealed = false ∧ st.targets.length < q ∧ t ∉ st.targets.map Prod.fst then
        (some (th st.seed t m), { st with targets := st.targets ++ [(t, m)] })
      else (none, st) := by unfold smDtTcrOracle; rfl

theorem smDtTcrOracle_reveal (th : Bytes → Bytes → Bytes → Bytes) (q : Nat) (st : TargetState) :
    smDtTcrOracle th q st .reveal = (some st.seed, { st with revealed := true }) := by
  unfold smDtTcrOracle; rfl

theorem smDtPreOracle_target (th : Bytes → Bytes → Bytes → Bytes) (q : Nat)
    (hidden : Nat → Bytes) (st : TargetState) (t d : Bytes) :
    smDtPreOracle th q hidden st (.target t d) =
      if st.revealed = false ∧ st.targets.length < q ∧ t ∉ st.targets.map Prod.fst then
        (some (th st.seed t (hidden st.targets.length)),
          { st with targets := st.targets ++ [(t, hidden st.targets.length)] })
      else (none, st) := by unfold smDtPreOracle; rfl

theorem smDtPreOracle_reveal (th : Bytes → Bytes → Bytes → Bytes) (q : Nat)
    (hidden : Nat → Bytes) (st : TargetState) :
    smDtPreOracle th q hidden st .reveal = (some st.seed, { st with revealed := true }) := by
  unfold smDtPreOracle; rfl

theorem smDtTcrWin_eq (th : Bytes → Bytes → Bytes → Bytes) (st : TargetState) (out : TargetBreak) :
    smDtTcrWin th st out =
      (decide ((out.tweak, out.committed) ∈ st.targets) &&
        (decide (out.candidate ≠ out.committed) &&
          decide (th st.seed out.tweak out.candidate = th st.seed out.tweak out.committed))) := by
  unfold smDtTcrWin; rfl

theorem smDtPreWin_eq (th : Bytes → Bytes → Bytes → Bytes) (st : TargetState) (out : TargetBreak) :
    smDtPreWin th st out =
      st.targets.any (fun e =>
        decide (e.1 = out.tweak) && decide (th st.seed e.1 out.candidate = th st.seed e.1 e.2)) := by
  unfold smDtPreWin; rfl

theorem smDtTcrRun_eq {n : Nat} (th : Bytes → Bytes → Bytes → Bytes) (q : Nat)
    (seed : Fin n → Bytes) (adv : Fin n → Code targetIface TargetBreak) (ω : Fin n) :
    smDtTcrRun th q seed adv ω = Code.play (smDtTcrOracle th q) (adv ω) ⟨seed ω, [], false⟩ := by
  unfold smDtTcrRun; rfl

theorem smDtTcrGame_win {n : Nat} (hPos : 0 < n) (th : Bytes → Bytes → Bytes → Bytes) (q : Nat)
    (seed : Fin n → Bytes) (adv : Fin n → Code targetIface TargetBreak) (ω : Fin n) :
    (smDtTcrGame hPos th q seed adv).win ω =
      smDtTcrWin th (smDtTcrRun th q seed adv ω).2 (smDtTcrRun th q seed adv ω).1 := by
  unfold smDtTcrGame; rfl

theorem itsrOracle_eq (q : Nat) (rand : Nat → Bytes) (log : List (Bytes × Bytes)) (msg : Bytes) :
    itsrOracle q rand log msg =
      if log.length < q then (rand log.length, log ++ [(rand log.length, msg)]) else ([], log) := by
  unfold itsrOracle; rfl

theorem itsrWin_eq (hmsg : Bytes → Bytes → List Nat) (log : List (Bytes × Bytes))
    (out : Bytes × Bytes) :
    itsrWin hmsg log out =
      (!decide (out ∈ log) &&
        (hmsg out.1 out.2).all (fun x => log.any (fun e => decide (x ∈ hmsg e.1 e.2)))) := by
  unfold itsrWin; rfl

theorem itsrRun_eq {n : Nat} (q : Nat) (rand : Fin n → Nat → Bytes)
    (adv : Fin n → Code byteOracleIface (Bytes × Bytes)) (ω : Fin n) :
    itsrRun q rand adv ω = Code.play (itsrOracle q (rand ω)) (adv ω) [] := by
  unfold itsrRun; rfl

theorem itsrGame_win {n : Nat} (hPos : 0 < n) (hmsg : Bytes → Bytes → List Nat) (q : Nat)
    (rand : Fin n → Nat → Bytes) (adv : Fin n → Code byteOracleIface (Bytes × Bytes)) (ω : Fin n) :
    (itsrGame hPos hmsg q rand adv).win ω =
      itsrWin hmsg (itsrRun q rand adv ω).2 (itsrRun q rand adv ω).1 := by
  unfold itsrGame; rfl

theorem SmDtPreSampleOk_eq (seedLen inputLen q : Nat) (x : Bytes × List Bytes) :
    SmDtPreSampleOk seedLen inputLen q x =
      (x.1.length = seedLen ∧ x.2.length = q ∧ ∀ h ∈ x.2, h.length = inputLen) := by
  unfold SmDtPreSampleOk; rfl

theorem ItsrSampleOk_eq (randLen q : Nat) (x : List Bytes) :
    ItsrSampleOk randLen q x = (x.length = q ∧ ∀ r ∈ x, r.length = randLen) := by
  unfold ItsrSampleOk; rfl

theorem PrfSampleOk_eq (keyLen inLen outLen : Nat) (x : Bytes × (Bytes → Bytes)) :
    PrfSampleOk keyLen inLen outLen x =
      (x.1.length = keyLen ∧
        ∀ inp : Bytes, (inp.length = inLen → (x.2 inp).length = outLen) ∧
          (inp.length ≠ inLen → x.2 inp = [])) := by
  unfold PrfSampleOk; rfl

theorem WithinPreQueries_eq (qTarget qEval : Nat) (c : Code targetIface TargetBreak) :
    WithinPreQueries qTarget qEval c =
      (Within qTarget c ∧
        ∃ dict : List Bytes, dict.length ≤ qEval ∧
          ∀ (oracle : TargetState → (qr : targetIface.Query) → targetIface.Resp qr × TargetState)
            (st : TargetState),
            (Code.play oracle c st).1.candidate ∈ ([] : Bytes) :: dict) := by
  unfold WithinPreQueries; rfl

theorem WithinTcrQueries_eq (qTarget qEval : Nat) (c : Code targetIface TargetBreak) :
    WithinTcrQueries qTarget qEval c =
      (Within qTarget c ∧
        ∃ cands : List Bytes, cands.length ≤ qEval ∧
          ∀ (oracle : TargetState → (qr : targetIface.Query) → targetIface.Resp qr × TargetState)
            (st : TargetState),
            (Code.play oracle c st).1.candidate ∈ ([] : Bytes) :: cands) := by
  unfold WithinTcrQueries; rfl

theorem WithinItsrQueries_eq (qSign qEval : Nat) (c : Code byteOracleIface (Bytes × Bytes)) :
    WithinItsrQueries qSign qEval c =
      (Within qSign c ∧
        ∃ pool : List (Bytes × Bytes), pool.length ≤ qEval ∧
          ∀ (oracle : List (Bytes × Bytes) → (msg : Bytes) → Bytes × List (Bytes × Bytes))
            (st : List (Bytes × Bytes)),
            (Code.play oracle c st).1 ∈ (([], []) : Bytes × Bytes) :: pool) := by
  unfold WithinItsrQueries; rfl

theorem boundedPreAdv_eq (th : Bytes → Bytes → Bytes → Bytes) (tweak : Bytes)
    (dict : List Bytes) :
    boundedPreAdv th tweak dict =
      .call (.target tweak []) (fun y =>
        .call .reveal (fun s =>
          .ret ⟨tweak, [], firstByteString
            (fun m => decide (some (th (s.getD []) tweak m) = y)) dict⟩)) := by
  unfold boundedPreAdv; rfl

#export_eqns budgetedFunOracle prfRealGame prfIdealGame byte1SeedSampler smDtPreGame smDtPreRun
#verify_constructive boundedPreAdv_singleton_wins

/-! ## 3. Operating-System and Hardware Platform Contracts

Each contract is a set of laws over the event traces of an explicit environment model. A model
that does not behave as required has no contract; each section gives a reference model that
satisfies the laws and a faulty model that provably does not. -/

/-! ### 3a. Crash-consistent storage (`fsync` + atomic `rename` + external monotone anchor) -/

/-- Storage event of a write-ahead log. -/
inductive FsyncOp where
  /-- Write a record to the staging file. -/
  | append (rec : Bytes)
  /-- `fsync` the staging file. -/
  | fsyncFile
  /-- Atomically `rename` the staging file over the log. -/
  | rename
  /-- `fsync` the parent directory. -/
  | fsyncDir
  /-- Advance the external monotone anchor to the durable log length. -/
  | bumpAnchor
  /-- Power loss followed by recovery. -/
  | crash
  deriving DecidableEq, Repr

/-- Storage environment: `durable s` is the record list a recovery from `s` returns, `anchor s`
    the value of the external monotone epoch anchor. -/
structure FsyncStorageModel where
  State : Type
  step : State → FsyncOp → State
  durable : State → List Bytes
  anchor : State → Nat

/-- Run a trace of storage events. -/
@[expose] def FsyncStorageModel.run (M : FsyncStorageModel) : M.State → List FsyncOp → M.State
  | s, [] => s
  | s, op :: rest => M.run (M.step s op) rest

theorem FsyncStorageModel.run_append (M : FsyncStorageModel) :
    ∀ (tr₁ tr₂ : List FsyncOp) (s : M.State), M.run s (tr₁ ++ tr₂) = M.run (M.run s tr₁) tr₂
  | [], _, _ => rfl
  | op :: rest, tr₂, s => M.run_append rest tr₂ (M.step s op)

/-- The commit protocol for one record: stage, `fsync` the file, `rename`, `fsync` the
    directory, advance the anchor. -/
@[expose] def walCommitOps (rec : Bytes) : List FsyncOp :=
  [.append rec, .fsyncFile, .rename, .fsyncDir, .bumpAnchor]

/-- POSIX crash-consistent write-ahead log contract for the storage environment `M`.

    `fsyncFile` denotes a flush to the storage medium (`F_FULLFSYNC` / a drive-cache flush), not
    a hand-off to a volatile drive cache. `committedRecordLast` does not say that a commit adds
    exactly one record: a `rename` that an earlier, unfinished commit performed is made durable
    by the directory `fsync` of the next commit, so the durable log may grow by those pending
    records first. `noRollback`, `anchorMonotone` and `anchorWitnessesDurable` are properties of
    the storage together with the host discipline of the write-ahead log: `rename` is refused
    unless the staging file is synced, and the anchor is not advanced while a rename is waiting
    for its directory `fsync`.

    Instance for the three-tier `PosixFsState` model: `Qsag.PosixWalHost.walModel_contract`
    (`Exec.PlatformContractInstances`). -/
structure PosixFsyncContract (M : FsyncStorageModel) : Prop where
  /-- After the commit protocol the record is the last durable record, behind everything that
      was durable and everything already renamed. -/
  committedRecordLast : ∀ (s : M.State) (rec : Bytes),
    ∃ pending : List Bytes,
      M.durable (M.run s (walCommitOps rec)) = M.durable s ++ pending ++ [rec]
  /-- No event trace, crashes included, removes or reorders durable records. -/
  noRollback : ∀ (s : M.State) (tr : List FsyncOp), M.durable s <+: M.durable (M.run s tr)
  /-- The external anchor never decreases. -/
  anchorMonotone : ∀ (s : M.State) (tr : List FsyncOp), M.anchor s ≤ M.anchor (M.run s tr)
  /-- An anchor that is a lower bound on the durable length stays one. -/
  anchorWitnessesDurable : ∀ (s : M.State) (tr : List FsyncOp),
    M.anchor s ≤ (M.durable s).length →
    M.anchor (M.run s tr) ≤ (M.durable (M.run s tr)).length

/-- A committed record is returned by every later recovery, whatever events follow. -/
theorem PosixFsyncContract.committed_survives {M : FsyncStorageModel} (c : PosixFsyncContract M)
    (s : M.State) (rec : Bytes) (post : List FsyncOp) :
    rec ∈ M.durable (M.run s (walCommitOps rec ++ post)) := by
  rw [M.run_append]
  obtain ⟨t, ht⟩ := c.noRollback (M.run s (walCommitOps rec)) post
  obtain ⟨pending, hp⟩ := c.committedRecordLast s rec
  rw [← ht, hp]
  exact List.mem_append_left t (List.mem_append_right _ (List.Mem.head _))

/-- A whole-log snapshot shorter than the anchor is never what recovery returns. -/
theorem PosixFsyncContract.anchor_excludes_stale_snapshot {M : FsyncStorageModel}
    (c : PosixFsyncContract M) (s : M.State) (tr : List FsyncOp)
    (h : M.anchor s ≤ (M.durable s).length) :
    M.anchor s ≤ (M.durable (M.run s tr)).length :=
  Nat.le_trans (c.anchorMonotone s tr) (c.anchorWitnessesDurable s tr h)

/-- State of the reference journal: the durable log, the records renamed into the log but not
    yet covered by a directory `fsync`, the staged record, whether the staging file is synced,
    and the anchor. -/
structure FsyncJournalState where
  durable : List Bytes
  pending : List Bytes
  staged : Option Bytes
  fileSynced : Bool
  anchor : Nat

/-- `rename` in the reference journal: a synced staged record joins the pending records; an
    unsynced or absent staging file is not renamed. -/
def fsyncJournalRename (s : FsyncJournalState) : FsyncJournalState :=
  match s.fileSynced, s.staged with
  | true, some rec => { s with pending := s.pending ++ [rec], staged := none, fileSynced := false }
  | _, _ => s

/-- Reference journal. A renamed record stays renamed: `append` starts a new staging file and
    leaves the pending records alone. Pending records become durable at the next directory
    `fsync`; a crash drops them. With `rollbackOnCrash = true` a crash also discards the durable
    log (a volume that loses synced data). -/
def fsyncJournalStep (rollbackOnCrash : Bool) (s : FsyncJournalState) :
    FsyncOp → FsyncJournalState
  | .append rec => { s with staged := some rec, fileSynced := false }
  | .fsyncFile => { s with fileSynced := s.staged.isSome }
  | .rename => fsyncJournalRename s
  | .fsyncDir => { s with durable := s.durable ++ s.pending, pending := [] }
  | .bumpAnchor => { s with anchor := Nat.max s.anchor s.durable.length }
  | .crash =>
    { durable := if rollbackOnCrash then [] else s.durable
      pending := []
      staged := none
      fileSynced := false
      anchor := s.anchor }

/-- The reference journal as a storage environment. -/
def fsyncJournalModel (rollbackOnCrash : Bool) : FsyncStorageModel where
  State := FsyncJournalState
  step := fsyncJournalStep rollbackOnCrash
  durable := fun s => s.durable
  anchor := fun s => s.anchor

private theorem fsyncJournalRename_facts (s : FsyncJournalState) :
    (fsyncJournalRename s).durable = s.durable ∧ (fsyncJournalRename s).anchor = s.anchor := by
  unfold fsyncJournalRename
  split <;> exact ⟨rfl, rfl⟩

private theorem fsyncJournalStep_prefix (s : FsyncJournalState) (op : FsyncOp) :
    s.durable <+: (fsyncJournalStep false s op).durable := by
  cases op with
  | fsyncDir => exact List.prefix_append _ _
  | append _ => exact List.prefix_refl _
  | fsyncFile => exact List.prefix_refl _
  | rename =>
    show s.durable <+: (fsyncJournalRename s).durable
    rw [(fsyncJournalRename_facts s).1]
    exact List.prefix_refl _
  | bumpAnchor => exact List.prefix_refl _
  | crash => exact List.prefix_refl _

private theorem fsyncJournalStep_anchor (s : FsyncJournalState) (op : FsyncOp) :
    s.anchor ≤ (fsyncJournalStep false s op).anchor := by
  cases op with
  | bumpAnchor => exact Nat.le_max_left _ _
  | append _ => exact Nat.le_refl _
  | fsyncFile => exact Nat.le_refl _
  | rename =>
    show s.anchor ≤ (fsyncJournalRename s).anchor
    rw [(fsyncJournalRename_facts s).2]
    exact Nat.le_refl _
  | fsyncDir => exact Nat.le_refl _
  | crash => exact Nat.le_refl _

private theorem fsyncJournalStep_anchor_le (s : FsyncJournalState) (op : FsyncOp)
    (h : s.anchor ≤ s.durable.length) :
    (fsyncJournalStep false s op).anchor ≤ (fsyncJournalStep false s op).durable.length := by
  cases op with
  | bumpAnchor => exact Nat.max_le.mpr ⟨h, Nat.le_refl _⟩
  | fsyncDir =>
    show s.anchor ≤ (s.durable ++ s.pending).length
    rw [List.length_append]
    exact Nat.le_trans h (Nat.le_add_right _ _)
  | append _ => exact h
  | fsyncFile => exact h
  | rename =>
    show (fsyncJournalRename s).anchor ≤ (fsyncJournalRename s).durable.length
    rw [(fsyncJournalRename_facts s).1, (fsyncJournalRename_facts s).2]
    exact h
  | crash => exact h

private theorem fsyncJournal_run_prefix :
    ∀ (tr : List FsyncOp) (s : FsyncJournalState),
      s.durable <+: ((fsyncJournalModel false).run s tr).durable
  | [], _ => List.prefix_refl _
  | op :: rest, s =>
    List.IsPrefix.trans (fsyncJournalStep_prefix s op)
      (fsyncJournal_run_prefix rest (fsyncJournalStep false s op))

private theorem fsyncJournal_run_anchor :
    ∀ (tr : List FsyncOp) (s : FsyncJournalState),
      s.anchor ≤ ((fsyncJournalModel false).run s tr).anchor
  | [], _ => Nat.le_refl _
  | op :: rest, s =>
    Nat.le_trans (fsyncJournalStep_anchor s op)
      (fsyncJournal_run_anchor rest (fsyncJournalStep false s op))

private theorem fsyncJournal_run_anchor_le :
    ∀ (tr : List FsyncOp) (s : FsyncJournalState), s.anchor ≤ s.durable.length →
      ((fsyncJournalModel false).run s tr).anchor ≤
        ((fsyncJournalModel false).run s tr).durable.length
  | [], _, h => h
  | op :: rest, s, h =>
    fsyncJournal_run_anchor_le rest (fsyncJournalStep false s op)
      (fsyncJournalStep_anchor_le s op h)

/-- The reference journal that keeps synced data across crashes satisfies the contract. -/
theorem fsyncJournalModel_contract : PosixFsyncContract (fsyncJournalModel false) where
  committedRecordLast s rec := ⟨s.pending, by
    show s.durable ++ (s.pending ++ [rec]) = s.durable ++ s.pending ++ [rec]
    rw [List.append_assoc]⟩
  noRollback s tr := fsyncJournal_run_prefix tr s
  anchorMonotone s tr := fsyncJournal_run_anchor tr s
  anchorWitnessesDurable s tr h := fsyncJournal_run_anchor_le tr s h

/-- A volume that loses its durable log at a crash has no contract. -/
theorem fsync_rollback_volume_has_no_contract : ¬ PosixFsyncContract (fsyncJournalModel true) := by
  intro c
  obtain ⟨t, ht⟩ := c.noRollback ⟨[[]], [], none, false, 0⟩ [.crash]
  have hLen := congrArg List.length ht
  rw [List.length_append] at hLen
  exact Nat.succ_ne_zero _ (Nat.eq_zero_of_add_eq_zero_right hLen)

/-- A commit does not add exactly one record: in the reference journal, a commit started while
    an earlier rename is waiting for its directory `fsync` makes that record durable too. The
    law "the commit protocol appends exactly its record" is false for honest storage. -/
theorem fsyncJournal_commit_flushes_pending_rename :
    ¬ ∀ (s : (fsyncJournalModel false).State) (rec : Bytes),
      (fsyncJournalModel false).durable ((fsyncJournalModel false).run s (walCommitOps rec)) =
        (fsyncJournalModel false).durable s ++ [rec] := by
  intro h
  exact absurd (congrArg List.length (h ⟨[], [[1]], none, false, 0⟩ [])) (by decide)

/-! ### 3b. Authenticated point-to-point channels -/

/-- Message on a point-to-point channel between custody / MPC peers. -/
structure ChannelMsg where
  sender : Nat
  receiver : Nat
  seq : Nat
  payload : Bytes
  deriving DecidableEq, Repr

/-- Channel event: `send m` is performed by `m.sender`; `deliver m` hands `m` to `m.receiver`
    as coming from `m.sender`. -/
inductive ChannelEvent where
  | send (m : ChannelMsg)
  | deliver (m : ChannelMsg)
  deriving DecidableEq, Repr

/-- The honest run that sends and then delivers each message of `msgs` once, in order. -/
def honestChannelRun (msgs : List ChannelMsg) : List ChannelEvent :=
  msgs.flatMap (fun m => [.send m, .deliver m])

/-- Sender-authenticated, replay-protected channel contract for a network environment given
    by its set `admits` of possible event traces. The environment must admit the honest runs,
    so the empty environment is not an instance.

    Instances: `checkedChannel_contract` (below) and the sequence-numbered anti-replay session
    channel `Qsag.Exec.PlatformContractInstances.seqSessionChannel_contract` (re-exported in
    `Qsag.Top.Custody` and `Qsag.Top.Credentials`). By contrast, the raw gossip step
    `RssParticipant.networkStep` allows re-delivery and leaves replay filtering to the receiving
    node, so it does not by itself satisfy `replayProtected`. -/
structure AuthenticatedChannelContract (admits : List ChannelEvent → Prop) : Prop where
  /-- Sending pairwise different messages and delivering each once is possible. -/
  honestRunsAdmitted : ∀ msgs : List ChannelMsg, msgs.Nodup → admits (honestChannelRun msgs)
  /-- Every delivery is preceded by the matching send from the named sender. -/
  peerAuthenticated : ∀ (tr : List ChannelEvent), admits tr →
    ∀ (pre post : List ChannelEvent) (m : ChannelMsg),
      tr = pre ++ .deliver m :: post → .send m ∈ pre
  /-- No message is delivered twice. -/
  replayProtected : ∀ (tr : List ChannelEvent), admits tr →
    ∀ (pre post : List ChannelEvent) (m : ChannelMsg),
      tr = pre ++ .deliver m :: post → .deliver m ∉ post

/-- Reference channel: a delivery is possible only for a message that was sent and has not
    been delivered. The accumulators are the sent and the delivered messages. -/
def channelRun : List ChannelEvent → List ChannelMsg → List ChannelMsg → Bool
  | [], _, _ => true
  | .send m :: rest, sent, dl => channelRun rest (m :: sent) dl
  | .deliver m :: rest, sent, dl =>
    decide (m ∈ sent) && (!decide (m ∈ dl) && channelRun rest sent (m :: dl))

private theorem channelRun_delivered_absent (m : ChannelMsg) :
    ∀ (tr : List ChannelEvent) (sent dl : List ChannelMsg),
      channelRun tr sent dl = true → m ∈ dl → .deliver m ∉ tr
  | [], _, _, _, _ => fun h => nomatch h
  | .send m' :: rest, sent, dl, hRun, hDl => fun hMem => by
    rcases List.mem_cons.mp hMem with hEq | hRest
    · cases hEq
    · exact channelRun_delivered_absent m rest (m' :: sent) dl hRun hDl hRest
  | .deliver m' :: rest, sent, dl, hRun, hDl => fun hMem => by
    have hRun' : (decide (m' ∈ sent) && (!decide (m' ∈ dl) && channelRun rest sent (m' :: dl))) =
        true := hRun
    obtain ⟨_, h2⟩ := andTrueSplit hRun'
    obtain ⟨hFresh, hRest⟩ := andTrueSplit h2
    rcases List.mem_cons.mp hMem with hEq | hTail
    · cases hEq
      rw [decide_eq_true hDl] at hFresh
      cases hFresh
    · exact channelRun_delivered_absent m rest sent (m' :: dl) hRest
        (List.mem_cons_of_mem _ hDl) hTail

private theorem channelRun_no_replay (m : ChannelMsg) (post : List ChannelEvent) :
    ∀ (pre : List ChannelEvent) (sent dl : List ChannelMsg),
      channelRun (pre ++ .deliver m :: post) sent dl = true → .deliver m ∉ post
  | [], sent, dl, hRun => by
    have hRun' : (decide (m ∈ sent) && (!decide (m ∈ dl) && channelRun post sent (m :: dl))) =
        true := hRun
    exact channelRun_delivered_absent m post sent (m :: dl)
      (andTrueSplit (andTrueSplit hRun').2).2 (List.Mem.head _)
  | .send m' :: pre, sent, dl, hRun => channelRun_no_replay m post pre (m' :: sent) dl hRun
  | .deliver m' :: pre, sent, dl, hRun => by
    have hRun' : (decide (m' ∈ sent) &&
        (!decide (m' ∈ dl) && channelRun (pre ++ .deliver m :: post) sent (m' :: dl))) = true :=
      hRun
    exact channelRun_no_replay m post pre sent (m' :: dl) (andTrueSplit (andTrueSplit hRun').2).2

private theorem channelRun_authentic (m : ChannelMsg) (post : List ChannelEvent) :
    ∀ (pre : List ChannelEvent) (sent dl : List ChannelMsg),
      channelRun (pre ++ .deliver m :: post) sent dl = true → m ∈ sent ∨ .send m ∈ pre
  | [], sent, dl, hRun => by
    have hRun' : (decide (m ∈ sent) && (!decide (m ∈ dl) && channelRun post sent (m :: dl))) =
        true := hRun
    exact .inl (of_decide_eq_true (andTrueSplit hRun').1)
  | .send m' :: pre, sent, dl, hRun => by
    rcases channelRun_authentic m post pre (m' :: sent) dl hRun with hSent | hPre
    · rcases List.mem_cons.mp hSent with hEq | hOld
      · exact .inr (hEq ▸ List.Mem.head _)
      · exact .inl hOld
    · exact .inr (List.mem_cons_of_mem _ hPre)
  | .deliver m' :: pre, sent, dl, hRun => by
    have hRun' : (decide (m' ∈ sent) &&
        (!decide (m' ∈ dl) && channelRun (pre ++ .deliver m :: post) sent (m' :: dl))) = true :=
      hRun
    rcases channelRun_authentic m post pre sent (m' :: dl)
      (andTrueSplit (andTrueSplit hRun').2).2 with hSent | hPre
    · exact .inl hSent
    · exact .inr (List.mem_cons_of_mem _ hPre)

private theorem channelRun_honest :
    ∀ (msgs : List ChannelMsg) (sent dl : List ChannelMsg), msgs.Nodup →
      (∀ m ∈ msgs, m ∉ dl) → channelRun (honestChannelRun msgs) sent dl = true
  | [], _, _, _, _ => rfl
  | m :: rest, sent, dl, hNd, hFresh => by
    obtain ⟨hHead, hTail⟩ := List.nodup_cons.mp hNd
    have ih := channelRun_honest rest (m :: sent) (m :: dl) hTail (fun m' hm' hIn => by
      rcases List.mem_cons.mp hIn with hEq | hOld
      · exact hHead (hEq ▸ hm')
      · exact hFresh m' (List.mem_cons_of_mem _ hm') hOld)
    show (decide (m ∈ m :: sent) &&
      (!decide (m ∈ dl) && channelRun (honestChannelRun rest) (m :: sent) (m :: dl))) = true
    have h1 : decide (m ∈ m :: sent) = true := decide_eq_true (List.Mem.head sent)
    have h2 : decide (m ∈ dl) = false := decide_eq_false (hFresh m (List.Mem.head rest))
    rw [h1, h2, ih]
    rfl

/-- The reference channel satisfies the contract. -/
theorem checkedChannel_contract :
    AuthenticatedChannelContract (fun tr => channelRun tr [] [] = true) where
  honestRunsAdmitted msgs hNd := channelRun_honest msgs [] [] hNd (fun _ _ h => nomatch h)
  peerAuthenticated tr hRun pre post m hEq := by
    rw [hEq] at hRun
    rcases channelRun_authentic m post pre [] [] hRun with hSent | hPre
    · exact nomatch hSent
    · exact hPre
  replayProtected tr hRun pre post m hEq := by
    rw [hEq] at hRun
    exact channelRun_no_replay m post pre [] [] hRun

/-- A network that admits every trace (an open relay) has no contract. -/
theorem open_relay_has_no_channel_contract :
    ¬ AuthenticatedChannelContract (fun _ => True) := by
  intro c
  exact nomatch c.peerAuthenticated [.deliver ⟨0, 0, 0, []⟩] trivial [] [] ⟨0, 0, 0, []⟩ rfl

/-- A network that admits no trace (it delivers nothing, and does not even exist as a run) has
    no contract: the laws are not allowed to hold vacuously. -/
theorem empty_network_has_no_channel_contract :
    ¬ AuthenticatedChannelContract (fun _ => False) :=
  fun c => c.honestRunsAdmitted [] List.nodup_nil

/-! ### 3c. Secret-share erasure at quarantine -/

/-- Event on the memory holding secret shares. -/
inductive ShareMemOp where
  /-- Write share bytes into a slot. -/
  | load (slot : Nat) (bytes : Bytes)
  /-- Compute with a slot. -/
  | use (slot : Nat)
  /-- Enter quarantine (fault or error return). -/
  | quarantine
  deriving DecidableEq, Repr

/-- `true` exactly on `load` events. -/
def ShareMemOp.isLoad : ShareMemOp → Bool
  | .load _ _ => true
  | _ => false

/-- Memory environment: `residue s slot` is the physical content of the slot in state `s`,
    as read by a core dump or a later allocation. -/
structure ShareMemoryModel where
  State : Type
  step : State → ShareMemOp → State
  residue : State → Nat → Bytes

/-- Run a trace of memory events. -/
def ShareMemoryModel.run (M : ShareMemoryModel) : M.State → List ShareMemOp → M.State
  | s, [] => s
  | s, op :: rest => M.run (M.step s op) rest

/-- Post-quarantine secret-key erasure contract (`ct_memzero` before a fault or error return)
    for the memory environment `M`.

    Instances: `shareMemoryModel_contract` (reference map model) and `arenaShareMemoryModel_contract`
    (contiguous byte-arena slot allocator wiped in place by full-arena `ct_memzero`, paired with
    `tooth_off_by_one_memzero_breaks_erasure_contract`). At the ISA level, the wipe routines are
    verified in `Qsag.current_ct_memzero_x86_64_mc_refines` and
    `Qsag.current_ct_memzero_aarch64_mc_refines`. -/
structure KeyErasureContract (M : ShareMemoryModel) : Prop where
  /-- A loaded share is physically present in its slot. -/
  loadStoresShare : ∀ (s : M.State) (slot : Nat) (bytes : Bytes),
    M.residue (M.step s (.load slot bytes)) slot = bytes
  /-- After quarantine, and until a new share is loaded, every byte of every slot is zero:
      the zeroing stores are performed, not eliminated as dead. -/
  quarantineZeroizesShares : ∀ (s : M.State) (tr : List ShareMemOp) (slot : Nat),
    (∀ op ∈ tr, op.isLoad = false) →
    ∀ b ∈ M.residue (M.run (M.step s .quarantine) tr) slot, b = 0

/-- Reference share memory. With `zeroizes = true` quarantine overwrites every slot with zero
    bytes in place; with `zeroizes = false` it leaves memory untouched (the zeroing stores were
    eliminated). -/
def shareMemoryModel (zeroizes : Bool) : ShareMemoryModel where
  State := Nat → Bytes
  step s
    | .load slot bytes => fun i => if i = slot then bytes else s i
    | .use _ => s
    | .quarantine => if zeroizes then fun i => (s i).map (fun _ => 0) else s
  residue s := s

private theorem shareMemory_run_zero :
    ∀ (tr : List ShareMemOp) (s : Nat → Bytes),
      (∀ slot, ∀ b ∈ s slot, b = 0) → (∀ op ∈ tr, op.isLoad = false) →
      ∀ slot, ∀ b ∈ (shareMemoryModel true).run s tr slot, b = 0
  | [], _, hZ, _ => hZ
  | .load sl bs :: _, _, _, hNo => nomatch hNo (.load sl bs) (List.Mem.head _)
  | .use sl :: rest, s, hZ, hNo =>
    shareMemory_run_zero rest s hZ (fun op h => hNo op (List.mem_cons_of_mem _ h))
  | .quarantine :: rest, s, hZ, hNo =>
    shareMemory_run_zero rest (fun i => (s i).map (fun _ => 0))
      (fun slot b hb => by
        obtain ⟨_, _, hEq⟩ := List.mem_map.mp hb
        exact hEq.symm)
      (fun op h => hNo op (List.mem_cons_of_mem _ h))

/-- The zeroizing reference memory satisfies the contract. -/
theorem shareMemoryModel_contract : KeyErasureContract (shareMemoryModel true) where
  loadStoresShare s slot bytes := iteOfPos rfl _ _
  quarantineZeroizesShares s tr slot hNo :=
    shareMemory_run_zero tr (fun i => (s i).map (fun _ => 0))
      (fun slot b hb => by
        obtain ⟨_, _, hEq⟩ := List.mem_map.mp hb
        exact hEq.symm)
      hNo slot

/-- A memory whose quarantine performs no zeroing stores has no contract. -/
theorem elided_zeroization_has_no_erasure_contract :
    ¬ KeyErasureContract (shareMemoryModel false) := by
  intro c
  have h : (1 : UInt8) = 0 :=
    c.quarantineZeroizesShares (fun _ => [1]) [] 0 (fun _ h => nomatch h) 1 (List.Mem.head _)
  exact absurd h (by decide)

/-- Contiguous byte-arena state tracking physical share allocations (`arena`) alongside a
    slot directory `(slot, offset, len)` and quarantine generation counter. -/
structure ArenaShareState where
  arena : Bytes
  dir : List (Nat × Nat × Nat)
  useCount : Nat
  quarantineGen : Nat
  deriving DecidableEq, Repr

/-- Lookup the latest `(offset, len)` slice allocated for `slot`. -/
def arenaLookupSlot : List (Nat × Nat × Nat) → Nat → Option (Nat × Nat)
  | [], _ => none
  | (sl, off, len) :: rest, target =>
    if sl = target then some (off, len) else arenaLookupSlot rest target

/-- Wipe a contiguous byte arena; when `offByOne = true`, stops one byte early (`len - 1`). -/
def wipeByteArena (offByOne : Bool) (arena : Bytes) : Bytes :=
  if offByOne then
    (arena.take (arena.length - 1)).map (fun _ => 0) ++ arena.drop (arena.length - 1)
  else
    arena.map (fun _ => 0)

/-- Concrete contiguous byte-arena `ShareMemoryModel`: `.load` appends `bytes` into `arena` and
    binds `slot` to `(arena.length, bytes.length)`, `.use` increments `useCount`, and `.quarantine`
    wipes `arena` in place via `wipeByteArena`. -/
def arenaShareMemoryModel (offByOne : Bool) : ShareMemoryModel where
  State := ArenaShareState
  step s
    | .load slot bytes =>
      { s with
        arena := s.arena ++ bytes
        dir := (slot, s.arena.length, bytes.length) :: s.dir }
    | .use _ => { s with useCount := s.useCount + 1 }
    | .quarantine =>
      { s with
        arena := wipeByteArena offByOne s.arena
        quarantineGen := s.quarantineGen + 1 }
  residue s slot :=
    match arenaLookupSlot s.dir slot with
    | none => []
    | some (off, len) => (s.arena.drop off).take len

private theorem mem_take_drop_zero :
    ∀ {xs : Bytes}, (∀ b ∈ xs, b = (0 : UInt8)) →
      ∀ (off len : Nat) {b : UInt8}, b ∈ (xs.drop off).take len → b = 0 := by
  intro xs hZ off len b hb
  exact hZ b (List.mem_of_mem_drop (List.mem_of_mem_take hb))

private theorem arenaShare_run_zero :
    ∀ (tr : List ShareMemOp) (s : ArenaShareState),
      (∀ b ∈ s.arena, b = 0) → (∀ op ∈ tr, op.isLoad = false) →
      ∀ b ∈ ((arenaShareMemoryModel false).run s tr).arena, b = 0
  | [], _, hZ, _ => hZ
  | .load sl bs :: _, _, _, hNo => nomatch hNo (.load sl bs) (List.Mem.head _)
  | .use _ :: rest, s, hZ, hNo =>
    arenaShare_run_zero rest { s with useCount := s.useCount + 1 } hZ
      (fun op h => hNo op (List.mem_cons_of_mem _ h))
  | .quarantine :: rest, s, _, hNo =>
    arenaShare_run_zero rest
      { s with arena := wipeByteArena false s.arena, quarantineGen := s.quarantineGen + 1 }
      (fun b hb => by
        obtain ⟨_, _, hEq⟩ := List.mem_map.mp hb
        exact hEq.symm)
      (fun op h => hNo op (List.mem_cons_of_mem _ h))

/-- **Concrete Contiguous Byte-Arena `KeyErasureContract` (`arenaShareMemoryModel_contract`)**:
    Full-length `ct_memzero` over the share arena satisfies `KeyErasureContract` across arbitrary
    multi-slot loads, computations, and post-quarantine event traces. -/
theorem arenaShareMemoryModel_contract : KeyErasureContract (arenaShareMemoryModel false) where
  loadStoresShare s slot bytes := by
    change (match arenaLookupSlot ((slot, s.arena.length, bytes.length) :: s.dir) slot with
      | none => []
      | some (off, len) => ((s.arena ++ bytes).drop off).take len) = bytes
    dsimp only [arenaLookupSlot]
    rw [iteOfPos rfl]
    dsimp only
    rw [List.drop_left, List.take_length]
  quarantineZeroizesShares s tr slot hNo b hb := by
    let sFinal : ArenaShareState :=
      (arenaShareMemoryModel false).run ((arenaShareMemoryModel false).step s .quarantine) tr
    have hZ : ∀ x ∈ sFinal.arena, x = 0 :=
      arenaShare_run_zero tr ((arenaShareMemoryModel false).step s .quarantine)
        (fun x hx => by
          obtain ⟨_, _, hEq⟩ := List.mem_map.mp hx
          exact hEq.symm)
        hNo
    change b ∈ (match arenaLookupSlot sFinal.dir slot with
      | none => []
      | some (off, len) => (sFinal.arena.drop off).take len) at hb
    cases hLook : arenaLookupSlot sFinal.dir slot with
    | none => rw [hLook] at hb; cases hb
    | some pair =>
      rw [hLook] at hb
      exact mem_take_drop_zero hZ pair.1 pair.2 hb

/-- **`#tooth` Off-by-One `ct_memzero` Leaves Residual Key Byte (`tooth_off_by_one_memzero_breaks_erasure_contract`)**:
    If `ct_memzero` wipes `arena.length - 1` bytes instead of `arena.length`, the final byte `0xAA`
    of a loaded 32-byte key share survives `.quarantine` in physical memory, violating
    `KeyErasureContract`! -/
theorem tooth_off_by_one_memzero_breaks_erasure_contract :
    ¬ KeyErasureContract (arenaShareMemoryModel true) := by
  intro c
  let s₀ : ArenaShareState := ⟨[], [], 0, 0⟩
  let share32 : Bytes := List.replicate 31 0x11 ++ [0xAA]
  let s₁ := (arenaShareMemoryModel true).step s₀ (.load 0 share32)
  have hMemAA : (0xAA : UInt8) ∈ (arenaShareMemoryModel true).residue
      ((arenaShareMemoryModel true).run ((arenaShareMemoryModel true).step s₁ .quarantine) []) 0 := by
    decide
  have hZero := c.quarantineZeroizesShares s₁ [] 0 (fun _ h => nomatch h) 0xAA hMemAA
  exact absurd hZero (by decide)

/-! ### 3d. Data-independent timing and SIMT workgroup execution -/

/-- Hardware data-independent timing (`DOIT` / `DIT`) contract. `observe mode op data` is the
    timing observation of executing `op` on operand values `data` with the processor in mode
    `mode`; with the processor in `ExecMode.constantTimeSafe` it does not depend on `data`.

    `Op` is the set of admitted kernel entries, not the instruction set: an ISA has
    instructions whose timing depends on operands in every mode (integer division), so the law
    is satisfiable only for entries restricted to the data-independent subset.

    The contract says nothing about which mode the processor is in. That the kernels run with
    `DIT` / `DOITM` set and clean SIMD upper halves is a hardware and operating-system
    assumption; every consequence below takes the mode as a hypothesis, and
    `dit_contract_silent_outside_safe_mode` shows that a contract constrains no other mode.
    The `speculationFence` bit of `ExecMode` is part of the safe mode but no leakage model of
    `Machine.ConstantTimeIsa` reads it: nothing here is a statement about transient execution.

    Instances: `Qsag.ConstantTimeIsa.armDitContract`, `x86DitContract`
    (`Machine.PlatformContractInstances`). -/
structure DitHardwareContract (Op Data Obs : Type) where
  observe : ExecMode → Op → Data → Obs
  dataIndependent : ∀ (op : Op) (d₁ d₂ : Data),
    observe ExecMode.constantTimeSafe op d₁ = observe ExecMode.constantTimeSafe op d₂

/-- The safe mode has `DIT` enabled, clean SIMD upper halves and the speculation fence. -/
theorem ExecMode.constantTimeSafe_flags :
    ExecMode.constantTimeSafe.ditEnabled = true ∧
    ExecMode.constantTimeSafe.cleanSimdUpper = true ∧
    ExecMode.constantTimeSafe.speculationFence = true :=
  ⟨rfl, rfl, rfl⟩

/-- If the processor is in the safe mode, two executions of the same sequence of kernel entries
    on different operand values produce the same timing trace. -/
theorem DitHardwareContract.trace_data_independent {Op Data Obs : Type}
    (c : DitHardwareContract Op Data Obs) (mode : ExecMode)
    (hMode : mode = ExecMode.constantTimeSafe) :
    ∀ (tr₁ tr₂ : List (Op × Data)), tr₁.map Prod.fst = tr₂.map Prod.fst →
      tr₁.map (fun e => c.observe mode e.1 e.2) = tr₂.map (fun e => c.observe mode e.1 e.2)
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | (op₁, d₁) :: r₁, (op₂, d₂) :: r₂, h => by
    have hOp : op₁ = op₂ := List.head_eq_of_cons_eq h
    have hTail : r₁.map Prod.fst = r₂.map Prod.fst := List.tail_eq_of_cons_eq h
    have ih := c.trace_data_independent mode hMode r₁ r₂ hTail
    show c.observe mode op₁ d₁ :: r₁.map (fun e => c.observe mode e.1 e.2) =
      c.observe mode op₂ d₂ :: r₂.map (fun e => c.observe mode e.1 e.2)
    rw [ih, hOp, hMode, c.dataIndependent op₂ d₁ d₂]

/-- An execution unit whose timing reveals its operand has no contract. -/
theorem operand_timed_unit_has_no_dit_contract :
    ¬ ∃ c : DitHardwareContract Unit Nat Nat, c.observe = fun _ _ d => d := by
  rintro ⟨c, hObs⟩
  have h := c.dataIndependent () 0 1
  rw [hObs] at h
  exact absurd h (by decide)

/-- A contract constrains the safe mode only: the unit that is silent with `DIT` enabled and
    reveals its operand otherwise has a contract, and leaks with `DIT` disabled. -/
theorem dit_contract_silent_outside_safe_mode :
    ∃ c : DitHardwareContract Unit Nat Nat,
      ¬ (c.observe { ExecMode.constantTimeSafe with ditEnabled := false } () 0 =
         c.observe { ExecMode.constantTimeSafe with ditEnabled := false } () 1) :=
  ⟨{ observe := fun mode _ d => if mode.ditEnabled then 0 else d
     dataIndependent := fun _ _ _ => rfl }, by decide⟩

/-- GPU SIMT workgroup execution of one barrier epoch of a SPIR-V batch-verification / NTT
    kernel: the subgroup and workgroup sizes, the basic-block trace of every invocation, and
    the storage cells every invocation writes and reads during the epoch. The subgroup size
    divides the workgroup size.

    The contract is per barrier epoch. A kernel with `OpControlBarrier`s is a sequence of
    epochs, each with its own contract; the access sets of different epochs are not compared,
    since a barrier orders them. -/
structure SimtWorkgroupContract where
  subgroupSize : Nat
  workgroupSize : Nat
  blockTrace : Nat → List Nat
  writeSet : Nat → List Nat
  readSet : Nat → List Nat
  h_divides : 0 < subgroupSize ∧ subgroupSize ∣ workgroupSize

theorem SimtWorkgroupContract.h_subgroup_pos (c : SimtWorkgroupContract) : 0 < c.subgroupSize :=
  c.h_divides.1

/-- Uniform control flow: invocations of one subgroup execute the same basic blocks. -/
@[expose] def SimtWorkgroupContract.UniformControlFlow (c : SimtWorkgroupContract) : Prop :=
  ∀ i j : Nat, i < c.workgroupSize → j < c.workgroupSize →
    i / c.subgroupSize = j / c.subgroupSize → c.blockTrace i = c.blockTrace j

/-- Disjoint storage bindings: a storage cell written by an invocation is neither written nor
    read by any other invocation in the epoch (`W(i) ∩ (W(j) ∪ R(j)) = ∅` for `i ≠ j`). This is
    the data-race-freedom condition under which the schedule of an epoch does not matter. -/
@[expose] def SimtWorkgroupContract.DisjointStorageBindings (c : SimtWorkgroupContract) : Prop :=
  ∀ i j : Nat, i < c.workgroupSize → j < c.workgroupSize → i ≠ j →
    ∀ cell ∈ c.writeSet i, cell ∉ c.writeSet j ∧ cell ∉ c.readSet j

/-- Well-formed SIMT execution of an epoch: divisibility of the sizes together with both
    safety properties of the execution.

    Instances: `Qsag.simtEpochContract_wellFormed_of_ownerCheck`,
    `Qsag.faial_disjointStorageBindings` (`Machine.PlatformContractInstances`). -/
structure WellFormedSimtContract (c : SimtWorkgroupContract) : Prop where
  h_divides : 0 < c.subgroupSize ∧ c.subgroupSize ∣ c.workgroupSize
  uniformControlFlow : c.UniformControlFlow
  disjointStorageBindings : c.DisjointStorageBindings

/-- The subgroups tile the workgroup exactly. -/
theorem SimtWorkgroupContract.subgroups_tile (c : SimtWorkgroupContract) :
    c.workgroupSize / c.subgroupSize * c.subgroupSize = c.workgroupSize := by
  obtain ⟨k, hk⟩ := c.h_divides.2
  rw [hk, Nat.mul_div_cancel_left k c.h_divides.1, Nat.mul_comm]

/-- Every invocation executes the basic blocks of the first invocation of its subgroup. -/
theorem WellFormedSimtContract.subgroup_leader_trace {c : SimtWorkgroupContract}
    (w : WellFormedSimtContract c) (i : Nat) (hi : i < c.workgroupSize) :
    c.blockTrace i = c.blockTrace (i / c.subgroupSize * c.subgroupSize) :=
  w.uniformControlFlow i (i / c.subgroupSize * c.subgroupSize) hi
    (Nat.lt_of_le_of_lt (Nat.div_mul_le_self i c.subgroupSize) hi)
    (Nat.mul_div_cancel _ w.h_divides.1).symm

/-- A storage cell written inside a well-formed epoch has a unique writer. -/
theorem WellFormedSimtContract.write_race_free {c : SimtWorkgroupContract}
    (w : WellFormedSimtContract c) (i j cell : Nat)
    (hi : i < c.workgroupSize) (hj : j < c.workgroupSize)
    (hci : cell ∈ c.writeSet i) (hcj : cell ∈ c.writeSet j) : i = j :=
  match Nat.decEq i j with
  | .isTrue h => h
  | .isFalse h => absurd hcj (w.disjointStorageBindings i j hi hj h cell hci).1

/-- A storage cell written inside a well-formed epoch is read only by its writer. -/
theorem WellFormedSimtContract.read_write_race_free {c : SimtWorkgroupContract}
    (w : WellFormedSimtContract c) (i j cell : Nat)
    (hi : i < c.workgroupSize) (hj : j < c.workgroupSize)
    (hci : cell ∈ c.writeSet i) (hcj : cell ∈ c.readSet j) : i = j :=
  match Nat.decEq i j with
  | .isTrue h => h
  | .isFalse h => absurd hcj (w.disjointStorageBindings i j hi hj h cell hci).2

/-- Subgroup size `32` with workgroup size `33` is not a SIMT contract. -/
theorem simt_subgroup32_workgroup33_rejected :
    ¬ ∃ c : SimtWorkgroupContract, c.subgroupSize = 32 ∧ c.workgroupSize = 33 := by
  rintro ⟨c, h32, h33⟩
  obtain ⟨k, hk⟩ := c.h_divides.2
  rw [h32, h33] at hk
  omega

/-- Two invocations writing the same cell. -/
def racingSimtContract : SimtWorkgroupContract where
  subgroupSize := 1
  workgroupSize := 2
  blockTrace _ := []
  writeSet _ := [0]
  readSet _ := []
  h_divides := ⟨Nat.one_pos, ⟨2, rfl⟩⟩

/-- A workgroup with a write race is not well formed, whatever its sizes. -/
theorem racing_simt_not_wellFormed : ¬ WellFormedSimtContract racingSimtContract := by
  intro w
  exact absurd (w.write_race_free 0 1 0 (by decide) (by decide) (List.Mem.head _) (List.Mem.head _))
    (by decide)

/-- Invocation `0` writes cell `0`, invocation `1` reads it: disjoint writes, one read/write
    race. -/
def readRacingSimtContract : SimtWorkgroupContract where
  subgroupSize := 1
  workgroupSize := 2
  blockTrace _ := []
  writeSet i := if i = 0 then [0] else []
  readSet i := if i = 1 then [0] else []
  h_divides := ⟨Nat.one_pos, ⟨2, rfl⟩⟩

/-- A workgroup in which one invocation reads a cell another writes in the same epoch is not
    well formed, although no cell has two writers. -/
theorem read_racing_simt_not_wellFormed : ¬ WellFormedSimtContract readRacingSimtContract := by
  intro w
  exact absurd (w.read_write_race_free 0 1 0 (by decide) (by decide) (List.Mem.head _)
    (List.Mem.head _)) (by decide)

#tooth_pair PosixFsyncContract.committed_survives vs fsync_rollback_volume_has_no_contract
#tooth_pair checkedChannel_contract vs open_relay_has_no_channel_contract
#tooth_pair shareMemoryModel_contract vs elided_zeroization_has_no_erasure_contract
#tooth_pair DitHardwareContract.trace_data_independent vs operand_timed_unit_has_no_dit_contract
#tooth_pair SimtWorkgroupContract.subgroups_tile vs simt_subgroup32_workgroup33_rejected
#tooth_pair WellFormedSimtContract.write_race_free vs racing_simt_not_wellFormed
#tooth_pair WellFormedSimtContract.read_write_race_free vs read_racing_simt_not_wellFormed
#tooth_pair PosixFsyncContract.anchor_excludes_stale_snapshot vs fsyncJournal_commit_flushes_pending_rename
#tooth_pair checkedChannel_contract vs empty_network_has_no_channel_contract

#verify_constructive
  Qsag.Spec.SecondPreimage.toCollision_collides
  Qsag.Spec.FramedCodec.collisionOfDigestEq_sound
  Qsag.Spec.FinGame.ext_win
  Qsag.Spec.Code.play_invariant
  Qsag.Spec.smDtTcrOracle_inv
  Qsag.Spec.smDtPreOracle_inv
  Qsag.Spec.smDtTcrRun_inv
  Qsag.Spec.smDtPreRun_inv
  Qsag.Spec.smDtTcrGame_win_sound
  Qsag.Spec.smDtPreGame_win_sound
  Qsag.Spec.itsrGame_win_sound
  Qsag.Spec.itsrRun_log_length_le
  Qsag.Spec.prfGames_agree_of_fun_eq
  Qsag.Spec.moduleSisGame_win_sound
  Qsag.Spec.FinGame.not_bound_of_forall_win
  Qsag.Spec.FinGame.bound_zero_of_forall_lose
  Qsag.Spec.FinGame.winProb_le_one
  Qsag.Spec.advDist_not_bound_of_always_never
  Qsag.Spec.CoinSplit.chal_free
  Qsag.Spec.prodCoin_right_pos
  Qsag.Spec.prodCoin_quot_lt
  Qsag.Spec.prodCoin_pair_lt
  Qsag.Spec.prodCoin_pair_quot
  Qsag.Spec.prodCoin_pair_rem
  Qsag.Spec.uniformOn_unique
  Qsag.Spec.constant_sampler_not_uniform
  Qsag.Spec.CoinSplit.sample_not_adversary_determined
  Qsag.Spec.SmDtTcrHard.mono
  Qsag.Spec.SmDtPreHard.mono
  Qsag.Spec.ItsrHard.mono
  Qsag.Spec.smDtTcrHard_one
  Qsag.Spec.decisionRlweHard_zero_samples
  Qsag.Spec.regularDualLpnHard_noRows
  Qsag.Spec.regularNoise_example
  Qsag.Spec.regularNoise_not_implied_by_weight
  Qsag.Spec.hashSig_forger_bound
  Qsag.Spec.smDtTcrHard_constHash_refuted
  Qsag.Spec.uniformOn_emptyBytes
  Qsag.Spec.smDtTcrHard_constHash_refuted_seedless
  Qsag.Spec.smDtPreHard_constHash_refuted
  Qsag.Spec.itsrHard_emptySelector_refuted
  Qsag.Spec.prfHard_emptyOutput_refuted
  Qsag.Spec.moduleSisHard_noRows_refuted
  Qsag.Spec.smDtTcr_constHash_adversary_wins
  Qsag.Spec.smDtTcr_committed_message_loses
  Qsag.Spec.itsr_answered_pair_loses
  Qsag.Spec.prf_real_ideal_games_differ
  Qsag.Spec.rqMul_negacyclic_wraparound
  Qsag.Spec.moduleSis_zero_vector_loses
  Qsag.Spec.FsyncStorageModel.run_append
  Qsag.Spec.PosixFsyncContract.committed_survives
  Qsag.Spec.PosixFsyncContract.anchor_excludes_stale_snapshot
  Qsag.Spec.fsyncJournalModel_contract
  Qsag.Spec.fsync_rollback_volume_has_no_contract
  Qsag.Spec.fsyncJournal_commit_flushes_pending_rename
  Qsag.Spec.checkedChannel_contract
  Qsag.Spec.open_relay_has_no_channel_contract
  Qsag.Spec.empty_network_has_no_channel_contract
  Qsag.Spec.shareMemoryModel_contract
  Qsag.Spec.elided_zeroization_has_no_erasure_contract
  Qsag.Spec.arenaShareMemoryModel_contract
  Qsag.Spec.tooth_off_by_one_memzero_breaks_erasure_contract
  Qsag.Spec.ExecMode.constantTimeSafe_flags
  Qsag.Spec.dit_contract_silent_outside_safe_mode
  Qsag.Spec.DitHardwareContract.trace_data_independent
  Qsag.Spec.operand_timed_unit_has_no_dit_contract
  Qsag.Spec.SimtWorkgroupContract.subgroups_tile
  Qsag.Spec.WellFormedSimtContract.subgroup_leader_trace
  Qsag.Spec.WellFormedSimtContract.write_race_free
  Qsag.Spec.simt_subgroup32_workgroup33_rejected
  Qsag.Spec.racing_simt_not_wellFormed
  Qsag.Spec.WellFormedSimtContract.read_write_race_free
  Qsag.Spec.read_racing_simt_not_wellFormed
  Qsag.Spec.iteOfPos
  Qsag.Spec.iteOfNeg
  Qsag.Spec.andTrueSplit
  Qsag.Spec.Code.play_ret
  Qsag.Spec.Code.play_call
  Qsag.Spec.targetInv_extend
  Qsag.Spec.SmDtTcrHard.anti
  Qsag.Spec.SmDtPreHard.anti
  Qsag.Spec.smDtPreHard_emptyClass
  Qsag.Spec.constHashTcr_play
  Qsag.Spec.constHashPre_play
  Qsag.Spec.emptyOutputDistinguisher_play
  Qsag.Spec.mem_allByteStrings
  Qsag.Spec.firstByteString_spec
  Qsag.Spec.preimageSearch_play
  Qsag.Spec.getD_zero_mem
  Qsag.Spec.smDtPreHard_preimageSearch_refuted
  Qsag.Spec.smDtPreHard_unrestricted_refuted
  Qsag.Spec.smDtPreHard_unrestricted_refuted_trivialSizes
  Qsag.Spec.fsyncJournalRename_facts
  Qsag.Spec.fsyncJournalStep_prefix
  Qsag.Spec.fsyncJournalStep_anchor
  Qsag.Spec.fsyncJournalStep_anchor_le
  Qsag.Spec.fsyncJournal_run_prefix
  Qsag.Spec.fsyncJournal_run_anchor
  Qsag.Spec.fsyncJournal_run_anchor_le
  Qsag.Spec.channelRun_delivered_absent
  Qsag.Spec.channelRun_no_replay
  Qsag.Spec.channelRun_authentic
  Qsag.Spec.channelRun_honest
  Qsag.Spec.shareMemory_run_zero
  Qsag.Spec.SimtWorkgroupContract.h_subgroup_pos
  Qsag.Spec.CoinSplit.card_eq
  Qsag.Spec.CoinSplit.sampleSum_eq
  Qsag.Spec.UniformOn.card_and_sampleSum_eq
  Qsag.Spec.lazyRomStep_mem
  Qsag.Spec.lazyRomStep_preserves_mem
  Qsag.Spec.lazyRomRun_bad_bound
  Qsag.Spec.withFinalRoCheck_within
  Qsag.Spec.withFinalRoCheck_mem
  Qsag.Spec.romSmDtTcr_within_bound
  Qsag.Spec.romSmDtPre_within_bound
  Qsag.Spec.romItsr_within_bound
  Qsag.Spec.romItsrTuple_within_bound
  Qsag.Spec.tooth_romSmDtTcr_without_within
  Qsag.Spec.tooth_romSmDtPre_without_within
  Qsag.Spec.tooth_romItsr_without_within
  Qsag.Spec.uniformOn_byte1Seed
  Qsag.Spec.uniformOn_byte1Pre
  Qsag.Spec.uniformOn_byte1Itsr
  Qsag.Spec.boundedPreAdv_mem_within
  Qsag.Spec.byteXorHash_smDtPreHard_within
  Qsag.Spec.boundedItsrAdv_mem_within
  Qsag.Spec.byteIdxHmsg_itsrHard_within
  Qsag.Spec.byteIdxHmsg_itsrHard_refuted
  Qsag.Spec.boundedTcrAdv_mem_within
  Qsag.Spec.poly257Hash_smDtTcrHard_within
  Qsag.Spec.poly257Hash_smDtTcrHard_refuted
  Qsag.Spec.uniformOn_byte1SeedAndPre
  Qsag.Spec.poly257Hash_smDtPreHard_within

-- Equation used by `Tests/CredentialsTeeth`; no body is exposed.
#export_eqns honestChannelRun

end Qsag.Spec
end
