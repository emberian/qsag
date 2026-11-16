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

/-- Union bound over three reduction events with proved bounds:
    `Pr[G] ≤ ε₁ + ε₂ + ε₃` when every win of `G` is a win of `R₁`, `R₂` or `R₃`. -/
theorem event_le_three_reductions {n : Nat} (G R₁ R₂ R₃ : FinGame n) {ε₁ ε₂ ε₃ : RatBound}
    (hExtract : ∀ ω : Fin n, G.win ω = true →
      R₁.win ω = true ∨ R₂.win ω = true ∨ R₃.win ω = true)
    (h₁ : GameBound R₁.winProb ε₁) (h₂ : GameBound R₂.winProb ε₂)
    (h₃ : GameBound R₃.winProb ε₃) :
    GameBound G.winProb ((ε₁.add ε₂).add ε₃) := by
  let r23 : FinGame n :=
    { samplePos := R₂.samplePos
      win := fun ω => R₂.win ω || R₃.win ω }
  have hA : GameBound G.winProb (R₁.winProb.add r23.winProb) := by
    apply event_le_two_reductions G R₁ r23
    intro ω hw
    rcases hExtract ω hw with hI | hT | hP
    · exact .inl hI
    · exact .inr (by dsimp only [r23]; rw [hT]; rfl)
    · exact .inr (by dsimp only [r23]; rw [hP, Bool.or_true])
  have hB : GameBound r23.winProb (R₂.winProb.add R₃.winProb) := by
    apply event_le_two_reductions r23 R₂ R₃
    intro ω hw
    dsimp only [r23] at hw
    cases ht : R₂.win ω
    · rw [ht, Bool.false_or] at hw
      exact .inr hw
    · exact .inl rfl
  have hBBound : r23.winProb.le (ε₂.add ε₃) :=
    RatBound.le_trans hB (RatBound.add_le_add h₂ h₃)
  have hTotal : (R₁.winProb.add r23.winProb).le (ε₁.add (ε₂.add ε₃)) :=
    RatBound.add_le_add h₁ hBBound
  have hAssoc : (ε₁.add (ε₂.add ε₃)).le ((ε₁.add ε₂).add ε₃) := by
    unfold RatBound.le RatBound.add
    dsimp only
    have hEq :
        (ε₁.num * (ε₂.den * ε₃.den) + (ε₂.num * ε₃.den + ε₃.num * ε₂.den) * ε₁.den) *
          (ε₁.den * ε₂.den * ε₃.den) =
        ((ε₁.num * ε₂.den + ε₂.num * ε₁.den) * ε₃.den + ε₃.num * (ε₁.den * ε₂.den)) *
          (ε₁.den * (ε₂.den * ε₃.den)) := by
      have hDen : ε₁.den * ε₂.den * ε₃.den = ε₁.den * (ε₂.den * ε₃.den) := Nat.mul_assoc _ _ _
      rw [hDen]
      apply congrArg (· * (ε₁.den * (ε₂.den * ε₃.den)))
      simp only [Nat.left_distrib, Nat.mul_left_comm, Nat.mul_comm, Nat.add_assoc]
    rw [hEq]
    exact Nat.le_refl _
  exact RatBound.le_trans hA (RatBound.le_trans hTotal hAssoc)

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
@[expose] def byteOracleIface : Iface where
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
@[expose] def targetIface : Iface where
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

    No instance exists in this library; `checkedChannel_contract` is a reference model only.
    The one network model of the execution layer (`RssParticipant.networkStep`) allows
    re-delivery and leaves replay handling to the receiving node, so it does not satisfy
    `replayProtected`. -/
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

    No instance exists in this library; `shareMemoryModel_contract` is a reference model only.
    The execution layer models erasure logically (`shareSlot := none`), and the machine layer
    has one refinement theorem per wipe routine (`Qsag.ct_memzero_x86_64_mc_refines`,
    `Qsag.ct_memzero_aarch64_mc_refines`); neither is a `ShareMemoryModel` with a physical
    residue across a quarantine event. -/
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
  Qsag.Spec.event_le_three_reductions
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

end Qsag.Spec
end
