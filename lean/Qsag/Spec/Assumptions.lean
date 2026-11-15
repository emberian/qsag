module
/-
# Qsag.Spec.Assumptions — Cryptographic Experiments, Oracle-Model Locales, and Platform Contracts

Assumption records (`structure`s, zero `axiom` declarations) for every cryptographic hardness
premise, idealized oracle model, and operating-system / hardware platform contract referenced by
top-level security theorems.

* A hardness locale is indexed by its primitive, the challenger's samplers, the adversary and the
  enforced resource bound; its game is constructed from those objects (`smDtTcrGame`,
  `smDtPreGame`, `itsrGame`, `prfRealGame` / `prfIdealGame`, the Ring-LWE, Module-SIS and
  dual-LPN games).
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

Every hardness locale below is indexed by the primitive, the challenger's coin-indexed samplers,
the adversary and the resource bound the challenger enforces. Its game is the function of those
objects defined here; a locale has no free `FinGame` field. A locale records a proved bound on
the success of one adversary in one experiment, which is the form a concrete reduction consumes.

The coin `ω : Fin n` indexes both the challenger's samples and the adversary's randomness. The
samplers are explicit fields, so a consumer can see what the adversary's coin dependence is
measured against; uniformity of a sampler is not expressible over a bare `Fin n` and is not
claimed. -/

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

/-! ### 2e. Hardness locales: a proved bound for one adversary in one experiment -/

/-- Multi-target, distinct-tweak target-collision resistance (`SM-DT-TCR`) of the tweakable
    hash `th`: the adversary `adv` wins `smDtTcrGame` with probability at most `εTcr` when the
    challenger admits `qSign` targets. -/
structure SmDtTcrAssumption (n : Nat) where
  samplePos : 0 < n
  th : Bytes → Bytes → Bytes → Bytes
  seed : Fin n → Bytes
  qSign : Nat
  adv : Fin n → Code targetIface TargetBreak
  εTcr : RatBound
  bound : GameBound (smDtTcrGame samplePos th qSign seed adv).winProb εTcr

/-- The `SM-DT-TCR` game of the locale. -/
def SmDtTcrAssumption.tcrGame {n : Nat} (A : SmDtTcrAssumption n) : FinGame n :=
  smDtTcrGame A.samplePos A.th A.qSign A.seed A.adv

theorem SmDtTcrAssumption.tcrGame_eq {n : Nat} (A : SmDtTcrAssumption n) :
    A.tcrGame = smDtTcrGame A.samplePos A.th A.qSign A.seed A.adv := by rfl

theorem SmDtTcrAssumption.tcrGame_bound {n : Nat} (A : SmDtTcrAssumption n) :
    GameBound A.tcrGame.winProb A.εTcr := A.bound

/-- Multi-target, distinct-tweak preimage resistance (`SM-DT-PRE`) of `th`. -/
structure SmDtPreAssumption (n : Nat) where
  samplePos : 0 < n
  th : Bytes → Bytes → Bytes → Bytes
  seed : Fin n → Bytes
  hidden : Fin n → Nat → Bytes
  qSign : Nat
  adv : Fin n → Code targetIface TargetBreak
  εPre : RatBound
  bound : GameBound (smDtPreGame samplePos th qSign seed hidden adv).winProb εPre

/-- The `SM-DT-PRE` game of the locale. -/
def SmDtPreAssumption.preGame {n : Nat} (A : SmDtPreAssumption n) : FinGame n :=
  smDtPreGame A.samplePos A.th A.qSign A.seed A.hidden A.adv

theorem SmDtPreAssumption.preGame_eq {n : Nat} (A : SmDtPreAssumption n) :
    A.preGame = smDtPreGame A.samplePos A.th A.qSign A.seed A.hidden A.adv := by rfl

theorem SmDtPreAssumption.preGame_bound {n : Nat} (A : SmDtPreAssumption n) :
    GameBound A.preGame.winProb A.εPre := A.bound

/-- Interleaved target subset resilience (`ITSR`) of the keyed subset hash `hmsg` used for
    FORS / TSW message hashing. -/
structure ItsrAssumption (n : Nat) where
  samplePos : 0 < n
  hmsg : Bytes → Bytes → List Nat
  rand : Fin n → Nat → Bytes
  qSign : Nat
  adv : Fin n → Code byteOracleIface (Bytes × Bytes)
  εItsr : RatBound
  bound : GameBound (itsrGame samplePos hmsg qSign rand adv).winProb εItsr

/-- The `ITSR` game of the locale. -/
def ItsrAssumption.itsrGame {n : Nat} (A : ItsrAssumption n) : FinGame n :=
  Qsag.Spec.itsrGame A.samplePos A.hmsg A.qSign A.rand A.adv

theorem ItsrAssumption.itsrGame_eq {n : Nat} (A : ItsrAssumption n) :
    A.itsrGame = Qsag.Spec.itsrGame A.samplePos A.hmsg A.qSign A.rand A.adv := by rfl

theorem ItsrAssumption.itsrGame_bound {n : Nat} (A : ItsrAssumption n) :
    GameBound A.itsrGame.winProb A.εItsr := A.bound

/-- Keyed pseudorandom function (`PRF`) distinguishing locale (PRSS and key generation): the
    distinguisher `adv` separates `prf (key ω)` from the sampled function `rf ω` with advantage
    at most `εPrf` in `qPrf` queries. -/
structure KeyedPrfAssumption (n : Nat) where
  samplePos : 0 < n
  prf : Bytes → Bytes → Bytes
  key : Fin n → Bytes
  rf : Fin n → Bytes → Bytes
  qPrf : Nat
  adv : Fin n → Code byteOracleIface Bool
  εPrf : RatBound
  bound : GameBound
    (AdvDist (prfRealGame samplePos prf qPrf key adv) (prfIdealGame samplePos qPrf rf adv)) εPrf

/-- The real game of the PRF locale. -/
def KeyedPrfAssumption.realGame {n : Nat} (P : KeyedPrfAssumption n) : FinGame n :=
  prfRealGame P.samplePos P.prf P.qPrf P.key P.adv

/-- The ideal game of the PRF locale. -/
def KeyedPrfAssumption.idealGame {n : Nat} (P : KeyedPrfAssumption n) : FinGame n :=
  prfIdealGame P.samplePos P.qPrf P.rf P.adv

theorem KeyedPrfAssumption.realGame_eq {n : Nat} (P : KeyedPrfAssumption n) :
    P.realGame = prfRealGame P.samplePos P.prf P.qPrf P.key P.adv := by rfl

theorem KeyedPrfAssumption.idealGame_eq {n : Nat} (P : KeyedPrfAssumption n) :
    P.idealGame = prfIdealGame P.samplePos P.qPrf P.rf P.adv := by rfl

theorem KeyedPrfAssumption.advantage_bound {n : Nat} (P : KeyedPrfAssumption n) :
    GameBound (AdvDist P.realGame P.idealGame) P.εPrf := P.bound

/-- Decision Ring-LWE locale over `ℤ_modulus[X]/(X^ringDim + 1)` with `samples` samples and
    secret and error of centered absolute value at most `errBound`. -/
structure DecisionRlweAssumption (n : Nat) where
  samplePos : 0 < n
  ringDim : Nat
  modulus : Nat
  samples : Nat
  errBound : Nat
  a : Fin n → Nat → List Nat
  s : Fin n → List Nat
  e : Fin n → Nat → List Nat
  u : Fin n → Nat → List Nat
  dist : Fin n → List (List Nat × List Nat) → Bool
  h_params : 0 < ringDim ∧ 2 ≤ modulus
  h_secret : ∀ ω : Fin n, rqShortOk ringDim modulus errBound (s ω) = true
  h_samples : ∀ (ω : Fin n) (i : Nat), i < samples →
    rqPolyOk ringDim modulus (a ω i) = true ∧
    rqShortOk ringDim modulus errBound (e ω i) = true ∧
    rqPolyOk ringDim modulus (u ω i) = true
  εRlwe : RatBound
  bound : GameBound
    (AdvDist
      (FinGame.mk samplePos
        (fun ω => dist ω (rlweRealSamples ringDim modulus samples (a ω) (s ω) (e ω))))
      (FinGame.mk samplePos (fun ω => dist ω (rlweUniformSamples samples (a ω) (u ω)))))
    εRlwe

/-- The real game of the Ring-LWE locale: the distinguisher sees `(aᵢ, aᵢ · s + eᵢ)`. -/
def DecisionRlweAssumption.rlweReal {n : Nat} (A : DecisionRlweAssumption n) : FinGame n :=
  ⟨A.samplePos, fun ω =>
    A.dist ω (rlweRealSamples A.ringDim A.modulus A.samples (A.a ω) (A.s ω) (A.e ω))⟩

/-- The ideal game of the Ring-LWE locale: the distinguisher sees `(aᵢ, uᵢ)`. -/
def DecisionRlweAssumption.rlweUniform {n : Nat} (A : DecisionRlweAssumption n) : FinGame n :=
  ⟨A.samplePos, fun ω => A.dist ω (rlweUniformSamples A.samples (A.a ω) (A.u ω))⟩

theorem DecisionRlweAssumption.advantage_bound {n : Nat} (A : DecisionRlweAssumption n) :
    GameBound (AdvDist A.rlweReal A.rlweUniform) A.εRlwe := A.bound

/-- Module-SIS locale over `ℤ_modulus[X]/(X^ringDim + 1)` for a `rows × cols` matrix and
    infinity-norm bound `betaInf`. -/
structure ModuleSisAssumption (n : Nat) where
  samplePos : 0 < n
  ringDim : Nat
  modulus : Nat
  rows : Nat
  cols : Nat
  betaInf : Nat
  matrix : Fin n → List (List (List Nat))
  adv : Fin n → List (List (List Nat)) → List (List Nat)
  h_params : 0 < ringDim ∧ 2 ≤ modulus
  h_matrix : ∀ ω : Fin n, (matrix ω).length = rows ∧
    ∀ row ∈ matrix ω, row.length = cols ∧ ∀ p ∈ row, rqPolyOk ringDim modulus p = true
  εSis : RatBound
  bound : GameBound (moduleSisGame samplePos ringDim modulus cols betaInf matrix adv).winProb εSis

/-- The Module-SIS game of the locale. -/
def ModuleSisAssumption.sisGame {n : Nat} (A : ModuleSisAssumption n) : FinGame n :=
  moduleSisGame A.samplePos A.ringDim A.modulus A.cols A.betaInf A.matrix A.adv

theorem ModuleSisAssumption.sisGame_eq {n : Nat} (A : ModuleSisAssumption n) :
    A.sisGame = moduleSisGame A.samplePos A.ringDim A.modulus A.cols A.betaInf A.matrix A.adv := by
  rfl

theorem ModuleSisAssumption.sisGame_bound {n : Nat} (A : ModuleSisAssumption n) :
    GameBound A.sisGame.winProb A.εSis := A.bound

/-- Dual-LPN locale for silent VOLE / PCG expansion: parity-check matrix with `syndromeDim`
    rows over `𝔽₂^ambientDim` and noise of Hamming weight `rowWeight`. -/
structure DualLpnAssumption (n : Nat) where
  samplePos : 0 < n
  ambientDim : Nat
  syndromeDim : Nat
  rowWeight : Nat
  parity : Fin n → List (List Bool)
  noise : Fin n → List Bool
  uniform : Fin n → List Bool
  dist : Fin n → List (List Bool) × List Bool → Bool
  h_shape : ∀ ω : Fin n,
    dualLpnShapeOk ambientDim syndromeDim rowWeight (parity ω) (noise ω) (uniform ω) = true
  εLpn : RatBound
  bound : GameBound
    (AdvDist
      (FinGame.mk samplePos (fun ω => dist ω (parity ω, lpnSyndrome (parity ω) (noise ω))))
      (FinGame.mk samplePos (fun ω => dist ω (parity ω, uniform ω))))
    εLpn

/-- The real game of the dual-LPN locale: the distinguisher sees `(H, H · e)`. -/
def DualLpnAssumption.lpnReal {n : Nat} (A : DualLpnAssumption n) : FinGame n :=
  ⟨A.samplePos, fun ω => A.dist ω (A.parity ω, lpnSyndrome (A.parity ω) (A.noise ω))⟩

/-- The ideal game of the dual-LPN locale: the distinguisher sees `(H, u)`. -/
def DualLpnAssumption.lpnUniform {n : Nat} (A : DualLpnAssumption n) : FinGame n :=
  ⟨A.samplePos, fun ω => A.dist ω (A.parity ω, A.uniform ω)⟩

theorem DualLpnAssumption.advantage_bound {n : Nat} (A : DualLpnAssumption n) :
    GameBound (AdvDist A.lpnReal A.lpnUniform) A.εLpn := A.bound

/-- Composed standard-model hash-signature assumption bundle (`ITSR + SM-DT-TCR + SM-DT-PRE`). -/
structure HashSigAssumptions (n : Nat) where
  itsr : ItsrAssumption n
  tcr : SmDtTcrAssumption n
  pre : SmDtPreAssumption n

/-- Combined rational upper bound `εItsr + εTcr + εPre` for `HashSigAssumptions`. -/
@[expose] def HashSigAssumptions.totalBound {n : Nat} (A : HashSigAssumptions n) : RatBound :=
  (A.itsr.εItsr.add A.tcr.εTcr).add A.pre.εPre

/-- A forger every one of whose winning coins is a winning coin of the `ITSR`, `SM-DT-TCR` or
    `SM-DT-PRE` experiment of the bundle wins with probability at most `εItsr + εTcr + εPre`. -/
theorem HashSigAssumptions.forger_bound {n : Nat} (A : HashSigAssumptions n)
    (forger : FinGame n)
    (hExtract : ∀ ω : Fin n, forger.win ω = true →
      A.itsr.itsrGame.win ω = true ∨
      A.tcr.tcrGame.win ω = true ∨
      A.pre.preGame.win ω = true) :
    GameBound forger.winProb A.totalBound :=
  event_le_three_reductions forger A.itsr.itsrGame A.tcr.tcrGame A.pre.preGame hExtract
    A.itsr.itsrGame_bound A.tcr.tcrGame_bound A.pre.preGame_bound

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

/-! ## 3. Idealized Oracle-Model Locales (ROM / Ideal Permutation / Compressed QROM) -/

/-- Classical lazy random-oracle model locale tracking digest bit-width `digestBits` and
    adversarial query budget `qRo`. -/
structure RandomOracleModel where
  digestBits : Nat
  qRo : Nat
  h_width : 256 ≤ digestBits

/-- Ideal public-permutation / sponge model locale tracking state width `stateBits`,
    capacity `capacityBits`, and permutation query budget `qPerm`. -/
structure IdealPermutationModel where
  stateBits : Nat
  capacityBits : Nat
  qPerm : Nat
  h_cap : 256 ≤ capacityBits ∧ capacityBits ≤ stateBits

/-- Zhandry compressed quantum random-oracle model (`QROM`) locale tracking digest width `digestBits`
    and superposition query budget `qQuantum`. -/
structure CompressedQromModel where
  digestBits : Nat
  qQuantum : Nat
  h_width : 256 ≤ digestBits

/-! ## 4. Operating-System and Hardware Platform Contracts

Each contract is a set of laws over the event traces of an explicit environment model. A model
that does not behave as required has no contract; each section gives a reference model that
satisfies the laws and a faulty model that provably does not. -/

/-! ### 4a. Crash-consistent storage (`fsync` + atomic `rename` + external monotone anchor) -/

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
def FsyncStorageModel.run (M : FsyncStorageModel) : M.State → List FsyncOp → M.State
  | s, [] => s
  | s, op :: rest => M.run (M.step s op) rest

theorem FsyncStorageModel.run_append (M : FsyncStorageModel) :
    ∀ (tr₁ tr₂ : List FsyncOp) (s : M.State), M.run s (tr₁ ++ tr₂) = M.run (M.run s tr₁) tr₂
  | [], _, _ => rfl
  | op :: rest, tr₂, s => M.run_append rest tr₂ (M.step s op)

/-- The commit protocol for one record: stage, `fsync` the file, `rename`, `fsync` the
    directory, advance the anchor. -/
def walCommitOps (rec : Bytes) : List FsyncOp :=
  [.append rec, .fsyncFile, .rename, .fsyncDir, .bumpAnchor]

/-- POSIX crash-consistent write-ahead log contract for the storage environment `M`. -/
structure PosixFsyncContract (M : FsyncStorageModel) : Prop where
  /-- The commit protocol appends exactly its record to the durable log. -/
  committedRecordDurable : ∀ (s : M.State) (rec : Bytes),
    M.durable (M.run s (walCommitOps rec)) = M.durable s ++ [rec]
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
  rw [← ht, c.committedRecordDurable]
  exact List.mem_append_left t (List.mem_append_right _ (List.Mem.head _))

/-- A whole-log snapshot shorter than the anchor is never what recovery returns. -/
theorem PosixFsyncContract.anchor_excludes_stale_snapshot {M : FsyncStorageModel}
    (c : PosixFsyncContract M) (s : M.State) (tr : List FsyncOp)
    (h : M.anchor s ≤ (M.durable s).length) :
    M.anchor s ≤ (M.durable (M.run s tr)).length :=
  Nat.le_trans (c.anchorMonotone s tr) (c.anchorWitnessesDurable s tr h)

/-- State of the reference journal: the durable log, the staged record, whether the staging
    file is synced, whether it has been renamed, and the anchor. -/
structure FsyncJournalState where
  durable : List Bytes
  staged : Option Bytes
  fileSynced : Bool
  renamed : Bool
  anchor : Nat

/-- Reference journal. A record becomes durable at the directory `fsync` that follows a
    `rename` of a synced staging file. With `rollbackOnCrash = true` a crash discards the
    durable log (a volume that loses synced data). -/
def fsyncJournalStep (rollbackOnCrash : Bool) (s : FsyncJournalState) :
    FsyncOp → FsyncJournalState
  | .append rec => { s with staged := some rec, fileSynced := false, renamed := false }
  | .fsyncFile => { s with fileSynced := s.staged.isSome }
  | .rename => { s with renamed := s.fileSynced }
  | .fsyncDir =>
    { s with
      durable := s.durable ++ (if s.renamed then s.staged.toList else [])
      staged := if s.renamed then none else s.staged
      fileSynced := s.fileSynced && !s.renamed
      renamed := false }
  | .bumpAnchor => { s with anchor := Nat.max s.anchor s.durable.length }
  | .crash =>
    { durable := if rollbackOnCrash then [] else s.durable
      staged := none
      fileSynced := false
      renamed := false
      anchor := s.anchor }

/-- The reference journal as a storage environment. -/
def fsyncJournalModel (rollbackOnCrash : Bool) : FsyncStorageModel where
  State := FsyncJournalState
  step := fsyncJournalStep rollbackOnCrash
  durable := fun s => s.durable
  anchor := fun s => s.anchor

private theorem fsyncJournalStep_prefix (s : FsyncJournalState) (op : FsyncOp) :
    s.durable <+: (fsyncJournalStep false s op).durable := by
  cases op with
  | fsyncDir => exact List.prefix_append _ _
  | append _ => exact List.prefix_refl _
  | fsyncFile => exact List.prefix_refl _
  | rename => exact List.prefix_refl _
  | bumpAnchor => exact List.prefix_refl _
  | crash => exact List.prefix_refl _

private theorem fsyncJournalStep_anchor (s : FsyncJournalState) (op : FsyncOp) :
    s.anchor ≤ (fsyncJournalStep false s op).anchor := by
  cases op with
  | bumpAnchor => exact Nat.le_max_left _ _
  | append _ => exact Nat.le_refl _
  | fsyncFile => exact Nat.le_refl _
  | rename => exact Nat.le_refl _
  | fsyncDir => exact Nat.le_refl _
  | crash => exact Nat.le_refl _

private theorem fsyncJournalStep_anchor_le (s : FsyncJournalState) (op : FsyncOp)
    (h : s.anchor ≤ s.durable.length) :
    (fsyncJournalStep false s op).anchor ≤ (fsyncJournalStep false s op).durable.length := by
  cases op with
  | bumpAnchor => exact Nat.max_le.mpr ⟨h, Nat.le_refl _⟩
  | fsyncDir =>
    show s.anchor ≤ (s.durable ++ (if s.renamed then s.staged.toList else [])).length
    rw [List.length_append]
    exact Nat.le_trans h (Nat.le_add_right _ _)
  | append _ => exact h
  | fsyncFile => exact h
  | rename => exact h
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
  committedRecordDurable _ _ := by rfl
  noRollback s tr := fsyncJournal_run_prefix tr s
  anchorMonotone s tr := fsyncJournal_run_anchor tr s
  anchorWitnessesDurable s tr h := fsyncJournal_run_anchor_le tr s h

/-- A volume that loses its durable log at a crash has no contract. -/
theorem fsync_rollback_volume_has_no_contract : ¬ PosixFsyncContract (fsyncJournalModel true) := by
  intro c
  obtain ⟨t, ht⟩ := c.noRollback ⟨[[]], none, false, false, 0⟩ [.crash]
  have hLen := congrArg List.length ht
  rw [List.length_append] at hLen
  exact Nat.succ_ne_zero _ (Nat.eq_zero_of_add_eq_zero_right hLen)

/-! ### 4b. Authenticated point-to-point channels -/

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

/-- Sender-authenticated, replay-protected channel contract for a network environment given
    by its set `admits` of possible event traces. -/
structure AuthenticatedChannelContract (admits : List ChannelEvent → Prop) : Prop where
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

/-- The reference channel satisfies the contract. -/
theorem checkedChannel_contract :
    AuthenticatedChannelContract (fun tr => channelRun tr [] [] = true) where
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

/-! ### 4c. Secret-share erasure at quarantine -/

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
    for the memory environment `M`. -/
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

/-! ### 4d. Data-independent timing and SIMT workgroup execution -/

/-- Hardware data-independent timing (`DOIT` / `DIT`) contract. `observe mode op data` is the
    timing observation of executing instruction `op` on operand values `data`; in the
    constant-time-safe mode it does not depend on `data`. -/
structure DitHardwareContract (Op Data Obs : Type) where
  mode : ExecMode
  mode_safe : mode = ExecMode.constantTimeSafe
  observe : ExecMode → Op → Data → Obs
  dataIndependent : ∀ (op : Op) (d₁ d₂ : Data),
    observe ExecMode.constantTimeSafe op d₁ = observe ExecMode.constantTimeSafe op d₂

theorem DitHardwareContract.dit_enabled {Op Data Obs : Type} (c : DitHardwareContract Op Data Obs) :
    c.mode.ditEnabled = true ∧ c.mode.cleanSimdUpper = true ∧ c.mode.speculationFence = true := by
  rw [c.mode_safe]
  exact ⟨rfl, rfl, rfl⟩

/-- Two executions of the same instruction sequence on different operand values produce the
    same timing trace. -/
theorem DitHardwareContract.trace_data_independent {Op Data Obs : Type}
    (c : DitHardwareContract Op Data Obs) :
    ∀ (tr₁ tr₂ : List (Op × Data)), tr₁.map Prod.fst = tr₂.map Prod.fst →
      tr₁.map (fun e => c.observe c.mode e.1 e.2) = tr₂.map (fun e => c.observe c.mode e.1 e.2)
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | (op₁, d₁) :: r₁, (op₂, d₂) :: r₂, h => by
    have hOp : op₁ = op₂ := List.head_eq_of_cons_eq h
    have hTail : r₁.map Prod.fst = r₂.map Prod.fst := List.tail_eq_of_cons_eq h
    have ih := c.trace_data_independent r₁ r₂ hTail
    show c.observe c.mode op₁ d₁ :: r₁.map (fun e => c.observe c.mode e.1 e.2) =
      c.observe c.mode op₂ d₂ :: r₂.map (fun e => c.observe c.mode e.1 e.2)
    rw [ih, hOp, c.mode_safe, c.dataIndependent op₂ d₁ d₂]

/-- An execution unit whose timing reveals its operand has no contract. -/
theorem operand_timed_unit_has_no_dit_contract :
    ¬ ∃ c : DitHardwareContract Unit Nat Nat, c.observe = fun _ _ d => d := by
  rintro ⟨c, hObs⟩
  have h := c.dataIndependent () 0 1
  rw [hObs] at h
  exact absurd h (by decide)

/-- GPU SIMT workgroup execution of a SPIR-V batch-verification / NTT kernel: the subgroup and
    workgroup sizes, the basic-block trace of every invocation and the storage cells every
    invocation writes. The subgroup size divides the workgroup size. -/
structure SimtWorkgroupContract where
  subgroupSize : Nat
  workgroupSize : Nat
  blockTrace : Nat → List Nat
  writeSet : Nat → List Nat
  h_divides : 0 < subgroupSize ∧ subgroupSize ∣ workgroupSize

theorem SimtWorkgroupContract.h_subgroup_pos (c : SimtWorkgroupContract) : 0 < c.subgroupSize :=
  c.h_divides.1

/-- Uniform control flow: invocations of one subgroup execute the same basic blocks. -/
def SimtWorkgroupContract.UniformControlFlow (c : SimtWorkgroupContract) : Prop :=
  ∀ i j : Nat, i < c.workgroupSize → j < c.workgroupSize →
    i / c.subgroupSize = j / c.subgroupSize → c.blockTrace i = c.blockTrace j

/-- Disjoint storage bindings: no storage cell is written by two invocations. -/
def SimtWorkgroupContract.DisjointStorageBindings (c : SimtWorkgroupContract) : Prop :=
  ∀ i j : Nat, i < c.workgroupSize → j < c.workgroupSize → i ≠ j →
    ∀ cell ∈ c.writeSet i, cell ∉ c.writeSet j

/-- Well-formed SIMT execution: divisibility of the sizes together with both safety
    properties of the execution. -/
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

/-- A storage cell written inside a well-formed workgroup has a unique writer. -/
theorem WellFormedSimtContract.write_race_free {c : SimtWorkgroupContract}
    (w : WellFormedSimtContract c) (i j cell : Nat)
    (hi : i < c.workgroupSize) (hj : j < c.workgroupSize)
    (hci : cell ∈ c.writeSet i) (hcj : cell ∈ c.writeSet j) : i = j :=
  match Nat.decEq i j with
  | .isTrue h => h
  | .isFalse h => absurd hcj (w.disjointStorageBindings i j hi hj h cell hci)

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
  h_divides := ⟨Nat.one_pos, ⟨2, rfl⟩⟩

/-- A workgroup with a write race is not well formed, whatever its sizes. -/
theorem racing_simt_not_wellFormed : ¬ WellFormedSimtContract racingSimtContract := by
  intro w
  exact absurd (w.write_race_free 0 1 0 (by decide) (by decide) (List.Mem.head _) (List.Mem.head _))
    (by decide)

#tooth_pair PosixFsyncContract.committed_survives vs fsync_rollback_volume_has_no_contract
#tooth_pair checkedChannel_contract vs open_relay_has_no_channel_contract
#tooth_pair shareMemoryModel_contract vs elided_zeroization_has_no_erasure_contract
#tooth_pair DitHardwareContract.trace_data_independent vs operand_timed_unit_has_no_dit_contract
#tooth_pair SimtWorkgroupContract.subgroups_tile vs simt_subgroup32_workgroup33_rejected
#tooth_pair WellFormedSimtContract.write_race_free vs racing_simt_not_wellFormed

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
  Qsag.Spec.SmDtTcrAssumption.tcrGame_bound
  Qsag.Spec.SmDtPreAssumption.preGame_bound
  Qsag.Spec.ItsrAssumption.itsrGame_bound
  Qsag.Spec.KeyedPrfAssumption.advantage_bound
  Qsag.Spec.DecisionRlweAssumption.advantage_bound
  Qsag.Spec.ModuleSisAssumption.sisGame_bound
  Qsag.Spec.DualLpnAssumption.advantage_bound
  Qsag.Spec.HashSigAssumptions.forger_bound
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
  Qsag.Spec.checkedChannel_contract
  Qsag.Spec.open_relay_has_no_channel_contract
  Qsag.Spec.shareMemoryModel_contract
  Qsag.Spec.elided_zeroization_has_no_erasure_contract
  Qsag.Spec.DitHardwareContract.dit_enabled
  Qsag.Spec.DitHardwareContract.trace_data_independent
  Qsag.Spec.operand_timed_unit_has_no_dit_contract
  Qsag.Spec.SimtWorkgroupContract.subgroups_tile
  Qsag.Spec.WellFormedSimtContract.subgroup_leader_trace
  Qsag.Spec.WellFormedSimtContract.write_race_free
  Qsag.Spec.simt_subgroup32_workgroup33_rejected
  Qsag.Spec.racing_simt_not_wellFormed

end Qsag.Spec
end
