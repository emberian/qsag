module
/-
# Qsag.Protocol.Signing.Compact1122ClosedEufCma — one-time EUF-CMA reduction for the target-sum Winternitz layer of `Compact1122`

The scheme (§2): `34` hash chains of `95` steps (`w = 96`) under a tweakable hash
`th seed tweak message` with `32`-byte digests; a codeword is `34` digits below `96` with digit
sum `1615` (`CodeOk`); a signature opens chain `i` at position `c[i]`; the public root is the
hash of the `34` chain ends. These are the `Compact1122` parameters `w = 96`, `L = 34`,
`S = 1615` of `compact1122Params`.

The experiment (§7): `eufGame` samples the seed, the `34` chain starts and the signing
randomizer uniformly; a forger sees the public key, may obtain one signature, and wins with a
verifying signature on another message.

The reductions are programs over the challenger interfaces of `Spec.Assumptions` that read the
challenger's answers:

* `tcrAdv` (§4) commits the honest input of all `3231` hash slots to the `SM-DT-TCR` challenger,
  which answers with the next chain value, and after `reveal` reports a hash input of the forgery
  that collides with a committed one.
* `preAdv` (§5) receives the image of the honest value at one chain position from the
  `SM-DT-PRE` challenger, rebuilds key and signature from it after `reveal`, and reports the
  forger's value advanced to that position.
* `itsrAdv` (§6) obtains the signing randomizer from the `ITSR` challenger.

`forgery_classified` shows that a winning run repeats the signed codeword, or collides with an
honest hash input, or carries the honest chain value at a position below what the signer opened
(two target-sum codewords are incomparable). `eufGame_win_reduction` turns the three cases into
winning coins of the three experiments on the same coin, and
`compact1122_closed_euf_cma_bound` is the resulting bound
`εItsr + εTcr + 34 · εPre + 3196 · εLink`.

What the statement depends on, beyond the hardness propositions:

* `ChainLinkHard` is not a proposition of `Spec.Assumptions`. `SmDtPreHard` speaks about uniform
  hidden inputs, which covers the `34` chain starts; at the `34 · 94` interior positions the
  hidden input is a hash output. One-wayness on those inputs does not follow from `SM-DT-TCR` and
  uniform-input `SM-DT-PRE`; the literature derives it from an undetectability assumption, which
  this library does not state.
* The model has a fixed frontier of `34` chains. The message-dependent antichain of
  `FrontierSumFts` in the height-`8` tree, the derivation of chain starts and randomizer from
  secret seeds, and the `cSHAKE256` framing of `FrontierCompact1122AndCorduroySecurity` are not
  part of it.

`tooth_drop_target_sum_forward_step_forges`: for a code without the digit-sum constraint a
forger that only steps chains forward wins on every coin.
-/

public import Qsag.Spec.Assumptions
public import Qsag.Protocol.Signing.ExecEufCmaClosedGame
public import Qsag.Protocol.Signing.FrontierCompact1122AndCorduroySecurity
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Compact1122
open Qsag.Spec

set_option autoImplicit false

private theorem itePos {α : Type} {p : Prop} [Decidable p] (hp : p) (a b : α) :
    (if p then a else b) = a := by
  cases ‹Decidable p› with
  | isTrue _ => rfl
  | isFalse hn => exact False.elim (hn hp)

private theorem iteNeg {α : Type} {p : Prop} [Decidable p] (hnp : ¬ p) (a b : α) :
    (if p then a else b) = b := by
  cases ‹Decidable p› with
  | isTrue hp => exact False.elim (hnp hp)
  | isFalse _ => rfl

/-! ## 1. Coin-space coordinates -/

/-- Move a coordinate of the adversary side to the challenger side: the challenger of the
    result reads `π₂`'s challenger coordinate inside `π₁`'s adversary coordinate. -/
def pullFromAdv {n c₁ a₁ c₂ a₂ : Nat} (π₁ : CoinSplit n c₁ a₁) (π₂ : CoinSplit a₁ c₂ a₂) :
    CoinSplit n c₂ (c₁ * a₂) where
  chal ω := π₂.chal (π₁.advc ω)
  advc ω := (CoinSplit.prod c₁ a₂).pair (π₁.chal ω) (π₂.advc (π₁.advc ω))
  pair c z := π₁.pair ((CoinSplit.prod c₁ a₂).chal z) (π₂.pair c ((CoinSplit.prod c₁ a₂).advc z))
  chal_pair c z := by rw [π₁.advc_pair, π₂.chal_pair]
  advc_pair c z := by rw [π₁.chal_pair, π₁.advc_pair, π₂.advc_pair, (CoinSplit.prod c₁ a₂).pair_eta]
  pair_eta ω := by
    rw [(CoinSplit.prod c₁ a₂).chal_pair, (CoinSplit.prod c₁ a₂).advc_pair, π₂.pair_eta, π₁.pair_eta]

/-- Split the challenger coordinate of `π` by `ρ` and hand the remainder to the adversary. -/
def pullFromChal {n c a c' a' : Nat} (π : CoinSplit n c a) (ρ : CoinSplit c c' a') :
    CoinSplit n c' (a' * a) where
  chal ω := ρ.chal (π.chal ω)
  advc ω := (CoinSplit.prod a' a).pair (ρ.advc (π.chal ω)) (π.advc ω)
  pair x z := π.pair (ρ.pair x ((CoinSplit.prod a' a).chal z)) ((CoinSplit.prod a' a).advc z)
  chal_pair x z := by rw [π.chal_pair, ρ.chal_pair]
  advc_pair x z := by rw [π.chal_pair, π.advc_pair, ρ.advc_pair, (CoinSplit.prod a' a).pair_eta]
  pair_eta ω := by
    rw [(CoinSplit.prod a' a).chal_pair, (CoinSplit.prod a' a).advc_pair, ρ.pair_eta, π.pair_eta]

/-- Join the challenger coordinates of two nested splits. -/
def joinChal {n c₁ a₁ c₂ a₂ : Nat} (π₁ : CoinSplit n c₁ a₁) (π₂ : CoinSplit a₁ c₂ a₂) :
    CoinSplit n (c₁ * c₂) a₂ where
  chal ω := (CoinSplit.prod c₁ c₂).pair (π₁.chal ω) (π₂.chal (π₁.advc ω))
  advc ω := π₂.advc (π₁.advc ω)
  pair z a := π₁.pair ((CoinSplit.prod c₁ c₂).chal z) (π₂.pair ((CoinSplit.prod c₁ c₂).advc z) a)
  chal_pair z a := by
    rw [π₁.chal_pair, π₁.advc_pair, π₂.chal_pair, (CoinSplit.prod c₁ c₂).pair_eta]
  advc_pair z a := by rw [π₁.advc_pair, π₂.advc_pair]
  pair_eta ω := by
    rw [(CoinSplit.prod c₁ c₂).chal_pair, (CoinSplit.prod c₁ c₂).advc_pair, π₂.pair_eta, π₁.pair_eta]

/-- `B ^ k`, right-nested so that `powN B (k + 1) = B * powN B k` by definition. -/
def powN (B : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => B * powN B k

theorem powN_pos {B : Nat} (hB : 0 < B) : ∀ k : Nat, 0 < powN B k
  | 0 => Nat.one_pos
  | k + 1 => Nat.mul_pos hB (powN_pos hB k)

/-- The split of a vector of `k + 1` digits that makes digit `i` the challenger coordinate. -/
def digitSplit (B : Nat) : (k : Nat) → Fin (k + 1) → CoinSplit (powN B (k + 1)) B (powN B k)
  | k, ⟨0, _⟩ => CoinSplit.prod B (powN B k)
  | 0, ⟨i + 1, h⟩ => absurd (Nat.lt_of_succ_lt_succ h) (Nat.not_lt_zero i)
  | k + 1, ⟨i + 1, h⟩ =>
    pullFromAdv (CoinSplit.prod B (powN B (k + 1))) (digitSplit B k ⟨i, Nat.lt_of_succ_lt_succ h⟩)

/-- A digit other than the pulled one does not depend on the pulled digit. -/
theorem digitSplit_chal_pair_ne (B : Nat) :
    ∀ (k : Nat) (i j : Fin (k + 1)), i ≠ j →
      ∀ (x x' : Fin B) (u : Fin (powN B k)),
        (digitSplit B k j).chal ((digitSplit B k i).pair x u) =
          (digitSplit B k j).chal ((digitSplit B k i).pair x' u)
  | _, ⟨0, _⟩, ⟨0, _⟩, hne, _, _, _ => absurd rfl hne
  | 0, ⟨i + 1, h⟩, _, _, _, _, _ => absurd (Nat.lt_of_succ_lt_succ h) (Nat.not_lt_zero i)
  | 0, _, ⟨j + 1, h⟩, _, _, _, _ => absurd (Nat.lt_of_succ_lt_succ h) (Nat.not_lt_zero j)
  | k + 1, ⟨0, _⟩, ⟨j + 1, hj⟩, _, x, x', u => by
    show (digitSplit B k ⟨j, _⟩).chal
        ((CoinSplit.prod B (powN B (k + 1))).advc ((CoinSplit.prod B (powN B (k + 1))).pair x u)) =
      (digitSplit B k ⟨j, _⟩).chal
        ((CoinSplit.prod B (powN B (k + 1))).advc ((CoinSplit.prod B (powN B (k + 1))).pair x' u))
    rw [(CoinSplit.prod B (powN B (k + 1))).advc_pair, (CoinSplit.prod B (powN B (k + 1))).advc_pair]
  | k + 1, ⟨i + 1, hi⟩, ⟨0, _⟩, _, x, x', u => by
    show (CoinSplit.prod B (powN B (k + 1))).chal
        ((CoinSplit.prod B (powN B (k + 1))).pair ((CoinSplit.prod B (powN B k)).chal u)
          ((digitSplit B k ⟨i, _⟩).pair x ((CoinSplit.prod B (powN B k)).advc u))) =
      (CoinSplit.prod B (powN B (k + 1))).chal
        ((CoinSplit.prod B (powN B (k + 1))).pair ((CoinSplit.prod B (powN B k)).chal u)
          ((digitSplit B k ⟨i, _⟩).pair x' ((CoinSplit.prod B (powN B k)).advc u)))
    rw [(CoinSplit.prod B (powN B (k + 1))).chal_pair, (CoinSplit.prod B (powN B (k + 1))).chal_pair]
  | k + 1, ⟨i + 1, hi⟩, ⟨j + 1, hj⟩, hne, x, x', u => by
    show (digitSplit B k ⟨j, _⟩).chal
        ((CoinSplit.prod B (powN B (k + 1))).advc
          ((CoinSplit.prod B (powN B (k + 1))).pair ((CoinSplit.prod B (powN B k)).chal u)
            ((digitSplit B k ⟨i, _⟩).pair x ((CoinSplit.prod B (powN B k)).advc u)))) =
      (digitSplit B k ⟨j, _⟩).chal
        ((CoinSplit.prod B (powN B (k + 1))).advc
          ((CoinSplit.prod B (powN B (k + 1))).pair ((CoinSplit.prod B (powN B k)).chal u)
            ((digitSplit B k ⟨i, _⟩).pair x' ((CoinSplit.prod B (powN B k)).advc u))))
    rw [(CoinSplit.prod B (powN B (k + 1))).advc_pair, (CoinSplit.prod B (powN B (k + 1))).advc_pair]
    exact digitSplit_chal_pair_ne B k ⟨i, Nat.lt_of_succ_lt_succ hi⟩ ⟨j, Nat.lt_of_succ_lt_succ hj⟩
      (fun h => hne (by cases h; rfl)) x x' _

/-! ## 2. The one-time target-sum Winternitz scheme at the `Compact1122` parameters

`34` hash chains of `95` steps (`w = 96`), codewords of `34` digits below `96` with digit sum
`1615`. Step `p` of chain `i` is the tweakable hash under tweak `tw (i * 95 + p)`; the public
root is the hash of the `34` chain ends under tweak `tw 3230`. -/

/-- Tweakable hash `th seed tweak message`. -/
abbrev TwHash : Type := Bytes → Bytes → Bytes → Bytes

/-- Chain `i` from a value `x` at position `pos`, advanced `steps` times. -/
@[expose] def chainFrom (th : TwHash) (tw : Nat → Bytes) (seed : Bytes) (i : Nat) : Nat → Nat → Bytes → Bytes
  | _, 0, x => x
  | pos, k + 1, x => chainFrom th tw seed i (pos + 1) k (th seed (tw (i * 95 + pos)) x)

theorem chainFrom_add (th : TwHash) (tw : Nat → Bytes) (seed : Bytes) (i : Nat) :
    ∀ (k₁ pos k₂ : Nat) (x : Bytes),
      chainFrom th tw seed i pos (k₁ + k₂) x =
        chainFrom th tw seed i (pos + k₁) k₂ (chainFrom th tw seed i pos k₁ x)
  | 0, pos, k₂, x => by rw [Nat.zero_add, Nat.add_zero]; rfl
  | k₁ + 1, pos, k₂, x => by
    have h1 : k₁ + 1 + k₂ = (k₁ + k₂) + 1 := by omega
    have h2 : pos + (k₁ + 1) = pos + 1 + k₁ := by omega
    rw [h1, h2]
    exact chainFrom_add th tw seed i k₁ (pos + 1) k₂ _

theorem chainFrom_succ_right (th : TwHash) (tw : Nat → Bytes) (seed : Bytes) (i pos k : Nat)
    (x : Bytes) :
    chainFrom th tw seed i pos (k + 1) x =
      th seed (tw (i * 95 + (pos + k))) (chainFrom th tw seed i pos k x) := by
  rw [chainFrom_add th tw seed i k pos 1 x]
  rfl

/-- Honest value of chain `i` at position `p` for chain starts `starts`. -/
def honestVal (th : TwHash) (tw : Nat → Bytes) (seed : Bytes) (starts : Nat → Bytes)
    (i p : Nat) : Bytes :=
  chainFrom th tw seed i 0 p (starts i)

theorem honestVal_succ (th : TwHash) (tw : Nat → Bytes) (seed : Bytes) (starts : Nat → Bytes)
    (i p : Nat) :
    honestVal th tw seed starts i (p + 1) =
      th seed (tw (i * 95 + p)) (honestVal th tw seed starts i p) := by
  unfold honestVal
  rw [chainFrom_succ_right, Nat.zero_add]

theorem honestVal_advance (th : TwHash) (tw : Nat → Bytes) (seed : Bytes) (starts : Nat → Bytes)
    (i a k : Nat) :
    chainFrom th tw seed i a k (honestVal th tw seed starts i a) =
      honestVal th tw seed starts i (a + k) := by
  unfold honestVal
  rw [chainFrom_add th tw seed i a 0 k, Nat.zero_add]

/-- Input of the root hash: the `34` chain ends of the value table `hv`. -/
@[expose] def rootInput (hv : Nat → Nat → Bytes) : Bytes :=
  ((List.range 34).map (fun i => hv i 95)).flatten

/-- Public root of the value table `hv`. -/
@[expose] def pkRoot (th : TwHash) (tw : Nat → Bytes) (seed : Bytes) (hv : Nat → Nat → Bytes) : Bytes :=
  th seed (tw 3230) (rootInput hv)

/-- Signature values for codeword `c`: chain `i` is opened at position `c[i]`. -/
@[expose] def signVals (hv : Nat → Nat → Bytes) (c : List Nat) : List Bytes :=
  (List.range 34).map (fun i => hv i (c.getD i 0))

/-- Chain ends recomputed by the verifier from signature values `vals` for codeword `c`. -/
@[expose] def sigEnds (th : TwHash) (tw : Nat → Bytes) (seed : Bytes) (c : List Nat) (vals : List Bytes) :
    List Bytes :=
  (List.range 34).map (fun i =>
    chainFrom th tw seed i (c.getD i 0) (95 - c.getD i 0) (vals.getD i []))

/-- Verification: `34` values of `32` bytes whose recomputed chain ends hash to the root. -/
@[expose] def verify (th : TwHash) (tw : Nat → Bytes) (seed root : Bytes) (c : List Nat)
    (vals : List Bytes) : Bool :=
  decide (vals.length = 34) &&
    (vals.all (fun v => decide (v.length = 32)) &&
      decide (th seed (tw 3230) (sigEnds th tw seed c vals).flatten = root))

/-- Target-sum codeword: `34` digits below `96` with digit sum `1615`. -/
@[expose] def CodeOk (c : List Nat) : Prop :=
  c.length = 34 ∧ c.sum = 1615 ∧ ∀ a ∈ c, a < 96

/-- One-time forger: given the public key it may ask for one signature, then outputs a message,
    a randomizer and signature values. -/
structure Forger where
  query : Bytes → Bytes → Option Bytes
  forge : Bytes → Bytes → Option (Bytes × List Bytes) → Bytes × Bytes × List Bytes

/-- Transcript of one run of the forgery experiment. -/
structure Outcome where
  root : Bytes
  queried : Option (Bytes × List Nat)
  msg : Bytes
  rand : Bytes
  vals : List Bytes

/-- Run the forger against the signer whose chain values are `hv` and whose randomizer is
    `rand`. The message codeword is `code randomizer (frame seed root message)`. -/
@[expose] def eufOutcome (th : TwHash) (tw : Nat → Bytes) (code : Bytes → Bytes → List Nat)
    (frame : Bytes → Bytes → Bytes → Bytes) (seed : Bytes) (hv : Nat → Nat → Bytes)
    (rand : Bytes) (F : Forger) : Outcome :=
  match F.query seed (pkRoot th tw seed hv) with
  | none =>
    let o := F.forge seed (pkRoot th tw seed hv) none
    ⟨pkRoot th tw seed hv, none, o.1, o.2.1, o.2.2⟩
  | some m₁ =>
    let o := F.forge seed (pkRoot th tw seed hv)
      (some (rand, signVals hv (code rand (frame seed (pkRoot th tw seed hv) m₁))))
    ⟨pkRoot th tw seed hv, some (m₁, code rand (frame seed (pkRoot th tw seed hv) m₁)),
      o.1, o.2.1, o.2.2⟩

/-- Codeword of the forged message. -/
@[expose] def forgedCode (code : Bytes → Bytes → List Nat) (frame : Bytes → Bytes → Bytes → Bytes)
    (seed : Bytes) (o : Outcome) : List Nat :=
  code o.rand (frame seed o.root o.msg)

/-- The forgery is on a message that was not signed and verifies. -/
@[expose] def eufWin (th : TwHash) (tw : Nat → Bytes) (code : Bytes → Bytes → List Nat)
    (frame : Bytes → Bytes → Bytes → Bytes) (seed : Bytes) (o : Outcome) : Bool :=
  (match o.queried with
    | none => true
    | some q => decide (o.msg ≠ q.1)) &&
    verify th tw seed o.root (forgedCode code frame seed o) o.vals

/-- Honest input of hash slot `t`: slot `i * 95 + p` is step `p` of chain `i`, slot `3230` is the
    root hash. -/
def slotInput (th : TwHash) (tw : Nat → Bytes) (seed : Bytes) (starts : Nat → Bytes) (t : Nat) :
    Bytes :=
  if t < 3230 then honestVal th tw seed starts (t / 95) (t % 95)
  else rootInput (honestVal th tw seed starts)

/-- Every hash input the verifier evaluates on a forgery, with its slot. -/
def forgeryHashInputs (th : TwHash) (tw : Nat → Bytes) (seed : Bytes) (c : List Nat)
    (vals : List Bytes) : List (Nat × Bytes) :=
  (List.range 34).flatMap (fun i =>
    (List.range 95).map (fun p =>
      (i * 95 + p, chainFrom th tw seed i (c.getD i 0) (p - c.getD i 0) (vals.getD i [])))) ++
    [(3230, (sigEnds th tw seed c vals).flatten)]

/-! ### Classification of a forgery -/

private theorem band_split {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | cases h

private theorem flatten_inj_of_len32 :
    ∀ (xs ys : List Bytes), xs.length = ys.length →
      (∀ x ∈ xs, x.length = 32) → (∀ y ∈ ys, y.length = 32) →
      xs.flatten = ys.flatten → xs = ys
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, h, _, _, _ => nomatch h
  | _ :: _, [], h, _, _, _ => nomatch h
  | x :: xs, y :: ys, hLen, hx, hy, hEq => by
    rw [List.flatten_cons, List.flatten_cons] at hEq
    have hxl : x.length = y.length :=
      (hx x (List.mem_cons_self ..)).trans (hy y (List.mem_cons_self ..)).symm
    obtain ⟨h1, h2⟩ := List.append_inj hEq hxl
    rw [h1, flatten_inj_of_len32 xs ys (Nat.succ.inj hLen)
      (fun a ha => hx a (List.mem_cons_of_mem _ ha))
      (fun a ha => hy a (List.mem_cons_of_mem _ ha)) h2]

private theorem forall_or_exists_lt (A B : Nat → Prop) :
    ∀ n : Nat, (∀ i, i < n → A i ∨ B i) → (∀ i, i < n → A i) ∨ ∃ i, i < n ∧ B i
  | 0, _ => .inl (fun _ h => absurd h (Nat.not_lt_zero _))
  | n + 1, h => by
    rcases forall_or_exists_lt A B n (fun i hi => h i (Nat.lt_succ_of_lt hi)) with hAll | ⟨i, hi, hB⟩
    · rcases h n (Nat.lt_succ_self n) with hA | hB
      · refine .inl (fun i hi => ?_)
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
        · exact hAll i hlt
        · rw [heq]; exact hA
      · exact .inr ⟨n, Nat.lt_succ_self n, hB⟩
    · exact .inr ⟨i, Nat.lt_succ_of_lt hi, hB⟩

/-- A value that reaches the honest chain end is the honest value at its position, or the two
    chains merge at a hash collision. -/
private theorem chain_agree_or_collision (th : TwHash) (tw : Nat → Bytes) (seed : Bytes)
    (starts : Nat → Bytes) (i : Nat) :
    ∀ (d a : Nat) (y : Bytes), a + d = 95 →
      chainFrom th tw seed i a d y = honestVal th tw seed starts i 95 →
      y = honestVal th tw seed starts i a ∨
      ∃ p, a ≤ p ∧ p < 95 ∧
        chainFrom th tw seed i a (p - a) y ≠ honestVal th tw seed starts i p ∧
        th seed (tw (i * 95 + p)) (chainFrom th tw seed i a (p - a) y) =
          th seed (tw (i * 95 + p)) (honestVal th tw seed starts i p)
  | 0, a, y, ha, hEnd => by
    have ha' : a = 95 := by omega
    subst ha'
    exact .inl hEnd
  | d + 1, a, y, ha, hEnd => by
    by_cases hy : y = honestVal th tw seed starts i a
    · exact .inl hy
    · refine .inr ?_
      have hStep : chainFrom th tw seed i a (d + 1) y =
          chainFrom th tw seed i (a + 1) d (th seed (tw (i * 95 + a)) y) := rfl
      rw [hStep] at hEnd
      rcases chain_agree_or_collision th tw seed starts i d (a + 1) _ (by omega) hEnd with
        hNext | ⟨p, hp1, hp2, hNe, hCol⟩
      · refine ⟨a, Nat.le_refl a, by omega, ?_, ?_⟩
        · rw [Nat.sub_self]; exact hy
        · rw [Nat.sub_self]
          show th seed (tw (i * 95 + a)) y = th seed (tw (i * 95 + a)) (honestVal th tw seed starts i a)
          rw [hNext, honestVal_succ]
      · have hShift : chainFrom th tw seed i a (p - a) y =
            chainFrom th tw seed i (a + 1) (p - (a + 1)) (th seed (tw (i * 95 + a)) y) := by
          have hpa : p - a = (p - (a + 1)) + 1 := by omega
          rw [hpa]
          rfl
        exact ⟨p, by omega, hp2, by rw [hShift]; exact hNe, by rw [hShift]; exact hCol⟩

private theorem sum_replicate_nat : ∀ (n c : Nat), (List.replicate n c).sum = n * c
  | 0, _ => by rw [Nat.zero_mul]; rfl
  | n + 1, c => by
    rw [List.replicate_succ, List.sum_cons, sum_replicate_nat n c, Nat.succ_mul, Nat.add_comm]

private theorem getD_eq_get (c : List Nat) (i : Nat) (h : i < c.length) :
    c.getD i 0 = c.get ⟨i, h⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- A codeword has a digit below `95`. -/
private theorem codeOk_has_digit_lt_95 {c : List Nat} (hc : CodeOk c) :
    ∃ i, i < 34 ∧ c.getD i 0 < 95 := by
  obtain ⟨hLen, hSum, _⟩ := hc
  have hRepLen : (List.replicate 34 95).length = 34 := List.length_replicate
  have hRepSum : (List.replicate 34 95).sum = 3230 := sum_replicate_nat 34 95
  have hNe : c ≠ List.replicate 34 95 := fun h => by
    rw [h, hRepSum] at hSum
    exact absurd hSum (by decide)
  let w := Qsag.findSmallerOffsetIdx c (List.replicate 34 95) (hLen.trans hRepLen.symm)
    (by rw [hSum, hRepSum]; decide) hNe
  refine ⟨w.1.1, Nat.lt_of_lt_of_eq w.1.2 hLen, ?_⟩
  have hMem : (List.replicate 34 95).get ⟨w.1.1, Nat.lt_of_lt_of_eq w.1.2 (hLen.trans hRepLen.symm)⟩ ∈
      List.replicate 34 95 := List.get_mem _ _
  have hw := w.2
  rw [(List.mem_replicate.mp hMem).2] at hw
  rw [getD_eq_get c w.1.1 w.1.2]
  exact hw

/-- Two different codewords: the second has a digit strictly below the first. -/
private theorem codeOk_ne_has_smaller_digit {c c' : List Nat} (hc : CodeOk c) (hc' : CodeOk c')
    (hNe : c' ≠ c) : ∃ i, i < 34 ∧ c'.getD i 0 < c.getD i 0 ∧ c.getD i 0 < 96 := by
  obtain ⟨hLen, hSum, hBnd⟩ := hc
  obtain ⟨hLen', hSum', _⟩ := hc'
  let w := Qsag.findSmallerOffsetIdx c' c (hLen'.trans hLen.symm) (by rw [hSum, hSum']; exact Nat.le_refl _) hNe
  have hi : w.1.1 < c.length := Nat.lt_of_lt_of_eq w.1.2 (hLen'.trans hLen.symm)
  refine ⟨w.1.1, Nat.lt_of_lt_of_eq w.1.2 hLen', ?_, ?_⟩
  · rw [getD_eq_get c' w.1.1 w.1.2, getD_eq_get c w.1.1 hi]
    exact w.2
  · rw [getD_eq_get c w.1.1 hi]
    exact hBnd _ (List.get_mem _ _)

/-- **Classification of a forgery.** A winning run repeats the codeword of the signed message,
    or evaluates the hash on an input that collides with the honest input of the same slot, or
    carries, on some chain `i`, the honest value at a position `j` strictly below every position
    the signer opened on that chain. -/
theorem forgery_classified (th : TwHash) (tw : Nat → Bytes)
    (hOut : ∀ s t m : Bytes, (th s t m).length = 32)
    (code : Bytes → Bytes → List Nat) (hCode : ∀ r m : Bytes, CodeOk (code r m))
    (frame : Bytes → Bytes → Bytes → Bytes) (seed : Bytes) (starts : Nat → Bytes)
    (rand : Bytes) (F : Forger)
    (hWin : eufWin th tw code frame seed
      (eufOutcome th tw code frame seed (honestVal th tw seed starts) rand F) = true) :
    let o := eufOutcome th tw code frame seed (honestVal th tw seed starts) rand F
    (∃ q, o.queried = some q ∧ o.msg ≠ q.1 ∧ forgedCode code frame seed o = q.2) ∨
    (∃ t x, (t, x) ∈ forgeryHashInputs th tw seed (forgedCode code frame seed o) o.vals ∧
      t ≤ 3230 ∧ x ≠ slotInput th tw seed starts t ∧
      th seed (tw t) x = th seed (tw t) (slotInput th tw seed starts t)) ∨
    (∃ i j, i < 34 ∧ j < 95 ∧ (forgedCode code frame seed o).getD i 0 ≤ j ∧
      (∀ q, o.queried = some q → q.2.getD i 0 = j + 1) ∧
      chainFrom th tw seed i ((forgedCode code frame seed o).getD i 0)
        (j - (forgedCode code frame seed o).getD i 0) (o.vals.getD i []) =
        honestVal th tw seed starts i j) := by
  intro o
  have hRoot : o.root = pkRoot th tw seed (honestVal th tw seed starts) := by
    show (eufOutcome th tw code frame seed (honestVal th tw seed starts) rand F).root = _
    unfold eufOutcome
    cases F.query seed (pkRoot th tw seed (honestVal th tw seed starts)) <;> rfl
  have hQCode : ∀ q, o.queried = some q → CodeOk q.2 := by
    intro q hq
    have hq' : (eufOutcome th tw code frame seed (honestVal th tw seed starts) rand F).queried =
        some q := hq
    unfold eufOutcome at hq'
    cases hQ : F.query seed (pkRoot th tw seed (honestVal th tw seed starts)) with
    | none => rw [hQ] at hq'; cases hq'
    | some m₁ =>
      rw [hQ] at hq'
      injection hq' with hq''
      rw [← hq'']
      exact hCode _ _
  have hW : eufWin th tw code frame seed o = true := hWin
  unfold eufWin at hW
  obtain ⟨hFresh, hVer⟩ := band_split hW
  unfold verify at hVer
  obtain ⟨hLenB, hRest⟩ := band_split hVer
  obtain ⟨hAllB, hRootB⟩ := band_split hRest
  have hLen : o.vals.length = 34 := of_decide_eq_true hLenB
  have hAll : ∀ v ∈ o.vals, v.length = 32 := fun v hv =>
    of_decide_eq_true (List.all_eq_true.mp hAllB v hv)
  have hRootEq : th seed (tw 3230)
      (sigEnds th tw seed (forgedCode code frame seed o) o.vals).flatten =
      th seed (tw 3230) (rootInput (honestVal th tw seed starts)) :=
    (of_decide_eq_true hRootB).trans hRoot
  have hc' : CodeOk (forgedCode code frame seed o) := hCode _ _
  by_cases hFl : (sigEnds th tw seed (forgedCode code frame seed o) o.vals).flatten =
      rootInput (honestVal th tw seed starts)
  · -- the chain ends agree
    have hEndsLen : (sigEnds th tw seed (forgedCode code frame seed o) o.vals).length =
        ((List.range 34).map (fun i => honestVal th tw seed starts i 95)).length := by
      unfold sigEnds
      rw [List.length_map, List.length_map]
    have hEnds : sigEnds th tw seed (forgedCode code frame seed o) o.vals =
        (List.range 34).map (fun i => honestVal th tw seed starts i 95) := by
      refine flatten_inj_of_len32 _ _ hEndsLen ?_ ?_ hFl
      · intro x hx
        unfold sigEnds at hx
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        have hi' : i < 34 := List.mem_range.mp hi
        cases hd : 95 - (forgedCode code frame seed o).getD i 0 with
        | zero =>
          show (o.vals.getD i []).length = 32
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hLen]; exact hi')]
          exact hAll _ (List.getElem_mem _)
        | succ k =>
          rw [chainFrom_succ_right]
          exact hOut _ _ _
      · intro y hy
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hy
        rw [honestVal_succ]
        exact hOut _ _ _
    have hEach : ∀ i, i < 34 →
        chainFrom th tw seed i ((forgedCode code frame seed o).getD i 0)
          (95 - (forgedCode code frame seed o).getD i 0) (o.vals.getD i []) =
          honestVal th tw seed starts i 95 := by
      intro i hi
      unfold sigEnds at hEnds
      exact List.map_inj_left.mp hEnds i (List.mem_range.mpr hi)
    have hDigit : ∀ i, i < 34 → (forgedCode code frame seed o).getD i 0 < 96 := by
      intro i hi
      have hil : i < (forgedCode code frame seed o).length := by rw [hc'.1]; exact hi
      rw [getD_eq_get _ i hil]
      exact hc'.2.2 _ (List.get_mem _ _)
    rcases forall_or_exists_lt
      (fun i => o.vals.getD i [] =
        honestVal th tw seed starts i ((forgedCode code frame seed o).getD i 0))
      (fun i => ∃ p, (forgedCode code frame seed o).getD i 0 ≤ p ∧ p < 95 ∧
        chainFrom th tw seed i ((forgedCode code frame seed o).getD i 0)
          (p - (forgedCode code frame seed o).getD i 0) (o.vals.getD i []) ≠
          honestVal th tw seed starts i p ∧
        th seed (tw (i * 95 + p)) (chainFrom th tw seed i ((forgedCode code frame seed o).getD i 0)
          (p - (forgedCode code frame seed o).getD i 0) (o.vals.getD i [])) =
          th seed (tw (i * 95 + p)) (honestVal th tw seed starts i p))
      34 (fun i hi => chain_agree_or_collision th tw seed starts i
        (95 - (forgedCode code frame seed o).getD i 0) ((forgedCode code frame seed o).getD i 0)
        (o.vals.getD i []) (by have := hDigit i hi; omega) (hEach i hi)) with
      hAgree | ⟨i, hi, p, hp1, hp2, hNe, hCol⟩
    · -- every signature value is the honest value at its position
      cases hQ : o.queried with
      | none =>
        obtain ⟨i, hi, hlt⟩ := codeOk_has_digit_lt_95 hc'
        refine .inr (.inr ⟨i, (forgedCode code frame seed o).getD i 0, hi, hlt, Nat.le_refl _,
          (fun q hq => nomatch hq), ?_⟩)
        rw [Nat.sub_self]
        exact hAgree i hi
      | some q =>
        by_cases hSame : forgedCode code frame seed o = q.2
        · rw [hQ] at hFresh
          exact .inl ⟨q, rfl, of_decide_eq_true hFresh, hSame⟩
        · obtain ⟨i, hi, hlt, hlt96⟩ := codeOk_ne_has_smaller_digit (hQCode q hQ) hc' hSame
          refine .inr (.inr ⟨i, q.2.getD i 0 - 1, hi, by omega, by omega,
            fun q' hq' => by injection hq' with hq''; rw [← hq'']; omega, ?_⟩)
          rw [hAgree i hi, honestVal_advance]
          congr 1
          omega
    · -- a chain merges into the honest chain at a collision
      refine .inr (.inl ⟨i * 95 + p,
        chainFrom th tw seed i ((forgedCode code frame seed o).getD i 0)
          (p - (forgedCode code frame seed o).getD i 0) (o.vals.getD i []), ?_, by omega, ?_, ?_⟩)
      · unfold forgeryHashInputs
        refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, ?_⟩)
        exact List.mem_map.mpr ⟨p, List.mem_range.mpr hp2, rfl⟩
      · have hSlot : slotInput th tw seed starts (i * 95 + p) = honestVal th tw seed starts i p := by
          unfold slotInput
          rw [itePos (by omega : i * 95 + p < 3230)]
          have h1 : (i * 95 + p) / 95 = i := by omega
          have h2 : (i * 95 + p) % 95 = p := by omega
          rw [h1, h2]
        rw [hSlot]
        exact hNe
      · have hSlot : slotInput th tw seed starts (i * 95 + p) = honestVal th tw seed starts i p := by
          unfold slotInput
          rw [itePos (by omega : i * 95 + p < 3230)]
          have h1 : (i * 95 + p) / 95 = i := by omega
          have h2 : (i * 95 + p) % 95 = p := by omega
          rw [h1, h2]
        rw [hSlot]
        exact hCol
  · -- the root hash collides
    refine .inr (.inl ⟨3230, (sigEnds th tw seed (forgedCode code frame seed o) o.vals).flatten,
      ?_, Nat.le_refl _, ?_, ?_⟩)
    · unfold forgeryHashInputs
      exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    · have hSlot : slotInput th tw seed starts 3230 = rootInput (honestVal th tw seed starts) := by
        unfold slotInput
        rw [iteNeg (by decide : ¬ 3230 < 3230)]
      rw [hSlot]
      exact hFl
    · have hSlot : slotInput th tw seed starts 3230 = rootInput (honestVal th tw seed starts) := by
        unfold slotInput
        rw [iteNeg (by decide : ¬ 3230 < 3230)]
      rw [hSlot]
      exact hRootEq


/-! ## 4. Reduction to `SM-DT-TCR`

The adversary commits the honest input of every hash slot as a target, in slot order: the
`3230` chain steps and then the root hash. Each answer is the next chain value. After `reveal`
it runs the forger on the real key and searches the hash inputs of the forgery for one that
collides with a committed input. -/

/-- Input committed for slot `t`, computed from the chain starts and the answers so far. -/
def commitInput (starts : Nat → Bytes) (outs : List Bytes) (t : Nat) : Bytes :=
  if t < 3230 then (if t % 95 = 0 then starts (t / 95) else outs.getD (t - 1) [])
  else ((List.range 34).map (fun i => outs.getD (i * 95 + 94) [])).flatten

/-- Commit slots `t, t + 1, …` for `fuel` steps, then continue with `k`. -/
def commitLoop (tw : Nat → Bytes) (starts : Nat → Bytes) :
    Nat → Nat → List Bytes → Code targetIface TargetBreak → Code targetIface TargetBreak
  | 0, _, _, k => k
  | f + 1, t, outs, k =>
    .call (.target (tw t) (commitInput starts outs t))
      (fun y => commitLoop tw starts f (t + 1) (outs ++ [y.getD []]) k)

/-- The collision the adversary reports: the first hash input of the forgery that differs from
    the honest input of its slot and has the same digest. -/
def tcrBreak (th : TwHash) (tw : Nat → Bytes) (code : Bytes → Bytes → List Nat)
    (frame : Bytes → Bytes → Bytes → Bytes) (seed : Bytes) (starts : Nat → Bytes) (rand : Bytes)
    (F : Forger) : TargetBreak :=
  match (forgeryHashInputs th tw seed
      (forgedCode code frame seed
        (eufOutcome th tw code frame seed (honestVal th tw seed starts) rand F))
      (eufOutcome th tw code frame seed (honestVal th tw seed starts) rand F).vals).find?
      (fun e => decide (e.2 ≠ slotInput th tw seed starts e.1) &&
        decide (th seed (tw e.1) e.2 = th seed (tw e.1) (slotInput th tw seed starts e.1))) with
  | some e => ⟨tw e.1, slotInput th tw seed starts e.1, e.2⟩
  | none => ⟨[], [], []⟩

/-- **`SM-DT-TCR` reduction adversary.** Its coin supplies the chain starts, the signing
    randomizer and the forger; the seed comes from the challenger at `reveal`. -/
def tcrAdv (th : TwHash) (tw : Nat → Bytes) (code : Bytes → Bytes → List Nat)
    (frame : Bytes → Bytes → Bytes → Bytes) (starts : Nat → Bytes) (rand : Bytes) (F : Forger) :
    Code targetIface TargetBreak :=
  commitLoop tw starts 3231 0 []
    (.call .reveal (fun s => .ret (tcrBreak th tw code frame (s.getD []) starts rand F)))

/-- Targets committed after `m` slots. -/
def committedTargets (th : TwHash) (tw : Nat → Bytes) (seed : Bytes) (starts : Nat → Bytes)
    (m : Nat) : List (Bytes × Bytes) :=
  (List.range m).map (fun u => (tw u, slotInput th tw seed starts u))

/-- Challenger answers to the first `m` slots. -/
def committedOuts (th : TwHash) (tw : Nat → Bytes) (seed : Bytes) (starts : Nat → Bytes)
    (m : Nat) : List Bytes :=
  (List.range m).map (fun u => th seed (tw u) (slotInput th tw seed starts u))

private theorem getD_map_range {α : Type} (f : Nat → α) (m u : Nat) (h : u < m) (d : α) :
    ((List.range m).map f).getD u d = f u := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]
  rfl

private theorem slotInput_chain (th : TwHash) (tw : Nat → Bytes) (seed : Bytes)
    (starts : Nat → Bytes) (i p : Nat) (hi : i < 34) (hp : p < 95) :
    slotInput th tw seed starts (i * 95 + p) = honestVal th tw seed starts i p := by
  unfold slotInput
  rw [itePos (by omega : i * 95 + p < 3230)]
  have h1 : (i * 95 + p) / 95 = i := by omega
  have h2 : (i * 95 + p) % 95 = p := by omega
  rw [h1, h2]

private theorem slotInput_root (th : TwHash) (tw : Nat → Bytes) (seed : Bytes)
    (starts : Nat → Bytes) :
    slotInput th tw seed starts 3230 = rootInput (honestVal th tw seed starts) := by
  unfold slotInput
  rw [iteNeg (by decide : ¬ 3230 < 3230)]

/-- The input the adversary computes for slot `t` is the honest input of that slot. -/
theorem commitInput_eq_slotInput (th : TwHash) (tw : Nat → Bytes) (seed : Bytes)
    (starts : Nat → Bytes) (t : Nat) (ht : t ≤ 3230) :
    commitInput starts (committedOuts th tw seed starts t) t = slotInput th tw seed starts t := by
  unfold commitInput
  by_cases hlt : t < 3230
  · rw [itePos hlt]
    by_cases h0 : t % 95 = 0
    · rw [itePos h0]
      unfold slotInput
      rw [itePos hlt, h0]
      rfl
    · rw [iteNeg h0]
      unfold committedOuts
      rw [getD_map_range _ t (t - 1) (by omega)]
      have e1 : t = ((t - 1) / 95) * 95 + ((t - 1) % 95 + 1) := by omega
      have hi : (t - 1) / 95 < 34 := by omega
      have hp : (t - 1) % 95 + 1 < 95 := by omega
      have e3 : (t - 1) = ((t - 1) / 95) * 95 + (t - 1) % 95 := by omega
      have hL : slotInput th tw seed starts (t - 1) =
          honestVal th tw seed starts ((t - 1) / 95) ((t - 1) % 95) := by
        have := slotInput_chain th tw seed starts ((t - 1) / 95) ((t - 1) % 95) hi (by omega)
        rw [← e3] at this
        exact this
      have hR : slotInput th tw seed starts t =
          honestVal th tw seed starts ((t - 1) / 95) ((t - 1) % 95 + 1) := by
        have := slotInput_chain th tw seed starts ((t - 1) / 95) ((t - 1) % 95 + 1) hi hp
        rw [← e1] at this
        exact this
      rw [hL, hR, honestVal_succ, ← e3]
  · rw [iteNeg hlt]
    have ht' : t = 3230 := by omega
    subst ht'
    rw [slotInput_root]
    unfold rootInput
    refine congrArg List.flatten (List.map_congr_left (fun i hi => ?_))
    have hi' : i < 34 := List.mem_range.mp hi
    unfold committedOuts
    rw [getD_map_range _ 3230 (i * 95 + 94) (by omega), slotInput_chain th tw seed starts i 94 hi'
      (by decide)]
    exact (honestVal_succ th tw seed starts i 94).symm

/-- Running the commitment loop against the `SM-DT-TCR` challenger commits the honest inputs
    of the next `f` slots and reaches the continuation with nothing refused. -/
theorem commitLoop_play {th : TwHash} (tw : Nat → Bytes)
    (hTw : ∀ a b : Nat, tw a = tw b → a = b) (q : Nat) (seed : Bytes) (starts : Nat → Bytes)
    (k : Code targetIface TargetBreak) :
    ∀ (f t : Nat), t + f ≤ 3231 → t + f ≤ q →
      Code.play (smDtTcrOracle th q)
        (commitLoop tw starts f t (committedOuts th tw seed starts t) k)
        ⟨seed, committedTargets th tw seed starts t, false⟩ =
      Code.play (smDtTcrOracle th q) k
        ⟨seed, committedTargets th tw seed starts (t + f), false⟩
  | 0, t, _, _ => rfl
  | f + 1, t, h1, h2 => by
    have hCond : (⟨seed, committedTargets th tw seed starts t, false⟩ : TargetState).revealed = false ∧
        (⟨seed, committedTargets th tw seed starts t, false⟩ : TargetState).targets.length < q ∧
        tw t ∉ (⟨seed, committedTargets th tw seed starts t, false⟩ : TargetState).targets.map
          Prod.fst := by
      refine ⟨rfl, ?_, ?_⟩
      · show (committedTargets th tw seed starts t).length < q
        unfold committedTargets
        rw [List.length_map, List.length_range]
        omega
      · show tw t ∉ (committedTargets th tw seed starts t).map Prod.fst
        unfold committedTargets
        rw [List.map_map]
        intro hMem
        obtain ⟨u, hu, hEq⟩ := List.mem_map.mp hMem
        have hu' : u < t := List.mem_range.mp hu
        have : u = t := hTw u t hEq
        omega
    show Code.play (smDtTcrOracle th q)
        (.call (.target (tw t) (commitInput starts (committedOuts th tw seed starts t) t))
          (fun y => commitLoop tw starts f (t + 1)
            (committedOuts th tw seed starts t ++ [y.getD []]) k))
        ⟨seed, committedTargets th tw seed starts t, false⟩ = _
    rw [Code.play_call, smDtTcrOracle_target, itePos hCond,
      commitInput_eq_slotInput th tw seed starts t (by omega)]
    have hOuts : committedOuts th tw seed starts t ++
        [(some (th seed (tw t) (slotInput th tw seed starts t)) : Option Bytes).getD []] =
        committedOuts th tw seed starts (t + 1) := by
      unfold committedOuts
      rw [List.range_succ, List.map_append]
      rfl
    have hTargets : committedTargets th tw seed starts t ++
        [(tw t, slotInput th tw seed starts t)] = committedTargets th tw seed starts (t + 1) := by
      unfold committedTargets
      rw [List.range_succ, List.map_append]
      rfl
    show Code.play (smDtTcrOracle th q)
        (commitLoop tw starts f (t + 1)
          (committedOuts th tw seed starts t ++
            [(some (th seed (tw t) (slotInput th tw seed starts t)) : Option Bytes).getD []]) k)
        ⟨seed, committedTargets th tw seed starts t ++ [(tw t, slotInput th tw seed starts t)],
          false⟩ = _
    rw [hOuts, hTargets, commitLoop_play (th := th) tw hTw q seed starts k f (t + 1) (by omega) (by omega)]
    have hAdd : t + 1 + f = t + (f + 1) := by omega
    rw [hAdd]

private theorem forgeryHashInputs_slot_le (th : TwHash) (tw : Nat → Bytes) (seed : Bytes)
    (c : List Nat) (vals : List Bytes) (e : Nat × Bytes)
    (he : e ∈ forgeryHashInputs th tw seed c vals) : e.1 ≤ 3230 := by
  unfold forgeryHashInputs at he
  rcases List.mem_append.mp he with h | h
  · obtain ⟨i, hi, hIn⟩ := List.mem_flatMap.mp h
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hIn
    have hi' : i < 34 := List.mem_range.mp hi
    have hp' : p < 95 := List.mem_range.mp hp
    show i * 95 + p ≤ 3230
    omega
  · rw [List.mem_singleton.mp h]
    exact Nat.le_refl _

/-- On a colliding forgery `tcrBreak` reports a hash input of the forgery that differs from the
    honest input of its slot and has the same digest. -/
theorem tcrBreak_spec (th : TwHash) (tw : Nat → Bytes) (code : Bytes → Bytes → List Nat)
    (frame : Bytes → Bytes → Bytes → Bytes) (seed : Bytes) (starts : Nat → Bytes) (rand : Bytes)
    (F : Forger)
    (hCol : ∃ t x, (t, x) ∈ forgeryHashInputs th tw seed
        (forgedCode code frame seed
          (eufOutcome th tw code frame seed (honestVal th tw seed starts) rand F))
        (eufOutcome th tw code frame seed (honestVal th tw seed starts) rand F).vals ∧
      t ≤ 3230 ∧ x ≠ slotInput th tw seed starts t ∧
      th seed (tw t) x = th seed (tw t) (slotInput th tw seed starts t)) :
    ∃ e : Nat × Bytes, e.1 ≤ 3230 ∧
      tcrBreak th tw code frame seed starts rand F =
        ⟨tw e.1, slotInput th tw seed starts e.1, e.2⟩ ∧
      e.2 ≠ slotInput th tw seed starts e.1 ∧
      th seed (tw e.1) e.2 = th seed (tw e.1) (slotInput th tw seed starts e.1) := by
  obtain ⟨t, x, hMem, _, hNe, hEq⟩ := hCol
  unfold tcrBreak
  cases hFind : (forgeryHashInputs th tw seed
      (forgedCode code frame seed
        (eufOutcome th tw code frame seed (honestVal th tw seed starts) rand F))
      (eufOutcome th tw code frame seed (honestVal th tw seed starts) rand F).vals).find?
      (fun e => decide (e.2 ≠ slotInput th tw seed starts e.1) &&
        decide (th seed (tw e.1) e.2 = th seed (tw e.1) (slotInput th tw seed starts e.1))) with
  | none =>
    have hNone := List.find?_eq_none.mp hFind (t, x) hMem
    exact absurd (by
      show (decide (x ≠ slotInput th tw seed starts t) &&
        decide (th seed (tw t) x = th seed (tw t) (slotInput th tw seed starts t))) = true
      rw [decide_eq_true hNe, decide_eq_true hEq]
      rfl) hNone
  | some e =>
    have hP := List.find?_some hFind
    have hIn := List.mem_of_find?_eq_some hFind
    obtain ⟨hP1, hP2⟩ := band_split hP
    exact ⟨e, forgeryHashInputs_slot_le th tw seed _ _ e hIn, rfl, of_decide_eq_true hP1,
      of_decide_eq_true hP2⟩

/-- Transcript of the reduction adversary against the `SM-DT-TCR` challenger with budget
    `q ≥ 3231`: every honest slot input is a committed target and the seed is revealed. -/
theorem tcrAdv_play {th : TwHash} (tw : Nat → Bytes)
    (hTw : ∀ a b : Nat, tw a = tw b → a = b) (code : Bytes → Bytes → List Nat)
    (frame : Bytes → Bytes → Bytes → Bytes) (seed : Bytes) (starts : Nat → Bytes) (rand : Bytes)
    (F : Forger) (q : Nat) (hq : 3231 ≤ q) :
    Code.play (smDtTcrOracle th q) (tcrAdv th tw code frame starts rand F) ⟨seed, [], false⟩ =
      (tcrBreak th tw code frame seed starts rand F,
        ⟨seed, committedTargets th tw seed starts 3231, true⟩) := by
  have h0 := commitLoop_play (th := th) tw hTw q seed starts
    (.call .reveal (fun s => .ret (tcrBreak th tw code frame (s.getD []) starts rand F)))
    3231 0 (Nat.le_of_eq (Nat.zero_add 3231)) (by omega)
  rw [Nat.zero_add] at h0
  have hT0 : committedTargets th tw seed starts 0 = [] := rfl
  have hO0 : committedOuts th tw seed starts 0 = [] := rfl
  rw [hT0, hO0] at h0
  unfold tcrAdv
  rw [h0, Code.play_call, smDtTcrOracle_reveal, Code.play_ret]
  dsimp only [Option.getD_some]

private theorem mem_committedTargets {th : TwHash} (tw : Nat → Bytes) (seed : Bytes)
    (starts : Nat → Bytes) (e : Nat × Bytes) (hSlot : e.1 ≤ 3230) :
    (tw e.1, slotInput th tw seed starts e.1) ∈ committedTargets th tw seed starts 3231 := by
  unfold committedTargets
  exact List.mem_map.mpr ⟨e.1, List.mem_range.mpr (by omega), rfl⟩

private theorem tcrWin_of_collision {th : TwHash} (tw : Nat → Bytes)
    (seed : Bytes) (starts : Nat → Bytes) (e : Nat × Bytes)
    (hMemT : (tw e.1, slotInput th tw seed starts e.1) ∈ committedTargets th tw seed starts 3231)
    (hNe : e.2 ≠ slotInput th tw seed starts e.1)
    (hEq : th seed (tw e.1) e.2 = th seed (tw e.1) (slotInput th tw seed starts e.1)) :
    smDtTcrWin th ⟨seed, committedTargets th tw seed starts 3231, true⟩
      ⟨tw e.1, slotInput th tw seed starts e.1, e.2⟩ = true := by
  rw [smDtTcrWin_eq]
  dsimp only
  rw [decide_eq_true hMemT, decide_eq_true hNe, decide_eq_true hEq]
  rfl

/-- **The `SM-DT-TCR` reduction wins on a colliding forgery.** If the forgery of the real run
    evaluates the hash on an input that collides with the honest input of its slot, the
    reduction adversary wins the `SM-DT-TCR` experiment with seed `seed` and budget `q ≥ 3231`. -/
theorem tcrAdv_wins {th : TwHash} (tw : Nat → Bytes)
    (hTw : ∀ a b : Nat, tw a = tw b → a = b) (code : Bytes → Bytes → List Nat)
    (frame : Bytes → Bytes → Bytes → Bytes) (seed : Bytes) (starts : Nat → Bytes) (rand : Bytes)
    (F : Forger) (q : Nat) (hq : 3231 ≤ q)
    (hCol : ∃ t x, (t, x) ∈ forgeryHashInputs th tw seed
        (forgedCode code frame seed
          (eufOutcome th tw code frame seed (honestVal th tw seed starts) rand F))
        (eufOutcome th tw code frame seed (honestVal th tw seed starts) rand F).vals ∧
      t ≤ 3230 ∧ x ≠ slotInput th tw seed starts t ∧
      th seed (tw t) x = th seed (tw t) (slotInput th tw seed starts t)) :
    smDtTcrWin th
      (Code.play (smDtTcrOracle th q) (tcrAdv th tw code frame starts rand F) ⟨seed, [], false⟩).2
      (Code.play (smDtTcrOracle th q) (tcrAdv th tw code frame starts rand F) ⟨seed, [], false⟩).1 =
      true := by
  obtain ⟨e, hSlot, hB, hNe, hEq⟩ := tcrBreak_spec th tw code frame seed starts rand F hCol
  rw [tcrAdv_play (th := th) tw hTw code frame seed starts rand F q hq, hB]
  exact tcrWin_of_collision (th := th) tw seed starts e (mem_committedTargets tw seed starts e hSlot) hNe hEq

/-- The reduction adversary makes `3232` oracle calls: `3231` targets and `reveal`. -/
theorem tcrAdv_within (th : TwHash) (tw : Nat → Bytes) (code : Bytes → Bytes → List Nat)
    (frame : Bytes → Bytes → Bytes → Bytes) (starts : Nat → Bytes) (rand : Bytes) (F : Forger) :
    Within 3232 (tcrAdv th tw code frame starts rand F) := by
  have hLoop : ∀ (f t : Nat) (outs : List Bytes) (k : Code targetIface TargetBreak) (b : Nat),
      Within b k → Within (f + b) (commitLoop tw starts f t outs k) := by
    intro f
    induction f with
    | zero => intro t outs k b hk; rw [Nat.zero_add]; exact hk
    | succ f ih =>
      intro t outs k b hk
      have hEq : f + 1 + b = (f + b) + 1 := by omega
      rw [hEq]
      exact .call _ _ (fun y => ih (t + 1) _ k b hk)
  exact hLoop 3231 0 [] _ 1 (.call _ _ (fun _ => .ret 0 _))

/-! ## 5. Reduction to `SM-DT-PRE` at chain position `(i, j)`

The adversary asks for one target under the tweak of step `j` of chain `i`; the answer is the
value of that chain at position `j + 1`. After `reveal` it rebuilds the public key and the
signature from that value and from the other chains, which it owns, runs the forger, and
advances the forger's value on chain `i` to position `j`. -/

/-- Chain values known to the reduction at `(i, j)`: chain `i` from position `j + 1` on, computed
    from the challenge image `y`; every other chain from its start. -/
def puncturedVal (th : TwHash) (tw : Nat → Bytes) (seed : Bytes) (starts : Nat → Bytes)
    (i j : Nat) (y : Bytes) (k p : Nat) : Bytes :=
  if k = i then (if j + 1 ≤ p then chainFrom th tw seed i (j + 1) (p - (j + 1)) y else [])
  else honestVal th tw seed starts k p

/-- Preimage candidate: the forger's value on chain `i`, advanced to position `j`. -/
def preBreak (th : TwHash) (tw : Nat → Bytes) (code : Bytes → Bytes → List Nat)
    (frame : Bytes → Bytes → Bytes → Bytes) (seed : Bytes) (starts : Nat → Bytes) (i j : Nat)
    (y rand : Bytes) (F : Forger) : TargetBreak :=
  ⟨tw (i * 95 + j), [],
    chainFrom th tw seed i
      ((forgedCode code frame seed
        (eufOutcome th tw code frame seed (puncturedVal th tw seed starts i j y) rand F)).getD i 0)
      (j - (forgedCode code frame seed
        (eufOutcome th tw code frame seed (puncturedVal th tw seed starts i j y) rand F)).getD i 0)
      ((eufOutcome th tw code frame seed (puncturedVal th tw seed starts i j y) rand F).vals.getD
        i [])⟩

/-- **`SM-DT-PRE` reduction adversary at chain position `(i, j)`.** Its coin supplies the starts
    of the other chains, the signing randomizer and the forger. -/
