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
def preAdv (th : TwHash) (tw : Nat → Bytes) (code : Bytes → Bytes → List Nat)
    (frame : Bytes → Bytes → Bytes → Bytes) (starts : Nat → Bytes) (i j : Nat) (rand : Bytes)
    (F : Forger) : Code targetIface TargetBreak :=
  .call (.target (tw (i * 95 + j)) [])
    (fun y => .call .reveal
      (fun s => .ret (preBreak th tw code frame (s.getD []) starts i j (y.getD []) rand F)))

theorem preAdv_within (th : TwHash) (tw : Nat → Bytes) (code : Bytes → Bytes → List Nat)
    (frame : Bytes → Bytes → Bytes → Bytes) (starts : Nat → Bytes) (i j : Nat) (rand : Bytes)
    (F : Forger) : Within 2 (preAdv th tw code frame starts i j rand F) :=
  .call _ _ (fun _ => .call _ _ (fun _ => .ret 0 _))

private theorem honestVal_congr (th : TwHash) (tw : Nat → Bytes) (seed : Bytes)
    (starts starts' : Nat → Bytes) (k p : Nat) (h : starts' k = starts k) :
    honestVal th tw seed starts' k p = honestVal th tw seed starts k p := by
  unfold honestVal
  rw [h]

/-- The forger's transcript depends on the chain values only through the chain ends and the
    positions the signer opens. -/
theorem eufOutcome_congr (th : TwHash) (tw : Nat → Bytes) (code : Bytes → Bytes → List Nat)
    (frame : Bytes → Bytes → Bytes → Bytes) (seed : Bytes) (hv hv' : Nat → Nat → Bytes)
    (rand : Bytes) (F : Forger)
    (hEnds : ∀ k, k < 34 → hv' k 95 = hv k 95)
    (hSig : ∀ m₁, F.query seed (pkRoot th tw seed hv) = some m₁ → ∀ k, k < 34 →
      hv' k ((code rand (frame seed (pkRoot th tw seed hv) m₁)).getD k 0) =
        hv k ((code rand (frame seed (pkRoot th tw seed hv) m₁)).getD k 0)) :
    eufOutcome th tw code frame seed hv' rand F = eufOutcome th tw code frame seed hv rand F := by
  have hRoot : pkRoot th tw seed hv' = pkRoot th tw seed hv := by
    unfold pkRoot rootInput
    exact congrArg (fun l => th seed (tw 3230) (List.flatten l))
      (List.map_congr_left (fun k hk => hEnds k (List.mem_range.mp hk)))
  unfold eufOutcome
  rw [hRoot]
  cases hQ : F.query seed (pkRoot th tw seed hv) with
  | none => rfl
  | some m₁ =>
    have hVals : signVals hv' (code rand (frame seed (pkRoot th tw seed hv) m₁)) =
        signVals hv (code rand (frame seed (pkRoot th tw seed hv) m₁)) := by
      unfold signVals
      exact List.map_congr_left (fun k hk => hSig m₁ hQ k (List.mem_range.mp hk))
    show Outcome.mk _ _ _ _ _ = Outcome.mk _ _ _ _ _
    rw [hVals]

theorem eufOutcome_queried (th : TwHash) (tw : Nat → Bytes) (code : Bytes → Bytes → List Nat)
    (frame : Bytes → Bytes → Bytes → Bytes) (seed : Bytes) (hv : Nat → Nat → Bytes)
    (rand : Bytes) (F : Forger) (m₁ : Bytes)
    (hQ : F.query seed (pkRoot th tw seed hv) = some m₁) :
    (eufOutcome th tw code frame seed hv rand F).queried =
      some (m₁, code rand (frame seed (pkRoot th tw seed hv) m₁)) := by
  unfold eufOutcome
  rw [hQ]

/-- From the challenge image of the honest value at `(i, j)` and the other chain starts, the
    reduction reproduces the forger's transcript of the real run, provided the signer opens
    chain `i` above position `j`. -/
theorem puncturedOutcome_eq (th : TwHash) (tw : Nat → Bytes) (code : Bytes → Bytes → List Nat)
    (frame : Bytes → Bytes → Bytes → Bytes) (seed : Bytes) (starts starts' : Nat → Bytes)
    (i j : Nat) (hj : j < 95) (rand : Bytes) (F : Forger)
    (hStarts : ∀ k, k ≠ i → starts' k = starts k)
    (hQ : ∀ q, (eufOutcome th tw code frame seed (honestVal th tw seed starts) rand F).queried =
      some q → q.2.getD i 0 = j + 1) :
    eufOutcome th tw code frame seed
      (puncturedVal th tw seed starts' i j (honestVal th tw seed starts i (j + 1))) rand F =
      eufOutcome th tw code frame seed (honestVal th tw seed starts) rand F := by
  refine eufOutcome_congr th tw code frame seed _ _ rand F (fun k _ => ?_) (fun m₁ hm k _ => ?_)
  · unfold puncturedVal
    by_cases hk : k = i
    · rw [itePos hk, itePos (by omega : j + 1 ≤ 95), honestVal_advance, hk]
      congr 1
      omega
    · rw [iteNeg hk]
      exact honestVal_congr th tw seed starts starts' k 95 (hStarts k hk)
  · unfold puncturedVal
    by_cases hk : k = i
    · have hOpen := hQ _ (eufOutcome_queried th tw code frame seed _ rand F m₁ hm)
      have hOpen' : (code rand (frame seed (pkRoot th tw seed (honestVal th tw seed starts)) m₁)).getD
          i 0 = j + 1 := hOpen
      rw [itePos hk, hk, hOpen', itePos (Nat.le_refl _), Nat.sub_self]
      rfl
    · rw [iteNeg hk]
      exact honestVal_congr th tw seed starts starts' k _ (hStarts k hk)

/-- Transcript of the reduction adversary against the one-target `SM-DT-PRE` challenger. -/
theorem preAdv_play {th : TwHash} (tw : Nat → Bytes)
    (code : Bytes → Bytes → List Nat) (frame : Bytes → Bytes → Bytes → Bytes) (seed : Bytes)
    (starts : Nat → Bytes) (i j : Nat) (rand : Bytes) (F : Forger) (hidden : Nat → Bytes) :
    Code.play (smDtPreOracle th 1 hidden) (preAdv th tw code frame starts i j rand F)
        ⟨seed, [], false⟩ =
      (preBreak th tw code frame seed starts i j (th seed (tw (i * 95 + j)) (hidden 0)) rand F,
        ⟨seed, [(tw (i * 95 + j), hidden 0)], true⟩) := by
  have hCond : (⟨seed, [], false⟩ : TargetState).revealed = false ∧
      (⟨seed, [], false⟩ : TargetState).targets.length < 1 ∧
      tw (i * 95 + j) ∉ (⟨seed, [], false⟩ : TargetState).targets.map Prod.fst :=
    ⟨rfl, Nat.one_pos, fun h => nomatch h⟩
  unfold preAdv
  rw [Code.play_call, smDtPreOracle_target, itePos hCond, Code.play_call, smDtPreOracle_reveal,
    Code.play_ret]
  dsimp only [Option.getD_some, List.nil_append, List.length_nil]

private theorem preWin_of_preimage {th : TwHash} (seed tweak hid cand : Bytes)
    (h : th seed tweak cand = th seed tweak hid) :
    smDtPreWin th ⟨seed, [(tweak, hid)], true⟩ ⟨tweak, [], cand⟩ = true := by
  rw [smDtPreWin_eq]
  dsimp only [List.any_cons, List.any_nil]
  rw [decide_eq_true (rfl : tweak = tweak), decide_eq_true h]
  rfl

/-- **The `SM-DT-PRE` reduction wins when the forgery carries the honest value at `(i, j)`.**
    `starts` are the chain starts of the real run and `hidden 0` is the honest value of chain
    `i` at position `j`; the adversary is run on `starts'`, which agrees with `starts` off
    chain `i`. -/
theorem preAdv_wins {th : TwHash} (tw : Nat → Bytes)
    (code : Bytes → Bytes → List Nat) (frame : Bytes → Bytes → Bytes → Bytes) (seed : Bytes)
    (starts starts' : Nat → Bytes) (i j : Nat) (hj : j < 95) (rand : Bytes) (F : Forger)
    (hidden : Nat → Bytes)
    (hStarts : ∀ k, k ≠ i → starts' k = starts k)
    (hHid : hidden 0 = honestVal th tw seed starts i j)
    (hQ : ∀ q, (eufOutcome th tw code frame seed (honestVal th tw seed starts) rand F).queried =
      some q → q.2.getD i 0 = j + 1)
    (hCand : chainFrom th tw seed i
        ((forgedCode code frame seed
          (eufOutcome th tw code frame seed (honestVal th tw seed starts) rand F)).getD i 0)
        (j - (forgedCode code frame seed
          (eufOutcome th tw code frame seed (honestVal th tw seed starts) rand F)).getD i 0)
        ((eufOutcome th tw code frame seed (honestVal th tw seed starts) rand F).vals.getD i []) =
      honestVal th tw seed starts i j) :
    smDtPreWin th
      (Code.play (smDtPreOracle th 1 hidden) (preAdv th tw code frame starts' i j rand F)
        ⟨seed, [], false⟩).2
      (Code.play (smDtPreOracle th 1 hidden) (preAdv th tw code frame starts' i j rand F)
        ⟨seed, [], false⟩).1 = true := by
  have hY : th seed (tw (i * 95 + j)) (hidden 0) = honestVal th tw seed starts i (j + 1) := by
    rw [hHid, honestVal_succ]
  have hBreak : preBreak th tw code frame seed starts' i j
      (th seed (tw (i * 95 + j)) (hidden 0)) rand F =
      ⟨tw (i * 95 + j), [], honestVal th tw seed starts i j⟩ := by
    unfold preBreak
    rw [hY, puncturedOutcome_eq th tw code frame seed starts starts' i j hj rand F hStarts hQ, hCand]
  rw [preAdv_play (th := th) tw code frame seed starts' i j rand F hidden, hBreak]
  exact preWin_of_preimage (th := th) seed _ _ _ (by rw [hHid])

/-! ## 6. Reduction to `ITSR`

The subset selected by a randomizer and a framed message is the set of opened positions of its
codeword. The adversary owns the whole key, asks the challenger for the signing randomizer, and
outputs the forger's randomizer and framed message. -/

/-- Opened positions of a codeword: digit `d` of chain `i` is the number `i * 96 + d`. -/
@[expose] def codeSubset (code : Bytes → Bytes → List Nat) (rand msg : Bytes) : List Nat :=
  (List.range (code rand msg).length).map (fun i => i * 96 + (code rand msg).getD i 0)

/-- **`ITSR` reduction adversary.** Its coin supplies the seed, the chain starts and the
    forger. -/
def itsrAdv (th : TwHash) (tw : Nat → Bytes) (code : Bytes → Bytes → List Nat)
    (frame : Bytes → Bytes → Bytes → Bytes) (seed : Bytes) (starts : Nat → Bytes) (F : Forger) :
    Code byteOracleIface (Bytes × Bytes) :=
  match F.query seed (pkRoot th tw seed (honestVal th tw seed starts)) with
  | none =>
    .ret ((F.forge seed (pkRoot th tw seed (honestVal th tw seed starts)) none).2.1,
      frame seed (pkRoot th tw seed (honestVal th tw seed starts))
        (F.forge seed (pkRoot th tw seed (honestVal th tw seed starts)) none).1)
  | some m₁ =>
    .call (frame seed (pkRoot th tw seed (honestVal th tw seed starts)) m₁)
      (fun rand =>
        .ret ((eufOutcome th tw code frame seed (honestVal th tw seed starts) rand F).rand,
          frame seed (pkRoot th tw seed (honestVal th tw seed starts))
            (eufOutcome th tw code frame seed (honestVal th tw seed starts) rand F).msg))

theorem itsrAdv_within (th : TwHash) (tw : Nat → Bytes) (code : Bytes → Bytes → List Nat)
    (frame : Bytes → Bytes → Bytes → Bytes) (seed : Bytes) (starts : Nat → Bytes) (F : Forger) :
    Within 1 (itsrAdv th tw code frame seed starts F) := by
  unfold itsrAdv
  cases F.query seed (pkRoot th tw seed (honestVal th tw seed starts)) with
  | none => exact .ret 1 _
  | some m₁ => exact .call _ _ (fun _ => .ret 0 _)

theorem eufOutcome_root (th : TwHash) (tw : Nat → Bytes) (code : Bytes → Bytes → List Nat)
    (frame : Bytes → Bytes → Bytes → Bytes) (seed : Bytes) (hv : Nat → Nat → Bytes)
    (rand : Bytes) (F : Forger) :
    (eufOutcome th tw code frame seed hv rand F).root = pkRoot th tw seed hv := by
  unfold eufOutcome
  cases F.query seed (pkRoot th tw seed hv) <;> rfl

/-- **The `ITSR` reduction wins when the forgery repeats the signed codeword.** -/
theorem itsrAdv_wins {code : Bytes → Bytes → List Nat}
    (th : TwHash) (tw : Nat → Bytes) (frame : Bytes → Bytes → Bytes → Bytes)
    (hFrame : ∀ s r m m' : Bytes, frame s r m = frame s r m' → m = m')
    (seed : Bytes) (starts : Nat → Bytes) (F : Forger) (randOf : Nat → Bytes) (q : Nat)
    (hq : 1 ≤ q)
    (hCase : ∃ q₀,
      (eufOutcome th tw code frame seed (honestVal th tw seed starts) (randOf 0) F).queried =
        some q₀ ∧
      (eufOutcome th tw code frame seed (honestVal th tw seed starts) (randOf 0) F).msg ≠ q₀.1 ∧
      forgedCode code frame seed
        (eufOutcome th tw code frame seed (honestVal th tw seed starts) (randOf 0) F) = q₀.2) :
    itsrWin (codeSubset code)
      (Code.play (itsrOracle q randOf) (itsrAdv th tw code frame seed starts F) []).2
      (Code.play (itsrOracle q randOf) (itsrAdv th tw code frame seed starts F) []).1 = true := by
  obtain ⟨q₀, hQd, hFresh, hSame⟩ := hCase
  cases hQ : F.query seed (pkRoot th tw seed (honestVal th tw seed starts)) with
  | none =>
    have hNone : (eufOutcome th tw code frame seed (honestVal th tw seed starts) (randOf 0)
        F).queried = none := by
      unfold eufOutcome
      rw [hQ]
    rw [hNone] at hQd
    cases hQd
  | some m₁ =>
    have hQd' := eufOutcome_queried th tw code frame seed (honestVal th tw seed starts)
      (randOf 0) F m₁ hQ
    rw [hQd] at hQd'
    injection hQd' with hq₀
    have hPlay : Code.play (itsrOracle q randOf) (itsrAdv th tw code frame seed starts F) [] =
        (((eufOutcome th tw code frame seed (honestVal th tw seed starts) (randOf 0) F).rand,
          frame seed (pkRoot th tw seed (honestVal th tw seed starts))
            (eufOutcome th tw code frame seed (honestVal th tw seed starts) (randOf 0) F).msg),
          [(randOf 0, frame seed (pkRoot th tw seed (honestVal th tw seed starts)) m₁)]) := by
      unfold itsrAdv
      rw [hQ]
      show Code.play (itsrOracle q randOf) (.call _ _) [] = _
      rw [Code.play_call, itsrOracle_eq, itePos (show ([] : List (Bytes × Bytes)).length < q from hq),
        Code.play_ret]
      rfl
    rw [hPlay, itsrWin_eq]
    have hMsgNe : (eufOutcome th tw code frame seed (honestVal th tw seed starts) (randOf 0)
        F).msg ≠ m₁ := by
      rw [hq₀] at hFresh
      exact hFresh
    have hFreshPair : ¬ (((eufOutcome th tw code frame seed (honestVal th tw seed starts)
        (randOf 0) F).rand,
        frame seed (pkRoot th tw seed (honestVal th tw seed starts))
          (eufOutcome th tw code frame seed (honestVal th tw seed starts) (randOf 0) F).msg) ∈
        [(randOf 0, frame seed (pkRoot th tw seed (honestVal th tw seed starts)) m₁)]) := by
      intro hMem
      have hEq := List.mem_singleton.mp hMem
      injection hEq with _ hFr
      exact hMsgNe (hFrame _ _ _ _ hFr)
    have hSub : codeSubset code
        (eufOutcome th tw code frame seed (honestVal th tw seed starts) (randOf 0) F).rand
        (frame seed (pkRoot th tw seed (honestVal th tw seed starts))
          (eufOutcome th tw code frame seed (honestVal th tw seed starts) (randOf 0) F).msg) =
        codeSubset code (randOf 0)
          (frame seed (pkRoot th tw seed (honestVal th tw seed starts)) m₁) := by
      have hSame' : code
          (eufOutcome th tw code frame seed (honestVal th tw seed starts) (randOf 0) F).rand
          (frame seed (pkRoot th tw seed (honestVal th tw seed starts))
            (eufOutcome th tw code frame seed (honestVal th tw seed starts) (randOf 0) F).msg) =
          code (randOf 0) (frame seed (pkRoot th tw seed (honestVal th tw seed starts)) m₁) := by
        have h1 := hSame
        unfold forgedCode at h1
        rw [eufOutcome_root] at h1
        rw [h1, hq₀]
      unfold codeSubset
      rw [hSame']
    dsimp only
    rw [decide_eq_false hFreshPair, hSub]
    refine (Bool.and_eq_true _ _).mpr ⟨rfl, List.all_eq_true.mpr (fun x hx => ?_)⟩
    exact List.any_eq_true.mpr ⟨_, List.mem_singleton.mpr rfl, decide_eq_true hx⟩

/-! ## 7. The closed experiment

The coin of the forgery experiment has four independent uniform coordinates: the public seed,
the signing randomizer, the `34` chain starts (`32` bytes each) and the forger's coin. Each
reduction reads its challenger's sample from one presentation of the same coin space:
`splitSeed` (the seed) for `SM-DT-TCR`, `splitItsr` (the randomizer) for `ITSR`, and
`splitLink i` (the seed and the start of chain `i`) for the preimage experiments of chain
`i`. -/

/-- Number of coins of the uniform `32`-byte sampler. -/
abbrev nB : Nat := Qsag.pow256 32

theorem nB_pos : 0 < nB := Qsag.pow256_pos 32

/-- Coin space of the forgery experiment for a forger with `nF` coins. -/
abbrev eufCoins (nF : Nat) : Nat := nB * (nB * (powN nB 34 * nF))

theorem eufCoins_pos {nF : Nat} (hF : 0 < nF) : 0 < eufCoins nF :=
  Nat.mul_pos nB_pos (Nat.mul_pos nB_pos (Nat.mul_pos (powN_pos nB_pos 34) hF))

private theorem ditePos {α : Type} {p : Prop} [Decidable p] (hp : p) (t : p → α) (e : ¬ p → α) :
    dite p t e = t hp := by
  cases ‹Decidable p› with
  | isTrue _ => rfl
  | isFalse hn => exact False.elim (hn hp)

private theorem diteNeg {α : Type} {p : Prop} [Decidable p] (hnp : ¬ p) (t : p → α) (e : ¬ p → α) :
    dite p t e = e hnp := by
  cases ‹Decidable p› with
  | isTrue hp => exact False.elim (hnp hp)
  | isFalse _ => rfl

/-- Chain starts encoded by a vector of `34` digits: start `k` is the `k`-th digit. -/
def startsOf (v : Fin (powN nB 34)) (k : Nat) : Bytes :=
  if h : k < 34 then Qsag.byteVecSampler 32 ((digitSplit nB 33 ⟨k, h⟩).chal v) else []

/-- The seed is the challenger coordinate. -/
abbrev splitSeed (nF : Nat) : CoinSplit (eufCoins nF) nB (nB * (powN nB 34 * nF)) :=
  CoinSplit.prod nB (nB * (powN nB 34 * nF))

/-- Inside the remaining coordinates, the signing randomizer. -/
abbrev splitRand (nF : Nat) : CoinSplit (nB * (powN nB 34 * nF)) nB (powN nB 34 * nF) :=
  CoinSplit.prod nB (powN nB 34 * nF)

/-- Inside the remaining coordinates, the vector of chain starts and the forger's coin. -/
abbrev splitStarts (nF : Nat) : CoinSplit (powN nB 34 * nF) (powN nB 34) nF :=
  CoinSplit.prod (powN nB 34) nF

/-- The signing randomizer is the challenger coordinate. -/
def splitItsr (nF : Nat) : CoinSplit (eufCoins nF) nB (nB * (powN nB 34 * nF)) :=
  pullFromAdv (splitSeed nF) (splitRand nF)

/-- The seed and the start of chain `i` are the challenger coordinate. -/
def splitLink (nF : Nat) (i : Fin 34) :
    CoinSplit (eufCoins nF) (nB * nB) (nB * (powN nB 33 * nF)) :=
  joinChal (splitSeed nF)
    (pullFromAdv (splitRand nF) (pullFromChal (splitStarts nF) (digitSplit nB 33 i)))

/-- Seed of the run on coin `ω`. -/
def seedAt {nF : Nat} (ω : Fin (eufCoins nF)) : Bytes :=
  Qsag.byteVecSampler 32 ((splitSeed nF).chal ω)

/-- Signing randomizer of the run on coin `ω`. -/
def randAt {nF : Nat} (ω : Fin (eufCoins nF)) : Bytes :=
  Qsag.byteVecSampler 32 ((splitRand nF).chal ((splitSeed nF).advc ω))

/-- Digit vector of the chain starts of the run on coin `ω`. -/
def startsIxAt {nF : Nat} (ω : Fin (eufCoins nF)) : Fin (powN nB 34) :=
  (splitStarts nF).chal ((splitRand nF).advc ((splitSeed nF).advc ω))

/-- Forger coin of the run on coin `ω`. -/
def forgerIxAt {nF : Nat} (ω : Fin (eufCoins nF)) : Fin nF :=
  (splitStarts nF).advc ((splitRand nF).advc ((splitSeed nF).advc ω))

/-- **Closed one-time EUF-CMA experiment** of the target-sum Winternitz scheme: the challenger
    samples the seed, the chain starts and the signing randomizer; the forger sees the public
    key, may obtain one signature, and wins with a verifying signature on another message. -/
def eufGame {nF : Nat} (hPos : 0 < eufCoins nF) (th : TwHash) (tw : Nat → Bytes)
    (code : Bytes → Bytes → List Nat) (frame : Bytes → Bytes → Bytes → Bytes)
    (forger : Fin nF → Forger) : FinGame (eufCoins nF) :=
  ⟨hPos, fun ω =>
    eufWin th tw code frame (seedAt ω)
      (eufOutcome th tw code frame (seedAt ω)
        (honestVal th tw (seedAt ω) (startsOf (startsIxAt ω))) (randAt ω)
        (forger (forgerIxAt ω)))⟩

theorem eufGame_win_eq {nF : Nat} (hPos : 0 < eufCoins nF) (th : TwHash) (tw : Nat → Bytes)
    (code : Bytes → Bytes → List Nat) (frame : Bytes → Bytes → Bytes → Bytes)
    (forger : Fin nF → Forger) (ω : Fin (eufCoins nF)) :
    (eufGame hPos th tw code frame forger).win ω =
      eufWin th tw code frame (seedAt ω)
        (eufOutcome th tw code frame (seedAt ω)
          (honestVal th tw (seedAt ω) (startsOf (startsIxAt ω))) (randAt ω)
          (forger (forgerIxAt ω))) := by rfl

theorem honestVal_eq (th : TwHash) (tw : Nat → Bytes) (seed : Bytes) (starts : Nat → Bytes)
    (i p : Nat) : honestVal th tw seed starts i p = chainFrom th tw seed i 0 p (starts i) := by rfl

theorem seedAt_length {nF : Nat} (ω : Fin (eufCoins nF)) : (seedAt ω).length = 32 :=
  Qsag.byteVecSampler_length 32 _

theorem randAt_length {nF : Nat} (ω : Fin (eufCoins nF)) : (randAt ω).length = 32 :=
  Qsag.byteVecSampler_length 32 _

theorem startsOf_length_eq (v : Fin (powN nB 34)) (i : Nat) (hi : i < 34) :
    (startsOf v i).length = 32 := by
  unfold startsOf
  rw [ditePos hi]
  exact Qsag.byteVecSampler_length 32 _

/-! ### The reduction adversaries as functions of their coin coordinate -/

/-- `SM-DT-TCR` adversary on the adversary coordinate of `splitSeed`. -/
def tcrAdvAt {nF : Nat} (th : TwHash) (tw : Nat → Bytes) (code : Bytes → Bytes → List Nat)
    (frame : Bytes → Bytes → Bytes → Bytes) (forger : Fin nF → Forger)
    (a : Fin (nB * (powN nB 34 * nF))) : Code targetIface TargetBreak :=
  tcrAdv th tw code frame (startsOf ((splitStarts nF).chal ((splitRand nF).advc a)))
    (Qsag.byteVecSampler 32 ((splitRand nF).chal a))
    (forger ((splitStarts nF).advc ((splitRand nF).advc a)))

/-- `ITSR` adversary on the adversary coordinate of `splitItsr`. -/
def itsrAdvAt {nF : Nat} (th : TwHash) (tw : Nat → Bytes) (code : Bytes → Bytes → List Nat)
    (frame : Bytes → Bytes → Bytes → Bytes) (forger : Fin nF → Forger)
    (b : Fin (nB * (powN nB 34 * nF))) : Code byteOracleIface (Bytes × Bytes) :=
  itsrAdv th tw code frame
    (Qsag.byteVecSampler 32 ((CoinSplit.prod nB (powN nB 34 * nF)).chal b))
    (startsOf ((splitStarts nF).chal ((CoinSplit.prod nB (powN nB 34 * nF)).advc b)))
    (forger ((splitStarts nF).advc ((CoinSplit.prod nB (powN nB 34 * nF)).advc b)))

/-- Preimage adversary for position `j` of chain `i`, on the adversary coordinate of
    `splitLink i`. The start of chain `i` is not among its coordinates; digit `0` stands in. -/
def linkAdvAt {nF : Nat} (th : TwHash) (tw : Nat → Bytes) (code : Bytes → Bytes → List Nat)
    (frame : Bytes → Bytes → Bytes → Bytes) (forger : Fin nF → Forger) (i : Fin 34) (j : Nat)
    (b : Fin (nB * (powN nB 33 * nF))) : Code targetIface TargetBreak :=
  preAdv th tw code frame
    (startsOf ((digitSplit nB 33 i).pair ⟨0, nB_pos⟩
      ((CoinSplit.prod (powN nB 33) nF).chal ((CoinSplit.prod nB (powN nB 33 * nF)).advc b))))
    i.1 j
    (Qsag.byteVecSampler 32 ((CoinSplit.prod nB (powN nB 33 * nF)).chal b))
    (forger ((CoinSplit.prod (powN nB 33) nF).advc ((CoinSplit.prod nB (powN nB 33 * nF)).advc b)))

/-- Challenger sample of the preimage experiments: a seed and one chain start. -/
def linkSample (z : Fin (nB * nB)) : Bytes × Bytes :=
  (Qsag.byteVecSampler 32 ((CoinSplit.prod nB nB).chal z),
    Qsag.byteVecSampler 32 ((CoinSplit.prod nB nB).advc z))

/-- **Preimage experiment for position `j` of chain `i`**: the `SM-DT-PRE` experiment with one
    target whose hidden input is the honest value of chain `i` at position `j`. -/
def linkGame {nF : Nat} (hPos : 0 < eufCoins nF) (th : TwHash) (tw : Nat → Bytes)
    (code : Bytes → Bytes → List Nat) (frame : Bytes → Bytes → Bytes → Bytes)
    (forger : Fin nF → Forger) (i : Fin 34) (j : Nat) : FinGame (eufCoins nF) :=
  smDtPreGame hPos th 1 (fun ω => (linkSample ((splitLink nF i).chal ω)).1)
    (fun ω k =>
      [chainFrom th tw (linkSample ((splitLink nF i).chal ω)).1 i.1 0 j
        (linkSample ((splitLink nF i).chal ω)).2].getD k [])
    (fun ω => linkAdvAt th tw code frame forger i j ((splitLink nF i).advc ω))

/-! ### Coordinates of a coin under the three presentations -/

private theorem linkSample_seed {nF : Nat} (i : Fin 34) (ω : Fin (eufCoins nF)) :
    (linkSample ((splitLink nF i).chal ω)).1 = seedAt ω := by
  show Qsag.byteVecSampler 32 ((CoinSplit.prod nB nB).chal ((CoinSplit.prod nB nB).pair _ _)) = _
  rw [(CoinSplit.prod nB nB).chal_pair]
  rfl

private theorem linkSample_start {nF : Nat} (i : Fin 34) (ω : Fin (eufCoins nF)) :
    (linkSample ((splitLink nF i).chal ω)).2 = startsOf (startsIxAt ω) i.1 := by
  show Qsag.byteVecSampler 32 ((CoinSplit.prod nB nB).advc ((CoinSplit.prod nB nB).pair _ _)) = _
  rw [(CoinSplit.prod nB nB).advc_pair]
  unfold startsOf
  rw [ditePos i.2]
  rfl

private theorem linkAdvAt_eq {nF : Nat} (th : TwHash) (tw : Nat → Bytes)
    (code : Bytes → Bytes → List Nat) (frame : Bytes → Bytes → Bytes → Bytes)
    (forger : Fin nF → Forger) (i : Fin 34) (j : Nat) (ω : Fin (eufCoins nF)) :
    linkAdvAt th tw code frame forger i j ((splitLink nF i).advc ω) =
      preAdv th tw code frame
        (startsOf ((digitSplit nB 33 i).pair ⟨0, nB_pos⟩
          ((digitSplit nB 33 i).advc (startsIxAt ω))))
        i.1 j (randAt ω) (forger (forgerIxAt ω)) := by
  unfold linkAdvAt
  show preAdv th tw code frame
      (startsOf ((digitSplit nB 33 i).pair ⟨0, nB_pos⟩
        ((CoinSplit.prod (powN nB 33) nF).chal ((CoinSplit.prod nB (powN nB 33 * nF)).advc
          ((CoinSplit.prod nB (powN nB 33 * nF)).pair _
            ((CoinSplit.prod (powN nB 33) nF).pair _ _))))))
      i.1 j
      (Qsag.byteVecSampler 32 ((CoinSplit.prod nB (powN nB 33 * nF)).chal
        ((CoinSplit.prod nB (powN nB 33 * nF)).pair _ _)))
      (forger ((CoinSplit.prod (powN nB 33) nF).advc ((CoinSplit.prod nB (powN nB 33 * nF)).advc
        ((CoinSplit.prod nB (powN nB 33 * nF)).pair _
          ((CoinSplit.prod (powN nB 33) nF).pair _ _))))) = _
  rw [(CoinSplit.prod nB (powN nB 33 * nF)).advc_pair, (CoinSplit.prod nB (powN nB 33 * nF)).chal_pair,
    (CoinSplit.prod (powN nB 33) nF).chal_pair, (CoinSplit.prod (powN nB 33) nF).advc_pair]
  rfl

/-- Off chain `i`, the starts the preimage adversary computes are the starts of the run. -/
private theorem startsOf_punctured (i : Fin 34) (v : Fin (powN nB 34)) (k : Nat) (hk : k ≠ i.1) :
    startsOf ((digitSplit nB 33 i).pair ⟨0, nB_pos⟩ ((digitSplit nB 33 i).advc v)) k =
      startsOf v k := by
  unfold startsOf
  by_cases h : k < 34
  · rw [ditePos h, ditePos h]
    have hne : i ≠ ⟨k, h⟩ := fun e => hk (by rw [e])
    have hEta : v = (digitSplit nB 33 i).pair ((digitSplit nB 33 i).chal v)
        ((digitSplit nB 33 i).advc v) := ((digitSplit nB 33 i).pair_eta v).symm
    have hInd := digitSplit_chal_pair_ne nB 33 i ⟨k, h⟩ hne ⟨0, nB_pos⟩
      ((digitSplit nB 33 i).chal v) ((digitSplit nB 33 i).advc v)
    rw [hInd, ← hEta]
  · rw [diteNeg h, diteNeg h]

private theorem itsrAdvAt_eq {nF : Nat} (th : TwHash) (tw : Nat → Bytes)
    (code : Bytes → Bytes → List Nat) (frame : Bytes → Bytes → Bytes → Bytes)
    (forger : Fin nF → Forger) (ω : Fin (eufCoins nF)) :
    itsrAdvAt th tw code frame forger ((splitItsr nF).advc ω) =
      itsrAdv th tw code frame (seedAt ω) (startsOf (startsIxAt ω)) (forger (forgerIxAt ω)) := by
  unfold itsrAdvAt
  show itsrAdv th tw code frame
      (Qsag.byteVecSampler 32 ((CoinSplit.prod nB (powN nB 34 * nF)).chal
        ((CoinSplit.prod nB (powN nB 34 * nF)).pair _ _)))
      (startsOf ((splitStarts nF).chal ((CoinSplit.prod nB (powN nB 34 * nF)).advc
        ((CoinSplit.prod nB (powN nB 34 * nF)).pair _ _))))
      (forger ((splitStarts nF).advc ((CoinSplit.prod nB (powN nB 34 * nF)).advc
        ((CoinSplit.prod nB (powN nB 34 * nF)).pair _ _)))) = _
  rw [(CoinSplit.prod nB (powN nB 34 * nF)).chal_pair, (CoinSplit.prod nB (powN nB 34 * nF)).advc_pair]
  rfl

/-! ### Uniformity of the challenger samplers -/

theorem uniformOn_linkSample :
    UniformOn (fun x : Bytes × Bytes => x.1.length = 32 ∧ x.2.length = 32) linkSample where
  mem z := ⟨Qsag.byteVecSampler_length 32 _, Qsag.byteVecSampler_length 32 _⟩
  injective z z' h := by
    have h1 : (CoinSplit.prod nB nB).chal z = (CoinSplit.prod nB nB).chal z' :=
      (Qsag.uniformOn_byteVecSampler 32).injective _ _ (congrArg Prod.fst h)
    have h2 : (CoinSplit.prod nB nB).advc z = (CoinSplit.prod nB nB).advc z' :=
      (Qsag.uniformOn_byteVecSampler 32).injective _ _ (congrArg Prod.snd h)
    rw [← (CoinSplit.prod nB nB).pair_eta z, ← (CoinSplit.prod nB nB).pair_eta z', h1, h2]
  surjective x hx := by
    obtain ⟨c₁, hc₁⟩ := (Qsag.uniformOn_byteVecSampler 32).surjective x.1 hx.1
    obtain ⟨c₂, hc₂⟩ := (Qsag.uniformOn_byteVecSampler 32).surjective x.2 hx.2
    refine ⟨(CoinSplit.prod nB nB).pair c₁ c₂, ?_⟩
    unfold linkSample
    rw [(CoinSplit.prod nB nB).chal_pair, (CoinSplit.prod nB nB).advc_pair, hc₁, hc₂]

/-- The start-of-chain sample in the shape of the `SM-DT-PRE` challenger. -/
def startSample (z : Fin (nB * nB)) : Bytes × List Bytes :=
  ((linkSample z).1, [(linkSample z).2])

theorem uniformOn_startSample :
    UniformOn (SmDtPreSampleOk 32 32 1) startSample where
  mem z := (preSampleOk_iff 32 32 1 _).mpr
    ⟨(uniformOn_linkSample.mem z).1, rfl, fun h hh => by
      rw [List.mem_singleton.mp hh]
      exact (uniformOn_linkSample.mem z).2⟩
  injective z z' h := by
    have h1a : (startSample z).1 = (startSample z').1 := congrArg Prod.fst h
    have h2a : (startSample z).2 = (startSample z').2 := congrArg Prod.snd h
    have h1 : (linkSample z).1 = (linkSample z').1 := h1a
    have h2 : [(linkSample z).2] = [(linkSample z').2] := h2a
    injection h2 with h3
    exact uniformOn_linkSample.injective z z' (Prod.ext h1 h3)
  surjective x hx := by
    obtain ⟨h1, h2, h3⟩ := (preSampleOk_iff 32 32 1 x).mp hx
    obtain ⟨s, l⟩ := x
    match l, h2, h3 with
    | [y], _, h3 =>
      obtain ⟨z, hz⟩ := uniformOn_linkSample.surjective (s, y) ⟨h1, h3 y (List.mem_singleton.mpr rfl)⟩
      refine ⟨z, ?_⟩
      unfold startSample
      rw [hz]

/-- The signing-randomizer sample in the shape of the `ITSR` challenger. -/
def randSample (c : Fin nB) : List Bytes := [Qsag.byteVecSampler 32 c]

theorem uniformOn_randSample :
    UniformOn (ItsrSampleOk 32 1) randSample where
  mem c := (itsrSampleOk_iff 32 1 _).mpr ⟨rfl, fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact Qsag.byteVecSampler_length 32 c⟩
  injective c c' h := by
    have h2 : [Qsag.byteVecSampler 32 c] = [Qsag.byteVecSampler 32 c'] := h
    injection h2 with h3
    exact (Qsag.uniformOn_byteVecSampler 32).injective c c' h3
  surjective x hx := by
    obtain ⟨h1, h2⟩ := (itsrSampleOk_iff 32 1 x).mp hx
    match x, h1, h2 with
    | [y], _, h2 =>
      obtain ⟨c, hc⟩ := (Qsag.uniformOn_byteVecSampler 32).surjective y
        (h2 y (List.mem_singleton.mpr rfl))
      exact ⟨c, by unfold randSample; rw [hc]⟩

/-! ### Every winning coin is a winning coin of a reduction -/

/-- The `ITSR` experiment of the reduction. -/
def itsrGameOf {nF : Nat} (hPos : 0 < eufCoins nF) (th : TwHash) (tw : Nat → Bytes)
    (code : Bytes → Bytes → List Nat) (frame : Bytes → Bytes → Bytes → Bytes)
    (forger : Fin nF → Forger) : FinGame (eufCoins nF) :=
  itsrGame hPos (codeSubset code) 1 (fun ω k => (randSample ((splitItsr nF).chal ω)).getD k [])
    (fun ω => itsrAdvAt th tw code frame forger ((splitItsr nF).advc ω))

/-- The `SM-DT-TCR` experiment of the reduction: `3231` targets. -/
def tcrGameOf {nF : Nat} (hPos : 0 < eufCoins nF) (th : TwHash) (tw : Nat → Bytes)
    (code : Bytes → Bytes → List Nat) (frame : Bytes → Bytes → Bytes → Bytes)
    (forger : Fin nF → Forger) : FinGame (eufCoins nF) :=
  smDtTcrGame hPos th 3231 (fun ω => Qsag.byteVecSampler 32 ((splitSeed nF).chal ω))
    (fun ω => tcrAdvAt th tw code frame forger ((splitSeed nF).advc ω))

/-- A coin on which the forgery carries the honest value of chain `i` at position `j`, below
    what the signer opened, is a winning coin of the preimage experiment at `(i, j)`. -/
theorem linkGame_win {th : TwHash} (tw : Nat → Bytes)
    (code : Bytes → Bytes → List Nat) (frame : Bytes → Bytes → Bytes → Bytes) {nF : Nat}
    (hPos : 0 < eufCoins nF) (forger : Fin nF → Forger) (i : Fin 34) (j : Nat) (hj : j < 95)
    (ω : Fin (eufCoins nF))
    (hQ : ∀ q, (eufOutcome th tw code frame (seedAt ω)
        (honestVal th tw (seedAt ω) (startsOf (startsIxAt ω))) (randAt ω)
        (forger (forgerIxAt ω))).queried = some q → q.2.getD i.1 0 = j + 1)
    (hCand : chainFrom th tw (seedAt ω) i.1
        ((forgedCode code frame (seedAt ω)
          (eufOutcome th tw code frame (seedAt ω)
            (honestVal th tw (seedAt ω) (startsOf (startsIxAt ω))) (randAt ω)
            (forger (forgerIxAt ω)))).getD i.1 0)
        (j - (forgedCode code frame (seedAt ω)
          (eufOutcome th tw code frame (seedAt ω)
            (honestVal th tw (seedAt ω) (startsOf (startsIxAt ω))) (randAt ω)
            (forger (forgerIxAt ω)))).getD i.1 0)
        ((eufOutcome th tw code frame (seedAt ω)
          (honestVal th tw (seedAt ω) (startsOf (startsIxAt ω))) (randAt ω)
          (forger (forgerIxAt ω))).vals.getD i.1 []) =
      honestVal th tw (seedAt ω) (startsOf (startsIxAt ω)) i.1 j) :
    (linkGame hPos th tw code frame forger i j).win ω = true := by
  unfold linkGame
  rw [smDtPreGame.public_eqs]
  show smDtPreWin th (smDtPreRun th 1 _ _ _ ω).2 (smDtPreRun th 1 _ _ _ ω).1 = true
  rw [smDtPreRun.public_eqs, linkSample_seed, linkSample_start, linkAdvAt_eq]
  exact preAdv_wins (th := th) tw code frame (seedAt ω) (startsOf (startsIxAt ω)) _ i.1 j hj (randAt ω)
    (forger (forgerIxAt ω)) _ (fun k hk => startsOf_punctured i (startsIxAt ω) k hk) rfl hQ hCand

/-- **Per-coin reduction.** On every winning coin of the forgery experiment, the `ITSR`
    adversary wins, or the `SM-DT-TCR` adversary wins, or the preimage adversary of some chain
    position `(i, j)` wins. -/
theorem eufGame_win_reduction {th : TwHash} (tw : Nat → Bytes)
    (hTw : ∀ a b : Nat, tw a = tw b → a = b)
    (hOut : ∀ s t m : Bytes, (th s t m).length = 32)
    (code : Bytes → Bytes → List Nat) (hCode : ∀ r m : Bytes, CodeOk (code r m))
    (frame : Bytes → Bytes → Bytes → Bytes)
    (hFrame : ∀ s r m m' : Bytes, frame s r m = frame s r m' → m = m')
    {nF : Nat} (hPos : 0 < eufCoins nF) (forger : Fin nF → Forger) (ω : Fin (eufCoins nF))
    (hWin : (eufGame hPos th tw code frame forger).win ω = true) :
    (itsrGameOf hPos th tw code frame forger).win ω = true ∨
    (tcrGameOf hPos th tw code frame forger).win ω = true ∨
    ∃ (i : Fin 34) (j : Nat), j < 95 ∧ (linkGame hPos th tw code frame forger i j).win ω = true := by
  have hW : eufWin th tw code frame (seedAt ω)
      (eufOutcome th tw code frame (seedAt ω)
        (honestVal th tw (seedAt ω) (startsOf (startsIxAt ω))) (randAt ω)
        (forger (forgerIxAt ω))) = true := hWin
  rcases forgery_classified th tw hOut code hCode frame (seedAt ω) (startsOf (startsIxAt ω))
      (randAt ω) (forger (forgerIxAt ω)) hW with hRepeat | hCol | ⟨i, j, hi, hj, _, hQ, hCand⟩
  · refine .inl ?_
    unfold itsrGameOf
    rw [itsrGame_win, itsrRun_eq, itsrAdvAt_eq]
    exact itsrAdv_wins (code := code) th tw frame hFrame (seedAt ω) (startsOf (startsIxAt ω))
      (forger (forgerIxAt ω)) _ 1 (Nat.le_refl 1) hRepeat
  · refine .inr (.inl ?_)
    unfold tcrGameOf
    rw [smDtTcrGame_win, smDtTcrRun_eq]
    exact tcrAdv_wins (th := th) tw hTw code frame (seedAt ω) (startsOf (startsIxAt ω)) (randAt ω)
      (forger (forgerIxAt ω)) 3231 (Nat.le_refl _) hCol
  · exact .inr (.inr ⟨⟨i, hi⟩, j, hj,
      linkGame_win (th := th) tw code frame hPos forger ⟨i, hi⟩ j hj ω hQ hCand⟩)

/-! ### The bound -/

/-- **One-wayness of the interior chain links** against the adversary class `𝒜`: for a uniform
    seed and a uniform `32`-byte start, every adversary with programs in `𝒜` wins the one-target
    `SM-DT-PRE` experiment whose hidden input is the value of chain `i` at position `j`,
    `1 ≤ j < 95`, with probability at most `ε`. At `j = 0` the hidden input is the uniform start
    and the experiment is the one of `SmDtPreHard`; for `j ≥ 1` the hidden input is a hash
    output, which `SmDtPreHard` does not cover. -/
@[expose] def ChainLinkHard (𝒜 : Code targetIface TargetBreak → Prop) (th : TwHash) (tw : Nat → Bytes)
    (ε : Spec.RatBound) : Prop :=
  ∀ (n nC nA : Nat) (hPos : 0 < n) (π : CoinSplit n nC nA) (sample : Fin nC → Bytes × Bytes),
    UniformOn (fun x : Bytes × Bytes => x.1.length = 32 ∧ x.2.length = 32) sample →
    ∀ (i j : Nat), i < 34 → 1 ≤ j → j < 95 →
    ∀ adv : Fin nA → Code targetIface TargetBreak, (∀ a : Fin nA, 𝒜 (adv a)) →
      GameBound (smDtPreGame hPos th 1 (fun ω => (sample (π.chal ω)).1)
        (fun ω k =>
          [chainFrom th tw (sample (π.chal ω)).1 i 0 j (sample (π.chal ω)).2].getD k [])
        (fun ω => adv (π.advc ω))).winProb ε

/-- **One-time EUF-CMA bound for the target-sum Winternitz layer of `Compact1122`**
    (`w = 96`, `34` chains, digit sum `1615`). For every forger family,

    `Pr[forgery] ≤ εItsr + εTcr + 34 · εPre + 3196 · εLink`,

    where `εItsr` bounds `ITSR` of the codeword subset hash, `εTcr` bounds `SM-DT-TCR` of `th`
    with `3231` targets, `εPre` bounds one-target `SM-DT-PRE` of `th` (the `34` chain starts),
    and `εLink` bounds `ChainLinkHard` (the `34 · 94` interior chain positions), each against a
    class containing the corresponding reduction adversaries. -/
theorem compact1122_closed_euf_cma_bound {th : TwHash}
    (tw : Nat → Bytes) (hTw : ∀ a b : Nat, tw a = tw b → a = b)
    (hOut : ∀ s t m : Bytes, (th s t m).length = 32)
    (code : Bytes → Bytes → List Nat) (hCode : ∀ r m : Bytes, CodeOk (code r m))
    (frame : Bytes → Bytes → Bytes → Bytes)
    (hFrame : ∀ s r m m' : Bytes, frame s r m = frame s r m' → m = m')
    {nF : Nat} (hPos : 0 < eufCoins nF) (forger : Fin nF → Forger)
    {𝒜I : Code byteOracleIface (Bytes × Bytes) → Prop}
    {𝒜T 𝒜P : Code targetIface TargetBreak → Prop}
    {εItsr εTcr εPre εLink : Spec.RatBound}
    (hItsr : ItsrHard 𝒜I (codeSubset code) 32 1 εItsr)
    (hTcr : SmDtTcrHard 𝒜T th 32 3231 εTcr)
    (hPre : SmDtPreHard 𝒜P th 32 32 1 εPre)
    (hLink : ChainLinkHard 𝒜P th tw εLink)
    (hAdvI : ∀ b, 𝒜I (itsrAdvAt th tw code frame forger b))
    (hAdvT : ∀ a, 𝒜T (tcrAdvAt th tw code frame forger a))
    (hAdvP : ∀ (i : Fin 34) (j : Nat) b, 𝒜P (linkAdvAt th tw code frame forger i j b)) :
    GameBound (eufGame hPos th tw code frame forger).winProb
      ((εItsr.add εTcr).add ((Spec.RatBound.scale 34 εPre).add (Spec.RatBound.scale 3196 εLink))) := by
  let A : Fin 34 → FinGame (eufCoins nF) := fun i => linkGame hPos th tw code frame forger i 0
  let B : Fin 3196 → FinGame (eufCoins nF) := fun t =>
    linkGame hPos th tw code frame forger ⟨t.1 / 94, by have := t.2; omega⟩ (t.1 % 94 + 1)
  have hA : ∀ i, GameBound (A i).winProb εPre := fun i =>
    hPre (eufCoins nF) (nB * nB) (nB * (powN nB 33 * nF)) hPos (splitLink nF i) startSample
      uniformOn_startSample (linkAdvAt th tw code frame forger i 0) (hAdvP i 0)
  have hB : ∀ t, GameBound (B t).winProb εLink := fun t =>
    hLink (eufCoins nF) (nB * nB) (nB * (powN nB 33 * nF)) hPos
      (splitLink nF ⟨t.1 / 94, by have := t.2; omega⟩) linkSample uniformOn_linkSample
      (t.1 / 94) (t.1 % 94 + 1) (by have := t.2; omega) (by omega) (by omega)
      (linkAdvAt th tw code frame forger ⟨t.1 / 94, by have := t.2; omega⟩ (t.1 % 94 + 1))
      (hAdvP _ _)
  let RA : FinGame (eufCoins nF) := ⟨hPos, Qsag.anySlotWins 34 A⟩
  let RB : FinGame (eufCoins nF) := ⟨hPos, Qsag.anySlotWins 3196 B⟩
  let RP : FinGame (eufCoins nF) :=
    ⟨hPos, fun ω => Qsag.anySlotWins 34 A ω || Qsag.anySlotWins 3196 B ω⟩
  have hRP : GameBound RP.winProb ((Spec.RatBound.scale 34 εPre).add (Spec.RatBound.scale 3196 εLink)) :=
    GameBound.trans
      (event_le_two_reductions RP RA RB (fun ω h => Bool.or_eq_true_iff.mp h))
      (Spec.RatBound.add_le_add (Qsag.anySlotWins_bound hPos 34 A hA)
        (Qsag.anySlotWins_bound hPos 3196 B hB))
  refine event_le_three_reductions (eufGame hPos th tw code frame forger)
    (itsrGameOf hPos th tw code frame forger) (tcrGameOf hPos th tw code frame forger) RP
    (fun ω hWin => ?_)
    (hItsr (eufCoins nF) nB (nB * (powN nB 34 * nF)) hPos (splitItsr nF) randSample
      uniformOn_randSample (itsrAdvAt th tw code frame forger) hAdvI)
    (hTcr (eufCoins nF) nB (nB * (powN nB 34 * nF)) hPos (splitSeed nF) (Qsag.byteVecSampler 32)
      (Qsag.uniformOn_byteVecSampler 32) (tcrAdvAt th tw code frame forger) hAdvT)
    hRP
  rcases eufGame_win_reduction (th := th) tw hTw hOut code hCode frame hFrame hPos forger ω hWin with
    h | h | ⟨i, j, hj, h⟩
  · exact .inl h
  · exact .inr (.inl h)
  · refine .inr (.inr ?_)
    show (Qsag.anySlotWins 34 A ω || Qsag.anySlotWins 3196 B ω) = true
    cases j with
    | zero =>
      rw [Qsag.anySlotWins_of_win 34 A ω i h]
      rfl
    | succ j' =>
      have hIdx : i.1 * 94 + j' < 3196 := by have := i.2; omega
      have hBwin : (B ⟨i.1 * 94 + j', hIdx⟩).win ω = true := by
        have hTransport : ∀ (i' : Fin 34) (jj : Nat), i' = i → jj = j' + 1 →
            (linkGame hPos th tw code frame forger i' jj).win ω = true := by
          intro i' jj h1 h2
          rw [h1, h2]
          exact h
        exact hTransport _ _ (Fin.ext (by show (i.1 * 94 + j') / 94 = i.1; omega))
          (by show (i.1 * 94 + j') % 94 + 1 = j' + 1; omega)
      rw [Qsag.anySlotWins_of_win 3196 B ω ⟨i.1 * 94 + j', hIdx⟩ hBwin]
      exact Bool.or_true _

/-! ## 8. Without the digit-sum constraint the scheme is forged by stepping chains forward -/

/-- Forger against a code whose codeword for `m₂` dominates the codeword for `m₁`: obtain a
    signature on `m₁` and advance every opened value to the position the codeword of `m₂`
    opens. It never inverts a hash. -/
def forwardForger (th : TwHash) (tw : Nat → Bytes) (code : Bytes → Bytes → List Nat)
    (frame : Bytes → Bytes → Bytes → Bytes) (m₁ m₂ r₂ : Bytes) : Forger where
  query _ _ := some m₁
  forge seed root sig :=
    match sig with
    | none => (m₂, r₂, [])
    | some s =>
      (m₂, r₂, (List.range 34).map (fun i =>
        chainFrom th tw seed i ((code s.1 (frame seed root m₁)).getD i 0)
          ((code r₂ (frame seed root m₂)).getD i 0 - (code s.1 (frame seed root m₁)).getD i 0)
          (s.2.getD i [])))

private theorem honestVal_length (th : TwHash) (tw : Nat → Bytes)
    (hOut : ∀ s t m : Bytes, (th s t m).length = 32) (seed : Bytes) (starts : Nat → Bytes)
    (i : Nat) (hStart : (starts i).length = 32) :
    ∀ p : Nat, (honestVal th tw seed starts i p).length = 32
  | 0 => hStart
  | p + 1 => by rw [honestVal_succ]; exact hOut _ _ _

private theorem startsOf_length (v : Fin (powN nB 34)) (i : Nat) (hi : i < 34) :
    (startsOf v i).length = 32 := by
  unfold startsOf
  rw [ditePos hi]
  exact Qsag.byteVecSampler_length 32 _

/-- **Correctness.** For `32`-byte chain starts and a codeword with digits at most `95`, the
    honest signature verifies under the honest root. -/
theorem verify_signVals (th : TwHash) (tw : Nat → Bytes)
    (hOut : ∀ s t m : Bytes, (th s t m).length = 32) (seed : Bytes) (starts : Nat → Bytes)
    (hStarts : ∀ i, i < 34 → (starts i).length = 32) (c : List Nat)
    (hc : ∀ i, i < 34 → c.getD i 0 ≤ 95) :
    verify th tw seed (pkRoot th tw seed (honestVal th tw seed starts)) c
      (signVals (honestVal th tw seed starts) c) = true := by
  have hLen : (signVals (honestVal th tw seed starts) c).length = 34 := by
    unfold signVals
    rw [List.length_map, List.length_range]
  have hAll : (signVals (honestVal th tw seed starts) c).all (fun v => decide (v.length = 32)) =
      true := by
    refine List.all_eq_true.mpr (fun v hv => ?_)
    unfold signVals at hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    exact decide_eq_true (honestVal_length th tw hOut seed starts i
      (hStarts i (List.mem_range.mp hi)) _)
  have hEnds : sigEnds th tw seed c (signVals (honestVal th tw seed starts) c) =
      (List.range 34).map (fun i => honestVal th tw seed starts i 95) := by
    unfold sigEnds signVals
    refine List.map_congr_left (fun i hi => ?_)
    have hi' : i < 34 := List.mem_range.mp hi
    rw [getD_map_range _ 34 i hi', honestVal_advance]
    congr 1
    have := hc i hi'
    omega
  have hRoot : th seed (tw 3230)
      ((List.range 34).map (fun i => honestVal th tw seed starts i 95)).flatten =
      pkRoot th tw seed (honestVal th tw seed starts) := rfl
  unfold verify
  rw [decide_eq_true hLen, hAll, hEnds, decide_eq_true hRoot]
  rfl

/-- **The forward-stepping forger wins on every coin** when the codeword of `m₂` dominates the
    codeword of `m₁` digit by digit. Two target-sum codewords never dominate one another unless
    they are equal, so this needs a code that violates `CodeOk`. -/
theorem forwardForger_wins (th : TwHash) (tw : Nat → Bytes)
    (hOut : ∀ s t m : Bytes, (th s t m).length = 32)
    (code : Bytes → Bytes → List Nat) (frame : Bytes → Bytes → Bytes → Bytes)
    (m₁ m₂ r₂ : Bytes) (hNe : m₂ ≠ m₁)
    (hDom : ∀ (rand seed root : Bytes) (i : Nat), i < 34 →
      (code rand (frame seed root m₁)).getD i 0 ≤ (code r₂ (frame seed root m₂)).getD i 0 ∧
      (code r₂ (frame seed root m₂)).getD i 0 ≤ 95)
    {nF : Nat} (hPos : 0 < eufCoins nF) (ω : Fin (eufCoins nF)) :
    (eufGame hPos th tw code frame
      (fun _ => forwardForger th tw code frame m₁ m₂ r₂)).win ω = true := by
  show eufWin th tw code frame (seedAt ω)
    (eufOutcome th tw code frame (seedAt ω)
      (honestVal th tw (seedAt ω) (startsOf (startsIxAt ω))) (randAt ω)
      (forwardForger th tw code frame m₁ m₂ r₂)) = true
  have hOutc : eufOutcome th tw code frame (seedAt ω)
      (honestVal th tw (seedAt ω) (startsOf (startsIxAt ω))) (randAt ω)
      (forwardForger th tw code frame m₁ m₂ r₂) =
      ⟨pkRoot th tw (seedAt ω) (honestVal th tw (seedAt ω) (startsOf (startsIxAt ω))),
        some (m₁, code (randAt ω) (frame (seedAt ω)
          (pkRoot th tw (seedAt ω) (honestVal th tw (seedAt ω) (startsOf (startsIxAt ω)))) m₁)),
        m₂, r₂,
        (List.range 34).map (fun i =>
          honestVal th tw (seedAt ω) (startsOf (startsIxAt ω)) i
            ((code r₂ (frame (seedAt ω)
              (pkRoot th tw (seedAt ω) (honestVal th tw (seedAt ω) (startsOf (startsIxAt ω))))
              m₂)).getD i 0))⟩ := by
    show Outcome.mk _ _ _ _ _ = Outcome.mk _ _ _ _ _
    refine congrArg (Outcome.mk _ _ m₂ r₂) (List.map_congr_left (fun i hi => ?_))
    have hi' : i < 34 := List.mem_range.mp hi
    show chainFrom th tw (seedAt ω) i _ _ ((signVals _ _).getD i []) = _
    unfold signVals
    rw [getD_map_range _ 34 i hi', honestVal_advance]
    dsimp only
    congr 1
    have := (hDom (randAt ω) (seedAt ω)
      (pkRoot th tw (seedAt ω) (honestVal th tw (seedAt ω) (startsOf (startsIxAt ω)))) i hi').1
    omega
  rw [hOutc]
  unfold eufWin forgedCode
  dsimp only
  have hVer := verify_signVals th tw hOut (seedAt ω) (startsOf (startsIxAt ω))
    (fun i hi => startsOf_length _ i hi)
    (code r₂ (frame (seedAt ω)
      (pkRoot th tw (seedAt ω) (honestVal th tw (seedAt ω) (startsOf (startsIxAt ω)))) m₂))
    (fun i hi => (hDom (randAt ω) (seedAt ω)
      (pkRoot th tw (seedAt ω) (honestVal th tw (seedAt ω) (startsOf (startsIxAt ω)))) i hi).2)
  unfold signVals at hVer
  rw [decide_eq_true hNe, hVer]
  rfl

/-- Code without the digit-sum constraint: digit `0` everywhere for the empty message, digit
    `1` everywhere otherwise. -/
def stepCode (_ msg : Bytes) : List Nat :=
  if msg = [] then List.replicate 34 0 else List.replicate 34 1

theorem stepCode_not_codeOk : ¬ ∀ r m : Bytes, CodeOk (stepCode r m) := by
  intro h
  have hSum := (h [] []).2.1
  have hZero : (stepCode [] []).sum = 0 := by decide
  rw [hZero] at hSum
  exact absurd hSum (by decide)

/-- Against `stepCode` the forward-stepping forger wins the experiment on every coin, for every
    tweakable hash with `32`-byte digests. -/
theorem forwardForger_wins_stepCode (th : TwHash) (tw : Nat → Bytes)
    (hOut : ∀ s t m : Bytes, (th s t m).length = 32) {nF : Nat} (hPos : 0 < eufCoins nF)
    (ω : Fin (eufCoins nF)) :
    (eufGame hPos th tw stepCode (fun _ _ m => m)
      (fun _ => forwardForger th tw stepCode (fun _ _ m => m) [] [0] [])).win ω = true := by
  refine forwardForger_wins th tw hOut stepCode (fun _ _ m => m) [] [0] [] (by decide)
    (fun rand seed root i hi => ?_) hPos ω
  have h0 : (stepCode rand []).getD i 0 = 0 := by
    show (List.replicate 34 0).getD i 0 = 0
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> rfl
  have h1 : (stepCode [] [0]).getD i 0 = 1 := by
    show (List.replicate 34 1).getD i 0 = 1
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, itePos hi]
    rfl
  show (stepCode rand []).getD i 0 ≤ (stepCode [] [0]).getD i 0 ∧
    (stepCode [] [0]).getD i 0 ≤ 95
  rw [h0, h1]
  exact ⟨by decide, by decide⟩

/-- **Tooth: the digit-sum constraint is load-bearing.** For the code `stepCode`, which violates
    `CodeOk` (`stepCode_not_codeOk`), no bound below `1` holds for the forgery experiment: the
    forward-stepping forger wins on every coin. -/
theorem tooth_drop_target_sum_forward_step_forges (th : TwHash) (tw : Nat → Bytes)
    (hOut : ∀ s t m : Bytes, (th s t m).length = 32) {nF : Nat} (hPos : 0 < eufCoins nF)
    {ε : Spec.RatBound} (hε : ε.num < ε.den) :
    ¬ GameBound (eufGame hPos th tw stepCode (fun _ _ m => m)
      (fun _ => forwardForger th tw stepCode (fun _ _ m => m) [] [0] [])).winProb ε :=
  FinGame.not_bound_of_forall_win _ (fun ω => forwardForger_wins_stepCode th tw hOut hPos ω) hε

#verify_constructive tcrAdv_wins tcrAdv_within commitLoop_play forgery_classified tcrAdv_play
  preAdv_wins preAdv_within itsrAdv_wins itsrAdv_within puncturedOutcome_eq
  eufGame_win_reduction compact1122_closed_euf_cma_bound verify_signVals
  forwardForger_wins forwardForger_wins_stepCode stepCode_not_codeOk
  tooth_drop_target_sum_forward_step_forges
  uniformOn_linkSample uniformOn_startSample uniformOn_randSample digitSplit_chal_pair_ne

#tooth_pair compact1122_closed_euf_cma_bound vs tooth_drop_target_sum_forward_step_forges

end Qsag.Compact1122
end
