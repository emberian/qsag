module
/-
# Qsag.Protocol.Threshold.MultiSessionMacBlindHybrid — `Q` Blinded MAC Checks Under One Key

`Qsag.Protocol.Threshold.ComputationalMacBlind` bounds ONE blinded SPDZ MAC-check opening
`w = (r + r_corrupt) · (Δx · α − Δm) + err` under a fresh MAC key `α`. This module composes
`Q` adaptive sequential openings under one persistent `α`, first with uniform independent
honest randomizers and then with randomizers expanded from one persistent PRG seed.

1. **Model** (sections 1, 2). An adversary is a strategy tree `SeqAdv`: each node fixes the
   shifts `Δx`, `Δm`, the corrupt randomizer sum and a post-OLE additive error, and continues
   on the opened value. `seqRun` runs it for at most `Q` openings under a poison policy: with
   poison ON the run stops at the first nonzero opening and the adversary must guess
   (`SpdzReservoir::poison`); with poison OFF it continues (`blind_open_pooled` at mesh level).
   The outcome carries the guess and two acceptance flags. The simulator `seqSimView` never
   reads `α`: for `Δx = 0` it computes the opening, whose defect `−Δm` is key-independent, and
   otherwise it outputs a uniform field element.
2. **Uniform randomizers** (section 3). `multiSession_blindedMac_uniform_randomizer_bound`:
   the real openings are within `Q / |F|` of the simulator, for BOTH poison policies, by the
   counting core `seq_real_sim_count_l1` (per round, `r ↦ (r + r_corrupt) · d + err` is a
   bijection unless `α = Δm · Δx⁻¹`).
3. **Forgery acceptance** (section 4). An opening with `Δx ≠ 0` that opens `0` passes one
   blinding round. Over `Q` openings this happens with probability at most `2Q / |F|`
   (`multiSession_blindedMac_single_round_acceptance_bound`), for any adversarial `err`; two
   consecutive such openings, the `BLIND_ROUNDS = 2` rule of `blind_open_pooled`, with
   probability at most `Q / |F| + Q / |F|²`
   (`multiSession_blindedMac_two_round_acceptance_bound`). The bound `Q / |F|` for one round is
   false: a zero total randomizer also opens `0`
   (`tooth_zero_randomizer_single_round_acceptance`).
4. **One persistent PRG seed** (section 6). The randomizer of opening `i` is
   `decodeMask (prg seed (leBytes L i))`, so `Q ≤ 256 ^ L`.
   `multiSession_blindedMac_persistent_alpha_bound`: distance `εPrf + Q / |F|` to the simulator
   for a `Q`-query `Spec.PrfHard` PRF, in ONE hop: `seqPrgGame` is equal to `prfRealGame` and
   `seqIdealGame` to `prfIdealGame` of the explicit distinguisher `seqPrfDistinguisher`
   (`Spec.Within Q`), for the challenger sampler `funTapePrfSampler`, which enumerates all
   functions from `L`-byte inputs to mask strings as a tape of `256 ^ L` mask coins. The shape
   `Q · εPrf + Q / |F|` is the corollary `…_mission_shape`.
5. **Instances** (section 7). `Tower128` with a 32-byte seed and a 5-byte counter:
   `εPrf + Q / 2¹²⁸` for `Q ≤ 2⁴⁰`. `GoldilocksExt2` (`|F| = p²`) for the uniform-randomizer
   results, with `Q / p² < 2⁻⁸⁷` for `Q ≤ 2⁴⁰`; it has no byte-bijective mask decoder here, so
   there is no PRG-seed instance for it.
6. **Teeth** (sections 5, 8). Without blinding and without poison, one aborted opening is the
   MAC key and the next opening forges with probability `1`
   (`tooth_unblinded_forgery_breaks_acceptance_bound`, `tooth_unblinded_not_simulatable`). With
   a reused randomizer and no poison, two openings determine the key and the third forges
   (`tooth_reused_randomizer_recovers_alpha`,
   `tooth_reused_randomizer_forgery_breaks_acceptance_bound`).

The joint bounds `multiSession_blindedMac_uniform_key_test_bound` and
`multiSession_blindedMac_persistent_key_test_bound` let the final test inspect the persistent
key as well as the outcome. The simulated opening strategy still receives only its own coin
and earlier responses. `unblinded_poison_key_observation` shows that with blinding removed
the first opening already reveals every predicate of the key, including when poison is on.
Poison can prevent a later forgery using that observation.

The Tower128 sampler follows from the exported PRF support equation.
`tower128_joint_premises` and `inhabited_multiSession_blindedMac_tower128` instantiate the
32-byte seed, 5-byte counter and two-opening experiment at PRF advantage one.
The model starts after the OLE/OT product and commitment setup. Errors are fixed before the
honest randomizer, and each opening checks one defect.
-/

public import Qsag.Protocol.Threshold.ComputationalMacBlind
import Qsag.Tactic.AssuranceKit

public section

namespace Qsag.MacBlind

open Qsag.FrozenChallenge CommRingOps
open Qsag.Spec (Bytes Code byteOracleIface FinGame GameBound AdvDist CoinSplit UniformOn)

set_option autoImplicit false

/-! ## 1. Adversaries, openings and the sequential run -/

private theorem iteOfPos.{u} {α : Sort u} {p : Prop} [Decidable p] (hp : p) (a b : α) :
    (if p then a else b) = a := by
  cases ‹Decidable p› with
  | isTrue _ => rfl
  | isFalse hn => exact False.elim (hn hp)

private theorem iteOfNeg.{u} {α : Sort u} {p : Prop} [Decidable p] (hnp : ¬ p) (a b : α) :
    (if p then a else b) = b := by
  cases ‹Decidable p› with
  | isTrue hp => exact False.elim (hnp hp)
  | isFalse _ => rfl

/-- Adaptive adversary against sequential blinded MAC-check openings under one MAC key, as a
    strategy tree. `done b` outputs the guess `b`. `round Δx Δm rCorrupt err next` asks for one
    opening with additive shifts `Δx`, `Δm` of the checked value and of its MAC, the sum
    `rCorrupt` of the corrupt parties' randomizer shares and a post-OLE additive error `err`,
    all fixed before the opening; `next w` is the strategy after seeing the opened value `w`. -/
inductive SeqAdv (F : Type) where
  | done (guess : Bool) : SeqAdv F
  | round (deltaX deltaM rCorrupt err : F) (next : F → SeqAdv F) : SeqAdv F

/-- The guess of a strategy that is allowed no further opening: a strategy that still asks for
    one outputs `false`. -/
@[expose] def seqFinalGuess {F : Type} : SeqAdv F → Bool
  | .done b => b
  | .round _ _ _ _ _ => false

/-- Outcome of a run: the adversary's guess, whether some opening with `Δx ≠ 0` opened `0`
    (a forged value passed one blinding round), and whether two consecutive openings with
    `Δx ≠ 0` both opened `0` (a forged value passed the two-round rule). -/
abbrev SeqOutcome : Type := Bool × Bool × Bool

/-- The adversary's guess. -/
def seqGuess (o : SeqOutcome) : Bool := o.1

/-- Some opening with `Δx ≠ 0` opened `0`. -/
def seqSingleAccept (o : SeqOutcome) : Bool := o.2.1

/-- Two consecutive openings with `Δx ≠ 0` both opened `0`. -/
def seqDoubleAccept (o : SeqOutcome) : Bool := o.2.2

/-- The real opened value `(r + rCorrupt) · (Δx · α − Δm) + err`: the expression that
    `macBlindOpen r rCorrupt (spdzMacDefect Δx α Δm) err` names. -/
@[expose] def seqRealView {F : Type} [LawfulCommRing F] (alpha r dx dm rC err : F) : F :=
  add (mul (add r rC) (sub (mul dx alpha) dm)) err

/-- The simulated opened value from one uniform field element `u`. For `Δx = 0` the defect is
    `−Δm` whatever the key, and the simulator computes the opening `(u + rCorrupt) · (−Δm) + err`;
    otherwise it outputs `u`. The MAC key is not an argument. -/
@[expose] def seqSimView {F : Type} [LawfulCommRing F] [DecidableEq F] (u dx dm rC err : F) : F :=
  if dx = zero then add (mul (add u rC) (neg dm)) err else u

/-- The unblinded opened value `(Δx · α − Δm) + err`: the raw MAC defect, with no randomizer. -/
def seqRawView {F : Type} [LawfulCommRing F] (alpha _r dx dm _rC err : F) : F :=
  add (sub (mul dx alpha) dm) err

/-- One round, given the opened value `w` and the continuation `k` of the run. With `poison`,
    a nonzero `w` ends the run: the adversary sees `w` and must guess. Otherwise the run
    continues with the acceptance flags updated. -/
@[expose] def seqRound {F : Type} [LawfulCommRing F] [DecidableEq F] (poison : Bool)
    (k : SeqAdv F → Bool → Bool → Bool → SeqOutcome) (dx : F) (next : F → SeqAdv F)
    (s d p : Bool) (w : F) : SeqOutcome :=
  if (poison && decide (w ≠ zero)) = true then (seqFinalGuess (next w), s, d)
  else k (next w) (s || decide (dx ≠ zero ∧ w = zero))
    (d || (p && decide (dx ≠ zero ∧ w = zero))) (decide (dx ≠ zero ∧ w = zero))

/-- Run a strategy for at most `q` openings. `view r Δx Δm rCorrupt err` is the opened value of
    a round whose honest randomizer is `r`; round `i` of the run reads `rnd i`. The flags `s`,
    `d` are the single and double acceptance seen so far and `p` says whether the previous
    opening was an accepted forgery. A strategy that asks for more than `q` openings is cut off
    with guess `false`. -/
@[expose] def seqRun {F : Type} [LawfulCommRing F] [DecidableEq F] (poison : Bool)
    (view : F → F → F → F → F → F) :
    Nat → SeqAdv F → (Nat → F) → Bool → Bool → Bool → SeqOutcome
  | _, .done b, _, s, d, _ => (b, s, d)
  | 0, .round _ _ _ _ _, _, s, d, _ => (false, s, d)
  | q + 1, .round dx dm rC err next, rnd, s, d, p =>
    seqRound poison (fun A' s' d' p' => seqRun poison view q A' (fun j => rnd (j + 1)) s' d' p')
      dx next s d p (view (rnd 0) dx dm rC err)

theorem seqRun_done {F : Type} [LawfulCommRing F] [DecidableEq F] (poison : Bool)
    (view : F → F → F → F → F → F) (q : Nat) (b : Bool) (rnd : Nat → F) (s d p : Bool) :
    seqRun poison view q (.done b) rnd s d p = (b, s, d) := by
  cases q <;> rfl

theorem seqRun_zero_round {F : Type} [LawfulCommRing F] [DecidableEq F] (poison : Bool)
    (view : F → F → F → F → F → F) (dx dm rC err : F) (next : F → SeqAdv F) (rnd : Nat → F)
    (s d p : Bool) :
    seqRun poison view 0 (.round dx dm rC err next) rnd s d p = (false, s, d) := by
  rfl

theorem seqRun_succ_round {F : Type} [LawfulCommRing F] [DecidableEq F] (poison : Bool)
    (view : F → F → F → F → F → F) (q : Nat) (dx dm rC err : F) (next : F → SeqAdv F)
    (rnd : Nat → F) (s d p : Bool) :
    seqRun poison view (q + 1) (.round dx dm rC err next) rnd s d p =
      seqRound poison
        (fun A' s' d' p' => seqRun poison view q A' (fun j => rnd (j + 1)) s' d' p')
        dx next s d p (view (rnd 0) dx dm rC err) := by
  rfl

theorem seqRound_stop {F : Type} [LawfulCommRing F] [DecidableEq F] {poison : Bool}
    (k : SeqAdv F → Bool → Bool → Bool → SeqOutcome) (dx : F) (next : F → SeqAdv F)
    (s d p : Bool) {w : F} (h : (poison && decide (w ≠ zero)) = true) :
    seqRound poison k dx next s d p w = (seqFinalGuess (next w), s, d) :=
  iteOfPos h _ _

theorem seqRound_cont {F : Type} [LawfulCommRing F] [DecidableEq F] {poison : Bool}
    (k : SeqAdv F → Bool → Bool → Bool → SeqOutcome) (dx : F) (next : F → SeqAdv F)
    (s d p : Bool) {w : F} (h : (poison && decide (w ≠ zero)) = false) :
    seqRound poison k dx next s d p w =
      k (next w) (s || decide (dx ≠ zero ∧ w = zero))
        (d || (p && decide (dx ≠ zero ∧ w = zero))) (decide (dx ≠ zero ∧ w = zero)) :=
  iteOfNeg (fun h' => Bool.noConfusion (h.symm.trans h')) _ _

/-- A run of at most `q` openings reads only the first `q` randomizers. -/
theorem seqRun_congr {F : Type} [LawfulCommRing F] [DecidableEq F] (poison : Bool)
    (view : F → F → F → F → F → F) :
    ∀ (q : Nat) (A : SeqAdv F) (rnd rnd' : Nat → F) (s d p : Bool),
      (∀ j : Nat, j < q → rnd j = rnd' j) →
      seqRun poison view q A rnd s d p = seqRun poison view q A rnd' s d p := by
  intro q
  induction q with
  | zero =>
    intro A rnd rnd' s d p _
    cases A with
    | done b => rfl
    | round dx dm rC err next => rfl
  | succ q ih =>
    intro A rnd rnd' s d p h
    cases A with
    | done b => rfl
    | round dx dm rC err next =>
      rw [seqRun_succ_round, seqRun_succ_round, h 0 (Nat.succ_pos q)]
      have hk : (fun (A' : SeqAdv F) (s' d' p' : Bool) =>
            seqRun poison view q A' (fun j => rnd (j + 1)) s' d' p') =
          (fun (A' : SeqAdv F) (s' d' p' : Bool) =>
            seqRun poison view q A' (fun j => rnd' (j + 1)) s' d' p') := by
        funext A' s' d' p'
        exact ih A' _ _ s' d' p' (fun j hj => h (j + 1) (Nat.succ_lt_succ hj))
      rw [hk]

/-! ## 2. Randomizer tapes and the counting core -/

/-- Number of tapes of `d` coins from `Fin n`. -/
@[expose] def seqTapeCard (n : Nat) : Nat → Nat
  | 0 => 1
  | d + 1 => n * seqTapeCard n d

theorem seqTapeCard_pos {n : Nat} (hn : 0 < n) : ∀ d : Nat, 0 < seqTapeCard n d
  | 0 => Nat.one_pos
  | d + 1 => Nat.mul_pos hn (seqTapeCard_pos hn d)

/-- Position `j` of a tape of `d` coins, read through `s`; `dflt` beyond the end of the tape. -/
@[expose] def tapeDigit {α : Type} {n : Nat} (s : Fin n → α) (dflt : α) :
    (d : Nat) → Fin (seqTapeCard n d) → Nat → α
  | 0, _, _ => dflt
  | d + 1, t, 0 => s ((CoinSplit.prod n (seqTapeCard n d)).chal t)
  | d + 1, t, j + 1 => tapeDigit s dflt d ((CoinSplit.prod n (seqTapeCard n d)).advc t) j

theorem tapeDigit_pair_zero {α : Type} {n : Nat} (s : Fin n → α) (dflt : α) (d : Nat)
    (r : Fin n) (t : Fin (seqTapeCard n d)) :
    tapeDigit s dflt (d + 1) ((CoinSplit.prod n (seqTapeCard n d)).pair r t) 0 = s r := by
  show s ((CoinSplit.prod n (seqTapeCard n d)).chal _) = s r
  rw [CoinSplit.chal_pair]

theorem tapeDigit_pair_succ {α : Type} {n : Nat} (s : Fin n → α) (dflt : α) (d : Nat)
    (r : Fin n) (t : Fin (seqTapeCard n d)) (j : Nat) :
    tapeDigit s dflt (d + 1) ((CoinSplit.prod n (seqTapeCard n d)).pair r t) (j + 1) =
      tapeDigit s dflt d t j := by
  show tapeDigit s dflt d ((CoinSplit.prod n (seqTapeCard n d)).advc _) j = _
  rw [CoinSplit.advc_pair]

private theorem natAbsDiff_self (a : Nat) : Spec.natAbsDiff a a = 0 := by
  unfold Spec.natAbsDiff
  split <;> omega

private theorem natAbsDiff_le_of_le {a b c : Nat} (ha : a ≤ c) (hb : b ≤ c) :
    Spec.natAbsDiff a b ≤ c := by
  unfold Spec.natAbsDiff
  split <;> omega

private theorem natAbsDiff_add_le' (a b c d : Nat) :
    Spec.natAbsDiff (a + b) (c + d) ≤ Spec.natAbsDiff a c + Spec.natAbsDiff b d := by
  unfold Spec.natAbsDiff
  split <;> split <;> split <;> omega

private theorem natAbsDiff_qsum_le' : ∀ {n : Nat} (f g : Fin n → Nat),
    Spec.natAbsDiff (qsum n f) (qsum n g) ≤ qsum n (fun i => Spec.natAbsDiff (f i) (g i))
  | 0, _, _ => Nat.le_of_eq (natAbsDiff_self 0)
  | _ + 1, f, g =>
    Nat.le_trans (natAbsDiff_add_le' _ _ _ _)
      (Nat.add_le_add_left (natAbsDiff_qsum_le' (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)
        (fun i => g ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩)) _)

private theorem qsum_bool_le_card {n : Nat} (p : Fin n → Bool) :
    qsum n (fun i => if p i = true then 1 else 0) ≤ n := by
  have h : qsum n (fun i => if p i = true then 1 else 0) ≤ qsum n (fun _ => 1) :=
    qsum_le_qsum (fun i => by cases p i <;> decide)
  rw [qsum_const, Nat.mul_one] at h
  exact h

/-- Number of tapes of `d` uniform randomizers on which the run of `A` has an outcome in `obs`. -/
def seqCount {F : Type} [LawfulCommRing F] [DecidableEq F] {cardF : Nat} (poison : Bool)
    (view : F → F → F → F → F → F) (enum : SimpleEquiv (Fin cardF) F) (q : Nat) (A : SeqAdv F)
    (d : Nat) (obs : SeqOutcome → Bool) (s dd p : Bool) : Nat :=
  qsum (seqTapeCard cardF d) (fun t =>
    if obs (seqRun poison view q A (tapeDigit enum.toFun zero d t) s dd p) = true then 1 else 0)

/-- The same count after the first opened value `w` of a round. -/
def seqAfterCount {F : Type} [LawfulCommRing F] [DecidableEq F] {cardF : Nat} (poison : Bool)
    (view : F → F → F → F → F → F) (enum : SimpleEquiv (Fin cardF) F) (q : Nat) (dx : F)
    (next : F → SeqAdv F) (d : Nat) (obs : SeqOutcome → Bool) (s dd p : Bool) (w : F) : Nat :=
  qsum (seqTapeCard cardF d) (fun t =>
    if obs (seqRound poison
      (fun A' s' d' p' => seqRun poison view q A' (tapeDigit enum.toFun zero d t) s' d' p')
      dx next s dd p w) = true then 1 else 0)

theorem seqCount_le {F : Type} [LawfulCommRing F] [DecidableEq F] {cardF : Nat} (poison : Bool)
    (view : F → F → F → F → F → F) (enum : SimpleEquiv (Fin cardF) F) (q : Nat) (A : SeqAdv F)
    (d : Nat) (obs : SeqOutcome → Bool) (s dd p : Bool) :
    seqCount poison view enum q A d obs s dd p ≤ seqTapeCard cardF d :=
  qsum_bool_le_card _

theorem seqAfterCount_le {F : Type} [LawfulCommRing F] [DecidableEq F] {cardF : Nat}
    (poison : Bool) (view : F → F → F → F → F → F) (enum : SimpleEquiv (Fin cardF) F) (q : Nat)
    (dx : F) (next : F → SeqAdv F) (d : Nat) (obs : SeqOutcome → Bool) (s dd p : Bool) (w : F) :
    seqAfterCount poison view enum q dx next d obs s dd p w ≤ seqTapeCard cardF d :=
  qsum_bool_le_card _

theorem seqCount_done {F : Type} [LawfulCommRing F] [DecidableEq F] {cardF : Nat} (poison : Bool)
    (view : F → F → F → F → F → F) (enum : SimpleEquiv (Fin cardF) F) (q : Nat) (b : Bool)
    (d : Nat) (obs : SeqOutcome → Bool) (s dd p : Bool) :
    seqCount poison view enum q (.done b) d obs s dd p =
      qsum (seqTapeCard cardF d) (fun _ => if obs (b, s, dd) = true then 1 else 0) :=
  qsum_congr (fun t => by rw [seqRun_done])

theorem seqCount_zero_round {F : Type} [LawfulCommRing F] [DecidableEq F] {cardF : Nat}
    (poison : Bool) (view : F → F → F → F → F → F) (enum : SimpleEquiv (Fin cardF) F)
    (dx dm rC err : F) (next : F → SeqAdv F) (d : Nat) (obs : SeqOutcome → Bool) (s dd p : Bool) :
    seqCount poison view enum 0 (.round dx dm rC err next) d obs s dd p =
      qsum (seqTapeCard cardF d) (fun _ => if obs (false, s, dd) = true then 1 else 0) :=
  qsum_congr (fun t => by rw [seqRun_zero_round])

/-- Peeling the first randomizer of the tape: the count of a round is the sum, over the first
    randomizer, of the counts after its opened value. -/
theorem seqCount_succ_round {F : Type} [LawfulCommRing F] [DecidableEq F] {cardF : Nat}
    (poison : Bool) (view : F → F → F → F → F → F) (enum : SimpleEquiv (Fin cardF) F) (q : Nat)
    (dx dm rC err : F) (next : F → SeqAdv F) (d : Nat) (obs : SeqOutcome → Bool) (s dd p : Bool) :
    seqCount poison view enum (q + 1) (.round dx dm rC err next) (d + 1) obs s dd p =
      qsum cardF (fun r => seqAfterCount poison view enum q dx next d obs s dd p
        (view (enum.toFun r) dx dm rC err)) := by
  refine (qsum_coinSplit (CoinSplit.prod cardF (seqTapeCard cardF d)) _).trans ?_
  refine qsum_congr (fun r => qsum_congr (fun t => ?_))
  have hS : (fun j => tapeDigit enum.toFun zero (d + 1)
        ((CoinSplit.prod cardF (seqTapeCard cardF d)).pair r t) (j + 1)) =
      tapeDigit enum.toFun zero d t :=
    funext (fun j => tapeDigit_pair_succ enum.toFun zero d r t j)
  rw [seqRun_succ_round, tapeDigit_pair_zero, hS]

theorem seqAfterCount_stop {F : Type} [LawfulCommRing F] [DecidableEq F] {cardF : Nat}
    {poison : Bool} (view : F → F → F → F → F → F) (enum : SimpleEquiv (Fin cardF) F) (q : Nat)
    (dx : F) (next : F → SeqAdv F) (d : Nat) (obs : SeqOutcome → Bool) (s dd p : Bool) {w : F}
    (h : (poison && decide (w ≠ zero)) = true) :
    seqAfterCount poison view enum q dx next d obs s dd p w =
      qsum (seqTapeCard cardF d)
        (fun _ => if obs (seqFinalGuess (next w), s, dd) = true then 1 else 0) :=
  qsum_congr (fun t => by rw [seqRound_stop _ dx next s dd p h])

theorem seqAfterCount_cont {F : Type} [LawfulCommRing F] [DecidableEq F] {cardF : Nat}
    {poison : Bool} (view : F → F → F → F → F → F) (enum : SimpleEquiv (Fin cardF) F) (q : Nat)
    (dx : F) (next : F → SeqAdv F) (d : Nat) (obs : SeqOutcome → Bool) (s dd p : Bool) {w : F}
    (h : (poison && decide (w ≠ zero)) = false) :
    seqAfterCount poison view enum q dx next d obs s dd p w =
      seqCount poison view enum q (next w) d obs (s || decide (dx ≠ zero ∧ w = zero))
        (dd || (p && decide (dx ≠ zero ∧ w = zero))) (decide (dx ≠ zero ∧ w = zero)) :=
  qsum_congr (fun t => by rw [seqRound_cont _ dx next s dd p h])

theorem seqRealView_zero_shift {F : Type} [LawfulCommRing F] [DecidableEq F]
    (alpha r dm rC err : F) :
    seqRealView alpha r zero dm rC err = seqSimView r zero dm rC err := by
  unfold seqRealView seqSimView
  rw [iteOfPos rfl, LawfulCommRing.zero_mul, LawfulCommRing.sub_eq_add_neg,
    LawfulCommRing.zero_add]

theorem seqSimView_shifted {F : Type} [LawfulCommRing F] [DecidableEq F] {dx : F}
    (hx : dx ≠ zero) (u dm rC err : F) : seqSimView u dx dm rC err = u :=
  iteOfNeg hx _ _

private theorem qsum_zero_fn {n : Nat} {f : Fin n → Nat} (h : ∀ i, f i = 0) : qsum n f = 0 := by
  rw [qsum_congr h, qsum_const, Nat.mul_zero]

/-- **Counting core.** For every strategy `A`, every joint key/outcome test and every `q ≤ d`, the
    counts of the real run (uniform independent randomizers, key `α`) and of the simulated run
    differ, summed over all keys `α`, by at most `q` times the number of tapes. One round with
    `Δx = 0` opens the same value in both runs; one round with `Δx ≠ 0` opens a uniform value
    in both runs for every key but `α = Δm · Δx⁻¹`. -/
theorem seq_key_test_count_l1 {F : Type} [LawfulField F] [DecidableEq F] {cardF : Nat}
    (enum : SimpleEquiv (Fin cardF) F) (poison : Bool) (test : F → SeqOutcome → Bool) :
    ∀ (q : Nat) (A : SeqAdv F) (d : Nat), q ≤ d → ∀ (s dd p : Bool),
      qsum cardF (fun ca => Spec.natAbsDiff
        (seqCount poison (seqRealView (enum.toFun ca)) enum q A d (test (enum.toFun ca)) s dd p)
        (seqCount poison seqSimView enum q A d (test (enum.toFun ca)) s dd p)) ≤ q * seqTapeCard cardF d := by
  intro q
  induction q with
  | zero =>
    intro A d _ s dd p
    refine Nat.le_trans (Nat.le_of_eq (qsum_zero_fn (fun ca => ?_))) (Nat.zero_le _)
    cases A with
    | done b => rw [seqCount_done, seqCount_done, natAbsDiff_self]
    | round dx dm rC err next => rw [seqCount_zero_round, seqCount_zero_round, natAbsDiff_self]
  | succ q ih =>
    intro A d hqd s dd p
    cases A with
    | done b =>
      refine Nat.le_trans (Nat.le_of_eq (qsum_zero_fn (fun ca => ?_))) (Nat.zero_le _)
      rw [seqCount_done, seqCount_done, natAbsDiff_self]
    | round dx dm rC err next =>
      cases d with
      | zero => exact absurd hqd (Nat.not_succ_le_zero q)
      | succ d =>
        have hq : q ≤ d := Nat.le_of_succ_le_succ hqd
        have hAfter : ∀ w : F,
            qsum cardF (fun ca => Spec.natAbsDiff
              (seqAfterCount poison (seqRealView (enum.toFun ca)) enum q dx next d (test (enum.toFun ca)) s dd p w)
              (seqAfterCount poison seqSimView enum q dx next d (test (enum.toFun ca)) s dd p w)) ≤
              q * seqTapeCard cardF d := by
          intro w
          cases hb : (poison && decide (w ≠ zero)) with
          | true =>
            refine Nat.le_trans (Nat.le_of_eq (qsum_zero_fn (fun ca => ?_))) (Nat.zero_le _)
            rw [seqAfterCount_stop _ enum q dx next d (test (enum.toFun ca)) s dd p hb,
              seqAfterCount_stop _ enum q dx next d (test (enum.toFun ca)) s dd p hb, natAbsDiff_self]
          | false =>
            refine Nat.le_trans (Nat.le_of_eq (qsum_congr (fun ca => ?_)))
              (ih (next w) d hq (s || decide (dx ≠ zero ∧ w = zero))
                (dd || (p && decide (dx ≠ zero ∧ w = zero))) (decide (dx ≠ zero ∧ w = zero)))
            rw [seqAfterCount_cont _ enum q dx next d (test (enum.toFun ca)) s dd p hb,
              seqAfterCount_cont _ enum q dx next d (test (enum.toFun ca)) s dd p hb]
        have hSwap : ∀ wf : Fin cardF → F,
            qsum cardF (fun ca => qsum cardF (fun r => Spec.natAbsDiff
              (seqAfterCount poison (seqRealView (enum.toFun ca)) enum q dx next d (test (enum.toFun ca)) s dd p
                (wf r))
              (seqAfterCount poison seqSimView enum q dx next d (test (enum.toFun ca)) s dd p (wf r)))) ≤
              q * (cardF * seqTapeCard cardF d) := by
          intro wf
          rw [qsum_comm]
          refine Nat.le_trans (qsum_le_qsum (fun r => hAfter (wf r))) ?_
          rw [qsum_const, Nat.mul_left_comm]
          exact Nat.le_refl _
        show qsum cardF (fun ca => Spec.natAbsDiff
            (seqCount poison (seqRealView (enum.toFun ca)) enum (q + 1)
              (.round dx dm rC err next) (d + 1) (test (enum.toFun ca)) s dd p)
            (seqCount poison seqSimView enum (q + 1) (.round dx dm rC err next) (d + 1) (test (enum.toFun ca))
              s dd p)) ≤ (q + 1) * (cardF * seqTapeCard cardF d)
        rw [Nat.succ_mul]
        by_cases hx : dx = zero
        · subst hx
          refine Nat.le_trans (Nat.le_trans (qsum_le_qsum (fun ca => ?_))
            (hSwap (fun r => seqSimView (enum.toFun r) zero dm rC err))) (Nat.le_add_right _ _)
          rw [seqCount_succ_round, seqCount_succ_round]
          refine Nat.le_trans (natAbsDiff_qsum_le' _ _) (Nat.le_of_eq (qsum_congr (fun r => ?_)))
          rw [seqRealView_zero_shift]
        · have hPt : ∀ ca : Fin cardF,
              Spec.natAbsDiff
                (seqCount poison (seqRealView (enum.toFun ca)) enum (q + 1)
                  (.round dx dm rC err next) (d + 1) (test (enum.toFun ca)) s dd p)
                (seqCount poison seqSimView enum (q + 1) (.round dx dm rC err next) (d + 1) (test (enum.toFun ca))
                  s dd p) ≤
              qsum cardF (fun r => Spec.natAbsDiff
                (seqAfterCount poison (seqRealView (enum.toFun ca)) enum q dx next d (test (enum.toFun ca)) s dd p
                  (enum.toFun r))
                (seqAfterCount poison seqSimView enum q dx next d (test (enum.toFun ca)) s dd p (enum.toFun r))) +
              (cardF * seqTapeCard cardF d) *
                (if decide (sub (mul dx (enum.toFun ca)) dm = zero) = true then 1 else 0) := by
            intro ca
            rw [seqCount_succ_round, seqCount_succ_round]
            have hSimEq : qsum cardF (fun r =>
                  seqAfterCount poison seqSimView enum q dx next d (test (enum.toFun ca)) s dd p
                    (seqSimView (enum.toFun r) dx dm rC err)) =
                qsum cardF (fun r =>
                  seqAfterCount poison seqSimView enum q dx next d (test (enum.toFun ca)) s dd p (enum.toFun r)) :=
              qsum_congr (fun r => by rw [seqSimView_shifted hx])
            rw [hSimEq]
            by_cases hd : sub (mul dx (enum.toFun ca)) dm = zero
            · rw [iteOfPos (decide_eq_true hd), Nat.mul_one]
              refine Nat.le_trans (natAbsDiff_le_of_le ?_ ?_) (Nat.le_add_left _ _)
              · refine Nat.le_trans (qsum_le_qsum (fun r => seqAfterCount_le _ _ _ _ _ _ _ _ _ _ _ _)) ?_
                rw [qsum_const]
                exact Nat.le_refl _
              · refine Nat.le_trans (qsum_le_qsum (fun r => seqAfterCount_le _ _ _ _ _ _ _ _ _ _ _ _)) ?_
                rw [qsum_const]
                exact Nat.le_refl _
            · have hBij : qsum cardF (fun r =>
                    seqAfterCount poison (seqRealView (enum.toFun ca)) enum q dx next d (test (enum.toFun ca))
                      s dd p (seqRealView (enum.toFun ca) (enum.toFun r) dx dm rC err)) =
                  qsum cardF (fun r =>
                    seqAfterCount poison (seqRealView (enum.toFun ca)) enum q dx next d (test (enum.toFun ca))
                      s dd p (enum.toFun r)) :=
                Eq.trans (qsum_congr (fun r => by rw [affineBlindEquiv_toFun]; rfl))
                  (qsum_bijection_invariant enum (affineBlindEquiv rC _ err hd)
                    (seqAfterCount poison (seqRealView (enum.toFun ca)) enum q dx next d (test (enum.toFun ca))
                      s dd p))
              rw [hBij]
              exact Nat.le_trans (natAbsDiff_qsum_le' _ _) (Nat.le_add_right _ _)
          refine Nat.le_trans (qsum_le_qsum hPt) ?_
          rw [qsum_add, qsum_mul_left]
          refine Nat.add_le_add (hSwap enum.toFun) ?_
          refine Nat.le_trans (Nat.mul_le_mul_left _
            (qsum_indicator_le_one_of_unique cardF
              (fun ca => decide (sub (mul dx (enum.toFun ca)) dm = zero))
              (fun i j hi hj => zero_defect_key_unique enum dx dm (fun h => hx h.1) i j
                (of_decide_eq_true hi) (of_decide_eq_true hj)))) ?_
          rw [Nat.mul_one]
          exact Nat.le_refl _

theorem seq_real_sim_count_l1 {F : Type} [LawfulField F] [DecidableEq F] {cardF : Nat}
    (enum : SimpleEquiv (Fin cardF) F) (poison : Bool) (obs : SeqOutcome → Bool) :
    ∀ (q : Nat) (A : SeqAdv F) (d : Nat), q ≤ d → ∀ (s dd p : Bool),
      qsum cardF (fun ca => Spec.natAbsDiff
        (seqCount poison (seqRealView (enum.toFun ca)) enum q A d obs s dd p)
        (seqCount poison seqSimView enum q A d obs s dd p)) ≤ q * seqTapeCard cardF d :=
  seq_key_test_count_l1 enum poison (fun _ => obs)

/-! ## 3. Games on the product coin space

The games are `coordGame`s on `(Fin cardK × tape) × (Fin cardF × Fin nA)`: an unused seed
coordinate (the PRG seed in section 6), the tape of honest randomizers, the MAC-key coin and
the adversary coin. -/

private theorem mul4_reorder (a b c d e : Nat) :
    a * (b * (c * d)) * e = c * ((a * d) * (e * b)) := by
  simp only [Nat.mul_comm, Nat.mul_left_comm]

/-- **Summed-over-keys identical-until-bad bound.** If, for every seed and adversary coin, the
    fibre counts of two coordinate games differ, summed over the MAC-key coin, by at most
    `Q · cardY`, their distinguishing advantage is at most `Q / cardF`. -/
theorem coordGame_advDist_le_of_l1 {cardK cardY cardF nA : Nat}
    (hPos : 0 < (cardK * cardY) * (cardF * nA)) (hF : 0 < cardF)
    (W₀ W₁ : Fin cardK → Fin cardY → Fin cardF → Fin nA → Bool) (Q : Nat)
    (hL1 : ∀ (ck : Fin cardK) (a : Fin nA), qsum cardF (fun ca => Spec.natAbsDiff
      (fibreWinCount W₀ ck ca a) (fibreWinCount W₁ ck ca a)) ≤ Q * cardY) :
    GameBound (AdvDist (coordGame hPos W₀) (coordGame hPos W₁)) ⟨Q, cardF, hF⟩ := by
  have hAbs : Spec.natAbsDiff (coordGame hPos W₀).winCount (coordGame hPos W₁).winCount ≤
      cardK * (nA * (Q * cardY)) := by
    rw [coordGame_winCount, coordGame_winCount]
    refine Nat.le_trans (natAbsDiff_qsum_le' _ _) ?_
    refine Nat.le_trans (qsum_le_qsum (g := fun _ => nA * (Q * cardY)) (fun ck => ?_))
      (Nat.le_of_eq (qsum_const cardK _))
    refine Nat.le_trans (natAbsDiff_qsum_le' _ _) ?_
    refine Nat.le_trans (qsum_le_qsum (fun ca => natAbsDiff_qsum_le' _ _)) ?_
    refine Nat.le_trans (Nat.le_of_eq (qsum_comm cardF nA (fun ca a =>
      Spec.natAbsDiff (fibreWinCount W₀ ck ca a) (fibreWinCount W₁ ck ca a)))) ?_
    exact Nat.le_trans (qsum_le_qsum (g := fun _ => Q * cardY) (fun a => hL1 ck a))
      (Nat.le_of_eq (qsum_const nA _))
  show Spec.natAbsDiff _ _ * cardF ≤ Q * ((cardK * cardY) * (cardF * nA))
  exact Nat.le_trans (Nat.mul_le_mul_right cardF hAbs) (Nat.le_of_eq (mul4_reorder _ _ _ _ _))

/-- If every fibre of a coordinate game has at most a `Q / M` fraction of accepting
    randomizer coins, its winning probability is at most `Q / M`. -/
theorem coordGame_winProb_le_of_fibre {cardK cardY cardF nA : Nat}
    (hPos : 0 < (cardK * cardY) * (cardF * nA))
    (W : Fin cardK → Fin cardY → Fin cardF → Fin nA → Bool) (Q M : Nat) (hM : 0 < M)
    (hFib : ∀ (ck : Fin cardK) (ca : Fin cardF) (a : Fin nA),
      M * fibreWinCount W ck ca a ≤ Q * cardY) :
    GameBound (coordGame hPos W).winProb ⟨Q, M, hM⟩ := by
  show (coordGame hPos W).winCount * M ≤ Q * ((cardK * cardY) * (cardF * nA))
  rw [coordGame_winCount, Nat.mul_comm _ M, ← qsum_mul_left]
  refine Nat.le_trans (qsum_le_qsum (g := fun _ => cardF * (nA * (Q * cardY))) (fun ck => ?_)) ?_
  · rw [← qsum_mul_left]
    refine Nat.le_trans (qsum_le_qsum (g := fun _ => nA * (Q * cardY)) (fun ca => ?_))
      (Nat.le_of_eq (qsum_const _ _))
    rw [← qsum_mul_left]
    exact Nat.le_trans (qsum_le_qsum (g := fun _ => Q * cardY) (fun a => hFib ck ca a))
      (Nat.le_of_eq (qsum_const _ _))
  · rw [qsum_const]
    refine Nat.le_of_eq ?_
    simp only [Nat.mul_comm, Nat.mul_left_comm]

/-- A game within `ε₁` of a game that is won with probability at most `ε₂` is won with
    probability at most `ε₁ + ε₂`. -/
theorem winProb_le_of_advDist {n : Nat} (G₀ G₁ : FinGame n) {ε₁ ε₂ : Spec.RatBound}
    (hD : GameBound (AdvDist G₀ G₁) ε₁) (hW : GameBound G₁.winProb ε₂) :
    GameBound G₀.winProb (ε₁.add ε₂) := by
  have hD' : Spec.natAbsDiff G₀.winCount G₁.winCount * ε₁.den ≤ ε₁.num * n := hD
  have hW' : G₁.winCount * ε₂.den ≤ ε₂.num * n := hW
  have h0 : G₀.winCount ≤ G₁.winCount + Spec.natAbsDiff G₀.winCount G₁.winCount := by
    unfold Spec.natAbsDiff
    split <;> omega
  show G₀.winCount * (ε₁.den * ε₂.den) ≤ (ε₁.num * ε₂.den + ε₂.num * ε₁.den) * n
  have hA := Nat.mul_le_mul_right ε₁.den hW'
  have hB := Nat.mul_le_mul_right ε₂.den hD'
  have h1 := Nat.mul_le_mul_right (ε₁.den * ε₂.den) h0
  rw [Nat.add_mul] at h1
  have e1 : G₁.winCount * (ε₁.den * ε₂.den) = G₁.winCount * ε₂.den * ε₁.den := by
    rw [Nat.mul_comm ε₁.den ε₂.den, Nat.mul_assoc]
  have e2 : Spec.natAbsDiff G₀.winCount G₁.winCount * (ε₁.den * ε₂.den) =
      Spec.natAbsDiff G₀.winCount G₁.winCount * ε₁.den * ε₂.den := by
    rw [Nat.mul_assoc]
  have e3 : (ε₁.num * ε₂.den + ε₂.num * ε₁.den) * n =
      ε₂.num * n * ε₁.den + ε₁.num * n * ε₂.den := by
    rw [Nat.add_mul, Nat.mul_right_comm ε₁.num ε₂.den n, Nat.mul_right_comm ε₂.num ε₁.den n,
      Nat.add_comm]
  rw [e1, e2] at h1
  rw [e3]
  exact Nat.le_trans h1 (Nat.add_le_add hA hB)

/-- **Uniform-randomizer game.** Uniform MAC key `α`, a tape of `d` uniform independent honest
    randomizers, adversary coin `a`. The adversary `adv a` gets at most `Q` openings
    `seqRealView α rᵢ …`; the game is won when the outcome of the run satisfies `obs`. -/
abbrev seqIdealKeyGame {F : Type} [LawfulCommRing F] [DecidableEq F] {cardK cardF nA d : Nat}
    (hPos : 0 < (cardK * seqTapeCard cardF d) * (cardF * nA)) (enum : SimpleEquiv (Fin cardF) F)
    (poison : Bool) (test : F → SeqOutcome → Bool) (Q : Nat) (adv : Fin nA → SeqAdv F) :
    FinGame ((cardK * seqTapeCard cardF d) * (cardF * nA)) :=
  coordGame hPos (fun (_ : Fin cardK) cy ca a =>
    test (enum.toFun ca) (seqRun poison (seqRealView (enum.toFun ca)) Q (adv a)
      (tapeDigit enum.toFun zero d cy) false false false))

@[expose] def seqIdealGame {F : Type} [LawfulCommRing F] [DecidableEq F] {cardK cardF nA d : Nat}
    (hPos : 0 < (cardK * seqTapeCard cardF d) * (cardF * nA)) (enum : SimpleEquiv (Fin cardF) F)
    (poison : Bool) (obs : SeqOutcome → Bool) (Q : Nat) (adv : Fin nA → SeqAdv F) :
    FinGame ((cardK * seqTapeCard cardF d) * (cardF * nA)) :=
  seqIdealKeyGame hPos enum poison (fun _ => obs) Q adv

/-- **Simulated game.** Opening `i` is `seqSimView uᵢ …` for the `i`-th uniform tape element;
    the MAC-key coin is not read. -/
abbrev seqSimKeyGame {F : Type} [LawfulCommRing F] [DecidableEq F] {cardK cardF nA d : Nat}
    (hPos : 0 < (cardK * seqTapeCard cardF d) * (cardF * nA)) (enum : SimpleEquiv (Fin cardF) F)
    (poison : Bool) (test : F → SeqOutcome → Bool) (Q : Nat) (adv : Fin nA → SeqAdv F) :
    FinGame ((cardK * seqTapeCard cardF d) * (cardF * nA)) :=
  coordGame hPos (fun (_ : Fin cardK) cy ca a =>
    test (enum.toFun ca) (seqRun poison seqSimView Q (adv a) (tapeDigit enum.toFun zero d cy) false false false))

@[expose] def seqSimGame {F : Type} [LawfulCommRing F] [DecidableEq F] {cardK cardF nA d : Nat}
    (hPos : 0 < (cardK * seqTapeCard cardF d) * (cardF * nA)) (enum : SimpleEquiv (Fin cardF) F)
    (poison : Bool) (obs : SeqOutcome → Bool) (Q : Nat) (adv : Fin nA → SeqAdv F) :
    FinGame ((cardK * seqTapeCard cardF d) * (cardF * nA)) :=
  seqSimKeyGame hPos enum poison (fun _ => obs) Q adv

/-- **(T1, any outcome test.)** `Q` adaptive openings under one MAC key with uniform independent
    honest randomizers are within `Q / |F|` of the simulator, for both poison policies and for
    every final test of the key, guess and acceptance flags. -/
theorem multiSession_blindedMac_uniform_key_test_bound {F : Type} [LawfulField F]
    [DecidableEq F] {cardK cardF nA d : Nat}
    (hPos : 0 < (cardK * seqTapeCard cardF d) * (cardF * nA)) (hF : 0 < cardF)
    (enum : SimpleEquiv (Fin cardF) F) (poison : Bool) (test : F → SeqOutcome → Bool) (Q : Nat)
    (hQ : Q ≤ d) (adv : Fin nA → SeqAdv F) :
    GameBound
      (AdvDist (seqIdealKeyGame hPos enum poison test Q adv) (seqSimKeyGame hPos enum poison test Q adv))
      ⟨Q, cardF, hF⟩ := by
  refine coordGame_advDist_le_of_l1 hPos hF _ _ Q (fun ck a => ?_)
  refine Nat.le_trans (Nat.le_of_eq (qsum_congr (fun ca => ?_)))
    (seq_key_test_count_l1 enum poison test Q (adv a) d hQ false false false)
  rw [fibreWinCount_eq, fibreWinCount_eq]
  rfl

theorem multiSession_blindedMac_uniform_randomizer_obs_bound {F : Type} [LawfulField F]
    [DecidableEq F] {cardK cardF nA d : Nat}
    (hPos : 0 < (cardK * seqTapeCard cardF d) * (cardF * nA)) (hF : 0 < cardF)
    (enum : SimpleEquiv (Fin cardF) F) (poison : Bool) (obs : SeqOutcome → Bool) (Q : Nat)
    (hQ : Q ≤ d) (adv : Fin nA → SeqAdv F) :
    GameBound
      (AdvDist (seqIdealGame hPos enum poison obs Q adv) (seqSimGame hPos enum poison obs Q adv))
      ⟨Q, cardF, hF⟩ :=
  multiSession_blindedMac_uniform_key_test_bound hPos hF enum poison (fun _ => obs) Q hQ adv

/-- **(T1.)** The adversary's guess after `Q` adaptive openings under one MAC key with uniform
    independent honest randomizers distinguishes the real openings from the simulator with
    advantage at most `Q / |F|`, with or without poisoning on the first nonzero opening. -/
theorem multiSession_blindedMac_uniform_randomizer_bound {F : Type} [LawfulField F]
    [DecidableEq F] {cardK cardF nA d : Nat}
    (hPos : 0 < (cardK * seqTapeCard cardF d) * (cardF * nA)) (hF : 0 < cardF)
    (enum : SimpleEquiv (Fin cardF) F) (poison : Bool) (Q : Nat) (hQ : Q ≤ d)
    (adv : Fin nA → SeqAdv F) :
    GameBound
      (AdvDist (seqIdealGame hPos enum poison seqGuess Q adv)
        (seqSimGame hPos enum poison seqGuess Q adv))
      ⟨Q, cardF, hF⟩ :=
  multiSession_blindedMac_uniform_randomizer_obs_bound hPos hF enum poison seqGuess Q hQ adv

/-! ## 4. Forgery acceptance -/

private theorem seqCount_const_false {cardF : Nat}
    (d : Nat) (obs : SeqOutcome → Bool) (o : SeqOutcome) (h : obs o = false) :
    qsum (seqTapeCard cardF d) (fun _ => if obs o = true then 1 else 0) = 0 := by
  rw [h]
  exact qsum_zero_fn (fun _ => rfl)

private theorem sim_hit_count_le_one {F : Type} [LawfulField F] [DecidableEq F] {cardF : Nat}
    (enum : SimpleEquiv (Fin cardF) F) (dx dm rC err : F) :
    qsum cardF (fun r => if decide (dx ≠ zero ∧
      seqSimView (enum.toFun r) dx dm rC err = zero) = true then 1 else 0) ≤ 1 := by
  refine qsum_indicator_le_one_of_unique cardF _ (fun i j hi hj => ?_)
  have hi' := of_decide_eq_true hi
  have hj' := of_decide_eq_true hj
  have ei : enum.toFun i = zero := by
    rw [← seqSimView_shifted hi'.1 (enum.toFun i) dm rC err]
    exact hi'.2
  have ej : enum.toFun j = zero := by
    rw [← seqSimView_shifted hj'.1 (enum.toFun j) dm rC err]
    exact hj'.2
  calc i = enum.invFun (enum.toFun i) := (enum.left_inv i).symm
    _ = enum.invFun (enum.toFun j) := by rw [ei, ej]
    _ = j := enum.left_inv j

/-- In the simulated run at most a `q / |F|` fraction of the tapes has an opening with `Δx ≠ 0`
    that opens `0`. -/
theorem seq_sim_single_count {F : Type} [LawfulField F] [DecidableEq F] {cardF : Nat}
    (enum : SimpleEquiv (Fin cardF) F) (poison : Bool) :
    ∀ (q : Nat) (A : SeqAdv F) (d : Nat), q ≤ d → ∀ (dd p : Bool),
      cardF * seqCount poison seqSimView enum q A d seqSingleAccept false dd p ≤
        q * seqTapeCard cardF d := by
  intro q
  induction q with
  | zero =>
    intro A d _ dd p
    cases A with
    | done b =>
      rw [seqCount_done, seqCount_const_false d _ _ rfl]
      exact Nat.zero_le _
    | round dx dm rC err next =>
      rw [seqCount_zero_round, seqCount_const_false d _ _ rfl]
      exact Nat.zero_le _
  | succ q ih =>
    intro A d hqd dd p
    cases A with
    | done b =>
      rw [seqCount_done, seqCount_const_false d _ _ rfl]
      exact Nat.zero_le _
    | round dx dm rC err next =>
      cases d with
      | zero => exact absurd hqd (Nat.not_succ_le_zero q)
      | succ d =>
        have hq : q ≤ d := Nat.le_of_succ_le_succ hqd
        have hW : ∀ w : F,
            cardF * seqAfterCount poison seqSimView enum q dx next d seqSingleAccept false dd p w ≤
              (cardF * seqTapeCard cardF d) *
                (if decide (dx ≠ zero ∧ w = zero) = true then 1 else 0) +
              q * seqTapeCard cardF d := by
          intro w
          cases hb : (poison && decide (w ≠ zero)) with
          | true =>
            rw [seqAfterCount_stop _ enum q dx next d _ false dd p hb,
              seqCount_const_false d _ _ rfl]
            exact Nat.zero_le _
          | false =>
            rw [seqAfterCount_cont _ enum q dx next d _ false dd p hb]
            cases hh : decide (dx ≠ zero ∧ w = zero) with
            | false => exact Nat.le_trans (ih (next w) d hq _ _) (Nat.le_add_left _ _)
            | true =>
              refine Nat.le_trans (Nat.mul_le_mul_left cardF (seqCount_le _ _ _ _ _ _ _ _ _ _)) ?_
              show cardF * seqTapeCard cardF d ≤ cardF * seqTapeCard cardF d * 1 + _
              omega
        rw [seqCount_succ_round, ← qsum_mul_left]
        refine Nat.le_trans (qsum_le_qsum (fun r => hW _)) ?_
        rw [qsum_add, qsum_mul_left, qsum_const]
        have h1 := Nat.mul_le_mul_left (cardF * seqTapeCard cardF d)
          (sim_hit_count_le_one enum dx dm rC err)
        show _ ≤ (q + 1) * (cardF * seqTapeCard cardF d)
        rw [Nat.succ_mul, Nat.mul_left_comm cardF q]
        omega

/-- In the simulated run at most a `q / |F|²` fraction of the tapes (plus `1 / |F|` when the
    previous opening was an accepted forgery) has two consecutive openings with `Δx ≠ 0` that
    both open `0`. -/
theorem seq_sim_double_count {F : Type} [LawfulField F] [DecidableEq F] {cardF : Nat}
    (enum : SimpleEquiv (Fin cardF) F) (poison : Bool) :
    ∀ (q : Nat) (A : SeqAdv F) (d : Nat), q ≤ d → ∀ (s p : Bool),
      (cardF * cardF) * seqCount poison seqSimView enum q A d seqDoubleAccept s false p ≤
        (q + (if p = true then cardF else 0)) * seqTapeCard cardF d := by
  intro q
  induction q with
  | zero =>
    intro A d _ s p
    cases A with
    | done b =>
      rw [seqCount_done, seqCount_const_false d _ _ rfl]
      exact Nat.zero_le _
    | round dx dm rC err next =>
      rw [seqCount_zero_round, seqCount_const_false d _ _ rfl]
      exact Nat.zero_le _
  | succ q ih =>
    intro A d hqd s p
    cases A with
    | done b =>
      rw [seqCount_done, seqCount_const_false d _ _ rfl]
      exact Nat.zero_le _
    | round dx dm rC err next =>
      cases d with
      | zero => exact absurd hqd (Nat.not_succ_le_zero q)
      | succ d =>
        have hq : q ≤ d := Nat.le_of_succ_le_succ hqd
        have hW : ∀ w : F,
            (cardF * cardF) *
              seqAfterCount poison seqSimView enum q dx next d seqDoubleAccept s false p w ≤
              ((if p = true then cardF * (cardF * seqTapeCard cardF d) else 0) +
                cardF * seqTapeCard cardF d) *
                (if decide (dx ≠ zero ∧ w = zero) = true then 1 else 0) +
              q * seqTapeCard cardF d := by
          intro w
          cases hb : (poison && decide (w ≠ zero)) with
          | true =>
            rw [seqAfterCount_stop _ enum q dx next d _ s false p hb,
              seqCount_const_false d _ _ rfl]
            exact Nat.zero_le _
          | false =>
            rw [seqAfterCount_cont _ enum q dx next d _ s false p hb]
            cases hh : decide (dx ≠ zero ∧ w = zero) with
            | false =>
              have h := ih (next w) d hq (s || false) false
              have e : (false || (p && false)) = false := by cases p <;> rfl
              rw [e]
              show _ ≤ _ * 0 + _
              have h' : (q + (if false = true then cardF else 0)) * seqTapeCard cardF d =
                  q * seqTapeCard cardF d := rfl
              rw [h'] at h
              omega
            | true =>
              cases p with
              | false =>
                have h := ih (next w) d hq (s || true) true
                have h' : (q + (if true = true then cardF else 0)) * seqTapeCard cardF d =
                    q * seqTapeCard cardF d + cardF * seqTapeCard cardF d := Nat.add_mul _ _ _
                rw [h'] at h
                show _ ≤ (0 + cardF * seqTapeCard cardF d) * 1 + _
                have h2 : (cardF * cardF) * seqCount poison seqSimView enum q (next w) d
                    seqDoubleAccept (s || true) (false || (false && true)) true =
                    (cardF * cardF) * seqCount poison seqSimView enum q (next w) d
                    seqDoubleAccept (s || true) false true := rfl
                omega
              | true =>
                have h := Nat.mul_le_mul_left (cardF * cardF)
                  (seqCount_le poison seqSimView enum q (next w) d seqDoubleAccept (s || true)
                    (false || (true && true)) true)
                have e := Nat.mul_assoc cardF cardF (seqTapeCard cardF d)
                show _ ≤ (cardF * (cardF * seqTapeCard cardF d) +
                  cardF * seqTapeCard cardF d) * 1 + _
                omega
        rw [seqCount_succ_round, ← qsum_mul_left]
        refine Nat.le_trans (qsum_le_qsum (fun r => hW _)) ?_
        rw [qsum_add, qsum_mul_left, qsum_const]
        have h1 := Nat.mul_le_mul_left
          ((if p = true then cardF * (cardF * seqTapeCard cardF d) else 0) +
            cardF * seqTapeCard cardF d)
          (sim_hit_count_le_one enum dx dm rC err)
        refine Nat.le_trans (Nat.add_le_add_right h1 _) ?_
        have e1 : cardF * (q * seqTapeCard cardF d) = q * (cardF * seqTapeCard cardF d) :=
          Nat.mul_left_comm _ _ _
        cases p with
        | false =>
          show (0 + cardF * seqTapeCard cardF d) * 1 + cardF * (q * seqTapeCard cardF d) ≤
            (q + 1 + 0) * (cardF * seqTapeCard cardF d)
          have e2 : (q + 1 + 0) * (cardF * seqTapeCard cardF d) =
              q * (cardF * seqTapeCard cardF d) + cardF * seqTapeCard cardF d := by
            rw [Nat.add_zero, Nat.succ_mul]
          omega
        | true =>
          show (cardF * (cardF * seqTapeCard cardF d) + cardF * seqTapeCard cardF d) * 1 +
            cardF * (q * seqTapeCard cardF d) ≤ (q + 1 + cardF) * (cardF * seqTapeCard cardF d)
          have e2 : (q + 1 + cardF) * (cardF * seqTapeCard cardF d) =
              q * (cardF * seqTapeCard cardF d) + cardF * seqTapeCard cardF d +
                cardF * (cardF * seqTapeCard cardF d) := by
            rw [Nat.add_mul, Nat.succ_mul]
          omega

/-- The simulator's openings contain an accepted forgery with probability at most `Q / |F|`. -/
theorem seqSimGame_single_accept_bound {F : Type} [LawfulField F] [DecidableEq F]
    {cardK cardF nA d : Nat}
    (hPos : 0 < (cardK * seqTapeCard cardF d) * (cardF * nA)) (hF : 0 < cardF)
    (enum : SimpleEquiv (Fin cardF) F) (poison : Bool) (Q : Nat) (hQ : Q ≤ d)
    (adv : Fin nA → SeqAdv F) :
    GameBound (seqSimGame hPos enum poison seqSingleAccept Q adv).winProb ⟨Q, cardF, hF⟩ := by
  unfold seqSimGame seqSimKeyGame
  refine coordGame_winProb_le_of_fibre hPos _ Q cardF hF (fun ck ca a => ?_)
  rw [fibreWinCount_eq]
  exact seq_sim_single_count enum poison Q (adv a) d hQ false false

/-- The simulator's openings contain two consecutive accepted forgeries with probability at
    most `Q / |F|²`. -/
theorem seqSimGame_double_accept_bound {F : Type} [LawfulField F] [DecidableEq F]
    {cardK cardF nA d : Nat}
    (hPos : 0 < (cardK * seqTapeCard cardF d) * (cardF * nA)) (hF : 0 < cardF)
    (enum : SimpleEquiv (Fin cardF) F) (poison : Bool) (Q : Nat) (hQ : Q ≤ d)
    (adv : Fin nA → SeqAdv F) :
    GameBound (seqSimGame hPos enum poison seqDoubleAccept Q adv).winProb
      ⟨Q, cardF * cardF, Nat.mul_pos hF hF⟩ := by
  unfold seqSimGame seqSimKeyGame
  refine coordGame_winProb_le_of_fibre hPos _ Q (cardF * cardF) (Nat.mul_pos hF hF)
    (fun ck ca a => ?_)
  rw [fibreWinCount_eq]
  exact seq_sim_double_count enum poison Q (adv a) d hQ false false

/-- **(T2, one blinding round.)** With uniform independent honest randomizers, the probability
    that some of `Q` adaptive openings with `Δx ≠ 0` opens `0` is at most `2Q / |F|`, for every
    choice of corrupt randomizer shares and additive errors `err` (acceptance is the opened
    value being `0`, whatever `err` is). -/
theorem multiSession_blindedMac_single_round_acceptance_bound {F : Type} [LawfulField F]
    [DecidableEq F] {cardK cardF nA d : Nat}
    (hPos : 0 < (cardK * seqTapeCard cardF d) * (cardF * nA)) (hF : 0 < cardF)
    (enum : SimpleEquiv (Fin cardF) F) (poison : Bool) (Q : Nat) (hQ : Q ≤ d)
    (adv : Fin nA → SeqAdv F) :
    GameBound (seqIdealGame hPos enum poison seqSingleAccept Q adv).winProb
      ⟨2 * Q, cardF, hF⟩ := by
  refine Spec.GameBound.trans (winProb_le_of_advDist _ _
    (multiSession_blindedMac_uniform_randomizer_obs_bound hPos hF enum poison seqSingleAccept Q
      hQ adv)
    (seqSimGame_single_accept_bound hPos hF enum poison Q hQ adv)) ?_
  show (Q * cardF + Q * cardF) * cardF ≤ 2 * Q * (cardF * cardF)
  rw [← Nat.two_mul, Nat.mul_assoc 2 Q (cardF * cardF), Nat.mul_assoc 2 (Q * cardF) cardF,
    Nat.mul_assoc Q cardF cardF]
  exact Nat.le_refl _

/-- **(T2, the two-round rule `BLIND_ROUNDS = 2`.)** With uniform independent honest
    randomizers, the probability that two consecutive openings with `Δx ≠ 0` among `Q` adaptive
    openings both open `0` is at most `Q / |F| + Q / |F|²`. -/
theorem multiSession_blindedMac_two_round_acceptance_bound {F : Type} [LawfulField F]
    [DecidableEq F] {cardK cardF nA d : Nat}
    (hPos : 0 < (cardK * seqTapeCard cardF d) * (cardF * nA)) (hF : 0 < cardF)
    (enum : SimpleEquiv (Fin cardF) F) (poison : Bool) (Q : Nat) (hQ : Q ≤ d)
    (adv : Fin nA → SeqAdv F) :
    GameBound (seqIdealGame hPos enum poison seqDoubleAccept Q adv).winProb
      ((⟨Q, cardF, hF⟩ : Spec.RatBound).add ⟨Q, cardF * cardF, Nat.mul_pos hF hF⟩) :=
  winProb_le_of_advDist _ _
    (multiSession_blindedMac_uniform_randomizer_obs_bound hPos hF enum poison seqDoubleAccept Q
      hQ adv)
    (seqSimGame_double_accept_bound hPos hF enum poison Q hQ adv)

/-! ## 5. Teeth

`zeroRandomizerAdv` shows that one blinding round accepts a forgery with probability above
`1 / |F|`. `learnAndForgeAdv` plays against the unblinded opening `seqRawView` without poison:
its first opening is the MAC key, its second is a forgery that opens `0` on every coin. -/

theorem seqCount_single_shot {F : Type} [LawfulCommRing F] [DecidableEq F] {cardF : Nat}
    (poison : Bool) (view : F → F → F → F → F → F) (enum : SimpleEquiv (Fin cardF) F) (q : Nat)
    (dx dm rC err : F) (b : Bool) (d : Nat) (dd p : Bool) :
    seqCount poison view enum (q + 1) (.round dx dm rC err (fun _ => .done b)) (d + 1)
        seqSingleAccept false dd p =
      qsum cardF (fun r => seqTapeCard cardF d *
        (if decide (dx ≠ zero ∧ view (enum.toFun r) dx dm rC err = zero) = true then 1 else 0)) := by
  rw [seqCount_succ_round]
  refine qsum_congr (fun r => ?_)
  generalize view (enum.toFun r) dx dm rC err = w
  cases hb : (poison && decide (w ≠ zero)) with
  | true =>
    have hw : w ≠ zero := by
      cases poison with
      | false => exact Bool.noConfusion hb
      | true => exact of_decide_eq_true hb
    rw [seqAfterCount_stop _ enum q dx _ d _ false dd p hb, seqCount_const_false d _ _ rfl,
      iteOfNeg (fun h => hw (of_decide_eq_true h).2), Nat.mul_zero]
  | false =>
    rw [seqAfterCount_cont _ enum q dx _ d _ false dd p hb, seqCount_done]
    cases hh : decide (dx ≠ zero ∧ w = zero) with
    | false =>
      rw [seqCount_const_false d _ _ rfl]
      rfl
    | true =>
      show qsum (seqTapeCard cardF d) (fun _ => 1) = seqTapeCard cardF d * 1
      exact qsum_const _ 1

/-- One opening with `Δx = 1`, `Δm = 0`, no corrupt randomizer and no error: it opens `r · α`. -/
def zeroRandomizerAdv (F : Type) [LawfulCommRing F] : SeqAdv F :=
  .round one zero zero zero (fun _ => .done false)

private theorem zeroRandomizer_pair_count {F : Type} [LawfulField F] [DecidableEq F]
    {cardF : Nat} (enum : SimpleEquiv (Fin cardF) F) (z : Fin cardF) (hz : enum.toFun z = zero) :
    cardF + cardF ≤ qsum cardF (fun ca => qsum cardF (fun r =>
      if decide ((one : F) ≠ zero ∧
        seqRealView (enum.toFun ca) (enum.toFun r) one zero zero zero = zero) = true
      then 1 else 0)) + 1 := by
  have hne : (one : F) ≠ zero := fun h => LawfulField.zero_ne_one h.symm
  have hR : ∀ alpha : F, seqRealView alpha zero one zero zero zero = zero := by
    intro alpha
    unfold seqRealView
    constructive_ring
  have hA : ∀ r : F, seqRealView zero r one zero zero zero = zero := by
    intro r
    unfold seqRealView
    constructive_ring
  have hPt : ∀ ca r : Fin cardF,
      (if r = z then 1 else 0) + (if ca = z then 1 else 0) ≤
        (if decide ((one : F) ≠ zero ∧
          seqRealView (enum.toFun ca) (enum.toFun r) one zero zero zero = zero) = true
          then 1 else 0) + (if ca = z then (if r = z then 1 else 0) else 0) := by
    intro ca r
    by_cases hr : r = z
    · have hInd : (if decide ((one : F) ≠ zero ∧
          seqRealView (enum.toFun ca) (enum.toFun r) one zero zero zero = zero) = true
          then 1 else 0) = 1 :=
        iteOfPos (decide_eq_true ⟨hne, by rw [hr, hz]; exact hR _⟩) _ _
      rw [hInd, iteOfPos hr]
      exact Nat.le_refl _
    · by_cases hc : ca = z
      · have hInd : (if decide ((one : F) ≠ zero ∧
            seqRealView (enum.toFun ca) (enum.toFun r) one zero zero zero = zero) = true
            then 1 else 0) = 1 :=
          iteOfPos (decide_eq_true ⟨hne, by rw [hc, hz]; exact hA _⟩) _ _
        rw [hInd, iteOfNeg hr, iteOfPos hc, iteOfPos hc]
        exact Nat.le_of_eq (Nat.add_comm 0 1)
      · rw [iteOfNeg hr, iteOfNeg hc]
        exact Nat.zero_le _
  have hDiag : ∀ ca : Fin cardF,
      qsum cardF (fun r => if ca = z then (if r = z then 1 else 0) else 0) =
        (if ca = z then 1 else 0) := by
    intro ca
    by_cases hc : ca = z
    · exact (qsum_congr (fun r => iteOfPos hc _ _)).trans
        ((qsum_eq_indicator cardF z).trans (iteOfPos hc _ _).symm)
    · exact (qsum_congr (fun r => iteOfNeg hc _ _)).trans
        ((qsum_const cardF 0).trans ((Nat.mul_zero cardF).trans (iteOfNeg hc _ _).symm))
  have h1 : qsum cardF (fun ca => 1 + cardF * (if ca = z then 1 else 0)) ≤
      qsum cardF (fun ca => qsum cardF (fun r =>
        if decide ((one : F) ≠ zero ∧
          seqRealView (enum.toFun ca) (enum.toFun r) one zero zero zero = zero) = true
        then 1 else 0) + (if ca = z then 1 else 0)) := by
    refine qsum_le_qsum (fun ca => ?_)
    have hL : qsum cardF (fun r => (if r = z then 1 else 0) + (if ca = z then 1 else 0)) =
        1 + cardF * (if ca = z then 1 else 0) := by
      rw [qsum_add, qsum_eq_indicator, qsum_const]
    refine Nat.le_trans (Nat.le_of_eq hL.symm)
      (Nat.le_trans (qsum_le_qsum (fun r => hPt ca r)) (Nat.le_of_eq ?_))
    rw [qsum_add, hDiag ca]
  rw [qsum_add, qsum_add, qsum_const, qsum_mul_left, qsum_eq_indicator] at h1
  omega

/-- **Tooth: one blinding round accepts a forgery with probability above `1 / |F|`.** The
    opening `r · α` of `zeroRandomizerAdv` is `0` when `α = 0` and also when `r = 0`, on
    `2|F| − 1` of the `|F|²` pairs. So the acceptance probability of `Q` single-round openings
    is not bounded by `Q / |F|`. -/
theorem tooth_zero_randomizer_single_round_acceptance {F : Type} [LawfulField F] [DecidableEq F]
    {cardK cardF nA : Nat} (hPos : 0 < (cardK * seqTapeCard cardF 1) * (cardF * nA))
    (hF2 : 2 ≤ cardF) (enum : SimpleEquiv (Fin cardF) F) (poison : Bool) :
    ¬ GameBound
      (seqIdealGame hPos enum poison seqSingleAccept 1
        (fun _ : Fin nA => zeroRandomizerAdv F)).winProb
      ⟨1, cardF, Nat.lt_of_lt_of_le Nat.zero_lt_two hF2⟩ := by
  intro hB
  have hB' : (seqIdealGame hPos enum poison seqSingleAccept 1
      (fun _ : Fin nA => zeroRandomizerAdv F)).winCount * cardF ≤
      1 * ((cardK * seqTapeCard cardF 1) * (cardF * nA)) := hB
  have hK : 0 < cardK := Nat.pos_of_ne_zero (fun h => by
    rw [h, Nat.zero_mul, Nat.zero_mul] at hPos
    exact Nat.lt_irrefl 0 hPos)
  have hA : 0 < nA := Nat.pos_of_ne_zero (fun h => by
    rw [h, Nat.mul_zero, Nat.mul_zero] at hPos
    exact Nat.lt_irrefl 0 hPos)
  have hFib : ∀ (ck : Fin cardK) (ca : Fin cardF) (a : Fin nA),
      fibreWinCount (fun (_ : Fin cardK) (cy : Fin (seqTapeCard cardF 1)) (ca : Fin cardF)
          (a : Fin nA) => seqSingleAccept (seqRun poison (seqRealView (enum.toFun ca)) 1
            ((fun _ : Fin nA => zeroRandomizerAdv F) a) (tapeDigit enum.toFun zero 1 cy)
            false false false)) ck ca a =
        qsum cardF (fun r => if decide ((one : F) ≠ zero ∧
          seqRealView (enum.toFun ca) (enum.toFun r) one zero zero zero = zero) = true
          then 1 else 0) := by
    intro ck ca a
    rw [fibreWinCount_eq]
    exact (seqCount_single_shot poison (seqRealView (enum.toFun ca)) enum 0 one zero zero zero
      false 0 false false).trans (qsum_congr (fun r => Nat.one_mul _))
  have hCount : (seqIdealGame hPos enum poison seqSingleAccept 1
      (fun _ : Fin nA => zeroRandomizerAdv F)).winCount =
      cardK * (nA * qsum cardF (fun ca => qsum cardF (fun r =>
        if decide ((one : F) ≠ zero ∧
          seqRealView (enum.toFun ca) (enum.toFun r) one zero zero zero = zero) = true
        then 1 else 0))) := by
    unfold seqIdealGame
    rw [coordGame_winCount]
    refine (qsum_congr (fun ck => (qsum_congr (fun ca =>
      (qsum_congr (fun a => hFib ck ca a)).trans (qsum_const nA _))).trans
      (qsum_mul_left nA _))).trans (qsum_const cardK _)
  have hC := zeroRandomizer_pair_count enum (enum.invFun zero) (enum.right_inv zero)
  rw [hCount] at hB'
  generalize qsum cardF (fun ca => qsum cardF (fun r =>
    if decide ((one : F) ≠ zero ∧
      seqRealView (enum.toFun ca) (enum.toFun r) one zero zero zero = zero) = true
    then 1 else 0)) = C at hB' hC
  have hB2 : (cardK * nA) * (C * cardF) ≤ (cardK * nA) * (cardF * cardF) := by
    refine Nat.le_trans (Nat.le_of_eq ?_) (Nat.le_trans hB' (Nat.le_of_eq ?_))
    · simp only [Nat.mul_comm, Nat.mul_left_comm]
    · show 1 * ((cardK * (cardF * 1)) * (cardF * nA)) = _
      rw [Nat.one_mul, Nat.mul_one]
      simp only [Nat.mul_comm, Nat.mul_left_comm]
  have hB3 : C * cardF ≤ cardF * cardF := Nat.le_of_mul_le_mul_left hB2 (Nat.mul_pos hK hA)
  have hB4 : C ≤ cardF :=
    Nat.le_of_mul_le_mul_right hB3 (Nat.lt_of_lt_of_le Nat.zero_lt_two hF2)
  omega

/-- **Unblinded game.** As `seqIdealGame`, with the raw MAC defect `seqRawView` opened in place
    of the blinded value; the randomizer tape is not read. -/
def seqUnblindedGame {F : Type} [LawfulCommRing F] [DecidableEq F] {cardK cardF nA d : Nat}
    (hPos : 0 < (cardK * seqTapeCard cardF d) * (cardF * nA)) (enum : SimpleEquiv (Fin cardF) F)
    (poison : Bool) (obs : SeqOutcome → Bool) (Q : Nat) (adv : Fin nA → SeqAdv F) :
    FinGame ((cardK * seqTapeCard cardF d) * (cardF * nA)) :=
  coordGame hPos (fun (_ : Fin cardK) cy ca a =>
    obs (seqRun poison (seqRawView (enum.toFun ca)) Q (adv a)
      (tapeDigit enum.toFun zero d cy) false false false))

/-- Two openings. The first has `Δx = 1`, `Δm = 0`; the second shifts the MAC by the first
    opened value, `Δx = 1`, `Δm = w₁`; the guess is whether the second opening is `0`. -/
def learnAndForgeAdv (F : Type) [LawfulCommRing F] [DecidableEq F] : SeqAdv F :=
  .round one zero zero zero (fun w₁ =>
    .round one w₁ zero zero (fun w₂ => .done (decide (w₂ = zero))))

theorem seqRawView_forge {F : Type} [LawfulCommRing F] (alpha r r' : F) :
    seqRawView alpha r' one (seqRawView alpha r one zero zero zero) zero zero = zero := by
  unfold seqRawView
  constructive_ring

/-- With poison on, the first unblinded opening already reveals every predicate of
    the key. The adversary returns immediately after observing that opening. -/
theorem unblinded_poison_key_observation {F : Type} [LawfulField F] [DecidableEq F]
    (test : F → Bool) (alpha : F) (rnd : Nat → F) :
    seqGuess (seqRun true (seqRawView alpha) 1
      (.round one zero zero zero (fun w => .done (test w))) rnd false false false) = test alpha := by
  have h : seqRawView alpha (rnd 0) one zero zero zero = alpha := by
    unfold seqRawView
    constructive_ring
  rw [seqRun_succ_round, h]
  unfold seqRound
  split <;> rfl

/-- Without blinding and without poison, the second opening of `learnAndForgeAdv` is an accepted
    forgery (`Δx = 1`, opened value `0`) for every key and every randomizer tape. -/
theorem learnAndForge_unblinded_run {F : Type} [LawfulField F] [DecidableEq F] (alpha : F)
    (rnd : Nat → F) :
    seqGuess (seqRun false (seqRawView alpha) 2 (learnAndForgeAdv F) rnd false false false) =
        true ∧
      seqSingleAccept
        (seqRun false (seqRawView alpha) 2 (learnAndForgeAdv F) rnd false false false) = true :=
  ⟨decide_eq_true (seqRawView_forge alpha (rnd 0) (rnd 1)),
   Bool.or_eq_true_iff.mpr (Or.inr (decide_eq_true
     ⟨fun h => LawfulField.zero_ne_one h.symm, seqRawView_forge alpha (rnd 0) (rnd 1)⟩))⟩

/-- Against the simulator, the guess of `learnAndForgeAdv` is `true` only when the simulated
    run contains an accepted forgery. -/
theorem learnAndForge_sim_run {F : Type} [LawfulField F] [DecidableEq F] (rnd : Nat → F)
    (h : seqGuess (seqRun false seqSimView 2 (learnAndForgeAdv F) rnd false false false) = true) :
    seqSingleAccept (seqRun false seqSimView 2 (learnAndForgeAdv F) rnd false false false) =
      true :=
  Bool.or_eq_true_iff.mpr (Or.inr (decide_eq_true
    ⟨fun h1 => LawfulField.zero_ne_one h1.symm, of_decide_eq_true h⟩))

/-- **Tooth: without blinding and without poison a forgery is accepted with probability `1`.**
    The first aborted opening is the MAC key; the second opening forges with it. The bound
    `2Q / |F|` of the blinded openings fails for the unblinded ones as soon as `|F| > 4`. -/
theorem tooth_unblinded_forgery_breaks_acceptance_bound {F : Type} [LawfulField F]
    [DecidableEq F] {cardK cardF nA d : Nat}
    (hPos : 0 < (cardK * seqTapeCard cardF d) * (cardF * nA)) (hF4 : 4 < cardF)
    (enum : SimpleEquiv (Fin cardF) F) :
    ¬ GameBound
      (seqUnblindedGame hPos enum false seqSingleAccept 2
        (fun _ : Fin nA => learnAndForgeAdv F)).winProb
      ⟨2 * 2, cardF, Nat.lt_trans (by decide) hF4⟩ := by
  intro hB
  have hB' : (seqUnblindedGame hPos enum false seqSingleAccept 2
      (fun _ : Fin nA => learnAndForgeAdv F)).winCount * cardF ≤
      2 * 2 * ((cardK * seqTapeCard cardF d) * (cardF * nA)) := hB
  rw [Spec.FinGame.winCount_of_forall_win _ (fun ω => (learnAndForge_unblinded_run _ _).2),
    Nat.mul_comm (2 * 2)] at hB'
  exact Nat.not_le_of_lt hF4 (Nat.le_of_mul_le_mul_left hB' hPos)

/-- **Tooth: the unblinded openings are not simulatable without poison.** `learnAndForgeAdv`
    outputs `true` on every coin of the unblinded game and with probability at most `2 / |F|`
    against the simulator, so the distance `Q / |F|` of the blinded openings fails for the
    unblinded ones as soon as `|F| > 4`. -/
theorem tooth_unblinded_not_simulatable {F : Type} [LawfulField F] [DecidableEq F]
    {cardK cardF nA d : Nat}
    (hPos : 0 < (cardK * seqTapeCard cardF d) * (cardF * nA)) (hF4 : 4 < cardF) (hd : 2 ≤ d)
    (enum : SimpleEquiv (Fin cardF) F) :
    ¬ GameBound
      (AdvDist
        (seqUnblindedGame hPos enum false seqGuess 2 (fun _ : Fin nA => learnAndForgeAdv F))
        (seqSimGame hPos enum false seqGuess 2 (fun _ : Fin nA => learnAndForgeAdv F)))
      ⟨2, cardF, Nat.lt_trans (by decide) hF4⟩ := by
  intro hB
  have hF : 0 < cardF := Nat.lt_trans (by decide) hF4
  have hB' : Spec.natAbsDiff
      (seqUnblindedGame hPos enum false seqGuess 2
        (fun _ : Fin nA => learnAndForgeAdv F)).winCount
      (seqSimGame hPos enum false seqGuess 2 (fun _ : Fin nA => learnAndForgeAdv F)).winCount *
        cardF ≤ 2 * ((cardK * seqTapeCard cardF d) * (cardF * nA)) := hB
  rw [Spec.FinGame.winCount_of_forall_win _ (fun ω => (learnAndForge_unblinded_run _ _).1)]
    at hB'
  have hLe : (seqSimGame hPos enum false seqGuess 2
        (fun _ : Fin nA => learnAndForgeAdv F)).winCount *
        ((cardK * seqTapeCard cardF d) * (cardF * nA)) ≤
      (seqSimGame hPos enum false seqSingleAccept 2
        (fun _ : Fin nA => learnAndForgeAdv F)).winCount *
        ((cardK * seqTapeCard cardF d) * (cardF * nA)) :=
    Spec.event_le_reduction_win _ _ (fun ω h => learnAndForge_sim_run _ h)
  have hAcc : (seqSimGame hPos enum false seqSingleAccept 2
        (fun _ : Fin nA => learnAndForgeAdv F)).winCount * cardF ≤
      2 * ((cardK * seqTapeCard cardF d) * (cardF * nA)) :=
    seqSimGame_single_accept_bound hPos hF enum false 2 hd _
  generalize (seqSimGame hPos enum false seqGuess 2
    (fun _ : Fin nA => learnAndForgeAdv F)).winCount = m at hB' hLe
  generalize (seqSimGame hPos enum false seqSingleAccept 2
    (fun _ : Fin nA => learnAndForgeAdv F)).winCount = m' at hLe hAcc
  clear hB
  generalize (cardK * seqTapeCard cardF d) * (cardF * nA) = N at hPos hB' hLe hAcc
  have hm : m ≤ m' := Spec.nat_le_of_mul_le_mul_right hLe hPos
  have h1 : N ≤ Spec.natAbsDiff N m + m := by
    unfold Spec.natAbsDiff
    split <;> omega
  have h2 := Nat.mul_le_mul_right cardF h1
  rw [Nat.add_mul] at h2
  have h3 := Nat.mul_le_mul_right cardF hm
  have h4 : N * cardF ≤ N * 4 := by omega
  exact Nat.not_le_of_lt hF4 (Nat.le_of_mul_le_mul_left h4 hPos)

/-- **Tooth: a reused randomizer determines the MAC key.** If the same honest randomizer
    `r ≠ 0` blinds two openings with shifts `(Δx, Δm) = (1, 0)` and `(1, 1)`, the opened values
    `w₁ = r · α` and `w₂ = r · (α − 1)` give `α = w₁ · (w₁ − w₂)⁻¹`. -/
theorem tooth_reused_randomizer_recovers_alpha {F : Type} [LawfulField F] :
    ∃ recover : F → F → F, ∀ alpha r : F, r ≠ zero →
      recover (seqRealView alpha r one zero zero zero) (seqRealView alpha r one one zero zero) =
        alpha := by
  refine ⟨fun w₁ w₂ => mul w₁ (LawfulField.inv (sub w₁ w₂)), fun alpha r hr => ?_⟩
  have h1 : seqRealView alpha r one zero zero zero = mul alpha r := by
    unfold seqRealView
    constructive_ring
  have h2 : sub (seqRealView alpha r one zero zero zero)
      (seqRealView alpha r one one zero zero) = r := by
    unfold seqRealView
    constructive_ring
  show mul (seqRealView alpha r one zero zero zero) (LawfulField.inv (sub
    (seqRealView alpha r one zero zero zero) (seqRealView alpha r one one zero zero))) = alpha
  rw [h2, h1, LawfulCommRing.mul_assoc, LawfulField.mul_inv_cancel hr, LawfulCommRing.mul_one]

/-! ## 6. One persistent PRG seed

The honest randomizer of opening `i` is `decodeMask (prg seed (leBytes L i))` for one uniform
seed. The PRF challenger samples a seed and a function from `L`-byte inputs to mask strings;
the function is a tape of `256 ^ L` mask coins, position `j` answering the input `leBytes L j`.
Decoded, the same tape is the randomizer tape of `seqIdealGame` at depth `256 ^ L`. -/

theorem seqCoinSpace_pos {cardK cardF nA : Nat} (hK : 0 < cardK) (hF : 0 < cardF) (hA : 0 < nA)
    (d : Nat) : 0 < (cardK * seqTapeCard cardF d) * (cardF * nA) :=
  Nat.mul_pos (Nat.mul_pos hK (seqTapeCard_pos hF d)) (Nat.mul_pos hF hA)

theorem tapeDigit_map {α β : Type} {n : Nat} (g : α → β) (s : Fin n → α) (dflt : α) (dflt' : β) :
    ∀ (d : Nat) (t : Fin (seqTapeCard n d)) (j : Nat), j < d →
      g (tapeDigit s dflt d t j) = tapeDigit (fun c => g (s c)) dflt' d t j
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, _, 0, _ => rfl
  | d + 1, _, j + 1, h => tapeDigit_map g s dflt dflt' d _ j (Nat.lt_of_succ_lt_succ h)

theorem tapeDigit_mem {α : Type} {n : Nat} (s : Fin n → α) (dflt : α) :
    ∀ (d : Nat) (t : Fin (seqTapeCard n d)) (j : Nat), j < d →
      ∃ c : Fin n, tapeDigit s dflt d t j = s c
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, _, 0, _ => ⟨_, rfl⟩
  | d + 1, _, j + 1, h => tapeDigit_mem s dflt d _ j (Nat.lt_of_succ_lt_succ h)

/-- Two tapes with the same digits under an injective reading are the same tape. -/
theorem tape_ext {α : Type} {n : Nat} (s : Fin n → α) (dflt : α)
    (hInj : ∀ c c' : Fin n, s c = s c' → c = c') :
    ∀ (d : Nat) (t t' : Fin (seqTapeCard n d)),
      (∀ j : Nat, j < d → tapeDigit s dflt d t j = tapeDigit s dflt d t' j) → t = t' := by
  intro d
  induction d with
  | zero =>
    intro t t' _
    exact Fin.ext ((Nat.lt_one_iff.mp t.2).trans (Nat.lt_one_iff.mp t'.2).symm)
  | succ d ih =>
    intro t t' h
    have h0 : (CoinSplit.prod n (seqTapeCard n d)).chal t =
        (CoinSplit.prod n (seqTapeCard n d)).chal t' := hInj _ _ (h 0 (Nat.succ_pos d))
    have h1 : (CoinSplit.prod n (seqTapeCard n d)).advc t =
        (CoinSplit.prod n (seqTapeCard n d)).advc t' :=
      ih _ _ (fun j hj => h (j + 1) (Nat.succ_lt_succ hj))
    have e1 := (CoinSplit.prod n (seqTapeCard n d)).pair_eta t
    have e2 := (CoinSplit.prod n (seqTapeCard n d)).pair_eta t'
    rw [h0, h1] at e1
    exact e1.symm.trans e2

/-- Every assignment of the first `d` positions to values in the image of the reading is the
    digit sequence of some tape. -/
theorem tape_exists {α : Type} {n : Nat} (s : Fin n → α) (dflt : α) :
    ∀ (d : Nat) (g : Nat → α), (∀ j : Nat, j < d → ∃ c : Fin n, s c = g j) →
      ∃ t : Fin (seqTapeCard n d), ∀ j : Nat, j < d → tapeDigit s dflt d t j = g j := by
  intro d
  induction d with
  | zero =>
    intro g _
    exact ⟨⟨0, Nat.one_pos⟩, fun j h => absurd h (Nat.not_lt_zero j)⟩
  | succ d ih =>
    intro g h
    obtain ⟨c, hc⟩ := h 0 (Nat.succ_pos d)
    obtain ⟨t, ht⟩ := ih (fun j => g (j + 1)) (fun j hj => h (j + 1) (Nat.succ_lt_succ hj))
    refine ⟨(CoinSplit.prod n (seqTapeCard n d)).pair c t, fun j hj => ?_⟩
    cases j with
    | zero => exact (tapeDigit_pair_zero s dflt d c t).trans hc
    | succ j =>
      exact (tapeDigit_pair_succ s dflt d c t j).trans (ht j (Nat.lt_of_succ_lt_succ hj))

/-- Challenger sampler of the PRF experiment at input length `L`: a seed and the function that
    answers the `L`-byte input `inp` with the mask at position `leValue inp` of a tape of
    `256 ^ L` mask coins, and every other input with `[]`. -/
@[expose] def funTapePrfSampler {cardK cardM : Nat} (keySampler : Fin cardK → Bytes)
    (maskSampler : Fin cardM → Bytes) (L : Nat)
    (c : Fin (cardK * seqTapeCard cardM (256 ^ L))) : Bytes × (Bytes → Bytes) :=
  (keySampler ((CoinSplit.prod cardK (seqTapeCard cardM (256 ^ L))).chal c),
   fun inp => if inp.length = L then
     tapeDigit maskSampler [] (256 ^ L)
       ((CoinSplit.prod cardK (seqTapeCard cardM (256 ^ L))).advc c) (leValue inp)
     else [])

theorem funTapePrfSampler_snd_idx {cardK cardM : Nat} (keySampler : Fin cardK → Bytes)
    (maskSampler : Fin cardM → Bytes) (L : Nat) (c : Fin (cardK * seqTapeCard cardM (256 ^ L)))
    (j : Nat) (hj : j < 256 ^ L) :
    (funTapePrfSampler keySampler maskSampler L c).2 (leBytes L j) =
      tapeDigit maskSampler [] (256 ^ L)
        ((CoinSplit.prod cardK (seqTapeCard cardM (256 ^ L))).advc c) j := by
  show (if (leBytes L j).length = L then
      tapeDigit maskSampler [] (256 ^ L)
        ((CoinSplit.prod cardK (seqTapeCard cardM (256 ^ L))).advc c) (leValue (leBytes L j))
      else []) = _
  rw [iteOfPos (leBytes_length L j), leValue_leBytes L j hj]

/-- `funTapePrfSampler` is uniform on the sample set of the PRF challenger, for uniform seed and mask samplers. -/
theorem uniformOn_funTapePrfSampler {cardK cardM keyLen outLen L : Nat}
    {keySampler : Fin cardK → Bytes} {maskSampler : Fin cardM → Bytes}
    (hKey : UniformOn (fun s : Bytes => s.length = keyLen) keySampler)
    (hMask : UniformOn (fun s : Bytes => s.length = outLen) maskSampler) :
    UniformOn (Spec.PrfSampleOk keyLen L outLen)
      (funTapePrfSampler keySampler maskSampler L) where
  mem c := (Eq.to_iff (Spec.PrfSampleOk.public_eqs _ _ _ _)).mpr ⟨hKey.mem _, fun inp =>
    ⟨fun hLen => by
      have hlt : leValue inp < 256 ^ L := by
        have h := leValue_lt inp
        rw [hLen] at h
        exact h
      obtain ⟨m, hm⟩ := tapeDigit_mem maskSampler [] (256 ^ L)
        ((CoinSplit.prod cardK (seqTapeCard cardM (256 ^ L))).advc c) (leValue inp) hlt
      show (if inp.length = L then
        tapeDigit maskSampler [] (256 ^ L)
          ((CoinSplit.prod cardK (seqTapeCard cardM (256 ^ L))).advc c) (leValue inp)
        else []).length = outLen
      rw [iteOfPos hLen, hm]
      exact hMask.mem m,
    fun hNe => iteOfNeg hNe _ _⟩⟩
  injective c c' h := by
    have hk : keySampler ((CoinSplit.prod cardK (seqTapeCard cardM (256 ^ L))).chal c) =
        keySampler ((CoinSplit.prod cardK (seqTapeCard cardM (256 ^ L))).chal c') :=
      congrArg Prod.fst h
    have h1 := hKey.injective _ _ hk
    have h2 : (CoinSplit.prod cardK (seqTapeCard cardM (256 ^ L))).advc c =
        (CoinSplit.prod cardK (seqTapeCard cardM (256 ^ L))).advc c' :=
      tape_ext maskSampler [] hMask.injective (256 ^ L) _ _ (fun j hj => by
        have hf := congrFun (congrArg Prod.snd h) (leBytes L j)
        rw [funTapePrfSampler_snd_idx keySampler maskSampler L c j hj,
          funTapePrfSampler_snd_idx keySampler maskSampler L c' j hj] at hf
        exact hf)
    calc c = (CoinSplit.prod cardK (seqTapeCard cardM (256 ^ L))).pair
            ((CoinSplit.prod cardK (seqTapeCard cardM (256 ^ L))).chal c)
            ((CoinSplit.prod cardK (seqTapeCard cardM (256 ^ L))).advc c) :=
          ((CoinSplit.prod cardK (seqTapeCard cardM (256 ^ L))).pair_eta c).symm
      _ = (CoinSplit.prod cardK (seqTapeCard cardM (256 ^ L))).pair
            ((CoinSplit.prod cardK (seqTapeCard cardM (256 ^ L))).chal c')
            ((CoinSplit.prod cardK (seqTapeCard cardM (256 ^ L))).advc c') := by rw [h1, h2]
      _ = c' := (CoinSplit.prod cardK (seqTapeCard cardM (256 ^ L))).pair_eta c'
  surjective x hx := by
    obtain ⟨hLen, hFun⟩ := (Eq.to_iff (Spec.PrfSampleOk.public_eqs _ _ _ x)).mp hx
    obtain ⟨ck, hck⟩ := hKey.surjective x.1 hLen
    obtain ⟨t, ht⟩ := tape_exists maskSampler [] (256 ^ L) (fun j => x.2 (leBytes L j))
      (fun j _ => hMask.surjective _ ((hFun (leBytes L j)).1 (leBytes_length L j)))
    refine ⟨(CoinSplit.prod cardK (seqTapeCard cardM (256 ^ L))).pair ck t, ?_⟩
    show (keySampler ((CoinSplit.prod cardK (seqTapeCard cardM (256 ^ L))).chal
        ((CoinSplit.prod cardK (seqTapeCard cardM (256 ^ L))).pair ck t)),
      fun inp => if inp.length = L then
        tapeDigit maskSampler [] (256 ^ L)
          ((CoinSplit.prod cardK (seqTapeCard cardM (256 ^ L))).advc
            ((CoinSplit.prod cardK (seqTapeCard cardM (256 ^ L))).pair ck t)) (leValue inp)
        else []) = x
    rw [CoinSplit.chal_pair, CoinSplit.advc_pair, hck]
    refine Prod.ext rfl (funext fun inp => ?_)
    by_cases hL : inp.length = L
    · have hlt : leValue inp < 256 ^ L := by
        have h := leValue_lt inp
        rw [hL] at h
        exact h
      have hEq : leBytes L (leValue inp) = inp := by
        rw [← hL]
        exact leBytes_leValue inp
      show (if inp.length = L then tapeDigit maskSampler [] (256 ^ L) t (leValue inp)
        else []) = x.2 inp
      rw [iteOfPos hL]
      exact (ht (leValue inp) hlt).trans (congrArg x.2 hEq)
    · show (if inp.length = L then tapeDigit maskSampler [] (256 ^ L) t (leValue inp)
        else []) = x.2 inp
      rw [iteOfNeg hL]
      exact ((hFun inp).2 hL).symm

/-- One round of the reduction distinguisher after the opened value `w`: the mirror of
    `seqRound` whose continuation is an oracle program. -/
def seqRoundCode {F : Type} [LawfulCommRing F] [DecidableEq F] (poison : Bool)
    (obs : SeqOutcome → Bool) (k : SeqAdv F → Bool → Bool → Bool → Code byteOracleIface Bool)
    (dx : F) (next : F → SeqAdv F) (s d p : Bool) (w : F) : Code byteOracleIface Bool :=
  if (poison && decide (w ≠ zero)) = true then .ret (obs (seqFinalGuess (next w), s, d))
  else k (next w) (s || decide (dx ≠ zero ∧ w = zero))
    (d || (p && decide (dx ≠ zero ∧ w = zero))) (decide (dx ≠ zero ∧ w = zero))

/-- **Reduction distinguisher.** With the MAC key `alpha` and the strategy fixed by its own
    coin, it plays the `q`-opening game against its oracle: opening number `i` queries the
    `L`-byte encoding of `i`, decodes the answer as the honest randomizer and computes the
    opened value. It returns the test `obs` of the outcome. -/
@[expose] def seqPrfDistinguisher {F : Type} [LawfulCommRing F] [DecidableEq F]
    (decodeMask : Bytes → F) (L : Nat) (poison : Bool) (obs : SeqOutcome → Bool) (alpha : F) :
    Nat → Nat → SeqAdv F → Bool → Bool → Bool → Code byteOracleIface Bool
  | _, _, .done b, s, d, _ => .ret (obs (b, s, d))
  | 0, _, .round _ _ _ _ _, s, d, _ => .ret (obs (false, s, d))
  | q + 1, i, .round dx dm rC err next, s, d, p =>
    .call (leBytes L i) (fun (y : Bytes) =>
      seqRoundCode poison obs
        (fun A' s' d' p' => seqPrfDistinguisher decodeMask L poison obs alpha q (i + 1) A' s' d' p')
        dx next s d p (seqRealView alpha (decodeMask y) dx dm rC err))

/-- The reduction distinguisher for `q` openings makes at most `q` oracle queries. -/
theorem seqPrfDistinguisher_within {F : Type} [LawfulCommRing F] [DecidableEq F]
    (decodeMask : Bytes → F) (L : Nat) (poison : Bool) (obs : SeqOutcome → Bool) (alpha : F) :
    ∀ (q i : Nat) (A : SeqAdv F) (s d p : Bool),
      Spec.Within q (seqPrfDistinguisher decodeMask L poison obs alpha q i A s d p) := by
  intro q
  induction q with
  | zero =>
    intro i A s d p
    cases A with
    | done b => exact Spec.Within.ret 0 _
    | round dx dm rC err next => exact Spec.Within.ret 0 _
  | succ q ih =>
    intro i A s d p
    cases A with
    | done b => exact Spec.Within.ret _ _
    | round dx dm rC err next =>
      refine Spec.Within.call (E := byteOracleIface) (b := q) (leBytes L i) _ (fun y => ?_)
      show Spec.Within q (seqRoundCode poison obs _ dx next s d p
        (seqRealView alpha (decodeMask y) dx dm rC err))
      unfold seqRoundCode
      split
      · exact Spec.Within.ret q _
      · exact ih _ _ _ _ _

/-- The distinguisher's output against a function oracle with enough budget is the test of the
    run whose `j`-th randomizer is the decoded answer to the query `leBytes L (i + j)`. -/
theorem seqPrfDistinguisher_play {F : Type} [LawfulCommRing F] [DecidableEq F]
    (decodeMask : Bytes → F) (L : Nat) (poison : Bool) (obs : SeqOutcome → Bool) (alpha : F)
    (f : Bytes → Bytes) (B : Nat) :
    ∀ (q i : Nat) (A : SeqAdv F) (s d p : Bool) (used : Nat) (rnd : Nat → F),
      used + q ≤ B → (∀ j : Nat, j < q → rnd j = decodeMask (f (leBytes L (i + j)))) →
      (Code.play (Spec.budgetedFunOracle f B)
        (seqPrfDistinguisher decodeMask L poison obs alpha q i A s d p) used).1 =
        obs (seqRun poison (seqRealView alpha) q A rnd s d p) := by
  intro q
  induction q with
  | zero =>
    intro i A s d p used rnd _ _
    cases A with
    | done b => exact congrArg Prod.fst (Code.play_ret _ _ _)
    | round dx dm rC err next => exact congrArg Prod.fst (Code.play_ret _ _ _)
  | succ q ih =>
    intro i A s d p used rnd hB h
    cases A with
    | done b => exact congrArg Prod.fst (Code.play_ret _ _ _)
    | round dx dm rC err next =>
      have h0 : rnd 0 = decodeMask (f (leBytes L i)) := h 0 (Nat.succ_pos q)
      have hOr : Spec.budgetedFunOracle f B used (leBytes L i) = (f (leBytes L i), used + 1) := by
        rw [Spec.budgetedFunOracle.public_eqs]
        exact iteOfPos (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.succ_pos q)) hB) _ _
      have hStep : Code.play (Spec.budgetedFunOracle f B)
            (seqPrfDistinguisher decodeMask L poison obs alpha (q + 1) i
              (.round dx dm rC err next) s d p) used =
          Code.play (Spec.budgetedFunOracle f B)
            (seqRoundCode poison obs
              (fun A' s' d' p' =>
                seqPrfDistinguisher decodeMask L poison obs alpha q (i + 1) A' s' d' p')
              dx next s d p (seqRealView alpha (decodeMask (f (leBytes L i))) dx dm rC err))
            (used + 1) :=
        (Code.play_call (Spec.budgetedFunOracle f B) (leBytes L i) _ used).trans
          (congrArg (fun pr : Bytes × Nat => Code.play (Spec.budgetedFunOracle f B)
            (seqRoundCode poison obs
              (fun A' s' d' p' =>
                seqPrfDistinguisher decodeMask L poison obs alpha q (i + 1) A' s' d' p')
              dx next s d p (seqRealView alpha (decodeMask pr.1) dx dm rC err)) pr.2) hOr)
      rw [hStep, seqRun_succ_round, h0]
      generalize seqRealView alpha (decodeMask (f (leBytes L i))) dx dm rC err = w
      cases hb : (poison && decide (w ≠ zero)) with
      | true =>
        rw [seqRound_stop _ dx next s d p hb]
        have hC : seqRoundCode poison obs
            (fun A' s' d' p' =>
              seqPrfDistinguisher decodeMask L poison obs alpha q (i + 1) A' s' d' p')
            dx next s d p w = .ret (obs (seqFinalGuess (next w), s, d)) := iteOfPos hb _ _
        rw [hC, Code.play_ret]
      | false =>
        rw [seqRound_cont _ dx next s d p hb]
        have hC : seqRoundCode poison obs
            (fun A' s' d' p' =>
              seqPrfDistinguisher decodeMask L poison obs alpha q (i + 1) A' s' d' p')
            dx next s d p w =
            seqPrfDistinguisher decodeMask L poison obs alpha q (i + 1) (next w)
              (s || decide (dx ≠ zero ∧ w = zero)) (d || (p && decide (dx ≠ zero ∧ w = zero)))
              (decide (dx ≠ zero ∧ w = zero)) :=
          iteOfNeg (fun h' => Bool.noConfusion (hb.symm.trans h')) _ _
        rw [hC]
        exact ih (i + 1) (next w) _ _ _ (used + 1) (fun j => rnd (j + 1))
          (by omega)
          (fun j hj => (h (j + 1) (Nat.succ_lt_succ hj)).trans
            (congrArg (fun k => decodeMask (f (leBytes L k)))
              (by omega : i + (j + 1) = i + 1 + j)))

/-- **Real game with one persistent seed.** Uniform seed, uniform MAC key `α`, adversary coin.
    The honest randomizer of opening `i` is `decodeMask (prg seed (leBytes L i))`; the tape
    coordinate of the coin is not read. -/
abbrev seqPrgKeyGame {F : Type} [LawfulCommRing F] [DecidableEq F] {cardK cardF nA : Nat}
    (L : Nat) (hPos : 0 < (cardK * seqTapeCard cardF (256 ^ L)) * (cardF * nA))
    (enum : SimpleEquiv (Fin cardF) F) (prg : Bytes → Bytes → Bytes)
    (keySampler : Fin cardK → Bytes) (decodeMask : Bytes → F) (poison : Bool)
    (test : F → SeqOutcome → Bool) (Q : Nat) (adv : Fin nA → SeqAdv F) :
    FinGame ((cardK * seqTapeCard cardF (256 ^ L)) * (cardF * nA)) :=
  coordGame hPos (fun ck (_ : Fin (seqTapeCard cardF (256 ^ L))) ca a =>
    test (enum.toFun ca) (seqRun poison (seqRealView (enum.toFun ca)) Q (adv a)
      (fun j => decodeMask (prg (keySampler ck) (leBytes L j))) false false false))

@[expose] def seqPrgGame {F : Type} [LawfulCommRing F] [DecidableEq F] {cardK cardF nA : Nat}
    (L : Nat) (hPos : 0 < (cardK * seqTapeCard cardF (256 ^ L)) * (cardF * nA))
    (enum : SimpleEquiv (Fin cardF) F) (prg : Bytes → Bytes → Bytes)
    (keySampler : Fin cardK → Bytes) (decodeMask : Bytes → F) (poison : Bool)
    (obs : SeqOutcome → Bool) (Q : Nat) (adv : Fin nA → SeqAdv F) :
    FinGame ((cardK * seqTapeCard cardF (256 ^ L)) * (cardF * nA)) :=
  seqPrgKeyGame L hPos enum prg keySampler decodeMask poison (fun _ => obs) Q adv

theorem funTapePrfSampler_decode {F : Type} {cardK cardF : Nat}
    (enum : SimpleEquiv (Fin cardF) F) (keySampler : Fin cardK → Bytes)
    (maskSampler : Fin cardF → Bytes) (decodeMask : Bytes → F) (dflt : F)
    (hDecode : ∀ i : Fin cardF, decodeMask (maskSampler i) = enum.toFun i) (L : Nat)
    (c : Fin (cardK * seqTapeCard cardF (256 ^ L))) (j : Nat) (hj : j < 256 ^ L) :
    decodeMask ((funTapePrfSampler keySampler maskSampler L c).2 (leBytes L j)) =
      tapeDigit enum.toFun dflt (256 ^ L)
        ((CoinSplit.prod cardK (seqTapeCard cardF (256 ^ L))).advc c) j := by
  have hFun : (fun i => decodeMask (maskSampler i)) = enum.toFun := funext hDecode
  rw [funTapePrfSampler_snd_idx keySampler maskSampler L c j hj,
    tapeDigit_map decodeMask maskSampler [] dflt (256 ^ L) _ j hj, hFun]

/-- **PRF hop for `Q` openings under one seed.** The game with PRG-expanded randomizers is the
    real `Spec.PrfHard` experiment of the reduction distinguishers and the game with a tape of
    uniform randomizers is the ideal one, for the challenger sampler `funTapePrfSampler`. -/
theorem seqPrg_key_test_prf_bound {F : Type} [LawfulCommRing F] [DecidableEq F]
    {cardK cardF nA : Nat} (L : Nat)
    (hPos : 0 < (cardK * seqTapeCard cardF (256 ^ L)) * (cardF * nA))
    (enum : SimpleEquiv (Fin cardF) F) (prg : Bytes → Bytes → Bytes) (keyLen outLen : Nat)
    (keySampler : Fin cardK → Bytes) (maskSampler : Fin cardF → Bytes) (decodeMask : Bytes → F)
    (hDecode : ∀ i : Fin cardF, decodeMask (maskSampler i) = enum.toFun i)
    (hU : UniformOn (Spec.PrfSampleOk keyLen L outLen)
      (funTapePrfSampler keySampler maskSampler L))
    {𝒜 : Code byteOracleIface Bool → Prop} {εPrf : Spec.RatBound} (poison : Bool)
    (test : F → SeqOutcome → Bool) (Q : Nat) (hQ : Q ≤ 256 ^ L)
    (hPrf : Spec.PrfHard 𝒜 prg keyLen L outLen Q εPrf) (adv : Fin nA → SeqAdv F)
    (h𝒜 : ∀ (alpha : F) (a : Fin nA),
      𝒜 (seqPrfDistinguisher decodeMask L poison (test alpha) alpha Q 0 (adv a) false false false)) :
    GameBound
      (AdvDist (seqPrgKeyGame L hPos enum prg keySampler decodeMask poison test Q adv)
        (seqIdealKeyGame hPos enum poison test Q adv)) εPrf := by
  let distinguisher (b : Fin (cardF * nA)) :=
    let alpha := enum.toFun ((CoinSplit.prod cardF nA).chal b)
    seqPrfDistinguisher decodeMask L poison (test alpha) alpha Q 0
      (adv ((CoinSplit.prod cardF nA).advc b)) false false false
  have hBound := hPrf ((cardK * seqTapeCard cardF (256 ^ L)) * (cardF * nA))
    (cardK * seqTapeCard cardF (256 ^ L)) (cardF * nA) hPos
    (CoinSplit.prod (cardK * seqTapeCard cardF (256 ^ L)) (cardF * nA))
    (funTapePrfSampler keySampler maskSampler L) hU
    distinguisher (fun b => h𝒜 _ _)
  have hReal : seqPrgKeyGame L hPos enum prg keySampler decodeMask poison test Q adv =
      Spec.prfRealGame hPos prg Q
        (fun ω => (funTapePrfSampler keySampler maskSampler L
          ((CoinSplit.prod (cardK * seqTapeCard cardF (256 ^ L)) (cardF * nA)).chal ω)).1)
        (fun ω => distinguisher ((CoinSplit.prod (cardK * seqTapeCard cardF (256 ^ L)) (cardF * nA)).advc ω)) := by
    rw [Spec.prfRealGame.public_eqs]
    apply Spec.FinGame.ext_win
    intro ω
    exact (seqPrfDistinguisher_play decodeMask L poison (test (enum.toFun _)) (enum.toFun _)
      (prg (keySampler _)) Q Q 0 (adv _) false false false 0
      (fun j => decodeMask (prg (keySampler _) (leBytes L j)))
      (Nat.le_of_eq (Nat.zero_add Q))
      (fun j _ => congrArg (fun k => decodeMask (prg (keySampler _) (leBytes L k)))
        (Nat.zero_add j).symm)).symm
  have hIdeal : seqIdealKeyGame hPos enum poison test Q adv =
      Spec.prfIdealGame hPos Q
        (fun ω => (funTapePrfSampler keySampler maskSampler L
          ((CoinSplit.prod (cardK * seqTapeCard cardF (256 ^ L)) (cardF * nA)).chal ω)).2)
        (fun ω => distinguisher ((CoinSplit.prod (cardK * seqTapeCard cardF (256 ^ L)) (cardF * nA)).advc ω)) := by
    rw [Spec.prfIdealGame.public_eqs]
    apply Spec.FinGame.ext_win
    intro ω
    exact (seqPrfDistinguisher_play decodeMask L poison (test (enum.toFun _)) (enum.toFun _)
      (funTapePrfSampler keySampler maskSampler L _).2 Q Q 0 (adv _) false false false 0
      (tapeDigit enum.toFun zero (256 ^ L) _)
      (Nat.le_of_eq (Nat.zero_add Q))
      (fun j hj => ((funTapePrfSampler_decode enum keySampler maskSampler decodeMask zero
        hDecode L _ j (Nat.lt_of_lt_of_le hj hQ)).symm.trans
        (congrArg (fun k => decodeMask ((funTapePrfSampler keySampler maskSampler L _).2
          (leBytes L k))) (Nat.zero_add j).symm)))).symm
  rw [hReal, hIdeal]
  exact hBound

theorem seqPrg_ideal_prf_bound {F : Type} [LawfulCommRing F] [DecidableEq F]
    {cardK cardF nA : Nat} (L : Nat)
    (hPos : 0 < (cardK * seqTapeCard cardF (256 ^ L)) * (cardF * nA))
    (enum : SimpleEquiv (Fin cardF) F) (prg : Bytes → Bytes → Bytes) (keyLen outLen : Nat)
    (keySampler : Fin cardK → Bytes) (maskSampler : Fin cardF → Bytes) (decodeMask : Bytes → F)
    (hDecode : ∀ i : Fin cardF, decodeMask (maskSampler i) = enum.toFun i)
    (hU : UniformOn (Spec.PrfSampleOk keyLen L outLen)
      (funTapePrfSampler keySampler maskSampler L))
    {𝒜 : Code byteOracleIface Bool → Prop} {εPrf : Spec.RatBound} (poison : Bool)
    (obs : SeqOutcome → Bool) (Q : Nat) (hQ : Q ≤ 256 ^ L)
    (hPrf : Spec.PrfHard 𝒜 prg keyLen L outLen Q εPrf) (adv : Fin nA → SeqAdv F)
    (h𝒜 : ∀ (alpha : F) (a : Fin nA),
      𝒜 (seqPrfDistinguisher decodeMask L poison obs alpha Q 0 (adv a) false false false)) :
    GameBound
      (AdvDist (seqPrgGame L hPos enum prg keySampler decodeMask poison obs Q adv)
        (seqIdealGame hPos enum poison obs Q adv)) εPrf :=
  seqPrg_key_test_prf_bound L hPos enum prg keyLen outLen keySampler maskSampler decodeMask
    hDecode hU poison (fun _ => obs) Q hQ hPrf adv h𝒜

/-- **`Q` blinded openings under one MAC key and one PRG seed, any outcome test.** -/
theorem multiSession_blindedMac_persistent_key_test_bound {F : Type} [LawfulField F]
    [DecidableEq F] {cardK cardF nA : Nat} (L : Nat)
    (hPos : 0 < (cardK * seqTapeCard cardF (256 ^ L)) * (cardF * nA)) (hF : 0 < cardF)
    (enum : SimpleEquiv (Fin cardF) F) (prg : Bytes → Bytes → Bytes) (keyLen outLen : Nat)
    (keySampler : Fin cardK → Bytes) (maskSampler : Fin cardF → Bytes) (decodeMask : Bytes → F)
    (hDecode : ∀ i : Fin cardF, decodeMask (maskSampler i) = enum.toFun i)
    (hU : UniformOn (Spec.PrfSampleOk keyLen L outLen)
      (funTapePrfSampler keySampler maskSampler L))
    {𝒜 : Code byteOracleIface Bool → Prop} {εPrf : Spec.RatBound} (poison : Bool)
    (test : F → SeqOutcome → Bool) (Q : Nat) (hQ : Q ≤ 256 ^ L)
    (hPrf : Spec.PrfHard 𝒜 prg keyLen L outLen Q εPrf) (adv : Fin nA → SeqAdv F)
    (h𝒜 : ∀ (alpha : F) (a : Fin nA),
      𝒜 (seqPrfDistinguisher decodeMask L poison (test alpha) alpha Q 0 (adv a) false false false)) :
    GameBound
      (AdvDist (seqPrgKeyGame L hPos enum prg keySampler decodeMask poison test Q adv)
        (seqSimKeyGame hPos enum poison test Q adv))
      (εPrf.add ⟨Q, cardF, hF⟩) :=
  Spec.GameBound.trans
    (Spec.adv_triangle _ (seqIdealKeyGame hPos enum poison test Q adv) _)
    (Spec.RatBound.add_le_add
      (seqPrg_key_test_prf_bound L hPos enum prg keyLen outLen keySampler maskSampler decodeMask
        hDecode hU poison test Q hQ hPrf adv h𝒜)
      (multiSession_blindedMac_uniform_key_test_bound hPos hF enum poison test Q hQ adv))

theorem multiSession_blindedMac_persistent_alpha_obs_bound {F : Type} [LawfulField F]
    [DecidableEq F] {cardK cardF nA : Nat} (L : Nat)
    (hPos : 0 < (cardK * seqTapeCard cardF (256 ^ L)) * (cardF * nA)) (hF : 0 < cardF)
    (enum : SimpleEquiv (Fin cardF) F) (prg : Bytes → Bytes → Bytes) (keyLen outLen : Nat)
    (keySampler : Fin cardK → Bytes) (maskSampler : Fin cardF → Bytes) (decodeMask : Bytes → F)
    (hDecode : ∀ i : Fin cardF, decodeMask (maskSampler i) = enum.toFun i)
    (hU : UniformOn (Spec.PrfSampleOk keyLen L outLen)
      (funTapePrfSampler keySampler maskSampler L))
    {𝒜 : Code byteOracleIface Bool → Prop} {εPrf : Spec.RatBound} (poison : Bool)
    (obs : SeqOutcome → Bool) (Q : Nat) (hQ : Q ≤ 256 ^ L)
    (hPrf : Spec.PrfHard 𝒜 prg keyLen L outLen Q εPrf) (adv : Fin nA → SeqAdv F)
    (h𝒜 : ∀ (alpha : F) (a : Fin nA),
      𝒜 (seqPrfDistinguisher decodeMask L poison obs alpha Q 0 (adv a) false false false)) :
    GameBound
      (AdvDist (seqPrgGame L hPos enum prg keySampler decodeMask poison obs Q adv)
        (seqSimGame hPos enum poison obs Q adv))
      (εPrf.add ⟨Q, cardF, hF⟩) :=
  multiSession_blindedMac_persistent_key_test_bound L hPos hF enum prg keyLen outLen keySampler
    maskSampler decodeMask hDecode hU poison (fun _ => obs) Q hQ hPrf adv h𝒜

/-- **(T3) `Q` adaptive blinded MAC-check openings under one persistent MAC key and one
    persistent PRG seed.** The honest randomizer of opening `i` is
    `decodeMask (prg seed (leBytes L i))`. For every adversary family whose reduction
    distinguishers lie in `𝒜`, and every `prg` that is a `Q`-query `Spec.PrfHard` PRF at input
    length `L` against `𝒜` with advantage `εPrf`, the adversary's guess distinguishes the real
    openings from the simulator `seqSimView`, which does not read the MAC key, with advantage
    at most `εPrf + Q / |F|`, with or without poisoning on the first nonzero opening. The PRF
    term appears once: all `Q` randomizers are outputs of one keyed function under one seed, so
    one `Q`-query PRF experiment replaces them all in a single hop. -/
theorem multiSession_blindedMac_persistent_alpha_bound {F : Type} [LawfulField F]
    [DecidableEq F] {cardK cardF nA : Nat} (L : Nat)
    (hPos : 0 < (cardK * seqTapeCard cardF (256 ^ L)) * (cardF * nA)) (hF : 0 < cardF)
    (enum : SimpleEquiv (Fin cardF) F) (prg : Bytes → Bytes → Bytes) (keyLen outLen : Nat)
    (keySampler : Fin cardK → Bytes) (maskSampler : Fin cardF → Bytes) (decodeMask : Bytes → F)
    (hDecode : ∀ i : Fin cardF, decodeMask (maskSampler i) = enum.toFun i)
    (hU : UniformOn (Spec.PrfSampleOk keyLen L outLen)
      (funTapePrfSampler keySampler maskSampler L))
    {𝒜 : Code byteOracleIface Bool → Prop} {εPrf : Spec.RatBound} (poison : Bool)
    (Q : Nat) (hQ : Q ≤ 256 ^ L)
    (hPrf : Spec.PrfHard 𝒜 prg keyLen L outLen Q εPrf) (adv : Fin nA → SeqAdv F)
    (h𝒜 : ∀ (alpha : F) (a : Fin nA),
      𝒜 (seqPrfDistinguisher decodeMask L poison seqGuess alpha Q 0 (adv a) false false false)) :
    GameBound
      (AdvDist (seqPrgGame L hPos enum prg keySampler decodeMask poison seqGuess Q adv)
        (seqSimGame hPos enum poison seqGuess Q adv))
      (εPrf.add ⟨Q, cardF, hF⟩) :=
  multiSession_blindedMac_persistent_alpha_obs_bound L hPos hF enum prg keyLen outLen keySampler
    maskSampler decodeMask hDecode hU poison seqGuess Q hQ hPrf adv h𝒜

/-- The bound of `multiSession_blindedMac_persistent_alpha_bound` in the weaker shape
    `Q · εPrf + Q / |F|`, for `Q ≥ 1`. The factor `Q` on the PRF term is not needed: a hybrid
    over `Q` independent seeds would pay one PRF term per seed, whereas here one seed keys one
    function that is queried `Q` times, and `εPrf` already bounds `Q`-query distinguishers. -/
theorem multiSession_blindedMac_persistent_alpha_bound_mission_shape {F : Type} [LawfulField F]
    [DecidableEq F] {cardK cardF nA : Nat} (L : Nat)
    (hPos : 0 < (cardK * seqTapeCard cardF (256 ^ L)) * (cardF * nA)) (hF : 0 < cardF)
    (enum : SimpleEquiv (Fin cardF) F) (prg : Bytes → Bytes → Bytes) (keyLen outLen : Nat)
    (keySampler : Fin cardK → Bytes) (maskSampler : Fin cardF → Bytes) (decodeMask : Bytes → F)
    (hDecode : ∀ i : Fin cardF, decodeMask (maskSampler i) = enum.toFun i)
    (hU : UniformOn (Spec.PrfSampleOk keyLen L outLen)
      (funTapePrfSampler keySampler maskSampler L))
    {𝒜 : Code byteOracleIface Bool → Prop} {εPrf : Spec.RatBound} (poison : Bool)
    (Q : Nat) (hQ1 : 1 ≤ Q) (hQ : Q ≤ 256 ^ L)
    (hPrf : Spec.PrfHard 𝒜 prg keyLen L outLen Q εPrf) (adv : Fin nA → SeqAdv F)
    (h𝒜 : ∀ (alpha : F) (a : Fin nA),
      𝒜 (seqPrfDistinguisher decodeMask L poison seqGuess alpha Q 0 (adv a) false false false)) :
    GameBound
      (AdvDist (seqPrgGame L hPos enum prg keySampler decodeMask poison seqGuess Q adv)
        (seqSimGame hPos enum poison seqGuess Q adv))
      ((εPrf.scale Q).add ⟨Q, cardF, hF⟩) :=
  Spec.GameBound.trans
    (multiSession_blindedMac_persistent_alpha_bound L hPos hF enum prg keyLen outLen keySampler
      maskSampler decodeMask hDecode hU poison Q hQ hPrf adv h𝒜)
    (Spec.RatBound.add_le_add
      (by
        show εPrf.num * εPrf.den ≤ Q * εPrf.num * εPrf.den
        exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ hQ1))
      (Spec.RatBound.le_refl _))

/-- **Forgery acceptance under one persistent seed, one blinding round.** -/
theorem multiSession_blindedMac_persistent_alpha_single_round_acceptance_bound {F : Type}
    [LawfulField F] [DecidableEq F] {cardK cardF nA : Nat} (L : Nat)
    (hPos : 0 < (cardK * seqTapeCard cardF (256 ^ L)) * (cardF * nA)) (hF : 0 < cardF)
    (enum : SimpleEquiv (Fin cardF) F) (prg : Bytes → Bytes → Bytes) (keyLen outLen : Nat)
    (keySampler : Fin cardK → Bytes) (maskSampler : Fin cardF → Bytes) (decodeMask : Bytes → F)
    (hDecode : ∀ i : Fin cardF, decodeMask (maskSampler i) = enum.toFun i)
    (hU : UniformOn (Spec.PrfSampleOk keyLen L outLen)
      (funTapePrfSampler keySampler maskSampler L))
    {𝒜 : Code byteOracleIface Bool → Prop} {εPrf : Spec.RatBound} (poison : Bool)
    (Q : Nat) (hQ : Q ≤ 256 ^ L)
    (hPrf : Spec.PrfHard 𝒜 prg keyLen L outLen Q εPrf) (adv : Fin nA → SeqAdv F)
    (h𝒜 : ∀ (alpha : F) (a : Fin nA),
      𝒜 (seqPrfDistinguisher decodeMask L poison seqSingleAccept alpha Q 0 (adv a)
        false false false)) :
    GameBound
      (seqPrgGame L hPos enum prg keySampler decodeMask poison seqSingleAccept Q adv).winProb
      ((εPrf.add ⟨Q, cardF, hF⟩).add ⟨Q, cardF, hF⟩) :=
  winProb_le_of_advDist _ _
    (multiSession_blindedMac_persistent_alpha_obs_bound L hPos hF enum prg keyLen outLen
      keySampler maskSampler decodeMask hDecode hU poison seqSingleAccept Q hQ hPrf adv h𝒜)
    (seqSimGame_single_accept_bound hPos hF enum poison Q hQ adv)

/-- **Forgery acceptance under one persistent seed, the two-round rule.** -/
theorem multiSession_blindedMac_persistent_alpha_two_round_acceptance_bound {F : Type}
    [LawfulField F] [DecidableEq F] {cardK cardF nA : Nat} (L : Nat)
    (hPos : 0 < (cardK * seqTapeCard cardF (256 ^ L)) * (cardF * nA)) (hF : 0 < cardF)
    (enum : SimpleEquiv (Fin cardF) F) (prg : Bytes → Bytes → Bytes) (keyLen outLen : Nat)
    (keySampler : Fin cardK → Bytes) (maskSampler : Fin cardF → Bytes) (decodeMask : Bytes → F)
    (hDecode : ∀ i : Fin cardF, decodeMask (maskSampler i) = enum.toFun i)
    (hU : UniformOn (Spec.PrfSampleOk keyLen L outLen)
      (funTapePrfSampler keySampler maskSampler L))
    {𝒜 : Code byteOracleIface Bool → Prop} {εPrf : Spec.RatBound} (poison : Bool)
    (Q : Nat) (hQ : Q ≤ 256 ^ L)
    (hPrf : Spec.PrfHard 𝒜 prg keyLen L outLen Q εPrf) (adv : Fin nA → SeqAdv F)
    (h𝒜 : ∀ (alpha : F) (a : Fin nA),
      𝒜 (seqPrfDistinguisher decodeMask L poison seqDoubleAccept alpha Q 0 (adv a)
        false false false)) :
    GameBound
      (seqPrgGame L hPos enum prg keySampler decodeMask poison seqDoubleAccept Q adv).winProb
      ((εPrf.add ⟨Q, cardF, hF⟩).add ⟨Q, cardF * cardF, Nat.mul_pos hF hF⟩) :=
  winProb_le_of_advDist _ _
    (multiSession_blindedMac_persistent_alpha_obs_bound L hPos hF enum prg keyLen outLen
      keySampler maskSampler decodeMask hDecode hU poison seqDoubleAccept Q hQ hPrf adv h𝒜)
    (seqSimGame_double_accept_bound hPos hF enum poison Q hQ adv)

/-! ## 7. Instances -/

/-- **`Tower128`, 32-byte seed, 16-byte masks, 5-byte opening counter.** Up to `256 ^ 5 = 2⁴⁰`
    openings under one MAC key and one seed are within `εPrf + Q / 2¹²⁸` of the simulator, if
    `prg` is a `Q`-query PRF at input length `5` against all `Q`-query distinguishers. -/
theorem multiSession_blindedMac_tower128_bound {nA : Nat}
    (hPos : 0 < (256 ^ 32 * seqTapeCard (256 ^ 16) (256 ^ 5)) * (256 ^ 16 * nA))
    (prg : Bytes → Bytes → Bytes)
    {εPrf : Spec.RatBound} (poison : Bool) (Q : Nat) (hQ : Q ≤ 256 ^ 5)
    (hPrf : Spec.PrfHard (fun c => Spec.Within Q c) prg 32 5 16 Q εPrf)
    (adv : Fin nA → SeqAdv Tower128) :
    GameBound
      (AdvDist
        (seqPrgGame 5 hPos tower128ByteEnum prg (bytesSampler 32) tower128DecodeMask poison
          seqGuess Q adv)
        (seqSimGame hPos tower128ByteEnum poison seqGuess Q adv))
      (εPrf.add ((Spec.RatBound.invPow2 128).scale Q)) :=
  Spec.GameBound.trans
    (multiSession_blindedMac_persistent_alpha_bound 5 hPos (Nat.pow_pos (by decide))
      tower128ByteEnum prg 32 16 (bytesSampler 32) (bytesSampler 16) tower128DecodeMask
      tower128DecodeMask_bytesSampler
      (uniformOn_funTapePrfSampler (uniformOn_bytesSampler 32) (uniformOn_bytesSampler 16))
      poison Q hQ hPrf adv
      (fun alpha a => seqPrfDistinguisher_within tower128DecodeMask 5 poison seqGuess alpha Q 0
        (adv a) false false false))
    (Spec.RatBound.add_le_add (Spec.RatBound.le_refl εPrf)
      (by
        show Q * 2 ^ 128 ≤ Q * 1 * 256 ^ 16
        rw [Nat.mul_one]
        exact Nat.mul_le_mul_left Q (by decide)))

/-- The premises of `multiSession_blindedMac_tower128_bound` are jointly satisfiable: the
    truncating PRG with the trivial advantage bound `1` of `prfHard_one`, one adversary coin,
    the two-opening adversary `learnAndForgeAdv` and poison on. -/
theorem inhabited_multiSession_blindedMac_tower128 :
    GameBound
      (AdvDist
        (seqPrgGame 5
          (seqCoinSpace_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide)) Nat.one_pos _)
          tower128ByteEnum (fun seed _ => seed.take 16) (bytesSampler 32) tower128DecodeMask true
          seqGuess 2 (fun _ : Fin 1 => learnAndForgeAdv Tower128))
        (seqSimGame
          (seqCoinSpace_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide)) Nat.one_pos _)
          tower128ByteEnum true seqGuess 2 (fun _ : Fin 1 => learnAndForgeAdv Tower128)))
      (Spec.RatBound.one.add ((Spec.RatBound.invPow2 128).scale 2)) :=
  multiSession_blindedMac_tower128_bound _ (fun seed _ => seed.take 16) true 2 (by decide)
    (prfHard_one _ _ 32 5 16 2) _

/-- One common assignment for the Tower128 reduction's positivity, counter and PRF premises. -/
theorem tower128_joint_premises :
    ∃ (nA Q : Nat) (prg : Bytes → Bytes → Bytes),
      0 < (256 ^ 32 * seqTapeCard (256 ^ 16) (256 ^ 5)) * (256 ^ 16 * nA) ∧
      Q ≤ 256 ^ 5 ∧ Spec.PrfHard (fun c => Spec.Within Q c) prg 32 5 16 Q Spec.RatBound.one :=
  ⟨1, 2, fun seed _ => seed.take 16,
    seqCoinSpace_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide)) Nat.one_pos _,
    by decide, prfHard_one _ _ 32 5 16 2⟩

/-- **`GoldilocksExt2` (`|F| = p²`), uniform independent randomizers.** The distance to the
    simulator is at most `Q / p²`, a forgery passes one blinding round with probability at
    most `2Q / p²` and the two-round rule with probability at most `Q / p² + Q / p⁴`. -/
theorem multiSession_blindedMac_goldilocksExt2_bounds {cardK nA d : Nat}
    (hPos : 0 < (cardK * seqTapeCard (goldilocksPrime ^ 2) d) * (goldilocksPrime ^ 2 * nA))
    (poison : Bool) (Q : Nat) (hQ : Q ≤ d) (adv : Fin nA → SeqAdv GoldilocksExt2) :
    GameBound
      (AdvDist (seqIdealGame hPos goldilocksExt2Enum poison seqGuess Q adv)
        (seqSimGame hPos goldilocksExt2Enum poison seqGuess Q adv))
      ⟨Q, goldilocksPrime ^ 2, Nat.pow_pos (by decide)⟩ ∧
    GameBound (seqIdealGame hPos goldilocksExt2Enum poison seqSingleAccept Q adv).winProb
      ⟨2 * Q, goldilocksPrime ^ 2, Nat.pow_pos (by decide)⟩ ∧
    GameBound (seqIdealGame hPos goldilocksExt2Enum poison seqDoubleAccept Q adv).winProb
      ((⟨Q, goldilocksPrime ^ 2, Nat.pow_pos (by decide)⟩ : Spec.RatBound).add
        ⟨Q, goldilocksPrime ^ 2 * goldilocksPrime ^ 2,
          Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))⟩) :=
  ⟨multiSession_blindedMac_uniform_randomizer_bound hPos _ goldilocksExt2Enum poison Q hQ adv,
   multiSession_blindedMac_single_round_acceptance_bound hPos _ goldilocksExt2Enum poison Q hQ
     adv,
   multiSession_blindedMac_two_round_acceptance_bound hPos _ goldilocksExt2Enum poison Q hQ adv⟩

/-- For `Q ≤ 2⁴⁰` openings over `GoldilocksExt2`, `Q / p² < 2⁻⁸⁷`. -/
theorem multiSession_goldilocksExt2_margin (Q : Nat) (hQ40 : Q ≤ 2 ^ 40) :
    (⟨Q, goldilocksPrime ^ 2, Nat.pow_pos (by decide)⟩ : Spec.RatBound).strictlyMoreThanBits
      87 :=
  Nat.lt_of_le_of_lt
    (Nat.le_trans (Nat.mul_le_mul_right (2 ^ 87) hQ40) (by decide : 2 ^ 40 * 2 ^ 87 ≤ 2 ^ 127))
    (goldilocksExt2_card_gt_two_pow_126 127 (Nat.le_refl 127))

/-- For `Q ≤ 2⁴⁰` openings over `Tower128`, `Q / 2¹²⁸ ≤ 2⁻⁸⁸`. -/
theorem multiSession_tower128_margin (Q : Nat) (hQ40 : Q ≤ 2 ^ 40) :
    ((Spec.RatBound.invPow2 128).scale Q).atLeastBits 88 := by
  show Q * 1 * 2 ^ 88 ≤ 2 ^ 128
  rw [Nat.mul_one]
  exact Nat.le_trans (Nat.mul_le_mul_right (2 ^ 88) hQ40) (by decide)

/-! ## 8. Tooth: a reused randomizer at game level -/

theorem reusedRandomizer_recover {F : Type} [LawfulField F] (alpha r : F) (hr : r ≠ zero) :
    mul (seqRealView alpha r one zero zero zero)
      (LawfulField.inv (sub (seqRealView alpha r one zero zero zero)
        (seqRealView alpha r one one zero zero))) = alpha := by
  have h1 : seqRealView alpha r one zero zero zero = mul alpha r := by
    unfold seqRealView
    constructive_ring
  have h2 : sub (seqRealView alpha r one zero zero zero)
      (seqRealView alpha r one one zero zero) = r := by
    unfold seqRealView
    constructive_ring
  rw [h2, h1, LawfulCommRing.mul_assoc, LawfulField.mul_inv_cancel hr, LawfulCommRing.mul_one]

/-- **Game with a reused randomizer.** As `seqIdealGame`, but the PRG index is not advanced:
    every opening is blinded by the first randomizer of the tape. -/
def seqReuseGame {F : Type} [LawfulCommRing F] [DecidableEq F] {cardK cardF nA d : Nat}
    (hPos : 0 < (cardK * seqTapeCard cardF d) * (cardF * nA)) (enum : SimpleEquiv (Fin cardF) F)
    (poison : Bool) (obs : SeqOutcome → Bool) (Q : Nat) (adv : Fin nA → SeqAdv F) :
    FinGame ((cardK * seqTapeCard cardF d) * (cardF * nA)) :=
  coordGame hPos (fun (_ : Fin cardK) cy ca a =>
    obs (seqRun poison (seqRealView (enum.toFun ca)) Q (adv a)
      (fun _ => tapeDigit enum.toFun zero d cy 0) false false false))

/-- Three openings: shifts `(1, 0)` and `(1, 1)`, then a forgery with `Δx = 1` and
    `Δm = w₁ · (w₁ − w₂)⁻¹`, the MAC key recovered from the first two opened values. -/
def reuseForgeAdv (F : Type) [LawfulField F] [DecidableEq F] : SeqAdv F :=
  .round one zero zero zero (fun w₁ =>
    .round one one zero zero (fun w₂ =>
      .round one (mul w₁ (LawfulField.inv (sub w₁ w₂))) zero zero (fun w₃ =>
        .done (decide (w₃ = zero)))))

/-- With one randomizer blinding every opening and no poison, `reuseForgeAdv` gets a forgery
    accepted for every key and every randomizer. -/
theorem reuseForge_run {F : Type} [LawfulField F] [DecidableEq F] (alpha r : F) :
    seqSingleAccept
      (seqRun false (seqRealView alpha) 3 (reuseForgeAdv F) (fun _ => r) false false false) =
      true := by
  have hne : (one : F) ≠ zero := fun h => LawfulField.zero_ne_one h.symm
  by_cases hr : r = zero
  · have hw1 : seqRealView alpha r one zero zero zero = zero := by
      rw [hr]
      unfold seqRealView
      constructive_ring
    exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr (Or.inl
      (Bool.or_eq_true_iff.mpr (Or.inr (decide_eq_true ⟨hne, hw1⟩))))))
  · have hw3 : seqRealView alpha r one
        (mul (seqRealView alpha r one zero zero zero)
          (LawfulField.inv (sub (seqRealView alpha r one zero zero zero)
            (seqRealView alpha r one one zero zero)))) zero zero = zero := by
      rw [reusedRandomizer_recover alpha r hr]
      unfold seqRealView
      constructive_ring
    exact Bool.or_eq_true_iff.mpr (Or.inr (decide_eq_true ⟨hne, hw3⟩))

/-- **Tooth: a reused randomizer without poison lets a forgery through with probability `1`.**
    Two openings under the same randomizer determine the MAC key, and the third opening forges
    with it; the bound `2Q / |F|` of fresh blinding fails as soon as `|F| > 6`. -/
theorem tooth_reused_randomizer_forgery_breaks_acceptance_bound {F : Type} [LawfulField F]
    [DecidableEq F] {cardK cardF nA d : Nat}
    (hPos : 0 < (cardK * seqTapeCard cardF d) * (cardF * nA)) (hF6 : 6 < cardF)
    (enum : SimpleEquiv (Fin cardF) F) :
    ¬ GameBound
      (seqReuseGame hPos enum false seqSingleAccept 3
        (fun _ : Fin nA => reuseForgeAdv F)).winProb
      ⟨2 * 3, cardF, Nat.lt_trans (by decide) hF6⟩ := by
  intro hB
  have hB' : (seqReuseGame hPos enum false seqSingleAccept 3
      (fun _ : Fin nA => reuseForgeAdv F)).winCount * cardF ≤
      2 * 3 * ((cardK * seqTapeCard cardF d) * (cardF * nA)) := hB
  rw [Spec.FinGame.winCount_of_forall_win _ (fun ω => reuseForge_run _ _),
    Nat.mul_comm (2 * 3)] at hB'
  exact Nat.not_le_of_lt hF6 (Nat.le_of_mul_le_mul_left hB' hPos)

#print axioms Qsag.Spec.PrfSampleOk.public_eqs
#print axioms uniformOn_funTapePrfSampler
#print axioms multiSession_blindedMac_persistent_alpha_bound
#print axioms multiSession_blindedMac_persistent_key_test_bound
#print axioms multiSession_blindedMac_tower128_bound
#print axioms inhabited_multiSession_blindedMac_tower128
#print axioms multiSession_blindedMac_single_round_acceptance_bound
#print axioms multiSession_blindedMac_two_round_acceptance_bound
#print axioms unblinded_poison_key_observation

#verify_constructive
  Qsag.MacBlind.seqRun_done
  Qsag.MacBlind.seqRun_zero_round
  Qsag.MacBlind.seqRun_succ_round
  Qsag.MacBlind.seqRound_stop
  Qsag.MacBlind.seqRound_cont
  Qsag.MacBlind.seqRun_congr
  Qsag.MacBlind.seqTapeCard_pos
  Qsag.MacBlind.tapeDigit_pair_zero
  Qsag.MacBlind.tapeDigit_pair_succ
  Qsag.MacBlind.seqCount_le
  Qsag.MacBlind.seqAfterCount_le
  Qsag.MacBlind.seqCount_done
  Qsag.MacBlind.seqCount_zero_round
  Qsag.MacBlind.seqCount_succ_round
  Qsag.MacBlind.seqAfterCount_stop
  Qsag.MacBlind.seqAfterCount_cont
  Qsag.MacBlind.seqRealView_zero_shift
  Qsag.MacBlind.seqSimView_shifted
  Qsag.MacBlind.seq_key_test_count_l1
  Qsag.MacBlind.multiSession_blindedMac_uniform_key_test_bound
  Qsag.MacBlind.seqPrg_key_test_prf_bound
  Qsag.MacBlind.multiSession_blindedMac_persistent_key_test_bound
  Qsag.MacBlind.unblinded_poison_key_observation
  Qsag.MacBlind.seq_real_sim_count_l1
  Qsag.MacBlind.coordGame_advDist_le_of_l1
  Qsag.MacBlind.coordGame_winProb_le_of_fibre
  Qsag.MacBlind.winProb_le_of_advDist
  Qsag.MacBlind.multiSession_blindedMac_uniform_randomizer_obs_bound
  Qsag.MacBlind.multiSession_blindedMac_uniform_randomizer_bound
  Qsag.MacBlind.seq_sim_single_count
  Qsag.MacBlind.seq_sim_double_count
  Qsag.MacBlind.seqSimGame_single_accept_bound
  Qsag.MacBlind.seqSimGame_double_accept_bound
  Qsag.MacBlind.multiSession_blindedMac_single_round_acceptance_bound
  Qsag.MacBlind.multiSession_blindedMac_two_round_acceptance_bound
  Qsag.MacBlind.seqCount_single_shot
  Qsag.MacBlind.tooth_zero_randomizer_single_round_acceptance
  Qsag.MacBlind.seqRawView_forge
  Qsag.MacBlind.learnAndForge_unblinded_run
  Qsag.MacBlind.learnAndForge_sim_run
  Qsag.MacBlind.tooth_unblinded_forgery_breaks_acceptance_bound
  Qsag.MacBlind.tooth_unblinded_not_simulatable
  Qsag.MacBlind.tooth_reused_randomizer_recovers_alpha
  Qsag.MacBlind.seqCoinSpace_pos
  Qsag.MacBlind.tapeDigit_map
  Qsag.MacBlind.tapeDigit_mem
  Qsag.MacBlind.tape_ext
  Qsag.MacBlind.tape_exists
  Qsag.MacBlind.funTapePrfSampler_snd_idx
  Qsag.MacBlind.uniformOn_funTapePrfSampler
  Qsag.MacBlind.seqPrfDistinguisher_within
  Qsag.MacBlind.seqPrfDistinguisher_play
  Qsag.MacBlind.funTapePrfSampler_decode
  Qsag.MacBlind.seqPrg_ideal_prf_bound
  Qsag.MacBlind.multiSession_blindedMac_persistent_alpha_obs_bound
  Qsag.MacBlind.multiSession_blindedMac_persistent_alpha_bound
  Qsag.MacBlind.multiSession_blindedMac_persistent_alpha_bound_mission_shape
  Qsag.MacBlind.multiSession_blindedMac_persistent_alpha_single_round_acceptance_bound
  Qsag.MacBlind.multiSession_blindedMac_persistent_alpha_two_round_acceptance_bound
  Qsag.MacBlind.multiSession_blindedMac_tower128_bound
  Qsag.MacBlind.tower128_joint_premises
  Qsag.MacBlind.inhabited_multiSession_blindedMac_tower128
  Qsag.MacBlind.multiSession_blindedMac_goldilocksExt2_bounds
  Qsag.MacBlind.multiSession_goldilocksExt2_margin
  Qsag.MacBlind.multiSession_tower128_margin
  Qsag.MacBlind.reusedRandomizer_recover
  Qsag.MacBlind.reuseForge_run
  Qsag.MacBlind.tooth_reused_randomizer_forgery_breaks_acceptance_bound

#verify_inhabited multiSession_blindedMac_tower128_bound tower128_joint_premises

#tooth_pair multiSession_blindedMac_single_round_acceptance_bound vs tooth_zero_randomizer_single_round_acceptance
#tooth_pair multiSession_blindedMac_single_round_acceptance_bound vs tooth_unblinded_forgery_breaks_acceptance_bound
#tooth_pair multiSession_blindedMac_single_round_acceptance_bound vs tooth_reused_randomizer_forgery_breaks_acceptance_bound
#tooth_pair multiSession_blindedMac_uniform_randomizer_bound vs tooth_unblinded_not_simulatable
#tooth_pair multiSession_blindedMac_persistent_alpha_bound vs tooth_unblinded_not_simulatable
#tooth_pair multiSession_blindedMac_persistent_alpha_bound vs tooth_reused_randomizer_recovers_alpha

end Qsag.MacBlind
end
