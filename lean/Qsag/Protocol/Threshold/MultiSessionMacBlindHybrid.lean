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
