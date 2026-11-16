module
/-
# Qsag.Protocol.Threshold.SacrificeFreezeSample — the sacrifice check in freeze/sample/check order

The triple-sacrifice check of the threshold ML-DSA engine, placed in the machine of
`Qsag.Oracle.FrozenChallengeGame`. A transcript is a list of gates; each gate carries the
reconstructed operands `x, y`, the claimed product `z`, and one sacrificial triple
`(a j, b j, c j)` per repetition `j`. Under challenge `χ` the gate opens
`ρ = χ·x − a`, `σ = y − b`, `τ = χ·z − c − a·σ − ρ·(b + σ)` and passes when `τ = 0`.
These are the formulas of `sacOpen204` in `ThresholdMlDsaAndToprf.lean`; `openTau_eq` is the
identity `τ = χ·(z − x·y) − (c − a·b)` proved there as `sacOpen204_tau`.

Results, for any constructive field `F` and any duplicate-free list `xs` of challenges:

* `sacrifice_frozen_soundness`: a transcript frozen before the challenges with one wrong
  product is accepted on at most one of the `xs.length ^ reps` challenge vectors.
  `sacrifice_frozen_cheat_attains_one` shows the count one is reached, so the bound
  `(1 / |F|) ^ reps` is exact for this check.
* `sacrifice_zero_reps_never_accepts`, and `step_empty_sample_rejected` in the game module:
  no verdict exists without at least one challenge.
* `sacrifice_honest_complete`: correct products with correct triples pass every challenge.
* `sacrifice_grinding_soundness`: `Q` adaptive attempts against fresh challenge vectors.
* `mldsa_sacrifice_frozen_soundness`: over `F_q`, `q = 8380417`, with `reps ≥ 6` the accepted
  fraction is below `2^-137` (`2^137 < q^6`).
* `tooth_swapped_order_cheat_always_accepted`: if the challenges are sampled before the
  transcript is frozen, the transcript `z = x·y + 1`, `c j = a j · b j + χ_j` is wrong and is
  accepted on every challenge vector.

Scope. Gate values are the reconstructed ones: per-party shares, MACs and the commitment that
realizes `freeze` are not modelled, so "frozen" is the machine's phase order and not a binding
argument. One challenge per repetition is shared by all gates of the transcript, and the
repetitions use independent challenges. The deployed engine draws one challenge in the
degree-6 extension of `F_q` and scales it by base-field values; coordinatewise that is six
base-field repetitions with one triple error per coordinate, which is the `reps = 6` instance
here. That correspondence is stated in this comment and is not a Lean theorem: this module does
not import the engine. Whether the engine's wire protocol fixes the transcript before its
challenge is derived is likewise outside this file.
-/
public import Qsag.Oracle.FrozenChallengeGame
public import Qsag.Math.Lattices
public import Qsag.Math.Tactic.CommRing

public section
namespace Qsag.SacrificeFreeze
open Qsag.FrozenChallenge CommRingOps
set_option autoImplicit false

/-- One checked multiplication with a sacrificial triple per repetition. -/
structure Gate (F : Type) where
  x : F
  y : F
  z : F
  a : Nat → F
  b : Nat → F
  c : Nat → F

variable {F : Type} [LawfulField F]

def gateError (g : Gate F) : F := sub g.z (mul g.x g.y)

def tripleError (g : Gate F) (j : Nat) : F := sub (g.c j) (mul (g.a j) (g.b j))

def openRho (g : Gate F) (j : Nat) (chi : F) : F := sub (mul chi g.x) (g.a j)

def openSigma (g : Gate F) (j : Nat) : F := sub g.y (g.b j)

def openTau (g : Gate F) (j : Nat) (chi : F) : F :=
  sub (sub (sub (mul chi g.z) (g.c j)) (mul (g.a j) (openSigma g j)))
    (mul (openRho g j chi) (add (g.b j) (openSigma g j)))

/-- The opened check value is `χ·(z − x·y) − (c − a·b)`. -/
theorem openTau_eq (g : Gate F) (j : Nat) (chi : F) :
    openTau g j chi = sub (mul chi (gateError g)) (tripleError g j) := by
  unfold openTau openRho openSigma gateError tripleError
  constructive_ring

def gatePasses [DecidableEq F] (g : Gate F) (j : Nat) (chi : F) : Bool :=
  decide (openTau g j chi = zero)

/-- Repetition `j` of a transcript: every gate passes under the shared challenge. -/
def transcriptPasses [DecidableEq F] (T : List (Gate F)) (j : Nat) (chi : F) : Bool :=
  T.all (fun g => gatePasses g j chi)

def sacConfig [DecidableEq F] (reps : Nat) : Config (List (Gate F)) F := ⟨reps, transcriptPasses⟩

/-- Some gate of the transcript claims a wrong product. -/
def Cheats (T : List (Gate F)) : Prop := ∃ g ∈ T, gateError g ≠ zero

/-- Every product and every triple of the transcript is correct. -/
def Honest (T : List (Gate F)) : Prop :=
  ∀ g ∈ T, gateError g = zero ∧ ∀ j, tripleError g j = zero

/-- A wrong gate passes under at most one challenge. -/
theorem wrong_gate_challenge_unique (g : Gate F) (j : Nat) (hd : gateError g ≠ zero)
    {chi1 chi2 : F} (h1 : openTau g j chi1 = zero) (h2 : openTau g j chi2 = zero) :
    chi1 = chi2 := by
  rw [openTau_eq] at h1 h2
  have e1 := LawfulCommRing.sub_eq_zero_iff.mp h1
  have e2 := LawfulCommRing.sub_eq_zero_iff.mp h2
  have solve : ∀ chi : F, mul chi (gateError g) = tripleError g j →
      chi = mul (tripleError g j) (LawfulField.inv (gateError g)) := by
    intro chi e
    rw [← e, LawfulCommRing.mul_assoc, LawfulField.mul_inv_cancel hd, LawfulCommRing.mul_one]
  rw [solve chi1 e1, solve chi2 e2]

theorem cheating_transcript_pass_count_le_one [DecidableEq F] (T : List (Gate F))
    (hCheat : Cheats T) (xs : List F) (hnd : xs.Nodup) (j : Nat) :
    countIf (transcriptPasses T j) xs ≤ 1 := by
  obtain ⟨g, hg, hd⟩ := hCheat
  apply countIf_le_one_of_unique hnd
  intro x y hx hy
  have hx' : gatePasses g j x = true := List.all_eq_true.mp hx g hg
  have hy' : gatePasses g j y = true := List.all_eq_true.mp hy g hg
  exact wrong_gate_challenge_unique g j hd (of_decide_eq_true hx') (of_decide_eq_true hy')

/-- **Sacrifice soundness, freeze before sample.** A transcript committed on the empty view
with a wrong product is accepted on at most one of the `xs.length ^ reps` challenge vectors. -/
theorem sacrifice_frozen_soundness [DecidableEq F] (reps : Nat)
    (A : Adversary (List (Gate F)) F) (xs : List F) (hnd : xs.Nodup)
    (hCheat : Cheats (A.commit [])) :
    countIf (frozenWins (sacConfig reps) A) (vectors xs reps) ≤ 1 ∧
      (vectors xs reps).length = xs.length ^ reps := by
  have h := frozen_win_count_le (sacConfig reps) A xs 1
    (fun j => cheating_transcript_pass_count_le_one (A.commit []) hCheat xs hnd j)
  rw [Nat.one_pow] at h
  exact h

/-- With no repetition configured nothing is accepted, whatever the challenge vector. -/
theorem sacrifice_zero_reps_never_accepts [DecidableEq F] (A : Adversary (List (Gate F)) F)
    (chis : List F) : frozenWins (sacConfig 0) A chis = false :=
  frozenWins_zero_reps (sacConfig 0) A chis rfl

theorem honest_transcript_passes [DecidableEq F] (T : List (Gate F)) (hH : Honest T) (j : Nat)
    (chi : F) : transcriptPasses T j chi = true := by
  apply List.all_eq_true.mpr
  intro g hg
  apply decide_eq_true
  rw [openTau_eq, (hH g hg).1, (hH g hg).2 j, LawfulCommRing.mul_zero, LawfulCommRing.sub_self]

/-- An honest transcript is accepted on every challenge vector of the configured length. -/
theorem sacrifice_honest_complete [DecidableEq F] (reps : Nat) (A : Adversary (List (Gate F)) F)
    (hH : Honest (A.commit [])) (chis : List F) (h1 : 1 ≤ reps) (hLen : chis.length = reps) :
    frozenWins (sacConfig reps) A chis = true :=
  frozenWins_of_allReps (sacConfig reps) A chis h1 hLen
    (allReps_of_getElem _ chis 0
      (fun j x _ => honest_transcript_passes (A.commit []) hH (0 + j) x))

/-- **Sacrifice soundness under grinding.** `Q` adaptive attempts, each a wrong transcript
checked against a fresh independent challenge vector: with `M = xs.length ^ reps`, at most
`Q * M ^ Q / M` of the `M ^ Q` challenge assignments contain an accepted attempt. -/
theorem sacrifice_grinding_soundness [DecidableEq F] (reps : Nat)
    (A : Adversary (List (Gate F)) (List F)) (xs : List F) (hnd : xs.Nodup)
    (hCheat : ∀ hist, Cheats (A.commit hist)) (Q : Nat) :
    countIf (grindWins (sacConfig reps) A []) (vectors (vectors xs reps) Q) * xs.length ^ reps ≤
      Q * (xs.length ^ reps) ^ Q := by
  have h := grinding_win_count_le (sacConfig reps) A xs 1
    (fun hist j => cheating_transcript_pass_count_le_one (A.commit hist) (hCheat hist) xs hnd j)
    Q []
  rw [Nat.one_pow, Nat.mul_one] at h
  exact h

/-! ## The exchanged order -/

/-- A wrong product whose triple errors are the challenges themselves. -/
def fitGate (chis : List F) : Gate F :=
  ⟨zero, zero, one, fun _ => zero, fun _ => zero, fun j => chis.getD j zero⟩

/-- Commits a transcript fitted to the challenge vector in its view. -/
def fittingAdversary : Adversary (List (Gate F)) F := ⟨fun chis => [fitGate chis]⟩

theorem fitGate_gateError (chis : List F) : gateError (fitGate chis) = one := by
  unfold gateError fitGate
  show sub (one : F) (mul zero zero) = one
  rw [LawfulCommRing.mul_zero, LawfulCommRing.sub_zero]

theorem fittingAdversary_cheats (chis : List F) :
    Cheats ((fittingAdversary (F := F)).commit chis) :=
  ⟨fitGate chis, List.mem_singleton.mpr rfl, by
    rw [fitGate_gateError]; exact LawfulField.one_ne_zero⟩

theorem fitGate_passes [DecidableEq F] (chis : List F) (j : Nat) (x : F)
    (hx : chis[j]? = some x) : transcriptPasses [fitGate chis] j x = true := by
  apply List.all_eq_true.mpr
  intro g hg
  rw [List.mem_singleton.mp hg]
  apply decide_eq_true
  rw [openTau_eq, fitGate_gateError]
  have hc : tripleError (fitGate chis) j = x := by
    unfold tripleError fitGate
    show sub (chis.getD j zero) (mul zero zero) = x
    rw [List.getD_eq_getElem?_getD, hx, LawfulCommRing.mul_zero, LawfulCommRing.sub_zero]
    rfl
  rw [hc, LawfulCommRing.mul_one, LawfulCommRing.sub_self]

/-- **Sample before freeze.** In the exchanged order there is an adversary whose transcript
always contains a wrong product and which is accepted on every challenge vector. -/
theorem tooth_swapped_order_cheat_always_accepted [DecidableEq F] (reps : Nat) (h1 : 1 ≤ reps)
    (xs : List F) :
    ∃ A : Adversary (List (Gate F)) F, (∀ chis, Cheats (A.commit chis)) ∧
      countIf (swappedWins (sacConfig reps) A) (vectors xs reps) = xs.length ^ reps :=
  ⟨fittingAdversary, fittingAdversary_cheats,
    swapped_win_count_all (sacConfig reps) fittingAdversary xs h1 (fun chis _ =>
      allReps_of_getElem _ chis 0 (fun j x hx => by
        rw [Nat.zero_add]; exact fitGate_passes chis j x hx))⟩

/-- The frozen bound is reached: a frozen wrong transcript that is accepted on exactly the
challenge vector it was fitted to. -/
theorem sacrifice_frozen_cheat_attains_one [DecidableEq F] (x : F) :
    ∃ A : Adversary (List (Gate F)) F, Cheats (A.commit []) ∧
      frozenWins (sacConfig 1) A [x] = true := by
  refine ⟨⟨fun _ => [fitGate [x]]⟩, fittingAdversary_cheats [x], ?_⟩
  exact frozenWins_of_allReps (sacConfig 1) _ [x] (Nat.le_refl 1) rfl
    (allReps_of_getElem _ [x] 0 (fun j y hy => by
      rw [Nat.zero_add]; exact fitGate_passes [x] j y hy))

/-! ## FIPS 204 modulus -/

/-- Every element of `F_q`, `q = 8380417`, once. -/
def fq204Elems : List Fq204 := enumBelow Fq204.ofNat mldsaQ

theorem fq204Elems_length : fq204Elems.length = mldsaQ := length_enumBelow _ _

theorem fq204Elems_nodup : fq204Elems.Nodup := by
  apply enumBelow_nodup
  intro i j hi hj h
  have hv : (Fq204.ofNat i).val = (Fq204.ofNat j).val := congrArg ModZq.val h
  have hv' : i % mldsaQ = j % mldsaQ := hv
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hv'
  exact hv'

theorem two_pow_137_lt_mldsaQ_pow_six : 2 ^ 137 < mldsaQ ^ 6 := by decide

/-- **ML-DSA sacrifice, freeze before sample.** Over `F_q` with at least six independent
challenges, a frozen transcript with a wrong product is accepted on fewer than a `2^-137`
fraction of the `q ^ reps` challenge vectors. -/
theorem mldsa_sacrifice_frozen_soundness (reps : Nat) (h6 : 6 ≤ reps)
    (A : Adversary (List (Gate Fq204)) Fq204) (hCheat : Cheats (A.commit [])) :
    countIf (frozenWins (sacConfig reps) A) (vectors fq204Elems reps) * 2 ^ 137 <
        (vectors fq204Elems reps).length ∧
      (vectors fq204Elems reps).length = mldsaQ ^ reps := by
  have h := sacrifice_frozen_soundness reps A fq204Elems fq204Elems_nodup hCheat
  rw [fq204Elems_length] at h
  refine ⟨?_, h.2⟩
  rw [h.2]
  have hPow : mldsaQ ^ 6 ≤ mldsaQ ^ reps := Nat.pow_le_pow_right (by decide) h6
  have hMul : countIf (frozenWins (sacConfig reps) A) (vectors fq204Elems reps) * 2 ^ 137 ≤
      1 * 2 ^ 137 := Nat.mul_le_mul_right _ h.1
  rw [Nat.one_mul] at hMul
  exact Nat.lt_of_le_of_lt hMul (Nat.lt_of_lt_of_le two_pow_137_lt_mldsaQ_pow_six hPow)

/-- Over `F_q` in the exchanged order the fitted wrong transcript is accepted on all `q ^ reps`
challenge vectors. -/
theorem tooth_mldsa_swapped_order_cheat_always_accepted (reps : Nat) (h1 : 1 ≤ reps) :
    ∃ A : Adversary (List (Gate Fq204)) Fq204, (∀ chis, Cheats (A.commit chis)) ∧
      countIf (swappedWins (sacConfig reps) A) (vectors fq204Elems reps) = mldsaQ ^ reps := by
  obtain ⟨A, hA, hC⟩ := tooth_swapped_order_cheat_always_accepted (F := Fq204) reps h1 fq204Elems
  rw [fq204Elems_length] at hC
  exact ⟨A, hA, hC⟩

/-! ## Witnesses -/

theorem fq204_zero_one_nodup : [Fq204.ofNat 0, Fq204.ofNat 1].Nodup := by
  refine List.nodup_cons.mpr ⟨fun hm => ?_, List.nodup_cons.mpr ⟨fun h => (nomatch h), List.nodup_nil⟩⟩
  have hv : (Fq204.ofNat 0).val = (Fq204.ofNat 1).val := congrArg ModZq.val (List.mem_singleton.mp hm)
  exact absurd hv (by decide)

/-- A two-challenge list and a frozen wrong transcript over `F_q`. -/
theorem inhabited_sacrifice_frozen_soundness :
    ∃ (A : Adversary (List (Gate Fq204)) Fq204) (xs : List Fq204),
      xs.Nodup ∧ Cheats (A.commit []) :=
  ⟨⟨fun _ => [fitGate []]⟩, [Fq204.ofNat 0, Fq204.ofNat 1], fq204_zero_one_nodup, fittingAdversary_cheats []⟩

theorem inhabited_mldsa_sacrifice_frozen_soundness :
    ∃ (reps : Nat) (A : Adversary (List (Gate Fq204)) Fq204),
      6 ≤ reps ∧ Cheats (A.commit []) :=
  ⟨6, ⟨fun _ => [fitGate []]⟩, by decide, fittingAdversary_cheats []⟩

theorem inhabited_sacrifice_grinding_soundness :
    ∃ (A : Adversary (List (Gate Fq204)) (List Fq204)) (xs : List Fq204),
      xs.Nodup ∧ ∀ hist, Cheats (A.commit hist) :=
  ⟨⟨fun _ => [fitGate []]⟩, [Fq204.ofNat 0, Fq204.ofNat 1], fq204_zero_one_nodup, fun _ => fittingAdversary_cheats []⟩

theorem inhabited_sacrifice_honest_complete :
    ∃ (reps : Nat) (A : Adversary (List (Gate Fq204)) Fq204) (chis : List Fq204),
      Honest (A.commit []) ∧ 1 ≤ reps ∧ chis.length = reps := by
  refine ⟨1, ⟨fun _ => []⟩, [Fq204.ofNat 1], ?_, Nat.le_refl 1, rfl⟩
  intro g hg
  exact nomatch hg

/-! ## Audits

The audit commands read proof bodies, which a module does not export, so they run here. -/

#verify_constructive openTau_eq
#verify_constructive wrong_gate_challenge_unique
#verify_constructive sacrifice_frozen_soundness
#verify_constructive sacrifice_zero_reps_never_accepts
#verify_constructive sacrifice_honest_complete
#verify_constructive sacrifice_grinding_soundness
#verify_constructive sacrifice_frozen_cheat_attains_one
#verify_constructive tooth_swapped_order_cheat_always_accepted
#verify_constructive mldsa_sacrifice_frozen_soundness
#verify_constructive tooth_mldsa_swapped_order_cheat_always_accepted
#verify_constructive fq204Elems_nodup

#verify_inhabited sacrifice_frozen_soundness inhabited_sacrifice_frozen_soundness
#verify_inhabited mldsa_sacrifice_frozen_soundness inhabited_mldsa_sacrifice_frozen_soundness
#verify_inhabited sacrifice_grinding_soundness inhabited_sacrifice_grinding_soundness
#verify_inhabited sacrifice_honest_complete inhabited_sacrifice_honest_complete

#tooth_pair sacrifice_frozen_soundness vs tooth_swapped_order_cheat_always_accepted
#tooth_pair sacrifice_frozen_soundness vs sacrifice_frozen_cheat_attains_one
#tooth_pair mldsa_sacrifice_frozen_soundness vs tooth_mldsa_swapped_order_cheat_always_accepted
#tooth_pair sacrifice_grinding_soundness vs tooth_swapped_order_cheat_always_accepted
#tooth_pair sacrifice_honest_complete vs sacrifice_zero_reps_never_accepts

end Qsag.SacrificeFreeze
