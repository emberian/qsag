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
base-field repetitions with one triple error per coordinate, connected to the signing engine
step in `Qsag.ThresholdMlDsaSecurity`. This module also mechanizes the dealerless FTS DKG
characteristic-2 Frobenius + sacrificial power-tuple consistency check (`(s, s^2, s^3)` and
`(a, ..., a^7)`) over binary extension fields (`Tower8`, `Tower128`, `Gf2Pow128`).
-/
public import Qsag.Oracle.FrozenChallengeGame
public import Qsag.Math.Lattices
public import Qsag.Math.Gf2Pow128
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

/-! ## Dealerless FTS `s, s², s³` & 7-Power Frobenius Consistency (`L-Ex-15`, `dkg.rs`) -/

section FtsFrobenius

/-- In any characteristic-2 commutative ring (`∀ x, x + x = 0`), negation is the identity. -/
theorem char2_neg_eq_self {K : Type} [LawfulCommRing K]
    (hChar2 : ∀ x : K, add x x = zero) (a : K) : neg a = a :=
  LawfulCommRing.add_left_cancel ((LawfulCommRing.add_right_neg a).trans (hChar2 a).symm)

theorem char2_sub_eq_add {K : Type} [LawfulCommRing K]
    (hChar2 : ∀ x : K, add x x = zero) (a b : K) : sub a b = add a b := by
  rw [LawfulCommRing.sub_eq_add_neg, char2_neg_eq_self hChar2 b]

/-- **Characteristic-2 Frobenius Linearity (`frobenius_sq_add_char2`)**:
    `(a + b)^2 = a^2 + b^2` whenever `∀ x, x + x = 0`. -/
theorem frobenius_sq_add_char2 {K : Type} [LawfulCommRing K]
    (hChar2 : ∀ x : K, add x x = zero) (a b : K) :
    mul (add a b) (add a b) = add (mul a a) (mul b b) := by
  have hExp : mul (add a b) (add a b) =
      add (add (mul a a) (add (mul a b) (mul a b))) (mul b b) := by
    constructive_ring
  rw [hExp, hChar2 (mul a b), LawfulCommRing.add_zero]

/-- Local share-squaring linearity in characteristic 2: `(∑_i s_i)^2 = ∑_i (s_i^2)`, allowing
    each party in the dealerless FTS DKG ceremony to generate additive shares of `r^2` locally
    without interaction. -/
theorem frobenius_sum_shares_eq_sum_squares {K : Type} [LawfulCommRing K]
    (hChar2 : ∀ x : K, add x x = zero) :
    ∀ shares : List K,
      mul (shares.foldr add zero) (shares.foldr add zero) =
        (shares.map (fun s => mul s s)).foldr add zero
  | [] => LawfulCommRing.zero_mul zero
  | s :: rest => by
    simp only [List.foldr_cons, List.map_cons]
    rw [frobenius_sq_add_char2 hChar2, frobenius_sum_shares_eq_sum_squares hChar2 rest]

/-- **Characteristic-2 Frobenius Injectivity (`frobenius_sq_injective_char2`)**:
    Over any characteristic-2 `[LawfulField K]`, `x^2 = y^2 → x = y`. -/
theorem frobenius_sq_injective_char2 {K : Type} [LawfulField K] [DecidableEq K]
    (hChar2 : ∀ x : K, add x x = zero) {x y : K} (hSq : mul x x = mul y y) :
    x = y := by
  have hDiffSq : mul (sub x y) (sub x y) = zero := by
    rw [char2_sub_eq_add hChar2, frobenius_sq_add_char2 hChar2, hSq, hChar2 (mul y y)]
  if hxy : sub x y = zero then
    exact LawfulCommRing.sub_eq_zero_iff.mp hxy
  else
    exfalso
    have hOne : (one : K) = zero := by
      calc (one : K)
          = mul (sub x y) (LawfulField.inv (sub x y)) := (LawfulField.mul_inv_cancel hxy).symm
        _ = mul (mul (sub x y) (LawfulField.inv (sub x y))) one := (LawfulCommRing.mul_one _).symm
        _ = mul (mul (sub x y) (LawfulField.inv (sub x y)))
              (mul (sub x y) (LawfulField.inv (sub x y))) := by
            rw [LawfulField.mul_inv_cancel hxy]
        _ = mul (mul (sub x y) (sub x y))
              (mul (LawfulField.inv (sub x y)) (LawfulField.inv (sub x y))) := by
            constructive_ring
        _ = mul zero _ := by rw [hDiffSq]
        _ = zero := LawfulCommRing.zero_mul _
    exact LawfulField.zero_ne_one hOne.symm

theorem towerElem_char2 (k : Nat) (x : TowerElem k) :
    add x x = (zero : TowerElem k) :=
  towerAdd_self_zero k x

theorem gf2Pow128_char2 (x : Qsag.Math.Gf2Pow128) :
    add x x = (zero : Qsag.Math.Gf2Pow128) :=
  LawfulCommRing.add_left_neg x

private theorem countIf_mono_on_mem {α : Type} {p q : α → Bool} :
    ∀ {xs : List α}, (∀ x ∈ xs, p x = true → q x = true) → countIf p xs ≤ countIf q xs
  | [], _ => Nat.le_refl 0
  | x :: xs, h => by
    show (if p x then 1 else 0) + countIf p xs ≤ (if q x then 1 else 0) + countIf q xs
    have ih := countIf_mono_on_mem (xs := xs) (fun y hy => h y (.tail x hy))
    cases hpx : p x with
    | false =>
      cases q x <;> simp only [↓reduceIte, Bool.false_eq_true] <;> omega
    | true =>
      rw [h x (.head xs) hpx]
      simp only [↓reduceIte]
      omega

private theorem countIf_step_le {α : Type} [DecidableEq α] {p : α → Bool} (B : Nat)
    (hStep : ∀ r : α, p r = true →
      ∀ {ys : List α}, ys.Nodup → countIf (fun x => decide (x ≠ r) && p x) ys ≤ B) :
    ∀ {xs : List α}, xs.Nodup → countIf p xs ≤ B + 1
  | [], _ => Nat.zero_le _
  | r :: rest, hnd => by
    have hCons := List.nodup_cons.mp hnd
    show (if p r then 1 else 0) + countIf p rest ≤ B + 1
    cases hpr : p r with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      exact countIf_step_le B hStep hCons.2
    | true =>
      have hSub : countIf p rest ≤ countIf (fun x => decide (x ≠ r) && p x) rest := by
        refine countIf_mono_on_mem (fun x hx hpx => ?_)
        have hNe : x ≠ r := fun heq => hCons.1 (heq ▸ hx)
        simp [hNe, hpx]
      have hRest := hStep r hpr hCons.2
      simp only [↓reduceIte]
      omega

private theorem field_mul_eq_zero_or {K : Type} [LawfulField K] [DecidableEq K] {a b : K}
    (h : mul a b = zero) : a = zero ∨ b = zero := by
  if ha : a = zero then
    exact Or.inl ha
  else
    refine Or.inr ?_
    calc b
        = mul one b := (LawfulCommRing.one_mul b).symm
      _ = mul (mul (LawfulField.inv a) a) b := by
          rw [LawfulCommRing.mul_comm (LawfulField.inv a) a, LawfulField.mul_inv_cancel ha]
      _ = mul (LawfulField.inv a) (mul a b) := LawfulCommRing.mul_assoc _ _ _
      _ = mul (LawfulField.inv a) zero := by rw [h]
      _ = zero := LawfulCommRing.mul_zero _

/-- Degree-`≤ 3` polynomial `c0 + c1·x + c2·x² + c3·x³`. -/
def evalCubic {K : Type} [LawfulCommRing K] (c0 c1 c2 c3 x : K) : K :=
  add (add (add c0 (mul c1 x)) (mul c2 (mul x x))) (mul c3 (mul x (mul x x)))

private theorem linear_roots_countIf_le_one {K : Type} [LawfulField K] [DecidableEq K]
    (c0 c1 : K) (hc1 : c1 ≠ zero) {xs : List K} (hnd : xs.Nodup) :
    countIf (fun x => decide (add c0 (mul c1 x) = zero)) xs ≤ 1 := by
  refine countIf_step_le 0 (fun r hr {ys} _ => ?_) hnd
  apply Nat.le_of_eq
  apply countIf_eq_zero_of_forall
  intro x _
  cases hConj : (decide (x ≠ r) && decide (add c0 (mul c1 x) = zero)) with
  | false => rfl
  | true =>
    exfalso
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hConj
    have hr0 := of_decide_eq_true hr
    have hDiff : mul c1 (sub x r) = zero := by
      have hId : mul c1 (sub x r) = sub (add c0 (mul c1 x)) (add c0 (mul c1 r)) := by
        constructive_ring
      rw [hId, hConj.2, hr0, LawfulCommRing.sub_self]
    rcases field_mul_eq_zero_or hDiff with hc10 | hxr0
    · exact hc1 hc10
    · exact hConj.1 (LawfulCommRing.sub_eq_zero_iff.mp hxr0)

private theorem quad_roots_countIf_le_two {K : Type} [LawfulField K] [DecidableEq K]
    (c0 c1 c2 : K) (hNz : c1 ≠ zero ∨ c2 ≠ zero) {xs : List K} (hnd : xs.Nodup) :
    countIf (fun x => decide (add (add c0 (mul c1 x)) (mul c2 (mul x x)) = zero)) xs ≤ 2 := by
  if hc2 : c2 = zero then
    have hc1 : c1 ≠ zero := by rcases hNz with h1 | h2; exact h1; exact absurd hc2 h2
    have hLe : countIf (fun x => decide (add (add c0 (mul c1 x)) (mul c2 (mul x x)) = zero)) xs ≤
        countIf (fun x => decide (add c0 (mul c1 x) = zero)) xs := by
      refine countIf_mono_on_mem (fun x _ hx => ?_)
      have hx0 := of_decide_eq_true hx
      rw [hc2, LawfulCommRing.zero_mul, LawfulCommRing.add_zero] at hx0
      exact decide_eq_true hx0
    exact Nat.le_trans hLe (Nat.le_succ_of_le (linear_roots_countIf_le_one c0 c1 hc1 hnd))
  else
    refine countIf_step_le 1 (fun r hr {ys} hndY => ?_) hnd
    have hSub :
        countIf (fun x => decide (x ≠ r) &&
          decide (add (add c0 (mul c1 x)) (mul c2 (mul x x)) = zero)) ys ≤
        countIf (fun x => decide (add (add c1 (mul c2 r)) (mul c2 x) = zero)) ys := by
      refine countIf_mono_on_mem (fun x _ hConj => ?_)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hConj
      have hr0 := of_decide_eq_true hr
      have hFact : mul (sub x r) (add (add c1 (mul c2 r)) (mul c2 x)) = zero := by
        have hId : mul (sub x r) (add (add c1 (mul c2 r)) (mul c2 x)) =
            sub (add (add c0 (mul c1 x)) (mul c2 (mul x x)))
                (add (add c0 (mul c1 r)) (mul c2 (mul r r))) := by
          constructive_ring
        rw [hId, hConj.2, hr0, LawfulCommRing.sub_self]
      rcases field_mul_eq_zero_or hFact with hxr0 | hLin0
      · exact absurd (LawfulCommRing.sub_eq_zero_iff.mp hxr0) hConj.1
      · exact decide_eq_true hLin0
    exact Nat.le_trans hSub (linear_roots_countIf_le_one (add c1 (mul c2 r)) c2 hc2 hndY)

/-- **Constructive Nonzero Cubic Root Bound (`cubic_roots_countIf_le_three`)**:
    Over any `[LawfulField K]`, a cubic `c0 + c1·x + c2·x² + c3·x³` with `(c1, c2, c3) ≠ (0, 0, 0)`
    vanishes on **at most `3` elements** of any duplicate-free list `xs : List K`. -/
theorem cubic_roots_countIf_le_three {K : Type} [LawfulField K] [DecidableEq K]
    (c0 c1 c2 c3 : K) (hNz : c1 ≠ zero ∨ c2 ≠ zero ∨ c3 ≠ zero)
    {xs : List K} (hnd : xs.Nodup) :
    countIf (fun x => decide (evalCubic c0 c1 c2 c3 x = zero)) xs ≤ 3 := by
  if hc3 : c3 = zero then
    have hNz2 : c1 ≠ zero ∨ c2 ≠ zero := by
      rcases hNz with h1 | h2 | h3
      · exact Or.inl h1
      · exact Or.inr h2
      · exact absurd hc3 h3
    have hLe : countIf (fun x => decide (evalCubic c0 c1 c2 c3 x = zero)) xs ≤
        countIf (fun x => decide (add (add c0 (mul c1 x)) (mul c2 (mul x x)) = zero)) xs := by
      refine countIf_mono_on_mem (fun x _ hx => ?_)
      have hx0 := of_decide_eq_true hx
      unfold evalCubic at hx0
      rw [hc3, LawfulCommRing.zero_mul, LawfulCommRing.add_zero] at hx0
      exact decide_eq_true hx0
    exact Nat.le_trans hLe (Nat.le_succ_of_le (quad_roots_countIf_le_two c0 c1 c2 hNz2 hnd))
  else
    refine countIf_step_le 2 (fun r hr {ys} hndY => ?_) hnd
    let q0 := add (add c1 (mul c2 r)) (mul c3 (mul r r))
    let q1 := add c2 (mul c3 r)
    have hSub :
        countIf (fun x => decide (x ≠ r) && decide (evalCubic c0 c1 c2 c3 x = zero)) ys ≤
        countIf (fun x => decide (add (add q0 (mul q1 x)) (mul c3 (mul x x)) = zero)) ys := by
      refine countIf_mono_on_mem (fun x _ hConj => ?_)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hConj
      have hr0 := of_decide_eq_true hr
      have hFact : mul (sub x r) (add (add q0 (mul q1 x)) (mul c3 (mul x x))) = zero := by
        have hId : mul (sub x r) (add (add q0 (mul q1 x)) (mul c3 (mul x x))) =
            sub (evalCubic c0 c1 c2 c3 x) (evalCubic c0 c1 c2 c3 r) := by
          dsimp only [q0, q1, evalCubic]
          constructive_ring
        rw [hId, hConj.2, hr0, LawfulCommRing.sub_self]
      rcases field_mul_eq_zero_or hFact with hxr0 | hQuad0
      · exact absurd (LawfulCommRing.sub_eq_zero_iff.mp hxr0) hConj.1
      · exact decide_eq_true hQuad0
    exact Nat.le_trans hSub (quad_roots_countIf_le_two q0 q1 c3 (Or.inr hc3) hndY)

private theorem nodup_map_of_injective {α β : Type} {f : α → β}
    (hInj : ∀ x y, f x = f y → x = y) :
    ∀ {xs : List α}, xs.Nodup → (xs.map f).Nodup
  | [], _ => List.nodup_nil
  | x :: xs, hnd => by
    have hc := List.nodup_cons.mp hnd
    refine List.nodup_cons.mpr ⟨fun hm => ?_, nodup_map_of_injective hInj hc.2⟩
    obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hm
    exact hc.1 (hInj x y hfy.symm ▸ hy)

/-- Exact two-challenge product-space count for any `Config C X` with `cfg.reps = 2`. -/
theorem frozenWins_two_reps_count_eq {C X : Type} (cfg : Config C X) (h2 : cfg.reps = 2)
    (A : Adversary C X) (xs : List X) :
    countIf (frozenWins cfg A) (vectors xs 2) =
      countIf (cfg.check (A.commit []) 0) xs * countIf (cfg.check (A.commit []) 1) xs := by
  let p0 := cfg.check (A.commit []) 0
  let p1 := cfg.check (A.commit []) 1
  have hCongr : countIf (frozenWins cfg A) (vectors xs 2) =
      countIf (fun v => allReps (cfg.check (A.commit [])) 0 v) (vectors xs 2) := by
    apply countIf_vectors_congr
    intro v hv
    cases hAll : allReps (cfg.check (A.commit [])) 0 v with
    | false =>
      rw [frozenWins_eq, hAll, Bool.and_false]
    | true =>
      exact frozenWins_of_allReps cfg A v (by omega) (hv.trans h2.symm) hAll
  rw [hCongr]
  show countIf (fun v => allReps (cfg.check (A.commit [])) 0 v) (extendAll xs (extendAll xs [[]])) =
    countIf p0 xs * countIf p1 xs
  rw [countIf_extendAll]
  have hInner : (fun x0 => countIf (fun v1 => allReps (cfg.check (A.commit [])) 0 (x0 :: v1))
        (extendAll xs [[]])) =
      (fun x0 => if p0 x0 then countIf p1 xs else 0) := by
    funext x0
    rw [countIf_extendAll]
    have hLeaf : (fun x1 => countIf (fun v2 => allReps (cfg.check (A.commit [])) 0 (x0 :: x1 :: v2)) [[]]) =
        (fun x1 => if p0 x0 && p1 x1 then 1 else 0) := by
      funext x1
      show (if allReps (cfg.check (A.commit [])) 0 [x0, x1] then 1 else 0) + 0 =
        if p0 x0 && p1 x1 then 1 else 0
      rw [allReps_cons, allReps_cons, allReps_nil, Bool.and_true, Nat.add_zero]
    rw [hLeaf]
    cases hp0 : p0 x0 with
    | false =>
      simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      rw [sumOver_const, Nat.mul_zero]
    | true =>
      simp only [Bool.true_and, ↓reduceIte]
      rw [sumOver_ite_const, Nat.mul_one]
  rw [hInner, sumOver_ite_const]

/-- Reconstructed FTS DKG power-triple `(s, s2, s3)` with sacrificial pair `(u, w)` (`w ≈ u·s`)
    and Frobenius squaring mask pair `(r, r2)` (`r2 ≈ r²`). -/
structure FtsPowerTriple (K : Type) where
  s : K
  s2 : K
  s3 : K
  u : K
  w : K
  r : K
  r2 : K

/-- Sacrificial cubic product check (`j = 0`, challenge `chi`):
    opens `rho = chi · s2 + u` and checks `chi · s3 + w + rho · s = 0`. -/
def ftsTripleProdResidual {K : Type} [LawfulCommRing K] (T : FtsPowerTriple K) (chi : K) : K :=
  let rho := add (mul chi T.s2) T.u
  sub (add (mul chi T.s3) T.w) (mul rho T.s)

/-- Frobenius squaring check (`j = 1`, challenge `theta`):
    opens `sqOpen = r + theta · s` and checks `(sqOpen)² = r2 + theta² · s2`. -/
def ftsTripleFrobResidual {K : Type} [LawfulCommRing K] (T : FtsPowerTriple K) (theta : K) : K :=
  let sqOpen := add T.r (mul theta T.s)
  sub (mul sqOpen sqOpen) (add T.r2 (mul (mul theta theta) T.s2))

def ftsTripleCheck {K : Type} [LawfulCommRing K] [DecidableEq K]
    (T : FtsPowerTriple K) : Nat → K → Bool
  | 0, chi => decide (ftsTripleProdResidual T chi = zero)
  | _, theta => decide (ftsTripleFrobResidual T theta = zero)

/-- Two-challenge (`[chi, theta]`) `FrozenChallenge` configuration for `FtsPowerTriple`. -/
def ftsTripleConfig {K : Type} [LawfulCommRing K] [DecidableEq K] : Config (FtsPowerTriple K) K :=
  ⟨2, ftsTripleCheck⟩

def FtsTripleHonest {K : Type} [LawfulCommRing K] (T : FtsPowerTriple K) : Prop :=
  T.s2 = mul T.s T.s ∧
  T.s3 = mul T.s2 T.s ∧
  T.w = mul T.u T.s ∧
  T.r2 = mul T.r T.r

def FtsTripleCheats {K : Type} [LawfulCommRing K] (T : FtsPowerTriple K) : Prop :=
  T.s2 ≠ mul T.s T.s ∨ T.s3 ≠ mul (mul T.s T.s) T.s

theorem ftsTripleProdResidual_eq {K : Type} [LawfulCommRing K] (T : FtsPowerTriple K) (chi : K) :
    ftsTripleProdResidual T chi =
      add (sub T.w (mul T.u T.s)) (mul chi (sub T.s3 (mul T.s2 T.s))) := by
  unfold ftsTripleProdResidual
  dsimp only
  constructive_ring

theorem ftsTripleFrobResidual_char2_eq {K : Type} [LawfulCommRing K]
    (hChar2 : ∀ x : K, add x x = zero) (T : FtsPowerTriple K) (theta : K) :
    ftsTripleFrobResidual T theta =
      add (sub (mul T.r T.r) T.r2)
          (mul (mul theta theta) (sub (mul T.s T.s) T.s2)) := by
  unfold ftsTripleFrobResidual
  dsimp only
  rw [frobenius_sq_add_char2 hChar2]
  have hSqMul : mul (mul theta T.s) (mul theta T.s) = mul (mul theta theta) (mul T.s T.s) := by
    constructive_ring
  rw [hSqMul]
  constructive_ring

/-- **Dealerless FTS `(s, s², s³)` + Frobenius Completeness (`ftsPowerTriple_honest_complete`)**:
    In characteristic 2, any honest power triple `(s, s², s³)` with `w = u · s` and local square
    mask `r2 = r²` passes **every** challenge pair `[chi, theta]`. -/
theorem ftsPowerTriple_honest_complete {K : Type} [LawfulField K] [DecidableEq K]
    (hChar2 : ∀ x : K, add x x = zero)
    (A : Adversary (FtsPowerTriple K) K) (hH : FtsTripleHonest (A.commit []))
    (chi theta : K) :
    frozenWins ftsTripleConfig A [chi, theta] = true := by
  rcases hH with ⟨hs2, hs3, hw, hr2⟩
  refine frozenWins_of_allReps ftsTripleConfig A [chi, theta] (show 1 ≤ 2 by decide) rfl ?_
  rw [allReps_cons, allReps_cons, allReps_nil]
  dsimp only [ftsTripleConfig]
  have hp0 : ftsTripleCheck (A.commit []) 0 chi = true := by
    unfold ftsTripleCheck
    apply decide_eq_true
    rw [ftsTripleProdResidual_eq, hw, hs3, LawfulCommRing.sub_self,
        LawfulCommRing.sub_self, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  have hp1 : ftsTripleCheck (A.commit []) 1 theta = true := by
    unfold ftsTripleCheck
    apply decide_eq_true
    rw [ftsTripleFrobResidual_char2_eq hChar2, hr2, hs2, LawfulCommRing.sub_self,
        LawfulCommRing.sub_self, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  rw [hp0, hp1]
  rfl

/-- **Dealerless FTS `(s, s², s³)` + Frobenius Freeze-Before-Sample Soundness
    (`ftsPowerTriple_frozen_soundness`)**:
    Over ANY characteristic-2 `[LawfulField K]` and duplicate-free challenge list `xs : List K`,
    if a frozen tuple violates `s2 = s²` OR `s3 = s³` (even if `r2 ≠ r²` and `w ≠ u · s`),
    it is accepted on **at most `xs.length` out of `xs.length ^ 2`** challenge pairs `[chi, theta]`
    (cheat probability `≤ 1 / |K|`: `≤ 2^-128` over `Tower128`/`Gf2Pow128`, `≤ 2^-8` over `Tower8`). -/
theorem ftsPowerTriple_frozen_soundness {K : Type} [LawfulField K] [DecidableEq K]
    (hChar2 : ∀ x : K, add x x = zero)
    (A : Adversary (FtsPowerTriple K) K) (xs : List K) (hnd : xs.Nodup)
    (hCheat : FtsTripleCheats (A.commit [])) :
    countIf (frozenWins ftsTripleConfig A) (vectors xs 2) ≤ xs.length ∧
      (vectors xs 2).length = xs.length ^ 2 := by
  refine ⟨?_, length_vectors xs 2⟩
  rw [frozenWins_two_reps_count_eq ftsTripleConfig rfl A xs]
  let T := A.commit []
  if hs2Eq : T.s2 = mul T.s T.s then
    have hs3Ne : T.s3 ≠ mul T.s2 T.s := by
      intro hEq
      rcases hCheat with hBad2 | hBad3
      · exact hBad2 hs2Eq
      · apply hBad3
        rw [← hs2Eq]
        exact hEq
    have hDelta3Nz : sub T.s3 (mul T.s2 T.s) ≠ zero :=
      fun hz => hs3Ne (LawfulCommRing.sub_eq_zero_iff.mp hz)
    have hProdLe1 : countIf (ftsTripleCheck T 0) xs ≤ 1 := by
      have hCongr : countIf (ftsTripleCheck T 0) xs ≤
          countIf (fun chi => decide (add (sub T.w (mul T.u T.s))
            (mul (sub T.s3 (mul T.s2 T.s)) chi) = zero)) xs := by
        refine countIf_mono_on_mem (fun chi _ h => ?_)
        have h0 := of_decide_eq_true h
        rw [ftsTripleProdResidual_eq, LawfulCommRing.mul_comm chi] at h0
        exact decide_eq_true h0
      exact Nat.le_trans hCongr (linear_roots_countIf_le_one _ _ hDelta3Nz hnd)
    have hFrobLeLen : countIf (ftsTripleCheck T 1) xs ≤ xs.length := countIf_le_length _ xs
    calc countIf (ftsTripleCheck T 0) xs * countIf (ftsTripleCheck T 1) xs
        ≤ 1 * xs.length := Nat.mul_le_mul hProdLe1 hFrobLeLen
      _ = xs.length := Nat.one_mul _
  else
    have hDelta2Nz : sub (mul T.s T.s) T.s2 ≠ zero :=
      fun hz => hs2Eq (LawfulCommRing.sub_eq_zero_iff.mp hz).symm
    have hSqNd : (xs.map (fun t => mul t t)).Nodup :=
      nodup_map_of_injective (fun _ _ => frobenius_sq_injective_char2 hChar2) hnd
    have hFrobLe1 : countIf (ftsTripleCheck T 1) xs ≤ 1 := by
      have hLeMap : countIf (ftsTripleCheck T 1) xs ≤
          countIf (fun y => decide (add (sub (mul T.r T.r) T.r2)
            (mul (sub (mul T.s T.s) T.s2) y) = zero)) (xs.map (fun t => mul t t)) := by
        rw [countIf_map]
        refine countIf_mono_on_mem (fun theta _ h => ?_)
        have h0 := of_decide_eq_true h
        rw [ftsTripleFrobResidual_char2_eq hChar2,
            LawfulCommRing.mul_comm (mul theta theta)] at h0
        exact decide_eq_true h0
      exact Nat.le_trans hLeMap (linear_roots_countIf_le_one _ _ hDelta2Nz hSqNd)
    have hProdLeLen : countIf (ftsTripleCheck T 0) xs ≤ xs.length := countIf_le_length _ xs
    calc countIf (ftsTripleCheck T 0) xs * countIf (ftsTripleCheck T 1) xs
        ≤ xs.length * 1 := Nat.mul_le_mul hProdLeLen hFrobLe1
      _ = xs.length := Nat.mul_one _

/-- **`#tooth` (`tooth_ftsPowerTriple_swapped_order_always_accepted`)**:
    If `[chi, theta]` are revealed BEFORE freezing `FtsPowerTriple`, an adversary sets
    `s = 0, s2 = 1, s3 = 0, r = 0, r2 = theta², u = 0, w = 0`, violating `s2 = s²` (`1 ≠ 0`)
    while passing **100% of all `xs.length ^ 2`** challenge pairs! -/
theorem tooth_ftsPowerTriple_swapped_order_always_accepted {K : Type}
    [LawfulField K] [DecidableEq K] (hChar2 : ∀ x : K, add x x = zero) (xs : List K) :
    ∃ A : Adversary (FtsPowerTriple K) K,
      (∀ chis, FtsTripleCheats (A.commit chis)) ∧
      countIf (swappedWins ftsTripleConfig A) (vectors xs 2) = xs.length ^ 2 := by
  let fit : List K → FtsPowerTriple K := fun chis =>
    let theta := chis.getD 1 zero
    { s := zero, s2 := one, s3 := zero, u := zero, w := zero, r := zero, r2 := mul theta theta }
  refine ⟨⟨fit⟩, fun chis => Or.inl ?_, ?_⟩
  · show (one : K) ≠ mul zero zero
    rw [LawfulCommRing.zero_mul]
    exact LawfulField.one_ne_zero
  · refine swapped_win_count_all ftsTripleConfig ⟨fit⟩ xs (show 1 ≤ 2 by decide) ?_
    intro chis hLen
    match chis, hLen with
    | [chi, theta], _ =>
      rw [allReps_cons, allReps_cons, allReps_nil]
      dsimp only [ftsTripleConfig]
      have hp0 : ftsTripleCheck (fit [chi, theta]) 0 chi = true := by
        unfold ftsTripleCheck
        apply decide_eq_true
        rw [ftsTripleProdResidual_eq]
        dsimp only [fit]
        rw [LawfulCommRing.mul_zero, LawfulCommRing.sub_self, LawfulCommRing.mul_zero,
            LawfulCommRing.sub_self, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
      have hp1 : ftsTripleCheck (fit [chi, theta]) 1 theta = true := by
        unfold ftsTripleCheck
        apply decide_eq_true
        rw [ftsTripleFrobResidual_char2_eq hChar2]
        dsimp only [fit]
        show add (sub (mul zero zero) (mul theta theta))
          (mul (mul theta theta) (sub (mul zero zero) one)) = zero
        rw [LawfulCommRing.zero_mul, char2_sub_eq_add hChar2, char2_sub_eq_add hChar2,
            LawfulCommRing.zero_add, LawfulCommRing.zero_add, LawfulCommRing.mul_one,
            hChar2 (mul theta theta)]
      rw [hp0, hp1]
      rfl

/-- Full 7-power tuple `(p1, p2, p3, p4, p5, p6, p7)` representing `(a, a², ..., a⁷)` in
    `crates/qsag-fts/src/dkg.rs:1078-1153, 1372-1379, 1483-1496`, paired with sacrificial
    pair `(u, w)` (`w ≈ u · a`) and Frobenius square mask `(r, r2)` (`r2 ≈ r²`). -/
structure FtsPower7Tuple (K : Type) where
  p1 : K
  p2 : K
  p3 : K
  p4 : K
  p5 : K
  p6 : K
  p7 : K
  u : K
  w : K
  r : K
  r2 : K

/-- `PowerChallenge::combine([s, s², s³], [x, y, z]) = s·x + s²·y + s³·z` (`dkg.rs:1135-1143`). -/
def ftsCombinePosDeg {K : Type} [LawfulCommRing K] (s x y z : K) : K :=
  let s2 := mul s s
  let s3 := mul s2 s
  add (add (mul s x) (mul s2 y)) (mul s3 z)

/-- Sacrificial odd-power product check (`j = 0`, challenge `s`, `dkg.rs:1376, 1490-1492`):
    `rho = s·p2 + s²·p4 + s³·p6 + u`, checked against `s·p3 + s²·p5 + s³·p7 + w + rho·p1 = 0`. -/
def ftsPower7ProdResidual {K : Type} [LawfulCommRing K] (T : FtsPower7Tuple K) (s : K) : K :=
  let rho := add (ftsCombinePosDeg s T.p2 T.p4 T.p6) T.u
  sub (add (ftsCombinePosDeg s T.p3 T.p5 T.p7) T.w) (mul rho T.p1)

/-- Batched Frobenius squaring check (`j = 1`, challenge `theta`, `dkg.rs:1378, 1494-1495`):
    `sqOpen = r + θ·p1 + θ²·p2 + θ³·p3`, checked against
    `(sqOpen)² = r2 + θ²·p2 + θ⁴·p4 + θ⁶·p6`. -/
def ftsPower7FrobResidual {K : Type} [LawfulCommRing K] (T : FtsPower7Tuple K) (theta : K) : K :=
  let sqOpen := add T.r (ftsCombinePosDeg theta T.p1 T.p2 T.p3)
  sub (mul sqOpen sqOpen) (add T.r2 (ftsCombinePosDeg (mul theta theta) T.p2 T.p4 T.p6))

def ftsPower7Check {K : Type} [LawfulCommRing K] [DecidableEq K]
    (T : FtsPower7Tuple K) : Nat → K → Bool
  | 0, s => decide (ftsPower7ProdResidual T s = zero)
  | _, theta => decide (ftsPower7FrobResidual T theta = zero)

def ftsPower7Config {K : Type} [LawfulCommRing K] [DecidableEq K] : Config (FtsPower7Tuple K) K :=
  ⟨2, ftsPower7Check⟩

def FtsPower7ValidPowers {K : Type} [LawfulCommRing K] (T : FtsPower7Tuple K) : Prop :=
  T.p2 = mul T.p1 T.p1 ∧
  T.p3 = mul T.p2 T.p1 ∧
  T.p4 = mul T.p2 T.p2 ∧
  T.p5 = mul T.p4 T.p1 ∧
  T.p6 = mul T.p3 T.p3 ∧
  T.p7 = mul T.p6 T.p1

def FtsPower7Honest {K : Type} [LawfulCommRing K] (T : FtsPower7Tuple K) : Prop :=
  FtsPower7ValidPowers T ∧ T.w = mul T.u T.p1 ∧ T.r2 = mul T.r T.r

theorem ftsPower7ProdResidual_eq_cubic {K : Type} [LawfulCommRing K]
    (T : FtsPower7Tuple K) (s : K) :
    ftsPower7ProdResidual T s =
      evalCubic
        (sub T.w (mul T.u T.p1))
        (sub T.p3 (mul T.p2 T.p1))
        (sub T.p5 (mul T.p4 T.p1))
        (sub T.p7 (mul T.p6 T.p1))
        s := by
  unfold ftsPower7ProdResidual ftsCombinePosDeg evalCubic
  dsimp only
  constructive_ring

theorem ftsPower7FrobResidual_char2_eq_cubic_sq {K : Type} [LawfulCommRing K]
    (hChar2 : ∀ x : K, add x x = zero) (T : FtsPower7Tuple K) (theta : K) :
    ftsPower7FrobResidual T theta =
      evalCubic
        (sub (mul T.r T.r) T.r2)
        (sub (mul T.p1 T.p1) T.p2)
        (sub (mul T.p2 T.p2) T.p4)
        (sub (mul T.p3 T.p3) T.p6)
        (mul theta theta) := by
  unfold ftsPower7FrobResidual ftsCombinePosDeg evalCubic
  dsimp only
  rw [frobenius_sq_add_char2 hChar2,
      frobenius_sq_add_char2 hChar2,
      frobenius_sq_add_char2 hChar2]
  constructive_ring

/-- **Dealerless FTS 7-Power `(a, ..., a⁷)` Completeness (`ftsPower7_honest_complete`)**:
    True power tuples pass **every** `[s, theta]` challenge pair in characteristic 2. -/
theorem ftsPower7_honest_complete {K : Type} [LawfulField K] [DecidableEq K]
    (hChar2 : ∀ x : K, add x x = zero)
    (A : Adversary (FtsPower7Tuple K) K) (hH : FtsPower7Honest (A.commit []))
    (s theta : K) :
    frozenWins ftsPower7Config A [s, theta] = true := by
  rcases hH with ⟨⟨hp2, hp3, hp4, hp5, hp6, hp7⟩, hw, hr2⟩
  refine frozenWins_of_allReps ftsPower7Config A [s, theta] (show 1 ≤ 2 by decide) rfl ?_
  rw [allReps_cons, allReps_cons, allReps_nil]
  dsimp only [ftsPower7Config]
  have hz0 : ftsPower7Check (A.commit []) 0 s = true := by
    unfold ftsPower7Check
    apply decide_eq_true
    rw [ftsPower7ProdResidual_eq_cubic, hw, hp3, hp5, hp7]
    unfold evalCubic
    simp only [LawfulCommRing.sub_self, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
  have hz1 : ftsPower7Check (A.commit []) 1 theta = true := by
    unfold ftsPower7Check
    apply decide_eq_true
    rw [ftsPower7FrobResidual_char2_eq_cubic_sq hChar2, hr2, ← hp4, ← hp2, ← hp6]
    unfold evalCubic
    simp only [LawfulCommRing.sub_self, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
  rw [hz0, hz1]
  rfl

/-- **Dealerless FTS 7-Power `(a, ..., a⁷)` Freeze-Before-Sample Soundness
    (`ftsPower7_frozen_soundness`, `dkg.rs`)**:
    Over any characteristic-2 `[LawfulField K]` and duplicate-free challenge list `xs : List K`,
    any frozen `FtsPower7Tuple` violating `FtsPower7ValidPowers` is accepted on **at most
    `3 * xs.length` out of `xs.length ^ 2`** challenge pairs (`≤ 3 / |K| < 2^-126` over `GF(2^128)`). -/
theorem ftsPower7_frozen_soundness {K : Type} [LawfulField K] [DecidableEq K]
    (hChar2 : ∀ x : K, add x x = zero)
    (A : Adversary (FtsPower7Tuple K) K) (xs : List K) (hnd : xs.Nodup)
    (hCheat : ¬ FtsPower7ValidPowers (A.commit [])) :
    countIf (frozenWins ftsPower7Config A) (vectors xs 2) ≤ 3 * xs.length ∧
      (vectors xs 2).length = xs.length ^ 2 := by
  refine ⟨?_, length_vectors xs 2⟩
  rw [frozenWins_two_reps_count_eq ftsPower7Config rfl A xs]
  let T := A.commit []
  if hEven : T.p2 = mul T.p1 T.p1 ∧ T.p4 = mul T.p2 T.p2 ∧ T.p6 = mul T.p3 T.p3 then
    have hOddNz :
        sub T.p3 (mul T.p2 T.p1) ≠ zero ∨
        sub T.p5 (mul T.p4 T.p1) ≠ zero ∨
        sub T.p7 (mul T.p6 T.p1) ≠ zero := by
      if h3 : sub T.p3 (mul T.p2 T.p1) = zero then
        if h5 : sub T.p5 (mul T.p4 T.p1) = zero then
          if h7 : sub T.p7 (mul T.p6 T.p1) = zero then
            exfalso
            exact hCheat ⟨hEven.1,
              LawfulCommRing.sub_eq_zero_iff.mp h3,
              hEven.2.1,
              LawfulCommRing.sub_eq_zero_iff.mp h5,
              hEven.2.2,
              LawfulCommRing.sub_eq_zero_iff.mp h7⟩
          else exact Or.inr (Or.inr h7)
        else exact Or.inr (Or.inl h5)
      else exact Or.inl h3
    have hProdLe3 : countIf (ftsPower7Check T 0) xs ≤ 3 := by
      have hCongr : countIf (ftsPower7Check T 0) xs ≤
          countIf (fun s => decide (evalCubic
            (sub T.w (mul T.u T.p1))
            (sub T.p3 (mul T.p2 T.p1))
            (sub T.p5 (mul T.p4 T.p1))
            (sub T.p7 (mul T.p6 T.p1)) s = zero)) xs := by
        refine countIf_mono_on_mem (fun s _ hs => ?_)
        have hs0 := of_decide_eq_true hs
        rw [ftsPower7ProdResidual_eq_cubic] at hs0
        exact decide_eq_true hs0
      exact Nat.le_trans hCongr (cubic_roots_countIf_le_three _ _ _ _ hOddNz hnd)
    exact Nat.mul_le_mul hProdLe3 (countIf_le_length _ xs)
  else
    have hEvenNz :
        sub (mul T.p1 T.p1) T.p2 ≠ zero ∨
        sub (mul T.p2 T.p2) T.p4 ≠ zero ∨
        sub (mul T.p3 T.p3) T.p6 ≠ zero := by
      if h2 : sub (mul T.p1 T.p1) T.p2 = zero then
        if h4 : sub (mul T.p2 T.p2) T.p4 = zero then
          if h6 : sub (mul T.p3 T.p3) T.p6 = zero then
            exfalso
            exact hEven ⟨(LawfulCommRing.sub_eq_zero_iff.mp h2).symm,
              (LawfulCommRing.sub_eq_zero_iff.mp h4).symm,
              (LawfulCommRing.sub_eq_zero_iff.mp h6).symm⟩
          else exact Or.inr (Or.inr h6)
        else exact Or.inr (Or.inl h4)
      else exact Or.inl h2
    have hSqNd : (xs.map (fun t => mul t t)).Nodup :=
      nodup_map_of_injective (fun _ _ => frobenius_sq_injective_char2 hChar2) hnd
    have hFrobLe3 : countIf (ftsPower7Check T 1) xs ≤ 3 := by
      have hLeMap : countIf (ftsPower7Check T 1) xs ≤
          countIf (fun y => decide (evalCubic
            (sub (mul T.r T.r) T.r2)
            (sub (mul T.p1 T.p1) T.p2)
            (sub (mul T.p2 T.p2) T.p4)
            (sub (mul T.p3 T.p3) T.p6) y = zero)) (xs.map (fun t => mul t t)) := by
        rw [countIf_map]
        refine countIf_mono_on_mem (fun theta _ ht => ?_)
        have ht0 := of_decide_eq_true ht
        rw [ftsPower7FrobResidual_char2_eq_cubic_sq hChar2] at ht0
        exact decide_eq_true ht0
      exact Nat.le_trans hLeMap (cubic_roots_countIf_le_three _ _ _ _ hEvenNz hSqNd)
    calc countIf (ftsPower7Check T 0) xs * countIf (ftsPower7Check T 1) xs
        ≤ xs.length * 3 := Nat.mul_le_mul (countIf_le_length _ xs) hFrobLe3
      _ = 3 * xs.length := Nat.mul_comm _ _

/-- Broken degree-0 product combiner `[1, s, s²]` (`1·x + s·y + s²·z`) violating `dkg.rs:1119`'s
    positive-degree requirement (`[s, s², s³]`). -/
def ftsBrokenDeg0ProdResidual {K : Type} [LawfulCommRing K] (T : FtsPower7Tuple K) (s : K) : K :=
  let comb2 (a b c : K) := add (add a (mul s b)) (mul (mul s s) c)
  let rho := add (comb2 T.p2 T.p4 T.p6) T.u
  sub (add (comb2 T.p3 T.p5 T.p7) T.w) (mul rho T.p1)

/-- **`#tooth` (`tooth_ftsPower7_degree0_weight_cancels_error`, `dkg.rs:1119`)**:
    If `PowerChallenge::products` started at weight `1` (`[1, s, s²]`) instead of `s` (`[s, s², s³]`),
    a **frozen** tuple with forged `p3 = 1 ≠ 0 = p1³` and compensating sacrificial error `w = 1`
    cancels the constant term and passes **every** challenge `s` and `theta`! -/
theorem tooth_ftsPower7_degree0_weight_cancels_error {K : Type}
    [LawfulField K] [DecidableEq K] (hChar2 : ∀ x : K, add x x = zero) :
    ∃ T : FtsPower7Tuple K,
      ¬ FtsPower7ValidPowers T ∧
      (∀ s : K, ftsBrokenDeg0ProdResidual T s = zero) ∧
      (∀ theta : K, ftsPower7Check T 1 theta = true) := by
  let T : FtsPower7Tuple K :=
    { p1 := zero, p2 := zero, p3 := one, p4 := zero, p5 := zero, p6 := one, p7 := zero,
      u := zero, w := one, r := zero, r2 := zero }
  refine ⟨T, ?_, ?_, ?_⟩
  · intro hV
    have hp3 : (one : K) = mul zero zero := hV.2.1
    rw [LawfulCommRing.zero_mul] at hp3
    exact LawfulField.one_ne_zero hp3
  · intro s
    unfold ftsBrokenDeg0ProdResidual
    dsimp only [T]
    rw [char2_sub_eq_add hChar2]
    have hSimp :
        add (add (add (add one (mul s zero)) (mul (mul s s) zero)) one)
            (mul (add (add (add zero (mul s zero)) (mul (mul s s) one)) zero) zero) =
        add one one := by
      constructive_ring
    rw [hSimp, hChar2 one]
  · intro theta
    unfold ftsPower7Check
    apply decide_eq_true
    rw [ftsPower7FrobResidual_char2_eq_cubic_sq hChar2]
    dsimp only [T]
    unfold evalCubic
    rw [LawfulCommRing.mul_zero, LawfulCommRing.mul_one, LawfulCommRing.sub_self,
        LawfulCommRing.sub_self, LawfulCommRing.zero_mul, LawfulCommRing.zero_mul,
        LawfulCommRing.zero_mul, LawfulCommRing.add_zero, LawfulCommRing.add_zero,
        LawfulCommRing.add_zero]

/-- Concrete `Tower8 = GF(2^8)` (`256` elements) and `Tower128 = GF(2^128)` instantiations of
    dealerless FTS `(s, s², s³)` + Frobenius freeze-before-sample soundness. -/
def tower8Elems : List Tower8 := enumBelow (fun n => unpackTower 3 (BitVec.ofNat 8 n)) 256

theorem tower8Elems_length : tower8Elems.length = 256 := length_enumBelow _ _

theorem tower8Elems_nodup : tower8Elems.Nodup := by
  apply enumBelow_nodup
  intro i j hi hj hEq
  have hPack := congrArg (packTower 3) hEq
  rw [packTower_unpackTower, packTower_unpackTower] at hPack
  have hToNat := congrArg BitVec.toNat hPack
  simp only [BitVec.toNat_ofNat] at hToNat
  rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hToNat

theorem ftsPowerTriple_tower8_frozen_soundness
    (A : Adversary (FtsPowerTriple Tower8) Tower8)
    (hCheat : FtsTripleCheats (A.commit [])) :
    countIf (frozenWins ftsTripleConfig A) (vectors tower8Elems 2) ≤ 256 ∧
      (vectors tower8Elems 2).length = 256 ^ 2 := by
  have h := ftsPowerTriple_frozen_soundness (towerElem_char2 3) A tower8Elems tower8Elems_nodup hCheat
  exact ⟨Nat.le_trans h.1 (Nat.le_of_eq tower8Elems_length),
         h.2.trans (by rw [tower8Elems_length])⟩

theorem ftsPowerTriple_gf2Pow128_frozen_soundness
    (A : Adversary (FtsPowerTriple Qsag.Math.Gf2Pow128) Qsag.Math.Gf2Pow128)
    (xs : List Qsag.Math.Gf2Pow128) (hnd : xs.Nodup)
    (hCheat : FtsTripleCheats (A.commit [])) :
    countIf (frozenWins ftsTripleConfig A) (vectors xs 2) ≤ xs.length ∧
      (vectors xs 2).length = xs.length ^ 2 :=
  ftsPowerTriple_frozen_soundness gf2Pow128_char2 A xs hnd hCheat

theorem inhabited_ftsPowerTriple_frozen_soundness :
    ∃ (A : Adversary (FtsPowerTriple Tower8) Tower8),
      FtsTripleCheats (A.commit []) :=
  ⟨⟨fun _ => { s := towerZero 3, s2 := towerOne 3, s3 := towerZero 3,
               u := towerZero 3, w := towerZero 3, r := towerZero 3, r2 := towerZero 3 }⟩,
   Or.inl (fun h => by
     have hz : mul (towerZero 3) (towerZero 3) = towerZero 3 := LawfulCommRing.zero_mul _
     exact towerZero_ne_towerOne 3 (hz.symm.trans h.symm))⟩

theorem inhabited_ftsPower7_frozen_soundness :
    ∃ (A : Adversary (FtsPower7Tuple Tower128) Tower128) (xs : List Tower128),
      (∀ x : Tower128, add x x = zero) ∧
      xs.Nodup ∧ ¬ FtsPower7ValidPowers (A.commit []) :=
  ⟨⟨fun _ => { p1 := towerZero 7, p2 := towerOne 7, p3 := towerZero 7, p4 := towerZero 7,
               p5 := towerZero 7, p6 := towerZero 7, p7 := towerZero 7,
               u := towerZero 7, w := towerZero 7, r := towerZero 7, r2 := towerZero 7 }⟩,
   [towerZero 7, towerOne 7],
   towerElem_char2 7,
   .cons (fun x hx heq => by
     subst heq
     exact towerZero_ne_towerOne 7 (List.mem_singleton.mp hx))
     (.cons (fun _ h => nomatch h) .nil),
   fun hV => by
     have hz : mul (towerZero 7) (towerZero 7) = towerZero 7 := LawfulCommRing.zero_mul _
     exact towerZero_ne_towerOne 7 (hz.symm.trans hV.1.symm)⟩

end FtsFrobenius

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
#verify_constructive frobenius_sq_add_char2
#verify_constructive frobenius_sum_shares_eq_sum_squares
#verify_constructive frobenius_sq_injective_char2
#verify_constructive cubic_roots_countIf_le_three
#verify_constructive ftsPowerTriple_honest_complete
#verify_constructive ftsPowerTriple_frozen_soundness
#verify_constructive tooth_ftsPowerTriple_swapped_order_always_accepted
#verify_constructive ftsPower7_honest_complete
#verify_constructive ftsPower7_frozen_soundness
#verify_constructive tooth_ftsPower7_degree0_weight_cancels_error
#verify_constructive ftsPowerTriple_tower8_frozen_soundness
#verify_constructive ftsPowerTriple_gf2Pow128_frozen_soundness

#verify_inhabited sacrifice_frozen_soundness inhabited_sacrifice_frozen_soundness
#verify_inhabited mldsa_sacrifice_frozen_soundness inhabited_mldsa_sacrifice_frozen_soundness
#verify_inhabited sacrifice_grinding_soundness inhabited_sacrifice_grinding_soundness
#verify_inhabited sacrifice_honest_complete inhabited_sacrifice_honest_complete
#verify_inhabited ftsPowerTriple_tower8_frozen_soundness inhabited_ftsPowerTriple_frozen_soundness
#verify_inhabited ftsPower7_frozen_soundness inhabited_ftsPower7_frozen_soundness

#tooth_pair sacrifice_frozen_soundness vs tooth_swapped_order_cheat_always_accepted
#tooth_pair sacrifice_frozen_soundness vs sacrifice_frozen_cheat_attains_one
#tooth_pair mldsa_sacrifice_frozen_soundness vs tooth_mldsa_swapped_order_cheat_always_accepted
#tooth_pair sacrifice_grinding_soundness vs tooth_swapped_order_cheat_always_accepted
#tooth_pair sacrifice_honest_complete vs sacrifice_zero_reps_never_accepts
#tooth_pair ftsPowerTriple_frozen_soundness vs tooth_ftsPowerTriple_swapped_order_always_accepted
#tooth_pair ftsPower7_frozen_soundness vs tooth_ftsPower7_degree0_weight_cancels_error

end Qsag.SacrificeFreeze
