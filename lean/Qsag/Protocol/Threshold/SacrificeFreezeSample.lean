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
step in `Qsag.ThresholdMlDsaSecurity`.
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

theorem gateError_eq (g : Gate F) : gateError g = sub g.z (mul g.x g.y) := by
  unfold gateError; rfl

theorem tripleError_eq (g : Gate F) (j : Nat) :
    tripleError g j = sub (g.c j) (mul (g.a j) (g.b j)) := by
  unfold tripleError; rfl

theorem gatePasses_eq [DecidableEq F] (g : Gate F) (j : Nat) (chi : F) :
    gatePasses g j chi = decide (openTau g j chi = zero) := by
  unfold gatePasses; rfl

theorem transcriptPasses_eq [DecidableEq F] (T : List (Gate F)) (j : Nat) (chi : F) :
    transcriptPasses T j chi = T.all (fun g => gatePasses g j chi) := by
  unfold transcriptPasses; rfl

theorem sacConfig_reps [DecidableEq F] (reps : Nat) :
    (sacConfig (F := F) reps).reps = reps := by
  unfold sacConfig; rfl

theorem sacConfig_check [DecidableEq F] (reps : Nat) :
    (sacConfig (F := F) reps).check = transcriptPasses (F := F) := by
  unfold sacConfig; rfl

theorem cheats_iff (T : List (Gate F)) :
    Cheats T ↔ ∃ g ∈ T, gateError g ≠ zero := by
  unfold Cheats; exact Iff.rfl

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

/-! ## Frobenius identities and polynomial root counts in characteristic two -/

section Frobenius

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

/-- Local share-squaring linearity in characteristic 2: `(∑_i s_i)^2 = ∑_i (s_i^2)`, so squaring additive shares locally gives shares of the square. -/
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

end Frobenius

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
