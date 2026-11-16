module
/-
# Qsag.Protocol.Credentials.RepetitionCutAndChoose — `N`-party, `τ`-repetition cut-and-choose

The selective-disclosure presentation of `crates/qsag-cred/src/blind_vc.rs` runs `τ`
repetitions (`sd_repetitions`: 17 or 33) of an `N = 256` party MPC-in-the-head check
(`VC_SD_LIMBO_PARTIES`) over `GF(p^5)`, `p` the Goldilocks prime. Its transcript order is

    round-1 commitments  →  folding weights γ  →  masked polynomial R̃
      →  evaluation point r ≠ 0  →  online broadcasts  →  hidden party h.

This module counts, for that order and any prover strategy, the challenge triples
`(γ⃗, r⃗, h⃗)` on which a commitment to a false statement is accepted.

The per-repetition verifier is a parameter (`Checker`), and so is the statement that it is
sound (`Checker.Sound`, the role `hEach` plays in `BlindVcQromSecurity.lean`):

* `fold`: at most `dG` folding challenges of a repetition are bad;
* `eval`: after a good folding challenge, and for every second message, at most `dR`
  evaluation points are bad;
* `open_`: after a good folding challenge and a good evaluation point, and for every second
  and third message, at most one hidden party is accepted.

Section 5 instantiates the opening condition with the hidden-party check of
`Qsag.Protocol.Credentials.AdvancedMpcAndCreds` (`credentialGgmCheckDefects`): for a verifier
whose last round tests the per-party check values of the repetition, `open_` follows from the
existence of one nonzero check value (`DefectChecker.sound_of_algebraic`). What stays a
hypothesis (`DefectChecker.AlgebraicSound`) is the algebra of `blind_vc.rs`: at most `dG`
folding challenges and at most `dR` evaluation points are bad, and after good challenges some
party's check value is nonzero. Nothing in this file derives those three from the Poseidon2
circuit, the commitments or the polynomial identity (witness-defect extraction).

Given `Checker.Sound`:

* `cut_and_choose_win_count_le`: the prover's second message may depend on all folding
  challenges and its third on all folding challenges and evaluation points; the number of
  accepted triples is at most `(dG·|R|·N + |G|·(dR·N + |R|)) ^ τ` out of `(|G|·|R|·N) ^ τ`,
  that is `(1/N + dR/|R| + dG/|G|) ^ τ`.
* `limbo256_tau33_soundness`, `limbo256_tau17_soundness`: with `N = 256`, evaluation points
  the `p^5 − 1` nonzero field elements, `dR = 384` (twice `SD_GRID_B`) and
  `dG / |G| ≤ 2^-300`, the accepted fraction is below `2^-263` for `τ = 33` and below `2^-135`
  for `τ = 17`. The comment at `blind_vc.rs:70` gives `2^-264` and `2^-136`, which is the term
  `(1/256)^τ` alone; `tooth_guessing_prover_attains_one_in_N` shows that term is reached.
* `winCount_zero_reps`: with no repetition nothing is accepted.

What the counts are not. They are for the interactive protocol with independent uniform
challenges per repetition. The code derives all challenges by Fiat–Shamir from one transcript,
expands the `τ` folding weights and the `τ` evaluation points from one 32-byte seed each, and
its prover may restart after seeing a challenge; a bound for that non-interactive protocol
needs a random-oracle argument over all three rounds and is not proved here. No quantum
adversary is modelled: halving the exponent for Grover search, as the Rust comment does, is a
heuristic and not a theorem of this file.
-/
public import Qsag.Oracle.FrozenChallengeGame
public import Qsag.Math.Primality
public import Qsag.Protocol.Credentials.AdvancedMpcAndCreds

public section
namespace Qsag.CutAndChoose
open Qsag.FrozenChallenge
set_option autoImplicit false
set_option exponentiation.threshold 512

/-! ## 1. Sums and products along challenge vectors -/

theorem sumOver_vectors_le {α : Type} (xs : List α) :
    ∀ (t : Nat) (f g : List α → Nat), (∀ v, v.length = t → f v ≤ g v) →
      sumOver f (vectors xs t) ≤ sumOver g (vectors xs t)
  | 0, _, _, h => Nat.add_le_add (h [] rfl) (Nat.le_refl 0)
  | t + 1, f, g, h => by
    show sumOver f (extendAll xs (vectors xs t)) ≤ sumOver g (extendAll xs (vectors xs t))
    rw [sumOver_extendAll, sumOver_extendAll]
    exact sumOver_le (fun x => sumOver_vectors_le xs t _ _
      (fun v hv => h (x :: v) (by rw [List.length_cons, hv]))) xs

/-- Sum of `c` on the entries satisfying `p` and `d` on the others. -/
theorem sumOver_ite_le {α : Type} (p : α → Bool) (c d : Nat) (xs : List α) :
    sumOver (fun x => if p x then c else d) xs ≤ countIf p xs * c + xs.length * d := by
  have h : sumOver (fun x => if p x then c else d) xs ≤
      sumOver (fun x => (if p x then c else 0) + d) xs :=
    sumOver_le (fun x => by
      show (if p x then c else d) ≤ (if p x then c else 0) + d
      cases p x
      · show d ≤ 0 + d
        rw [Nat.zero_add]; exact Nat.le_refl d
      · exact Nat.le_add_right c d) xs
  rw [sumOver_add, sumOver_ite_const, sumOver_const] at h
  exact h

/-- Repetition `j, j+1, …` of a three-challenge check; false on vectors of unequal length. -/
def allZip {G R H : Type} (P : Nat → G → R → H → Bool) : Nat → List G → List R → List H → Bool
  | _, [], [], [] => true
  | j, g :: gs, r :: rs, h :: hs => P j g r h && allZip P (j + 1) gs rs hs
  | _, _, _, _ => false

def prodZip {G R : Type} (w : Nat → G → R → Nat) : Nat → List G → List R → Nat
  | _, [], [] => 1
  | j, g :: gs, r :: rs => w j g r * prodZip w (j + 1) gs rs
  | _, _, _ => 0

def prodOne {G : Type} (u : Nat → G → Nat) : Nat → List G → Nat
  | _, [] => 1
  | j, g :: gs => u j g * prodOne u (j + 1) gs

def prodRange (f : Nat → Nat) : Nat → Nat → Nat
  | _, 0 => 1
  | j, t + 1 => f j * prodRange f (j + 1) t

theorem countIf_allZip_vectors {G R H : Type} (P : Nat → G → R → H → Bool) (Hs : List H) :
    ∀ (t j : Nat) (gs : List G) (rs : List R), gs.length = t → rs.length = t →
      countIf (allZip P j gs rs) (vectors Hs t) =
        prodZip (fun j g r => countIf (P j g r) Hs) j gs rs
  | 0, _, [], [], _, _ => by rfl
  | 0, _, _ :: _, _, hg, _ => (Nat.succ_ne_zero _ hg).elim
  | 0, _, [], _ :: _, _, hr => (Nat.succ_ne_zero _ hr).elim
  | _ + 1, _, [], _, hg, _ => (Nat.succ_ne_zero _ hg.symm).elim
  | _ + 1, _, _ :: _, [], _, hr => (Nat.succ_ne_zero _ hr.symm).elim
  | t + 1, j, g :: gs, r :: rs, hg, hr => by
    show countIf (allZip P j (g :: gs) (r :: rs)) (extendAll Hs (vectors Hs t)) =
      countIf (P j g r) Hs * prodZip (fun j g r => countIf (P j g r) Hs) (j + 1) gs rs
    rw [countIf_extendAll]
    have e : (fun h => countIf (fun v => allZip P j (g :: gs) (r :: rs) (h :: v))
          (vectors Hs t)) =
        (fun h => if P j g r h then
          prodZip (fun j g r => countIf (P j g r) Hs) (j + 1) gs rs else 0) := by
      funext h
      show countIf (fun v => P j g r h && allZip P (j + 1) gs rs v) (vectors Hs t) = _
      rw [countIf_and_const, countIf_allZip_vectors P Hs t (j + 1) gs rs
        (Nat.succ.inj hg) (Nat.succ.inj hr)]
    rw [e, sumOver_ite_const]

theorem sumOver_prodZip_vectors {G R : Type} (w : Nat → G → R → Nat) (Rs : List R) :
    ∀ (t j : Nat) (gs : List G), gs.length = t →
      sumOver (prodZip w j gs) (vectors Rs t) = prodOne (fun j g => sumOver (w j g) Rs) j gs
  | 0, _, [], _ => by rfl
  | 0, _, _ :: _, hg => (Nat.succ_ne_zero _ hg).elim
  | _ + 1, _, [], hg => (Nat.succ_ne_zero _ hg.symm).elim
  | t + 1, j, g :: gs, hg => by
    show sumOver (prodZip w j (g :: gs)) (extendAll Rs (vectors Rs t)) =
      sumOver (w j g) Rs * prodOne (fun j g => sumOver (w j g) Rs) (j + 1) gs
    rw [sumOver_extendAll]
    have e : (fun r => sumOver (fun v => prodZip w j (g :: gs) (r :: v)) (vectors Rs t)) =
        (fun r => w j g r * prodOne (fun j g => sumOver (w j g) Rs) (j + 1) gs) := by
      funext r
      show sumOver (fun v => w j g r * prodZip w (j + 1) gs v) (vectors Rs t) = _
      rw [sumOver_mul_left, sumOver_prodZip_vectors w Rs t (j + 1) gs (Nat.succ.inj hg)]
    rw [e, sumOver_mul_right]

theorem sumOver_prodOne_vectors {G : Type} (u : Nat → G → Nat) (Gs : List G) :
    ∀ (t j : Nat),
      sumOver (prodOne u j) (vectors Gs t) = prodRange (fun j => sumOver (u j) Gs) j t
  | 0, _ => by rfl
  | t + 1, j => by
    show sumOver (prodOne u j) (extendAll Gs (vectors Gs t)) =
      sumOver (u j) Gs * prodRange (fun j => sumOver (u j) Gs) (j + 1) t
    rw [sumOver_extendAll]
    have e : (fun g => sumOver (fun v => prodOne u j (g :: v)) (vectors Gs t)) =
        (fun g => u j g * prodRange (fun j => sumOver (u j) Gs) (j + 1) t) := by
      funext g
      show sumOver (fun v => u j g * prodOne u (j + 1) v) (vectors Gs t) = _
      rw [sumOver_mul_left, sumOver_prodOne_vectors u Gs t (j + 1)]
    rw [e, sumOver_mul_right]

theorem prodZip_le {G R : Type} {w w' : Nat → G → R → Nat} (h : ∀ j g r, w j g r ≤ w' j g r) :
    ∀ (gs : List G) (rs : List R) (j : Nat), prodZip w j gs rs ≤ prodZip w' j gs rs
  | [], [], _ => Nat.le_refl 1
  | [], _ :: _, _ => Nat.le_refl 0
  | _ :: _, [], _ => Nat.le_refl 0
  | g :: gs, r :: rs, j => Nat.mul_le_mul (h j g r) (prodZip_le h gs rs (j + 1))

theorem prodOne_le {G : Type} {u u' : Nat → G → Nat} (h : ∀ j g, u j g ≤ u' j g) :
    ∀ (gs : List G) (j : Nat), prodOne u j gs ≤ prodOne u' j gs
  | [], _ => Nat.le_refl 1
  | g :: gs, j => Nat.mul_le_mul (h j g) (prodOne_le h gs (j + 1))

theorem prodRange_le_pow (f : Nat → Nat) (a : Nat) (h : ∀ j, f j ≤ a) :
    ∀ (t j : Nat), prodRange f j t ≤ a ^ t
  | 0, _ => Nat.le_refl 1
  | t + 1, j => by
    show f j * prodRange f (j + 1) t ≤ a ^ (t + 1)
    rw [Nat.pow_succ, Nat.mul_comm (a ^ t) a]
    exact Nat.mul_le_mul (h j) (prodRange_le_pow f a h t (j + 1))

/-! ## 2. The three-challenge protocol -/

/-- The per-repetition verifier, as three predicates. `C` is the round-1 commitment, `G` a
folding challenge, `B1` the prover's second message, `R` an evaluation point, `B2` the third
message and `H` a hidden-party index. -/
structure Checker (C G B1 R B2 H : Type) where
  /-- The folding challenge of repetition `j` hides the defect of the committed witness. -/
  foldBad : C → Nat → G → Bool
  /-- The evaluation point of repetition `j` is a root of the nonzero check polynomial. -/
  evalBad : C → Nat → G → B1 → R → Bool
  /-- Repetition `j` is accepted when the hidden party is `h`. -/
  openOk : C → Nat → G → B1 → R → B2 → H → Bool

/-- Soundness of the per-repetition verifier on commitment `c`. This is the hypothesis the
circuit-level analysis has to supply. -/
structure Checker.Sound {C G B1 R B2 H : Type} (K : Checker C G B1 R B2 H) (c : C)
    (Gs : List G) (Rs : List R) (Hs : List H) (dG dR : Nat) : Prop where
  fold : ∀ j, countIf (K.foldBad c j) Gs ≤ dG
  eval : ∀ j g b1, K.foldBad c j g = false → countIf (K.evalBad c j g b1) Rs ≤ dR
  open_ : ∀ j g b1 r b2, K.foldBad c j g = false → K.evalBad c j g b1 r = false →
    countIf (K.openOk c j g b1 r b2) Hs ≤ 1

/-- A prover strategy. Its types fix what each message may depend on: the commitment on
nothing, the second message on the folding challenges, the third on those and the evaluation
points, and no message on the hidden parties. -/
structure Prover (C G B1 R B2 : Type) where
  commit : C
  respond1 : List G → B1
  respond2 : List G → List R → B2

/-- The verifier's verdict on one challenge triple. It rejects unless there is at least one
repetition and all three challenge vectors have the configured length. -/
def accepts {C G B1 R B2 H : Type} (K : Checker C G B1 R B2 H) (reps : Nat)
    (P : Prover C G B1 R B2) (gs : List G) (rs : List R) (hs : List H) : Bool :=
  decide (1 ≤ reps ∧ gs.length = reps ∧ rs.length = reps) &&
    allZip (fun j g r h => K.openOk P.commit j g (P.respond1 gs) r (P.respond2 gs rs) h)
      0 gs rs hs

/-- Number of accepted challenge triples. -/
def winCount {C G B1 R B2 H : Type} (K : Checker C G B1 R B2 H) (reps : Nat)
    (P : Prover C G B1 R B2) (Gs : List G) (Rs : List R) (Hs : List H) : Nat :=
  sumOver (fun gs => sumOver (fun rs => countIf (accepts K reps P gs rs) (vectors Hs reps))
    (vectors Rs reps)) (vectors Gs reps)

/-- Number of challenge triples. -/
def challengeCount {G R H : Type} (reps : Nat) (Gs : List G) (Rs : List R) (Hs : List H) : Nat :=
  sumOver (fun _ => sumOver (fun _ => (vectors Hs reps).length) (vectors Rs reps))
    (vectors Gs reps)

theorem challengeCount_eq {G R H : Type} (reps : Nat) (Gs : List G) (Rs : List R)
    (Hs : List H) : challengeCount reps Gs Rs Hs = (Gs.length * Rs.length * Hs.length) ^ reps := by
  unfold challengeCount
  rw [sumOver_const, sumOver_const, length_vectors, length_vectors, length_vectors,
    Nat.mul_pow, Nat.mul_pow, Nat.mul_assoc]

theorem accepts_zero_reps {C G B1 R B2 H : Type} (K : Checker C G B1 R B2 H)
    (P : Prover C G B1 R B2) (gs : List G) (rs : List R) (hs : List H) :
    accepts K 0 P gs rs hs = false := by
  have hd : decide (1 ≤ 0 ∧ gs.length = 0 ∧ rs.length = 0) = false :=
    decide_eq_false (fun hc => Nat.not_succ_le_zero 0 hc.1)
  unfold accepts
  rw [hd]; rfl

/-- With no repetition configured, no challenge triple is accepted. -/
theorem winCount_zero_reps {C G B1 R B2 H : Type} (K : Checker C G B1 R B2 H)
    (P : Prover C G B1 R B2) (Gs : List G) (Rs : List R) (Hs : List H) :
    winCount K 0 P Gs Rs Hs = 0 := by
  have h : (fun gs : List G => sumOver (fun rs : List R =>
      countIf (accepts K 0 P gs rs) (vectors Hs 0)) (vectors Rs 0)) = (fun _ => 0) := by
    funext gs
    have h2 : (fun rs : List R => countIf (accepts K 0 P gs rs) (vectors Hs 0)) =
        (fun _ => 0) := by
      funext rs
      exact countIf_eq_zero_of_forall (fun hs _ => accepts_zero_reps K P gs rs hs)
    rw [h2, sumOver_const, Nat.mul_zero]
  unfold winCount
  rw [h, sumOver_const, Nat.mul_zero]

theorem open_count_le {C G B1 R B2 H : Type} (K : Checker C G B1 R B2 H) (c : C)
    (Gs : List G) (Rs : List R) (Hs : List H) (dG dR : Nat) (hS : K.Sound c Gs Rs Hs dG dR)
    (b1 : B1) (b2 : B2) (j : Nat) (g : G) (r : R) :
    countIf (K.openOk c j g b1 r b2) Hs ≤
      (if K.foldBad c j g || K.evalBad c j g b1 r then Hs.length else 1) := by
  cases hf : K.foldBad c j g with
  | true => exact countIf_le_length _ _
  | false =>
    cases he : K.evalBad c j g b1 r with
    | true => exact countIf_le_length _ _
    | false => exact hS.open_ j g b1 r b2 hf he

theorem eval_sum_le {C G B1 R B2 H : Type} (K : Checker C G B1 R B2 H) (c : C)
    (Gs : List G) (Rs : List R) (Hs : List H) (dG dR : Nat) (hS : K.Sound c Gs Rs Hs dG dR)
    (b1 : B1) (N : Nat) (j : Nat) (g : G) :
    sumOver (fun r => if K.foldBad c j g || K.evalBad c j g b1 r then N else 1) Rs ≤
      (if K.foldBad c j g then Rs.length * N else dR * N + Rs.length) := by
  cases hf : K.foldBad c j g with
  | true =>
    show sumOver (fun _ => N) Rs ≤ Rs.length * N
    rw [sumOver_const]; exact Nat.le_refl _
  | false =>
    show sumOver (fun r => if K.evalBad c j g b1 r then N else 1) Rs ≤ dR * N + Rs.length
    have h := sumOver_ite_le (K.evalBad c j g b1) N 1 Rs
    rw [Nat.mul_one] at h
    exact Nat.le_trans h (Nat.add_le_add_right (Nat.mul_le_mul_right N (hS.eval j g b1 hf)) _)

/-- **Cut-and-choose count.** For a sound per-repetition verifier and any prover strategy, the
number of accepted challenge triples is at most
`(dG·(|R|·N) + |G|·(dR·N + |R|)) ^ reps`, with `N = Hs.length`. -/
theorem cut_and_choose_win_count_le {C G B1 R B2 H : Type} (K : Checker C G B1 R B2 H)
    (reps : Nat) (P : Prover C G B1 R B2) (Gs : List G) (Rs : List R) (Hs : List H)
    (dG dR : Nat) (hS : K.Sound P.commit Gs Rs Hs dG dR) :
    winCount K reps P Gs Rs Hs ≤
      (dG * (Rs.length * Hs.length) + Gs.length * (dR * Hs.length + Rs.length)) ^ reps := by
  have hInner : ∀ gs : List G, gs.length = reps →
      sumOver (fun rs => countIf (accepts K reps P gs rs) (vectors Hs reps)) (vectors Rs reps) ≤
        prodOne (fun j g => if K.foldBad P.commit j g then Rs.length * Hs.length
          else dR * Hs.length + Rs.length) 0 gs := by
    intro gs hg
    have h1 : sumOver (fun rs => countIf (accepts K reps P gs rs) (vectors Hs reps))
        (vectors Rs reps) ≤
        sumOver (prodZip (fun j g r =>
          if K.foldBad P.commit j g || K.evalBad P.commit j g (P.respond1 gs) r
          then Hs.length else 1) 0 gs) (vectors Rs reps) := by
      apply sumOver_vectors_le
      intro rs hr
      have ha : countIf (accepts K reps P gs rs) (vectors Hs reps) ≤
          countIf (allZip (fun j g r h =>
            K.openOk P.commit j g (P.respond1 gs) r (P.respond2 gs rs) h) 0 gs rs)
            (vectors Hs reps) := by
        show countIf (fun hs => decide (1 ≤ reps ∧ gs.length = reps ∧ rs.length = reps) &&
          allZip (fun j g r h =>
            K.openOk P.commit j g (P.respond1 gs) r (P.respond2 gs rs) h) 0 gs rs hs)
          (vectors Hs reps) ≤ _
        rw [countIf_and_const]
        split
        · exact Nat.le_refl _
        · exact Nat.zero_le _
      rw [countIf_allZip_vectors _ Hs reps 0 gs rs hg hr] at ha
      exact Nat.le_trans ha (prodZip_le (fun j g r =>
        open_count_le K P.commit Gs Rs Hs dG dR hS (P.respond1 gs) (P.respond2 gs rs) j g r)
        gs rs 0)
    rw [sumOver_prodZip_vectors _ Rs reps 0 gs hg] at h1
    exact Nat.le_trans h1 (prodOne_le (fun j g =>
      eval_sum_le K P.commit Gs Rs Hs dG dR hS (P.respond1 gs) Hs.length j g) gs 0)
  have hOuter := sumOver_vectors_le Gs reps _ _ hInner
  rw [sumOver_prodOne_vectors] at hOuter
  refine Nat.le_trans hOuter (prodRange_le_pow _ _ (fun j => ?_) reps 0)
  have h := sumOver_ite_le (K.foldBad P.commit j) (Rs.length * Hs.length)
    (dR * Hs.length + Rs.length) Gs
  exact Nat.le_trans h (Nat.add_le_add_right
    (Nat.mul_le_mul_right _ (hS.fold j)) _)

/-! ## 3. Numbers -/

theorem nat_lt_of_mul_lt_mul_right {a b c : Nat} (h : a * c < b * c) : a < b :=
  Nat.lt_of_not_ge (fun hba => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h (Nat.mul_le_mul_right c hba)))

/-- With relative fold and evaluation luck at most `1 / (n·V)` each, one repetition's accepted
fraction is at most `(V + 2) / (n·V)`. -/
theorem rep_fraction_core (G R n dG dR V : Nat) (hG : dG * (n * V) ≤ G)
    (hR : dR * (n * V) ≤ R) :
    (dG * (R * n) + G * (dR * n + R)) * (n * V) ≤ (G * R * n) * (V + 2) := by
  have s1 : dG * (R * n) * (n * V) ≤ G * R * n := by
    have h := Nat.mul_le_mul_right (R * n) hG
    have e1 : dG * (R * n) * (n * V) = dG * (n * V) * (R * n) := by ac_rfl
    have e2 : G * (R * n) = G * R * n := by ac_rfl
    rw [e1, ← e2]; exact h
  have s2 : G * (dR * n) * (n * V) ≤ G * R * n := by
    have h := Nat.mul_le_mul_left (G * n) hR
    have e1 : G * (dR * n) * (n * V) = G * n * (dR * (n * V)) := by ac_rfl
    have e2 : G * n * R = G * R * n := by ac_rfl
    rw [e1, ← e2]; exact h
  have s3 : G * R * (n * V) = G * R * n * V := by ac_rfl
  have eL : (dG * (R * n) + G * (dR * n + R)) * (n * V) =
      dG * (R * n) * (n * V) + (G * (dR * n) * (n * V) + G * R * (n * V)) := by
    rw [Nat.add_mul, Nat.mul_add G, Nat.add_mul]
  have eR : (G * R * n) * (V + 2) = G * R * n + (G * R * n + G * R * n * V) := by
    rw [Nat.mul_add, Nat.mul_two]; ac_rfl
  rw [eL, eR, s3]
  exact Nat.add_le_add s1 (Nat.add_le_add s2 (Nat.le_refl _))

theorem pow_cancel_core (a T W U t B : Nat) (hA : a * W ≤ T * U) (hT : 0 < T)
    (hNum : U ^ t * B < W ^ t) : a ^ t * B < T ^ t := by
  have hP := Nat.pow_le_pow_left hA t
  rw [Nat.mul_pow, Nat.mul_pow] at hP
  have h1 : a ^ t * B * W ^ t ≤ T ^ t * (U ^ t * B) := by
    have h := Nat.mul_le_mul_right B hP
    have e1 : a ^ t * B * W ^ t = a ^ t * W ^ t * B := Nat.mul_right_comm _ _ _
    have e2 : T ^ t * (U ^ t * B) = T ^ t * U ^ t * B := (Nat.mul_assoc _ _ _).symm
    rw [e1, e2]; exact h
  have h2 : T ^ t * (U ^ t * B) < T ^ t * W ^ t :=
    Nat.mul_lt_mul_of_pos_left hNum (Nat.pow_pos hT)
  exact nat_lt_of_mul_lt_mul_right (Nat.lt_of_le_of_lt h1 h2)

theorem two_pow_300_eq : (2 : Nat) ^ 300 = 256 * 2 ^ 292 := by decide +kernel

/-- `(1/256 + 2·2^-300)^33 < 2^-263`. -/
theorem limbo_tau33_numeric : (2 ^ 292 + 2) ^ 33 * 2 ^ 263 < (256 * 2 ^ 292) ^ 33 := by
  decide +kernel

/-- `(1/256 + 2·2^-300)^17 < 2^-135`. -/
theorem limbo_tau17_numeric : (2 ^ 292 + 2) ^ 17 * 2 ^ 135 < (256 * 2 ^ 292) ^ 17 := by
  decide +kernel

/-- `(1/256)^33 = 2^-264` exactly, so the bound `2^-263` cannot be replaced by `2^-264` once
either algebraic term is positive. -/
theorem limbo_tau33_leading_term : (256 : Nat) ^ 33 = 2 ^ 264 := by decide +kernel

/-- Evaluation points of the deployed check: the nonzero elements of `GF(p^5)`. -/
def fp5NonzeroCount : Nat := goldilocksPrime ^ 5 - 1

/-- Degree bound of the masked check polynomial: twice `SD_GRID_B = 192`. -/
def limboEvalDegree : Nat := 384

theorem fp5NonzeroCount_eq : fp5NonzeroCount = 18446744069414584321 ^ 5 - 1 := by rfl

theorem limboEvalDegree_eq : limboEvalDegree = 2 * 192 := by rfl

/-- A degree-384 polynomial vanishes on at most a `2^-300` fraction of the nonzero points. -/
theorem limbo_eval_luck : limboEvalDegree * 2 ^ 300 ≤ fp5NonzeroCount := by decide +kernel

theorem limbo_soundness_core {C G B1 R B2 H : Type} (K : Checker C G B1 R B2 H)
    (reps bits : Nat) (P : Prover C G B1 R B2) (Gs : List G) (Rs : List R) (Hs : List H)
    (dG : Nat) (hS : K.Sound P.commit Gs Rs Hs dG limboEvalDegree) (hH : Hs.length = 256)
    (hRs : Rs.length = fp5NonzeroCount) (hG : dG * 2 ^ 300 ≤ Gs.length) (hGpos : 0 < Gs.length)
    (hNum : (2 ^ 292 + 2) ^ reps * 2 ^ bits < (256 * 2 ^ 292) ^ reps) :
    winCount K reps P Gs Rs Hs * 2 ^ bits < challengeCount reps Gs Rs Hs := by
  rw [challengeCount_eq]
  have hW := cut_and_choose_win_count_le K reps P Gs Rs Hs dG limboEvalDegree hS
  have hR : limboEvalDegree * 2 ^ 300 ≤ Rs.length := hRs ▸ limbo_eval_luck
  rw [two_pow_300_eq] at hG hR
  rw [hH] at hW ⊢
  have hRpos : 0 < Rs.length := by
    rw [hRs]; exact Nat.lt_of_lt_of_le (by decide +kernel) limbo_eval_luck
  have hT : 0 < Gs.length * Rs.length * 256 :=
    Nat.mul_pos (Nat.mul_pos hGpos hRpos) (by decide)
  have hA := rep_fraction_core Gs.length Rs.length 256 dG limboEvalDegree (2 ^ 292) hG hR
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ hW)
    (pow_cancel_core _ _ _ _ reps (2 ^ bits) hA hT hNum)

/-- **256 parties, 33 repetitions.** For a sound per-repetition verifier with the deployed
evaluation domain and degree, and folding luck at most `2^-300`, fewer than a `2^-263` fraction
of the challenge triples is accepted. -/
theorem limbo256_tau33_soundness {C G B1 R B2 H : Type} (K : Checker C G B1 R B2 H)
    (P : Prover C G B1 R B2) (Gs : List G) (Rs : List R) (Hs : List H) (dG : Nat)
    (hS : K.Sound P.commit Gs Rs Hs dG limboEvalDegree) (hH : Hs.length = 256)
    (hRs : Rs.length = fp5NonzeroCount) (hG : dG * 2 ^ 300 ≤ Gs.length) (hGpos : 0 < Gs.length) :
    winCount K 33 P Gs Rs Hs * 2 ^ 263 < challengeCount 33 Gs Rs Hs :=
  limbo_soundness_core K 33 263 P Gs Rs Hs dG hS hH hRs hG hGpos limbo_tau33_numeric

/-- **256 parties, 17 repetitions.** The same with `τ = 17`: fewer than a `2^-135` fraction. -/
theorem limbo256_tau17_soundness {C G B1 R B2 H : Type} (K : Checker C G B1 R B2 H)
    (P : Prover C G B1 R B2) (Gs : List G) (Rs : List R) (Hs : List H) (dG : Nat)
    (hS : K.Sound P.commit Gs Rs Hs dG limboEvalDegree) (hH : Hs.length = 256)
    (hRs : Rs.length = fp5NonzeroCount) (hG : dG * 2 ^ 300 ≤ Gs.length) (hGpos : 0 < Gs.length) :
    winCount K 17 P Gs Rs Hs * 2 ^ 135 < challengeCount 17 Gs Rs Hs :=
  limbo_soundness_core K 17 135 P Gs Rs Hs dG hS hH hRs hG hGpos limbo_tau17_numeric

/-! ## 4. Small instances -/

/-- Accepts exactly when the hidden party is party 0: a prover that corrupts party 0. -/
def guessChecker : Checker Unit Unit Unit Unit Unit Nat :=
  ⟨fun _ _ _ => false, fun _ _ _ _ _ => false, fun _ _ _ _ _ _ h => decide (h = 0)⟩

/-- Accepts whatever the hidden party is: a verifier that does not check the opened views. -/
def laxChecker : Checker Unit Unit Unit Unit Unit Nat :=
  ⟨fun _ _ _ => false, fun _ _ _ _ _ => false, fun _ _ _ _ _ _ _ => true⟩

def unitProver : Prover Unit Unit Unit Unit Unit := ⟨(), fun _ => (), fun _ _ => ()⟩

theorem guessChecker_sound (Gs Rs : List Unit) (Hs : List Nat) (hnd : Hs.Nodup) :
    guessChecker.Sound unitProver.commit Gs Rs Hs 0 0 where
  fold := fun _ => Nat.le_of_eq (countIf_false Gs)
  eval := fun _ _ _ _ => Nat.le_of_eq (countIf_false Rs)
  open_ := fun _ _ _ _ _ _ _ =>
    countIf_le_one_of_unique hnd (fun _ _ hx hy =>
      (of_decide_eq_true hx).trans (of_decide_eq_true hy).symm)

/-- The term `(1/N)^τ` is reached: with two parties and two repetitions the guessing prover is
accepted on exactly one of the four challenge triples, and the verifier is sound. -/
theorem tooth_guessing_prover_attains_one_in_N :
    ∃ (K : Checker Unit Unit Unit Unit Unit Nat) (P : Prover Unit Unit Unit Unit Unit),
      K.Sound P.commit [()] [()] [0, 1] 0 0 ∧
      winCount K 2 P [()] [()] [0, 1] = 1 ∧ challengeCount 2 [()] [()] [0, 1] = 4 :=
  ⟨guessChecker, unitProver, guessChecker_sound [()] [()] [0, 1] (by decide), by decide,
    by decide⟩

/-- Without the opening condition of `Checker.Sound` the count is not bounded: the lax
verifier satisfies the fold and evaluation conditions with `dG = dR = 0` and accepts both of
the two challenge triples, where `cut_and_choose_win_count_le` would give at most one. -/
theorem tooth_lax_checker_exceeds_bound :
    ∃ (K : Checker Unit Unit Unit Unit Unit Nat) (P : Prover Unit Unit Unit Unit Unit),
      (∀ j, countIf (K.foldBad P.commit j) [()] ≤ 0) ∧
      ¬ (winCount K 1 P [()] [()] [0, 1] ≤
        (0 * ([()].length * [0, 1].length) + [()].length * (0 * [0, 1].length + [()].length)) ^ 1) :=
  ⟨laxChecker, unitProver, fun _ => Nat.le_refl 0, by decide⟩

theorem inhabited_cut_and_choose_win_count_le :
    ∃ (K : Checker Unit Unit Unit Unit Unit Nat) (P : Prover Unit Unit Unit Unit Unit)
      (Gs Rs : List Unit) (Hs : List Nat) (dG dR : Nat), K.Sound P.commit Gs Rs Hs dG dR :=
  ⟨guessChecker, unitProver, [()], [()], [0, 1], 0, 0,
    guessChecker_sound [()] [()] [0, 1] (by decide)⟩

/-- The hypotheses of the 256-party theorems are jointly satisfiable: 256 hidden-party indices,
`p^5 − 1` evaluation points, the guessing verifier. -/
theorem inhabited_limbo256_soundness :
    ∃ (K : Checker Unit Unit Unit Unit Unit Nat) (P : Prover Unit Unit Unit Unit Unit)
      (Gs Rs : List Unit) (Hs : List Nat) (dG : Nat),
      K.Sound P.commit Gs Rs Hs dG limboEvalDegree ∧ Hs.length = 256 ∧
      Rs.length = fp5NonzeroCount ∧ dG * 2 ^ 300 ≤ Gs.length ∧ 0 < Gs.length := by
  refine ⟨guessChecker, unitProver, [()], List.replicate fp5NonzeroCount (),
    enumBelow (fun i => i) 256, 0, ?_, length_enumBelow _ _, List.length_replicate, ?_, ?_⟩
  · have h := guessChecker_sound [()] (List.replicate fp5NonzeroCount ())
      (enumBelow (fun i => i) 256) (enumBelow_nodup (fun _ _ _ _ h => h))
    exact ⟨h.fold, fun j g b1 hf => Nat.le_trans (h.eval j g b1 hf) (Nat.zero_le _), h.open_⟩
  · have h : ∀ x : Nat, 0 * x ≤ ([()] : List Unit).length := fun x => by
      rw [Nat.zero_mul]; exact Nat.zero_le _
    exact h _
  · exact Nat.zero_lt_one

/-! ## 5. The hidden-party check of the `N = 256` presentation

`verify_presentation` accepts a repetition when the hidden party it derives from the transcript
is the one the prover left unopened. In the model of `AdvancedMpcAndCreds` the opened parties'
recomputed broadcasts are summarized by one check value in `GF(p^5)` per party, and the opening
passes when every opened party's value is zero (`credentialGgmCheckDefects`). -/

/-- A per-repetition verifier whose opening round is the hidden-party check on a table of check
values. `defect c j g b1 r b2` is the table of repetition `j` after folding challenge `g`,
second message `b1`, evaluation point `r` and third message `b2`. -/
structure DefectChecker (C G B1 R B2 : Type) where
  foldBad : C → Nat → G → Bool
  evalBad : C → Nat → G → B1 → R → Bool
  defect : C → Nat → G → B1 → R → B2 → Fin credentialSdParties → CredentialFp5

/-- The three-challenge checker of a `DefectChecker`; hidden parties are `Fin 256`. -/
def DefectChecker.toChecker {C G B1 R B2 : Type} (K : DefectChecker C G B1 R B2) :
    Checker C G B1 R B2 (Fin credentialSdParties) :=
  ⟨K.foldBad, K.evalBad,
    fun c j g b1 r b2 h => credentialGgmCheckDefects (K.defect c j g b1 r b2) h⟩

/-- All hidden-party indices. -/
def limboParties : List (Fin credentialSdParties) := List.finRange credentialSdParties

theorem limboParties_length : limboParties.length = 256 := by
  unfold limboParties
  rw [List.length_finRange, credentialSdParties_eq]

/-- **One nonzero check value leaves one hidden party.** -/
theorem DefectChecker.open_count_le_one {C G B1 R B2 : Type} (K : DefectChecker C G B1 R B2)
    (c : C) (j : Nat) (g : G) (b1 : B1) (r : R) (b2 : B2) (bad : Fin credentialSdParties)
    (hBad : K.defect c j g b1 r b2 bad ≠ credentialFp5Zero) :
    countIf (K.toChecker.openOk c j g b1 r b2) limboParties ≤ 1 :=
  countIf_le_one_of_unique (List.nodup_finRange _) (fun x y hx hy =>
    (credentialGgmCheckDefects_unique _ bad hBad x hx).trans
      (credentialGgmCheckDefects_unique _ bad hBad y hy).symm)

/-- What the algebra of the presentation has to supply for commitment `c`: few bad folding
challenges, few bad evaluation points, and a nonzero check value after good challenges. -/
structure DefectChecker.AlgebraicSound {C G B1 R B2 : Type} (K : DefectChecker C G B1 R B2)
    (c : C) (Gs : List G) (Rs : List R) (dG dR : Nat) : Prop where
  fold : ∀ j, countIf (K.foldBad c j) Gs ≤ dG
  eval : ∀ j g b1, K.foldBad c j g = false → countIf (K.evalBad c j g b1) Rs ≤ dR
  nonzero : ∀ j g b1 r b2, K.foldBad c j g = false → K.evalBad c j g b1 r = false →
    ∃ bad, K.defect c j g b1 r b2 bad ≠ credentialFp5Zero

/-- The opening condition of `Checker.Sound` holds for the hidden-party check. -/
theorem DefectChecker.sound_of_algebraic {C G B1 R B2 : Type} (K : DefectChecker C G B1 R B2)
    (c : C) (Gs : List G) (Rs : List R) (dG dR : Nat)
    (h : K.AlgebraicSound c Gs Rs dG dR) : K.toChecker.Sound c Gs Rs limboParties dG dR where
  fold := h.fold
  eval := h.eval
  open_ := fun j g b1 r b2 hf he => by
    obtain ⟨bad, hBad⟩ := h.nonzero j g b1 r b2 hf he
    exact K.open_count_le_one c j g b1 r b2 bad hBad

/-- **Deployed profile, interactive count.** 256 parties, `credentialSdRepetitions = 33`
repetitions, evaluation points the nonzero elements of `GF(p^5)`, evaluation degree `384`,
folding luck at most `2^-300`: a prover whose commitment satisfies `AlgebraicSound` is accepted
on fewer than a `2^-263` fraction of the challenge triples `(γ⃗, r⃗, h⃗)`. Independent uniform
challenges per repetition; no Fiat–Shamir, no quantum adversary. -/
theorem limbo256_tau33_defect_check_soundness {C G B1 R B2 : Type}
    (K : DefectChecker C G B1 R B2) (P : Prover C G B1 R B2) (Gs : List G) (Rs : List R)
    (dG : Nat) (hS : K.AlgebraicSound P.commit Gs Rs dG limboEvalDegree)
    (hRs : Rs.length = fp5NonzeroCount) (hG : dG * 2 ^ 300 ≤ Gs.length) (hGpos : 0 < Gs.length) :
    winCount K.toChecker credentialSdRepetitions P Gs Rs limboParties * 2 ^ 263 <
      challengeCount credentialSdRepetitions Gs Rs limboParties := by
  rw [credentialSdRepetitions_eq]
  exact limbo256_tau33_soundness K.toChecker P Gs Rs limboParties dG
    (K.sound_of_algebraic P.commit Gs Rs dG limboEvalDegree hS) limboParties_length hRs hG hGpos

/-- The same for the classical profile, `17` repetitions: fewer than a `2^-135` fraction. -/
theorem limbo256_tau17_defect_check_soundness {C G B1 R B2 : Type}
    (K : DefectChecker C G B1 R B2) (P : Prover C G B1 R B2) (Gs : List G) (Rs : List R)
    (dG : Nat) (hS : K.AlgebraicSound P.commit Gs Rs dG limboEvalDegree)
    (hRs : Rs.length = fp5NonzeroCount) (hG : dG * 2 ^ 300 ≤ Gs.length) (hGpos : 0 < Gs.length) :
    winCount K.toChecker credentialSdRepetitionsClassical P Gs Rs limboParties * 2 ^ 135 <
      challengeCount credentialSdRepetitionsClassical Gs Rs limboParties := by
  rw [credentialSdRepetitionsClassical_eq]
  exact limbo256_tau17_soundness K.toChecker P Gs Rs limboParties dG
    (K.sound_of_algebraic P.commit Gs Rs dG limboEvalDegree hS) limboParties_length hRs hG hGpos

/-- A defect checker with one nonzero check value, at party 255, in every table. -/
def oneDefectChecker : DefectChecker Unit Unit Unit Unit Unit :=
  ⟨fun _ _ _ => false, fun _ _ _ _ _ => false,
    fun _ _ _ _ _ _ p _ => if p.val = 255 then Goldilocks.one else Goldilocks.zero⟩

theorem oneDefectChecker_algebraicSound (Gs Rs : List Unit) (dG dR : Nat) :
    oneDefectChecker.AlgebraicSound () Gs Rs dG dR where
  fold := fun _ => by
    show countIf (fun _ => false) Gs ≤ dG
    rw [countIf_false]; exact Nat.zero_le _
  eval := fun _ _ _ _ => by
    show countIf (fun _ => false) Rs ≤ dR
    rw [countIf_false]; exact Nat.zero_le _
  nonzero := fun _ _ _ _ _ _ _ => by
    refine ⟨⟨255, by rw [credentialSdParties_eq]; decide⟩, fun he => ?_⟩
    have hc : Goldilocks.one = Goldilocks.zero := by
      have h0 := congrFun he 0
      rw [credentialFp5Zero_apply] at h0
      exact h0
    have hv := congrArg Goldilocks.val hc
    rw [Goldilocks.one_val, Goldilocks.zero_val] at hv
    exact absurd hv (by decide)

/-- The hypotheses of the deployed-profile count are jointly satisfiable. -/
theorem inhabited_limbo256_defect_check_soundness :
    ∃ (K : DefectChecker Unit Unit Unit Unit Unit) (P : Prover Unit Unit Unit Unit Unit)
      (Gs Rs : List Unit) (dG : Nat),
      K.AlgebraicSound P.commit Gs Rs dG limboEvalDegree ∧
      Rs.length = fp5NonzeroCount ∧ dG * 2 ^ 300 ≤ Gs.length ∧ 0 < Gs.length :=
  ⟨oneDefectChecker, unitProver, [()], List.replicate fp5NonzeroCount (), 0,
    oneDefectChecker_algebraicSound _ _ 0 limboEvalDegree, List.length_replicate,
    by rw [Nat.zero_mul]; exact Nat.zero_le _, Nat.zero_lt_one⟩

/-! ## Audits

The audit commands read proof bodies, which a module does not export, so they run here. -/

#verify_constructive cut_and_choose_win_count_le
#verify_constructive challengeCount_eq
#verify_constructive winCount_zero_reps
#verify_constructive limbo256_tau33_soundness
#verify_constructive limbo256_tau17_soundness
#verify_constructive limbo_eval_luck
#verify_constructive limbo_tau33_leading_term
#verify_constructive tooth_guessing_prover_attains_one_in_N
#verify_constructive tooth_lax_checker_exceeds_bound

#verify_inhabited cut_and_choose_win_count_le inhabited_cut_and_choose_win_count_le
#verify_inhabited limbo256_tau33_soundness inhabited_limbo256_soundness
#verify_inhabited limbo256_tau17_soundness inhabited_limbo256_soundness

#tooth_pair cut_and_choose_win_count_le vs tooth_lax_checker_exceeds_bound
#tooth_pair cut_and_choose_win_count_le vs tooth_guessing_prover_attains_one_in_N
#tooth_pair limbo256_tau33_soundness vs tooth_lax_checker_exceeds_bound
#tooth_pair limbo256_tau17_soundness vs tooth_guessing_prover_attains_one_in_N

#verify_constructive DefectChecker.open_count_le_one
#verify_constructive DefectChecker.sound_of_algebraic
#verify_constructive limbo256_tau33_defect_check_soundness
#verify_constructive limbo256_tau17_defect_check_soundness
#verify_inhabited limbo256_tau33_defect_check_soundness inhabited_limbo256_defect_check_soundness
#verify_inhabited limbo256_tau17_defect_check_soundness inhabited_limbo256_defect_check_soundness

end Qsag.CutAndChoose
