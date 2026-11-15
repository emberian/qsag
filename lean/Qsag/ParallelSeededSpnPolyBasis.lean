module
/-
# Qsag.ParallelSeededSpnPolyBasis — the tower SPN is the Rust polynomial-basis computation

`ParallelSeededSpnSecurity` states its results for `spnDaviesMeyer48` over `Tower128`. This
module transcribes the arithmetic of `crates/qsag-fts/src/parallel_mpc.rs` on Rust's `u128`
coefficient words and carries the tower statements across `psiTower128ToPoly`, which
`Tower128PolyBasisIso` proves to be a field isomorphism.

* `rustPow7` is `pow7_plain`; `rustSpnRound` is one loop body of `algebraic_step_plain`
  (`x7 ^ mul(y7, GF128_MDS_A)`, `y7 ^ mul(x7, GF128_MDS_B)`); `rustAlgebraicStep` is the 48
  rounds with the Davies–Meyer input feed-forward. Round constants are a parameter
  `Nat → u128 × u128`; `rustSpnRoundConstants` gives their byte framing over an arbitrary
  32-byte hash, which Rust instantiates with `cshake256_framed_32`.
* `rustAlgebraicStep_eq_tower`: for every Rust input and every round-constant sequence, the
  Rust value is the image of `spnDaviesMeyer48` at `gf128MdsATower`, `gf128MdsBTower`.
* Transported consumers, stated on Rust words: `rustPow7_bijective`,
  `rustPow7_differential_uniformity_le_six`, `rustSpn48_active_sboxes_ge_72`,
  `rustSpnIter48_injective`.
* `rustBytes32ToLanes` / `rustLanesToBytes32`: the little-endian lane framing, with both
  round trips, and `rustParallelChainStep_eq_tower` for `parallel_chain_step`.

Limits. The Rust side is a Lean transcription; no MIR or machine-code refinement is claimed.
The hash is a parameter here, so nothing is asserted about cSHAKE-derived constants beyond
their framing. The active-box count and S-box root bound are structural; they give no trail
probability for fixed public constants (see `HashTrailSampling`). The Davies–Meyer map is not
claimed injective, collision resistant or preimage resistant.
-/

public import Qsag.Tower128PolyBasisIso
import all Qsag.Tower128PolyBasisIso
import all Qsag.ParallelSeededSpnSecurity
import all Qsag.ActiveMigrationZeroTest
import all Qsag.SimulationSpine

public section
namespace Qsag
open MigrationExecution

set_option autoImplicit false

/-! ## 1. Rust arithmetic model -/

/-- `pow7_plain` (`parallel_mpc.rs:510`): `x2 = x·x`, `x4 = x2·x2`, `(x·x2)·x4`. -/
def rustPow7 (x : BitVec 128) : BitVec 128 :=
  let x2 := rustGf128Mul x x
  let x4 := rustGf128Mul x2 x2
  rustGf128Mul (rustGf128Mul x x2) x4

/-- One iteration of the loop in `algebraic_step_plain` (`parallel_mpc.rs:529-538`). -/
def rustSpnRound (rc st : BitVec 128 × BitVec 128) : BitVec 128 × BitVec 128 :=
  let x7 := rustPow7 (st.1 ^^^ rc.1)
  let y7 := rustPow7 (st.2 ^^^ rc.2)
  (x7 ^^^ rustGf128Mul y7 gf128MdsAPolyBits, y7 ^^^ rustGf128Mul x7 gf128MdsBPolyBits)

/-- The first `r` loop iterations; `rcs round` is `round_constants(c0, c1, round)`. -/
def rustSpnIter (rcs : Nat → BitVec 128 × BitVec 128) :
    Nat → BitVec 128 × BitVec 128 → BitVec 128 × BitVec 128
  | 0, st => st
  | r + 1, st => rustSpnRound (rcs r) (rustSpnIter rcs r st)

/-- `algebraic_step_plain`: 48 rounds, then `(state.0 ^ input.0, state.1 ^ input.1)`. -/
def rustAlgebraicStep (rcs : Nat → BitVec 128 × BitVec 128)
    (inp : BitVec 128 × BitVec 128) : BitVec 128 × BitVec 128 :=
  let out := rustSpnIter rcs spnRounds inp
  (out.1 ^^^ inp.1, out.2 ^^^ inp.2)

/-! ## 2. Lane-pair basis change -/

def psiTower128Pair (p : Tower128 × Tower128) : BitVec 128 × BitVec 128 :=
  (psiTower128ToPoly p.1, psiTower128ToPoly p.2)

def polyToTower128Pair (p : BitVec 128 × BitVec 128) : Tower128 × Tower128 :=
  (polyToTower128 p.1, polyToTower128 p.2)

theorem psiTower128Pair_polyToTower128Pair (p : BitVec 128 × BitVec 128) :
    psiTower128Pair (polyToTower128Pair p) = p :=
  Prod.ext (psiTower128ToPoly_polyToTower128 p.1) (psiTower128ToPoly_polyToTower128 p.2)

theorem polyToTower128Pair_psiTower128Pair (p : Tower128 × Tower128) :
    polyToTower128Pair (psiTower128Pair p) = p :=
  Prod.ext (polyToTower128_psiTower128ToPoly p.1) (polyToTower128_psiTower128ToPoly p.2)

theorem psiTower128Pair_injective (p q : Tower128 × Tower128)
    (h : psiTower128Pair p = psiTower128Pair q) : p = q := by
  have hc := congrArg polyToTower128Pair h
  rw [polyToTower128Pair_psiTower128Pair, polyToTower128Pair_psiTower128Pair] at hc
  exact hc

theorem polyToTower128Pair_injective (p q : BitVec 128 × BitVec 128)
    (h : polyToTower128Pair p = polyToTower128Pair q) : p = q := by
  have hc := congrArg psiTower128Pair h
  rw [psiTower128Pair_polyToTower128Pair, psiTower128Pair_polyToTower128Pair] at hc
  exact hc

/-! ## 3. Transport of the S-box, the mixing layer, the rounds and Davies–Meyer -/

theorem psiTower128ToPoly_sbox7 (x : Tower128) :
    psiTower128ToPoly (towerSbox7 7 x) = rustPow7 (psiTower128ToPoly x) := by
  unfold towerSbox7 rustPow7
  simp only [psiTower128ToPoly_mul_rust, rustGf128Mul_assoc]

theorem polyToTower128_rustPow7 (a : BitVec 128) :
    polyToTower128 (rustPow7 a) = towerSbox7 7 (polyToTower128 a) := by
  apply psiTower128ToPoly_injective
  rw [psiTower128ToPoly_polyToTower128, psiTower128ToPoly_sbox7,
    psiTower128ToPoly_polyToTower128]

theorem psiTower128Pair_spnLinearMix (st : Tower128 × Tower128) :
    psiTower128Pair (spnLinearMix 7 gf128MdsATower gf128MdsBTower st) =
      (psiTower128ToPoly st.1 ^^^ rustGf128Mul (psiTower128ToPoly st.2) gf128MdsAPolyBits,
       psiTower128ToPoly st.2 ^^^ rustGf128Mul (psiTower128ToPoly st.1) gf128MdsBPolyBits) := by
  apply Prod.ext
  · show psiTower128ToPoly (towerAdd 7 st.1 (towerMul 7 gf128MdsATower st.2)) =
      psiTower128ToPoly st.1 ^^^ rustGf128Mul (psiTower128ToPoly st.2) gf128MdsAPolyBits
    rw [psiTower128ToPoly_add, psiTower128ToPoly_mul_rust, gf128_mds_constants_certified.1,
      rustGf128Mul_comm gf128MdsAPolyBits]
  · show psiTower128ToPoly (towerAdd 7 st.2 (towerMul 7 gf128MdsBTower st.1)) =
      psiTower128ToPoly st.2 ^^^ rustGf128Mul (psiTower128ToPoly st.1) gf128MdsBPolyBits
    rw [psiTower128ToPoly_add, psiTower128ToPoly_mul_rust, gf128_mds_constants_certified.2.1,
      rustGf128Mul_comm gf128MdsBPolyBits]

theorem psiTower128Pair_spnRound128 (rc st : Tower128 × Tower128) :
    psiTower128Pair (spnRound128 gf128MdsATower gf128MdsBTower rc st) =
      rustSpnRound (psiTower128Pair rc) (psiTower128Pair st) := by
  unfold spnRound128
  rw [psiTower128Pair_spnLinearMix]
  show (psiTower128ToPoly (towerSbox7 7 (towerAdd 7 st.1 rc.1)) ^^^
        rustGf128Mul (psiTower128ToPoly (towerSbox7 7 (towerAdd 7 st.2 rc.2))) gf128MdsAPolyBits,
      psiTower128ToPoly (towerSbox7 7 (towerAdd 7 st.2 rc.2)) ^^^
        rustGf128Mul (psiTower128ToPoly (towerSbox7 7 (towerAdd 7 st.1 rc.1))) gf128MdsBPolyBits) =
    (rustPow7 (psiTower128ToPoly st.1 ^^^ psiTower128ToPoly rc.1) ^^^
        rustGf128Mul (rustPow7 (psiTower128ToPoly st.2 ^^^ psiTower128ToPoly rc.2))
          gf128MdsAPolyBits,
      rustPow7 (psiTower128ToPoly st.2 ^^^ psiTower128ToPoly rc.2) ^^^
        rustGf128Mul (rustPow7 (psiTower128ToPoly st.1 ^^^ psiTower128ToPoly rc.1))
          gf128MdsBPolyBits)
  rw [psiTower128ToPoly_sbox7, psiTower128ToPoly_sbox7, psiTower128ToPoly_add,
    psiTower128ToPoly_add]

theorem psiTower128Pair_spnIterRounds128 (rcs : Nat → Tower128 × Tower128) :
    ∀ (r : Nat) (st : Tower128 × Tower128),
      psiTower128Pair (spnIterRounds128 gf128MdsATower gf128MdsBTower rcs r st) =
        rustSpnIter (fun i => psiTower128Pair (rcs i)) r (psiTower128Pair st)
  | 0, _ => rfl
  | r + 1, st => by
    show psiTower128Pair (spnRound128 gf128MdsATower gf128MdsBTower (rcs r)
        (spnIterRounds128 gf128MdsATower gf128MdsBTower rcs r st)) =
      rustSpnRound (psiTower128Pair (rcs r))
        (rustSpnIter (fun i => psiTower128Pair (rcs i)) r (psiTower128Pair st))
    rw [psiTower128Pair_spnRound128, psiTower128Pair_spnIterRounds128 rcs r st]

/-- **Tower SPN ↦ Rust SPN.** The image of the tower Davies–Meyer value is the Rust value on
    the image input with image round constants. -/
theorem psiTower128Pair_spnDaviesMeyer48 (rcs : Nat → Tower128 × Tower128)
    (inp : Tower128 × Tower128) :
    psiTower128Pair (spnDaviesMeyer48 gf128MdsATower gf128MdsBTower rcs inp) =
      rustAlgebraicStep (fun i => psiTower128Pair (rcs i)) (psiTower128Pair inp) := by
  have hIter := psiTower128Pair_spnIterRounds128 rcs spnRounds inp
  apply Prod.ext
  · show psiTower128ToPoly (towerAdd 7
        (spnIterRounds128 gf128MdsATower gf128MdsBTower rcs spnRounds inp).1 inp.1) =
      (rustSpnIter (fun i => psiTower128Pair (rcs i)) spnRounds (psiTower128Pair inp)).1 ^^^
        psiTower128ToPoly inp.1
    rw [psiTower128ToPoly_add, ← hIter]
    rfl
  · show psiTower128ToPoly (towerAdd 7
        (spnIterRounds128 gf128MdsATower gf128MdsBTower rcs spnRounds inp).2 inp.2) =
      (rustSpnIter (fun i => psiTower128Pair (rcs i)) spnRounds (psiTower128Pair inp)).2 ^^^
        psiTower128ToPoly inp.2
    rw [psiTower128ToPoly_add, ← hIter]
    rfl

private theorem psi_comp_inv (rcs : Nat → BitVec 128 × BitVec 128) :
    (fun i => psiTower128Pair (polyToTower128Pair (rcs i))) = rcs :=
  funext fun i => psiTower128Pair_polyToTower128Pair (rcs i)

/-- Rust rounds on arbitrary Rust words are the tower rounds on their preimages. -/
theorem rustSpnIter_eq_tower (rcs : Nat → BitVec 128 × BitVec 128) (r : Nat)
    (st : BitVec 128 × BitVec 128) :
    rustSpnIter rcs r st =
      psiTower128Pair (spnIterRounds128 gf128MdsATower gf128MdsBTower
        (fun i => polyToTower128Pair (rcs i)) r (polyToTower128Pair st)) := by
  rw [psiTower128Pair_spnIterRounds128, psi_comp_inv, psiTower128Pair_polyToTower128Pair]

/-- **Rust SPN = tower SPN, quantified on the Rust side.** For every `u128` input pair and
    every round-constant sequence, `algebraic_step_plain` equals the image of the tower
    `spnDaviesMeyer48` with the certified tower constants. -/
theorem rustAlgebraicStep_eq_tower (rcs : Nat → BitVec 128 × BitVec 128)
    (inp : BitVec 128 × BitVec 128) :
    rustAlgebraicStep rcs inp =
      psiTower128Pair (spnDaviesMeyer48 gf128MdsATower gf128MdsBTower
        (fun i => polyToTower128Pair (rcs i)) (polyToTower128Pair inp)) := by
  rw [psiTower128Pair_spnDaviesMeyer48, psi_comp_inv, psiTower128Pair_polyToTower128Pair]

/-! ## 4. Tower results restated on Rust words -/

/-- `pow7_plain` is a permutation of the `u128` words. -/
theorem rustPow7_bijective : IsBijective rustPow7 :=
  ⟨fun a b h => polyToTower128_injective a b (pow7_tower128_bijective.1 _ _ (by
      rw [← polyToTower128_rustPow7, ← polyToTower128_rustPow7, h])),
   fun b => ⟨psiTower128ToPoly (towerSbox7Inv128 (polyToTower128 b)), by
      rw [← psiTower128ToPoly_sbox7, towerSbox7Inv128_right_inv,
        psiTower128ToPoly_polyToTower128]⟩⟩

/-- Injective maps preserve duplicate-freeness. -/
theorem psiTransport_nodup_map {α β : Type} (f : α → β) (hf : ∀ a b, f a = f b → a = b) :
    ∀ {l : List α}, l.Nodup → (l.map f).Nodup
  | [], _ => .nil
  | a :: l, .cons hrel htail => by
    refine .cons (fun b hb => ?_) (psiTransport_nodup_map f hf htail)
    obtain ⟨a', ha', hEq⟩ := List.mem_map.mp hb
    intro hab
    exact hrel a' ha' (hf a a' (hab.trans hEq.symm))

/-- Counting a predicate on the image list is counting its pullback. -/
theorem psiTransport_filter_map_length {α β : Type} (f : α → β) (p : β → Bool) :
    ∀ l : List α, ((l.map f).filter p).length = (l.filter (fun a => p (f a))).length
  | [] => rfl
  | a :: l => by
    have ih := psiTransport_filter_map_length f p l
    show ((f a :: l.map f).filter p).length = ((a :: l).filter (fun a => p (f a))).length
    rw [List.filter_cons, List.filter_cons]
    cases h : p (f a)
    · simp only [Bool.false_eq_true, ↓reduceIte, ih]
    · simp only [↓reduceIte, List.length_cons, ih]

private theorem polyToTower128_pow7_diff (x delta : BitVec 128) :
    polyToTower128 (rustPow7 (x ^^^ delta) ^^^ rustPow7 x) =
      towerAdd 7 (towerSbox7 7 (towerAdd 7 (polyToTower128 x) (polyToTower128 delta)))
        (towerSbox7 7 (polyToTower128 x)) := by
  rw [polyToTower128_xor, polyToTower128_rustPow7, polyToTower128_rustPow7, polyToTower128_xor]

/-- **Differential uniformity of `pow7_plain` on Rust words.** For a nonzero input XOR
    difference and any output XOR difference, at most six words of any duplicate-free list
    satisfy the differential. -/
theorem rustPow7_differential_uniformity_le_six (delta outDiff : BitVec 128)
    (hDelta : delta ≠ 0#128) (S : List (BitVec 128)) (hNodup : S.Nodup) :
    (S.filter (fun x => decide (rustPow7 (x ^^^ delta) ^^^ rustPow7 x = outDiff))).length ≤ 6 := by
  have hDeltaT : polyToTower128 delta ≠ towerZero 7 :=
    fun h => hDelta ((polyToTower128_eq_zero_iff delta).mp h)
  have hTower := towerSbox7_differential_uniformity_le_six 7 (polyToTower128 delta)
    (polyToTower128 outDiff) hDeltaT (S.map polyToTower128)
    (psiTransport_nodup_map polyToTower128 polyToTower128_injective hNodup)
  rw [psiTransport_filter_map_length] at hTower
  have hPred : (fun x => decide (rustPow7 (x ^^^ delta) ^^^ rustPow7 x = outDiff)) =
      (fun x => decide (towerAdd 7
        (towerSbox7 7 (towerAdd 7 (polyToTower128 x) (polyToTower128 delta)))
        (towerSbox7 7 (polyToTower128 x)) = polyToTower128 outDiff)) := by
    funext x
    have hIff : (rustPow7 (x ^^^ delta) ^^^ rustPow7 x = outDiff) ↔
        (towerAdd 7 (towerSbox7 7 (towerAdd 7 (polyToTower128 x) (polyToTower128 delta)))
          (towerSbox7 7 (polyToTower128 x)) = polyToTower128 outDiff) := by
      rw [← polyToTower128_pow7_diff]
      exact ⟨fun h => congrArg polyToTower128 h, fun h => polyToTower128_injective _ _ h⟩
    by_cases hp : rustPow7 (x ^^^ delta) ^^^ rustPow7 x = outDiff
    · rw [decide_eq_true hp, decide_eq_true (hIff.mp hp)]
    · rw [decide_eq_false hp, decide_eq_false (fun h => hp (hIff.mpr h))]
  rw [hPred]
  exact hTower

/-- Number of nonzero lanes of a Rust XOR difference. -/
def rustLaneActiveWeight (d : BitVec 128 × BitVec 128) : Nat :=
  (if d.1 = 0#128 then 0 else 1) + (if d.2 = 0#128 then 0 else 1)

/-- Active S-boxes of two Rust executions over the first `r` rounds: nonzero lanes of the XOR
    difference entering each round. -/
def rustSpnTrailActiveSboxes (rcs : Nat → BitVec 128 × BitVec 128) :
    Nat → BitVec 128 × BitVec 128 → BitVec 128 × BitVec 128 → Nat
  | 0, _, _ => 0
  | r + 1, s, s' =>
    let cur := rustSpnIter rcs r s
    let cur' := rustSpnIter rcs r s'
    rustSpnTrailActiveSboxes rcs r s s' +
      rustLaneActiveWeight (cur.1 ^^^ cur'.1, cur.2 ^^^ cur'.2)

set_option linter.unusedSimpArgs false in
private theorem rustLaneActiveWeight_psi_diff (u u' : Tower128 × Tower128) :
    rustLaneActiveWeight
        ((psiTower128Pair u).1 ^^^ (psiTower128Pair u').1,
         (psiTower128Pair u).2 ^^^ (psiTower128Pair u').2) =
      laneActiveWeight 7 (towerAdd 7 u.1 u'.1, towerAdd 7 u.2 u'.2) := by
  have hLane : ∀ a b : Tower128,
      (if psiTower128ToPoly a ^^^ psiTower128ToPoly b = 0#128 then 0 else 1) =
        (if towerAdd 7 a b = towerZero 7 then 0 else 1) := by
    intro a b
    rw [← psiTower128ToPoly_add]
    by_cases h : towerAdd 7 a b = towerZero 7
    · rw [(psiTower128ToPoly_eq_zero_iff _).mpr h]
      simp only [h, ↓reduceIte]
    · have h' : ¬ psiTower128ToPoly (towerAdd 7 a b) = 0#128 :=
        fun h' => h ((psiTower128ToPoly_eq_zero_iff _).mp h')
      simp only [h, h', ↓reduceIte]
  show (if psiTower128ToPoly u.1 ^^^ psiTower128ToPoly u'.1 = 0#128 then 0 else 1) +
      (if psiTower128ToPoly u.2 ^^^ psiTower128ToPoly u'.2 = 0#128 then 0 else 1) =
    (if towerAdd 7 u.1 u'.1 = towerZero 7 then 0 else 1) +
      (if towerAdd 7 u.2 u'.2 = towerZero 7 then 0 else 1)
  rw [hLane, hLane]

theorem rustSpnTrailActiveSboxes_psi (rcs : Nat → Tower128 × Tower128) :
    ∀ (r : Nat) (s s' : Tower128 × Tower128),
      rustSpnTrailActiveSboxes (fun i => psiTower128Pair (rcs i)) r
          (psiTower128Pair s) (psiTower128Pair s') =
        spnTrailActiveSboxes gf128MdsATower gf128MdsBTower rcs r s s'
  | 0, _, _ => rfl
  | r + 1, s, s' => by
    show rustSpnTrailActiveSboxes (fun i => psiTower128Pair (rcs i)) r
          (psiTower128Pair s) (psiTower128Pair s') +
        rustLaneActiveWeight
          ((rustSpnIter (fun i => psiTower128Pair (rcs i)) r (psiTower128Pair s)).1 ^^^
            (rustSpnIter (fun i => psiTower128Pair (rcs i)) r (psiTower128Pair s')).1,
           (rustSpnIter (fun i => psiTower128Pair (rcs i)) r (psiTower128Pair s)).2 ^^^
            (rustSpnIter (fun i => psiTower128Pair (rcs i)) r (psiTower128Pair s')).2) =
      spnTrailActiveSboxes gf128MdsATower gf128MdsBTower rcs r s s' +
        laneActiveWeight 7
          (towerAdd 7 (spnIterRounds128 gf128MdsATower gf128MdsBTower rcs r s).1
              (spnIterRounds128 gf128MdsATower gf128MdsBTower rcs r s').1,
           towerAdd 7 (spnIterRounds128 gf128MdsATower gf128MdsBTower rcs r s).2
              (spnIterRounds128 gf128MdsATower gf128MdsBTower rcs r s').2)
    rw [rustSpnTrailActiveSboxes_psi rcs r s s', ← psiTower128Pair_spnIterRounds128,
      ← psiTower128Pair_spnIterRounds128, rustLaneActiveWeight_psi_diff]

/-- **At least 72 active S-boxes in the Rust computation.** Two distinct `u128` input pairs
    under the same round constants activate at least 72 `pow7_plain` evaluations across the 48
    rounds. This is a count of nonzero XOR differences, not a probability. -/
theorem rustSpn48_active_sboxes_ge_72 (rcs : Nat → BitVec 128 × BitVec 128)
    (s s' : BitVec 128 × BitVec 128) (hNe : s ≠ s') :
    72 ≤ rustSpnTrailActiveSboxes rcs spnRounds s s' := by
  have hNeT : polyToTower128Pair s ≠ polyToTower128Pair s' :=
    fun h => hNe (polyToTower128Pair_injective s s' h)
  have hTower := (spn48_active_sboxes_ge_72 parallelSeededMdsPair
    (fun i => polyToTower128Pair (rcs i)) (polyToTower128Pair s) (polyToTower128Pair s') hNeT).1
  have hEq := rustSpnTrailActiveSboxes_psi (fun i => polyToTower128Pair (rcs i)) spnRounds
    (polyToTower128Pair s) (polyToTower128Pair s')
  rw [psi_comp_inv, psiTower128Pair_polyToTower128Pair,
    psiTower128Pair_polyToTower128Pair] at hEq
  rw [hEq]
  exact hTower

/-- The 48 Rust rounds before the feed-forward are injective. Nothing is claimed for the
    Davies–Meyer output `rustAlgebraicStep`. -/
theorem rustSpnIter48_injective (rcs : Nat → BitVec 128 × BitVec 128)
    (s s' : BitVec 128 × BitVec 128) (hNe : s ≠ s') :
    rustSpnIter rcs spnRounds s ≠ rustSpnIter rcs spnRounds s' := by
  have hNeT : polyToTower128Pair s ≠ polyToTower128Pair s' :=
    fun h => hNe (polyToTower128Pair_injective s s' h)
  have hTower := (spnIterRounds_even_active_bound parallelSeededMdsPair
    (fun i => polyToTower128Pair (rcs i)) 24 (polyToTower128Pair s) (polyToTower128Pair s')
    hNeT).1
  intro hEq
  rw [rustSpnIter_eq_tower, rustSpnIter_eq_tower] at hEq
  exact hTower (psiTower128Pair_injective _ _ hEq)

/-! ## 5. Little-endian lane framing -/

theorem encodeNatLeBytes_decodeNatLeBytes : ∀ bs : List UInt8,
    encodeNatLeBytes bs.length (decodeNatLeBytes bs) = bs
  | [] => rfl
  | b :: bs => by
    have hb := b.toNat_lt
    have hmod : (b.toNat + 256 * decodeNatLeBytes bs) % 256 = b.toNat := by omega
    have hdiv : (b.toNat + 256 * decodeNatLeBytes bs) / 256 = decodeNatLeBytes bs := by omega
    show UInt8.ofNat ((b.toNat + 256 * decodeNatLeBytes bs) % 256) ::
        encodeNatLeBytes bs.length ((b.toNat + 256 * decodeNatLeBytes bs) / 256) = b :: bs
    rw [hmod, hdiv, UInt8.ofNat_toNat, encodeNatLeBytes_decodeNatLeBytes bs]

theorem decodeNatLeBytes_lt : ∀ bs : List UInt8, decodeNatLeBytes bs < 256 ^ bs.length
  | [] => Nat.zero_lt_one
  | b :: bs => by
    have hb := b.toNat_lt
    have ih := decodeNatLeBytes_lt bs
    show b.toNat + 256 * decodeNatLeBytes bs < 256 ^ (bs.length + 1)
    rw [Nat.pow_succ]
    omega

/-- `u128::from_le_bytes`: byte `i` holds coefficients `x^(8i) … x^(8i+7)`, least significant
    bit first. -/
def rustU128FromLeBytes (bs : List UInt8) : BitVec 128 := BitVec.ofNat 128 (decodeNatLeBytes bs)

/-- `u128::to_le_bytes`. -/
def rustU128ToLeBytes (v : BitVec 128) : List UInt8 := encodeNatLeBytes 16 v.toNat

private theorem pow256_16 : (256 : Nat) ^ 16 = 2 ^ 128 := by decide

theorem rustU128ToLeBytes_length (v : BitVec 128) : (rustU128ToLeBytes v).length = 16 :=
  encodeNatLeBytes_length 16 v.toNat

theorem rustU128FromLeBytes_toLeBytes (v : BitVec 128) :
    rustU128FromLeBytes (rustU128ToLeBytes v) = v := by
  unfold rustU128FromLeBytes rustU128ToLeBytes
  rw [decodeNatLeBytes_encodeNatLeBytes 16 v.toNat (pow256_16 ▸ v.isLt)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt v.isLt

theorem rustU128ToLeBytes_fromLeBytes (bs : List UInt8) (hLen : bs.length = 16) :
    rustU128ToLeBytes (rustU128FromLeBytes bs) = bs := by
  have hLt : decodeNatLeBytes bs < 2 ^ 128 := by
    have h := decodeNatLeBytes_lt bs
    rw [hLen, pow256_16] at h
    exact h
  have hRound := encodeNatLeBytes_decodeNatLeBytes bs
  rw [hLen] at hRound
  unfold rustU128ToLeBytes rustU128FromLeBytes
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hLt]
  exact hRound

/-- `bytes32_to_lanes` (`parallel_mpc.rs:495`): lane 0 from bytes `0..16`, lane 1 from
    bytes `16..32`. -/
def rustBytes32ToLanes (b : List UInt8) : BitVec 128 × BitVec 128 :=
  (rustU128FromLeBytes (b.take 16), rustU128FromLeBytes (b.drop 16))

/-- `lanes_to_bytes32` (`parallel_mpc.rs:503`). -/
def rustLanesToBytes32 (l : BitVec 128 × BitVec 128) : List UInt8 :=
  rustU128ToLeBytes l.1 ++ rustU128ToLeBytes l.2

private theorem take_append_length_self {α : Type} : ∀ (l₁ l₂ : List α),
    (l₁ ++ l₂).take l₁.length = l₁
  | [], _ => rfl
  | a :: l₁, l₂ => congrArg (a :: ·) (take_append_length_self l₁ l₂)

private theorem drop_append_length_self {α : Type} : ∀ (l₁ l₂ : List α),
    (l₁ ++ l₂).drop l₁.length = l₂
  | [], _ => rfl
  | _ :: l₁, l₂ => drop_append_length_self l₁ l₂

theorem rustLanesToBytes32_length (l : BitVec 128 × BitVec 128) :
    (rustLanesToBytes32 l).length = 32 := by
  unfold rustLanesToBytes32
  rw [List.length_append, rustU128ToLeBytes_length, rustU128ToLeBytes_length]

theorem rustBytes32ToLanes_lanesToBytes32 (l : BitVec 128 × BitVec 128) :
    rustBytes32ToLanes (rustLanesToBytes32 l) = l := by
  have hTake := take_append_length_self (rustU128ToLeBytes l.1) (rustU128ToLeBytes l.2)
  have hDrop := drop_append_length_self (rustU128ToLeBytes l.1) (rustU128ToLeBytes l.2)
  rw [rustU128ToLeBytes_length] at hTake hDrop
  apply Prod.ext
  · show rustU128FromLeBytes ((rustU128ToLeBytes l.1 ++ rustU128ToLeBytes l.2).take 16) = l.1
    rw [hTake, rustU128FromLeBytes_toLeBytes]
  · show rustU128FromLeBytes ((rustU128ToLeBytes l.1 ++ rustU128ToLeBytes l.2).drop 16) = l.2
    rw [hDrop, rustU128FromLeBytes_toLeBytes]

theorem rustLanesToBytes32_bytes32ToLanes (b : List UInt8) (hLen : b.length = 32) :
    rustLanesToBytes32 (rustBytes32ToLanes b) = b := by
  have hT : (b.take 16).length = 16 := by rw [List.length_take, hLen]; rfl
  have hD : (b.drop 16).length = 16 := by rw [List.length_drop, hLen]
  show rustU128ToLeBytes (rustU128FromLeBytes (b.take 16)) ++
    rustU128ToLeBytes (rustU128FromLeBytes (b.drop 16)) = b
  rw [rustU128ToLeBytes_fromLeBytes _ hT, rustU128ToLeBytes_fromLeBytes _ hD,
    List.take_append_drop]

/-! ## 6. `round_constants`, `derive_chain_tweak` and `parallel_chain_step` framing

The 32-byte hash is a parameter `hash32 customization frames`. Rust uses
`cshake256_framed_32`, modelled by `cshake256FramedBytes` in `ThresholdMlDsaAndToprf`; that
module is not imported here and nothing below depends on properties of the hash. -/

/-- ASCII `QSAG.PSFTS.POW7_ROUND.V4`. -/
def spnPow7RoundCustomization : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2e, 0x50, 0x53, 0x46, 0x54, 0x53, 0x2e, 0x50, 0x4f, 0x57, 0x37,
   0x5f, 0x52, 0x4f, 0x55, 0x4e, 0x44, 0x2e, 0x56, 0x34]

/-- ASCII `QSAG.PSFTS.CHAIN_TWK.V2`. -/
def spnChainTweakCustomization : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2e, 0x50, 0x53, 0x46, 0x54, 0x53, 0x2e, 0x43, 0x48, 0x41, 0x49,
   0x4e, 0x5f, 0x54, 0x57, 0x4b, 0x2e, 0x56, 0x32]

/-- `round_constants(c0, c1, round)` (`parallel_mpc.rs:516`): frames `c0.to_le_bytes()`,
    `c1.to_le_bytes()`, `(round as u32).to_be_bytes()`. -/
def rustSpnRoundConstants (hash32 : List UInt8 → List (List UInt8) → List UInt8)
    (c : BitVec 128 × BitVec 128) (round : Nat) : BitVec 128 × BitVec 128 :=
  rustBytes32ToLanes (hash32 spnPow7RoundCustomization
    [rustU128ToLeBytes c.1, rustU128ToLeBytes c.2, be 4 round])

/-- `derive_chain_tweak` (`parallel_mpc.rs:552`): frames `pk_seed`, `epoch` (u32 BE),
    `chain_idx` (u16 BE), `[step]`. -/
def rustDeriveChainTweak (hash32 : List UInt8 → List (List UInt8) → List UInt8)
    (pkSeed : List UInt8) (epoch chainIdx : Nat) (step : UInt8) : BitVec 128 × BitVec 128 :=
  rustBytes32ToLanes (hash32 spnChainTweakCustomization
    [pkSeed, be 4 epoch, be 2 chainIdx, [step]])

/-- `parallel_chain_step` (`parallel_mpc.rs:585`) on 32-byte chain nodes. -/
def rustParallelChainStep (hash32 : List UInt8 → List (List UInt8) → List UInt8)
    (pkSeed : List UInt8) (epoch chainIdx : Nat) (step : UInt8) (cur : List UInt8) :
    List UInt8 :=
  rustLanesToBytes32
    (rustAlgebraicStep
      (rustSpnRoundConstants hash32 (rustDeriveChainTweak hash32 pkSeed epoch chainIdx step))
      (rustBytes32ToLanes cur))

/-- **Byte-level chain step = framed tower Davies–Meyer**, for any hash and any bytes. -/
theorem rustParallelChainStep_eq_tower
    (hash32 : List UInt8 → List (List UInt8) → List UInt8)
    (pkSeed : List UInt8) (epoch chainIdx : Nat) (step : UInt8) (cur : List UInt8) :
    rustParallelChainStep hash32 pkSeed epoch chainIdx step cur =
      rustLanesToBytes32 (psiTower128Pair
        (spnDaviesMeyer48 gf128MdsATower gf128MdsBTower
          (fun i => polyToTower128Pair
            (rustSpnRoundConstants hash32
              (rustDeriveChainTweak hash32 pkSeed epoch chainIdx step) i))
          (polyToTower128Pair (rustBytes32ToLanes cur)))) := by
  unfold rustParallelChainStep
  rw [rustAlgebraicStep_eq_tower]

theorem rustParallelChainStep_length
    (hash32 : List UInt8 → List (List UInt8) → List UInt8)
    (pkSeed : List UInt8) (epoch chainIdx : Nat) (step : UInt8) (cur : List UInt8) :
    (rustParallelChainStep hash32 pkSeed epoch chainIdx step cur).length = 32 :=
  rustLanesToBytes32_length _

/-! ## 7. Controls -/

set_option maxRecDepth 4096 in
/-- Positive controls: values of the Rust model, cross-checked against an independent
    transcription of `gf2_128_mul` / `pow7_plain` / the round body outside Lean. -/
theorem rust_spn_poly_basis_kats :
    rustPow7 2#128 = 0x80#128 ∧
    rustPow7 3#128 = 0xff#128 ∧
    rustSpnRound (7#128, 11#128) (3#128, 5#128) =
      (0x7e449a0c3042bf1c84c9783f54d336e9#128, 0x11db4739396e6534126ec4cc445b09a2#128) ∧
    rustSpnRound (0#128, 0#128) (1#128, 0#128) = (1#128, gf128MdsBPolyBits) := by
  decide +kernel

/-- Positive control for the framing: the little-endian bytes of `GF128_MDS_A`; byte 0 bit 0
    is the constant coefficient and byte 15 bit 7 is `x^127`. -/
theorem rust_le_lane_framing_kats :
    rustU128FromLeBytes [0x35, 0xc8, 0xed, 0x5c, 0x60, 0xc0, 0x9c, 0xf3,
      0x15, 0x7c, 0x4a, 0x7f, 0xb9, 0x79, 0x37, 0x9e] = gf128MdsAPolyBits ∧
    rustU128FromLeBytes [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = 1#128 ∧
    rustU128FromLeBytes [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x80] =
      BitVec.twoPow 128 127 ∧
    rustU128ToLeBytes 2#128 = [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide +kernel

/-- Negative control: reading the same sixteen bytes big-endian gives a different field
    element. -/
theorem tooth_big_endian_lane_framing_differs :
    BitVec.ofNat 128 (ofBE [0x35, 0xc8, 0xed, 0x5c, 0x60, 0xc0, 0x9c, 0xf3,
      0x15, 0x7c, 0x4a, 0x7f, 0xb9, 0x79, 0x37, 0x9e]) ≠ gf128MdsAPolyBits := by
  decide +kernel

set_option maxRecDepth 4096 in
/-- Negative control: exchanging `GF128_MDS_A` and `GF128_MDS_B` changes the round. -/
theorem tooth_swapped_mds_constants_change_round :
    ∃ st : BitVec 128 × BitVec 128,
      rustSpnRound (0#128, 0#128) st ≠
        (let x7 := rustPow7 st.1
         let y7 := rustPow7 st.2
         (x7 ^^^ rustGf128Mul y7 gf128MdsBPolyBits, y7 ^^^ rustGf128Mul x7 gf128MdsAPolyBits)) :=
  ⟨(1#128, 0#128), by decide +kernel⟩

set_option maxRecDepth 4096 in
/-- Negative control: with tower constants read as raw `packTower` words instead of their
    images, the Rust round disagrees with the image of the tower round. -/
theorem tooth_untranslated_tower_constant_breaks_round :
    psiTower128Pair (spnRound128 gf128MdsATower gf128MdsBTower
        (towerZero 7, towerZero 7) (towerZero 7, towerOne 7)) ≠
      (rustGf128Mul 1#128 gf128MdsATowerBits, 1#128) ∧
    psiTower128Pair (spnRound128 gf128MdsATower gf128MdsBTower
        (towerZero 7, towerZero 7) (towerZero 7, towerOne 7)) =
      (gf128MdsAPolyBits, 1#128) := by
  have hEq : psiTower128Pair (spnRound128 gf128MdsATower gf128MdsBTower
        (towerZero 7, towerZero 7) (towerZero 7, towerOne 7)) = (gf128MdsAPolyBits, 1#128) := by
    rw [psiTower128Pair_spnRound128]
    show rustSpnRound (psiTower128ToPoly (towerZero 7), psiTower128ToPoly (towerZero 7))
      (psiTower128ToPoly (towerZero 7), psiTower128ToPoly (towerOne 7)) = _
    rw [psiTower128ToPoly_zero, psiTower128ToPoly_one]
    decide +kernel
  refine ⟨?_, hEq⟩
  rw [hEq]
  decide +kernel

end Qsag
end

#verify_constructive
  Qsag.rustAlgebraicStep_eq_tower
  Qsag.psiTower128Pair_spnDaviesMeyer48
  Qsag.rustPow7_bijective
  Qsag.rustPow7_differential_uniformity_le_six
  Qsag.rustSpn48_active_sboxes_ge_72
  Qsag.rustSpnIter48_injective
  Qsag.rustBytes32ToLanes_lanesToBytes32
  Qsag.rustLanesToBytes32_bytes32ToLanes
  Qsag.rustParallelChainStep_eq_tower
  Qsag.rust_spn_poly_basis_kats
  Qsag.rust_le_lane_framing_kats
  Qsag.tooth_big_endian_lane_framing_differs
  Qsag.tooth_swapped_mds_constants_change_round
  Qsag.tooth_untranslated_tower_constant_breaks_round
