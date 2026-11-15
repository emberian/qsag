module
/-
# Qsag.ZkHemSoundnessAndPrivacy — zk-Hem pads, masks, simulation and extraction

Field: quartic Goldilocks `F_p ⊂ F_{p^2} ⊂ F_{p^4} = F_p[v]/(v^4 - 7)` in the certified tower
representation `Qsag.GoldilocksField.GoldilocksExt4` (`(A, B) = A + B v`, `A, B ∈ F_{p^2}`,
`v^2 = u`, `u^2 = 7`). In the polynomial basis `c_0 + c_1 v + c_2 v^2 + c_3 v^3` the tower
coordinate `B` is `(c_1, c_3)`, so `B = 0` is `c_1 = c_3 = 0`, i.e. membership in `F_{p^2}`
(`tower_c1_zero_iff_poly_odd_zero`).

Zero knowledge is stated as `PerfectlySimulated real sim`: for every witness there is an
explicit bijection from prover coins to simulator coins under which the honest view equals
the simulator's view, and `sim` has no witness argument. Uniform coins on one side are
uniform on the other, so the two views are identically distributed.

§1  Pad rank. Four pad cells `r_0..r_3 ∈ F_p` of a base-field polynomial contribute
    `r_0 + r_1 z + r_2 z^2 + r_3 z^3` to its evaluation at the WHIR point `(z, z^2, ...)`.
    `quartic_primitive_pad_bijection`: for `z ∉ F_{p^2}` this map `F_p^4 → F_{p^4}` has an
    explicit two-sided inverse. `tooth_quadratic_subfield_pad_rank_deficient`,
    `tooth_subfield_challenge_leaks_odd_coordinates`: for `z ∈ F_{p^2}` its image lies in
    `F_{p^2}` and the `(c_1, c_3)` half of a padded value is unpadded. `pad_full_rank_iff`.
§2  `PerfectlySimulated`, `padded_evaluation_perfectly_simulated`.
§3  Separable Libra mask `g = a0 + ∑ a_{i,k} x_i^{k+1}` for any number of rounds and degree:
    `libra_sumcheck_perfectly_simulated`. The witness side is any telescoping transcript
    (`WitnessRounds.Honest`); the mask side is the iterated Boolean sum `sepSum` of `g`.
    `tooth_unmasked_sumcheck_round_leaks`.
§4  `tooth_stage0_only_blinding_leaks_via_early_stop`, `..._via_ood`: blinding sized for the
    stage-0 queries leaves the terminal polynomial and an out-of-domain sample unmasked.
§5  Salted leaves in the random-oracle model: `saltShiftBij`, `salted_leaf_digest_simulated`,
    `salted_leaves_identical_until_bad` for adaptive query trees. The probability that a run
    queries a hidden salt is not bounded here. `tooth_unsalted_leaf_confirms_guess`.
§6  Companion word `U_γ = (1 - γ) B + γ C`: `companion_blend_perfectly_simulated`,
    `blended_terminal_fold_perfectly_simulated`, and the composed
    `zkHem_perfect_hvzk_simulation` over the interface `ZkHemModel`, whose fields state what
    the composition uses: coins ↔ direct observations of `B` are in bijection for every
    witness, and the sumcheck terminal value is a function of those observations.
    `tooth_zero_blend_challenge_reveals_word`.
§7  `blindingEvalBij`, `opened_symbols_perfectly_simulated`: `q` blinding coefficients against
    `q` distinct opened points (Newton interpolation).
§8  Soundness of the two added challenges. `libra_special_soundness`,
    `companion_special_soundness` (two accepting challenges force the claims on the committed
    data); `maskRbr` and `zkHem_mask_rounds_state_restoration_soundness` (at most one bad
    challenge per round, through `rbr_implies_state_restoration_soundness`);
    `masked_sumcheck_round_flip_le_degree`; `tooth_uncommitted_companion_forges_arbitrary_statement`.
    The statement of the mask protocol is the data fixed by the stage-0 commitment; extracting
    that data from a Merkle root against a quantum adversary is the subject of
    `Qsag.QromMerkleOnlineExtraction` and is not re-proved or composed here.
§9  `padModel`, `honest_linear_round`: inhabitants of the interfaces.
    `batched_base_companion_perfectly_simulated`: four base-field companion words batched
    with a challenge outside `F_{p^2}` mask a word over `F_{p^4}` perfectly.
-/

<<<<<<< lean/Qsag/ZkHemSoundnessAndPrivacy.lean
public import Qsag.Math.GoldilocksPrimalityAndExt4Field
import all Qsag.Math.Goldilocks
import all Qsag.Math.GoldilocksPrimalityAndExt4Field
public import Qsag.Coding.AffineProximityGaps
public import Qsag.Oracle.MultiRoundFsQrom
public import Qsag.Tactic.ConstructiveRing
=======
public import Qsag.Math.QuarticExt4
import all Qsag.Math.Goldilocks
import all Qsag.Math.QuarticExt4
public import Qsag.Coding.Cwyz26
public import Qsag.Protocol.Aggregation.MultiRoundFsQrom
public import Qsag.Tactic.CommRing
>>>>>>> /Users/ember/.gemini/antigravity-cli/brain/b2b581fc-3b3a-42dc-9fb9-a018aa1a91d8/scratch/optimistic/arch-layer1/lean/Qsag/ZkHemSoundnessAndPrivacy.lean
public import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.ZkHem

set_option autoImplicit false
open CommRingOps

abbrev Fp := Goldilocks
abbrev Fp2 := GoldilocksExt2
abbrev Fp4 := GoldilocksField.GoldilocksExt4

/-! ## §0. Coordinate formulas of the tower -/

theorem fp2_add_c0 (x y : Fp2) : (add x y).c0 = add x.c0 y.c0 := by rfl
theorem fp2_add_c1 (x y : Fp2) : (add x y).c1 = add x.c1 y.c1 := by rfl
theorem fp2_sub_c0 (x y : Fp2) : (sub x y).c0 = sub x.c0 y.c0 := by rfl
theorem fp2_sub_c1 (x y : Fp2) : (sub x y).c1 = sub x.c1 y.c1 := by rfl
theorem fp2_neg_c0 (x : Fp2) : (neg x).c0 = neg x.c0 := by rfl
theorem fp2_neg_c1 (x : Fp2) : (neg x).c1 = neg x.c1 := by rfl
theorem fp2_mul_c0 (x y : Fp2) :
    (mul x y).c0 = add (mul x.c0 y.c0) (mul GoldilocksExt2.nonResidue (mul x.c1 y.c1)) := by rfl
theorem fp2_mul_c1 (x y : Fp2) : (mul x y).c1 = add (mul x.c0 y.c1) (mul x.c1 y.c0) := by rfl
theorem fp2_zero_c0 : (zero : Fp2).c0 = zero := by rfl
theorem fp2_zero_c1 : (zero : Fp2).c1 = zero := by rfl
theorem fp2_one_c0 : (one : Fp2).c0 = one := by rfl
theorem fp2_one_c1 : (one : Fp2).c1 = zero := by rfl
theorem fp2_u_c0 : GoldilocksExt2.uBasis.c0 = zero := by rfl
theorem fp2_u_c1 : GoldilocksExt2.uBasis.c1 = one := by rfl

theorem fp4_add_c0 (x y : Fp4) : (add x y).c0 = add x.c0 y.c0 := by rfl
theorem fp4_add_c1 (x y : Fp4) : (add x y).c1 = add x.c1 y.c1 := by rfl
theorem fp4_sub_c0 (x y : Fp4) : (sub x y).c0 = sub x.c0 y.c0 := by rfl
theorem fp4_sub_c1 (x y : Fp4) : (sub x y).c1 = sub x.c1 y.c1 := by rfl
theorem fp4_mul_c0 (x y : Fp4) :
    (mul x y).c0 = add (mul x.c0 y.c0) (mul GoldilocksExt2.uBasis (mul x.c1 y.c1)) := by rfl
theorem fp4_mul_c1 (x y : Fp4) : (mul x y).c1 = add (mul x.c0 y.c1) (mul x.c1 y.c0) := by rfl
theorem fp4_zero_c0 : (zero : Fp4).c0 = zero := by rfl
theorem fp4_zero_c1 : (zero : Fp4).c1 = zero := by rfl

theorem ofBase_mul_c0 (a : Fp) (x : Fp2) : (mul (GoldilocksExt2.ofBase a) x).c0 = mul a x.c0 := by
  simp only [fp2_mul_c0, GoldilocksExt2.ofBase_c0, GoldilocksExt2.ofBase_c1]
  constructive_ring

theorem ofBase_mul_c1 (a : Fp) (x : Fp2) : (mul (GoldilocksExt2.ofBase a) x).c1 = mul a x.c1 := by
  simp only [fp2_mul_c1, GoldilocksExt2.ofBase_c0, GoldilocksExt2.ofBase_c1]
  constructive_ring

/-- `B = 0` in the tower is `c_1 = c_3 = 0` in the polynomial basis. -/
theorem tower_c1_zero_iff_poly_odd_zero (z : Fp4) :
    z.c1 = zero ↔
      (GoldilocksField.GoldilocksExt4.towerToPoly z).a1 = zero ∧
      (GoldilocksField.GoldilocksExt4.towerToPoly z).a3 = zero := by
  constructor
  · intro h
    exact ⟨congrArg GoldilocksExt2.c0 h, congrArg GoldilocksExt2.c1 h⟩
  · intro h
    exact GoldilocksExt2.ext h.1 h.2

/-! ## §1. Four base-field pad cells against one `F_{p^4}` evaluation -/

/-- Two-by-two Cramer solution over a constructive field. -/
def cramerX {F : Type} [LawfulField F] (a b c d e f : F) : F :=
  mul (sub (mul e d) (mul b f)) (LawfulField.inv (sub (mul a d) (mul b c)))

def cramerY {F : Type} [LawfulField F] (a b c d e f : F) : F :=
  mul (sub (mul a f) (mul e c)) (LawfulField.inv (sub (mul a d) (mul b c)))

theorem cramer_sound {F : Type} [LawfulField F] (a b c d e f : F)
    (hDet : sub (mul a d) (mul b c) ≠ zero) :
    add (mul a (cramerX a b c d e f)) (mul b (cramerY a b c d e f)) = e ∧
    add (mul c (cramerX a b c d e f)) (mul d (cramerY a b c d e f)) = f := by
  have hi := LawfulField.mul_inv_cancel hDet
  unfold cramerX cramerY
  generalize LawfulField.inv (sub (mul a d) (mul b c)) = i at hi
  constructor
  · have h : add (mul a (mul (sub (mul e d) (mul b f)) i)) (mul b (mul (sub (mul a f) (mul e c)) i)) =
        mul e (mul (sub (mul a d) (mul b c)) i) := by constructive_ring
    rw [hi, LawfulCommRing.mul_one] at h
    exact h
  · have h : add (mul c (mul (sub (mul e d) (mul b f)) i)) (mul d (mul (sub (mul a f) (mul e c)) i)) =
        mul f (mul (sub (mul a d) (mul b c)) i) := by constructive_ring
    rw [hi, LawfulCommRing.mul_one] at h
    exact h

theorem cramer_unique {F : Type} [LawfulField F] (a b c d x y : F)
    (hDet : sub (mul a d) (mul b c) ≠ zero) :
    cramerX a b c d (add (mul a x) (mul b y)) (add (mul c x) (mul d y)) = x ∧
    cramerY a b c d (add (mul a x) (mul b y)) (add (mul c x) (mul d y)) = y := by
  have hi := LawfulField.mul_inv_cancel hDet
  unfold cramerX cramerY
  generalize LawfulField.inv (sub (mul a d) (mul b c)) = i at hi
  constructor
  · have h : mul (sub (mul (add (mul a x) (mul b y)) d) (mul b (add (mul c x) (mul d y)))) i =
        mul x (mul (sub (mul a d) (mul b c)) i) := by constructive_ring
    rw [hi, LawfulCommRing.mul_one] at h
    exact h
  · have h : mul (sub (mul a (add (mul c x) (mul d y))) (mul (add (mul a x) (mul b y)) c)) i =
        mul y (mul (sub (mul a d) (mul b c)) i) := by constructive_ring
    rw [hi, LawfulCommRing.mul_one] at h
    exact h

/-- Four base-field pad cells. -/
structure Pad where
  r0 : Fp
  r1 : Fp
  r2 : Fp
  r3 : Fp
  deriving DecidableEq

def embed (a : Fp) : Fp4 := ⟨GoldilocksExt2.ofBase a, zero⟩

/-- Contribution of the pad cells to an evaluation at the point generated by `z`. -/
def padMap (z : Fp4) (r : Pad) : Fp4 :=
  add (add (add (embed r.r0) (mul (embed r.r1) z)) (mul (embed r.r2) (mul z z)))
    (mul (embed r.r3) (mul z (mul z z)))

/-- Trace and norm of `z = A + B v` over `F_{p^2}`: `z^2 = T z - N`. -/
def zT (z : Fp4) : Fp2 := add z.c0 z.c0
def zN (z : Fp4) : Fp2 :=
  sub (mul z.c0 z.c0) (mul GoldilocksExt2.uBasis (mul z.c1 z.c1))
/-- `z^3 = S z - W`. -/
def zS (z : Fp4) : Fp2 := sub (mul (zT z) (zT z)) (zN z)
def zW (z : Fp4) : Fp2 := mul (zT z) (zN z)

/-- Coordinates of `padMap z r` in the `F_{p^2}`-basis `{1, z}`. -/
def padAlpha (z : Fp4) (r : Pad) : Fp2 :=
  sub (sub (GoldilocksExt2.ofBase r.r0) (mul (GoldilocksExt2.ofBase r.r2) (zN z)))
    (mul (GoldilocksExt2.ofBase r.r3) (zW z))
def padBeta (z : Fp4) (r : Pad) : Fp2 :=
  add (add (GoldilocksExt2.ofBase r.r1) (mul (GoldilocksExt2.ofBase r.r2) (zT z)))
    (mul (GoldilocksExt2.ofBase r.r3) (zS z))

theorem padMap_eq (z : Fp4) (r : Pad) :
    padMap z r = ⟨add (padAlpha z r) (mul (padBeta z r) z.c0), mul (padBeta z r) z.c1⟩ := by
  apply GoldilocksField.GoldilocksExt4.ext
  · simp only [padMap, embed, padAlpha, padBeta, zS, zW, zT, zN, fp4_add_c0, fp4_mul_c0,
      fp4_mul_c1]
    constructive_ring
  · simp only [padMap, embed, padBeta, zS, zT, zN, fp4_add_c1, fp4_mul_c0, fp4_mul_c1]
    constructive_ring

/-- Determinant of the `F_p`-linear system for `(r_2, r_3)`. -/
def padDet (z : Fp4) : Fp :=
  sub (mul (neg (zN z).c1) (zS z).c1) (mul (neg (zW z).c1) (zT z).c1)

theorem padAlpha_c0 (z : Fp4) (r : Pad) :
    (padAlpha z r).c0 = sub (sub r.r0 (mul r.r2 (zN z).c0)) (mul r.r3 (zW z).c0) := by
  simp only [padAlpha, fp2_sub_c0, ofBase_mul_c0, GoldilocksExt2.ofBase_c0]

theorem padAlpha_c1 (z : Fp4) (r : Pad) :
    (padAlpha z r).c1 = add (mul (neg (zN z).c1) r.r2) (mul (neg (zW z).c1) r.r3) := by
  simp only [padAlpha, fp2_sub_c1, ofBase_mul_c1, GoldilocksExt2.ofBase_c1]
  constructive_ring

theorem padBeta_c0 (z : Fp4) (r : Pad) :
    (padBeta z r).c0 = add (add r.r1 (mul r.r2 (zT z).c0)) (mul r.r3 (zS z).c0) := by
  simp only [padBeta, fp2_add_c0, ofBase_mul_c0, GoldilocksExt2.ofBase_c0]

theorem padBeta_c1 (z : Fp4) (r : Pad) :
    (padBeta z r).c1 = add (mul (zT z).c1 r.r2) (mul (zS z).c1 r.r3) := by
  simp only [padBeta, fp2_add_c1, ofBase_mul_c1, GoldilocksExt2.ofBase_c1]
  constructive_ring

def solveR2 (z : Fp4) (α β : Fp2) : Fp :=
  cramerX (neg (zN z).c1) (neg (zW z).c1) (zT z).c1 (zS z).c1 α.c1 β.c1
def solveR3 (z : Fp4) (α β : Fp2) : Fp :=
  cramerY (neg (zN z).c1) (neg (zW z).c1) (zT z).c1 (zS z).c1 α.c1 β.c1

/-- The pad with prescribed `{1, z}`-coordinates `(α, β)`. -/
def solvePad (z : Fp4) (α β : Fp2) : Pad :=
  ⟨add (add α.c0 (mul (solveR2 z α β) (zN z).c0)) (mul (solveR3 z α β) (zW z).c0),
   sub (sub β.c0 (mul (solveR2 z α β) (zT z).c0)) (mul (solveR3 z α β) (zS z).c0),
   solveR2 z α β, solveR3 z α β⟩

theorem solvePad_right (z : Fp4) (hDet : padDet z ≠ zero) (α β : Fp2) :
    padAlpha z (solvePad z α β) = α ∧ padBeta z (solvePad z α β) = β := by
  have hc := cramer_sound (neg (zN z).c1) (neg (zW z).c1) (zT z).c1 (zS z).c1 α.c1 β.c1 hDet
  constructor
  · apply GoldilocksExt2.ext
    · rw [padAlpha_c0]
      simp only [solvePad]
      constructive_ring
    · rw [padAlpha_c1]
      exact hc.1
  · apply GoldilocksExt2.ext
    · rw [padBeta_c0]
      simp only [solvePad]
      constructive_ring
    · rw [padBeta_c1]
      exact hc.2

theorem solvePad_left (z : Fp4) (hDet : padDet z ≠ zero) (r : Pad) :
    solvePad z (padAlpha z r) (padBeta z r) = r := by
  have hu := cramer_unique (neg (zN z).c1) (neg (zW z).c1) (zT z).c1 (zS z).c1 r.r2 r.r3 hDet
  have h2 : solveR2 z (padAlpha z r) (padBeta z r) = r.r2 := by
    unfold solveR2
    rw [padAlpha_c1, padBeta_c1]
    exact hu.1
  have h3 : solveR3 z (padAlpha z r) (padBeta z r) = r.r3 := by
    unfold solveR3
    rw [padAlpha_c1, padBeta_c1]
    exact hu.2
  have e0 : add (add (padAlpha z r).c0 (mul r.r2 (zN z).c0)) (mul r.r3 (zW z).c0) = r.r0 := by
    rw [padAlpha_c0]
    constructive_ring
  have e1 : sub (sub (padBeta z r).c0 (mul r.r2 (zT z).c0)) (mul r.r3 (zS z).c0) = r.r1 := by
    rw [padBeta_c0]
    constructive_ring
  unfold solvePad
  rw [h2, h3, e0, e1]

/-- `(N_1 - T_1 A)^2 - u (T_1 B)^2` is the base-field element `padDet z`. -/
theorem padDet_norm_identity (z : Fp4) :
    GoldilocksField.GoldilocksExt4.norm
      ⟨sub (GoldilocksExt2.ofBase (zN z).c1) (mul (GoldilocksExt2.ofBase (zT z).c1) z.c0),
       mul (GoldilocksExt2.ofBase (zT z).c1) z.c1⟩ = GoldilocksExt2.ofBase (padDet z) := by
  obtain ⟨⟨a0, a1⟩, ⟨b0, b1⟩⟩ := z
  apply GoldilocksExt2.ext
  · simp only [GoldilocksField.GoldilocksExt4.norm, GoldilocksField.GoldilocksExt4.nonResidue,
      padDet, zS, zW, zT, zN, fp2_sub_c0, fp2_sub_c1, fp2_mul_c0, fp2_mul_c1, fp2_add_c0,
      fp2_add_c1, fp2_u_c0, fp2_u_c1, GoldilocksExt2.ofBase_c0, GoldilocksExt2.ofBase_c1]
    constructive_ring
  · simp only [GoldilocksField.GoldilocksExt4.norm, GoldilocksField.GoldilocksExt4.nonResidue,
      padDet, zS, zW, zT, zN, fp2_sub_c0, fp2_sub_c1, fp2_mul_c0, fp2_mul_c1, fp2_add_c0,
      fp2_add_c1, fp2_u_c0, fp2_u_c1, GoldilocksExt2.ofBase_c0, GoldilocksExt2.ofBase_c1]
    constructive_ring

theorem fp_two_ne_zero : add (one : Fp) one ≠ zero := by decide

theorem padDet_ne_zero (z : Fp4) (hB : z.c1 ≠ zero) : padDet z ≠ zero := by
  intro hDet
  have hNorm := padDet_norm_identity z
  rw [hDet] at hNorm
  obtain ⟨⟨a0, a1⟩, ⟨b0, b1⟩⟩ := z
  by_cases hXY :
      (⟨sub (GoldilocksExt2.ofBase (zN ⟨⟨a0, a1⟩, ⟨b0, b1⟩⟩).c1)
          (mul (GoldilocksExt2.ofBase (zT ⟨⟨a0, a1⟩, ⟨b0, b1⟩⟩).c1) ⟨a0, a1⟩),
        mul (GoldilocksExt2.ofBase (zT ⟨⟨a0, a1⟩, ⟨b0, b1⟩⟩).c1) ⟨b0, b1⟩⟩ : Fp4) =
        GoldilocksField.GoldilocksExt4.zero
  · have hX := congrArg GoldilocksField.GoldilocksExt4.c0 hXY
    have hY := congrArg GoldilocksField.GoldilocksExt4.c1 hXY
    have hτ : add a1 a1 = zero := by
      rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hY with h | h
      · exact congrArg GoldilocksExt2.c0 h
      · exact absurd h hB
    have ha1 : a1 = zero := by
      have e : mul (add one one) a1 = add a1 a1 := by constructive_ring
      rw [hτ] at e
      rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero e with h | h
      · exact absurd h fp_two_ne_zero
      · exact h
    have hν : (zN ⟨⟨a0, a1⟩, ⟨b0, b1⟩⟩).c1 = zero := by
      have h0 := congrArg GoldilocksExt2.c0 hX
      simp only [fp2_sub_c0, ofBase_mul_c0, GoldilocksExt2.ofBase_c0] at h0
      have hT : (zT ⟨⟨a0, a1⟩, ⟨b0, b1⟩⟩).c1 = zero := hτ
      rw [hT] at h0
      have e : (zN ⟨⟨a0, a1⟩, ⟨b0, b1⟩⟩).c1 =
          sub (zN ⟨⟨a0, a1⟩, ⟨b0, b1⟩⟩).c1 (mul zero a0) := by constructive_ring
      rw [e]
      exact h0
    have hsum : add (mul b0 b0) (mul GoldilocksExt2.nonResidue (mul b1 b1)) = zero := by
      have e : add (mul b0 b0) (mul GoldilocksExt2.nonResidue (mul b1 b1)) =
          sub (mul (add a0 a0) a1) (zN ⟨⟨a0, a1⟩, ⟨b0, b1⟩⟩).c1 := by
        simp only [zN, fp2_sub_c1, fp2_mul_c0, fp2_mul_c1, fp2_u_c0, fp2_u_c1]
        constructive_ring
      rw [hν, ha1] at e
      have e2 : sub (mul (add a0 a0) (zero : Fp)) zero = zero := by constructive_ring
      exact e.trans e2
    by_cases hb1 : b1 = zero
    · have hb0sq : mul b0 b0 = zero := by
        have e : mul b0 b0 =
            add (mul b0 b0) (mul GoldilocksExt2.nonResidue (mul (zero : Fp) zero)) := by
          constructive_ring
        rw [hb1] at hsum
        exact e.trans hsum
      have hb0 : b0 = zero := by
        rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hb0sq with h | h <;> exact h
      exact hB (GoldilocksExt2.ext hb0 hb1)
    · have hi : mul b1 (Goldilocks.inv b1) = one := Goldilocks.mul_inv_cancel hb1
      generalize Goldilocks.inv b1 = i at hi
      have e : mul (mul b0 i) (mul b0 i) =
          sub (mul (add (mul b0 b0) (mul GoldilocksExt2.nonResidue (mul b1 b1))) (mul i i))
            (mul GoldilocksExt2.nonResidue (mul (mul b1 i) (mul b1 i))) := by constructive_ring
      rw [hsum, hi] at e
      have e2 : sub (mul (zero : Fp) (mul i i)) (mul GoldilocksExt2.nonResidue (mul one one)) =
          neg GoldilocksExt2.nonResidue := by constructive_ring
      exact neg_seven_not_square_in_goldilocks _ (e.trans e2)
  · exact GoldilocksField.GoldilocksExt4.norm_ne_zero hXY hNorm

/-- `{1, z}`-coordinates of an arbitrary `v ∈ F_{p^4}` when `B ≠ 0`. -/
def padDecompBeta (z v : Fp4) : Fp2 := mul v.c1 (GoldilocksExt2.inv z.c1)
def padDecompAlpha (z v : Fp4) : Fp2 := sub v.c0 (mul (padDecompBeta z v) z.c0)

/-- Explicit inverse of `padMap z` for `z ∉ F_{p^2}`. -/
def padInv (z v : Fp4) : Pad := solvePad z (padDecompAlpha z v) (padDecompBeta z v)

theorem padMap_padInv (z : Fp4) (hz : z.c1 ≠ zero) (v : Fp4) : padMap z (padInv z v) = v := by
  have hs := solvePad_right z (padDet_ne_zero z hz) (padDecompAlpha z v) (padDecompBeta z v)
  have hi : mul z.c1 (GoldilocksExt2.inv z.c1) = one := GoldilocksExt2.mul_inv_cancel hz
  rw [padMap_eq]
  unfold padInv
  rw [hs.1, hs.2]
  apply GoldilocksField.GoldilocksExt4.ext
  · show add (padDecompAlpha z v) (mul (padDecompBeta z v) z.c0) = v.c0
    unfold padDecompAlpha
    constructive_ring
  · show mul (padDecompBeta z v) z.c1 = v.c1
    unfold padDecompBeta
    have e : mul (mul v.c1 (GoldilocksExt2.inv z.c1)) z.c1 =
        mul v.c1 (mul z.c1 (GoldilocksExt2.inv z.c1)) := by constructive_ring
    rw [e, hi, LawfulCommRing.mul_one]

theorem padInv_padMap (z : Fp4) (hz : z.c1 ≠ zero) (r : Pad) : padInv z (padMap z r) = r := by
  have hi : mul z.c1 (GoldilocksExt2.inv z.c1) = one := GoldilocksExt2.mul_inv_cancel hz
  have hβ : padDecompBeta z (padMap z r) = padBeta z r := by
    rw [padMap_eq]
    show mul (mul (padBeta z r) z.c1) (GoldilocksExt2.inv z.c1) = padBeta z r
    have e : mul (mul (padBeta z r) z.c1) (GoldilocksExt2.inv z.c1) =
        mul (padBeta z r) (mul z.c1 (GoldilocksExt2.inv z.c1)) := by constructive_ring
    rw [e, hi, LawfulCommRing.mul_one]
  have hα : padDecompAlpha z (padMap z r) = padAlpha z r := by
    unfold padDecompAlpha
    rw [hβ, padMap_eq]
    show sub (add (padAlpha z r) (mul (padBeta z r) z.c0)) (mul (padBeta z r) z.c0) = padAlpha z r
    constructive_ring
  unfold padInv
  rw [hα, hβ]
  exact solvePad_left z (padDet_ne_zero z hz) r

/-- **Full-rank pad.** For a challenge outside `F_{p^2}` the four base-field pad cells are an
    `F_p`-basis coordinate system of `F_{p^4}`: `padMap z` and `padInv z` are mutually inverse. -/
theorem quartic_primitive_pad_bijection (z : Fp4) (hz : z.c1 ≠ zero) :
    (∀ v : Fp4, padMap z (padInv z v) = v) ∧ (∀ r : Pad, padInv z (padMap z r) = r) :=
  ⟨padMap_padInv z hz, padInv_padMap z hz⟩

theorem padMap_c1_of_subfield (z : Fp4) (hz : z.c1 = zero) (r : Pad) :
    (padMap z r).c1 = zero := by
  rw [padMap_eq]
  show mul (padBeta z r) z.c1 = zero
  rw [hz]
  exact LawfulCommRing.mul_zero _

/-- **Counterexample 1.** A challenge in `F_{p^2}` leaves the pad image inside `F_{p^2}`:
    `v` is not a pad value, so the pad map is not onto. -/
theorem tooth_quadratic_subfield_pad_rank_deficient (z : Fp4) (hz : z.c1 = zero) :
    ¬ ∃ r : Pad, padMap z r = GoldilocksField.GoldilocksExt4.vBasis := by
  rintro ⟨r, h⟩
  have h1 := padMap_c1_of_subfield z hz r
  rw [h] at h1
  exact absurd h1 (by decide)

/-- With a subfield challenge the `(c_1, c_3)` half of a padded value is the unpadded one:
    values that differ there are told apart under every choice of pads. -/
theorem tooth_subfield_challenge_leaks_odd_coordinates (z : Fp4) (hz : z.c1 = zero)
    (w w' : Fp4) (hw : w.c1 ≠ w'.c1) (r r' : Pad) :
    ¬ (add w (padMap z r) = add w' (padMap z r')) := by
  intro h
  have h1 := congrArg GoldilocksField.GoldilocksExt4.c1 h
  rw [fp4_add_c1, fp4_add_c1, padMap_c1_of_subfield z hz, padMap_c1_of_subfield z hz,
    LawfulCommRing.add_zero, LawfulCommRing.add_zero] at h1
  exact hw h1

/-- The pad map is onto exactly for challenges outside `F_{p^2}`. -/
theorem pad_full_rank_iff (z : Fp4) : (∀ v : Fp4, ∃ r : Pad, padMap z r = v) ↔ z.c1 ≠ zero := by
  constructor
  · intro hSurj hz
    exact tooth_quadratic_subfield_pad_rank_deficient z hz (hSurj _)
  · intro hz v
    exact ⟨padInv z v, padMap_padInv z hz v⟩

/-! ## §2. Perfect simulation by a bijection of coins -/

/-- Explicit two-sided bijection. -/
structure Bij (α β : Type) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a : α, invFun (toFun a) = a
  right_inv : ∀ b : β, toFun (invFun b) = b

def Bij.symm {α β : Type} (e : Bij α β) : Bij β α :=
  ⟨e.invFun, e.toFun, e.right_inv, e.left_inv⟩

def Bij.trans {α β γ : Type} (e : Bij α β) (f : Bij β γ) : Bij α γ :=
  ⟨fun a => f.toFun (e.toFun a), fun c => e.invFun (f.invFun c),
   fun a => by rw [f.left_inv, e.left_inv], fun c => by rw [e.right_inv, f.right_inv]⟩

/-- `real w` on uniform prover coins `R` and `sim` on uniform simulator coins `C` are the same
    distribution for every witness `w`: a bijection of coins carries one onto the other. The
    simulator `sim` does not take `w`. -/
def PerfectlySimulated {W R C V : Type} (real : W → R → V) (sim : C → V) : Prop :=
  ∀ w : W, ∃ Φ : Bij R C, ∀ r : R, real w r = sim (Φ.toFun r)

/-- Perfect simulation gives perfect witness indistinguishability. -/
theorem PerfectlySimulated.witness_indistinguishable {W R C V : Type}
    {real : W → R → V} {sim : C → V} (h : PerfectlySimulated real sim) (w w' : W) :
    ∃ φ : Bij R R, ∀ r : R, real w r = real w' (φ.toFun r) := by
  obtain ⟨Φ, hΦ⟩ := h w
  obtain ⟨Φ', hΦ'⟩ := h w'
  refine ⟨Φ.trans Φ'.symm, fun r => ?_⟩
  rw [hΦ r, hΦ' ((Φ.trans Φ'.symm).toFun r)]
  show sim (Φ.toFun r) = sim (Φ'.toFun (Φ'.invFun (Φ.toFun r)))
  rw [Φ'.right_inv]

/-- Terminal operand pad: for a challenge outside `F_{p^2}` the padded evaluation
    `w + padMap z r` is simulated by a uniform element of `F_{p^4}`. -/
theorem padded_evaluation_perfectly_simulated (z : Fp4) (hz : z.c1 ≠ zero) :
    PerfectlySimulated (fun (w : Fp4) (r : Pad) => add w (padMap z r)) (fun (o : Fp4) => o) := by
  intro w
  refine ⟨⟨fun r => add w (padMap z r), fun o => padInv z (sub o w), fun r => ?_, fun o => ?_⟩,
    fun r => rfl⟩
  · have e : sub (add w (padMap z r)) w = padMap z r := by constructive_ring
    rw [e, padInv_padMap z hz]
  · rw [padMap_padInv z hz]
    constructive_ring

/-! ## §3. Separable (Libra) sumcheck mask -/

section Libra
variable {F : Type} [LawfulField F]
open RoundPoly

/-- `2^n` as a field element. -/
def pow2 : Nat → F
  | 0 => one
  | n + 1 => add (pow2 n) (pow2 n)

theorem pow2_ne_zero [DecidableEq F] (h2 : add (one : F) one ≠ zero) : ∀ n : Nat, (pow2 n : F) ≠ zero
  | 0 => LawfulField.one_ne_zero
  | n + 1 => by
    intro h
    have e : mul (add one one) (pow2 n : F) = add (pow2 n) (pow2 n) := by constructive_ring
    rcases LawfulField.mul_eq_zero (e.trans h) with h' | h'
    · exact h2 h'
    · exact pow2_ne_zero h2 n h'

/-- Univariate `c_1 X + ... + c_d X^d` (no constant term) from `[c_1, ..., c_d]`. -/
def evalNoConst (cs : List F) (x : F) : F := mul x (evalCoeffs cs x)

/-- `∑_{x ∈ {0,1}^m} (κ + ∑_j u_j(x_j))` for the separable univariates `us = [u_1, ..., u_m]`. -/
def sepSum : List (List F) → F → F
  | [], κ => κ
  | u :: us, κ =>
    add (sepSum us (add κ (evalNoConst u zero))) (sepSum us (add κ (evalNoConst u one)))

theorem sepSum_shift : ∀ (us : List (List F)) (κ c : F),
    sepSum us (add κ c) = add (sepSum us κ) (mul (pow2 us.length) c)
  | [], κ, c => by
    show add κ c = add κ (mul one c)
    constructive_ring
  | u :: us, κ, c => by
    show add (sepSum us (add (add κ c) (evalNoConst u zero)))
        (sepSum us (add (add κ c) (evalNoConst u one))) =
      add (add (sepSum us (add κ (evalNoConst u zero))) (sepSum us (add κ (evalNoConst u one))))
        (mul (add (pow2 us.length) (pow2 us.length)) c)
    have e0 : add (add κ c) (evalNoConst u zero) = add (add κ (evalNoConst u zero)) c := by
      constructive_ring
    have e1 : add (add κ c) (evalNoConst u one) = add (add κ (evalNoConst u one)) c := by
      constructive_ring
    rw [e0, e1, sepSum_shift us _ c, sepSum_shift us _ c]
    constructive_ring

theorem evalCoeffs_map_mul (p : F) : ∀ (cs : List F) (x : F),
    evalCoeffs (cs.map (mul p)) x = mul p (evalCoeffs cs x)
  | [], x => by
    show (zero : F) = mul p zero
    constructive_ring
  | c :: cs, x => by
    show add (mul p c) (mul x (evalCoeffs (cs.map (mul p)) x)) =
      mul p (add c (mul x (evalCoeffs cs x)))
    rw [evalCoeffs_map_mul p cs x]
    constructive_ring

/-- The round polynomial of a separable mask, as a coefficient list, is the Boolean sum of
    the mask over the remaining variables. -/
theorem maskRound_eval (κ : F) (u : List F) (rest : List (List F)) (x : F) :
    evalCoeffs (sepSum rest κ :: u.map (mul (pow2 rest.length))) x =
      sepSum rest (add κ (evalNoConst u x)) := by
  rw [sepSum_shift]
  show add (sepSum rest κ) (mul x (evalCoeffs (u.map (mul (pow2 rest.length))) x)) = _
  rw [evalCoeffs_map_mul]
  unfold evalNoConst
  constructive_ring

def coefList (d : Nat) (f : Nat → F) : List F := (List.range d).map f

/-- Honest sumcheck messages for the witness polynomial: round `i` sends
    `const i + ∑_{k<d} coef i k · X^{k+1}`. -/
structure WitnessRounds (F : Type) where
  H : F
  const : Nat → F
  coef : Nat → Nat → F

def WitnessRounds.msg (w : WitnessRounds F) (d i : Nat) : List F :=
  w.const i :: coefList d (w.coef i)

def WitnessRounds.claim (w : WitnessRounds F) (d : Nat) (c : Nat → F) : Nat → F
  | 0 => w.H
  | i + 1 => evalCoeffs (w.msg d i) (c i)

/-- The messages telescope: `s_i(0) + s_i(1)` is the running claim. -/
def WitnessRounds.Honest (w : WitnessRounds F) (n d : Nat) (c : Nat → F) : Prop :=
  ∀ i : Nat, i < n →
    add (evalCoeffs (w.msg d i) zero) (evalCoeffs (w.msg d i) one) = w.claim d c i

/-- Mask `g(x) = a0 + ∑_i ∑_{k<d} a i k · x_i^{k+1}`. -/
structure LibraMask (F : Type) where
  a0 : F
  a : Nat → Nat → F

def maskUs (a : Nat → Nat → F) (d i cnt : Nat) : List (List F) :=
  (List.range' i cnt).map (fun j => coefList d (a j))

omit [LawfulField F] in
theorem maskUs_length (a : Nat → Nat → F) (d i cnt : Nat) : (maskUs a d i cnt).length = cnt := by
  unfold maskUs
  rw [List.length_map, List.length_range']

omit [LawfulField F] in
theorem maskUs_succ (a : Nat → Nat → F) (d i cnt : Nat) :
    maskUs a d i (cnt + 1) = coefList d (a i) :: maskUs a d (i + 1) cnt := by
  unfold maskUs
  rw [List.range'_succ, List.map_cons]

/-- `a0 + ∑_{j<i} u_j(c_j)`. -/
def maskKappa (m : LibraMask F) (d : Nat) (c : Nat → F) : Nat → F
  | 0 => m.a0
  | i + 1 => add (maskKappa m d c i) (evalNoConst (coefList d (m.a i)) (c i))

/-- `G = ∑_{x ∈ {0,1}^n} g(x)`. -/
def maskSum (m : LibraMask F) (n d : Nat) : F := sepSum (maskUs m.a d 0 n) m.a0

def maskMsg (m : LibraMask F) (n d : Nat) (c : Nat → F) (i : Nat) : List F :=
  sepSum (maskUs m.a d (i + 1) (n - (i + 1))) (maskKappa m d c i) ::
    (coefList d (m.a i)).map (mul (pow2 (n - (i + 1))))

def maskClaim (m : LibraMask F) (n d : Nat) (c : Nat → F) : Nat → F
  | 0 => maskSum m n d
  | i + 1 => evalCoeffs (maskMsg m n d c i) (c i)

theorem maskMsg_eval (m : LibraMask F) (n d : Nat) (c : Nat → F) (i : Nat) (x : F) :
    evalCoeffs (maskMsg m n d c i) x =
      sepSum (maskUs m.a d (i + 1) (n - (i + 1)))
        (add (maskKappa m d c i) (evalNoConst (coefList d (m.a i)) x)) := by
  have h := maskRound_eval (maskKappa m d c i) (coefList d (m.a i))
    (maskUs m.a d (i + 1) (n - (i + 1))) x
  rw [maskUs_length] at h
  exact h

theorem maskClaim_eq (m : LibraMask F) (n d : Nat) (c : Nat → F) :
    ∀ i : Nat, i ≤ n → maskClaim m n d c i = sepSum (maskUs m.a d i (n - i)) (maskKappa m d c i)
  | 0, _ => by rfl
  | i + 1, _ => by
    show evalCoeffs (maskMsg m n d c i) (c i) = _
    rw [maskMsg_eval]
    rfl

theorem maskMsg_telescope (m : LibraMask F) (n d : Nat) (c : Nat → F) (i : Nat) (hi : i < n) :
    add (evalCoeffs (maskMsg m n d c i) zero) (evalCoeffs (maskMsg m n d c i) one) =
      maskClaim m n d c i := by
  rw [maskMsg_eval, maskMsg_eval, maskClaim_eq m n d c i (Nat.le_of_lt hi)]
  have hn : n - i = (n - (i + 1)) + 1 := by omega
  rw [hn, maskUs_succ]
  rfl

/-- Verifier view of the masked sumcheck: the mask sum `G`, the round polynomials of
    `f + ρ g`, and the opened mask value `g(c)`. -/
structure LibraView (F : Type) where
  G : F
  msgs : List (List F)
  gAtPoint : F

def realCoef (w : WitnessRounds F) (m : LibraMask F) (n : Nat) (ρ : F) (i k : Nat) : F :=
  add (w.coef i k) (mul ρ (mul (pow2 (n - (i + 1))) (m.a i k)))

/-- Round `i` of the honest prover: the coefficientwise sum of the witness message and `ρ`
    times the mask message. -/
def realMsg (w : WitnessRounds F) (m : LibraMask F) (n d : Nat) (c : Nat → F) (ρ : F)
    (i : Nat) : List F :=
  add (w.const i) (mul ρ (sepSum (maskUs m.a d (i + 1) (n - (i + 1))) (maskKappa m d c i))) ::
    coefList d (realCoef w m n ρ i)

def libraReal (n d : Nat) (c : Nat → F) (ρ : F) (w : WitnessRounds F) (m : LibraMask F) :
    LibraView F :=
  ⟨maskSum m n d, (List.range n).map (realMsg w m n d c ρ), maskKappa m d c n⟩

theorem evalCoeffs_map_combine (p q : Nat → F) (ρ P x : F) : ∀ l : List Nat,
    evalCoeffs (l.map (fun k => add (p k) (mul ρ (mul P (q k))))) x =
      add (evalCoeffs (l.map p) x) (mul ρ (evalCoeffs ((l.map q).map (mul P)) x))
  | [] => by
    show (zero : F) = add zero (mul ρ zero)
    constructive_ring
  | k :: l => by
    show add (add (p k) (mul ρ (mul P (q k))))
        (mul x (evalCoeffs (l.map (fun k => add (p k) (mul ρ (mul P (q k))))) x)) =
      add (add (p k) (mul x (evalCoeffs (l.map p) x)))
        (mul ρ (add (mul P (q k)) (mul x (evalCoeffs ((l.map q).map (mul P)) x))))
    rw [evalCoeffs_map_combine p q ρ P x l]
    constructive_ring

theorem realMsg_eval (w : WitnessRounds F) (m : LibraMask F) (n d : Nat) (c : Nat → F) (ρ : F)
    (i : Nat) (x : F) :
    evalCoeffs (realMsg w m n d c ρ i) x =
      add (evalCoeffs (w.msg d i) x) (mul ρ (evalCoeffs (maskMsg m n d c i) x)) := by
  show add (add (w.const i) (mul ρ (sepSum (maskUs m.a d (i + 1) (n - (i + 1))) (maskKappa m d c i))))
      (mul x (evalCoeffs ((List.range d).map
        (fun k => add (w.coef i k) (mul ρ (mul (pow2 (n - (i + 1))) (m.a i k))))) x)) =
    add (add (w.const i) (mul x (evalCoeffs ((List.range d).map (w.coef i)) x)))
      (mul ρ (add (sepSum (maskUs m.a d (i + 1) (n - (i + 1))) (maskKappa m d c i))
        (mul x (evalCoeffs (((List.range d).map (m.a i)).map (mul (pow2 (n - (i + 1))))) x))))
  rw [evalCoeffs_map_combine]
  constructive_ring

/-- Simulator coins: the value sent as `G` and the non-constant coefficients of every round. -/
structure LibraCoins (F : Type) where
  G : F
  coef : Nat → Nat → F

/-- The constant coefficient forced by `s(0) + s(1) = claim`. -/
def fixConst (claim : F) (cs : List F) : F :=
  mul (sub claim (evalCoeffs cs one)) (LawfulField.inv (add one one))

theorem fixConst_unique (h2 : add (one : F) one ≠ zero) (c0 claim : F) (cs : List F)
    (h : add (evalCoeffs (c0 :: cs) zero) (evalCoeffs (c0 :: cs) one) = claim) :
    c0 = fixConst claim cs := by
  have hi := LawfulField.mul_inv_cancel h2
  unfold fixConst
  generalize LawfulField.inv (add (one : F) one) = i at hi
  subst h
  have e : mul (sub (add (evalCoeffs (c0 :: cs) zero) (evalCoeffs (c0 :: cs) one))
      (evalCoeffs cs one)) i = mul c0 (mul (add one one) i) := by
    show mul (sub (add (add c0 (mul zero (evalCoeffs cs zero)))
      (add c0 (mul one (evalCoeffs cs one)))) (evalCoeffs cs one)) i = _
    constructive_ring
  rw [e, hi, LawfulCommRing.mul_one]

def simClaim (H ρ : F) (d : Nat) (c : Nat → F) (s : LibraCoins F) : Nat → F
  | 0 => add H (mul ρ s.G)
  | i + 1 =>
    evalCoeffs (fixConst (simClaim H ρ d c s i) (coefList d (s.coef i)) :: coefList d (s.coef i))
      (c i)

def simMsg (H ρ : F) (d : Nat) (c : Nat → F) (s : LibraCoins F) (i : Nat) : List F :=
  fixConst (simClaim H ρ d c s i) (coefList d (s.coef i)) :: coefList d (s.coef i)

/-- Simulator for the masked sumcheck. Inputs: the public claim `H`, the terminal value `y`
    of the witness sumcheck, the challenges, and coins. -/
def libraSim (n d : Nat) (c : Nat → F) (ρ H y : F) (s : LibraCoins F) : LibraView F :=
  ⟨s.G, (List.range n).map (simMsg H ρ d c s),
    mul (sub (simClaim H ρ d c s n) y) (LawfulField.inv ρ)⟩

def libraCoinsOf (n d : Nat) (ρ : F) (w : WitnessRounds F) (m : LibraMask F) : LibraCoins F :=
  ⟨maskSum m n d, realCoef w m n ρ⟩

theorem libra_claims_agree (h2 : add (one : F) one ≠ zero) (n d : Nat) (c : Nat → F) (ρ : F)
    (w : WitnessRounds F) (hw : w.Honest n d c) (m : LibraMask F) :
    ∀ i : Nat, i ≤ n →
      simClaim w.H ρ d c (libraCoinsOf n d ρ w m) i =
        add (w.claim d c i) (mul ρ (maskClaim m n d c i)) ∧
      (∀ j : Nat, j < i → simMsg w.H ρ d c (libraCoinsOf n d ρ w m) j = realMsg w m n d c ρ j)
  | 0, _ => ⟨by rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | i + 1, hi => by
    obtain ⟨ihC, ihM⟩ := libra_claims_agree h2 n d c ρ w hw m i (Nat.le_of_succ_le hi)
    have hTel : add (evalCoeffs (realMsg w m n d c ρ i) zero)
        (evalCoeffs (realMsg w m n d c ρ i) one) =
        simClaim w.H ρ d c (libraCoinsOf n d ρ w m) i := by
      rw [realMsg_eval, realMsg_eval, ihC, ← hw i hi, ← maskMsg_telescope m n d c i hi]
      constructive_ring
    have hMsg : simMsg w.H ρ d c (libraCoinsOf n d ρ w m) i = realMsg w m n d c ρ i := by
      show fixConst _ (coefList d (realCoef w m n ρ i)) :: coefList d (realCoef w m n ρ i) =
        _ :: coefList d (realCoef w m n ρ i)
      rw [← fixConst_unique h2 _ _ _ hTel]
    refine ⟨?_, fun j hj => ?_⟩
    · show evalCoeffs (simMsg w.H ρ d c (libraCoinsOf n d ρ w m) i) (c i) = _
      rw [hMsg, realMsg_eval]
      rfl
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · exact ihM j h
      · rw [h]
        exact hMsg

/-- The honest masked transcript equals the simulator's output on the coins `libraCoinsOf`. -/
theorem libra_real_eq_sim (h2 : add (one : F) one ≠ zero) (n d : Nat) (c : Nat → F) (ρ : F)
    (hρ : ρ ≠ zero) (w : WitnessRounds F) (hw : w.Honest n d c) (m : LibraMask F) :
    libraReal n d c ρ w m =
      libraSim n d c ρ w.H (w.claim d c n) (libraCoinsOf n d ρ w m) := by
  obtain ⟨hC, hM⟩ := libra_claims_agree h2 n d c ρ w hw m n (Nat.le_refl n)
  have hMsgs : (List.range n).map (realMsg w m n d c ρ) =
      (List.range n).map (simMsg w.H ρ d c (libraCoinsOf n d ρ w m)) :=
    List.map_congr_left (fun j hj => (hM j (List.mem_range.mp hj)).symm)
  have hK : maskClaim m n d c n = maskKappa m d c n := by
    rw [maskClaim_eq m n d c n (Nat.le_refl n), Nat.sub_self]
    rfl
  have hi := LawfulField.mul_inv_cancel hρ
  have hG : maskKappa m d c n =
      mul (sub (simClaim w.H ρ d c (libraCoinsOf n d ρ w m) n) (w.claim d c n))
        (LawfulField.inv ρ) := by
    rw [hC, hK]
    generalize LawfulField.inv ρ = i at hi
    have e : mul (sub (add (w.claim d c n) (mul ρ (maskKappa m d c n))) (w.claim d c n)) i =
        mul (maskKappa m d c n) (mul ρ i) := by constructive_ring
    rw [e, hi, LawfulCommRing.mul_one]
  unfold libraReal libraSim
  rw [hMsgs, ← hG]
  rfl

/-- Inverse of `libraCoinsOf`: the mask that makes the honest transcript equal given coins. -/
def libraMaskA (n : Nat) (ρ : F) (w : WitnessRounds F) (s : LibraCoins F) : Nat → Nat → F :=
  fun i k =>
    mul (sub (s.coef i k) (w.coef i k)) (LawfulField.inv (mul ρ (pow2 (n - (i + 1)))))

def libraMaskOf (n d : Nat) (ρ : F) (w : WitnessRounds F) (s : LibraCoins F) : LibraMask F :=
  ⟨mul (sub s.G (sepSum (maskUs (libraMaskA n ρ w s) d 0 n) zero)) (LawfulField.inv (pow2 n)),
   libraMaskA n ρ w s⟩

theorem maskSum_split (m : LibraMask F) (n d : Nat) :
    maskSum m n d = add (sepSum (maskUs m.a d 0 n) zero) (mul (pow2 n) m.a0) := by
  unfold maskSum
  have h := sepSum_shift (maskUs m.a d 0 n) zero m.a0
  rw [maskUs_length, LawfulCommRing.zero_add] at h
  exact h

/-- Mask ↔ simulator-coin bijection. Coordinate `(i, k)` of the coins is an affine bijective
    image of coordinate `(i, k)` of the mask alone; `G` is an affine bijective image of `a0`. -/
def libraCoinBij [DecidableEq F] (h2 : add (one : F) one ≠ zero) (n d : Nat) (ρ : F) (hρ : ρ ≠ zero)
    (w : WitnessRounds F) : Bij (LibraMask F) (LibraCoins F) where
  toFun := libraCoinsOf n d ρ w
  invFun := libraMaskOf n d ρ w
  left_inv m := by
    have hA : libraMaskA n ρ w (libraCoinsOf n d ρ w m) = m.a := by
      funext i k
      have hne : mul ρ (pow2 (n - (i + 1)) : F) ≠ zero := fun h => by
        rcases LawfulField.mul_eq_zero h with h' | h'
        · exact hρ h'
        · exact pow2_ne_zero h2 _ h'
      have hi := LawfulField.mul_inv_cancel hne
      show mul (sub (add (w.coef i k) (mul ρ (mul (pow2 (n - (i + 1))) (m.a i k)))) (w.coef i k))
        (LawfulField.inv (mul ρ (pow2 (n - (i + 1))))) = m.a i k
      generalize LawfulField.inv (mul ρ (pow2 (n - (i + 1)) : F)) = j at hi
      have e : mul (sub (add (w.coef i k) (mul ρ (mul (pow2 (n - (i + 1))) (m.a i k))))
          (w.coef i k)) j = mul (m.a i k) (mul (mul ρ (pow2 (n - (i + 1)))) j) := by
        constructive_ring
      rw [e, hi, LawfulCommRing.mul_one]
    have hi := LawfulField.mul_inv_cancel (pow2_ne_zero h2 n)
    have h0 : mul (sub (maskSum m n d) (sepSum (maskUs m.a d 0 n) zero))
        (LawfulField.inv (pow2 n)) = m.a0 := by
      rw [maskSum_split]
      generalize LawfulField.inv (pow2 n : F) = j at hi
      have e : mul (sub (add (sepSum (maskUs m.a d 0 n) zero) (mul (pow2 n) m.a0))
          (sepSum (maskUs m.a d 0 n) zero)) j = mul m.a0 (mul (pow2 n) j) := by
        constructive_ring
      rw [e, hi, LawfulCommRing.mul_one]
    show (⟨mul (sub (maskSum m n d)
        (sepSum (maskUs (libraMaskA n ρ w (libraCoinsOf n d ρ w m)) d 0 n) zero))
        (LawfulField.inv (pow2 n)), libraMaskA n ρ w (libraCoinsOf n d ρ w m)⟩ : LibraMask F) = m
    rw [hA, h0]
  right_inv s := by
    have hCoef : realCoef w (libraMaskOf n d ρ w s) n ρ = s.coef := by
      funext i k
      have hne : mul ρ (pow2 (n - (i + 1)) : F) ≠ zero := fun h => by
        rcases LawfulField.mul_eq_zero h with h' | h'
        · exact hρ h'
        · exact pow2_ne_zero h2 _ h'
      have hi := LawfulField.mul_inv_cancel hne
      show add (w.coef i k) (mul ρ (mul (pow2 (n - (i + 1)))
        (mul (sub (s.coef i k) (w.coef i k)) (LawfulField.inv (mul ρ (pow2 (n - (i + 1))))))))
        = s.coef i k
      generalize LawfulField.inv (mul ρ (pow2 (n - (i + 1)) : F)) = j at hi
      have e : add (w.coef i k) (mul ρ (mul (pow2 (n - (i + 1)))
          (mul (sub (s.coef i k) (w.coef i k)) j))) =
          add (w.coef i k) (mul (sub (s.coef i k) (w.coef i k))
            (mul (mul ρ (pow2 (n - (i + 1)))) j)) := by constructive_ring
      rw [e, hi]
      constructive_ring
    have hi := LawfulField.mul_inv_cancel (pow2_ne_zero h2 n)
    have hG : maskSum (libraMaskOf n d ρ w s) n d = s.G := by
      rw [maskSum_split]
      show add (sepSum (maskUs (libraMaskA n ρ w s) d 0 n) zero)
        (mul (pow2 n) (mul (sub s.G (sepSum (maskUs (libraMaskA n ρ w s) d 0 n) zero))
          (LawfulField.inv (pow2 n)))) = s.G
      generalize LawfulField.inv (pow2 n : F) = j at hi
      have e : add (sepSum (maskUs (libraMaskA n ρ w s) d 0 n) zero)
          (mul (pow2 n) (mul (sub s.G (sepSum (maskUs (libraMaskA n ρ w s) d 0 n) zero)) j)) =
          add (sepSum (maskUs (libraMaskA n ρ w s) d 0 n) zero)
            (mul (sub s.G (sepSum (maskUs (libraMaskA n ρ w s) d 0 n) zero)) (mul (pow2 n) j)) := by
        constructive_ring
      rw [e, hi]
      constructive_ring
    show (⟨maskSum (libraMaskOf n d ρ w s) n d, realCoef w (libraMaskOf n d ρ w s) n ρ⟩ :
      LibraCoins F) = s
    rw [hCoef, hG]

/-- **Libra mask: perfect simulation of the sumcheck transcript.** Over honest witness
    transcripts with public claim `H` and terminal value `y`, the masked sumcheck view is
    produced from `(H, y)`, the challenges and uniform coins. -/
theorem libra_sumcheck_perfectly_simulated [DecidableEq F] (h2 : add (one : F) one ≠ zero) (n d : Nat)
    (c : Nat → F) (ρ : F) (hρ : ρ ≠ zero) (H y : F) :
    PerfectlySimulated
      (fun (w : {w : WitnessRounds F // w.Honest n d c ∧ w.H = H ∧ w.claim d c n = y})
        (m : LibraMask F) => libraReal n d c ρ w.1 m)
      (libraSim n d c ρ H y) := by
  rintro ⟨w, hw, hH, hy⟩
  refine ⟨libraCoinBij h2 n d ρ hρ w, fun m => ?_⟩
  show libraReal n d c ρ w m = libraSim n d c ρ H y (libraCoinsOf n d ρ w m)
  rw [libra_real_eq_sim h2 n d c ρ hρ w hw m, hH, hy]

/-- Without the mask (`ρ = 0`) the round message is the witness message: witnesses whose
    first-round constants differ are told apart under every mask. -/
theorem tooth_unmasked_sumcheck_round_leaks (n d : Nat) (c : Nat → F)
    (w w' : WitnessRounds F) (hw : w.const 0 ≠ w'.const 0) (m m' : LibraMask F) :
    ¬ (realMsg w m n d c zero 0 = realMsg w' m' n d c zero 0) := by
  intro h
  have h0 := (List.cons.inj h).1
  have e : ∀ (a b : F), add a (mul zero b) = a := fun a b => by constructive_ring
  rw [e, e] at h0
  exact hw h0

end Libra

/-! ## §4. Counterexample 2: blinding sized for the stage-0 queries only -/

section StageZeroOnly
variable {F : Type} [LawfulField F]

/-- One binary fold of a coefficient vector: `f_even + α f_odd`. -/
def foldCoeffs (α : F) (f : Nat → F) : Nat → F :=
  fun i => add (f (2 * i)) (mul α (f (2 * i + 1)))

/-- Witness `w0 + w1 X` blinded with one coin: `B(X) = w0 + w1 X + r X^2`. One coin covers
    one opened stage-0 position. -/
def stage0Blinded (w0 w1 r : F) : Nat → F
  | 0 => w0
  | 1 => w1
  | 2 => r
  | _ => zero

def evalQuad (f : Nat → F) (x : F) : F :=
  add (f 0) (add (mul (f 1) x) (mul (f 2) (mul x x)))

/-- What the verifier sees: one opened stage-0 symbol at `x`, one out-of-domain sample at
    `z`, and the two coefficients of the once-folded polynomial sent in the clear. -/
structure Stage0View (F : Type) where
  opened : F
  ood : F
  terminal0 : F
  terminal1 : F

def stage0OnlyView (α x z w0 w1 r : F) : Stage0View F :=
  ⟨evalQuad (stage0Blinded w0 w1 r) x, evalQuad (stage0Blinded w0 w1 r) z,
   foldCoeffs α (stage0Blinded w0 w1 r) 0, foldCoeffs α (stage0Blinded w0 w1 r) 1⟩

/-- **Counterexample 2 (terminal polynomial).** The constant coefficient of the folded
    polynomial is `w0 + α w1` whatever the coin: witnesses that differ there have different
    views under every pair of coins. -/
theorem tooth_stage0_only_blinding_leaks_via_early_stop (α x z w0 w1 w0' w1' : F)
    (h : add w0 (mul α w1) ≠ add w0' (mul α w1')) (r r' : F) :
    ¬ (stage0OnlyView α x z w0 w1 r = stage0OnlyView α x z w0' w1' r') := by
  intro hEq
  exact h (congrArg Stage0View.terminal0 hEq)

/-- **Counterexample 2 (out-of-domain sample).** Even with the terminal polynomial hidden,
    the opened symbol and the out-of-domain sample together determine
    `w0 (x^2 - z^2) + w1 x z (x - z)`, a function of the witness alone. -/
theorem tooth_stage0_only_blinding_leaks_via_ood (α x z w0 w1 w0' w1' : F)
    (h : add (mul w0 (sub (mul x x) (mul z z))) (mul w1 (mul (mul x z) (sub x z))) ≠
      add (mul w0' (sub (mul x x) (mul z z))) (mul w1' (mul (mul x z) (sub x z)))) (r r' : F) :
    ¬ (((stage0OnlyView α x z w0 w1 r).opened, (stage0OnlyView α x z w0 w1 r).ood) =
      ((stage0OnlyView α x z w0' w1' r').opened, (stage0OnlyView α x z w0' w1' r').ood)) := by
  intro hEq
  have hO : add w0 (add (mul w1 x) (mul r (mul x x))) =
      add w0' (add (mul w1' x) (mul r' (mul x x))) := congrArg Prod.fst hEq
  have hZ : add w0 (add (mul w1 z) (mul r (mul z z))) =
      add w0' (add (mul w1' z) (mul r' (mul z z))) := congrArg Prod.snd hEq
  have e : ∀ a b t : F, add (mul a (sub (mul x x) (mul z z))) (mul b (mul (mul x z) (sub x z))) =
      sub (mul (mul x x) (add a (add (mul b z) (mul t (mul z z)))))
        (mul (mul z z) (add a (add (mul b x) (mul t (mul x x))))) := fun a b t => by
    constructive_ring
  apply h
  rw [e w0 w1 r, e w0' w1' r', hO, hZ]

end StageZeroOnly

/-! ## §5. Salted Merkle leaves in the random-oracle model -/

section SaltedLeaves
variable {F : Type} [LawfulField F] {S D A : Type}

/-- Re-key the oracle on every salt `s` by shifting the cell argument by `δ s`. -/
def saltShift (δ : S → F) (O : S × F → D) : S × F → D :=
  fun q => O (q.1, add q.2 (δ q.1))

/-- `saltShift δ` is a bijection of oracles: a uniform oracle stays uniform. -/
def saltShiftBij (δ : S → F) : Bij (S × F → D) (S × F → D) where
  toFun := saltShift δ
  invFun := saltShift (fun s => neg (δ s))
  left_inv O := by
    funext q
    show O (q.1, add (add q.2 (neg (δ q.1))) (δ q.1)) = O q
    have e : add (add q.2 (neg (δ q.1))) (δ q.1) = q.2 := by constructive_ring
    rw [e]
  right_inv O := by
    funext q
    show O (q.1, add (add q.2 (δ q.1)) (neg (δ q.1))) = O q
    have e : add (add q.2 (δ q.1)) (neg (δ q.1)) = q.2 := by constructive_ring
    rw [e]

/-- The digest of a salted leaf holding the witness cell `w s` under `O` is the digest of a
    leaf holding `0` under the re-keyed oracle. -/
theorem salted_leaf_digest_simulated (O : S × F → D) (w : S → F) (s : S) :
    O (s, w s) = saltShift w O (s, zero) := by
  show O (s, w s) = O (s, add zero (w s))
  rw [LawfulCommRing.zero_add]

/-- Adaptive random-oracle adversary: a decision tree of queries. -/
inductive RoAdv (S F D A : Type) where
  | done : A → RoAdv S F D A
  | query : S × F → (D → RoAdv S F D A) → RoAdv S F D A

def RoAdv.run (O : S × F → D) : RoAdv S F D A → A
  | .done a => a
  | .query q k => (k (O q)).run O

/-- The run under `O` never queries a salt in `hidden`. -/
def RoAdv.Avoids (O : S × F → D) (hidden : S → Prop) : RoAdv S F D A → Prop
  | .done _ => True
  | .query q k => ¬ hidden q.1 ∧ (k (O q)).Avoids O hidden

/-- Salts queried along the run under `O`. -/
def RoAdv.queriedSalts (O : S × F → D) : RoAdv S F D A → List S
  | .done _ => []
  | .query q k => q.1 :: (k (O q)).queriedSalts O

omit [LawfulField F] in
theorem RoAdv.avoids_iff (O : S × F → D) (hidden : S → Prop) :
    ∀ adv : RoAdv S F D A, adv.Avoids O hidden ↔ ∀ s ∈ adv.queriedSalts O, ¬ hidden s
  | .done _ => ⟨fun _ s hs => absurd hs List.not_mem_nil, fun _ => True.intro⟩
  | .query q k => by
    have ih := RoAdv.avoids_iff O hidden (k (O q))
    constructor
    · rintro ⟨hq, hk⟩ s hs
      rcases List.mem_cons.mp hs with h | h
      · rw [h]
        exact hq
      · exact ih.mp hk s h
    · intro h
      exact ⟨h q.1 (List.mem_cons_self), ih.mpr (fun s hs => h s (List.mem_cons_of_mem _ hs))⟩

/-- **Identical until bad.** If `δ` vanishes off the hidden salts and the adversary's run
    never queries a hidden salt, the run is the same under `O` and under the re-keyed oracle.
    Together with `salted_leaf_digest_simulated` and `saltShiftBij`: the digests of unopened
    leaves and the adversary's oracle view are those of leaves holding `0`, unless the
    adversary queries one of the hidden salts. -/
theorem salted_leaves_identical_until_bad (δ : S → F) (hidden : S → Prop)
    (hδ : ∀ s : S, ¬ hidden s → δ s = zero) (O : S × F → D) :
    ∀ adv : RoAdv S F D A, adv.Avoids O hidden → adv.run (saltShift δ O) = adv.run O
  | .done _, _ => rfl
  | .query q k, h => by
    have hq : saltShift δ O q = O q := by
      show O (q.1, add q.2 (δ q.1)) = O q
      rw [hδ q.1 h.1, LawfulCommRing.add_zero]
    show (k (saltShift δ O q)).run (saltShift δ O) = (k (O q)).run O
    rw [hq]
    exact salted_leaves_identical_until_bad δ hidden hδ O (k (O q)) h.2

/-- One query that tests a guessed cell value against a published unsalted digest. -/
def guessAdv [DecidableEq D] (v : F) (digest : D) : RoAdv Unit F D Bool :=
  .query ((), v) (fun d => .done (decide (d = digest)))

omit [LawfulField F] in
/-- Without a salt the digest of a cell is a test oracle for guesses of that cell. -/
theorem tooth_unsalted_leaf_confirms_guess [DecidableEq D] (O : Unit × F → D) (v v' : F)
    (h : O ((), v) ≠ O ((), v')) :
    ¬ ((guessAdv v (O ((), v))).run O = (guessAdv v (O ((), v'))).run O) := by
  show ¬ (decide (O ((), v) = O ((), v)) = decide (O ((), v) = O ((), v')))
  rw [decide_eq_true rfl, decide_eq_false h]
  exact Bool.noConfusion

end SaltedLeaves

/-! ## §6. Companion word and the composed view -/

section Companion
variable {F : Type} [LawfulField F] {ι : Type}

/-- `U_γ = (1 - γ) B + γ C`. -/
def blend (γ : F) (B C : ι → F) : ι → F :=
  fun i => add (mul (sub one γ) (B i)) (mul γ (C i))

def unblend (γ : F) (B U : ι → F) : ι → F :=
  fun i => mul (sub (U i) (mul (sub one γ) (B i))) (LawfulField.inv γ)

theorem unblend_blend (γ : F) (hγ : γ ≠ zero) (B C : ι → F) :
    unblend γ B (blend γ B C) = C := by
  funext i
  have hi := LawfulField.mul_inv_cancel hγ
  show mul (sub (add (mul (sub one γ) (B i)) (mul γ (C i))) (mul (sub one γ) (B i)))
    (LawfulField.inv γ) = C i
  generalize LawfulField.inv γ = j at hi
  have e : mul (sub (add (mul (sub one γ) (B i)) (mul γ (C i))) (mul (sub one γ) (B i))) j =
      mul (C i) (mul γ j) := by constructive_ring
  rw [e, hi, LawfulCommRing.mul_one]

theorem blend_unblend (γ : F) (hγ : γ ≠ zero) (B U : ι → F) :
    blend γ B (unblend γ B U) = U := by
  funext i
  have hi := LawfulField.mul_inv_cancel hγ
  show add (mul (sub one γ) (B i))
    (mul γ (mul (sub (U i) (mul (sub one γ) (B i))) (LawfulField.inv γ))) = U i
  generalize LawfulField.inv γ = j at hi
  have e : add (mul (sub one γ) (B i)) (mul γ (mul (sub (U i) (mul (sub one γ) (B i))) j)) =
      add (mul (sub one γ) (B i)) (mul (sub (U i) (mul (sub one γ) (B i))) (mul γ j)) := by
    constructive_ring
  rw [e, hi]
  constructive_ring

/-- For `γ ≠ 0` and a uniform companion `C`, the blended word is uniform whatever `B` is. -/
theorem companion_blend_perfectly_simulated (γ : F) (hγ : γ ≠ zero) :
    PerfectlySimulated (fun (B : ι → F) (C : ι → F) => blend γ B C) (fun (U : ι → F) => U) :=
  fun B => ⟨⟨blend γ B, unblend γ B, unblend_blend γ hγ B, blend_unblend γ hγ B⟩, fun _ => rfl⟩

/-- Every fold of the blended coefficient vector, in particular the terminal polynomial sent
    in the clear, is a function of a uniform word. Compare
    `tooth_stage0_only_blinding_leaks_via_early_stop`. -/
theorem blended_terminal_fold_perfectly_simulated (γ : F) (hγ : γ ≠ zero) (α : F) :
    PerfectlySimulated (fun (B : Nat → F) (C : Nat → F) => foldCoeffs α (blend γ B C))
      (fun (U : Nat → F) => foldCoeffs α U) :=
  fun B => ⟨⟨blend γ B, unblend γ B, unblend_blend γ hγ B, blend_unblend γ hγ B⟩, fun _ => rfl⟩

/-- `F`-linear functional on words (an evaluation claim `⟨·, t⟩`). -/
structure LinForm (ι F : Type) [LawfulField F] where
  app : (ι → F) → F
  lin : ∀ (a b : F) (u v : ι → F),
    app (fun i => add (mul a (u i)) (mul b (v i))) = add (mul a (app u)) (mul b (app v))

/-- Evaluation at one index. -/
def LinForm.evalAt (i : ι) : LinForm ι F := ⟨fun u => u i, fun _ _ _ _ => rfl⟩

/-- Weighted sum `∑_j t_j · u(i_j)`. -/
def dotAt (ts : List (ι × F)) (u : ι → F) : F :=
  match ts with
  | [] => zero
  | t :: rest => add (mul t.2 (u t.1)) (dotAt rest u)

def LinForm.dot (ts : List (ι × F)) : LinForm ι F where
  app := dotAt ts
  lin a b u v := by
    induction ts with
    | nil =>
      show (zero : F) = add (mul a zero) (mul b zero)
      constructive_ring
    | cons t rest ih =>
      show add (mul t.2 (add (mul a (u t.1)) (mul b (v t.1))))
          (dotAt rest (fun i => add (mul a (u i)) (mul b (v i)))) =
        add (mul a (add (mul t.2 (u t.1)) (dotAt rest u)))
          (mul b (add (mul t.2 (v t.1)) (dotAt rest v)))
      rw [ih]
      constructive_ring

theorem blend_claim (ℓ : LinForm ι F) (γ : F) (B C : ι → F) :
    ℓ.app (blend γ B C) = add (mul (sub one γ) (ℓ.app B)) (mul γ (ℓ.app C)) :=
  ℓ.lin _ _ B C

end Companion

/-- Algebraic interface of one zk-Hem opening at fixed verifier challenges.
    * `enc w κ` is the stage-0 word `B` committed for witness `w` with pad and blinding
      coins `κ`.
    * `obs w κ` collects what is revealed about `B` itself: the padded terminal operand
      evaluations and the opened stage-0 symbols. `obs_left`/`obs_right` say that for every
      witness the coins are in bijection with these observations.
    * `ell` is the evaluation claim on `B`; its value is part of the observations.
    * `rounds w κ` is the honest sumcheck transcript of the constraint polynomial, with
      public claim `pubH` and terminal value determined by the observations. -/
structure ZkHemModel (F : Type) [LawfulField F] where
  Wit : Type
  Coin : Type
  Obs : Type
  Idx : Type
  n : Nat
  d : Nat
  c : Nat → F
  pubH : F
  enc : Wit → Coin → Idx → F
  ell : LinForm Idx F
  obs : Wit → Coin → Obs
  obsInv : Wit → Obs → Coin
  obs_left : ∀ (w : Wit) (κ : Coin), obsInv w (obs w κ) = κ
  obs_right : ∀ (w : Wit) (o : Obs), obs w (obsInv w o) = o
  evalOf : Obs → F
  eval_obs : ∀ (w : Wit) (κ : Coin), ell.app (enc w κ) = evalOf (obs w κ)
  term : Obs → F
  rounds : Wit → Coin → WitnessRounds F
  rounds_honest : ∀ (w : Wit) (κ : Coin), (rounds w κ).Honest n d c
  rounds_claim : ∀ (w : Wit) (κ : Coin), (rounds w κ).H = pubH
  rounds_term : ∀ (w : Wit) (κ : Coin), (rounds w κ).claim d c n = term (obs w κ)

section Composed
variable {F : Type} [LawfulField F]

/-- Field view of one zk-Hem opening. `word` is the whole blended word `U_γ`: every
    out-of-domain answer, fold oracle, later-stage opening and the terminal polynomial of
    the WHIR run on `U_γ` is a function of it, and the opened companion symbols are
    functions of `word` and `obs`. `sigma` is the committed companion claim `⟨C, t⟩`. -/
structure ZkHemView (M : ZkHemModel F) where
  obs : M.Obs
  word : M.Idx → F
  sigma : F
  libra : LibraView F

def ZkHemModel.real (M : ZkHemModel F) (ρ γ : F) (w : M.Wit)
    (r : M.Coin × (M.Idx → F) × LibraMask F) : ZkHemView M :=
  ⟨M.obs w r.1, blend γ (M.enc w r.1) r.2.1, M.ell.app r.2.1,
   libraReal M.n M.d M.c ρ (M.rounds w r.1) r.2.2⟩

/-- Simulator: no witness argument. -/
def ZkHemModel.sim (M : ZkHemModel F) (ρ γ : F)
    (s : M.Obs × (M.Idx → F) × LibraCoins F) : ZkHemView M :=
  ⟨s.1, s.2.1,
   mul (sub (M.ell.app s.2.1) (mul (sub one γ) (M.evalOf s.1))) (LawfulField.inv γ),
   libraSim M.n M.d M.c ρ M.pubH (M.term s.1) s.2.2⟩

/-- **Perfect HVZK of the zk-Hem field view.** For `ρ ≠ 0`, `γ ≠ 0` and characteristic
    `≠ 2`, the honest view on uniform pad/blinding coins, companion word and Libra mask
    equals the simulator's view on uniform observations, word and coins. -/
theorem zkHem_perfect_hvzk_simulation [DecidableEq F] (M : ZkHemModel F)
    (h2 : add (one : F) one ≠ zero) (ρ γ : F) (hρ : ρ ≠ zero) (hγ : γ ≠ zero) :
    PerfectlySimulated (M.real ρ γ) (M.sim ρ γ) := by
  intro w
  refine ⟨⟨fun r => (M.obs w r.1, blend γ (M.enc w r.1) r.2.1,
      libraCoinsOf M.n M.d ρ (M.rounds w r.1) r.2.2),
    fun s => (M.obsInv w s.1, unblend γ (M.enc w (M.obsInv w s.1)) s.2.1,
      libraMaskOf M.n M.d ρ (M.rounds w (M.obsInv w s.1)) s.2.2), ?_, ?_⟩, ?_⟩
  · rintro ⟨κ, C, m⟩
    show (M.obsInv w (M.obs w κ),
        unblend γ (M.enc w (M.obsInv w (M.obs w κ))) (blend γ (M.enc w κ) C),
        libraMaskOf M.n M.d ρ (M.rounds w (M.obsInv w (M.obs w κ)))
          (libraCoinsOf M.n M.d ρ (M.rounds w κ) m)) = (κ, C, m)
    rw [M.obs_left, unblend_blend γ hγ]
    have hL := (libraCoinBij h2 M.n M.d ρ hρ (M.rounds w κ)).left_inv m
    show (κ, C, libraMaskOf M.n M.d ρ (M.rounds w κ) (libraCoinsOf M.n M.d ρ (M.rounds w κ) m)) =
      (κ, C, m)
    exact congrArg (fun x => (κ, C, x)) hL
  · rintro ⟨o, U, s⟩
    show (M.obs w (M.obsInv w o),
        blend γ (M.enc w (M.obsInv w o)) (unblend γ (M.enc w (M.obsInv w o)) U),
        libraCoinsOf M.n M.d ρ (M.rounds w (M.obsInv w o))
          (libraMaskOf M.n M.d ρ (M.rounds w (M.obsInv w o)) s)) = (o, U, s)
    rw [M.obs_right, blend_unblend γ hγ]
    have hR := (libraCoinBij h2 M.n M.d ρ hρ (M.rounds w (M.obsInv w o))).right_inv s
    exact congrArg (fun x => (o, U, x)) hR
  · rintro ⟨κ, C, m⟩
    have hi := LawfulField.mul_inv_cancel hγ
    have hσ : M.ell.app C =
        mul (sub (M.ell.app (blend γ (M.enc w κ) C))
          (mul (sub one γ) (M.evalOf (M.obs w κ)))) (LawfulField.inv γ) := by
      rw [blend_claim, ← M.eval_obs]
      generalize LawfulField.inv γ = j at hi
      have e : mul (sub (add (mul (sub one γ) (M.ell.app (M.enc w κ))) (mul γ (M.ell.app C)))
          (mul (sub one γ) (M.ell.app (M.enc w κ)))) j = mul (M.ell.app C) (mul γ j) := by
        constructive_ring
      rw [e, hi, LawfulCommRing.mul_one]
    have hL : libraReal M.n M.d M.c ρ (M.rounds w κ) m =
        libraSim M.n M.d M.c ρ M.pubH (M.term (M.obs w κ))
          (libraCoinsOf M.n M.d ρ (M.rounds w κ) m) := by
      rw [libra_real_eq_sim h2 M.n M.d M.c ρ hρ (M.rounds w κ) (M.rounds_honest w κ) m,
        M.rounds_claim, M.rounds_term]
    show (⟨M.obs w κ, blend γ (M.enc w κ) C, M.ell.app C,
        libraReal M.n M.d M.c ρ (M.rounds w κ) m⟩ : ZkHemView M) =
      ⟨M.obs w κ, blend γ (M.enc w κ) C,
        mul (sub (M.ell.app (blend γ (M.enc w κ) C))
          (mul (sub one γ) (M.evalOf (M.obs w κ)))) (LawfulField.inv γ),
        libraSim M.n M.d M.c ρ M.pubH (M.term (M.obs w κ))
          (libraCoinsOf M.n M.d ρ (M.rounds w κ) m)⟩
    rw [← hσ, ← hL]

/-- Any two witnesses give the same distribution of views. -/
theorem zkHem_witness_indistinguishable [DecidableEq F] (M : ZkHemModel F)
    (h2 : add (one : F) one ≠ zero) (ρ γ : F) (hρ : ρ ≠ zero) (hγ : γ ≠ zero) (w w' : M.Wit) :
    ∃ φ : Bij (M.Coin × (M.Idx → F) × LibraMask F) (M.Coin × (M.Idx → F) × LibraMask F),
      ∀ r, M.real ρ γ w r = M.real ρ γ w' (φ.toFun r) :=
  (zkHem_perfect_hvzk_simulation M h2 ρ γ hρ hγ).witness_indistinguishable w w'

end Composed

/-- With `γ = 0` the blended word is the stage-0 word itself: witnesses with different
    stage-0 words have different views under all coins. -/
theorem tooth_zero_blend_challenge_reveals_word {F : Type} [LawfulField F] (M : ZkHemModel F)
    (ρ : F) (w w' : M.Wit) (r r' : M.Coin × (M.Idx → F) × LibraMask F)
    (h : M.enc w r.1 ≠ M.enc w' r'.1) :
    ¬ (M.real ρ zero w r = M.real ρ zero w' r') := by
  intro hEq
  have hW := congrArg ZkHemView.word hEq
  have e : ∀ (B C : M.Idx → F), blend zero B C = B := fun B C => by
    funext i
    show add (mul (sub one zero) (B i)) (mul zero (C i)) = B i
    constructive_ring
  have hW' : blend zero (M.enc w r.1) r.2.1 = blend zero (M.enc w' r'.1) r'.2.1 := hW
  rw [e, e] at hW'
  exact h hW'

/-! ## §7. Opened stage-0 symbols: `q` blinding coefficients against `q` distinct points -/

section Blinding
variable {F : Type} [LawfulField F]
open RoundPoly

/-- Coefficients of `y + (X - x) q(X)`. -/
def unquot (x : F) : F → List F → List F
  | y, [] => [y]
  | y, q0 :: qs => sub y (mul x q0) :: unquot x q0 qs

theorem unquot_length (x : F) : ∀ (y : F) (q : List F), (unquot x y q).length = q.length + 1
  | _, [] => rfl
  | _, q0 :: qs => by
    show (unquot x q0 qs).length + 1 = qs.length + 1 + 1
    rw [unquot_length x q0 qs]

theorem evalCoeffs_unquot (x : F) : ∀ (y : F) (q : List F) (t : F),
    evalCoeffs (unquot x y q) t = add y (mul (sub t x) (evalCoeffs q t))
  | y, [], t => by
    show add y (mul t zero) = add y (mul (sub t x) zero)
    constructive_ring
  | y, q0 :: qs, t => by
    show add (sub y (mul x q0)) (mul t (evalCoeffs (unquot x q0 qs) t)) =
      add y (mul (sub t x) (add q0 (mul t (evalCoeffs qs t))))
    rw [evalCoeffs_unquot x q0 qs t]
    constructive_ring

theorem unquot_quotLinear (x : F) : ∀ (cs : List F), cs ≠ [] →
    unquot x (evalCoeffs cs x) (quotLinear cs x) = cs
  | [], h => absurd rfl h
  | [c0], _ => by
    show [add c0 (mul x zero)] = [c0]
    have e : add c0 (mul x zero) = c0 := by constructive_ring
    rw [e]
  | c0 :: c1 :: cs, _ => by
    show sub (add c0 (mul x (evalCoeffs (c1 :: cs) x))) (mul x (evalCoeffs (c1 :: cs) x)) ::
      unquot x (evalCoeffs (c1 :: cs) x) (quotLinear (c1 :: cs) x) = c0 :: c1 :: cs
    rw [unquot_quotLinear x (c1 :: cs) (List.cons_ne_nil _ _)]
    have e : sub (add c0 (mul x (evalCoeffs (c1 :: cs) x))) (mul x (evalCoeffs (c1 :: cs) x)) =
        c0 := by constructive_ring
    rw [e]

/-- Divided differences against the first point. -/
def divDiff (x y : F) : List F → List F → List F
  | xi :: xs, yi :: ys => mul (sub yi y) (LawfulField.inv (sub xi x)) :: divDiff x y xs ys
  | _, _ => []

theorem divDiff_length (x y : F) : ∀ (xs ys : List F), xs.length = ys.length →
    (divDiff x y xs ys).length = xs.length
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | _ :: xs, _ :: ys, h => by
    show (divDiff x y xs ys).length + 1 = xs.length + 1
    rw [divDiff_length x y xs ys (Nat.succ.inj h)]

/-- Newton interpolation: the coefficient list of length `|xs|` with values `ys` at `xs`. -/
def interp : List F → List F → List F
  | x :: xs, y :: ys => unquot x y (interp xs (divDiff x y xs ys))
  | _, _ => []

theorem interp_length : ∀ (xs ys : List F), xs.length = ys.length →
    (interp xs ys).length = xs.length
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: xs, y :: ys, h => by
    show (unquot x y (interp xs (divDiff x y xs ys))).length = xs.length + 1
    rw [unquot_length, interp_length xs (divDiff x y xs ys)
      (divDiff_length x y xs ys (Nat.succ.inj h)).symm]

def evalAll (cs xs : List F) : List F := xs.map (evalCoeffs cs)

theorem undo_divDiff (x y : F) (g : F → F) : ∀ (xs ys : List F), xs.length = ys.length →
    (∀ t ∈ xs, t ≠ x) → xs.map g = divDiff x y xs ys →
    xs.map (fun t => add y (mul (sub t x) (g t))) = ys
  | [], [], _, _, _ => rfl
  | [], _ :: _, h, _, _ => by cases h
  | _ :: _, [], h, _, _ => by cases h
  | t :: xs, yi :: ys, h, hx, hg => by
    have hg' : g t :: xs.map g =
        mul (sub yi y) (LawfulField.inv (sub t x)) :: divDiff x y xs ys := hg
    obtain ⟨h0, hTail⟩ := List.cons.inj hg'
    have hne : sub t x ≠ zero := fun h0' =>
      hx t (List.mem_cons_self) (LawfulCommRing.sub_eq_zero_iff.mp h0')
    have hi := LawfulField.mul_inv_cancel hne
    show add y (mul (sub t x) (g t)) :: xs.map (fun t => add y (mul (sub t x) (g t))) = yi :: ys
    rw [undo_divDiff x y g xs ys (Nat.succ.inj h)
      (fun t' ht' => hx t' (List.mem_cons_of_mem _ ht')) hTail, h0]
    generalize LawfulField.inv (sub t x) = j at hi
    have e : add y (mul (sub t x) (mul (sub yi y) j)) =
        add y (mul (sub yi y) (mul (sub t x) j)) := by constructive_ring
    rw [e, hi]
    have e2 : add y (mul (sub yi y) one) = yi := by constructive_ring
    rw [e2]

theorem evalAll_interp : ∀ (xs ys : List F), xs.Nodup → xs.length = ys.length →
    evalAll (interp xs ys) xs = ys
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h
  | x :: xs, y :: ys, hnd, h => by
    obtain ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
    have hlen : xs.length = (divDiff x y xs ys).length :=
      (divDiff_length x y xs ys (Nat.succ.inj h)).symm
    have ih := evalAll_interp xs (divDiff x y xs ys) hnd' hlen
    have hTail := undo_divDiff x y (evalCoeffs (interp xs (divDiff x y xs ys))) xs ys
      (Nat.succ.inj h) (fun t ht hEq => hx (hEq ▸ ht)) ih
    show evalCoeffs (unquot x y (interp xs (divDiff x y xs ys))) x ::
      xs.map (evalCoeffs (unquot x y (interp xs (divDiff x y xs ys)))) = y :: ys
    have hFun : evalCoeffs (unquot x y (interp xs (divDiff x y xs ys))) =
        fun t => add y (mul (sub t x) (evalCoeffs (interp xs (divDiff x y xs ys)) t)) :=
      funext (fun t => evalCoeffs_unquot x y _ t)
    rw [hFun, hTail]
    have e : add y (mul (sub x x) (evalCoeffs (interp xs (divDiff x y xs ys)) x)) = y := by
      constructive_ring
    show add y (mul (sub x x) (evalCoeffs (interp xs (divDiff x y xs ys)) x)) :: ys = y :: ys
    rw [e]

theorem divDiff_evalAll (x : F) (cs : List F) : ∀ (xs : List F), (∀ t ∈ xs, t ≠ x) →
    divDiff x (evalCoeffs cs x) xs (xs.map (evalCoeffs cs)) =
      xs.map (evalCoeffs (quotLinear cs x))
  | [], _ => rfl
  | t :: xs, hx => by
    have hne : sub t x ≠ zero := fun h0 =>
      hx t (List.mem_cons_self) (LawfulCommRing.sub_eq_zero_iff.mp h0)
    have hi := LawfulField.mul_inv_cancel hne
    show mul (sub (evalCoeffs cs t) (evalCoeffs cs x)) (LawfulField.inv (sub t x)) ::
      divDiff x (evalCoeffs cs x) xs (xs.map (evalCoeffs cs)) =
      evalCoeffs (quotLinear cs x) t :: xs.map (evalCoeffs (quotLinear cs x))
    rw [divDiff_evalAll x cs xs (fun t' ht' => hx t' (List.mem_cons_of_mem _ ht')),
      evalCoeffs_eq_mul_quotLinear_add cs x t]
    generalize LawfulField.inv (sub t x) = j at hi
    have e : mul (sub (add (mul (sub t x) (evalCoeffs (quotLinear cs x) t)) (evalCoeffs cs x))
        (evalCoeffs cs x)) j = mul (evalCoeffs (quotLinear cs x) t) (mul (sub t x) j) := by
      constructive_ring
    rw [e, hi, LawfulCommRing.mul_one]

theorem interp_evalAll : ∀ (xs cs : List F), xs.Nodup → cs.length = xs.length →
    interp xs (evalAll cs xs) = cs
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by cases h
  | x :: xs, cs, hnd, h => by
    obtain ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
    have hcs : cs ≠ [] := fun h0 => by
      rw [h0] at h
      cases h
    have hq : (quotLinear cs x).length = xs.length := by
      rw [quotLinear_length, h]
      rfl
    show unquot x (evalCoeffs cs x)
      (interp xs (divDiff x (evalCoeffs cs x) xs (xs.map (evalCoeffs cs)))) = cs
    rw [divDiff_evalAll x cs xs (fun t ht hEq => hx (hEq ▸ ht))]
    have ih := interp_evalAll xs (quotLinear cs x) hnd' hq
    have ih' : interp xs (xs.map (evalCoeffs (quotLinear cs x))) = quotLinear cs x := ih
    rw [ih', unquot_quotLinear x cs hcs]

/-- **`q`-wise independence.** For `q` pairwise distinct points, evaluation is a bijection
    between blinding polynomials with `q` coefficients and vectors of `q` opened values. -/
def blindingEvalBij (xs : List F) (hnd : xs.Nodup) :
    Bij {cs : List F // cs.length = xs.length} {ys : List F // ys.length = xs.length} where
  toFun cs := ⟨evalAll cs.1 xs, List.length_map _⟩
  invFun ys := ⟨interp xs ys.1, interp_length xs ys.1 ys.2.symm⟩
  left_inv cs := Subtype.ext (interp_evalAll xs cs.1 hnd cs.2)
  right_inv ys := Subtype.ext (evalAll_interp xs ys.1 hnd ys.2.symm)

def vadd : List F → List F → List F
  | a :: as, b :: bs => add a b :: vadd as bs
  | _, _ => []

def vsub : List F → List F → List F
  | a :: as, b :: bs => sub a b :: vsub as bs
  | _, _ => []

theorem vadd_length : ∀ (as bs : List F), as.length = bs.length → (vadd as bs).length = bs.length
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | _ :: as, _ :: bs, h => by
    show (vadd as bs).length + 1 = bs.length + 1
    rw [vadd_length as bs (Nat.succ.inj h)]

theorem vsub_length : ∀ (as bs : List F), as.length = bs.length → (vsub as bs).length = bs.length
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | _ :: as, _ :: bs, h => by
    show (vsub as bs).length + 1 = bs.length + 1
    rw [vsub_length as bs (Nat.succ.inj h)]

theorem vsub_vadd : ∀ (v e : List F), v.length = e.length → vsub (vadd v e) v = e
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | a :: v, b :: e, h => by
    show sub (add a b) a :: vsub (vadd v e) v = b :: e
    rw [vsub_vadd v e (Nat.succ.inj h)]
    have e1 : sub (add a b) a = b := by constructive_ring
    rw [e1]

theorem vadd_vsub : ∀ (v o : List F), v.length = o.length → vadd v (vsub o v) = o
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | a :: v, b :: o, h => by
    show add a (sub b a) :: vadd v (vsub o v) = b :: o
    rw [vadd_vsub v o (Nat.succ.inj h)]
    have e1 : add a (sub b a) = b := by constructive_ring
    rw [e1]

/-- The opened stage-0 symbols `v_i + R(x_i)` at `q` distinct points, for a blinding
    polynomial `R` with `q` uniform coefficients, are `q` uniform field elements. -/
theorem opened_symbols_perfectly_simulated (xs : List F) (hnd : xs.Nodup) :
    PerfectlySimulated
      (fun (v : {v : List F // v.length = xs.length})
        (r : {cs : List F // cs.length = xs.length}) => vadd v.1 (evalAll r.1 xs))
      (fun (o : {ys : List F // ys.length = xs.length}) => o.1) := by
  intro v
  have hE : ∀ r : {cs : List F // cs.length = xs.length}, v.1.length = (evalAll r.1 xs).length :=
    fun r => v.2.trans (List.length_map _).symm
  refine ⟨⟨fun r => ⟨vadd v.1 (evalAll r.1 xs), (vadd_length _ _ (hE r)).trans (List.length_map _)⟩,
    fun o => (blindingEvalBij xs hnd).invFun
      ⟨vsub o.1 v.1, (vsub_length _ _ (o.2.trans v.2.symm)).trans v.2⟩, fun r => ?_, fun o => ?_⟩,
    fun _ => rfl⟩
  · have h1 : (⟨vsub (vadd v.1 (evalAll r.1 xs)) v.1,
        (vsub_length _ _ (((vadd_length _ _ (hE r)).trans (List.length_map _)).trans
          v.2.symm)).trans v.2⟩ : {ys : List F // ys.length = xs.length}) =
        (blindingEvalBij xs hnd).toFun r := Subtype.ext (vsub_vadd _ _ (hE r))
    show (blindingEvalBij xs hnd).invFun _ = r
    rw [h1]
    exact (blindingEvalBij xs hnd).left_inv r
  · apply Subtype.ext
    show vadd v.1 (evalAll (interp xs (vsub o.1 v.1)) xs) = o.1
    rw [evalAll_interp xs _ hnd ((vsub_length _ _ (o.2.trans v.2.symm)).trans v.2).symm]
    exact vadd_vsub v.1 o.1 (v.2.trans o.2.symm)

end Blinding

/-! ## §8. Soundness of the two mask challenges and extraction -/

section Soundness
variable {F : Type} [LawfulField F] [DecidableEq F]

/-- Batched sum claim: `∑ (f + ρ g) = H + ρ G` on the committed sums. -/
@[expose] def libraCheck (sumF H sumG G ρ : F) : Prop :=
  add sumF (mul ρ sumG) = add H (mul ρ G)

/-- Blended evaluation claim: `⟨U_γ, t⟩ = (1 - γ) b + γ σ` on the committed words. -/
@[expose] def companionCheck (evB b evC σ γ : F) : Prop :=
  add (mul (sub one γ) evB) (mul γ evC) = add (mul (sub one γ) b) (mul γ σ)

instance instDecidableLibraCheck (sumF H sumG G ρ : F) :
    Decidable (libraCheck sumF H sumG G ρ) :=
  inferInstanceAs (Decidable (add sumF (mul ρ sumG) = add H (mul ρ G)))

instance instDecidableCompanionCheck (evB b evC σ γ : F) :
    Decidable (companionCheck evB b evC σ γ) :=
  inferInstanceAs
    (Decidable (add (mul (sub one γ) evB) (mul γ evC) = add (mul (sub one γ) b) (mul γ σ)))

/-- An affine function with two distinct roots is zero. -/
theorem affine_two_roots_zero (a b x y : F) (hne : x ≠ y)
    (hx : add a (mul x b) = zero) (hy : add a (mul y b) = zero) : a = zero ∧ b = zero := by
  have e : mul (sub x y) b = sub (add a (mul x b)) (add a (mul y b)) := by constructive_ring
  rw [hx, hy, LawfulCommRing.sub_self] at e
  have hb : b = zero := by
    rcases LawfulField.mul_eq_zero e with h | h
    · exact absurd (LawfulCommRing.sub_eq_zero_iff.mp h) hne
    · exact h
  refine ⟨?_, hb⟩
  rw [hb] at hx
  have e2 : a = add a (mul x zero) := by constructive_ring
  exact e2.trans hx

theorem affine_root_unique (a b x y : F) (ha : a ≠ zero)
    (hx : add a (mul x b) = zero) (hy : add a (mul y b) = zero) : x = y :=
  if h : x = y then h else absurd (affine_two_roots_zero a b x y h hx hy).1 ha

omit [DecidableEq F] in
theorem libraCheck_zero_form (sumF H sumG G ρ : F) (h : libraCheck sumF H sumG G ρ) :
    add (sub sumF H) (mul ρ (sub sumG G)) = zero := by
  have e : add (sub sumF H) (mul ρ (sub sumG G)) =
      sub (add sumF (mul ρ sumG)) (add H (mul ρ G)) := by constructive_ring
  rw [e, h, LawfulCommRing.sub_self]

omit [DecidableEq F] in
theorem companionCheck_zero_form (evB b evC σ γ : F) (h : companionCheck evB b evC σ γ) :
    add (sub evB b) (mul γ (sub (sub evC σ) (sub evB b))) = zero := by
  have e : add (sub evB b) (mul γ (sub (sub evC σ) (sub evB b))) =
      sub (add (mul (sub one γ) evB) (mul γ evC)) (add (mul (sub one γ) b) (mul γ σ)) := by
    constructive_ring
  rw [e, h, LawfulCommRing.sub_self]

/-- **Extraction for the Libra batching challenge.** Two accepting challenges for the same
    committed sums force both sum claims. -/
theorem libra_special_soundness (sumF H sumG G ρ ρ' : F) (hne : ρ ≠ ρ')
    (h : libraCheck sumF H sumG G ρ) (h' : libraCheck sumF H sumG G ρ') :
    sumF = H ∧ sumG = G := by
  obtain ⟨ha, hb⟩ := affine_two_roots_zero _ _ ρ ρ' hne
    (libraCheck_zero_form sumF H sumG G ρ h) (libraCheck_zero_form sumF H sumG G ρ' h')
  exact ⟨LawfulCommRing.sub_eq_zero_iff.mp ha, LawfulCommRing.sub_eq_zero_iff.mp hb⟩

/-- **Extraction for the companion challenge.** Two accepting blend challenges for the same
    committed pair `(B, C)` force both evaluation claims. -/
theorem companion_special_soundness (evB b evC σ γ γ' : F) (hne : γ ≠ γ')
    (h : companionCheck evB b evC σ γ) (h' : companionCheck evB b evC σ γ') :
    evB = b ∧ evC = σ := by
  obtain ⟨ha, hb⟩ := affine_two_roots_zero _ _ γ γ' hne
    (companionCheck_zero_form evB b evC σ γ h) (companionCheck_zero_form evB b evC σ γ' h')
  have hB : evB = b := LawfulCommRing.sub_eq_zero_iff.mp ha
  refine ⟨hB, LawfulCommRing.sub_eq_zero_iff.mp ?_⟩
  have e : sub evC σ = add (sub (sub evC σ) (sub evB b)) (sub evB b) := by constructive_ring
  rw [e, hb, ha, LawfulCommRing.add_zero]

omit [DecidableEq F] in
/-- **Uncommitted companion.** If the companion claim `σ` may be chosen after `γ`, every
    evaluation claim `b`, true or false, passes for every `γ ≠ 0`. -/
theorem tooth_uncommitted_companion_forges_arbitrary_statement (evB b evC γ : F)
    (hγ : γ ≠ zero) : ∃ σ : F, companionCheck evB b evC σ γ := by
  have hi := LawfulField.mul_inv_cancel hγ
  refine ⟨add evC (mul (mul (sub one γ) (sub evB b)) (LawfulField.inv γ)), ?_⟩
  unfold companionCheck
  generalize LawfulField.inv γ = j at hi
  have e : add (mul (sub one γ) b) (mul γ (add evC (mul (mul (sub one γ) (sub evB b)) j))) =
      add (add (mul (sub one γ) b) (mul γ evC)) (mul (mul (sub one γ) (sub evB b)) (mul γ j)) := by
    constructive_ring
  rw [e, hi]
  constructive_ring

omit [DecidableEq F] in
/-- The same for the mask sum `G` chosen after `ρ`. -/
theorem tooth_uncommitted_mask_sum_forges_arbitrary_claim (sumF H sumG ρ : F)
    (hρ : ρ ≠ zero) : ∃ G : F, libraCheck sumF H sumG G ρ := by
  have hi := LawfulField.mul_inv_cancel hρ
  refine ⟨add sumG (mul (sub sumF H) (LawfulField.inv ρ)), ?_⟩
  unfold libraCheck
  generalize LawfulField.inv ρ = j at hi
  have e : add H (mul ρ (add sumG (mul (sub sumF H) j))) =
      add (add H (mul ρ sumG)) (mul (sub sumF H) (mul ρ j)) := by constructive_ring
  rw [e, hi]
  constructive_ring

/-- Committed data of the two mask reductions: true Boolean sums of `f` and `g`, the public
    sum claim `H`, true evaluations of `B` and `C`, and the evaluation claim `b`. -/
structure MaskStmt (F : Type) where
  sumF : F
  H : F
  sumG : F
  evB : F
  b : F
  evC : F

/-- Two-round public-coin protocol. Round 0: the prover sends the mask sum `G`, the verifier
    draws `ρ ∈ S`. Round 1: the prover sends the companion claim `σ`, the verifier draws
    `γ ∈ S`. The final checks are the two batched claims on the committed data. -/
def maskIop (S : List F) (hS : 0 < S.length) : PublicCoinIop (MaskStmt F) F 2 where
  challengeCard := fun _ => S.length
  h_chal_pos := fun _ => hS
  inLang := fun x => x.sumF = x.H ∧ x.evB = x.b
  verify := fun x tr =>
    match tr with
    | [(G, i), (σ, j)] =>
      decide (libraCheck x.sumF x.H x.sumG G (S.getD i zero)) &&
        decide (companionCheck x.evB x.b x.evC σ (S.getD j zero))
    | _ => false

def maskLive (S : List F) (x : MaskStmt F) (tr : List (F × Nat)) : Prop :=
  match tr with
  | [] => x.sumF = x.H ∧ x.evB = x.b
  | [(G, i)] => libraCheck x.sumF x.H x.sumG G (S.getD i zero) ∧ x.evB = x.b
  | [(G, i), (σ, j)] =>
    libraCheck x.sumF x.H x.sumG G (S.getD i zero) ∧
      companionCheck x.evB x.b x.evC σ (S.getD j zero)
  | _ => False

omit [LawfulField F] [DecidableEq F] in
theorem length_le_one_of_all_eq {α : Type} : ∀ (L : List α), L.Nodup →
    (∀ a ∈ L, ∀ b ∈ L, a = b) → L.length ≤ 1
  | [], _, _ => Nat.zero_le _
  | [_], _, _ => Nat.le_refl _
  | a :: b :: l, hnd, h => by
    have hab := h a (List.mem_cons_self) b (List.mem_cons_of_mem _ (List.mem_cons_self))
    have hna := (List.nodup_cons.mp hnd).1
    rw [hab] at hna
    exact absurd (List.mem_cons_self) hna

omit [LawfulField F] [DecidableEq F] in
theorem getD_mem_of_lt {α : Type} (d : α) : ∀ (S : List α) (i : Nat), i < S.length →
    S.getD i d ∈ S
  | [], i, h => absurd h (Nat.not_lt_zero i)
  | _ :: _, 0, _ => List.mem_cons_self
  | a :: S, i + 1, h =>
    List.mem_cons_of_mem a (getD_mem_of_lt d S i (Nat.lt_of_succ_lt_succ h))

omit [LawfulField F] [DecidableEq F] in
theorem getD_inj_of_nodup {α : Type} (d : α) : ∀ (S : List α), S.Nodup →
    ∀ (i j : Nat), i < S.length → j < S.length → S.getD i d = S.getD j d → i = j
  | [], _, i, _, hi, _, _ => absurd hi (Nat.not_lt_zero i)
  | a :: S, hnd, i, j, hi, hj, h => by
    obtain ⟨ha, hnd'⟩ := List.nodup_cons.mp hnd
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        have hm := getD_mem_of_lt d S j (Nat.lt_of_succ_lt_succ hj)
        have h' : a = S.getD j d := h
        rw [← h'] at hm
        exact absurd hm ha
    | succ i =>
      cases j with
      | zero =>
        have hm := getD_mem_of_lt d S i (Nat.lt_of_succ_lt_succ hi)
        have h' : S.getD i d = a := h
        rw [h'] at hm
        exact absurd hm ha
      | succ j =>
        have h' : S.getD i d = S.getD j d := h
        rw [getD_inj_of_nodup d S hnd' i j (Nat.lt_of_succ_lt_succ hi)
          (Nat.lt_of_succ_lt_succ hj) h']

theorem mask_round_flip_bound (S : List F) (hNd : S.Nodup) (x : MaskStmt F) (r : Fin 2)
    (pref : List (F × Nat)) (m : F) (hLen : pref.length = r.1)
    (hDoomed : ¬ maskLive S x pref)
    (L : List (Fin S.length)) (hL : L.Nodup)
    (hLive : ∀ ch ∈ L, ¬¬ maskLive S x (pref ++ [(m, ch.1)])) : L.length ≤ 1 := by
  apply length_le_one_of_all_eq L hL
  intro ch hch ch' hch'
  apply Fin.ext
  apply getD_inj_of_nodup zero S hNd ch.1 ch'.1 ch.2 ch'.2
  obtain ⟨r, hr⟩ := r
  have hr01 : r = 0 ∨ r = 1 := by omega
  rcases hr01 with h0 | h1
  · subst h0
    have hNil : pref = [] := List.eq_nil_of_length_eq_zero hLen
    subst hNil
    have hA : libraCheck x.sumF x.H x.sumG m (S.getD ch.1 zero) ∧ x.evB = x.b :=
      Decidable.of_not_not (hLive ch hch)
    have hA' : libraCheck x.sumF x.H x.sumG m (S.getD ch'.1 zero) ∧ x.evB = x.b :=
      Decidable.of_not_not (hLive ch' hch')
    have hF : sub x.sumF x.H ≠ zero := fun h0 =>
      hDoomed ⟨LawfulCommRing.sub_eq_zero_iff.mp h0, hA.2⟩
    exact affine_root_unique _ _ _ _ hF (libraCheck_zero_form _ _ _ _ _ hA.1)
      (libraCheck_zero_form _ _ _ _ _ hA'.1)
  · subst h1
    rcases pref with _ | ⟨⟨G, i⟩, _ | ⟨q, tl⟩⟩
    · cases hLen
    · have hA : libraCheck x.sumF x.H x.sumG G (S.getD i zero) ∧
          companionCheck x.evB x.b x.evC m (S.getD ch.1 zero) :=
        Decidable.of_not_not (hLive ch hch)
      have hA' : libraCheck x.sumF x.H x.sumG G (S.getD i zero) ∧
          companionCheck x.evB x.b x.evC m (S.getD ch'.1 zero) :=
        Decidable.of_not_not (hLive ch' hch')
      have hB : sub x.evB x.b ≠ zero := fun h0 =>
        hDoomed ⟨hA.1, LawfulCommRing.sub_eq_zero_iff.mp h0⟩
      exact affine_root_unique _ _ _ _ hB (companionCheck_zero_form _ _ _ _ _ hA.2)
        (companionCheck_zero_form _ _ _ _ _ hA'.2)
    · simp only [List.length_cons] at hLen
      omega

/-- Round-by-round state function of the two mask challenges: each doomed state turns live
    on at most one challenge. -/
def maskRbr (S : List F) (hS : 0 < S.length) (hNd : S.Nodup) :
    RbrStateFunction (maskIop S hS) where
  Live := maskLive S
  badCard := fun _ => 1
  doomed_init := fun _ hNot hLive => hNot hLive
  accept_implies_live := fun x tr _ hVer => by
    rcases tr with _ | ⟨⟨G, i⟩, _ | ⟨⟨σ, j⟩, _ | ⟨q, tl⟩⟩⟩
    · exact Bool.noConfusion hVer
    · exact Bool.noConfusion hVer
    · have h : (decide (libraCheck x.sumF x.H x.sumG G (S.getD i zero)) &&
          decide (companionCheck x.evB x.b x.evC σ (S.getD j zero))) = true := hVer
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
      exact h
    · exact Bool.noConfusion hVer
  round_flip_bound := fun x r pref m hLen hDoomed L hL hLive =>
    mask_round_flip_bound S hNd x r pref m hLen hDoomed L hL hLive

/-- **State-restoration soundness of the mask rounds.** For committed data with a false sum
    claim or a false evaluation claim, any adaptive rewinding prover reaches an accepting
    transcript with probability at most `(number of rewinds) / |S|`: the Libra mask and the
    companion blend each add `1 / |S|` per visit to the soundness error of the protocol run
    on `f + ρ g` and `U_γ`. -/
theorem zkHem_mask_rounds_state_restoration_soundness (S : List F) (hS : 0 < S.length)
    (hNd : S.Nodup) (x : MaskStmt F) (hFalse : ¬ (x.sumF = x.H ∧ x.evB = x.b))
    (sched : List (Fin 2)) (tree : SrScheduleTree (maskIop S hS) sched) :
    RatBound.le (srTreeAcceptProb (maskIop S hS) tree x)
      (srScheduleErrorSum (maskRbr S hS hNd) sched) :=
  rbr_implies_state_restoration_soundness (maskRbr S hS hNd) x hFalse sched tree

/-- Completeness of the mask rounds: true claims with the honest `G` and `σ` pass on every
    pair of challenges. -/
theorem maskIop_honest_accepts (S : List F) (hS : 0 < S.length) (sumF sumG evB evC : F)
    (i j : Nat) :
    (maskIop S hS).verify ⟨sumF, sumF, sumG, evB, evB, evC⟩ [(sumG, i), (evC, j)] = true := by
  show (decide (libraCheck sumF sumF sumG sumG (S.getD i zero)) &&
    decide (companionCheck evB evB evC evC (S.getD j zero))) = true
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  exact ⟨rfl, rfl⟩

/-- One masked sumcheck round: a message whose Boolean sum differs from that of the true
    round polynomial agrees with it on at most `d` challenges. -/
theorem masked_sumcheck_round_flip_le_degree (d : Nat) (m t : List F)
    (hm : m.length ≤ d + 1) (ht : t.length ≤ d + 1)
    (hne : add (RoundPoly.evalCoeffs m zero) (RoundPoly.evalCoeffs m one) ≠
      add (RoundPoly.evalCoeffs t zero) (RoundPoly.evalCoeffs t one))
    (S : List F) (hS : S.Nodup) :
    (S.filter (fun c => decide (RoundPoly.evalCoeffs m c = RoundPoly.evalCoeffs t c))).length ≤ d := by
  letI : NoZeroDivisors F := LawfulField.toNoZeroDivisors F
  have hlen : (RoundPoly.subCoeffs m t).length ≤ d + 1 := by
    rw [RoundPoly.subCoeffs_length]
    exact Nat.max_le.mpr ⟨hm, ht⟩
  have hx : ∃ x₀ : F, RoundPoly.evalCoeffs (RoundPoly.subCoeffs m t) x₀ ≠ zero := by
    by_cases h0 : RoundPoly.evalCoeffs m zero = RoundPoly.evalCoeffs t zero
    · refine ⟨one, fun h1 => hne ?_⟩
      rw [RoundPoly.evalCoeffs_sub] at h1
      rw [h0, LawfulCommRing.sub_eq_zero_iff.mp h1]
    · refine ⟨zero, fun h1 => h0 ?_⟩
      rw [RoundPoly.evalCoeffs_sub] at h1
      exact LawfulCommRing.sub_eq_zero_iff.mp h1
  have hRoots := RoundPoly.roots_nodup_length_le d (RoundPoly.subCoeffs m t) S hS hlen hx
  have hFilt : S.filter (fun c => decide (RoundPoly.evalCoeffs m c = RoundPoly.evalCoeffs t c)) =
      S.filter (fun r => decide (RoundPoly.evalCoeffs (RoundPoly.subCoeffs m t) r = zero)) := by
    apply List.filter_congr
    intro c _
    rw [RoundPoly.evalCoeffs_sub]
    by_cases h : RoundPoly.evalCoeffs m c = RoundPoly.evalCoeffs t c
    · rw [decide_eq_true h, decide_eq_true (LawfulCommRing.sub_eq_zero_iff.mpr h)]
    · rw [decide_eq_false h,
        decide_eq_false (fun h' => h (LawfulCommRing.sub_eq_zero_iff.mp h'))]
  rw [hFilt]
  exact hRoots

end Soundness

/-- Algebraic discrepancy added by masking: `nv` masked sumcheck rounds of degree `d`
    (`masked_sumcheck_round_flip_le_degree`) and the two mask challenges (`maskRbr`), over
    challenges drawn from all of `F_{p^4}`. For `d ≤ 8`, `nv ≤ 30` it is below `2^-240`. -/
theorem zkHem_mask_discrepancy_below_2_pow_neg_240 (d nv : Nat) (hd : d ≤ 8) (hnv : nv ≤ 30) :
    (d * nv + 2) * 2 ^ 240 ≤ goldilocksPrime ^ 4 := by
  have h1 : d * nv + 2 ≤ 242 := by
    have := Nat.mul_le_mul hd hnv
    omega
  have h2 : 242 * 2 ^ 240 ≤ goldilocksPrime ^ 4 := by decide
  exact Nat.le_trans (Nat.mul_le_mul_right _ h1) h2

/-! ## §9. Instances: the interface is inhabited -/

/-- A one-round, degree-one honest witness transcript: `f(X) = f0 + f1 X`. -/
theorem honest_linear_round {F : Type} [LawfulField F] (f0 f1 : F) (c : Nat → F) :
    (⟨add (add f0 f0) f1, fun _ => f0, fun _ _ => f1⟩ : WitnessRounds F).Honest 1 1 c := by
  intro i hi
  have h0 : i = 0 := by omega
  subst h0
  show add (add f0 (mul zero (add f1 (mul zero zero)))) (add f0 (mul one (add f1 (mul one zero)))) =
    add (add f0 f0) f1
  constructive_ring

/-- Field structure of the certified tower, kept local to this module. -/
@[reducible] def fp4Field : LawfulField Fp4 where
  inv := GoldilocksField.GoldilocksExt4.inv
  zero_ne_one := fun h =>
    LawfulField.zero_ne_one (F := Fp2) (congrArg GoldilocksField.GoldilocksExt4.c0 h)
  mul_inv_cancel := fun {_} ha => (GoldilocksField.GoldilocksExt4.ext4_mul_inv_cancel ha).1

theorem fp4_two_ne_zero : add (one : Fp4) one ≠ zero := fun h =>
  fp_two_ne_zero (congrArg (fun z : Fp4 => z.c0.c0) h)

/-- One terminal operand `w ∈ F_{p^4}` padded with four base-field cells at a challenge
    outside `F_{p^2}`, with a zero-round sumcheck: an instance of `ZkHemModel`. -/
def padModel (z : Fp4) (hz : z.c1 ≠ zero) : @ZkHemModel Fp4 fp4Field :=
  letI := fp4Field
  { Wit := Fp4
    Coin := Pad
    Obs := Fp4
    Idx := Unit
    n := 0
    d := 0
    c := fun _ => zero
    pubH := zero
    enc := fun w κ _ => add w (padMap z κ)
    ell := LinForm.evalAt ()
    obs := fun w κ => add w (padMap z κ)
    obsInv := fun w o => padInv z (sub o w)
    obs_left := fun w κ => by
      have e : sub (add w (padMap z κ)) w = padMap z κ := by constructive_ring
      rw [e, padInv_padMap z hz]
    obs_right := fun w o => by
      rw [padMap_padInv z hz]
      constructive_ring
    evalOf := fun o => o
    eval_obs := fun _ _ => rfl
    term := fun _ => zero
    rounds := fun _ _ => ⟨zero, fun _ => zero, fun _ _ => zero⟩
    rounds_honest := fun _ _ i hi => absurd hi (Nat.not_lt_zero i)
    rounds_claim := fun _ _ => rfl
    rounds_term := fun _ _ => rfl }

/-- Perfect HVZK of the padded opening for every challenge outside `F_{p^2}`. -/
theorem zkHem_padded_opening_perfect_hvzk (z : Fp4) (hz : z.c1 ≠ zero) (ρ γ : Fp4)
    (hρ : ρ ≠ zero) (hγ : γ ≠ zero) :
    PerfectlySimulated (@ZkHemModel.real Fp4 fp4Field (padModel z hz) ρ γ)
      (@ZkHemModel.sim Fp4 fp4Field (padModel z hz) ρ γ) :=
  @zkHem_perfect_hvzk_simulation Fp4 fp4Field _ (padModel z hz) fp4_two_ne_zero ρ γ hρ hγ

/-- **Companion from four base-field words.** For a batching challenge `β ∉ F_{p^2}`, the
    word `B + β C_0 + β^2 C_1 + β^3 C_2 + β^4 C_3` with four uniform base-field companion
    words `C_j` (one `Pad` per index) is uniform over `F_{p^4}` whatever `B` is: the pad
    bijection of §1 applied at every index. -/
theorem batched_base_companion_perfectly_simulated {ι : Type} (β : Fp4) (hβ : β.c1 ≠ zero) :
    PerfectlySimulated
      (fun (B : ι → Fp4) (C : ι → Pad) => fun i => add (B i) (mul β (padMap β (C i))))
      (fun (U : ι → Fp4) => U) := by
  have hβ0 : β ≠ GoldilocksField.GoldilocksExt4.zero := fun h =>
    hβ (congrArg GoldilocksField.GoldilocksExt4.c1 h)
  have hi : mul β (GoldilocksField.GoldilocksExt4.inv β) = one :=
    (GoldilocksField.GoldilocksExt4.ext4_mul_inv_cancel hβ0).1
  intro B
  refine ⟨⟨fun C i => add (B i) (mul β (padMap β (C i))),
    fun U i => padInv β (mul (GoldilocksField.GoldilocksExt4.inv β) (sub (U i) (B i))),
    fun C => ?_, fun U => ?_⟩, fun _ => rfl⟩
  · funext i
    show padInv β (mul (GoldilocksField.GoldilocksExt4.inv β)
      (sub (add (B i) (mul β (padMap β (C i)))) (B i))) = C i
    generalize GoldilocksField.GoldilocksExt4.inv β = j at hi
    have e : mul j (sub (add (B i) (mul β (padMap β (C i)))) (B i)) =
        mul (padMap β (C i)) (mul β j) := by constructive_ring
    rw [e, hi, LawfulCommRing.mul_one, padInv_padMap β hβ]
  · funext i
    show add (B i) (mul β (padMap β (padInv β
      (mul (GoldilocksField.GoldilocksExt4.inv β) (sub (U i) (B i)))))) = U i
    rw [padMap_padInv β hβ]
    generalize GoldilocksField.GoldilocksExt4.inv β = j at hi
    have e : add (B i) (mul β (mul j (sub (U i) (B i)))) =
        add (B i) (mul (sub (U i) (B i)) (mul β j)) := by constructive_ring
    rw [e, hi]
    constructive_ring

theorem witness_primitive_challenge : ∃ z : Fp4, z.c1 ≠ zero :=
  ⟨GoldilocksField.GoldilocksExt4.vBasis, by decide⟩

/-! ## §10. Audit gates -/

#verify_constructive Qsag.ZkHem.quartic_primitive_pad_bijection Qsag.ZkHem.pad_full_rank_iff
  Qsag.ZkHem.padded_evaluation_perfectly_simulated
  Qsag.ZkHem.libra_real_eq_sim Qsag.ZkHem.libra_sumcheck_perfectly_simulated
  Qsag.ZkHem.salted_leaves_identical_until_bad Qsag.ZkHem.salted_leaf_digest_simulated
  Qsag.ZkHem.companion_blend_perfectly_simulated
  Qsag.ZkHem.blended_terminal_fold_perfectly_simulated
  Qsag.ZkHem.opened_symbols_perfectly_simulated
  Qsag.ZkHem.zkHem_perfect_hvzk_simulation Qsag.ZkHem.zkHem_witness_indistinguishable
  Qsag.ZkHem.zkHem_padded_opening_perfect_hvzk Qsag.ZkHem.honest_linear_round
  Qsag.ZkHem.batched_base_companion_perfectly_simulated
  Qsag.ZkHem.libra_special_soundness Qsag.ZkHem.companion_special_soundness
  Qsag.ZkHem.zkHem_mask_rounds_state_restoration_soundness Qsag.ZkHem.maskIop_honest_accepts
  Qsag.ZkHem.masked_sumcheck_round_flip_le_degree
  Qsag.ZkHem.zkHem_mask_discrepancy_below_2_pow_neg_240

#tooth_pair Qsag.ZkHem.quartic_primitive_pad_bijection vs
  Qsag.ZkHem.tooth_quadratic_subfield_pad_rank_deficient
#tooth_pair Qsag.ZkHem.padded_evaluation_perfectly_simulated vs
  Qsag.ZkHem.tooth_subfield_challenge_leaks_odd_coordinates
#tooth_pair Qsag.ZkHem.batched_base_companion_perfectly_simulated vs
  Qsag.ZkHem.tooth_quadratic_subfield_pad_rank_deficient
#tooth_pair Qsag.ZkHem.libra_sumcheck_perfectly_simulated vs
  Qsag.ZkHem.tooth_unmasked_sumcheck_round_leaks
#tooth_pair Qsag.ZkHem.blended_terminal_fold_perfectly_simulated vs
  Qsag.ZkHem.tooth_stage0_only_blinding_leaks_via_early_stop
#tooth_pair Qsag.ZkHem.blended_terminal_fold_perfectly_simulated vs
  Qsag.ZkHem.tooth_stage0_only_blinding_leaks_via_ood
#tooth_pair Qsag.ZkHem.salted_leaves_identical_until_bad vs
  Qsag.ZkHem.tooth_unsalted_leaf_confirms_guess
#tooth_pair Qsag.ZkHem.zkHem_perfect_hvzk_simulation vs
  Qsag.ZkHem.tooth_zero_blend_challenge_reveals_word
#tooth_pair Qsag.ZkHem.zkHem_mask_rounds_state_restoration_soundness vs
  Qsag.ZkHem.tooth_uncommitted_companion_forges_arbitrary_statement
#tooth_pair Qsag.ZkHem.zkHem_mask_rounds_state_restoration_soundness vs
  Qsag.ZkHem.tooth_uncommitted_mask_sum_forges_arbitrary_claim

end Qsag.ZkHem
end
