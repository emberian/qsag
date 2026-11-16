module
/-
# Qsag.Protocol.Aggregation.ZkHem — zk-Hem pads, masks, simulation and extraction

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
    queries a fresh hidden salt has the finite bound proved in §11; a complete multi-leaf
    collision and joint-view coupling theorem is still a separate obligation. `tooth_unsalted_leaf_confirms_guess`.
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
§9  `honest_linear_round`; the zero-round `padModel` fixture lives in Tests/AggregationParityTeeth.
    `batched_base_companion_perfectly_simulated`: four base-field companion words batched
    with a challenge outside `F_{p^2}` mask a word over `F_{p^4}` perfectly.
§10 Boolean-cube multilinear extensions and the degree-9/degree-2 honest sumcheck prover.
§11 Public Hem uses one assignment table on `varBits`. Its matrix multiplication, row
    constraint sumcheck, and variable-subcube column sumcheck are connected by proved claim
    identities and degree-specific flip counts. Twelve base-field masking cells in three
    four-corner groups jointly pad the revealed row triple; the group determinant is
    `k₁ k₂ k₃`, with an explicit inverse and inhabited full-rank corner bases.
    `five_table_kernel_view_perfectly_simulated` jointly simulates the blended word and
    all four companion claims against a fixed public reference assignment with the same
    kernel value. The column transcript lemma omits the two unexposed terminal operands.
    These results do not yet construct the deployed five-table joint HVZK simulator.
-/

public import Init.Data.List.FinRange
public import Qsag.Coding.WelchBerlekampDecoder
public import Qsag.Math.QuarticExt4
public import Qsag.Coding.Cwyz26
public import Qsag.Protocol.Aggregation.MultiRoundFsQrom
public import Qsag.Protocol.Aggregation.HemRbrSoundness
public import Qsag.Math.Tactic.CommRing
public import Qsag.Math.Tactic.MaskBijection
public import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.ZkHem

set_option autoImplicit false
open CommRingOps

abbrev Fp := Goldilocks
abbrev Fp2 := GoldilocksExt2
abbrev Fp4 := GoldilocksField.GoldilocksExt4

/-! ## §0. Coordinate formulas of the tower -/

theorem fp2_add_c0 (x y : Fp2) : (add x y).c0 = add x.c0 y.c0 := GoldilocksExt2.add_c0 x y
theorem fp2_add_c1 (x y : Fp2) : (add x y).c1 = add x.c1 y.c1 := GoldilocksExt2.add_c1 x y
theorem fp2_sub_c0 (x y : Fp2) : (sub x y).c0 = sub x.c0 y.c0 := GoldilocksExt2.sub_c0 x y
theorem fp2_sub_c1 (x y : Fp2) : (sub x y).c1 = sub x.c1 y.c1 := GoldilocksExt2.sub_c1 x y
theorem fp2_neg_c0 (x : Fp2) : (neg x).c0 = neg x.c0 := GoldilocksExt2.neg_c0 x
theorem fp2_neg_c1 (x : Fp2) : (neg x).c1 = neg x.c1 := GoldilocksExt2.neg_c1 x
theorem fp2_mul_c0 (x y : Fp2) :
    (mul x y).c0 = add (mul x.c0 y.c0) (mul GoldilocksExt2.nonResidue (mul x.c1 y.c1)) :=
  GoldilocksExt2.mul_c0 x y
theorem fp2_mul_c1 (x y : Fp2) : (mul x y).c1 = add (mul x.c0 y.c1) (mul x.c1 y.c0) :=
  GoldilocksExt2.mul_c1 x y
theorem fp2_zero_c0 : (zero : Fp2).c0 = zero := GoldilocksExt2.ringZero_c0
theorem fp2_zero_c1 : (zero : Fp2).c1 = zero := GoldilocksExt2.ringZero_c1
theorem fp2_one_c0 : (one : Fp2).c0 = one := GoldilocksExt2.ringOne_c0
theorem fp2_one_c1 : (one : Fp2).c1 = zero := GoldilocksExt2.ringOne_c1
theorem fp2_u_c0 : GoldilocksExt2.uBasis.c0 = zero := GoldilocksExt2.uBasis_c0
theorem fp2_u_c1 : GoldilocksExt2.uBasis.c1 = one := GoldilocksExt2.uBasis_c1

theorem fp4_add_c0 (x y : Fp4) : (add x y).c0 = add x.c0 y.c0 := QuarticGoldilocks.add_c0 x y
theorem fp4_add_c1 (x y : Fp4) : (add x y).c1 = add x.c1 y.c1 := QuarticGoldilocks.add_c1 x y
theorem fp4_sub_c0 (x y : Fp4) : (sub x y).c0 = sub x.c0 y.c0 := QuarticGoldilocks.sub_c0 x y
theorem fp4_sub_c1 (x y : Fp4) : (sub x y).c1 = sub x.c1 y.c1 := QuarticGoldilocks.sub_c1 x y
theorem fp4_mul_c0 (x y : Fp4) :
    (mul x y).c0 = add (mul x.c0 y.c0) (mul GoldilocksExt2.uBasis (mul x.c1 y.c1)) :=
  QuarticGoldilocks.mul_c0 x y
theorem fp4_mul_c1 (x y : Fp4) : (mul x y).c1 = add (mul x.c0 y.c1) (mul x.c1 y.c0) :=
  QuarticGoldilocks.mul_c1 x y
theorem fp4_zero_c0 : (zero : Fp4).c0 = zero := QuarticGoldilocks.ringZero_c0
theorem fp4_zero_c1 : (zero : Fp4).c1 = zero := QuarticGoldilocks.ringZero_c1
theorem fp4_one_c0 : (one : Fp4).c0 = one := QuarticGoldilocks.ringOne_c0
theorem fp4_one_c1 : (one : Fp4).c1 = zero := QuarticGoldilocks.ringOne_c1

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
    exact ⟨(congrArg GoldilocksExt2.c0 h).trans fp2_zero_c0,
      (congrArg GoldilocksExt2.c1 h).trans fp2_zero_c1⟩
  · intro h
    exact GoldilocksExt2.ext (h.1.trans fp2_zero_c0.symm) (h.2.trans fp2_zero_c1.symm)

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
      fp4_mul_c1, GoldilocksField.GoldilocksExt4.c0, GoldilocksField.GoldilocksExt4.c1]
    constructive_ring
  · simp only [padMap, embed, padBeta, zS, zT, zN, fp4_add_c1, fp4_mul_c0, fp4_mul_c1,
      GoldilocksField.GoldilocksExt4.c0, GoldilocksField.GoldilocksExt4.c1]
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
  · simp only [GoldilocksField.GoldilocksExt4.norm,
      QuarticGoldilocks.norm_eq, GoldilocksField.GoldilocksExt4.c0, GoldilocksField.GoldilocksExt4.c1,
      padDet, zS, zW, zT, zN, fp2_sub_c0, fp2_sub_c1, fp2_mul_c0, fp2_mul_c1, fp2_add_c0,
      fp2_add_c1, fp2_u_c0, fp2_u_c1, GoldilocksExt2.ofBase_c0, GoldilocksExt2.ofBase_c1]
    constructive_ring
  · simp only [GoldilocksField.GoldilocksExt4.norm,
      QuarticGoldilocks.norm_eq, GoldilocksField.GoldilocksExt4.c0, GoldilocksField.GoldilocksExt4.c1,
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
        mul (GoldilocksExt2.ofBase (zT ⟨⟨a0, a1⟩, ⟨b0, b1⟩⟩).c1) ⟨b0, b1⟩⟩ : Fp4) = zero
  · have hX := (congrArg QuarticGoldilocks.c0 hXY).trans fp4_zero_c0
    have hY := (congrArg QuarticGoldilocks.c1 hXY).trans fp4_zero_c1
    have hτ : add a1 a1 = zero := by
      rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hY with h | h
      · have h0 := (congrArg GoldilocksExt2.c0 h).trans fp2_zero_c0
        rw [GoldilocksExt2.ofBase_c0] at h0
        exact (fp2_add_c1 _ _).symm.trans h0
      · exact absurd h hB
    have ha1 : a1 = zero := by
      have e : mul (add one one) a1 = add a1 a1 := by constructive_ring
      rw [hτ] at e
      rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero e with h | h
      · exact absurd h fp_two_ne_zero
      · exact h
    have hν : (zN ⟨⟨a0, a1⟩, ⟨b0, b1⟩⟩).c1 = zero := by
      have h0 := (congrArg GoldilocksExt2.c0 hX).trans fp2_zero_c0
      simp only [fp2_sub_c0, ofBase_mul_c0, GoldilocksExt2.ofBase_c0] at h0
      have hT : (zT ⟨⟨a0, a1⟩, ⟨b0, b1⟩⟩).c1 = zero := (fp2_add_c1 _ _).trans hτ
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
      exact hB (GoldilocksExt2.ext (hb0.trans fp2_zero_c0.symm) (hb1.trans fp2_zero_c1.symm))
    · have hi : mul b1 (Goldilocks.inv b1) = one := Goldilocks.mul_inv_cancel hb1
      generalize Goldilocks.inv b1 = i at hi
      have e : mul (mul b0 i) (mul b0 i) =
          sub (mul (add (mul b0 b0) (mul GoldilocksExt2.nonResidue (mul b1 b1))) (mul i i))
            (mul GoldilocksExt2.nonResidue (mul (mul b1 i) (mul b1 i))) := by constructive_ring
      rw [hsum, hi] at e
      have e2 : sub (mul (zero : Fp) (mul i i)) (mul GoldilocksExt2.nonResidue (mul one one)) =
          neg GoldilocksExt2.nonResidue := by constructive_ring
      exact neg_seven_not_square_in_goldilocks _ (e.trans e2)
  · exact GoldilocksField.GoldilocksExt4.norm_ne_zero
      (fun h => hXY (h.trans GoldilocksField.GoldilocksExt4.zero_eq_ringZero))
      (hNorm.trans ((congrArg GoldilocksExt2.ofBase Goldilocks.ring_zero).trans
        GoldilocksExt2.ofBase_zero))

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
  exact LawfulField.zero_ne_one (F := Fp2) (h1.symm.trans QuarticGoldilocks.vBasis_c1)

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

/-- `real w` on uniform prover coins `R` and `sim` on uniform simulator coins `C` are the same
    distribution for every witness `w`: a bijection of coins carries one onto the other. The
    simulator `sim` does not take `w`. -/
def PerfectlySimulated {W R C V : Type} (real : W → R → V) (sim : C → V) : Prop :=
  ∀ w : W, ∃ Φ : SimpleEquiv R C, ∀ r : R, real w r = sim (Φ.toFun r)

/-- Perfect simulation gives perfect witness indistinguishability. -/
theorem PerfectlySimulated.witness_indistinguishable {W R C V : Type}
    {real : W → R → V} {sim : C → V} (h : PerfectlySimulated real sim) (w w' : W) :
    ∃ φ : SimpleEquiv R R, ∀ r : R, real w r = real w' (φ.toFun r) := by
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
    (w : WitnessRounds F) : SimpleEquiv (LibraMask F) (LibraCoins F) where
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

