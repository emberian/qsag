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

/-! ## §5. Salted Merkle leaves in the random-oracle model -/

section SaltedLeaves
variable {F : Type} [LawfulField F] {S D A : Type}

/-- Re-key the oracle on every salt `s` by shifting the cell argument by `δ s`. -/
def saltShift (δ : S → F) (O : S × F → D) : S × F → D :=
  fun q => O (q.1, add q.2 (δ q.1))

/-- `saltShift δ` is a bijection of oracles: a uniform oracle stays uniform. -/
def saltShiftBij (δ : S → F) : SimpleEquiv (S × F → D) (S × F → D) where
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
    ∃ φ : SimpleEquiv (M.Coin × (M.Idx → F) × LibraMask F) (M.Coin × (M.Idx → F) × LibraMask F),
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
    SimpleEquiv {cs : List F // cs.length = xs.length} {ys : List F // ys.length = xs.length} where
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
@[reducible] def fp4Field : LawfulField Fp4 := inferInstance

theorem fp4_two_ne_zero : add (one : Fp4) one ≠ zero := fun h => by
  have h1 := congrArg (fun z : Fp4 => z.c0.c0) h
  simp only [fp4_add_c0, fp2_add_c0, fp4_one_c0, fp2_one_c0, fp4_zero_c0, fp2_zero_c0] at h1
  exact fp_two_ne_zero h1

/-- **Companion from four base-field words.** For a batching challenge `β ∉ F_{p^2}`, the
    word `B + β C_0 + β^2 C_1 + β^3 C_2 + β^4 C_3` with four uniform base-field companion
    words `C_j` (one `Pad` per index) is uniform over `F_{p^4}` whatever `B` is: the pad
    bijection of §1 applied at every index. -/
theorem batched_base_companion_perfectly_simulated {ι : Type} (β : Fp4) (hβ : β.c1 ≠ zero) :
    PerfectlySimulated
      (fun (B : ι → Fp4) (C : ι → Pad) => fun i => add (B i) (mul β (padMap β (C i))))
      (fun (U : ι → Fp4) => U) := by
  have hβ0 : β ≠ GoldilocksField.GoldilocksExt4.zero := fun h =>
    hβ ((congrArg GoldilocksField.GoldilocksExt4.c1
      (h.trans GoldilocksField.GoldilocksExt4.zero_eq_ringZero)).trans fp4_zero_c1)
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
  ⟨GoldilocksField.GoldilocksExt4.vBasis, fun h =>
    LawfulField.zero_ne_one (F := Fp2) (h.symm.trans QuarticGoldilocks.vBasis_c1)⟩

/-! ## §10. Boolean-cube sums, multilinear extensions and the honest sumcheck prover -/

section Cube
variable {F : Type} [LawfulField F]
open RoundPoly

/-- `0` and `1` as field elements. -/
def bitF : Bool → F
  | false => zero
  | true => one

/-- A Boolean point as a field point. -/
def bitPt (bs : List Bool) : List F := bs.map bitF

/-- Sum of `f` over `{0,1}^m`, first bit first. -/
def bitSum : Nat → (List Bool → F) → F
  | 0, f => f []
  | m + 1, f => add (bitSum m (fun bs => f (false :: bs))) (bitSum m (fun bs => f (true :: bs)))

theorem bitSum_congr : ∀ (m : Nat) (f g : List Bool → F),
    (∀ bs : List Bool, bs.length = m → f bs = g bs) → bitSum m f = bitSum m g
  | 0, _, _, h => h [] rfl
  | m + 1, f, g, h => by
    show add (bitSum m (fun bs => f (false :: bs))) (bitSum m (fun bs => f (true :: bs))) =
      add (bitSum m (fun bs => g (false :: bs))) (bitSum m (fun bs => g (true :: bs)))
    rw [bitSum_congr m (fun bs => f (false :: bs)) (fun bs => g (false :: bs))
        (fun bs hb => h (false :: bs) (congrArg Nat.succ hb)),
      bitSum_congr m (fun bs => f (true :: bs)) (fun bs => g (true :: bs))
        (fun bs hb => h (true :: bs) (congrArg Nat.succ hb))]

theorem bitSum_zero : ∀ m : Nat, bitSum m (fun _ => (zero : F)) = zero
  | 0 => by rfl
  | m + 1 => by
    show add (bitSum m (fun _ => (zero : F))) (bitSum m (fun _ => (zero : F))) = zero
    rw [bitSum_zero m]
    constructive_ring

theorem bitSum_add : ∀ (m : Nat) (f g : List Bool → F),
    bitSum m (fun bs => add (f bs) (g bs)) = add (bitSum m f) (bitSum m g)
  | 0, _, _ => by rfl
  | m + 1, f, g => by
    show add (bitSum m (fun bs => add (f (false :: bs)) (g (false :: bs))))
        (bitSum m (fun bs => add (f (true :: bs)) (g (true :: bs)))) =
      add (add (bitSum m (fun bs => f (false :: bs))) (bitSum m (fun bs => f (true :: bs))))
        (add (bitSum m (fun bs => g (false :: bs))) (bitSum m (fun bs => g (true :: bs))))
    rw [bitSum_add m (fun bs => f (false :: bs)) (fun bs => g (false :: bs)),
      bitSum_add m (fun bs => f (true :: bs)) (fun bs => g (true :: bs))]
    constructive_ring

theorem bitSum_mul_left (a : F) : ∀ (m : Nat) (f : List Bool → F),
    bitSum m (fun bs => mul a (f bs)) = mul a (bitSum m f)
  | 0, _ => by rfl
  | m + 1, f => by
    show add (bitSum m (fun bs => mul a (f (false :: bs))))
        (bitSum m (fun bs => mul a (f (true :: bs)))) =
      mul a (add (bitSum m (fun bs => f (false :: bs))) (bitSum m (fun bs => f (true :: bs))))
    rw [bitSum_mul_left a m (fun bs => f (false :: bs)),
      bitSum_mul_left a m (fun bs => f (true :: bs))]
    constructive_ring

/-- Exchange of two cube sums. -/
theorem bitSum_comm : ∀ (m k : Nat) (f : List Bool → List Bool → F),
    bitSum m (fun a => bitSum k (fun b => f a b)) = bitSum k (fun b => bitSum m (fun a => f a b))
  | 0, _, _ => by rfl
  | m + 1, k, f => by
    show add (bitSum m (fun a => bitSum k (fun b => f (false :: a) b)))
        (bitSum m (fun a => bitSum k (fun b => f (true :: a) b))) =
      bitSum k (fun b => add (bitSum m (fun a => f (false :: a) b))
        (bitSum m (fun a => f (true :: a) b)))
    rw [bitSum_comm m k (fun a b => f (false :: a) b), bitSum_comm m k (fun a b => f (true :: a) b),
      bitSum_add]

/-- Multilinear extension of the table `T` on `{0,1}^m` at a point; the first coordinate of
    the point is the first bit. Missing coordinates read as `0`. -/
def mle : Nat → (List Bool → F) → List F → F
  | 0, T, _ => T []
  | m + 1, T, xs =>
    add (mul (sub one (xs.headD zero)) (mle m (fun bs => T (false :: bs)) xs.tail))
      (mul (xs.headD zero) (mle m (fun bs => T (true :: bs)) xs.tail))

theorem mle_zero_dim (T : List Bool → F) (xs : List F) : mle 0 T xs = T [] := by rfl

theorem mle_cons (m : Nat) (T : List Bool → F) (x : F) (xs : List F) :
    mle (m + 1) T (x :: xs) =
      add (mul (sub one x) (mle m (fun bs => T (false :: bs)) xs))
        (mul x (mle m (fun bs => T (true :: bs)) xs)) := by rfl

/-- On a Boolean point the multilinear extension is the table entry. -/
theorem mle_bitPt : ∀ (m : Nat) (T : List Bool → F) (bs : List Bool), bs.length = m →
    mle m T (bitPt bs) = T bs
  | 0, _, [], _ => by rfl
  | 0, _, _ :: _, h => absurd h (Nat.succ_ne_zero _)
  | m + 1, _, [], h => absurd h.symm (Nat.succ_ne_zero m)
  | m + 1, T, b :: bs, h => by
    have ih0 := mle_bitPt m (fun t => T (false :: t)) bs (Nat.succ.inj h)
    have ih1 := mle_bitPt m (fun t => T (true :: t)) bs (Nat.succ.inj h)
    cases b with
    | false =>
      show add (mul (sub one zero) (mle m (fun t => T (false :: t)) (bitPt bs)))
        (mul zero (mle m (fun t => T (true :: t)) (bitPt bs))) = T (false :: bs)
      rw [ih0]
      constructive_ring
    | true =>
      show add (mul (sub one one) (mle m (fun t => T (false :: t)) (bitPt bs)))
        (mul one (mle m (fun t => T (true :: t)) (bitPt bs))) = T (true :: bs)
      rw [ih1]
      constructive_ring

theorem mle_congr : ∀ (m : Nat) (T T' : List Bool → F) (xs : List F),
    (∀ bs : List Bool, bs.length = m → T bs = T' bs) → mle m T xs = mle m T' xs
  | 0, _, _, _, h => h [] rfl
  | m + 1, T, T', xs, h => by
    show add (mul (sub one (xs.headD zero)) (mle m (fun bs => T (false :: bs)) xs.tail))
        (mul (xs.headD zero) (mle m (fun bs => T (true :: bs)) xs.tail)) =
      add (mul (sub one (xs.headD zero)) (mle m (fun bs => T' (false :: bs)) xs.tail))
        (mul (xs.headD zero) (mle m (fun bs => T' (true :: bs)) xs.tail))
    rw [mle_congr m (fun bs => T (false :: bs)) (fun bs => T' (false :: bs)) xs.tail
        (fun bs hb => h (false :: bs) (congrArg Nat.succ hb)),
      mle_congr m (fun bs => T (true :: bs)) (fun bs => T' (true :: bs)) xs.tail
        (fun bs hb => h (true :: bs) (congrArg Nat.succ hb))]

theorem mle_add : ∀ (m : Nat) (T T' : List Bool → F) (xs : List F),
    mle m (fun bs => add (T bs) (T' bs)) xs = add (mle m T xs) (mle m T' xs)
  | 0, _, _, _ => by rfl
  | m + 1, T, T', xs => by
    show add (mul (sub one (xs.headD zero))
          (mle m (fun bs => add (T (false :: bs)) (T' (false :: bs))) xs.tail))
        (mul (xs.headD zero) (mle m (fun bs => add (T (true :: bs)) (T' (true :: bs))) xs.tail)) =
      add (add (mul (sub one (xs.headD zero)) (mle m (fun bs => T (false :: bs)) xs.tail))
          (mul (xs.headD zero) (mle m (fun bs => T (true :: bs)) xs.tail)))
        (add (mul (sub one (xs.headD zero)) (mle m (fun bs => T' (false :: bs)) xs.tail))
          (mul (xs.headD zero) (mle m (fun bs => T' (true :: bs)) xs.tail)))
    rw [mle_add m (fun bs => T (false :: bs)) (fun bs => T' (false :: bs)) xs.tail,
      mle_add m (fun bs => T (true :: bs)) (fun bs => T' (true :: bs)) xs.tail]
    constructive_ring

theorem mle_mul_left (a : F) : ∀ (m : Nat) (T : List Bool → F) (xs : List F),
    mle m (fun bs => mul a (T bs)) xs = mul a (mle m T xs)
  | 0, _, _ => by rfl
  | m + 1, T, xs => by
    show add (mul (sub one (xs.headD zero)) (mle m (fun bs => mul a (T (false :: bs))) xs.tail))
        (mul (xs.headD zero) (mle m (fun bs => mul a (T (true :: bs))) xs.tail)) =
      mul a (add (mul (sub one (xs.headD zero)) (mle m (fun bs => T (false :: bs)) xs.tail))
        (mul (xs.headD zero) (mle m (fun bs => T (true :: bs)) xs.tail)))
    rw [mle_mul_left a m (fun bs => T (false :: bs)) xs.tail,
      mle_mul_left a m (fun bs => T (true :: bs)) xs.tail]
    constructive_ring

theorem mle_const_zero : ∀ (m : Nat) (xs : List F), mle m (fun _ => (zero : F)) xs = zero
  | 0, _ => by rfl
  | m + 1, xs => by
    show add (mul (sub one (xs.headD zero)) (mle m (fun _ => (zero : F)) xs.tail))
      (mul (xs.headD zero) (mle m (fun _ => (zero : F)) xs.tail)) = zero
    rw [mle_const_zero m xs.tail]
    constructive_ring

/-- The multilinear extension commutes with a cube sum over a second index. -/
theorem mle_bitSum (m : Nat) (xs : List F) : ∀ (k : Nat) (f : List Bool → List Bool → F),
    mle m (fun i => bitSum k (fun y => f i y)) xs = bitSum k (fun y => mle m (fun i => f i y) xs)
  | 0, _ => by rfl
  | k + 1, f => by
    show mle m (fun i => add (bitSum k (fun y => f i (false :: y)))
        (bitSum k (fun y => f i (true :: y)))) xs =
      add (bitSum k (fun y => mle m (fun i => f i (false :: y)) xs))
        (bitSum k (fun y => mle m (fun i => f i (true :: y)) xs))
    rw [mle_add, mle_bitSum m xs k (fun i y => f i (false :: y)),
      mle_bitSum m xs k (fun i y => f i (true :: y))]

/-- A function of a point that is affine in every coordinate. -/
def CoordAffine (h : List F → F) : Prop :=
  ∀ (cs : List F) (x : F) (t : List F),
    h (cs ++ x :: t) =
      add (h (cs ++ zero :: t)) (mul x (sub (h (cs ++ one :: t)) (h (cs ++ zero :: t))))

theorem mle_coordAffine : ∀ (m : Nat) (T : List Bool → F), CoordAffine (mle m T)
  | 0, T, _, x, _ => by
    show T [] = add (T []) (mul x (sub (T []) (T [])))
    constructive_ring
  | m + 1, T, [], x, t => by
    show add (mul (sub one x) (mle m (fun bs => T (false :: bs)) t))
        (mul x (mle m (fun bs => T (true :: bs)) t)) =
      add (add (mul (sub one zero) (mle m (fun bs => T (false :: bs)) t))
          (mul zero (mle m (fun bs => T (true :: bs)) t)))
        (mul x (sub (add (mul (sub one one) (mle m (fun bs => T (false :: bs)) t))
            (mul one (mle m (fun bs => T (true :: bs)) t)))
          (add (mul (sub one zero) (mle m (fun bs => T (false :: bs)) t))
            (mul zero (mle m (fun bs => T (true :: bs)) t)))))
    constructive_ring
  | m + 1, T, c :: cs, x, t => by
    show add (mul (sub one c) (mle m (fun bs => T (false :: bs)) (cs ++ x :: t)))
        (mul c (mle m (fun bs => T (true :: bs)) (cs ++ x :: t))) =
      add (add (mul (sub one c) (mle m (fun bs => T (false :: bs)) (cs ++ zero :: t)))
          (mul c (mle m (fun bs => T (true :: bs)) (cs ++ zero :: t))))
        (mul x (sub (add (mul (sub one c) (mle m (fun bs => T (false :: bs)) (cs ++ one :: t)))
            (mul c (mle m (fun bs => T (true :: bs)) (cs ++ one :: t))))
          (add (mul (sub one c) (mle m (fun bs => T (false :: bs)) (cs ++ zero :: t)))
            (mul c (mle m (fun bs => T (true :: bs)) (cs ++ zero :: t))))))
    rw [mle_coordAffine m (fun bs => T (false :: bs)) cs x t,
      mle_coordAffine m (fun bs => T (true :: bs)) cs x t]
    constructive_ring

/-- `eq(τ, x) = ∏_j (τ_j x_j + (1 - τ_j)(1 - x_j))`. -/
def eqPt : List F → List F → F
  | [], _ => one
  | t :: ts, xs =>
    mul (add (mul t (xs.headD zero)) (mul (sub one t) (sub one (xs.headD zero)))) (eqPt ts xs.tail)

theorem eqPt_coordAffine : ∀ tau : List F, CoordAffine (eqPt tau)
  | [], _, x, _ => by
    show (one : F) = add one (mul x (sub one one))
    constructive_ring
  | a :: ts, [], x, t => by
    show mul (add (mul a x) (mul (sub one a) (sub one x))) (eqPt ts t) =
      add (mul (add (mul a zero) (mul (sub one a) (sub one zero))) (eqPt ts t))
        (mul x (sub (mul (add (mul a one) (mul (sub one a) (sub one one))) (eqPt ts t))
          (mul (add (mul a zero) (mul (sub one a) (sub one zero))) (eqPt ts t))))
    constructive_ring
  | a :: ts, c :: cs, x, t => by
    show mul (add (mul a c) (mul (sub one a) (sub one c))) (eqPt ts (cs ++ x :: t)) =
      add (mul (add (mul a c) (mul (sub one a) (sub one c))) (eqPt ts (cs ++ zero :: t)))
        (mul x (sub (mul (add (mul a c) (mul (sub one a) (sub one c))) (eqPt ts (cs ++ one :: t)))
          (mul (add (mul a c) (mul (sub one a) (sub one c))) (eqPt ts (cs ++ zero :: t)))))
    rw [eqPt_coordAffine ts cs x t]
    constructive_ring

/-- The first `i` challenges as a point. -/
def chalPrefix (c : Nat → F) (i : Nat) : List F := (List.range i).map c

omit [LawfulField F] in
theorem chalPrefix_length (c : Nat → F) (i : Nat) : (chalPrefix c i).length = i := by
  unfold chalPrefix
  rw [List.length_map, List.length_range]

omit [LawfulField F] in
theorem chalPrefix_succ (c : Nat → F) (i : Nat) :
    chalPrefix c (i + 1) = chalPrefix c i ++ [c i] := by
  unfold chalPrefix
  rw [List.range_succ, List.map_append]
  rfl

/-- Sum of `g` over the Boolean completions of the bound prefix `cs` of an `n`-variable point. -/
def cubeClaim (g : List F → F) (n : Nat) (cs : List F) : F :=
  bitSum (n - cs.length) (fun bs => g (cs ++ bitPt bs))

/-- The round polynomial after the prefix `cs`, as a function of the next variable. -/
def cubeRound (g : List F → F) (n : Nat) (cs : List F) (x : F) : F :=
  bitSum (n - (cs.length + 1)) (fun bs => g (cs ++ x :: bitPt bs))

theorem cubeRound_telescope (g : List F → F) (n : Nat) (cs : List F) (h : cs.length < n) :
    add (cubeRound g n cs zero) (cubeRound g n cs one) = cubeClaim g n cs := by
  unfold cubeRound cubeClaim
  have hn : n - cs.length = (n - (cs.length + 1)) + 1 := by omega
  rw [hn]
  rfl

theorem cubeRound_eq_claim (g : List F → F) (n : Nat) (cs : List F) (x : F) :
    cubeRound g n cs x = cubeClaim g n (cs ++ [x]) := by
  unfold cubeRound cubeClaim
  rw [List.length_append]
  exact bitSum_congr _ _ _ (fun bs _ => by rw [List.append_assoc]; rfl)

theorem cubeClaim_full (g : List F → F) (n : Nat) (cs : List F) (h : cs.length = n) :
    cubeClaim g n cs = g cs := by
  unfold cubeClaim
  rw [h, Nat.sub_self]
  show g (cs ++ []) = g cs
  rw [List.append_nil]

/-- `w` is an honest sumcheck transcript for the summand `g` on `n` variables: its claim is
    the cube sum of `g` and its `i`-th message is the round polynomial at the challenge
    prefix. -/
def WitnessRounds.Proves (w : WitnessRounds F) (g : List F → F) (n d : Nat) (c : Nat → F) : Prop :=
  w.H = cubeClaim g n [] ∧
    ∀ i : Nat, i < n → ∀ x : F, evalCoeffs (w.msg d i) x = cubeRound g n (chalPrefix c i) x

theorem WitnessRounds.Proves.claim_eq {w : WitnessRounds F} {g : List F → F} {n d : Nat}
    {c : Nat → F} (h : w.Proves g n d c) :
    ∀ i : Nat, i ≤ n → w.claim d c i = cubeClaim g n (chalPrefix c i)
  | 0, _ => h.1
  | i + 1, hi => by
    show evalCoeffs (w.msg d i) (c i) = _
    rw [h.2 i hi (c i), cubeRound_eq_claim, chalPrefix_succ]

theorem WitnessRounds.Proves.honest {w : WitnessRounds F} {g : List F → F} {n d : Nat}
    {c : Nat → F} (h : w.Proves g n d c) : w.Honest n d c := by
  intro i hi
  rw [h.2 i hi zero, h.2 i hi one,
    cubeRound_telescope g n _ (by rw [chalPrefix_length]; exact hi),
    ← h.claim_eq i (Nat.le_of_lt hi)]

/-- The last running claim of an honest transcript is the summand at the challenge point. -/
theorem WitnessRounds.Proves.terminal {w : WitnessRounds F} {g : List F → F} {n d : Nat}
    {c : Nat → F} (h : w.Proves g n d c) : w.claim d c n = g (chalPrefix c n) := by
  rw [h.claim_eq n (Nat.le_refl n), cubeClaim_full _ _ _ (chalPrefix_length c n)]

/-- `cs` has at most `d + 1` coefficients and is the univariate `f`. -/
def CoeffRep (d : Nat) (f : F → F) (cs : List F) : Prop :=
  cs.length ≤ d + 1 ∧ ∀ x : F, evalCoeffs cs x = f x

omit [LawfulField F] in
theorem rawAdd_length_le [CommRingOps F] : ∀ (a b : List F) (B : Nat), a.length ≤ B → b.length ≤ B →
    (rawAddCoeffs a b).length ≤ B
  | [], _, _, _, hb => hb
  | _ :: _, [], _, ha, _ => ha
  | _ :: _, _ :: _, 0, ha, _ => absurd ha (Nat.not_succ_le_zero _)
  | _ :: cs, _ :: es, B + 1, ha, hb =>
    Nat.succ_le_succ (rawAdd_length_le cs es B (Nat.le_of_succ_le_succ ha)
      (Nat.le_of_succ_le_succ hb))

theorem rawMul_length_le : ∀ (a b : List F), (rawMul a b).length ≤ a.length + (b.length - 1)
  | [], _ => Nat.zero_le _
  | c :: cs, b => by
    show (rawAddCoeffs (b.map (mul c)) (zero :: rawMul cs b)).length ≤
      cs.length + 1 + (b.length - 1)
    have ih := rawMul_length_le cs b
    apply rawAdd_length_le
    · rw [List.length_map]
      omega
    · show (rawMul cs b).length + 1 ≤ cs.length + 1 + (b.length - 1)
      omega

theorem CoeffRep.mono {d d' : Nat} {f : F → F} {cs : List F} (h : CoeffRep d f cs)
    (hd : d ≤ d') : CoeffRep d' f cs :=
  ⟨Nat.le_trans h.1 (Nat.succ_le_succ hd), h.2⟩

theorem CoeffRep.mul {d₁ d₂ : Nat} {f g : F → F} {p q : List F} (hp : CoeffRep d₁ f p)
    (hq : CoeffRep d₂ g q) : CoeffRep (d₁ + d₂) (fun x => mul (f x) (g x)) (rawMul p q) := by
  refine ⟨?_, fun x => ?_⟩
  · have h := rawMul_length_le p q
    have h1 := hp.1
    have h2 := hq.1
    omega
  · rw [evalCoeffs_rawMul, hp.2, hq.2]

theorem CoeffRep.add {d : Nat} {f g : F → F} {p q : List F} (hp : CoeffRep d f p)
    (hq : CoeffRep d g q) : CoeffRep d (fun x => add (f x) (g x)) (rawAddCoeffs p q) :=
  ⟨rawAdd_length_le p q _ hp.1 hq.1, fun x => by rw [evalCoeffs_rawAdd, hp.2, hq.2]⟩

theorem CoeffRep.sub {d : Nat} {f g : F → F} {p q : List F} (hp : CoeffRep d f p)
    (hq : CoeffRep d g q) : CoeffRep d (fun x => sub (f x) (g x)) (subCoeffs p q) := by
  refine ⟨?_, fun x => by rw [evalCoeffs_sub, hp.2, hq.2]⟩
  rw [subCoeffs_length]
  exact Nat.max_le.mpr ⟨hp.1, hq.1⟩

/-- The two coefficients of a coordinatewise affine function along one coordinate. -/
def line2 (h : List F → F) (cs t : List F) : List F :=
  [h (cs ++ zero :: t), sub (h (cs ++ one :: t)) (h (cs ++ zero :: t))]

theorem CoordAffine.rep {h : List F → F} (hh : CoordAffine h) (cs t : List F) :
    CoeffRep 1 (fun x => h (cs ++ x :: t)) (line2 h cs t) := by
  refine ⟨Nat.le_refl 2, fun x => ?_⟩
  show add (h (cs ++ zero :: t))
    (mul x (add (sub (h (cs ++ one :: t)) (h (cs ++ zero :: t))) (mul x zero))) = h (cs ++ x :: t)
  rw [hh cs x t]
  constructive_ring

/-- Coefficientwise sum of polynomials over `{0,1}^m`. -/
def bitSumL : Nat → (List Bool → List F) → List F
  | 0, f => f []
  | m + 1, f =>
    rawAddCoeffs (bitSumL m (fun bs => f (false :: bs))) (bitSumL m (fun bs => f (true :: bs)))

theorem bitSumL_length_le (B : Nat) : ∀ (m : Nat) (f : List Bool → List F),
    (∀ bs : List Bool, (f bs).length ≤ B) → (bitSumL m f).length ≤ B
  | 0, _, h => h []
  | m + 1, _, h =>
    rawAdd_length_le _ _ B (bitSumL_length_le B m _ (fun bs => h (false :: bs)))
      (bitSumL_length_le B m _ (fun bs => h (true :: bs)))

theorem evalCoeffs_bitSumL (x : F) : ∀ (m : Nat) (f : List Bool → List F),
    evalCoeffs (bitSumL m f) x = bitSum m (fun bs => evalCoeffs (f bs) x)
  | 0, _ => by rfl
  | m + 1, f => by
    show evalCoeffs (rawAddCoeffs (bitSumL m (fun bs => f (false :: bs)))
        (bitSumL m (fun bs => f (true :: bs)))) x =
      add (bitSum m (fun bs => evalCoeffs (f (false :: bs)) x))
        (bitSum m (fun bs => evalCoeffs (f (true :: bs)) x))
    rw [evalCoeffs_rawAdd, evalCoeffs_bitSumL x m (fun bs => f (false :: bs)),
      evalCoeffs_bitSumL x m (fun bs => f (true :: bs))]

/-- Degree-`d` coefficient lists of a summand along every coordinate line. -/
structure LineRep (g : List F → F) (d : Nat) where
  line : List F → List F → List F
  len : ∀ cs t : List F, (line cs t).length ≤ d + 1
  eval : ∀ (cs t : List F) (x : F), evalCoeffs (line cs t) x = g (cs ++ x :: t)

/-- Coefficients of the round polynomial after the prefix `cs`. -/
def cubeMsg {g : List F → F} {d : Nat} (L : LineRep g d) (n : Nat) (cs : List F) : List F :=
  bitSumL (n - (cs.length + 1)) (fun bs => L.line cs (bitPt bs))

theorem cubeMsg_rep {g : List F → F} {d : Nat} (L : LineRep g d) (n : Nat) (cs : List F) :
    CoeffRep d (cubeRound g n cs) (cubeMsg L n cs) := by
  refine ⟨bitSumL_length_le _ _ _ (fun bs => L.len cs (bitPt bs)), fun x => ?_⟩
  unfold cubeMsg cubeRound
  rw [evalCoeffs_bitSumL]
  exact bitSum_congr _ _ _ (fun bs _ => L.eval cs (bitPt bs) x)

theorem evalCoeffs_getD_range' (x : F) : ∀ (cs : List F) (s m : Nat) (g : Nat → F),
    cs.length ≤ m → (∀ k : Nat, g (s + k) = cs.getD k zero) →
    evalCoeffs ((List.range' s m).map g) x = evalCoeffs cs x
  | [], _, 0, _, _, _ => by rfl
  | [], s, m + 1, g, _, h => by
    show add (g s) (mul x (evalCoeffs ((List.range' (s + 1) m).map g) x)) = zero
    have h0 : g s = zero := h 0
    rw [h0, evalCoeffs_getD_range' x [] (s + 1) m g (Nat.zero_le m) (fun k => by
      rw [Nat.succ_add_eq_add_succ]
      exact h (k + 1))]
    show add zero (mul x zero) = (zero : F)
    constructive_ring
  | _ :: _, _, 0, _, hl, _ => absurd hl (Nat.not_succ_le_zero _)
  | c :: cs, s, m + 1, g, hl, h => by
    show add (g s) (mul x (evalCoeffs ((List.range' (s + 1) m).map g) x)) =
      add c (mul x (evalCoeffs cs x))
    have h0 : g s = c := h 0
    rw [h0, evalCoeffs_getD_range' x cs (s + 1) m g (Nat.le_of_succ_le_succ hl) (fun k => by
      rw [Nat.succ_add_eq_add_succ]
      exact h (k + 1))]

/-- A sumcheck transcript from its claim and its round coefficient lists. -/
def roundsOfMsgs (H : F) (msgs : Nat → List F) : WitnessRounds F :=
  ⟨H, fun i => (msgs i).getD 0 zero, fun i k => (msgs i).getD (k + 1) zero⟩

theorem roundsOfMsgs_eval (H : F) (msgs : Nat → List F) (d i : Nat)
    (hl : (msgs i).length ≤ d + 1) (x : F) :
    evalCoeffs ((roundsOfMsgs H msgs).msg d i) x = evalCoeffs (msgs i) x := by
  show add ((msgs i).getD 0 zero)
    (mul x (evalCoeffs ((List.range d).map (fun k => (msgs i).getD (k + 1) zero)) x)) = _
  rw [List.range_eq_range']
  generalize msgs i = l at hl
  cases l with
  | nil =>
    rw [evalCoeffs_getD_range' x [] 0 d (fun k => ([] : List F).getD (k + 1) zero)
      (Nat.zero_le d) (fun _ => rfl)]
    show add zero (mul x zero) = (zero : F)
    constructive_ring
  | cons c tl =>
    rw [evalCoeffs_getD_range' x tl 0 d (fun k => (c :: tl).getD (k + 1) zero)
      (Nat.le_of_succ_le_succ hl) (fun k => by rw [Nat.zero_add]; rfl)]
    rfl

/-- The honest sumcheck prover for a summand with degree-`d` line coefficients. -/
def cubeProver {g : List F → F} {d : Nat} (L : LineRep g d) (n : Nat) (c : Nat → F) :
    WitnessRounds F :=
  roundsOfMsgs (cubeClaim g n []) (fun i => cubeMsg L n (chalPrefix c i))

theorem cubeProver_proves {g : List F → F} {d : Nat} (L : LineRep g d) (n : Nat) (c : Nat → F) :
    (cubeProver L n c).Proves g n d c :=
  ⟨rfl, fun i _ x => by
    show evalCoeffs ((roundsOfMsgs (cubeClaim g n []) (fun i => cubeMsg L n (chalPrefix c i))).msg
      d i) x = _
    rw [roundsOfMsgs_eval _ _ d i (cubeMsg_rep L n (chalPrefix c i)).1,
      (cubeMsg_rep L n (chalPrefix c i)).2]⟩

/-- `a^7`, multiplied as in `row_gate` of `zk_hem/protocol.rs`. -/
def pow7 (a : F) : F := mul (mul (mul (mul a a) (mul a a)) (mul a a)) a

/-- Row constraint `s (a^7 - a b) + a b - c`: `a^7 = c` on S-box rows (`s = 1`), `a b = c`
    on multiplication rows (`s = 0`). -/
def rowGate (s a b c : F) : F := add (mul s (sub (pow7 a) (mul a b))) (sub (mul a b) c)

/-- Summand of the row sumcheck: `eq(τ, x) · gate(sel(x), A(x), B(x), C(x))` for the selector
    table and the three row tables on `{0,1}^n`. -/
def rowSummand (n : Nat) (tau : List F) (sel ta tb tc : List Bool → F) (x : List F) : F :=
  mul (eqPt tau x) (rowGate (mle n sel x) (mle n ta x) (mle n tb x) (mle n tc x))

/-- Summand of the column sumcheck: `M(y) · Z(y)` on `{0,1}^k`. -/
def colSummand (k : Nat) (tm tz : List Bool → F) (y : List F) : F :=
  mul (mle k tm y) (mle k tz y)

/-- Coefficients of the row summand along one coordinate: individual degree `9`
    (`ROW_DEGREE`). -/
def rowLine (n : Nat) (tau : List F) (sel ta tb tc : List Bool → F) (cs t : List F) : List F :=
  rawMul (line2 (eqPt tau) cs t)
    (rawAddCoeffs
      (rawMul (line2 (mle n sel) cs t)
        (subCoeffs
          (rawMul (rawMul (rawMul (rawMul (line2 (mle n ta) cs t) (line2 (mle n ta) cs t))
            (rawMul (line2 (mle n ta) cs t) (line2 (mle n ta) cs t)))
            (rawMul (line2 (mle n ta) cs t) (line2 (mle n ta) cs t))) (line2 (mle n ta) cs t))
          (rawMul (line2 (mle n ta) cs t) (line2 (mle n tb) cs t))))
      (subCoeffs (rawMul (line2 (mle n ta) cs t) (line2 (mle n tb) cs t))
        (line2 (mle n tc) cs t)))

theorem rowLine_rep (n : Nat) (tau : List F) (sel ta tb tc : List Bool → F) (cs t : List F) :
    CoeffRep 9 (fun x => rowSummand n tau sel ta tb tc (cs ++ x :: t))
      (rowLine n tau sel ta tb tc cs t) := by
  have he := (eqPt_coordAffine tau).rep cs t
  have hs := (mle_coordAffine n sel).rep cs t
  have ha := (mle_coordAffine n ta).rep cs t
  have hb := (mle_coordAffine n tb).rep cs t
  have hc := (mle_coordAffine n tc).rep cs t
  have hab : CoeffRep 2 _ _ := ha.mul hb
  have ha2 : CoeffRep 2 _ _ := ha.mul ha
  have ha7 : CoeffRep 7 _ _ := ((ha2.mul ha2).mul ha2).mul ha
  have hin : CoeffRep 7 _ _ := ha7.sub (hab.mono (by decide))
  have ht1 : CoeffRep 8 _ _ := hs.mul hin
  have ht2 : CoeffRep 8 _ _ := (hab.sub (hc.mono (by decide))).mono (by decide)
  have hg : CoeffRep 8 _ _ := ht1.add ht2
  exact he.mul hg

/-- Degree-`9` line coefficients of the row summand. -/
def rowLineRep (n : Nat) (tau : List F) (sel ta tb tc : List Bool → F) :
    LineRep (rowSummand n tau sel ta tb tc) 9 where
  line := rowLine n tau sel ta tb tc
  len := fun cs t => (rowLine_rep n tau sel ta tb tc cs t).1
  eval := fun cs t x => (rowLine_rep n tau sel ta tb tc cs t).2 x

theorem colLine_rep (k : Nat) (tm tz : List Bool → F) (cs t : List F) :
    CoeffRep 2 (fun x => colSummand k tm tz (cs ++ x :: t))
      (rawMul (line2 (mle k tm) cs t) (line2 (mle k tz) cs t)) :=
  ((mle_coordAffine k tm).rep cs t).mul ((mle_coordAffine k tz).rep cs t)

/-- Degree-`2` line coefficients of the column summand (`COL_DEGREE`). -/
def colLineRep (k : Nat) (tm tz : List Bool → F) : LineRep (colSummand k tm tz) 2 where
  line := fun cs t => rawMul (line2 (mle k tm) cs t) (line2 (mle k tz) cs t)
  len := fun cs t => (colLine_rep k tm tz cs t).1
  eval := fun cs t x => (colLine_rep k tm tz cs t).2 x

end Cube

/-! ## §11. Public subcube relation, masking rows and finite salt queries -/

attribute [-instance] Fin.instLinearOrderPackage

/-! ## Twelve masking cells and the deployed corner-row linear map

The three groups of four cells are the twelve rows allocated by `MASK_ROWS`.
The two low row variables supply the four multilinear corner weights; all remaining
row variables contribute the group's `cornerFactor`. The resulting three-by-three
map has determinant `k₁ k₂ k₃`, independently of the witness. -/

def cornerFactorFrom (base j : Nat) : List Fp4 → Fp4
  | [] => one
  | x :: xs => mul (if (base / 2 ^ j) % 2 = 1 then x else sub one x)
      (cornerFactorFrom base (j + 1) xs)

def cornerFactor (rx : List Fp4) (base : Nat) : Fp4 :=
  cornerFactorFrom base 2 (rx.drop 2)

def cornerPad (a b : Fp4) (r : Pad) : Fp4 :=
  add (add (add
    (mul (embed r.r0) (mul (sub one a) (sub one b)))
    (mul (embed r.r1) (mul a (sub one b))))
    (mul (embed r.r2) (mul (sub one a) b)))
    (mul (embed r.r3) (mul a b))

theorem Pad.ext {x y : Pad} (h0 : x.r0 = y.r0) (h1 : x.r1 = y.r1)
    (h2 : x.r2 = y.r2) (h3 : x.r3 = y.r3) : x = y := by
  cases x; cases y; cases h0; cases h1; cases h2; cases h3; rfl

/-- Base-field change of coordinates from Boolean-corner to monomial coefficients. -/
def cornerCoeffs (r : Pad) : Pad :=
  ⟨r.r0, sub r.r1 r.r0, sub r.r2 r.r0,
   add (sub (sub r.r0 r.r1) r.r2) r.r3⟩

def cornerCoeffsInv (r : Pad) : Pad :=
  ⟨r.r0, add r.r1 r.r0, add r.r2 r.r0,
   add (add (add r.r3 r.r1) r.r2) r.r0⟩

theorem cornerCoeffs_left (r : Pad) : cornerCoeffsInv (cornerCoeffs r) = r := by
  apply Pad.ext <;> dsimp [cornerCoeffs, cornerCoeffsInv] <;> constructive_ring

theorem cornerCoeffs_right (r : Pad) : cornerCoeffs (cornerCoeffsInv r) = r := by
  apply Pad.ext <;> dsimp [cornerCoeffs, cornerCoeffsInv] <;> constructive_ring

theorem embed_add (a b : Fp) : embed (add a b) = add (embed a) (embed b) := by
  exact GoldilocksField.GoldilocksExt4.embedBase_add a b

theorem embed_sub (a b : Fp) : embed (sub a b) = sub (embed a) (embed b) := by
  exact GoldilocksField.GoldilocksExt4.embedBase_sub a b

theorem cornerPad_power_point (z : Fp4) (r : Pad) :
    cornerPad z (mul z z) r = padMap z (cornerCoeffs r) := by
  simp only [cornerPad, padMap, cornerCoeffs, embed_add, embed_sub]
  constructive_ring

/-- A rank certificate for the actual four Boolean-corner weights. This is the condition
    checked by the four-by-four base-field elimination in Rust's `CornerPadBasis::new`. -/
structure CornerPadBasis (a b : Fp4) where
  invert : Fp4 → Pad
  left_inv : ∀ r, invert (cornerPad a b r) = r
  right_inv : ∀ v, cornerPad a b (invert v) = v

/-- The rank predicate has genuine inhabitants: every primitive power point works. -/
def cornerPadBasis_power_point (z : Fp4) (hz : z.c1 ≠ zero) : CornerPadBasis z (mul z z) where
  invert v := cornerCoeffsInv (padInv z v)
  left_inv r := by
    rw [cornerPad_power_point, padInv_padMap z hz, cornerCoeffs_left]
  right_inv v := by
    rw [cornerPad_power_point, cornerCoeffs_right, padMap_padInv z hz]

structure RowTriple where
  a : Fp4
  b : Fp4
  c : Fp4

theorem RowTriple.ext {x y : RowTriple} (ha : x.a = y.a) (hb : x.b = y.b)
    (hc : x.c = y.c) : x = y := by
  cases x; cases y; cases ha; cases hb; cases hc; rfl

/-- Twelve independent base-field masking variables, split into three groups of four. -/
structure RowMaskCells where
  first : Pad
  second : Pad
  third : Pad

def rowMaskMap (k₁ k₂ k₃ : Fp4) (e : RowTriple) : RowTriple :=
  ⟨add (mul k₁ e.a) (mul k₃ e.c), mul k₂ e.b,
   add (add (mul k₁ e.a) (mul k₂ e.b)) (add (mul k₃ e.c) (mul k₃ e.c))⟩

def rowMaskInv (k₁ k₂ k₃ : Fp4) (d : RowTriple) : RowTriple :=
  let e₃ := mul (sub (sub d.c d.b) d.a) (LawfulField.inv k₃)
  ⟨mul (sub d.a (mul k₃ e₃)) (LawfulField.inv k₁),
   mul d.b (LawfulField.inv k₂), e₃⟩

/-- The determinant of the three row groups, expanded without a matrix-library convention. -/
theorem rowMask_determinant (k₁ k₂ k₃ : Fp4) :
    sub (mul (mul k₁ k₂) (add k₃ k₃)) (mul (mul k₃ k₂) k₁) =
      mul (mul k₁ k₂) k₃ := by
  constructive_ring

theorem scale_inv (k x : Fp4) (hk : k ≠ zero) :
    mul k (mul x (LawfulField.inv k)) = x := by
  calc
    _ = mul x (mul k (LawfulField.inv k)) := by constructive_ring
    _ = x := by rw [LawfulField.mul_inv_cancel hk, LawfulCommRing.mul_one]

theorem inv_scale (k x : Fp4) (hk : k ≠ zero) :
    mul (mul k x) (LawfulField.inv k) = x := by
  calc
    _ = mul x (mul k (LawfulField.inv k)) := by constructive_ring
    _ = x := by rw [LawfulField.mul_inv_cancel hk, LawfulCommRing.mul_one]

theorem rowMaskMap_right (k₁ k₂ k₃ : Fp4)
    (h₁ : k₁ ≠ zero) (h₂ : k₂ ≠ zero) (h₃ : k₃ ≠ zero) (d : RowTriple) :
    rowMaskMap k₁ k₂ k₃ (rowMaskInv k₁ k₂ k₃ d) = d := by
  apply RowTriple.ext <;>
    dsimp [rowMaskMap, rowMaskInv] <;>
    simp only [scale_inv k₁ _ h₁, scale_inv k₂ _ h₂, scale_inv k₃ _ h₃] <;>
    constructive_ring

theorem rowMaskMap_left (k₁ k₂ k₃ : Fp4)
    (h₁ : k₁ ≠ zero) (h₂ : k₂ ≠ zero) (h₃ : k₃ ≠ zero) (e : RowTriple) :
    rowMaskInv k₁ k₂ k₃ (rowMaskMap k₁ k₂ k₃ e) = e := by
  have hc : sub (sub (rowMaskMap k₁ k₂ k₃ e).c (rowMaskMap k₁ k₂ k₃ e).b)
      (rowMaskMap k₁ k₂ k₃ e).a = mul k₃ e.c := by
    simp only [rowMaskMap]
    constructive_ring
  have ha : sub (rowMaskMap k₁ k₂ k₃ e).a (mul k₃ e.c) = mul k₁ e.a := by
    simp only [rowMaskMap]
    constructive_ring
  unfold rowMaskInv
  rw [hc, inv_scale k₃ _ h₃]
  dsimp only
  rw [ha]
  simp only [rowMaskMap, inv_scale k₁ _ h₁, inv_scale k₂ _ h₂]

def rowMaskCellsMap {a b : Fp4} (_basis : CornerPadBasis a b)
    (k₁ k₂ k₃ : Fp4) (r : RowMaskCells) : RowTriple :=
  rowMaskMap k₁ k₂ k₃
    ⟨cornerPad a b r.first, cornerPad a b r.second, cornerPad a b r.third⟩

def rowMaskCellsInv {a b : Fp4} (basis : CornerPadBasis a b)
    (k₁ k₂ k₃ : Fp4) (v : RowTriple) : RowMaskCells :=
  let e := rowMaskInv k₁ k₂ k₃ v
  ⟨basis.invert e.a, basis.invert e.b, basis.invert e.c⟩

/-- Exactly the three nonzero corner factors and the four-corner rank test suffice;
    no witness-specific invertibility premise is needed. -/
def rowMaskCellsBij {a b : Fp4} (basis : CornerPadBasis a b)
    (k₁ k₂ k₃ : Fp4) (h₁ : k₁ ≠ zero) (h₂ : k₂ ≠ zero) (h₃ : k₃ ≠ zero) :
    SimpleEquiv RowMaskCells RowTriple where
  toFun := rowMaskCellsMap basis k₁ k₂ k₃
  invFun := rowMaskCellsInv basis k₁ k₂ k₃
  left_inv r := by
    dsimp [rowMaskCellsMap, rowMaskCellsInv]
    rw [rowMaskMap_left k₁ k₂ k₃ h₁ h₂ h₃]
    simp only [basis.left_inv]
  right_inv v := by
    dsimp [rowMaskCellsMap, rowMaskCellsInv]
    rw [basis.right_inv, basis.right_inv, basis.right_inv]
    exact rowMaskMap_right k₁ k₂ k₃ h₁ h₂ h₃ v

def rowTripleAdd (w v : RowTriple) : RowTriple :=
  ⟨add w.a v.a, add w.b v.b, add w.c v.c⟩

def rowTripleSub (v w : RowTriple) : RowTriple :=
  ⟨sub v.a w.a, sub v.b w.b, sub v.c w.c⟩

/-- The actual twelve-cell masking-row observation is uniform jointly in all three
    revealed operands. Its simulator has no assignment/witness argument. -/
theorem masking_rows_joint_perfectly_simulated {a b : Fp4} (basis : CornerPadBasis a b)
    (k₁ k₂ k₃ : Fp4) (h₁ : k₁ ≠ zero) (h₂ : k₂ ≠ zero) (h₃ : k₃ ≠ zero) :
    PerfectlySimulated
      (fun (w : RowTriple) (r : RowMaskCells) =>
        rowTripleAdd w (rowMaskCellsMap basis k₁ k₂ k₃ r))
      (fun (v : RowTriple) => v) := by
  let e := rowMaskCellsBij basis k₁ k₂ k₃ h₁ h₂ h₃
  intro w
  refine ⟨⟨fun r => rowTripleAdd w (e.toFun r),
    fun v => e.invFun (rowTripleSub v w), ?_, ?_⟩, fun _ => rfl⟩
  · intro r
    have h : rowTripleSub (rowTripleAdd w (e.toFun r)) w = e.toFun r := by
      apply RowTriple.ext <;> dsimp [rowTripleAdd, rowTripleSub] <;> constructive_ring
    rw [h, e.left_inv]
  · intro v
    rw [e.right_inv]
    apply RowTriple.ext <;> dsimp [rowTripleAdd, rowTripleSub] <;> constructive_ring

#verify_constructive Qsag.ZkHem.cornerCoeffs_left Qsag.ZkHem.cornerCoeffs_right
  Qsag.ZkHem.cornerPad_power_point Qsag.ZkHem.rowMask_determinant
  Qsag.ZkHem.masking_rows_joint_perfectly_simulated

/-- Salt-query bad-event accounting for a finite adaptive oracle run. The reference
    oracle and its answers may be arbitrary; the fresh uniform salt is sampled
    independently of this reference run. Repetitions in the query log only weaken the bound. -/
theorem fresh_hidden_salt_query_bound {F D A : Type} {N Q : Nat}
    (O : Fin N × F → D) (adv : RoAdv (Fin N) F D A)
    (hQ : (adv.queriedSalts O).length ≤ Q) :
    qsum N (fun s => if s ∈ adv.queriedSalts O then 1 else 0) ≤ Q :=
  Nat.le_trans (qsum_mem_list_le N (adv.queriedSalts O)) hQ

/-- The same finite bad event controls the witness-removing oracle re-keying, rather
    than an unrelated salt guess game. The adversary is adaptive through its oracle replies. -/
theorem fresh_hidden_salt_coupling {F D A : Type} [LawfulField F] {N : Nat}
    (O : Fin N × F → D) (adv : RoAdv (Fin N) F D A) (s : Fin N) (δ : F)
    (hFresh : s ∉ adv.queriedSalts O) :
    adv.run (saltShift (fun t => if t = s then δ else zero) O) = adv.run O := by
  apply salted_leaves_identical_until_bad _ (fun t => t = s)
  · intro t ht
    exact ite_eq_right ht
  · apply (RoAdv.avoids_iff O (fun t => t = s) adv).mpr
    intro t ht heq
    exact hFresh (heq ▸ ht)

#verify_constructive Qsag.ZkHem.fresh_hidden_salt_query_bound
  Qsag.ZkHem.fresh_hidden_salt_coupling


/-! ## One-table public Hem: a relation on exactly the variable subcube -/
section PublicHem
variable {F : Type} [LawfulField F]

/-- The three sparse relation matrices, represented by their Boolean-row/column entries.
    `Z` below has exactly `varBits` variables: masks and opening blinders are absent. -/
structure HemPublicShape (F : Type) where
  rowBits : Nat
  varBits : Nat
  selector : List Bool → F
  matrixA : List Bool → List Bool → F
  matrixB : List Bool → List Bool → F
  matrixC : List Bool → List Bool → F

def matrixProduct (k : Nat) (M : List Bool → List Bool → F)
    (Z : List Bool → F) (row : List Bool) : F :=
  bitSum k (fun col => mul (M row col) (Z col))

def HemPublicShape.Satisfied (s : HemPublicShape F) (Z : List Bool → F) : Prop :=
  ∀ row : List Bool, row.length = s.rowBits →
    rowGate (s.selector row) (matrixProduct s.varBits s.matrixA Z row)
      (matrixProduct s.varBits s.matrixB Z row)
      (matrixProduct s.varBits s.matrixC Z row) = zero

def HemPublicShape.rowFunction (s : HemPublicShape F) (Z : List Bool → F)
    (tau : List F) : List F → F :=
  rowSummand s.rowBits tau s.selector (matrixProduct s.varBits s.matrixA Z)
    (matrixProduct s.varBits s.matrixB Z) (matrixProduct s.varBits s.matrixC Z)

def HemPublicShape.rowProver (s : HemPublicShape F) (Z : List Bool → F)
    (tau : List F) (c : Nat → F) : WitnessRounds F :=
  cubeProver (rowLineRep s.rowBits tau s.selector (matrixProduct s.varBits s.matrixA Z)
    (matrixProduct s.varBits s.matrixB Z) (matrixProduct s.varBits s.matrixC Z)) s.rowBits c

theorem publicHem_row_claim_zero (s : HemPublicShape F) (Z : List Bool → F)
    (hZ : s.Satisfied Z) (tau : List F) :
    cubeClaim (s.rowFunction Z tau) s.rowBits [] = zero := by
  unfold cubeClaim
  simp only [List.length_nil, Nat.sub_zero, List.nil_append]
  calc
    _ = bitSum s.rowBits (fun _ => (zero : F)) := by
      apply bitSum_congr
      intro row hrow
      simp only [HemPublicShape.rowFunction, rowSummand,
        mle_bitPt s.rowBits _ row hrow, hZ row hrow, LawfulCommRing.mul_zero]
    _ = zero := bitSum_zero s.rowBits

theorem publicHem_row_prover_correct (s : HemPublicShape F) (Z : List Bool → F)
    (hZ : s.Satisfied Z) (tau : List F) (c : Nat → F) :
    (s.rowProver Z tau c).H = zero ∧
    (s.rowProver Z tau c).Honest s.rowBits 9 c ∧
    (s.rowProver Z tau c).claim 9 c s.rowBits = s.rowFunction Z tau (chalPrefix c s.rowBits) := by
  have h := cubeProver_proves (rowLineRep s.rowBits tau s.selector
    (matrixProduct s.varBits s.matrixA Z) (matrixProduct s.varBits s.matrixB Z)
    (matrixProduct s.varBits s.matrixC Z)) s.rowBits c
  exact ⟨h.1.trans (publicHem_row_claim_zero s Z hZ tau), h.honest, h.terminal⟩

/-- Matrix-vector multiplication commutes with multilinear evaluation of the row index. -/
theorem matrixProduct_mle (n k : Nat) (M : List Bool → List Bool → F)
    (Z : List Bool → F) (rx : List F) :
    mle n (matrixProduct k M Z) rx =
      bitSum k (fun col => mul (mle n (fun row => M row col) rx) (Z col)) := by
  unfold matrixProduct
  rw [mle_bitSum]
  apply bitSum_congr
  intro col _
  calc
    _ = mle n (fun row => mul (Z col) (M row col)) rx := by
      apply mle_congr
      intro row _
      exact LawfulCommRing.mul_comm _ _
    _ = mul (Z col) (mle n (fun row => M row col) rx) := mle_mul_left _ _ _ _
    _ = _ := LawfulCommRing.mul_comm _ _

/-- Three independent `ZKHEM_COMBINE` challenges `(c0, c1, c2)` (`zk_hem/protocol.rs:1593`). -/
structure HemCombine (F : Type) where
  c0 : F
  c1 : F
  c2 : F
  deriving DecidableEq

/-- Little-endian `k`-bit Boolean address of cell index `cell` (`bit 0` first). -/
def cellBits : Nat → Nat → List Bool
  | 0, _ => []
  | k + 1, cell => decide (cell % 2 = 1) :: cellBits k (cell / 2)

omit [LawfulField F] in
theorem cellBits_length : ∀ (k cell : Nat), (cellBits k cell).length = k
  | 0, _ => rfl
  | k + 1, cell => congrArg Nat.succ (cellBits_length k (cell / 2))

/-- Boolean-cube indicator of `cell` on `{0,1}^k`. -/
def cellIndicator : Nat → Nat → List Bool → F
  | 0, _, _ => one
  | k + 1, cell, col =>
    if col.headD false = decide (cell % 2 = 1) then
      cellIndicator k (cell / 2) col.tail
    else zero

/-- Verifier's `eq(ry, cell)` evaluation (`zk_hem/protocol.rs:1670-1676`). -/
def eqCell : Nat → Nat → List F → F
  | 0, _, _ => one
  | k + 1, cell, ry =>
    mul (if cell % 2 = 1 then ry.headD zero else sub one (ry.headD zero))
      (eqCell k (cell / 2) ry.tail)

theorem mle_cellIndicator : ∀ (k cell : Nat) (ry : List F),
    mle k (cellIndicator k cell) ry = eqCell k cell ry
  | 0, _, _ => rfl
  | k + 1, cell, ry => by
    show add (mul (sub one (ry.headD zero))
          (mle k (fun bs => if false = decide (cell % 2 = 1) then
            cellIndicator k (cell / 2) bs else zero) ry.tail))
        (mul (ry.headD zero)
          (mle k (fun bs => if true = decide (cell % 2 = 1) then
            cellIndicator k (cell / 2) bs else zero) ry.tail)) =
      mul (if cell % 2 = 1 then ry.headD zero else sub one (ry.headD zero))
        (eqCell k (cell / 2) ry.tail)
    by_cases hodd : cell % 2 = 1
    · simp only [hodd, decide_true, ↓reduceIte, Bool.false_eq_true, mle_const_zero,
        mle_cellIndicator k (cell / 2) ry.tail]
      constructive_ring
    · simp only [hodd, decide_false, ↓reduceIte, Bool.true_eq_false, mle_const_zero,
        mle_cellIndicator k (cell / 2) ry.tail]
      constructive_ring

theorem bitSum_cellIndicator_mul : ∀ (k cell : Nat) (Z : List Bool → F),
    bitSum k (fun col => mul (cellIndicator k cell col) (Z col)) = Z (cellBits k cell)
  | 0, _, Z => LawfulCommRing.one_mul (Z [])
  | k + 1, cell, Z => by
    show add (bitSum k (fun bs => mul (if false = decide (cell % 2 = 1) then
            cellIndicator k (cell / 2) bs else zero) (Z (false :: bs))))
        (bitSum k (fun bs => mul (if true = decide (cell % 2 = 1) then
            cellIndicator k (cell / 2) bs else zero) (Z (true :: bs)))) =
      Z (decide (cell % 2 = 1) :: cellBits k (cell / 2))
    by_cases hodd : cell % 2 = 1
    · simp only [hodd, decide_true, Bool.false_eq_true, ↓reduceIte, LawfulCommRing.zero_mul,
        bitSum_zero, bitSum_cellIndicator_mul k (cell / 2) (fun bs => Z (true :: bs)),
        LawfulCommRing.zero_add]
    · simp only [hodd, decide_false, Bool.true_eq_false, ↓reduceIte, LawfulCommRing.zero_mul,
        bitSum_zero, bitSum_cellIndicator_mul k (cell / 2) (fun bs => Z (false :: bs)),
        LawfulCommRing.add_zero]

/-- Horner-nested sum `∑_{j < m} lam^(j + 1) · f (off + j)`. -/
def hornerCells (lam : F) (f : Nat → F) : Nat → Nat → F
  | 0, _ => zero
  | m + 1, off => mul lam (add (f off) (hornerCells lam f m (off + 1)))

theorem mle_hornerCells_cellIndicator (k : Nat) (lam : F) (ry : List F) :
    ∀ (m off : Nat),
      mle k (fun col => hornerCells lam (fun cell => cellIndicator k cell col) m off) ry =
        hornerCells lam (fun cell => eqCell k cell ry) m off
  | 0, _ => mle_const_zero k ry
  | m + 1, off => by
    show mle k (fun col => mul lam (add (cellIndicator k off col)
        (hornerCells lam (fun cell => cellIndicator k cell col) m (off + 1)))) ry =
      mul lam (add (eqCell k off ry) (hornerCells lam (fun cell => eqCell k cell ry) m (off + 1)))
    rw [mle_mul_left, mle_add, mle_cellIndicator, mle_hornerCells_cellIndicator k lam ry m (off + 1)]

theorem bitSum_hornerCells_cellIndicator_mul (k : Nat) (lam : F) (Z : List Bool → F) :
    ∀ (m off : Nat),
      bitSum k (fun col =>
          mul (hornerCells lam (fun cell => cellIndicator k cell col) m off) (Z col)) =
        hornerCells lam (fun cell => Z (cellBits k cell)) m off
  | 0, _ => by
    calc
      _ = bitSum k (fun _ => (zero : F)) :=
        bitSum_congr k _ _ (fun col _ => LawfulCommRing.zero_mul (Z col))
      _ = zero := bitSum_zero k
  | m + 1, off => by
    have hsplit : bitSum k (fun col =>
          mul (mul lam (add (cellIndicator k off col)
            (hornerCells lam (fun cell => cellIndicator k cell col) m (off + 1)))) (Z col)) =
        mul lam (add (bitSum k (fun col => mul (cellIndicator k off col) (Z col)))
          (bitSum k (fun col =>
            mul (hornerCells lam (fun cell => cellIndicator k cell col) m (off + 1)) (Z col)))) := by
      rw [← bitSum_add, ← bitSum_mul_left]
      apply bitSum_congr
      intro col _
      constructive_ring
    show bitSum k (fun col =>
        mul (mul lam (add (cellIndicator k off col)
          (hornerCells lam (fun cell => cellIndicator k cell col) m (off + 1)))) (Z col)) =
      mul lam (add (Z (cellBits k off)) (hornerCells lam (fun cell => Z (cellBits k cell)) m (off + 1)))
    rw [hsplit, bitSum_cellIndicator_mul,
      bitSum_hornerCells_cellIndicator_mul k lam Z m (off + 1)]

theorem hornerCells_eq_evalCoeffs (lam : F) :
    ∀ (vals : List F) (off : Nat) (f : Nat → F),
      (∀ j < vals.length, f (off + j) = vals.getD j zero) →
      hornerCells lam f vals.length off = RoundPoly.evalCoeffs (zero :: vals) lam
  | [], _, _, _ => by
    show zero = add zero (mul lam zero)
    constructive_ring
  | v :: vs, off, f, hf => by
    have h0 : f off = v := by
      have h := hf 0 (Nat.zero_lt_succ _)
      rw [Nat.add_zero] at h
      exact h
    have ih := hornerCells_eq_evalCoeffs lam vs (off + 1) f (fun j hj => by
      have h := hf (j + 1) (Nat.succ_lt_succ hj)
      rw [Nat.succ_add_eq_add_succ off j]
      exact h)
    have h1 : RoundPoly.evalCoeffs (zero :: vs) lam = mul lam (RoundPoly.evalCoeffs vs lam) := by
      show add zero (mul lam (RoundPoly.evalCoeffs vs lam)) = mul lam (RoundPoly.evalCoeffs vs lam)
      exact LawfulCommRing.zero_add _
    rw [h1] at ih
    show mul lam (add (f off) (hornerCells lam f vs.length (off + 1))) =
      add zero (mul lam (add v (mul lam (RoundPoly.evalCoeffs vs lam))))
    rw [h0, ih, LawfulCommRing.zero_add]

/-- Prover's public-cell column weight `∑_{cell < numCells} λ^{cell+1} 1_{col=cell}`
    (`zk_hem/protocol.rs:1598-1602`). -/
def publicCellTableWeight (k numCells : Nat) (lam : F) (col : List Bool) : F :=
  hornerCells lam (fun cell => cellIndicator k cell col) numCells 0

/-- Verifier's public-cell terminal factor `∑_{cell < numCells} λ^{cell+1} eq(ry, cell)`
    (`zk_hem/protocol.rs:1668-1679`). -/
def publicCellEqSum (k numCells : Nat) (lam : F) (ry : List F) : F :=
  hornerCells lam (fun cell => eqCell k cell ry) numCells 0

/-- Verifier's public-cell initial claim `λ · 1 + ∑_{i < |public|} λ^{i+2} · public[i]`
    (`zk_hem/protocol.rs:1653-1656`). -/
def publicCellClaim (public : List F) (lam : F) : F :=
  RoundPoly.evalCoeffs (zero :: one :: public) lam

/-- First `m` committed cells `[Z(0), ..., Z(m - 1)]` on `s.varBits`. -/
def HemPublicShape.truePublicCells (s : HemPublicShape F) (Z : List Bool → F) (m : Nat) : List F :=
  (List.range m).map (fun cell => Z (cellBits s.varBits cell))

omit [LawfulField F] in
theorem truePublicCells_length (s : HemPublicShape F) (Z : List Bool → F) (m : Nat) :
    (s.truePublicCells Z m).length = m := by
  unfold HemPublicShape.truePublicCells
  rw [List.length_map, List.length_range]

/-- `Z(0) = 1` and `Z(1 ..= public.length) = public`. -/
def HemPublicShape.PublicCellsMatch (s : HemPublicShape F) (Z : List Bool → F)
    (public : List F) : Prop :=
  s.truePublicCells Z (public.length + 1) = one :: public

/-- Three-challenge linear combination `c0 A(rx, ·) + c1 B(rx, ·) + c2 C(rx, ·)`
    (`zk_hem/protocol.rs:1593, 1597`). -/
def HemPublicShape.baseColumnMatrix (s : HemPublicShape F) (rx : List F)
    (combine : HemCombine F) (col : List Bool) : F :=
  add (add (mul combine.c0 (mle s.rowBits (fun row => s.matrixA row col) rx))
    (mul combine.c1 (mle s.rowBits (fun row => s.matrixB row col) rx)))
    (mul combine.c2 (mle s.rowBits (fun row => s.matrixC row col) rx))

/-- Full `prove_public` column table (`zk_hem/protocol.rs:1597-1602`):
    `c0 A(rx, ·) + c1 B(rx, ·) + c2 C(rx, ·) + ∑_{cell=0..=numPublic} λ^{cell+1} 1_{col=cell}`. -/
def HemPublicShape.columnMatrix (s : HemPublicShape F) (rx : List F)
    (combine : HemCombine F) (numPublic : Nat) (lam : F) (col : List Bool) : F :=
  add (s.baseColumnMatrix rx combine col)
    (publicCellTableWeight s.varBits (numPublic + 1) lam col)

/-- True column sum on committed `Z`. -/
def HemPublicShape.columnClaim (s : HemPublicShape F) (Z : List Bool → F)
    (rx : List F) (combine : HemCombine F) (numPublic : Nat) (lam : F) : F :=
  add (add (add
    (mul combine.c0 (mle s.rowBits (matrixProduct s.varBits s.matrixA Z) rx))
    (mul combine.c1 (mle s.rowBits (matrixProduct s.varBits s.matrixB Z) rx)))
    (mul combine.c2 (mle s.rowBits (matrixProduct s.varBits s.matrixC Z) rx)))
    (RoundPoly.evalCoeffs (zero :: s.truePublicCells Z (numPublic + 1)) lam)

/-- `verify_public` initial column-sumcheck claim (`zk_hem/protocol.rs:1651-1656`). -/
def HemPublicShape.verifierColumnClaim (_s : HemPublicShape F)
    (combine : HemCombine F) (a b c : F) (public : List F) (lam : F) : F :=
  add (add (add (mul combine.c0 a) (mul combine.c1 b)) (mul combine.c2 c))
    (publicCellClaim public lam)

/-- `verify_public` terminal matrix evaluation at `(rx, ry)` (`zk_hem/protocol.rs:1666-1679`). -/
def HemPublicShape.verifierMatrixAt (s : HemPublicShape F) (rx ry : List F)
    (combine : HemCombine F) (numPublic : Nat) (lam : F) : F :=
  add (mle s.varBits (s.baseColumnMatrix rx combine) ry)
    (publicCellEqSum s.varBits (numPublic + 1) lam ry)

def HemPublicShape.columnProver (s : HemPublicShape F) (Z : List Bool → F)
    (rx : List F) (combine : HemCombine F) (numPublic : Nat) (lam : F)
    (c : Nat → F) : WitnessRounds F :=
  cubeProver (colLineRep s.varBits (s.columnMatrix rx combine numPublic lam) Z) s.varBits c

theorem publicHem_verifierMatrixAt_eq_mle (s : HemPublicShape F) (rx ry : List F)
    (combine : HemCombine F) (numPublic : Nat) (lam : F) :
    mle s.varBits (s.columnMatrix rx combine numPublic lam) ry =
      s.verifierMatrixAt rx ry combine numPublic lam := by
  unfold HemPublicShape.columnMatrix HemPublicShape.verifierMatrixAt
    publicCellTableWeight publicCellEqSum
  rw [mle_add, mle_hornerCells_cellIndicator]

private theorem getD_map_range {α : Type} (d : α) (f : Nat → α) :
    ∀ (m j : Nat), j < m → ((List.range m).map f).getD j d = f j := by
  intro m j hj
  rw [List.getD_eq_getElem?_getD]
  have hlen : j < ((List.range m).map f).length := by
    rw [List.length_map, List.length_range]
    exact hj
  rw [List.getElem?_eq_getElem hlen, Option.getD_some, List.getElem_map, List.getElem_range]

theorem publicHem_column_claim (s : HemPublicShape F) (Z : List Bool → F)
    (rx : List F) (combine : HemCombine F) (numPublic : Nat) (lam : F) :
    cubeClaim (colSummand s.varBits (s.columnMatrix rx combine numPublic lam) Z) s.varBits [] =
      s.columnClaim Z rx combine numPublic lam := by
  unfold cubeClaim
  simp only [List.length_nil, Nat.sub_zero, List.nil_append]
  have hPub : bitSum s.varBits (fun col =>
        mul (publicCellTableWeight s.varBits (numPublic + 1) lam col) (Z col)) =
      RoundPoly.evalCoeffs (zero :: s.truePublicCells Z (numPublic + 1)) lam := by
    unfold publicCellTableWeight
    rw [bitSum_hornerCells_cellIndicator_mul]
    have hlen := (truePublicCells_length s Z (numPublic + 1)).symm
    rw [hlen]
    apply hornerCells_eq_evalCoeffs
    intro j hj
    rw [Nat.zero_add]
    rw [truePublicCells_length] at hj
    exact (getD_map_range zero (fun cell => Z (cellBits s.varBits cell)) (numPublic + 1) j hj).symm
  have hBase : bitSum s.varBits (fun col => mul (s.baseColumnMatrix rx combine col) (Z col)) =
      add (add
        (mul combine.c0 (mle s.rowBits (matrixProduct s.varBits s.matrixA Z) rx))
        (mul combine.c1 (mle s.rowBits (matrixProduct s.varBits s.matrixB Z) rx)))
        (mul combine.c2 (mle s.rowBits (matrixProduct s.varBits s.matrixC Z) rx)) := by
    rw [matrixProduct_mle, matrixProduct_mle, matrixProduct_mle,
      ← bitSum_mul_left, ← bitSum_mul_left, ← bitSum_mul_left, ← bitSum_add, ← bitSum_add]
    apply bitSum_congr
    intro col _
    simp only [HemPublicShape.baseColumnMatrix]
    constructive_ring
  calc
    _ = bitSum s.varBits (fun col => mul (s.columnMatrix rx combine numPublic lam col) (Z col)) := by
      apply bitSum_congr
      intro col hcol
      simp only [colSummand, mle_bitPt s.varBits _ col hcol]
    _ = add (bitSum s.varBits (fun col => mul (s.baseColumnMatrix rx combine col) (Z col)))
          (bitSum s.varBits (fun col =>
            mul (publicCellTableWeight s.varBits (numPublic + 1) lam col) (Z col))) := by
      rw [← bitSum_add]
      apply bitSum_congr
      intro col _
      simp only [HemPublicShape.columnMatrix]
      constructive_ring
    _ = s.columnClaim Z rx combine numPublic lam := by
      unfold HemPublicShape.columnClaim
      rw [hBase, hPub]

theorem publicHem_column_prover_correct (s : HemPublicShape F) (Z : List Bool → F)
    (rx : List F) (combine : HemCombine F) (numPublic : Nat) (lam : F) (c : Nat → F) :
    (s.columnProver Z rx combine numPublic lam c).H =
        s.columnClaim Z rx combine numPublic lam ∧
    (s.columnProver Z rx combine numPublic lam c).Honest s.varBits 2 c ∧
    (s.columnProver Z rx combine numPublic lam c).claim 2 c s.varBits =
      mul (s.verifierMatrixAt rx (chalPrefix c s.varBits) combine numPublic lam)
        (mle s.varBits Z (chalPrefix c s.varBits)) := by
  have h := cubeProver_proves
    (colLineRep s.varBits (s.columnMatrix rx combine numPublic lam) Z) s.varBits c
  refine ⟨h.1.trans (publicHem_column_claim s Z rx combine numPublic lam), h.honest, ?_⟩
  have ht : (s.columnProver Z rx combine numPublic lam c).claim 2 c s.varBits =
      mul (mle s.varBits (s.columnMatrix rx combine numPublic lam) (chalPrefix c s.varBits))
        (mle s.varBits Z (chalPrefix c s.varBits)) := h.terminal
  rw [ht, publicHem_verifierMatrixAt_eq_mle]

/-- Honest completeness against `verify_public`: when `Z(0) = 1` and `Z(1..=numPublic) = public`,
    the prover's column sumcheck claim equals `verifierColumnClaim`. -/
theorem publicHem_verifier_column_complete (s : HemPublicShape F) (Z : List Bool → F)
    (public : List F) (hPub : s.PublicCellsMatch Z public)
    (rx : List F) (combine : HemCombine F) (lam : F) (c : Nat → F) :
    let a := mle s.rowBits (matrixProduct s.varBits s.matrixA Z) rx
    let b := mle s.rowBits (matrixProduct s.varBits s.matrixB Z) rx
    let cv := mle s.rowBits (matrixProduct s.varBits s.matrixC Z) rx
    (s.columnProver Z rx combine public.length lam c).H =
      s.verifierColumnClaim combine a b cv public lam ∧
    (s.columnProver Z rx combine public.length lam c).Honest s.varBits 2 c := by
  have hc := publicHem_column_prover_correct s Z rx combine public.length lam c
  refine ⟨hc.1.trans ?_, hc.2.1⟩
  unfold HemPublicShape.columnClaim HemPublicShape.verifierColumnClaim publicCellClaim
  rw [hPub]

theorem evalCoeffs_replicate_zero : ∀ (m : Nat) (x : F),
    RoundPoly.evalCoeffs (List.replicate m zero) x = zero
  | 0, _ => rfl
  | m + 1, x => by
    show add zero (mul x (RoundPoly.evalCoeffs (List.replicate m zero) x)) = zero
    rw [evalCoeffs_replicate_zero m x]
    constructive_ring

/-- Any degree-`≤ d` polynomial with at least one nonzero coefficient has at most `d` roots in
    any duplicate-free challenge pool `S` (proved constructively via `interp_evalAll`). -/
theorem roots_le_of_exists_nonzero [DecidableEq F] (d : Nat) (cs : List F)
    (hlen : cs.length ≤ d + 1) (hnz : ∃ c ∈ cs, c ≠ zero)
    (S : List F) (hS : S.Nodup) :
    (S.filter (fun x => decide (RoundPoly.evalCoeffs cs x = zero))).length ≤ d := by
  let R := S.filter (fun x => decide (RoundPoly.evalCoeffs cs x = zero))
  cases Nat.lt_or_ge d R.length with
  | inr hle => exact hle
  | inl hgt =>
    exfalso
    have hRnd : R.Nodup := hS.filter _
    let xs := R.take cs.length
    have hxsSub : xs.Sublist R := List.take_sublist cs.length R
    have hxsNd : xs.Nodup := hxsSub.nodup hRnd
    have hcsLeR : cs.length ≤ R.length := Nat.le_trans hlen hgt
    have hxsLen : xs.length = cs.length := List.length_take_of_le hcsLeR
    have hAllZero : evalAll cs xs = evalAll (List.replicate cs.length zero) xs := by
      unfold evalAll
      apply List.map_congr_left
      intro x hx
      have hxR : x ∈ R := hxsSub.subset hx
      have hx0 : RoundPoly.evalCoeffs cs x = zero := of_decide_eq_true (List.mem_filter.mp hxR).2
      rw [hx0, evalCoeffs_replicate_zero]
    have hEqCs : cs = List.replicate cs.length zero := by
      rw [← interp_evalAll xs cs hxsNd hxsLen.symm, hAllZero,
        interp_evalAll xs (List.replicate cs.length zero) hxsNd
          (List.length_replicate.trans hxsLen.symm)]
    obtain ⟨c, hcMem, hcNe⟩ := hnz
    rw [hEqCs] at hcMem
    exact hcNe (List.eq_of_mem_replicate hcMem)

theorem subCoeffs_exists_nonzero_of_ne [DecidableEq F] :
    ∀ (p q : List F), p.length = q.length → p ≠ q →
      ∃ c ∈ RoundPoly.subCoeffs p q, c ≠ zero
  | [], [], _, hne => absurd rfl hne
  | [], _ :: _, hlen, _ => by cases hlen
  | _ :: _, [], hlen, _ => by cases hlen
  | a :: ps, b :: qs, hlen, hne => by
    by_cases hab : a = b
    · subst hab
      have hneTail : ps ≠ qs := fun h => hne (congrArg (List.cons a) h)
      obtain ⟨c, hcMem, hcNe⟩ :=
        subCoeffs_exists_nonzero_of_ne ps qs (Nat.succ.inj hlen) hneTail
      exact ⟨c, List.mem_cons_of_mem (sub a a) hcMem, hcNe⟩
    · refine ⟨sub a b, List.mem_cons_self, fun h0 => hab (LawfulCommRing.sub_eq_zero_iff.mp h0)⟩

/-- **Soundness of `HEM_PUBLIC_CELLS` (`λ`) batching (`zk_hem/protocol.rs:1594-1596, 1650-1656`)**:
    Because `(a, b, c)` and `combine` are absorbed before `λ` is squeezed, any mismatch in either
    the combined row claim `c0 a + c1 b + c2 c` OR any public/constant cell `Z(0) = 1`,
    `Z(1..=numPublic) = public` makes `verifierColumnClaim - columnClaim` a nonzero polynomial of
    degree `≤ public.length + 1` in `λ` (erroneous `row_values` sit in `λ^0` and cannot cancel
    erroneous public cells in `λ^1 .. λ^{numPublic+1}`). -/
theorem publicHem_lambda_batch_soundness [DecidableEq F]
    (s : HemPublicShape F) (Z : List Bool → F) (rx : List F)
    (combine : HemCombine F) (a b c : F) (public : List F)
    (hBad : ¬ (add (add (mul combine.c0 a) (mul combine.c1 b)) (mul combine.c2 c) =
        add (add
          (mul combine.c0 (mle s.rowBits (matrixProduct s.varBits s.matrixA Z) rx))
          (mul combine.c1 (mle s.rowBits (matrixProduct s.varBits s.matrixB Z) rx)))
          (mul combine.c2 (mle s.rowBits (matrixProduct s.varBits s.matrixC Z) rx)) ∧
      s.PublicCellsMatch Z public))
    (S : List F) (hS : S.Nodup) :
    (S.filter (fun lam =>
      decide (s.verifierColumnClaim combine a b c public lam =
        s.columnClaim Z rx combine public.length lam))).length ≤ public.length + 1 := by
  let lhsBase := add (add (mul combine.c0 a) (mul combine.c1 b)) (mul combine.c2 c)
  let rhsBase := add (add
    (mul combine.c0 (mle s.rowBits (matrixProduct s.varBits s.matrixA Z) rx))
    (mul combine.c1 (mle s.rowBits (matrixProduct s.varBits s.matrixB Z) rx)))
    (mul combine.c2 (mle s.rowBits (matrixProduct s.varBits s.matrixC Z) rx))
  let pPoly : List F := lhsBase :: one :: public
  let qPoly : List F := rhsBase :: s.truePublicCells Z (public.length + 1)
  have hpLen : pPoly.length = public.length + 2 := rfl
  have hqLen : qPoly.length = public.length + 2 :=
    congrArg Nat.succ (truePublicCells_length s Z (public.length + 1))
  have hpqNe : pPoly ≠ qPoly := by
    intro hEq
    obtain ⟨hBase, hCells⟩ := List.cons.inj hEq
    exact hBad ⟨hBase, hCells.symm⟩
  have hSubLen : (RoundPoly.subCoeffs pPoly qPoly).length ≤ (public.length + 1) + 1 := by
    rw [RoundPoly.subCoeffs_length, hpLen, hqLen, Nat.max_self]
    exact Nat.le_refl _
  have hNz := subCoeffs_exists_nonzero_of_ne pPoly qPoly (hpLen.trans hqLen.symm) hpqNe
  have hRoots := roots_le_of_exists_nonzero (public.length + 1)
    (RoundPoly.subCoeffs pPoly qPoly) hSubLen hNz S hS
  have hFilt : S.filter (fun lam =>
        decide (s.verifierColumnClaim combine a b c public lam =
          s.columnClaim Z rx combine public.length lam)) =
      S.filter (fun lam =>
        decide (RoundPoly.evalCoeffs (RoundPoly.subCoeffs pPoly qPoly) lam = zero)) := by
    apply List.filter_congr
    intro lam _
    have hEval : RoundPoly.evalCoeffs (RoundPoly.subCoeffs pPoly qPoly) lam =
        sub (s.verifierColumnClaim combine a b c public lam)
          (s.columnClaim Z rx combine public.length lam) := by
      rw [RoundPoly.evalCoeffs_sub]
      show sub (add lhsBase (mul lam (RoundPoly.evalCoeffs (one :: public) lam)))
          (add rhsBase (mul lam (RoundPoly.evalCoeffs (s.truePublicCells Z (public.length + 1)) lam))) =
        sub (add lhsBase (add zero (mul lam (RoundPoly.evalCoeffs (one :: public) lam))))
          (add rhsBase (add zero (mul lam (RoundPoly.evalCoeffs (s.truePublicCells Z (public.length + 1)) lam))))
      constructive_ring
    rw [hEval]
    by_cases h : s.verifierColumnClaim combine a b c public lam =
        s.columnClaim Z rx combine public.length lam
    · rw [decide_eq_true h, decide_eq_true (LawfulCommRing.sub_eq_zero_iff.mpr h)]
    · rw [decide_eq_false h, decide_eq_false (fun h0 => h (LawfulCommRing.sub_eq_zero_iff.mp h0))]
  rw [hFilt]
  exact hRoots

/-- All `|S|^3` triples `(c0, c1, c2) ∈ S³` of `ZKHEM_COMBINE`. -/
def combineTriples (S : List F) : List (HemCombine F) :=
  S.flatMap fun c0 => S.flatMap fun c1 => S.flatMap fun c2 => [⟨c0, c1, c2⟩]

omit [LawfulField F] in
theorem combineTriples_length (S : List F) :
    (combineTriples S).length = S.length * (S.length * S.length) := by
  unfold combineTriples
  have h1 : ∀ c0 c1 : F, (S.flatMap fun c2 => ([⟨c0, c1, c2⟩] : List (HemCombine F))).length = S.length := by
    intro c0 c1
    induction S with
    | nil => rfl
    | cons _ tl ih => simp only [List.flatMap_cons, List.length_append, List.length_singleton, ih, Nat.add_comm]
  have h2 : ∀ c0 : F, (S.flatMap fun c1 => S.flatMap fun c2 => ([⟨c0, c1, c2⟩] : List (HemCombine F))).length =
      S.length * S.length := by
    intro c0
    generalize hM : S.length = M
    have h1' : ∀ c1 : F, (S.flatMap fun c2 => ([⟨c0, c1, c2⟩] : List (HemCombine F))).length = M :=
      fun c1 => (h1 c0 c1).trans hM
    clear h1 hM
    induction S with
    | nil => simp
    | cons x tl ih =>
      simp only [List.flatMap_cons, List.length_append, h1' x, ih, List.length_cons,
        Nat.add_mul, Nat.one_mul, Nat.add_comm]
  generalize hN : S.length * S.length = N at h2
  induction S with
  | nil => simp
  | cons x tl ih =>
    simp only [List.flatMap_cons, List.length_append, h2 x, ih, List.length_cons,
      Nat.add_mul, Nat.one_mul, Nat.add_comm]

omit [LawfulField F] in
private theorem length_filter_flatMap_le {α β : Type} (p : β → Bool) (B : Nat) :
    ∀ (L : List α) (f : α → List β),
      (∀ x ∈ L, ((f x).filter p).length ≤ B) →
      ((L.flatMap f).filter p).length ≤ L.length * B
  | [], _, _ => Nat.zero_le _
  | x :: xs, f, h => by
    simp only [List.flatMap_cons, List.filter_append, List.length_append, List.length_cons]
    have hx := h x List.mem_cons_self
    have hxs := length_filter_flatMap_le p B xs f (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hmul : (xs.length + 1) * B = B + xs.length * B := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    rw [hmul]
    exact Nat.add_le_add hx hxs

omit [LawfulField F] in
private theorem length_filter_flatMap_append {α β : Type} (p : β → Bool) :
    ∀ (B : List α) (f₁ f₂ : α → List β),
      ((B.flatMap fun y => f₁ y ++ f₂ y).filter p).length =
        ((B.flatMap f₁).filter p).length + ((B.flatMap f₂).filter p).length
  | [], _, _ => rfl
  | _ :: bs, f₁, f₂ => by
    simp only [List.flatMap_cons, List.filter_append, List.length_append]
    rw [length_filter_flatMap_append p bs f₁ f₂]
    ac_rfl

omit [LawfulField F] in
private theorem length_filter_flatMap_const_nil {α β : Type} (p : β → Bool) :
    ∀ (B : List α), ((B.flatMap fun _ => ([] : List β)).filter p).length = 0
  | [] => rfl
  | _ :: bs => length_filter_flatMap_const_nil p bs

omit [LawfulField F] in
private theorem length_filter_flatMap_comm {α β γ : Type} (p : γ → Bool) :
    ∀ (A : List α) (B : List β) (g : α → β → List γ),
      ((A.flatMap fun x => B.flatMap fun y => g x y).filter p).length =
        ((B.flatMap fun y => A.flatMap fun x => g x y).filter p).length
  | [], B, _ => (length_filter_flatMap_const_nil p B).symm
  | a :: as, B, g => by
    simp only [List.flatMap_cons, List.filter_append, List.length_append]
    rw [length_filter_flatMap_comm p as B g,
      length_filter_flatMap_append p B (g a) (fun y => as.flatMap fun x => g x y)]

private theorem affine_filter_le_one [DecidableEq F] (S : List F) (hS : S.Nodup)
    (k d : F) (hd : d ≠ zero) (pred : F → Bool)
    (hp : ∀ x : F, pred x = true → add k (mul x d) = zero) :
    ((S.flatMap fun x => [x]).filter pred).length ≤ 1 := by
  have hMap : (S.flatMap fun x => [x]) = S := by
    induction S with
    | nil => rfl
    | cons a tl ih => simp only [List.flatMap_cons, List.singleton_append, ih]
  rw [hMap]
  apply length_le_one_of_all_eq _ (hS.filter _)
  intro x hx y hy
  exact affine_root_unique d k x y hd
    (by have h := hp x (List.mem_filter.mp hx).2; rw [LawfulCommRing.add_comm, LawfulCommRing.mul_comm] at h; exact h)
    (by have h := hp y (List.mem_filter.mp hy).2; rw [LawfulCommRing.add_comm, LawfulCommRing.mul_comm] at h; exact h)

private theorem length_filter_singleton_map {α β : Type} (p : β → Bool) (f : α → β) :
    ∀ (S : List α), ((S.flatMap fun x => [f x]).filter p).length =
      ((S.flatMap fun x => [x]).filter (fun x => p (f x))).length
  | [] => rfl
  | x :: xs => by
    simp only [List.flatMap_cons, List.filter_append, List.length_append, List.filter_cons,
      List.filter_nil, length_filter_singleton_map p f xs]
    cases p (f x) <;> rfl

/-- **Soundness of 3 independent `ZKHEM_COMBINE` challenges `(c0, c1, c2)` (`protocol.rs:1649`)**:
    Whenever `(a, b, c) ≠ (Az(rx), Bz(rx), Cz(rx))`, at most `|S|²` of the `|S|³` challenge
    triples in `S³` equate `c0 a + c1 b + c2 c` with `c0 Az(rx) + c1 Bz(rx) + c2 Cz(rx)`
    (error `≤ 1 / |S|`, replacing the legacy `(1, ν, ν²)` `2 / |S|` bound). -/
theorem publicHem_combine_three_challenge_soundness [DecidableEq F]
    (a b c Az Bz Cz : F)
    (hWrong : ¬ (a = Az ∧ b = Bz ∧ c = Cz))
    (S : List F) (hS : S.Nodup) :
    ((combineTriples S).filter (fun ch =>
      decide (add (add (mul ch.c0 a) (mul ch.c1 b)) (mul ch.c2 c) =
        add (add (mul ch.c0 Az) (mul ch.c1 Bz)) (mul ch.c2 Cz)))).length ≤
      S.length * S.length := by
  let pred : HemCombine F → Bool := fun ch =>
    decide (add (add (mul ch.c0 a) (mul ch.c1 b)) (mul ch.c2 c) =
      add (add (mul ch.c0 Az) (mul ch.c1 Bz)) (mul ch.c2 Cz))
  let da := sub a Az
  let db := sub b Bz
  let dc := sub c Cz
  have hLin : ∀ ch : HemCombine F, pred ch = true →
      add (add (mul ch.c0 da) (mul ch.c1 db)) (mul ch.c2 dc) = zero := by
    intro ch hp
    have heq := of_decide_eq_true hp
    have e : add (add (mul ch.c0 da) (mul ch.c1 db)) (mul ch.c2 dc) =
        sub (add (add (mul ch.c0 a) (mul ch.c1 b)) (mul ch.c2 c))
          (add (add (mul ch.c0 Az) (mul ch.c1 Bz)) (mul ch.c2 Cz)) := by
      dsimp only [da, db, dc]
      constructive_ring
    rw [e, heq, LawfulCommRing.sub_self]
  by_cases hdc : dc = zero
  · by_cases hdb : db = zero
    · have hda : da ≠ zero := fun hda0 =>
        hWrong ⟨LawfulCommRing.sub_eq_zero_iff.mp hda0,
          LawfulCommRing.sub_eq_zero_iff.mp hdb,
          LawfulCommRing.sub_eq_zero_iff.mp hdc⟩
      have hSwap1 : ((combineTriples S).filter pred).length =
          ((S.flatMap fun c1 => S.flatMap fun c2 => S.flatMap fun c0 =>
            ([⟨c0, c1, c2⟩] : List (HemCombine F))).filter pred).length := by
        unfold combineTriples
        rw [length_filter_flatMap_comm pred S S]
        have hInner : ∀ c1 : F,
            ((S.flatMap fun c0 => S.flatMap fun c2 => ([⟨c0, c1, c2⟩] : List (HemCombine F))).filter pred).length =
            ((S.flatMap fun c2 => S.flatMap fun c0 => ([⟨c0, c1, c2⟩] : List (HemCombine F))).filter pred).length :=
          fun c1 => length_filter_flatMap_comm pred S S _
        clear hLin hWrong hda hdb hdc
        induction S with
        | nil => rfl
        | cons x tl ih =>
          simp only [List.flatMap_cons, List.filter_append, List.length_append, hInner x, ih]
      rw [hSwap1]
      have hb1 := length_filter_flatMap_le pred S.length S
        (fun c1 => S.flatMap fun c2 => S.flatMap fun c0 => [⟨c0, c1, c2⟩])
        (fun c1 _ => by
          have hb2 := length_filter_flatMap_le pred 1 S
            (fun c2 => S.flatMap fun c0 => [⟨c0, c1, c2⟩])
            (fun c2 _ => by
              rw [length_filter_singleton_map pred (fun c0 => ⟨c0, c1, c2⟩) S]
              exact affine_filter_le_one S hS (add (mul c1 db) (mul c2 dc)) da hda _
                (fun c0 hp => by
                  have hl := hLin ⟨c0, c1, c2⟩ hp
                  have e : add (add (mul c1 db) (mul c2 dc)) (mul c0 da) =
                      add (add (mul c0 da) (mul c1 db)) (mul c2 dc) := by constructive_ring
                  exact e.trans hl))
          simpa only [Nat.mul_one] using hb2)
      exact hb1
    · have hSwap : ((combineTriples S).filter pred).length =
          ((S.flatMap fun c0 => S.flatMap fun c2 => S.flatMap fun c1 =>
            ([⟨c0, c1, c2⟩] : List (HemCombine F))).filter pred).length := by
        unfold combineTriples
        have hInner : ∀ c0 : F,
            ((S.flatMap fun c1 => S.flatMap fun c2 => ([⟨c0, c1, c2⟩] : List (HemCombine F))).filter pred).length =
            ((S.flatMap fun c2 => S.flatMap fun c1 => ([⟨c0, c1, c2⟩] : List (HemCombine F))).filter pred).length :=
          fun c0 => length_filter_flatMap_comm pred S S _
        clear hLin hWrong hdb hdc
        induction S with
        | nil => rfl
        | cons x tl ih =>
          simp only [List.flatMap_cons, List.filter_append, List.length_append, hInner x, ih]
      rw [hSwap]
      exact length_filter_flatMap_le pred S.length S _
        (fun c0 _ => by
          have hb2 := length_filter_flatMap_le pred 1 S
            (fun c2 => S.flatMap fun c1 => [⟨c0, c1, c2⟩])
            (fun c2 _ => by
              rw [length_filter_singleton_map pred (fun c1 => ⟨c0, c1, c2⟩) S]
              exact affine_filter_le_one S hS (add (mul c0 da) (mul c2 dc)) db hdb _
                (fun c1 hp => by
                  have hl := hLin ⟨c0, c1, c2⟩ hp
                  have e : add (add (mul c0 da) (mul c2 dc)) (mul c1 db) =
                      add (add (mul c0 da) (mul c1 db)) (mul c2 dc) := by constructive_ring
                  exact e.trans hl))
          simpa only [Nat.mul_one] using hb2)
  · unfold combineTriples
    exact length_filter_flatMap_le pred S.length S _
      (fun c0 _ => by
        have hb2 := length_filter_flatMap_le pred 1 S
          (fun c1 => S.flatMap fun c2 => [⟨c0, c1, c2⟩])
          (fun c1 _ => by
            rw [length_filter_singleton_map pred (fun c2 => ⟨c0, c1, c2⟩) S]
            exact affine_filter_le_one S hS (add (mul c0 da) (mul c1 db)) dc hdc _
              (fun c2 hp => hLin ⟨c0, c1, c2⟩ hp))
        simpa only [Nat.mul_one] using hb2)

/-- Concretesumcheck flip bound against the constructed honest round polynomial.
    This gives degree 9 for `rowLineRep`, degree 2 for `colLineRep`. -/
theorem cubeProver_round_flip_bound [DecidableEq F] {g : List F → F} {d : Nat}
    (L : LineRep g d) (n : Nat) (cs : List F) (hcs : cs.length < n)
    (msg : List F) (hm : msg.length ≤ d + 1)
    (hWrong : add (RoundPoly.evalCoeffs msg zero) (RoundPoly.evalCoeffs msg one) ≠
      cubeClaim g n cs) (S : List F) (hS : S.Nodup) :
    (S.filter (fun x => decide (RoundPoly.evalCoeffs msg x = cubeRound g n cs x))).length ≤ d := by
  have hrep := cubeMsg_rep L n cs
  have hne : add (RoundPoly.evalCoeffs msg zero) (RoundPoly.evalCoeffs msg one) ≠
      add (RoundPoly.evalCoeffs (cubeMsg L n cs) zero)
        (RoundPoly.evalCoeffs (cubeMsg L n cs) one) := by
    rw [hrep.2 zero, hrep.2 one, cubeRound_telescope g n cs hcs]
    exact hWrong
  have hb := masked_sumcheck_round_flip_le_degree d msg (cubeMsg L n cs) hm hrep.1 hne S hS
  have heq : S.filter (fun x => decide (RoundPoly.evalCoeffs msg x = cubeRound g n cs x)) =
      S.filter (fun x => decide (RoundPoly.evalCoeffs msg x =
        RoundPoly.evalCoeffs (cubeMsg L n cs) x)) := by
    apply List.filter_congr
    intro x _
    rw [hrep.2 x]
  rw [heq]
  exact hb
end PublicHem

/-- **Tooth (`λ = 0` unbinds `Z[0] = 1` and `public`)**:
    When `lam = zero`, `verifierColumnClaim` agrees with `columnClaim` even on an all-zero table
    `Z = 0` that violates `Z[0] = 1` and `public = [1]`. -/
theorem tooth_publicHem_zero_lambda_unbinds_public_cells :
    let s : HemPublicShape Fp4 :=
      ⟨1, 1, fun _ => zero, fun _ _ => zero, fun _ _ => zero, fun _ _ => zero⟩
    let Z : List Bool → Fp4 := fun _ => zero
    let combine : HemCombine Fp4 := ⟨one, one, one⟩
    ¬ s.PublicCellsMatch Z [one] ∧
    s.verifierColumnClaim combine zero zero zero [one] zero =
      s.columnClaim Z [zero] combine 1 zero := by
  refine ⟨fun h => ?_, ?_⟩
  · have h0 : (zero : Fp4) = one := (List.cons.inj h).1
    exact LawfulField.zero_ne_one h0
  · unfold HemPublicShape.verifierColumnClaim HemPublicShape.columnClaim publicCellClaim
      HemPublicShape.truePublicCells matrixProduct
    simp only [List.range, List.range.loop, List.map_cons, List.map_nil, mle_cons, mle_zero_dim,
      bitSum, LawfulCommRing.zero_mul, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    rfl

theorem inhabited_publicHem_lambda_batch_soundness :
    ∃ (s : HemPublicShape Fp4) (Z : List Bool → Fp4) (rx : List Fp4)
      (combine : HemCombine Fp4) (a b c : Fp4) (public : List Fp4) (S : List Fp4),
      ¬ (add (add (mul combine.c0 a) (mul combine.c1 b)) (mul combine.c2 c) =
          add (add
            (mul combine.c0 (mle s.rowBits (matrixProduct s.varBits s.matrixA Z) rx))
            (mul combine.c1 (mle s.rowBits (matrixProduct s.varBits s.matrixB Z) rx)))
            (mul combine.c2 (mle s.rowBits (matrixProduct s.varBits s.matrixC Z) rx)) ∧
        s.PublicCellsMatch Z public) ∧
      S.Nodup := by
  refine ⟨⟨1, 1, fun _ => zero, fun _ _ => zero, fun _ _ => zero, fun _ _ => zero⟩,
    fun _ => zero, [zero], ⟨one, one, one⟩, zero, zero, zero, [one], [zero, one], ?_, ?_⟩
  · intro h
    have h0 : (zero : Fp4) = one := (List.cons.inj h.2).1
    exact LawfulField.zero_ne_one h0
  · refine List.nodup_cons.mpr ⟨fun h => ?_, List.nodup_singleton one⟩
    rcases List.mem_singleton.mp h with h0
    exact LawfulField.zero_ne_one h0

#verify_constructive Qsag.ZkHem.publicHem_row_prover_correct
  Qsag.ZkHem.publicHem_verifierMatrixAt_eq_mle
  Qsag.ZkHem.publicHem_column_prover_correct
  Qsag.ZkHem.publicHem_verifier_column_complete
  Qsag.ZkHem.publicHem_lambda_batch_soundness
  Qsag.ZkHem.publicHem_combine_three_challenge_soundness
  Qsag.ZkHem.tooth_publicHem_zero_lambda_unbinds_public_cells
  Qsag.ZkHem.inhabited_publicHem_lambda_batch_soundness
  Qsag.ZkHem.cubeProver_round_flip_bound
#verify_inhabited Qsag.ZkHem.publicHem_lambda_batch_soundness
  Qsag.ZkHem.inhabited_publicHem_lambda_batch_soundness
#tooth_pair Qsag.ZkHem.publicHem_lambda_batch_soundness vs
  Qsag.ZkHem.tooth_publicHem_zero_lambda_unbinds_public_cells



/-! ## Fresh salt vectors: query hits and birthday collisions in one finite experiment -/

/-- Exact bad-leaf mass for `m` independent uniform salts. A query hit or a repeat of an
    earlier salt is bad; after the first bad salt all suffixes are counted. The reference
    query list may be the adaptive `RoAdv.queriedSalts O` of any fixed reference oracle. -/
def saltVectorBadMass {N : Nat} (queries : List (Fin N)) : List (Fin N) → Nat → Nat
  | _, 0 => 0
  | prior, m + 1 => qsum N (fun s =>
      if s ∈ queries ++ prior then N ^ m else saltVectorBadMass queries (s :: prior) m)

private theorem saltBinom_succ (m : Nat) : (m + 1) * m / 2 = m + m * (m - 1) / 2 := by
  have he : (m + 1) * m = 2 * m + m * (m - 1) := by
    cases m with
    | zero => rfl
    | succ k =>
      simp only [Nat.add_sub_cancel]
      have h : k + 1 + 1 = 2 + k := by omega
      rw [h, Nat.add_mul]
      rw [Nat.mul_comm k (k + 1)]
  rw [he]
  omega

/-- Exact union bound `m(|queries|+|prior|) + binom(m,2)`, with no independence
    assumption on the query list's dependence on the *reference oracle*. The newly sampled
    salt vector is independent of that reference run. -/
theorem saltVectorBadMass_bound {N : Nat} (queries : List (Fin N)) :
    ∀ (m : Nat) (prior : List (Fin N)),
      saltVectorBadMass queries prior m ≤
        (m * (queries.length + prior.length) + m * (m - 1) / 2) * N ^ (m - 1)
  | 0, prior => by
    simp only [saltVectorBadMass, Nat.zero_mul, Nat.zero_div, Nat.zero_add]
    exact Nat.le_refl 0
  | m + 1, prior => by
    have hSplit := qsum_le_qsum (n := N) (fun s : Fin N => show
        (if s ∈ queries ++ prior then N ^ m else saltVectorBadMass queries (s :: prior) m) ≤
        (if s ∈ queries ++ prior then N ^ m else 0) + saltVectorBadMass queries (s :: prior) m from by
      split <;> omega)
    rw [qsum_add] at hSplit
    have hBad : qsum N (fun s => if s ∈ queries ++ prior then N ^ m else 0) ≤
        (queries.length + prior.length) * N ^ m := by
      have hEq : qsum N (fun s => if s ∈ queries ++ prior then N ^ m else 0) =
          qsum N (fun s => (if s ∈ queries ++ prior then 1 else 0) * N ^ m) := by
        apply qsum_congr
        intro s
        split <;> simp
      rw [hEq, qsum_mul_right]
      have h := Nat.mul_le_mul_right (N ^ m) (qsum_mem_list_le N (queries ++ prior))
      simpa only [List.length_append] using h
    have hFuture : qsum N (fun s => saltVectorBadMass queries (s :: prior) m) ≤
        (m * (queries.length + prior.length + 1) + m * (m - 1) / 2) * N ^ m := by
      have h := qsum_le_qsum (fun s : Fin N => saltVectorBadMass_bound queries m (s :: prior))
      simp only [List.length_cons, ← Nat.add_assoc] at h
      rw [qsum_const] at h
      have he : N * ((m * (queries.length + prior.length + 1) + m * (m - 1) / 2) * N ^ (m - 1)) =
          (m * (queries.length + prior.length + 1) + m * (m - 1) / 2) * N ^ m := by
        cases m with
        | zero => simp
        | succ k =>
          simp only [Nat.add_sub_cancel, Nat.pow_succ]
          ac_rfl
      rw [he] at h
      exact h
    have hTotal := Nat.le_trans hSplit (Nat.add_le_add hBad hFuture)
    have hc : queries.length + prior.length +
        (m * (queries.length + prior.length + 1) + m * (m - 1) / 2) =
        (m + 1) * (queries.length + prior.length) + (m + 1) * m / 2 := by
      rw [saltBinom_succ, Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one]
      omega
    simpa only [saltVectorBadMass, Nat.add_sub_cancel, ← Nat.add_mul, hc] using hTotal

/-- Query-hit and repeated-salt probability for `m` fresh independent salts. -/
theorem saltVector_bad_probability {N : Nat} (hN : 0 < N)
    (queries : List (Fin N)) (m : Nat) :
    RatBound.le
      ⟨saltVectorBadMass queries [] m, N ^ m, Nat.pow_pos hN⟩
      ⟨m * queries.length + m * (m - 1) / 2, N, hN⟩ := by
  unfold RatBound.le
  dsimp only
  cases m with
  | zero => simp only [saltVectorBadMass, Nat.zero_mul, Nat.zero_div, Nat.zero_add]; omega
  | succ k =>
    have h := Nat.mul_le_mul_right N (saltVectorBadMass_bound queries (k + 1) [])
    simpa only [List.length_nil, Nat.add_zero, Nat.add_sub_cancel, Nat.mul_assoc,
      ← Nat.pow_succ] using h

#verify_constructive Qsag.ZkHem.saltVectorBadMass_bound Qsag.ZkHem.saltVector_bad_probability



/-! ## Five-table companion word together with all four announced kernel claims

This is the linear-opening part of the private protocol. The reference assignment is fixed
public data with the same public kernel claim. Raw assignment openings and the two sumcheck
views are not included in this lemma; composing their masking coins remains necessary. -/

theorem embed_mul (a b : Fp) : embed (mul a b) = mul (embed a) (embed b) :=
  GoldilocksField.GoldilocksExt4.embedBase_mul a b

def padAdd (a b : Pad) : Pad :=
  ⟨add a.r0 b.r0, add a.r1 b.r1, add a.r2 b.r2, add a.r3 b.r3⟩

def padScale (a : Fp) (r : Pad) : Pad :=
  ⟨mul a r.r0, mul a r.r1, mul a r.r2, mul a r.r3⟩

theorem padMap_add (z : Fp4) (a b : Pad) :
    padMap z (padAdd a b) = add (padMap z a) (padMap z b) := by
  simp only [padMap, padAdd, embed_add]
  constructive_ring

theorem padMap_scale (z : Fp4) (a : Fp) (r : Pad) :
    padMap z (padScale a r) = mul (embed a) (padMap z r) := by
  simp only [padMap, padScale, embed_mul]
  constructive_ring

/-- The five committed base-field tables, packed as one assignment and four companions. -/
def privateBatchWord {ι : Type} (β : Fp4) (Z : ι → Fp) (C : ι → Pad) : ι → Fp4 :=
  fun i => add (embed (Z i)) (mul β (padMap β (C i)))

theorem privateBatchWord_five_terms {ι : Type} (β : Fp4) (Z : ι → Fp) (C : ι → Pad) (i : ι) :
    privateBatchWord β Z C i =
      add (add (add (add (embed (Z i)) (mul β (embed (C i).r0)))
        (mul (mul β β) (embed (C i).r1)))
        (mul (mul β (mul β β)) (embed (C i).r2)))
        (mul (mul β (mul β (mul β β))) (embed (C i).r3)) := by
  simp only [privateBatchWord, padMap]
  constructive_ring

structure CompanionClaims where
  sigma0 : Fp4
  sigma1 : Fp4
  sigma2 : Fp4
  sigma3 : Fp4

theorem CompanionClaims.ext {x y : CompanionClaims}
    (h0 : x.sigma0 = y.sigma0) (h1 : x.sigma1 = y.sigma1)
    (h2 : x.sigma2 = y.sigma2) (h3 : x.sigma3 = y.sigma3) : x = y := by
  cases x; cases y; cases h0; cases h1; cases h2; cases h3; rfl

def companionClaims {ι : Type} (K : LinForm ι Fp4) (C : ι → Pad) : CompanionClaims :=
  ⟨K.app (fun i => embed (C i).r0), K.app (fun i => embed (C i).r1),
   K.app (fun i => embed (C i).r2), K.app (fun i => embed (C i).r3)⟩

def privateCompanionView {ι : Type} (β : Fp4) (K : LinForm ι Fp4)
    (Z : ι → Fp) (C : ι → Pad) : (ι → Fp4) × CompanionClaims :=
  (privateBatchWord β Z C, companionClaims K C)

def companionCancelPad (β : Fp4) : Pad := padInv β (LawfulField.inv β)

theorem companionCancelPad_sound (β : Fp4) (hβ : β.c1 ≠ zero) :
    mul β (padMap β (companionCancelPad β)) = one := by
  unfold companionCancelPad
  rw [padMap_padInv β hβ]
  apply LawfulField.mul_inv_cancel
  intro heq
  exact hβ ((congrArg GoldilocksField.GoldilocksExt4.c1 heq).trans fp4_zero_c1)

/-- Translating all four companion tables by fixed multiples of the base-field
    assignment difference preserves their uniform distribution. -/
def companionTranslate {ι : Type} (β : Fp4) (delta : ι → Fp) (C : ι → Pad) : ι → Pad :=
  fun i => padAdd (C i) (padScale (delta i) (companionCancelPad β))

def companionTranslateBij {ι : Type} (β : Fp4) (delta : ι → Fp) :
    SimpleEquiv (ι → Pad) (ι → Pad) where
  toFun := companionTranslate β delta
  invFun := companionTranslate β (fun i => neg (delta i))
  left_inv C := by
    funext i
    apply Pad.ext <;> dsimp [companionTranslate, padAdd, padScale] <;> constructive_ring
  right_inv C := by
    funext i
    apply Pad.ext <;> dsimp [companionTranslate, padAdd, padScale] <;> constructive_ring

theorem privateBatchWord_translate {ι : Type} (β : Fp4) (hβ : β.c1 ≠ zero)
    (Z Z0 : ι → Fp) (C : ι → Pad) :
    privateBatchWord β Z0 (companionTranslate β (fun i => sub (Z i) (Z0 i)) C) =
      privateBatchWord β Z C := by
  funext i
  have hc := companionCancelPad_sound β hβ
  simp only [privateBatchWord, companionTranslate, padMap_add, padMap_scale, embed_sub]
  calc
    _ = add (embed (Z0 i)) (add (mul β (padMap β (C i)))
        (mul (sub (embed (Z i)) (embed (Z0 i))) (mul β (padMap β (companionCancelPad β))))) := by
      constructive_ring
    _ = _ := by rw [hc]; constructive_ring

theorem kernel_base_difference_zero {ι : Type} (K : LinForm ι Fp4)
    (Z Z0 : ι → Fp) (hK : K.app (fun i => embed (Z i)) = K.app (fun i => embed (Z0 i))) :
    K.app (fun i => embed (sub (Z i) (Z0 i))) = zero := by
  have he : (fun i => embed (sub (Z i) (Z0 i))) =
      (fun i => add (mul (one : Fp4) (embed (Z i))) (mul (neg one) (embed (Z0 i)))) := by
    funext i
    rw [embed_sub]
    constructive_ring
  rw [he, K.lin, hK]
  constructive_ring

theorem kernel_base_shift {ι : Type} (K : LinForm ι Fp4) (V delta : ι → Fp)
    (r : Fp) (hd : K.app (fun i => embed (delta i)) = zero) :
    K.app (fun i => embed (add (V i) (mul (delta i) r))) = K.app (fun i => embed (V i)) := by
  have he : (fun i => embed (add (V i) (mul (delta i) r))) =
      (fun i => add (mul (one : Fp4) (embed (V i))) (mul (embed r) (embed (delta i)))) := by
    funext i
    rw [embed_add, embed_mul]
    constructive_ring
  rw [he, K.lin, hd]
  constructive_ring

theorem companionClaims_translate {ι : Type} (K : LinForm ι Fp4) (β : Fp4)
    (delta : ι → Fp) (C : ι → Pad) (hd : K.app (fun i => embed (delta i)) = zero) :
    companionClaims K (companionTranslate β delta C) = companionClaims K C := by
  apply CompanionClaims.ext <;>
    dsimp [companionClaims, companionTranslate, padAdd, padScale] <;>
    apply kernel_base_shift K _ delta _ hd

/-- Joint simulation of the full blended word AND all four companion claims, for any
    number of cells and any extension-field-valued linear functional. The simulator uses
    the fixed public reference assignment, never the private assignment. -/
theorem five_table_kernel_view_perfectly_simulated {ι : Type} (β : Fp4) (hβ : β.c1 ≠ zero)
    (K : LinForm ι Fp4) (Z0 : ι → Fp) :
    PerfectlySimulated
      (fun (Z : {Z : ι → Fp // K.app (fun i => embed (Z i)) = K.app (fun i => embed (Z0 i))})
        (C : ι → Pad) => privateCompanionView β K Z.val C)
      (fun (C : ι → Pad) => privateCompanionView β K Z0 C) := by
  intro Z
  refine ⟨companionTranslateBij β (fun i => sub (Z.val i) (Z0 i)), ?_⟩
  intro C
  apply Prod.ext
  · exact (privateBatchWord_translate β hβ Z.val Z0 C).symm
  · exact (companionClaims_translate K β (fun i => sub (Z.val i) (Z0 i)) C
      (kernel_base_difference_zero K Z.val Z0 Z.property)).symm

#verify_constructive Qsag.ZkHem.privateBatchWord_five_terms
  Qsag.ZkHem.five_table_kernel_view_perfectly_simulated



/-! ## The column transcript does not reveal `Z(ry)` or `g₂(ry)` separately -/
section HiddenColumnTerminal
variable {F : Type} [LawfulField F]

/-- The public mask sum and masked round polynomials. The verifier obtains the final
    combined value by evaluating the last polynomial; neither individual terminal operand
    is a field in this view. -/
def libraPublicTranscript (v : LibraView F) : F × List (List F) := (v.G, v.msgs)

def libraPublicSim (n d : Nat) (c : Nat → F) (ρ H : F) (s : LibraCoins F) :
    F × List (List F) := (s.G, (List.range n).map (simMsg H ρ d c s))

/-- Unlike the full Libra view, the column transcript is simulatable from its public
    initial claim alone. No hypothesis makes the private terminal operand public. -/
theorem libra_public_transcript_perfectly_simulated [DecidableEq F]
    (h2 : add (one : F) one ≠ zero) (n d : Nat) (c : Nat → F)
    (ρ : F) (hρ : ρ ≠ zero) (H : F) :
    PerfectlySimulated
      (fun (w : {w : WitnessRounds F // w.Honest n d c ∧ w.H = H}) (m : LibraMask F) =>
        libraPublicTranscript (libraReal n d c ρ w.val m))
      (libraPublicSim n d c ρ H) := by
  rintro ⟨w, hw, hH⟩
  refine ⟨libraCoinBij h2 n d ρ hρ w, fun m => ?_⟩
  change libraPublicTranscript (libraReal n d c ρ w m) =
    libraPublicSim n d c ρ H (libraCoinsOf n d ρ w m)
  rw [libra_real_eq_sim h2 n d c ρ hρ w hw m, hH]
  rfl
end HiddenColumnTerminal

#verify_constructive Qsag.ZkHem.libra_public_transcript_perfectly_simulated


/-! ## Raw base-field openings of all five tables

Companion translation preserves every linear observation on which the two assignments
agree. This includes raw RS symbols once their base-field linear evaluation maps are
instantiated. It does not construct the public reference assignment or the layout masks.
-/

def rawFiveTableView {ι κ : Type} (R : κ → LinForm ι Fp)
    (Z : ι → Fp) (C : ι → Pad) : κ → Fp × Pad :=
  fun j => ((R j).app Z,
    ⟨(R j).app (fun i => (C i).r0), (R j).app (fun i => (C i).r1),
     (R j).app (fun i => (C i).r2), (R j).app (fun i => (C i).r3)⟩)

theorem base_difference_zero {ι : Type} (R : LinForm ι Fp) (Z Z0 : ι → Fp)
    (h : R.app Z = R.app Z0) : R.app (fun i => sub (Z i) (Z0 i)) = zero := by
  have he : (fun i => sub (Z i) (Z0 i)) =
      (fun i => add (mul (one : Fp) (Z i)) (mul (neg one) (Z0 i))) := by
    funext i; constructive_ring
  rw [he, R.lin, h]
  constructive_ring

theorem base_shift {ι : Type} (R : LinForm ι Fp) (V delta : ι → Fp) (r : Fp)
    (hd : R.app delta = zero) :
    R.app (fun i => add (V i) (mul (delta i) r)) = R.app V := by
  have he : (fun i => add (V i) (mul (delta i) r)) =
      (fun i => add (mul (one : Fp) (V i)) (mul r (delta i))) := by
    funext i; constructive_ring
  rw [he, R.lin, hd]
  constructive_ring

theorem rawFiveTableView_translate {ι κ : Type} (R : κ → LinForm ι Fp)
    (β : Fp4) (Z Z0 : ι → Fp) (C : ι → Pad)
    (hR : ∀ j, (R j).app Z = (R j).app Z0) :
    rawFiveTableView R Z0 (companionTranslate β (fun i => sub (Z i) (Z0 i)) C) =
      rawFiveTableView R Z C := by
  funext j
  apply Prod.ext
  · exact (hR j).symm
  · apply Pad.ext <;>
      dsimp [rawFiveTableView, companionTranslate, padAdd, padScale] <;>
      exact base_shift (R j) _ _ _ (base_difference_zero (R j) Z Z0 (hR j))

/-- The single companion-coin bijection hides the blended word, all four announced kernel
    claims, and raw symbols of ALL FIVE tables jointly. The public reference must satisfy
    the same raw observations and kernel claim; obtaining it from layout simulation is a
    separate obligation. -/
theorem five_table_opening_view_perfectly_simulated {ι κ : Type}
    (β : Fp4) (hβ : β.c1 ≠ zero) (K : LinForm ι Fp4)
    (R : κ → LinForm ι Fp) (Z0 : ι → Fp) :
    PerfectlySimulated
      (fun (Z : {Z : ι → Fp //
          K.app (fun i => embed (Z i)) = K.app (fun i => embed (Z0 i)) ∧
          ∀ j, (R j).app Z = (R j).app Z0}) (C : ι → Pad) =>
        (privateCompanionView β K Z.val C, rawFiveTableView R Z.val C))
      (fun C => (privateCompanionView β K Z0 C, rawFiveTableView R Z0 C)) := by
  intro Z
  refine ⟨companionTranslateBij β (fun i => sub (Z.val i) (Z0 i)), ?_⟩
  intro C
  apply Prod.ext
  · apply Prod.ext
    · exact (privateBatchWord_translate β hβ Z.val Z0 C).symm
    · exact (companionClaims_translate K β (fun i => sub (Z.val i) (Z0 i)) C
        (kernel_base_difference_zero K Z.val Z0 Z.property.1)).symm
  · exact (rawFiveTableView_translate R β Z.val Z0 C Z.property.2).symm

#verify_constructive Qsag.ZkHem.rawFiveTableView_translate
  Qsag.ZkHem.five_table_opening_view_perfectly_simulated

/-! ## Public finite reference assignment and joint five-table linear observations -/

open RoundPoly

/-- A finite public weight vector, interpreted on the actual finite table carrier. -/
def finiteWeightedForm {F : Type} [LawfulField F] (n : Nat) (weights : List F) :
    LinForm (Fin n) F := LinForm.dot ((List.finRange n).zip weights)

private theorem dotAt_zip {ι F : Type} [LawfulField F] (u : ι → F) :
    ∀ (is : List ι) (ws : List F), dotAt (is.zip ws) u = dotVec ws (is.map u)
  | [], [] => rfl
  | [], _ :: _ => by simp only [List.zip_nil_left, List.map_nil, dotAt, dotVec_nil_right]
  | _ :: _, [] => by simp only [List.zip_nil_right, dotAt, dotVec_nil_left]
  | i :: is, w :: ws => by
    simp only [List.zip_cons_cons, List.map_cons, dotAt, dotVec_cons, dotAt_zip u is ws]

def finiteTable {F : Type} {n : Nat} (u : Fin n → F) : List F :=
  (List.finRange n).map u

theorem finiteTable_length {F : Type} {n : Nat} (u : Fin n → F) :
    (finiteTable u).length = n := by
  simp only [finiteTable, List.length_map, List.length_finRange]

theorem finiteWeightedForm_app {F : Type} [LawfulField F] {n : Nat}
    (weights : List F) (u : Fin n → F) :
    (finiteWeightedForm n weights).app u = dotVec weights (finiteTable u) :=
  dotAt_zip u _ _

def finiteTableRead {F : Type} [CommRingOps F] (n : Nat) (v : List F) : Fin n → F :=
  fun i => v.getD i.val zero

private theorem finiteTable_ofFn {F : Type} {n : Nat} (u : Fin n → F) :
    finiteTable u = List.ofFn u := by
  simp only [finiteTable, List.finRange, List.map_ofFn, Function.comp_def]

theorem finiteTable_read {F : Type} [CommRingOps F] {n : Nat} (v : List F)
    (hlen : v.length = n) : finiteTable (finiteTableRead n v) = v := by
  rw [finiteTable_ofFn]
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using hlen.symm
  · intro i hi hv
    simp only [List.getElem_ofFn, finiteTableRead, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hv, Option.getD_some]

/-- Augmentation uses the negative public right-hand side. -/
def affineObservationRow {F : Type} [CommRingOps F] (weights : List F) (value : F) : List F :=
  weights ++ [neg value]

theorem affineObservationRow_dot {F : Type} [LawfulCommRing F]
    (weights v : List F) (value : F) (hlen : weights.length = v.length) :
    dotVec (affineObservationRow weights value) (v ++ [one]) =
      sub (dotVec weights v) value := by
  rw [affineObservationRow, dotVec_append_eq _ _ _ _ hlen]
  simp only [dotVec_cons, dotVec_nil_left, LawfulCommRing.mul_one, LawfulCommRing.add_zero]
  constructive_ring

/-- Tower-coordinate order `[1,u,v,uv]`, used consistently in public augmented rows. -/
def baseCoordinate (j : Fin 4) (x : Fp4) : Fp :=
  match j.val with
  | 0 => x.c0.c0
  | 1 => x.c0.c1
  | 2 => x.c1.c0
  | _ => x.c1.c1

theorem baseCoordinate_ext (x y : Fp4)
    (h : ∀ j, baseCoordinate j x = baseCoordinate j y) : x = y := by
  apply GoldilocksField.GoldilocksExt4.ext
  · exact GoldilocksExt2.ext (by simpa only [baseCoordinate] using h ⟨0, by decide⟩)
      (by simpa only [baseCoordinate] using h ⟨1, by decide⟩)
  · exact GoldilocksExt2.ext (by simpa only [baseCoordinate] using h ⟨2, by decide⟩)
      (by simpa only [baseCoordinate] using h ⟨3, by decide⟩)

theorem baseCoordinate_add (j : Fin 4) (x y : Fp4) :
    baseCoordinate j (add x y) = add (baseCoordinate j x) (baseCoordinate j y) := by
  rcases j with ⟨j, hj⟩
  rcases j with _ | _ | _ | _ | j
  · simp only [baseCoordinate, fp4_add_c0, fp2_add_c0]
  · simp only [baseCoordinate, fp4_add_c0, fp2_add_c1]
  · simp only [baseCoordinate, fp4_add_c1, fp2_add_c0]
  · simp only [baseCoordinate, fp4_add_c1, fp2_add_c1]
  · omega

theorem baseCoordinate_zero (j : Fin 4) : baseCoordinate j zero = zero := by
  rcases j with ⟨j, hj⟩
  rcases j with _ | _ | _ | _ | j
  · simp only [baseCoordinate, fp4_zero_c0, fp2_zero_c0]
  · simp only [baseCoordinate, fp4_zero_c0, fp2_zero_c1]
  · simp only [baseCoordinate, fp4_zero_c1, fp2_zero_c0]
  · simp only [baseCoordinate, fp4_zero_c1, fp2_zero_c1]
  · omega

private theorem embed_scale_c0 (a : Fp) (x : Fp4) :
    (mul (embed a) x).c0 = mul (GoldilocksExt2.ofBase a) x.c0 := by
  change add (mul (GoldilocksExt2.ofBase a) x.c0)
    (mul GoldilocksExt2.uBasis (mul zero x.c1)) = _
  rw [LawfulCommRing.zero_mul, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

private theorem embed_scale_c1 (a : Fp) (x : Fp4) :
    (mul (embed a) x).c1 = mul (GoldilocksExt2.ofBase a) x.c1 := by
  change add (mul (GoldilocksExt2.ofBase a) x.c1) (mul zero x.c0) = _
  rw [LawfulCommRing.zero_mul, LawfulCommRing.add_zero]

theorem baseCoordinate_mul_embed (j : Fin 4) (x : Fp4) (a : Fp) :
    baseCoordinate j (mul x (embed a)) = mul (baseCoordinate j x) a := by
  rw [LawfulCommRing.mul_comm x (embed a)]
  rcases j with ⟨j, hj⟩
  rcases j with _ | _ | _ | _ | j
  · simp only [baseCoordinate, embed_scale_c0, ofBase_mul_c0]
    exact LawfulCommRing.mul_comm _ _
  · simp only [baseCoordinate, embed_scale_c0, ofBase_mul_c1]
    exact LawfulCommRing.mul_comm _ _
  · simp only [baseCoordinate, embed_scale_c1, ofBase_mul_c0]
    exact LawfulCommRing.mul_comm _ _
  · simp only [baseCoordinate, embed_scale_c1, ofBase_mul_c1]
    exact LawfulCommRing.mul_comm _ _
  · omega

theorem baseCoordinate_dot (j : Fin 4) : ∀ (weights : List Fp4) (v : List Fp),
    baseCoordinate j (dotVec weights (v.map embed)) = dotVec (weights.map (baseCoordinate j)) v
  | [], _ => by simp only [dotVec_nil_left, List.map_nil, baseCoordinate_zero]
  | _ :: _, [] => by simp only [List.map_nil, dotVec_nil_right, baseCoordinate_zero]
  | w :: ws, a :: v => by
    simp only [List.map_cons, dotVec_cons, baseCoordinate_add, baseCoordinate_mul_embed,
      baseCoordinate_dot j ws v]

structure PublicOpeningMatrix (n q : Nat) where
  kernel : List Fp4
  raw : Fin q → List Fp
  kernel_length : kernel.length = n
  raw_length : ∀ j, (raw j).length = n

structure PublicOpeningClaims (q : Nat) where
  kernel : Fp4
  raw : Fin q → Fp

def PublicOpeningMatrix.kernelForm {n q : Nat} (M : PublicOpeningMatrix n q) :
    LinForm (Fin n) Fp4 := finiteWeightedForm n M.kernel

def PublicOpeningMatrix.rawForm {n q : Nat} (M : PublicOpeningMatrix n q) (j : Fin q) :
    LinForm (Fin n) Fp := finiteWeightedForm n (M.raw j)

def publicOpeningMatches {n q : Nat} (M : PublicOpeningMatrix n q)
    (V : PublicOpeningClaims q) (Z : Fin n → Fp) : Prop :=
  M.kernelForm.app (fun i => embed (Z i)) = V.kernel ∧
    ∀ j, (M.rawForm j).app Z = V.raw j

/-- Four base-field equations encode the extension-field kernel claim; all raw-symbol
constraints share exactly the same assignment variables. -/
def publicOpeningRows {n q : Nat} (M : PublicOpeningMatrix n q)
    (V : PublicOpeningClaims q) : List (List Fp) :=
  (List.finRange 4).map (fun j =>
    affineObservationRow (M.kernel.map (baseCoordinate j)) (baseCoordinate j V.kernel)) ++
  (List.finRange q).map (fun j => affineObservationRow (M.raw j) (V.raw j))

theorem publicOpeningRows_length {n q : Nat} (M : PublicOpeningMatrix n q)
    (V : PublicOpeningClaims q) : (publicOpeningRows M V).length = 4 + q := by
  simp only [publicOpeningRows, List.length_append, List.length_map, List.length_finRange]

theorem publicOpeningRows_width {n q : Nat} (M : PublicOpeningMatrix n q)
    (V : PublicOpeningClaims q) : ∀ r ∈ publicOpeningRows M V, r.length = n + 1 := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
    simp only [affineObservationRow, List.length_append, List.length_map,
      M.kernel_length, List.length_cons, List.length_nil]
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
    simp only [affineObservationRow, List.length_append, M.raw_length j,
      List.length_cons, List.length_nil]

private theorem kernelForm_coordinate {n q : Nat} (M : PublicOpeningMatrix n q)
    (Z : Fin n → Fp) (j : Fin 4) :
    baseCoordinate j (M.kernelForm.app (fun i => embed (Z i))) =
      dotVec (M.kernel.map (baseCoordinate j)) (finiteTable Z) := by
  rw [PublicOpeningMatrix.kernelForm, finiteWeightedForm_app]
  have he : finiteTable (fun i => embed (Z i)) = (finiteTable Z).map embed := by
    simp only [finiteTable, List.map_map, Function.comp_def]
  rw [he, baseCoordinate_dot]

/-- Every actual finite word supplies consistency, solely in the proof. -/
theorem publicOpeningRows_consistent {n q : Nat} (M : PublicOpeningMatrix n q)
    (V : PublicOpeningClaims q) (Z : Fin n → Fp) (hZ : publicOpeningMatches M V Z) :
    WelchBerlekamp.AffineConsistent n (publicOpeningRows M V) := by
  apply (WelchBerlekamp.affineConsistent_iff n _).mpr
  refine ⟨finiteTable Z, finiteTable_length Z, ?_⟩
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
    rw [affineObservationRow_dot _ _ _ (by rw [List.length_map, M.kernel_length, finiteTable_length])]
    rw [← kernelForm_coordinate M Z j, hZ.1, LawfulCommRing.sub_self]
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
    rw [affineObservationRow_dot _ _ _ (by rw [M.raw_length, finiteTable_length])]
    have he := hZ.2 j
    change (finiteWeightedForm n (M.raw j)).app Z = V.raw j at he
    rw [finiteWeightedForm_app] at he
    rw [he, LawfulCommRing.sub_self]

/-- The public reference assignment is computed from the public matrix and public claims.
Its inputs contain no witness, secret key, original word, or consistency proof. -/
def publicReferenceAssignment {n q : Nat} (M : PublicOpeningMatrix n q)
    (V : PublicOpeningClaims q) : Fin n → Fp :=
  finiteTableRead n (WelchBerlekamp.solveAffine n (publicOpeningRows M V))

theorem publicReferenceAssignment_matches {n q : Nat} (M : PublicOpeningMatrix n q)
    (V : PublicOpeningClaims q) (hconsistent : WelchBerlekamp.AffineConsistent n
      (publicOpeningRows M V)) : publicOpeningMatches M V (publicReferenceAssignment M V) := by
  let v := WelchBerlekamp.solveAffine n (publicOpeningRows M V)
  have hlen : v.length = n := WelchBerlekamp.solveAffine_length n _
  have ht : finiteTable (publicReferenceAssignment M V) = v := finiteTable_read v hlen
  have hs := WelchBerlekamp.solveAffine_spec n (publicOpeningRows M V)
    (publicOpeningRows_width M V) hconsistent
  constructor
  · apply baseCoordinate_ext
    intro j
    have hr : affineObservationRow (M.kernel.map (baseCoordinate j)) (baseCoordinate j V.kernel)
        ∈ publicOpeningRows M V :=
      List.mem_append_left _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
    have he := hs _ hr
    rw [affineObservationRow_dot _ _ _ (by rw [List.length_map, M.kernel_length, hlen])] at he
    rw [kernelForm_coordinate M (publicReferenceAssignment M V) j, ht]
    exact LawfulCommRing.sub_eq_zero_iff.mp he
  · intro j
    have hr : affineObservationRow (M.raw j) (V.raw j) ∈ publicOpeningRows M V :=
      List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
    have he := hs _ hr
    rw [affineObservationRow_dot _ _ _ (by rw [M.raw_length, hlen])] at he
    rw [PublicOpeningMatrix.rawForm, finiteWeightedForm_app, ht]
    exact LawfulCommRing.sub_eq_zero_iff.mp he

theorem publicReferenceAssignment_cost {n q : Nat} (M : PublicOpeningMatrix n q)
    (V : PublicOpeningClaims q) :
    (WelchBerlekamp.solveAffineT n (publicOpeningRows M V)).cost ≤
      n * ((4 + q) * (2 * n + 4) + 2 * n + 5) := by
  have h := WelchBerlekamp.solveAffine_ops_poly n (publicOpeningRows M V)
    (fun r hr => Nat.le_of_eq (publicOpeningRows_width M V r hr))
  simpa only [publicOpeningRows_length] using h

/-- Joint linear-opening simulation using a reference computed solely from public data.
This includes the entire blended word, all four companion claims, and raw observations of
all five finite tables. It does not yet include row/column mask coins or salt queries. -/
theorem five_table_public_reference_linear_simulation {n q : Nat}
    (M : PublicOpeningMatrix n q) (V : PublicOpeningClaims q)
    (hpossible : ∃ Z, publicOpeningMatches M V Z) (β : Fp4) (hβ : β.c1 ≠ zero) :
    PerfectlySimulated
      (fun (Z : {Z : Fin n → Fp // publicOpeningMatches M V Z}) (C : Fin n → Pad) =>
        (privateCompanionView β M.kernelForm Z.val C, rawFiveTableView M.rawForm Z.val C))
      (fun C =>
        (privateCompanionView β M.kernelForm (publicReferenceAssignment M V) C,
         rawFiveTableView M.rawForm (publicReferenceAssignment M V) C)) := by
  obtain ⟨Zexist, hZexist⟩ := hpossible
  have hr := publicReferenceAssignment_matches M V
    (publicOpeningRows_consistent M V Zexist hZexist)
  intro Z
  let Z0 := publicReferenceAssignment M V
  have hK : M.kernelForm.app (fun i => embed (Z.val i)) =
      M.kernelForm.app (fun i => embed (Z0 i)) := Z.property.1.trans hr.1.symm
  have hR : ∀ j, (M.rawForm j).app Z.val = (M.rawForm j).app Z0 :=
    fun j => (Z.property.2 j).trans (hr.2 j).symm
  refine ⟨companionTranslateBij β (fun i => sub (Z.val i) (Z0 i)), ?_⟩
  intro C
  apply Prod.ext
  · apply Prod.ext
    · exact (privateBatchWord_translate β hβ Z.val Z0 C).symm
    · exact (companionClaims_translate M.kernelForm β (fun i => sub (Z.val i) (Z0 i)) C
        (kernel_base_difference_zero M.kernelForm Z.val Z0 hK)).symm
  · exact (rawFiveTableView_translate M.rawForm β Z.val Z0 C hR).symm

#verify_constructive finiteWeightedForm_app finiteTable_read affineObservationRow_dot
  baseCoordinate_ext baseCoordinate_add baseCoordinate_zero baseCoordinate_mul_embed baseCoordinate_dot
  publicOpeningRows_consistent publicReferenceAssignment_matches publicReferenceAssignment_cost
  five_table_public_reference_linear_simulation

/-! ## Computed arbitrary-point corner rank and the public abort branch -/

def padUnit (j : Fin 4) : Pad :=
  ⟨if j.val = 0 then one else zero, if j.val = 1 then one else zero,
    if j.val = 2 then one else zero, if j.val = 3 then one else zero⟩

def padCoordinates (x : Fp4) : Pad := ⟨x.c0.c0, x.c0.c1, x.c1.c0, x.c1.c1⟩
def padAssemble (r : Pad) : Fp4 := ⟨⟨r.r0, r.r1⟩, ⟨r.r2, r.r3⟩⟩

theorem padCoordinates_assemble (r : Pad) : padCoordinates (padAssemble r) = r := by
  cases r; rfl

theorem padAssemble_coordinates (x : Fp4) : padAssemble (padCoordinates x) = x := by
  cases x with | mk a b => cases a; cases b; rfl

theorem padCoordinates_add (x y : Fp4) :
    padCoordinates (add x y) = padAdd (padCoordinates x) (padCoordinates y) := by
  apply Pad.ext <;> simp only [padCoordinates, padAdd, fp4_add_c0, fp4_add_c1,
    fp2_add_c0, fp2_add_c1]

theorem padCoordinates_scale (a : Fp) (x : Fp4) :
    padCoordinates (mul x (embed a)) = padScale a (padCoordinates x) := by
  apply Pad.ext
  all_goals first
    | exact (baseCoordinate_mul_embed ⟨0, by decide⟩ x a).trans (LawfulCommRing.mul_comm _ _)
    | exact (baseCoordinate_mul_embed ⟨1, by decide⟩ x a).trans (LawfulCommRing.mul_comm _ _)
    | exact (baseCoordinate_mul_embed ⟨2, by decide⟩ x a).trans (LawfulCommRing.mul_comm _ _)
    | exact (baseCoordinate_mul_embed ⟨3, by decide⟩ x a).trans (LawfulCommRing.mul_comm _ _)

structure LinearPadMap where
  app : Pad → Pad
  map_add : ∀ x y, app (padAdd x y) = padAdd (app x) (app y)
  map_scale : ∀ a x, app (padScale a x) = padScale a (app x)

def LinearPadMap.id : LinearPadMap := ⟨fun x => x, fun _ _ => rfl, fun _ _ => rfl⟩
def LinearPadMap.comp (f g : LinearPadMap) : LinearPadMap where
  app x := f.app (g.app x)
  map_add x y := by rw [g.map_add, f.map_add]
  map_scale a x := by rw [g.map_scale, f.map_scale]

def padCombine (cols : Fin 4 → Pad) (r : Pad) : Pad :=
  padAdd (padAdd (padAdd (padScale r.r0 (cols ⟨0, by decide⟩))
    (padScale r.r1 (cols ⟨1, by decide⟩)))
    (padScale r.r2 (cols ⟨2, by decide⟩))) (padScale r.r3 (cols ⟨3, by decide⟩))

theorem padCombine_units (r : Pad) : padCombine padUnit r = r := by
  apply Pad.ext <;> simp only [padCombine, padAdd, padScale, padUnit, ite_true,
    ite_false, Nat.reduceEqDiff, LawfulCommRing.mul_one, LawfulCommRing.mul_zero,
    LawfulCommRing.add_zero, LawfulCommRing.zero_add]

def linearPadColumns (cols : Fin 4 → Pad) : LinearPadMap where
  app := padCombine cols
  map_add x y := by apply Pad.ext <;> dsimp [padCombine, padAdd, padScale] <;> constructive_ring
  map_scale a x := by apply Pad.ext <;> dsimp [padCombine, padAdd, padScale] <;> constructive_ring

theorem LinearPadMap.expand (L : LinearPadMap) (r : Pad) :
    L.app r = padCombine (fun j => L.app (padUnit j)) r := by
  calc
    _ = L.app (padCombine padUnit r) := congrArg L.app (padCombine_units r).symm
    _ = _ := by simp only [padCombine, L.map_add, L.map_scale]

theorem LinearPadMap.ext_app (L M : LinearPadMap)
    (h : ∀ j, L.app (padUnit j) = M.app (padUnit j)) : ∀ r, L.app r = M.app r := by
  intro r
  rw [L.expand, M.expand]
  exact congrArg (fun cs => padCombine cs r) (funext h)

theorem cornerPad_add (a b : Fp4) (r s : Pad) :
    cornerPad a b (padAdd r s) = add (cornerPad a b r) (cornerPad a b s) := by
  simp only [cornerPad, padAdd, embed_add]
  constructive_ring

theorem cornerPad_scale (a b : Fp4) (r : Pad) (c : Fp) :
    cornerPad a b (padScale c r) = mul (cornerPad a b r) (embed c) := by
  simp only [cornerPad, padScale, embed_mul]
  constructive_ring

def cornerLinear (a b : Fp4) : LinearPadMap where
  app r := padCoordinates (cornerPad a b r)
  map_add r s := by rw [cornerPad_add, padCoordinates_add]
  map_scale c r := by rw [cornerPad_scale, padCoordinates_scale]

/-- This public rank guard checks both compositions on the four base-coordinate vectors. -/
def cornerInverseGuard (a b : Fp4) (cols : Fin 4 → Pad) : Prop :=
  ∀ j : Fin 4,
    (linearPadColumns cols).app ((cornerLinear a b).app (padUnit j)) = padUnit j ∧
    (cornerLinear a b).app ((linearPadColumns cols).app (padUnit j)) = padUnit j

instance (a b : Fp4) (cols : Fin 4 → Pad) : Decidable (cornerInverseGuard a b cols) :=
  inferInstanceAs (Decidable (∀ j : Fin 4,
    (linearPadColumns cols).app ((cornerLinear a b).app (padUnit j)) = padUnit j ∧
    (cornerLinear a b).app ((linearPadColumns cols).app (padUnit j)) = padUnit j))

def checkedCornerPadBasis (a b : Fp4) (cols : Fin 4 → Pad) : Option (CornerPadBasis a b) :=
  if h : cornerInverseGuard a b cols then
    some {
      invert v := (linearPadColumns cols).app (padCoordinates v)
      left_inv r := by
        exact LinearPadMap.ext_app ((linearPadColumns cols).comp (cornerLinear a b))
          LinearPadMap.id (fun j => (h j).1) r
      right_inv v := by
        have he := LinearPadMap.ext_app ((cornerLinear a b).comp (linearPadColumns cols))
          LinearPadMap.id (fun j => (h j).2) (padCoordinates v)
        have hr := congrArg padAssemble he
        simpa only [LinearPadMap.comp, LinearPadMap.id, cornerLinear,
          padAssemble_coordinates] using hr }
  else none

theorem checkedCornerPadBasis_some_iff (a b : Fp4) (cols : Fin 4 → Pad) :
    (checkedCornerPadBasis a b cols).isSome = true ↔ cornerInverseGuard a b cols := by
  unfold checkedCornerPadBasis
  split <;> simp_all only [Option.isSome_some, Option.isSome_none, Bool.false_eq_true]

theorem linearPadColumns_unit (cols : Fin 4 → Pad) (j : Fin 4) :
    (linearPadColumns cols).app (padUnit j) = cols j := by
  rcases j with ⟨j, hj⟩
  rcases j with _ | _ | _ | _ | j
  all_goals first
    | omega
    | (apply Pad.ext <;> simp only [linearPadColumns, padCombine, padAdd, padScale,
        padUnit, Nat.reduceEqDiff, ite_true, ite_false, LawfulCommRing.one_mul,
        LawfulCommRing.zero_mul, LawfulCommRing.add_zero, LawfulCommRing.zero_add])

/-- The actual corner weights, as one public four-variable extension-field equation. -/
def cornerOpeningMatrix (a b : Fp4) : PublicOpeningMatrix 4 0 where
  kernel := [mul (sub one a) (sub one b), mul a (sub one b), mul (sub one a) b, mul a b]
  raw j := Fin.elim0 j
  kernel_length := rfl
  raw_length j := Fin.elim0 j

def cornerOpeningClaims (v : Fp4) : PublicOpeningClaims 0 where
  kernel := v
  raw j := Fin.elim0 j

def padAssignment (r : Pad) (j : Fin 4) : Fp :=
  match j.val with | 0 => r.r0 | 1 => r.r1 | 2 => r.r2 | _ => r.r3

def assignmentPad (u : Fin 4 → Fp) : Pad :=
  ⟨u ⟨0, by decide⟩, u ⟨1, by decide⟩, u ⟨2, by decide⟩, u ⟨3, by decide⟩⟩

theorem padAssignment_assignmentPad (u : Fin 4 → Fp) : padAssignment (assignmentPad u) = u := by
  funext j
  rcases j with ⟨j, hj⟩
  rcases j with _ | _ | _ | _ | j
  all_goals first | omega | rfl

theorem cornerOpeningMatrix_app (a b : Fp4) (u : Fin 4 → Fp) :
    (cornerOpeningMatrix a b).kernelForm.app (fun i => embed (u i)) =
      cornerPad a b (assignmentPad u) := by
  rw [PublicOpeningMatrix.kernelForm, finiteWeightedForm_app]
  simp only [cornerOpeningMatrix, finiteTable, List.finRange, List.map_ofFn]
  change add (mul (mul (sub one a) (sub one b)) (embed (u ⟨0, by decide⟩)))
    (add (mul (mul a (sub one b)) (embed (u ⟨1, by decide⟩)))
      (add (mul (mul (sub one a) b) (embed (u ⟨2, by decide⟩)))
        (add (mul (mul a b) (embed (u ⟨3, by decide⟩))) zero))) = _
  simp only [cornerPad, assignmentPad]
  constructive_ring

/-- Four independent public affine solves; no row witness enters the algorithm. -/
def cornerColumnCandidates (a b : Fp4) (j : Fin 4) : Pad :=
  assignmentPad (publicReferenceAssignment (cornerOpeningMatrix a b)
    (cornerOpeningClaims (padAssemble (padUnit j))))

theorem cornerColumnCandidates_correct (a b : Fp4) (basis : CornerPadBasis a b)
    (j : Fin 4) : cornerPad a b (cornerColumnCandidates a b j) = padAssemble (padUnit j) := by
  let v := padAssemble (padUnit j)
  have hp : publicOpeningMatches (cornerOpeningMatrix a b) (cornerOpeningClaims v)
      (padAssignment (basis.invert v)) := by
    constructor
    · rw [cornerOpeningMatrix_app]
      have h : assignmentPad (padAssignment (basis.invert v)) = basis.invert v := by
        cases basis.invert v; rfl
      rw [h]
      exact basis.right_inv v
    · intro k; exact Fin.elim0 k
  have he := publicReferenceAssignment_matches (cornerOpeningMatrix a b) (cornerOpeningClaims v)
    (publicOpeningRows_consistent _ _ _ hp)
  have heK := he.1
  rw [cornerOpeningMatrix_app] at heK
  exact heK

private theorem cornerInverseGuard_of_right (a b : Fp4) (cols : Fin 4 → Pad)
    (basis : CornerPadBasis a b)
    (hc : ∀ j, cornerPad a b (cols j) = padAssemble (padUnit j)) :
    cornerInverseGuard a b cols := by
  have hr : ∀ r, (cornerLinear a b).app ((linearPadColumns cols).app r) = r := by
    apply LinearPadMap.ext_app ((cornerLinear a b).comp (linearPadColumns cols)) LinearPadMap.id
    intro j
    change padCoordinates (cornerPad a b ((linearPadColumns cols).app (padUnit j))) = padUnit j
    rw [linearPadColumns_unit, hc, padCoordinates_assemble]
  intro j
  refine ⟨?_, hr (padUnit j)⟩
  have he := hr ((cornerLinear a b).app (padUnit j))
  have ht := congrArg (fun r => basis.invert (padAssemble r)) he
  simpa only [cornerLinear, padAssemble_coordinates, basis.left_inv] using ht

/-- A witness-free, checked Gaussian rank constructor for arbitrary public row points. -/
def makeCornerPadBasis (a b : Fp4) : Option (CornerPadBasis a b) :=
  checkedCornerPadBasis a b (cornerColumnCandidates a b)

/-- The computed constructor succeeds exactly when the corner map is invertible. -/
theorem makeCornerPadBasis_success_iff (a b : Fp4) :
    (makeCornerPadBasis a b).isSome = true ↔ Nonempty (CornerPadBasis a b) := by
  constructor
  · intro h
    cases hb : makeCornerPadBasis a b with
    | none => simp only [hb, Option.isSome_none, Bool.false_eq_true] at h
    | some basis => exact ⟨basis⟩
  · rintro ⟨basis⟩
    apply (checkedCornerPadBasis_some_iff a b _).mpr
    exact cornerInverseGuard_of_right a b _ basis (cornerColumnCandidates_correct a b basis)

structure RowRankCertificate (a b k₁ k₂ k₃ : Fp4) where
  basis : CornerPadBasis a b
  first_nonzero : k₁ ≠ zero
  second_nonzero : k₂ ≠ zero
  third_nonzero : k₃ ≠ zero

/-- Exactly the public four-corner rank check and three nonzero corner factors. -/
def checkRowRank (a b k₁ k₂ k₃ : Fp4) : Option (RowRankCertificate a b k₁ k₂ k₃) :=
  (makeCornerPadBasis a b).bind fun basis =>
    if h₁ : k₁ ≠ zero then
      if h₂ : k₂ ≠ zero then
        if h₃ : k₃ ≠ zero then some ⟨basis, h₁, h₂, h₃⟩ else none
      else none
    else none

def rowCellsCoordinatesBij : SimpleEquiv RowMaskCells RowTriple where
  toFun r := ⟨padAssemble r.first, padAssemble r.second, padAssemble r.third⟩
  invFun v := ⟨padCoordinates v.a, padCoordinates v.b, padCoordinates v.c⟩
  left_inv r := by
    simp only [padCoordinates_assemble]
  right_inv v := by
    simp only [padAssemble_coordinates]

def rankCheckedRowView (a b k₁ k₂ k₃ : Fp4) (w : RowTriple) (r : RowMaskCells) :
    Option RowTriple :=
  (checkRowRank a b k₁ k₂ k₃).map fun cert =>
    rowTripleAdd w (rowMaskCellsMap cert.basis k₁ k₂ k₃ r)

def rankCheckedRowSim (a b k₁ k₂ k₃ : Fp4) (v : RowTriple) : Option RowTriple :=
  (checkRowRank a b k₁ k₂ k₃).map (fun _ => v)

/-- The rank-failure abort is part of the view. Accepted views jointly simulate the three
row operands from twelve base-field cells; rejected views are the same public abort. -/
theorem rank_checked_masking_rows_perfectly_simulated (a b k₁ k₂ k₃ : Fp4) :
    PerfectlySimulated (rankCheckedRowView a b k₁ k₂ k₃) (rankCheckedRowSim a b k₁ k₂ k₃) := by
  intro w
  cases hc : checkRowRank a b k₁ k₂ k₃ with
  | none =>
    refine ⟨rowCellsCoordinatesBij, ?_⟩
    intro r
    simp only [rankCheckedRowView, rankCheckedRowSim, hc, Option.map_none]
  | some cert =>
    obtain ⟨e, he⟩ := masking_rows_joint_perfectly_simulated cert.basis k₁ k₂ k₃
      cert.first_nonzero cert.second_nonzero cert.third_nonzero w
    refine ⟨e, ?_⟩
    intro r
    simp only [rankCheckedRowView, rankCheckedRowSim, hc, Option.map_some]
    exact congrArg some (he r)

#verify_constructive padCoordinates_scale LinearPadMap.ext_app cornerPad_add cornerPad_scale
  checkedCornerPadBasis_some_iff cornerColumnCandidates_correct makeCornerPadBasis_success_iff
  rank_checked_masking_rows_perfectly_simulated

section CubeSumcheckSoundness
variable {F : Type} [LawfulField F] [DecidableEq F]

/-- A running unmasked sumcheck: the bound prefix and the current claimed Boolean sum. -/
abbrev CubeState (F : Type) := Option (List F × F)

@[expose] def cubeLive (g : List F → F) (n : Nat) (_ : F) : CubeState F → Prop
  | none => False
  | some (cs, claim) => claim = cubeClaim g n cs

instance cubeLiveDecidable (g : List F → F) (n : Nat) (x : F) (st : CubeState F) :
    Decidable (cubeLive g n x st) := by
  cases st with
  | none => unfold cubeLive; exact isFalse id
  | some p => exact inferInstanceAs (Decidable (p.2 = cubeClaim g n p.1))

def cubeStep (n d : Nat) (S : List F) : CubeState F → List F → Nat → CubeState F
  | none, _, _ => none
  | some (cs, claim), p, ch =>
    if cs.length < n ∧ p.length ≤ d + 1 ∧
        add (RoundPoly.evalCoeffs p zero) (RoundPoly.evalCoeffs p one) = claim then
      some (cs ++ [S.getD ch zero], RoundPoly.evalCoeffs p (S.getD ch zero))
    else none

private theorem cubeStep_flip_bound {g : List F → F} {d : Nat} (R : LineRep g d)
    (n : Nat) (S : List F) (hS : S.Nodup)
    (x : F) (st : CubeState F) (p : List F)
    (hDoomed : ¬ cubeLive g n x st) (L : List (Fin S.length)) (hL : L.Nodup)
    (hLive : ∀ ch ∈ L, ¬¬ cubeLive g n x (cubeStep n d S st p ch.1)) : L.length ≤ d := by
  cases st with
  | none =>
    have hempty : L = [] := by
      cases L with
      | nil => rfl
      | cons ch tail => exact False.elim (hLive ch (.head tail) id)
    rw [hempty]; exact Nat.zero_le _
  | some st =>
    rcases st with ⟨cs, claim⟩
    by_cases hcheck : cs.length < n ∧ p.length ≤ d + 1 ∧
        add (RoundPoly.evalCoeffs p zero) (RoundPoly.evalCoeffs p one) = claim
    · have hWrong : add (RoundPoly.evalCoeffs p zero) (RoundPoly.evalCoeffs p one) ≠
          cubeClaim g n cs := by
        rw [hcheck.2.2]; exact hDoomed
      let vals := L.map (fun ch => S.getD ch.val zero)
      have hNd : vals.Nodup := List.Pairwise.map _
        (fun a b hab h => hab (Fin.ext (getD_inj_of_nodup zero S hS a.val b.val a.isLt b.isLt h))) hL
      have hBound := cubeProver_round_flip_bound R n cs hcheck.1 p hcheck.2.1 hWrong vals hNd
      have hAll : vals.filter (fun z => decide (RoundPoly.evalCoeffs p z = cubeRound g n cs z)) = vals := by
        apply List.filter_eq_self.mpr
        intro z hz
        rcases List.mem_map.mp hz with ⟨ch, hch, rfl⟩
        have h := Decidable.of_not_not (hLive ch hch)
        change cubeLive g n x
          (if _ then some (cs ++ [S.getD ch.val zero], RoundPoly.evalCoeffs p (S.getD ch.val zero)) else none) at h
        rw [ite_eq_left hcheck] at h
        change RoundPoly.evalCoeffs p (S.getD ch.val zero) =
          cubeClaim g n (cs ++ [S.getD ch.val zero]) at h
        rw [← cubeRound_eq_claim] at h
        exact decide_eq_true h
      rw [hAll, List.length_map] at hBound
      exact hBound
    · have hempty : L = [] := by
        cases L with
        | nil => rfl
        | cons ch tail =>
          have h := Decidable.of_not_not (hLive ch (.head tail))
          change cubeLive g n x (if _ then _ else none) at h
          rw [ite_eq_right hcheck] at h
          exact False.elim h
      rw [hempty]; exact Nat.zero_le _

/-- Every round checks the degree and telescoping equation before the random challenge.
    A wrong running claim can become correct at at most `d` challenge values. -/
def cubeRoundSpec {g : List F → F} {d : Nat} (R : LineRep g d)
    (n : Nat) (S : List F) (hS : S.Nodup) (hpos : 0 < S.length) :
    SeqRoundSpec F (CubeState F) (List F) (cubeLive g n) where
  chalCard := S.length
  h_pos := hpos
  bad := d
  step := fun _ => cubeStep n d S
  flip_bound := cubeStep_flip_bound R n S hS

def cubeRoundSpecs {g : List F → F} {d : Nat} (R : LineRep g d)
    (n : Nat) (S : List F) (hS : S.Nodup) (hpos : 0 < S.length) :=
  List.replicate n (cubeRoundSpec R n S hS hpos)

/-- The terminal check evaluates the actual committed summand at the full challenge point. -/
def cubeVerify {g : List F → F} {d : Nat} (R : LineRep g d)
    (n : Nat) (S : List F) (hS : S.Nodup) (hpos : 0 < S.length)
    (x : F) (tr : List (List F × Nat)) : Bool :=
  match runSeqSpecs (cubeRoundSpecs R n S hS hpos) x (some ([], x)) tr with
  | none => false
  | some (cs, claim) => decide (cs.length = n ∧ claim = g cs)

def cubeIop {g : List F → F} {d : Nat} (R : LineRep g d)
    (n : Nat) (S : List F) (hS : S.Nodup) (hpos : 0 < S.length) :=
  seqSpecsIop (cubeRoundSpecs R n S hS hpos) (fun x => x = cubeClaim g n [])
    (cubeVerify R n S hS hpos)

/-- Round-by-round soundness of the executable Boolean-cube sumcheck, for arbitrary
    positive row/column dimensions. Its terminal check refers to the true summand. -/
def cubeRbr {g : List F → F} {d : Nat} (R : LineRep g d)
    (n : Nat) (S : List F) (hS : S.Nodup) (hpos : 0 < S.length) :
    RbrStateFunction (cubeIop R n S hS hpos) :=
  seqSpecsRbr (cubeRoundSpecs R n S hS hpos) (fun x => some ([], x))
    (fun x => x = cubeClaim g n []) (cubeVerify R n S hS hpos)
    (fun _ hx => hx) (fun x tr _ hv => by
      unfold cubeVerify at hv
      generalize runSeqSpecs (cubeRoundSpecs R n S hS hpos) x (some ([], x)) tr = st at hv ⊢
      cases st with
      | none => exact Bool.noConfusion hv
      | some st =>
        rcases st with ⟨cs, claim⟩
        have h : cs.length = n ∧ claim = g cs := of_decide_eq_true hv
        change claim = cubeClaim g n cs
        rw [cubeClaim_full g n cs h.1]
        exact h.2)

/-- State-restoration soundness against an adaptive rewinding tree, not just a fixed
    round polynomial. Rows instantiate `d=9`; columns instantiate `d=2`. -/
theorem cube_sumcheck_state_restoration_soundness {g : List F → F} {d : Nat}
    (R : LineRep g d) (n : Nat) (S : List F) (hS : S.Nodup) (hpos : 0 < S.length)
    (x : F) (hx : x ≠ cubeClaim g n [])
    (sched : List (Fin (cubeRoundSpecs R n S hS hpos).length))
    (tree : SrScheduleTree (cubeIop R n S hS hpos) sched) :
    RatBound.le (srTreeAcceptProb (cubeIop R n S hS hpos) tree x)
      (srScheduleErrorSum (cubeRbr R n S hS hpos) sched) :=
  rbr_implies_state_restoration_soundness (cubeRbr R n S hS hpos) x
    (by simpa only [cubeIop, seqSpecsIop_inLang] using hx) sched tree

#verify_constructive Qsag.ZkHem.cube_sumcheck_state_restoration_soundness
end CubeSumcheckSoundness

/-! ## §12. Audit gates -/

#verify_constructive Qsag.ZkHem.quartic_primitive_pad_bijection Qsag.ZkHem.pad_full_rank_iff
  Qsag.ZkHem.padded_evaluation_perfectly_simulated
  Qsag.ZkHem.libra_real_eq_sim Qsag.ZkHem.libra_sumcheck_perfectly_simulated
  Qsag.ZkHem.salted_leaves_identical_until_bad Qsag.ZkHem.salted_leaf_digest_simulated
  Qsag.ZkHem.companion_blend_perfectly_simulated
  Qsag.ZkHem.blended_terminal_fold_perfectly_simulated
  Qsag.ZkHem.opened_symbols_perfectly_simulated
  Qsag.ZkHem.zkHem_perfect_hvzk_simulation Qsag.ZkHem.zkHem_witness_indistinguishable
  Qsag.ZkHem.honest_linear_round
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
