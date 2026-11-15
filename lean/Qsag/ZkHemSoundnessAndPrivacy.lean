module
/-
# Qsag.ZkHemSoundnessAndPrivacy — zk-Hem pads, masks, simulation and extraction

Field: quartic Goldilocks `F_p ⊂ F_{p^2} ⊂ F_{p^4} = F_p[v]/(v^4 - 7)` in the certified tower
representation `Qsag.GoldilocksField.GoldilocksExt4` (`(A, B) = A + B v`, `A, B ∈ F_{p^2}`,
`v^2 = u`, `u^2 = 7`). In the polynomial basis `c_0 + c_1 v + c_2 v^2 + c_3 v^3` the tower
coordinate `B` is `(c_1, c_3)`, so `B = 0` is `c_1 = c_3 = 0`, i.e. membership in `F_{p^2}`.

§1  Pad rank. A base-field polynomial committed with four pad cells `r_0..r_3 ∈ F_p` contributes
    `r_0 + r_1 z + r_2 z^2 + r_3 z^3` to its evaluation at the WHIR point `(z, z^2, ...)`.
    `quartic_primitive_pad_bijection`: for `B ≠ 0` this map `F_p^4 → F_{p^4}` has an explicit
    two-sided inverse. `tooth_quadratic_subfield_pad_rank_deficient`: for `B = 0` its image
    lies in `F_{p^2}`.
-/

public import Qsag.GoldilocksPrimalityAndExt4Field
import all Qsag.Goldilocks
import all Qsag.GoldilocksPrimalityAndExt4Field
public import Qsag.AffineProximityGaps
public import Qsag.MultiRoundFsQrom
public import Qsag.Tactic.ConstructiveRing
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
    add w (padMap z r) ≠ add w' (padMap z r') := by
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

end Qsag.ZkHem
end
