module
public import Qsag.Math.Goldilocks
public import Qsag.Spec.Encoding
public import Qsag.Tactic.Prelude

public section
namespace Qsag
set_option autoImplicit false
/-! ## §4. `QuarticGoldilocks` Quartic Extension Field, Polynomial Root-Counting Schwartz–Zippel
           & `Hem` WHIR Soundness Regimes (`crates/qsag-agg/src/field.rs`, `pcs.rs`) -/

private theorem quadExtMulComm0 {R : Type} [LawfulCommRing R] (n x0 x1 y0 y1 : R) :
    CommRingOps.add (CommRingOps.mul x0 y0) (CommRingOps.mul n (CommRingOps.mul x1 y1)) =
      CommRingOps.add (CommRingOps.mul y0 x0) (CommRingOps.mul n (CommRingOps.mul y1 x1)) := by
  rw [LawfulCommRing.mul_comm x0 y0, LawfulCommRing.mul_comm x1 y1]

private theorem quadExtMulComm1 {R : Type} [LawfulCommRing R] (x0 x1 y0 y1 : R) :
    CommRingOps.add (CommRingOps.mul x0 y1) (CommRingOps.mul x1 y0) =
      CommRingOps.add (CommRingOps.mul y0 x1) (CommRingOps.mul y1 x0) := by
  rw [LawfulCommRing.mul_comm x0 y1, LawfulCommRing.mul_comm x1 y0, LawfulCommRing.add_comm]

private theorem quadExtOneMul0 {R : Type} [LawfulCommRing R] (n x0 x1 : R) :
    CommRingOps.add (CommRingOps.mul CommRingOps.one x0)
      (CommRingOps.mul n (CommRingOps.mul CommRingOps.zero x1)) = x0 := by
  rw [LawfulCommRing.one_mul, LawfulCommRing.zero_mul, LawfulCommRing.mul_zero,
      LawfulCommRing.add_zero]

private theorem quadExtOneMul1 {R : Type} [LawfulCommRing R] (x0 x1 : R) :
    CommRingOps.add (CommRingOps.mul CommRingOps.one x1)
      (CommRingOps.mul CommRingOps.zero x0) = x1 := by
  rw [LawfulCommRing.one_mul, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]

private theorem quadExtMulOne0 {R : Type} [LawfulCommRing R] (n x0 x1 : R) :
    CommRingOps.add (CommRingOps.mul x0 CommRingOps.one)
      (CommRingOps.mul n (CommRingOps.mul x1 CommRingOps.zero)) = x0 := by
  rw [LawfulCommRing.mul_one, LawfulCommRing.mul_zero, LawfulCommRing.mul_zero,
      LawfulCommRing.add_zero]

private theorem quadExtMulOne1 {R : Type} [LawfulCommRing R] (x0 x1 : R) :
    CommRingOps.add (CommRingOps.mul x0 CommRingOps.zero)
      (CommRingOps.mul x1 CommRingOps.one) = x1 := by
  rw [LawfulCommRing.mul_zero, LawfulCommRing.mul_one, LawfulCommRing.zero_add]

private theorem quadExtLeftDistrib0 {R : Type} [LawfulCommRing R] (n x0 x1 y0 y1 z0 z1 : R) :
    CommRingOps.add (CommRingOps.mul x0 (CommRingOps.add y0 z0))
      (CommRingOps.mul n (CommRingOps.mul x1 (CommRingOps.add y1 z1))) =
    CommRingOps.add
      (CommRingOps.add (CommRingOps.mul x0 y0) (CommRingOps.mul n (CommRingOps.mul x1 y1)))
      (CommRingOps.add (CommRingOps.mul x0 z0) (CommRingOps.mul n (CommRingOps.mul x1 z1))) := by
  rw [LawfulCommRing.left_distrib, LawfulCommRing.left_distrib, LawfulCommRing.left_distrib]
  exact LawfulCommRing.add_add_add_comm _ _ _ _

private theorem quadExtLeftDistrib1 {R : Type} [LawfulCommRing R] (x0 x1 y0 y1 z0 z1 : R) :
    CommRingOps.add (CommRingOps.mul x0 (CommRingOps.add y1 z1))
      (CommRingOps.mul x1 (CommRingOps.add y0 z0)) =
    CommRingOps.add
      (CommRingOps.add (CommRingOps.mul x0 y1) (CommRingOps.mul x1 y0))
      (CommRingOps.add (CommRingOps.mul x0 z1) (CommRingOps.mul x1 z0)) := by
  rw [LawfulCommRing.left_distrib, LawfulCommRing.left_distrib]
  exact LawfulCommRing.add_add_add_comm _ _ _ _

private theorem quadExtRightDistrib0 {R : Type} [LawfulCommRing R] (n x0 x1 y0 y1 z0 z1 : R) :
    CommRingOps.add (CommRingOps.mul (CommRingOps.add x0 y0) z0)
      (CommRingOps.mul n (CommRingOps.mul (CommRingOps.add x1 y1) z1)) =
    CommRingOps.add
      (CommRingOps.add (CommRingOps.mul x0 z0) (CommRingOps.mul n (CommRingOps.mul x1 z1)))
      (CommRingOps.add (CommRingOps.mul y0 z0) (CommRingOps.mul n (CommRingOps.mul y1 z1))) := by
  rw [LawfulCommRing.right_distrib, LawfulCommRing.right_distrib, LawfulCommRing.left_distrib]
  exact LawfulCommRing.add_add_add_comm _ _ _ _

private theorem quadExtRightDistrib1 {R : Type} [LawfulCommRing R] (x0 x1 y0 y1 z0 z1 : R) :
    CommRingOps.add (CommRingOps.mul (CommRingOps.add x0 y0) z1)
      (CommRingOps.mul (CommRingOps.add x1 y1) z0) =
    CommRingOps.add
      (CommRingOps.add (CommRingOps.mul x0 z1) (CommRingOps.mul x1 z0))
      (CommRingOps.add (CommRingOps.mul y0 z1) (CommRingOps.mul y1 z0)) := by
  rw [LawfulCommRing.right_distrib, LawfulCommRing.right_distrib]
  exact LawfulCommRing.add_add_add_comm _ _ _ _

private theorem quadExtMulAssoc0 {R : Type} [LawfulCommRing R] (n x0 x1 y0 y1 z0 z1 : R) :
    CommRingOps.add
      (CommRingOps.mul
        (CommRingOps.add (CommRingOps.mul x0 y0) (CommRingOps.mul n (CommRingOps.mul x1 y1))) z0)
      (CommRingOps.mul n
        (CommRingOps.mul (CommRingOps.add (CommRingOps.mul x0 y1) (CommRingOps.mul x1 y0)) z1)) =
    CommRingOps.add
      (CommRingOps.mul x0
        (CommRingOps.add (CommRingOps.mul y0 z0) (CommRingOps.mul n (CommRingOps.mul y1 z1))))
      (CommRingOps.mul n
        (CommRingOps.mul x1 (CommRingOps.add (CommRingOps.mul y0 z1) (CommRingOps.mul y1 z0)))) := by
  rw [LawfulCommRing.right_distrib, LawfulCommRing.right_distrib,
      LawfulCommRing.left_distrib, LawfulCommRing.left_distrib,
      LawfulCommRing.left_distrib, LawfulCommRing.left_distrib]
  have t1 : CommRingOps.mul (CommRingOps.mul x0 y0) z0 =
      CommRingOps.mul x0 (CommRingOps.mul y0 z0) :=
    LawfulCommRing.mul_assoc _ _ _
  have t2 : CommRingOps.mul (CommRingOps.mul n (CommRingOps.mul x1 y1)) z0 =
      CommRingOps.mul n (CommRingOps.mul x1 (CommRingOps.mul y1 z0)) := by
    rw [LawfulCommRing.mul_assoc, LawfulCommRing.mul_assoc]
  have t3 : CommRingOps.mul n (CommRingOps.mul (CommRingOps.mul x0 y1) z1) =
      CommRingOps.mul x0 (CommRingOps.mul n (CommRingOps.mul y1 z1)) := by
    rw [LawfulCommRing.mul_assoc x0 y1 z1,
        ← LawfulCommRing.mul_assoc n x0 _,
        LawfulCommRing.mul_comm n x0,
        LawfulCommRing.mul_assoc]
  have t4 : CommRingOps.mul n (CommRingOps.mul (CommRingOps.mul x1 y0) z1) =
      CommRingOps.mul n (CommRingOps.mul x1 (CommRingOps.mul y0 z1)) := by
    rw [LawfulCommRing.mul_assoc]
  rw [t1, t2, t3, t4, LawfulCommRing.add_add_add_comm]
  congr 1
  exact LawfulCommRing.add_comm _ _

private theorem quadExtMulAssoc1 {R : Type} [LawfulCommRing R] (n x0 x1 y0 y1 z0 z1 : R) :
    CommRingOps.add
      (CommRingOps.mul
        (CommRingOps.add (CommRingOps.mul x0 y0) (CommRingOps.mul n (CommRingOps.mul x1 y1))) z1)
      (CommRingOps.mul
        (CommRingOps.add (CommRingOps.mul x0 y1) (CommRingOps.mul x1 y0)) z0) =
    CommRingOps.add
      (CommRingOps.mul x0
        (CommRingOps.add (CommRingOps.mul y0 z1) (CommRingOps.mul y1 z0)))
      (CommRingOps.mul x1
        (CommRingOps.add (CommRingOps.mul y0 z0) (CommRingOps.mul n (CommRingOps.mul y1 z1)))) := by
  rw [LawfulCommRing.right_distrib, LawfulCommRing.right_distrib,
      LawfulCommRing.left_distrib, LawfulCommRing.left_distrib]
  have s1 : CommRingOps.mul (CommRingOps.mul x0 y0) z1 =
      CommRingOps.mul x0 (CommRingOps.mul y0 z1) :=
    LawfulCommRing.mul_assoc _ _ _
  have s2 : CommRingOps.mul (CommRingOps.mul n (CommRingOps.mul x1 y1)) z1 =
      CommRingOps.mul x1 (CommRingOps.mul n (CommRingOps.mul y1 z1)) := by
    rw [LawfulCommRing.mul_assoc n _ z1,
        LawfulCommRing.mul_assoc x1 y1 z1,
        ← LawfulCommRing.mul_assoc n x1 _,
        LawfulCommRing.mul_comm n x1,
        LawfulCommRing.mul_assoc]
  have s3 : CommRingOps.mul (CommRingOps.mul x0 y1) z0 =
      CommRingOps.mul x0 (CommRingOps.mul y1 z0) :=
    LawfulCommRing.mul_assoc _ _ _
  have s4 : CommRingOps.mul (CommRingOps.mul x1 y0) z0 =
      CommRingOps.mul x1 (CommRingOps.mul y0 z0) :=
    LawfulCommRing.mul_assoc _ _ _
  rw [s1, s2, s3, s4, LawfulCommRing.add_add_add_comm]
  congr 1
  exact LawfulCommRing.add_comm _ _

/-- Quartic extension field `QuarticGoldilocks = 𝔽_{p^2}[v] / (v^2 - u)` where `u = GoldilocksExt2.uBasis`
    (`u^2 = 7`), matching `GoldilocksExt4` in `crates/qsag-agg/src/field.rs` (`|𝔽_{p^4}| = p^4 > 2^255`). -/
structure QuarticGoldilocks where
  c0 : GoldilocksExt2
  c1 : GoldilocksExt2
  deriving DecidableEq, Repr

namespace QuarticGoldilocks

@[ext] theorem ext {x y : QuarticGoldilocks} (h0 : x.c0 = y.c0) (h1 : x.c1 = y.c1) : x = y := by
  cases x; cases y; subst h0; subst h1; rfl

def zero : QuarticGoldilocks := ⟨CommRingOps.zero, CommRingOps.zero⟩
def one : QuarticGoldilocks := ⟨CommRingOps.one, CommRingOps.zero⟩
def vBasis : QuarticGoldilocks := ⟨CommRingOps.zero, CommRingOps.one⟩
def ofExt2 (a : GoldilocksExt2) : QuarticGoldilocks := ⟨a, CommRingOps.zero⟩

instance : Inhabited QuarticGoldilocks := ⟨zero⟩

def add (x y : QuarticGoldilocks) : QuarticGoldilocks :=
  ⟨CommRingOps.add x.c0 y.c0, CommRingOps.add x.c1 y.c1⟩

def neg (x : QuarticGoldilocks) : QuarticGoldilocks :=
  ⟨CommRingOps.neg x.c0, CommRingOps.neg x.c1⟩

def sub (x y : QuarticGoldilocks) : QuarticGoldilocks :=
  ⟨CommRingOps.sub x.c0 y.c0, CommRingOps.sub x.c1 y.c1⟩

def mul (x y : QuarticGoldilocks) : QuarticGoldilocks :=
  ⟨CommRingOps.add (CommRingOps.mul x.c0 y.c0)
      (CommRingOps.mul GoldilocksExt2.uBasis (CommRingOps.mul x.c1 y.c1)),
   CommRingOps.add (CommRingOps.mul x.c0 y.c1) (CommRingOps.mul x.c1 y.c0)⟩

instance : CommRingOps QuarticGoldilocks where
  zero := zero
  one := one
  add := add
  mul := mul
  neg := neg
  sub := sub

instance : LawfulCommRing QuarticGoldilocks where
  add_assoc x y z := by
    apply ext
    · exact LawfulCommRing.add_assoc x.c0 y.c0 z.c0
    · exact LawfulCommRing.add_assoc x.c1 y.c1 z.c1
  add_comm x y := by
    apply ext
    · exact LawfulCommRing.add_comm x.c0 y.c0
    · exact LawfulCommRing.add_comm x.c1 y.c1
  zero_add x := by
    apply ext
    · exact LawfulCommRing.zero_add x.c0
    · exact LawfulCommRing.zero_add x.c1
  add_zero x := by
    apply ext
    · exact LawfulCommRing.add_zero x.c0
    · exact LawfulCommRing.add_zero x.c1
  add_left_neg x := by
    apply ext
    · exact LawfulCommRing.add_left_neg x.c0
    · exact LawfulCommRing.add_left_neg x.c1
  sub_eq_add_neg x y := by
    apply ext
    · exact LawfulCommRing.sub_eq_add_neg x.c0 y.c0
    · exact LawfulCommRing.sub_eq_add_neg x.c1 y.c1
  mul_comm x y := by
    apply ext
    · exact quadExtMulComm0 GoldilocksExt2.uBasis x.c0 x.c1 y.c0 y.c1
    · exact quadExtMulComm1 x.c0 x.c1 y.c0 y.c1
  one_mul x := by
    apply ext
    · exact quadExtOneMul0 GoldilocksExt2.uBasis x.c0 x.c1
    · exact quadExtOneMul1 x.c0 x.c1
  mul_one x := by
    apply ext
    · exact quadExtMulOne0 GoldilocksExt2.uBasis x.c0 x.c1
    · exact quadExtMulOne1 x.c0 x.c1
  left_distrib x y z := by
    apply ext
    · exact quadExtLeftDistrib0 GoldilocksExt2.uBasis x.c0 x.c1 y.c0 y.c1 z.c0 z.c1
    · exact quadExtLeftDistrib1 x.c0 x.c1 y.c0 y.c1 z.c0 z.c1
  right_distrib x y z := by
    apply ext
    · exact quadExtRightDistrib0 GoldilocksExt2.uBasis x.c0 x.c1 y.c0 y.c1 z.c0 z.c1
    · exact quadExtRightDistrib1 x.c0 x.c1 y.c0 y.c1 z.c0 z.c1
  mul_assoc x y z := by
    apply ext
    · exact quadExtMulAssoc0 GoldilocksExt2.uBasis x.c0 x.c1 y.c0 y.c1 z.c0 z.c1
    · exact quadExtMulAssoc1 GoldilocksExt2.uBasis x.c0 x.c1 y.c0 y.c1 z.c0 z.c1

/-- Square root of `-1` in `Goldilocks` (`2^48` since `(2^48)^2 = 2^96 ≡ -1 mod p`). -/
def sqrtNegOneGoldilocks : Goldilocks := Goldilocks.ofNat 281474976710656

private theorem sqrtNegOne_sq :
    CommRingOps.mul sqrtNegOneGoldilocks sqrtNegOneGoldilocks =
      CommRingOps.neg (CommRingOps.one : Goldilocks) := by
  apply Goldilocks.ext
  show (Goldilocks.mul sqrtNegOneGoldilocks sqrtNegOneGoldilocks).val = (Goldilocks.neg Goldilocks.one).val
  rw [Goldilocks.mul_val, Goldilocks.neg_val]
  decide

/-- **Quartic Irreducibility Theorem (`uBasis_not_square`)**:
    `u = ⟨0, 1⟩ ∈ GoldilocksExt2` has no square root in `GoldilocksExt2`, so `v^2 - u` is
    irreducible over `𝔽_{p^2}` and `QuarticGoldilocks` is a genuine field! -/
theorem uBasis_not_square (z : GoldilocksExt2) :
    CommRingOps.mul z z ≠ GoldilocksExt2.uBasis := by
  intro hSq
  have hRe : CommRingOps.add (CommRingOps.mul z.c0 z.c0)
      (CommRingOps.mul GoldilocksExt2.nonResidue (CommRingOps.mul z.c1 z.c1)) =
      (CommRingOps.zero : Goldilocks) := by
    simpa only [GoldilocksExt2.mul_c0, GoldilocksExt2.uBasis_c0] using congrArg GoldilocksExt2.c0 hSq
  have hIm : CommRingOps.add (CommRingOps.mul z.c0 z.c1) (CommRingOps.mul z.c1 z.c0) =
      (CommRingOps.one : Goldilocks) := by
    simpa only [GoldilocksExt2.mul_c1, GoldilocksExt2.uBasis_c1] using congrArg GoldilocksExt2.c1 hSq
  if hc1 : z.c1 = Goldilocks.zero then
    rw [hc1] at hIm
    change CommRingOps.add (CommRingOps.mul z.c0 CommRingOps.zero)
        (CommRingOps.mul CommRingOps.zero z.c0) = CommRingOps.one at hIm
    rw [LawfulCommRing.mul_zero, LawfulCommRing.zero_mul, LawfulCommRing.add_zero] at hIm
    exact absurd (congrArg Goldilocks.val hIm) (by decide)
  else
    have hNegEq : CommRingOps.mul z.c0 z.c0 =
        CommRingOps.neg (CommRingOps.mul GoldilocksExt2.nonResidue (CommRingOps.mul z.c1 z.c1)) := by
      have hSub := congrArg (fun t =>
        CommRingOps.add t (CommRingOps.neg (CommRingOps.mul GoldilocksExt2.nonResidue (CommRingOps.mul z.c1 z.c1)))) hRe
      rw [LawfulCommRing.add_assoc, LawfulCommRing.add_right_neg,
          LawfulCommRing.add_zero, LawfulCommRing.zero_add] at hSub
      exact hSub
    let w : Goldilocks :=
      CommRingOps.mul (CommRingOps.mul z.c0 (Goldilocks.inv z.c1)) sqrtNegOneGoldilocks
    have hwSq : CommRingOps.mul w w = GoldilocksExt2.nonResidue := by
      dsimp only [w]
      let q := CommRingOps.mul z.c0 (Goldilocks.inv z.c1)
      have h1 : CommRingOps.mul (CommRingOps.mul q sqrtNegOneGoldilocks)
          (CommRingOps.mul q sqrtNegOneGoldilocks) =
          CommRingOps.mul (CommRingOps.mul q q)
            (CommRingOps.mul sqrtNegOneGoldilocks sqrtNegOneGoldilocks) := by
        rw [LawfulCommRing.mul_assoc q sqrtNegOneGoldilocks _,
            ← LawfulCommRing.mul_assoc sqrtNegOneGoldilocks q _,
            LawfulCommRing.mul_comm sqrtNegOneGoldilocks q,
            LawfulCommRing.mul_assoc q sqrtNegOneGoldilocks _,
            ← LawfulCommRing.mul_assoc q q _]
      have hqSq : CommRingOps.mul q q = CommRingOps.neg GoldilocksExt2.nonResidue := by
        dsimp only [q]
        have ha : CommRingOps.mul (CommRingOps.mul z.c0 (Goldilocks.inv z.c1))
            (CommRingOps.mul z.c0 (Goldilocks.inv z.c1)) =
            CommRingOps.mul (CommRingOps.mul z.c0 z.c0)
              (CommRingOps.mul (Goldilocks.inv z.c1) (Goldilocks.inv z.c1)) := by
          rw [LawfulCommRing.mul_assoc z.c0 (Goldilocks.inv z.c1) _,
              ← LawfulCommRing.mul_assoc (Goldilocks.inv z.c1) z.c0 _,
              LawfulCommRing.mul_comm (Goldilocks.inv z.c1) z.c0,
              LawfulCommRing.mul_assoc z.c0 (Goldilocks.inv z.c1) _,
              ← LawfulCommRing.mul_assoc z.c0 z.c0 _]
        rw [ha, hNegEq, LawfulCommRing.neg_mul, LawfulCommRing.mul_assoc GoldilocksExt2.nonResidue]
        have hCancel : CommRingOps.mul (CommRingOps.mul z.c1 z.c1)
            (CommRingOps.mul (Goldilocks.inv z.c1) (Goldilocks.inv z.c1)) = CommRingOps.one := by
          rw [LawfulCommRing.mul_assoc z.c1 z.c1 _,
              ← LawfulCommRing.mul_assoc z.c1 (Goldilocks.inv z.c1) _,
              Goldilocks.mul_inv_cancel hc1, LawfulCommRing.one_mul,
              Goldilocks.mul_inv_cancel hc1]
        rw [hCancel, LawfulCommRing.mul_one]
      rw [h1, hqSq, sqrtNegOne_sq, LawfulCommRing.neg_mul, LawfulCommRing.mul_neg,
          LawfulCommRing.mul_one, LawfulCommRing.neg_neg]
    exact GoldilocksExt2.nonResidue_not_square w hwSq

def norm (z : QuarticGoldilocks) : GoldilocksExt2 :=
  CommRingOps.sub (CommRingOps.mul z.c0 z.c0)
    (CommRingOps.mul GoldilocksExt2.uBasis (CommRingOps.mul z.c1 z.c1))

theorem norm_ne_zero {z : QuarticGoldilocks} (hz : z ≠ zero) :
    norm z ≠ GoldilocksExt2.zero := by
  intro hNorm
  have hEq : CommRingOps.mul z.c0 z.c0 =
      CommRingOps.mul GoldilocksExt2.uBasis (CommRingOps.mul z.c1 z.c1) :=
    LawfulCommRing.sub_eq_zero_iff.mp hNorm
  if hc1 : z.c1 = GoldilocksExt2.zero then
    have hrhs : CommRingOps.mul GoldilocksExt2.uBasis (CommRingOps.mul z.c1 z.c1) =
        GoldilocksExt2.zero := by
      rw [hc1]
      change CommRingOps.mul GoldilocksExt2.uBasis
        (CommRingOps.mul CommRingOps.zero CommRingOps.zero) = CommRingOps.zero
      rw [LawfulCommRing.mul_zero, LawfulCommRing.mul_zero]
    rw [hrhs] at hEq
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hEq with hc0 | hc0 <;>
      exact hz (ext hc0 hc1)
  else
    let q := CommRingOps.mul z.c0 (GoldilocksExt2.inv z.c1)
    have hqSq : CommRingOps.mul q q = GoldilocksExt2.uBasis := by
      dsimp only [q]
      have hassoc : CommRingOps.mul (CommRingOps.mul z.c0 (GoldilocksExt2.inv z.c1))
          (CommRingOps.mul z.c0 (GoldilocksExt2.inv z.c1)) =
          CommRingOps.mul (CommRingOps.mul z.c0 z.c0)
            (CommRingOps.mul (GoldilocksExt2.inv z.c1) (GoldilocksExt2.inv z.c1)) := by
        rw [LawfulCommRing.mul_assoc z.c0 (GoldilocksExt2.inv z.c1) _,
            ← LawfulCommRing.mul_assoc (GoldilocksExt2.inv z.c1) z.c0 _,
            LawfulCommRing.mul_comm (GoldilocksExt2.inv z.c1) z.c0,
            LawfulCommRing.mul_assoc z.c0 (GoldilocksExt2.inv z.c1) _,
            ← LawfulCommRing.mul_assoc z.c0 z.c0 _]
      rw [hassoc, hEq, LawfulCommRing.mul_assoc GoldilocksExt2.uBasis]
      have hCancel : CommRingOps.mul (CommRingOps.mul z.c1 z.c1)
          (CommRingOps.mul (GoldilocksExt2.inv z.c1) (GoldilocksExt2.inv z.c1)) = CommRingOps.one := by
        rw [LawfulCommRing.mul_assoc z.c1 z.c1 _,
            ← LawfulCommRing.mul_assoc z.c1 (GoldilocksExt2.inv z.c1) _,
            GoldilocksExt2.mul_inv_cancel hc1, LawfulCommRing.one_mul,
            GoldilocksExt2.mul_inv_cancel hc1]
      rw [hCancel, LawfulCommRing.mul_one]
    exact uBasis_not_square q hqSq

def inv (z : QuarticGoldilocks) : QuarticGoldilocks :=
  let invN := GoldilocksExt2.inv (norm z)
  ⟨CommRingOps.mul z.c0 invN, CommRingOps.neg (CommRingOps.mul z.c1 invN)⟩

theorem mul_inv_cancel {z : QuarticGoldilocks} (hz : z ≠ zero) :
    CommRingOps.mul z (inv z) = CommRingOps.one := by
  have hnormNe := norm_ne_zero hz
  let invN := GoldilocksExt2.inv (norm z)
  apply ext
  · change CommRingOps.add
        (CommRingOps.mul z.c0 (CommRingOps.mul z.c0 invN))
        (CommRingOps.mul GoldilocksExt2.uBasis
          (CommRingOps.mul z.c1 (CommRingOps.neg (CommRingOps.mul z.c1 invN)))) =
      CommRingOps.one
    rw [← LawfulCommRing.mul_assoc z.c0 z.c0 invN,
        LawfulCommRing.mul_neg z.c1, LawfulCommRing.mul_neg GoldilocksExt2.uBasis,
        ← LawfulCommRing.mul_assoc z.c1 z.c1 invN,
        ← LawfulCommRing.mul_assoc GoldilocksExt2.uBasis _ invN,
        ← LawfulCommRing.sub_eq_add_neg,
        ← LawfulCommRing.sub_mul]
    exact GoldilocksExt2.mul_inv_cancel hnormNe
  · change CommRingOps.add
        (CommRingOps.mul z.c0 (CommRingOps.neg (CommRingOps.mul z.c1 invN)))
        (CommRingOps.mul z.c1 (CommRingOps.mul z.c0 invN)) =
      CommRingOps.zero
    rw [LawfulCommRing.mul_neg,
        ← LawfulCommRing.mul_assoc z.c0 z.c1 invN,
        ← LawfulCommRing.mul_assoc z.c1 z.c0 invN,
        LawfulCommRing.mul_comm z.c1 z.c0,
        LawfulCommRing.add_left_neg]

end QuarticGoldilocks

instance : NoZeroDivisors QuarticGoldilocks where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} h := by
    if ha : a = QuarticGoldilocks.zero then
      exact .inl ha
    else
      right
      have hmul := congrArg (CommRingOps.mul (QuarticGoldilocks.inv a)) h
      rw [LawfulCommRing.mul_zero, ← LawfulCommRing.mul_assoc,
          LawfulCommRing.mul_comm (QuarticGoldilocks.inv a) a,
          QuarticGoldilocks.mul_inv_cancel ha, LawfulCommRing.one_mul] at hmul
      exact hmul



theorem QuarticGoldilocks.inv_zero :
    QuarticGoldilocks.inv QuarticGoldilocks.zero = QuarticGoldilocks.zero := by
  unfold QuarticGoldilocks.inv QuarticGoldilocks.zero
  apply QuarticGoldilocks.ext <;> dsimp only
  · exact LawfulCommRing.zero_mul _
  · rw [LawfulCommRing.zero_mul]
    have h1 := LawfulCommRing.add_left_neg (CommRingOps.zero : GoldilocksExt2)
    rw [LawfulCommRing.add_zero] at h1
    exact h1

instance : Mul QuarticGoldilocks := ⟨QuarticGoldilocks.mul⟩
instance : Inv QuarticGoldilocks := ⟨QuarticGoldilocks.inv⟩
instance : LawfulField QuarticGoldilocks where
  inv := QuarticGoldilocks.inv
  zero_ne_one h := by
    have hz := congrArg (fun z : QuarticGoldilocks => z.c0.c0) h
    have hf : Goldilocks.zero = Goldilocks.one := by
      simpa only [CommRingOps.zero, CommRingOps.one, QuarticGoldilocks.zero, QuarticGoldilocks.one,
        GoldilocksExt2.zero_c0, GoldilocksExt2.one_c0] using hz
    exact Nat.noConfusion (congrArg Goldilocks.val hf)
  inv_zero := QuarticGoldilocks.inv_zero
  mul_inv_cancel := QuarticGoldilocks.mul_inv_cancel

namespace GoldilocksField
/-- Compatibility spelling of the canonical tower field. -/
abbrev GoldilocksExt4 := Qsag.QuarticGoldilocks
namespace GoldilocksExt4
abbrev c0 (z : GoldilocksExt4) := QuarticGoldilocks.c0 z
abbrev c1 (z : GoldilocksExt4) := QuarticGoldilocks.c1 z
abbrev mk := QuarticGoldilocks.mk
abbrev ext := @QuarticGoldilocks.ext
abbrev nonResidue := GoldilocksExt2.uBasis
abbrev zero := QuarticGoldilocks.zero
abbrev one := QuarticGoldilocks.one
abbrev vBasis := QuarticGoldilocks.vBasis
abbrev ofExt2 := QuarticGoldilocks.ofExt2
abbrev add := QuarticGoldilocks.add
abbrev neg := QuarticGoldilocks.neg
abbrev sub := QuarticGoldilocks.sub
abbrev mul := QuarticGoldilocks.mul
abbrev norm := QuarticGoldilocks.norm
abbrev inv := QuarticGoldilocks.inv

def embedBase (a : Goldilocks) : GoldilocksExt4 := ofExt2 (GoldilocksExt2.ofBase a)
theorem uBasis_not_square (z : GoldilocksExt2) : CommRingOps.mul z z ≠ nonResidue := QuarticGoldilocks.uBasis_not_square z
theorem norm_ne_zero {z : GoldilocksExt4} (hz : z ≠ zero) : norm z ≠ GoldilocksExt2.zero := QuarticGoldilocks.norm_ne_zero hz
theorem ext4_mul_inv_cancel {z : GoldilocksExt4} (hz : z ≠ zero) : z * z⁻¹ = one ∧ z⁻¹ * z = one :=
  ⟨QuarticGoldilocks.mul_inv_cancel hz, (LawfulCommRing.mul_comm _ _).trans (QuarticGoldilocks.mul_inv_cancel hz)⟩
/-- **Absence of Non-Trivial Zero Divisors in `GoldilocksExt4` (`ext4_mul_eq_zero_iff`)**. -/
theorem ext4_mul_eq_zero_iff (z w : GoldilocksExt4) : z * w = zero ↔ z = zero ∨ w = zero := by
  constructor
  · exact NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero
  · rintro (rfl | rfl)
    · exact LawfulCommRing.zero_mul w
    · exact LawfulCommRing.mul_zero z


theorem vBasis_pow4_eq_seven :
    (vBasis * vBasis) * (vBasis * vBasis) = embedBase GoldilocksExt2.nonResidue := by
  have hs : vBasis * vBasis = ofExt2 GoldilocksExt2.uBasis := by
    apply ext <;> change _ = _
    · change CommRingOps.add (CommRingOps.mul CommRingOps.zero CommRingOps.zero)
        (CommRingOps.mul GoldilocksExt2.uBasis (CommRingOps.mul CommRingOps.one CommRingOps.one)) = GoldilocksExt2.uBasis
      rw [LawfulCommRing.zero_mul, LawfulCommRing.mul_one, LawfulCommRing.mul_one, LawfulCommRing.zero_add]
    · change CommRingOps.add (CommRingOps.mul CommRingOps.zero CommRingOps.one)
        (CommRingOps.mul CommRingOps.one CommRingOps.zero) = CommRingOps.zero
      rw [LawfulCommRing.zero_mul, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  rw [hs]
  apply ext
  · change CommRingOps.add (GoldilocksExt2.mul GoldilocksExt2.uBasis GoldilocksExt2.uBasis)
      (CommRingOps.mul GoldilocksExt2.uBasis (CommRingOps.mul CommRingOps.zero CommRingOps.zero)) = GoldilocksExt2.ofBase GoldilocksExt2.nonResidue
    rw [LawfulCommRing.zero_mul, LawfulCommRing.mul_zero, LawfulCommRing.add_zero, GoldilocksExt2.uBasis_mul_self]
  · change CommRingOps.add (CommRingOps.mul GoldilocksExt2.uBasis CommRingOps.zero)
      (CommRingOps.mul CommRingOps.zero GoldilocksExt2.uBasis) = CommRingOps.zero
    rw [LawfulCommRing.mul_zero, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]

/-- Direct polynomial-basis carrier $a_0 + a_1 v + a_2 v^2 + a_3 v^3 \in \mathbb{F}_p[v]/(v^4 - 7)$. -/
structure Ext4Poly where
  a0 : Goldilocks
  a1 : Goldilocks
  a2 : Goldilocks
  a3 : Goldilocks
  deriving DecidableEq, Repr

/-- Multiplication directly in polynomial basis $[1, v, v^2, v^3]$ modulo $v^4 - 7$. -/
@[expose] def Ext4Poly.mul (x y : Ext4Poly) : Ext4Poly :=
  let s := GoldilocksExt2.nonResidue
  { a0 := CommRingOps.add (CommRingOps.mul x.a0 y.a0)
            (CommRingOps.mul s (CommRingOps.add (CommRingOps.add (CommRingOps.mul x.a1 y.a3)
              (CommRingOps.mul x.a2 y.a2)) (CommRingOps.mul x.a3 y.a1)))
    a1 := CommRingOps.add (CommRingOps.add (CommRingOps.mul x.a0 y.a1) (CommRingOps.mul x.a1 y.a0))
            (CommRingOps.mul s (CommRingOps.add (CommRingOps.mul x.a2 y.a3) (CommRingOps.mul x.a3 y.a2)))
    a2 := CommRingOps.add (CommRingOps.add (CommRingOps.add (CommRingOps.mul x.a0 y.a2)
            (CommRingOps.mul x.a1 y.a1)) (CommRingOps.mul x.a2 y.a0))
            (CommRingOps.mul s (CommRingOps.mul x.a3 y.a3))
    a3 := CommRingOps.add (CommRingOps.add (CommRingOps.mul x.a0 y.a3) (CommRingOps.mul x.a1 y.a2))
            (CommRingOps.add (CommRingOps.mul x.a2 y.a1) (CommRingOps.mul x.a3 y.a0)) }

/-- `[0, 2, 1, 3]` basis bijection mapping `(A0 + A1 u) + (B0 + B1 u) v` to `A0 + B0 v + A1 v^2 + B1 v^3`. -/
@[expose] def towerToPoly (z : GoldilocksExt4) : Ext4Poly := ⟨z.c0.c0, z.c1.c0, z.c0.c1, z.c1.c1⟩
def polyToTower (p : Ext4Poly) : GoldilocksExt4 := ⟨⟨p.a0, p.a2⟩, ⟨p.a1, p.a3⟩⟩

theorem polyToTower_towerToPoly (z : GoldilocksExt4) : polyToTower (towerToPoly z) = z := by
  cases z with | mk c0 c1 => cases c0; cases c1; rfl
theorem towerToPoly_polyToTower (p : Ext4Poly) : towerToPoly (polyToTower p) = p := by
  cases p; rfl

/-- Ring-multiplication homomorphism between quadratic tower `GoldilocksExt4` and $\mathbb{F}_p[v]/(v^4 - 7)$. -/
theorem towerToPoly_mul_hom (x y : GoldilocksExt4) :
    towerToPoly (x * y) = Ext4Poly.mul (towerToPoly x) (towerToPoly y) := by
  unfold towerToPoly Ext4Poly.mul
  change Ext4Poly.mk ((QuarticGoldilocks.mul x y).c0.c0) ((QuarticGoldilocks.mul x y).c1.c0)
    ((QuarticGoldilocks.mul x y).c0.c1) ((QuarticGoldilocks.mul x y).c1.c1) = _
  simp only [QuarticGoldilocks.mul,
    GoldilocksExt2.add_c0, GoldilocksExt2.add_c1, GoldilocksExt2.mul_c0, GoldilocksExt2.mul_c1,
    GoldilocksExt2.uBasis_c0, GoldilocksExt2.uBasis_c1]
  congr 1 <;> constructive_ring



def ofLimbs (l0 l1 l2 l3 : Goldilocks) : GoldilocksExt4 := ⟨⟨l0, l1⟩, ⟨l2, l3⟩⟩
def toLimbs (x : GoldilocksExt4) : List Goldilocks := [x.c0.c0, x.c0.c1, x.c1.c0, x.c1.c1]
@[simp] theorem ofExt2_c0 (a : GoldilocksExt2) : (ofExt2 a).c0 = a := by rfl
@[simp] theorem ofExt2_c1 (a : GoldilocksExt2) : (ofExt2 a).c1 = CommRingOps.zero := by rfl
@[simp] theorem embedBase_c0_c0 (a : Goldilocks) : (embedBase a).c0.c0 = a := GoldilocksExt2.ofBase_c0 a
theorem embedBase_zero : embedBase Goldilocks.zero = zero := by
  unfold embedBase
  rw [GoldilocksExt2.ofBase_zero]
  rfl

theorem embedBase_one : embedBase Goldilocks.one = one := by
  unfold embedBase
  rw [GoldilocksExt2.ofBase_one]
  rfl

theorem ofExt2_injective {a b : GoldilocksExt2} (h : ofExt2 a = ofExt2 b) : a = b := by
  exact congrArg c0 h

theorem ofExt2_add (a b : GoldilocksExt2) :
    ofExt2 (CommRingOps.add a b) = CommRingOps.add (ofExt2 a) (ofExt2 b) := by
  exact ext rfl (LawfulCommRing.add_zero _).symm

theorem ofExt2_sub (a b : GoldilocksExt2) :
    ofExt2 (CommRingOps.sub a b) = CommRingOps.sub (ofExt2 a) (ofExt2 b) := by
  exact ext rfl (LawfulCommRing.sub_self _).symm

theorem ofExt2_mul (a b : GoldilocksExt2) :
    ofExt2 (CommRingOps.mul a b) = CommRingOps.mul (ofExt2 a) (ofExt2 b) := by
  apply ext
  · change CommRingOps.mul a b =
      CommRingOps.add (CommRingOps.mul a b)
        (CommRingOps.mul nonResidue (CommRingOps.mul CommRingOps.zero CommRingOps.zero))
    rw [LawfulCommRing.mul_zero, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  · change CommRingOps.zero =
      CommRingOps.add (CommRingOps.mul a CommRingOps.zero) (CommRingOps.mul CommRingOps.zero b)
    rw [LawfulCommRing.mul_zero, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]

theorem embedBase_injective {a b : Goldilocks} (h : embedBase a = embedBase b) : a = b := by
  exact GoldilocksExt2.ofBase_injective (ofExt2_injective h)

theorem embedBase_add (a b : Goldilocks) :
    embedBase (CommRingOps.add a b) = CommRingOps.add (embedBase a) (embedBase b) := by
  unfold embedBase
  rw [GoldilocksExt2.ofBase_add, ofExt2_add]

theorem embedBase_sub (a b : Goldilocks) :
    embedBase (CommRingOps.sub a b) = CommRingOps.sub (embedBase a) (embedBase b) := by
  unfold embedBase
  rw [GoldilocksExt2.ofBase_sub, ofExt2_sub]

theorem embedBase_mul (a b : Goldilocks) :
    embedBase (CommRingOps.mul a b) = CommRingOps.mul (embedBase a) (embedBase b) := by
  unfold embedBase
  rw [GoldilocksExt2.ofBase_mul, ofExt2_mul]

/-- Base-field membership predicate `z ∈ F_p ↪ F_{p^4}`. -/
def isBase (z : GoldilocksExt4) : Bool :=
  (z.c0.c1 == Goldilocks.zero) && (z.c1 == GoldilocksExt2.zero)

theorem isBase_embedBase (a : Goldilocks) : isBase (embedBase a) = true := by
  simp only [isBase, embedBase, ofExt2, QuarticGoldilocks.ofExt2, c0, c1, GoldilocksExt2.ofBase_c1, Goldilocks.ring_zero, GoldilocksExt2.ring_zero, beq_self_eq_true, Bool.and_true]

theorem eq_embedBase_of_isBase {z : GoldilocksExt4} (h : isBase z = true) :
    z = embedBase z.c0.c0 := by
  unfold isBase at h
  rcases Bool.and_eq_true_iff.mp h with ⟨h01, h1⟩
  apply ext
  · apply GoldilocksExt2.ext
    · exact (GoldilocksExt2.ofBase_c0 _).symm
    · simpa only [embedBase, ofExt2, QuarticGoldilocks.ofExt2, c0, GoldilocksExt2.ofBase_c1, Goldilocks.ring_zero] using (eq_of_beq h01)
  · exact eq_of_beq h1

/-- Canonical 32-byte big-endian limb encoding (`4 × 8 = 32` bytes). -/
def encodeBytes32 (z : GoldilocksExt4) : List UInt8 :=
  be 8 z.c0.c0.val ++ (be 8 z.c0.c1.val ++ (be 8 z.c1.c0.val ++ be 8 z.c1.c1.val))

theorem encodeBytes32_length (z : GoldilocksExt4) : (encodeBytes32 z).length = 32 := by
  simp [encodeBytes32, length_be]

theorem encodeBytes32_injective {x y : GoldilocksExt4}
    (h : encodeBytes32 x = encodeBytes32 y) : x = y := by
  have hb : goldilocksPrime < 256 ^ 8 := by decide
  unfold encodeBytes32 at h
  obtain ⟨h00, r1⟩ := List.append_inj h (by simp [length_be])
  obtain ⟨h01, r2⟩ := List.append_inj r1 (by simp [length_be])
  obtain ⟨h10, h11⟩ := List.append_inj r2 (by simp [length_be])
  have e00 := be_injective (Nat.lt_trans x.c0.c0.isLt hb) (Nat.lt_trans y.c0.c0.isLt hb) h00
  have e01 := be_injective (Nat.lt_trans x.c0.c1.isLt hb) (Nat.lt_trans y.c0.c1.isLt hb) h01
  have e10 := be_injective (Nat.lt_trans x.c1.c0.isLt hb) (Nat.lt_trans y.c1.c0.isLt hb) h10
  have e11 := be_injective (Nat.lt_trans x.c1.c1.isLt hb) (Nat.lt_trans y.c1.c1.isLt hb) h11
  exact ext (GoldilocksExt2.ext (Goldilocks.ext e00) (Goldilocks.ext e01))
    (GoldilocksExt2.ext (Goldilocks.ext e10) (Goldilocks.ext e11))

/-- Checked canonical 32-byte decoder rejecting non-canonical (`≥ p`) 64-bit limbs. -/
def decodeBytes32 (bs : List UInt8) : Option GoldilocksExt4 :=
  if bs.length = 32 then
    let v00 := ofBE (bs.take 8)
    let v01 := ofBE ((bs.drop 8).take 8)
    let v10 := ofBE ((bs.drop 16).take 8)
    let v11 := ofBE ((bs.drop 24).take 8)
    if h00 : v00 < goldilocksPrime then
      if h01 : v01 < goldilocksPrime then
        if h10 : v10 < goldilocksPrime then
          if h11 : v11 < goldilocksPrime then
            some ⟨⟨⟨v00, h00⟩, ⟨v01, h01⟩⟩, ⟨⟨v10, h10⟩, ⟨v11, h11⟩⟩⟩
          else none
        else none
      else none
    else none
  else none

theorem decodeBytes32_encodeBytes32 (z : GoldilocksExt4) :
    decodeBytes32 (encodeBytes32 z) = some z := by
  have hb : goldilocksPrime < 256 ^ 8 := by decide
  have hLen := encodeBytes32_length z
  unfold decodeBytes32
  simp only [hLen, ↓reduceIte]
  have t00 : (encodeBytes32 z).take 8 = be 8 z.c0.c0.val := by
    unfold encodeBytes32
    rw [List.take_left' (length_be 8 z.c0.c0.val)]
  have d8 : (encodeBytes32 z).drop 8 =
      be 8 z.c0.c1.val ++ (be 8 z.c1.c0.val ++ be 8 z.c1.c1.val) := by
    unfold encodeBytes32
    rw [List.drop_left' (length_be 8 z.c0.c0.val)]
  have t01 : ((encodeBytes32 z).drop 8).take 8 = be 8 z.c0.c1.val := by
    rw [d8, List.take_left' (length_be 8 z.c0.c1.val)]
  have d16 : (encodeBytes32 z).drop 16 = be 8 z.c1.c0.val ++ be 8 z.c1.c1.val := by
    have h16 : (16 : Nat) = 8 + 8 := rfl
    rw [h16, ← List.drop_drop, d8, List.drop_left' (length_be 8 z.c0.c1.val)]
  have t10 : ((encodeBytes32 z).drop 16).take 8 = be 8 z.c1.c0.val := by
    rw [d16, List.take_left' (length_be 8 z.c1.c0.val)]
  have d24 : (encodeBytes32 z).drop 24 = be 8 z.c1.c1.val := by
    have h24 : (24 : Nat) = 16 + 8 := rfl
    rw [h24, ← List.drop_drop, d16, List.drop_left' (length_be 8 z.c1.c0.val)]
  have t11 : ((encodeBytes32 z).drop 24).take 8 = be 8 z.c1.c1.val := by
    rw [d24, List.take_of_length_le (Nat.le_of_eq (length_be 8 z.c1.c1.val))]
  rw [t00, t01, t10, t11,
      ofBE_be (Nat.lt_trans z.c0.c0.isLt hb),
      ofBE_be (Nat.lt_trans z.c0.c1.isLt hb),
      ofBE_be (Nat.lt_trans z.c1.c0.isLt hb),
      ofBE_be (Nat.lt_trans z.c1.c1.isLt hb)]
  simp only [z.c0.c0.isLt, z.c0.c1.isLt, z.c1.c0.isLt, z.c1.c1.isLt, ↓reduceDIte]


theorem mul_inv_cancel {z : GoldilocksExt4} (hz : z ≠ zero) : CommRingOps.mul z (inv z) = CommRingOps.one := QuarticGoldilocks.mul_inv_cancel hz
theorem nonResidue_not_square (z : GoldilocksExt2) : CommRingOps.mul z z ≠ nonResidue := QuarticGoldilocks.uBasis_not_square z
theorem zero_eq_ringZero : zero = CommRingOps.zero := by rfl
theorem one_eq_ringOne : one = CommRingOps.one := by rfl
end GoldilocksExt4
end GoldilocksField

abbrev GoldilocksExt4 := QuarticGoldilocks
namespace GoldilocksExt4
abbrev c0 (z : GoldilocksExt4) := QuarticGoldilocks.c0 z
abbrev c1 (z : GoldilocksExt4) := QuarticGoldilocks.c1 z
abbrev mk := @GoldilocksField.GoldilocksExt4.mk
abbrev ext := @GoldilocksField.GoldilocksExt4.ext
abbrev nonResidue := @GoldilocksField.GoldilocksExt4.nonResidue
abbrev zero := @GoldilocksField.GoldilocksExt4.zero
abbrev one := @GoldilocksField.GoldilocksExt4.one
abbrev vBasis := @GoldilocksField.GoldilocksExt4.vBasis
abbrev ofExt2 := @GoldilocksField.GoldilocksExt4.ofExt2
abbrev embedBase := @GoldilocksField.GoldilocksExt4.embedBase
abbrev embedBase_zero := GoldilocksField.GoldilocksExt4.embedBase_zero
abbrev embedBase_one := GoldilocksField.GoldilocksExt4.embedBase_one
abbrev add := @GoldilocksField.GoldilocksExt4.add
abbrev neg := @GoldilocksField.GoldilocksExt4.neg
abbrev sub := @GoldilocksField.GoldilocksExt4.sub
abbrev mul := @GoldilocksField.GoldilocksExt4.mul
abbrev norm := @GoldilocksField.GoldilocksExt4.norm
abbrev inv := @GoldilocksField.GoldilocksExt4.inv
abbrev ofLimbs := @GoldilocksField.GoldilocksExt4.ofLimbs
abbrev toLimbs := @GoldilocksField.GoldilocksExt4.toLimbs
abbrev ofExt2_c0 := @GoldilocksField.GoldilocksExt4.ofExt2_c0
abbrev ofExt2_c1 := @GoldilocksField.GoldilocksExt4.ofExt2_c1
abbrev embedBase_c0_c0 := @GoldilocksField.GoldilocksExt4.embedBase_c0_c0
abbrev ofExt2_injective := @GoldilocksField.GoldilocksExt4.ofExt2_injective
abbrev ofExt2_add := @GoldilocksField.GoldilocksExt4.ofExt2_add
abbrev ofExt2_sub := @GoldilocksField.GoldilocksExt4.ofExt2_sub
abbrev ofExt2_mul := @GoldilocksField.GoldilocksExt4.ofExt2_mul
abbrev embedBase_injective := @GoldilocksField.GoldilocksExt4.embedBase_injective
abbrev embedBase_add := @GoldilocksField.GoldilocksExt4.embedBase_add
abbrev embedBase_sub := @GoldilocksField.GoldilocksExt4.embedBase_sub
abbrev embedBase_mul := @GoldilocksField.GoldilocksExt4.embedBase_mul
abbrev isBase := @GoldilocksField.GoldilocksExt4.isBase
abbrev isBase_embedBase := @GoldilocksField.GoldilocksExt4.isBase_embedBase
abbrev eq_embedBase_of_isBase := @GoldilocksField.GoldilocksExt4.eq_embedBase_of_isBase
abbrev encodeBytes32 := @GoldilocksField.GoldilocksExt4.encodeBytes32
abbrev encodeBytes32_length := @GoldilocksField.GoldilocksExt4.encodeBytes32_length
abbrev encodeBytes32_injective := @GoldilocksField.GoldilocksExt4.encodeBytes32_injective
abbrev decodeBytes32 := @GoldilocksField.GoldilocksExt4.decodeBytes32
abbrev decodeBytes32_encodeBytes32 := @GoldilocksField.GoldilocksExt4.decodeBytes32_encodeBytes32
abbrev mul_inv_cancel := @GoldilocksField.GoldilocksExt4.mul_inv_cancel
abbrev nonResidue_not_square := @GoldilocksField.GoldilocksExt4.nonResidue_not_square
abbrev uBasis_not_square := @GoldilocksField.GoldilocksExt4.uBasis_not_square
abbrev norm_ne_zero := @GoldilocksField.GoldilocksExt4.norm_ne_zero
abbrev zero_eq_ringZero := @GoldilocksField.GoldilocksExt4.zero_eq_ringZero
abbrev one_eq_ringOne := @GoldilocksField.GoldilocksExt4.one_eq_ringOne
end GoldilocksExt4

namespace Aggregation
abbrev GoldilocksExt4 := QuarticGoldilocks
namespace GoldilocksExt4
abbrev c0 (z : GoldilocksExt4) := QuarticGoldilocks.c0 z
abbrev c1 (z : GoldilocksExt4) := QuarticGoldilocks.c1 z
abbrev mk := @GoldilocksField.GoldilocksExt4.mk
abbrev ext := @GoldilocksField.GoldilocksExt4.ext
abbrev nonResidue := @GoldilocksField.GoldilocksExt4.nonResidue
abbrev zero := @GoldilocksField.GoldilocksExt4.zero
abbrev one := @GoldilocksField.GoldilocksExt4.one
abbrev vBasis := @GoldilocksField.GoldilocksExt4.vBasis
abbrev ofExt2 := @GoldilocksField.GoldilocksExt4.ofExt2
abbrev embedBase := @GoldilocksField.GoldilocksExt4.embedBase
abbrev embedBase_zero := GoldilocksField.GoldilocksExt4.embedBase_zero
abbrev embedBase_one := GoldilocksField.GoldilocksExt4.embedBase_one
abbrev add := @GoldilocksField.GoldilocksExt4.add
abbrev neg := @GoldilocksField.GoldilocksExt4.neg
abbrev sub := @GoldilocksField.GoldilocksExt4.sub
abbrev mul := @GoldilocksField.GoldilocksExt4.mul
abbrev norm := @GoldilocksField.GoldilocksExt4.norm
abbrev inv := @GoldilocksField.GoldilocksExt4.inv
abbrev ofLimbs := @GoldilocksField.GoldilocksExt4.ofLimbs
abbrev toLimbs := @GoldilocksField.GoldilocksExt4.toLimbs
abbrev ofExt2_c0 := @GoldilocksField.GoldilocksExt4.ofExt2_c0
abbrev ofExt2_c1 := @GoldilocksField.GoldilocksExt4.ofExt2_c1
abbrev embedBase_c0_c0 := @GoldilocksField.GoldilocksExt4.embedBase_c0_c0
abbrev ofExt2_injective := @GoldilocksField.GoldilocksExt4.ofExt2_injective
abbrev ofExt2_add := @GoldilocksField.GoldilocksExt4.ofExt2_add
abbrev ofExt2_sub := @GoldilocksField.GoldilocksExt4.ofExt2_sub
abbrev ofExt2_mul := @GoldilocksField.GoldilocksExt4.ofExt2_mul
abbrev embedBase_injective := @GoldilocksField.GoldilocksExt4.embedBase_injective
abbrev embedBase_add := @GoldilocksField.GoldilocksExt4.embedBase_add
abbrev embedBase_sub := @GoldilocksField.GoldilocksExt4.embedBase_sub
abbrev embedBase_mul := @GoldilocksField.GoldilocksExt4.embedBase_mul
abbrev isBase := @GoldilocksField.GoldilocksExt4.isBase
abbrev isBase_embedBase := @GoldilocksField.GoldilocksExt4.isBase_embedBase
abbrev eq_embedBase_of_isBase := @GoldilocksField.GoldilocksExt4.eq_embedBase_of_isBase
abbrev encodeBytes32 := @GoldilocksField.GoldilocksExt4.encodeBytes32
abbrev encodeBytes32_length := @GoldilocksField.GoldilocksExt4.encodeBytes32_length
abbrev encodeBytes32_injective := @GoldilocksField.GoldilocksExt4.encodeBytes32_injective
abbrev decodeBytes32 := @GoldilocksField.GoldilocksExt4.decodeBytes32
abbrev decodeBytes32_encodeBytes32 := @GoldilocksField.GoldilocksExt4.decodeBytes32_encodeBytes32
abbrev mul_inv_cancel := @GoldilocksField.GoldilocksExt4.mul_inv_cancel
abbrev nonResidue_not_square := @GoldilocksField.GoldilocksExt4.nonResidue_not_square
abbrev uBasis_not_square := @GoldilocksField.GoldilocksExt4.uBasis_not_square
abbrev norm_ne_zero := @GoldilocksField.GoldilocksExt4.norm_ne_zero
abbrev zero_eq_ringZero := @GoldilocksField.GoldilocksExt4.zero_eq_ringZero
abbrev one_eq_ringOne := @GoldilocksField.GoldilocksExt4.one_eq_ringOne
end GoldilocksExt4
end Aggregation
/-! ### Canonical 32-byte little-endian encoding (`field.rs:to_le_bytes`, `from_le_bytes_canonical`) -/

/-- Byte `(n / d) mod 256`; `d` ranges over `256^i`. -/
def leByte (n d : Nat) : UInt8 := UInt8.ofNatLT (n / d % 256) (Nat.mod_lt _ (by decide))

theorem leByte_toNat (n d : Nat) : (leByte n d).toNat = n / d % 256 := by rfl

/-- Value of eight little-endian bytes. -/
def le64Value (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : Nat :=
  b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat +
    4294967296 * b4.toNat + 1099511627776 * b5.toNat + 281474976710656 * b6.toNat +
    72057594037927936 * b7.toNat

private theorem le64_recompose (n : Nat) (h : n < 18446744073709551616) :
    n / 1 % 256 + 256 * (n / 256 % 256) + 65536 * (n / 65536 % 256) +
      16777216 * (n / 16777216 % 256) + 4294967296 * (n / 4294967296 % 256) +
      1099511627776 * (n / 1099511627776 % 256) +
      281474976710656 * (n / 281474976710656 % 256) +
      72057594037927936 * (n / 72057594037927936 % 256) = n := by
  omega

private theorem le64_digit (v0 v1 v2 v3 v4 v5 v6 v7 : Nat)
    (h0 : v0 < 256) (h1 : v1 < 256) (h2 : v2 < 256) (h3 : v3 < 256)
    (h4 : v4 < 256) (h5 : v5 < 256) (h6 : v6 < 256) (h7 : v7 < 256)
    (N : Nat)
    (hN : N = v0 + 256 * v1 + 65536 * v2 + 16777216 * v3 + 4294967296 * v4 +
      1099511627776 * v5 + 281474976710656 * v6 + 72057594037927936 * v7) :
    N / 1 % 256 = v0 ∧ N / 256 % 256 = v1 ∧ N / 65536 % 256 = v2 ∧
    N / 16777216 % 256 = v3 ∧ N / 4294967296 % 256 = v4 ∧
    N / 1099511627776 % 256 = v5 ∧ N / 281474976710656 % 256 = v6 ∧
    N / 72057594037927936 % 256 = v7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- `field.rs:Goldilocks::to_le_bytes`: eight little-endian bytes of the canonical value. -/
def encodeGoldilocksLe8 (a : Goldilocks) : List UInt8 :=
  [leByte a.val 1, leByte a.val 256, leByte a.val 65536, leByte a.val 16777216,
   leByte a.val 4294967296, leByte a.val 1099511627776, leByte a.val 281474976710656,
   leByte a.val 72057594037927936]

/-- `field.rs:Goldilocks::from_le_bytes_canonical` on the first eight bytes: rejects a limb
    `≥ p` and returns the unconsumed tail. -/
def decodeGoldilocksLe8 : List UInt8 → Option (Goldilocks × List UInt8)
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
    if h : le64Value b0 b1 b2 b3 b4 b5 b6 b7 < goldilocksPrime then
      some (⟨le64Value b0 b1 b2 b3 b4 b5 b6 b7, h⟩, rest)
    else none
  | _ => none

theorem decodeGoldilocksLe8_encode (a : Goldilocks) (rest : List UInt8) :
    decodeGoldilocksLe8 (encodeGoldilocksLe8 a ++ rest) = some (a, rest) := by
  have hv : le64Value (leByte a.val 1) (leByte a.val 256) (leByte a.val 65536)
      (leByte a.val 16777216) (leByte a.val 4294967296) (leByte a.val 1099511627776)
      (leByte a.val 281474976710656) (leByte a.val 72057594037927936) = a.val :=
    le64_recompose a.val (Goldilocks.val_lt_two_pow_64 a)
  have hlt : le64Value (leByte a.val 1) (leByte a.val 256) (leByte a.val 65536)
      (leByte a.val 16777216) (leByte a.val 4294967296) (leByte a.val 1099511627776)
      (leByte a.val 281474976710656) (leByte a.val 72057594037927936) < goldilocksPrime := by
    rw [hv]; exact a.isLt
  show decodeGoldilocksLe8
      (leByte a.val 1 :: leByte a.val 256 :: leByte a.val 65536 :: leByte a.val 16777216 ::
        leByte a.val 4294967296 :: leByte a.val 1099511627776 ::
        leByte a.val 281474976710656 :: leByte a.val 72057594037927936 :: rest) = some (a, rest)
  rw [decodeGoldilocksLe8, dite_eq_left hlt]
  exact congrArg (fun g => some (g, rest)) (Goldilocks.ext hv)

theorem decodeGoldilocksLe8_canonical :
    ∀ (bs : List UInt8) (a : Goldilocks) (rest : List UInt8),
      decodeGoldilocksLe8 bs = some (a, rest) → bs = encodeGoldilocksLe8 a ++ rest
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: r, a, rest, h => by
    rw [decodeGoldilocksLe8] at h
    by_cases hlt : le64Value b0 b1 b2 b3 b4 b5 b6 b7 < goldilocksPrime
    · rw [dite_eq_left hlt] at h
      obtain ⟨ha, hr⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ :=
        le64_digit b0.toNat b1.toNat b2.toNat b3.toNat b4.toNat b5.toNat b6.toNat b7.toNat
          (UInt8.toNat_lt b0) (UInt8.toNat_lt b1) (UInt8.toNat_lt b2) (UInt8.toNat_lt b3)
          (UInt8.toNat_lt b4) (UInt8.toNat_lt b5) (UInt8.toNat_lt b6) (UInt8.toNat_lt b7)
          (le64Value b0 b1 b2 b3 b4 b5 b6 b7) rfl
      rw [← ha, ← hr]
      show b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: r =
        leByte (le64Value b0 b1 b2 b3 b4 b5 b6 b7) 1 ::
        leByte (le64Value b0 b1 b2 b3 b4 b5 b6 b7) 256 ::
        leByte (le64Value b0 b1 b2 b3 b4 b5 b6 b7) 65536 ::
        leByte (le64Value b0 b1 b2 b3 b4 b5 b6 b7) 16777216 ::
        leByte (le64Value b0 b1 b2 b3 b4 b5 b6 b7) 4294967296 ::
        leByte (le64Value b0 b1 b2 b3 b4 b5 b6 b7) 1099511627776 ::
        leByte (le64Value b0 b1 b2 b3 b4 b5 b6 b7) 281474976710656 ::
        leByte (le64Value b0 b1 b2 b3 b4 b5 b6 b7) 72057594037927936 :: r
      rw [UInt8.toNat_inj.mp ((leByte_toNat _ 1).trans e0),
        UInt8.toNat_inj.mp ((leByte_toNat _ 256).trans e1),
        UInt8.toNat_inj.mp ((leByte_toNat _ 65536).trans e2),
        UInt8.toNat_inj.mp ((leByte_toNat _ 16777216).trans e3),
        UInt8.toNat_inj.mp ((leByte_toNat _ 4294967296).trans e4),
        UInt8.toNat_inj.mp ((leByte_toNat _ 1099511627776).trans e5),
        UInt8.toNat_inj.mp ((leByte_toNat _ 281474976710656).trans e6),
        UInt8.toNat_inj.mp ((leByte_toNat _ 72057594037927936).trans e7)]
    · rw [dite_eq_right hlt] at h; cases h
  | [], _, _, h => by cases h
  | [_], _, _, h => by cases h
  | [_, _], _, _, h => by cases h
  | [_, _, _], _, _, h => by cases h
  | [_, _, _, _], _, _, h => by cases h
  | [_, _, _, _, _], _, _, h => by cases h
  | [_, _, _, _, _, _], _, _, h => by cases h
  | [_, _, _, _, _, _, _], _, _, h => by cases h

/-- `field.rs:GoldilocksExt4::to_le_bytes`: the four limbs `[c0.c0, c0.c1, c1.c0, c1.c1]`, eight
    little-endian bytes each. -/
def encodeExt4Bytes32 (x : GoldilocksExt4) : List UInt8 :=
  encodeGoldilocksLe8 x.c0.c0 ++ (encodeGoldilocksLe8 x.c0.c1 ++
    (encodeGoldilocksLe8 x.c1.c0 ++ (encodeGoldilocksLe8 x.c1.c1 ++ [])))

/-- `field.rs:GoldilocksExt4::from_le_bytes_canonical`: accepts exactly 32 bytes whose four
    limbs are all `< p`. -/
def decodeExt4Bytes32 (bs : List UInt8) : Option GoldilocksExt4 :=
  match decodeGoldilocksLe8 bs with
  | none => none
  | some (l0, r0) =>
    match decodeGoldilocksLe8 r0 with
    | none => none
    | some (l1, r1) =>
      match decodeGoldilocksLe8 r1 with
      | none => none
      | some (l2, r2) =>
        match decodeGoldilocksLe8 r2 with
        | some (l3, []) => some (GoldilocksExt4.ofLimbs l0 l1 l2 l3)
        | _ => none

theorem encodeExt4Bytes32_length (x : GoldilocksExt4) : (encodeExt4Bytes32 x).length = 32 := by
  rfl

/-- **Canonical 32-byte roundtrip.** -/
theorem decodeExt4Bytes32_encode (x : GoldilocksExt4) :
    decodeExt4Bytes32 (encodeExt4Bytes32 x) = some x := by
  obtain ⟨⟨a0, a1⟩, ⟨a2, a3⟩⟩ := x
  simp only [decodeExt4Bytes32, encodeExt4Bytes32, decodeGoldilocksLe8_encode,
    GoldilocksExt4.ofLimbs, GoldilocksField.GoldilocksExt4.ofLimbs]

/-- **Non-malleability.** Every accepted byte string is the canonical encoding of the decoded
    element; in particular a string with a limb `≥ p`, or of length other than 32, is rejected. -/
theorem decodeExt4Bytes32_canonical (bs : List UInt8) (x : GoldilocksExt4)
    (h : decodeExt4Bytes32 bs = some x) : encodeExt4Bytes32 x = bs := by
  unfold decodeExt4Bytes32 at h
  cases h0 : decodeGoldilocksLe8 bs with
  | none => rw [h0] at h; cases h
  | some p0 =>
    obtain ⟨l0, r0⟩ := p0
    rw [h0] at h
    dsimp only at h
    cases h1 : decodeGoldilocksLe8 r0 with
    | none => rw [h1] at h; cases h
    | some p1 =>
      obtain ⟨l1, r1⟩ := p1
      rw [h1] at h
      dsimp only at h
      cases h2 : decodeGoldilocksLe8 r1 with
      | none => rw [h2] at h; cases h
      | some p2 =>
        obtain ⟨l2, r2⟩ := p2
        rw [h2] at h
        dsimp only at h
        cases h3 : decodeGoldilocksLe8 r2 with
        | none => rw [h3] at h; cases h
        | some p3 =>
          obtain ⟨l3, r3⟩ := p3
          rw [h3] at h
          cases r3 with
          | cons _ _ => cases h
          | nil =>
            have hx : GoldilocksExt4.ofLimbs l0 l1 l2 l3 = x := Option.some.inj h
            rw [← hx, decodeGoldilocksLe8_canonical bs l0 r0 h0,
              decodeGoldilocksLe8_canonical r0 l1 r1 h1,
              decodeGoldilocksLe8_canonical r1 l2 r2 h2,
              decodeGoldilocksLe8_canonical r2 l3 [] h3]
            rfl

/-- Two byte strings that decode to the same element are equal. -/
theorem decodeExt4Bytes32_injective (bs bs' : List UInt8) (x : GoldilocksExt4)
    (h : decodeExt4Bytes32 bs = some x) (h' : decodeExt4Bytes32 bs' = some x) : bs = bs' :=
  (decodeExt4Bytes32_canonical bs x h).symm.trans (decodeExt4Bytes32_canonical bs' x h')

end Qsag

namespace Qsag
open CommRingOps
namespace QuarticGoldilocks

def baseEmbeddingHom : RingHom Goldilocks QuarticGoldilocks where
  toFun := GoldilocksField.GoldilocksExt4.embedBase
  map_zero := by rw [Goldilocks.ring_zero]; exact GoldilocksField.GoldilocksExt4.embedBase_zero
  map_one := by rw [Goldilocks.ring_one]; exact GoldilocksField.GoldilocksExt4.embedBase_one
  map_add := GoldilocksField.GoldilocksExt4.embedBase_add
  map_mul := GoldilocksField.GoldilocksExt4.embedBase_mul

theorem natCast_eq (k : Nat) : (CRing.natCast k : QuarticGoldilocks) =
    ⟨⟨(CRing.natCast k : Goldilocks), CommRingOps.zero⟩, CommRingOps.zero⟩ := by
  rw [← baseEmbeddingHom.map_natCast]
  apply QuarticGoldilocks.ext
  · apply GoldilocksExt2.ext
    · exact GoldilocksExt2.ofBase_c0 _
    · exact GoldilocksExt2.ofBase_c1 _
  · rfl

/-- `1, …, p - 1` are nonzero in `QuarticGoldilocks`. -/
theorem natCast_ne_zero (k : Nat) (h1 : 1 ≤ k) (hk : k < goldilocksPrime) :
    (CRing.natCast k : QuarticGoldilocks) ≠ CommRingOps.zero := fun e => by
  rw [natCast_eq] at e
  exact Goldilocks.natCast_ne_zero k h1 hk
    (by
      have h := congrArg (fun q : QuarticGoldilocks => q.c0.c0) e
      change (CRing.natCast k : Goldilocks) = GoldilocksExt2.zero.c0 at h
      simpa only [GoldilocksExt2.zero_c0, Goldilocks.ring_zero] using h)

end QuarticGoldilocks


end Qsag
