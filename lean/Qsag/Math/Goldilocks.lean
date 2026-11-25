module
/- The certified quadratic extension of the canonical Goldilocks base field. -/
public import Qsag.Math.GoldilocksBase
import Qsag.Tactic.AssuranceKit
public section
namespace Qsag
set_option autoImplicit false
/-! ## 6. Quadratic Extension `GoldilocksExt2` ($\mathbb{F}_{p^2} = \mathbb{F}_p[u]/(u^2 - 7)$) -/

structure GoldilocksExt2 where
  c0 : Goldilocks
  c1 : Goldilocks
  deriving Repr

namespace GoldilocksExt2

@[expose, instance_reducible] def _root_.Qsag.instDecidableEqGoldilocksExt2 (a b : GoldilocksExt2) : Decidable (a = b) :=
  if h0 : a.c0 = b.c0 then
    if h1 : a.c1 = b.c1 then isTrue (by cases a; cases b; cases h0; cases h1; rfl)
    else isFalse (fun h => h1 (congrArg GoldilocksExt2.c1 h))
  else isFalse (fun h => h0 (congrArg GoldilocksExt2.c0 h))
attribute [instance] _root_.Qsag.instDecidableEqGoldilocksExt2

@[expose] def nonResidue : Goldilocks := ⟨7, by decide⟩

theorem ext {x y : GoldilocksExt2} (h0 : x.c0 = y.c0) (h1 : x.c1 = y.c1) : x = y := by
  cases x; cases y; simp only at h0 h1; subst h0 h1; rfl

@[expose] def ofBase (a : Goldilocks) : GoldilocksExt2 := ⟨a, CommRingOps.zero⟩
@[expose] def zero : GoldilocksExt2 := ⟨CommRingOps.zero, CommRingOps.zero⟩
@[expose] def one : GoldilocksExt2 := ⟨CommRingOps.one, CommRingOps.zero⟩
@[expose] def uBasis : GoldilocksExt2 := ⟨CommRingOps.zero, CommRingOps.one⟩

instance : Inhabited GoldilocksExt2 := ⟨zero⟩

@[simp] theorem ofBase_c0 (a : Goldilocks) : (ofBase a).c0 = a := by unfold ofBase; rfl
@[simp] theorem ofBase_c1 (a : Goldilocks) : (ofBase a).c1 = CommRingOps.zero := by unfold ofBase; rfl

@[expose] def add (x y : GoldilocksExt2) : GoldilocksExt2 :=
  ⟨CommRingOps.add x.c0 y.c0, CommRingOps.add x.c1 y.c1⟩

@[expose] def neg (x : GoldilocksExt2) : GoldilocksExt2 :=
  ⟨CommRingOps.neg x.c0, CommRingOps.neg x.c1⟩

@[expose] def sub (x y : GoldilocksExt2) : GoldilocksExt2 :=
  ⟨CommRingOps.sub x.c0 y.c0, CommRingOps.sub x.c1 y.c1⟩

@[expose] def mul (x y : GoldilocksExt2) : GoldilocksExt2 :=
  ⟨CommRingOps.add (CommRingOps.mul x.c0 y.c0)
      (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1)),
   CommRingOps.add (CommRingOps.mul x.c0 y.c1) (CommRingOps.mul x.c1 y.c0)⟩

instance : CommRingOps GoldilocksExt2 where
  zero := zero
  one := one
  add := add
  mul := mul
  neg := neg
  sub := sub

instance : LawfulCommRing GoldilocksExt2 where
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
    · change CommRingOps.add (CommRingOps.mul x.c0 y.c0)
          (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1)) =
        CommRingOps.add (CommRingOps.mul y.c0 x.c0)
          (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 x.c1))
      rw [LawfulCommRing.mul_comm x.c0 y.c0, LawfulCommRing.mul_comm x.c1 y.c1]
    · change CommRingOps.add (CommRingOps.mul x.c0 y.c1) (CommRingOps.mul x.c1 y.c0) =
        CommRingOps.add (CommRingOps.mul y.c0 x.c1) (CommRingOps.mul y.c1 x.c0)
      rw [LawfulCommRing.mul_comm x.c0 y.c1, LawfulCommRing.mul_comm x.c1 y.c0,
          LawfulCommRing.add_comm]
  one_mul x := by
    apply ext
    · change CommRingOps.add (CommRingOps.mul CommRingOps.one x.c0)
          (CommRingOps.mul nonResidue (CommRingOps.mul CommRingOps.zero x.c1)) = x.c0
      rw [LawfulCommRing.one_mul, LawfulCommRing.zero_mul, LawfulCommRing.mul_zero,
          LawfulCommRing.add_zero]
    · change CommRingOps.add (CommRingOps.mul CommRingOps.one x.c1)
          (CommRingOps.mul CommRingOps.zero x.c0) = x.c1
      rw [LawfulCommRing.one_mul, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
  mul_one x := by
    apply ext
    · change CommRingOps.add (CommRingOps.mul x.c0 CommRingOps.one)
          (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 CommRingOps.zero)) = x.c0
      rw [LawfulCommRing.mul_one, LawfulCommRing.mul_zero, LawfulCommRing.mul_zero,
          LawfulCommRing.add_zero]
    · change CommRingOps.add (CommRingOps.mul x.c0 CommRingOps.zero)
          (CommRingOps.mul x.c1 CommRingOps.one) = x.c1
      rw [LawfulCommRing.mul_zero, LawfulCommRing.mul_one, LawfulCommRing.zero_add]
  left_distrib x y z := by
    apply ext
    · change CommRingOps.add (CommRingOps.mul x.c0 (CommRingOps.add y.c0 z.c0))
          (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 (CommRingOps.add y.c1 z.c1))) = _
      rw [LawfulCommRing.left_distrib, LawfulCommRing.left_distrib, LawfulCommRing.left_distrib,
          LawfulCommRing.add_add_add_comm]
      rfl
    · change CommRingOps.add (CommRingOps.mul x.c0 (CommRingOps.add y.c1 z.c1))
          (CommRingOps.mul x.c1 (CommRingOps.add y.c0 z.c0)) = _
      rw [LawfulCommRing.left_distrib, LawfulCommRing.left_distrib,
          LawfulCommRing.add_add_add_comm]
      rfl
  right_distrib x y z := by
    apply ext
    · change CommRingOps.add (CommRingOps.mul (CommRingOps.add x.c0 y.c0) z.c0)
          (CommRingOps.mul nonResidue (CommRingOps.mul (CommRingOps.add x.c1 y.c1) z.c1)) = _
      rw [LawfulCommRing.right_distrib, LawfulCommRing.right_distrib, LawfulCommRing.left_distrib,
          LawfulCommRing.add_add_add_comm]
      rfl
    · change CommRingOps.add (CommRingOps.mul (CommRingOps.add x.c0 y.c0) z.c1)
          (CommRingOps.mul (CommRingOps.add x.c1 y.c1) z.c0) = _
      rw [LawfulCommRing.right_distrib, LawfulCommRing.right_distrib,
          LawfulCommRing.add_add_add_comm]
      rfl
  mul_assoc x y z := by
    apply ext
    · change CommRingOps.add
          (CommRingOps.mul
            (CommRingOps.add (CommRingOps.mul x.c0 y.c0)
              (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1))) z.c0)
          (CommRingOps.mul nonResidue
            (CommRingOps.mul
              (CommRingOps.add (CommRingOps.mul x.c0 y.c1) (CommRingOps.mul x.c1 y.c0)) z.c1)) =
        CommRingOps.add
          (CommRingOps.mul x.c0
            (CommRingOps.add (CommRingOps.mul y.c0 z.c0)
              (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 z.c1))))
          (CommRingOps.mul nonResidue
            (CommRingOps.mul x.c1
              (CommRingOps.add (CommRingOps.mul y.c0 z.c1) (CommRingOps.mul y.c1 z.c0))))
      rw [LawfulCommRing.right_distrib, LawfulCommRing.right_distrib,
          LawfulCommRing.left_distrib, LawfulCommRing.left_distrib,
          LawfulCommRing.left_distrib, LawfulCommRing.left_distrib]
      have t1 : CommRingOps.mul (CommRingOps.mul x.c0 y.c0) z.c0 =
          CommRingOps.mul x.c0 (CommRingOps.mul y.c0 z.c0) :=
        LawfulCommRing.mul_assoc _ _ _
      have t2 : CommRingOps.mul (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1)) z.c0 =
          CommRingOps.mul nonResidue (CommRingOps.mul x.c1 (CommRingOps.mul y.c1 z.c0)) := by
        rw [LawfulCommRing.mul_assoc, LawfulCommRing.mul_assoc]
      have t3 : CommRingOps.mul nonResidue (CommRingOps.mul (CommRingOps.mul x.c0 y.c1) z.c1) =
          CommRingOps.mul x.c0 (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 z.c1)) := by
        rw [LawfulCommRing.mul_assoc x.c0 y.c1 z.c1,
            ← LawfulCommRing.mul_assoc nonResidue x.c0 _,
            LawfulCommRing.mul_comm nonResidue x.c0,
            LawfulCommRing.mul_assoc]
      have t4 : CommRingOps.mul nonResidue (CommRingOps.mul (CommRingOps.mul x.c1 y.c0) z.c1) =
          CommRingOps.mul nonResidue (CommRingOps.mul x.c1 (CommRingOps.mul y.c0 z.c1)) := by
        rw [LawfulCommRing.mul_assoc]
      rw [t1, t2, t3, t4, LawfulCommRing.add_add_add_comm]
      congr 1
      exact LawfulCommRing.add_comm _ _
    · change CommRingOps.add
          (CommRingOps.mul
            (CommRingOps.add (CommRingOps.mul x.c0 y.c0)
              (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1))) z.c1)
          (CommRingOps.mul
            (CommRingOps.add (CommRingOps.mul x.c0 y.c1) (CommRingOps.mul x.c1 y.c0)) z.c0) =
        CommRingOps.add
          (CommRingOps.mul x.c0
            (CommRingOps.add (CommRingOps.mul y.c0 z.c1) (CommRingOps.mul y.c1 z.c0)))
          (CommRingOps.mul x.c1
            (CommRingOps.add (CommRingOps.mul y.c0 z.c0)
              (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 z.c1))))
      rw [LawfulCommRing.right_distrib, LawfulCommRing.right_distrib,
          LawfulCommRing.left_distrib, LawfulCommRing.left_distrib]
      have s1 : CommRingOps.mul (CommRingOps.mul x.c0 y.c0) z.c1 =
          CommRingOps.mul x.c0 (CommRingOps.mul y.c0 z.c1) :=
        LawfulCommRing.mul_assoc _ _ _
      have s2 : CommRingOps.mul (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1)) z.c1 =
          CommRingOps.mul x.c1 (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 z.c1)) := by
        rw [LawfulCommRing.mul_assoc nonResidue _ z.c1,
            LawfulCommRing.mul_assoc x.c1 y.c1 z.c1,
            ← LawfulCommRing.mul_assoc nonResidue x.c1 _,
            LawfulCommRing.mul_comm nonResidue x.c1,
            LawfulCommRing.mul_assoc]
      have s3 : CommRingOps.mul (CommRingOps.mul x.c0 y.c1) z.c0 =
          CommRingOps.mul x.c0 (CommRingOps.mul y.c1 z.c0) :=
        LawfulCommRing.mul_assoc _ _ _
      have s4 : CommRingOps.mul (CommRingOps.mul x.c1 y.c0) z.c0 =
          CommRingOps.mul x.c1 (CommRingOps.mul y.c0 z.c0) :=
        LawfulCommRing.mul_assoc _ _ _
      rw [s1, s2, s3, s4, LawfulCommRing.add_add_add_comm]
      congr 1
      exact LawfulCommRing.add_comm _ _

private theorem pow_mod_congr {x y m : Nat} (h : x % m = y % m) :
    ∀ k : Nat, (x ^ k) % m = (y ^ k) % m
  | 0 => rfl
  | k + 1 => by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mod, pow_mod_congr h k, h, ← Nat.mul_mod]

/-- **Quadratic Non-Residue Theorem (`GoldilocksExt2.nonResidue_not_square`)**:
    $7$ has no square root in `Goldilocks`, so $u^2 - 7$ is irreducible over $\mathbb{F}_p$. -/
theorem nonResidue_not_square (y : Goldilocks) :
    CommRingOps.mul y y ≠ nonResidue := by
  intro hsq
  have hval : (y.val * y.val) % goldilocksPrime = 7 := by
    have hv := congrArg Goldilocks.val hsq
    rw [show CommRingOps.mul y y = Goldilocks.mul y y from rfl, Goldilocks.mul_val] at hv
    exact hv
  let half := (goldilocksPrime - 1) / 2
  have hy2 : (y.val ^ 2) % goldilocksPrime = 7 % goldilocksPrime := by
    have h2 : y.val ^ 2 = y.val * y.val := by simp [Nat.pow_succ]
    rw [h2, hval]
    decide
  have hpowEq : ((y.val ^ 2) ^ half) % goldilocksPrime = (7 ^ half) % goldilocksPrime :=
    pow_mod_congr hy2 half
  rw [← Nat.pow_mul] at hpowEq
  have h2half : 2 * half = goldilocksPrime - 1 := by decide
  rw [h2half] at hpowEq
  have hyNe : y.val ≠ 0 := by
    intro hy0
    rw [hy0] at hval
    cases hval
  have hnotDvd : ¬ (goldilocksPrime ∣ y.val) := fun hd => by
    have hle := Nat.le_of_dvd (by omega) hd
    have hlt := y.isLt
    omega
  have hflt := (goldilocksPrime_isPrime ()).pow_sub_one_mod hnotDvd
  have heuler := goldilocksEuler_modPow () rfl
  rw [hflt, heuler] at hpowEq
  revert hpowEq
  decide

def norm (z : GoldilocksExt2) : Goldilocks :=
  CommRingOps.sub (CommRingOps.mul z.c0 z.c0)
    (CommRingOps.mul nonResidue (CommRingOps.mul z.c1 z.c1))

theorem norm_ne_zero {z : GoldilocksExt2} (hz : z ≠ zero) :
    norm z ≠ Goldilocks.zero := by
  intro hnorm
  change CommRingOps.sub (CommRingOps.mul z.c0 z.c0)
      (CommRingOps.mul nonResidue (CommRingOps.mul z.c1 z.c1)) =
      CommRingOps.zero at hnorm
  have hEq : CommRingOps.mul z.c0 z.c0 =
      CommRingOps.mul nonResidue (CommRingOps.mul z.c1 z.c1) :=
    LawfulCommRing.sub_eq_zero_iff.mp hnorm
  if hc1 : z.c1 = Goldilocks.zero then
    have hrhs : CommRingOps.mul nonResidue (CommRingOps.mul z.c1 z.c1) =
        Goldilocks.zero := by
      rw [hc1]
      change CommRingOps.mul nonResidue
        (CommRingOps.mul CommRingOps.zero CommRingOps.zero) = CommRingOps.zero
      rw [LawfulCommRing.mul_zero, LawfulCommRing.mul_zero]
    rw [hrhs] at hEq
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hEq with hc0 | hc0 <;>
      exact hz (ext hc0 hc1)
  else
    let q := CommRingOps.mul z.c0 (Goldilocks.inv z.c1)
    have hqSq : CommRingOps.mul q q = nonResidue := by
      dsimp only [q]
      have hassoc : CommRingOps.mul (CommRingOps.mul z.c0 (Goldilocks.inv z.c1))
          (CommRingOps.mul z.c0 (Goldilocks.inv z.c1)) =
          CommRingOps.mul (CommRingOps.mul z.c0 z.c0)
            (CommRingOps.mul (Goldilocks.inv z.c1) (Goldilocks.inv z.c1)) := by
        rw [LawfulCommRing.mul_assoc z.c0 (Goldilocks.inv z.c1) _,
            ← LawfulCommRing.mul_assoc (Goldilocks.inv z.c1) z.c0 _,
            LawfulCommRing.mul_comm (Goldilocks.inv z.c1) z.c0,
            LawfulCommRing.mul_assoc z.c0 (Goldilocks.inv z.c1) _,
            ← LawfulCommRing.mul_assoc z.c0 z.c0 _]
      rw [hassoc, hEq, LawfulCommRing.mul_assoc nonResidue]
      have hcancel : CommRingOps.mul (CommRingOps.mul z.c1 z.c1)
          (CommRingOps.mul (Goldilocks.inv z.c1) (Goldilocks.inv z.c1)) = CommRingOps.one := by
        rw [LawfulCommRing.mul_assoc z.c1 z.c1 _,
            ← LawfulCommRing.mul_assoc z.c1 (Goldilocks.inv z.c1) _,
            Goldilocks.mul_inv_cancel hc1, LawfulCommRing.one_mul,
            Goldilocks.mul_inv_cancel hc1]
      rw [hcancel, LawfulCommRing.mul_one]
    exact nonResidue_not_square q hqSq

@[expose] def inv (z : GoldilocksExt2) : GoldilocksExt2 :=
  let invN := Goldilocks.inv (norm z)
  ⟨CommRingOps.mul z.c0 invN, CommRingOps.neg (CommRingOps.mul z.c1 invN)⟩

theorem mul_inv_cancel {z : GoldilocksExt2} (hz : z ≠ zero) :
    CommRingOps.mul z (inv z) = CommRingOps.one := by
  have hnormNe := norm_ne_zero hz
  let invN := Goldilocks.inv (norm z)
  apply ext
  · change CommRingOps.add
        (CommRingOps.mul z.c0 (CommRingOps.mul z.c0 invN))
        (CommRingOps.mul nonResidue
          (CommRingOps.mul z.c1 (CommRingOps.neg (CommRingOps.mul z.c1 invN)))) =
      CommRingOps.one
    rw [← LawfulCommRing.mul_assoc z.c0 z.c0 invN,
        LawfulCommRing.mul_neg z.c1, LawfulCommRing.mul_neg nonResidue,
        ← LawfulCommRing.mul_assoc z.c1 z.c1 invN,
        ← LawfulCommRing.mul_assoc nonResidue _ invN,
        ← LawfulCommRing.sub_eq_add_neg,
        ← LawfulCommRing.sub_mul]
    exact Goldilocks.mul_inv_cancel hnormNe
  · change CommRingOps.add
        (CommRingOps.mul z.c0 (CommRingOps.neg (CommRingOps.mul z.c1 invN)))
        (CommRingOps.mul z.c1 (CommRingOps.mul z.c0 invN)) =
      CommRingOps.zero
    rw [LawfulCommRing.mul_neg,
        ← LawfulCommRing.mul_assoc z.c0 z.c1 invN,
        ← LawfulCommRing.mul_assoc z.c1 z.c0 invN,
        LawfulCommRing.mul_comm z.c1 z.c0,
        LawfulCommRing.add_left_neg]

theorem ofBase_injective {a b : Goldilocks} (h : ofBase a = ofBase b) : a = b :=
  congrArg c0 h

theorem ofBase_add (a b : Goldilocks) :
    ofBase (CommRingOps.add a b) = CommRingOps.add (ofBase a) (ofBase b) := by
  apply ext
  · rfl
  · exact (LawfulCommRing.add_zero _).symm

theorem ofBase_sub (a b : Goldilocks) :
    ofBase (CommRingOps.sub a b) = CommRingOps.sub (ofBase a) (ofBase b) := by
  apply ext
  · rfl
  · exact (LawfulCommRing.sub_self _).symm

theorem ofBase_mul (a b : Goldilocks) :
    ofBase (CommRingOps.mul a b) = CommRingOps.mul (ofBase a) (ofBase b) := by
  apply ext
  · change CommRingOps.mul a b =
      CommRingOps.add (CommRingOps.mul a b)
        (CommRingOps.mul nonResidue (CommRingOps.mul CommRingOps.zero CommRingOps.zero))
    rw [LawfulCommRing.mul_zero, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  · change CommRingOps.zero =
      CommRingOps.add (CommRingOps.mul a CommRingOps.zero) (CommRingOps.mul CommRingOps.zero b)
    rw [LawfulCommRing.mul_zero, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]


/-- Coordinate interface for multiplication in the quadratic extension. -/
theorem mul_c0 (a b : GoldilocksExt2) :
    (CommRingOps.mul a b).c0 = CommRingOps.add (CommRingOps.mul a.c0 b.c0)
      (CommRingOps.mul nonResidue (CommRingOps.mul a.c1 b.c1)) := by
  change (mul a b).c0 = _
  unfold mul
  rfl

theorem mul_c1 (a b : GoldilocksExt2) :
    (CommRingOps.mul a b).c1 = CommRingOps.add (CommRingOps.mul a.c0 b.c1)
      (CommRingOps.mul a.c1 b.c0) := by
  change (mul a b).c1 = _
  unfold mul
  rfl

theorem uBasis_c0 : uBasis.c0 = CommRingOps.zero := by unfold uBasis; rfl
theorem uBasis_c1 : uBasis.c1 = CommRingOps.one := by unfold uBasis; rfl

end GoldilocksExt2

instance : NoZeroDivisors GoldilocksExt2 where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} h := by
    if ha : a = GoldilocksExt2.zero then
      exact .inl ha
    else
      right
      have hmul := congrArg (CommRingOps.mul (GoldilocksExt2.inv a)) h
      rw [LawfulCommRing.mul_zero, ← LawfulCommRing.mul_assoc,
          LawfulCommRing.mul_comm (GoldilocksExt2.inv a) a,
          GoldilocksExt2.mul_inv_cancel ha, LawfulCommRing.one_mul] at hmul
      exact hmul

/-- Challenge space lower bound: $|\mathbb{F}_{p^2}| = p^2 > 2^{127}$. -/
theorem goldilocksExt2_card_gt_two_pow_126 (k : Nat) (hk : k ≤ 127) :
    2 ^ k < goldilocksPrime ^ 2 := by
  have hpow : 2 ^ k ≤ 2 ^ 127 := Nat.pow_le_pow_right (by decide) hk
  have hlt : 2 ^ 127 < goldilocksPrime ^ 2 := by decide
  exact Nat.lt_of_le_of_lt hpow hlt

instance : LawfulField Goldilocks where
  inv := Goldilocks.inv
  zero_ne_one := by decide
  inv_zero := by decide
  mul_inv_cancel := Goldilocks.mul_inv_cancel

instance : LawfulField GoldilocksExt2 where
  inv := GoldilocksExt2.inv
  zero_ne_one := by decide
  inv_zero := by decide
  mul_inv_cancel := GoldilocksExt2.mul_inv_cancel

/-! ## 2. Universal Two-Sided Multiplicative Inverse & Bezout Equivalence on `Goldilocks` -/

/-- Constructive extended-Euclidean Bezout field inverse on `Goldilocks` (`invBezout 0 = 0`). -/
def Goldilocks.invBezout (x : Goldilocks) : Goldilocks :=
  if x.val = 0 then Goldilocks.zero else goldOfInt (extGcd x.val Goldilocks.p).2.1

/-- **Universal Two-Sided `Goldilocks` Inverse Law (`goldilocks_universal_mul_inv_cancel`)**. -/
theorem goldilocks_universal_mul_inv_cancel (x : Goldilocks) (hx : x ≠ Goldilocks.zero) :
    CommRingOps.mul x (Goldilocks.inv x) = CommRingOps.one ∧
    CommRingOps.mul (Goldilocks.inv x) x = CommRingOps.one :=
  let hR := Goldilocks.mul_inv_cancel hx
  ⟨hR, (LawfulCommRing.mul_comm _ _).trans hR⟩

/-- **Universal Bezout Inverse Soundness (`goldilocks_mul_invBezout_cancel`)**. -/
theorem goldilocks_mul_invBezout_cancel (x : Goldilocks) (hx : x ≠ Goldilocks.zero) :
    CommRingOps.mul x (Goldilocks.invBezout x) = CommRingOps.one ∧
    CommRingOps.mul (Goldilocks.invBezout x) x = CommRingOps.one := by
  have hxValNe : x.val ≠ 0 := fun h0 => hx (Goldilocks.ext h0)
  obtain ⟨hdx, hdp⟩ := extGcd_dvd x.val Goldilocks.p
  have hg1 : (extGcd x.val Goldilocks.p).1 = 1 := by
    rcases goldilocksPrime_is_prime.2 _ hdp with h1 | hpEq
    · exact h1
    · rw [hpEq] at hdx
      have hle := Nat.le_of_dvd (by omega) hdx; have := x.isLt; unfold Goldilocks.p at hle; omega
  have hbez := extGcd_bezout x.val Goldilocks.p; rw [hg1] at hbez
  have hRight : CommRingOps.mul x (Goldilocks.invBezout x) = CommRingOps.one := by
    unfold Goldilocks.invBezout; simp only [hxValNe, ↓reduceIte]
    change Goldilocks.mul x (goldOfInt (extGcd x.val Goldilocks.p).2.1) = Goldilocks.one
    have hMulInt : Goldilocks.mul x (goldOfInt (extGcd x.val Goldilocks.p).2.1) =
        goldOfInt ((x.val : Int) * (extGcd x.val Goldilocks.p).2.1) := by
      have h := goldOfInt_mul x.val (extGcd x.val Goldilocks.p).2.1; rwa [goldOfInt_nat] at h
    rw [hMulInt]; apply Goldilocks.ext; apply Int.ofNat_inj.mp; rw [goldOfInt_val]
    have hMod : ((x.val : Int) * (extGcd x.val Goldilocks.p).2.1) % goldP = 1 := by
      have hEq : (x.val : Int) * (extGcd x.val Goldilocks.p).2.1 =
          1 + goldP * (-(extGcd x.val Goldilocks.p).2.2) := by
        dsimp only [goldP, Goldilocks.p] at hbez ⊢; rw [Int.mul_neg]; omega
      rw [hEq, Int.add_mul_emod_self_left]; decide
    rw [hMod]; rfl
  exact ⟨hRight, (LawfulCommRing.mul_comm _ _).trans hRight⟩

/-- Exact agreement of Fermat exponentiation inverse and Euclidean Bezout inverse for ALL `x`. -/
theorem goldilocks_invBezout_eq_inv (x : Goldilocks) :
    Goldilocks.invBezout x = Goldilocks.inv x := by
  if hx : x = Goldilocks.zero then subst hx; rfl
  else
    have hB := (goldilocks_mul_invBezout_cancel x hx).1
    have hF := (goldilocks_universal_mul_inv_cancel x hx).2
    calc Goldilocks.invBezout x
        = CommRingOps.mul CommRingOps.one (Goldilocks.invBezout x) := (LawfulCommRing.one_mul _).symm
      _ = CommRingOps.mul (CommRingOps.mul (Goldilocks.inv x) x) (Goldilocks.invBezout x) := by rw [hF]
      _ = CommRingOps.mul (Goldilocks.inv x) (CommRingOps.mul x (Goldilocks.invBezout x)) :=
            LawfulCommRing.mul_assoc _ _ _
      _ = CommRingOps.mul (Goldilocks.inv x) CommRingOps.one := by rw [hB]
      _ = Goldilocks.inv x := LawfulCommRing.mul_one _

/-- **Integral-Domain Zero-Product Characterization (`goldilocks_mul_eq_zero_iff`)**. -/
theorem goldilocks_mul_eq_zero_iff (x y : Goldilocks) :
    CommRingOps.mul x y = Goldilocks.zero ↔ x = Goldilocks.zero ∨ y = Goldilocks.zero := by
  constructor
  · exact NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero
  · rintro (rfl | rfl)
    · exact LawfulCommRing.zero_mul y
    · exact LawfulCommRing.mul_zero x


private theorem sq_mul_sq_eq {R : Type} [LawfulCommRing R] (a b : R) :
    CommRingOps.mul (CommRingOps.mul a b) (CommRingOps.mul a b) =
      CommRingOps.mul (CommRingOps.mul a a) (CommRingOps.mul b b) := by
  rw [LawfulCommRing.mul_assoc a b _, ← LawfulCommRing.mul_assoc b a _,
      LawfulCommRing.mul_comm b a, LawfulCommRing.mul_assoc a b _, ← LawfulCommRing.mul_assoc a a _]

/-- Exact norm characterization on `GoldilocksExt2`: $a^2 - 7 b^2 = 0 \iff a = 0 \land b = 0$. -/
theorem norm_ext2_eq_zero_iff (z : GoldilocksExt2) :
    GoldilocksExt2.norm z = Goldilocks.zero ↔ z = GoldilocksExt2.zero := by
  constructor
  · intro hN
    if hz : z = GoldilocksExt2.zero then exact hz
    else exact False.elim (GoldilocksExt2.norm_ne_zero hz hN)
  · rintro rfl
    change CommRingOps.sub (CommRingOps.mul CommRingOps.zero CommRingOps.zero)
      (CommRingOps.mul GoldilocksExt2.nonResidue (CommRingOps.mul CommRingOps.zero CommRingOps.zero)) =
      CommRingOps.zero
    rw [LawfulCommRing.mul_zero, LawfulCommRing.mul_zero, LawfulCommRing.sub_self]

/-- Parametric modular quadratic-extension multiplication $(a_0 + a_1 u)(b_0 + b_1 u) \bmod (m, u^2 - r)$. -/
@[expose] def quadExtMulMod (m r : Nat) (x y : Nat × Nat) : Nat × Nat :=
  ((x.1 * y.1 + r * (x.2 * y.2)) % m, (x.1 * y.2 + x.2 * y.1) % m)

theorem goldilocksExt2_mul_coords_eq_quadExtMulMod (x y : GoldilocksExt2) :
    ((GoldilocksExt2.mul x y).c0.val, (GoldilocksExt2.mul x y).c1.val) =
      quadExtMulMod Goldilocks.p 7 (x.c0.val, x.c1.val) (y.c0.val, y.c1.val) := by
  unfold GoldilocksExt2.mul quadExtMulMod
  dsimp only [CommRingOps.add, CommRingOps.mul, GoldilocksExt2.nonResidue, Goldilocks.p]
  apply Prod.ext <;> dsimp only
  · rw [Goldilocks.add_val, Goldilocks.mul_val, Goldilocks.mul_val, Goldilocks.mul_val,
        Nat.mul_mod_mod, Nat.add_mod_mod, Nat.mod_add_mod]
  · rw [Goldilocks.add_val, Goldilocks.mul_val, Goldilocks.mul_val, Nat.mod_add_mod, Nat.add_mod_mod]

/-- **Universal Integral-Domain Law via `quadExtMulMod` at `(Goldilocks.p, 7)`**. -/
theorem goldilocks_quadExtMulMod_no_zero_divisors (x y : GoldilocksExt2) :
    quadExtMulMod Goldilocks.p 7 (x.c0.val, x.c1.val) (y.c0.val, y.c1.val) = (0, 0) ↔
      x = GoldilocksExt2.zero ∨ y = GoldilocksExt2.zero := by
  rw [← goldilocksExt2_mul_coords_eq_quadExtMulMod]
  constructor
  · intro hPair
    exact NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero
      (GoldilocksExt2.ext (Goldilocks.ext (Prod.mk.inj hPair).1) (Goldilocks.ext (Prod.mk.inj hPair).2))
  · rintro (rfl | rfl)
    · rw [show GoldilocksExt2.mul GoldilocksExt2.zero y = GoldilocksExt2.zero from LawfulCommRing.zero_mul y]; rfl
    · rw [show GoldilocksExt2.mul x GoldilocksExt2.zero = GoldilocksExt2.zero from LawfulCommRing.mul_zero x]; rfl

/-- Square root of $-1$ in `Goldilocks`: $\iota = 2^{48}$ satisfies $\iota^2 = 2^{96} \equiv -1 \pmod p$. -/
def goldilocksSqrtNegOne : Goldilocks := ⟨2 ^ 48, by decide⟩

theorem goldilocksSqrtNegOne_sq :
    CommRingOps.mul goldilocksSqrtNegOne goldilocksSqrtNegOne = CommRingOps.neg CommRingOps.one := by
  apply Goldilocks.ext
  change (Goldilocks.mul goldilocksSqrtNegOne goldilocksSqrtNegOne).val = (Goldilocks.neg Goldilocks.one).val
  rw [Goldilocks.mul_val, Goldilocks.neg_val]; decide

/-- $-7$ is ALSO a quadratic non-residue in `Goldilocks`. -/
theorem neg_seven_not_square_in_goldilocks (x : Goldilocks) :
    CommRingOps.mul x x ≠ CommRingOps.neg GoldilocksExt2.nonResidue := by
  intro hSq
  have hwSq : CommRingOps.mul (CommRingOps.mul x goldilocksSqrtNegOne)
      (CommRingOps.mul x goldilocksSqrtNegOne) = GoldilocksExt2.nonResidue := by
    rw [sq_mul_sq_eq, hSq, goldilocksSqrtNegOne_sq, LawfulCommRing.neg_mul,
        LawfulCommRing.mul_neg, LawfulCommRing.neg_neg, LawfulCommRing.mul_one]
  exact GoldilocksExt2.nonResidue_not_square _ hwSq

/-- Predicate stating $(v^2 + a_1 v + a_0)(v^2 + b_1 v + b_0) = v^4 - 7$ in $\mathbb{F}_p[v]$. -/
def IsMonicQuadFactorOfV4Sub7 (a1 a0 b1 b0 : Goldilocks) : Prop :=
  CommRingOps.add a1 b1 = Goldilocks.zero ∧
  CommRingOps.add (CommRingOps.add a0 b0) (CommRingOps.mul a1 b1) = Goldilocks.zero ∧
  CommRingOps.add (CommRingOps.mul a1 b0) (CommRingOps.mul b1 a0) = Goldilocks.zero ∧
  CommRingOps.mul a0 b0 = CommRingOps.neg GoldilocksExt2.nonResidue

/-- **Complete Polynomial Irreducibility of $v^4 - 7 \in \mathbb{F}_p[v]$ (`v_pow4_sub_seven_irreducible`)**. -/
theorem v_pow4_sub_seven_irreducible :
    (∀ r : Goldilocks,
      CommRingOps.mul (CommRingOps.mul r r) (CommRingOps.mul r r) ≠ GoldilocksExt2.nonResidue) ∧
    (∀ a1 a0 b1 b0 : Goldilocks, ¬ IsMonicQuadFactorOfV4Sub7 a1 a0 b1 b0) := by
  refine ⟨fun r h4 => GoldilocksExt2.nonResidue_not_square (CommRingOps.mul r r) h4, ?_⟩
  intro a1 a0 b1 b0 ⟨hDeg3, hDeg2, hDeg1, hConst⟩
  have hb1 : b1 = CommRingOps.neg a1 :=
    LawfulCommRing.add_left_cancel (hDeg3.trans (LawfulCommRing.add_right_neg a1).symm)
  if ha1Zero : a1 = Goldilocks.zero then
    subst ha1Zero
    have ha1b1 : CommRingOps.mul Goldilocks.zero b1 = CommRingOps.zero := LawfulCommRing.zero_mul b1
    rw [ha1b1, LawfulCommRing.add_zero] at hDeg2
    have hb0 : b0 = CommRingOps.neg a0 :=
      LawfulCommRing.add_left_cancel (hDeg2.trans (LawfulCommRing.add_right_neg a0).symm)
    rw [hb0, LawfulCommRing.mul_neg] at hConst
    have hNeg := congrArg CommRingOps.neg hConst
    rw [LawfulCommRing.neg_neg, LawfulCommRing.neg_neg] at hNeg
    exact GoldilocksExt2.nonResidue_not_square a0 hNeg
  else
    rw [hb1, LawfulCommRing.neg_mul, ← LawfulCommRing.sub_eq_add_neg, ← LawfulCommRing.mul_sub] at hDeg1
    rcases (goldilocks_mul_eq_zero_iff a1 (CommRingOps.sub b0 a0)).mp hDeg1 with hBad | hSub0
    · exact ha1Zero hBad
    · rw [LawfulCommRing.sub_eq_zero_iff.mp hSub0] at hConst
      exact neg_seven_not_square_in_goldilocks a0 hConst


namespace GoldilocksExt2
@[simp] theorem add_c0 (x y : GoldilocksExt2) : (CommRingOps.add x y).c0 = CommRingOps.add x.c0 y.c0 := by change (add x y).c0 = _; unfold add; rfl
@[simp] theorem add_c1 (x y : GoldilocksExt2) : (CommRingOps.add x y).c1 = CommRingOps.add x.c1 y.c1 := by change (add x y).c1 = _; unfold add; rfl
@[simp] theorem zero_c0 : zero.c0 = CommRingOps.zero := by unfold zero; rfl
@[simp] theorem zero_c1 : zero.c1 = CommRingOps.zero := by unfold zero; rfl
@[simp] theorem one_c0 : one.c0 = CommRingOps.one := by unfold one; rfl
@[simp] theorem one_c1 : one.c1 = CommRingOps.zero := by unfold one; rfl
theorem uBasis_mul_self : mul uBasis uBasis = ofBase nonResidue := by
  apply ext <;> apply Goldilocks.ext <;> decide
end GoldilocksExt2

theorem Goldilocks.ring_zero : (CommRingOps.zero : Goldilocks) = Goldilocks.zero := by rfl
theorem Goldilocks.ring_one : (CommRingOps.one : Goldilocks) = Goldilocks.one := by rfl
theorem GoldilocksExt2.ring_zero : (CommRingOps.zero : GoldilocksExt2) = GoldilocksExt2.zero := by rfl
theorem GoldilocksExt2.ring_one : (CommRingOps.one : GoldilocksExt2) = GoldilocksExt2.one := by rfl
theorem GoldilocksExt2.ofBase_zero : GoldilocksExt2.ofBase Goldilocks.zero = GoldilocksExt2.zero := by unfold GoldilocksExt2.ofBase GoldilocksExt2.zero; rfl
theorem GoldilocksExt2.ofBase_one : GoldilocksExt2.ofBase Goldilocks.one = GoldilocksExt2.one := by unfold GoldilocksExt2.ofBase GoldilocksExt2.one; rfl
end Qsag
end

public section
namespace Qsag
open CommRingOps
namespace Goldilocks

theorem natCast_val : ∀ k : Nat, (CRing.natCast k : Goldilocks).val = k % goldilocksPrime
  | 0 => rfl
  | 1 => by decide
  | n + 2 => by
    show (Goldilocks.add (CRing.natCast (n + 1)) Goldilocks.one).val = _
    rw [Goldilocks.add_val, natCast_val (n + 1), Goldilocks.one_val, Nat.mod_add_mod]

/-- `1, …, p - 1` are nonzero in `Goldilocks`. -/
theorem natCast_ne_zero (k : Nat) (h1 : 1 ≤ k) (hk : k < goldilocksPrime) :
    (CRing.natCast k : Goldilocks) ≠ zero := fun e => by
  have hv := congrArg Goldilocks.val e
  rw [natCast_val, Nat.mod_eq_of_lt hk] at hv
  have h0 : k = 0 := hv
  rw [h0] at h1
  exact absurd h1 (by decide)

end Goldilocks

/-! ### Exports for lane zkhem -/

namespace GoldilocksExt2

theorem sub_c0 (x y : GoldilocksExt2) :
    (CommRingOps.sub x y).c0 = CommRingOps.sub x.c0 y.c0 := by
  change (GoldilocksExt2.sub x y).c0 = _; unfold GoldilocksExt2.sub; rfl
theorem sub_c1 (x y : GoldilocksExt2) :
    (CommRingOps.sub x y).c1 = CommRingOps.sub x.c1 y.c1 := by
  change (GoldilocksExt2.sub x y).c1 = _; unfold GoldilocksExt2.sub; rfl
theorem neg_c0 (x : GoldilocksExt2) : (CommRingOps.neg x).c0 = CommRingOps.neg x.c0 := by
  change (GoldilocksExt2.neg x).c0 = _; unfold GoldilocksExt2.neg; rfl
theorem neg_c1 (x : GoldilocksExt2) : (CommRingOps.neg x).c1 = CommRingOps.neg x.c1 := by
  change (GoldilocksExt2.neg x).c1 = _; unfold GoldilocksExt2.neg; rfl
theorem ringZero_c0 : (CommRingOps.zero : GoldilocksExt2).c0 = CommRingOps.zero := zero_c0
theorem ringZero_c1 : (CommRingOps.zero : GoldilocksExt2).c1 = CommRingOps.zero := zero_c1
theorem ringOne_c0 : (CommRingOps.one : GoldilocksExt2).c0 = CommRingOps.one := one_c0
theorem ringOne_c1 : (CommRingOps.one : GoldilocksExt2).c1 = CommRingOps.zero := one_c1
theorem norm_eq (z : GoldilocksExt2) :
    norm z = CommRingOps.sub (CommRingOps.mul z.c0 z.c0)
      (CommRingOps.mul nonResidue (CommRingOps.mul z.c1 z.c1)) := by
  unfold norm; rfl
theorem inv_c0 (z : GoldilocksExt2) :
    (inv z).c0 = CommRingOps.mul z.c0 (Goldilocks.inv (norm z)) := by unfold inv; rfl
theorem inv_c1 (z : GoldilocksExt2) :
    (inv z).c1 = CommRingOps.neg (CommRingOps.mul z.c1 (Goldilocks.inv (norm z))) := by
  unfold inv; rfl

end GoldilocksExt2


end Qsag

-- Owning-module audit certificates for theorems audited and paired in `Tests/MathAndCoding`.
#verify_constructive
  Qsag.goldilocks_mul_invBezout_cancel
  Qsag.goldilocks_quadExtMulMod_no_zero_divisors
  Qsag.goldilocks_universal_mul_inv_cancel
  Qsag.v_pow4_sub_seven_irreducible
  Qsag.Goldilocks.natCast_ne_zero
  Qsag.goldilocks_invBezout_eq_inv
