module

public section
namespace Qsag
set_option autoImplicit false
/-! ## 1. Polymorphic Commutative Ring & Integral Domain Typeclasses -/

/-- Algebraic operations of a commutative ring with unity. -/
class CommRingOps (R : Type) where
  zero : R
  one : R
  add : R → R → R
  mul : R → R → R
  neg : R → R
  sub : R → R → R

/-- Lawful commutative ring axioms over `CommRingOps R`. -/
class LawfulCommRing (R : Type) extends CommRingOps R where
  add_assoc : ∀ a b c : R, add (add a b) c = add a (add b c)
  add_comm : ∀ a b : R, add a b = add b a
  zero_add : ∀ a : R, add zero a = a
  add_zero : ∀ a : R, add a zero = a
  add_left_neg : ∀ a : R, add (neg a) a = zero
  sub_eq_add_neg : ∀ a b : R, sub a b = add a (neg b)
  mul_assoc : ∀ a b c : R, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b : R, mul a b = mul b a
  one_mul : ∀ a : R, mul one a = a
  mul_one : ∀ a : R, mul a one = a
  left_distrib : ∀ a b c : R, mul a (add b c) = add (mul a b) (mul a c)
  right_distrib : ∀ a b c : R, mul (add a b) c = add (mul a c) (mul b c)

/-- Integral domain property: no non-trivial zero divisors. -/
class NoZeroDivisors (R : Type) [CommRingOps R] : Type where
  eq_zero_or_eq_zero_of_mul_eq_zero :
    ∀ {a b : R}, CommRingOps.mul a b = CommRingOps.zero →
      a = CommRingOps.zero ∨ b = CommRingOps.zero

namespace LawfulCommRing
variable {R : Type} [LawfulCommRing R]
open CommRingOps

theorem add_right_neg (a : R) : add a (neg a) = zero := by
  rw [add_comm, add_left_neg]

theorem add_left_cancel {a b c : R} (h : add a b = add a c) : b = c := by
  have h1 : add (neg a) (add a b) = add (neg a) (add a c) := congrArg (add (neg a)) h
  rw [← add_assoc, ← add_assoc, add_left_neg, zero_add, zero_add] at h1
  exact h1

theorem sub_self (a : R) : sub a a = zero := by
  rw [sub_eq_add_neg, add_right_neg]

theorem neg_zero (R : Type) [LawfulCommRing R] : neg (zero : R) = zero := by
  apply add_left_cancel (a := zero)
  rw [add_right_neg, add_zero]

theorem sub_zero (a : R) : sub a zero = a := by
  rw [sub_eq_add_neg, neg_zero R, add_zero]

theorem mul_zero (a : R) : mul a zero = zero := by
  apply add_left_cancel (a := mul a zero)
  rw [← left_distrib, add_zero, add_zero]

theorem zero_mul (a : R) : mul zero a = zero := by
  rw [mul_comm, mul_zero]

theorem neg_neg (a : R) : neg (neg a) = a := by
  apply add_left_cancel (a := neg a)
  rw [add_right_neg, add_left_neg]

theorem mul_neg (a b : R) : mul a (neg b) = neg (mul a b) := by
  apply add_left_cancel (a := mul a b)
  rw [← left_distrib, add_right_neg, mul_zero, add_right_neg]

theorem neg_mul (a b : R) : mul (neg a) b = neg (mul a b) := by
  rw [mul_comm, mul_neg, mul_comm]

theorem mul_sub (a b c : R) : mul a (sub b c) = sub (mul a b) (mul a c) := by
  rw [sub_eq_add_neg, left_distrib, mul_neg, ← sub_eq_add_neg]

theorem sub_mul (a b c : R) : mul (sub a b) c = sub (mul a c) (mul b c) := by
  rw [sub_eq_add_neg, right_distrib, neg_mul, ← sub_eq_add_neg]

theorem add_sub_cancel_left (a b : R) : add a (sub b a) = b := by
  rw [sub_eq_add_neg, add_comm b (neg a), ← add_assoc, add_right_neg, zero_add]

theorem add_add_add_comm (a b c d : R) :
    add (add a b) (add c d) = add (add a c) (add b d) := by
  rw [add_assoc, ← add_assoc b c d, add_comm b c, add_assoc c b d, ← add_assoc]

theorem sub_eq_zero_iff {a b : R} : sub a b = zero ↔ a = b := by
  constructor
  · intro h
    have h1 := congrArg (fun z => add z b) h
    rw [zero_add, sub_eq_add_neg, add_assoc, add_left_neg, add_zero] at h1
    exact h1
  · intro h
    subst h
    exact sub_self a

end LawfulCommRing
/-- Constructive field typeclass extending `LawfulCommRing F` with an explicit total inverse `inv`
    satisfying `a * inv a = 1` for `a ≠ 0` and the totalization convention `inv 0 = 0`. -/
class LawfulField (F : Type) extends LawfulCommRing F where
  inv : F → F
  zero_ne_one : (CommRingOps.zero : F) ≠ (CommRingOps.one : F)
  inv_zero : inv CommRingOps.zero = CommRingOps.zero
  mul_inv_cancel : ∀ {a : F}, a ≠ CommRingOps.zero →
    CommRingOps.mul a (inv a) = CommRingOps.one

namespace LawfulField
variable {F : Type} [LawfulField F]
open CommRingOps

theorem inv_mul_cancel {a : F} (ha : a ≠ zero) : mul (inv a) a = one := by
  rw [LawfulCommRing.mul_comm, mul_inv_cancel ha]

theorem one_ne_zero : (one : F) ≠ zero :=
  fun h => zero_ne_one h.symm

theorem mul_eq_zero {a b : F} [DecidableEq F]
    (h : mul a b = zero) : a = zero ∨ b = zero := by
  if ha : a = zero then
    exact .inl ha
  else
    right
    have hmul := congrArg (mul (inv a)) h
    rw [LawfulCommRing.mul_zero, ← LawfulCommRing.mul_assoc,
        inv_mul_cancel ha, LawfulCommRing.one_mul] at hmul
    exact hmul

/-- Constructive `NoZeroDivisors F` dictionary derived from `LawfulField F` without creating
    global typeclass diamonds against concrete rings that already register `NoZeroDivisors`. -/
@[instance_reducible] def toNoZeroDivisors (F : Type) [LawfulField F] [DecidableEq F] : NoZeroDivisors F where
  eq_zero_or_eq_zero_of_mul_eq_zero := mul_eq_zero

end LawfulField

end Qsag
