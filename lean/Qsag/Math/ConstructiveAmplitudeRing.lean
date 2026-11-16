module
/-
# Qsag.Math.ConstructiveAmplitudeRing — ordered `*`-rings of exact quantum amplitudes

A choice-free tower of amplitude rings for exact (square-root-free) quantum mechanics.

1. `OrderedCommRing`, `FormallyRealRing`, `LinearOrderedDomain`: partially ordered commutative
   rings, with the order consequences used later derived from five order axioms.
2. `PosFrac R`: the fraction field of a linearly ordered domain as a quotient of pairs with a
   positive denominator. `PosFrac Int` is `ℚ`; core `Rat` is not used because every lemma about
   it depends on `Classical.choice` in Lean 4.35.
3. `QuadExt R d = R[√d]` with the cone of totally positive elements (nonnegative under both
   `√d ↦ ±√d`), which is formally real whenever `0 < d`.
4. `Complexified R = R[i]` and the class `ConstructiveAmplitudeRing R A`: a commutative `*`-ring
   `A` over an ordered ring `R` with `z * star z = ofReal (normSq z)`. Multiplicativity of
   `normSq`, definiteness and the parallelogram law are theorems, not axioms.
5. Instances `ℤ[i]`, `ℚ[i]`, `ℚ[√2]`, `ℚ[√2, i]`, the exact unit `3/5 + 4/5 i`, the proof that no
   power of two clears its denominator, and the eighth root of unity `ζ₈ ∈ ℚ[√2, i]`.
-/
public import Qsag.Math.Goldilocks
public import Qsag.Math.Tactic.CommRing

public section
namespace Qsag
set_option autoImplicit false

open CommRingOps

/-! ## 1. Ordered commutative rings -/

/-- A commutative ring with a compatible partial order. The order need not be total. -/
class OrderedCommRing (R : Type) extends LawfulCommRing R where
  le : R → R → Prop
  le_refl : ∀ a : R, le a a
  le_trans : ∀ {a b c : R}, le a b → le b c → le a c
  le_antisymm : ∀ {a b : R}, le a b → le b a → a = b
  add_le_add_left : ∀ {a b : R} (c : R), le a b → le (add c a) (add c b)
  mul_nonneg : ∀ {a b : R}, le zero a → le zero b → le zero (mul a b)

/-- Strict positivity `0 ≤ a ∧ a ≠ 0`. -/
structure IsPos {R : Type} [OrderedCommRing R] (a : R) : Prop where
  nonneg : OrderedCommRing.le zero a
  ne_zero : a ≠ zero

namespace OrderedCommRing
variable {R : Type} [OrderedCommRing R]

theorem le_of_eq {a b : R} (h : a = b) : le a b := h ▸ le_refl a

theorem sub_nonneg_of_le {a b : R} (h : le a b) : le zero (sub b a) := by
  have h1 := add_le_add_left (neg a) h
  have e1 : add (neg a) a = zero := by constructive_ring
  have e2 : add (neg a) b = sub b a := by constructive_ring
  rw [e1, e2] at h1
  exact h1

theorem le_of_sub_nonneg {a b : R} (h : le zero (sub b a)) : le a b := by
  have h1 := add_le_add_left a h
  have e1 : add a zero = a := by constructive_ring
  have e2 : add a (sub b a) = b := by constructive_ring
  rw [e1, e2] at h1
  exact h1

theorem add_le_add {a b c d : R} (h1 : le a b) (h2 : le c d) : le (add a c) (add b d) := by
  have s1 := add_le_add_left a h2
  have s2 := add_le_add_left d h1
  rw [LawfulCommRing.add_comm d a, LawfulCommRing.add_comm d b] at s2
  exact le_trans s1 s2

theorem add_nonneg {a b : R} (ha : le zero a) (hb : le zero b) : le zero (add a b) := by
  have h := add_le_add ha hb
  rw [LawfulCommRing.zero_add] at h
  exact h

theorem le_add_of_nonneg_right {a c : R} (hc : le zero c) : le a (add a c) := by
  have h := add_le_add_left a hc
  rw [LawfulCommRing.add_zero] at h
  exact h

theorem mul_le_mul_of_nonneg_left {a b c : R} (h : le a b) (hc : le zero c) :
    le (mul c a) (mul c b) := by
  have h1 := mul_nonneg hc (sub_nonneg_of_le h)
  have e : mul c (sub b a) = sub (mul c b) (mul c a) := by constructive_ring
  rw [e] at h1
  exact le_of_sub_nonneg h1

theorem mul_le_mul_of_nonneg_right {a b c : R} (h : le a b) (hc : le zero c) :
    le (mul a c) (mul b c) := by
  rw [LawfulCommRing.mul_comm a c, LawfulCommRing.mul_comm b c]
  exact mul_le_mul_of_nonneg_left h hc

theorem mul_le_mul_nonneg {a b c d : R} (h1 : le a b) (h2 : le c d)
    (ha : le zero a) (hd : le zero d) : le (mul a c) (mul b d) :=
  le_trans (mul_le_mul_of_nonneg_left h2 ha) (mul_le_mul_of_nonneg_right h1 hd)

theorem neg_nonneg_of_nonpos {a : R} (h : le a zero) : le zero (neg a) := by
  have h1 := sub_nonneg_of_le h
  have e : sub zero a = neg a := by constructive_ring
  rw [e] at h1
  exact h1

theorem nonpos_of_neg_nonneg {a : R} (h : le zero (neg a)) : le a zero := by
  apply le_of_sub_nonneg
  have e : sub zero a = neg a := by constructive_ring
  rw [e]
  exact h

theorem eq_zero_of_add_eq_zero_left {a b : R} (ha : le zero a) (hb : le zero b)
    (h : add a b = zero) : a = zero := by
  have h1 := le_add_of_nonneg_right (a := a) hb
  rw [h] at h1
  exact le_antisymm h1 ha

theorem eq_zero_of_add_eq_zero_right {a b : R} (ha : le zero a) (hb : le zero b)
    (h : add a b = zero) : b = zero :=
  eq_zero_of_add_eq_zero_left hb ha (by rw [LawfulCommRing.add_comm]; exact h)

end OrderedCommRing

/-- An ordered ring in which squares are nonnegative and only zero squares to zero. -/
class FormallyRealRing (R : Type) extends OrderedCommRing R where
  sq_nonneg : ∀ a : R, le zero (mul a a)
  sq_eq_zero : ∀ {a : R}, mul a a = zero → a = zero

/-- A nontrivial totally ordered integral domain. -/
class LinearOrderedDomain (R : Type) extends OrderedCommRing R where
  le_total : ∀ a b : R, le a b ∨ le b a
  mul_eq_zero : ∀ {a b : R}, mul a b = zero → a = zero ∨ b = zero
  zero_ne_one : (zero : R) ≠ one

namespace LinearOrderedDomain
variable {R : Type} [LinearOrderedDomain R]
open OrderedCommRing

theorem sq_nonneg' (a : R) : le zero (mul a a) := by
  rcases le_total zero a with h | h
  · exact mul_nonneg h h
  · have hn := neg_nonneg_of_nonpos h
    have h2 := mul_nonneg hn hn
    have e : mul (neg a) (neg a) = mul a a := by constructive_ring
    rw [e] at h2
    exact h2

theorem sq_eq_zero' {a : R} (h : mul a a = zero) : a = zero := by
  rcases mul_eq_zero h with h | h <;> exact h

instance toFormallyRealRing : FormallyRealRing R where
  sq_nonneg := sq_nonneg'
  sq_eq_zero := sq_eq_zero'

theorem mul_pos {a b : R} (ha : IsPos a) (hb : IsPos b) : IsPos (mul a b) :=
  ⟨mul_nonneg ha.nonneg hb.nonneg, fun h => by
    rcases mul_eq_zero h with h | h
    · exact ha.ne_zero h
    · exact hb.ne_zero h⟩

theorem one_pos : IsPos (one : R) :=
  ⟨by
    have h := sq_nonneg' (one : R)
    rw [LawfulCommRing.mul_one] at h
    exact h, fun h => zero_ne_one h.symm⟩

theorem eq_of_mul_eq_mul_right {a b c : R} (hc : c ≠ zero) (h : mul a c = mul b c) : a = b := by
  have e : mul (sub a b) c = sub (mul a c) (mul b c) := by constructive_ring
  rw [h, LawfulCommRing.sub_self] at e
  rcases mul_eq_zero e with h1 | h1
  · exact LawfulCommRing.sub_eq_zero_iff.mp h1
  · exact absurd h1 hc

theorem le_of_mul_le_mul_right {a b c : R} (hc : IsPos c) (h : le (mul a c) (mul b c)) :
    le a b := by
  rcases le_total a b with hab | hba
  · exact hab
  · have h1 := mul_le_mul_of_nonneg_right hba hc.nonneg
    exact le_of_eq (eq_of_mul_eq_mul_right hc.ne_zero (le_antisymm h h1))

/-- Square-root-free comparison: `y² ≤ x²` and `0 ≤ x` give `y ≤ x`. -/
theorem le_of_sq_le_sq {x y : R} (hx : le zero x) (h : le (mul y y) (mul x x)) : le y x := by
  rcases le_total y x with hyx | hxy
  · exact hyx
  · have hy : le zero y := le_trans hx hxy
    have h1 : le (mul x x) (mul x y) := mul_le_mul_of_nonneg_left hxy hx
    have h2 : le (mul x y) (mul y y) := mul_le_mul_of_nonneg_right hxy hy
    have e1 : mul x y = mul x x := le_antisymm (le_trans h2 h) h1
    have e2 : mul x (sub y x) = zero := by
      have e : mul x (sub y x) = sub (mul x y) (mul x x) := by constructive_ring
      rw [e, e1, LawfulCommRing.sub_self]
    rcases mul_eq_zero e2 with h0 | h0
    · subst h0
      rw [LawfulCommRing.mul_zero] at h
      exact le_of_eq (sq_eq_zero' (le_antisymm h (sq_nonneg' y)))
    · exact le_of_eq (LawfulCommRing.sub_eq_zero_iff.mp h0)

end LinearOrderedDomain

/-! ## 2. The integers -/

instance intCommRingOps : CommRingOps Int where
  zero := 0
  one := 1
  add := Int.add
  mul := Int.mul
  neg := Int.neg
  sub := Int.sub

instance intLawfulCommRing : LawfulCommRing Int where
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  add_left_neg := Int.add_left_neg
  sub_eq_add_neg := fun _ _ => Int.sub_eq_add_neg
  mul_assoc := Int.mul_assoc
  mul_comm := Int.mul_comm
  one_mul := Int.one_mul
  mul_one := Int.mul_one
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul

instance intOrderedCommRing : OrderedCommRing Int where
  le := Int.le
  le_refl := Int.le_refl
  le_trans := Int.le_trans
  le_antisymm := Int.le_antisymm
  add_le_add_left := fun c h => Int.add_le_add_left h c
  mul_nonneg := Int.mul_nonneg

instance intLinearOrderedDomain : LinearOrderedDomain Int where
  le_total := Int.le_total
  mul_eq_zero := Int.mul_eq_zero.mp
  zero_ne_one := by decide

/-! ## 3. Fractions with a positive denominator -/

/-- A numerator and a strictly positive denominator. -/
structure PosPreFrac (R : Type) [LinearOrderedDomain R] where
  num : R
  den : R
  den_pos : IsPos den

namespace PosPreFrac
variable {R : Type} [LinearOrderedDomain R]
open OrderedCommRing LinearOrderedDomain

/-- Cross-multiplied equality of fractions. -/
def rel (x y : PosPreFrac R) : Prop := mul x.num y.den = mul y.num x.den

theorem rel_refl (x : PosPreFrac R) : rel x x := by rfl

theorem rel_symm {x y : PosPreFrac R} (h : rel x y) : rel y x := by
  unfold rel at *
  exact h.symm

theorem rel_trans {x y z : PosPreFrac R} (h1 : rel x y) (h2 : rel y z) : rel x z := by
  unfold rel at *
  apply eq_of_mul_eq_mul_right y.den_pos.ne_zero
  have e1 : mul (mul x.num z.den) y.den = mul (mul x.num y.den) z.den := by constructive_ring
  have e2 : mul (mul z.num x.den) y.den = mul (mul z.num y.den) x.den := by constructive_ring
  rw [e1, e2, h1, ← h2]
  constructive_ring

instance setoid (R : Type) [LinearOrderedDomain R] : Setoid (PosPreFrac R) :=
  ⟨rel, ⟨rel_refl, rel_symm, rel_trans⟩⟩

def pzero : PosPreFrac R := ⟨zero, one, one_pos⟩
def pone : PosPreFrac R := ⟨one, one, one_pos⟩
def padd (x y : PosPreFrac R) : PosPreFrac R :=
  ⟨add (mul x.num y.den) (mul y.num x.den), mul x.den y.den, mul_pos x.den_pos y.den_pos⟩
def pmul (x y : PosPreFrac R) : PosPreFrac R :=
  ⟨mul x.num y.num, mul x.den y.den, mul_pos x.den_pos y.den_pos⟩
def pneg (x : PosPreFrac R) : PosPreFrac R := ⟨neg x.num, x.den, x.den_pos⟩
def ple (x y : PosPreFrac R) : Prop := le (mul x.num y.den) (mul y.num x.den)

theorem padd_congr {a a' c c' : PosPreFrac R} (h1 : rel a a') (h2 : rel c c') :
    rel (padd a c) (padd a' c') := by
  unfold rel at *
  dsimp only [padd]
  have e : mul (add (mul a.num c.den) (mul c.num a.den)) (mul a'.den c'.den) =
      add (mul (mul a.num a'.den) (mul c.den c'.den))
        (mul (mul c.num c'.den) (mul a.den a'.den)) := by constructive_ring
  rw [e, h1, h2]
  constructive_ring

theorem pmul_congr {a a' c c' : PosPreFrac R} (h1 : rel a a') (h2 : rel c c') :
    rel (pmul a c) (pmul a' c') := by
  unfold rel at *
  dsimp only [pmul]
  have e : mul (mul a.num c.num) (mul a'.den c'.den) =
      mul (mul a.num a'.den) (mul c.num c'.den) := by constructive_ring
  rw [e, h1, h2]
  constructive_ring

theorem pneg_congr {a a' : PosPreFrac R} (h1 : rel a a') : rel (pneg a) (pneg a') := by
  unfold rel at *
  dsimp only [pneg]
  have e : mul (neg a.num) a'.den = neg (mul a.num a'.den) := by constructive_ring
  rw [e, h1]
  constructive_ring

theorem ple_congr {a a' c c' : PosPreFrac R} (h1 : rel a a') (h2 : rel c c')
    (h : ple a c) : ple a' c' := by
  unfold rel at h1 h2
  unfold ple at h ⊢
  have hm := mul_le_mul_of_nonneg_right h (mul_pos a'.den_pos c'.den_pos).nonneg
  have e1 : mul (mul a.num c.den) (mul a'.den c'.den) =
      mul (mul a.num a'.den) (mul c.den c'.den) := by constructive_ring
  have e2 : mul (mul c.num a.den) (mul a'.den c'.den) =
      mul (mul c.num c'.den) (mul a.den a'.den) := by constructive_ring
  rw [e1, e2, h1, h2] at hm
  apply le_of_mul_le_mul_right (mul_pos a.den_pos c.den_pos)
  have e3 : mul (mul a'.num c'.den) (mul a.den c.den) =
      mul (mul a'.num a.den) (mul c.den c'.den) := by constructive_ring
  have e4 : mul (mul c'.num a'.den) (mul a.den c.den) =
      mul (mul c'.num c.den) (mul a.den a'.den) := by constructive_ring
  rw [e3, e4]
  exact hm

end PosPreFrac

/-- The fraction field of a linearly ordered domain; `PosFrac Int` is `ℚ`. -/
@[expose] def PosFrac (R : Type) [LinearOrderedDomain R] : Type := Quotient (PosPreFrac.setoid R)

namespace PosFrac
variable {R : Type} [LinearOrderedDomain R]
open OrderedCommRing LinearOrderedDomain PosPreFrac

def mk (x : PosPreFrac R) : PosFrac R := Quotient.mk _ x

theorem sound {x y : PosPreFrac R} (h : PosPreFrac.rel x y) : mk x = mk y := Quotient.sound h

theorem exact {x y : PosPreFrac R} (h : mk x = mk y) : PosPreFrac.rel x y := Quotient.exact h

theorem ind {p : PosFrac R → Prop} (h : ∀ x, p (mk x)) (q : PosFrac R) : p q :=
  Quotient.inductionOn q h

def fadd (p q : PosFrac R) : PosFrac R :=
  Quotient.liftOn₂ p q (fun x y => mk (padd x y)) (fun _ _ _ _ h1 h2 => sound (padd_congr h1 h2))
def fmul (p q : PosFrac R) : PosFrac R :=
  Quotient.liftOn₂ p q (fun x y => mk (pmul x y)) (fun _ _ _ _ h1 h2 => sound (pmul_congr h1 h2))
def fneg (p : PosFrac R) : PosFrac R :=
  Quotient.liftOn p (fun x => mk (pneg x)) (fun _ _ h => sound (pneg_congr h))
def fle (p q : PosFrac R) : Prop :=
  Quotient.liftOn₂ p q ple (fun _ _ _ _ h1 h2 =>
    propext ⟨ple_congr h1 h2, ple_congr (rel_symm h1) (rel_symm h2)⟩)

instance commRingOps : CommRingOps (PosFrac R) where
  zero := mk pzero
  one := mk pone
  add := fadd
  mul := fmul
  neg := fneg
  sub p q := fadd p (fneg q)

theorem add_mk (x y : PosPreFrac R) : add (mk x) (mk y) = mk (padd x y) := by rfl
theorem mul_mk (x y : PosPreFrac R) : mul (mk x) (mk y) = mk (pmul x y) := by rfl
theorem neg_mk (x : PosPreFrac R) : neg (mk x) = mk (pneg x) := by rfl
theorem zero_mk : (zero : PosFrac R) = mk pzero := by rfl
theorem one_mk : (one : PosFrac R) = mk pone := by rfl
theorem fle_mk (x y : PosPreFrac R) : fle (mk x) (mk y) = ple x y := by rfl

instance lawfulCommRing : LawfulCommRing (PosFrac R) where
  add_assoc a b c := by
    induction a using ind with | h x => ?_
    induction b using ind with | h y => ?_
    induction c using ind with | h z => ?_
    rw [add_mk, add_mk, add_mk, add_mk]
    apply sound
    dsimp only [rel, padd]
    constructive_ring
  add_comm a b := by
    induction a using ind with | h x => ?_
    induction b using ind with | h y => ?_
    rw [add_mk, add_mk]
    apply sound
    dsimp only [rel, padd]
    constructive_ring
  zero_add a := by
    induction a using ind with | h x => ?_
    rw [zero_mk, add_mk]
    apply sound
    dsimp only [rel, padd, pzero]
    constructive_ring
  add_zero a := by
    induction a using ind with | h x => ?_
    rw [zero_mk, add_mk]
    apply sound
    dsimp only [rel, padd, pzero]
    constructive_ring
  add_left_neg a := by
    induction a using ind with | h x => ?_
    rw [neg_mk, add_mk, zero_mk]
    apply sound
    dsimp only [rel, padd, pneg, pzero]
    constructive_ring
  sub_eq_add_neg _ _ := by rfl
  mul_assoc a b c := by
    induction a using ind with | h x => ?_
    induction b using ind with | h y => ?_
    induction c using ind with | h z => ?_
    rw [mul_mk, mul_mk, mul_mk, mul_mk]
    apply sound
    dsimp only [rel, pmul]
    constructive_ring
  mul_comm a b := by
    induction a using ind with | h x => ?_
    induction b using ind with | h y => ?_
    rw [mul_mk, mul_mk]
    apply sound
    dsimp only [rel, pmul]
    constructive_ring
  one_mul a := by
    induction a using ind with | h x => ?_
    rw [one_mk, mul_mk]
    apply sound
    dsimp only [rel, pmul, pone]
    constructive_ring
  mul_one a := by
    induction a using ind with | h x => ?_
    rw [one_mk, mul_mk]
    apply sound
    dsimp only [rel, pmul, pone]
    constructive_ring
  left_distrib a b c := by
    induction a using ind with | h x => ?_
    induction b using ind with | h y => ?_
    induction c using ind with | h z => ?_
    rw [add_mk, mul_mk, mul_mk, mul_mk, add_mk]
    apply sound
    dsimp only [rel, pmul, padd]
    constructive_ring
  right_distrib a b c := by
    induction a using ind with | h x => ?_
    induction b using ind with | h y => ?_
    induction c using ind with | h z => ?_
    rw [add_mk, mul_mk, mul_mk, mul_mk, add_mk]
    apply sound
    dsimp only [rel, pmul, padd]
    constructive_ring

theorem ple_zero_iff (x : PosPreFrac R) : ple pzero x ↔ le zero x.num := by
  unfold ple
  dsimp only [pzero]
  rw [LawfulCommRing.zero_mul, LawfulCommRing.mul_one]

instance orderedCommRing : OrderedCommRing (PosFrac R) where
  le := fle
  le_refl a := by
    induction a using ind with | h x => ?_
    rw [fle_mk]
    exact le_refl _
  le_trans {a b c} hab hbc := by
    induction a using ind with | h x => ?_
    induction b using ind with | h y => ?_
    induction c using ind with | h z => ?_
    rw [fle_mk] at hab hbc ⊢
    unfold ple at *
    apply le_of_mul_le_mul_right y.den_pos
    have s1 := mul_le_mul_of_nonneg_right hab z.den_pos.nonneg
    have s2 := mul_le_mul_of_nonneg_right hbc x.den_pos.nonneg
    have e1 : mul (mul x.num z.den) y.den = mul (mul x.num y.den) z.den := by constructive_ring
    have e2 : mul (mul y.num x.den) z.den = mul (mul y.num z.den) x.den := by constructive_ring
    have e3 : mul (mul z.num x.den) y.den = mul (mul z.num y.den) x.den := by constructive_ring
    rw [e1, e3]
    rw [e2] at s1
    exact le_trans s1 s2
  le_antisymm {a b} hab hba := by
    induction a using ind with | h x => ?_
    induction b using ind with | h y => ?_
    rw [fle_mk] at hab hba
    exact sound (le_antisymm hab hba)
  add_le_add_left {a b} c hab := by
    induction a using ind with | h x => ?_
    induction b using ind with | h y => ?_
    induction c using ind with | h z => ?_
    rw [fle_mk] at hab
    rw [add_mk, add_mk, fle_mk]
    unfold ple at *
    dsimp only [padd]
    have s := mul_le_mul_of_nonneg_right hab (sq_nonneg' z.den)
    have s2 := add_le_add_left (mul (mul z.num z.den) (mul x.den y.den)) s
    have e1 : mul (add (mul z.num x.den) (mul x.num z.den)) (mul z.den y.den) =
        add (mul (mul z.num z.den) (mul x.den y.den))
          (mul (mul x.num y.den) (mul z.den z.den)) := by constructive_ring
    have e2 : mul (add (mul z.num y.den) (mul y.num z.den)) (mul z.den x.den) =
        add (mul (mul z.num z.den) (mul x.den y.den))
          (mul (mul y.num x.den) (mul z.den z.den)) := by constructive_ring
    rw [e1, e2]
    exact s2
  mul_nonneg {a b} ha hb := by
    induction a using ind with | h x => ?_
    induction b using ind with | h y => ?_
    rw [zero_mk, fle_mk, ple_zero_iff] at ha hb
    rw [zero_mk, mul_mk, fle_mk, ple_zero_iff]
    exact mul_nonneg ha hb

instance linearOrderedDomain : LinearOrderedDomain (PosFrac R) where
  le_total a b := by
    induction a using ind with | h x => ?_
    induction b using ind with | h y => ?_
    exact le_total (mul x.num y.den) (mul y.num x.den)
  mul_eq_zero {a b} h := by
    induction a using ind with | h x => ?_
    induction b using ind with | h y => ?_
    rw [mul_mk, zero_mk] at h
    have h1 := exact h
    unfold rel at h1
    dsimp only [pmul, pzero] at h1
    rw [LawfulCommRing.mul_one, LawfulCommRing.zero_mul] at h1
    rcases mul_eq_zero h1 with h0 | h0
    · left
      rw [zero_mk]
      apply sound
      unfold rel
      dsimp only [pzero]
      rw [h0, LawfulCommRing.zero_mul, LawfulCommRing.zero_mul]
    · right
      rw [zero_mk]
      apply sound
      unfold rel
      dsimp only [pzero]
      rw [h0, LawfulCommRing.zero_mul, LawfulCommRing.zero_mul]
  zero_ne_one h := by
    rw [zero_mk, one_mk] at h
    have h1 := exact h
    unfold rel at h1
    dsimp only [pzero, pone] at h1
    rw [LawfulCommRing.mul_one, LawfulCommRing.mul_one] at h1
    exact zero_ne_one h1

/-- The embedding of the base ring. -/
def ofBase (r : R) : PosFrac R := mk ⟨r, one, one_pos⟩

/-- The fraction `n / d` for a positive `d`. -/
def frac (n d : R) (hd : IsPos d) : PosFrac R := mk ⟨n, d, hd⟩

theorem ofBase_add (r s : R) : ofBase (add r s) = add (ofBase r) (ofBase s) := by
  unfold ofBase
  rw [add_mk]
  apply sound
  dsimp only [rel, padd]
  constructive_ring

theorem ofBase_mul (r s : R) : ofBase (mul r s) = mul (ofBase r) (ofBase s) := by
  unfold ofBase
  rw [mul_mk]
  apply sound
  dsimp only [rel, pmul]
  constructive_ring

theorem ofBase_injective {r s : R} (h : ofBase r = ofBase s) : r = s := by
  have h1 := exact h
  unfold rel at h1
  dsimp only at h1
  rw [LawfulCommRing.mul_one, LawfulCommRing.mul_one] at h1
  exact h1

/-- Every positive element of the base ring becomes invertible: `d * (n / d) = n`. -/
theorem ofBase_mul_frac (n d : R) (hd : IsPos d) : mul (ofBase d) (frac n d hd) = ofBase n := by
  unfold ofBase frac
  rw [mul_mk]
  apply sound
  dsimp only [rel, pmul]
  constructive_ring

theorem frac_eq_iff (n d n' d' : R) (hd : IsPos d) (hd' : IsPos d') :
    frac n d hd = frac n' d' hd' ↔ mul n d' = mul n' d :=
  ⟨fun h => exact h, fun h => sound h⟩

theorem ofBase_le_iff (r s : R) : le (ofBase r) (ofBase s) ↔ le r s := by
  show ple _ _ ↔ _
  unfold ple
  dsimp only
  rw [LawfulCommRing.mul_one, LawfulCommRing.mul_one]

end PosFrac

/-! ## 4. Quadratic radical extensions `R[√d]` -/

/-- `a + b √d` over `R`. The radicand is a type parameter, so `QuadExt R d` is `R[X]/(X² - d)`. -/
structure QuadExt (R : Type) (d : R) where
  a : R
  b : R
  deriving DecidableEq

namespace QuadExt
variable {R : Type}

theorem ext' {d : R} {x y : QuadExt R d} (ha : x.a = y.a) (hb : x.b = y.b) : x = y := by
  cases x; cases y; cases ha; cases hb; rfl

instance commRingOps [CommRingOps R] (d : R) : CommRingOps (QuadExt R d) where
  zero := ⟨zero, zero⟩
  one := ⟨one, zero⟩
  add x y := ⟨add x.a y.a, add x.b y.b⟩
  mul x y := ⟨add (mul x.a y.a) (mul d (mul x.b y.b)), add (mul x.a y.b) (mul x.b y.a)⟩
  neg x := ⟨neg x.a, neg x.b⟩
  sub x y := ⟨sub x.a y.a, sub x.b y.b⟩

section Coordinates
variable [CommRingOps R] {d : R}
theorem zero_a : (zero : QuadExt R d).a = zero := by rfl
theorem zero_b : (zero : QuadExt R d).b = zero := by rfl
theorem one_a : (one : QuadExt R d).a = one := by rfl
theorem one_b : (one : QuadExt R d).b = zero := by rfl
theorem add_a (x y : QuadExt R d) : (add x y).a = add x.a y.a := by rfl
theorem add_b (x y : QuadExt R d) : (add x y).b = add x.b y.b := by rfl
theorem mul_a (x y : QuadExt R d) :
    (mul x y).a = add (mul x.a y.a) (mul d (mul x.b y.b)) := by rfl
theorem mul_b (x y : QuadExt R d) : (mul x y).b = add (mul x.a y.b) (mul x.b y.a) := by rfl
theorem neg_a (x : QuadExt R d) : (neg x).a = neg x.a := by rfl
theorem neg_b (x : QuadExt R d) : (neg x).b = neg x.b := by rfl
theorem sub_a (x y : QuadExt R d) : (sub x y).a = sub x.a y.a := by rfl
theorem sub_b (x y : QuadExt R d) : (sub x y).b = sub x.b y.b := by rfl
end Coordinates

instance lawfulCommRing [LawfulCommRing R] (d : R) : LawfulCommRing (QuadExt R d) where
  add_assoc _ _ _ := by apply ext' <;> simp only [add_a, add_b] <;> constructive_ring
  add_comm _ _ := by apply ext' <;> simp only [add_a, add_b] <;> constructive_ring
  zero_add _ := by apply ext' <;> simp only [add_a, add_b, zero_a, zero_b] <;> constructive_ring
  add_zero _ := by apply ext' <;> simp only [add_a, add_b, zero_a, zero_b] <;> constructive_ring
  add_left_neg _ := by
    apply ext' <;> simp only [add_a, add_b, neg_a, neg_b, zero_a, zero_b] <;> constructive_ring
  sub_eq_add_neg _ _ := by
    apply ext' <;> simp only [add_a, add_b, neg_a, neg_b, sub_a, sub_b] <;> constructive_ring
  mul_assoc _ _ _ := by
    apply ext' <;> simp only [mul_a, mul_b] <;> constructive_ring
  mul_comm _ _ := by apply ext' <;> simp only [mul_a, mul_b] <;> constructive_ring
  one_mul _ := by apply ext' <;> simp only [mul_a, mul_b, one_a, one_b] <;> constructive_ring
  mul_one _ := by apply ext' <;> simp only [mul_a, mul_b, one_a, one_b] <;> constructive_ring
  left_distrib _ _ _ := by
    apply ext' <;> simp only [mul_a, mul_b, add_a, add_b] <;> constructive_ring
  right_distrib _ _ _ := by
    apply ext' <;> simp only [mul_a, mul_b, add_a, add_b] <;> constructive_ring

/-- The embedding `r ↦ r + 0 √d`. -/
def ofBase [CommRingOps R] {d : R} (r : R) : QuadExt R d := ⟨r, zero⟩

/-- The adjoined root `√d`. -/
def sqrtd [CommRingOps R] {d : R} : QuadExt R d := ⟨zero, one⟩

theorem sqrtd_mul_self [LawfulCommRing R] (d : R) :
    mul (sqrtd : QuadExt R d) sqrtd = ofBase d := by
  apply ext' <;> simp only [mul_a, mul_b, sqrtd, ofBase] <;> constructive_ring

end QuadExt

/-- The radicand of a real quadratic extension is strictly positive. -/
class PosRadicand {R : Type} [LinearOrderedDomain R] (d : R) : Prop where
  pos : IsPos d

namespace QuadExt
variable {R : Type} [LinearOrderedDomain R] {d : R} [PosRadicand d]
open OrderedCommRing LinearOrderedDomain

/-- Total positivity: `a + b√d` is nonnegative under both embeddings `√d ↦ ±√d`. -/
def nonneg (x : QuadExt R d) : Prop :=
  le zero x.a ∧ le (mul d (mul x.b x.b)) (mul x.a x.a)

theorem radicand_sq_nonneg (b : R) : le zero (mul d (mul b b)) :=
  mul_nonneg (PosRadicand.pos (d := d)).nonneg (sq_nonneg' b)

omit [PosRadicand d] in
theorem nonneg_zero : nonneg (zero : QuadExt R d) := by
  unfold nonneg
  simp only [zero_a, zero_b]
  rw [LawfulCommRing.mul_zero, LawfulCommRing.mul_zero]
  exact ⟨le_refl _, le_refl _⟩

theorem cross_le {x y : QuadExt R d} (hx : nonneg x) (hy : nonneg y) :
    le (mul d (mul x.b y.b)) (mul x.a y.a) := by
  apply le_of_sq_le_sq (mul_nonneg hx.1 hy.1)
  have h := mul_le_mul_nonneg hx.2 hy.2 (radicand_sq_nonneg x.b) (sq_nonneg' y.a)
  have e1 : mul (mul d (mul x.b y.b)) (mul d (mul x.b y.b)) =
      mul (mul d (mul x.b x.b)) (mul d (mul y.b y.b)) := by constructive_ring
  have e2 : mul (mul x.a y.a) (mul x.a y.a) = mul (mul x.a x.a) (mul y.a y.a) := by
    constructive_ring
  rw [e1, e2]
  exact h

theorem neg_cross_le {x y : QuadExt R d} (hx : nonneg x) (hy : nonneg y) :
    le (neg (mul d (mul x.b y.b))) (mul x.a y.a) := by
  apply le_of_sq_le_sq (mul_nonneg hx.1 hy.1)
  have h := mul_le_mul_nonneg hx.2 hy.2 (radicand_sq_nonneg x.b) (sq_nonneg' y.a)
  have e1 : mul (neg (mul d (mul x.b y.b))) (neg (mul d (mul x.b y.b))) =
      mul (mul d (mul x.b x.b)) (mul d (mul y.b y.b)) := by constructive_ring
  have e2 : mul (mul x.a y.a) (mul x.a y.a) = mul (mul x.a x.a) (mul y.a y.a) := by
    constructive_ring
  rw [e1, e2]
  exact h

theorem nonneg_add {x y : QuadExt R d} (hx : nonneg x) (hy : nonneg y) : nonneg (add x y) := by
  refine ⟨?_, ?_⟩
  · rw [add_a]
    exact add_nonneg hx.1 hy.1
  · rw [add_a, add_b]
    have c := cross_le hx hy
    have e1 : mul d (mul (add x.b y.b) (add x.b y.b)) =
        add (add (mul d (mul x.b x.b)) (mul d (mul y.b y.b)))
          (add (mul d (mul x.b y.b)) (mul d (mul x.b y.b))) := by constructive_ring
    have e2 : mul (add x.a y.a) (add x.a y.a) =
        add (add (mul x.a x.a) (mul y.a y.a)) (add (mul x.a y.a) (mul x.a y.a)) := by
      constructive_ring
    rw [e1, e2]
    exact add_le_add (add_le_add hx.2 hy.2) (add_le_add c c)

theorem nonneg_mul {x y : QuadExt R d} (hx : nonneg x) (hy : nonneg y) : nonneg (mul x y) := by
  refine ⟨?_, ?_⟩
  · rw [mul_a]
    have h := sub_nonneg_of_le (neg_cross_le hx hy)
    have e : sub (mul x.a y.a) (neg (mul d (mul x.b y.b))) =
        add (mul x.a y.a) (mul d (mul x.b y.b)) := by constructive_ring
    rw [e] at h
    exact h
  · rw [mul_a, mul_b]
    apply le_of_sub_nonneg
    have h := mul_nonneg (sub_nonneg_of_le hx.2) (sub_nonneg_of_le hy.2)
    have e : mul (sub (mul x.a x.a) (mul d (mul x.b x.b)))
        (sub (mul y.a y.a) (mul d (mul y.b y.b))) =
        sub (mul (add (mul x.a y.a) (mul d (mul x.b y.b))) (add (mul x.a y.a) (mul d (mul x.b y.b))))
          (mul d (mul (add (mul x.a y.b) (mul x.b y.a)) (add (mul x.a y.b) (mul x.b y.a)))) := by
      constructive_ring
    rw [e] at h
    exact h

theorem eq_zero_of_nonneg_of_neg_nonneg {x : QuadExt R d} (hx : nonneg x)
    (hn : nonneg (neg x)) : x = zero := by
  have ha : x.a = zero := by
    have h1 := hn.1
    rw [neg_a] at h1
    exact le_antisymm (nonpos_of_neg_nonneg h1) hx.1
  have hb : x.b = zero := by
    have h2 := hx.2
    rw [ha, LawfulCommRing.mul_zero] at h2
    rcases mul_eq_zero (le_antisymm h2 (radicand_sq_nonneg x.b)) with h0 | h0
    · exact absurd h0 (PosRadicand.pos (d := d)).ne_zero
    · exact sq_eq_zero' h0
  exact ext' (by rw [ha, zero_a]) (by rw [hb, zero_b])

instance orderedCommRing : OrderedCommRing (QuadExt R d) where
  le x y := nonneg (sub y x)
  le_refl x := by
    rw [LawfulCommRing.sub_self]
    exact nonneg_zero
  le_trans {x y z} hxy hyz := by
    have h := nonneg_add hyz hxy
    have e : add (sub z y) (sub y x) = sub z x := by constructive_ring
    rw [e] at h
    exact h
  le_antisymm {x y} hxy hyx := by
    have e : sub x y = neg (sub y x) := by constructive_ring
    rw [e] at hyx
    have h0 := eq_zero_of_nonneg_of_neg_nonneg hxy hyx
    exact (LawfulCommRing.sub_eq_zero_iff.mp h0).symm
  add_le_add_left {x y} c h := by
    have e : sub (add c y) (add c x) = sub y x := by constructive_ring
    rw [e]
    exact h
  mul_nonneg {x y} hx hy := by
    rw [LawfulCommRing.sub_zero] at hx hy ⊢
    exact nonneg_mul hx hy

theorem nonneg_sq (x : QuadExt R d) : nonneg (mul x x) := by
  refine ⟨?_, ?_⟩
  · rw [mul_a]
    exact add_nonneg (sq_nonneg' x.a) (radicand_sq_nonneg x.b)
  · rw [mul_a, mul_b]
    apply le_of_sub_nonneg
    have h := sq_nonneg' (sub (mul x.a x.a) (mul d (mul x.b x.b)))
    have e : mul (sub (mul x.a x.a) (mul d (mul x.b x.b))) (sub (mul x.a x.a) (mul d (mul x.b x.b))) =
        sub (mul (add (mul x.a x.a) (mul d (mul x.b x.b))) (add (mul x.a x.a) (mul d (mul x.b x.b))))
          (mul d (mul (add (mul x.a x.b) (mul x.b x.a)) (add (mul x.a x.b) (mul x.b x.a)))) := by
      constructive_ring
    rw [e] at h
    exact h

instance formallyRealRing : FormallyRealRing (QuadExt R d) where
  sq_nonneg x := by
    show nonneg (sub (mul x x) zero)
    rw [LawfulCommRing.sub_zero]
    exact nonneg_sq x
  sq_eq_zero {x} h := by
    have h1 := congrArg QuadExt.a h
    rw [mul_a, zero_a] at h1
    have ha := sq_eq_zero' (eq_zero_of_add_eq_zero_left (sq_nonneg' x.a) (radicand_sq_nonneg x.b) h1)
    have hb0 := eq_zero_of_add_eq_zero_right (sq_nonneg' x.a) (radicand_sq_nonneg x.b) h1
    have hb : x.b = zero := by
      rcases mul_eq_zero hb0 with h0 | h0
      · exact absurd h0 (PosRadicand.pos (d := d)).ne_zero
      · exact sq_eq_zero' h0
    exact ext' (by rw [ha, zero_a]) (by rw [hb, zero_b])

end QuadExt

/-! ## 5. Complexification and the amplitude-ring class -/

/-- `re + im · i` over `R`. -/
structure Complexified (R : Type) where
  re : R
  im : R
  deriving DecidableEq

namespace Complexified
variable {R : Type}

theorem ext' {z w : Complexified R} (hr : z.re = w.re) (hi : z.im = w.im) : z = w := by
  cases z; cases w; cases hr; cases hi; rfl

instance commRingOps [CommRingOps R] : CommRingOps (Complexified R) where
  zero := ⟨zero, zero⟩
  one := ⟨one, zero⟩
  add z w := ⟨add z.re w.re, add z.im w.im⟩
  mul z w := ⟨sub (mul z.re w.re) (mul z.im w.im), add (mul z.re w.im) (mul z.im w.re)⟩
  neg z := ⟨neg z.re, neg z.im⟩
  sub z w := ⟨sub z.re w.re, sub z.im w.im⟩

section Coordinates
variable [CommRingOps R]
theorem zero_re : (zero : Complexified R).re = zero := by rfl
theorem zero_im : (zero : Complexified R).im = zero := by rfl
theorem one_re : (one : Complexified R).re = one := by rfl
theorem one_im : (one : Complexified R).im = zero := by rfl
theorem add_re (z w : Complexified R) : (add z w).re = add z.re w.re := by rfl
theorem add_im (z w : Complexified R) : (add z w).im = add z.im w.im := by rfl
theorem mul_re (z w : Complexified R) :
    (mul z w).re = sub (mul z.re w.re) (mul z.im w.im) := by rfl
theorem mul_im (z w : Complexified R) :
    (mul z w).im = add (mul z.re w.im) (mul z.im w.re) := by rfl
theorem neg_re (z : Complexified R) : (neg z).re = neg z.re := by rfl
theorem neg_im (z : Complexified R) : (neg z).im = neg z.im := by rfl
theorem sub_re (z w : Complexified R) : (sub z w).re = sub z.re w.re := by rfl
theorem sub_im (z w : Complexified R) : (sub z w).im = sub z.im w.im := by rfl
end Coordinates

instance lawfulCommRing [LawfulCommRing R] : LawfulCommRing (Complexified R) where
  add_assoc _ _ _ := by apply ext' <;> simp only [add_re, add_im] <;> constructive_ring
  add_comm _ _ := by apply ext' <;> simp only [add_re, add_im] <;> constructive_ring
  zero_add _ := by
    apply ext' <;> simp only [add_re, add_im, zero_re, zero_im] <;> constructive_ring
  add_zero _ := by
    apply ext' <;> simp only [add_re, add_im, zero_re, zero_im] <;> constructive_ring
  add_left_neg _ := by
    apply ext' <;> simp only [add_re, add_im, neg_re, neg_im, zero_re, zero_im] <;>
      constructive_ring
  sub_eq_add_neg _ _ := by
    apply ext' <;> simp only [add_re, add_im, neg_re, neg_im, sub_re, sub_im] <;>
      constructive_ring
  mul_assoc _ _ _ := by apply ext' <;> simp only [mul_re, mul_im] <;> constructive_ring
  mul_comm _ _ := by apply ext' <;> simp only [mul_re, mul_im] <;> constructive_ring
  one_mul _ := by
    apply ext' <;> simp only [mul_re, mul_im, one_re, one_im] <;> constructive_ring
  mul_one _ := by
    apply ext' <;> simp only [mul_re, mul_im, one_re, one_im] <;> constructive_ring
  left_distrib _ _ _ := by
    apply ext' <;> simp only [mul_re, mul_im, add_re, add_im] <;> constructive_ring
  right_distrib _ _ _ := by
    apply ext' <;> simp only [mul_re, mul_im, add_re, add_im] <;> constructive_ring

/-- The imaginary unit. -/
def I [CommRingOps R] : Complexified R := ⟨zero, one⟩

theorem I_mul_I [LawfulCommRing R] : mul (I : Complexified R) I = neg one := by
  apply ext' <;> simp only [mul_re, mul_im, neg_re, neg_im, one_re, one_im, I] <;>
    constructive_ring

end Complexified

/-- **Constructive amplitude ring.** A commutative `*`-ring `A` over an ordered commutative
    ring `R`: an involution `star`, a ring embedding `ofReal : R → A` and a squared modulus
    `normSq : A → R` with `z * star z = ofReal (normSq z)`, nonnegative and definite. No square
    root, no division and no decidable equality is assumed. -/
class ConstructiveAmplitudeRing (R : outParam Type) (A : Type) [OrderedCommRing R]
    extends LawfulCommRing A where
  star : A → A
  ofReal : R → A
  normSq : A → R
  star_add : ∀ z w : A, star (add z w) = add (star z) (star w)
  star_mul : ∀ z w : A, star (mul z w) = mul (star z) (star w)
  star_star : ∀ z : A, star (star z) = z
  ofReal_add : ∀ r s : R, ofReal (CommRingOps.add r s) = add (ofReal r) (ofReal s)
  ofReal_mul : ∀ r s : R, ofReal (CommRingOps.mul r s) = mul (ofReal r) (ofReal s)
  ofReal_one : ofReal CommRingOps.one = one
  ofReal_injective : ∀ {r s : R}, ofReal r = ofReal s → r = s
  star_ofReal : ∀ r : R, star (ofReal r) = ofReal r
  mul_star_self : ∀ z : A, mul z (star z) = ofReal (normSq z)
  normSq_nonneg : ∀ z : A, OrderedCommRing.le CommRingOps.zero (normSq z)
  normSq_eq_zero : ∀ {z : A}, normSq z = CommRingOps.zero → z = zero

namespace ConstructiveAmplitudeRing
variable {R A : Type} [OrderedCommRing R] [ConstructiveAmplitudeRing R A]
open OrderedCommRing

theorem ofReal_zero : (ofReal (zero : R) : A) = zero := by
  have h := ofReal_add (A := A) (zero : R) zero
  rw [LawfulCommRing.add_zero] at h
  apply LawfulCommRing.add_left_cancel (a := (ofReal (zero : R) : A))
  rw [LawfulCommRing.add_zero]
  exact h.symm

theorem ofReal_neg (r : R) : (ofReal (neg r) : A) = neg (ofReal r) := by
  apply LawfulCommRing.add_left_cancel (a := (ofReal r : A))
  rw [← ofReal_add, LawfulCommRing.add_right_neg, ofReal_zero, LawfulCommRing.add_right_neg]

theorem ofReal_sub (r s : R) : (ofReal (sub r s) : A) = sub (ofReal r) (ofReal s) := by
  rw [LawfulCommRing.sub_eq_add_neg, ofReal_add, ofReal_neg, ← LawfulCommRing.sub_eq_add_neg]

theorem star_zero : star (zero : A) = zero := by
  have h := star_add (R := R) (zero : A) zero
  rw [LawfulCommRing.add_zero] at h
  apply LawfulCommRing.add_left_cancel (a := star (zero : A))
  rw [LawfulCommRing.add_zero]
  exact h.symm

theorem star_neg (z : A) : star (neg z) = neg (star z) := by
  apply LawfulCommRing.add_left_cancel (a := star z)
  rw [← star_add, LawfulCommRing.add_right_neg, star_zero (R := R),
    LawfulCommRing.add_right_neg]

theorem star_sub (z w : A) : star (sub z w) = sub (star z) (star w) := by
  rw [LawfulCommRing.sub_eq_add_neg, star_add, star_neg, ← LawfulCommRing.sub_eq_add_neg]

theorem star_one : star (one : A) = one := by
  have h := star_mul (R := R) (one : A) (star one)
  rw [LawfulCommRing.one_mul, star_star, LawfulCommRing.mul_one] at h
  exact h.symm

/-- The squared modulus is multiplicative. -/
theorem normSq_mul (z w : A) : normSq (mul z w) = mul (normSq z) (normSq w) := by
  apply ofReal_injective (A := A)
  rw [ofReal_mul, ← mul_star_self, ← mul_star_self, ← mul_star_self, star_mul]
  constructive_ring

theorem normSq_zero : normSq (zero : A) = (zero : R) := by
  apply ofReal_injective (A := A)
  rw [← mul_star_self, ofReal_zero, LawfulCommRing.zero_mul]

/-- Definiteness. -/
theorem normSq_eq_zero_iff (z : A) : normSq z = (zero : R) ↔ z = zero :=
  ⟨fun h => normSq_eq_zero h, fun h => by rw [h, normSq_zero]⟩

theorem normSq_one : normSq (one : A) = (one : R) := by
  apply ofReal_injective (A := A)
  rw [← mul_star_self, ofReal_one, star_one (R := R), LawfulCommRing.mul_one]

theorem normSq_star (z : A) : normSq (star z) = normSq z := by
  apply ofReal_injective (A := A)
  rw [← mul_star_self, ← mul_star_self, star_star, LawfulCommRing.mul_comm]

theorem normSq_neg (z : A) : normSq (neg z) = normSq z := by
  apply ofReal_injective (A := A)
  rw [← mul_star_self, ← mul_star_self, star_neg]
  constructive_ring

theorem normSq_ofReal (r : R) : normSq (ofReal r : A) = mul r r := by
  apply ofReal_injective (A := A)
  rw [← mul_star_self, star_ofReal, ofReal_mul]

/-- **Parallelogram law** `|u + v|² + |u - v|² = (|u|² + |v|²) + (|u|² + |v|²)`. -/
theorem normSq_parallelogram (u v : A) :
    add (normSq (add u v)) (normSq (sub u v)) =
      add (add (normSq u) (normSq v)) (add (normSq u) (normSq v)) := by
  apply ofReal_injective (A := A)
  rw [ofReal_add, ofReal_add, ofReal_add, ← mul_star_self, ← mul_star_self, ← mul_star_self,
    ← mul_star_self, star_add, star_sub]
  constructive_ring

/-- The parallelogram law with the factor two spelled as `1 + 1`. -/
theorem normSq_parallelogram_two (u v : A) :
    add (normSq (add u v)) (normSq (sub u v)) =
      mul (add one one) (add (normSq u) (normSq v)) := by
  rw [normSq_parallelogram]
  constructive_ring

theorem normSq_add_le (u v : A) :
    le (normSq (add u v)) (add (add (normSq u) (normSq v)) (add (normSq u) (normSq v))) := by
  rw [← normSq_parallelogram]
  exact le_add_of_nonneg_right (normSq_nonneg _)

theorem normSq_sub_le (u v : A) :
    le (normSq (sub u v)) (add (add (normSq u) (normSq v)) (add (normSq u) (normSq v))) := by
  rw [← normSq_parallelogram, LawfulCommRing.add_comm]
  exact le_add_of_nonneg_right (normSq_nonneg _)

end ConstructiveAmplitudeRing

namespace Complexified
variable {R : Type} [FormallyRealRing R]
open OrderedCommRing

/-- `R[i]` is an amplitude ring over every formally real `R`. -/
instance amplitudeRing : ConstructiveAmplitudeRing R (Complexified R) where
  star z := ⟨z.re, neg z.im⟩
  ofReal r := ⟨r, zero⟩
  normSq z := add (mul z.re z.re) (mul z.im z.im)
  star_add _ _ := by apply ext' <;> simp only [add_re, add_im] <;> constructive_ring
  star_mul _ _ := by apply ext' <;> simp only [mul_re, mul_im] <;> constructive_ring
  star_star _ := by apply ext' <;> simp only <;> constructive_ring
  ofReal_add _ _ := by apply ext' <;> simp only [add_re, add_im] <;> constructive_ring
  ofReal_mul _ _ := by apply ext' <;> simp only [mul_re, mul_im] <;> constructive_ring
  ofReal_one := by rfl
  ofReal_injective h := congrArg Complexified.re h
  star_ofReal _ := by apply ext' <;> simp only <;> constructive_ring
  mul_star_self _ := by apply ext' <;> simp only [mul_re, mul_im] <;> constructive_ring
  normSq_nonneg z := add_nonneg (FormallyRealRing.sq_nonneg z.re) (FormallyRealRing.sq_nonneg z.im)
  normSq_eq_zero {z} h := by
    have hr := FormallyRealRing.sq_eq_zero (eq_zero_of_add_eq_zero_left
      (FormallyRealRing.sq_nonneg z.re) (FormallyRealRing.sq_nonneg z.im) h)
    have hi := FormallyRealRing.sq_eq_zero (eq_zero_of_add_eq_zero_right
      (FormallyRealRing.sq_nonneg z.re) (FormallyRealRing.sq_nonneg z.im) h)
    exact ext' (by rw [hr, zero_re]) (by rw [hi, zero_im])

theorem star_re (z : Complexified R) : (ConstructiveAmplitudeRing.star z).re = z.re := by rfl
theorem star_im (z : Complexified R) : (ConstructiveAmplitudeRing.star z).im = neg z.im := by rfl
theorem ofReal_re (r : R) : (ConstructiveAmplitudeRing.ofReal r : Complexified R).re = r := by rfl
theorem ofReal_im (r : R) :
    (ConstructiveAmplitudeRing.ofReal r : Complexified R).im = zero := by rfl
theorem normSq_eq (z : Complexified R) :
    ConstructiveAmplitudeRing.normSq z = add (mul z.re z.re) (mul z.im z.im) := by rfl

end Complexified

/-- Real amplitudes: a formally real ring is an amplitude ring over itself with the trivial
    involution and `normSq z = z²`. Not a global instance; use it locally for real registers
    such as exact Hadamard circuits over `ℚ[√2]`. -/
@[reducible] def realAmplitudeRing (R : Type) [FormallyRealRing R] :
    ConstructiveAmplitudeRing R R where
  star z := z
  ofReal r := r
  normSq z := mul z z
  star_add _ _ := by rfl
  star_mul _ _ := by rfl
  star_star _ := by rfl
  ofReal_add _ _ := by rfl
  ofReal_mul _ _ := by rfl
  ofReal_one := by rfl
  ofReal_injective h := h
  star_ofReal _ := by rfl
  mul_star_self _ := by rfl
  normSq_nonneg z := FormallyRealRing.sq_nonneg z
  normSq_eq_zero h := FormallyRealRing.sq_eq_zero h

/-! ## 6. Concrete amplitude rings: `ℤ[i]`, `ℚ[i]`, `ℚ[√2]`, `ℚ[√2, i]` -/

/-- `ℚ` as the fraction field of `ℤ`. -/
abbrev RatQ : Type := PosFrac Int

/-- The Gaussian integers `ℤ[i]` as an amplitude ring over `ℤ`. -/
abbrev GaussIntRing : Type := Complexified Int

/-- The Gaussian rationals `ℚ[i]` as an amplitude ring over `ℚ`. -/
abbrev RatComplex : Type := Complexified RatQ

theorem isPos_int_of_pos {d : Int} (h : 0 < d) : IsPos d :=
  ⟨Int.le_of_lt h, fun e => by
    have h0 : (0 : Int) < 0 := by
      rw [e] at h
      exact h
    exact Int.lt_irrefl 0 h0⟩

/-- The rational `n / d` for a positive integer `d`. -/
def ratOfInts (n d : Int) (h : 0 < d) : RatQ := PosFrac.frac n d (isPos_int_of_pos h)

theorem ratOfInts_eq_iff (n d n' d' : Int) (h : 0 < d) (h' : 0 < d') :
    ratOfInts n d h = ratOfInts n' d' h' ↔ n * d' = n' * d :=
  PosFrac.frac_eq_iff n d n' d' _ _

/-- The exact unit-modulus amplitude `3/5 + 4/5 i ∈ ℚ[i]`. -/
def unitThreeFourFifths : RatComplex :=
  ⟨ratOfInts 3 5 (by decide), ratOfInts 4 5 (by decide)⟩

/-- `|3/5 + 4/5 i|² = 1` exactly: a rational phase with no square root and no rescaling. -/
theorem unitThreeFourFifths_normSq :
    ConstructiveAmplitudeRing.normSq unitThreeFourFifths = (one : RatQ) := by
  rw [Complexified.normSq_eq]
  exact PosFrac.sound (by unfold PosPreFrac.rel; decide)

/-- Its inverse is its conjugate. -/
theorem unitThreeFourFifths_mul_star :
    mul unitThreeFourFifths (ConstructiveAmplitudeRing.star unitThreeFourFifths) = one := by
  rw [ConstructiveAmplitudeRing.mul_star_self, unitThreeFourFifths_normSq,
    ConstructiveAmplitudeRing.ofReal_one]

theorem two_pow_emod_five_ne_zero (k : Nat) : (2 : Int) ^ k % 5 ≠ 0 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Int.pow_succ]
    generalize (2 : Int) ^ k = x at ih
    omega

/-- A rational `3 · 2^k / 5` is never an integer. -/
theorem three_fifths_not_dyadic (a : Int) (k : Nat) :
    ¬ (PosFrac.ofBase a = mul (PosFrac.ofBase ((2 : Int) ^ k)) (ratOfInts 3 5 (by decide))) := by
  intro h
  have h1 : a * (1 * 5) = (2 : Int) ^ k * 3 * 1 := PosFrac.exact h
  have h2 := two_pow_emod_five_ne_zero k
  generalize (2 : Int) ^ k = x at h1 h2
  omega

/-- **`ℚ[i]` strictly extends the dyadic Gaussian amplitudes.** No power of two clears the
    denominator of `3/5 + 4/5 i`: there are no Gaussian integer `z` and exponent `k` with
    `z = 2^k · (3/5 + 4/5 i)`, i.e. the amplitude is not of the form `z / 2^k`. -/
theorem unitThreeFourFifths_not_dyadic :
    ¬ ∃ (z : GaussIntRing) (k : Nat),
      (⟨PosFrac.ofBase z.re, PosFrac.ofBase z.im⟩ : RatComplex) =
        mul (ConstructiveAmplitudeRing.ofReal (PosFrac.ofBase ((2 : Int) ^ k)))
          unitThreeFourFifths := by
  rintro ⟨z, k, h⟩
  have hre := congrArg Complexified.re h
  rw [Complexified.mul_re, Complexified.ofReal_re, Complexified.ofReal_im,
    LawfulCommRing.zero_mul, LawfulCommRing.sub_zero] at hre
  exact three_fifths_not_dyadic z.re k hre

/-- `2` is a positive radicand in `ℚ`. -/
instance ratTwoPosRadicand : PosRadicand (PosFrac.ofBase (2 : Int) : RatQ) where
  pos := ⟨(PosFrac.ofBase_le_iff (0 : Int) 2).mpr (by show (0 : Int) ≤ 2; decide),
    fun h => absurd (PosFrac.ofBase_injective (s := (0 : Int)) h) (by decide)⟩

/-- `ℚ[√2]`, ordered by total positivity. -/
abbrev RatSqrt2 : Type := QuadExt RatQ (PosFrac.ofBase (2 : Int))

/-- `ℚ[√2, i] = ℚ(ζ₈)`: contains every Clifford+T amplitude and every rational phase. -/
abbrev CyclotomicEight : Type := Complexified RatSqrt2

/-- The exact Hadamard amplitude `1/√2 = √2 / 2 ∈ ℚ[√2]`. -/
def invSqrtTwo : RatSqrt2 := ⟨zero, ratOfInts 1 2 (by decide)⟩

/-- `(1/√2)² + (1/√2)² = 1`: the Hadamard gate is an exact scale-one unitary over `ℚ[√2]`. -/
theorem invSqrtTwo_sq_add_sq : add (mul invSqrtTwo invSqrtTwo) (mul invSqrtTwo invSqrtTwo) = one := by
  apply QuadExt.ext'
  · rw [QuadExt.add_a, QuadExt.mul_a, QuadExt.one_a]
    exact PosFrac.sound (by unfold PosPreFrac.rel; decide)
  · rw [QuadExt.add_b, QuadExt.mul_b, QuadExt.one_b]
    exact PosFrac.sound (by unfold PosPreFrac.rel; decide)

/-- The primitive eighth root of unity `ζ₈ = (1 + i)/√2`, the phase of the `T` gate. -/
def zetaEight : CyclotomicEight := ⟨invSqrtTwo, invSqrtTwo⟩

theorem zetaEight_normSq : ConstructiveAmplitudeRing.normSq zetaEight = (one : RatSqrt2) := by
  rw [Complexified.normSq_eq]
  exact invSqrtTwo_sq_add_sq

/-- `ζ₈² = i`. -/
theorem zetaEight_sq : mul zetaEight zetaEight = Complexified.I := by
  apply Complexified.ext'
  · rw [Complexified.mul_re]
    show sub (mul invSqrtTwo invSqrtTwo) (mul invSqrtTwo invSqrtTwo) = zero
    exact LawfulCommRing.sub_self _
  · rw [Complexified.mul_im]
    exact invSqrtTwo_sq_add_sq

/-- The embedding `ℚ[i] → ℚ[√2, i]`. -/
def ratComplexToCyclotomic (z : RatComplex) : CyclotomicEight :=
  ⟨QuadExt.ofBase z.re, QuadExt.ofBase z.im⟩

/-- The rational phase keeps unit modulus inside `ℚ[√2, i]`, next to `ζ₈`. -/
theorem ratComplexToCyclotomic_unit_normSq :
    ConstructiveAmplitudeRing.normSq (ratComplexToCyclotomic unitThreeFourFifths) =
      (one : RatSqrt2) := by
  rw [Complexified.normSq_eq]
  apply QuadExt.ext'
  · rw [QuadExt.add_a, QuadExt.mul_a, QuadExt.mul_a, QuadExt.one_a]
    exact PosFrac.sound (by unfold PosPreFrac.rel; decide)
  · rw [QuadExt.add_b, QuadExt.mul_b, QuadExt.mul_b, QuadExt.one_b]
    exact PosFrac.sound (by unfold PosPreFrac.rel; decide)

#verify_constructive
  Qsag.LinearOrderedDomain.le_of_sq_le_sq
  Qsag.PosPreFrac.ple_congr
  Qsag.PosFrac.ofBase_mul_frac
  Qsag.PosFrac.ofBase_injective
  Qsag.QuadExt.nonneg_add
  Qsag.QuadExt.nonneg_mul
  Qsag.QuadExt.nonneg_sq
  Qsag.QuadExt.sqrtd_mul_self
  Qsag.Complexified.I_mul_I
  Qsag.ConstructiveAmplitudeRing.normSq_mul
  Qsag.ConstructiveAmplitudeRing.normSq_eq_zero_iff
  Qsag.ConstructiveAmplitudeRing.normSq_parallelogram
  Qsag.ConstructiveAmplitudeRing.normSq_parallelogram_two
  Qsag.ConstructiveAmplitudeRing.normSq_add_le
  Qsag.unitThreeFourFifths_normSq
  Qsag.unitThreeFourFifths_mul_star
  Qsag.three_fifths_not_dyadic
  Qsag.unitThreeFourFifths_not_dyadic
  Qsag.invSqrtTwo_sq_add_sq
  Qsag.zetaEight_normSq
  Qsag.zetaEight_sq
  Qsag.ratComplexToCyclotomic_unit_normSq

end Qsag
end
