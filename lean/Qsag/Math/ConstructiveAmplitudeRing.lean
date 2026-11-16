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
