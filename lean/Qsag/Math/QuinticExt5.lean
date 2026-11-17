module
public import Qsag.Math.Goldilocks
public import Qsag.Math.Tactic.CommRing
public import Qsag.Tactic.AssuranceKit

public section
namespace Qsag
set_option autoImplicit false
set_option linter.unusedSimpArgs false
/-! ## `QuinticGoldilocks`: the quintic extension field $\mathbb{F}_{p^5} = \mathbb{F}_p[X]/(X^5 - 3)$

The challenge field of zk-Hem v2 (`crates/qsag-agg/src/zk_hem/v2/field5.rs`, type `Fp5`), in the
power basis `c0 + c1 X + c2 X^2 + c3 X^3 + c4 X^4` over `Goldilocks`.

* Ring structure: schoolbook product with the reduction `X^5 = 3`, every `LawfulCommRing` law.
* `frob`: the Frobenius `x ↦ x^p`, which is `X ↦ ζ X` for `ζ = 3^((p-1)/5)`, a ring automorphism of
  order five whose fixed points are exactly the base field.
* `norm z = z · frob z · frob² z · frob³ z · frob⁴ z ∈ 𝔽_p` and the Itoh–Tsujii inverse
  `inv z = (frob z · frob² z · frob³ z · frob⁴ z) · (norm z)⁻¹`.
* `norm z = 0` only for `z = 0`: a nonzero element of least polynomial degree with zero norm
  would give a linear or a quadratic factor of `X^5 - 3`, and each of those makes `3` a fifth
  power in `𝔽_p`, which `3^((p-1)/5) = ζ ≠ 1` excludes.
-/

local infixl:65 " +ᵍ " => CommRingOps.add
local infixl:70 " *ᵍ " => CommRingOps.mul

/-! ### Generic cofactor helpers -/

private theorem quintEqOfSubEqMul {R : Type} [LawfulCommRing R] {l r : R} (k s : R)
    (hk : k = CommRingOps.zero) (h : CommRingOps.sub l r = k *ᵍ s) : l = r := by
  rw [hk, LawfulCommRing.zero_mul] at h
  exact LawfulCommRing.sub_eq_zero_iff.mp h

private theorem quintEqOfSubEqMul2 {R : Type} [LawfulCommRing R] {l r : R} (k₁ s₁ k₂ s₂ : R)
    (h₁ : k₁ = CommRingOps.zero) (h₂ : k₂ = CommRingOps.zero)
    (h : CommRingOps.sub l r = k₁ *ᵍ s₁ +ᵍ k₂ *ᵍ s₂) : l = r := by
  rw [h₁, h₂, LawfulCommRing.zero_mul, LawfulCommRing.zero_mul, LawfulCommRing.add_zero] at h
  exact LawfulCommRing.sub_eq_zero_iff.mp h

/-- If `v` is invertible and `u^5 = w v^5`, then `u / v` is a fifth root of `w`. -/
private theorem quintFifthRootOfRatio {R : Type} [LawfulCommRing R] (w u v j : R)
    (hi : v *ᵍ j = CommRingOps.one)
    (hE : CRing.npow u 5 = w *ᵍ CRing.npow v 5) :
    CRing.npow (u *ᵍ j) 5 = w := by
  refine quintEqOfSubEqMul2
    (CommRingOps.sub (CRing.npow u 5) (w *ᵍ CRing.npow v 5)) (CRing.npow j 5)
    (CommRingOps.sub (v *ᵍ j) CommRingOps.one)
    (w *ᵍ (CRing.npow (v *ᵍ j) 4 +ᵍ CRing.npow (v *ᵍ j) 3 +ᵍ CRing.npow (v *ᵍ j) 2 +ᵍ v *ᵍ j +ᵍ
      CommRingOps.one))
    (by rw [hE, LawfulCommRing.sub_self]) (by rw [hi, LawfulCommRing.sub_self]) ?_
  constructive_ring

/-- A monic-up-to-scaling quadratic `a X^2 + b X + c` whose remainder into `X^5 - w` vanishes
    (`h1`: the `X` coefficient, `h0`: the constant coefficient) forces
    `(b^2 - a c)^5 = w (a b)^5`. -/
private theorem quintQuadKey {R : Type} [LawfulCommRing R] (w a b c : R)
    (h1 : CommRingOps.sub (CRing.natCast 3 *ᵍ (a *ᵍ ((b *ᵍ b) *ᵍ c)))
        (CRing.npow b 4 +ᵍ (a *ᵍ a) *ᵍ (c *ᵍ c)) = CommRingOps.zero)
    (h0 : c *ᵍ CommRingOps.sub (CRing.natCast 2 *ᵍ (a *ᵍ (b *ᵍ c))) (CRing.npow b 3) +ᵍ
        w *ᵍ CRing.npow a 4 = CommRingOps.zero) :
    CRing.npow (CommRingOps.sub (b *ᵍ b) (a *ᵍ c)) 5 = w *ᵍ CRing.npow (a *ᵍ b) 5 := by
  refine quintEqOfSubEqMul2 _
    (CommRingOps.sub
      (CRing.npow a 3 *ᵍ CRing.npow c 3 +ᵍ CRing.natCast 3 *ᵍ (a *ᵍ (CRing.npow b 4 *ᵍ c)))
      (CRing.natCast 2 *ᵍ (CRing.npow a 2 *ᵍ (CRing.npow b 2 *ᵍ CRing.npow c 2)) +ᵍ
        CRing.npow b 6))
    _ (CommRingOps.neg (a *ᵍ CRing.npow b 5)) h1 h0 ?_
  constructive_ring

private theorem quintPowModCongr {x y m : Nat} (h : x % m = y % m) :
    ∀ k : Nat, (x ^ k) % m = (y ^ k) % m
  | 0 => rfl
  | k + 1 => by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mod, quintPowModCongr h k, h, ← Nat.mul_mod]

private theorem goldNpowVal (t : Goldilocks) :
    ∀ k : Nat, (CRing.npow t k).val = t.val ^ k % goldilocksPrime
  | 0 => by
    show (1 : Nat) = t.val ^ 0 % goldilocksPrime
    rw [Nat.pow_zero]
    decide
  | k + 1 => by
    show (Goldilocks.mul (CRing.npow t k) t).val = _
    rw [Goldilocks.mul_val, goldNpowVal t k, Nat.pow_succ, Nat.mod_mul_mod]

private theorem goldNpowEqZero (c : Goldilocks) :
    ∀ k : Nat, CRing.npow c k = CommRingOps.zero → c = CommRingOps.zero
  | 0, h =>
    absurd (show (CommRingOps.zero : Goldilocks) = CommRingOps.one from h.symm)
      LawfulField.zero_ne_one
  | k + 1, h => by
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero (a := CRing.npow c k) (b := c) h
      with h0 | h0
    · exact goldNpowEqZero c k h0
    · exact h0

private theorem goldFixedCoeff {k c : Goldilocks} (hk : k ≠ CommRingOps.one)
    (h : k *ᵍ c = c) : c = CommRingOps.zero := by
  have e : CommRingOps.sub k CommRingOps.one *ᵍ c = CommRingOps.zero := by
    have e1 : CommRingOps.sub k CommRingOps.one *ᵍ c = CommRingOps.sub (k *ᵍ c) c := by
      constructive_ring
    rw [e1, h, LawfulCommRing.sub_self]
  rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero e with h0 | h0
  · exact absurd (LawfulCommRing.sub_eq_zero_iff.mp h0) hk
  · exact h0

private theorem three_fifth_modPow_abstract (e : Nat) (hLt : e < 2 ^ 64)
    (hEval : modPowFuel 64 3 e goldilocksPrime = 1041288259238279555) :
    (3 ^ e) % goldilocksPrime = 1041288259238279555 := by
  rw [← modPowFuel_eq_pow_mod 64 3 e goldilocksPrime hLt]
  exact hEval

/-- `3^((p-1)/5) ≡ ζ (mod p)` with `ζ = 1041288259238279555 ≠ 1`, by the verified 64-step
    modular exponentiation. -/
theorem goldilocks_three_fifth_modPow :
    (3 ^ ((goldilocksPrime - 1) / 5)) % goldilocksPrime = 1041288259238279555 :=
  three_fifth_modPow_abstract ((goldilocksPrime - 1) / 5) (by decide) (by decide)

/-- Quintic extension field `QuinticGoldilocks = 𝔽_p[X] / (X^5 - 3)` in the power basis,
    matching `Fp5` in `crates/qsag-agg/src/zk_hem/v2/field5.rs` (`|𝔽_{p^5}| = p^5 > 2^319`). -/
structure QuinticGoldilocks where
  c0 : Goldilocks
  c1 : Goldilocks
  c2 : Goldilocks
  c3 : Goldilocks
  c4 : Goldilocks
  deriving Repr

@[expose, instance_reducible] def instDecidableEqQuinticGoldilocks (a b : QuinticGoldilocks) :
    Decidable (a = b) :=
  if h0 : a.c0 = b.c0 then
    if h1 : a.c1 = b.c1 then
      if h2 : a.c2 = b.c2 then
        if h3 : a.c3 = b.c3 then
          if h4 : a.c4 = b.c4 then
            isTrue (by cases a; cases b; cases h0; cases h1; cases h2; cases h3; cases h4; rfl)
          else isFalse (fun h => h4 (congrArg QuinticGoldilocks.c4 h))
        else isFalse (fun h => h3 (congrArg QuinticGoldilocks.c3 h))
      else isFalse (fun h => h2 (congrArg QuinticGoldilocks.c2 h))
    else isFalse (fun h => h1 (congrArg QuinticGoldilocks.c1 h))
  else isFalse (fun h => h0 (congrArg QuinticGoldilocks.c0 h))
attribute [instance] instDecidableEqQuinticGoldilocks

namespace QuinticGoldilocks

@[ext] theorem ext {x y : QuinticGoldilocks} (h0 : x.c0 = y.c0) (h1 : x.c1 = y.c1)
    (h2 : x.c2 = y.c2) (h3 : x.c3 = y.c3) (h4 : x.c4 = y.c4) : x = y := by
  cases x; cases y; subst h0; subst h1; subst h2; subst h3; subst h4; rfl

/-- The reduction constant: `X^5 = 3`. -/
@[expose] def nonResidue : Goldilocks := ⟨3, by decide⟩

/-- `ζ = 3^((p-1)/5)`, a primitive fifth root of unity in `Goldilocks`. -/
def zeta : Goldilocks := ⟨1041288259238279555, by decide⟩

@[expose] def zero : QuinticGoldilocks :=
  ⟨CommRingOps.zero, CommRingOps.zero, CommRingOps.zero, CommRingOps.zero, CommRingOps.zero⟩
@[expose] def one : QuinticGoldilocks :=
  ⟨CommRingOps.one, CommRingOps.zero, CommRingOps.zero, CommRingOps.zero, CommRingOps.zero⟩
/-- The class of `X`. -/
@[expose] def xBasis : QuinticGoldilocks :=
  ⟨CommRingOps.zero, CommRingOps.one, CommRingOps.zero, CommRingOps.zero, CommRingOps.zero⟩
/-- The base-field embedding `a ↦ a + 0 X + 0 X^2 + 0 X^3 + 0 X^4`. -/
@[expose] def ofBase (a : Goldilocks) : QuinticGoldilocks :=
  ⟨a, CommRingOps.zero, CommRingOps.zero, CommRingOps.zero, CommRingOps.zero⟩

instance : Inhabited QuinticGoldilocks := ⟨zero⟩

@[expose] def add (x y : QuinticGoldilocks) : QuinticGoldilocks :=
  ⟨x.c0 +ᵍ y.c0, x.c1 +ᵍ y.c1, x.c2 +ᵍ y.c2, x.c3 +ᵍ y.c3, x.c4 +ᵍ y.c4⟩

@[expose] def neg (x : QuinticGoldilocks) : QuinticGoldilocks :=
  ⟨CommRingOps.neg x.c0, CommRingOps.neg x.c1, CommRingOps.neg x.c2, CommRingOps.neg x.c3,
    CommRingOps.neg x.c4⟩

@[expose] def sub (x y : QuinticGoldilocks) : QuinticGoldilocks :=
  ⟨CommRingOps.sub x.c0 y.c0, CommRingOps.sub x.c1 y.c1, CommRingOps.sub x.c2 y.c2,
    CommRingOps.sub x.c3 y.c3, CommRingOps.sub x.c4 y.c4⟩

/-- Schoolbook product in `𝔽_p[X]/(X^5 - n)`. The field uses `n = nonResidue`; the parameter
    lets the teeth run the same product with a reduction constant that is a fifth power. -/
@[expose] def mulWith (n : Goldilocks) (x y : QuinticGoldilocks) : QuinticGoldilocks :=
  ⟨x.c0 *ᵍ y.c0 +ᵍ n *ᵍ (x.c1 *ᵍ y.c4 +ᵍ x.c2 *ᵍ y.c3 +ᵍ x.c3 *ᵍ y.c2 +ᵍ x.c4 *ᵍ y.c1),
   x.c0 *ᵍ y.c1 +ᵍ x.c1 *ᵍ y.c0 +ᵍ n *ᵍ (x.c2 *ᵍ y.c4 +ᵍ x.c3 *ᵍ y.c3 +ᵍ x.c4 *ᵍ y.c2),
   x.c0 *ᵍ y.c2 +ᵍ x.c1 *ᵍ y.c1 +ᵍ x.c2 *ᵍ y.c0 +ᵍ n *ᵍ (x.c3 *ᵍ y.c4 +ᵍ x.c4 *ᵍ y.c3),
   x.c0 *ᵍ y.c3 +ᵍ x.c1 *ᵍ y.c2 +ᵍ x.c2 *ᵍ y.c1 +ᵍ x.c3 *ᵍ y.c0 +ᵍ n *ᵍ (x.c4 *ᵍ y.c4),
   x.c0 *ᵍ y.c4 +ᵍ x.c1 *ᵍ y.c3 +ᵍ x.c2 *ᵍ y.c2 +ᵍ x.c3 *ᵍ y.c1 +ᵍ x.c4 *ᵍ y.c0⟩

@[expose] def mul (x y : QuinticGoldilocks) : QuinticGoldilocks := mulWith nonResidue x y

instance : CommRingOps QuinticGoldilocks where
  zero := zero
  one := one
  add := add
  mul := mul
  neg := neg
  sub := sub

theorem ring_add (x y : QuinticGoldilocks) : CommRingOps.add x y = add x y := by rfl
theorem ring_sub (x y : QuinticGoldilocks) : CommRingOps.sub x y = sub x y := by rfl
theorem ring_mul (x y : QuinticGoldilocks) : CommRingOps.mul x y = mul x y := by rfl
theorem ring_neg (x : QuinticGoldilocks) : CommRingOps.neg x = neg x := by rfl
theorem ring_zero : (CommRingOps.zero : QuinticGoldilocks) = zero := by rfl
theorem ring_one : (CommRingOps.one : QuinticGoldilocks) = one := by rfl

/-- The Frobenius `x ↦ x^p`: `X ↦ ζ X`, so `c_i ↦ ζ^i c_i`. -/
def frob (z : QuinticGoldilocks) : QuinticGoldilocks :=
  ⟨z.c0, zeta *ᵍ z.c1, (zeta *ᵍ zeta) *ᵍ z.c2, (zeta *ᵍ zeta *ᵍ zeta) *ᵍ z.c3,
    ((zeta *ᵍ zeta) *ᵍ (zeta *ᵍ zeta)) *ᵍ z.c4⟩

/-- Unfold the ring operations to coordinates. -/
local macro "quint_coords" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp only [ring_mul, ring_add, ring_sub, ring_neg, ring_zero, ring_one,
      mul, mulWith, add, sub, neg, zero, one, ofBase, xBasis, frob, $ts,*])

instance : LawfulCommRing QuinticGoldilocks where
  add_assoc x y z := by apply ext <;> quint_coords [] <;> constructive_ring
  add_comm x y := by apply ext <;> quint_coords [] <;> constructive_ring
  zero_add x := by apply ext <;> quint_coords [] <;> constructive_ring
  add_zero x := by apply ext <;> quint_coords [] <;> constructive_ring
  add_left_neg x := by apply ext <;> quint_coords [] <;> constructive_ring
  sub_eq_add_neg x y := by apply ext <;> quint_coords [] <;> constructive_ring
  mul_assoc x y z := by apply ext <;> quint_coords [] <;> constructive_ring
  mul_comm x y := by apply ext <;> quint_coords [] <;> constructive_ring
  one_mul x := by apply ext <;> quint_coords [] <;> constructive_ring
  mul_one x := by apply ext <;> quint_coords [] <;> constructive_ring
  left_distrib x y z := by apply ext <;> quint_coords [] <;> constructive_ring
  right_distrib x y z := by apply ext <;> quint_coords [] <;> constructive_ring

/-! ### Coordinates -/

theorem add_c0 (x y : QuinticGoldilocks) : (x +ᵍ y).c0 = x.c0 +ᵍ y.c0 := by rfl
theorem add_c1 (x y : QuinticGoldilocks) : (x +ᵍ y).c1 = x.c1 +ᵍ y.c1 := by rfl
theorem add_c2 (x y : QuinticGoldilocks) : (x +ᵍ y).c2 = x.c2 +ᵍ y.c2 := by rfl
theorem add_c3 (x y : QuinticGoldilocks) : (x +ᵍ y).c3 = x.c3 +ᵍ y.c3 := by rfl
theorem add_c4 (x y : QuinticGoldilocks) : (x +ᵍ y).c4 = x.c4 +ᵍ y.c4 := by rfl
theorem mul_c0 (x y : QuinticGoldilocks) : (x *ᵍ y).c0 =
    x.c0 *ᵍ y.c0 +ᵍ
      nonResidue *ᵍ (x.c1 *ᵍ y.c4 +ᵍ x.c2 *ᵍ y.c3 +ᵍ x.c3 *ᵍ y.c2 +ᵍ x.c4 *ᵍ y.c1) := by rfl
theorem mul_c1 (x y : QuinticGoldilocks) : (x *ᵍ y).c1 =
    x.c0 *ᵍ y.c1 +ᵍ x.c1 *ᵍ y.c0 +ᵍ
      nonResidue *ᵍ (x.c2 *ᵍ y.c4 +ᵍ x.c3 *ᵍ y.c3 +ᵍ x.c4 *ᵍ y.c2) := by rfl
theorem mul_c2 (x y : QuinticGoldilocks) : (x *ᵍ y).c2 =
    x.c0 *ᵍ y.c2 +ᵍ x.c1 *ᵍ y.c1 +ᵍ x.c2 *ᵍ y.c0 +ᵍ
      nonResidue *ᵍ (x.c3 *ᵍ y.c4 +ᵍ x.c4 *ᵍ y.c3) := by rfl
theorem mul_c3 (x y : QuinticGoldilocks) : (x *ᵍ y).c3 =
    x.c0 *ᵍ y.c3 +ᵍ x.c1 *ᵍ y.c2 +ᵍ x.c2 *ᵍ y.c1 +ᵍ x.c3 *ᵍ y.c0 +ᵍ
      nonResidue *ᵍ (x.c4 *ᵍ y.c4) := by rfl
theorem mul_c4 (x y : QuinticGoldilocks) : (x *ᵍ y).c4 =
    x.c0 *ᵍ y.c4 +ᵍ x.c1 *ᵍ y.c3 +ᵍ x.c2 *ᵍ y.c2 +ᵍ x.c3 *ᵍ y.c1 +ᵍ x.c4 *ᵍ y.c0 := by rfl
theorem frob_c0 (z : QuinticGoldilocks) : (frob z).c0 = z.c0 := by rfl
theorem frob_c1 (z : QuinticGoldilocks) : (frob z).c1 = zeta *ᵍ z.c1 := by rfl
theorem frob_c2 (z : QuinticGoldilocks) : (frob z).c2 = (zeta *ᵍ zeta) *ᵍ z.c2 := by rfl
theorem frob_c3 (z : QuinticGoldilocks) :
    (frob z).c3 = (zeta *ᵍ zeta *ᵍ zeta) *ᵍ z.c3 := by rfl
theorem frob_c4 (z : QuinticGoldilocks) :
    (frob z).c4 = ((zeta *ᵍ zeta) *ᵍ (zeta *ᵍ zeta)) *ᵍ z.c4 := by rfl
theorem zeta_val : zeta.val = 1041288259238279555 := by rfl

/-! ### The base-field embedding is an injective ring homomorphism -/

theorem ofBase_c0 (a : Goldilocks) : (ofBase a).c0 = a := by rfl
theorem ofBase_zero : ofBase CommRingOps.zero = CommRingOps.zero := by rfl
theorem ofBase_one : ofBase CommRingOps.one = CommRingOps.one := by rfl
theorem ofBase_injective {a b : Goldilocks} (h : ofBase a = ofBase b) : a = b :=
  congrArg QuinticGoldilocks.c0 h
theorem ofBase_add (a b : Goldilocks) : ofBase (a +ᵍ b) = ofBase a +ᵍ ofBase b := by
  apply ext <;> quint_coords [] <;> constructive_ring
theorem ofBase_neg (a : Goldilocks) :
    ofBase (CommRingOps.neg a) = CommRingOps.neg (ofBase a) := by
  apply ext <;> quint_coords [] <;> constructive_ring
theorem ofBase_sub (a b : Goldilocks) :
    ofBase (CommRingOps.sub a b) = CommRingOps.sub (ofBase a) (ofBase b) := by
  apply ext <;> quint_coords [] <;> constructive_ring
theorem ofBase_mul (a b : Goldilocks) : ofBase (a *ᵍ b) = ofBase a *ᵍ ofBase b := by
  apply ext <;> quint_coords [] <;> constructive_ring

/-- `X^5 = 3`. -/
theorem xBasis_pow5 :
    ((xBasis *ᵍ xBasis) *ᵍ (xBasis *ᵍ xBasis)) *ᵍ xBasis = ofBase nonResidue := by
  apply ext <;> quint_coords [] <;> constructive_ring

/-! ### `3` is not a fifth power in `Goldilocks` -/

theorem zeta_pow5 : CRing.npow zeta 5 = CommRingOps.one := by
  apply Goldilocks.ext
  rw [goldNpowVal]
  decide

private theorem zeta1_ne_one : zeta ≠ CommRingOps.one := by decide +kernel
private theorem zeta2_ne_one : zeta *ᵍ zeta ≠ CommRingOps.one := by decide +kernel
private theorem zeta3_ne_one : zeta *ᵍ zeta *ᵍ zeta ≠ CommRingOps.one := by decide +kernel
private theorem zeta4_ne_one : (zeta *ᵍ zeta) *ᵍ (zeta *ᵍ zeta) ≠ CommRingOps.one := by
  decide +kernel
private theorem nonResidue_ne_zero : nonResidue ≠ CommRingOps.zero := by decide +kernel

/-- **Quintic non-residue theorem**: `3` has no fifth root in `Goldilocks`, because
    `t^5 = 3` would give `1 = t^(p-1) = 3^((p-1)/5) = ζ ≠ 1`. -/
theorem nonResidue_not_fifth_power (t : Goldilocks) : CRing.npow t 5 ≠ nonResidue := by
  intro h5
  have hval : (t.val ^ 5) % goldilocksPrime = 3 := by
    have hv := congrArg Goldilocks.val h5
    rw [goldNpowVal] at hv
    exact hv
  let fifth := (goldilocksPrime - 1) / 5
  have ht5 : (t.val ^ 5) % goldilocksPrime = 3 % goldilocksPrime := by
    rw [hval]
    decide
  have hpowEq : ((t.val ^ 5) ^ fifth) % goldilocksPrime = (3 ^ fifth) % goldilocksPrime :=
    quintPowModCongr ht5 fifth
  rw [← Nat.pow_mul] at hpowEq
  have h5fifth : 5 * fifth = goldilocksPrime - 1 := by decide
  rw [h5fifth] at hpowEq
  have hnotDvd : ¬ (goldilocksPrime ∣ t.val) := fun hd => by
    rcases hd with ⟨q, hq⟩
    cases q with
    | zero =>
      rw [Nat.mul_zero] at hq
      rw [hq] at hval
      exact absurd hval (by decide)
    | succ q =>
      have hlt := t.isLt
      rw [hq, Nat.mul_succ] at hlt
      exact absurd hlt (Nat.not_lt.mpr (Nat.le_add_left _ _))
  have hflt := (goldilocksPrime_isPrime ()).pow_sub_one_mod hnotDvd
  rw [hflt, goldilocks_three_fifth_modPow] at hpowEq
  exact absurd hpowEq (by decide)

/-! ### Frobenius -/

theorem frob_add (x y : QuinticGoldilocks) : frob (x +ᵍ y) = frob x +ᵍ frob y := by
  apply ext <;> quint_coords [] <;> constructive_ring

theorem frob_one : frob CommRingOps.one = CommRingOps.one := by
  apply ext <;> quint_coords [] <;> constructive_ring

theorem frob_zero : frob CommRingOps.zero = CommRingOps.zero := by
  apply ext <;> quint_coords [] <;> constructive_ring

theorem frob_ofBase (a : Goldilocks) : frob (ofBase a) = ofBase a := by
  apply ext <;> quint_coords [] <;> constructive_ring

private theorem zeta_pow5_sub_one :
    CommRingOps.sub (CRing.npow zeta 5) CommRingOps.one = CommRingOps.zero := by
  rw [zeta_pow5, LawfulCommRing.sub_self]

/-- `frob` is multiplicative: the wrapped terms carry `ζ^5 = 1`. -/
theorem frob_mul (x y : QuinticGoldilocks) : frob (x *ᵍ y) = frob x *ᵍ frob y := by
  apply ext <;> quint_coords []
  · refine quintEqOfSubEqMul _
      (CommRingOps.neg (nonResidue *ᵍ
        (x.c1 *ᵍ y.c4 +ᵍ x.c2 *ᵍ y.c3 +ᵍ x.c3 *ᵍ y.c2 +ᵍ x.c4 *ᵍ y.c1)))
      zeta_pow5_sub_one ?_
    constructive_ring
  · refine quintEqOfSubEqMul _
      (CommRingOps.neg (nonResidue *ᵍ (zeta *ᵍ
        (x.c2 *ᵍ y.c4 +ᵍ x.c3 *ᵍ y.c3 +ᵍ x.c4 *ᵍ y.c2))))
      zeta_pow5_sub_one ?_
    constructive_ring
  · refine quintEqOfSubEqMul _
      (CommRingOps.neg (nonResidue *ᵍ (CRing.npow zeta 2 *ᵍ
        (x.c3 *ᵍ y.c4 +ᵍ x.c4 *ᵍ y.c3))))
      zeta_pow5_sub_one ?_
    constructive_ring
  · refine quintEqOfSubEqMul _
      (CommRingOps.neg (nonResidue *ᵍ (CRing.npow zeta 3 *ᵍ (x.c4 *ᵍ y.c4))))
      zeta_pow5_sub_one ?_
    constructive_ring
  · constructive_ring

/-- `frob` has order five. -/
theorem frob_pow5 (z : QuinticGoldilocks) : frob (frob (frob (frob (frob z)))) = z := by
  apply ext
  · rfl
  · quint_coords []
    refine quintEqOfSubEqMul _ z.c1 zeta_pow5_sub_one ?_
    constructive_ring
  · quint_coords []
    refine quintEqOfSubEqMul _ ((CRing.npow zeta 5 +ᵍ CommRingOps.one) *ᵍ z.c2)
      zeta_pow5_sub_one ?_
    constructive_ring
  · quint_coords []
    refine quintEqOfSubEqMul _
      ((CRing.npow zeta 10 +ᵍ CRing.npow zeta 5 +ᵍ CommRingOps.one) *ᵍ z.c3)
      zeta_pow5_sub_one ?_
    constructive_ring
  · quint_coords []
    refine quintEqOfSubEqMul _
      ((CRing.npow zeta 15 +ᵍ CRing.npow zeta 10 +ᵍ CRing.npow zeta 5 +ᵍ CommRingOps.one) *ᵍ
        z.c4)
      zeta_pow5_sub_one ?_
    constructive_ring

/-- The fixed field of `frob` is the base field: there is no element of `𝔽_{p^5}` outside
    `𝔽_p` that the Frobenius fixes. -/
theorem frob_eq_self_iff (z : QuinticGoldilocks) : frob z = z ↔ z = ofBase z.c0 := by
  constructor
  · intro h
    have h1 : z.c1 = CommRingOps.zero :=
      goldFixedCoeff (k := zeta) (c := z.c1) zeta1_ne_one (congrArg QuinticGoldilocks.c1 h)
    have h2 : z.c2 = CommRingOps.zero :=
      goldFixedCoeff (k := zeta *ᵍ zeta) (c := z.c2) zeta2_ne_one
        (congrArg QuinticGoldilocks.c2 h)
    have h3 : z.c3 = CommRingOps.zero :=
      goldFixedCoeff (k := zeta *ᵍ zeta *ᵍ zeta) (c := z.c3) zeta3_ne_one
        (congrArg QuinticGoldilocks.c3 h)
    have h4 : z.c4 = CommRingOps.zero :=
      goldFixedCoeff (k := (zeta *ᵍ zeta) *ᵍ (zeta *ᵍ zeta)) (c := z.c4) zeta4_ne_one
        (congrArg QuinticGoldilocks.c4 h)
    exact ext rfl h1 h2 h3 h4
  · intro h
    rw [h]
    exact frob_ofBase _

/-! ### Norm and inverse -/

/-- Product of the four proper conjugates `frob z · frob² z · frob³ z · frob⁴ z`. -/
def conj (z : QuinticGoldilocks) : QuinticGoldilocks :=
  frob z *ᵍ frob (frob z) *ᵍ frob (frob (frob z)) *ᵍ frob (frob (frob (frob z)))

/-- Field norm `N(z) = z · frob z · frob² z · frob³ z · frob⁴ z ∈ 𝔽_p`. -/
def norm (z : QuinticGoldilocks) : Goldilocks := (z *ᵍ conj z).c0

/-- Itoh–Tsujii inverse `conj z · N(z)⁻¹` (with `inv 0 = 0`). -/
def inv (z : QuinticGoldilocks) : QuinticGoldilocks :=
  conj z *ᵍ ofBase (Goldilocks.inv (norm z))

/-- `z · conj z` is fixed by `frob`, hence is the base-field element `norm z`. -/
theorem mul_conj (z : QuinticGoldilocks) : z *ᵍ conj z = ofBase (norm z) := by
  have hfix : frob (z *ᵍ conj z) = z *ᵍ conj z := by
    unfold conj
    simp only [frob_mul, frob_pow5]
    constructive_ring
  exact (frob_eq_self_iff _).mp hfix

theorem norm_mul (x y : QuinticGoldilocks) : norm (x *ᵍ y) = norm x *ᵍ norm y := by
  apply ofBase_injective
  rw [ofBase_mul, ← mul_conj, ← mul_conj, ← mul_conj]
  unfold conj
  simp only [frob_mul]
  constructive_ring

theorem norm_ofBase (a : Goldilocks) : norm (ofBase a) = CRing.npow a 5 := by
  unfold norm conj
  simp only [frob_ofBase, ← ofBase_mul, ofBase_c0]
  constructive_ring

/-- The two-multiplication form of `conj` computed by `Fp5::conjugate_product`:
    with `t = frob z · frob² z` it is `t · frob² t`. -/
theorem conj_eq_two_mul (z : QuinticGoldilocks) :
    conj z = (frob z *ᵍ frob (frob z)) *ᵍ frob (frob (frob z *ᵍ frob (frob z))) := by
  unfold conj
  simp only [frob_mul]
  constructive_ring

/-- Multiplication by a base-field element scales every coordinate (`Fp5::mul_base`). -/
theorem mul_ofBase (z : QuinticGoldilocks) (a : Goldilocks) :
    z *ᵍ ofBase a = ⟨z.c0 *ᵍ a, z.c1 *ᵍ a, z.c2 *ᵍ a, z.c3 *ᵍ a, z.c4 *ᵍ a⟩ := by
  apply ext <;> quint_coords [] <;> constructive_ring

/-- `inv` is `conj z` scaled by the base-field inverse of the norm, as `Fp5::inv` computes it. -/
