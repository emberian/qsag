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
theorem inv_eq_scale (z : QuinticGoldilocks) :
    inv z = ⟨(conj z).c0 *ᵍ Goldilocks.inv (norm z), (conj z).c1 *ᵍ Goldilocks.inv (norm z),
      (conj z).c2 *ᵍ Goldilocks.inv (norm z), (conj z).c3 *ᵍ Goldilocks.inv (norm z),
      (conj z).c4 *ᵍ Goldilocks.inv (norm z)⟩ :=
  mul_ofBase (conj z) (Goldilocks.inv (norm z))

theorem norm_one : norm CommRingOps.one = CommRingOps.one := by
  rw [← ofBase_one, norm_ofBase]
  constructive_ring

/-- An element with nonzero norm is not a zero divisor. -/
private theorem eq_zero_of_mul_eq_zero_of_norm_ne {z q : QuinticGoldilocks}
    (hq : norm q ≠ CommRingOps.zero) (h : z *ᵍ q = CommRingOps.zero) :
    z = CommRingOps.zero := by
  have hi := Goldilocks.mul_inv_cancel hq
  have e : z = (z *ᵍ q) *ᵍ (conj q *ᵍ ofBase (Goldilocks.inv (norm q))) := by
    rw [LawfulCommRing.mul_assoc, ← LawfulCommRing.mul_assoc q, mul_conj, ← ofBase_mul, hi,
      ofBase_one, LawfulCommRing.mul_one]
  rw [e, h, LawfulCommRing.zero_mul]

/-! ### `norm z = 0` only at `z = 0`, by polynomial degree -/

/-- `(a X + b) · linCofactor a b = a^5 X^5 + b^5`. -/
private def linCofactor (a b : Goldilocks) : QuinticGoldilocks :=
  ⟨CRing.npow b 4, CommRingOps.neg (a *ᵍ CRing.npow b 3), CRing.npow a 2 *ᵍ CRing.npow b 2,
    CommRingOps.neg (CRing.npow a 3 *ᵍ b), CRing.npow a 4⟩

private theorem linCofactor_mul (z : QuinticGoldilocks) (h2 : z.c2 = CommRingOps.zero)
    (h3 : z.c3 = CommRingOps.zero) (h4 : z.c4 = CommRingOps.zero) :
    z *ᵍ linCofactor z.c1 z.c0 =
      ofBase (nonResidue *ᵍ CRing.npow z.c1 5 +ᵍ CRing.npow z.c0 5) := by
  apply ext <;> quint_coords [linCofactor, h2, h3, h4] <;> constructive_ring

/-- Degree at most one. A zero norm on `a X + b` with `a ≠ 0` gives `(-b/a)^5 = 3`. -/
private theorem eq_zero_of_norm_low1 {z : QuinticGoldilocks} (h2 : z.c2 = CommRingOps.zero)
    (h3 : z.c3 = CommRingOps.zero) (h4 : z.c4 = CommRingOps.zero)
    (hn : norm z = CommRingOps.zero) : z = CommRingOps.zero := by
  have hprod : norm (z *ᵍ linCofactor z.c1 z.c0) = CommRingOps.zero := by
    rw [norm_mul, hn, LawfulCommRing.zero_mul]
  rw [linCofactor_mul z h2 h3 h4, norm_ofBase] at hprod
  have hs := goldNpowEqZero _ 5 hprod
  if h1 : z.c1 = CommRingOps.zero then
    have h0 : z.c0 = CommRingOps.zero := by
      rw [h1] at hs
      have e : CRing.npow z.c0 5 =
          nonResidue *ᵍ CRing.npow (CommRingOps.zero : Goldilocks) 5 +ᵍ CRing.npow z.c0 5 := by
        constructive_ring
      exact goldNpowEqZero _ 5 (e.trans hs)
    exact ext h0 h1 h2 h3 h4
  else
    exfalso
    have hi := Goldilocks.mul_inv_cancel h1
    have hE : CRing.npow (CommRingOps.neg z.c0) 5 = nonResidue *ᵍ CRing.npow z.c1 5 := by
      refine quintEqOfSubEqMul _ (CommRingOps.neg CommRingOps.one) hs ?_
      constructive_ring
    exact nonResidue_not_fifth_power _
      (quintFifthRootOfRatio nonResidue (CommRingOps.neg z.c0) z.c1 (Goldilocks.inv z.c1) hi hE)

/-- Constant coefficient of `(a X^2 + b X + c) · quadCofactor a b c` after `X^5 = 3`. -/
private def quadRem0 (a b c : Goldilocks) : Goldilocks :=
  c *ᵍ CommRingOps.sub (CRing.natCast 2 *ᵍ (a *ᵍ (b *ᵍ c))) (CRing.npow b 3) +ᵍ
    nonResidue *ᵍ CRing.npow a 4

/-- `X` coefficient of `(a X^2 + b X + c) · quadCofactor a b c`. -/
private def quadRem1 (a b c : Goldilocks) : Goldilocks :=
  CommRingOps.sub (CRing.natCast 3 *ᵍ (a *ᵍ ((b *ᵍ b) *ᵍ c)))
    (CRing.npow b 4 +ᵍ (a *ᵍ a) *ᵍ (c *ᵍ c))

/-- The cubic `a^3 X^3 - a^2 b X^2 + (a b^2 - a^2 c) X + (2 a b c - b^3)`: the quotient of
    `a^4 X^5` by `a X^2 + b X + c`. -/
private def quadCofactor (a b c : Goldilocks) : QuinticGoldilocks :=
  ⟨CommRingOps.sub (CRing.natCast 2 *ᵍ (a *ᵍ (b *ᵍ c))) (CRing.npow b 3),
    CommRingOps.sub (a *ᵍ (b *ᵍ b)) ((a *ᵍ a) *ᵍ c),
    CommRingOps.neg ((a *ᵍ a) *ᵍ b),
    CRing.npow a 3,
    CommRingOps.zero⟩

private theorem quadCofactor_mul (z : QuinticGoldilocks) (h3 : z.c3 = CommRingOps.zero)
    (h4 : z.c4 = CommRingOps.zero) :
    z *ᵍ quadCofactor z.c2 z.c1 z.c0 =
      ⟨quadRem0 z.c2 z.c1 z.c0, quadRem1 z.c2 z.c1 z.c0, CommRingOps.zero, CommRingOps.zero,
        CommRingOps.zero⟩ := by
  apply ext <;> quint_coords [quadCofactor, quadRem0, quadRem1, h3, h4] <;> constructive_ring

/-- No quadratic `a X^2 + b X + c` with `a ≠ 0` divides `X^5 - 3` over `Goldilocks`. -/
private theorem goldNoQuadFactor (a b c : Goldilocks) (ha : a ≠ CommRingOps.zero)
    (h1 : quadRem1 a b c = CommRingOps.zero) (h0 : quadRem0 a b c = CommRingOps.zero) :
    False := by
  have hE := quintQuadKey nonResidue a b c h1 h0
  unfold quadRem1 at h1
  unfold quadRem0 at h0
  if hb : b = CommRingOps.zero then
    have hac : (a *ᵍ a) *ᵍ (c *ᵍ c) = CommRingOps.zero := by
      refine quintEqOfSubEqMul2 _ (CommRingOps.neg CommRingOps.one) b
        (CommRingOps.sub (CRing.natCast 3 *ᵍ (a *ᵍ (b *ᵍ c))) (CRing.npow b 3)) h1 hb ?_
      constructive_ring
    have hc : c = CommRingOps.zero := by
      rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hac with h | h
      · rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h with h' | h' <;>
          exact absurd h' ha
      · rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h with h' | h' <;> exact h'
    have hwa : nonResidue *ᵍ CRing.npow a 4 = CommRingOps.zero := by
      refine quintEqOfSubEqMul2 _ CommRingOps.one c
        (CommRingOps.neg (CommRingOps.sub (CRing.natCast 2 *ᵍ (a *ᵍ (b *ᵍ c))) (CRing.npow b 3)))
        h0 hc ?_
      constructive_ring
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hwa with h | h
    · exact nonResidue_ne_zero h
    · exact ha (goldNpowEqZero a 4 h)
  else
    have hab : a *ᵍ b ≠ CommRingOps.zero := fun h =>
      (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h).elim ha hb
    have hi := Goldilocks.mul_inv_cancel hab
    exact nonResidue_not_fifth_power _
      (quintFifthRootOfRatio nonResidue _ (a *ᵍ b) (Goldilocks.inv (a *ᵍ b)) hi hE)

/-- Degree at most two. The cubic cofactor sends `z` to a zero-norm element of degree at most
    one, which vanishes, so `z` would be a quadratic factor of `X^5 - 3`. -/
private theorem eq_zero_of_norm_low2 {z : QuinticGoldilocks} (h3 : z.c3 = CommRingOps.zero)
    (h4 : z.c4 = CommRingOps.zero) (hn : norm z = CommRingOps.zero) :
    z = CommRingOps.zero := by
  if h2 : z.c2 = CommRingOps.zero then
    exact eq_zero_of_norm_low1 h2 h3 h4 hn
  else
    exfalso
    have hprod : norm (z *ᵍ quadCofactor z.c2 z.c1 z.c0) = CommRingOps.zero := by
      rw [norm_mul, hn, LawfulCommRing.zero_mul]
    rw [quadCofactor_mul z h3 h4] at hprod
    have hρ := eq_zero_of_norm_low1 (z := _) (by rfl) (by rfl) (by rfl) hprod
    exact goldNoQuadFactor z.c2 z.c1 z.c0 h2 (congrArg QuinticGoldilocks.c1 hρ)
      (congrArg QuinticGoldilocks.c0 hρ)

/-- `(a X^3 + b X^2 + c X + d) · cubicCofactor a b c` has no `X^3` and no `X^4` term. -/
private def cubicCofactor (a b c : Goldilocks) : QuinticGoldilocks :=
  ⟨CommRingOps.sub (b *ᵍ b) (c *ᵍ a), CommRingOps.neg (b *ᵍ a), a *ᵍ a, CommRingOps.zero,
    CommRingOps.zero⟩

private theorem cubicCofactor_mul_c3 (z : QuinticGoldilocks) (h4 : z.c4 = CommRingOps.zero) :
    (z *ᵍ cubicCofactor z.c3 z.c2 z.c1).c3 = CommRingOps.zero := by
  quint_coords [cubicCofactor, h4]
  constructive_ring

private theorem cubicCofactor_mul_c4 (z : QuinticGoldilocks) (h4 : z.c4 = CommRingOps.zero) :
    (z *ᵍ cubicCofactor z.c3 z.c2 z.c1).c4 = CommRingOps.zero := by
  quint_coords [cubicCofactor, h4]
  constructive_ring

/-- Degree at most three. The quadratic cofactor `q` has nonzero norm by the previous case and
    `z · q` has degree at most two and zero norm, so `z · q = 0` and `z = 0`. -/
private theorem eq_zero_of_norm_low3 {z : QuinticGoldilocks} (h4 : z.c4 = CommRingOps.zero)
    (hn : norm z = CommRingOps.zero) : z = CommRingOps.zero := by
  if h3 : z.c3 = CommRingOps.zero then
    exact eq_zero_of_norm_low2 h3 h4 hn
  else
    exfalso
    have hprod : norm (z *ᵍ cubicCofactor z.c3 z.c2 z.c1) = CommRingOps.zero := by
      rw [norm_mul, hn, LawfulCommRing.zero_mul]
    have hρ := eq_zero_of_norm_low2 (cubicCofactor_mul_c3 z h4) (cubicCofactor_mul_c4 z h4) hprod
    have hqn : norm (cubicCofactor z.c3 z.c2 z.c1) ≠ CommRingOps.zero := fun hq => by
      have hq0 := eq_zero_of_norm_low2 (z := cubicCofactor z.c3 z.c2 z.c1) (by rfl) (by rfl) hq
      have hsq : z.c3 *ᵍ z.c3 = CommRingOps.zero := congrArg QuinticGoldilocks.c2 hq0
      rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hsq with h | h <;> exact h3 h
    exact h3 (congrArg QuinticGoldilocks.c3 (eq_zero_of_mul_eq_zero_of_norm_ne hqn hρ))

/-- `(a X^4 + b X^3 + …) · lastCofactor a b` has no `X^4` term. -/
private def lastCofactor (a b : Goldilocks) : QuinticGoldilocks :=
  ⟨CommRingOps.neg b, a, CommRingOps.zero, CommRingOps.zero, CommRingOps.zero⟩

private theorem lastCofactor_mul_c4 (z : QuinticGoldilocks) :
    (z *ᵍ lastCofactor z.c4 z.c3).c4 = CommRingOps.zero := by
  quint_coords [lastCofactor]
  constructive_ring

/-- **The norm vanishes only at zero.** -/
theorem eq_zero_of_norm_eq_zero {z : QuinticGoldilocks} (hn : norm z = CommRingOps.zero) :
    z = CommRingOps.zero := by
  if h4 : z.c4 = CommRingOps.zero then
    exact eq_zero_of_norm_low3 h4 hn
  else
    exfalso
    have hprod : norm (z *ᵍ lastCofactor z.c4 z.c3) = CommRingOps.zero := by
      rw [norm_mul, hn, LawfulCommRing.zero_mul]
    have hρ := eq_zero_of_norm_low3 (lastCofactor_mul_c4 z) hprod
    have hqn : norm (lastCofactor z.c4 z.c3) ≠ CommRingOps.zero := fun hq => by
      have hq0 := eq_zero_of_norm_low1 (z := lastCofactor z.c4 z.c3) (by rfl) (by rfl) (by rfl) hq
      exact h4 (congrArg QuinticGoldilocks.c1 hq0)
    exact h4 (congrArg QuinticGoldilocks.c4 (eq_zero_of_mul_eq_zero_of_norm_ne hqn hρ))

/-- **Quintic irreducibility, in norm form (`norm_ne_zero`)**: a nonzero element of
    `𝔽_p[X]/(X^5 - 3)` has a nonzero norm, so the ring is a field. -/
theorem norm_ne_zero {z : QuinticGoldilocks} (hz : z ≠ zero) : norm z ≠ Goldilocks.zero :=
  fun hn => hz (eq_zero_of_norm_eq_zero hn)

theorem norm_zero : norm zero = Goldilocks.zero := by
  show norm (ofBase CommRingOps.zero) = CommRingOps.zero
  rw [norm_ofBase]
  constructive_ring

theorem norm_eq_zero_iff (z : QuinticGoldilocks) : norm z = Goldilocks.zero ↔ z = zero :=
  ⟨eq_zero_of_norm_eq_zero, fun h => h ▸ norm_zero⟩

theorem mul_inv_cancel {z : QuinticGoldilocks} (hz : z ≠ zero) :
    z *ᵍ inv z = CommRingOps.one := by
  show z *ᵍ (conj z *ᵍ ofBase (Goldilocks.inv (norm z))) = CommRingOps.one
  rw [← LawfulCommRing.mul_assoc, mul_conj, ← ofBase_mul,
    Goldilocks.mul_inv_cancel (norm_ne_zero hz), ofBase_one]

theorem inv_zero : inv zero = zero := by
  show conj zero *ᵍ ofBase (Goldilocks.inv (norm zero)) = CommRingOps.zero
  rw [norm_zero]
  show conj zero *ᵍ ofBase (LawfulField.inv (CommRingOps.zero : Goldilocks)) = CommRingOps.zero
  rw [LawfulField.inv_zero, ofBase_zero, LawfulCommRing.mul_zero]

/-- The reduction constant is what makes the ring a domain: with `nonResidue` it has no zero
    divisors. -/
theorem mulWith_nonResidue_eq_zero {a b : QuinticGoldilocks}
    (h : mulWith nonResidue a b = zero) : a = zero ∨ b = zero := by
  if ha : a = zero then
    exact .inl ha
  else
    right
    have hmul := congrArg (fun t => inv a *ᵍ t) (show a *ᵍ b = CommRingOps.zero from h)
    rw [LawfulCommRing.mul_zero, ← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm (inv a) a,
      mul_inv_cancel ha, LawfulCommRing.one_mul] at hmul
    exact hmul

/-- With a reduction constant `n = t^5` that IS a fifth power, the same product has the zero
    divisors `X - t` and `X^4 + t X^3 + t^2 X^2 + t^3 X + t^4`. -/
theorem mulWith_fifth_power_zero_divisor (n t : Goldilocks) (h : CRing.npow t 5 = n) :
    mulWith n
      ⟨CommRingOps.neg t, CommRingOps.one, CommRingOps.zero, CommRingOps.zero, CommRingOps.zero⟩
      ⟨CRing.npow t 4, CRing.npow t 3, CRing.npow t 2, t, CommRingOps.one⟩ = zero := by
  have hk : CommRingOps.sub (CRing.npow t 5) n = CommRingOps.zero := by
    rw [h, LawfulCommRing.sub_self]
  apply ext <;> quint_coords []
  · refine quintEqOfSubEqMul _ (CommRingOps.neg CommRingOps.one) hk ?_
    constructive_ring
  all_goals constructive_ring

/-- Inverses are unique: a right inverse is `inv`. -/
theorem inv_eq_of_mul_eq_one {a b : QuinticGoldilocks} (h : a *ᵍ b = CommRingOps.one) :
    inv a = b := by
  have ha : a ≠ zero := fun h0 => by
    rw [h0] at h
    have hz : (zero : QuinticGoldilocks) *ᵍ b = CommRingOps.zero := LawfulCommRing.zero_mul b
    rw [hz] at h
    exact LawfulField.zero_ne_one (F := Goldilocks) (congrArg QuinticGoldilocks.c0 h)
  have e : inv a = inv a *ᵍ (a *ᵍ b) := by rw [h, LawfulCommRing.mul_one]
  rw [e, ← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm (inv a) a, mul_inv_cancel ha,
    LawfulCommRing.one_mul]

end QuinticGoldilocks

instance : NoZeroDivisors QuinticGoldilocks where
  eq_zero_or_eq_zero_of_mul_eq_zero {_ _} h := QuinticGoldilocks.mulWith_nonResidue_eq_zero h

instance : Mul QuinticGoldilocks := ⟨QuinticGoldilocks.mul⟩
instance : Inv QuinticGoldilocks := ⟨QuinticGoldilocks.inv⟩
instance : LawfulField QuinticGoldilocks where
  inv := QuinticGoldilocks.inv
  zero_ne_one h :=
    LawfulField.zero_ne_one (F := Goldilocks) (congrArg QuinticGoldilocks.c0 h)
  inv_zero := QuinticGoldilocks.inv_zero
  mul_inv_cancel := QuinticGoldilocks.mul_inv_cancel

namespace QuinticGoldilocks

theorem fieldInv_eq (z : QuinticGoldilocks) : LawfulField.inv z = inv z := by rfl

/-- The base-field embedding as a `RingHom`. -/
def baseEmbeddingHom : RingHom Goldilocks QuinticGoldilocks where
  toFun := ofBase
  map_zero := ofBase_zero
  map_one := ofBase_one
  map_add := ofBase_add
  map_mul := ofBase_mul

theorem natCast_eq (k : Nat) :
    (CRing.natCast k : QuinticGoldilocks) = ofBase (CRing.natCast k : Goldilocks) := by
  rw [← baseEmbeddingHom.map_natCast]
  rfl

/-- `1, …, p - 1` are nonzero in `QuinticGoldilocks`. -/
theorem natCast_ne_zero (k : Nat) (h1 : 1 ≤ k) (hk : k < goldilocksPrime) :
    (CRing.natCast k : QuinticGoldilocks) ≠ CommRingOps.zero := fun e => by
  rw [natCast_eq] at e
  exact Goldilocks.natCast_ne_zero k h1 hk (congrArg QuinticGoldilocks.c0 e)

end QuinticGoldilocks

namespace GoldilocksField
/-- The zk-Hem v2 challenge field, in the spelling of the quartic tower's exports. -/
abbrev GoldilocksExt5 := Qsag.QuinticGoldilocks
namespace GoldilocksExt5
abbrev c0 (z : GoldilocksExt5) := QuinticGoldilocks.c0 z
abbrev c1 (z : GoldilocksExt5) := QuinticGoldilocks.c1 z
abbrev c2 (z : GoldilocksExt5) := QuinticGoldilocks.c2 z
abbrev c3 (z : GoldilocksExt5) := QuinticGoldilocks.c3 z
abbrev c4 (z : GoldilocksExt5) := QuinticGoldilocks.c4 z
abbrev mk := QuinticGoldilocks.mk
abbrev ext := @QuinticGoldilocks.ext
abbrev nonResidue := QuinticGoldilocks.nonResidue
abbrev zero := QuinticGoldilocks.zero
abbrev one := QuinticGoldilocks.one
abbrev xBasis := QuinticGoldilocks.xBasis
abbrev ofBase := QuinticGoldilocks.ofBase
abbrev embedBase := QuinticGoldilocks.ofBase
abbrev add := QuinticGoldilocks.add
abbrev neg := QuinticGoldilocks.neg
abbrev sub := QuinticGoldilocks.sub
abbrev mul := QuinticGoldilocks.mul
abbrev frob := QuinticGoldilocks.frob
abbrev norm := QuinticGoldilocks.norm
abbrev inv := QuinticGoldilocks.inv

theorem norm_ne_zero {z : GoldilocksExt5} (hz : z ≠ zero) : norm z ≠ Goldilocks.zero :=
  QuinticGoldilocks.norm_ne_zero hz
theorem mul_inv_cancel {z : GoldilocksExt5} (hz : z ≠ zero) :
    CommRingOps.mul z (inv z) = CommRingOps.one := QuinticGoldilocks.mul_inv_cancel hz
theorem ext5_mul_inv_cancel {z : GoldilocksExt5} (hz : z ≠ zero) :
    z * z⁻¹ = one ∧ z⁻¹ * z = one :=
  ⟨QuinticGoldilocks.mul_inv_cancel hz,
    (LawfulCommRing.mul_comm _ _).trans (QuinticGoldilocks.mul_inv_cancel hz)⟩
/-- **Absence of non-trivial zero divisors in `GoldilocksExt5`.** -/
theorem ext5_mul_eq_zero_iff (z w : GoldilocksExt5) : z * w = zero ↔ z = zero ∨ w = zero := by
  constructor
  · exact NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero
  · rintro (rfl | rfl)
    · exact LawfulCommRing.zero_mul w
    · exact LawfulCommRing.mul_zero z
theorem xBasis_pow5_eq_three :
    ((xBasis * xBasis) * (xBasis * xBasis)) * xBasis = embedBase nonResidue :=
  QuinticGoldilocks.xBasis_pow5
theorem nonResidue_not_fifth_power (t : Goldilocks) : CRing.npow t 5 ≠ nonResidue :=
  QuinticGoldilocks.nonResidue_not_fifth_power t
theorem embedBase_c0 (a : Goldilocks) : (embedBase a).c0 = a := QuinticGoldilocks.ofBase_c0 a
theorem embedBase_zero : embedBase Goldilocks.zero = zero := QuinticGoldilocks.ofBase_zero
theorem embedBase_one : embedBase Goldilocks.one = one := QuinticGoldilocks.ofBase_one
theorem embedBase_injective {a b : Goldilocks} (h : embedBase a = embedBase b) : a = b :=
  QuinticGoldilocks.ofBase_injective h
theorem embedBase_add (a b : Goldilocks) :
    embedBase (CommRingOps.add a b) = CommRingOps.add (embedBase a) (embedBase b) :=
  QuinticGoldilocks.ofBase_add a b
theorem embedBase_sub (a b : Goldilocks) :
    embedBase (CommRingOps.sub a b) = CommRingOps.sub (embedBase a) (embedBase b) :=
  QuinticGoldilocks.ofBase_sub a b
theorem embedBase_mul (a b : Goldilocks) :
    embedBase (CommRingOps.mul a b) = CommRingOps.mul (embedBase a) (embedBase b) :=
  QuinticGoldilocks.ofBase_mul a b
theorem frob_eq_self_iff (z : GoldilocksExt5) : frob z = z ↔ z = embedBase z.c0 :=
  QuinticGoldilocks.frob_eq_self_iff z
theorem zero_eq_ringZero : zero = CommRingOps.zero := by rfl
theorem one_eq_ringOne : one = CommRingOps.one := by rfl
end GoldilocksExt5
end GoldilocksField

/-! ### Kernel-evaluated known answers

`frob`, `norm` and `inv` are sealed outside this module, so their concrete values are stated
here; `Tests/QuinticExt5Teeth` pairs them with the multiplication known answers. The values
were computed independently (Python, `F_p[X]/(X^5 - 3)` with `p = 2^64 - 2^32 + 1`) and pin
`Fp5` in `crates/qsag-agg/src/zk_hem/v2/field5.rs`. -/

namespace QuinticGoldilocks

/-- The element `1 + 2 X + 3 X^2 + 4 X^3 + 5 X^4`. -/
def kat12345 : QuinticGoldilocks :=
  ⟨Goldilocks.ofNat 1, Goldilocks.ofNat 2, Goldilocks.ofNat 3, Goldilocks.ofNat 4,
    Goldilocks.ofNat 5⟩

theorem frob_kat12345 : frob kat12345 =
    ⟨Goldilocks.ofNat 1, Goldilocks.ofNat 2082576518476559110,
      Goldilocks.ofNat 10568986813412808496, Goldilocks.ofNat 846350220555798788,
      Goldilocks.ofNat 6865216354783480110⟩ := by decide +kernel

theorem norm_kat12345 : norm kat12345 = Goldilocks.ofNat 214567 := by decide +kernel

theorem inv_kat12345 : inv kat12345 =
    ⟨Goldilocks.ofNat 16227807958868272813, Goldilocks.ofNat 4552730750487813724,
      Goldilocks.ofNat 11612833514307017418, Goldilocks.ofNat 9161515214422980997,
      Goldilocks.ofNat 13509202856671625680⟩ := by decide +kernel

/-- A full-width element (every limb above `2^56`). -/
def katWide : QuinticGoldilocks :=
  ⟨Goldilocks.ofNat 81985529216486895, Goldilocks.ofNat 18364758544493064720,
    Goldilocks.ofNat 16045690984503098046, Goldilocks.ofNat 1089357896855742840,
    Goldilocks.ofNat 1234605616436508552⟩

theorem frob_katWide : frob katWide =
    ⟨Goldilocks.ofNat 81985529216486895, Goldilocks.ofNat 9961272706250400476,
      Goldilocks.ofNat 4912495906482251711, Goldilocks.ofNat 9291945967817452589,
      Goldilocks.ofNat 15493897884983376685⟩ := by decide +kernel

theorem norm_katWide : norm katWide = Goldilocks.ofNat 11913873338696290852 := by
  decide +kernel

theorem inv_katWide : inv katWide =
    ⟨Goldilocks.ofNat 17033286724174752684, Goldilocks.ofNat 16464919206864593009,
      Goldilocks.ofNat 3901309921467269908, Goldilocks.ofNat 17713944588012397749,
      Goldilocks.ofNat 16392840534563784651⟩ := by decide +kernel

/-- A nonzero element whose inverse is nonzero: the hypothesis of `ext5_mul_inv_cancel` is
    inhabited and its conclusion is not vacuous. -/
theorem witness_ext5_nontrivial_element :
    ∃ z : GoldilocksField.GoldilocksExt5, z ≠ GoldilocksField.GoldilocksExt5.zero ∧
      z⁻¹ ≠ GoldilocksField.GoldilocksExt5.zero := by
  have key : ∀ z : GoldilocksField.GoldilocksExt5, z ≠ GoldilocksField.GoldilocksExt5.zero →
      z⁻¹ ≠ GoldilocksField.GoldilocksExt5.zero := by
    intro z hz h
    have hc := (GoldilocksField.GoldilocksExt5.ext5_mul_inv_cancel hz).2
    rw [h] at hc
    have hZero : GoldilocksField.GoldilocksExt5.zero * z = GoldilocksField.GoldilocksExt5.zero :=
      LawfulCommRing.zero_mul z
    rw [hZero] at hc
    exact LawfulField.zero_ne_one (F := Goldilocks) (congrArg QuinticGoldilocks.c0 hc)
  have hz : xBasis ≠ GoldilocksField.GoldilocksExt5.zero := fun h =>
    LawfulField.zero_ne_one (F := Goldilocks) (congrArg QuinticGoldilocks.c1 h).symm
  exact ⟨_, hz, key _ hz⟩

end QuinticGoldilocks

end Qsag
end
#verify_constructive
  Qsag.goldilocks_three_fifth_modPow
  Qsag.QuinticGoldilocks.nonResidue_not_fifth_power
  Qsag.QuinticGoldilocks.xBasis_pow5
  Qsag.QuinticGoldilocks.zeta_pow5
  Qsag.QuinticGoldilocks.frob_add
  Qsag.QuinticGoldilocks.frob_mul
  Qsag.QuinticGoldilocks.frob_one
  Qsag.QuinticGoldilocks.frob_pow5
  Qsag.QuinticGoldilocks.frob_eq_self_iff
  Qsag.QuinticGoldilocks.ofBase_injective
  Qsag.QuinticGoldilocks.ofBase_add
  Qsag.QuinticGoldilocks.ofBase_mul
  Qsag.QuinticGoldilocks.mul_conj
  Qsag.QuinticGoldilocks.norm_mul
  Qsag.QuinticGoldilocks.norm_ofBase
  Qsag.QuinticGoldilocks.conj_eq_two_mul
  Qsag.QuinticGoldilocks.mul_ofBase
  Qsag.QuinticGoldilocks.inv_eq_scale
  Qsag.QuinticGoldilocks.eq_zero_of_norm_eq_zero
  Qsag.QuinticGoldilocks.norm_ne_zero
  Qsag.QuinticGoldilocks.norm_eq_zero_iff
  Qsag.QuinticGoldilocks.mul_inv_cancel
  Qsag.QuinticGoldilocks.inv_zero
  Qsag.QuinticGoldilocks.inv_eq_of_mul_eq_one
  Qsag.QuinticGoldilocks.mulWith_nonResidue_eq_zero
  Qsag.QuinticGoldilocks.mulWith_fifth_power_zero_divisor
  Qsag.QuinticGoldilocks.natCast_ne_zero
  Qsag.GoldilocksField.GoldilocksExt5.ext5_mul_inv_cancel
  Qsag.GoldilocksField.GoldilocksExt5.ext5_mul_eq_zero_iff
  Qsag.GoldilocksField.GoldilocksExt5.xBasis_pow5_eq_three
  Qsag.GoldilocksField.GoldilocksExt5.frob_eq_self_iff
  Qsag.QuinticGoldilocks.frob_kat12345
  Qsag.QuinticGoldilocks.norm_kat12345
  Qsag.QuinticGoldilocks.inv_kat12345
  Qsag.QuinticGoldilocks.frob_katWide
  Qsag.QuinticGoldilocks.norm_katWide
  Qsag.QuinticGoldilocks.inv_katWide
  Qsag.QuinticGoldilocks.witness_ext5_nontrivial_element
#verify_inhabited Qsag.GoldilocksField.GoldilocksExt5.ext5_mul_inv_cancel
  Qsag.QuinticGoldilocks.witness_ext5_nontrivial_element
