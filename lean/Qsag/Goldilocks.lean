module
/-
# Qsag.Goldilocks — Zero-Mathlib Commutative Rings, Goldilocks Field, Ext2 & Root Bounds

Self-contained Lean 4.35 algebraic foundation (`Init` only, 0 Mathlib, 0 sorry, 0 custom axioms):
1. `CommRingOps R`, `LawfulCommRing R`, and `NoZeroDivisors R` with derived ring identities.
2. Canonical 64-bit `Goldilocks` prime field ($p = 2^{64} - 2^{32} + 1 = 18446744069414584321$)
   backed by hardware-exact 128-to-64 shift/mask modular reduction (`goldilocksReduce128Spec_sound`).
3. Constructive zero-axiom Proth primality proof (`goldilocksPrime_isPrime`) via Fermat's Little
   Theorem (`IsPrimeNat.pow_sub_one_mod`) and Lucas/Euler witness $7^{(p-1)/2} \equiv -1 \pmod p$.
4. Quadratic extension field `GoldilocksExt2` ($\mathbb{F}_{p^2} = \mathbb{F}_p[u]/(u^2 - 7)$)
   with irreducibility proof (`nonResidue_not_square`), constructive inversion (`mul_inv_cancel`),
   and $> 2^{127}$ challenge cardinality (`goldilocksExt2_card_gt_two_pow_126`).
5. Univariate `RoundPoly R` synthetic division (`evalCoeffs_eq_mul_quotLinear_add`) and
   Factor-Theorem root bound (`roots_nodup_length_le`).
-/

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

/-! ## 2. Goldilocks Prime ($p = 2^{64} - 2^{32} + 1$) Hardware-Exact 128-to-64 Reduction -/

/-- The Goldilocks prime $p = 2^{64} - 2^{32} + 1 = 18446744069414584321$. -/
@[expose] def goldilocksPrime : Nat := 18446744069414584321

/-- The Goldilocks reduction constant $\epsilon = 2^{32} - 1 = 4294967295$. -/
def goldilocksEpsilon : Nat := 4294967295

theorem goldilocks_base_congruence :
    2 ^ 64 = goldilocksPrime + goldilocksEpsilon ∧
    (2 ^ 64) % goldilocksPrime = goldilocksEpsilon ∧
    (2 ^ 96 + 1) % goldilocksPrime = 0 := by
  refine ⟨by decide, by decide, by decide⟩

def goldilocksCanon64 (x : Nat) : Nat :=
  if goldilocksPrime ≤ x then x - goldilocksPrime else x

theorem goldilocksCanon64_spec {x : Nat} (hx : x < 2 ^ 64) :
    goldilocksCanon64 x < goldilocksPrime ∧
    goldilocksCanon64 x = x % goldilocksPrime := by
  unfold goldilocksCanon64
  split
  · rename_i hge
    have hlt : x - goldilocksPrime < goldilocksPrime := by unfold goldilocksPrime at *; omega
    refine ⟨hlt, ?_⟩
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
  · rename_i hlt'
    have hlt : x < goldilocksPrime := by omega
    exact ⟨hlt, (Nat.mod_eq_of_lt hlt).symm⟩

@[expose] def goldilocksAddSpec (a b : Nat) : Nat :=
  let ca := if goldilocksPrime ≤ a then a - goldilocksPrime else a
  let cb := if goldilocksPrime ≤ b then b - goldilocksPrime else b
  if goldilocksPrime ≤ ca + cb then ca + cb - goldilocksPrime else ca + cb

theorem goldilocksAddSpec_spec {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    goldilocksAddSpec a b < goldilocksPrime ∧
    goldilocksAddSpec a b = (a + b) % goldilocksPrime := by
  rcases goldilocksCanon64_spec ha with ⟨hcaLt, hcaMod⟩
  rcases goldilocksCanon64_spec hb with ⟨hcbLt, hcbMod⟩
  have hSumMod : (a + b) % goldilocksPrime =
      (goldilocksCanon64 a + goldilocksCanon64 b) % goldilocksPrime := by
    rw [Nat.add_mod, ← hcaMod, ← hcbMod]
  change (if goldilocksPrime ≤ goldilocksCanon64 a + goldilocksCanon64 b
          then goldilocksCanon64 a + goldilocksCanon64 b - goldilocksPrime
          else goldilocksCanon64 a + goldilocksCanon64 b) < goldilocksPrime ∧
         (if goldilocksPrime ≤ goldilocksCanon64 a + goldilocksCanon64 b
          then goldilocksCanon64 a + goldilocksCanon64 b - goldilocksPrime
          else goldilocksCanon64 a + goldilocksCanon64 b) = (a + b) % goldilocksPrime
  split
  · rename_i hge
    have hlt : goldilocksCanon64 a + goldilocksCanon64 b - goldilocksPrime < goldilocksPrime := by omega
    refine ⟨hlt, ?_⟩
    rw [hSumMod, Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
  · rename_i hlt'
    have hlt : goldilocksCanon64 a + goldilocksCanon64 b < goldilocksPrime := by omega
    rw [hSumMod, Nat.mod_eq_of_lt hlt]
    exact ⟨hlt, rfl⟩

@[expose] def goldilocksSubSpec (a b : Nat) : Nat :=
  let ca := if goldilocksPrime ≤ a then a - goldilocksPrime else a
  let cb := if goldilocksPrime ≤ b then b - goldilocksPrime else b
  if cb ≤ ca then ca - cb else (goldilocksPrime - cb) + ca

theorem goldilocksSubSpec_spec {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    goldilocksSubSpec a b < goldilocksPrime ∧
    goldilocksSubSpec a b =
      (goldilocksCanon64 a + goldilocksPrime - goldilocksCanon64 b) % goldilocksPrime := by
  rcases goldilocksCanon64_spec ha with ⟨hcaLt, _⟩
  rcases goldilocksCanon64_spec hb with ⟨hcbLt, _⟩
  change (if goldilocksCanon64 b ≤ goldilocksCanon64 a
          then goldilocksCanon64 a - goldilocksCanon64 b
          else (goldilocksPrime - goldilocksCanon64 b) + goldilocksCanon64 a) < goldilocksPrime ∧
         (if goldilocksCanon64 b ≤ goldilocksCanon64 a
          then goldilocksCanon64 a - goldilocksCanon64 b
          else (goldilocksPrime - goldilocksCanon64 b) + goldilocksCanon64 a) =
           (goldilocksCanon64 a + goldilocksPrime - goldilocksCanon64 b) % goldilocksPrime
  split
  · rename_i hle
    have hlt : goldilocksCanon64 a - goldilocksCanon64 b < goldilocksPrime := by omega
    refine ⟨hlt, ?_⟩
    have hDecomp : goldilocksCanon64 a + goldilocksPrime - goldilocksCanon64 b =
        (goldilocksCanon64 a - goldilocksCanon64 b) + goldilocksPrime * 1 := by omega
    rw [hDecomp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  · rename_i hgt
    have hlt : (goldilocksPrime - goldilocksCanon64 b) + goldilocksCanon64 a < goldilocksPrime := by omega
    refine ⟨hlt, ?_⟩
    have hEq : goldilocksCanon64 a + goldilocksPrime - goldilocksCanon64 b =
        (goldilocksPrime - goldilocksCanon64 b) + goldilocksCanon64 a := by omega
    rw [hEq, Nat.mod_eq_of_lt hlt]

/-- Hardware-exact 128-to-64 Goldilocks shift/mask reduction (`crates/qsag-core/src/field/goldilocks.rs`). -/
@[expose] def goldilocksReduce128Spec (lo hi : Nat) : Nat :=
  let hiLo := hi % 4294967296
  let hiHi := hi / 4294967296
  let mid := hiLo * 4294967296 - hiLo
  goldilocksSubSpec (goldilocksAddSpec lo mid) hiHi

private theorem goldilocksReduce128_identity (lo hi hiLo hiHi t1 q : Nat)
    (hHiLo : hiLo < 4294967296) (hHiHi : hiHi < 4294967296)
    (hhi : hiLo + 4294967296 * hiHi = hi)
    (ht1 : t1 + goldilocksPrime * q = lo + (hiLo * 4294967296 - hiLo)) :
    (t1 + goldilocksPrime - hiHi) % goldilocksPrime = (lo + 2 ^ 64 * hi) % goldilocksPrime := by
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
  have key : lo + 2 ^ 64 * hi + goldilocksPrime * 1 =
      (t1 + goldilocksPrime - hiHi) + goldilocksPrime * (q + hiLo + 4294967297 * hiHi) := by
    rw [h64]; unfold goldilocksPrime at *; omega
  rw [← Nat.add_mul_mod_self_left (lo + 2 ^ 64 * hi) goldilocksPrime 1, key, Nat.add_mul_mod_self_left]

/-- **`goldilocksReduce128Spec_sound`**: for all `lo, hi < 2^64`, the shift/mask reduction produces a
    canonical element `< p` equal to `(lo + 2^64 * hi) % p`. -/
theorem goldilocksReduce128Spec_sound {lo hi : Nat}
    (hLo : lo < 2 ^ 64) (hHi : hi < 2 ^ 64) :
    goldilocksReduce128Spec lo hi < goldilocksPrime ∧
    goldilocksReduce128Spec lo hi = (lo + 2 ^ 64 * hi) % goldilocksPrime := by
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
  have hHiLo : hi % 4294967296 < 4294967296 := Nat.mod_lt hi (by decide)
  have hHiHi : hi / 4294967296 < 4294967296 := by
    rw [h64] at hHi
    omega
  unfold goldilocksReduce128Spec
  dsimp only
  have hMidLt : hi % 4294967296 * 4294967296 - hi % 4294967296 < 2 ^ 64 := by rw [h64]; omega
  have hHiHiLt : hi / 4294967296 < 2 ^ 64 := by rw [h64]; omega
  obtain ⟨ht1LtP, ht1Mod⟩ := goldilocksAddSpec_spec hLo hMidLt
  have ht1Lt64 :
      goldilocksAddSpec lo (hi % 4294967296 * 4294967296 - hi % 4294967296) < 2 ^ 64 := by
    unfold goldilocksPrime at ht1LtP; rw [h64]; omega
  obtain ⟨hSubLtP, hSubMod⟩ := goldilocksSubSpec_spec ht1Lt64 hHiHiLt
  refine ⟨hSubLtP, ?_⟩
  rw [hSubMod]
  have hc1 : goldilocksCanon64 (goldilocksAddSpec lo (hi % 4294967296 * 4294967296 - hi % 4294967296)) =
      goldilocksAddSpec lo (hi % 4294967296 * 4294967296 - hi % 4294967296) := by
    unfold goldilocksCanon64; split <;> omega
  have hc2 : goldilocksCanon64 (hi / 4294967296) = hi / 4294967296 := by
    unfold goldilocksCanon64 goldilocksPrime; split <;> omega
  rw [hc1, hc2, ht1Mod]
  exact goldilocksReduce128_identity lo hi (hi % 4294967296) (hi / 4294967296) _ _ hHiLo hHiHi
    (Nat.mod_add_div hi 4294967296)
    (Nat.mod_add_div (lo + (hi % 4294967296 * 4294967296 - hi % 4294967296)) goldilocksPrime)

/-! ## 3. Canonical `Goldilocks` Carrier & `LawfulCommRing` Instance -/

/-- Canonical element of $\mathbb{F}_p$ ($p = 2^{64} - 2^{32} + 1$). -/
structure Goldilocks where
  val : Nat
  isLt : val < goldilocksPrime
  deriving DecidableEq, Repr

namespace Goldilocks

theorem ext {a b : Goldilocks} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp only at h; subst h; rfl

theorem val_lt_two_pow_64 (a : Goldilocks) : a.val < 2 ^ 64 := by
  have hp : goldilocksPrime < 2 ^ 64 := by decide
  exact Nat.lt_trans a.isLt hp

@[expose] def ofNat (n : Nat) : Goldilocks :=
  ⟨n % goldilocksPrime, Nat.mod_lt n (by decide)⟩

@[expose] def zero : Goldilocks := ⟨0, by decide⟩
@[expose] def one : Goldilocks := ⟨1, by decide⟩

instance : Inhabited Goldilocks := ⟨zero⟩

@[simp] theorem zero_val : zero.val = 0 := rfl
@[simp] theorem one_val : one.val = 1 := rfl
@[simp] theorem ofNat_val (n : Nat) : (ofNat n).val = n % goldilocksPrime := rfl

theorem canon_eq_val (a : Goldilocks) : goldilocksCanon64 a.val = a.val := by
  unfold goldilocksCanon64
  have h := a.isLt
  split <;> omega

@[expose] def add (a b : Goldilocks) : Goldilocks :=
  ⟨goldilocksAddSpec a.val b.val,
   (goldilocksAddSpec_spec (val_lt_two_pow_64 a) (val_lt_two_pow_64 b)).1⟩

theorem add_val (a b : Goldilocks) :
    (add a b).val = (a.val + b.val) % goldilocksPrime :=
  (goldilocksAddSpec_spec (val_lt_two_pow_64 a) (val_lt_two_pow_64 b)).2

@[expose] def sub (a b : Goldilocks) : Goldilocks :=
  ⟨goldilocksSubSpec a.val b.val,
   (goldilocksSubSpec_spec (val_lt_two_pow_64 a) (val_lt_two_pow_64 b)).1⟩

theorem sub_val (a b : Goldilocks) :
    (sub a b).val = (a.val + goldilocksPrime - b.val) % goldilocksPrime := by
  unfold sub
  dsimp only
  have h := (goldilocksSubSpec_spec (val_lt_two_pow_64 a) (val_lt_two_pow_64 b)).2
  simpa only [canon_eq_val] using h

def neg (a : Goldilocks) : Goldilocks :=
  sub zero a

theorem neg_val (a : Goldilocks) :
    (neg a).val = (goldilocksPrime - a.val) % goldilocksPrime := by
  unfold neg
  simpa [zero] using sub_val zero a

theorem div64_lt_of_lt_square (x : Nat) (h : x < 2 ^ 64 * 2 ^ 64) :
    x / 2 ^ 64 < 2 ^ 64 := by omega

@[expose] def mul (a b : Goldilocks) : Goldilocks :=
  let prod := a.val * b.val
  let lo := prod % (2 ^ 64)
  let hi := prod / (2 ^ 64)
  have hLo : lo < 2 ^ 64 := Nat.mod_lt prod (by decide)
  have hHi : hi < 2 ^ 64 :=
    div64_lt_of_lt_square _ (Nat.mul_lt_mul'' (val_lt_two_pow_64 a) (val_lt_two_pow_64 b))
  ⟨goldilocksReduce128Spec lo hi, (goldilocksReduce128Spec_sound hLo hHi).1⟩

theorem mul_val (a b : Goldilocks) :
    (mul a b).val = (a.val * b.val) % goldilocksPrime := by
  unfold mul
  dsimp only
  have hLo : (a.val * b.val) % (2 ^ 64) < 2 ^ 64 := Nat.mod_lt _ (by decide)
  have hHi : (a.val * b.val) / (2 ^ 64) < 2 ^ 64 :=
    div64_lt_of_lt_square _ (Nat.mul_lt_mul'' (val_lt_two_pow_64 a) (val_lt_two_pow_64 b))
  rw [(goldilocksReduce128Spec_sound hLo hHi).2, Nat.mod_add_div]

instance : CommRingOps Goldilocks where
  zero := zero
  one := one
  add := add
  mul := mul
  neg := neg
  sub := sub

instance : LawfulCommRing Goldilocks where
  add_assoc a b c := by
    apply ext
    simp only [CommRingOps.add, add_val, Nat.add_mod_mod, Nat.mod_add_mod, Nat.add_assoc]
  add_comm a b := by
    apply ext
    simp only [CommRingOps.add, add_val, Nat.add_comm]
  zero_add a := by
    apply ext
    simp only [CommRingOps.add, CommRingOps.zero, add_val, zero, Nat.zero_add,
      Nat.mod_eq_of_lt a.isLt]
  add_zero a := by
    apply ext
    simp only [CommRingOps.add, CommRingOps.zero, add_val, zero, Nat.add_zero,
      Nat.mod_eq_of_lt a.isLt]
  add_left_neg a := by
    apply ext
    simp only [CommRingOps.add, CommRingOps.neg, CommRingOps.zero, add_val, neg_val, zero,
      Nat.mod_add_mod]
    have ha := a.isLt
    have hsum : goldilocksPrime - a.val + a.val = goldilocksPrime := by omega
    rw [hsum, Nat.mod_self]
  sub_eq_add_neg a b := by
    apply ext
    simp only [CommRingOps.sub, CommRingOps.add, CommRingOps.neg, sub_val, add_val, neg_val,
      Nat.add_mod_mod]
    have hb := b.isLt
    have h1 : a.val + (goldilocksPrime - b.val) = a.val + goldilocksPrime - b.val := by omega
    rw [h1]
  mul_assoc a b c := by
    apply ext
    simp only [CommRingOps.mul, mul_val]
    rw [Nat.mod_mul_mod, Nat.mul_assoc, ← Nat.mul_mod_mod]
  mul_comm a b := by
    apply ext
    simp only [CommRingOps.mul, mul_val, Nat.mul_comm]
  one_mul a := by
    apply ext
    simp only [CommRingOps.mul, CommRingOps.one, mul_val, one, Nat.one_mul,
      Nat.mod_eq_of_lt a.isLt]
  mul_one a := by
    apply ext
    simp only [CommRingOps.mul, CommRingOps.one, mul_val, one, Nat.mul_one,
      Nat.mod_eq_of_lt a.isLt]
  left_distrib a b c := by
    apply ext
    simp only [CommRingOps.mul, CommRingOps.add, mul_val, add_val]
    rw [Nat.mul_mod_mod, Nat.add_mod_mod, Nat.mod_add_mod, ← Nat.left_distrib]
  right_distrib a b c := by
    apply ext
    simp only [CommRingOps.mul, CommRingOps.add, mul_val, add_val]
    rw [Nat.mod_mul_mod, Nat.add_mod_mod, Nat.mod_add_mod, ← Nat.right_distrib]

end Goldilocks

/-! ## 4. Signed Integer Projection `goldOfInt` for Linear-Layer Homomorphisms -/

abbrev goldP : Int := (goldilocksPrime : Int)

@[expose] def goldOfInt (z : Int) : Goldilocks :=
  ⟨(z % goldP).toNat, by
    have := Int.emod_nonneg z (show goldP ≠ 0 by decide)
    have := Int.emod_lt_of_pos z (show 0 < goldP by decide)
    dsimp only [goldP] at *
    omega⟩

theorem goldOfInt_val (z : Int) : ((goldOfInt z).val : Int) = z % goldP :=
  Int.toNat_of_nonneg (Int.emod_nonneg z (by decide))

theorem goldOfInt_nat (a : Goldilocks) : goldOfInt a.val = a := by
  apply Goldilocks.ext
  have h : (a.val : Int) % goldP = a.val :=
    Int.emod_eq_of_lt (by omega) (by have := a.isLt; dsimp only [goldP]; omega)
  have := goldOfInt_val a.val
  omega

theorem gold_add_int (a b : Goldilocks) :
    ((Goldilocks.add a b).val : Int) = ((a.val : Int) + b.val) % goldP := by
  rw [Goldilocks.add_val, Int.natCast_emod, Int.natCast_add]

theorem gold_mul_int (a b : Goldilocks) :
    ((Goldilocks.mul a b).val : Int) = ((a.val : Int) * b.val) % goldP := by
  rw [Goldilocks.mul_val, Int.natCast_emod, Int.natCast_mul]

theorem gold_sub_int (a b : Goldilocks) :
    ((Goldilocks.sub a b).val : Int) = ((a.val : Int) - b.val) % goldP := by
  rw [Goldilocks.sub_val, Int.natCast_emod,
    Int.ofNat_sub (by have := b.isLt; omega), Int.natCast_add]
  have he : (a.val : Int) + goldP - b.val = ((a.val : Int) - b.val) + goldP := by omega
  rw [he, Int.add_emod_right]

theorem goldOfInt_add (a b : Int) :
    Goldilocks.add (goldOfInt a) (goldOfInt b) = goldOfInt (a + b) := by
  apply Goldilocks.ext; apply Int.ofNat_inj.mp
  rw [gold_add_int, goldOfInt_val, goldOfInt_val, goldOfInt_val, ← Int.add_emod]

theorem goldOfInt_sub (a b : Int) :
    Goldilocks.sub (goldOfInt a) (goldOfInt b) = goldOfInt (a - b) := by
  apply Goldilocks.ext; apply Int.ofNat_inj.mp
  rw [gold_sub_int, goldOfInt_val, goldOfInt_val, goldOfInt_val, ← Int.sub_emod]

theorem goldOfInt_mul (a b : Int) :
    Goldilocks.mul (goldOfInt a) (goldOfInt b) = goldOfInt (a * b) := by
  apply Goldilocks.ext; apply Int.ofNat_inj.mp
  rw [gold_mul_int, goldOfInt_val, goldOfInt_val, goldOfInt_val, ← Int.mul_emod]

/-! ## 5. Zero-Axiom Proth Primality of `goldilocksPrime` & Field Inversion -/

private def strictNat (n : Nat) (k : Nat → Nat) : Nat :=
  match n with
  | 0 => k 0
  | m + 1 => k (m + 1)

private theorem strictNat_eq (n : Nat) (k : Nat → Nat) : strictNat n k = k n := by
  cases n <;> rfl

def modPowFuel : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, m => 1 % m
  | fuel + 1, base, exp, m =>
    if exp = 0 then 1 % m
    else
      strictNat (modPowFuel fuel base (exp / 2) m) fun half =>
        strictNat ((half * half) % m) fun sq =>
          if exp % 2 = 1 then (sq * (base % m)) % m else sq

private theorem pow_two_mul (b k : Nat) : b ^ (2 * k) = (b ^ k) * (b ^ k) := by
  rw [Nat.mul_comm 2 k, Nat.pow_mul, Nat.pow_succ, Nat.pow_one]

theorem modPowFuel_eq_pow_mod :
    ∀ (fuel base exp m : Nat), exp < 2 ^ fuel → modPowFuel fuel base exp m = (base ^ exp) % m
  | 0, _, exp, m, hlt => by
    have he0 : exp = 0 := by simp at hlt; omega
    subst he0; simp [modPowFuel]
  | fuel + 1, base, exp, m, hlt => by
    simp only [modPowFuel]
    if h0 : exp = 0 then
      subst h0; simp
    else
      simp only [h0, ↓reduceIte, strictNat_eq]
      have hexpHalf : exp / 2 < 2 ^ fuel := by
        rw [Nat.pow_succ] at hlt; omega
      have ih := modPowFuel_eq_pow_mod fuel base (exp / 2) m hexpHalf
      have hsq : ((modPowFuel fuel base (exp / 2) m) * (modPowFuel fuel base (exp / 2) m)) % m =
          (base ^ (2 * (exp / 2))) % m := by
        rw [ih, ← Nat.mul_mod, ← pow_two_mul]
      have hmod2 : exp % 2 = 0 ∨ exp % 2 = 1 := by omega
      rcases hmod2 with hr0 | hr1
      · simp only [hr0, show ¬ (0 = 1) by decide, ↓reduceIte]
        have hexp : 2 * (exp / 2) = exp := by omega
        rw [hsq, hexp]
      · simp only [hr1, ↓reduceIte]
        have hexp : exp = 2 * (exp / 2) + 1 := by omega
        conv => rhs; rw [hexp, Nat.pow_add, Nat.pow_one, Nat.mul_mod]
        rw [hsq]

/-- Elementary primality predicate on `Nat`. -/
def IsPrimeNat (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

private def minDivisorAux (n d : Nat) : Nat → Nat
  | 0 => n
  | fuel + 1 => if n % d = 0 then d else minDivisorAux n (d + 1) fuel

private def minDivisor (n : Nat) : Nat :=
  if n < 2 then n else minDivisorAux n 2 n

private theorem minDivisorAux_spec :
    ∀ (fuel n d : Nat),
      2 ≤ n → 2 ≤ d → n ≤ d + fuel →
      (∀ k : Nat, 2 ≤ k → k < d → ¬ (k ∣ n)) →
      let q := minDivisorAux n d fuel
      2 ≤ q ∧ q ∣ n ∧ (∀ k : Nat, 2 ≤ k → k < q → ¬ (k ∣ n))
  | 0, n, d, hn2, _, _, hno => by
    dsimp only [minDivisorAux]
    refine ⟨hn2, Nat.dvd_refl n, ?_⟩
    intro k hk2 hklt
    exact hno k hk2 (by omega)
  | fuel + 1, n, d, hn2, hd, hle, hno => by
    dsimp only [minDivisorAux]
    if hmod : n % d = 0 then
      simp only [hmod, ↓reduceIte]
      exact ⟨hd, Nat.dvd_of_mod_eq_zero hmod, hno⟩
    else
      simp only [hmod, ↓reduceIte]
      apply minDivisorAux_spec fuel n (d + 1) hn2 (by omega) (by omega)
      intro k hk2 hklt
      if hkd : k = d then
        subst hkd
        intro hdvd
        exact hmod (Nat.mod_eq_zero_of_dvd hdvd)
      else
        exact hno k hk2 (by omega)

private theorem minDivisor_isPrime {n : Nat} (hn : 2 ≤ n) :
    IsPrimeNat (minDivisor n) ∧ minDivisor n ∣ n ∧ minDivisor n ≤ n := by
  unfold minDivisor
  have hnot : ¬ n < 2 := by omega
  simp only [hnot, ↓reduceIte]
  obtain ⟨hq2, hqdvd, hqmin⟩ := minDivisorAux_spec n n 2 hn (by decide) (by omega) (by intros; omega)
  have hqle : minDivisorAux n 2 n ≤ n := Nat.le_of_dvd (by omega) hqdvd
  refine ⟨⟨hq2, ?_⟩, hqdvd, hqle⟩
  intro d hd
  if hd1 : d = 1 then exact .inl hd1
  else if hdq : d = minDivisorAux n 2 n then exact .inr hdq
  else
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
    have hdle : d ≤ minDivisorAux n 2 n := Nat.le_of_dvd (by omega) hd
    exact False.elim (hqmin d (by omega) (by omega) (Nat.dvd_trans hd hqdvd))

def extGcd (a b : Nat) : Nat × Int × Int :=
  if _hb : b = 0 then (a, 1, 0)
  else
    let r := extGcd b (a % b)
    (r.1, r.2.2, r.2.1 - ((a / b : Nat) : Int) * r.2.2)
termination_by b
decreasing_by exact Nat.mod_lt a (Nat.pos_of_ne_zero _hb)

theorem extGcd_dvd (a b : Nat) : (extGcd a b).1 ∣ a ∧ (extGcd a b).1 ∣ b := by
  if hb : b = 0 then
    subst hb
    rw [extGcd]
    simp only [↓reduceDIte]
    exact ⟨Nat.dvd_refl a, Nat.dvd_zero a⟩
  else
    obtain ⟨hdb, hdmod⟩ := extGcd_dvd b (a % b)
    have heq : (extGcd a b).1 = (extGcd b (a % b)).1 := by
      conv => lhs; rw [extGcd]
      simp [hb]
    rw [heq]
    refine ⟨?_, hdb⟩
    have hdiv : b * (a / b) + a % b = a := Nat.div_add_mod a b
    have hmul : (extGcd b (a % b)).1 ∣ b * (a / b) := Nat.dvd_trans hdb (Nat.dvd_mul_right b (a / b))
    have hsum := Nat.dvd_add hmul hdmod
    rwa [hdiv] at hsum
termination_by b
decreasing_by exact Nat.mod_lt a (Nat.pos_of_ne_zero hb)

theorem extGcd_bezout (a b : Nat) :
    (a : Int) * (extGcd a b).2.1 + (b : Int) * (extGcd a b).2.2 = ((extGcd a b).1 : Int) := by
  if hb : b = 0 then
    subst hb
    rw [extGcd]
    simp
  else
    have ih := extGcd_bezout b (a % b)
    have hstep : extGcd a b =
        ((extGcd b (a % b)).1,
         (extGcd b (a % b)).2.2,
         (extGcd b (a % b)).2.1 - ((a / b : Nat) : Int) * (extGcd b (a % b)).2.2) := by
      conv => lhs; rw [extGcd]
      simp [hb]
    rw [hstep]
    dsimp only
    have hdivInt : (b : Int) * ((a / b : Nat) : Int) + ((a % b : Nat) : Int) = (a : Int) := by
      exact_mod_cast Nat.div_add_mod a b
    have h1 : (b : Int) * ((extGcd b (a % b)).2.1 - ((a / b : Nat) : Int) * (extGcd b (a % b)).2.2) =
        (b : Int) * (extGcd b (a % b)).2.1 - ((b : Int) * ((a / b : Nat) : Int)) * (extGcd b (a % b)).2.2 := by
      rw [Int.mul_sub, Int.mul_assoc]
    have h2 : ((a : Int) - (b : Int) * ((a / b : Nat) : Int)) * (extGcd b (a % b)).2.2 =
        (a : Int) * (extGcd b (a % b)).2.2 - ((b : Int) * ((a / b : Nat) : Int)) * (extGcd b (a % b)).2.2 :=
      Int.sub_mul _ _ _
    have h3 : ((a % b : Nat) : Int) = (a : Int) - (b : Int) * ((a / b : Nat) : Int) := by omega
    rw [h3, h2] at ih
    rw [h1]
    omega
termination_by b
decreasing_by exact Nat.mod_lt a (Nat.pos_of_ne_zero hb)

theorem IsPrimeNat.dvd_mul {q a b : Nat} (hq : IsPrimeNat q)
    (hdvd : q ∣ a * b) (hna : ¬ (q ∣ a)) : q ∣ b := by
  obtain ⟨hda, hdq⟩ := extGcd_dvd a q
  have hg1 : (extGcd a q).1 = 1 := by
    rcases hq.2 _ hdq with h1 | hqq
    · exact h1
    · rw [hqq] at hda
      exact False.elim (hna hda)
  have hbez := extGcd_bezout a q
  rw [hg1] at hbez
  obtain ⟨k, hk⟩ := hdvd
  have hmul : ((a : Int) * (extGcd a q).2.1 + (q : Int) * (extGcd a q).2.2) * (b : Int) =
      1 * (b : Int) := congrArg (· * (b : Int)) hbez
  rw [Int.add_mul, Int.one_mul] at hmul
  have hab : (a : Int) * (extGcd a q).2.1 * (b : Int) =
      (q : Int) * ((k : Int) * (extGcd a q).2.1) := by
    have hkInt : (a : Int) * (b : Int) = (q : Int) * (k : Int) := by exact_mod_cast hk
    rw [Int.mul_right_comm (a : Int), hkInt, Int.mul_assoc]
  rw [hab, Int.mul_assoc (q : Int), ← Int.mul_add] at hmul
  exact Int.ofNat_dvd.1 ⟨(k : Int) * (extGcd a q).2.1 + (extGcd a q).2.2 * (b : Int), hmul.symm⟩

private def posRange : Nat → List Nat
  | 0 => []
  | n + 1 => (n + 1) :: posRange n

private theorem mem_posRange_iff {x : Nat} : ∀ {n : Nat}, x ∈ posRange n ↔ 1 ≤ x ∧ x ≤ n
  | 0 => by
    constructor
    · intro h; cases h
    · rintro ⟨hLo, hHi⟩; omega
  | n + 1 => by
    simp only [posRange, List.mem_cons, mem_posRange_iff]
    constructor
    · intro h
      rcases h with hEq | ⟨hLo, hHi⟩
      · subst hEq; exact ⟨Nat.succ_pos n, Nat.le_refl _⟩
      · exact ⟨hLo, Nat.le_trans hHi (Nat.le_succ n)⟩
    · rintro ⟨hLo, hHi⟩
      by_cases hEq : x = n + 1
      · exact .inl hEq
      · exact .inr ⟨hLo, by omega⟩

private theorem posRange_nodup : ∀ (n : Nat), (posRange n).Nodup
  | 0 => .nil
  | n + 1 =>
    .cons
      (fun b hb heq => by
        have hle := (mem_posRange_iff.1 hb).2
        omega)
      (posRange_nodup n)

private def listProd : List Nat → Nat
  | [] => 1
  | x :: xs => x * listProd xs

private def eraseFirst (v : Nat) : List Nat → List Nat
  | [] => []
  | y :: ys => if y = v then ys else y :: eraseFirst v ys

private theorem mem_of_mem_eraseFirst {v z : Nat} :
    ∀ {ys : List Nat}, z ∈ eraseFirst v ys → z ∈ ys
  | [], h => by cases h
  | y :: ys, h => by
    simp only [eraseFirst] at h
    split at h
    · exact .tail _ h
    · cases h with
      | head => exact .head _
      | tail _ ht => exact .tail _ (mem_of_mem_eraseFirst ht)

private theorem eraseFirst_spec {v : Nat} :
    ∀ {ys : List Nat},
      ys.Nodup → v ∈ ys →
      listProd ys = v * listProd (eraseFirst v ys) ∧
      (eraseFirst v ys).length + 1 = ys.length ∧
      (eraseFirst v ys).Nodup ∧
      (∀ z : Nat, z ≠ v → z ∈ ys → z ∈ eraseFirst v ys)
  | [], _, hmem => by cases hmem
  | y :: ys, .cons hrel hnd, hmem => by
    dsimp only [eraseFirst]
    if hy : y = v then
      subst hy
      simp only [↓reduceIte, listProd, List.length_cons]
      refine ⟨trivial, trivial, hnd, ?_⟩
      intro z hzne hzmem
      cases hzmem with
      | head => exact False.elim (hzne rfl)
      | tail _ htail => exact htail
    else
      simp only [hy, ↓reduceIte, listProd, List.length_cons]
      have hvTail : v ∈ ys := by
        cases hmem with
        | head => exact False.elim (hy rfl)
        | tail _ ht => exact ht
      obtain ⟨hprod, hlen, hnd', hsub⟩ := eraseFirst_spec hnd hvTail
      refine ⟨?_, by omega, .cons (fun b hb heq => hrel b (mem_of_mem_eraseFirst hb) heq) hnd', ?_⟩
      · rw [hprod, ← Nat.mul_assoc, Nat.mul_comm y v, Nat.mul_assoc]
      · intro z hzne hzmem
        cases hzmem with
        | head => exact .head _
        | tail _ ht => exact .tail _ (hsub z hzne ht)

private theorem listProd_eq_of_nodup_subset :
    ∀ {xs ys : List Nat},
      xs.Nodup → ys.Nodup → xs.length = ys.length →
      (∀ x ∈ xs, x ∈ ys) → listProd xs = listProd ys
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, hlen, _ => by cases hlen
  | x :: xs, ys, .cons hrel hndX, hndY, hlen, hsub => by
    obtain ⟨hprodY, hlenE, hndE, hmemE⟩ := eraseFirst_spec hndY (hsub x (.head _))
    simp only [List.length_cons] at hlen
    have ih := listProd_eq_of_nodup_subset hndX hndE (by omega) (fun z hz =>
      hmemE z (fun heq => hrel z hz heq.symm) (hsub z (.tail _ hz)))
    simp only [listProd, ih, hprodY]

private theorem listProd_map_mul_mod (a q : Nat) :
    ∀ (n : Nat),
      listProd ((posRange n).map (fun i => (a * i) % q)) % q =
      (a ^ n * listProd (posRange n)) % q
  | 0 => by simp [posRange, listProd]
  | n + 1 => by
    simp only [posRange, List.map_cons, listProd]
    rw [Nat.mul_mod ((a * (n + 1)) % q), Nat.mod_mod, listProd_map_mul_mod a q n, ← Nat.mul_mod]
    have hcomm : a * (n + 1) * (a ^ n * listProd (posRange n)) =
        a ^ (n + 1) * ((n + 1) * listProd (posRange n)) := by
      rw [Nat.pow_succ, Nat.mul_comm (a ^ n) a]
      rw [Nat.mul_assoc a (n + 1) (a ^ n * listProd (posRange n)),
          ← Nat.mul_assoc (n + 1) (a ^ n) (listProd (posRange n)),
          Nat.mul_comm (n + 1) (a ^ n),
          Nat.mul_assoc (a ^ n) (n + 1) (listProd (posRange n)),
          ← Nat.mul_assoc a (a ^ n) _]
    rw [hcomm]

private theorem not_dvd_listProd_posRange {q : Nat} (hq : IsPrimeNat q) :
    ∀ {n : Nat}, n < q → ¬ (q ∣ listProd (posRange n))
  | 0, _, hdvd => by
    dsimp only [posRange, listProd] at hdvd
    have hle := Nat.le_of_dvd (by decide) hdvd
    have hq2 := hq.1
    omega
  | n + 1, hlt, hdvd => by
    simp only [posRange, listProd] at hdvd
    have hnot1 : ¬ (q ∣ (n + 1)) := by
      intro h1
      have hle := Nat.le_of_dvd (by omega) h1
      omega
    exact not_dvd_listProd_posRange hq (by omega) (hq.dvd_mul hdvd hnot1)

private theorem sub_dvd_of_mod_eq {x y q : Nat} (hle : y ≤ x) (hmod : x % q = y % q) :
    q ∣ (x - y) := by
  have hx : q * (x / q) + x % q = x := Nat.div_add_mod x q
  have hy : q * (y / q) + y % q = y := Nat.div_add_mod y q
  have hdivLe : y / q ≤ x / q := Nat.div_le_div_right hle
  refine ⟨x / q - y / q, ?_⟩
  rw [Nat.mul_sub]
  omega

private theorem one_le_pow_of_pos {a : Nat} (ha : 1 ≤ a) : ∀ k : Nat, 1 ≤ a ^ k
  | 0 => Nat.le_refl 1
  | k + 1 => by
    rw [Nat.pow_succ]
    exact Nat.le_trans (one_le_pow_of_pos ha k) (Nat.le_mul_of_pos_right _ ha)

/-- **Fermat's Little Theorem (`IsPrimeNat.pow_sub_one_mod`)**. -/
