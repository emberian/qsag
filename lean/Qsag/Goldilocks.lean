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
theorem IsPrimeNat.pow_sub_one_mod {q a : Nat} (hq : IsPrimeNat q) (hna : ¬ (q ∣ a)) :
    (a ^ (q - 1)) % q = 1 := by
  let L := posRange (q - 1)
  let f := fun i : Nat => (a * i) % q
  have hMem : ∀ x ∈ L.map f, x ∈ L := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hi1, hi2⟩ := mem_posRange_iff.1 hi
    have hni : ¬ (q ∣ i) := fun hd => by
      have hle := Nat.le_of_dvd (by omega) hd
      have hq2 := hq.1
      omega
    have hnai : ¬ (q ∣ a * i) := fun hd => hni (hq.dvd_mul (Nat.mul_comm a i ▸ hd) hna)
    have hmodPos : 0 < (a * i) % q := by
      if hz : (a * i) % q = 0 then
        exact False.elim (hnai (Nat.dvd_of_mod_eq_zero hz))
      else omega
    have hmodLt : (a * i) % q < q := Nat.mod_lt _ (by have := hq.1; omega)
    dsimp only [f]
    exact mem_posRange_iff.2 ⟨hmodPos, by omega⟩
  have hInjOn : ∀ i j : Nat, i ∈ L → j ∈ L → f i = f j → i = j := by
    intro i j hi hj hij
    obtain ⟨hi1, hi2⟩ := mem_posRange_iff.1 hi
    obtain ⟨hj1, hj2⟩ := mem_posRange_iff.1 hj
    have hq2 := hq.1
    if hijLe : i ≤ j then
      have hdvd : q ∣ a * (j - i) := by
        have hmul : a * j - a * i = a * (j - i) := (Nat.mul_sub a j i).symm
        rw [← hmul]
        exact sub_dvd_of_mod_eq (Nat.mul_le_mul_left a hijLe) hij.symm
      have hdvdDiff : q ∣ (j - i) := hq.dvd_mul hdvd hna
      if hdiff0 : j - i = 0 then omega
      else
        have hle := Nat.le_of_dvd (by omega) hdvdDiff
        omega
    else
      have hjiLe : j ≤ i := by omega
      have hdvd : q ∣ a * (i - j) := by
        have hmul : a * i - a * j = a * (i - j) := (Nat.mul_sub a i j).symm
        rw [← hmul]
        exact sub_dvd_of_mod_eq (Nat.mul_le_mul_left a hjiLe) hij
      have hdvdDiff : q ∣ (i - j) := hq.dvd_mul hdvd hna
      if hdiff0 : i - j = 0 then omega
      else
        have hle := Nat.le_of_dvd (by omega) hdvdDiff
        omega
  have hNodupMap : (L.map f).Nodup := by
    have hsubNd : ∀ {xs : List Nat}, xs.Nodup → (∀ z ∈ xs, z ∈ L) → (xs.map f).Nodup := by
      intro xs hnd hxs
      induction hnd with
      | nil => exact .nil
      | @cons x rest hrel hndRest ih =>
        refine .cons (fun b hb heq => ?_) (ih (fun z hz => hxs z (.tail _ hz)))
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
        have hxy := hInjOn x y (hxs x (.head _)) (hxs y (.tail _ hy)) heq
        exact hrel y hy hxy
    exact hsubNd (posRange_nodup (q - 1)) (fun z hz => hz)
  have hProdEq : listProd (L.map f) = listProd L :=
    listProd_eq_of_nodup_subset hNodupMap (posRange_nodup (q - 1)) (by simp) hMem
  have hModEq : (a ^ (q - 1) * listProd L) % q = (listProd L) % q := by
    rw [← listProd_map_mul_mod a q (q - 1), hProdEq]
  have haPos : 1 ≤ a := by
    if ha0 : a = 0 then subst ha0; exact False.elim (hna (Nat.dvd_zero q))
    else omega
  have hpowPos : 1 ≤ a ^ (q - 1) := one_le_pow_of_pos haPos (q - 1)
  have hdvdMul : q ∣ (a ^ (q - 1) - 1) * listProd L := by
    have hsub : a ^ (q - 1) * listProd L - listProd L = (a ^ (q - 1) - 1) * listProd L := by
      rw [Nat.sub_mul, Nat.one_mul]
    rw [← hsub]
    exact sub_dvd_of_mod_eq (Nat.le_mul_of_pos_left _ hpowPos) hModEq
  have hnotF : ¬ (q ∣ listProd L) :=
    not_dvd_listProd_posRange hq (by have := hq.1; omega)
  have hdvdPow : q ∣ (a ^ (q - 1) - 1) :=
    hq.dvd_mul (Nat.mul_comm (a ^ (q - 1) - 1) (listProd L) ▸ hdvdMul) hnotF
  obtain ⟨k, hk⟩ := hdvdPow
  have hEq : a ^ (q - 1) = q * k + 1 := by omega
  rw [hEq, Nat.mul_add_mod, Nat.mod_eq_of_lt hq.1]

private theorem pow_mod_eq_one_of_eq_one {a q : Nat} (hq : 2 ≤ q) (ha : a % q = 1) :
    ∀ k : Nat, (a ^ k) % q = 1
  | 0 => Nat.mod_eq_of_lt hq
  | k + 1 => by
    rw [Nat.pow_succ, Nat.mul_mod, pow_mod_eq_one_of_eq_one hq ha k, ha]
    exact Nat.mod_eq_of_lt hq

private theorem pow_gcd_mod_eq_one {a q : Nat} (hq : 2 ≤ q) :
    ∀ (m n : Nat), (a ^ m) % q = 1 → (a ^ n) % q = 1 → (a ^ (Nat.gcd m n)) % q = 1
  | 0, n, _, hn => by simpa [Nat.gcd_zero_left] using hn
  | m + 1, n, hm, hn => by
    have hdiv : (m + 1) * (n / (m + 1)) + n % (m + 1) = n := Nat.div_add_mod n (m + 1)
    have hrem : (a ^ (n % (m + 1))) % q = 1 := by
      have hn' : (a ^ ((m + 1) * (n / (m + 1)) + n % (m + 1))) % q = 1 := hdiv.symm ▸ hn
      rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod,
          pow_mod_eq_one_of_eq_one hq hm (n / (m + 1)), Nat.one_mul, Nat.mod_mod] at hn'
      exact hn'
    rw [Nat.gcd_rec (m + 1) n]
    exact pow_gcd_mod_eq_one hq (n % (m + 1)) (m + 1) hrem hm
termination_by m _ => m
decreasing_by exact Nat.mod_lt n (Nat.succ_pos m)

private theorem dvd_of_two_pow_dvd_mul_odd :
    ∀ (k g c : Nat), c % 2 = 1 → 2 ^ k ∣ g * c → 2 ^ k ∣ g
  | 0, g, _, _, _ => Nat.one_dvd g
  | k + 1, g, c, hodd, hdvd => by
    have h2prime : IsPrimeNat 2 := ⟨by decide, fun d hd => by
      have hpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by decide)
      have hle : d ≤ 2 := Nat.le_of_dvd (by decide) hd
      omega⟩
    have hnc : ¬ (2 ∣ c) := fun hc => by obtain ⟨t, rfl⟩ := hc; omega
    have h2dvd : 2 ∣ g * c := by
      rw [Nat.pow_succ] at hdvd
      exact Nat.dvd_trans (Nat.dvd_mul_left 2 (2 ^ k)) hdvd
    obtain ⟨g', rfl⟩ := h2prime.dvd_mul (Nat.mul_comm g c ▸ h2dvd) hnc
    have hdvd' : 2 ^ k ∣ g' * c := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc 2 g' c] at hdvd
      exact Nat.dvd_of_mul_dvd_mul_left (by decide) hdvd
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2]
    exact Nat.mul_dvd_mul_left 2 (dvd_of_two_pow_dvd_mul_odd k g' c hodd hdvd')

private theorem goldilocksEuler_modPow_abstract (e : Nat)
    (hLt : e < 2 ^ 64)
    (hEval : modPowFuel 64 7 e goldilocksPrime = goldilocksPrime - 1) :
    (7 ^ e) % goldilocksPrime = goldilocksPrime - 1 := by
  rw [← modPowFuel_eq_pow_mod 64 7 e goldilocksPrime hLt]
  exact hEval

/-- Euler witness `7 ^ ((p - 1) / 2) ≡ -1 (mod p)` via verified 64-step modular exponentiation. -/
private theorem goldilocksEuler_modPow :
    ∀ u : Unit, u = () →
      (7 ^ ((goldilocksPrime - 1) / 2)) % goldilocksPrime = goldilocksPrime - 1 :=
  fun _ _ => goldilocksEuler_modPow_abstract ((goldilocksPrime - 1) / 2) (by decide) (by decide)

/-- Proth-style divisor argument with the modulus and the half-exponent abstract: the kernel never
    meets a closed power with a 63-bit exponent while checking it. -/
private theorem dvd_cases_of_euler_certificate (p half : Nat)
    (hpPos : 1 ≤ p) (hpLt : p < (2 ^ 32) * (2 ^ 32)) (hodd : p % 2 = 1)
    (hrem : p % 3 ≠ 0 ∧ p % 5 ≠ 0 ∧ p % 7 ≠ 0)
    (hEuler : 7 ^ half % p = p - 1) (h2half : p - 1 = 2 * half)
    (h2pow32 : 2 ^ 32 ∣ (p - 1)) (d : Nat) (hd : d ∣ p) :
    d = 1 ∨ d = p := by
  if hd1 : d = 1 then exact .inl hd1
  else if hdp : d = p then exact .inr hdp
  else
    exfalso
    obtain ⟨e, he⟩ := hd
    have hdPos : 2 ≤ d := by
      if hd0 : d = 0 then subst hd0; rw [Nat.zero_mul] at he; omega
      else omega
    have hePos : 2 ≤ e := by
      if he0 : e = 0 then subst he0; rw [Nat.mul_zero] at he; omega
      else if he1 : e = 1 then subst he1; rw [Nat.mul_one] at he; exact False.elim (hdp he.symm)
      else omega
    let m := if d ≤ e then d else e
    have hm2 : 2 ≤ m := by dsimp [m]; split <;> omega
    have hmDvd : m ∣ p := by
      dsimp [m]; split
      · exact ⟨e, he⟩
      · exact ⟨d, Nat.mul_comm d e ▸ he⟩
    have hmSq : m * m ≤ p := by
      dsimp [m]; split
      · rename_i hle; rw [he]; exact Nat.mul_le_mul_left d hle
      · rename_i hgt; rw [he, Nat.mul_comm d e]; exact Nat.mul_le_mul_left e (by omega)
    obtain ⟨q, hqDef⟩ : ∃ q, minDivisor m = q := ⟨minDivisor m, rfl⟩
    obtain ⟨hqPrime, hqDvdM, hqLeM⟩ := minDivisor_isPrime hm2
    rw [hqDef] at hqPrime hqDvdM hqLeM
    have hqDvdP : q ∣ p := Nat.dvd_trans hqDvdM hmDvd
    have hqSq : q * q < (2 ^ 32) * (2 ^ 32) := by
      exact Nat.lt_of_le_of_lt (Nat.le_trans (Nat.mul_le_mul hqLeM hqLeM) hmSq) hpLt
    have hqLt32 : q < 2 ^ 32 := by
      if hge : 2 ^ 32 ≤ q then
        have hsqGe := Nat.mul_le_mul hge hge
        omega
      else omega
    have hqGe3 : 3 ≤ q := by
      have hq2 := hqPrime.1
      if hqEq2 : q = 2 then
        obtain ⟨k, hk⟩ := hqDvdP
        rw [hqEq2] at hk
        omega
      else omega
    have hqNotDvd7 : ¬ (q ∣ 7) := by
      intro hd7
      have hle7 : q ≤ 7 := Nat.le_of_dvd (by decide) hd7
      obtain ⟨k, hk⟩ := hqDvdP
      have hcases : q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl
      · exact hrem.1 (by omega)
      · rcases hqPrime.2 2 ⟨2, rfl⟩ with h | h <;> omega
      · exact hrem.2.1 (by omega)
      · rcases hqPrime.2 2 ⟨3, rfl⟩ with h | h <;> omega
      · exact hrem.2.2 (by omega)
    have hHalfPlusOneDvdP : p ∣ (7 ^ half + 1) := by
      have hdiv := Nat.div_add_mod (7 ^ half) p
      rw [hEuler] at hdiv
      refine ⟨(7 ^ half) / p + 1, ?_⟩
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have hHalfPlusOneDvdQ : q ∣ (7 ^ half + 1) := Nat.dvd_trans hqDvdP hHalfPlusOneDvdP
    have hHalfModQ : (7 ^ half) % q = q - 1 := by
      obtain ⟨t, ht⟩ := hHalfPlusOneDvdQ
      have htPos : 1 ≤ t := by
        if ht0 : t = 0 then
          rw [ht0, Nat.mul_zero] at ht
          exact False.elim (Nat.succ_ne_zero (7 ^ half) ht)
        else omega
      have hEq : 7 ^ half = q * (t - 1) + (q - 1) := by
        rw [Nat.mul_sub, Nat.mul_one]
        have hq1 : q ≤ q * t := by
          have h := Nat.mul_le_mul_left q htPos
          rwa [Nat.mul_one] at h
        omega
      rw [hEq, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    have hPm1ModQ : (7 ^ (p - 1)) % q = 1 := by
      rw [h2half, pow_two_mul, Nat.mul_mod, hHalfModQ]
      obtain ⟨q2, hq2Eq⟩ : ∃ q2, q = q2 + 3 := ⟨q - 3, by omega⟩
      have hsq : (q - 1) * (q - 1) = q * (q - 2) + 1 := by
        rw [hq2Eq]
        have ha : q2 + 3 - 1 = q2 + 2 := by omega
        have hb : q2 + 3 - 2 = q2 + 1 := by omega
        rw [ha, hb]
        simp only [Nat.mul_add, Nat.add_mul]
        omega
      rw [hsq, Nat.mul_add_mod, Nat.mod_eq_of_lt hqPrime.1]
    have hQm1ModQ : (7 ^ (q - 1)) % q = 1 := hqPrime.pow_sub_one_mod hqNotDvd7
    obtain ⟨g, hgDef⟩ : ∃ g, Nat.gcd (p - 1) (q - 1) = g := ⟨_, rfl⟩
    have hgPow : (7 ^ g) % q = 1 := by
      rw [← hgDef]
      exact pow_gcd_mod_eq_one hqPrime.1 (p - 1) (q - 1) hPm1ModQ hQm1ModQ
    have hgNotDvdHalf : ¬ (g ∣ half) := by
      rintro ⟨u, hu⟩
      have h1 : (7 ^ half) % q = 1 := by
        rw [hu, Nat.pow_mul]
        exact pow_mod_eq_one_of_eq_one hqPrime.1 hgPow u
      rw [hHalfModQ] at h1
      omega
    obtain ⟨c, hc⟩ := hgDef ▸ Nat.gcd_dvd_left (p - 1) (q - 1)
    have hcOdd : c % 2 = 1 := by
      if hce : c % 2 = 0 then
        obtain ⟨c', hc'⟩ : ∃ c', c = 2 * c' := ⟨c / 2, by omega⟩
        have hmul : 2 * half = 2 * (g * c') := by
          rw [← h2half, hc, hc', ← Nat.mul_assoc, Nat.mul_comm g 2, Nat.mul_assoc]
        have hhalfEq : half = g * c' := by omega
        exact False.elim (hgNotDvdHalf ⟨c', hhalfEq⟩)
      else omega
    have h2pow32DvdPm1 : 2 ^ 32 ∣ (p - 1) := h2pow32
    rw [hc] at h2pow32DvdPm1
    have h2pow32DvdG : 2 ^ 32 ∣ g := dvd_of_two_pow_dvd_mul_odd 32 g c hcOdd h2pow32DvdPm1
    have h2pow32DvdQm1 : 2 ^ 32 ∣ (q - 1) :=
      Nat.dvd_trans h2pow32DvdG (hgDef ▸ Nat.gcd_dvd_right (p - 1) (q - 1))
    have hge : 2 ^ 32 ≤ q - 1 := Nat.le_of_dvd (by omega) h2pow32DvdQm1
    omega

/-- **Zero-Axiom Proth Primality Theorem for `goldilocksPrime` ($p = 2^{64} - 2^{32} + 1$)**. -/
theorem goldilocksPrime_dvd_cases (d : Nat) (hd : d ∣ goldilocksPrime) :
    d = 1 ∨ d = goldilocksPrime :=
  dvd_cases_of_euler_certificate goldilocksPrime ((goldilocksPrime - 1) / 2)
    (by decide) (by decide) (by decide) (by decide) (goldilocksEuler_modPow () rfl) (by decide)
    ⟨2 ^ 32 - 1, by decide⟩ d hd

theorem goldilocksPrime_isPrime (u : Unit) : IsPrimeNat goldilocksPrime :=
  ⟨by decide, fun _ => (let _ := u; goldilocksPrime_dvd_cases _)⟩

/-- Constructive field inverse in `Goldilocks` via $a^{p-2} \bmod p$ (`inv 0 = 0`). -/
def Goldilocks.inv (a : Goldilocks) : Goldilocks :=
  if a.val = 0 then Goldilocks.zero
  else Goldilocks.ofNat (modPowFuel 64 a.val (goldilocksPrime - 2) goldilocksPrime)

theorem Goldilocks.mul_inv_cancel {a : Goldilocks} (ha : a ≠ Goldilocks.zero) :
    CommRingOps.mul a (Goldilocks.inv a) = CommRingOps.one := by
  have hvalNe : a.val ≠ 0 := fun h => ha (Goldilocks.ext h)
  have hnotDvd : ¬ (goldilocksPrime ∣ a.val) := fun hd => by
    have hle := Nat.le_of_dvd (by omega) hd
    have hlt := a.isLt
    omega
  apply Goldilocks.ext
  change (Goldilocks.mul a (Goldilocks.inv a)).val = 1
  rw [Goldilocks.mul_val]
  unfold Goldilocks.inv
  simp only [hvalNe, ↓reduceIte, Goldilocks.ofNat]
  rw [modPowFuel_eq_pow_mod 64 a.val (goldilocksPrime - 2) goldilocksPrime (by decide),
      Nat.mod_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_comm a.val,
      ← Nat.pow_succ, show (goldilocksPrime - 2).succ = goldilocksPrime - 1 by decide]
  exact (goldilocksPrime_isPrime ()).pow_sub_one_mod hnotDvd

instance : NoZeroDivisors Goldilocks where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} h := by
    if ha : a = Goldilocks.zero then
      exact .inl ha
    else
      right
      have hmul := congrArg (CommRingOps.mul (Goldilocks.inv a)) h
      rw [LawfulCommRing.mul_zero, ← LawfulCommRing.mul_assoc,
          LawfulCommRing.mul_comm (Goldilocks.inv a) a,
          Goldilocks.mul_inv_cancel ha, LawfulCommRing.one_mul] at hmul
      exact hmul

/-! ## 6. Quadratic Extension `GoldilocksExt2` ($\mathbb{F}_{p^2} = \mathbb{F}_p[u]/(u^2 - 7)$) -/

structure GoldilocksExt2 where
  c0 : Goldilocks
  c1 : Goldilocks
  deriving DecidableEq, Repr

namespace GoldilocksExt2

def nonResidue : Goldilocks := ⟨7, by decide⟩

theorem ext {x y : GoldilocksExt2} (h0 : x.c0 = y.c0) (h1 : x.c1 = y.c1) : x = y := by
  cases x; cases y; simp only at h0 h1; subst h0 h1; rfl

def ofBase (a : Goldilocks) : GoldilocksExt2 := ⟨a, CommRingOps.zero⟩
def zero : GoldilocksExt2 := ⟨CommRingOps.zero, CommRingOps.zero⟩
def one : GoldilocksExt2 := ⟨CommRingOps.one, CommRingOps.zero⟩
def uBasis : GoldilocksExt2 := ⟨CommRingOps.zero, CommRingOps.one⟩

instance : Inhabited GoldilocksExt2 := ⟨zero⟩

@[simp] theorem ofBase_c0 (a : Goldilocks) : (ofBase a).c0 = a := by unfold ofBase; rfl
@[simp] theorem ofBase_c1 (a : Goldilocks) : (ofBase a).c1 = CommRingOps.zero := by unfold ofBase; rfl

def add (x y : GoldilocksExt2) : GoldilocksExt2 :=
  ⟨CommRingOps.add x.c0 y.c0, CommRingOps.add x.c1 y.c1⟩

def neg (x : GoldilocksExt2) : GoldilocksExt2 :=
  ⟨CommRingOps.neg x.c0, CommRingOps.neg x.c1⟩

def sub (x y : GoldilocksExt2) : GoldilocksExt2 :=
  ⟨CommRingOps.sub x.c0 y.c0, CommRingOps.sub x.c1 y.c1⟩

def mul (x y : GoldilocksExt2) : GoldilocksExt2 :=
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

def inv (z : GoldilocksExt2) : GoldilocksExt2 :=
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

/-! ## 7. Univariate Polynomials (`RoundPoly R`) & Factor-Theorem Root Bound -/

structure RoundPoly (R : Type) where
  coeffs : List R
  deriving DecidableEq, Repr

namespace RoundPoly

@[expose] def evalCoeffs {R : Type} [CommRingOps R] : List R → R → R
  | [], _ => CommRingOps.zero
  | c :: cs, x => CommRingOps.add c (CommRingOps.mul x (evalCoeffs cs x))

@[simp] theorem evalCoeffs_nil {R : Type} [CommRingOps R] (x : R) :
    evalCoeffs ([] : List R) x = CommRingOps.zero := rfl

@[simp] theorem evalCoeffs_cons {R : Type} [CommRingOps R] (c : R) (cs : List R) (x : R) :
    evalCoeffs (c :: cs) x = CommRingOps.add c (CommRingOps.mul x (evalCoeffs cs x)) := rfl

def eval {R : Type} [CommRingOps R] (p : RoundPoly R) (x : R) : R :=
  evalCoeffs p.coeffs x

def subCoeffs {R : Type} [CommRingOps R] : List R → List R → List R
  | [], [] => []
  | c :: cs, [] => c :: subCoeffs cs []
  | [], d :: ds => CommRingOps.neg d :: subCoeffs [] ds
  | c :: cs, d :: ds => CommRingOps.sub c d :: subCoeffs cs ds

theorem subCoeffs_length :
    ∀ {R : Type} [CommRingOps R] (cs ds : List R),
      (subCoeffs cs ds).length = Nat.max cs.length ds.length
  | _, _, [], [] => by simp [subCoeffs]
  | _, _, _ :: cs, [] => by simp [subCoeffs, subCoeffs_length cs []]
  | _, _, [], _ :: ds => by simp [subCoeffs, subCoeffs_length [] ds]
  | _, _, _ :: cs, _ :: ds => by
    simp [subCoeffs, subCoeffs_length cs ds, Nat.succ_max_succ]

theorem evalCoeffs_sub {R : Type} [LawfulCommRing R] :
    ∀ (cs ds : List R) (x : R),
      evalCoeffs (subCoeffs cs ds) x = CommRingOps.sub (evalCoeffs cs x) (evalCoeffs ds x)
  | [], [], _ => by
    simp [subCoeffs, evalCoeffs, LawfulCommRing.sub_self]
  | c :: cs, [], x => by
    simp only [subCoeffs, evalCoeffs, evalCoeffs_sub cs [] x]
    rw [LawfulCommRing.sub_zero, LawfulCommRing.sub_zero]
  | [], d :: ds, x => by
    simp only [subCoeffs, evalCoeffs, evalCoeffs_sub [] ds x]
    rw [LawfulCommRing.sub_eq_add_neg CommRingOps.zero (evalCoeffs ds x),
        LawfulCommRing.zero_add, LawfulCommRing.mul_neg,
        LawfulCommRing.sub_eq_add_neg CommRingOps.zero _,
        LawfulCommRing.zero_add]
    apply LawfulCommRing.add_left_cancel
      (a := CommRingOps.add d (CommRingOps.mul x (evalCoeffs ds x)))
    rw [LawfulCommRing.add_right_neg,
        LawfulCommRing.add_add_add_comm,
        LawfulCommRing.add_right_neg,
        LawfulCommRing.add_right_neg,
        LawfulCommRing.add_zero]
  | c :: cs, d :: ds, x => by
    simp only [subCoeffs, evalCoeffs, evalCoeffs_sub cs ds x]
    rw [LawfulCommRing.mul_sub]
    apply LawfulCommRing.add_left_cancel
      (a := CommRingOps.add d (CommRingOps.mul x (evalCoeffs ds x)))
    rw [LawfulCommRing.add_sub_cancel_left]
    rw [LawfulCommRing.add_add_add_comm,
        LawfulCommRing.add_sub_cancel_left,
        LawfulCommRing.add_sub_cancel_left]

/-- Monic synthetic linear division quotient `(p(X) - p(r)) / (X - r)`. -/
def quotLinear {R : Type} [CommRingOps R] : List R → R → List R
  | [], _ => []
  | [_], _ => []
  | _ :: c₁ :: cs, r => evalCoeffs (c₁ :: cs) r :: quotLinear (c₁ :: cs) r

theorem quotLinear_length {R : Type} [CommRingOps R] :
    ∀ (cs : List R) (r : R), (quotLinear cs r).length = cs.length - 1
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: c₁ :: cs, r => by
    simp only [quotLinear, List.length_cons, quotLinear_length (c₁ :: cs) r]
    simp

/-- **Factor Theorem Identity (`evalCoeffs_eq_mul_quotLinear_add`)**:
    $p(x) = (x - r) \cdot q(x) + p(r)$ in every `LawfulCommRing R`. -/
theorem evalCoeffs_eq_mul_quotLinear_add {R : Type} [LawfulCommRing R] :
    ∀ (cs : List R) (r x : R),
      evalCoeffs cs x =
        CommRingOps.add
          (CommRingOps.mul (CommRingOps.sub x r) (evalCoeffs (quotLinear cs r) x))
          (evalCoeffs cs r)
  | [], r, x => by
    simp [quotLinear, evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  | [c₀], r, x => by
    simp [quotLinear, evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.zero_add]
  | c₀ :: c₁ :: cs, r, x => by
    let tl := c₁ :: cs
    have ih := evalCoeffs_eq_mul_quotLinear_add tl r x
    change CommRingOps.add c₀ (CommRingOps.mul x (evalCoeffs tl x)) =
      CommRingOps.add
        (CommRingOps.mul (CommRingOps.sub x r)
          (CommRingOps.add (evalCoeffs tl r) (CommRingOps.mul x (evalCoeffs (quotLinear tl r) x))))
        (CommRingOps.add c₀ (CommRingOps.mul r (evalCoeffs tl r)))
    rw [ih]
    rw [LawfulCommRing.left_distrib x,
        LawfulCommRing.left_distrib (CommRingOps.sub x r),
        LawfulCommRing.sub_mul x r (evalCoeffs tl r)]
    have hcommX : CommRingOps.mul (CommRingOps.sub x r)
        (CommRingOps.mul x (evalCoeffs (quotLinear tl r) x)) =
        CommRingOps.mul x
          (CommRingOps.mul (CommRingOps.sub x r) (evalCoeffs (quotLinear tl r) x)) := by
      rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm (CommRingOps.sub x r) x,
          LawfulCommRing.mul_assoc]
    rw [hcommX]
    apply LawfulCommRing.add_left_cancel (a := CommRingOps.mul r (evalCoeffs tl r))
    let A := CommRingOps.mul r (evalCoeffs tl r)
    let B := CommRingOps.mul x (evalCoeffs tl r)
    let C := CommRingOps.mul x (CommRingOps.mul (CommRingOps.sub x r) (evalCoeffs (quotLinear tl r) x))
    change CommRingOps.add A (CommRingOps.add c₀ (CommRingOps.add C B)) =
      CommRingOps.add A (CommRingOps.add (CommRingOps.add (CommRingOps.sub B A) C) (CommRingOps.add c₀ A))
    rw [← LawfulCommRing.add_assoc A (CommRingOps.add (CommRingOps.sub B A) C) (CommRingOps.add c₀ A),
        ← LawfulCommRing.add_assoc A (CommRingOps.sub B A) C,
        LawfulCommRing.add_sub_cancel_left A B]
    rw [LawfulCommRing.add_comm C B,
        LawfulCommRing.add_comm c₀ A,
        ← LawfulCommRing.add_assoc A c₀ (CommRingOps.add B C),
        LawfulCommRing.add_comm A c₀,
        LawfulCommRing.add_assoc c₀ A (CommRingOps.add B C),
        ← LawfulCommRing.add_assoc c₀ A (CommRingOps.add B C),
        LawfulCommRing.add_comm (CommRingOps.add c₀ A) (CommRingOps.add B C)]

private theorem mem_of_mem_filter_local {α : Type} {p : α → Bool} {x : α} :
    ∀ {l : List α}, x ∈ l.filter p → x ∈ l
  | [], h => by cases h
  | _ :: _, h => by
    simp only [List.filter] at h
    split at h
    · cases h with
      | head => exact .head _
      | tail _ hm => exact .tail _ (mem_of_mem_filter_local hm)
    · exact .tail _ (mem_of_mem_filter_local h)

private theorem pred_of_mem_filter_local {α : Type} {p : α → Bool} {x : α} :
    ∀ {l : List α}, x ∈ l.filter p → p x = true
  | [], h => by cases h
  | _ :: _, h => by
    simp only [List.filter] at h
    split at h
    · rename_i hpx
      cases h with
      | head => exact hpx
      | tail _ hm => exact pred_of_mem_filter_local hm
    · exact pred_of_mem_filter_local h

private theorem nodup_filter_local {α : Type} (p : α → Bool) :
    ∀ {l : List α}, l.Nodup → (l.filter p).Nodup
  | [], _ => .nil
  | _ :: _, .cons hrel htail => by
    simp only [List.filter]
    split
    · exact .cons (fun b hb => hrel b (mem_of_mem_filter_local hb)) (nodup_filter_local p htail)
    · exact nodup_filter_local p htail

private theorem filter_eq_self_of_forall {α : Type} {p : α → Bool} :
    ∀ {xs : List α}, (∀ x ∈ xs, p x = true) → xs.filter p = xs
  | [], _ => rfl
  | y :: ys, h => by
    have hy := h y (.head _)
    simp only [List.filter, hy]
    exact congrArg (y :: ·) (filter_eq_self_of_forall (fun z hz => h z (.tail _ hz)))

/-- **Lagrange / Factor-Theorem Root-Counting Bound (`roots_nodup_length_le`)**:
    Over every `LawfulCommRing R` without zero divisors, any non-zero polynomial of formal
    degree $\le d$ has at most `d` roots in any duplicate-free list `S : List R`. -/
theorem roots_nodup_length_le
    {R : Type} [LawfulCommRing R] [DecidableEq R] [NoZeroDivisors R] :
    ∀ (d : Nat) (cs : List R) (S : List R),
      S.Nodup →
      cs.length ≤ d + 1 →
      (∃ x₀ : R, evalCoeffs cs x₀ ≠ CommRingOps.zero) →
      (S.filter (fun r => decide (evalCoeffs cs r = CommRingOps.zero))).length ≤ d
  | 0, cs, S, _, hlen, ⟨x₀, hx₀⟩ => by
    have hempty : S.filter (fun r => decide (evalCoeffs cs r = CommRingOps.zero)) = [] := by
      cases hfilt : S.filter (fun r => decide (evalCoeffs cs r = CommRingOps.zero)) with
      | nil => rfl
      | cons r rs =>
        exfalso
        have hpred := pred_of_mem_filter_local (p := fun r => decide (evalCoeffs cs r = CommRingOps.zero))
          (l := S) (x := r) (by rw [hfilt]; exact .head _)
        rw [decide_eq_true_eq] at hpred
        cases cs with
        | nil => exact hx₀ rfl
        | cons c₀ tl =>
          cases tl with
          | nil =>
            simp only [evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero] at hpred hx₀
            exact hx₀ hpred
          | cons _ _ =>
            simp only [List.length_cons] at hlen
            omega
    rw [hempty]
    exact Nat.le_refl 0
  | d + 1, cs, S, hNodup, hlen, ⟨x₀, hx₀⟩ => by
    have hndRoots : (S.filter (fun r => decide (evalCoeffs cs r = CommRingOps.zero))).Nodup :=
      nodup_filter_local _ hNodup
    cases hRoots : S.filter (fun r => decide (evalCoeffs cs r = CommRingOps.zero)) with
    | nil => simp
    | cons r rest =>
      rw [hRoots] at hndRoots
      cases hndRoots with
      | cons hNotMem hndRest =>
        have hrRoot : evalCoeffs cs r = CommRingOps.zero := by
          have hp := pred_of_mem_filter_local
            (p := fun r => decide (evalCoeffs cs r = CommRingOps.zero))
            (l := S) (x := r) (by rw [hRoots]; exact .head _)
          exact of_decide_eq_true hp
        let qcs := quotLinear cs r
        have hqLen : qcs.length ≤ d + 1 := by
          dsimp [qcs]; rw [quotLinear_length]; omega
        have hqNonzero : ∃ x₁ : R, evalCoeffs qcs x₁ ≠ CommRingOps.zero := by
          refine ⟨x₀, fun hq0 => hx₀ ?_⟩
          rw [evalCoeffs_eq_mul_quotLinear_add cs r x₀, hq0, hrRoot,
              LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
        have hSubRest : ∀ y ∈ rest, decide (evalCoeffs qcs y = CommRingOps.zero) = true := by
          intro y hy
          have hyInFilt : y ∈ S.filter (fun r => decide (evalCoeffs cs r = CommRingOps.zero)) := by
            rw [hRoots]; exact .tail _ hy
          have hyRoot : evalCoeffs cs y = CommRingOps.zero :=
            of_decide_eq_true
              (pred_of_mem_filter_local (p := fun r => decide (evalCoeffs cs r = CommRingOps.zero)) hyInFilt)
          have hyNeR : y ≠ r := fun heq => hNotMem y hy heq.symm
          have hSubNe : CommRingOps.sub y r ≠ CommRingOps.zero :=
            fun hsub0 => hyNeR (LawfulCommRing.sub_eq_zero_iff.mp hsub0)
          have hfac := evalCoeffs_eq_mul_quotLinear_add cs r y
          rw [hyRoot, hrRoot, LawfulCommRing.add_zero] at hfac
          rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hfac.symm with hbad | hqy0
          · exact False.elim (hSubNe hbad)
          · exact decide_eq_true hqy0
        have hRestEq : rest.filter (fun y => decide (evalCoeffs qcs y = CommRingOps.zero)) = rest :=
          filter_eq_self_of_forall hSubRest
        have ih := roots_nodup_length_le d qcs rest hndRest hqLen hqNonzero
        rw [hRestEq] at ih
        simp only [List.length_cons]
        omega

end RoundPoly
end Qsag
end
