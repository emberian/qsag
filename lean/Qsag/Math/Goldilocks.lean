module
/-
# Qsag.Math.Goldilocks — Zero-Mathlib Commutative Rings, Goldilocks Field, Ext2 & Root Bounds

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

public import Qsag.Math.Algebra
public import Qsag.Math.Primality

public section
namespace Qsag

set_option autoImplicit false


/-! ## 2. Goldilocks Prime ($p = 2^{64} - 2^{32} + 1$) Hardware-Exact 128-to-64 Reduction -/

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
  deriving Repr

namespace Goldilocks

theorem ext {a b : Goldilocks} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp only at h; subst h; rfl

/-- Equality is decided on canonical residues; consumers need no private field representation. -/
instance : DecidableEq Goldilocks := fun a b =>
  if h : a.val = b.val then isTrue (ext h)
  else isFalse (fun e => h (congrArg Goldilocks.val e))

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

/-! ## 3. Irreducibility of $v^4 - 7 \in \mathbb{F}_p[v]$ & Universal `GoldilocksExt4` Division -/

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


end Qsag
