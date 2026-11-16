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

@[expose] def neg (a : Goldilocks) : Goldilocks :=
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
@[expose] def Goldilocks.inv (a : Goldilocks) : Goldilocks :=
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


end Qsag
