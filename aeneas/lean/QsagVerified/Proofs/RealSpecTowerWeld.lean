module
import all QsagVerified.Funs
public import QsagVerified.Proofs.TowerBdoz
public import Qsag.Math.Gf2Pow128
import all Qsag.Math.Gf2Pow128

/-!
# Binary-tower weld between the Aeneas extraction and `Qsag.BinaryTower`

Every extracted Wiedemann-tower operation is identified with the canonical recursive field
`Qsag.TowerElem k` under `Qsag.unpackTower`: GF(256) (`k = 3`), `Tower128` (`k = 7`) and
`Tower256` (`k = 8`), for both addition and multiplication. The wide levels are obtained from
one level-generic Karatsuba step (`wide_mul_step`, `wide_scale_step`) instantiated at 16, 32, 64
and 128 bits, so no level is checked by enumeration above GF(256).

These statements concern the functions of the verified crate. They say nothing about a
separately compiled implementation that does not call them.
-/

public section
namespace qsag_verified.proofs
open Aeneas Aeneas.Std Result
open qsag_verified
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
attribute [-simp] BitVec.getLsbD_eq_getElem

set_option linter.unusedSimpArgs false in
/-- The base-256 MIR product uses the canonical Wiedemann packed coordinates. -/
theorem pureGf256Mul_eq_qsag (a b : Std.U8) :
    (pureGf256Mul a b).bv = Qsag.mulExec 3 a.bv b.bv := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change i < 8 at hi
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp only [Qsag.mulExec.eq_1, Qsag.mulExec.eq_2, Qsag.scaleXExec.eq_1,
      Qsag.scaleXExec.eq_2, Qsag.joinBits.eq_def, Qsag.lowBits.eq_def, Qsag.highBits.eq_def]
    simp [-BitVec.setWidth_setWidth, pureGf256Mul, pureMulT2, pureMulT1, pureScaleXT1, pureScaleXT2,
      UScalar.bv_and, UScalar.bv_or, UScalar.bv_xor, UScalarTy.numBits,
      BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_xor,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_append, BitVec.getLsbD_cast, BitVec.getLsbD_extractLsb',
      Bool.xor_assoc]
    all_goals simp [-BitVec.setWidth_setWidth, HAppend.hAppend, BitVec.append, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth',
      BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_extractLsb', Bool.xor_assoc]
  | i + 8, hi => omega

/-- Refinement to the canonical abstract field, not only another packed implementation. -/
theorem gf256_mul_refines_qsag (a b : Std.U8) :
    ∃ y, tower.gf256_mul a b = .ok y ∧
      Qsag.unpackTower 3 y.bv =
        Qsag.towerMul 3 (Qsag.unpackTower 3 a.bv) (Qsag.unpackTower 3 b.bv) := by
  refine ⟨pureGf256Mul a b, gf256_mul_eq_pure a b, ?_⟩
  rw [pureGf256Mul_eq_qsag]
  have h := Qsag.mulExec_refines 3 (Qsag.unpackTower 3 a.bv) (Qsag.unpackTower 3 b.bv)
  rw [Qsag.packTower_unpackTower, Qsag.packTower_unpackTower] at h
  rw [h, Qsag.unpackTower_packTower]
/-- Packed XOR is canonical tower addition at every level. -/
theorem unpackTower_xor (k : Nat) (a b : Qsag.TowerBitVec k) :
    Qsag.unpackTower k (a ^^^ b) =
      Qsag.towerAdd k (Qsag.unpackTower k a) (Qsag.unpackTower k b) := by
  have h := Qsag.packTower_add k (Qsag.unpackTower k a) (Qsag.unpackTower k b)
  rw [Qsag.packTower_unpackTower, Qsag.packTower_unpackTower] at h
  rw [← h, Qsag.unpackTower_packTower]

/-- Extracted GF(256) addition in the same coordinates as the multiplication weld. -/
theorem gf256_add_refines_qsag (a b : Std.U8) :
    ∃ y, tower.gf256_add a b = .ok y ∧
      Qsag.unpackTower 3 y.bv =
        Qsag.towerAdd 3 (Qsag.unpackTower 3 a.bv) (Qsag.unpackTower 3 b.bv) :=
  ⟨a ^^^ b, rfl, unpackTower_xor 3 a.bv b.bv⟩

/-- Extracted 128-bit addition refines the canonical level-seven operation. -/
theorem tower128_add_refines_qsag (a b : Std.U128) :
    ∃ y, tower.tower128_add a b = .ok y ∧
      Qsag.unpackTower 7 y.bv =
        Qsag.towerAdd 7 (Qsag.unpackTower 7 a.bv) (Qsag.unpackTower 7 b.bv) :=
  ⟨a ^^^ b, rfl, unpackTower_xor 7 a.bv b.bv⟩


/-! ## Level-generic packed Karatsuba step -/

/-- Constructive form of the low-mask bit test (the core lemma depends on `Classical.choice`). -/
private theorem testBit_lowMask (n i : Nat) : (2 ^ n - 1).testBit i = decide (i < n) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    have hpos : 0 < 2 ^ n := Nat.pow_pos (by decide)
    have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
    cases i with
    | zero =>
      rw [Nat.testBit_zero]
      have : (2 ^ (n + 1) - 1) % 2 = 1 := by omega
      simp [this]
    | succ i =>
      rw [Nat.testBit_succ, show (2 ^ (n + 1) - 1) / 2 = 2 ^ n - 1 by omega, ih]
      simp

private theorem and_lowMask (x n : Nat) : x &&& (2 ^ n - 1) = x % 2 ^ n := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, testBit_lowMask, Nat.testBit_mod_two_pow, Bool.and_comm]

private theorem towerLow (k : Nat) (a m : BitVec (2 ^ (k + 1)))
    (hm : m.toNat = 2 ^ (2 ^ k) - 1) :
    (a &&& m).setWidth (2 ^ k) = Qsag.lowBits k a := by
  apply BitVec.eq_of_toNat_eq
  simp only [Qsag.lowBits, BitVec.toNat_setWidth, BitVec.toNat_and, hm,
    BitVec.extractLsb'_toNat, and_lowMask, Nat.shiftRight_zero, Nat.mod_mod]

private theorem towerHigh (k : Nat) (a m : BitVec (2 ^ (k + 1)))
    (hm : m.toNat = 2 ^ (2 ^ k) - 1) :
    ((a >>> (2 ^ k)) &&& m).setWidth (2 ^ k) = Qsag.highBits k a := by
  apply BitVec.eq_of_toNat_eq
  simp only [Qsag.highBits, BitVec.toNat_setWidth, BitVec.toNat_and, hm,
    BitVec.extractLsb'_toNat, and_lowMask, BitVec.toNat_ushiftRight,
    Nat.mod_mod]

private theorem towerJoin (k : Nat) (lo hi : BitVec (2 ^ k)) :
    lo.setWidth (2 ^ (k + 1)) ||| (hi.setWidth (2 ^ (k + 1)) <<< (2 ^ k)) =
      Qsag.joinBits k lo hi := by
  have hw : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [Qsag.joinBits, BitVec.getLsbD_or, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_cast, BitVec.getLsbD_append]
  by_cases h : i < 2 ^ k
  · simp [h, hi']
  · have hlo : lo.getLsbD i = false := BitVec.getLsbD_of_ge lo i (by omega)
    have h2 : i - 2 ^ k < 2 ^ (k + 1) := by omega
    simp [h, hi', hlo, h2]

private theorem mulExec_succ (k : Nat) (a b : Qsag.TowerBitVec (k + 1)) :
    Qsag.mulExec (k + 1) a b =
      Qsag.joinBits k
        (Qsag.mulExec k (Qsag.lowBits k a) (Qsag.lowBits k b) ^^^
          Qsag.mulExec k (Qsag.highBits k a) (Qsag.highBits k b))
        (Qsag.mulExec k (Qsag.lowBits k a ^^^ Qsag.highBits k a)
            (Qsag.lowBits k b ^^^ Qsag.highBits k b) ^^^
          (Qsag.mulExec k (Qsag.lowBits k a) (Qsag.lowBits k b) ^^^
            Qsag.mulExec k (Qsag.highBits k a) (Qsag.highBits k b)) ^^^
          Qsag.scaleXExec k (Qsag.mulExec k (Qsag.highBits k a) (Qsag.highBits k b))) := by
  simp only [Qsag.mulExec]

private theorem scaleXExec_succ (k : Nat) (a : Qsag.TowerBitVec (k + 1)) :
    Qsag.scaleXExec (k + 1) a =
      Qsag.joinBits k (Qsag.highBits k a)
        (Qsag.lowBits k a ^^^ Qsag.scaleXExec k (Qsag.highBits k a)) := by
  simp only [Qsag.scaleXExec]

/-- One Karatsuba level: if `mulS`/`sxS` compute the canonical packed product and `X`-scaling
at level `k`, the mask/shift/zero-extend shape used by the Rust source computes the canonical
packed product at level `k + 1`. -/
private theorem wide_mul_step (k : Nat) (a b m : BitVec (2 ^ (k + 1)))
    (hm : m.toNat = 2 ^ (2 ^ k) - 1)
    (mulS : BitVec (2 ^ k) → BitVec (2 ^ k) → BitVec (2 ^ k))
    (sxS : BitVec (2 ^ k) → BitVec (2 ^ k))
    (hmul : ∀ x y, mulS x y = Qsag.mulExec k x y)
    (hsx : ∀ x, sxS x = Qsag.scaleXExec k x) :
    (mulS ((a &&& m).setWidth (2 ^ k)) ((b &&& m).setWidth (2 ^ k)) ^^^
        mulS (((a >>> (2 ^ k)) &&& m).setWidth (2 ^ k))
          (((b >>> (2 ^ k)) &&& m).setWidth (2 ^ k))).setWidth (2 ^ (k + 1)) |||
      ((mulS ((a &&& m).setWidth (2 ^ k) ^^^ ((a >>> (2 ^ k)) &&& m).setWidth (2 ^ k))
            ((b &&& m).setWidth (2 ^ k) ^^^ ((b >>> (2 ^ k)) &&& m).setWidth (2 ^ k)) ^^^
          mulS ((a &&& m).setWidth (2 ^ k)) ((b &&& m).setWidth (2 ^ k)) ^^^
          mulS (((a >>> (2 ^ k)) &&& m).setWidth (2 ^ k))
            (((b >>> (2 ^ k)) &&& m).setWidth (2 ^ k)) ^^^
          sxS (mulS (((a >>> (2 ^ k)) &&& m).setWidth (2 ^ k))
            (((b >>> (2 ^ k)) &&& m).setWidth (2 ^ k)))).setWidth (2 ^ (k + 1)) <<< (2 ^ k)) =
      Qsag.mulExec (k + 1) a b := by
  rw [towerJoin, mulExec_succ, towerHigh k a m hm, towerHigh k b m hm, towerLow k a m hm,
    towerLow k b m hm]
  simp only [hmul, hsx, BitVec.xor_assoc]

private theorem wide_scale_step (k : Nat) (a m : BitVec (2 ^ (k + 1)))
    (hm : m.toNat = 2 ^ (2 ^ k) - 1)
    (sxS : BitVec (2 ^ k) → BitVec (2 ^ k))
    (hsx : ∀ x, sxS x = Qsag.scaleXExec k x) :
    (((a >>> (2 ^ k)) &&& m).setWidth (2 ^ k)).setWidth (2 ^ (k + 1)) |||
      (((a &&& m).setWidth (2 ^ k) ^^^
          sxS (((a >>> (2 ^ k)) &&& m).setWidth (2 ^ k))).setWidth (2 ^ (k + 1)) <<< (2 ^ k)) =
      Qsag.scaleXExec (k + 1) a := by
  rw [towerJoin, scaleXExec_succ, towerHigh k a m hm, towerLow k a m hm, hsx]

/-! ## The extracted levels 3 to 7 -/

set_option linter.unusedSimpArgs false in
/-- The 8-bit `X₂`-scaling uses the canonical packed coordinates. -/
theorem pureScaleXT3_eq_qsag (a : Std.U8) :
    (pureScaleXT3 a).bv = Qsag.scaleXExec 3 a.bv := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change i < 8 at hi
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp only [Qsag.scaleXExec.eq_1, Qsag.scaleXExec.eq_2, Qsag.joinBits.eq_def,
      Qsag.lowBits.eq_def, Qsag.highBits.eq_def]
    simp [-BitVec.setWidth_setWidth, pureScaleXT3, pureScaleXT2, pureScaleXT1,
      UScalar.bv_and, UScalar.bv_or, UScalar.bv_xor, UScalarTy.numBits,
      BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_xor,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_append, BitVec.getLsbD_cast, BitVec.getLsbD_extractLsb',
      Bool.xor_assoc]
    all_goals simp [-BitVec.setWidth_setWidth, HAppend.hAppend, BitVec.append, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeftZeroExtend, BitVec.getLsbD_setWidth',
      BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_extractLsb', Bool.xor_assoc]
  | i + 8, hi => omega

theorem pureMulT4_eq_qsag (a b : Std.U16) :
    (pureMulT4 a b).bv = Qsag.mulExec 4 a.bv b.bv :=
  wide_mul_step 3 a.bv b.bv (255#u16).bv (by decide)
    (fun x y => (pureGf256Mul ⟨x⟩ ⟨y⟩).bv) (fun x => (pureScaleXT3 ⟨x⟩).bv)
    (fun x y => pureGf256Mul_eq_qsag ⟨x⟩ ⟨y⟩) (fun x => pureScaleXT3_eq_qsag ⟨x⟩)

theorem pureScaleXT4_eq_qsag (a : Std.U16) :
    (pureScaleXT4 a).bv = Qsag.scaleXExec 4 a.bv :=
  wide_scale_step 3 a.bv (255#u16).bv (by decide)
    (fun x => (pureScaleXT3 ⟨x⟩).bv) (fun x => pureScaleXT3_eq_qsag ⟨x⟩)

theorem pureMulT5_eq_qsag (a b : Std.U32) :
    (pureMulT5 a b).bv = Qsag.mulExec 5 a.bv b.bv :=
  wide_mul_step 4 a.bv b.bv (65535#u32).bv (by decide)
    (fun x y => (pureMulT4 ⟨x⟩ ⟨y⟩).bv) (fun x => (pureScaleXT4 ⟨x⟩).bv)
    (fun x y => pureMulT4_eq_qsag ⟨x⟩ ⟨y⟩) (fun x => pureScaleXT4_eq_qsag ⟨x⟩)

theorem pureScaleXT5_eq_qsag (a : Std.U32) :
    (pureScaleXT5 a).bv = Qsag.scaleXExec 5 a.bv :=
  wide_scale_step 4 a.bv (65535#u32).bv (by decide)
    (fun x => (pureScaleXT4 ⟨x⟩).bv) (fun x => pureScaleXT4_eq_qsag ⟨x⟩)

theorem pureMulT6_eq_qsag (a b : Std.U64) :
    (pureMulT6 a b).bv = Qsag.mulExec 6 a.bv b.bv :=
  wide_mul_step 5 a.bv b.bv (4294967295#u64).bv (by decide)
    (fun x y => (pureMulT5 ⟨x⟩ ⟨y⟩).bv) (fun x => (pureScaleXT5 ⟨x⟩).bv)
    (fun x y => pureMulT5_eq_qsag ⟨x⟩ ⟨y⟩) (fun x => pureScaleXT5_eq_qsag ⟨x⟩)

theorem pureScaleXT6_eq_qsag (a : Std.U64) :
    (pureScaleXT6 a).bv = Qsag.scaleXExec 6 a.bv :=
  wide_scale_step 5 a.bv (4294967295#u64).bv (by decide)
    (fun x => (pureScaleXT5 ⟨x⟩).bv) (fun x => pureScaleXT5_eq_qsag ⟨x⟩)

/-- The 128-bit MIR product uses the canonical Wiedemann packed coordinates. -/
theorem pureTower128Mul_eq_qsag (a b : Std.U128) :
    (pureTower128Mul a b).bv = Qsag.mulExec 7 a.bv b.bv :=
  wide_mul_step 6 a.bv b.bv (18446744073709551615#u128).bv (by decide)
    (fun x y => (pureMulT6 ⟨x⟩ ⟨y⟩).bv) (fun x => (pureScaleXT6 ⟨x⟩).bv)
    (fun x y => pureMulT6_eq_qsag ⟨x⟩ ⟨y⟩) (fun x => pureScaleXT6_eq_qsag ⟨x⟩)

/-- Pure model of the extracted `scale_x_t7`. -/
def pureScaleXT7 (a : Std.U128) : Std.U128 :=
  let hi : Std.U64 :=
    UScalar.cast .U64 ((⟨a.bv >>> 64⟩ : Std.U128) &&& 18446744073709551615#u128)
  let sx := pureScaleXT6 hi
  ⟨(UScalar.cast .U128 hi).bv |||
    ((UScalar.cast .U128
      ((UScalar.cast .U64 (a &&& 18446744073709551615#u128)) ^^^ sx)).bv <<< 64)⟩

theorem scale_x_t7_eq_pure (a : Std.U128) :
    tower.scale_x_t7 a = .ok (pureScaleXT7 a) := by
  let hi : Std.U64 :=
    UScalar.cast .U64 ((⟨a.bv >>> 64⟩ : Std.U128) &&& 18446744073709551615#u128)
  have hs := scale_x_t6_eq_independent hi
  have ha : (a >>> 64#i32 : Result Std.U128) = .ok ⟨a.bv >>> 64⟩ := rfl
  change tower.scale_x_t7 a = .ok ⟨(UScalar.cast .U128 hi).bv |||
    ((UScalar.cast .U128
      ((UScalar.cast .U64 (a &&& 18446744073709551615#u128)) ^^^ pureScaleXT6 hi)).bv <<< 64)⟩
  unfold tower.scale_x_t7
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step ha
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hs
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  rfl

theorem pureScaleXT7_eq_qsag (a : Std.U128) :
    (pureScaleXT7 a).bv = Qsag.scaleXExec 7 a.bv :=
  wide_scale_step 6 a.bv (18446744073709551615#u128).bv (by decide)
    (fun x => (pureScaleXT6 ⟨x⟩).bv) (fun x => pureScaleXT6_eq_qsag ⟨x⟩)

/-- Every extracted 128-bit multiplication is multiplication in the canonical field
`Qsag.TowerElem 7`. -/
theorem tower128_mul_refines_qsag (a b : Std.U128) :
    ∃ y, tower.tower128_mul a b = .ok y ∧
      Qsag.unpackTower 7 y.bv =
        Qsag.towerMul 7 (Qsag.unpackTower 7 a.bv) (Qsag.unpackTower 7 b.bv) := by
  refine ⟨pureTower128Mul a b, tower128_mul_eq_independent a b, ?_⟩
  rw [pureTower128Mul_eq_qsag]
  have h := Qsag.mulExec_refines 7 (Qsag.unpackTower 7 a.bv) (Qsag.unpackTower 7 b.bv)
  rw [Qsag.packTower_unpackTower, Qsag.packTower_unpackTower] at h
  rw [h, Qsag.unpackTower_packTower]

/-- The canonical field has no zero divisors, so neither does the extracted product:
an extracted `Tower128` product vanishes exactly when a factor does. This is the algebraic
fact a BDOZ MAC forgery bound needs from the implementation. -/
theorem tower128_mul_eq_zero_iff (a b : Std.U128) :
    tower.tower128_mul a b = .ok 0#u128 ↔ a = 0#u128 ∨ b = 0#u128 := by
  obtain ⟨y, hy, hAbs⟩ := tower128_mul_refines_qsag a b
  have hzero : ∀ x : Std.U128, Qsag.unpackTower 7 x.bv = Qsag.towerZero 7 ↔ x = 0#u128 := by
    intro x
    constructor
    · intro h
      have hp := congrArg (Qsag.packTower 7) h
      rw [Qsag.packTower_unpackTower, Qsag.packTower_zero] at hp
      exact UScalar.ext hp
    · intro h
      subst h
      exact Qsag.unpackTower_zero 7
  rw [hy]
  constructor
  · intro h
    have hy0 : y = 0#u128 := Result.ok.inj h
    have hprod := hAbs.symm.trans ((hzero y).mpr hy0)
    rcases (Qsag.towerMul_eq_zero_iff 7 _ _).mp hprod with h | h
    · exact Or.inl ((hzero a).mp h)
    · exact Or.inr ((hzero b).mp h)
  · intro h
    have hprod : Qsag.towerMul 7 (Qsag.unpackTower 7 a.bv) (Qsag.unpackTower 7 b.bv) =
        Qsag.towerZero 7 :=
      (Qsag.towerMul_eq_zero_iff 7 _ _).mpr (h.imp (hzero a).mpr (hzero b).mpr)
    exact congrArg Result.ok ((hzero y).mp (hAbs.trans hprod))

/-! ## Tower256 -/

/-- Production-order low/high coordinates of an extracted 256-bit tower element. -/
def tower256Abs (a : tower.Tower256) : Qsag.TowerElem 8 :=
  (Qsag.unpackTower 7 a.lo.bv, Qsag.unpackTower 7 a.hi.bv)

/-- Extracted 256-bit addition refines the canonical level-eight operation. -/
theorem tower256_add_refines_qsag (a b : tower.Tower256) :
    ∃ y, tower.tower256_add a b = .ok y ∧
      tower256Abs y = Qsag.towerAdd 8 (tower256Abs a) (tower256Abs b) := by
  refine ⟨⟨a.lo ^^^ b.lo, a.hi ^^^ b.hi⟩, rfl, ?_⟩
  change (Qsag.unpackTower 7 (a.lo.bv ^^^ b.lo.bv),
      Qsag.unpackTower 7 (a.hi.bv ^^^ b.hi.bv)) = _
  rw [unpackTower_xor 7, unpackTower_xor 7]
  rfl

/-- Pure model of the extracted `tower256_mul`. -/
def pureTower256Mul (a b : tower.Tower256) : tower.Tower256 :=
  let p := pureTower128Mul a.lo b.lo
  let q := pureTower128Mul a.hi b.hi
  let r := pureTower128Mul (a.lo ^^^ a.hi) (b.lo ^^^ b.hi)
  ⟨p ^^^ q, r ^^^ p ^^^ q ^^^ pureScaleXT7 q⟩

theorem tower256_mul_eq_pure (a b : tower.Tower256) :
    tower.tower256_mul a b = .ok (pureTower256Mul a b) := by
  have hp := tower128_mul_eq_independent a.lo b.lo
  have hq := tower128_mul_eq_independent a.hi b.hi
  have hr := tower128_mul_eq_independent (a.lo ^^^ a.hi) (b.lo ^^^ b.hi)
  have hs := scale_x_t7_eq_pure (pureTower128Mul a.hi b.hi)
  unfold tower.tower256_mul
  apply bind_ok_step hp
  apply bind_ok_step hq
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hr
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step (lift_eq_ok _)
  apply bind_ok_step hs
  apply bind_ok_step (lift_eq_ok _)
  rfl

private theorem pack_tower256Abs (a : tower.Tower256) :
    Qsag.packTower 8 (tower256Abs a) = Qsag.joinBits 7 a.lo.bv a.hi.bv := by
  show Qsag.joinBits 7 (Qsag.packTower 7 (Qsag.unpackTower 7 a.lo.bv))
    (Qsag.packTower 7 (Qsag.unpackTower 7 a.hi.bv)) = _
  rw [Qsag.packTower_unpackTower, Qsag.packTower_unpackTower]

/-- Every extracted 256-bit multiplication is multiplication in the canonical field
`Qsag.TowerElem 8`. -/
theorem tower256_mul_refines_qsag (a b : tower.Tower256) :
    ∃ y, tower.tower256_mul a b = .ok y ∧
      tower256Abs y = Qsag.towerMul 8 (tower256Abs a) (tower256Abs b) := by
  refine ⟨pureTower256Mul a b, tower256_mul_eq_pure a b, ?_⟩
  apply Qsag.packTower_injective 8
  rw [← Qsag.mulExec_refines, pack_tower256Abs, pack_tower256Abs, pack_tower256Abs,
    mulExec_succ 7]
  simp only [Qsag.lowBits_join, Qsag.highBits_join, pureTower256Mul, UScalar.bv_xor,
    pureTower128Mul_eq_qsag, pureScaleXT7_eq_qsag, BitVec.xor_assoc]

/-- `#tooth`: the welds separate the operations and the levels. In `Tower256` the generator
satisfies `X₇² = 1 + X₆·X₇` (not `X₇`, and not the sum `0`), while the same low words multiply
to `3` at level seven. -/
theorem tooth_tower256_generator_square :
    (pureTower256Mul ⟨0#u128, 1#u128⟩ ⟨0#u128, 1#u128⟩).lo = 1#u128 ∧
      (pureTower256Mul ⟨0#u128, 1#u128⟩ ⟨0#u128, 1#u128⟩).hi = 18446744073709551616#u128 ∧
      pureTower128Mul 2#u128 2#u128 = 3#u128 := by decide

end qsag_verified.proofs
