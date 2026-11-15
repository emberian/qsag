module
/-
# Qsag.Math.Tower128PolyBasisIso — `psiTower128ToPoly` is a field isomorphism onto Rust's GF(2^128)

`ParallelSeededSpnSecurity` proves its S-box, branch-number and active-box results over the
Wiedemann tower `Tower128`, while `crates/qsag-fts/src/parallel_mpc.rs` computes with
`qsag_accel::gf2_128::gf2_128_mul`: the 128-step shift-and-reduce loop on `u128` coefficient
words (bit `i` is the coefficient of `x^i`) modulo `x^128 + x^7 + x^2 + x + 1`.

This module supplies the map between the two carriers for every input:

1. `gf2_128_mul_bv_eq_rustGf128Mul`: the range-doubling definition `gf2_128_mul_bv` used by
   `psiTower128ToPoly` equals `MigrationExecution.rustGf128Mul`, the literal transcription of
   the Rust loop. Its ring laws (already proved there on the loop) therefore apply.
2. `psiTower128ToPoly` (generators `TOWER128_POLY_GENERATORS` of
   `crates/qsag-asm/src/portable.rs`) preserves zero, one, addition and multiplication.
3. `polyToTower128` is its two-sided inverse, so the map is a bijection.

`MigrationExecution.towerToRust` is a different isomorphism of the same two fields (it picks the
conjugate root from level 3 upward); `towerToRust_differs_from_psi_on_mds_constant` records that
the SPN constants are certified under `psiTower128ToPoly` only.

Scope: this relates Lean models. The Rust loop model is a transcription; no MIR or machine-code
refinement of `gf2_128_mul` is claimed here.
-/

public import Qsag.Oracle.ParallelSeededSpnSecurity
import all Qsag.Oracle.ParallelSeededSpnSecurity
public import Qsag.Protocol.Migration.ActiveMigrationZeroTest
import all Qsag.Protocol.Migration.ActiveMigrationZeroTest

public section
namespace Qsag
open MigrationExecution

set_option autoImplicit false

/-! ## 1. `gf2_128_mul_bv` is the Rust shift-and-reduce loop -/

private theorem gf128_xor_left_comm (a b c : BitVec 128) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc]

private theorem poly128Xtimes_eq_rustMulX (a : BitVec 128) :
    poly128Xtimes a = rustGf128MulX a := by
  unfold poly128Xtimes rustGf128MulX
  cases a.getLsbD 127
  · exact BitVec.xor_zero.symm
  · rfl

/-- `n` applications of multiplication by `x`. -/
def rustGf128MulXIter : Nat → BitVec 128 → BitVec 128
  | 0, a => a
  | n + 1, a => rustGf128MulXIter n (rustGf128MulX a)

theorem rustGf128MulXIter_add : ∀ (m n : Nat) (a : BitVec 128),
    rustGf128MulXIter (m + n) a = rustGf128MulXIter n (rustGf128MulXIter m a)
  | 0, n, a => by rw [Nat.zero_add]; rfl
  | m + 1, n, a => by
    rw [Nat.succ_add]
    exact rustGf128MulXIter_add m n (rustGf128MulX a)

private theorem poly128ShiftPow_eq_iter : ∀ (k : Nat) (a : BitVec 128),
    poly128ShiftPow k a = rustGf128MulXIter (2 ^ k) a
  | 0, a => poly128Xtimes_eq_rustMulX a
  | k + 1, a => by
    show poly128ShiftPow k (poly128ShiftPow k a) = _
    rw [poly128ShiftPow_eq_iter k, poly128ShiftPow_eq_iter k, Nat.pow_succ, Nat.mul_two,
      rustGf128MulXIter_add]

/-- The bit polynomial of a multiplicand splits at any degree. -/
theorem rustPolyAct_split : ∀ (m n : Nat) (f : Nat → Bool) (x : BitVec 128),
    rustPolyAct (m + n) f x =
      rustPolyAct m f x ^^^ rustPolyAct n (fun i => f (i + m)) (rustGf128MulXIter m x)
  | 0, n, f, x => by
    rw [Nat.zero_add]
    exact (BitVec.zero_xor).symm
  | m + 1, n, f, x => by
    rw [Nat.succ_add]
    show (if f 0 then x else 0#128) ^^^
        rustPolyAct (m + n) (fun i => f (i + 1)) (rustGf128MulX x) =
      ((if f 0 then x else 0#128) ^^^ rustPolyAct m (fun i => f (i + 1)) (rustGf128MulX x)) ^^^
        rustPolyAct n (fun i => f (i + (m + 1))) (rustGf128MulXIter m (rustGf128MulX x))
    rw [rustPolyAct_split m n, BitVec.xor_assoc]
    rfl

private theorem poly128MulRange_eq_act : ∀ (k : Nat) (a b : BitVec 128),
    poly128MulRange k a b = rustPolyAct (2 ^ k) b.getLsbD a
  | 0, a, b => by
    show (if b.getLsbD 0 then a else 0#128) = (if b.getLsbD 0 then a else 0#128) ^^^ 0#128
    rw [BitVec.xor_zero]
  | k + 1, a, b => by
    have hShift : (b >>> (2 ^ k)).getLsbD = fun i => b.getLsbD (i + 2 ^ k) := by
      funext i
      rw [BitVec.getLsbD_ushiftRight, Nat.add_comm]
    show poly128MulRange k a b ^^^ poly128MulRange k (poly128ShiftPow k a) (b >>> (2 ^ k)) = _
    rw [poly128MulRange_eq_act k, poly128MulRange_eq_act k, poly128ShiftPow_eq_iter, hShift,
      Nat.pow_succ, Nat.mul_two, rustPolyAct_split]

/-- **The definition used by `psiTower128ToPoly` is the Rust loop**, for all inputs. -/
theorem gf2_128_mul_bv_eq_rustGf128Mul (a b : BitVec 128) :
    gf2_128_mul_bv a b = rustGf128Mul a b := by
  unfold gf2_128_mul_bv
  rw [poly128MulRange_eq_act, rustGf128Mul_eq_act]

theorem gf2_128_mul_bv_comm (a b : BitVec 128) : gf2_128_mul_bv a b = gf2_128_mul_bv b a := by
  simp only [gf2_128_mul_bv_eq_rustGf128Mul, rustGf128Mul_comm a b]

theorem gf2_128_mul_bv_assoc (a b c : BitVec 128) :
    gf2_128_mul_bv (gf2_128_mul_bv a b) c = gf2_128_mul_bv a (gf2_128_mul_bv b c) := by
  simp only [gf2_128_mul_bv_eq_rustGf128Mul, rustGf128Mul_assoc]

theorem gf2_128_mul_bv_xor_right (a b c : BitVec 128) :
    gf2_128_mul_bv a (b ^^^ c) = gf2_128_mul_bv a b ^^^ gf2_128_mul_bv a c := by
  simp only [gf2_128_mul_bv_eq_rustGf128Mul, rustGf128Mul_xor_right]

theorem gf2_128_mul_bv_xor_left (a b c : BitVec 128) :
    gf2_128_mul_bv (a ^^^ b) c = gf2_128_mul_bv a c ^^^ gf2_128_mul_bv b c := by
  simp only [gf2_128_mul_bv_eq_rustGf128Mul, rustGf128Mul_xor_left]

theorem gf2_128_mul_bv_one_left (a : BitVec 128) : gf2_128_mul_bv 1#128 a = a := by
  rw [gf2_128_mul_bv_eq_rustGf128Mul, rustGf128Mul_one_left]

theorem gf2_128_mul_bv_one_right (a : BitVec 128) : gf2_128_mul_bv a 1#128 = a := by
  rw [gf2_128_mul_bv_eq_rustGf128Mul, rustGf128Mul_one_right]

/-! ## 2. The generator recursion as a level-indexed map -/

/-- Image of the level-`k` Wiedemann generator `towerX k`: `1` at level `0`, then
    `TOWER128_POLY_GENERATORS[k - 1]`. -/
def tower128PolyGenLevel : Nat → BitVec 128
  | 0 => 1#128
  | k + 1 => if h : k < 7 then tower128PolyGen ⟨k, h⟩ else 0#128

/-- `psiTower128ToPoly` at every tower level, with multiplication written as the Rust loop. -/
def towerToPolyBasis : (k : Nat) → TowerElem k → BitVec 128
  | 0, a => match (a : Bool) with | true => 1#128 | false => 0#128
  | k + 1, a =>
    towerToPolyBasis k a.1 ^^^
      rustGf128Mul (tower128PolyGenLevel (k + 1)) (towerToPolyBasis k a.2)

private theorem psiRec_eq_towerToPolyBasis : ∀ (k : Nat) (hk : k ≤ 7) (a : TowerElem k),
    psiRec k hk a = towerToPolyBasis k a
  | 0, _, _ => rfl
  | k + 1, hk, a => by
    rcases a with ⟨a0, a1⟩
    have hGen : tower128PolyGenLevel (k + 1) = tower128PolyGen ⟨k, hk⟩ := by
      have hk' : k < 7 := hk
      simp only [tower128PolyGenLevel, hk', ↓reduceDIte]
    show psiRec k (Nat.le_of_succ_le hk) a0 ^^^
        gf2_128_mul_bv (tower128PolyGen ⟨k, hk⟩) (psiRec k (Nat.le_of_succ_le hk) a1) =
      towerToPolyBasis k a0 ^^^
        rustGf128Mul (tower128PolyGenLevel (k + 1)) (towerToPolyBasis k a1)
    rw [psiRec_eq_towerToPolyBasis k _ a0, psiRec_eq_towerToPolyBasis k _ a1,
      gf2_128_mul_bv_eq_rustGf128Mul, hGen]

theorem psiTower128ToPoly_eq_towerToPolyBasis (x : Tower128) :
    psiTower128ToPoly x = towerToPolyBasis 7 x :=
  psiRec_eq_towerToPolyBasis 7 (Nat.le_refl 7) x

theorem towerToPolyBasis_zero : ∀ k : Nat, towerToPolyBasis k (towerZero k) = 0#128
  | 0 => rfl
  | k + 1 => by
    show towerToPolyBasis k (towerZero k) ^^^
      rustGf128Mul (tower128PolyGenLevel (k + 1)) (towerToPolyBasis k (towerZero k)) = 0#128
    rw [towerToPolyBasis_zero k, rustGf128Mul_zero_right, BitVec.xor_zero]

theorem towerToPolyBasis_one : ∀ k : Nat, towerToPolyBasis k (towerOne k) = 1#128
  | 0 => rfl
  | k + 1 => by
    show towerToPolyBasis k (towerOne k) ^^^
      rustGf128Mul (tower128PolyGenLevel (k + 1)) (towerToPolyBasis k (towerZero k)) = 1#128
    rw [towerToPolyBasis_one k, towerToPolyBasis_zero, rustGf128Mul_zero_right, BitVec.xor_zero]

theorem towerToPolyBasis_add : ∀ (k : Nat) (a b : TowerElem k),
    towerToPolyBasis k (towerAdd k a b) = towerToPolyBasis k a ^^^ towerToPolyBasis k b
  | 0, a, b => by cases a <;> cases b <;> decide
  | k + 1, a, b => by
    show towerToPolyBasis k (towerAdd k a.1 b.1) ^^^
        rustGf128Mul (tower128PolyGenLevel (k + 1)) (towerToPolyBasis k (towerAdd k a.2 b.2)) =
      (towerToPolyBasis k a.1 ^^^
        rustGf128Mul (tower128PolyGenLevel (k + 1)) (towerToPolyBasis k a.2)) ^^^
      (towerToPolyBasis k b.1 ^^^
        rustGf128Mul (tower128PolyGenLevel (k + 1)) (towerToPolyBasis k b.2))
    rw [towerToPolyBasis_add k, towerToPolyBasis_add k, rustGf128Mul_xor_right]
    simp only [BitVec.xor_assoc, gf128_xor_left_comm]

theorem towerToPolyBasis_X : ∀ k : Nat, towerToPolyBasis k (towerX k) = tower128PolyGenLevel k
  | 0 => rfl
  | k + 1 => by
    show towerToPolyBasis k (towerZero k) ^^^
      rustGf128Mul (tower128PolyGenLevel (k + 1)) (towerToPolyBasis k (towerOne k)) =
        tower128PolyGenLevel (k + 1)
    rw [towerToPolyBasis_zero, towerToPolyBasis_one, rustGf128Mul_one_right, BitVec.zero_xor]

/-- The seven Artin–Schreier relations `g_k^2 = g_k · g_{k-1} + 1` (`g_{-1} = 1`) hold for the
    Rust generators under the Rust multiplication. Kernel-evaluated. -/
theorem tower128PolyGenLevel_sq (k : Nat) (hk : k < 7) :
    rustGf128Mul (tower128PolyGenLevel (k + 1)) (tower128PolyGenLevel (k + 1)) =
      rustGf128Mul (tower128PolyGenLevel (k + 1)) (tower128PolyGenLevel k) ^^^ 1#128 := by
  have h : ∀ k : Fin 7,
      rustGf128Mul (tower128PolyGenLevel (k.val + 1)) (tower128PolyGenLevel (k.val + 1)) =
        rustGf128Mul (tower128PolyGenLevel (k.val + 1)) (tower128PolyGenLevel k.val) ^^^
          1#128 := by
    decide +kernel
  exact h ⟨k, hk⟩

set_option linter.unusedSimpArgs false in
private theorem gf128_tower_step (A1 A2 B1 B2 T U : BitVec 128)
    (hT : rustGf128Mul T T = rustGf128Mul T U ^^^ 1#128) :
    (rustGf128Mul A1 B1 ^^^ rustGf128Mul A2 B2) ^^^
      rustGf128Mul T ((rustGf128Mul A1 B2 ^^^ rustGf128Mul A2 B1) ^^^
        rustGf128Mul U (rustGf128Mul A2 B2)) =
    rustGf128Mul (A1 ^^^ rustGf128Mul T A2) (B1 ^^^ rustGf128Mul T B2) := by
  have hs : rustGf128Mul (rustGf128Mul T A2) (rustGf128Mul T B2) =
      rustGf128Mul (rustGf128Mul A2 B2) (rustGf128Mul T T) := by
    simp only [rustGf128Mul_comm, rustGf128Mul_left_comm]
  have h4 : rustGf128Mul (rustGf128Mul T A2) (rustGf128Mul T B2) =
      rustGf128Mul (rustGf128Mul A2 B2) (rustGf128Mul T U) ^^^ rustGf128Mul A2 B2 := by
    rw [hs, hT, rustGf128Mul_xor_right, rustGf128Mul_one_right]
  rw [rustGf128Mul_xor_left A1 (rustGf128Mul T A2), rustGf128Mul_xor_right A1,
    rustGf128Mul_xor_right (rustGf128Mul T A2), h4]
  simp only [rustGf128Mul_xor_right, rustGf128Mul_comm,
    rustGf128Mul_left_comm, BitVec.xor_assoc, BitVec.xor_comm, gf128_xor_left_comm]

theorem towerToPolyBasis_mul : ∀ (k : Nat), k ≤ 7 → ∀ a b : TowerElem k,
    towerToPolyBasis k (towerMul k a b) =
      rustGf128Mul (towerToPolyBasis k a) (towerToPolyBasis k b)
  | 0, _, a, b => by cases a <;> cases b <;> decide +kernel
  | k + 1, hk, a, b => by
    have ih := towerToPolyBasis_mul k (Nat.le_of_succ_le hk)
    show towerToPolyBasis k (towerAdd k (towerMul k a.1 b.1) (towerMul k a.2 b.2)) ^^^
        rustGf128Mul (tower128PolyGenLevel (k + 1)) (towerToPolyBasis k (towerAdd k
          (towerAdd k (towerMul k a.1 b.2) (towerMul k a.2 b.1))
          (towerMul k (towerX k) (towerMul k a.2 b.2)))) =
      rustGf128Mul
        (towerToPolyBasis k a.1 ^^^
          rustGf128Mul (tower128PolyGenLevel (k + 1)) (towerToPolyBasis k a.2))
        (towerToPolyBasis k b.1 ^^^
          rustGf128Mul (tower128PolyGenLevel (k + 1)) (towerToPolyBasis k b.2))
    simp only [towerToPolyBasis_add, ih, towerToPolyBasis_X]
    exact gf128_tower_step _ _ _ _ _ _ (tower128PolyGenLevel_sq k hk)

/-! ## 3. `psiTower128ToPoly` is a ring homomorphism for every pair of inputs -/

theorem psiTower128ToPoly_zero : psiTower128ToPoly (towerZero 7) = 0#128 := by
  rw [psiTower128ToPoly_eq_towerToPolyBasis, towerToPolyBasis_zero]

theorem psiTower128ToPoly_one : psiTower128ToPoly (towerOne 7) = 1#128 := by
  rw [psiTower128ToPoly_eq_towerToPolyBasis, towerToPolyBasis_one]

theorem psiTower128ToPoly_add (a b : Tower128) :
    psiTower128ToPoly (towerAdd 7 a b) = psiTower128ToPoly a ^^^ psiTower128ToPoly b := by
  simp only [psiTower128ToPoly_eq_towerToPolyBasis, towerToPolyBasis_add]

/-- Multiplicativity against the literal Rust loop model. -/
theorem psiTower128ToPoly_mul_rust (a b : Tower128) :
    psiTower128ToPoly (towerMul 7 a b) =
      rustGf128Mul (psiTower128ToPoly a) (psiTower128ToPoly b) := by
  simp only [psiTower128ToPoly_eq_towerToPolyBasis, towerToPolyBasis_mul 7 (Nat.le_refl 7)]

theorem psiTower128ToPoly_mul (a b : Tower128) :
    psiTower128ToPoly (towerMul 7 a b) =
      gf2_128_mul_bv (psiTower128ToPoly a) (psiTower128ToPoly b) := by
  rw [gf2_128_mul_bv_eq_rustGf128Mul, psiTower128ToPoly_mul_rust]

/-- A ring homomorphism out of a field is injective. -/
theorem psiTower128ToPoly_injective (a b : Tower128)
    (h : psiTower128ToPoly a = psiTower128ToPoly b) : a = b := by
  have hsum : psiTower128ToPoly (towerAdd 7 a b) = 0#128 := by
    rw [psiTower128ToPoly_add, h, BitVec.xor_self]
  by_cases hz : towerAdd 7 a b = towerZero 7
  · have hc := towerAdd_cancel 7 a b
    rw [hz, towerAdd_zero] at hc
    exact hc
  · exfalso
    have h1 := congrArg psiTower128ToPoly (towerMul_inv 7 _ hz)
    rw [psiTower128ToPoly_mul_rust, hsum, rustGf128Mul_zero_left, psiTower128ToPoly_one] at h1
    exact absurd h1 (by decide)

theorem psiTower128ToPoly_eq_zero_iff (a : Tower128) :
    psiTower128ToPoly a = 0#128 ↔ a = towerZero 7 :=
  ⟨fun h => psiTower128ToPoly_injective a _ (h.trans psiTower128ToPoly_zero.symm),
   fun h => by rw [h, psiTower128ToPoly_zero]⟩

/-! ## 4. Explicit inverse: Horner evaluation at the tower preimage of `x` -/

def polyGenTower128Bits : BitVec 128 := 0xbf72eab170e2403236a22fb2474b2624#128

/-- The tower element whose image is Rust's `x` (`2#128`): a root of
    `x^128 + x^7 + x^2 + x + 1` in `Tower128`, in `packTower` coordinates. -/
def polyGenTower128 : Tower128 := unpackTower 7 polyGenTower128Bits

set_option maxRecDepth 4096 in
theorem psiTower128ToPoly_polyGenTower128 : psiTower128ToPoly polyGenTower128 = 2#128 := by
  decide +kernel

def polyToTower128Aux : Nat → (Nat → Bool) → Tower128
  | 0, _ => towerZero 7
  | n + 1, f =>
    towerAdd 7 (if f 0 then towerOne 7 else towerZero 7)
      (towerMul 7 polyGenTower128 (polyToTower128Aux n (fun i => f (i + 1))))

/-- Inverse basis change: the Rust coefficient word evaluated at `polyGenTower128`. -/
def polyToTower128 (a : BitVec 128) : Tower128 := polyToTower128Aux 128 a.getLsbD

private theorem psiTower128ToPoly_bit (c : Bool) :
    psiTower128ToPoly (if c then towerOne 7 else towerZero 7) = if c then 1#128 else 0#128 := by
  cases c
  · exact psiTower128ToPoly_zero
  · exact psiTower128ToPoly_one

private theorem psiTower128ToPoly_polyToTower128Aux : ∀ (n : Nat) (f : Nat → Bool),
    psiTower128ToPoly (polyToTower128Aux n f) = rustPolyAct n f 1#128
  | 0, _ => psiTower128ToPoly_zero
  | n + 1, f => by
    show psiTower128ToPoly (towerAdd 7 (if f 0 then towerOne 7 else towerZero 7)
        (towerMul 7 polyGenTower128 (polyToTower128Aux n (fun i => f (i + 1))))) =
      (if f 0 then 1#128 else 0#128) ^^^
        rustPolyAct n (fun i => f (i + 1)) (rustGf128MulX 1#128)
    rw [psiTower128ToPoly_add, psiTower128ToPoly_mul_rust, psiTower128ToPoly_polyGenTower128,
      psiTower128ToPoly_polyToTower128Aux n, psiTower128ToPoly_bit, rustPolyAct_mulX,
      rustGf128MulX_eq_mul]

theorem psiTower128ToPoly_polyToTower128 (a : BitVec 128) :
    psiTower128ToPoly (polyToTower128 a) = a := by
  unfold polyToTower128
  rw [psiTower128ToPoly_polyToTower128Aux, rustPolyAct_bits_one]

theorem polyToTower128_psiTower128ToPoly (t : Tower128) :
    polyToTower128 (psiTower128ToPoly t) = t :=
  psiTower128ToPoly_injective _ _ (psiTower128ToPoly_polyToTower128 _)

theorem polyToTower128_injective (a b : BitVec 128)
    (h : polyToTower128 a = polyToTower128 b) : a = b := by
  have hc := congrArg psiTower128ToPoly h
  rw [psiTower128ToPoly_polyToTower128, psiTower128ToPoly_polyToTower128] at hc
  exact hc

theorem polyToTower128_zero : polyToTower128 0#128 = towerZero 7 := by
  apply psiTower128ToPoly_injective
  rw [psiTower128ToPoly_polyToTower128, psiTower128ToPoly_zero]

theorem polyToTower128_one : polyToTower128 1#128 = towerOne 7 := by
  apply psiTower128ToPoly_injective
  rw [psiTower128ToPoly_polyToTower128, psiTower128ToPoly_one]

theorem polyToTower128_xor (a b : BitVec 128) :
    polyToTower128 (a ^^^ b) = towerAdd 7 (polyToTower128 a) (polyToTower128 b) := by
  apply psiTower128ToPoly_injective
  rw [psiTower128ToPoly_polyToTower128, psiTower128ToPoly_add,
    psiTower128ToPoly_polyToTower128, psiTower128ToPoly_polyToTower128]

/-- Rust's multiplication is tower multiplication under the inverse basis change. -/
theorem polyToTower128_mul_rust (a b : BitVec 128) :
    polyToTower128 (rustGf128Mul a b) = towerMul 7 (polyToTower128 a) (polyToTower128 b) := by
  apply psiTower128ToPoly_injective
  rw [psiTower128ToPoly_polyToTower128, psiTower128ToPoly_mul_rust,
    psiTower128ToPoly_polyToTower128, psiTower128ToPoly_polyToTower128]

theorem polyToTower128_mul (a b : BitVec 128) :
    polyToTower128 (gf2_128_mul_bv a b) = towerMul 7 (polyToTower128 a) (polyToTower128 b) := by
  rw [gf2_128_mul_bv_eq_rustGf128Mul, polyToTower128_mul_rust]

theorem polyToTower128_eq_zero_iff (a : BitVec 128) :
    polyToTower128 a = towerZero 7 ↔ a = 0#128 :=
  ⟨fun h => polyToTower128_injective a _ (h.trans polyToTower128_zero.symm),
   fun h => by rw [h, polyToTower128_zero]⟩

theorem psiTower128ToPoly_bijective : IsBijective psiTower128ToPoly :=
  ⟨psiTower128ToPoly_injective, fun b => ⟨polyToTower128 b, psiTower128ToPoly_polyToTower128 b⟩⟩

/-- **Field isomorphism `Tower128 ≅ GF(2)[x]/(x^128+x^7+x^2+x+1)` in Rust's coordinates.**
    Every conjunct quantifies over all field elements; none is a constant check. -/
theorem psiTower128ToPoly_field_isomorphism :
    psiTower128ToPoly (towerZero 7) = 0#128 ∧
    psiTower128ToPoly (towerOne 7) = 1#128 ∧
    (∀ a b : Tower128,
      psiTower128ToPoly (towerAdd 7 a b) = psiTower128ToPoly a ^^^ psiTower128ToPoly b) ∧
    (∀ a b : Tower128,
      psiTower128ToPoly (towerMul 7 a b) =
        rustGf128Mul (psiTower128ToPoly a) (psiTower128ToPoly b)) ∧
    (∀ t : Tower128, polyToTower128 (psiTower128ToPoly t) = t) ∧
    (∀ a : BitVec 128, psiTower128ToPoly (polyToTower128 a) = a) :=
  ⟨psiTower128ToPoly_zero, psiTower128ToPoly_one, psiTower128ToPoly_add,
   psiTower128ToPoly_mul_rust, polyToTower128_psiTower128ToPoly,
   psiTower128ToPoly_polyToTower128⟩

/-! ## 5. Controls -/

/-- The certified SPN constants are the inverse images of the Rust constants. -/
theorem polyToTower128_mds_constants :
    polyToTower128 gf128MdsAPolyBits = gf128MdsATower ∧
    polyToTower128 gf128MdsBPolyBits = gf128MdsBTower := by
  refine ⟨?_, ?_⟩
  · rw [← gf128_mds_constants_certified.1, polyToTower128_psiTower128ToPoly]
  · rw [← gf128_mds_constants_certified.2.1, polyToTower128_psiTower128ToPoly]

/-- Negative control: `packTower` coordinates are not the Rust basis. The tower element with
    packed word `2` (the level-1 generator) maps to `TOWER128_POLY_GENERATORS[0]`, and its
    square is `3` in packed tower coordinates but `x^2 = 4` for Rust's word `2`. -/
theorem tooth_packTower_is_not_the_poly_basis :
    psiTower128ToPoly (unpackTower 7 2#128) ≠ 2#128 ∧
    mulExec 7 2#128 2#128 = 3#128 ∧ rustGf128Mul 2#128 2#128 = 4#128 := by
  refine ⟨?_, ?_, rust_gf128_basis_kats.1⟩
  · have h : psiTower128ToPoly (unpackTower 7 2#128) =
        0x295ac0b1f4731af9676aac9fa4b20b08#128 := by decide +kernel
    rw [h]; decide
  · decide +kernel

/-- Negative control: the other verified isomorphism `MigrationExecution.towerToRust` (conjugate
    root choice) does not send the tower SPN constant to the Rust constant. Statements about
    `gf128MdsATower` transport to Rust arithmetic through `psiTower128ToPoly`, not through it. -/
theorem towerToRust_differs_from_psi_on_mds_constant :
    towerToRust 7 gf128MdsATower ≠ gf128MdsAPolyBits ∧
    psiTower128ToPoly gf128MdsATower = gf128MdsAPolyBits := by
  refine ⟨?_, gf128_mds_constants_certified.1⟩
  decide +kernel

end Qsag
end

#verify_constructive
  Qsag.gf2_128_mul_bv_eq_rustGf128Mul
  Qsag.psiTower128ToPoly_field_isomorphism
  Qsag.psiTower128ToPoly_mul
  Qsag.psiTower128ToPoly_bijective
  Qsag.polyToTower128_mul
  Qsag.polyToTower128_mds_constants
  Qsag.tooth_packTower_is_not_the_poly_basis
  Qsag.towerToRust_differs_from_psi_on_mds_constant
