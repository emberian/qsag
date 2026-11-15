module
/-
# Qsag.Math.Gf2Pow128 — Canonical Polynomial-Basis GF(2^128) Field and Five-Way Isomorphism

Unifies all scattered `𝔽_{2^{128}}` representations across the codebase under a single canonical
`LawfulField` carrier `Gf2Pow128` (`𝔽_2[x]/(x^128 + x^7 + x^2 + x + 1)`) and explicit `FieldIso`
with Wiedemann's binary tower `Tower128`:
1. `Tower128` (`BinaryTower.TowerElem 7`, Wiedemann tower `𝔽_2[x₀,…,x₆]/(xₖ² + xₖ xₖ₋₁ + 1)`),
2. `MigrationExecution.rustGf128Mul` (`ActiveMigrationZeroTest`, 128-step shift-and-reduce),
3. `gf2_128_mul_bv` (`ParallelSeededSpnSecurity` bit-vector field product),
4. `gf128FieldMul` (`McRefine` carry-less polynomial remainder), and
5. `SimdBinaryEquiv.fastRemainder ∘ pclmulqdqFourProduct256` / `pmullFourProduct256`
   (`Gf128ClmulLoopAgreement` x86-64 `PCLMULQDQ` and AArch64 `PMULL` two-fold `0x87` kernels).
-/

public import Qsag.Math.QuarticExt4
public import Qsag.Gf128ClmulLoopAgreement
import all Qsag.BinaryTower
import all Qsag.Tower128PolyBasisIso
import Qsag.Tactic.AssuranceKit

public section

namespace Qsag

theorem towerZero_ne_towerOne (k : Nat) : towerZero k ≠ towerOne k :=
  fun h => towerOne_ne_zero k h.symm

instance instLawfulFieldTowerElem (k : Nat) : LawfulField (TowerElem k) where
  inv := towerInv k
  zero_ne_one := towerZero_ne_towerOne k
  mul_inv_cancel {_a} ha := towerMul_inv k _ ha

end Qsag

namespace Qsag.Math

set_option autoImplicit false

/-- Canonical polynomial-basis element of `𝔽_{2^{128}} = 𝔽_2[x]/(x^128 + x^7 + x^2 + x + 1)`. -/
structure Gf2Pow128 where
  bits : BitVec 128
  deriving DecidableEq, Repr

namespace Gf2Pow128

@[ext] theorem ext {a b : Gf2Pow128} (h : a.bits = b.bits) : a = b := by
  cases a; cases b; cases h; rfl

@[expose] def zero : Gf2Pow128 := ⟨0#128⟩

@[expose] def one : Gf2Pow128 := ⟨1#128⟩

@[expose] def add (a b : Gf2Pow128) : Gf2Pow128 := ⟨a.bits ^^^ b.bits⟩

@[expose] def mul (a b : Gf2Pow128) : Gf2Pow128 := ⟨Qsag.gf128FieldMul a.bits b.bits⟩

@[expose] def inv (a : Gf2Pow128) : Gf2Pow128 :=
  ⟨Qsag.psiTower128ToPoly (Qsag.towerInv 7 (Qsag.polyToTower128 a.bits))⟩

instance : Inhabited Gf2Pow128 := ⟨zero⟩

instance : CommRingOps Gf2Pow128 where
  zero := zero
  one := one
  add := add
  mul := mul
  neg a := a
  sub := add

private theorem toTower_inj {a b : Gf2Pow128}
    (h : Qsag.polyToTower128 a.bits = Qsag.polyToTower128 b.bits) : a = b :=
  ext (Qsag.polyToTower128_injective a.bits b.bits h)

private theorem toTower_add (a b : Gf2Pow128) :
    Qsag.polyToTower128 (CommRingOps.add a b).bits =
      Qsag.towerAdd 7 (Qsag.polyToTower128 a.bits) (Qsag.polyToTower128 b.bits) :=
  Qsag.polyToTower128_xor a.bits b.bits

private theorem toTower_mul (a b : Gf2Pow128) :
    Qsag.polyToTower128 (CommRingOps.mul a b).bits =
      Qsag.towerMul 7 (Qsag.polyToTower128 a.bits) (Qsag.polyToTower128 b.bits) :=
  Qsag.polyToTower128_gf128FieldMul a.bits b.bits

instance : LawfulCommRing Gf2Pow128 where
  add_assoc a b c := by
    apply toTower_inj
    rw [toTower_add, toTower_add, toTower_add, toTower_add]
    exact Qsag.towerAdd_assoc 7 _ _ _
  add_comm a b := by
    apply toTower_inj
    rw [toTower_add, toTower_add]
    exact Qsag.towerAdd_comm 7 _ _
  zero_add a := by
    apply toTower_inj
    rw [toTower_add, show (CommRingOps.zero : Gf2Pow128).bits = 0#128 from rfl, Qsag.polyToTower128_zero]
    exact Qsag.towerZero_add 7 _
  add_zero a := by
    apply toTower_inj
    rw [toTower_add, show (CommRingOps.zero : Gf2Pow128).bits = 0#128 from rfl, Qsag.polyToTower128_zero]
    exact Qsag.towerAdd_zero 7 _
  add_left_neg a := by
    apply toTower_inj
    change Qsag.polyToTower128 (CommRingOps.add a a).bits = Qsag.polyToTower128 (CommRingOps.zero : Gf2Pow128).bits
    rw [toTower_add, show (CommRingOps.zero : Gf2Pow128).bits = 0#128 from rfl, Qsag.polyToTower128_zero]
    exact Qsag.towerAdd_self_zero 7 _
  sub_eq_add_neg _ _ := rfl
  mul_comm a b := by
    apply toTower_inj
    rw [toTower_mul, toTower_mul]
    exact Qsag.towerMul_comm 7 _ _
  one_mul a := by
    apply toTower_inj
    rw [toTower_mul, show (CommRingOps.one : Gf2Pow128).bits = 1#128 from rfl, Qsag.polyToTower128_one]
    exact Qsag.towerOne_mul 7 _
  mul_one a := by
    apply toTower_inj
    rw [toTower_mul, show (CommRingOps.one : Gf2Pow128).bits = 1#128 from rfl, Qsag.polyToTower128_one]
    exact Qsag.towerMul_one 7 _
  left_distrib a b c := by
    apply toTower_inj
    rw [toTower_mul, toTower_add, toTower_add, toTower_mul, toTower_mul]
    exact Qsag.towerMul_add_distrib 7 _ _ _
  right_distrib a b c := by
    apply toTower_inj
    rw [toTower_mul, toTower_add, toTower_add, toTower_mul, toTower_mul]
    exact Qsag.towerAdd_mul_distrib 7 _ _ _
  mul_assoc a b c := by
    apply toTower_inj
    rw [toTower_mul, toTower_mul, toTower_mul, toTower_mul]
    exact Qsag.towerMul_assoc 7 _ _ _

theorem mul_inv_cancel {a : Gf2Pow128} (ha : a ≠ CommRingOps.zero) :
    CommRingOps.mul a (inv a) = CommRingOps.one := by
  apply toTower_inj
  rw [toTower_mul, show (CommRingOps.one : Gf2Pow128).bits = 1#128 from rfl]
  unfold inv
  dsimp only
  rw [Qsag.polyToTower128_psiTower128ToPoly, Qsag.polyToTower128_one]
  have hTowerNe : Qsag.polyToTower128 a.bits ≠ Qsag.towerZero 7 := by
    intro h0
    apply ha
    apply ext
    exact (Qsag.polyToTower128_eq_zero_iff a.bits).mp h0
  exact Qsag.towerMul_inv 7 _ hTowerNe

theorem zero_ne_one : (CommRingOps.zero : Gf2Pow128) ≠ CommRingOps.one := by
  intro h
  have hb : (0#128 : BitVec 128) = 1#128 := congrArg Gf2Pow128.bits h
  exact absurd hb (by decide)

instance : LawfulField Gf2Pow128 where
  inv := inv
  zero_ne_one := zero_ne_one
  mul_inv_cancel := mul_inv_cancel

instance : NoZeroDivisors Gf2Pow128 :=
  Qsag.LawfulField.toNoZeroDivisors Gf2Pow128

end Gf2Pow128

/-- Constructive ring isomorphism `Tower128 ≃+* Gf2Pow128`. -/
def ringIsoTower128ToPoly : RingIso Qsag.Tower128 Gf2Pow128 where
  toFun t := ⟨Qsag.psiTower128ToPoly t⟩
  invFun p := Qsag.polyToTower128 p.bits
  left_inv t := Qsag.polyToTower128_psiTower128ToPoly t
  right_inv p := Gf2Pow128.ext (Qsag.psiTower128ToPoly_polyToTower128 p.bits)
  map_zero := Gf2Pow128.ext Qsag.psiTower128ToPoly_zero
  map_one := Gf2Pow128.ext Qsag.psiTower128ToPoly_one
  map_add x y := Gf2Pow128.ext (Qsag.psiTower128ToPoly_add x y)
  map_neg _ := rfl
  map_sub x y := Gf2Pow128.ext (Qsag.psiTower128ToPoly_add x y)
  map_mul x y := Gf2Pow128.ext (Qsag.psiTower128ToPoly_mul_fieldMul x y)

theorem towerInv_zero : ∀ k : Nat, Qsag.towerInv k (Qsag.towerZero k) = Qsag.towerZero k
  | 0 => rfl
  | k + 1 => by
    unfold Qsag.towerInv Qsag.towerZero
    dsimp only
    rw [Qsag.towerMul_zero, Qsag.towerAdd_zero, Qsag.towerZero_mul]

theorem towerInv7_zero :
    LawfulField.inv (CommRingOps.zero : Qsag.Tower128) = CommRingOps.zero :=
  towerInv_zero 7

theorem gf2Pow128_inv_zero :
    LawfulField.inv (CommRingOps.zero : Gf2Pow128) = CommRingOps.zero := by
  change Gf2Pow128.inv Gf2Pow128.zero = Gf2Pow128.zero
  unfold Gf2Pow128.inv Gf2Pow128.zero
  rw [Qsag.polyToTower128_zero, towerInv_zero 7, Qsag.psiTower128ToPoly_zero]

/-- **Canonical Field Isomorphism (`isoTower128ToPoly : FieldIso Tower128 Gf2Pow128`)**:
    Preserves `0, 1, +, -, sub, *`, and `inv` across Wiedemann's tower and the polynomial basis. -/
@[expose] def isoTower128ToPoly : FieldIso Qsag.Tower128 Gf2Pow128 :=
  ringIsoTower128ToPoly.toFieldIso towerInv7_zero gf2Pow128_inv_zero

/-- **Five-Way `𝔽_{2^{128}}` Multiplication Agreement (`gf2Pow128_five_way_mul_agreement`)**:
    Certifies that canonical `Gf2Pow128.mul` agrees identically on all 128-bit inputs with:
    1. Wiedemann `towerMul 7` transported via `psiTower128ToPoly` / `polyToTower128`,
    2. `MigrationExecution.rustGf128Mul` (128-step Rust shift-and-reduce),
    3. `gf2_128_mul_bv` (`ParallelSeededSpnSecurity` bit-vector multiplication),
    4. `SimdBinaryEquiv.fastRemainder ∘ pclmulqdqFourProduct256` (x86-64 `PCLMULQDQ`), and
    5. `SimdBinaryEquiv.fastRemainder ∘ pmullFourProduct256` (AArch64 `PMULL` / `PMULL2`). -/
theorem gf2Pow128_five_way_mul_agreement (a b : BitVec 128) :
    let prod := (Gf2Pow128.mul ⟨a⟩ ⟨b⟩).bits
    prod = Qsag.psiTower128ToPoly (Qsag.towerMul 7 (Qsag.polyToTower128 a) (Qsag.polyToTower128 b)) ∧
    prod = Qsag.MigrationExecution.rustGf128Mul a b ∧
    prod = Qsag.gf2_128_mul_bv a b ∧
    prod = Qsag.SimdBinaryEquiv.fastRemainder (Qsag.pclmulqdqFourProduct256 a b) ∧
    prod = Qsag.SimdBinaryEquiv.fastRemainder (Qsag.pmullFourProduct256 a b) := by
  intro prod
  dsimp only [prod, Gf2Pow128.mul]
  refine ⟨?_, Qsag.gf128FieldMul_eq_rustGf128Mul a b,
    Qsag.gf128FieldMul_eq_gf2_128_mul_bv a b,
    (Qsag.pclmulqdqFourProduct_reduce_eq_gf128FieldMul a b).symm,
    (Qsag.pmullFourProduct_reduce_eq_gf128FieldMul a b).symm⟩
  rw [← Qsag.polyToTower128_gf128FieldMul a b, Qsag.psiTower128ToPoly_polyToTower128]

#verify_constructive
  Qsag.Math.Gf2Pow128.mul_inv_cancel
  Qsag.Math.gf2Pow128_five_way_mul_agreement

end Qsag.Math
end
