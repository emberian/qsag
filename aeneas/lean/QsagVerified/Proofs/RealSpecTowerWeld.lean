module
public import QsagVerified.Proofs.TowerBdoz
public import Qsag.BinaryTower
import all Qsag.BinaryTower

/-!
Canonical multiplication coverage currently reaches GF(256). Addition below reaches
Tower128 and Tower256. The independent wider multiplication expressions in TowerBdoz
are not yet canonical multiplication welds, and none of these statements certifies
that a separately compiled production implementation executes the extracted function.
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
  exact congrArg₂ Prod.mk (unpackTower_xor 7 a.lo.bv b.lo.bv)
    (unpackTower_xor 7 a.hi.bv b.hi.bv)

end qsag_verified.proofs
