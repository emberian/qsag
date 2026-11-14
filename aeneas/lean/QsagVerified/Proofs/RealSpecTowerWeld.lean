module
public import QsagVerified.Proofs.TowerBdoz
public import Qsag.BinaryTower
import all Qsag.BinaryTower

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
end qsag_verified.proofs
