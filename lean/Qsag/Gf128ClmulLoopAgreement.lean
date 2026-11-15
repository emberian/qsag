module
/-
# Qsag.Gf128ClmulLoopAgreement — the carry-less-multiply specification is the Rust loop

Two Lean specifications of multiplication in `GF(2)[x]/(x^128 + x^7 + x^2 + x + 1)` exist:

* `gf128FieldMul` (`McRefine`): schoolbook carry-less product followed by polynomial long
  division. The PCLMULQDQ, VPCLMULQDQ and NEON kernels behind `bdoz_gf2_128_batch_dot` are
  verified against it in `ElfFunctionalEquiv`.
* `MigrationExecution.rustGf128Mul`: the shift-and-reduce loop of
  `qsag_accel::gf2_128::gf2_128_mul`, which `parallel_mpc.rs` uses for the SPN and for share
  arithmetic.

`gf128FieldMul_eq_rustGf128Mul` proves they are the same function. The proof does not
enumerate monomial pairs. Long division commutes with multiplication by `x`
(`gf128Reduce_shiftLeft_one`, from XOR-linearity and the 256 monomials of the double-width
product), so `reduce(a · x^n)` is `n` applications of the loop's `mul-by-x` step; summing over
the set bits of `b` gives the loop. With `Tower128PolyBasisIso` the kernel specification is
therefore tower multiplication under `polyToTower128`.

Scope: this is an equality of Lean specifications. It adds nothing to the existing
machine-code results and claims no refinement of the Rust loop itself.
-/

public import Qsag.McRefine
import all Qsag.McRefine
public import Qsag.Tower128PolyBasisIso
import all Qsag.Tower128PolyBasisIso
import all Qsag.ActiveMigrationZeroTest

public section
namespace Qsag
open MigrationExecution

set_option autoImplicit false

theorem gf128Reduce_zero : gf128Reduce 0#256 = 0#128 := by
  have h := gf128Reduce_xor 0#256 0#256
  rw [BitVec.xor_self, BitVec.xor_self] at h
  exact h

private theorem rustGf128MulX_xor' (a b : BitVec 128) :
    rustGf128MulX (a ^^^ b) = rustGf128MulX a ^^^ rustGf128MulX b := by
  rw [rustGf128MulX_eq_mul, rustGf128MulX_eq_mul, rustGf128MulX_eq_mul, rustGf128Mul_xor_right]

private theorem rustGf128MulX_zero' : rustGf128MulX 0#128 = 0#128 := by
  rw [rustGf128MulX_eq_mul, rustGf128Mul_zero_right]

private theorem ite_bool_xor_split (c d : Bool) (k : BitVec 128) :
    (if (c ^^ d) = true then k else 0#128) =
      (if c = true then k else 0#128) ^^^ (if d = true then k else 0#128) := by
  cases c <;> cases d
  · exact BitVec.xor_zero.symm
  · exact BitVec.zero_xor.symm
  · exact BitVec.xor_zero.symm
  · exact BitVec.xor_self.symm

private theorem xor_shuffle (a b c d : BitVec 128) :
    (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  rw [BitVec.xor_assoc, ← BitVec.xor_assoc b c d, BitVec.xor_comm b c, BitVec.xor_assoc c b d,
    ← BitVec.xor_assoc]

/-- Correction for the one monomial `x^255` whose shift leaves the 256-bit word. -/
private def gf128TopShiftCorrection : BitVec 128 :=
  rustGf128MulX (gf128Reduce ((1 : BitVec 256) <<< 255))

set_option maxRecDepth 8192 in
private theorem gf128Reduce_shift_monomials : ∀ m : Fin 256,
    gf128Reduce (((1 : BitVec 256) <<< m.val) <<< 1) =
      rustGf128MulX (gf128Reduce ((1 : BitVec 256) <<< m.val)) ^^^
        (if ((1 : BitVec 256) <<< m.val).getLsbD 255 then gf128TopShiftCorrection else 0#128) := by
  decide +kernel

/-- **Long division commutes with multiplication by `x`**, for every double-width polynomial
    of degree below 255. -/
theorem gf128Reduce_shiftLeft_one (p : BitVec 256) (hTop : p.getLsbD 255 = false) :
    gf128Reduce (p <<< 1) = rustGf128MulX (gf128Reduce p) := by
  have hAll := gf128Linear_ext
    (fun p : BitVec 256 => gf128Reduce (p <<< 1))
    (fun p : BitVec 256 => rustGf128MulX (gf128Reduce p) ^^^
      (if p.getLsbD 255 then gf128TopShiftCorrection else 0#128))
    (by show gf128Reduce ((0 : BitVec 256) <<< 1) = 0
        rw [show (0 : BitVec 256) <<< 1 = 0#256 from by decide]; exact gf128Reduce_zero)
    (by show rustGf128MulX (gf128Reduce (0 : BitVec 256)) ^^^
          (if (0 : BitVec 256).getLsbD 255 then gf128TopShiftCorrection else 0#128) = 0
        rw [show (0 : BitVec 256).getLsbD 255 = false from by decide]
        show rustGf128MulX (gf128Reduce 0#256) ^^^ 0#128 = 0#128
        rw [gf128Reduce_zero, rustGf128MulX_zero', BitVec.xor_zero])
    (fun x y => by
      show gf128Reduce ((x ^^^ y) <<< 1) = gf128Reduce (x <<< 1) ^^^ gf128Reduce (y <<< 1)
      rw [BitVec.shiftLeft_xor_distrib, gf128Reduce_xor])
    (fun x y => by
      show rustGf128MulX (gf128Reduce (x ^^^ y)) ^^^
          (if (x ^^^ y).getLsbD 255 then gf128TopShiftCorrection else 0#128) =
        (rustGf128MulX (gf128Reduce x) ^^^
          (if x.getLsbD 255 then gf128TopShiftCorrection else 0#128)) ^^^
        (rustGf128MulX (gf128Reduce y) ^^^
          (if y.getLsbD 255 then gf128TopShiftCorrection else 0#128))
      rw [gf128Reduce_xor, rustGf128MulX_xor', BitVec.getLsbD_xor, ite_bool_xor_split,
        xor_shuffle])
    (fun m hm => gf128Reduce_shift_monomials ⟨m, hm⟩) p
  have hP : gf128Reduce (p <<< 1) = rustGf128MulX (gf128Reduce p) ^^^
      (if p.getLsbD 255 then gf128TopShiftCorrection else 0#128) := hAll
  rw [hP, hTop]
  exact BitVec.xor_zero

set_option maxRecDepth 8192 in
private theorem gf128Reduce_setWidth_monomials : ∀ i : Fin 128,
    gf128Reduce (((1 : BitVec 128) <<< i.val).setWidth 256) = (1 : BitVec 128) <<< i.val := by
  decide +kernel

/-- Long division fixes polynomials of degree below 128. -/
theorem gf128Reduce_setWidth (a : BitVec 128) : gf128Reduce (a.setWidth 256) = a :=
  gf128Linear_ext (fun a : BitVec 128 => gf128Reduce (a.setWidth 256)) (fun a => a)
    (by show gf128Reduce ((0 : BitVec 128).setWidth 256) = 0
        rw [show (0 : BitVec 128).setWidth 256 = 0#256 from by decide]; exact gf128Reduce_zero)
    rfl
    (fun x y => by
      show gf128Reduce ((x ^^^ y).setWidth 256) =
        gf128Reduce (x.setWidth 256) ^^^ gf128Reduce (y.setWidth 256)
      rw [BitVec.setWidth_xor, gf128Reduce_xor])
    (fun _ _ => rfl)
    (fun i hi => gf128Reduce_setWidth_monomials ⟨i, hi⟩) a

private theorem setWidth_shift_top_clear (a : BitVec 128) (n : Nat) (hn : n ≤ 126) :
    ((a.setWidth 256) <<< n).getLsbD 255 = false := by
  have h : a.getLsbD (255 - n) = false := BitVec.getLsbD_of_ge a _ (by omega)
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, h, Bool.and_false]

/-- `reduce(a · x^n)` is `n` loop steps applied to `a`, for `n ≤ 127`. -/
theorem gf128Reduce_shiftLeft_setWidth (a : BitVec 128) : ∀ n : Nat, n ≤ 127 →
    gf128Reduce ((a.setWidth 256) <<< n) = rustGf128MulXIter n a
  | 0, _ => by
    rw [show (a.setWidth 256) <<< 0 = a.setWidth 256 from BitVec.shiftLeft_zero _]
    exact gf128Reduce_setWidth a
  | n + 1, hn => by
    rw [BitVec.shiftLeft_add,
      gf128Reduce_shiftLeft_one _ (setWidth_shift_top_clear a n (by omega)),
      gf128Reduce_shiftLeft_setWidth a n (by omega), rustGf128MulXIter_add n 1 a]
    rfl

private theorem gf128Reduce_polyMulAux (a b : BitVec 128) : ∀ n : Nat, n ≤ 128 →
    gf128Reduce (gf128PolyMulAux (a.setWidth 256) b n) = rustPolyAct n b.getLsbD a
  | 0, _ => gf128Reduce_zero
  | n + 1, hn => by
    have hTerm : gf128Reduce (if b.getLsbD n then (a.setWidth 256) <<< n else 0) =
        (if b.getLsbD n then rustGf128MulXIter n a else 0#128) := by
      cases b.getLsbD n
      · exact gf128Reduce_zero
      · exact gf128Reduce_shiftLeft_setWidth a n (by omega)
    show gf128Reduce (gf128PolyMulAux (a.setWidth 256) b n ^^^
      (if b.getLsbD n then (a.setWidth 256) <<< n else 0)) = _
    rw [gf128Reduce_xor, gf128Reduce_polyMulAux a b n (by omega), hTerm, rustPolyAct_split n 1]
    show _ = rustPolyAct n b.getLsbD a ^^^
      ((if b.getLsbD (0 + n) then rustGf128MulXIter n a else 0#128) ^^^ 0#128)
    rw [Nat.zero_add, BitVec.xor_zero]

/-- **Carry-less multiply then reduce = shift-and-reduce loop**, for all inputs. -/
theorem gf128FieldMul_eq_rustGf128Mul (a b : BitVec 128) :
    gf128FieldMul a b = rustGf128Mul a b := by
  rw [rustGf128Mul_eq_act]
  exact gf128Reduce_polyMulAux a b 128 (Nat.le_refl 128)

theorem gf128FieldMul_eq_gf2_128_mul_bv (a b : BitVec 128) :
    gf128FieldMul a b = gf2_128_mul_bv a b := by
  rw [gf128FieldMul_eq_rustGf128Mul, gf2_128_mul_bv_eq_rustGf128Mul]

/-- The kernel specification is tower multiplication under the basis change. -/
theorem polyToTower128_gf128FieldMul (a b : BitVec 128) :
    polyToTower128 (gf128FieldMul a b) = towerMul 7 (polyToTower128 a) (polyToTower128 b) := by
  rw [gf128FieldMul_eq_rustGf128Mul, polyToTower128_mul_rust]

theorem psiTower128ToPoly_mul_fieldMul (a b : Tower128) :
    psiTower128ToPoly (towerMul 7 a b) =
      gf128FieldMul (psiTower128ToPoly a) (psiTower128ToPoly b) := by
  rw [gf128FieldMul_eq_rustGf128Mul, psiTower128ToPoly_mul_rust]

end Qsag
end

#verify_constructive
  Qsag.gf128Reduce_shiftLeft_one
  Qsag.gf128FieldMul_eq_rustGf128Mul
  Qsag.polyToTower128_gf128FieldMul
  Qsag.psiTower128ToPoly_mul_fieldMul
