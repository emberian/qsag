module
/-
# Qsag.Machine.Gf128ClmulLoopAgreement — Symbolic Field-Loop Agreement and SIMD Carry-Less Multiply Bridge

Three representations of multiplication in `GF(2^128)` appear across specifications,
Rust share/SPN arithmetic, and SIMD assembly kernels:

* `towerMul 7` (`ParallelSeededSpn`): Wiedemann tower `GF(2)[x₀,…,x₆]/(xₖ² + xₖ·xₖ₋₁ + 1)`.
* `MigrationExecution.rustGf128Mul`: the 128-step shift-and-reduce loop of
  `qsag_accel::gf2_128::gf2_128_mul` over `GF(2)[z]/(z^128 + z^7 + z^2 + z + 1)`.
* `gf128FieldMul` (`McRefine`) and `SimdBinaryEquiv.fastRemainder ∘ SimdBinaryEquiv.clmul128`:
  four-limb carry-less multiplication (`PCLMULQDQ` / `VPCLMULQDQ` / `PMULL` + `PMULL2`)
  followed by two-fold `0x87` polynomial reduction (`gf2_128_reduce_x128_7_2_1_0`).

`gf128Reduce_shiftLeft_one` and `gf128Reduce_setWidth` are proved structurally from the
single-step shift commutation `gf128ReduceStep (k + 1) (p <<< 1) = (gf128ReduceStep k p) <<< 1`
without enumerating 256-bit or 128-bit monomial tables in the kernel. Combining this with
`Tower128PolyBasisIso` and `SimdBinaryEquiv` links `towerMul 7`, `rustGf128Mul`,
`gf128FieldMul`, single-lane `PCLMULQDQ` / `PMULL` reduction, and dual-lane `VPCLMULQDQ`
carry-less dot-product accumulation under the explicit basis isomorphism `psiTower128ToPoly` /
`polyToTower128`.
-/

public import Qsag.Machine.McRefine
import all Qsag.Machine.McRefine
public import Qsag.Math.Tower128PolyBasisIso
import all Qsag.Math.Tower128PolyBasisIso
public import Qsag.Machine.SimdBinaryEquiv
import all Qsag.Machine.SimdBinaryEquiv
import all Qsag.Protocol.Migration.ActiveMigrationZeroTest

public section
namespace Qsag
open MigrationExecution

set_option autoImplicit false

theorem gf128Reduce_zero : gf128Reduce 0#256 = 0#128 := by
  have h := gf128Reduce_xor 0#256 0#256
  rw [BitVec.xor_self, BitVec.xor_self] at h
  exact h

private theorem gf128ReduceStep_shiftLeft_one (k : Nat) (hk : k < 127) (p : BitVec 256) :
    gf128ReduceStep (k + 1) (p <<< 1) = (gf128ReduceStep k p) <<< 1 := by
  unfold gf128ReduceStep
  have hBit : (p <<< 1).getLsbD (128 + (k + 1)) = p.getLsbD (128 + k) := by
    simp only [BitVec.getLsbD_shiftLeft, show 128 + (k + 1) < 256 by omega, decide_true,
      show ¬ (128 + (k + 1) < 1) by omega, decide_false, Bool.not_false, Bool.true_and,
      show 128 + (k + 1) - 1 = 128 + k by omega]
  rw [hBit]
  cases p.getLsbD (128 + k)
  · rfl
  · simp only [↓reduceIte, BitVec.shiftLeft_xor_distrib, ← BitVec.shiftLeft_add]

private theorem gf128ReduceAux_shiftLeft_one :
    ∀ (n : Nat), n ≤ 127 → ∀ (q : BitVec 256),
      gf128ReduceAux (n + 1) (q <<< 1) = gf128ReduceStep 0 ((gf128ReduceAux n q) <<< 1)
  | 0, _, _ => rfl
  | m + 1, hm, q => by
    change gf128ReduceAux (m + 1) (gf128ReduceStep (m + 1) (q <<< 1)) =
      gf128ReduceStep 0 ((gf128ReduceAux m (gf128ReduceStep m q)) <<< 1)
    rw [gf128ReduceStep_shiftLeft_one m (by omega) q,
      gf128ReduceAux_shiftLeft_one m (by omega) (gf128ReduceStep m q)]

private theorem setWidth128_shiftLeft_one (u : BitVec 256) :
    (u <<< 1).setWidth 128 = (u.setWidth 128) <<< 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and,
    show i < 256 by omega]
  by_cases hi0 : i < 1
  · simp [hi0]
  · simp [hi0, show i - 1 < 128 by omega]

private theorem gf128ReduceStep_zero_shiftLeft_setWidth (u : BitVec 256) :
    (gf128ReduceStep 0 (u <<< 1)).setWidth 128 = rustGf128MulX (u.setWidth 128) := by
  unfold gf128ReduceStep rustGf128MulX
  have hBit1 : (u <<< 1).getLsbD (128 + 0) = u.getLsbD 127 := by simp
  have hBit2 : (u.setWidth 128).getLsbD 127 = u.getLsbD 127 := by simp
  have hMod : gf128Modulus.setWidth 128 = 0x87#128 := by decide
  rw [hBit1, hBit2, BitVec.shiftLeft_zero]
  cases u.getLsbD 127
  · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.xor_zero, setWidth128_shiftLeft_one]
  · simp only [↓reduceIte, BitVec.setWidth_xor, setWidth128_shiftLeft_one, hMod]

/-- **Long division commutes with multiplication by `x`**, for every double-width polynomial
    of degree below 255. Proved structurally without monomial table enumeration. -/
theorem gf128Reduce_shiftLeft_one (p : BitVec 256) (hTop : p.getLsbD 255 = false) :
    gf128Reduce (p <<< 1) = rustGf128MulX (gf128Reduce p) := by
  have hStep127 : gf128ReduceStep 127 p = p := by
    unfold gf128ReduceStep
    rw [show 128 + 127 = 255 from rfl, hTop]
    rfl
  have hAux128 : gf128ReduceAux 128 p = gf128ReduceAux 127 p := by
    change gf128ReduceAux 127 (gf128ReduceStep 127 p) = gf128ReduceAux 127 p
    rw [hStep127]
  unfold gf128Reduce
  rw [gf128ReduceAux_shiftLeft_one 127 (Nat.le_refl 127) p, ← hAux128,
    gf128ReduceStep_zero_shiftLeft_setWidth]

private theorem gf128ReduceAux_of_high_clear :
    ∀ (n : Nat) (p : BitVec 256),
      (∀ k, k < n → p.getLsbD (128 + k) = false) → gf128ReduceAux n p = p
  | 0, _, _ => rfl
  | n + 1, p, hClear => by
    have hn : p.getLsbD (128 + n) = false := hClear n (Nat.lt_succ_self n)
    simp only [gf128ReduceAux, gf128ReduceStep, hn, Bool.false_eq_true, ↓reduceIte]
    exact gf128ReduceAux_of_high_clear n p (fun k hk => hClear k (by omega))

/-- Long division fixes polynomials of degree below 128. -/
theorem gf128Reduce_setWidth (a : BitVec 128) : gf128Reduce (a.setWidth 256) = a := by
  unfold gf128Reduce
  rw [gf128ReduceAux_of_high_clear 128 (a.setWidth 256)]
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [hi]
  · intro k _
    simp

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

/-! ## Connection to `SimdBinaryEquiv` (`PCLMULQDQ` / `VPCLMULQDQ` / `PMULL` + `0x87` Reduction) -/

private theorem simdXorSum_eq_gf128PolyMulAux (a b : BitVec 128) :
    ∀ n : Nat,
      SimdBinaryEquiv.xorSum n (fun i => if b.getLsbD i then a.setWidth 256 <<< i else 0) =
        gf128PolyMulAux (a.setWidth 256) b n
  | 0 => rfl
  | n + 1 => by
    simp only [SimdBinaryEquiv.xorSum, gf128PolyMulAux, simdXorSum_eq_gf128PolyMulAux a b n]

/-- `SimdBinaryEquiv.clmul128` is definitionally aligned with `McRefine.gf128PolyMul`. -/
theorem simdClmul128_eq_gf128PolyMul (a b : BitVec 128) :
    SimdBinaryEquiv.clmul128 a b = gf128PolyMul (a.setWidth 256) b :=
  simdXorSum_eq_gf128PolyMulAux a b 128

private theorem simdRemainderSteps_eq_gf128ReduceAux :
    ∀ (n : Nat) (p : BitVec 256),
      SimdBinaryEquiv.polynomialRemainderSteps n p = gf128ReduceAux n p
  | 0, _ => rfl
  | n + 1, p => by
    simp only [SimdBinaryEquiv.polynomialRemainderSteps, gf128ReduceAux, gf128ReduceStep,
      gf128Modulus]
    exact simdRemainderSteps_eq_gf128ReduceAux n _

/-- `SimdBinaryEquiv.polynomialRemainder` equals `McRefine.gf128Reduce`. -/
theorem simdPolynomialRemainder_eq_gf128Reduce (p : BitVec 256) :
    SimdBinaryEquiv.polynomialRemainder p = gf128Reduce p := by
  unfold SimdBinaryEquiv.polynomialRemainder gf128Reduce
  rw [simdRemainderSteps_eq_gf128ReduceAux]

/-- Two-fold `0x87` carry-less reduction (`gf2_128_reduce_x128_7_2_1_0`) in `SimdBinaryEquiv`
    agrees with `McRefine.gf128Reduce` on all 256-bit carry-less products. -/
theorem simdFastRemainder_eq_gf128Reduce (p : BitVec 256) :
    SimdBinaryEquiv.fastRemainder p = gf128Reduce p := by
  unfold SimdBinaryEquiv.fastRemainder
  rw [SimdBinaryEquiv.gf2_128_reduce_exact, simdPolynomialRemainder_eq_gf128Reduce]

/-- Single-lane `PCLMULQDQ` four-selector product + two-fold `0x87` hardware reduction
    computes `gf128FieldMul` (and `rustGf128Mul`). -/
def pclmulqdqFourProduct256 (a b : BitVec 128) : BitVec 256 :=
  (SimdBinaryEquiv.pclmulqdq a b 0x00).setWidth 256 ^^^
    (((SimdBinaryEquiv.pclmulqdq a b 0x01).setWidth 256 ^^^
      (SimdBinaryEquiv.pclmulqdq a b 0x10).setWidth 256) <<< 64) ^^^
    ((SimdBinaryEquiv.pclmulqdq a b 0x11).setWidth 256 <<< 128)

theorem pclmulqdqFourProduct_reduce_eq_gf128FieldMul (a b : BitVec 128) :
    SimdBinaryEquiv.fastRemainder (pclmulqdqFourProduct256 a b) = gf128FieldMul a b := by
  unfold pclmulqdqFourProduct256 gf128FieldMul
  rw [← SimdBinaryEquiv.clmul128_eq_four_pclmulqdq, simdClmul128_eq_gf128PolyMul,
    simdFastRemainder_eq_gf128Reduce]

/-- AArch64 `PMULL` / `PMULL2` / `EXT #8` carry-less limb products assemble the exact same
    256-bit unreduced polynomial product as `pclmulqdqFourProduct256`. -/
def pmullFourProduct256 (a b : BitVec 128) : BitVec 256 :=
  let bSwap := SimdBinaryEquiv.ext b b ⟨8, by decide⟩
  (SimdBinaryEquiv.pmull a b).setWidth 256 ^^^
    (((SimdBinaryEquiv.pmull a bSwap).setWidth 256 ^^^
      (SimdBinaryEquiv.pmull2 a bSwap).setWidth 256) <<< 64) ^^^
    ((SimdBinaryEquiv.pmull2 a b).setWidth 256 <<< 128)

private theorem ext_self_8_lo (b : BitVec 128) :
    (SimdBinaryEquiv.ext b b ⟨8, by decide⟩).setWidth 64 = ((b >>> 64).setWidth 64) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [SimdBinaryEquiv.ext, BitVec.getLsbD_ushiftRight, hi, show i < 128 by omega,
    show 64 + i < 128 by omega, show 64 + i < 256 by omega]

private theorem ext_self_8_hi (b : BitVec 128) :
    ((SimdBinaryEquiv.ext b b ⟨8, by decide⟩) >>> 64).setWidth 64 = b.setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hFalse : b.getLsbD (64 + (64 + i)) = false := BitVec.getLsbD_of_ge b _ (by omega)
  simp [SimdBinaryEquiv.ext, BitVec.getLsbD_ushiftRight, hi, hFalse,
    show i < 128 by omega, show 64 + i < 128 by omega, show 64 + (64 + i) < 256 by omega,
    show ¬ (64 + (64 + i) < 128) by omega, show 64 + (64 + i) - 128 = i by omega]

theorem pmullFourProduct_reduce_eq_gf128FieldMul (a b : BitVec 128) :
    SimdBinaryEquiv.fastRemainder (pmullFourProduct256 a b) = gf128FieldMul a b := by
  have hEq : pmullFourProduct256 a b = pclmulqdqFourProduct256 a b := by
    unfold pmullFourProduct256 pclmulqdqFourProduct256
    dsimp only [SimdBinaryEquiv.pmull, SimdBinaryEquiv.pmull2, SimdBinaryEquiv.pclmulqdq]
    simp only [Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, BitVec.ushiftRight_zero,
      ext_self_8_lo, ext_self_8_hi]
    rw [BitVec.xor_comm
      ((SimdBinaryEquiv.clmul64 (a.setWidth 64) ((b >>> 64).setWidth 64)).setWidth 256)]
  rw [hEq, pclmulqdqFourProduct_reduce_eq_gf128FieldMul]

/-- End-to-end isomorphism bridge: `PCLMULQDQ` + two-fold `0x87` reduction implements
    Wiedemann `towerMul 7` under `polyToTower128` / `psiTower128ToPoly`. -/
theorem polyToTower128_pclmulqdq_reduce (a b : BitVec 128) :
    polyToTower128 (SimdBinaryEquiv.fastRemainder (pclmulqdqFourProduct256 a b)) =
      towerMul 7 (polyToTower128 a) (polyToTower128 b) := by
  rw [pclmulqdqFourProduct_reduce_eq_gf128FieldMul, polyToTower128_gf128FieldMul]

theorem psiTower128ToPoly_mul_eq_pclmulqdq_reduce (a b : Tower128) :
    psiTower128ToPoly (towerMul 7 a b) =
      SimdBinaryEquiv.fastRemainder
        (pclmulqdqFourProduct256 (psiTower128ToPoly a) (psiTower128ToPoly b)) := by
  rw [pclmulqdqFourProduct_reduce_eq_gf128FieldMul, psiTower128ToPoly_mul_fieldMul]

/-- Pack two 128-bit polynomial-basis elements into a 256-bit `YmmReg` for `VPCLMULQDQ`. -/
def packYmmLanes (lo hi : BitVec 128) : BitVec 256 :=
  lo.setWidth 256 ||| (hi.setWidth 256 <<< 128)

private theorem lane128_packYmmLanes_0 (lo hi : BitVec 128) :
    SimdBinaryEquiv.lane128 (packYmmLanes lo hi) 0 = lo := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hiLt
  simp [SimdBinaryEquiv.lane128, packYmmLanes, hiLt]

private theorem lane128_packYmmLanes_1 (lo hi : BitVec 128) :
    SimdBinaryEquiv.lane128 (packYmmLanes lo hi) 1 = hi := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hiLt
  simp [SimdBinaryEquiv.lane128, packYmmLanes, BitVec.getLsbD_ushiftRight,
    hiLt, show 128 + i < 256 by omega]

private theorem evalVec_carryless_eq_packYmmLanes (va vb : BitVec 256) (imm : Nat) :
    SimdBinaryEquiv.evalVec .carryless va vb imm =
      packYmmLanes
        (SimdBinaryEquiv.pclmulqdq (SimdBinaryEquiv.lane128 va 0) (SimdBinaryEquiv.lane128 vb 0) imm)
        (SimdBinaryEquiv.pclmulqdq (SimdBinaryEquiv.lane128 va 1) (SimdBinaryEquiv.lane128 vb 1) imm) :=
  rfl

/-- Two-lane `VPCLMULQDQ` (`SimdBinaryEquiv.evalVec .carryless`) unreduced 2-pair dot-product
    step: executes four 256-bit `VPCLMULQDQ` instructions across both 128-bit lanes and folds
    lane 0 with lane 1 (`VEXTRACTI128` + `VPXOR`) prior to single-pass `0x87` reduction. -/
def vpclmul2LaneDotUnreduced (va vb : BitVec 256) : BitVec 256 :=
  let q00 := SimdBinaryEquiv.evalVec .carryless va vb 0x00
  let q01 := SimdBinaryEquiv.evalVec .carryless va vb 0x01
  let q10 := SimdBinaryEquiv.evalVec .carryless va vb 0x10
  let q11 := SimdBinaryEquiv.evalVec .carryless va vb 0x11
  let lo := SimdBinaryEquiv.lane128 q00 0 ^^^ SimdBinaryEquiv.lane128 q00 1
  let mid := (SimdBinaryEquiv.lane128 q01 0 ^^^ SimdBinaryEquiv.lane128 q01 1) ^^^
             (SimdBinaryEquiv.lane128 q10 0 ^^^ SimdBinaryEquiv.lane128 q10 1)
  let hi := SimdBinaryEquiv.lane128 q11 0 ^^^ SimdBinaryEquiv.lane128 q11 1
  lo.setWidth 256 ^^^ (mid.setWidth 256 <<< 64) ^^^ (hi.setWidth 256 <<< 128)

private theorem xor_rearrange_lanes (p0 p1 q0 q1 r0 r1 s0 s1 : BitVec 256) :
    (p0 ^^^ p1) ^^^ (((q0 ^^^ q1) ^^^ (r0 ^^^ r1)) ^^^ (s0 ^^^ s1)) =
      (p0 ^^^ (q0 ^^^ r0) ^^^ s0) ^^^ (p1 ^^^ (q1 ^^^ r1) ^^^ s1) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor]
  cases p0.getLsbD i <;> cases p1.getLsbD i <;> cases q0.getLsbD i <;> cases q1.getLsbD i <;>
    cases r0.getLsbD i <;> cases r1.getLsbD i <;> cases s0.getLsbD i <;> cases s1.getLsbD i <;> rfl

private theorem vpclmul2LaneDotUnreduced_eq_xor_fourProduct (x0 x1 y0 y1 : BitVec 128) :
    vpclmul2LaneDotUnreduced (packYmmLanes x0 x1) (packYmmLanes y0 y1) =
      pclmulqdqFourProduct256 x0 y0 ^^^ pclmulqdqFourProduct256 x1 y1 := by
  unfold vpclmul2LaneDotUnreduced pclmulqdqFourProduct256
  simp only [evalVec_carryless_eq_packYmmLanes, lane128_packYmmLanes_0, lane128_packYmmLanes_1,
    BitVec.setWidth_xor, BitVec.shiftLeft_xor_distrib, BitVec.xor_assoc]
  simpa only [BitVec.xor_assoc] using xor_rearrange_lanes
    ((SimdBinaryEquiv.pclmulqdq x0 y0 0x00).setWidth 256)
    ((SimdBinaryEquiv.pclmulqdq x1 y1 0x00).setWidth 256)
    ((SimdBinaryEquiv.pclmulqdq x0 y0 0x01).setWidth 256 <<< 64)
    ((SimdBinaryEquiv.pclmulqdq x1 y1 0x01).setWidth 256 <<< 64)
    ((SimdBinaryEquiv.pclmulqdq x0 y0 0x10).setWidth 256 <<< 64)
    ((SimdBinaryEquiv.pclmulqdq x1 y1 0x10).setWidth 256 <<< 64)
    ((SimdBinaryEquiv.pclmulqdq x0 y0 0x11).setWidth 256 <<< 128)
    ((SimdBinaryEquiv.pclmulqdq x1 y1 0x11).setWidth 256 <<< 128)

/-- Dual-lane `VPCLMULQDQ` carry-less inner product + deferred single `0x87` reduction
    maps under `polyToTower128` to `towerAdd 7 (towerMul 7 a0 b0) (towerMul 7 a1 b1)`. -/
theorem polyToTower128_vpclmul2LaneDot_reduce (a0 a1 b0 b1 : Tower128) :
    let va := packYmmLanes (psiTower128ToPoly a0) (psiTower128ToPoly a1)
    let vb := packYmmLanes (psiTower128ToPoly b0) (psiTower128ToPoly b1)
    polyToTower128 (SimdBinaryEquiv.fastRemainder (vpclmul2LaneDotUnreduced va vb)) =
      towerAdd 7 (towerMul 7 a0 b0) (towerMul 7 a1 b1) := by
  dsimp only
  rw [vpclmul2LaneDotUnreduced_eq_xor_fourProduct, SimdBinaryEquiv.fastRemainder_xor,
    polyToTower128_xor, polyToTower128_pclmulqdq_reduce, polyToTower128_pclmulqdq_reduce,
    polyToTower128_psiTower128ToPoly, polyToTower128_psiTower128ToPoly,
    polyToTower128_psiTower128ToPoly, polyToTower128_psiTower128ToPoly]

private theorem xorSum_zero_fn {w : Nat} :
    ∀ n : Nat, SimdBinaryEquiv.xorSum n (fun _ => 0#w) = 0#w
  | 0 => rfl
  | n + 1 => by simp [SimdBinaryEquiv.xorSum, xorSum_zero_fn n]

private theorem clmul64_zero_left (b : BitVec 64) :
    SimdBinaryEquiv.clmul64 0#64 b = 0#128 := by
  unfold SimdBinaryEquiv.clmul64
  have h : (fun i => if b.getLsbD i then (0#64).setWidth 128 <<< i else (0 : BitVec 128)) =
      (fun _ => 0#128) := by
    funext i; cases b.getLsbD i <;> simp
  rw [h]; exact xorSum_zero_fn 64

private theorem clmul64_zero_right (a : BitVec 64) :
    SimdBinaryEquiv.clmul64 a 0#64 = 0#128 := by
  unfold SimdBinaryEquiv.clmul64
  have h : (fun i => if (0#64).getLsbD i then a.setWidth 128 <<< i else (0 : BitVec 128)) =
      (fun _ => 0#128) := by
    funext i; simp
  rw [h]; exact xorSum_zero_fn 64

private theorem xorSum_tail_zero {w : Nat} (f : Nat → BitVec w) :
    ∀ (m : Nat), (∀ i, 1 ≤ i → f i = 0#w) →
      SimdBinaryEquiv.xorSum (1 + m) f = f 0
  | 0, _ => by simp [SimdBinaryEquiv.xorSum]
  | m + 1, hZero => by
    rw [Nat.add_succ, SimdBinaryEquiv.xorSum, hZero (1 + m) (by omega),
      BitVec.xor_zero, xorSum_tail_zero f m hZero]

private theorem simd_clmul64_one_one : SimdBinaryEquiv.clmul64 1#64 1#64 = 1#128 := by
  unfold SimdBinaryEquiv.clmul64
  rw [show (64 : Nat) = 1 + 63 from rfl, xorSum_tail_zero]
  · decide
  · intro i hi
    have hBit : (1#64).getLsbD i = false := by
      simp [BitVec.getLsbD, show (1 : Nat).testBit i = false by
        cases i with
        | zero => omega
        | succ k => simp [Nat.testBit_succ]]
    simp [hBit]

/-- `#tooth` Replacing `PCLMULQDQ` high-limb selector `0x11` with `0x00` corrupts `z^64 · z^64 = z^128`. -/
theorem tooth_pclmulqdq_wrong_high_selector :
    ∃ a b : BitVec 128,
      SimdBinaryEquiv.fastRemainder
        ((SimdBinaryEquiv.pclmulqdq a b 0x00).setWidth 256 ^^^
          (((SimdBinaryEquiv.pclmulqdq a b 0x01).setWidth 256 ^^^
            (SimdBinaryEquiv.pclmulqdq a b 0x10).setWidth 256) <<< 64) ^^^
          ((SimdBinaryEquiv.pclmulqdq a b 0x00).setWidth 256 <<< 128)) ≠
        gf128FieldMul a b := by
  refine ⟨1#128 <<< 64, 1#128 <<< 64, ?_⟩
  have hLo : ((1#128 <<< 64) >>> 0).setWidth 64 = 0#64 := by decide
  have hHi : ((1#128 <<< 64) >>> 64).setWidth 64 = 1#64 := by decide
  have hP00 : SimdBinaryEquiv.pclmulqdq (1#128 <<< 64) (1#128 <<< 64) 0x00 = 0#128 := by
    dsimp only [SimdBinaryEquiv.pclmulqdq]
    simp only [Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, hLo, clmul64_zero_left]
  have hP01 : SimdBinaryEquiv.pclmulqdq (1#128 <<< 64) (1#128 <<< 64) 0x01 = 0#128 := by
    dsimp only [SimdBinaryEquiv.pclmulqdq]
    simp only [Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, hLo, hHi, clmul64_zero_right]
  have hP10 : SimdBinaryEquiv.pclmulqdq (1#128 <<< 64) (1#128 <<< 64) 0x10 = 0#128 := by
    dsimp only [SimdBinaryEquiv.pclmulqdq]
    simp only [Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, hLo, hHi, clmul64_zero_left]
  have hP11 : SimdBinaryEquiv.pclmulqdq (1#128 <<< 64) (1#128 <<< 64) 0x11 = 1#128 := by
    dsimp only [SimdBinaryEquiv.pclmulqdq]
    simp only [Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, hHi, simd_clmul64_one_one]
  rw [← pclmulqdqFourProduct_reduce_eq_gf128FieldMul]
  unfold pclmulqdqFourProduct256
  rw [hP00, hP01, hP10, hP11, simdFastRemainder_eq_gf128Reduce, simdFastRemainder_eq_gf128Reduce]
  have hZero256 : ((0#128).setWidth 256 ^^^ ((((0#128).setWidth 256 ^^^ (0#128).setWidth 256) <<< 64)) ^^^
      ((0#128).setWidth 256 <<< 128)) = 0#256 := by decide
  have hRhs256 : ((0#128).setWidth 256 ^^^ ((((0#128).setWidth 256 ^^^ (0#128).setWidth 256) <<< 64)) ^^^
      ((1#128).setWidth 256 <<< 128)) = (1#256 <<< 127) <<< 1 := by decide
  rw [hZero256, hRhs256, gf128Reduce_zero, gf128Reduce_shiftLeft_one _ (by decide),
    show (1#256 <<< 127) = (1#128 <<< 127).setWidth 256 by decide, gf128Reduce_setWidth]
  decide

theorem gf128Reduce_shiftLeft_one_inhabited :
    ∃ p : BitVec 256, p.getLsbD 255 = false ∧ gf128Reduce (p <<< 1) = 0x87#128 :=
  ⟨1#256 <<< 127, by decide, by
    rw [gf128Reduce_shiftLeft_one _ (by decide)]
    have hSet : (1#256 <<< 127) = (1#128 <<< 127).setWidth 256 := by decide
    rw [hSet, gf128Reduce_setWidth]
    decide⟩

#tooth_pair pclmulqdqFourProduct_reduce_eq_gf128FieldMul vs tooth_pclmulqdq_wrong_high_selector
#verify_inhabited gf128Reduce_shiftLeft_one gf128Reduce_shiftLeft_one_inhabited

end Qsag
end

#verify_constructive
  Qsag.gf128Reduce_shiftLeft_one
  Qsag.gf128FieldMul_eq_rustGf128Mul
  Qsag.polyToTower128_gf128FieldMul
  Qsag.psiTower128ToPoly_mul_fieldMul
  Qsag.pclmulqdqFourProduct_reduce_eq_gf128FieldMul
  Qsag.pmullFourProduct_reduce_eq_gf128FieldMul
  Qsag.polyToTower128_pclmulqdq_reduce
  Qsag.polyToTower128_vpclmul2LaneDot_reduce
