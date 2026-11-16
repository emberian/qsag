module
/-
# Qsag.Gf128ClmulLoopAgreement — Symbolic Field-Loop Agreement and SIMD Carry-Less Multiply Bridge

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

public import Qsag.Math.Gf2Pow128
public import Qsag.Math.GoldilocksBase
public import Qsag.Machine.McRefine
public import Qsag.Machine.ClmulSimd

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
  simp only [gf128ReduceStep.public_eq_1]
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
  | 0, _, q => by
    rw [gf128ReduceAux.public_eq_2, gf128ReduceAux.public_eq_1, gf128ReduceAux.public_eq_1]
  | m + 1, hm, q => by
    rw [gf128ReduceAux.public_eq_2, gf128ReduceAux.public_eq_2 q m,
      gf128ReduceStep_shiftLeft_one m (by omega) q,
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
  rw [gf128ReduceStep.public_eq_1, rustGf128MulX.public_eq_1]
  have hBit1 : (u <<< 1).getLsbD (128 + 0) = u.getLsbD 127 := by simp
  have hBit2 : (u.setWidth 128).getLsbD 127 = u.getLsbD 127 := by simp
  have hMod : gf128Modulus.setWidth 128 = 0x87#128 := by
    rw [gf128Modulus.public_eq_1]; decide
  rw [hBit1, hBit2, BitVec.shiftLeft_zero]
  cases u.getLsbD 127
  · simp only [Bool.false_eq_true, ↓reduceIte, BitVec.xor_zero, setWidth128_shiftLeft_one]
  · simp only [↓reduceIte, BitVec.setWidth_xor, setWidth128_shiftLeft_one, hMod]

/-- The double-width polynomial has degree below 255 (coefficient 255 is clear). -/
abbrev gf128DegreeBelow255 (p : BitVec 256) : Prop := p.getLsbD 255 = false

/-- **Long division commutes with multiplication by `x`**, for every double-width polynomial
    of degree below 255. Proved structurally without monomial table enumeration. -/
theorem gf128Reduce_shiftLeft_one (p : BitVec 256) (hTop : gf128DegreeBelow255 p) :
    gf128Reduce (p <<< 1) = rustGf128MulX (gf128Reduce p) := by
  have hTop : p.getLsbD 255 = false := hTop
  have hStep127 : gf128ReduceStep 127 p = p := by
    rw [gf128ReduceStep.public_eq_1, show 128 + 127 = 255 from rfl, hTop]
    rfl
  have hAux128 : gf128ReduceAux 128 p = gf128ReduceAux 127 p := by
    rw [gf128ReduceAux.public_eq_2, hStep127]
  simp only [gf128Reduce.public_eq_1]
  rw [gf128ReduceAux_shiftLeft_one 127 (Nat.le_refl 127) p, ← hAux128,
    gf128ReduceStep_zero_shiftLeft_setWidth]

private theorem gf128ReduceAux_of_high_clear :
    ∀ (n : Nat) (p : BitVec 256),
      (∀ k, k < n → p.getLsbD (128 + k) = false) → gf128ReduceAux n p = p
  | 0, p, _ => gf128ReduceAux.public_eq_1 p
  | n + 1, p, hClear => by
    have hn : p.getLsbD (128 + n) = false := hClear n (Nat.lt_succ_self n)
    rw [gf128ReduceAux.public_eq_2, gf128ReduceStep.public_eq_1, hn]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact gf128ReduceAux_of_high_clear n p (fun k hk => hClear k (by omega))

/-- Long division fixes polynomials of degree below 128. -/
theorem gf128Reduce_setWidth (a : BitVec 128) : gf128Reduce (a.setWidth 256) = a := by
  rw [gf128Reduce.public_eq_1, gf128ReduceAux_of_high_clear 128 (a.setWidth 256)]
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
    rw [show (a.setWidth 256) <<< 0 = a.setWidth 256 from BitVec.shiftLeft_zero _,
      rustGf128MulXIter.public_eq_1]
    exact gf128Reduce_setWidth a
  | n + 1, hn => by
    rw [BitVec.shiftLeft_add,
      gf128Reduce_shiftLeft_one _ (setWidth_shift_top_clear a n (by omega)),
      gf128Reduce_shiftLeft_setWidth a n (by omega), rustGf128MulXIter_add n 1 a,
      rustGf128MulXIter.public_eq_2, rustGf128MulXIter.public_eq_1]

private theorem gf128Reduce_polyMulAux (a b : BitVec 128) : ∀ n : Nat, n ≤ 128 →
    gf128Reduce (gf128PolyMulAux (a.setWidth 256) b n) = rustPolyAct n b.getLsbD a
  | 0, _ => by
    rw [gf128PolyMulAux.public_eq_1, rustPolyAct.public_eq_1]
    exact gf128Reduce_zero
  | n + 1, hn => by
    have hTerm : gf128Reduce (if b.getLsbD n then (a.setWidth 256) <<< n else 0) =
        (if b.getLsbD n then rustGf128MulXIter n a else 0#128) := by
      cases b.getLsbD n
      · exact gf128Reduce_zero
      · exact gf128Reduce_shiftLeft_setWidth a n (by omega)
    rw [gf128PolyMulAux.public_eq_2, gf128Reduce_xor, gf128Reduce_polyMulAux a b n (by omega),
      hTerm, rustPolyAct_split n 1, rustPolyAct.public_eq_2, rustPolyAct.public_eq_1,
      Nat.zero_add, BitVec.xor_zero]

/-- **Carry-less multiply then reduce = shift-and-reduce loop**, for all inputs. -/
theorem gf128FieldMul_eq_rustGf128Mul (a b : BitVec 128) :
    gf128FieldMul a b = rustGf128Mul a b := by
  rw [rustGf128Mul_eq_act, gf128FieldMul.public_eq_1, gf128PolyMul.public_eq_1]
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
  | 0 => by rw [SimdBinaryEquiv.xorSum.public_eq_1, gf128PolyMulAux.public_eq_1]
  | n + 1 => by
    rw [SimdBinaryEquiv.xorSum.public_eq_2, gf128PolyMulAux.public_eq_2,
      simdXorSum_eq_gf128PolyMulAux a b n]

/-- `SimdBinaryEquiv.clmul128` is definitionally aligned with `McRefine.gf128PolyMul`. -/
theorem simdClmul128_eq_gf128PolyMul (a b : BitVec 128) :
    SimdBinaryEquiv.clmul128 a b = gf128PolyMul (a.setWidth 256) b := by
  rw [SimdBinaryEquiv.clmul128.public_eq_1, gf128PolyMul.public_eq_1]
  exact simdXorSum_eq_gf128PolyMulAux a b 128

private theorem simdRemainderSteps_eq_gf128ReduceAux :
    ∀ (n : Nat) (p : BitVec 256),
      SimdBinaryEquiv.polynomialRemainderSteps n p = gf128ReduceAux n p
  | 0, p => by
    rw [SimdBinaryEquiv.polynomialRemainderSteps.public_eq_1, gf128ReduceAux.public_eq_1]
  | n + 1, p => by
    rw [SimdBinaryEquiv.polynomialRemainderSteps.public_eq_2, gf128ReduceAux.public_eq_2,
      gf128ReduceStep.public_eq_1, gf128Modulus.public_eq_1]
    exact simdRemainderSteps_eq_gf128ReduceAux n _

/-- `SimdBinaryEquiv.polynomialRemainder` equals `McRefine.gf128Reduce`. -/
theorem simdPolynomialRemainder_eq_gf128Reduce (p : BitVec 256) :
    SimdBinaryEquiv.polynomialRemainder p = gf128Reduce p := by
  rw [SimdBinaryEquiv.polynomialRemainder.public_eq_1, gf128Reduce.public_eq_1,
    simdRemainderSteps_eq_gf128ReduceAux]

/-- Two-fold `0x87` carry-less reduction (`gf2_128_reduce_x128_7_2_1_0`) in `SimdBinaryEquiv`
    agrees with `McRefine.gf128Reduce` on all 256-bit carry-less products. -/
theorem simdFastRemainder_eq_gf128Reduce (p : BitVec 256) :
    SimdBinaryEquiv.fastRemainder p = gf128Reduce p := by
  rw [SimdBinaryEquiv.fastRemainder.public_eq_1, SimdBinaryEquiv.gf2_128_reduce_exact, simdPolynomialRemainder_eq_gf128Reduce]

/-- Single-lane `PCLMULQDQ` four-selector product + two-fold `0x87` hardware reduction
    computes `gf128FieldMul` (and `rustGf128Mul`). -/
def pclmulqdqFourProduct256 (a b : BitVec 128) : BitVec 256 :=
  (SimdBinaryEquiv.pclmulqdq a b 0x00).setWidth 256 ^^^
    (((SimdBinaryEquiv.pclmulqdq a b 0x01).setWidth 256 ^^^
      (SimdBinaryEquiv.pclmulqdq a b 0x10).setWidth 256) <<< 64) ^^^
    ((SimdBinaryEquiv.pclmulqdq a b 0x11).setWidth 256 <<< 128)

theorem pclmulqdqFourProduct_reduce_eq_gf128FieldMul (a b : BitVec 128) :
    SimdBinaryEquiv.fastRemainder (pclmulqdqFourProduct256 a b) = gf128FieldMul a b := by
  unfold pclmulqdqFourProduct256
  rw [gf128FieldMul.public_eq_1, ← SimdBinaryEquiv.clmul128_eq_four_pclmulqdq, simdClmul128_eq_gf128PolyMul,
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
  rw [SimdBinaryEquiv.ext.public_eq_1, show 8 * (⟨8, by decide⟩ : Fin 16).val = 64 from rfl]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_ushiftRight, hi, show i < 128 by omega,
    show 64 + i < 128 by omega, show 64 + i < 256 by omega]

private theorem ext_self_8_hi (b : BitVec 128) :
    ((SimdBinaryEquiv.ext b b ⟨8, by decide⟩) >>> 64).setWidth 64 = b.setWidth 64 := by
  rw [SimdBinaryEquiv.ext.public_eq_1, show 8 * (⟨8, by decide⟩ : Fin 16).val = 64 from rfl]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hFalse : b.getLsbD (64 + (64 + i)) = false := BitVec.getLsbD_of_ge b _ (by omega)
  simp [BitVec.getLsbD_ushiftRight, hi, hFalse,
    show i < 128 by omega, show 64 + i < 128 by omega, show 64 + (64 + i) < 256 by omega,
    show ¬ (64 + (64 + i) < 128) by omega, show 64 + (64 + i) - 128 = i by omega]

theorem pmullFourProduct_reduce_eq_gf128FieldMul (a b : BitVec 128) :
    SimdBinaryEquiv.fastRemainder (pmullFourProduct256 a b) = gf128FieldMul a b := by
  have hEq : pmullFourProduct256 a b = pclmulqdqFourProduct256 a b := by
    unfold pmullFourProduct256 pclmulqdqFourProduct256
    simp only [SimdBinaryEquiv.pmull.public_eq_1, SimdBinaryEquiv.pmull2.public_eq_1,
      SimdBinaryEquiv.pclmulqdq.public_eq_1, Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, BitVec.ushiftRight_zero,
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
  simp [SimdBinaryEquiv.lane128.public_eq_1, packYmmLanes, hiLt]

private theorem lane128_packYmmLanes_1 (lo hi : BitVec 128) :
    SimdBinaryEquiv.lane128 (packYmmLanes lo hi) 1 = hi := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hiLt
  simp [SimdBinaryEquiv.lane128.public_eq_1, packYmmLanes, BitVec.getLsbD_ushiftRight,
    hiLt, show 128 + i < 256 by omega]

private theorem evalVec_carryless_eq_packYmmLanes (va vb : BitVec 256) (imm : Nat) :
    SimdBinaryEquiv.evalVec .carryless va vb imm =
      packYmmLanes
        (SimdBinaryEquiv.pclmulqdq (SimdBinaryEquiv.lane128 va 0) (SimdBinaryEquiv.lane128 vb 0) imm)
        (SimdBinaryEquiv.pclmulqdq (SimdBinaryEquiv.lane128 va 1) (SimdBinaryEquiv.lane128 vb 1) imm) := by
  rw [SimdBinaryEquiv.evalVec.public_eq_9]
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
  | 0 => SimdBinaryEquiv.xorSum.public_eq_1 _
  | n + 1 => by rw [SimdBinaryEquiv.xorSum.public_eq_2, xorSum_zero_fn n, BitVec.xor_zero]

private theorem clmul64_zero_left (b : BitVec 64) :
    SimdBinaryEquiv.clmul64 0#64 b = 0#128 := by
  rw [SimdBinaryEquiv.clmul64.public_eq_1]
  have h : (fun i => if b.getLsbD i then (0#64).setWidth 128 <<< i else (0 : BitVec 128)) =
      (fun _ => 0#128) := by
    funext i; cases b.getLsbD i <;> simp
  rw [h]; exact xorSum_zero_fn 64

private theorem clmul64_zero_right (a : BitVec 64) :
    SimdBinaryEquiv.clmul64 a 0#64 = 0#128 := by
  rw [SimdBinaryEquiv.clmul64.public_eq_1]
  have h : (fun i => if (0#64).getLsbD i then a.setWidth 128 <<< i else (0 : BitVec 128)) =
      (fun _ => 0#128) := by
    funext i; simp
  rw [h]; exact xorSum_zero_fn 64

private theorem xorSum_tail_zero {w : Nat} (f : Nat → BitVec w) :
    ∀ (m : Nat), (∀ i, 1 ≤ i → f i = 0#w) →
      SimdBinaryEquiv.xorSum (1 + m) f = f 0
  | 0, _ => by
    rw [show 1 + 0 = Nat.succ 0 from rfl, SimdBinaryEquiv.xorSum.public_eq_2,
      SimdBinaryEquiv.xorSum.public_eq_1]
    exact BitVec.zero_xor
  | m + 1, hZero => by
    rw [Nat.add_succ, SimdBinaryEquiv.xorSum.public_eq_2, hZero (1 + m) (by omega),
      BitVec.xor_zero, xorSum_tail_zero f m hZero]

private theorem simd_clmul64_one_one : SimdBinaryEquiv.clmul64 1#64 1#64 = 1#128 := by
  rw [SimdBinaryEquiv.clmul64.public_eq_1]
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
    rw [SimdBinaryEquiv.pclmulqdq.public_eq_1]
    simp only [Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, hLo, clmul64_zero_left]
  have hP01 : SimdBinaryEquiv.pclmulqdq (1#128 <<< 64) (1#128 <<< 64) 0x01 = 0#128 := by
    rw [SimdBinaryEquiv.pclmulqdq.public_eq_1]
    simp only [Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, hLo, hHi, clmul64_zero_right]
  have hP10 : SimdBinaryEquiv.pclmulqdq (1#128 <<< 64) (1#128 <<< 64) 0x10 = 0#128 := by
    rw [SimdBinaryEquiv.pclmulqdq.public_eq_1]
    simp only [Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, hLo, hHi, clmul64_zero_left]
  have hP11 : SimdBinaryEquiv.pclmulqdq (1#128 <<< 64) (1#128 <<< 64) 0x11 = 1#128 := by
    rw [SimdBinaryEquiv.pclmulqdq.public_eq_1]
    simp only [Nat.reduceMod, Nat.reduceDiv, Nat.reduceMul, hHi, simd_clmul64_one_one]
  rw [← pclmulqdqFourProduct_reduce_eq_gf128FieldMul]
  unfold pclmulqdqFourProduct256
  rw [hP00, hP01, hP10, hP11, simdFastRemainder_eq_gf128Reduce, simdFastRemainder_eq_gf128Reduce]
  have hZero256 : ((0#128).setWidth 256 ^^^ ((((0#128).setWidth 256 ^^^ (0#128).setWidth 256) <<< 64)) ^^^
      ((0#128).setWidth 256 <<< 128)) = 0#256 := by decide
  have hRhs256 : ((0#128).setWidth 256 ^^^ ((((0#128).setWidth 256 ^^^ (0#128).setWidth 256) <<< 64)) ^^^
      ((1#128).setWidth 256 <<< 128)) = (1#256 <<< 127) <<< 1 := by decide
  rw [hZero256, hRhs256, gf128Reduce_zero, gf128Reduce_shiftLeft_one _ (by decide),
    show (1#256 <<< 127) = (1#128 <<< 127).setWidth 256 by decide, gf128Reduce_setWidth,
    rustGf128MulX.public_eq_1]
  decide

theorem gf128Reduce_shiftLeft_one_inhabited :
    ∃ p : BitVec 256, gf128DegreeBelow255 p ∧ gf128Reduce (p <<< 1) = 0x87#128 :=
  ⟨1#256 <<< 127, by decide, by
    rw [gf128Reduce_shiftLeft_one _ (by decide)]
    have hSet : (1#256 <<< 127) = (1#128 <<< 127).setWidth 256 := by decide
    rw [hSet, gf128Reduce_setWidth, rustGf128MulX.public_eq_1]
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

public section
namespace Qsag.Math
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
  rw [Gf2Pow128.mul_bits]
  have h := (Qsag.gf128FieldMul_eq_gf2_128_mul_bv a b).symm
  refine ⟨?_, h.trans (Qsag.gf128FieldMul_eq_rustGf128Mul a b), rfl,
    h.trans (Qsag.pclmulqdqFourProduct_reduce_eq_gf128FieldMul a b).symm,
    h.trans (Qsag.pmullFourProduct_reduce_eq_gf128FieldMul a b).symm⟩
  rw [h, ← Qsag.polyToTower128_gf128FieldMul a b, Qsag.psiTower128ToPoly_polyToTower128]

end Qsag.Math

/-! ## Machine ≃ `Qsag.Math` bridges (L-Ex-12)

The Goldilocks theorems take the execution of the decoded production kernel (`runX86` / `runArm64`
on the slice extracted from the shipped archive, as proved in `McRefine`) and conclude with the
`Qsag.Math` field operation on the residue classes of the input registers. The `GF(2^128)` theorems
relate the carry-less limb products and word reduction evaluated by the `PCLMULQDQ` / `PMULL` step
semantics (`clmul64`, `gf128WordReduce`) to `Qsag.Math.Gf2Pow128.mul` and `towerMul 7`. -/

namespace Qsag

set_option autoImplicit false

private theorem mod_add_sub_mod (a c p : Nat) (hc : c ≤ p) :
    (a % p + p - c) % p = (a + p - c) % p := by
  rw [Nat.add_sub_assoc hc, Nat.add_sub_assoc hc, Nat.add_mod (a % p), Nat.mod_mod, ← Nat.add_mod]

/-- **x86-64 `goldilocks_add_ct` computes `Goldilocks.add`.** After the decoded production kernel
    halts, `rax` holds the canonical representative of the field sum of the classes of `rdi` and
    `rsi`, for arbitrary (also non-canonical) 64-bit inputs. -/
theorem current_goldilocks_add_ct_x86_64_refines_math :
    ∃ slice prog, findSliceByNameBytes currentX86ExtractedSlices goldAddX86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 25 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        ((runX86 prog fuel s).1.gpr.get 0).toNat =
          (Goldilocks.add (Goldilocks.ofNat (s.gpr.get 7).toNat)
            (Goldilocks.ofNat (s.gpr.get 6).toNat)).val := by
  obtain ⟨slice, prog, hf, hd, h⟩ := current_goldilocks_add_ct_x86_64_mc_refines
  refine ⟨slice, prog, hf, hd, fun s fuel hpc hh hfuel => ?_⟩
  obtain ⟨hHalt, hVal, _⟩ := h s fuel hpc hh hfuel
  refine ⟨hHalt, ?_⟩
  rw [hVal, Goldilocks.add_val, Goldilocks.ofNat_val, Goldilocks.ofNat_val, ← Nat.add_mod]

/-- **x86-64 `goldilocks_sub_ct` computes `Goldilocks.sub`.** -/
theorem current_goldilocks_sub_ct_x86_64_refines_math :
    ∃ slice prog, findSliceByNameBytes currentX86ExtractedSlices goldSubX86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 31 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        ((runX86 prog fuel s).1.gpr.get 0).toNat =
          (Goldilocks.sub (Goldilocks.ofNat (s.gpr.get 7).toNat)
            (Goldilocks.ofNat (s.gpr.get 6).toNat)).val := by
  obtain ⟨slice, prog, hf, hd, h⟩ := current_goldilocks_sub_ct_x86_64_mc_refines
  refine ⟨slice, prog, hf, hd, fun s fuel hpc hh hfuel => ?_⟩
  obtain ⟨hHalt, hVal, _⟩ := h s fuel hpc hh hfuel
  refine ⟨hHalt, ?_⟩
  rw [hVal, Goldilocks.sub_val, Goldilocks.ofNat_val, Goldilocks.ofNat_val,
    mod_add_sub_mod _ _ _ (Nat.le_of_lt (Nat.mod_lt _ (by decide)))]

/-- **x86-64 `goldilocks_mul_ct` computes `Goldilocks.mul`.** -/
theorem current_goldilocks_mul_ct_x86_64_refines_math :
    ∃ slice prog, findSliceByNameBytes currentX86ExtractedSlices goldMulX86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 33 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        ((runX86 prog fuel s).1.gpr.get 0).toNat =
          (Goldilocks.mul (Goldilocks.ofNat (s.gpr.get 7).toNat)
            (Goldilocks.ofNat (s.gpr.get 6).toNat)).val := by
  obtain ⟨slice, prog, hf, hd, h⟩ := current_goldilocks_mul_ct_x86_64_mc_refines
  refine ⟨slice, prog, hf, hd, fun s fuel hpc hh hfuel => ?_⟩
  obtain ⟨hHalt, hVal, _⟩ := h s fuel hpc hh hfuel
  refine ⟨hHalt, ?_⟩
  rw [hVal, Goldilocks.mul_val, Goldilocks.ofNat_val, Goldilocks.ofNat_val, ← Nat.mul_mod]

/-- **AArch64 `goldilocks_mul_ct` computes `Goldilocks.mul`.** -/
theorem current_goldilocks_mul_ct_aarch64_refines_math :
    ∃ slice prog, findSliceByNameBytes currentAarch64ExtractedSlices goldMulArmName = some slice ∧
      decodeArm64Stream slice.code = some prog ∧
      ∀ (s : Arm64State) (fuel : Nat), s.pc = 0 → s.halted = false → 30 ≤ fuel →
        (runArm64 prog fuel s).1.halted = true ∧
        ((runArm64 prog fuel s).1.gpr.get 0).toNat =
          (Goldilocks.mul (Goldilocks.ofNat (s.gpr.get 0).toNat)
            (Goldilocks.ofNat (s.gpr.get 1).toNat)).val := by
  obtain ⟨slice, prog, hf, hd, h⟩ := current_goldilocks_mul_ct_aarch64_mc_refines
  refine ⟨slice, prog, hf, hd, fun s fuel hpc hh hfuel => ?_⟩
  obtain ⟨hHalt, hVal, _⟩ := h s fuel hpc hh hfuel
  refine ⟨hHalt, ?_⟩
  rw [hVal, Goldilocks.mul_val, Goldilocks.ofNat_val, Goldilocks.ofNat_val, ← Nat.mul_mod]

/-- **Four-product `PCLMULQDQ` datapath computes `Gf2Pow128.mul` / `towerMul 7`.** The four
    machine carry-less limb products (`clmul64`, the function the x86-64 and AArch64 step
    semantics evaluate), recombined at the word boundary and reduced by the two-fold `0x87` word
    reduction, are the canonical polynomial-basis product of the operand blocks, and the tower
    product under the basis isomorphism. -/
theorem gf128_clmul_four_words_reduce_eq_math (a0 a1 b0 b1 : UInt64) :
    let p00 := clmul64 a0 b0
    let p01 := clmul64 a0 b1
    let p10 := clmul64 a1 b0
    let p11 := clmul64 a1 b1
    let out := gf128WordReduce p00.w0 (p00.w1 ^^^ p01.w0 ^^^ p10.w0)
      (p11.w0 ^^^ p01.w1 ^^^ p10.w1) p11.w1
    out = (Qsag.Math.Gf2Pow128.mul ⟨gf128Words a0 a1⟩ ⟨gf128Words b0 b1⟩).bits ∧
    out = psiTower128ToPoly (towerMul 7 (polyToTower128 (gf128Words a0 a1))
      (polyToTower128 (gf128Words b0 b1))) := by
  have h := gf128_clmul_four_words a0 a1 b0 b1
  dsimp only at h ⊢
  rw [gf128WordReduce_eq_reduce, h, ← gf128FieldMul_eq, Qsag.Math.Gf2Pow128.mul_bits,
    psiTower128ToPoly_mul_fieldMul, psiTower128ToPoly_polyToTower128,
    psiTower128ToPoly_polyToTower128]
  exact ⟨gf128FieldMul_eq_gf2_128_mul_bv _ _, rfl⟩

/-- **Three-product Karatsuba datapath computes `Gf2Pow128.mul` / `towerMul 7`.** -/
theorem gf128_clmul_karatsuba_words_reduce_eq_math (a0 a1 b0 b1 : UInt64) :
    let p00 := clmul64 a0 b0
    let p11 := clmul64 a1 b1
    let pm := clmul64 (a0 ^^^ a1) (b0 ^^^ b1)
    let m0 := pm.w0 ^^^ p00.w0 ^^^ p11.w0
    let m1 := pm.w1 ^^^ p00.w1 ^^^ p11.w1
    let out := gf128WordReduce p00.w0 (p00.w1 ^^^ m0) (p11.w0 ^^^ m1) p11.w1
    out = (Qsag.Math.Gf2Pow128.mul ⟨gf128Words a0 a1⟩ ⟨gf128Words b0 b1⟩).bits ∧
    out = psiTower128ToPoly (towerMul 7 (polyToTower128 (gf128Words a0 a1))
      (polyToTower128 (gf128Words b0 b1))) := by
  have h := gf128_clmul_karatsuba_words a0 a1 b0 b1
  dsimp only at h ⊢
  rw [gf128WordReduce_eq_reduce, h, ← gf128FieldMul_eq, Qsag.Math.Gf2Pow128.mul_bits,
    psiTower128ToPoly_mul_fieldMul, psiTower128ToPoly_polyToTower128,
    psiTower128ToPoly_polyToTower128]
  exact ⟨gf128FieldMul_eq_gf2_128_mul_bv _ _, rfl⟩

/-- **Accumulation step of the `gf2_128_mul_acc` kernels in the tower.** XOR-accumulating one
    kernel product is `towerAdd 7` of `towerMul 7` under `polyToTower128`; induction on the block
    count turns the kernels' field dot product into the tower dot product. -/
theorem polyToTower128_gf128FieldMul_xor (a b acc : BitVec 128) :
    polyToTower128 (gf128FieldMul a b ^^^ acc) =
      towerAdd 7 (towerMul 7 (polyToTower128 a) (polyToTower128 b)) (polyToTower128 acc) := by
  rw [polyToTower128_xor, polyToTower128_gf128FieldMul]

end Qsag

#verify_constructive
  Qsag.current_goldilocks_add_ct_x86_64_refines_math
  Qsag.current_goldilocks_sub_ct_x86_64_refines_math
  Qsag.current_goldilocks_mul_ct_x86_64_refines_math
  Qsag.current_goldilocks_mul_ct_aarch64_refines_math
  Qsag.gf128_clmul_four_words_reduce_eq_math
  Qsag.gf128_clmul_karatsuba_words_reduce_eq_math
  Qsag.polyToTower128_gf128FieldMul_xor
