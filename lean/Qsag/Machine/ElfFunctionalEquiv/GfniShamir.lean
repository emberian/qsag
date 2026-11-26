module

public import Qsag.Machine.ElfFunctionalEquiv.SimdAndScalarKernels
import Qsag.Tactic.Prelude
import Qsag.Tactic.AssuranceKit

public section

namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
  UInt64.instLawfulOrderOrd String.instLawfulEqOrd
  Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe
set_option autoImplicit false
set_option maxRecDepth 65536

attribute [local simp]
  X86BvState.ofX86State Arm64BvState.ofArm64State bank16OfU64 bank32OfU64
  b16get_0 b16get_1 b16get_2 b16get_3 b16get_4 b16get_5 b16get_6 b16get_7
  b16get_8 b16get_9 b16get_10 b16get_11 b16get_12 b16get_13 b16get_14 b16get_15
  b32get_0 b32get_1 b32get_2


/-! Fresh GFNI Shamir MAC: arbitrary-count execution and byte refinement. -/

def gf256MacGfniProg : List (DecodedInstr X86Instr) := [
  ⟨0, 10, .movImm true 0 0x71500a8a86be78ce⟩,
  ⟨10, 5, .vmovGprToXmm true 14 0⟩,
  ⟨15, 5, .vpbroadcast true true 14 14⟩,
  ⟨20, 10, .movImm true 0 0xa1e4f8e072a2700c⟩,
  ⟨30, 5, .vmovGprToXmm true 15 0⟩,
  ⟨35, 5, .vpbroadcast true true 15 15⟩,
  ⟨40, 4, .vmovGprToXmm false 3 2⟩,
  ⟨44, 5, .vpbroadcast false true 3 3⟩,
  ⟨49, 6, .vgf2p8affineqb true 3 3 14 0⟩,
  ⟨55, 4, .vload true 0 (.baseDisp 6 0)⟩,
  ⟨59, 4, .vload true 1 (.baseDisp 7 0)⟩,
  ⟨63, 6, .vgf2p8affineqb true 0 0 14 0⟩,
  ⟨69, 5, .vbinOp .vgf2p8mulb true 2 0 3⟩,
  ⟨74, 6, .vgf2p8affineqb true 2 2 15 0⟩,
  ⟨80, 4, .vbinOp .vpxor true 1 1 2⟩,
  ⟨84, 4, .vstore true 1 (.baseDisp 7 0)⟩,
  ⟨88, 4, .aluImm .add true 6 32⟩,
  ⟨92, 4, .aluImm .add true 7 32⟩,
  ⟨96, 3, .incDec false true 1⟩,
  ⟨99, 2, .jcc 5 55⟩,
  ⟨101, 4, .vbinOp .vpxor true 0 0 0⟩,
  ⟨105, 4, .vbinOp .vpxor true 1 1 1⟩,
  ⟨109, 4, .vbinOp .vpxor true 2 2 2⟩,
  ⟨113, 4, .vbinOp .vpxor true 3 3 3⟩,
  ⟨117, 5, .vbinOp .vpxor true 14 14 14⟩,
  ⟨122, 5, .vbinOp .vpxor true 15 15 15⟩,
  ⟨127, 2, .aluRegReg .xorOp false 0 0⟩,
  ⟨129, 2, .aluRegReg .xorOp false 2 2⟩,
  ⟨131, 3, .vzeroall⟩,
  ⟨134, 3, .vzeroupper⟩,
  ⟨137, 2, .aluRegReg .xorOp false 7 7⟩,
  ⟨139, 2, .aluRegReg .xorOp false 6 6⟩,
  ⟨141, 2, .aluRegReg .xorOp false 2 2⟩,
  ⟨143, 2, .aluRegReg .xorOp false 1 1⟩,
  ⟨145, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨148, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨151, 3, .aluRegReg .xorOp false 10 10⟩,
  ⟨154, 3, .aluRegReg .xorOp false 11 11⟩,
  ⟨157, 2, .aluRegReg .xorOp false 0 0⟩,
  ⟨159, 1, .ret⟩
]

def gf256MacGfniBroadcast (scalar : UInt64) : Vec256 :=
  let w := mapBytes64 (fun _ => (maskGprWidth false scalar).toUInt8)
  ⟨w, w, w, w⟩

def gf256MacGfniVec (share acc : Vec256) (scalar : UInt64) : Vec256 :=
  evalVecBin256 .vpxor acc (gf256MulGfniVec share (gf256MacGfniBroadcast scalar))

def gf256MacGfniStepMem (mem : UInt64 → UInt8) (dst src scalar : UInt64) : UInt64 → UInt8 :=
  writeMem256 mem dst (gf256MacGfniVec (readMem256 mem src) (readMem256 mem dst) scalar)

def gf256MacGfniIterMem : Nat → (UInt64 → UInt8) → UInt64 → UInt64 → UInt64 → (UInt64 → UInt8)
  | 0, mem, _, _, _ => mem
  | k + 1, mem, dst, src, scalar =>
    gf256MacGfniIterMem k (gf256MacGfniStepMem mem dst src scalar) (dst + 32) (src + 32) scalar

private theorem gf256MacGfniBody_one_iter
    (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 : Vec256)
    (cf o zf : Bool) (m : UInt64 → UInt8) :
    let mT2R : Vec256 := ⟨gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat⟩
    let mR2T : Vec256 := ⟨gfniRijndaelToTowerMat, gfniRijndaelToTowerMat, gfniRijndaelToTowerMat, gfniRijndaelToTowerMat⟩
    StepsX86 gf256MacGfniProg 11
      ⟨55, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨y0, y1, y2, (gfniAffineVec256 (gf256MacGfniBroadcast r2) ⟨gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat⟩ 0), y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, mT2R, mR2T⟩,
        cf, o, zf, true, false, m⟩
      ⟨jccPc (!((r1 - 1) == 0)) 55 101,
        ⟨r0, r1 - 1, r2, r3, r4, r5, r6 + 32, r7 + 32, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨gfniAffineVec256 (readMem256 m r6) mT2R 0,
          gf256MacGfniVec (readMem256 m r6) (readMem256 m r7) r2,
          gf256MulGfniVec (readMem256 m r6) (gf256MacGfniBroadcast r2),
          (gfniAffineVec256 (gf256MacGfniBroadcast r2) ⟨gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat⟩ 0), y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, mT2R, mR2T⟩,
        decide (r7.toNat + (32 : UInt64).toNat ≥ 0x10000000000000000),
        evalX86IncDecOf false true r1,
        (r1 - 1) == 0, true, false, gf256MacGfniStepMem m r7 r6 r2⟩ := by
  dsimp only
  iterate 7
    apply StepsX86.cons rfl rfl
    · simp only [stepX86, evalX86Addr, clampVecWidth, evalVecBin256,
        u64_add_zero, b16get_6, b16get_7]
      rfl
  iterate 2
    apply StepsX86.cons rfl rfl
    · rw [stepX86_addImm64]
  apply StepsX86.cons rfl rfl
  · rw [stepX86_dec64]
  apply StepsX86.cons rfl rfl
  · rw [stepX86_jnz]
  exact StepsX86.zero _

private theorem gf256MacGfniLoop_steps (k : Nat) (hk : k + 1 < 0x10000000000000000)
    (r0 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 : Vec256)
    (cf o zf : Bool) (m : UInt64 → UInt8) :
    let mT2R : Vec256 := ⟨gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat⟩
    let mR2T : Vec256 := ⟨gfniRijndaelToTowerMat, gfniRijndaelToTowerMat, gfniRijndaelToTowerMat, gfniRijndaelToTowerMat⟩
    ∃ cf' o' zf',
      StepsX86 gf256MacGfniProg (17 + 11 * k)
        ⟨55, ⟨r0, UInt64.ofNat (k + 1), r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
          ⟨y0, y1, y2, (gfniAffineVec256 (gf256MacGfniBroadcast r2) ⟨gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat⟩ 0), y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, mT2R, mR2T⟩,
          cf, o, zf, true, false, m⟩
        ⟨127,
          ⟨r0, 0, r2, r3, r4, r5,
            r6 + UInt64.ofNat (32 * (k + 1)), r7 + UInt64.ofNat (32 * (k + 1)),
            r8, r9, r10, r11, r12, r13, r14, r15⟩,
          ⟨Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13,
            Vec256.zero, Vec256.zero⟩,
          cf', o', zf', true, false, gf256MacGfniIterMem (k + 1) m r7 r6 r2⟩ := by
  induction k generalizing r6 r7 y0 y1 y2 cf o zf m with
  | zero =>
    dsimp only
    have h1 : UInt64.ofNat 1 - 1 = 0 := by decide
    have hIter := gf256MacGfniBody_one_iter r0 (UInt64.ofNat 1) r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
      y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 cf o zf m
    dsimp only at hIter
    rw [h1, u64_zero_beq_zero] at hIter
    rw [show jccPc (!true) 55 101 = 101 from rfl] at hIter
    have hEpi : StepsX86 gf256MacGfniProg 6
        ⟨101, ⟨r0, 0, r2, r3, r4, r5, r6 + 32, r7 + 32, r8, r9, r10, r11, r12, r13, r14, r15⟩,
          ⟨gfniAffineVec256 (readMem256 m r6) ⟨gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat⟩ 0,
            gf256MacGfniVec (readMem256 m r6) (readMem256 m r7) r2,
            gf256MulGfniVec (readMem256 m r6) (gf256MacGfniBroadcast r2),
            (gfniAffineVec256 (gf256MacGfniBroadcast r2) ⟨gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat⟩ 0), y4, y5, y6, y7, y8, y9, y10, y11, y12, y13,
            ⟨gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat⟩,
            ⟨gfniRijndaelToTowerMat, gfniRijndaelToTowerMat, gfniRijndaelToTowerMat, gfniRijndaelToTowerMat⟩⟩,
          decide (r7.toNat + (32 : UInt64).toNat ≥ 0x10000000000000000),
          evalX86IncDecOf false true (UInt64.ofNat 1),
          true, true, false, gf256MacGfniStepMem m r7 r6 r2⟩
        ⟨127, ⟨r0, 0, r2, r3, r4, r5, r6 + 32, r7 + 32, r8, r9, r10, r11, r12, r13, r14, r15⟩,
          ⟨Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13,
            Vec256.zero, Vec256.zero⟩,
          decide (r7.toNat + (32 : UInt64).toNat ≥ 0x10000000000000000),
          evalX86IncDecOf false true (UInt64.ofNat 1),
          true, true, false, gf256MacGfniStepMem m r7 r6 r2⟩ := by
      iterate 6
        apply StepsX86.cons rfl rfl
        · simp only [stepX86, clampVecWidth, evalVecBin256, elf_u64_xor_self]
          rfl
      exact StepsX86.zero _
    have hComb := StepsX86_trans hIter hEpi
    exact ⟨_, _, _, hComb⟩
  | succ j ih =>
    dsimp only
    have hDec : UInt64.ofNat (j + 1 + 1) - 1 = UInt64.ofNat (j + 1) := by
      apply UInt64.eq_of_toBitVec_eq
      apply BitVec.eq_of_toNat_eq
      have hlt2 : j + 1 < 0x10000000000000000 := by omega
      simp [UInt64.toNat_toBitVec, Nat.mod_eq_of_lt hlt2]
    have hNz : (UInt64.ofNat (j + 1) == 0) = false := by
      cases h : UInt64.ofNat (j + 1) == 0
      · rfl
      · have hn := congrArg UInt64.toNat (beq_iff_eq.mp h)
        have hlt : j + 1 < 0x10000000000000000 := by omega
        rw [show (UInt64.ofNat (j + 1)).toNat = j + 1 from Nat.mod_eq_of_lt hlt] at hn
        exact absurd hn (Nat.succ_ne_zero j)
    have hIter := gf256MacGfniBody_one_iter r0 (UInt64.ofNat (j + 1 + 1)) r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
      y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 cf o zf m
    dsimp only at hIter
    rw [hDec, hNz] at hIter
    rw [show jccPc (!false) 55 101 = 55 from rfl] at hIter
    obtain ⟨cf', o', zf', hRest⟩ := ih (by omega) (r6 + 32) (r7 + 32)
      (gfniAffineVec256 (readMem256 m r6) ⟨gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat⟩ 0)
      (gf256MacGfniVec (readMem256 m r6) (readMem256 m r7) r2)
      (gf256MulGfniVec (readMem256 m r6) (gf256MacGfniBroadcast r2))
      (decide (r7.toNat + (32 : UInt64).toNat ≥ 0x10000000000000000))
      (evalX86IncDecOf false true (UInt64.ofNat (j + 1 + 1))) false (gf256MacGfniStepMem m r7 r6 r2)
    have hComb := StepsX86_trans hIter hRest
    have hStepEq : 11 + (17 + 11 * j) = 17 + 11 * (j + 1) := by omega
    have hAddPtr : ∀ p : UInt64, (p + 32) + UInt64.ofNat (32 * (j + 1)) = p + UInt64.ofNat (32 * (j + 1 + 1)) := by
      intro p
      apply UInt64.eq_of_toBitVec_eq
      simp only [UInt64.toBitVec_add, BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp [UInt64.toNat_toBitVec]
      omega
    rw [hStepEq, hAddPtr r6, hAddPtr r7] at hComb
    exact ⟨cf', o', zf', hComb⟩

private theorem gf256MacGfniCore_reaches (k : Nat) (hk : k + 1 < 0x10000000000000000)
    (r0 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Vec256)
    (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    ∃ cf' o' zf',
      StepsX86 gf256MacGfniProg (26 + 11 * k)
        ⟨0, ⟨r0, UInt64.ofNat (k + 1), r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
          ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
          cf, o, zf, dy, false, m⟩
        ⟨127,
          ⟨gfniRijndaelToTowerMat, 0, r2, r3, r4, r5,
            r6 + UInt64.ofNat (32 * (k + 1)), r7 + UInt64.ofNat (32 * (k + 1)),
            r8, r9, r10, r11, r12, r13, r14, r15⟩,
          ⟨Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13,
            Vec256.zero, Vec256.zero⟩,
          cf', o', zf', true, false, gf256MacGfniIterMem (k + 1) m r7 r6 r2⟩ := by
  have hPrologue : StepsX86 gf256MacGfniProg 9
      ⟨0, ⟨r0, UInt64.ofNat (k + 1), r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
        cf, o, zf, dy, false, m⟩
      ⟨55, ⟨gfniRijndaelToTowerMat, UInt64.ofNat (k + 1), r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨y0, y1, y2, (gfniAffineVec256 (gf256MacGfniBroadcast r2) ⟨gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat⟩ 0), y4, y5, y6, y7, y8, y9, y10, y11, y12, y13,
          ⟨gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat⟩,
          ⟨gfniRijndaelToTowerMat, gfniRijndaelToTowerMat, gfniRijndaelToTowerMat, gfniRijndaelToTowerMat⟩⟩,
        cf, o, zf, true, false, m⟩ := by
    iterate 9
      apply StepsX86.cons rfl rfl
      · simp only [stepX86, maskGprWidth_true, b16get_0, b16set_0, Bool.or_true]
        rfl
    exact StepsX86.zero _
  obtain ⟨cf', o', zf', hLoop⟩ := gf256MacGfniLoop_steps k hk gfniRijndaelToTowerMat
    r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
    y0 y1 y2 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 cf o zf m
  have hComb := StepsX86_trans hPrologue hLoop
  have hEq : 9 + (17 + 11 * k) = 26 + 11 * k := by omega
  rw [hEq] at hComb
  exact ⟨cf', o', zf', hComb⟩


private theorem gf256MacGfni_reaches_full (k : Nat) (hk : k + 1 < 0x10000000000000000)
    (r0 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Vec256)
    (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    ∃ cf' o' zf',
      ExecReachesX86 gf256MacGfniProg (39 + 11 * k)
        ⟨0, ⟨r0, UInt64.ofNat (k + 1), r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
          ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
          cf, o, zf, dy, false, m⟩
        ⟨159,
          ⟨0, 0, 0, r3, r4, r5, 0, 0, 0, 0, 0, 0, r12, r13, r14, r15⟩,
          Bank16.const Vec256.zero,
          cf', o', zf', false, false, gf256MacGfniIterMem (k + 1) m r7 r6 r2⟩ := by
  obtain ⟨cf', o', zf', hCore⟩ := gf256MacGfniCore_reaches k hk
    r0 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
    y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 cf o zf dy m
  have hTrans := hCore.toExecReaches
  have hTail : ExecReachesX86 gf256MacGfniProg 13
      ⟨127,
        ⟨gfniRijndaelToTowerMat, 0, r2, r3, r4, r5,
          r6 + UInt64.ofNat (32 * (k + 1)), r7 + UInt64.ofNat (32 * (k + 1)),
          r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13,
          Vec256.zero, Vec256.zero⟩,
        cf', o', zf', true, false, gf256MacGfniIterMem (k + 1) m r7 r6 r2⟩
        ⟨159,
          ⟨0, 0, 0, r3, r4, r5, 0, 0, 0, 0, 0, 0, r12, r13, r14, r15⟩,
          Bank16.const Vec256.zero,
          false, false, true, false, false, gf256MacGfniIterMem (k + 1) m r7 r6 r2⟩ := by
    apply StepsX86.toExecReaches
    iterate 13
      apply StepsX86.cons rfl rfl
      · simp only [current_vzeroall_step, current_vzeroupper_zero_step, stepX86_xorRR, mask32_xor_self, u64_zero_beq_zero,
          b16set_0, b16set_1, b16set_2, b16set_6, b16set_7,
          b16set_8, b16set_9, b16set_10, b16set_11]
        rfl
    exact StepsX86.zero _
  have hFull := ExecReachesX86_trans hTrans hTail
  have hStepEq : (26 + 11 * k) + 13 = 39 + 11 * k := by omega
  rw [hStepEq] at hFull
  exact ⟨false, false, true, hFull⟩


private theorem gf256MacGfni_getByte_xor (a b : UInt64) (i : Nat) (hi : i < 8) :
    getByte64 (a ^^^ b) i = getByte64 a i ^^^ getByte64 b i := by
  apply UInt8.eq_of_toBitVec_eq
  simp only [getByte64_bv _ i hi, UInt64.toBitVec_xor, UInt8.toBitVec_xor,
    BitVec.ushiftRight_xor_distrib, BitVec.setWidth_xor]

private theorem gf256MacGfniVec_lane_byte (share acc : Vec256) (scalar : UInt64) (r : Nat) (hr : r < 8) :
    getByte64 (gf256MacGfniVec share acc scalar).w0 r =
      getByte64 acc.w0 r ^^^ gfniTowerMulByte (getByte64 share.w0 r) (maskGprWidth false scalar).toUInt8 ∧
    getByte64 (gf256MacGfniVec share acc scalar).w1 r =
      getByte64 acc.w1 r ^^^ gfniTowerMulByte (getByte64 share.w1 r) (maskGprWidth false scalar).toUInt8 ∧
    getByte64 (gf256MacGfniVec share acc scalar).w2 r =
      getByte64 acc.w2 r ^^^ gfniTowerMulByte (getByte64 share.w2 r) (maskGprWidth false scalar).toUInt8 ∧
    getByte64 (gf256MacGfniVec share acc scalar).w3 r =
      getByte64 acc.w3 r ^^^ gfniTowerMulByte (getByte64 share.w3 r) (maskGprWidth false scalar).toUInt8 := by
  have h := gf256MulGfniVec_lane_byte share (gf256MacGfniBroadcast scalar) r hr
  simp only [gf256MacGfniBroadcast, getByte64_mapBytes64 _ r hr] at h
  rcases h with ⟨h0, h1, h2, h3⟩
  simp only [gf256MacGfniVec, evalVecBin256, gf256MacGfni_getByte_xor _ _ r hr,
    gf256MacGfniBroadcast, h0, h1, h2, h3, and_self]

theorem gf256MacGfniStepMem_at (mem : UInt64 → UInt8) (dst src scalar : UInt64) (k : Nat) (hk : k < 32) :
    gf256MacGfniStepMem mem dst src scalar (dst + UInt64.ofNat k) =
      mem (dst + UInt64.ofNat k) ^^^ gfniTowerMulByte (mem (src + UInt64.ofNat k)) (maskGprWidth false scalar).toUInt8 := by
  unfold gf256MacGfniStepMem
  rw [writeMem256_at _ dst _ k hk]
  by_cases h0 : k < 8
  · simp only [h0, ↓reduceIte]
    rw [(gf256MacGfniVec_lane_byte _ _ _ k h0).1]
    unfold readMem256; dsimp only
    rw [getByte64_readMem64 mem dst k h0, getByte64_readMem64 mem src k h0]
  · by_cases h1 : k < 16
    · simp only [h0, h1, ↓reduceIte]
      rw [(gf256MacGfniVec_lane_byte _ _ _ (k - 8) (by omega)).2.1]
      unfold readMem256; dsimp only
      rw [getByte64_readMem64 mem (dst + 8) (k - 8) (by omega),
          getByte64_readMem64 mem (src + 8) (k - 8) (by omega)]
      have ha : (dst + 8) + UInt64.ofNat (k - 8) = dst + UInt64.ofNat k := by
        change (dst + UInt64.ofNat 8) + UInt64.ofNat (k - 8) = dst + UInt64.ofNat k
        rw [u64_add_ofNat_assoc dst 8 (k - 8) (by omega), show 8 + (k - 8) = k by omega]
      have hb : (src + 8) + UInt64.ofNat (k - 8) = src + UInt64.ofNat k := by
        change (src + UInt64.ofNat 8) + UInt64.ofNat (k - 8) = src + UInt64.ofNat k
        rw [u64_add_ofNat_assoc src 8 (k - 8) (by omega), show 8 + (k - 8) = k by omega]
      rw [ha, hb]
    · by_cases h2 : k < 24
      · simp only [h0, h1, h2, ↓reduceIte]
        rw [(gf256MacGfniVec_lane_byte _ _ _ (k - 16) (by omega)).2.2.1]
        unfold readMem256; dsimp only
        rw [getByte64_readMem64 mem (dst + 16) (k - 16) (by omega),
            getByte64_readMem64 mem (src + 16) (k - 16) (by omega)]
        have ha : (dst + 16) + UInt64.ofNat (k - 16) = dst + UInt64.ofNat k := by
          change (dst + UInt64.ofNat 16) + UInt64.ofNat (k - 16) = dst + UInt64.ofNat k
          rw [u64_add_ofNat_assoc dst 16 (k - 16) (by omega), show 16 + (k - 16) = k by omega]
        have hb : (src + 16) + UInt64.ofNat (k - 16) = src + UInt64.ofNat k := by
          change (src + UInt64.ofNat 16) + UInt64.ofNat (k - 16) = src + UInt64.ofNat k
          rw [u64_add_ofNat_assoc src 16 (k - 16) (by omega), show 16 + (k - 16) = k by omega]
        rw [ha, hb]
      · simp only [h0, h1, h2, ↓reduceIte]
        rw [(gf256MacGfniVec_lane_byte _ _ _ (k - 24) (by omega)).2.2.2]
        unfold readMem256; dsimp only
        rw [getByte64_readMem64 mem (dst + 24) (k - 24) (by omega),
            getByte64_readMem64 mem (src + 24) (k - 24) (by omega)]
        have ha : (dst + 24) + UInt64.ofNat (k - 24) = dst + UInt64.ofNat k := by
          change (dst + UInt64.ofNat 24) + UInt64.ofNat (k - 24) = dst + UInt64.ofNat k
          rw [u64_add_ofNat_assoc dst 24 (k - 24) (by omega), show 24 + (k - 24) = k by omega]
        have hb : (src + 24) + UInt64.ofNat (k - 24) = src + UInt64.ofNat k := by
          change (src + UInt64.ofNat 24) + UInt64.ofNat (k - 24) = src + UInt64.ofNat k
          rw [u64_add_ofNat_assoc src 24 (k - 24) (by omega), show 24 + (k - 24) = k by omega]
        rw [ha, hb]

theorem gf256MacGfniStepMem_outside (mem : UInt64 → UInt8) (dst src scalar a : UInt64)
    (ha : ∀ k : Nat, k < 32 → a ≠ dst + UInt64.ofNat k) :
    gf256MacGfniStepMem mem dst src scalar a = mem a :=
  writeMem256_outside mem dst _ a ha

theorem gf256MacGfniIterMem_outside (n : Nat) (mem : UInt64 → UInt8) (dst src scalar a : UInt64)
    (hn : 32 * n ≤ 0x10000000000000000)
    (ha : ∀ idx : Nat, idx < 32 * n → a ≠ dst + UInt64.ofNat idx) :
    gf256MacGfniIterMem n mem dst src scalar a = mem a := by
  induction n generalizing mem dst src scalar with
  | zero => rfl
  | succ k ih =>
    unfold gf256MacGfniIterMem
    rw [ih _ (dst + 32) (src + 32) scalar (by omega) (fun idx hidx heq => by
      change a = (dst + UInt64.ofNat 32) + UInt64.ofNat idx at heq
      rw [u64_add_ofNat_assoc dst 32 idx (by omega)] at heq
      exact ha (32 + idx) (by omega) heq)]
    exact gf256MacGfniStepMem_outside mem dst src scalar a (fun j hj => ha j (by omega))

theorem gf256MacGfniIterMem_at (n : Nat) (mem : UInt64 → UInt8) (dst src scalar : UInt64)
    (hn : 32 * n ≤ 0x10000000000000000)
    (hDisjA : ∀ i j : Nat, i < 32 * n → j < 32 * n → dst + UInt64.ofNat i ≠ src + UInt64.ofNat j)
    (idx : Nat) (hidx : idx < 32 * n) :
    gf256MacGfniIterMem n mem dst src scalar (dst + UInt64.ofNat idx) =
      mem (dst + UInt64.ofNat idx) ^^^ gfniTowerMulByte (mem (src + UInt64.ofNat idx)) (maskGprWidth false scalar).toUInt8 := by
  induction n generalizing mem dst src scalar idx with
  | zero => exact absurd hidx (by omega)
  | succ k ih =>
    unfold gf256MacGfniIterMem
    by_cases hFirst : idx < 32
    · rw [gf256MacGfniIterMem_outside k _ (dst + 32) (src + 32) scalar _ (by omega)
        (fun j hj heq => by
          change dst + UInt64.ofNat idx = (dst + UInt64.ofNat 32) + UInt64.ofNat j at heq
          rw [u64_add_ofNat_assoc dst 32 j (by omega)] at heq
          have := u64_add_ofNat_inj (by omega) (by omega) heq
          omega)]
      exact gf256MacGfniStepMem_at mem dst src scalar idx hFirst
    · have hAddr : dst + UInt64.ofNat idx = (dst + 32) + UInt64.ofNat (idx - 32) := by
        change dst + UInt64.ofNat idx = (dst + UInt64.ofNat 32) + UInt64.ofNat (idx - 32)
        rw [u64_add_ofNat_assoc dst 32 (idx - 32) (by omega), show 32 + (idx - 32) = idx by omega]
      rw [hAddr, ih (gf256MacGfniStepMem mem dst src scalar) (dst + 32) (src + 32) scalar (by omega)
        (fun i j hi hj heq => by
          change (dst + UInt64.ofNat 32) + UInt64.ofNat i = (src + UInt64.ofNat 32) + UInt64.ofNat j at heq
          rw [u64_add_ofNat_assoc dst 32 i (by omega), u64_add_ofNat_assoc src 32 j (by omega)] at heq
          exact hDisjA (32 + i) (32 + j) (by omega) (by omega) heq)
        (idx - 32) (by omega)]
      have hA : (src + 32) + UInt64.ofNat (idx - 32) = src + UInt64.ofNat idx := by
        change (src + UInt64.ofNat 32) + UInt64.ofNat (idx - 32) = src + UInt64.ofNat idx
        rw [u64_add_ofNat_assoc src 32 (idx - 32) (by omega), show 32 + (idx - 32) = idx by omega]
      rw [← hAddr, hA,
          gf256MacGfniStepMem_outside mem dst src scalar (dst + UInt64.ofNat idx)
            (fun j hj heq => by
              have := u64_add_ofNat_inj (by omega) (by omega) heq
              omega),
          gf256MacGfniStepMem_outside mem dst src scalar (src + UInt64.ofNat idx)
            (fun j hj heq => hDisjA j idx (by omega) hidx heq.symm)]


def gf256MacGfniName : List UInt8 :=
  [0x71, 0x73, 0x61, 0x67, 0x5f, 0x61, 0x73, 0x6d, 0x5f, 0x67, 0x66, 0x32, 0x35, 0x36, 0x5f, 0x73, 0x68, 0x61, 0x6d, 0x69, 0x72, 0x5f, 0x6d, 0x61, 0x63, 0x5f, 0x67, 0x66, 0x6e, 0x69]

theorem gf256MacGfni_fresh_decode :
    ∃ slice, findSliceByNameBytes currentX86ExtractedSlices
      gf256MacGfniName = some slice ∧
      decodeX86Stream slice.code = some gf256MacGfniProg := by
  exact ⟨currentX86ExtractedSlices[3], by decide +kernel, by decide +kernel⟩

/-- Positive block counts only: the zero-count guard belongs to Rust, not this symbol. -/
theorem current_gf256_shamir_mac_gfni_loop_functional
    (k : Nat) (s : X86State)
    (hk : 32 * (k + 1) ≤ 0x10000000000000000)
    (hpc : s.pc = 0) (hh : s.halted = false)
    (hc : s.gpr.get 1 = UInt64.ofNat (k + 1))
    (hDisj : ∀ i j : Nat, i < 32 * (k + 1) → j < 32 * (k + 1) →
      s.gpr.get 7 + UInt64.ofNat i ≠ s.gpr.get 6 + UInt64.ofNat j) :
    ∃ slice prog, findSliceByNameBytes currentX86ExtractedSlices
      gf256MacGfniName = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ extra : Nat,
        let result := runX86 prog (40 + 11 * k + extra) s
        result.1.halted = true ∧ result.1.pc = (readMem64 result.1.mem (s.gpr.get 4)).toNat ∧
        result.2.length = 40 + 11 * k ∧ result.1.ymmDirty = false ∧
        result.1.ymm = Bank16.const Vec256.zero ∧
        (∀ idx : Nat, idx < 32 * (k + 1) →
          Simulates 3
            (towerAdd 3 (unpackTower 3 (s.mem (s.gpr.get 7 + UInt64.ofNat idx)).toBitVec)
              (towerMul 3 (unpackTower 3 (s.mem (s.gpr.get 6 + UInt64.ofNat idx)).toBitVec)
                (unpackTower 3 (maskGprWidth false (s.gpr.get 2)).toUInt8.toBitVec)))
            (result.1.mem (s.gpr.get 7 + UInt64.ofNat idx)).toBitVec) ∧
        (∀ a : UInt64, (∀ idx : Nat, idx < 32 * (k + 1) →
          a ≠ s.gpr.get 7 + UInt64.ofNat idx) → result.1.mem a = s.mem a) := by
  obtain ⟨slice, hf, hd⟩ := gf256MacGfni_fresh_decode
  refine ⟨slice, gf256MacGfniProg, hf, hd, ?_⟩
  rcases s with ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
    ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
    cf, o, zf, dy, hlt, mem⟩
  dsimp only at hpc hh; subst hpc hh
  have hr1 : r1 = UInt64.ofNat (k + 1) := hc
  subst hr1
  obtain ⟨cf', o', zf', hR⟩ := gf256MacGfni_reaches_full k (by omega)
    r0 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
    y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 cf o zf dy mem
  obtain ⟨_, _, hPost⟩ := ExecReachesX86_ret hR rfl (show
    findInstrAtPc 159 gf256MacGfniProg = some ⟨159, 1, .ret⟩ from rfl)
  intro extra
  have hRun := (hPost extra).1
  have hLen := (hPost extra).2
  have hN : 39 + 11 * k + 1 = 40 + 11 * k := by omega
  rw [hN] at hRun hLen
  dsimp only
  rw [hRun, hLen]
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro idx hidx
    dsimp only
    simp only [b16get_7, b16get_6, b16get_2]
    rw [gf256MacGfniIterMem_at (k + 1) mem r7 r6 r2 hk hDisj idx hidx,
      UInt8.toBitVec_xor]
    exact Simulates.add 3 (elfSimulates_unpack 3 _)
      (gfniTowerMulByte_simulates_binaryTower _ _)
  · intro a ha
    exact gf256MacGfniIterMem_outside (k + 1) mem r7 r6 r2 a hk ha


/-- A nonzero accumulator and zero scalar distinguish MAC from overwriting multiply. -/
def gf256MacGfniWitnessState : X86State :=
  ⟨0, ⟨0, 1, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩,
    Bank16.const Vec256.zero, false, false, false, false, false, fun _ => 1⟩

private theorem gf256MacGfniWitness_disjoint :
    ∀ i j : Nat, i < 32 * (0 + 1) → j < 32 * (0 + 1) →
      gf256MacGfniWitnessState.gpr.get 7 + UInt64.ofNat i ≠
        gf256MacGfniWitnessState.gpr.get 6 + UInt64.ofNat j := by
  intro i j hi hj heq
  have h := congrArg UInt64.toNat heq
  change (0 + UInt64.ofNat i).toNat = (64 + UInt64.ofNat j).toNat at h
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat'] at h
  change (0 + i % 18446744073709551616) % 18446744073709551616 =
    (64 + j % 18446744073709551616) % 18446744073709551616 at h
  omega

theorem gf256MacGfni_inhabited :
    ∃ k : Nat, ∃ s : X86State,
      32 * (k + 1) ≤ 0x10000000000000000 ∧
      s.pc = 0 ∧ s.halted = false ∧ s.gpr.get 1 = UInt64.ofNat (k + 1) ∧
      (∀ i j : Nat, i < 32 * (k + 1) → j < 32 * (k + 1) →
        s.gpr.get 7 + UInt64.ofNat i ≠ s.gpr.get 6 + UInt64.ofNat j) := by
  exact ⟨0, gf256MacGfniWitnessState, by decide, rfl, rfl, rfl, gf256MacGfniWitness_disjoint⟩

theorem gf256MacGfni_overwrite_tooth :
    ∃ slice prog, findSliceByNameBytes currentX86ExtractedSlices
      gf256MacGfniName = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      (runX86 prog 40 gf256MacGfniWitnessState).1.mem 0 ≠
        gfniTowerMulByte (gf256MacGfniWitnessState.mem 64) 0 := by
  obtain ⟨slice, prog, hf, hd, hfun⟩ := current_gf256_shamir_mac_gfni_loop_functional
    0 gf256MacGfniWitnessState (by decide) rfl rfl rfl gf256MacGfniWitness_disjoint
  refine ⟨slice, prog, hf, hd, ?_⟩
  have hb := (hfun 0).2.2.2.2.2.1 0 (by decide)
  change Simulates 3 (towerAdd 3 (unpackTower 3 (1 : UInt8).toBitVec)
    (towerMul 3 (unpackTower 3 (1 : UInt8).toBitVec)
      (unpackTower 3 (0 : UInt8).toBitVec)))
    ((runX86 prog 40 gf256MacGfniWitnessState).1.mem 0).toBitVec at hb
  have hone : ((runX86 prog 40 gf256MacGfniWitnessState).1.mem 0).toBitVec = 1#8 :=
    (elfSimulates_pack_eq hb).symm.trans (by
      simp only [unpackTower, packTower, towerAdd, towerMul, lowBits.public_eq_1, highBits.public_eq_1, joinBits_eq_append]
      decide +kernel)
  intro heq
  have hzero := congrArg UInt8.toBitVec heq
  rw [hone] at hzero
  exact (by decide : (1#8 : BitVec 8) ≠ (gfniTowerMulByte 1 0).toBitVec) hzero

#tooth_pair current_gf256_shamir_mac_gfni_loop_functional vs gf256MacGfni_overwrite_tooth
#verify_inhabited current_gf256_shamir_mac_gfni_loop_functional gf256MacGfni_inhabited


/-- Byte effect of `vpcmpgtb zero, x`. -/
def gf256Avx2SignMask (x : UInt8) : UInt8 :=
  if signExt8ToInt 0 > signExt8ToInt x then 0xff else 0

/-- The exact doubling/reduction sequence used by both AVX2 Shamir kernels. -/
def gf256Avx2Double (x : UInt8) : UInt8 :=
  (x + x) ^^^ (0x1b &&& gf256Avx2SignMask x)

theorem gf256Avx2Double_eq_xtime (x : UInt8) :
    gf256Avx2Double x = xtimeRijndael x := by
  rcases x with ⟨⟨n⟩⟩; revert n; decide +kernel

def gf256Avx2HornerRounds : Nat → UInt8 → UInt8 → UInt8 → UInt8
  | 0, _, _, acc => acc
  | n + 1, a, b, acc =>
    gf256Avx2HornerRounds n a (b + b)
      (gf256Avx2Double acc ^^^ (a &&& gf256Avx2SignMask (b + b)))

def gf256Avx2HornerByte (a b : UInt8) : UInt8 :=
  gf256Avx2HornerRounds 7 a b (a &&& gf256Avx2SignMask b)

private theorem gf256Avx2HornerRounds_linear (n : Nat) (a1 a2 b c1 c2 : UInt8) :
    gf256Avx2HornerRounds n (a1 ^^^ a2) b (c1 ^^^ c2) =
      gf256Avx2HornerRounds n a1 b c1 ^^^ gf256Avx2HornerRounds n a2 b c2 := by
  induction n generalizing b c1 c2 with
  | zero => rfl
  | succ n ih =>
    simp only [gf256Avx2HornerRounds, gf256Avx2Double_eq_xtime,
      xtimeRijndael_xor, u8_and_xor_left]
    rw [u8_xor_four, ih]

private theorem gf256Avx2HornerByte_linear (a1 a2 b : UInt8) :
    gf256Avx2HornerByte (a1 ^^^ a2) b =
      gf256Avx2HornerByte a1 b ^^^ gf256Avx2HornerByte a2 b := by
  simp only [gf256Avx2HornerByte, u8_and_xor_left, gf256Avx2HornerRounds_linear]

private theorem gf256Avx2HornerByte_zero (b : UInt8) :
    gf256Avx2HornerByte 0 b = gfniMulByte 0 b := by
  simp [gf256Avx2HornerByte, gf256Avx2HornerRounds, gf256Avx2Double, gf256Avx2SignMask,
    gfniMulByte, xtimeRijndael]

private theorem gf256Avx2HornerByte_basis (a b : UInt8)
    (ha : a = 1 ∨ a = 2 ∨ a = 4 ∨ a = 8 ∨ a = 16 ∨ a = 32 ∨ a = 64 ∨ a = 128) :
    gf256Avx2HornerByte a b = gfniMulByte a b := by
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (rcases b with ⟨⟨n⟩⟩; revert n; decide +kernel)

theorem gf256Avx2HornerByte_eq_gfniMulByte (a b : UInt8) :
    gf256Avx2HornerByte a b = gfniMulByte a b := by
  have hBit : ∀ m : UInt8,
      m = 1 ∨ m = 2 ∨ m = 4 ∨ m = 8 ∨ m = 16 ∨ m = 32 ∨ m = 64 ∨ m = 128 →
      gf256Avx2HornerByte (a &&& m) b = gfniMulByte (a &&& m) b := by
    intro m hm
    rcases u8_bit_cases a m hm with h0 | h1
    · rw [h0]; exact gf256Avx2HornerByte_zero b
    · rw [h1]; exact gf256Avx2HornerByte_basis m b hm
  conv => lhs; rw [u8_basis_decomp a]
  conv => rhs; rw [u8_basis_decomp a]
  simp only [gf256Avx2HornerByte_linear, gfniMulByte_xor_left,
    hBit 0x01 (Or.inl rfl),
    hBit 0x02 (Or.inr (Or.inl rfl)),
    hBit 0x04 (Or.inr (Or.inr (Or.inl rfl))),
    hBit 0x08 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
    hBit 0x10 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),
    hBit 0x20 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))),
    hBit 0x40 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))),
    hBit 0x80 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))]


def gf256Avx2SignVec (v : Vec256) : Vec256 := evalVecBin256 .vpcmpgtb Vec256.zero v

def gf256Avx2Reduction : Vec256 :=
  ⟨0x1b1b1b1b1b1b1b1b, 0x1b1b1b1b1b1b1b1b, 0x1b1b1b1b1b1b1b1b, 0x1b1b1b1b1b1b1b1b⟩

def gf256Avx2DoubleVec (v : Vec256) : Vec256 :=
  evalVecBin256 .vpxor (evalVecBin256 .vpaddb v v)
    (evalVecBin256 .vpand gf256Avx2Reduction (gf256Avx2SignVec v))

def gf256Avx2HornerVecRounds : Nat → Vec256 → Vec256 → Vec256 → Vec256
  | 0, _, _, acc => acc
  | n + 1, a, b, acc =>
    let b' := evalVecBin256 .vpaddb b b
    gf256Avx2HornerVecRounds n a b'
      (evalVecBin256 .vpxor (gf256Avx2DoubleVec acc)
        (evalVecBin256 .vpand a (gf256Avx2SignVec b')))

def gf256Avx2HornerVec (a b : Vec256) : Vec256 :=
  gf256Avx2HornerVecRounds 7 a b (evalVecBin256 .vpand a (gf256Avx2SignVec b))

private def gf256Avx2GetWord (v : Vec256) : Nat → UInt64
  | 0 => v.w0 | 1 => v.w1 | 2 => v.w2 | _ => v.w3

private def gf256Avx2GetByte (v : Vec256) (w r : Nat) : UInt8 :=
  getByte64 (gf256Avx2GetWord v w) r

private theorem gf256Avx2_getByte_and (a b : UInt64) (r : Nat) (hr : r < 8) :
    getByte64 (a &&& b) r = getByte64 a r &&& getByte64 b r := by
  apply UInt8.eq_of_toBitVec_eq
  simp only [getByte64_bv _ r hr, UInt64.toBitVec_and, UInt8.toBitVec_and,
    BitVec.ushiftRight_and_distrib, BitVec.setWidth_and]

private theorem gf256Avx2_vecbyte_xor (a b : Vec256) (w r : Nat) (hr : r < 8) :
    gf256Avx2GetByte (evalVecBin256 .vpxor a b) w r =
      gf256Avx2GetByte a w r ^^^ gf256Avx2GetByte b w r := by
  match w with
  | 0 | 1 | 2 | n+3 =>
    exact gf256MacGfni_getByte_xor _ _ r hr

private theorem gf256Avx2_vecbyte_and (a b : Vec256) (w r : Nat) (hr : r < 8) :
    gf256Avx2GetByte (evalVecBin256 .vpand a b) w r =
      gf256Avx2GetByte a w r &&& gf256Avx2GetByte b w r := by
  match w with
  | 0 | 1 | 2 | n+3 =>
    exact gf256Avx2_getByte_and _ _ r hr

private theorem gf256Avx2_vecbyte_map (a b : Vec256) (f : UInt8 → UInt8 → UInt8)
    (w r : Nat) (hr : r < 8) :
    gf256Avx2GetByte (mapBytesVec256 a b f) w r =
      f (gf256Avx2GetByte a w r) (gf256Avx2GetByte b w r) := by
  match w with
  | 0 | 1 | 2 | n+3 =>
    simp only [gf256Avx2GetByte, gf256Avx2GetWord, mapBytesVec256, getByte64_mapBytes64 _ r hr]

private theorem gf256Avx2_vecbyte_add (a b : Vec256) (w r : Nat) (hr : r < 8) :
    gf256Avx2GetByte (evalVecBin256 .vpaddb a b) w r =
      gf256Avx2GetByte a w r + gf256Avx2GetByte b w r :=
  gf256Avx2_vecbyte_map a b _ w r hr

private theorem gf256Avx2_vecbyte_zero (w r : Nat) :
    gf256Avx2GetByte Vec256.zero w r = 0 := by
  match w with
  | 0 | 1 | 2 | n+3 => simp [gf256Avx2GetByte, gf256Avx2GetWord, Vec256.zero, getByte64]

private theorem gf256Avx2_vecbyte_sign (v : Vec256) (w r : Nat) (hr : r < 8) :
    gf256Avx2GetByte (gf256Avx2SignVec v) w r =
      gf256Avx2SignMask (gf256Avx2GetByte v w r) := by
  simp only [gf256Avx2SignVec, evalVecBin256, gf256Avx2_vecbyte_map _ _ _ w r hr,
    gf256Avx2_vecbyte_zero, gf256Avx2SignMask]

private theorem gf256Avx2_vecbyte_reduction (w r : Nat) (hr : r < 8) :
    gf256Avx2GetByte gf256Avx2Reduction w r = 0x1b := by
  have h : getByte64 0x1b1b1b1b1b1b1b1b r = 0x1b := by
    match r, hr with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => decide
    | n+8, hn => omega
  match w with
  | 0 | 1 | 2 | n+3 => exact h

private theorem gf256Avx2_vecbyte_double (v : Vec256) (w r : Nat) (hr : r < 8) :
    gf256Avx2GetByte (gf256Avx2DoubleVec v) w r =
      gf256Avx2Double (gf256Avx2GetByte v w r) := by
  simp only [gf256Avx2DoubleVec, gf256Avx2_vecbyte_xor _ _ w r hr,
    gf256Avx2_vecbyte_add _ _ w r hr, gf256Avx2_vecbyte_and _ _ w r hr,
    gf256Avx2_vecbyte_sign _ w r hr, gf256Avx2_vecbyte_reduction w r hr,
    gf256Avx2Double]

private theorem gf256Avx2_vecbyte_rounds (n : Nat) (a b acc : Vec256) (w r : Nat) (hr : r < 8) :
    gf256Avx2GetByte (gf256Avx2HornerVecRounds n a b acc) w r =
      gf256Avx2HornerRounds n (gf256Avx2GetByte a w r) (gf256Avx2GetByte b w r)
        (gf256Avx2GetByte acc w r) := by
  induction n generalizing b acc with
  | zero => rfl
  | succ n ih =>
    simp only [gf256Avx2HornerVecRounds, ih, gf256Avx2_vecbyte_xor _ _ w r hr,
      gf256Avx2_vecbyte_double _ w r hr, gf256Avx2_vecbyte_and _ _ w r hr,
      gf256Avx2_vecbyte_sign _ w r hr, gf256Avx2_vecbyte_add _ _ w r hr,
      gf256Avx2HornerRounds]

theorem gf256Avx2_ext {a b : Vec256} (h0 : a.w0 = b.w0) (h1 : a.w1 = b.w1)
    (h2 : a.w2 = b.w2) (h3 : a.w3 = b.w3) : a = b := by
  cases a; cases b
  cases h0; cases h1; cases h2; cases h3
  rfl

theorem gf256Avx2HornerVec_eq_gfniMul (a b : Vec256) :
    gf256Avx2HornerVec a b = mapBytesVec256 a b gfniMulByte := by
  have h (w r : Nat) (hr : r < 8) :
      getByte64 (gf256Avx2GetWord (gf256Avx2HornerVec a b) w) r =
        getByte64 (gf256Avx2GetWord (mapBytesVec256 a b gfniMulByte) w) r := by
    change gf256Avx2GetByte _ w r = gf256Avx2GetByte _ w r
    simp only [gf256Avx2HornerVec, gf256Avx2_vecbyte_rounds _ _ _ _ w r hr,
      gf256Avx2_vecbyte_and _ _ w r hr, gf256Avx2_vecbyte_sign _ w r hr,
      gf256Avx2_vecbyte_map _ _ _ w r hr]
    exact gf256Avx2HornerByte_eq_gfniMulByte _ _
  have hw (w : Nat) : gf256Avx2GetWord (gf256Avx2HornerVec a b) w =
      gf256Avx2GetWord (mapBytesVec256 a b gfniMulByte) w := by
    rw [← mapBytes64_getByte64 (gf256Avx2GetWord (gf256Avx2HornerVec a b) w),
      ← mapBytes64_getByte64 (gf256Avx2GetWord (mapBytesVec256 a b gfniMulByte) w)]
    simp only [mapBytes64, h w 0 (by decide), h w 1 (by decide), h w 2 (by decide),
      h w 3 (by decide), h w 4 (by decide), h w 5 (by decide), h w 6 (by decide), h w 7 (by decide)]
  exact gf256Avx2_ext (hw 0) (hw 1) (hw 2) (hw 3)


section
set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-- The duplicated 16-byte nibble tables loaded by the AVX2 kernels. -/
def gf256Avx2Table (mat : UInt64) (high : Bool) : Vec256 :=
  let f := fun i => gfniAffineByte (if high then UInt8.ofNat i <<< 4 else UInt8.ofNat i) mat 0
  let lo := mapBytes64 f
  let hi := mapBytes64 (fun i => f (i + 8))
  ⟨lo, hi, lo, hi⟩

def gf256Avx2Mask : Vec256 := ⟨0x0f0f0f0f0f0f0f0f, 0x0f0f0f0f0f0f0f0f,
  0x0f0f0f0f0f0f0f0f, 0x0f0f0f0f0f0f0f0f⟩

def gf256Avx2Convert (lo hi v : Vec256) : Vec256 :=
  let vl := evalVecBin256 .vpand gf256Avx2Mask v
  let vh := evalVecBin256 .vpand gf256Avx2Mask (evalVecShift256 .vpsrlw v 4)
  evalVecBin256 .vpxor (evalVecBin256 .vpshufb lo vl) (evalVecBin256 .vpshufb hi vh)

private theorem gf256Avx2_byte_ext (x y : UInt64)
    (h : ∀ i : Nat, i < 8 → getByte64 x i = getByte64 y i) : x = y := by
  rw [← mapBytes64_getByte64 x, ← mapBytes64_getByte64 y]
  simp only [mapBytes64, h 0 (by decide), h 1 (by decide), h 2 (by decide),
    h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)]

private theorem gf256Avx2_low_byte (v : UInt64) (i : Nat) (hi : i < 8) :
    getByte64 ((0x0f0f0f0f0f0f0f0f : UInt64) &&& v) i = getByte64 v i &&& 15 := by
  apply UInt8.eq_of_toBitVec_eq
  simp only [getByte64_bv _ i hi, UInt64.toBitVec_and, UInt8.toBitVec_and,
    BitVec.ushiftRight_and_distrib, BitVec.setWidth_and]
  have hm : BitVec.setWidth 8 ((0x0f0f0f0f0f0f0f0f#64) >>> (i * 8)) = 15#8 := by
    match i, hi with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => decide
    | n+8, h => omega
  rw [show UInt64.toBitVec 0x0f0f0f0f0f0f0f0f = 0x0f0f0f0f0f0f0f0f#64 from by decide +kernel,
    show UInt8.toBitVec 15 = 15#8 from by decide +kernel, hm, BitVec.and_comm]

private theorem gf256Avx2_high_byte (v : UInt64) (i : Nat) (hi : i < 8) :
    getByte64 ((0x0f0f0f0f0f0f0f0f : UInt64) &&& ((v >>> 4) &&& 0x0fff0fff0fff0fff)) i =
      (getByte64 v i >>> 4) &&& 15 := by
  apply UInt8.eq_of_toBitVec_eq
  rw [getByte64_bv _ i hi]
  ext j hj
  simp only [UInt64.toBitVec_and, UInt64.toBitVec_shiftRight, BitVec.getElem_setWidth,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, UInt8.toBitVec_and,
    UInt8.toBitVec_shiftRight, BitVec.getElem_and, getByte64_bv _ i hi]
  match i, hi, j, hj with
  | 0, _, 0, _ | 0, _, 1, _ | 0, _, 2, _ | 0, _, 3, _ | 0, _, 4, _ | 0, _, 5, _ | 0, _, 6, _ | 0, _, 7, _
  | 1, _, 0, _ | 1, _, 1, _ | 1, _, 2, _ | 1, _, 3, _ | 1, _, 4, _ | 1, _, 5, _ | 1, _, 6, _ | 1, _, 7, _
  | 2, _, 0, _ | 2, _, 1, _ | 2, _, 2, _ | 2, _, 3, _ | 2, _, 4, _ | 2, _, 5, _ | 2, _, 6, _ | 2, _, 7, _
  | 3, _, 0, _ | 3, _, 1, _ | 3, _, 2, _ | 3, _, 3, _ | 3, _, 4, _ | 3, _, 5, _ | 3, _, 6, _ | 3, _, 7, _
  | 4, _, 0, _ | 4, _, 1, _ | 4, _, 2, _ | 4, _, 3, _ | 4, _, 4, _ | 4, _, 5, _ | 4, _, 6, _ | 4, _, 7, _
  | 5, _, 0, _ | 5, _, 1, _ | 5, _, 2, _ | 5, _, 3, _ | 5, _, 4, _ | 5, _, 5, _ | 5, _, 6, _ | 5, _, 7, _
  | 6, _, 0, _ | 6, _, 1, _ | 6, _, 2, _ | 6, _, 3, _ | 6, _, 4, _ | 6, _, 5, _ | 6, _, 6, _ | 6, _, 7, _
  | 7, _, 0, _ | 7, _, 1, _ | 7, _, 2, _ | 7, _, 3, _ | 7, _, 4, _ | 7, _, 5, _ | 7, _, 6, _ | 7, _, 7, _ => simp
  | n+8, h, _, _ => omega
  | _, _, n+8, h => omega

private theorem gf256Avx2_nibble_bound (x : UInt8) :
    (x &&& 15).toNat < 16 ∧ ((x >>> 4) &&& 15).toNat < 16 := by
  rcases x with ⟨⟨n⟩⟩; revert n; decide +kernel

private theorem gf256Avx2_nibble_pick (mat : UInt64) (high : Bool) (x : UInt8)
    (hx : x.toNat < 16) :
    (if (x &&& 0x80) != 0 then 0 else
      if (x &&& 15).toNat < 8 then
        getByte64 (gf256Avx2Table mat high).w0 (x &&& 15).toNat
      else getByte64 (gf256Avx2Table mat high).w1 ((x &&& 15).toNat - 8)) =
      gfniAffineByte (if high then x <<< 4 else x) mat 0 := by
  have hz : (x &&& 0x80) = 0 := by
    rcases x with ⟨⟨n⟩⟩; revert hx n; decide +kernel
  have hm : x &&& 15 = x := by
    rcases x with ⟨⟨n⟩⟩; revert hx n; decide +kernel
  simp only [hz, hm, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  by_cases hl : x.toNat < 8
  · rw [ite_eq_left hl]
    simp only [gf256Avx2Table, getByte64_mapBytes64 _ x.toNat hl, UInt8.ofNat_toNat]
  · rw [ite_eq_right hl]
    simp only [gf256Avx2Table, getByte64_mapBytes64 _ (x.toNat - 8) (by omega)]
    rw [show x.toNat - 8 + 8 = x.toNat by omega, UInt8.ofNat_toNat]

private theorem gf256Avx2_split_t2r (x : UInt8) :
    gfniAffineByte (x &&& 15) gfniTowerToRijndaelMat 0 ^^^
      gfniAffineByte (((x >>> 4) &&& 15) <<< 4) gfniTowerToRijndaelMat 0 =
        gfniAffineByte x gfniTowerToRijndaelMat 0 := by
  rcases x with ⟨⟨n⟩⟩; revert n; decide +kernel

private theorem gf256Avx2_split_r2t (x : UInt8) :
    gfniAffineByte (x &&& 15) gfniRijndaelToTowerMat 0 ^^^
      gfniAffineByte (((x >>> 4) &&& 15) <<< 4) gfniRijndaelToTowerMat 0 =
        gfniAffineByte x gfniRijndaelToTowerMat 0 := by
  rcases x with ⟨⟨n⟩⟩; revert n; decide +kernel

private theorem gf256Avx2_shift4_word (w : UInt64) :
    (if (4 : Nat) ≥ 16 then (0 : UInt64) else
      (w >>> UInt64.ofNat 4) &&&
        (((0xFFFF : UInt64) >>> UInt64.ofNat 4) ||| (((0xFFFF : UInt64) >>> UInt64.ofNat 4) <<< 16) |||
         (((0xFFFF : UInt64) >>> UInt64.ofNat 4) <<< 32) ||| (((0xFFFF : UInt64) >>> UInt64.ofNat 4) <<< 48))) =
      ((w >>> 4) &&& 0x0fff0fff0fff0fff) := by
  rw [ite_eq_right (by decide), show UInt64.ofNat 4 = (4 : UInt64) from by decide +kernel]
  have hc : (((0xFFFF : UInt64) >>> 4) ||| (((0xFFFF : UInt64) >>> 4) <<< 16) |||
    (((0xFFFF : UInt64) >>> 4) <<< 32) ||| (((0xFFFF : UInt64) >>> 4) <<< 48)) =
      0x0fff0fff0fff0fff := by decide +kernel
  rw [hc]

private theorem gf256Avx2_high_byte_masked (v : UInt64) (i : Nat) (hi : i < 8) :
    getByte64 ((v >>> 4) &&& 0x0fff0fff0fff0fff) i &&& (15 : UInt8) =
      (getByte64 v i >>> 4) &&& (15 : UInt8) := by
  rw [← gf256Avx2_low_byte _ i hi]
  exact gf256Avx2_high_byte v i hi

private theorem gf256Avx2Table_w2 (mat : UInt64) (high : Bool) :
    (gf256Avx2Table mat high).w2 = (gf256Avx2Table mat high).w0 := rfl
private theorem gf256Avx2Table_w3 (mat : UInt64) (high : Bool) :
    (gf256Avx2Table mat high).w3 = (gf256Avx2Table mat high).w1 := rfl

private theorem gf256Avx2_convert_eq (mat : UInt64) (v : Vec256)
    (h : ∀ x : UInt8, gfniAffineByte (x &&& 15) mat 0 ^^^
      gfniAffineByte (((x >>> 4) &&& 15) <<< 4) mat 0 = gfniAffineByte x mat 0) :
    gf256Avx2Convert (gf256Avx2Table mat false) (gf256Avx2Table mat true) v =
      gfniAffineVec256 v ⟨mat, mat, mat, mat⟩ 0 := by
  cases v with
  | mk v0 v1 v2 v3 =>
    apply gf256Avx2_ext <;> apply gf256Avx2_byte_ext <;> intro i hi <;>
      simp only [gf256Avx2Convert, evalVecBin256, evalVecShift256, gf256Avx2Mask,
        gfniAffineVec256, gf256MacGfni_getByte_xor _ _ i hi,
        getByte64_mapBytes64 _ i hi, gf256Avx2_shift4_word, gf256Avx2_low_byte _ i hi,
        gf256Avx2_high_byte_masked _ i hi, gf256Avx2Table_w2, gf256Avx2Table_w3]
    all_goals
      change (if ((getByte64 _ i &&& 15) &&& 0x80) != 0 then _ else _) ^^^ _ = _
      rw [gf256Avx2_nibble_pick mat false _ (gf256Avx2_nibble_bound _).1,
        gf256Avx2_nibble_pick mat true _ (gf256Avx2_nibble_bound _).2]
      simpa only [Bool.false_eq_true, Bool.true_eq, ↓reduceIte] using h (getByte64 _ i)

theorem gf256Avx2_convert_t2r (v : Vec256) :
    gf256Avx2Convert (gf256Avx2Table gfniTowerToRijndaelMat false)
      (gf256Avx2Table gfniTowerToRijndaelMat true) v =
      gfniAffineVec256 v ⟨gfniTowerToRijndaelMat, gfniTowerToRijndaelMat,
        gfniTowerToRijndaelMat, gfniTowerToRijndaelMat⟩ 0 :=
  gf256Avx2_convert_eq _ v gf256Avx2_split_t2r

theorem gf256Avx2_convert_r2t (v : Vec256) :
    gf256Avx2Convert (gf256Avx2Table gfniRijndaelToTowerMat false)
      (gf256Avx2Table gfniRijndaelToTowerMat true) v =
      gfniAffineVec256 v ⟨gfniRijndaelToTowerMat, gfniRijndaelToTowerMat,
        gfniRijndaelToTowerMat, gfniRijndaelToTowerMat⟩ 0 :=
  gf256Avx2_convert_eq _ v gf256Avx2_split_r2t


def gf256MulAvx2Prog : List (DecodedInstr X86Instr) := [
  ⟨0, 5, .vload true 12 (.baseDisp 8 0)⟩,
  ⟨5, 6, .vload true 13 (.baseDisp 8 32)⟩,
  ⟨11, 6, .vload true 14 (.baseDisp 8 64)⟩,
  ⟨17, 6, .vload true 15 (.baseDisp 8 96)⟩,
  ⟨23, 5, .movImm false 0 15⟩,
  ⟨28, 4, .vmovGprToXmm false 10 0⟩,
  ⟨32, 5, .vpbroadcast false true 10 10⟩,
  ⟨37, 5, .movImm false 0 27⟩,
  ⟨42, 4, .vmovGprToXmm false 11 0⟩,
  ⟨46, 5, .vpbroadcast false true 11 11⟩,
  ⟨51, 5, .vbinOp .vpxor true 9 9 9⟩,
  ⟨56, 4, .vload true 0 (.baseDisp 6 0)⟩,
  ⟨60, 4, .vload true 1 (.baseDisp 2 0)⟩,
  ⟨64, 4, .vbinOp .vpand true 3 10 0⟩,
  ⟨68, 5, .vshiftImm .vpsrlw true 4 0 4⟩,
  ⟨73, 4, .vbinOp .vpand true 4 10 4⟩,
  ⟨77, 5, .vbinOp .vpshufb true 3 12 3⟩,
  ⟨82, 5, .vbinOp .vpshufb true 4 13 4⟩,
  ⟨87, 4, .vbinOp .vpxor true 0 3 4⟩,
  ⟨91, 4, .vbinOp .vpand true 3 10 1⟩,
  ⟨95, 5, .vshiftImm .vpsrlw true 4 1 4⟩,
  ⟨100, 4, .vbinOp .vpand true 4 10 4⟩,
  ⟨104, 5, .vbinOp .vpshufb true 3 12 3⟩,
  ⟨109, 5, .vbinOp .vpshufb true 4 13 4⟩,
  ⟨114, 4, .vbinOp .vpxor true 1 3 4⟩,
  ⟨118, 4, .vbinOp .vpcmpgtb true 2 9 1⟩,
  ⟨122, 4, .vbinOp .vpand true 2 0 2⟩,
  ⟨126, 4, .vbinOp .vpaddb true 1 1 1⟩,
  ⟨130, 4, .vbinOp .vpcmpgtb true 5 9 2⟩,
  ⟨134, 4, .vbinOp .vpaddb true 2 2 2⟩,
  ⟨138, 4, .vbinOp .vpand true 5 11 5⟩,
  ⟨142, 4, .vbinOp .vpxor true 2 2 5⟩,
  ⟨146, 4, .vbinOp .vpcmpgtb true 6 9 1⟩,
  ⟨150, 4, .vbinOp .vpand true 6 0 6⟩,
  ⟨154, 4, .vbinOp .vpxor true 2 2 6⟩,
  ⟨158, 4, .vbinOp .vpaddb true 1 1 1⟩,
  ⟨162, 4, .vbinOp .vpcmpgtb true 5 9 2⟩,
  ⟨166, 4, .vbinOp .vpaddb true 2 2 2⟩,
  ⟨170, 4, .vbinOp .vpand true 5 11 5⟩,
  ⟨174, 4, .vbinOp .vpxor true 2 2 5⟩,
  ⟨178, 4, .vbinOp .vpcmpgtb true 6 9 1⟩,
  ⟨182, 4, .vbinOp .vpand true 6 0 6⟩,
  ⟨186, 4, .vbinOp .vpxor true 2 2 6⟩,
  ⟨190, 4, .vbinOp .vpaddb true 1 1 1⟩,
  ⟨194, 4, .vbinOp .vpcmpgtb true 5 9 2⟩,
  ⟨198, 4, .vbinOp .vpaddb true 2 2 2⟩,
  ⟨202, 4, .vbinOp .vpand true 5 11 5⟩,
  ⟨206, 4, .vbinOp .vpxor true 2 2 5⟩,
  ⟨210, 4, .vbinOp .vpcmpgtb true 6 9 1⟩,
  ⟨214, 4, .vbinOp .vpand true 6 0 6⟩,
  ⟨218, 4, .vbinOp .vpxor true 2 2 6⟩,
  ⟨222, 4, .vbinOp .vpaddb true 1 1 1⟩,
  ⟨226, 4, .vbinOp .vpcmpgtb true 5 9 2⟩,
  ⟨230, 4, .vbinOp .vpaddb true 2 2 2⟩,
  ⟨234, 4, .vbinOp .vpand true 5 11 5⟩,
  ⟨238, 4, .vbinOp .vpxor true 2 2 5⟩,
  ⟨242, 4, .vbinOp .vpcmpgtb true 6 9 1⟩,
  ⟨246, 4, .vbinOp .vpand true 6 0 6⟩,
  ⟨250, 4, .vbinOp .vpxor true 2 2 6⟩,
  ⟨254, 4, .vbinOp .vpaddb true 1 1 1⟩,
  ⟨258, 4, .vbinOp .vpcmpgtb true 5 9 2⟩,
  ⟨262, 4, .vbinOp .vpaddb true 2 2 2⟩,
  ⟨266, 4, .vbinOp .vpand true 5 11 5⟩,
  ⟨270, 4, .vbinOp .vpxor true 2 2 5⟩,
  ⟨274, 4, .vbinOp .vpcmpgtb true 6 9 1⟩,
  ⟨278, 4, .vbinOp .vpand true 6 0 6⟩,
  ⟨282, 4, .vbinOp .vpxor true 2 2 6⟩,
  ⟨286, 4, .vbinOp .vpaddb true 1 1 1⟩,
  ⟨290, 4, .vbinOp .vpcmpgtb true 5 9 2⟩,
  ⟨294, 4, .vbinOp .vpaddb true 2 2 2⟩,
  ⟨298, 4, .vbinOp .vpand true 5 11 5⟩,
  ⟨302, 4, .vbinOp .vpxor true 2 2 5⟩,
  ⟨306, 4, .vbinOp .vpcmpgtb true 6 9 1⟩,
  ⟨310, 4, .vbinOp .vpand true 6 0 6⟩,
  ⟨314, 4, .vbinOp .vpxor true 2 2 6⟩,
  ⟨318, 4, .vbinOp .vpaddb true 1 1 1⟩,
  ⟨322, 4, .vbinOp .vpcmpgtb true 5 9 2⟩,
  ⟨326, 4, .vbinOp .vpaddb true 2 2 2⟩,
  ⟨330, 4, .vbinOp .vpand true 5 11 5⟩,
  ⟨334, 4, .vbinOp .vpxor true 2 2 5⟩,
  ⟨338, 4, .vbinOp .vpcmpgtb true 6 9 1⟩,
  ⟨342, 4, .vbinOp .vpand true 6 0 6⟩,
  ⟨346, 4, .vbinOp .vpxor true 2 2 6⟩,
  ⟨350, 4, .vbinOp .vpand true 3 10 2⟩,
  ⟨354, 5, .vshiftImm .vpsrlw true 4 2 4⟩,
  ⟨359, 4, .vbinOp .vpand true 4 10 4⟩,
  ⟨363, 5, .vbinOp .vpshufb true 3 14 3⟩,
  ⟨368, 5, .vbinOp .vpshufb true 4 15 4⟩,
  ⟨373, 4, .vbinOp .vpxor true 2 3 4⟩,
  ⟨377, 4, .vstore true 2 (.baseDisp 7 0)⟩,
  ⟨381, 4, .aluImm .add true 6 32⟩,
  ⟨385, 4, .aluImm .add true 2 32⟩,
  ⟨389, 4, .aluImm .add true 7 32⟩,
  ⟨393, 3, .incDec false true 1⟩,
  ⟨396, 6, .jcc 5 56⟩,
  ⟨402, 4, .vbinOp .vpxor true 0 0 0⟩,
  ⟨406, 4, .vbinOp .vpxor true 1 1 1⟩,
  ⟨410, 4, .vbinOp .vpxor true 2 2 2⟩,
  ⟨414, 4, .vbinOp .vpxor true 3 3 3⟩,
  ⟨418, 4, .vbinOp .vpxor true 4 4 4⟩,
  ⟨422, 4, .vbinOp .vpxor true 5 5 5⟩,
  ⟨426, 4, .vbinOp .vpxor true 6 6 6⟩,
  ⟨430, 5, .vbinOp .vpxor true 10 10 10⟩,
  ⟨435, 5, .vbinOp .vpxor true 11 11 11⟩,
  ⟨440, 5, .vbinOp .vpxor true 12 12 12⟩,
  ⟨445, 5, .vbinOp .vpxor true 13 13 13⟩,
  ⟨450, 5, .vbinOp .vpxor true 14 14 14⟩,
  ⟨455, 5, .vbinOp .vpxor true 15 15 15⟩,
  ⟨460, 2, .aluRegReg .xorOp false 0 0⟩,
  ⟨462, 3, .vzeroall⟩,
  ⟨465, 3, .vzeroupper⟩,
  ⟨468, 2, .aluRegReg .xorOp false 7 7⟩,
  ⟨470, 2, .aluRegReg .xorOp false 6 6⟩,
  ⟨472, 2, .aluRegReg .xorOp false 2 2⟩,
  ⟨474, 2, .aluRegReg .xorOp false 1 1⟩,
  ⟨476, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨479, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨482, 3, .aluRegReg .xorOp false 10 10⟩,
  ⟨485, 3, .aluRegReg .xorOp false 11 11⟩,
  ⟨488, 2, .aluRegReg .xorOp false 0 0⟩,
  ⟨490, 1, .ret⟩
]

def gf256MacAvx2Prog : List (DecodedInstr X86Instr) := [
  ⟨0, 5, .vload true 12 (.baseDisp 8 0)⟩,
  ⟨5, 6, .vload true 13 (.baseDisp 8 32)⟩,
  ⟨11, 6, .vload true 14 (.baseDisp 8 64)⟩,
  ⟨17, 6, .vload true 15 (.baseDisp 8 96)⟩,
  ⟨23, 5, .movImm false 0 15⟩,
  ⟨28, 4, .vmovGprToXmm false 10 0⟩,
  ⟨32, 5, .vpbroadcast false true 10 10⟩,
  ⟨37, 5, .movImm false 0 27⟩,
  ⟨42, 4, .vmovGprToXmm false 11 0⟩,
  ⟨46, 5, .vpbroadcast false true 11 11⟩,
  ⟨51, 5, .vbinOp .vpxor true 9 9 9⟩,
  ⟨56, 4, .vmovGprToXmm false 0 2⟩,
  ⟨60, 5, .vpbroadcast false true 0 0⟩,
  ⟨65, 9, .vload true 1 (.baseDisp 8 128)⟩,
  ⟨74, 4, .vbinOp .vpand true 3 10 0⟩,
  ⟨78, 5, .vshiftImm .vpsrlw true 4 0 4⟩,
  ⟨83, 4, .vbinOp .vpand true 4 10 4⟩,
  ⟨87, 5, .vbinOp .vpshufb true 3 12 3⟩,
  ⟨92, 5, .vbinOp .vpshufb true 4 13 4⟩,
  ⟨97, 4, .vbinOp .vpxor true 0 3 4⟩,
  ⟨101, 4, .vbinOp .vpand true 3 10 1⟩,
  ⟨105, 5, .vshiftImm .vpsrlw true 4 1 4⟩,
  ⟨110, 4, .vbinOp .vpand true 4 10 4⟩,
  ⟨114, 5, .vbinOp .vpshufb true 3 12 3⟩,
  ⟨119, 5, .vbinOp .vpshufb true 4 13 4⟩,
  ⟨124, 4, .vbinOp .vpxor true 1 3 4⟩,
  ⟨128, 4, .vbinOp .vpcmpgtb true 2 9 1⟩,
  ⟨132, 4, .vbinOp .vpand true 2 0 2⟩,
  ⟨136, 4, .vbinOp .vpaddb true 1 1 1⟩,
  ⟨140, 4, .vbinOp .vpcmpgtb true 5 9 2⟩,
  ⟨144, 4, .vbinOp .vpaddb true 2 2 2⟩,
  ⟨148, 4, .vbinOp .vpand true 5 11 5⟩,
  ⟨152, 4, .vbinOp .vpxor true 2 2 5⟩,
  ⟨156, 4, .vbinOp .vpcmpgtb true 6 9 1⟩,
  ⟨160, 4, .vbinOp .vpand true 6 0 6⟩,
  ⟨164, 4, .vbinOp .vpxor true 2 2 6⟩,
  ⟨168, 4, .vbinOp .vpaddb true 1 1 1⟩,
  ⟨172, 4, .vbinOp .vpcmpgtb true 5 9 2⟩,
  ⟨176, 4, .vbinOp .vpaddb true 2 2 2⟩,
  ⟨180, 4, .vbinOp .vpand true 5 11 5⟩,
  ⟨184, 4, .vbinOp .vpxor true 2 2 5⟩,
  ⟨188, 4, .vbinOp .vpcmpgtb true 6 9 1⟩,
  ⟨192, 4, .vbinOp .vpand true 6 0 6⟩,
  ⟨196, 4, .vbinOp .vpxor true 2 2 6⟩,
  ⟨200, 4, .vbinOp .vpaddb true 1 1 1⟩,
  ⟨204, 4, .vbinOp .vpcmpgtb true 5 9 2⟩,
  ⟨208, 4, .vbinOp .vpaddb true 2 2 2⟩,
  ⟨212, 4, .vbinOp .vpand true 5 11 5⟩,
  ⟨216, 4, .vbinOp .vpxor true 2 2 5⟩,
  ⟨220, 4, .vbinOp .vpcmpgtb true 6 9 1⟩,
  ⟨224, 4, .vbinOp .vpand true 6 0 6⟩,
  ⟨228, 4, .vbinOp .vpxor true 2 2 6⟩,
  ⟨232, 4, .vbinOp .vpaddb true 1 1 1⟩,
  ⟨236, 4, .vbinOp .vpcmpgtb true 5 9 2⟩,
  ⟨240, 4, .vbinOp .vpaddb true 2 2 2⟩,
  ⟨244, 4, .vbinOp .vpand true 5 11 5⟩,
  ⟨248, 4, .vbinOp .vpxor true 2 2 5⟩,
  ⟨252, 4, .vbinOp .vpcmpgtb true 6 9 1⟩,
  ⟨256, 4, .vbinOp .vpand true 6 0 6⟩,
  ⟨260, 4, .vbinOp .vpxor true 2 2 6⟩,
  ⟨264, 4, .vbinOp .vpaddb true 1 1 1⟩,
  ⟨268, 4, .vbinOp .vpcmpgtb true 5 9 2⟩,
  ⟨272, 4, .vbinOp .vpaddb true 2 2 2⟩,
  ⟨276, 4, .vbinOp .vpand true 5 11 5⟩,
  ⟨280, 4, .vbinOp .vpxor true 2 2 5⟩,
  ⟨284, 4, .vbinOp .vpcmpgtb true 6 9 1⟩,
  ⟨288, 4, .vbinOp .vpand true 6 0 6⟩,
  ⟨292, 4, .vbinOp .vpxor true 2 2 6⟩,
  ⟨296, 4, .vbinOp .vpaddb true 1 1 1⟩,
  ⟨300, 4, .vbinOp .vpcmpgtb true 5 9 2⟩,
  ⟨304, 4, .vbinOp .vpaddb true 2 2 2⟩,
  ⟨308, 4, .vbinOp .vpand true 5 11 5⟩,
  ⟨312, 4, .vbinOp .vpxor true 2 2 5⟩,
  ⟨316, 4, .vbinOp .vpcmpgtb true 6 9 1⟩,
  ⟨320, 4, .vbinOp .vpand true 6 0 6⟩,
  ⟨324, 4, .vbinOp .vpxor true 2 2 6⟩,
  ⟨328, 4, .vbinOp .vpaddb true 1 1 1⟩,
  ⟨332, 4, .vbinOp .vpcmpgtb true 5 9 2⟩,
  ⟨336, 4, .vbinOp .vpaddb true 2 2 2⟩,
  ⟨340, 4, .vbinOp .vpand true 5 11 5⟩,
  ⟨344, 4, .vbinOp .vpxor true 2 2 5⟩,
  ⟨348, 4, .vbinOp .vpcmpgtb true 6 9 1⟩,
  ⟨352, 4, .vbinOp .vpand true 6 0 6⟩,
  ⟨356, 4, .vbinOp .vpxor true 2 2 6⟩,
  ⟨360, 4, .vbinOp .vpand true 3 10 2⟩,
  ⟨364, 5, .vshiftImm .vpsrlw true 4 2 4⟩,
  ⟨369, 4, .vbinOp .vpand true 4 10 4⟩,
  ⟨373, 5, .vbinOp .vpshufb true 3 14 3⟩,
  ⟨378, 5, .vbinOp .vpshufb true 4 15 4⟩,
  ⟨383, 4, .vbinOp .vpxor true 2 3 4⟩,
  ⟨387, 6, .vperm2i128 7 2 2 0⟩,
  ⟨393, 6, .vperm2i128 8 2 2 17⟩,
  ⟨399, 4, .vload true 0 (.baseDisp 6 0)⟩,
  ⟨403, 4, .vload true 1 (.baseDisp 7 0)⟩,
  ⟨407, 4, .vbinOp .vpand true 2 10 0⟩,
  ⟨411, 5, .vshiftImm .vpsrlw true 3 0 4⟩,
  ⟨416, 4, .vbinOp .vpand true 3 10 3⟩,
  ⟨420, 5, .vbinOp .vpshufb true 2 7 2⟩,
  ⟨425, 5, .vbinOp .vpshufb true 3 8 3⟩,
  ⟨430, 4, .vbinOp .vpxor true 1 1 2⟩,
  ⟨434, 4, .vbinOp .vpxor true 1 1 3⟩,
  ⟨438, 4, .vstore true 1 (.baseDisp 7 0)⟩,
  ⟨442, 4, .aluImm .add true 6 32⟩,
  ⟨446, 4, .aluImm .add true 7 32⟩,
  ⟨450, 3, .incDec false true 1⟩,
  ⟨453, 2, .jcc 5 399⟩,
  ⟨455, 4, .vbinOp .vpxor true 0 0 0⟩,
  ⟨459, 4, .vbinOp .vpxor true 1 1 1⟩,
  ⟨463, 4, .vbinOp .vpxor true 2 2 2⟩,
  ⟨467, 4, .vbinOp .vpxor true 3 3 3⟩,
  ⟨471, 4, .vbinOp .vpxor true 4 4 4⟩,
  ⟨475, 4, .vbinOp .vpxor true 5 5 5⟩,
  ⟨479, 4, .vbinOp .vpxor true 6 6 6⟩,
  ⟨483, 4, .vbinOp .vpxor true 7 7 7⟩,
  ⟨487, 5, .vbinOp .vpxor true 8 8 8⟩,
  ⟨492, 5, .vbinOp .vpxor true 10 10 10⟩,
  ⟨497, 5, .vbinOp .vpxor true 11 11 11⟩,
  ⟨502, 5, .vbinOp .vpxor true 12 12 12⟩,
  ⟨507, 5, .vbinOp .vpxor true 13 13 13⟩,
  ⟨512, 5, .vbinOp .vpxor true 14 14 14⟩,
  ⟨517, 5, .vbinOp .vpxor true 15 15 15⟩,
  ⟨522, 2, .aluRegReg .xorOp false 0 0⟩,
  ⟨524, 2, .aluRegReg .xorOp false 2 2⟩,
  ⟨526, 3, .vzeroall⟩,
  ⟨529, 3, .vzeroupper⟩,
  ⟨532, 2, .aluRegReg .xorOp false 7 7⟩,
  ⟨534, 2, .aluRegReg .xorOp false 6 6⟩,
  ⟨536, 2, .aluRegReg .xorOp false 2 2⟩,
  ⟨538, 2, .aluRegReg .xorOp false 1 1⟩,
  ⟨540, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨543, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨546, 3, .aluRegReg .xorOp false 10 10⟩,
  ⟨549, 3, .aluRegReg .xorOp false 11 11⟩,
  ⟨552, 2, .aluRegReg .xorOp false 0 0⟩,
  ⟨554, 1, .ret⟩
]


def gf256MulAvx2Tables (m : UInt64 → UInt8) (base : UInt64) : Prop :=
  readMem256 m base = gf256Avx2Table gfniTowerToRijndaelMat false ∧
  readMem256 m (base + 32) = gf256Avx2Table gfniTowerToRijndaelMat true ∧
  readMem256 m (base + 64) = gf256Avx2Table gfniRijndaelToTowerMat false ∧
  readMem256 m (base + 96) = gf256Avx2Table gfniRijndaelToTowerMat true

def gf256MulAvx2Name : List UInt8 :=
  [113, 115, 97, 103, 95, 97, 115, 109, 95, 103, 102, 50, 53, 54, 95, 115, 104, 97, 109, 105, 114, 95, 109, 117, 108, 95, 97, 118, 120, 50]

def gf256MacAvx2Name : List UInt8 :=
  [113, 115, 97, 103, 95, 97, 115, 109, 95, 103, 102, 50, 53, 54, 95, 115, 104, 97, 109, 105, 114, 95, 109, 97, 99, 95, 97, 118, 120, 50]

theorem gf256MulAvx2_fresh_decode :
    ∃ slice, findSliceByNameBytes currentX86ExtractedSlices
      gf256MulAvx2Name = some slice ∧
      decodeX86Stream slice.code = some gf256MulAvx2Prog := by
  exact ⟨currentX86ExtractedSlices[4], by decide +kernel, by decide +kernel⟩

theorem gf256MacAvx2_fresh_decode :
    ∃ slice, findSliceByNameBytes currentX86ExtractedSlices
      gf256MacAvx2Name = some slice ∧
      decodeX86Stream slice.code = some gf256MacAvx2Prog := by
  exact ⟨currentX86ExtractedSlices[5], by decide +kernel, by decide +kernel⟩


def gf256MulAvx2Vec (a b : Vec256) : Vec256 :=
  gf256Avx2Convert (gf256Avx2Table gfniRijndaelToTowerMat false)
    (gf256Avx2Table gfniRijndaelToTowerMat true)
    (gf256Avx2HornerVec
      (gf256Avx2Convert (gf256Avx2Table gfniTowerToRijndaelMat false)
        (gf256Avx2Table gfniTowerToRijndaelMat true) a)
      (gf256Avx2Convert (gf256Avx2Table gfniTowerToRijndaelMat false)
        (gf256Avx2Table gfniTowerToRijndaelMat true) b))

theorem gf256MulAvx2Vec_eq (a b : Vec256) :
    gf256MulAvx2Vec a b = gf256MulGfniVec a b := by
  simp only [gf256MulAvx2Vec, gf256Avx2_convert_t2r, gf256Avx2_convert_r2t,
    gf256Avx2HornerVec_eq_gfniMul, gf256MulGfniVec]

/-- Refinement over the four 32-byte vectors actually read from the public table region. -/
theorem gf256MulAvx2_table_bytes_refine (mem : UInt64 → UInt8) (base : UInt64)
    (a b : Vec256) (ht : gf256MulAvx2Tables mem base) :
    gf256Avx2Convert (readMem256 mem (base + 64)) (readMem256 mem (base + 96))
      (gf256Avx2HornerVec
        (gf256Avx2Convert (readMem256 mem base) (readMem256 mem (base + 32)) a)
        (gf256Avx2Convert (readMem256 mem base) (readMem256 mem (base + 32)) b)) =
      gf256MulGfniVec a b := by
  rcases ht with ⟨ht0,ht1,ht2,ht3⟩
  rw [ht0,ht1,ht2,ht3]
  exact gf256MulAvx2Vec_eq a b

def gf256Avx2RoundProg (off : Nat) : List (DecodedInstr X86Instr) := [
  ⟨off, 4, .vbinOp .vpaddb true 1 1 1⟩,
  ⟨off+4, 4, .vbinOp .vpcmpgtb true 5 9 2⟩,
  ⟨off+8, 4, .vbinOp .vpaddb true 2 2 2⟩,
  ⟨off+12, 4, .vbinOp .vpand true 5 11 5⟩,
  ⟨off+16, 4, .vbinOp .vpxor true 2 2 5⟩,
  ⟨off+20, 4, .vbinOp .vpcmpgtb true 6 9 1⟩,
  ⟨off+24, 4, .vbinOp .vpand true 6 0 6⟩,
  ⟨off+28, 4, .vbinOp .vpxor true 2 2 6⟩]

def gf256Avx2Advance : Nat → Vec256 → Vec256
  | 0, b => b
  | n+1, b => gf256Avx2Advance n (evalVecBin256 .vpaddb b b)

private theorem gf256Avx2_round_steps (off : Nat) (g : Bank16 UInt64)
    (a b acc y3 y4 y5 y6 y7 y8 y10 y12 y13 y14 y15 : Vec256)
    (cf o zf : Bool) (m : UInt64 → UInt8) :
    StepsX86 (gf256Avx2RoundProg off) 8
      ⟨off, g, ⟨a,b,acc,y3,y4,y5,y6,y7,y8,Vec256.zero,y10,gf256Avx2Reduction,y12,y13,y14,y15⟩,
        cf,o,zf,true,false,m⟩
      ⟨off+32, g,
        ⟨a, evalVecBin256 .vpaddb b b,
          evalVecBin256 .vpxor (gf256Avx2DoubleVec acc)
            (evalVecBin256 .vpand a (gf256Avx2SignVec (evalVecBin256 .vpaddb b b))),
          y3,y4,evalVecBin256 .vpand gf256Avx2Reduction (gf256Avx2SignVec acc),
          evalVecBin256 .vpand a (gf256Avx2SignVec (evalVecBin256 .vpaddb b b)),
          y7,y8,Vec256.zero,y10,gf256Avx2Reduction,y12,y13,y14,y15⟩,
        cf,o,zf,true,false,m⟩ := by
  have hne (n : Nat) (hn : 0 < n) : ¬ off = off + n := by omega
  iterate 8
    apply StepsX86.cons rfl (by
      simp only [findInstrAtPc, gf256Avx2RoundProg, beq_iff_eq, Nat.add_left_cancel_iff,
        hne 4 (by decide), hne 8 (by decide), hne 12 (by decide), hne 16 (by decide),
        hne 20 (by decide), hne 24 (by decide), hne 28 (by decide), Nat.reduceEqDiff, ↓reduceIte]
      rfl)
    · simp only [stepX86, clampVecWidth, Nat.add_assoc]
      rfl
  exact StepsX86.zero _

private theorem gf256Avx2_rounds_reaches (prog : List (DecodedInstr X86Instr))
    (base : Nat) (hp : ∀ j : Nat, j < 7 → progPreservesNonRet (gf256Avx2RoundProg (base+32*j)) prog = true)
    (n j : Nat) (hn : j + n ≤ 7) (g : Bank16 UInt64)
    (a b acc y3 y4 y5 y6 y7 y8 y10 y12 y13 y14 y15 : Vec256)
    (cf o zf : Bool) (m : UInt64 → UInt8) :
    ∃ z5 z6 : Vec256, ExecReachesX86 prog (8*n)
      ⟨base+32*j,g,⟨a,b,acc,y3,y4,y5,y6,y7,y8,Vec256.zero,y10,gf256Avx2Reduction,y12,y13,y14,y15⟩,
        cf,o,zf,true,false,m⟩
      ⟨base+32*(j+n),g,
        ⟨a,gf256Avx2Advance n b,gf256Avx2HornerVecRounds n a b acc,y3,y4,z5,z6,y7,y8,
          Vec256.zero,y10,gf256Avx2Reduction,y12,y13,y14,y15⟩,cf,o,zf,true,false,m⟩ := by
  induction n generalizing j b acc y5 y6 with
  | zero => exact ⟨y5,y6,ExecReachesX86_zero _ _⟩
  | succ n ih =>
    have hr := ExecReachesX86_transfer_nonret (hp j (by omega))
      (gf256Avx2_round_steps (base+32*j) g a b acc y3 y4 y5 y6 y7 y8 y10 y12 y13 y14 y15 cf o zf m).toExecReaches rfl
    have hoff : base+32*j+32 = base+32*(j+1) := by omega
    rw [hoff] at hr
    obtain ⟨z5,z6,hrest⟩ := ih (j+1) (by omega)
      (evalVecBin256 .vpaddb b b)
      (evalVecBin256 .vpxor (gf256Avx2DoubleVec acc)
        (evalVecBin256 .vpand a (gf256Avx2SignVec (evalVecBin256 .vpaddb b b))))
      (evalVecBin256 .vpand gf256Avx2Reduction (gf256Avx2SignVec acc))
      (evalVecBin256 .vpand a (gf256Avx2SignVec (evalVecBin256 .vpaddb b b)))
    have hc := ExecReachesX86_trans hr hrest
    have hcount : 8+8*n = 8*(n+1) := by omega
    rw [hcount, show j+1+n=j+(n+1) by omega] at hc
    exact ⟨z5,z6,hc⟩

private theorem gf256MulAvx2_rounds_preserved (j : Nat) (hj : j < 7) :
    progPreservesNonRet (gf256Avx2RoundProg (126+32*j)) gf256MulAvx2Prog = true := by
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ => decide +kernel
  | n+7, h => omega

private theorem gf256MulAvx2_body
    (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y0 y1 y2 y3 y4 y5 y6 y7 y8 : Vec256)
    (cf o zf : Bool) (m : UInt64 → UInt8) :
    ∃ z0 z1 z2 z3 z4 z5 z6 : Vec256,
      ExecReachesX86 gf256MulAvx2Prog 84
        ⟨56, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
          ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, Vec256.zero, gf256Avx2Mask, gf256Avx2Reduction, gf256Avx2Table gfniTowerToRijndaelMat false, gf256Avx2Table gfniTowerToRijndaelMat true, gf256Avx2Table gfniRijndaelToTowerMat false, gf256Avx2Table gfniRijndaelToTowerMat true⟩, cf, o, zf, true, false, m⟩
        ⟨jccPc (!((r1 - 1) == 0)) 56 402, ⟨r0, r1 - 1, r2 + 32, r3, r4, r5, r6 + 32, r7 + 32, r8, r9, r10, r11, r12, r13, r14, r15⟩,
          ⟨z0, z1, z2, z3, z4, z5, z6, y7, y8, Vec256.zero, gf256Avx2Mask, gf256Avx2Reduction, gf256Avx2Table gfniTowerToRijndaelMat false, gf256Avx2Table gfniTowerToRijndaelMat true, gf256Avx2Table gfniRijndaelToTowerMat false, gf256Avx2Table gfniRijndaelToTowerMat true⟩,
          decide (r7.toNat + (32 : UInt64).toNat ≥ 0x10000000000000000),
          evalX86IncDecOf false true r1, (r1 - 1) == 0, true, false,
          gf256MulGfniStepMem m r7 r6 r2⟩ := by
  let a := gf256Avx2Convert (gf256Avx2Table gfniTowerToRijndaelMat false)
    (gf256Avx2Table gfniTowerToRijndaelMat true) (readMem256 m r6)
  let b := gf256Avx2Convert (gf256Avx2Table gfniTowerToRijndaelMat false)
    (gf256Avx2Table gfniTowerToRijndaelMat true) (readMem256 m r2)
  let bLo := evalVecBin256 .vpshufb (gf256Avx2Table gfniTowerToRijndaelMat false)
    (evalVecBin256 .vpand gf256Avx2Mask (readMem256 m r2))
  let bHi := evalVecBin256 .vpshufb (gf256Avx2Table gfniTowerToRijndaelMat true)
    (evalVecBin256 .vpand gf256Avx2Mask (evalVecShift256 .vpsrlw (readMem256 m r2) 4))
  let init := evalVecBin256 .vpand a (gf256Avx2SignVec b)
  have hStart : StepsX86 gf256MulAvx2Prog 16
      ⟨56,⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, Vec256.zero, gf256Avx2Mask, gf256Avx2Reduction, gf256Avx2Table gfniTowerToRijndaelMat false, gf256Avx2Table gfniTowerToRijndaelMat true, gf256Avx2Table gfniRijndaelToTowerMat false, gf256Avx2Table gfniRijndaelToTowerMat true⟩,cf,o,zf,true,false,m⟩
      ⟨126,⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,⟨a, b, init, bLo, bHi, y5, y6, y7, y8, Vec256.zero, gf256Avx2Mask, gf256Avx2Reduction, gf256Avx2Table gfniTowerToRijndaelMat false, gf256Avx2Table gfniTowerToRijndaelMat true, gf256Avx2Table gfniRijndaelToTowerMat false, gf256Avx2Table gfniRijndaelToTowerMat true⟩,cf,o,zf,true,false,m⟩ := by
    iterate 16
      apply StepsX86.cons rfl rfl
      · simp only [stepX86, evalX86Addr, clampVecWidth, u64_add_zero, b16get_2, b16get_6]
        rfl
    exact StepsX86.zero _
  obtain ⟨z5,z6,hRounds⟩ := gf256Avx2_rounds_reaches gf256MulAvx2Prog 126
    gf256MulAvx2_rounds_preserved 7 0 (by decide) ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩
    a b init bLo bHi y5 y6 y7 y8 gf256Avx2Mask
    (gf256Avx2Table gfniTowerToRijndaelMat false) (gf256Avx2Table gfniTowerToRijndaelMat true)
    (gf256Avx2Table gfniRijndaelToTowerMat false) (gf256Avx2Table gfniRijndaelToTowerMat true) cf o zf m
  let prod := gf256Avx2HornerVec a b
  let outLo := evalVecBin256 .vpshufb (gf256Avx2Table gfniRijndaelToTowerMat false)
    (evalVecBin256 .vpand gf256Avx2Mask prod)
  let outHi := evalVecBin256 .vpshufb (gf256Avx2Table gfniRijndaelToTowerMat true)
    (evalVecBin256 .vpand gf256Avx2Mask (evalVecShift256 .vpsrlw prod 4))
  let out := gf256Avx2Convert (gf256Avx2Table gfniRijndaelToTowerMat false)
    (gf256Avx2Table gfniRijndaelToTowerMat true) prod
  have hTail : StepsX86 gf256MulAvx2Prog 12
      ⟨350,⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,⟨a, gf256Avx2Advance 7 b, prod, bLo, bHi, z5, z6, y7, y8, Vec256.zero, gf256Avx2Mask, gf256Avx2Reduction, gf256Avx2Table gfniTowerToRijndaelMat false, gf256Avx2Table gfniTowerToRijndaelMat true, gf256Avx2Table gfniRijndaelToTowerMat false, gf256Avx2Table gfniRijndaelToTowerMat true⟩,cf,o,zf,true,false,m⟩
      ⟨jccPc (!((r1-1)==0)) 56 402,⟨r0, r1 - 1, r2 + 32, r3, r4, r5, r6 + 32, r7 + 32, r8, r9, r10, r11, r12, r13, r14, r15⟩,⟨a, gf256Avx2Advance 7 b, out, outLo, outHi, z5, z6, y7, y8, Vec256.zero, gf256Avx2Mask, gf256Avx2Reduction, gf256Avx2Table gfniTowerToRijndaelMat false, gf256Avx2Table gfniTowerToRijndaelMat true, gf256Avx2Table gfniRijndaelToTowerMat false, gf256Avx2Table gfniRijndaelToTowerMat true⟩,
        decide (r7.toNat + (32 : UInt64).toNat ≥ 0x10000000000000000),
        evalX86IncDecOf false true r1,(r1-1)==0,true,false,writeMem256 m r7 out⟩ := by
    iterate 7
      apply StepsX86.cons rfl rfl
      · simp only [stepX86, evalX86Addr, clampVecWidth, u64_add_zero, b16get_7]
        rfl
    iterate 3
      apply StepsX86.cons rfl rfl
      · rw [stepX86_addImm64]
    apply StepsX86.cons rfl rfl
    · rw [stepX86_dec64]
    apply StepsX86.cons rfl rfl
    · rw [stepX86_jnz]
    exact StepsX86.zero _
  have hc := ExecReachesX86_trans (ExecReachesX86_trans hStart.toExecReaches hRounds) hTail.toExecReaches
  have hm : writeMem256 m r7 out = gf256MulGfniStepMem m r7 r6 r2 := by
    change writeMem256 m r7 (gf256MulAvx2Vec (readMem256 m r6) (readMem256 m r2)) = _
    rw [gf256MulAvx2Vec_eq]
    rfl
  rw [hm] at hc
  exact ⟨a,gf256Avx2Advance 7 b,out,outLo,outHi,z5,z6,hc⟩

private theorem gf256MulAvx2_loop_steps (k : Nat) (hk : k + 1 < 0x10000000000000000)
    (r0 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y0 y1 y2 y3 y4 y5 y6 y7 y8 : Vec256)
    (cf o zf : Bool) (m : UInt64 → UInt8) :
    ∃ z0 z1 z2 z3 z4 z5 z6 : Vec256, ∃ cf' o' zf',
      ExecReachesX86 gf256MulAvx2Prog (84 + 84 * k)
        ⟨56, ⟨r0, UInt64.ofNat (k + 1), r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, Vec256.zero, gf256Avx2Mask, gf256Avx2Reduction, gf256Avx2Table gfniTowerToRijndaelMat false, gf256Avx2Table gfniTowerToRijndaelMat true, gf256Avx2Table gfniRijndaelToTowerMat false, gf256Avx2Table gfniRijndaelToTowerMat true⟩, cf, o, zf, true, false, m⟩
        ⟨402, ⟨r0, 0, r2 + UInt64.ofNat (32 * (k + 1)), r3, r4, r5, r6 + UInt64.ofNat (32 * (k + 1)), r7 + UInt64.ofNat (32 * (k + 1)), r8, r9, r10, r11, r12, r13, r14, r15⟩, ⟨z0, z1, z2, z3, z4, z5, z6, y7, y8, Vec256.zero, gf256Avx2Mask, gf256Avx2Reduction, gf256Avx2Table gfniTowerToRijndaelMat false, gf256Avx2Table gfniTowerToRijndaelMat true, gf256Avx2Table gfniRijndaelToTowerMat false, gf256Avx2Table gfniRijndaelToTowerMat true⟩, cf', o', zf', true, false,
          gf256MulGfniIterMem (k + 1) m r7 r6 r2⟩ := by
  induction k generalizing r2 r6 r7 y0 y1 y2 y3 y4 y5 y6 cf o zf m with
  | zero =>
    obtain ⟨z0,z1,z2,z3,z4,z5,z6,hIter⟩ := gf256MulAvx2_body r0 (UInt64.ofNat 1)
      r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 y0 y1 y2 y3 y4 y5 y6 y7 y8 cf o zf m
    have h1 : UInt64.ofNat 1 - 1 = 0 := by decide +kernel
    rw [h1, u64_zero_beq_zero] at hIter
    exact ⟨z0,z1,z2,z3,z4,z5,z6,_,_,_,hIter⟩
  | succ j ih =>
    have hDec : UInt64.ofNat (j + 1 + 1) - 1 = UInt64.ofNat (j + 1) := by
      apply UInt64.eq_of_toBitVec_eq
      apply BitVec.eq_of_toNat_eq
      have hlt2 : j + 1 < 0x10000000000000000 := by omega
      simp [UInt64.toNat_toBitVec, Nat.mod_eq_of_lt hlt2]
    have hNz : (UInt64.ofNat (j + 1) == 0) = false := by
      cases h : UInt64.ofNat (j + 1) == 0
      · rfl
      · have hn := congrArg UInt64.toNat (beq_iff_eq.mp h)
        have hlt : j + 1 < 0x10000000000000000 := by omega
        rw [show (UInt64.ofNat (j + 1)).toNat = j + 1 from Nat.mod_eq_of_lt hlt] at hn
        exact absurd hn (Nat.succ_ne_zero j)
    obtain ⟨z0,z1,z2,z3,z4,z5,z6,hIter⟩ := gf256MulAvx2_body r0 (UInt64.ofNat (j + 1 + 1))
      r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 y0 y1 y2 y3 y4 y5 y6 y7 y8 cf o zf m
    rw [hDec, hNz] at hIter
    rw [show jccPc (!false) 56 402 = 56 from rfl] at hIter
    obtain ⟨w0,w1,w2,w3,w4,w5,w6,cf',o',zf',hRest⟩ := ih (by omega) (r2 + 32) (r6 + 32) (r7 + 32)
      z0 z1 z2 z3 z4 z5 z6
      (decide (r7.toNat + (32 : UInt64).toNat ≥ 0x10000000000000000))
      (evalX86IncDecOf false true (UInt64.ofNat (j + 1 + 1))) false (gf256MulGfniStepMem m r7 r6 r2)
    have hComb := ExecReachesX86_trans hIter hRest
    have hStepEq : 84 + (84 + 84 * j) = 84 + 84 * (j + 1) := by omega
    have hAddPtr : ∀ p : UInt64, (p + 32) + UInt64.ofNat (32 * (j + 1)) = p + UInt64.ofNat (32 * (j + 1 + 1)) := by
      intro p
      apply UInt64.eq_of_toBitVec_eq
      simp only [UInt64.toBitVec_add, BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp [UInt64.toNat_toBitVec]
      omega
    rw [hStepEq, hAddPtr r2, hAddPtr r6, hAddPtr r7] at hComb
    exact ⟨w0,w1,w2,w3,w4,w5,w6,cf',o',zf',hComb⟩


private theorem gf256MulAvx2_reaches_full (k : Nat) (hk : k + 1 < 0x10000000000000000)
    (r0 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Vec256)
    (cf o zf dy : Bool) (m : UInt64 → UInt8) (ht : gf256MulAvx2Tables m r8) :
    ExecReachesX86 gf256MulAvx2Prog (120 + 84 * k)
      ⟨0, ⟨r0, UInt64.ofNat (k + 1), r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩, cf, o, zf, dy, false, m⟩
      ⟨490, ⟨0, 0, 0, r3, r4, r5, 0, 0, 0, 0, 0, 0, r12, r13, r14, r15⟩, Bank16.const Vec256.zero,
        false, false, true, false, false, gf256MulGfniIterMem (k + 1) m r7 r6 r2⟩ := by
  rcases ht with ⟨ht0, ht1, ht2, ht3⟩
  have hMask : maskGprWidth false 15 = 15 := by decide +kernel
  have hRed : maskGprWidth false 27 = 27 := by decide +kernel
  have hMaskB : mapBytes64 (fun _ => (15 : UInt64).toUInt8) = 0x0f0f0f0f0f0f0f0f := by decide +kernel
  have hRedB : mapBytes64 (fun _ => (27 : UInt64).toUInt8) = 0x1b1b1b1b1b1b1b1b := by decide +kernel
  have hXor (v : Vec256) : evalVecBin256 .vpxor v v = Vec256.zero := by
    cases v; simp [evalVecBin256, Vec256.zero]
  have hPrologue : StepsX86 gf256MulAvx2Prog 11
      ⟨0, ⟨r0, UInt64.ofNat (k + 1), r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩, cf, o, zf, dy, false, m⟩
      ⟨56, ⟨27, UInt64.ofNat (k + 1), r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, Vec256.zero, gf256Avx2Mask, gf256Avx2Reduction, gf256Avx2Table gfniTowerToRijndaelMat false, gf256Avx2Table gfniTowerToRijndaelMat true, gf256Avx2Table gfniRijndaelToTowerMat false, gf256Avx2Table gfniRijndaelToTowerMat true⟩, cf, o, zf, true, false, m⟩ := by
    iterate 11
      apply StepsX86.cons rfl rfl
      · simp only [stepX86, evalX86Addr, clampVecWidth, u64_add_zero,
          Bank16.get, Bank16.set, Bool.or_true, ↓reduceIte,
          hMask, hRed, hMaskB, hRedB, hXor, ht0, ht1, ht2, ht3]
        rfl
    exact StepsX86.zero _
  obtain ⟨z0,z1,z2,z3,z4,z5,z6,cf',o',zf',hLoop⟩ := gf256MulAvx2_loop_steps k hk 27
    r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
    y0 y1 y2 y3 y4 y5 y6 y7 y8 cf o zf m
  have hTail : StepsX86 gf256MulAvx2Prog 25
      ⟨402, ⟨27, 0, r2 + UInt64.ofNat (32 * (k + 1)), r3, r4, r5, r6 + UInt64.ofNat (32 * (k + 1)), r7 + UInt64.ofNat (32 * (k + 1)), r8, r9, r10, r11, r12, r13, r14, r15⟩, ⟨z0, z1, z2, z3, z4, z5, z6, y7, y8, Vec256.zero, gf256Avx2Mask, gf256Avx2Reduction, gf256Avx2Table gfniTowerToRijndaelMat false, gf256Avx2Table gfniTowerToRijndaelMat true, gf256Avx2Table gfniRijndaelToTowerMat false, gf256Avx2Table gfniRijndaelToTowerMat true⟩,
        cf', o', zf', true, false, gf256MulGfniIterMem (k + 1) m r7 r6 r2⟩
      ⟨490, ⟨0, 0, 0, r3, r4, r5, 0, 0, 0, 0, 0, 0, r12, r13, r14, r15⟩, Bank16.const Vec256.zero,
        false, false, true, false, false, gf256MulGfniIterMem (k + 1) m r7 r6 r2⟩ := by
    iterate 13
      apply StepsX86.cons rfl rfl
      · simp only [stepX86, clampVecWidth, hXor]
        rfl
    iterate 12
      apply StepsX86.cons rfl rfl
      · simp only [current_vzeroall_step, current_vzeroupper_zero_step, stepX86_xorRR,
          mask32_xor_self, u64_zero_beq_zero,
          b16set_0, b16set_1, b16set_2, b16set_6, b16set_7,
          b16set_8, b16set_9, b16set_10, b16set_11]
        rfl
    exact StepsX86.zero _
  have hComb := ExecReachesX86_trans (ExecReachesX86_trans hPrologue.toExecReaches hLoop) hTail.toExecReaches
  have hN : (11 + (84 + 84 * k)) + 25 = 120 + 84 * k := by omega
  rw [hN] at hComb
  exact hComb


theorem current_gf256_shamir_mul_avx2_loop_functional
    (k : Nat) (s : X86State)
    (hk : 32 * (k + 1) ≤ 0x10000000000000000)
    (hpc : s.pc = 0) (hh : s.halted = false)
    (hc : s.gpr.get 1 = UInt64.ofNat (k + 1))
    (hDisjA : ∀ i j : Nat, i < 32 * (k + 1) → j < 32 * (k + 1) →
      s.gpr.get 7 + UInt64.ofNat i ≠ s.gpr.get 6 + UInt64.ofNat j)
    (hDisjB : ∀ i j : Nat, i < 32 * (k + 1) → j < 32 * (k + 1) →
      s.gpr.get 7 + UInt64.ofNat i ≠ s.gpr.get 2 + UInt64.ofNat j)
    (hTables : gf256MulAvx2Tables s.mem (s.gpr.get 8)) :
    ∃ slice prog, findSliceByNameBytes currentX86ExtractedSlices
      gf256MulAvx2Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ extra : Nat,
        let result := runX86 prog (121 + 84 * k + extra) s
        result.1.halted = true ∧ result.1.pc = (readMem64 result.1.mem (s.gpr.get 4)).toNat ∧
        result.2.length = 121 + 84 * k ∧ result.1.ymmDirty = false ∧
        result.1.ymm = Bank16.const Vec256.zero ∧
        (∀ idx : Nat, idx < 32 * (k + 1) →
          Simulates 3
            (towerMul 3 (unpackTower 3 (s.mem (s.gpr.get 6 + UInt64.ofNat idx)).toBitVec)
              (unpackTower 3 (s.mem (s.gpr.get 2 + UInt64.ofNat idx)).toBitVec))
            (result.1.mem (s.gpr.get 7 + UInt64.ofNat idx)).toBitVec) ∧
        (∀ a : UInt64, (∀ idx : Nat, idx < 32 * (k + 1) →
          a ≠ s.gpr.get 7 + UInt64.ofNat idx) → result.1.mem a = s.mem a) := by
  obtain ⟨slice, hf, hd⟩ := gf256MulAvx2_fresh_decode
  refine ⟨slice, gf256MulAvx2Prog, hf, hd, ?_⟩
  rcases s with ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
    ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
    cf, o, zf, dy, hlt, mem⟩
  dsimp only at hpc hh; subst hpc hh
  have hr1 : r1 = UInt64.ofNat (k + 1) := hc
  subst hr1
  have hR := gf256MulAvx2_reaches_full k (by omega)
    r0 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
    y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 cf o zf dy mem hTables
  obtain ⟨_, _, hPost⟩ := ExecReachesX86_ret hR rfl (show
    findInstrAtPc 490 gf256MulAvx2Prog = some ⟨490, 1, .ret⟩ from rfl)
  intro extra
  have hRun := (hPost extra).1
  have hLen := (hPost extra).2
  have hN : 120 + 84 * k + 1 = 121 + 84 * k := by omega
  rw [hN] at hRun hLen
  dsimp only
  rw [hRun, hLen]
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro idx hidx
    dsimp only
    simp only [b16get_7, b16get_6, b16get_2]
    rw [gf256MulGfniIterMem_at (k + 1) mem r7 r6 r2 hk hDisjA hDisjB idx hidx]
    exact gfniTowerMulByte_simulates_binaryTower _ _
  · intro a ha
    exact gf256MulGfniIterMem_outside (k + 1) mem r7 r6 r2 a hk ha


/-- Concrete static-table bytes, plus unit-valued input and accumulator buffers. -/
def gf256Avx2WitnessMem (a : UInt64) : UInt8 :=
  if a.toNat < 32 then
    gfniAffineByte (UInt8.ofNat (a.toNat % 16)) gfniTowerToRijndaelMat 0
  else if a.toNat < 64 then
    gfniAffineByte (UInt8.ofNat (a.toNat % 16) <<< 4) gfniTowerToRijndaelMat 0
  else if a.toNat < 96 then
    gfniAffineByte (UInt8.ofNat (a.toNat % 16)) gfniRijndaelToTowerMat 0
  else if a.toNat < 128 then
    gfniAffineByte (UInt8.ofNat (a.toNat % 16) <<< 4) gfniRijndaelToTowerMat 0
  else if a.toNat < 144 then UInt8.ofNat (a.toNat - 128)
  else if a.toNat < 160 then UInt8.ofNat (a.toNat - 144) <<< 4
  else 1

def gf256MulAvx2WitnessState : X86State :=
  ⟨0, ⟨0, 1, 320, 0, 0, 0, 256, 384, 0, 0, 0, 0, 0, 0, 0, 0⟩,
    Bank16.const Vec256.zero, false, false, false, false, false, gf256Avx2WitnessMem⟩

theorem gf256MulAvx2Witness_tables : gf256MulAvx2Tables gf256Avx2WitnessMem 0 := by
  unfold gf256MulAvx2Tables
  decide +kernel

private theorem gf256MulAvx2Witness_disjointA :
    ∀ i j : Nat, i < 32 → j < 32 → (384 : UInt64) + UInt64.ofNat i ≠ 256 + UInt64.ofNat j := by
  intro i j hi hj heq
  have h := congrArg UInt64.toNat heq
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat'] at h
  change (384 + i % 18446744073709551616) % 18446744073709551616 =
    (256 + j % 18446744073709551616) % 18446744073709551616 at h
  omega

private theorem gf256MulAvx2Witness_disjointB :
    ∀ i j : Nat, i < 32 → j < 32 → (384 : UInt64) + UInt64.ofNat i ≠ 320 + UInt64.ofNat j := by
  intro i j hi hj heq
  have h := congrArg UInt64.toNat heq
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat'] at h
  change (384 + i % 18446744073709551616) % 18446744073709551616 =
    (320 + j % 18446744073709551616) % 18446744073709551616 at h
  omega

theorem gf256MulAvx2_inhabited :
    ∃ k : Nat, ∃ s : X86State,
      32 * (k + 1) ≤ 0x10000000000000000 ∧
      s.pc = 0 ∧ s.halted = false ∧ s.gpr.get 1 = UInt64.ofNat (k + 1) ∧
      (∀ i j : Nat, i < 32 * (k + 1) → j < 32 * (k + 1) →
        s.gpr.get 7 + UInt64.ofNat i ≠ s.gpr.get 6 + UInt64.ofNat j) ∧
      (∀ i j : Nat, i < 32 * (k + 1) → j < 32 * (k + 1) →
        s.gpr.get 7 + UInt64.ofNat i ≠ s.gpr.get 2 + UInt64.ofNat j) ∧
      gf256MulAvx2Tables s.mem (s.gpr.get 8) := by
  exact ⟨0, gf256MulAvx2WitnessState, by decide, rfl, rfl, rfl,
    gf256MulAvx2Witness_disjointA, gf256MulAvx2Witness_disjointB, gf256MulAvx2Witness_tables⟩

/-- Refutes replacing tower multiplication with byte XOR on the fresh multiply symbol. -/
theorem gf256MulAvx2_xor_tooth :
    ∃ slice prog, findSliceByNameBytes currentX86ExtractedSlices gf256MulAvx2Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      (runX86 prog 121 gf256MulAvx2WitnessState).1.mem 384 ≠
        (gf256MulAvx2WitnessState.mem 256 ^^^ gf256MulAvx2WitnessState.mem 320) := by
  obtain ⟨slice, prog, hf, hd, hfun⟩ := current_gf256_shamir_mul_avx2_loop_functional
    0 gf256MulAvx2WitnessState (by decide) rfl rfl rfl
    gf256MulAvx2Witness_disjointA gf256MulAvx2Witness_disjointB gf256MulAvx2Witness_tables
  refine ⟨slice, prog, hf, hd, ?_⟩
  have hb := (hfun 0).2.2.2.2.2.1 0 (by decide)
  change Simulates 3 (towerMul 3 (unpackTower 3 (1 : UInt8).toBitVec)
    (unpackTower 3 (1 : UInt8).toBitVec))
    ((runX86 prog 121 gf256MulAvx2WitnessState).1.mem 384).toBitVec at hb
  have hone : ((runX86 prog 121 gf256MulAvx2WitnessState).1.mem 384).toBitVec = 1#8 :=
    (elfSimulates_pack_eq hb).symm.trans (by
      simp only [unpackTower, packTower, towerAdd, towerMul, lowBits.public_eq_1, highBits.public_eq_1, joinBits_eq_append]
      decide +kernel)
  intro heq
  have hzero := congrArg UInt8.toBitVec heq
  rw [hone] at hzero
  exact (by decide : (1#8 : BitVec 8) ≠ ((1 : UInt8) ^^^ 1).toBitVec) hzero

#tooth_pair current_gf256_shamir_mul_avx2_loop_functional vs gf256MulAvx2_xor_tooth
#verify_inhabited current_gf256_shamir_mul_avx2_loop_functional gf256MulAvx2_inhabited


end

section
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def gf256MacAvx2Basis : Vec256 :=
  ⟨mapBytes64 (fun i => UInt8.ofNat i), mapBytes64 (fun i => UInt8.ofNat (i + 8)),
   mapBytes64 (fun i => UInt8.ofNat i <<< 4), mapBytes64 (fun i => UInt8.ofNat (i + 8) <<< 4)⟩

def gf256MacAvx2Table (scalar : UInt64) (high : Bool) : Vec256 :=
  let f := fun i => gfniTowerMulByte (if high then UInt8.ofNat i <<< 4 else UInt8.ofNat i)
    (maskGprWidth false scalar).toUInt8
  let lo := mapBytes64 f
  let hi := mapBytes64 (fun i => f (i + 8))
  ⟨lo, hi, lo, hi⟩

private theorem gf256MacAvx2_table_w2 (scalar : UInt64) (high : Bool) :
    (gf256MacAvx2Table scalar high).w2 = (gf256MacAvx2Table scalar high).w0 := rfl

private theorem gf256MacAvx2_table_w3 (scalar : UInt64) (high : Bool) :
    (gf256MacAvx2Table scalar high).w3 = (gf256MacAvx2Table scalar high).w1 := rfl

private theorem gf256MacAvx2_mul_comm (a b : UInt8) : gfniTowerMulByte a b = gfniTowerMulByte b a := by
  apply UInt8.eq_of_toBitVec_eq
  rw [gfniTowerMulByte_eq_mulExec, gfniTowerMulByte_eq_mulExec,
    mulExec_eq_pack_towerMul, mulExec_eq_pack_towerMul, towerMul_comm]

/-- The exact low/high half replication done by `vperm2i128` immediates 0/17. -/
theorem gf256MacAvx2_synthesized_tables (scalar : UInt64) :
    let v := gf256MulAvx2Vec (gf256MacGfniBroadcast scalar) gf256MacAvx2Basis
    (⟨v.w0, v.w1, v.w0, v.w1⟩ : Vec256) = gf256MacAvx2Table scalar false ∧
    (⟨v.w2, v.w3, v.w2, v.w3⟩ : Vec256) = gf256MacAvx2Table scalar true := by
  dsimp only
  rw [gf256MulAvx2Vec_eq]
  have h (r : Nat) (hr : r < 8) :=
    gf256MulGfniVec_lane_byte (gf256MacGfniBroadcast scalar) gf256MacAvx2Basis r hr
  constructor <;> apply gf256Avx2_ext <;> apply gf256Avx2_byte_ext <;> intro r hr
  all_goals
    have h0 := h r hr
    simp only [gf256MacGfniBroadcast, gf256MacAvx2Basis, getByte64_mapBytes64 _ r hr] at h0
    simp only [gf256MacAvx2Table, gf256MacGfniBroadcast, gf256MacAvx2Basis,
      getByte64_mapBytes64 _ r hr, Bool.false_eq_true, ↓reduceIte]
    first
    | rw [h0.1, gf256MacAvx2_mul_comm]
    | rw [h0.2.1, gf256MacAvx2_mul_comm]
    | rw [h0.2.2.1, gf256MacAvx2_mul_comm]
    | rw [h0.2.2.2, gf256MacAvx2_mul_comm]

private theorem gf256MacAvx2_nibble_pick (scalar : UInt64) (high : Bool) (x : UInt8)
    (hx : x.toNat < 16) :
    (if (x &&& 0x80) != 0 then 0 else
      if (x &&& 15).toNat < 8 then
        getByte64 (gf256MacAvx2Table scalar high).w0 (x &&& 15).toNat
      else getByte64 (gf256MacAvx2Table scalar high).w1 ((x &&& 15).toNat - 8)) =
      gfniTowerMulByte (if high then x <<< 4 else x) (maskGprWidth false scalar).toUInt8 := by
  have hz : (x &&& 0x80) = 0 := by
    rcases x with ⟨⟨n⟩⟩; revert hx n; decide +kernel
  have hm : x &&& 15 = x := by
    rcases x with ⟨⟨n⟩⟩; revert hx n; decide +kernel
  simp only [hz, hm, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  by_cases hl : x.toNat < 8
  · rw [ite_eq_left hl]
    simp only [gf256MacAvx2Table, getByte64_mapBytes64 _ x.toNat hl, UInt8.ofNat_toNat]
  · rw [ite_eq_right hl]
    simp only [gf256MacAvx2Table, getByte64_mapBytes64 _ (x.toNat - 8) (by omega)]
    rw [show x.toNat - 8 + 8 = x.toNat by omega, UInt8.ofNat_toNat]


private theorem gf256MacAvx2_split (scalar : UInt64) (x : UInt8) :
    gfniTowerMulByte (x &&& 15) (maskGprWidth false scalar).toUInt8 ^^^
      gfniTowerMulByte (((x >>> 4) &&& 15) <<< 4) (maskGprWidth false scalar).toUInt8 =
        gfniTowerMulByte x (maskGprWidth false scalar).toUInt8 := by
  rw [← gfniTowerMulByte_xor_left]
  have h : (x &&& (15 : UInt8)) ^^^ (((x >>> 4) &&& (15 : UInt8)) <<< 4) = x := by
    rcases x with ⟨⟨n⟩⟩; revert n; decide +kernel
  rw [h]

theorem gf256MacAvx2_lookup_eq (scalar : UInt64) (v : Vec256) :
    gf256Avx2Convert (gf256MacAvx2Table scalar false) (gf256MacAvx2Table scalar true) v =
      gf256MulGfniVec v (gf256MacGfniBroadcast scalar) := by
  have h (r : Nat) (hr : r < 8) := gf256MulGfniVec_lane_byte v (gf256MacGfniBroadcast scalar) r hr
  apply gf256Avx2_ext <;> apply gf256Avx2_byte_ext <;> intro i hi
  all_goals
    have hb := h i hi
    simp only [gf256MacGfniBroadcast, getByte64_mapBytes64 _ i hi] at hb
    simp only [gf256MacGfniBroadcast]
    first | rw [hb.1] | rw [hb.2.1] | rw [hb.2.2.1] | rw [hb.2.2.2]
    simp only [gf256Avx2Convert, evalVecBin256, evalVecShift256, gf256Avx2Mask,
      gf256MacGfni_getByte_xor _ _ i hi, getByte64_mapBytes64 _ i hi, gf256Avx2_shift4_word,
      gf256Avx2_low_byte _ i hi, gf256Avx2_high_byte_masked _ i hi,
      gf256MacAvx2_table_w2, gf256MacAvx2_table_w3]
    rw [gf256MacAvx2_nibble_pick scalar false _ (gf256Avx2_nibble_bound _).1,
      gf256MacAvx2_nibble_pick scalar true _ (gf256Avx2_nibble_bound _).2]
    simpa only [Bool.false_eq_true, Bool.true_eq, ↓reduceIte] using gf256MacAvx2_split scalar (getByte64 _ i)


def gf256MacAvx2Vec (scalar : UInt64) (share acc : Vec256) : Vec256 :=
  let lo := evalVecBin256 .vpshufb (gf256MacAvx2Table scalar false)
    (evalVecBin256 .vpand gf256Avx2Mask share)
  let hi := evalVecBin256 .vpshufb (gf256MacAvx2Table scalar true)
    (evalVecBin256 .vpand gf256Avx2Mask (evalVecShift256 .vpsrlw share 4))
  evalVecBin256 .vpxor (evalVecBin256 .vpxor acc lo) hi

theorem gf256MacAvx2Vec_eq (scalar : UInt64) (share acc : Vec256) :
    gf256MacAvx2Vec scalar share acc = gf256MacGfniVec share acc scalar := by
  have hassoc (a b c : Vec256) :
      evalVecBin256 .vpxor (evalVecBin256 .vpxor a b) c =
        evalVecBin256 .vpxor a (evalVecBin256 .vpxor b c) := by
    apply gf256Avx2_ext <;> apply UInt64.eq_of_toBitVec_eq <;>
      simp only [evalVecBin256, UInt64.toBitVec_xor, BitVec.xor_assoc]
  unfold gf256MacAvx2Vec
  rw [hassoc]
  change evalVecBin256 .vpxor acc (gf256Avx2Convert
    (gf256MacAvx2Table scalar false) (gf256MacAvx2Table scalar true) share) = _
  rw [gf256MacAvx2_lookup_eq]
  rfl


end

section
set_option maxRecDepth 10000
set_option maxHeartbeats 0

def gf256MacAvx2Tables (mem : UInt64 → UInt8) (base : UInt64) : Prop :=
  gf256MulAvx2Tables mem base ∧ readMem256 mem (base + 128) = gf256MacAvx2Basis

/-- The scalar-product tables synthesized from exactly the five public vectors loaded by MAC. -/
theorem gf256MacAvx2_table_bytes_refine (mem : UInt64 → UInt8) (base scalar : UInt64)
    (ht : gf256MacAvx2Tables mem base) :
    let v := gf256Avx2Convert (readMem256 mem (base + 64)) (readMem256 mem (base + 96))
      (gf256Avx2HornerVec
        (gf256Avx2Convert (readMem256 mem base) (readMem256 mem (base + 32))
          (gf256MacGfniBroadcast scalar))
        (gf256Avx2Convert (readMem256 mem base) (readMem256 mem (base + 32))
          (readMem256 mem (base + 128))))
    (⟨v.w0,v.w1,v.w0,v.w1⟩ : Vec256) = gf256MacAvx2Table scalar false ∧
      (⟨v.w2,v.w3,v.w2,v.w3⟩ : Vec256) = gf256MacAvx2Table scalar true := by
  rcases ht with ⟨⟨ht0,ht1,ht2,ht3⟩,ht4⟩
  rw [ht0,ht1,ht2,ht3,ht4]
  exact gf256MacAvx2_synthesized_tables scalar

private theorem gf256MacAvx2_body
    (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y0 y1 y2 y3 y4 y5 y6 : Vec256)
    (cf o zf : Bool) (m : UInt64 → UInt8) :
    ∃ z0 z1 z2 z3 : Vec256,
      StepsX86 gf256MacAvx2Prog 14
        ⟨399, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, ⟨y0, y1, y2, y3, y4, y5, y6, gf256MacAvx2Table r2 false, gf256MacAvx2Table r2 true, Vec256.zero, gf256Avx2Mask, gf256Avx2Reduction, gf256Avx2Table gfniTowerToRijndaelMat false, gf256Avx2Table gfniTowerToRijndaelMat true, gf256Avx2Table gfniRijndaelToTowerMat false, gf256Avx2Table gfniRijndaelToTowerMat true⟩, cf, o, zf, true, false, m⟩
        ⟨jccPc (!((r1 - 1) == 0)) 399 455, ⟨r0, r1 - 1, r2, r3, r4, r5, r6 + 32, r7 + 32, r8, r9, r10, r11, r12, r13, r14, r15⟩, ⟨z0, z1, z2, z3, y4, y5, y6, gf256MacAvx2Table r2 false, gf256MacAvx2Table r2 true, Vec256.zero, gf256Avx2Mask, gf256Avx2Reduction, gf256Avx2Table gfniTowerToRijndaelMat false, gf256Avx2Table gfniTowerToRijndaelMat true, gf256Avx2Table gfniRijndaelToTowerMat false, gf256Avx2Table gfniRijndaelToTowerMat true⟩,
          decide (r7.toNat + (32 : UInt64).toNat ≥ 0x10000000000000000),
          evalX86IncDecOf false true r1, (r1 - 1) == 0, true, false,
          gf256MacGfniStepMem m r7 r6 r2⟩ := by
  unfold gf256MacGfniStepMem
  rw [← gf256MacAvx2Vec_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  rotate_left 4
  iterate 10
    apply StepsX86.cons rfl rfl
    · simp only [stepX86, evalX86Addr, clampVecWidth, u64_add_zero,
        b16get_6, b16get_7]
      rfl
  iterate 2
    apply StepsX86.cons rfl rfl
    · rw [stepX86_addImm64]
  apply StepsX86.cons rfl rfl
  · rw [stepX86_dec64]
  apply StepsX86.cons rfl rfl
  · rw [stepX86_jnz]
  exact StepsX86.zero _

private theorem gf256MacAvx2_loop_steps (k : Nat) (hk : k + 1 < 0x10000000000000000)
    (r0 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y0 y1 y2 y3 y4 y5 y6 : Vec256)
    (cf o zf : Bool) (m : UInt64 → UInt8) :
    ∃ z0 z1 z2 z3 : Vec256, ∃ cf' o' zf',
      StepsX86 gf256MacAvx2Prog (14 + 14 * k)
        ⟨399, ⟨r0, UInt64.ofNat (k + 1), r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, ⟨y0, y1, y2, y3, y4, y5, y6, gf256MacAvx2Table r2 false, gf256MacAvx2Table r2 true, Vec256.zero, gf256Avx2Mask, gf256Avx2Reduction, gf256Avx2Table gfniTowerToRijndaelMat false, gf256Avx2Table gfniTowerToRijndaelMat true, gf256Avx2Table gfniRijndaelToTowerMat false, gf256Avx2Table gfniRijndaelToTowerMat true⟩, cf, o, zf, true, false, m⟩
        ⟨455, ⟨r0, 0, r2, r3, r4, r5, r6 + UInt64.ofNat (32 * (k + 1)), r7 + UInt64.ofNat (32 * (k + 1)), r8, r9, r10, r11, r12, r13, r14, r15⟩, ⟨z0, z1, z2, z3, y4, y5, y6, gf256MacAvx2Table r2 false, gf256MacAvx2Table r2 true, Vec256.zero, gf256Avx2Mask, gf256Avx2Reduction, gf256Avx2Table gfniTowerToRijndaelMat false, gf256Avx2Table gfniTowerToRijndaelMat true, gf256Avx2Table gfniRijndaelToTowerMat false, gf256Avx2Table gfniRijndaelToTowerMat true⟩, cf', o', zf', true, false,
          gf256MacGfniIterMem (k + 1) m r7 r6 r2⟩ := by
  induction k generalizing r6 r7 y0 y1 y2 y3 cf o zf m with
  | zero =>
    obtain ⟨z0,z1,z2,z3,hIter⟩ := gf256MacAvx2_body r0 (UInt64.ofNat 1)
      r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 y0 y1 y2 y3 y4 y5 y6 cf o zf m
    have h1 : UInt64.ofNat 1 - 1 = 0 := by decide +kernel
    rw [h1, u64_zero_beq_zero] at hIter
    exact ⟨z0,z1,z2,z3,_,_,_,hIter⟩
  | succ j ih =>
    have hDec : UInt64.ofNat (j + 1 + 1) - 1 = UInt64.ofNat (j + 1) := by
      apply UInt64.eq_of_toBitVec_eq
      apply BitVec.eq_of_toNat_eq
      have hlt2 : j + 1 < 0x10000000000000000 := by omega
      simp [UInt64.toNat_toBitVec, Nat.mod_eq_of_lt hlt2]
    have hNz : (UInt64.ofNat (j + 1) == 0) = false := by
      cases h : UInt64.ofNat (j + 1) == 0
      · rfl
      · have hn := congrArg UInt64.toNat (beq_iff_eq.mp h)
        have hlt : j + 1 < 0x10000000000000000 := by omega
        rw [show (UInt64.ofNat (j + 1)).toNat = j + 1 from Nat.mod_eq_of_lt hlt] at hn
        exact absurd hn (Nat.succ_ne_zero j)
    obtain ⟨z0,z1,z2,z3,hIter⟩ := gf256MacAvx2_body r0 (UInt64.ofNat (j + 1 + 1))
      r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 y0 y1 y2 y3 y4 y5 y6 cf o zf m
    rw [hDec, hNz] at hIter
    rw [show jccPc (!false) 399 455 = 399 from rfl] at hIter
    obtain ⟨w0,w1,w2,w3,cf',o',zf',hRest⟩ := ih (by omega) (r6 + 32) (r7 + 32)
      z0 z1 z2 z3
      (decide (r7.toNat + (32 : UInt64).toNat ≥ 0x10000000000000000))
      (evalX86IncDecOf false true (UInt64.ofNat (j + 1 + 1))) false (gf256MacGfniStepMem m r7 r6 r2)
    have hComb := StepsX86_trans hIter hRest
    have hStepEq : 14 + (14 + 14 * j) = 14 + 14 * (j + 1) := by omega
    have hAddPtr : ∀ p : UInt64, (p + 32) + UInt64.ofNat (32 * (j + 1)) = p + UInt64.ofNat (32 * (j + 1 + 1)) := by
      intro p
      apply UInt64.eq_of_toBitVec_eq
      simp only [UInt64.toBitVec_add, BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp [UInt64.toNat_toBitVec]
      omega
    rw [hStepEq, hAddPtr r6, hAddPtr r7] at hComb
    exact ⟨w0,w1,w2,w3,cf',o',zf',hComb⟩


private theorem gf256MacAvx2_rounds_preserved (j : Nat) (hj : j < 7) :
    progPreservesNonRet (gf256Avx2RoundProg (136+32*j)) gf256MacAvx2Prog = true := by
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ => decide +kernel
  | n+7, h => omega

private theorem gf256MacAvx2_prefix (k : Nat)
    (r0 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Vec256)
    (cf o zf dy : Bool) (m : UInt64 → UInt8) (ht : gf256MacAvx2Tables m r8) :
    ∃ z0 z1 z2 z3 z4 z5 z6 : Vec256,
      ExecReachesX86 gf256MacAvx2Prog 92
        ⟨0, ⟨r0, UInt64.ofNat (k + 1), r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩, cf, o, zf, dy, false, m⟩
        ⟨399, ⟨27, UInt64.ofNat (k + 1), r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
          ⟨z0, z1, z2, z3, z4, z5, z6, gf256MacAvx2Table r2 false, gf256MacAvx2Table r2 true, Vec256.zero, gf256Avx2Mask, gf256Avx2Reduction, gf256Avx2Table gfniTowerToRijndaelMat false, gf256Avx2Table gfniTowerToRijndaelMat true, gf256Avx2Table gfniRijndaelToTowerMat false, gf256Avx2Table gfniRijndaelToTowerMat true⟩, cf, o, zf, true, false, m⟩ := by
  rcases ht with ⟨⟨ht0, ht1, ht2, ht3⟩, ht4⟩
  have hMask : maskGprWidth false 15 = 15 := by decide +kernel
  have hRed : maskGprWidth false 27 = 27 := by decide +kernel
  have hMaskB : mapBytes64 (fun _ => (15 : UInt64).toUInt8) = 0x0f0f0f0f0f0f0f0f := by decide +kernel
  have hRedB : mapBytes64 (fun _ => (27 : UInt64).toUInt8) = 0x1b1b1b1b1b1b1b1b := by decide +kernel
  have hXor (v : Vec256) : evalVecBin256 .vpxor v v = Vec256.zero := by
    cases v; simp [evalVecBin256, Vec256.zero]
  let a := gf256Avx2Convert (gf256Avx2Table gfniTowerToRijndaelMat false)
    (gf256Avx2Table gfniTowerToRijndaelMat true) (gf256MacGfniBroadcast r2)
  let b := gf256Avx2Convert (gf256Avx2Table gfniTowerToRijndaelMat false)
    (gf256Avx2Table gfniTowerToRijndaelMat true) gf256MacAvx2Basis
  let bLo := evalVecBin256 .vpshufb (gf256Avx2Table gfniTowerToRijndaelMat false)
    (evalVecBin256 .vpand gf256Avx2Mask gf256MacAvx2Basis)
  let bHi := evalVecBin256 .vpshufb (gf256Avx2Table gfniTowerToRijndaelMat true)
    (evalVecBin256 .vpand gf256Avx2Mask (evalVecShift256 .vpsrlw gf256MacAvx2Basis 4))
  let init := evalVecBin256 .vpand a (gf256Avx2SignVec b)
  have hStart : StepsX86 gf256MacAvx2Prog 28
      ⟨0,⟨r0, UInt64.ofNat (k + 1), r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,cf,o,zf,dy,false,m⟩
      ⟨136,⟨27, UInt64.ofNat (k + 1), r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,⟨a, b, init, bLo, bHi, y5, y6, y7, y8, Vec256.zero, gf256Avx2Mask, gf256Avx2Reduction, gf256Avx2Table gfniTowerToRijndaelMat false, gf256Avx2Table gfniTowerToRijndaelMat true, gf256Avx2Table gfniRijndaelToTowerMat false, gf256Avx2Table gfniRijndaelToTowerMat true⟩,cf,o,zf,true,false,m⟩ := by
    iterate 28
      apply StepsX86.cons rfl rfl
      · simp only [stepX86, evalX86Addr, clampVecWidth, u64_add_zero,
          Bank16.get, Bank16.set, Bool.or_true, ↓reduceIte,
          hMask, hRed, hMaskB, hRedB, hXor, ht0, ht1, ht2, ht3, ht4]
        rfl
    exact StepsX86.zero _
  obtain ⟨z5,z6,hRounds⟩ := gf256Avx2_rounds_reaches gf256MacAvx2Prog 136
    gf256MacAvx2_rounds_preserved 7 0 (by decide) ⟨27, UInt64.ofNat (k + 1), r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩
    a b init bLo bHi y5 y6 y7 y8 gf256Avx2Mask
    (gf256Avx2Table gfniTowerToRijndaelMat false) (gf256Avx2Table gfniTowerToRijndaelMat true)
    (gf256Avx2Table gfniRijndaelToTowerMat false) (gf256Avx2Table gfniRijndaelToTowerMat true) cf o zf m
  let prod := gf256Avx2HornerVec a b
  let outLo := evalVecBin256 .vpshufb (gf256Avx2Table gfniRijndaelToTowerMat false)
    (evalVecBin256 .vpand gf256Avx2Mask prod)
  let outHi := evalVecBin256 .vpshufb (gf256Avx2Table gfniRijndaelToTowerMat true)
    (evalVecBin256 .vpand gf256Avx2Mask (evalVecShift256 .vpsrlw prod 4))
  let out := gf256Avx2Convert (gf256Avx2Table gfniRijndaelToTowerMat false)
    (gf256Avx2Table gfniRijndaelToTowerMat true) prod
  have hTail : StepsX86 gf256MacAvx2Prog 8
      ⟨360,⟨27, UInt64.ofNat (k + 1), r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,⟨a, gf256Avx2Advance 7 b, prod, bLo, bHi, z5, z6, y7, y8, Vec256.zero, gf256Avx2Mask, gf256Avx2Reduction, gf256Avx2Table gfniTowerToRijndaelMat false, gf256Avx2Table gfniTowerToRijndaelMat true, gf256Avx2Table gfniRijndaelToTowerMat false, gf256Avx2Table gfniRijndaelToTowerMat true⟩,cf,o,zf,true,false,m⟩
      ⟨399,⟨27, UInt64.ofNat (k + 1), r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,⟨a, gf256Avx2Advance 7 b, out, outLo, outHi, z5, z6, ⟨out.w0,out.w1,out.w0,out.w1⟩, ⟨out.w2,out.w3,out.w2,out.w3⟩, Vec256.zero, gf256Avx2Mask, gf256Avx2Reduction, gf256Avx2Table gfniTowerToRijndaelMat false, gf256Avx2Table gfniTowerToRijndaelMat true, gf256Avx2Table gfniRijndaelToTowerMat false, gf256Avx2Table gfniRijndaelToTowerMat true⟩,
        cf,o,zf,true,false,m⟩ := by
    iterate 8
      apply StepsX86.cons rfl rfl
      · simp only [stepX86, clampVecWidth]
        rfl
    exact StepsX86.zero _
  have hc := ExecReachesX86_trans (ExecReachesX86_trans hStart.toExecReaches hRounds) hTail.toExecReaches
  have hs := gf256MacAvx2_synthesized_tables r2
  change (⟨out.w0,out.w1,out.w0,out.w1⟩ : Vec256) = gf256MacAvx2Table r2 false ∧
    (⟨out.w2,out.w3,out.w2,out.w3⟩ : Vec256) = gf256MacAvx2Table r2 true at hs
  rw [hs.1,hs.2] at hc
  exact ⟨a,gf256Avx2Advance 7 b,out,outLo,outHi,z5,z6,hc⟩

private theorem gf256MacAvx2_reaches_full (k : Nat) (hk : k + 1 < 0x10000000000000000)
    (r0 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Vec256)
    (cf o zf dy : Bool) (m : UInt64 → UInt8) (ht : gf256MacAvx2Tables m r8) :
    ExecReachesX86 gf256MacAvx2Prog (134 + 14 * k)
      ⟨0, ⟨r0, UInt64.ofNat (k + 1), r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩, cf, o, zf, dy, false, m⟩
      ⟨554, ⟨0, 0, 0, r3, r4, r5, 0, 0, 0, 0, 0, 0, r12, r13, r14, r15⟩, Bank16.const Vec256.zero,
        false, false, true, false, false, gf256MacGfniIterMem (k + 1) m r7 r6 r2⟩ := by
  obtain ⟨z0,z1,z2,z3,z4,z5,z6,hPrefix⟩ := gf256MacAvx2_prefix k
    r0 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
    y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 cf o zf dy m ht
  obtain ⟨w0,w1,w2,w3,cf',o',zf',hLoop⟩ := gf256MacAvx2_loop_steps k hk 27
    r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
    z0 z1 z2 z3 z4 z5 z6 cf o zf m
  have hXor (v : Vec256) : evalVecBin256 .vpxor v v = Vec256.zero := by
    cases v; simp [evalVecBin256, Vec256.zero]
  have hTail : StepsX86 gf256MacAvx2Prog 28
      ⟨455, ⟨27, 0, r2, r3, r4, r5, r6 + UInt64.ofNat (32 * (k + 1)), r7 + UInt64.ofNat (32 * (k + 1)), r8, r9, r10, r11, r12, r13, r14, r15⟩, ⟨w0, w1, w2, w3, z4, z5, z6, gf256MacAvx2Table r2 false, gf256MacAvx2Table r2 true, Vec256.zero, gf256Avx2Mask, gf256Avx2Reduction, gf256Avx2Table gfniTowerToRijndaelMat false, gf256Avx2Table gfniTowerToRijndaelMat true, gf256Avx2Table gfniRijndaelToTowerMat false, gf256Avx2Table gfniRijndaelToTowerMat true⟩,
        cf', o', zf', true, false, gf256MacGfniIterMem (k + 1) m r7 r6 r2⟩
      ⟨554, ⟨0, 0, 0, r3, r4, r5, 0, 0, 0, 0, 0, 0, r12, r13, r14, r15⟩, Bank16.const Vec256.zero,
        false, false, true, false, false, gf256MacGfniIterMem (k + 1) m r7 r6 r2⟩ := by
    iterate 15
      apply StepsX86.cons rfl rfl
      · simp only [stepX86, clampVecWidth, hXor]
        rfl
    iterate 13
      apply StepsX86.cons rfl rfl
      · simp only [current_vzeroall_step, current_vzeroupper_zero_step, stepX86_xorRR,
          mask32_xor_self, u64_zero_beq_zero,
          b16set_0, b16set_1, b16set_2, b16set_6, b16set_7,
          b16set_8, b16set_9, b16set_10, b16set_11]
        rfl
    exact StepsX86.zero _
  have hComb := ExecReachesX86_trans (ExecReachesX86_trans hPrefix hLoop.toExecReaches) hTail.toExecReaches
  have hN : (92 + (14 + 14 * k)) + 28 = 134 + 14 * k := by omega
  rw [hN] at hComb
  exact hComb

theorem current_gf256_shamir_mac_avx2_loop_functional
    (k : Nat) (s : X86State)
    (hk : 32 * (k + 1) ≤ 0x10000000000000000)
    (hpc : s.pc = 0) (hh : s.halted = false)
    (hc : s.gpr.get 1 = UInt64.ofNat (k + 1))
    (hDisj : ∀ i j : Nat, i < 32 * (k + 1) → j < 32 * (k + 1) →
      s.gpr.get 7 + UInt64.ofNat i ≠ s.gpr.get 6 + UInt64.ofNat j)
    (hTables : gf256MacAvx2Tables s.mem (s.gpr.get 8)) :
    ∃ slice prog, findSliceByNameBytes currentX86ExtractedSlices
      gf256MacAvx2Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ extra : Nat,
        let result := runX86 prog (135 + 14 * k + extra) s
        result.1.halted = true ∧ result.1.pc = (readMem64 result.1.mem (s.gpr.get 4)).toNat ∧
        result.2.length = 135 + 14 * k ∧ result.1.ymmDirty = false ∧
        result.1.ymm = Bank16.const Vec256.zero ∧
        (∀ idx : Nat, idx < 32 * (k + 1) →
          Simulates 3
            (towerAdd 3 (unpackTower 3 (s.mem (s.gpr.get 7 + UInt64.ofNat idx)).toBitVec)
              (towerMul 3 (unpackTower 3 (s.mem (s.gpr.get 6 + UInt64.ofNat idx)).toBitVec)
                (unpackTower 3 (maskGprWidth false (s.gpr.get 2)).toUInt8.toBitVec)))
            (result.1.mem (s.gpr.get 7 + UInt64.ofNat idx)).toBitVec) ∧
        (∀ a : UInt64, (∀ idx : Nat, idx < 32 * (k + 1) →
          a ≠ s.gpr.get 7 + UInt64.ofNat idx) → result.1.mem a = s.mem a) := by
  obtain ⟨slice, hf, hd⟩ := gf256MacAvx2_fresh_decode
  refine ⟨slice, gf256MacAvx2Prog, hf, hd, ?_⟩
  rcases s with ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
    ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
    cf, o, zf, dy, hlt, mem⟩
  dsimp only at hpc hh; subst hpc hh
  have hr1 : r1 = UInt64.ofNat (k + 1) := hc
  subst hr1
  have hR := gf256MacAvx2_reaches_full k (by omega)
    r0 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
    y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 cf o zf dy mem hTables
  obtain ⟨_, _, hPost⟩ := ExecReachesX86_ret hR rfl (show
    findInstrAtPc 554 gf256MacAvx2Prog = some ⟨554, 1, .ret⟩ from rfl)
  intro extra
  have hRun := (hPost extra).1
  have hLen := (hPost extra).2
  have hN : 134 + 14 * k + 1 = 135 + 14 * k := by omega
  rw [hN] at hRun hLen
  dsimp only
  rw [hRun, hLen]
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro idx hidx
    dsimp only
    simp only [b16get_7, b16get_6, b16get_2]
    rw [gf256MacGfniIterMem_at (k + 1) mem r7 r6 r2 hk hDisj idx hidx,
      UInt8.toBitVec_xor]
    exact Simulates.add 3 (elfSimulates_unpack 3 _)
      (gfniTowerMulByte_simulates_binaryTower _ _)
  · intro a ha
    exact gf256MacGfniIterMem_outside (k + 1) mem r7 r6 r2 a hk ha


def gf256MacAvx2WitnessState : X86State :=
  ⟨0, ⟨0, 1, 0, 0, 0, 0, 256, 384, 0, 0, 0, 0, 0, 0, 0, 0⟩,
    Bank16.const Vec256.zero, false, false, false, false, false, gf256Avx2WitnessMem⟩

theorem gf256MacAvx2Witness_tables : gf256MacAvx2Tables gf256Avx2WitnessMem 0 := by
  exact ⟨gf256MulAvx2Witness_tables, by decide +kernel⟩

theorem gf256MacAvx2_inhabited :
    ∃ k : Nat, ∃ s : X86State,
      32 * (k + 1) ≤ 0x10000000000000000 ∧
      s.pc = 0 ∧ s.halted = false ∧ s.gpr.get 1 = UInt64.ofNat (k + 1) ∧
      (∀ i j : Nat, i < 32 * (k + 1) → j < 32 * (k + 1) →
        s.gpr.get 7 + UInt64.ofNat i ≠ s.gpr.get 6 + UInt64.ofNat j) ∧
      gf256MacAvx2Tables s.mem (s.gpr.get 8) := by
  exact ⟨0, gf256MacAvx2WitnessState, by decide, rfl, rfl, rfl,
    gf256MulAvx2Witness_disjointA, gf256MacAvx2Witness_tables⟩

theorem gf256MacAvx2_overwrite_tooth :
    ∃ slice prog, findSliceByNameBytes currentX86ExtractedSlices gf256MacAvx2Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      (runX86 prog 135 gf256MacAvx2WitnessState).1.mem 384 ≠
        gfniTowerMulByte (gf256MacAvx2WitnessState.mem 256) 0 := by
  obtain ⟨slice, prog, hf, hd, hfun⟩ := current_gf256_shamir_mac_avx2_loop_functional
    0 gf256MacAvx2WitnessState (by decide) rfl rfl rfl
    gf256MulAvx2Witness_disjointA gf256MacAvx2Witness_tables
  refine ⟨slice, prog, hf, hd, ?_⟩
  have hb := (hfun 0).2.2.2.2.2.1 0 (by decide)
  change Simulates 3 (towerAdd 3 (unpackTower 3 (1 : UInt8).toBitVec)
    (towerMul 3 (unpackTower 3 (1 : UInt8).toBitVec)
      (unpackTower 3 (0 : UInt8).toBitVec)))
    ((runX86 prog 135 gf256MacAvx2WitnessState).1.mem 384).toBitVec at hb
  have hone : ((runX86 prog 135 gf256MacAvx2WitnessState).1.mem 384).toBitVec = 1#8 :=
    (elfSimulates_pack_eq hb).symm.trans (by
      simp only [unpackTower, packTower, towerAdd, towerMul, lowBits.public_eq_1, highBits.public_eq_1, joinBits_eq_append]
      decide +kernel)
  intro heq
  have hzero := congrArg UInt8.toBitVec heq
  rw [hone] at hzero
  exact (by decide : (1#8 : BitVec 8) ≠ (gfniTowerMulByte 1 0).toBitVec) hzero

#tooth_pair current_gf256_shamir_mac_avx2_loop_functional vs gf256MacAvx2_overwrite_tooth
#verify_inhabited current_gf256_shamir_mac_avx2_loop_functional gf256MacAvx2_inhabited


end

end Qsag
end
