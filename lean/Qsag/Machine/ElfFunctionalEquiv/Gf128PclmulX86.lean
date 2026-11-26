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


section Gf128KernelEquivalence

theorem elf_gf128Reduce_zero : gf128Reduce 0 = 0 := by
  have h := gf128Reduce_xor 0 0
  simp only [BitVec.xor_self] at h
  exact h

theorem elf_gf128FieldMul_zero_left (b : BitVec 128) : gf128FieldMul 0#128 b = 0#128 := by
  have h := gf128FieldMul_xor_left 0 0 b
  simp only [BitVec.xor_self] at h
  exact h

theorem elf_gf128Words_one_zero : gf128Words 1 0 = 1#128 := by
  rw [gf128Words.public_eq_1]; decide

theorem elf_gf128Words_zero_zero : gf128Words 0 0 = 0#128 := by
  rw [gf128Words.public_eq_1]; decide

/-- `1 · 1 ≠ 0` for one block of the portable GF(2^128) dot product. -/
theorem elf_gf128_one_block_ne_zero {a0 a1 b0 b1 : UInt64}
    (ha0 : a0 = 1) (ha1 : a1 = 0) (hb0 : b0 = 1) (hb1 : b1 = 0) :
    gf128FieldMul (gf128Words a0 a1) (gf128Words b0 b1) ^^^ (0 : BitVec 128) ≠ 0 := by
  subst ha0 ha1 hb0 hb1
  rw [elf_gf128Words_one_zero, gf128FieldMul_one_one]
  decide

/-- `1 · 1 ⊕ 0 · d ≠ 0` for one two-lane block. -/
theorem elf_gf128_two_lane_block_ne_zero {a0 a1 b0 b1 c0 c1 d0 d1 : UInt64}
    (ha0 : a0 = 1) (ha1 : a1 = 0) (hb0 : b0 = 1) (hb1 : b1 = 0) (hc0 : c0 = 0) (hc1 : c1 = 0) :
    (gf128FieldMul (gf128Words a0 a1) (gf128Words b0 b1) ^^^
      gf128FieldMul (gf128Words c0 c1) (gf128Words d0 d1)) ^^^ (0 : BitVec 128) ≠ 0 := by
  subst ha0 ha1 hb0 hb1 hc0 hc1
  rw [elf_gf128Words_one_zero, gf128FieldMul_one_one, elf_gf128Words_zero_zero,
    elf_gf128FieldMul_zero_left]
  decide

/-- A zero left block contributes zero. -/
theorem elf_gf128_zero_block {a0 a1 b0 b1 : UInt64} (ha0 : a0 = 0) (ha1 : a1 = 0) :
    gf128FieldMul (gf128Words a0 a1) (gf128Words b0 b1) ^^^ (0 : BitVec 128) = 0 := by
  subst ha0 ha1
  rw [elf_gf128Words_zero_zero, elf_gf128FieldMul_zero_left]
  decide

attribute [local irreducible] clmul64

def gf128VpclmulName : List UInt8 := [0x71, 0x73, 0x61, 0x67, 0x5f, 0x61, 0x73, 0x6d, 0x5f, 0x67, 0x66, 0x32, 0x5f, 0x31, 0x32, 0x38, 0x5f, 0x6d, 0x75, 0x6c, 0x5f, 0x61, 0x63, 0x63, 0x5f, 0x76, 0x70, 0x63, 0x6c, 0x6d, 0x75, 0x6c]

def gf128PclmulName : List UInt8 := [0x71, 0x73, 0x61, 0x67, 0x5f, 0x61, 0x73, 0x6d, 0x5f, 0x67, 0x66, 0x32, 0x5f, 0x31, 0x32, 0x38, 0x5f, 0x6d, 0x75, 0x6c, 0x5f, 0x61, 0x63, 0x63, 0x5f, 0x70, 0x63, 0x6c, 0x6d, 0x75, 0x6c]

def gf128PclmulProg : List (DecodedInstr X86Instr) := [
  ⟨0, 4, .vbinOp .vpxor false 0 0 0⟩,
  ⟨4, 4, .vbinOp .vpxor false 1 1 1⟩,
  ⟨8, 4, .vbinOp .vpxor false 2 2 2⟩,
  ⟨12, 4, .vload false 4 (.baseDisp 6 0)⟩,
  ⟨16, 4, .vload false 5 (.baseDisp 2 0)⟩,
  ⟨20, 6, .vpclmulqdq false 6 4 5 0x0⟩,
  ⟨26, 6, .vpclmulqdq false 7 4 5 0x11⟩,
  ⟨32, 5, .vshiftImm .vpshufd false 8 4 0x4e⟩,
  ⟨37, 5, .vshiftImm .vpshufd false 9 5 0x4e⟩,
  ⟨42, 4, .vbinOp .vpxor false 8 8 4⟩,
  ⟨46, 4, .vbinOp .vpxor false 9 9 5⟩,
  ⟨50, 6, .vpclmulqdq false 8 8 9 0x0⟩,
  ⟨56, 4, .vbinOp .vpxor false 0 0 6⟩,
  ⟨60, 4, .vbinOp .vpxor false 1 1 7⟩,
  ⟨64, 4, .vbinOp .vpxor false 2 8 2⟩,
  ⟨68, 4, .aluImm .add true 6 0x10⟩,
  ⟨72, 4, .aluImm .add true 2 0x10⟩,
  ⟨76, 3, .incDec false true 1⟩,
  ⟨79, 2, .jcc 5 12⟩,
  ⟨81, 4, .vbinOp .vpxor false 2 2 0⟩,
  ⟨85, 4, .vbinOp .vpxor false 2 2 1⟩,
  ⟨89, 5, .vshiftImm .vpslldq false 3 2 0x8⟩,
  ⟨94, 5, .vshiftImm .vpsrldq false 2 2 0x8⟩,
  ⟨99, 4, .vbinOp .vpxor false 0 0 3⟩,
  ⟨103, 4, .vbinOp .vpxor false 1 1 2⟩,
  ⟨107, 5, .movImm false 0 0x87⟩,
  ⟨112, 5, .vmovGprToXmm true 10 0⟩,
  ⟨117, 6, .vpclmulqdq false 6 1 10 0x1⟩,
  ⟨123, 5, .vshiftImm .vpslldq false 7 6 0x8⟩,
  ⟨128, 5, .vshiftImm .vpsrldq false 8 6 0x8⟩,
  ⟨133, 4, .vbinOp .vpxor false 0 0 7⟩,
  ⟨137, 4, .vbinOp .vpxor false 1 8 1⟩,
  ⟨141, 6, .vpclmulqdq false 6 1 10 0x0⟩,
  ⟨147, 4, .vbinOp .vpxor false 0 0 6⟩,
  ⟨151, 4, .vpxorLoad128 0 0 (.baseDisp 7 0)⟩,
  ⟨155, 4, .vstore false 0 (.baseDisp 7 0)⟩,
  ⟨159, 4, .vbinOp .vpxor false 0 0 0⟩,
  ⟨163, 4, .vbinOp .vpxor false 1 1 1⟩,
  ⟨167, 4, .vbinOp .vpxor false 2 2 2⟩,
  ⟨171, 4, .vbinOp .vpxor false 3 3 3⟩,
  ⟨175, 4, .vbinOp .vpxor false 4 4 4⟩,
  ⟨179, 4, .vbinOp .vpxor false 5 5 5⟩,
  ⟨183, 4, .vbinOp .vpxor false 6 6 6⟩,
  ⟨187, 4, .vbinOp .vpxor false 7 7 7⟩,
  ⟨191, 5, .vbinOp .vpxor false 8 8 8⟩,
  ⟨196, 5, .vbinOp .vpxor false 9 9 9⟩,
  ⟨201, 5, .vbinOp .vpxor false 10 10 10⟩,
  ⟨206, 2, .aluRegReg .xorOp false 0 0⟩,
  ⟨208, 3, .vzeroupper⟩,
  ⟨211, 1, .ret⟩
]

def gf128VpclmulProg : List (DecodedInstr X86Instr) := [
  ⟨0, 4, .vbinOp .vpxor false 0 0 0⟩,
  ⟨4, 4, .vbinOp .vpxor false 1 1 1⟩,
  ⟨8, 4, .vbinOp .vpxor false 2 2 2⟩,
  ⟨12, 4, .vload true 4 (.baseDisp 6 0)⟩,
  ⟨16, 4, .vload true 5 (.baseDisp 2 0)⟩,
  ⟨20, 6, .vpclmulqdq true 6 4 5 0x0⟩,
  ⟨26, 6, .vpclmulqdq true 7 4 5 0x11⟩,
  ⟨32, 5, .vshiftImm .vpshufd true 8 4 0x4e⟩,
  ⟨37, 5, .vshiftImm .vpshufd true 9 5 0x4e⟩,
  ⟨42, 4, .vbinOp .vpxor true 8 8 4⟩,
  ⟨46, 4, .vbinOp .vpxor true 9 9 5⟩,
  ⟨50, 6, .vpclmulqdq true 8 8 9 0x0⟩,
  ⟨56, 4, .vbinOp .vpxor true 0 0 6⟩,
  ⟨60, 4, .vbinOp .vpxor true 1 1 7⟩,
  ⟨64, 4, .vbinOp .vpxor true 2 8 2⟩,
  ⟨68, 4, .aluImm .add true 6 0x20⟩,
  ⟨72, 4, .aluImm .add true 2 0x20⟩,
  ⟨76, 3, .incDec false true 1⟩,
  ⟨79, 2, .jcc 5 12⟩,
  ⟨81, 6, .vshiftImm .vextracti128 false 3 0 0x1⟩,
  ⟨87, 4, .vbinOp .vpxor false 0 0 3⟩,
  ⟨91, 6, .vshiftImm .vextracti128 false 3 1 0x1⟩,
  ⟨97, 4, .vbinOp .vpxor false 1 1 3⟩,
  ⟨101, 6, .vshiftImm .vextracti128 false 3 2 0x1⟩,
  ⟨107, 4, .vbinOp .vpxor false 2 2 3⟩,
  ⟨111, 4, .vbinOp .vpxor false 2 2 0⟩,
  ⟨115, 4, .vbinOp .vpxor false 2 2 1⟩,
  ⟨119, 5, .vshiftImm .vpslldq false 3 2 0x8⟩,
  ⟨124, 5, .vshiftImm .vpsrldq false 2 2 0x8⟩,
  ⟨129, 4, .vbinOp .vpxor false 0 0 3⟩,
  ⟨133, 4, .vbinOp .vpxor false 1 1 2⟩,
  ⟨137, 5, .movImm false 0 0x87⟩,
  ⟨142, 5, .vmovGprToXmm true 10 0⟩,
  ⟨147, 6, .vpclmulqdq false 6 1 10 0x1⟩,
  ⟨153, 5, .vshiftImm .vpslldq false 7 6 0x8⟩,
  ⟨158, 5, .vshiftImm .vpsrldq false 8 6 0x8⟩,
  ⟨163, 4, .vbinOp .vpxor false 0 0 7⟩,
  ⟨167, 4, .vbinOp .vpxor false 1 8 1⟩,
  ⟨171, 6, .vpclmulqdq false 6 1 10 0x0⟩,
  ⟨177, 4, .vbinOp .vpxor false 0 0 6⟩,
  ⟨181, 4, .vpxorLoad128 0 0 (.baseDisp 7 0)⟩,
  ⟨185, 4, .vstore false 0 (.baseDisp 7 0)⟩,
  ⟨189, 4, .vbinOp .vpxor false 0 0 0⟩,
  ⟨193, 4, .vbinOp .vpxor false 1 1 1⟩,
  ⟨197, 4, .vbinOp .vpxor false 2 2 2⟩,
  ⟨201, 4, .vbinOp .vpxor false 3 3 3⟩,
  ⟨205, 4, .vbinOp .vpxor false 4 4 4⟩,
  ⟨209, 4, .vbinOp .vpxor false 5 5 5⟩,
  ⟨213, 4, .vbinOp .vpxor false 6 6 6⟩,
  ⟨217, 4, .vbinOp .vpxor false 7 7 7⟩,
  ⟨221, 5, .vbinOp .vpxor false 8 8 8⟩,
  ⟨226, 5, .vbinOp .vpxor false 9 9 9⟩,
  ⟨231, 5, .vbinOp .vpxor false 10 10 10⟩,
  ⟨236, 2, .aluRegReg .xorOp false 0 0⟩,
  ⟨238, 3, .vzeroupper⟩,
  ⟨241, 1, .ret⟩
]

/-- Kernel-checked decode of the current pclmul archive slice. -/
theorem gf128Pclmul_current_decode :
    (findSliceByNameBytes currentX86ExtractedSlices
      gf128PclmulName).map
      (fun s => decodeX86Stream s.code) = some (some gf128PclmulProg) := by
  decide +kernel

/-- Kernel-checked decode of the current vpclmul archive slice. -/
theorem gf128Vpclmul_current_decode :
    (findSliceByNameBytes currentX86ExtractedSlices
      gf128VpclmulName).map
      (fun s => decodeX86Stream s.code) = some (some gf128VpclmulProg) := by
  decide +kernel

/-- Zero the high half of a vector, retaining its plain 128-bit word pair. -/
def gf128PclmulLift (x : Vec128) : Vec256 := ⟨x.w0, x.w1, 0, 0⟩

def gf128PclmulXor (a b : Vec256) : Vec256 :=
  clampVecWidth false (evalVecBin256 .vpxor a b)

def gf128PclmulShuffleXor (a : Vec256) : Vec256 :=
  gf128PclmulXor (clampVecWidth false (evalVecShift256 .vpshufd a 0x4e)) a

def gf128PclmulCross (a b : Vec256) : Vec256 :=
  gf128PclmulLift (clmul64 (gf128PclmulShuffleXor a).w0 (gf128PclmulShuffleXor b).w0)

/-- Full register summary of one loop body, before the counter branch. -/
def gf128PclmulBodyVec (y : Bank16 Vec256) (a b : Vec256) : Bank16 Vec256 :=
  let lo := gf128PclmulLift (clmul64 a.w0 b.w0)
  let hi := gf128PclmulLift (clmul64 a.w1 b.w1)
  let mid := gf128PclmulCross a b
  ⟨gf128PclmulXor y.r0 lo, gf128PclmulXor y.r1 hi, gf128PclmulXor mid y.r2,
   y.r3, a, b, lo, hi, mid, gf128PclmulShuffleXor b,
   y.r10, y.r11, y.r12, y.r13, y.r14, y.r15⟩


private theorem gf128Pclmul_body_one_iter
    (g : Bank16 UInt64) (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    StepsX86 gf128PclmulProg 16
      ⟨12, g, y, cf, o, zf, dy, false, m⟩
      ⟨jccPc (!((g.r1 - 1) == 0)) 12 81,
        {g with r1 := g.r1 - 1, r2 := g.r2 + 16, r6 := g.r6 + 16},
        gf128PclmulBodyVec y (gf128PclmulLift (readMem128 m g.r6))
          (gf128PclmulLift (readMem128 m g.r2)),
        decide (g.r2.toNat + (16 : UInt64).toNat ≥ 0x10000000000000000),
        evalX86IncDecOf false true g.r1, (g.r1 - 1) == 0, dy, false, m⟩ := by
  iterate 12
    apply StepsX86.cons rfl rfl
    · simp only [stepX86, evalX86Addr, clampVecWidth, evalVecBin256,
        u64_add_zero, Bool.or_false]
      rfl
  iterate 2
    apply StepsX86.cons rfl rfl
    · rw [stepX86_addImm64]
  apply StepsX86.cons rfl rfl
  · rw [stepX86_dec64]
  apply StepsX86.cons rfl rfl
  · rw [stepX86_jnz]
  unfold gf128PclmulBodyVec gf128PclmulCross gf128PclmulShuffleXor gf128PclmulXor gf128PclmulLift
  dsimp only [Bank16.get, Bank16.set, clampVecWidth, evalVecBin256]
  exact StepsX86.zero _

/-- Accumulate the three polynomial products without touching memory. -/
def gf128PclmulIterVec : Nat → (UInt64 → UInt8) → UInt64 → UInt64 → Bank16 Vec256 → Bank16 Vec256
  | 0, _, _, _, y => y
  | n+1, m, pL, pR, y => gf128PclmulIterVec n m (pL+16) (pR+16)
      (gf128PclmulBodyVec y (gf128PclmulLift (readMem128 m pL))
        (gf128PclmulLift (readMem128 m pR)))

private theorem gf128Pclmul_loop_steps (k : Nat) (hk : k+1 < 2^64)
    (g : Bank16 UInt64) (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    ∃ cf' o' zf', StepsX86 gf128PclmulProg (16 * (k+1))
      ⟨12, {g with r1 := UInt64.ofNat (k+1)}, y, cf, o, zf, dy, false, m⟩
      ⟨81, {g with r1 := 0, r2 := g.r2 + UInt64.ofNat (16*(k+1)), r6 := g.r6 + UInt64.ofNat (16*(k+1))},
        gf128PclmulIterVec (k+1) m g.r6 g.r2 y, cf', o', zf', dy, false, m⟩ := by
  induction k generalizing g y cf o zf with
  | zero =>
    have h := gf128Pclmul_body_one_iter {g with r1 := 1} y cf o zf dy m
    have hd : (1 : UInt64) - 1 = 0 := by decide
    dsimp only at h
    rw [hd, u64_zero_beq_zero] at h
    exact ⟨_, _, _, h⟩
  | succ k ih =>
    have hd : UInt64.ofNat (k+1+1) - 1 = UInt64.ofNat (k+1) := by
      apply UInt64.eq_of_toBitVec_eq
      apply BitVec.eq_of_toNat_eq
      have hb : k+1 < 2^64 := by omega
      simp [UInt64.toNat_toBitVec, Nat.mod_eq_of_lt hb]
    have hz : (UInt64.ofNat (k+1) == 0) = false := by
      cases h : UInt64.ofNat (k+1) == 0
      · rfl
      · have hn := congrArg UInt64.toNat (beq_iff_eq.mp h)
        have hb : k+1 < 2^64 := by omega
        rw [show (UInt64.ofNat (k+1)).toNat = k+1 from Nat.mod_eq_of_lt hb] at hn
        change k+1 = 0 at hn
        omega
    have h := gf128Pclmul_body_one_iter {g with r1 := UInt64.ofNat (k+1+1)} y cf o zf dy m
    dsimp only at h
    rw [hd, hz] at h
    rw [show jccPc (!false) 12 81 = 12 from rfl] at h
    obtain ⟨cf', o', zf', hr⟩ := ih (by omega)
      {g with r2 := g.r2+16, r6 := g.r6+16}
      (gf128PclmulBodyVec y (gf128PclmulLift (readMem128 m g.r6))
        (gf128PclmulLift (readMem128 m g.r2)))
      (decide (g.r2.toNat + (16 : UInt64).toNat ≥ 0x10000000000000000))
      (evalX86IncDecOf false true (UInt64.ofNat (k+1+1))) false
    have hc := StepsX86_trans h hr
    have he : 16 + 16 * (k+1) = 16 * (k+1+1) := by omega
    have hp (p : UInt64) : (p+16) + UInt64.ofNat (16*(k+1)) = p + UInt64.ofNat (16*(k+1+1)) := by
      apply UInt64.eq_of_toBitVec_eq
      simp only [UInt64.toBitVec_add, BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp [UInt64.toNat_toBitVec]
      omega
    dsimp only at hc
    rw [he, hp, hp] at hc
    exact ⟨cf', o', zf', hc⟩

def gf128PclmulReduce (lo hi mid : Vec256) : Vec256 :=
  let cross := gf128PclmulXor (gf128PclmulXor mid lo) hi
  let l := gf128PclmulXor lo (clampVecWidth false (evalVecShift256 .vpslldq cross 8))
  let h := gf128PclmulXor hi (clampVecWidth false (evalVecShift256 .vpsrldq cross 8))
  let r1 := gf128PclmulLift (clmul64 h.w1 0x87)
  let l1 := gf128PclmulXor l (clampVecWidth false (evalVecShift256 .vpslldq r1 8))
  let h1 := gf128PclmulXor (clampVecWidth false (evalVecShift256 .vpsrldq r1 8)) h
  gf128PclmulXor l1 (gf128PclmulLift (clmul64 h1.w0 0x87))

def gf128PclmulOutput (y : Bank16 Vec256) (acc : Vec128) : Vec128 :=
  let v := gf128PclmulXor (gf128PclmulReduce y.r0 y.r1 y.r2) (gf128PclmulLift acc)
  ⟨v.w0, v.w1⟩

private theorem gf128Pclmul_exit_steps
    (g : Bank16 UInt64) (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    StepsX86 gf128PclmulProg 31 ⟨81, g, y, cf, o, zf, dy, false, m⟩
      ⟨(readMem64 (writeMem128 m g.r7 (gf128PclmulOutput y (readMem128 m g.r7))) g.r4).toNat,
        {g with r0 := 0, r4 := g.r4 + 8},
        ⟨Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero,
         Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero,
         clampVecWidth false y.r11, clampVecWidth false y.r12, clampVecWidth false y.r13,
         clampVecWidth false y.r14, clampVecWidth false y.r15⟩,
        false, false, true, false, true,
        writeMem128 m g.r7 (gf128PclmulOutput y (readMem128 m g.r7))⟩ := by
  iterate 17
    apply StepsX86.cons rfl rfl
    · simp only [stepX86, evalX86Addr, clampVecWidth, evalVecBin256,
        maskGprWidth, u64_add_zero, Bool.or_false]
      rfl
  iterate 11
    apply StepsX86.cons rfl rfl
    · simp only [stepX86, clampVecWidth, evalVecBin256, u64_xor_self, Bool.or_false]
      rfl
  apply StepsX86.cons rfl rfl
  · simp only [stepX86_xorRR, mask32_xor_self, u64_zero_beq_zero]
    rfl
  apply StepsX86.cons rfl rfl
  · rfl
  apply StepsX86.cons rfl rfl
  · rfl
  exact StepsX86.zero _

def gf128PclmulInitVec (y : Bank16 Vec256) : Bank16 Vec256 :=
  { y with r0 := Vec256.zero, r1 := Vec256.zero, r2 := Vec256.zero }

private theorem gf128Pclmul_entry_steps
    (g : Bank16 UInt64) (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    StepsX86 gf128PclmulProg 3 ⟨0, g, y, cf, o, zf, dy, false, m⟩
      ⟨12, g, gf128PclmulInitVec y, cf, o, zf, dy, false, m⟩ := by
  iterate 3
    apply StepsX86.cons rfl rfl
    · simp only [stepX86, clampVecWidth, evalVecBin256, u64_xor_self, Bool.or_false]
      rfl
  exact StepsX86.zero _

/-- The pclmul loop's algebraic memory summary, before identifying its reduction
with polynomial division. No memory disjointness assumption is needed: all reads
precede the single final store. -/
private theorem gf128Pclmul_whole_memory (k : Nat) (hk : k+1 < 2^64)
    (s : X86State) (hp : s.pc = 0) (hh : s.halted = false)
    (hn : s.gpr.r1 = UInt64.ofNat (k+1)) (extra : Nat) :
    (runX86 gf128PclmulProg (34 + 16*(k+1) + extra) s).1.mem =
      writeMem128 s.mem s.gpr.r7
        (gf128PclmulOutput
          (gf128PclmulIterVec (k+1) s.mem s.gpr.r6 s.gpr.r2 (gf128PclmulInitVec s.ymm))
          (readMem128 s.mem s.gpr.r7)) ∧
    (runX86 gf128PclmulProg (34 + 16*(k+1) + extra) s).1.halted = true := by
  rcases s with ⟨pc, g, y, cf, o, zf, dy, halted, m⟩
  dsimp only at hp hh hn ⊢
  subst pc halted
  have he := gf128Pclmul_entry_steps g y cf o zf dy m
  obtain ⟨cf', o', zf', hl⟩ := gf128Pclmul_loop_steps k hk g (gf128PclmulInitVec y) cf o zf dy m
  have hg : {g with r1 := UInt64.ofNat (k+1)} = g := by
    rw [←hn]
  rw [hg] at hl
  have hx := gf128Pclmul_exit_steps
    {g with r1 := 0, r2 := g.r2 + UInt64.ofNat (16*(k+1)), r6 := g.r6 + UInt64.ofNat (16*(k+1))}
    (gf128PclmulIterVec (k+1) m g.r6 g.r2 (gf128PclmulInitVec y)) cf' o' zf' dy m
  have h := (StepsX86_trans (StepsX86_trans he hl) hx).toExecReaches.run extra
  have hc : 3 + 16*(k+1) + 31 = 34 + 16*(k+1) := by omega
  rw [hc] at h
  rw [h.1, runX86_halted_fst _ _ _ rfl]
  exact ⟨rfl, rfl⟩

/-- Fresh bytes execute the pclmul accumulation/reduction expression for every
positive ABI counter, including wraparound pointer arithmetic. -/
theorem gf128Pclmul_current_execution
    (s : X86State) (k extra : Nat) (hk : k+1 < 2^64) (hp : s.pc = 0)
    (hh : s.halted = false) (hn : s.gpr.r1 = UInt64.ofNat (k+1)) :
    ∃ slice, findSliceByNameBytes currentX86ExtractedSlices gf128PclmulName = some slice ∧
      decodeX86Stream slice.code = some gf128PclmulProg ∧
      (runX86 gf128PclmulProg (34 + 16*(k+1) + extra) s).1.mem =
        writeMem128 s.mem s.gpr.r7
          (gf128PclmulOutput
            (gf128PclmulIterVec (k+1) s.mem s.gpr.r6 s.gpr.r2 (gf128PclmulInitVec s.ymm))
            (readMem128 s.mem s.gpr.r7)) ∧
      (runX86 gf128PclmulProg (34 + 16*(k+1) + extra) s).1.halted = true := by
  cases hf : findSliceByNameBytes currentX86ExtractedSlices gf128PclmulName with
  | none =>
    have h := gf128Pclmul_current_decode
    rw [hf] at h
    contradiction
  | some slice =>
    have hd := gf128Pclmul_current_decode
    rw [hf] at hd
    exact ⟨slice, rfl, Option.some.inj hd, gf128Pclmul_whole_memory k hk s hp hh hn extra⟩

/-- Nonzero multiplicands in disjoint example blocks, with zero initial accumulator. -/
def gf128PclmulWitnessState : X86State :=
  ⟨0, ⟨0, 1, 8192, 0, 0, 0, 4096, 12288, 0, 0, 0, 0, 0, 0, 0, 0⟩,
   Bank16.const Vec256.zero, false, false, false, false, false,
   fun a => if a == 4096 || a == 8192 then 1 else 0⟩

theorem gf128Pclmul_execution_inhabited :
    ∃ (s : X86State) (k extra : Nat), k+1 < 2^64 ∧ s.pc = 0 ∧
      s.halted = false ∧ s.gpr.r1 = UInt64.ofNat (k+1) ∧ extra = 0 := by
  exact ⟨gf128PclmulWitnessState, 0, 0, by decide, rfl, rfl, rfl, rfl⟩

/-- A mutant returning zero instead of the field accumulator loses 1·1 = 1. -/
theorem gf128Pclmul_zero_result_tooth :
    gf128PclmulOutput
      (gf128PclmulIterVec 1 gf128PclmulWitnessState.mem 4096 8192
        (gf128PclmulInitVec gf128PclmulWitnessState.ymm))
      (readMem128 gf128PclmulWitnessState.mem 12288) ≠ Vec128.zero := by
  decide +kernel

#tooth_pair gf128Pclmul_current_execution vs gf128Pclmul_zero_result_tooth
#verify_inhabited gf128Pclmul_current_execution gf128Pclmul_execution_inhabited

private theorem gf128_reassemble32 (a : UInt64) :
    (a &&& (0xffffffff : UInt64)) |||
      (((a >>> 32) &&& (0xffffffff : UInt64)) <<< 32) = a := by
  apply UInt64.eq_of_toBitVec_eq
  have hm : (0xffffffff : BitVec 64) = (BitVec.allOnes 32).setWidth 64 := by decide +kernel
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_and, UInt64.toBitVec_shiftLeft,
    UInt64.toBitVec_shiftRight, UInt64.toBitVec_ofNat, BitVec.shiftLeft_eq',
    BitVec.ushiftRight_eq']
  change (a.toBitVec &&& (0xffffffff : BitVec 64)) |||
    (((a.toBitVec >>> 32) &&& (0xffffffff : BitVec 64)) <<< 32) = a.toBitVec
  rw [hm]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_setWidth,
    Constructive.getLsbD_allOnes, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    hi, decide_true, Bool.true_and]
  by_cases h : i < 32
  · simp [h]
  · have he : 32 + (i-32) = i := by omega
    simp [h, he, show i-32 < 64 by omega, show i-32 < 32 by omega]

/-- PSHUFD 0x4e swaps the two qwords in each 128-bit lane. -/
theorem gf128_shuffle4e_words (a : Vec256) :
    evalVecShift256 .vpshufd a 0x4e = ⟨a.w1, a.w0, a.w3, a.w2⟩ := by
  change (⟨(a.w1 >>> 0 &&& (0xffffffff : UInt64)) ||| ((a.w1 >>> 32 &&& (0xffffffff : UInt64)) <<< 32),
    (a.w0 >>> 0 &&& (0xffffffff : UInt64)) ||| ((a.w0 >>> 32 &&& (0xffffffff : UInt64)) <<< 32),
    (a.w3 >>> 0 &&& (0xffffffff : UInt64)) ||| ((a.w3 >>> 32 &&& (0xffffffff : UInt64)) <<< 32),
    (a.w2 >>> 0 &&& (0xffffffff : UInt64)) ||| ((a.w2 >>> 32 &&& (0xffffffff : UInt64)) <<< 32)⟩ : Vec256) = _
  simp only [UInt64.shiftRight_zero, gf128_reassemble32]

private theorem gf128Pclmul_xor_left_comm (a b c : UInt64) :
    a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← UInt64.xor_assoc, UInt64.xor_comm a b, UInt64.xor_assoc]

/-- The unreduced polynomial represented by the three Karatsuba accumulators. -/
def gf128PclmulRaw (y : Bank16 Vec256) : BitVec 256 :=
  let m0 := y.r2.w0 ^^^ y.r0.w0 ^^^ y.r1.w0
  let m1 := y.r2.w1 ^^^ y.r0.w1 ^^^ y.r1.w1
  gf128Words (y.r1.w0 ^^^ m1) y.r1.w1 ++ gf128Words y.r0.w0 (y.r0.w1 ^^^ m0)

private theorem gf128Pclmul_cross_words (a b : Vec256) :
    gf128PclmulCross a b =
      gf128PclmulLift (clmul64 (a.w0 ^^^ a.w1) (b.w0 ^^^ b.w1)) := by
  simp [gf128PclmulCross, gf128PclmulShuffleXor, gf128PclmulXor,
    gf128_shuffle4e_words, clampVecWidth, evalVecBin256, UInt64.xor_comm]

private theorem gf128Pclmul_raw_add
    (l0 l1 h0 h1 m0 m1 : UInt64) (p q r : Vec128) :
    gf128Words ((h0 ^^^ q.w0) ^^^ ((r.w1 ^^^ m1) ^^^ (l1 ^^^ p.w1) ^^^ (h1 ^^^ q.w1)))
      (h1 ^^^ q.w1) ++
      gf128Words (l0 ^^^ p.w0)
        ((l1 ^^^ p.w1) ^^^ ((r.w0 ^^^ m0) ^^^ (l0 ^^^ p.w0) ^^^ (h0 ^^^ q.w0))) =
    (gf128Words (h0 ^^^ (m1 ^^^ l1 ^^^ h1)) h1 ++
      gf128Words l0 (l1 ^^^ (m0 ^^^ l0 ^^^ h0))) ^^^
    (gf128Words (q.w0 ^^^ (r.w1 ^^^ p.w1 ^^^ q.w1)) q.w1 ++
      gf128Words p.w0 (p.w1 ^^^ (r.w0 ^^^ p.w0 ^^^ q.w0))) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [gf128Words.public_eq_1, BitVec.getLsbD_append, UInt64.toBitVec_xor, BitVec.getLsbD_xor]
  split <;> split <;> simp only [Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]

private theorem gf128Pclmul_body_polynomial (y : Bank16 Vec256) (a b : Vec256) :
    gf128PclmulRaw (gf128PclmulBodyVec y a b) = gf128PclmulRaw y ^^^
      gf128PolyMul ((gf128Words a.w0 a.w1).setWidth 256) (gf128Words b.w0 b.w1) := by
  rw [← gf128_clmul_karatsuba_words]
  simp only [gf128PclmulRaw, gf128PclmulBodyVec, gf128Pclmul_cross_words]
  exact gf128Pclmul_raw_add y.r0.w0 y.r0.w1 y.r1.w0 y.r1.w1 y.r2.w0 y.r2.w1
    (clmul64 a.w0 b.w0) (clmul64 a.w1 b.w1)
    (clmul64 (a.w0 ^^^ a.w1) (b.w0 ^^^ b.w1))

/-- Polynomial products of 16-byte input blocks, with machine pointer arithmetic. -/
def gf128PclmulPolySum : Nat → (UInt64 → UInt8) → UInt64 → UInt64 → BitVec 256
  | 0, _, _, _ => 0
  | n+1, m, pL, pR =>
      gf128PolyMul
        ((gf128Words (readMem128 m pL).w0 (readMem128 m pL).w1).setWidth 256)
        (gf128Words (readMem128 m pR).w0 (readMem128 m pR).w1) ^^^
      gf128PclmulPolySum n m (pL+16) (pR+16)

/-- Mathematical GF(2^128) dot product of the input blocks. -/
def gf128PclmulFieldSum : Nat → (UInt64 → UInt8) → UInt64 → UInt64 → BitVec 128
  | 0, _, _, _ => 0
  | n+1, m, pL, pR =>
      gf128FieldMul
        (gf128Words (readMem128 m pL).w0 (readMem128 m pL).w1)
        (gf128Words (readMem128 m pR).w0 (readMem128 m pR).w1) ^^^
      gf128PclmulFieldSum n m (pL+16) (pR+16)

private theorem gf128Pclmul_iter_polynomial (n : Nat) (m : UInt64 → UInt8)
    (pL pR : UInt64) (y : Bank16 Vec256) :
    gf128PclmulRaw (gf128PclmulIterVec n m pL pR y) =
      gf128PclmulRaw y ^^^ gf128PclmulPolySum n m pL pR := by
  induction n generalizing pL pR y with
  | zero => simp [gf128PclmulIterVec, gf128PclmulPolySum]
  | succ n ih =>
    simp only [gf128PclmulIterVec, ih, gf128Pclmul_body_polynomial,
      gf128PclmulPolySum, gf128PclmulLift, BitVec.xor_assoc]

private theorem gf128Pclmul_sum_reduce (n : Nat) (m : UInt64 → UInt8) (pL pR : UInt64) :
    gf128Reduce (gf128PclmulPolySum n m pL pR) = gf128PclmulFieldSum n m pL pR := by
  induction n generalizing pL pR with
  | zero => exact elf_gf128Reduce_zero
  | succ n ih =>
    simp only [gf128PclmulPolySum, gf128PclmulFieldSum, gf128Reduce_xor, ih, gf128FieldMul.public_eq_1]

private theorem gf128Pclmul_output_reduce (y : Bank16 Vec256) (acc : Vec128) :
    gf128Words (gf128PclmulOutput y acc).w0 (gf128PclmulOutput y acc).w1 =
      gf128Reduce (gf128PclmulRaw y) ^^^ gf128Words acc.w0 acc.w1 := by
  change gf128Words ((gf128PclmulReduce y.r0 y.r1 y.r2).w0 ^^^ acc.w0)
    ((gf128PclmulReduce y.r0 y.r1 y.r2).w1 ^^^ acc.w1) = _
  rw [gf128Words_xor]
  congr 1
  unfold gf128PclmulRaw
  rw [← gf128WordReduce_eq_reduce]
  simp [gf128PclmulReduce, gf128PclmulXor, gf128PclmulLift,
    evalVecBin256, evalVecShift256, clampVecWidth, gf128WordReduce.public_eq_1,
    UInt64.xor_assoc, UInt64.xor_comm, gf128Pclmul_xor_left_comm]

/-- The accumulated machine output is the mathematical field sum XOR the initial accumulator. -/
private theorem gf128Pclmul_output_field (n : Nat) (m : UInt64 → UInt8)
    (pL pR : UInt64) (y : Bank16 Vec256) (acc : Vec128) :
    gf128Words
      (gf128PclmulOutput (gf128PclmulIterVec n m pL pR (gf128PclmulInitVec y)) acc).w0
      (gf128PclmulOutput (gf128PclmulIterVec n m pL pR (gf128PclmulInitVec y)) acc).w1 =
      gf128PclmulFieldSum n m pL pR ^^^ gf128Words acc.w0 acc.w1 := by
  rw [gf128Pclmul_output_reduce, gf128Pclmul_iter_polynomial]
  have hz : gf128PclmulRaw (gf128PclmulInitVec y) = 0 := by
    simp [gf128PclmulRaw, gf128PclmulInitVec, Vec256.zero, gf128Words.public_eq_1]
  rw [hz]
  simp only [BitVec.ofNat_eq_ofNat, BitVec.zero_xor, gf128Pclmul_sum_reduce]

/-- Fresh pclmul bytes compute accumulation of the portable GF(2^128) products
for every positive 64-bit counter. The mathematical specification uses plain
little-endian polynomial bits and z^128+z^7+z²+z+1. -/
theorem current_rlib_gf2_128_mul_acc_pclmul_functional
    (s : X86State) (k extra : Nat) (hk : k+1 < 2^64) (hp : s.pc = 0)
    (hh : s.halted = false) (hn : s.gpr.r1 = UInt64.ofNat (k+1)) :
    ∃ slice, findSliceByNameBytes currentX86ExtractedSlices gf128PclmulName = some slice ∧
      decodeX86Stream slice.code = some gf128PclmulProg ∧
      (runX86 gf128PclmulProg (34 + 16*(k+1) + extra) s).1.halted = true ∧
      gf128Words
        (readMem64 (runX86 gf128PclmulProg (34 + 16*(k+1) + extra) s).1.mem s.gpr.r7)
        (readMem64 (runX86 gf128PclmulProg (34 + 16*(k+1) + extra) s).1.mem (s.gpr.r7+8)) =
        gf128Words (readMem64 s.mem s.gpr.r7) (readMem64 s.mem (s.gpr.r7+8)) ^^^
          gf128PclmulFieldSum (k+1) s.mem s.gpr.r6 s.gpr.r2 ∧
      (∀ a : UInt64, (∀ i : Nat, i < 16 → a ≠ s.gpr.r7 + UInt64.ofNat i) →
        (runX86 gf128PclmulProg (34 + 16*(k+1) + extra) s).1.mem a = s.mem a) := by
  obtain ⟨slice, hf, hd, hm, hh'⟩ := gf128Pclmul_current_execution s k extra hk hp hh hn
  refine ⟨slice, hf, hd, hh', ?_, ?_⟩
  · rw [hm, readMem64_writeMem128_lo, readMem64_writeMem128_hi]
    simpa only [readMem128, BitVec.xor_comm] using
      gf128Pclmul_output_field (k+1) s.mem s.gpr.r6 s.gpr.r2 s.ymm (readMem128 s.mem s.gpr.r7)
  · intro a ha
    rw [hm]
    exact writeMem128_outside _ _ _ _ ha

/-- A zero-result specification is refuted on 1·1. -/
theorem gf128Pclmul_field_zero_tooth :
    gf128PclmulFieldSum 1 gf128PclmulWitnessState.mem 4096 8192 ≠ 0 :=
  elf_gf128_one_block_ne_zero (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

#tooth_pair current_rlib_gf2_128_mul_acc_pclmul_functional vs gf128Pclmul_field_zero_tooth
#verify_inhabited current_rlib_gf2_128_mul_acc_pclmul_functional gf128Pclmul_execution_inhabited

def gf128VpclmulXor (a b : Vec256) : Vec256 := evalVecBin256 .vpxor a b

def gf128VpclmulShuffleXor (a : Vec256) : Vec256 :=
  gf128VpclmulXor (evalVecShift256 .vpshufd a 0x4e) a

def gf128VpclmulLo (a b : Vec256) : Vec256 :=
  let p := clmul64 a.w0 b.w0
  let q := clmul64 a.w2 b.w2
  ⟨p.w0, p.w1, q.w0, q.w1⟩

def gf128VpclmulHi (a b : Vec256) : Vec256 :=
  let p := clmul64 a.w1 b.w1
  let q := clmul64 a.w3 b.w3
  ⟨p.w0, p.w1, q.w0, q.w1⟩

def gf128VpclmulCross (a b : Vec256) : Vec256 :=
  gf128VpclmulLo (gf128VpclmulShuffleXor a) (gf128VpclmulShuffleXor b)

def gf128VpclmulBodyVec (y : Bank16 Vec256) (a b : Vec256) : Bank16 Vec256 :=
  let lo := gf128VpclmulLo a b
  let hi := gf128VpclmulHi a b
  let mid := gf128VpclmulCross a b
  ⟨gf128VpclmulXor y.r0 lo, gf128VpclmulXor y.r1 hi, gf128VpclmulXor mid y.r2,
   y.r3, a, b, lo, hi, mid, gf128VpclmulShuffleXor b,
   y.r10, y.r11, y.r12, y.r13, y.r14, y.r15⟩

private theorem gf128Vpclmul_body_one_iter
    (g : Bank16 UInt64) (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    StepsX86 gf128VpclmulProg 16
      ⟨12, g, y, cf, o, zf, dy, false, m⟩
      ⟨jccPc (!((g.r1 - 1) == 0)) 12 81,
        {g with r1 := g.r1 - 1, r2 := g.r2 + 32, r6 := g.r6 + 32},
        gf128VpclmulBodyVec y (readMem256 m g.r6) (readMem256 m g.r2),
        decide (g.r2.toNat + (32 : UInt64).toNat ≥ 0x10000000000000000),
        evalX86IncDecOf false true g.r1, (g.r1 - 1) == 0, true, false, m⟩ := by
  iterate 12
    apply StepsX86.cons rfl rfl
    · simp only [stepX86, evalX86Addr, clampVecWidth, evalVecBin256,
        u64_add_zero, Bool.or_true]
      rfl
  iterate 2
    apply StepsX86.cons rfl rfl
    · rw [stepX86_addImm64]
  apply StepsX86.cons rfl rfl
  · rw [stepX86_dec64]
  apply StepsX86.cons rfl rfl
  · rw [stepX86_jnz]
  unfold gf128VpclmulBodyVec gf128VpclmulCross gf128VpclmulShuffleXor
    gf128VpclmulXor gf128VpclmulLo gf128VpclmulHi
  dsimp only [Bank16.get, Bank16.set, clampVecWidth, evalVecBin256]
  exact StepsX86.zero _

def gf128VpclmulIterVec : Nat → (UInt64 → UInt8) → UInt64 → UInt64 → Bank16 Vec256 → Bank16 Vec256
  | 0, _, _, _, y => y
  | n+1, m, pL, pR, y => gf128VpclmulIterVec n m (pL+32) (pR+32)
      (gf128VpclmulBodyVec y (readMem256 m pL) (readMem256 m pR))

private theorem gf128Vpclmul_loop_steps (k : Nat) (hk : k+1 < 2^64)
    (g : Bank16 UInt64) (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    ∃ cf' o' zf', StepsX86 gf128VpclmulProg (16 * (k+1))
      ⟨12, {g with r1 := UInt64.ofNat (k+1)}, y, cf, o, zf, dy, false, m⟩
      ⟨81, {g with r1 := 0, r2 := g.r2 + UInt64.ofNat (32*(k+1)), r6 := g.r6 + UInt64.ofNat (32*(k+1))},
        gf128VpclmulIterVec (k+1) m g.r6 g.r2 y, cf', o', zf', true, false, m⟩ := by
  induction k generalizing g y cf o zf dy with
  | zero =>
    have h := gf128Vpclmul_body_one_iter {g with r1 := 1} y cf o zf dy m
    have hd : (1 : UInt64) - 1 = 0 := by decide
    dsimp only at h
    rw [hd, u64_zero_beq_zero] at h
    exact ⟨_, _, _, h⟩
  | succ k ih =>
    have hd : UInt64.ofNat (k+1+1) - 1 = UInt64.ofNat (k+1) := by
      apply UInt64.eq_of_toBitVec_eq
      apply BitVec.eq_of_toNat_eq
      have hb : k+1 < 2^64 := by omega
      simp [UInt64.toNat_toBitVec, Nat.mod_eq_of_lt hb]
    have hz : (UInt64.ofNat (k+1) == 0) = false := by
      cases h : UInt64.ofNat (k+1) == 0
      · rfl
      · have hn := congrArg UInt64.toNat (beq_iff_eq.mp h)
        have hb : k+1 < 2^64 := by omega
        rw [show (UInt64.ofNat (k+1)).toNat = k+1 from Nat.mod_eq_of_lt hb] at hn
        change k+1 = 0 at hn
        omega
    have h := gf128Vpclmul_body_one_iter {g with r1 := UInt64.ofNat (k+1+1)} y cf o zf dy m
    dsimp only at h
    rw [hd, hz] at h
    rw [show jccPc (!false) 12 81 = 12 from rfl] at h
    obtain ⟨cf', o', zf', hr⟩ := ih (by omega)
      {g with r2 := g.r2+32, r6 := g.r6+32}
      (gf128VpclmulBodyVec y (readMem256 m g.r6)
        (readMem256 m g.r2))
      (decide (g.r2.toNat + (32 : UInt64).toNat ≥ 0x10000000000000000))
      (evalX86IncDecOf false true (UInt64.ofNat (k+1+1))) false true
    have hc := StepsX86_trans h hr
    have he : 16 + 16 * (k+1) = 16 * (k+1+1) := by omega
    have hp (p : UInt64) : (p+32) + UInt64.ofNat (32*(k+1)) = p + UInt64.ofNat (32*(k+1+1)) := by
      apply UInt64.eq_of_toBitVec_eq
      simp only [UInt64.toBitVec_add, BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp [UInt64.toNat_toBitVec]
      omega
    dsimp only at hc
    rw [he, hp, hp] at hc
    exact ⟨cf', o', zf', hc⟩


def gf128VpclmulCollapse (y : Bank16 Vec256) : Bank16 Vec256 :=
  {y with
    r0 := gf128PclmulXor y.r0 (evalVecShift256 .vextracti128 y.r0 1),
    r1 := gf128PclmulXor y.r1 (evalVecShift256 .vextracti128 y.r1 1),
    r2 := gf128PclmulXor y.r2 (evalVecShift256 .vextracti128 y.r2 1)}

def gf128VpclmulOutput (y : Bank16 Vec256) (acc : Vec128) : Vec128 :=
  gf128PclmulOutput (gf128VpclmulCollapse y) acc

private theorem gf128Vpclmul_exit_steps
    (g : Bank16 UInt64) (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    StepsX86 gf128VpclmulProg 37 ⟨81, g, y, cf, o, zf, dy, false, m⟩
      ⟨(readMem64 (writeMem128 m g.r7 (gf128VpclmulOutput y (readMem128 m g.r7))) g.r4).toNat,
        {g with r0 := 0, r4 := g.r4 + 8},
        ⟨Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero,
         Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero,
         clampVecWidth false y.r11, clampVecWidth false y.r12, clampVecWidth false y.r13,
         clampVecWidth false y.r14, clampVecWidth false y.r15⟩,
        false, false, true, false, true,
        writeMem128 m g.r7 (gf128VpclmulOutput y (readMem128 m g.r7))⟩ := by
  iterate 23
    apply StepsX86.cons rfl rfl
    · simp only [stepX86, evalX86Addr, clampVecWidth, evalVecBin256,
        maskGprWidth, u64_add_zero, Bool.or_false]
      rfl
  iterate 11
    apply StepsX86.cons rfl rfl
    · simp only [stepX86, clampVecWidth, evalVecBin256, u64_xor_self, Bool.or_false]
      rfl
  apply StepsX86.cons rfl rfl
  · simp only [stepX86_xorRR, mask32_xor_self, u64_zero_beq_zero]
    rfl
  apply StepsX86.cons rfl rfl
  · rfl
  apply StepsX86.cons rfl rfl
  · rfl
  exact StepsX86.zero _

private theorem gf128Vpclmul_entry_steps
    (g : Bank16 UInt64) (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    StepsX86 gf128VpclmulProg 3 ⟨0, g, y, cf, o, zf, dy, false, m⟩
      ⟨12, g, gf128PclmulInitVec y, cf, o, zf, dy, false, m⟩ := by
  iterate 3
    apply StepsX86.cons rfl rfl
    · simp only [stepX86, clampVecWidth, evalVecBin256, u64_xor_self, Bool.or_false]
      rfl
  exact StepsX86.zero _

private theorem gf128Vpclmul_whole_memory (k : Nat) (hk : k+1 < 2^64)
    (s : X86State) (hp : s.pc = 0) (hh : s.halted = false)
    (hn : s.gpr.r1 = UInt64.ofNat (k+1)) (extra : Nat) :
    (runX86 gf128VpclmulProg (40 + 16*(k+1) + extra) s).1.mem =
      writeMem128 s.mem s.gpr.r7
        (gf128VpclmulOutput
          (gf128VpclmulIterVec (k+1) s.mem s.gpr.r6 s.gpr.r2 (gf128PclmulInitVec s.ymm))
          (readMem128 s.mem s.gpr.r7)) ∧
    (runX86 gf128VpclmulProg (40 + 16*(k+1) + extra) s).1.halted = true := by
  rcases s with ⟨pc, g, y, cf, o, zf, dy, halted, m⟩
  dsimp only at hp hh hn ⊢
  subst pc halted
  have he := gf128Vpclmul_entry_steps g y cf o zf dy m
  obtain ⟨cf', o', zf', hl⟩ := gf128Vpclmul_loop_steps k hk g (gf128PclmulInitVec y) cf o zf dy m
  have hg : {g with r1 := UInt64.ofNat (k+1)} = g := by
    rw [←hn]
  rw [hg] at hl
  have hx := gf128Vpclmul_exit_steps
    {g with r1 := 0, r2 := g.r2 + UInt64.ofNat (32*(k+1)), r6 := g.r6 + UInt64.ofNat (32*(k+1))}
    (gf128VpclmulIterVec (k+1) m g.r6 g.r2 (gf128PclmulInitVec y)) cf' o' zf' true m
  have h := (StepsX86_trans (StepsX86_trans he hl) hx).toExecReaches.run extra
  have hc : 3 + 16*(k+1) + 37 = 40 + 16*(k+1) := by omega
  rw [hc] at h
  rw [h.1, runX86_halted_fst _ _ _ rfl]
  exact ⟨rfl, rfl⟩

/-- Fresh bytes execute the vpclmul accumulation/reduction expression for every
positive ABI counter, including wraparound pointer arithmetic. -/
theorem gf128Vpclmul_current_execution
    (s : X86State) (k extra : Nat) (hk : k+1 < 2^64) (hp : s.pc = 0)
    (hh : s.halted = false) (hn : s.gpr.r1 = UInt64.ofNat (k+1)) :
    ∃ slice, findSliceByNameBytes currentX86ExtractedSlices gf128VpclmulName = some slice ∧
      decodeX86Stream slice.code = some gf128VpclmulProg ∧
      (runX86 gf128VpclmulProg (40 + 16*(k+1) + extra) s).1.mem =
        writeMem128 s.mem s.gpr.r7
          (gf128VpclmulOutput
            (gf128VpclmulIterVec (k+1) s.mem s.gpr.r6 s.gpr.r2 (gf128PclmulInitVec s.ymm))
            (readMem128 s.mem s.gpr.r7)) ∧
      (runX86 gf128VpclmulProg (40 + 16*(k+1) + extra) s).1.halted = true := by
  cases hf : findSliceByNameBytes currentX86ExtractedSlices gf128VpclmulName with
  | none =>
    have h := gf128Vpclmul_current_decode
    rw [hf] at h
    contradiction
  | some slice =>
    have hd := gf128Vpclmul_current_decode
    rw [hf] at hd
    exact ⟨slice, rfl, Option.some.inj hd, gf128Vpclmul_whole_memory k hk s hp hh hn extra⟩


theorem gf128Vpclmul_zero_result_tooth :
    gf128VpclmulOutput
      (gf128VpclmulIterVec 1 gf128PclmulWitnessState.mem 4096 8192
        (gf128PclmulInitVec gf128PclmulWitnessState.ymm))
      (readMem128 gf128PclmulWitnessState.mem 12288) ≠ Vec128.zero := by
  decide +kernel

#tooth_pair gf128Vpclmul_current_execution vs gf128Vpclmul_zero_result_tooth
#verify_inhabited gf128Vpclmul_current_execution gf128Pclmul_execution_inhabited

def gf128VpclmulRaw (y : Bank16 Vec256) : BitVec 256 :=
  gf128PclmulRaw (gf128VpclmulCollapse y)

private theorem gf128Vpclmul_cross_words (a b : Vec256) :
    gf128VpclmulCross a b =
      let p := clmul64 (a.w0 ^^^ a.w1) (b.w0 ^^^ b.w1)
      let q := clmul64 (a.w2 ^^^ a.w3) (b.w2 ^^^ b.w3)
      ⟨p.w0, p.w1, q.w0, q.w1⟩ := by
  simp [gf128VpclmulCross, gf128VpclmulLo, gf128VpclmulShuffleXor, gf128VpclmulXor,
    gf128_shuffle4e_words, evalVecBin256, UInt64.xor_comm]

private def gf128VpclmulRawWords (l0 l1 h0 h1 m0 m1 : UInt64) : BitVec 256 :=
  gf128Words (h0 ^^^ (m1 ^^^ l1 ^^^ h1)) h1 ++
    gf128Words l0 (l1 ^^^ (m0 ^^^ l0 ^^^ h0))

private theorem gf128Vpclmul_raw_linear
    (l0 l1 h0 h1 m0 m1 L0 L1 H0 H1 M0 M1 : UInt64) :
    gf128VpclmulRawWords (l0 ^^^ L0) (l1 ^^^ L1) (h0 ^^^ H0) (h1 ^^^ H1)
      (m0 ^^^ M0) (m1 ^^^ M1) =
    gf128VpclmulRawWords l0 l1 h0 h1 m0 m1 ^^^ gf128VpclmulRawWords L0 L1 H0 H1 M0 M1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [gf128VpclmulRawWords, gf128Words.public_eq_1, BitVec.getLsbD_append,
    UInt64.toBitVec_xor, BitVec.getLsbD_xor]
  split <;> split <;> simp only [Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]

private theorem gf128Vpclmul_raw_add
    (l0 l1 h0 h1 m0 m1 L0 L1 H0 H1 M0 M1 : UInt64)
    (p0 q0 r0 p1 q1 r1 : Vec128) :
    gf128VpclmulRawWords
      ((l0 ^^^ p0.w0) ^^^ (L0 ^^^ p1.w0))
      ((l1 ^^^ p0.w1) ^^^ (L1 ^^^ p1.w1))
      ((h0 ^^^ q0.w0) ^^^ (H0 ^^^ q1.w0))
      ((h1 ^^^ q0.w1) ^^^ (H1 ^^^ q1.w1))
      ((r0.w0 ^^^ m0) ^^^ (r1.w0 ^^^ M0))
      ((r0.w1 ^^^ m1) ^^^ (r1.w1 ^^^ M1)) =
    gf128VpclmulRawWords (l0 ^^^ L0) (l1 ^^^ L1) (h0 ^^^ H0) (h1 ^^^ H1)
      (m0 ^^^ M0) (m1 ^^^ M1) ^^^
    (gf128VpclmulRawWords p0.w0 p0.w1 q0.w0 q0.w1 r0.w0 r0.w1 ^^^
      gf128VpclmulRawWords p1.w0 p1.w1 q1.w0 q1.w1 r1.w0 r1.w1) := by
  rw [UInt64.xor_comm r0.w0 m0, UInt64.xor_comm r0.w1 m1,
    UInt64.xor_comm r1.w0 M0, UInt64.xor_comm r1.w1 M1]
  simp only [gf128Vpclmul_raw_linear]
  exact gf128XorShuffle _ _ _ _

private theorem gf128Vpclmul_body_polynomial (y : Bank16 Vec256) (a b : Vec256) :
    gf128VpclmulRaw (gf128VpclmulBodyVec y a b) = gf128VpclmulRaw y ^^^
      (gf128PolyMul ((gf128Words a.w0 a.w1).setWidth 256) (gf128Words b.w0 b.w1) ^^^
       gf128PolyMul ((gf128Words a.w2 a.w3).setWidth 256) (gf128Words b.w2 b.w3)) := by
  rw [← gf128_clmul_karatsuba_words a.w0 a.w1 b.w0 b.w1,
    ← gf128_clmul_karatsuba_words a.w2 a.w3 b.w2 b.w3]
  simp only [gf128VpclmulRaw, gf128PclmulRaw, gf128VpclmulBodyVec,
    gf128Vpclmul_cross_words]
  exact gf128Vpclmul_raw_add y.r0.w0 y.r0.w1 y.r1.w0 y.r1.w1 y.r2.w0 y.r2.w1
    y.r0.w2 y.r0.w3 y.r1.w2 y.r1.w3 y.r2.w2 y.r2.w3
    (clmul64 a.w0 b.w0) (clmul64 a.w1 b.w1)
    (clmul64 (a.w0 ^^^ a.w1) (b.w0 ^^^ b.w1))
    (clmul64 a.w2 b.w2) (clmul64 a.w3 b.w3)
    (clmul64 (a.w2 ^^^ a.w3) (b.w2 ^^^ b.w3))

def gf128VpclmulPolySum : Nat → (UInt64 → UInt8) → UInt64 → UInt64 → BitVec 256
  | 0, _, _, _ => 0
  | n+1, m, pL, pR =>
      let a := readMem256 m pL
      let b := readMem256 m pR
      (gf128PolyMul ((gf128Words a.w0 a.w1).setWidth 256) (gf128Words b.w0 b.w1) ^^^
       gf128PolyMul ((gf128Words a.w2 a.w3).setWidth 256) (gf128Words b.w2 b.w3)) ^^^
      gf128VpclmulPolySum n m (pL+32) (pR+32)

/-- Two GF(2^128) products per 32-byte block. -/
def gf128VpclmulFieldSum : Nat → (UInt64 → UInt8) → UInt64 → UInt64 → BitVec 128
  | 0, _, _, _ => 0
  | n+1, m, pL, pR =>
      let a := readMem256 m pL
      let b := readMem256 m pR
      (gf128FieldMul (gf128Words a.w0 a.w1) (gf128Words b.w0 b.w1) ^^^
       gf128FieldMul (gf128Words a.w2 a.w3) (gf128Words b.w2 b.w3)) ^^^
      gf128VpclmulFieldSum n m (pL+32) (pR+32)

private theorem gf128Vpclmul_iter_polynomial (n : Nat) (m : UInt64 → UInt8)
    (pL pR : UInt64) (y : Bank16 Vec256) :
    gf128VpclmulRaw (gf128VpclmulIterVec n m pL pR y) =
      gf128VpclmulRaw y ^^^ gf128VpclmulPolySum n m pL pR := by
  induction n generalizing pL pR y with
  | zero => simp [gf128VpclmulIterVec, gf128VpclmulPolySum]
  | succ n ih =>
    simp only [gf128VpclmulIterVec, ih, gf128Vpclmul_body_polynomial,
      gf128VpclmulPolySum, BitVec.xor_assoc]

private theorem gf128Vpclmul_sum_reduce (n : Nat) (m : UInt64 → UInt8) (pL pR : UInt64) :
    gf128Reduce (gf128VpclmulPolySum n m pL pR) = gf128VpclmulFieldSum n m pL pR := by
  induction n generalizing pL pR with
  | zero => exact elf_gf128Reduce_zero
  | succ n ih =>
    simp only [gf128VpclmulPolySum, gf128VpclmulFieldSum, gf128Reduce_xor, ih, gf128FieldMul.public_eq_1]

private theorem gf128Vpclmul_output_field (n : Nat) (m : UInt64 → UInt8)
    (pL pR : UInt64) (y : Bank16 Vec256) (acc : Vec128) :
    gf128Words
      (gf128VpclmulOutput (gf128VpclmulIterVec n m pL pR (gf128PclmulInitVec y)) acc).w0
      (gf128VpclmulOutput (gf128VpclmulIterVec n m pL pR (gf128PclmulInitVec y)) acc).w1 =
      gf128VpclmulFieldSum n m pL pR ^^^ gf128Words acc.w0 acc.w1 := by
  unfold gf128VpclmulOutput
  rw [gf128Pclmul_output_reduce]
  change gf128Reduce (gf128VpclmulRaw _) ^^^ _ = _
  rw [gf128Vpclmul_iter_polynomial]
  have hz : gf128VpclmulRaw (gf128PclmulInitVec y) = 0 := by
    simp [gf128VpclmulRaw, gf128PclmulRaw, gf128PclmulInitVec, gf128VpclmulCollapse,
      gf128PclmulXor, evalVecBin256, evalVecShift256, clampVecWidth, Vec256.zero, gf128Words.public_eq_1]
  rw [hz]
  simp only [BitVec.ofNat_eq_ofNat, BitVec.zero_xor, gf128Vpclmul_sum_reduce]

/-- Fresh vpclmul bytes compute accumulation of two portable GF(2^128) products
per iteration for every positive 64-bit pair counter. The mathematical specification uses plain
little-endian polynomial bits and z^128+z^7+z²+z+1. -/
theorem current_rlib_gf2_128_mul_acc_vpclmul_functional
    (s : X86State) (k extra : Nat) (hk : k+1 < 2^64) (hp : s.pc = 0)
    (hh : s.halted = false) (hn : s.gpr.r1 = UInt64.ofNat (k+1)) :
    ∃ slice, findSliceByNameBytes currentX86ExtractedSlices gf128VpclmulName = some slice ∧
      decodeX86Stream slice.code = some gf128VpclmulProg ∧
      (runX86 gf128VpclmulProg (40 + 16*(k+1) + extra) s).1.halted = true ∧
      gf128Words
        (readMem64 (runX86 gf128VpclmulProg (40 + 16*(k+1) + extra) s).1.mem s.gpr.r7)
        (readMem64 (runX86 gf128VpclmulProg (40 + 16*(k+1) + extra) s).1.mem (s.gpr.r7+8)) =
        gf128Words (readMem64 s.mem s.gpr.r7) (readMem64 s.mem (s.gpr.r7+8)) ^^^
          gf128VpclmulFieldSum (k+1) s.mem s.gpr.r6 s.gpr.r2 ∧
      (∀ a : UInt64, (∀ i : Nat, i < 16 → a ≠ s.gpr.r7 + UInt64.ofNat i) →
        (runX86 gf128VpclmulProg (40 + 16*(k+1) + extra) s).1.mem a = s.mem a) := by
  obtain ⟨slice, hf, hd, hm, hh'⟩ := gf128Vpclmul_current_execution s k extra hk hp hh hn
  refine ⟨slice, hf, hd, hh', ?_, ?_⟩
  · rw [hm, readMem64_writeMem128_lo, readMem64_writeMem128_hi]
    simpa only [readMem128, BitVec.xor_comm] using
      gf128Vpclmul_output_field (k+1) s.mem s.gpr.r6 s.gpr.r2 s.ymm (readMem128 s.mem s.gpr.r7)
  · intro a ha
    rw [hm]
    exact writeMem128_outside _ _ _ _ ha

/-- A zero-result specification is refuted on 1·1. -/
theorem gf128Vpclmul_field_zero_tooth :
    gf128VpclmulFieldSum 1 gf128PclmulWitnessState.mem 4096 8192 ≠ 0 :=
  elf_gf128_two_lane_block_ne_zero (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

#tooth_pair current_rlib_gf2_128_mul_acc_vpclmul_functional vs gf128Vpclmul_field_zero_tooth
#verify_inhabited current_rlib_gf2_128_mul_acc_vpclmul_functional gf128Pclmul_execution_inhabited

open SydTv

/-- UTF-8 bytes of `qsag_asm_tower128_bdoz_mac_vpclmul`. -/
def gf128BdozName : List UInt8 := [0x71, 0x73, 0x61, 0x67, 0x5f, 0x61, 0x73, 0x6d, 0x5f, 0x74, 0x6f, 0x77, 0x65, 0x72, 0x31, 0x32, 0x38, 0x5f, 0x62, 0x64, 0x6f, 0x7a, 0x5f, 0x6d, 0x61, 0x63, 0x5f, 0x76, 0x70, 0x63, 0x6c, 0x6d, 0x75, 0x6c]

def gf128BdozFreshProg : List (DecodedInstr X86Instr) := [
  ⟨0, 4, .vbinOp .vpxor true 0 0 0⟩,
  ⟨4, 4, .vbinOp .vpxor true 1 1 1⟩,
  ⟨8, 4, .vload true 2 (.baseDisp 6 0)⟩,
  ⟨12, 4, .vload true 3 (.baseDisp 2 0)⟩,
  ⟨16, 6, .vpclmulqdq true 4 2 3 0x00⟩,
  ⟨22, 6, .vpclmulqdq true 5 2 3 0x11⟩,
  ⟨28, 6, .vpclmulqdq true 6 2 3 0x01⟩,
  ⟨34, 6, .vpclmulqdq true 7 2 3 0x10⟩,
  ⟨40, 4, .vbinOp .vpxor true 6 6 7⟩,
  ⟨44, 5, .vshiftImm .vpslldq true 7 6 8⟩,
  ⟨49, 5, .vshiftImm .vpsrldq true 6 6 8⟩,
  ⟨54, 4, .vbinOp .vpxor true 4 4 7⟩,
  ⟨58, 4, .vbinOp .vpxor true 5 5 6⟩,
  ⟨62, 4, .vbinOp .vpxor true 0 0 4⟩,
  ⟨66, 4, .vbinOp .vpxor true 1 1 5⟩,
  ⟨70, 4, .aluImm .add true 6 32⟩,
  ⟨74, 4, .aluImm .add true 2 32⟩,
  ⟨78, 3, .incDec false true 1⟩,
  ⟨81, 2, .jcc 5 8⟩,
  ⟨83, 5, .movImm false 0 0x87⟩,
  ⟨88, 5, .vmovGprToXmm true 8 0⟩,
  ⟨93, 5, .vpbroadcast true true 8 8⟩,
  ⟨98, 6, .vpclmulqdq true 4 1 8 0x01⟩,
  ⟨104, 5, .vshiftImm .vpslldq true 5 4 8⟩,
  ⟨109, 5, .vshiftImm .vpsrldq true 6 4 8⟩,
  ⟨114, 4, .vbinOp .vpxor true 0 0 5⟩,
  ⟨118, 4, .vbinOp .vpxor true 1 1 6⟩,
  ⟨122, 6, .vpclmulqdq true 4 1 8 0x00⟩,
  ⟨128, 4, .vbinOp .vpxor true 0 0 4⟩,
  ⟨132, 4, .vstore true 0 (.baseDisp 7 0)⟩,
  ⟨136, 4, .vbinOp .vpxor true 0 0 0⟩,
  ⟨140, 4, .vbinOp .vpxor true 1 1 1⟩,
  ⟨144, 4, .vbinOp .vpxor true 2 2 2⟩,
  ⟨148, 4, .vbinOp .vpxor true 3 3 3⟩,
  ⟨152, 4, .vbinOp .vpxor true 4 4 4⟩,
  ⟨156, 4, .vbinOp .vpxor true 5 5 5⟩,
  ⟨160, 4, .vbinOp .vpxor true 6 6 6⟩,
  ⟨164, 4, .vbinOp .vpxor true 7 7 7⟩,
  ⟨168, 5, .vbinOp .vpxor true 8 8 8⟩,
  ⟨173, 2, .aluRegReg .xorOp false 0 0⟩,
  ⟨175, 3, .vzeroall⟩,
  ⟨178, 3, .vzeroupper⟩,
  ⟨181, 2, .aluRegReg .xorOp false 7 7⟩,
  ⟨183, 2, .aluRegReg .xorOp false 6 6⟩,
  ⟨185, 2, .aluRegReg .xorOp false 2 2⟩,
  ⟨187, 2, .aluRegReg .xorOp false 1 1⟩,
  ⟨189, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨192, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨195, 3, .aluRegReg .xorOp false 10 10⟩,
  ⟨198, 3, .aluRegReg .xorOp false 11 11⟩,
  ⟨201, 2, .aluRegReg .xorOp false 0 0⟩,
  ⟨203, 1, .ret⟩
]

def gf128BdozExitObs (rsp outPtr : UInt64) : List StepObs :=
  [⟨83, [], true⟩, ⟨88, [], true⟩, ⟨93, [], true⟩, ⟨98, [], true⟩, ⟨104, [], true⟩,
   ⟨109, [], true⟩, ⟨114, [], true⟩, ⟨118, [], true⟩, ⟨122, [], true⟩, ⟨128, [], true⟩,
   ⟨132, [(outPtr, 32)], true⟩, ⟨136, [], true⟩, ⟨140, [], true⟩, ⟨144, [], true⟩,
   ⟨148, [], true⟩, ⟨152, [], true⟩, ⟨156, [], true⟩, ⟨160, [], true⟩, ⟨164, [], true⟩,
   ⟨168, [], true⟩, ⟨173, [], true⟩, ⟨175, [], true⟩, ⟨178, [], true⟩, ⟨181, [], true⟩, ⟨183, [], true⟩, ⟨185, [], true⟩, ⟨187, [], true⟩, ⟨189, [], true⟩, ⟨192, [], true⟩, ⟨195, [], true⟩, ⟨198, [], true⟩, ⟨201, [], true⟩, ⟨203, [(rsp, 8)], true⟩]

def gf128BdozAsmFfiRun (rsp : UInt64) (n : Word) (baseL baseR outP : UInt64) (mem : UInt64 → UInt8) :
    AsmFfiBdozMac × List StepObs :=
  if n = 0 then
    (⟨baseL, baseR, outP, Vec256.zero, Vec256.zero, 0, mem⟩,
     [⟨0, [], true⟩])
  else
    let loop := runCuts asmFfiVpclmulBodyStep n.toNat ⟨baseL, baseR, outP, Vec256.zero, Vec256.zero, n.toNat, mem⟩
    let red := poly87Reduce256 loop.1.accLo loop.1.accHi
    ({ loop.1 with mem := writeMem256 mem outP red },
     vpclmulEntryObs ++ loop.2 ++ gf128BdozExitObs rsp outP)

theorem gf128BdozEntry (fetch : Nat → Option (DecodedInstr X86Instr))
    (hf : ∀ d ∈ gf128BdozFreshProg, fetch d.offset = some d)
    (g : Bank16 UInt64) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Vec256)
    (cf o zf dy : Bool) (m : UInt64 → UInt8) (fuel : Nat) :
    runX86Fetch fetch (2 + fuel)
      ⟨0, g, ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
        cf, o, zf, dy, false, m⟩ =
      let u := runX86Fetch fetch fuel
        ⟨8, g, ⟨Vec256.zero, Vec256.zero, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
          cf, o, zf, true, false, m⟩
      (u.1, vpclmulEntryObs ++ u.2) := by
  rw [show 2 + fuel = (fuel + 1) + 1 from by omega]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vbinOp256, b16get_0, vpxor_self, b16set_0]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vbinOp256, b16get_1, vpxor_self, b16set_1, vpclmulEntryObs.public_eq_1]
  rfl

theorem gf128BdozBody (fetch : Nat → Option (DecodedInstr X86Instr))
    (hf : ∀ d ∈ gf128BdozFreshProg, fetch d.offset = some d)
    (r0 c pR r3 r4 r5 pL r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (lo hi y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Vec256)
    (cf o zf dy : Bool) (m : UInt64 → UInt8) (fuel : Nat) :
    let s : X86State := ⟨8, ⟨r0, c, pR, r3, r4, r5, pL, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
      ⟨lo, hi, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
      cf, o, zf, dy, false, m⟩
    runX86Fetch fetch (17 + fuel) s =
      ((runX86Fetch fetch fuel (vpclmulBodyStep s).1).1,
       (vpclmulBodyStep s).2 ++ (runX86Fetch fetch fuel (vpclmulBodyStep s).1).2) := by
  dsimp only
  rw [show 17 + fuel = ((((((((((((((((fuel + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 from by omega]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vload256, b16get_6, b16set_2]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vload256, b16get_2, b16set_3]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vpclmul256, b16get_2, b16get_3, b16set_4]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vpclmul256, b16get_2, b16get_3, b16set_5]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vpclmul256, b16get_2, b16get_3, b16set_6]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vpclmul256, b16get_2, b16get_3, b16set_7]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vbinOp256, b16get_6, b16get_7, b16set_6]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vshift256, b16get_6, b16set_7]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vshift256, b16get_6, b16set_6]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vbinOp256, b16get_4, b16get_7, b16set_4]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vbinOp256, b16get_5, b16get_6, b16set_5]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vbinOp256, b16get_0, b16get_4, b16set_0]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vbinOp256, b16get_1, b16get_5, b16set_1]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_addImm64, b16get_6, b16set_6]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_addImm64, b16get_2, b16set_2]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_dec64, b16get_1, b16set_1]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]
  simp only [stepX86Full_jnz, vpclmulBodyStep.public_eq_1, vpclmulBodyObs.public_eq_1,
    b16get_0, b16get_1, b16get_2, b16get_6,
    b16set_0, b16set_1, b16set_2, b16set_3, b16set_4, b16set_5, b16set_6, b16set_7]
  rfl

private theorem gf128BdozVzeroall (off len pc : Nat) (g : Bank16 UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    stepX86 ⟨off, len, .vzeroall⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g, Bank16.ofFn (fun _ => Vec256.zero), cf, o, zf, false, false, m⟩,
        ⟨off, [], true⟩) := by rfl

theorem gf128BdozExit (fetch : Nat → Option (DecodedInstr X86Instr))
    (hf : ∀ d ∈ gf128BdozFreshProg, fetch d.offset = some d)
    (r0 r1 r2 r3 r4 r5 r6 outP r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (lo hi y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Vec256)
    (cf o zf dy : Bool) (m : UInt64 → UInt8) (extra : Nat) :
    runX86Fetch fetch (33 + extra)
      ⟨83, ⟨r0, r1, r2, r3, r4, r5, r6, outP, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨lo, hi, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
        cf, o, zf, dy, false, m⟩ =
      (⟨(readMem64 (writeMem256 m outP (poly87Reduce256 lo hi)) r4).toNat, ⟨0, 0, 0, r3, r4 + 8, r5, 0, 0, 0, 0, 0, 0, r12, r13, r14, r15⟩,
        ⟨Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero⟩,
        false, false, true, false, true, writeMem256 m outP (poly87Reduce256 lo hi)⟩,
       gf128BdozExitObs r4 outP) := by
  have h87 : maskGprWidth false 0x87 = 0x87 := rfl
  rw [show 33 + extra = (((((((((((((((((((((((((((((((((extra + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) from by omega]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_movImm, h87, b16set_0]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vmovGprToXmm, maskGprWidth_true, b16get_0, b16set_8]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vpbroadcastQ, b16get_8, b16set_8]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vpclmul256, b16get_1, b16get_8, b16set_4]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vshift256, b16get_4, b16set_5]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vshift256, b16get_4, b16set_6]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vbinOp256, b16get_0, b16get_5, b16set_0]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vbinOp256, b16get_1, b16get_6, b16set_1]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vpclmul256, b16get_1, b16get_8, b16set_4]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vbinOp256, b16get_0, b16get_4, b16set_0]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vstore256, b16get_7, b16get_0]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vbinOp256, b16get_0, vpxor_self, b16set_0]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vbinOp256, b16get_1, vpxor_self, b16set_1]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vbinOp256, b16get_2, vpxor_self, b16set_2]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vbinOp256, b16get_3, vpxor_self, b16set_3]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vbinOp256, b16get_4, vpxor_self, b16set_4]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vbinOp256, b16get_5, vpxor_self, b16set_5]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vbinOp256, b16get_6, vpxor_self, b16set_6]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vbinOp256, b16get_7, vpxor_self, b16set_7]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vbinOp256, b16get_8, vpxor_self, b16set_8]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_xorRR, b16get_0, mask32_xor_self_eq, u64_zero_beq_true, b16set_0]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [gf128BdozVzeroall]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vzeroupper, vzeroupper_bank16]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_xorRR, b16get_7, mask32_xor_self_eq, u64_zero_beq_true, b16set_7]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_xorRR, b16get_6, mask32_xor_self_eq, u64_zero_beq_true, b16set_6]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_xorRR, b16get_2, mask32_xor_self_eq, u64_zero_beq_true, b16set_2]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_xorRR, b16get_1, mask32_xor_self_eq, u64_zero_beq_true, b16set_1]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_xorRR, b16get_8, mask32_xor_self_eq, u64_zero_beq_true, b16set_8]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_xorRR, b16get_9, mask32_xor_self_eq, u64_zero_beq_true, b16set_9]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_xorRR, b16get_10, mask32_xor_self_eq, u64_zero_beq_true, b16set_10]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_xorRR, b16get_11, mask32_xor_self_eq, u64_zero_beq_true, b16set_11]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_xorRR, b16get_0, mask32_xor_self_eq, u64_zero_beq_true, b16set_0]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]
  simp only [stepX86Full_ret, poly87Reduce256.public_eq_1, gf128BdozExitObs, b16get_4, b16set_4]
  rw [runX86Fetch_halted _ _ _ rfl]
  rfl

theorem gf128BdozReplay (fetch : Nat → Option (DecodedInstr X86Instr))
    (hf : ∀ d ∈ gf128BdozFreshProg, fetch d.offset = some d)
    (s₀ : X86State) (n : Nat) (hn : 0 < n) (hbound : n < 2 ^ 64) (rem : Nat) :
    ∀ v a m fuel, v + rem = n → VpclmulRel s₀ n v a m →
      runX86Fetch fetch (17 * rem + fuel) a =
        let loop := runCuts vpclmulBodyStep rem a
        let u := runX86Fetch fetch fuel loop.1
        (u.1, loop.2 ++ u.2) := by
  induction rem with
  | zero => intro v a m fuel _ _; simp [runCuts.public_eq_1]
  | succ k ih =>
    intro v a m fuel hv hrel
    have hvn : v < n := by omega
    rcases hrel with ⟨cf, o, zf, y2, y3, y4, y5, y6, y7, ha, hpL, hpR, hout, hmr, hmem⟩
    have hrel' : VpclmulRel s₀ n v a m := ⟨cf, o, zf, y2, y3, y4, y5, y6, y7, ha, hpL, hpR, hout, hmr, hmem⟩
    have hbody := (vpclmulPosCert s₀ n hn hbound).body v a m hvn hrel'
    obtain ⟨_, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
      ⟨oy0, oy1, oy2, oy3, oy4, oy5, oy6, oy7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
      _, _, _, _, _, mem⟩ := s₀
    have ha8 : a = ⟨8, ⟨r0, UInt64.ofNat (n - v), ptrStride r2 32 v, r3, r4, r5, ptrStride r6 32 v,
        r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨m.accLo, m.accHi, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
        cf, o, zf, true, false, mem⟩ := by
      simpa [Nat.ne_of_lt hvn, b16get_2, b16get_6,
        b16set_0, b16set_1, b16set_2, b16set_3, b16set_4, b16set_5, b16set_6, b16set_7] using ha
    rw [show 17 * (k + 1) + fuel = 17 + (17 * k + fuel) from by omega, ha8]
    rw [gf128BdozBody fetch hf]
    rw [← ha8]
    rw [ih (v + 1) (vpclmulBodyStep a).1 (asmFfiVpclmulBodyStep m).1 fuel (by omega) hbody.1]
    simp [runCuts.public_eq_2, List.append_assoc]

def gf128BdozFreshCert (fetch : Nat → Option (DecodedInstr X86Instr))
    (hf : ∀ d ∈ gf128BdozFreshProg, fetch d.offset = some d)
    (s₀ : X86State) (fuel : Nat) (hpc : s₀.pc = 0) (hh : s₀.halted = false)
    (n : Word) (hcount : s₀.gpr.get 1 = UInt64.ofBitVec n)
    (hfuel : 17 * n.toNat + 35 ≤ fuel) :
    UnrestrictedLoopCert X86State AsmFfiBdozMac n
      (vpclmulGuardedRun fetch fuel)
      (fun m => gf128BdozAsmFfiRun (s₀.gpr.get 4) n m.lhsPtr m.rhsPtr m.outPtr m.mem)
      vpclmulBodyStep asmFfiVpclmulBodyStep
      s₀ ⟨s₀.gpr.get 6, s₀.gpr.get 2, s₀.gpr.get 7, Vec256.zero, Vec256.zero, n.toNat, s₀.mem⟩
      ⟨8, s₀.gpr.set 1 (UInt64.ofNat n.toNat), (s₀.ymm.set 0 Vec256.zero |>.set 1 Vec256.zero),
        s₀.cf, s₀.ofFlag, s₀.zf, true, false, s₀.mem⟩
      ⟨s₀.gpr.get 6, s₀.gpr.get 2, s₀.gpr.get 7, Vec256.zero, Vec256.zero, n.toNat, s₀.mem⟩
      (VpclmulLoopPost s₀ n.toNat)
      (VpclmulPost s₀ n) where
  zeroSchedule := [⟨0, [], true⟩]
  entrySchedule := vpclmulEntryObs
  bodySchedule := fun v => vpclmulBodyObs (ptrStride (s₀.gpr.get 6) 32 v) (ptrStride (s₀.gpr.get 2) 32 v)
  exitSchedule := gf128BdozExitObs (s₀.gpr.get 4) (s₀.gpr.get 7)
  zero_cut := by
    intro hz; subst hz
    have hg0 : (s₀.gpr.get 1 == 0) = true := by simp [hcount]
    dsimp only [vpclmulGuardedRun, gf128BdozAsmFfiRun]
    rw [ite_eq_left hg0, ite_eq_left rfl]
    obtain ⟨_, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, _, _, _, _, _, _, _⟩ := s₀
    have hr1 : r1 = 0 := hcount
    refine ⟨⟨rfl, rfl, rfl, rfl, hr1, rfl, fun h => absurd rfl h, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      vpclmulExpected_field 0 _ _ _⟩, rfl, rfl⟩
  pos_cert := fun hn =>
    vpclmulPosCert s₀ n.toNat (bv64_pos_of_ne_zero n hn) n.isLt
  pos_sched := fun _ => rfl
  pos_replay := by
    intro hn hlp hal hml
    have hg0 : ¬ ((s₀.gpr.get 1 == 0) = true) := by
      rw [beq_false_of_ne (hcount ▸ (bv64_ne_zero_iff_u64_ne_zero n).mp hn)]; decide
    dsimp only [vpclmulGuardedRun, gf128BdozAsmFfiRun]
    rw [ite_eq_right hg0, ite_eq_right hn]
    obtain ⟨extra, hextra⟩ : ∃ extra, fuel = 2 + (17 * n.toNat + (33 + extra)) :=
      ⟨fuel - (17 * n.toNat + 35), by omega⟩
    rw [hextra]
    obtain ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
      ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
      cf, o, zf, dy, hlt, m⟩ := s₀
    cases hpc; cases hh
    have hr1 : r1 = UInt64.ofNat n.toNat := by
      apply u64_eq_of_toNat_eq
      have : r1 = UInt64.ofBitVec n := hcount
      rw [this, UInt64.toNat_ofNat', Nat.mod_eq_of_lt n.isLt]; rfl
    rw [gf128BdozEntry fetch hf]
    have headEq : (⟨8, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨Vec256.zero, Vec256.zero, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
        cf, o, zf, true, false, m⟩ : X86State) =
      ⟨8, (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15).set 1 (UInt64.ofNat n.toNat),
        ((Bank16.mk y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).set 0 Vec256.zero |>.set 1 Vec256.zero),
        cf, o, zf, true, false, m⟩ := by
      simp [hr1, b16set_0, b16set_1]
    rw [headEq]
    have hpos := bv64_pos_of_ne_zero n hn
    have hrep := gf128BdozReplay fetch hf
      ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩, cf, o, zf, dy, false, m⟩
      n.toNat hpos n.isLt n.toNat 0 _ ⟨r6, r2, r7, Vec256.zero, Vec256.zero, n.toNat, m⟩ (33 + extra) (by omega)
      (vpclmulPosCert _ n.toNat hpos n.isLt).entry
    dsimp only at hrep ⊢
    rw [hrep]
    rcases hlp with ⟨cfL, oL, zfL, y2L, y3L, y4L, y5L, y6L, y7L, haL, _, _, _⟩
    let mFinal := (runCuts asmFfiVpclmulBodyStep n.toNat ⟨r6, r2, r7, Vec256.zero, Vec256.zero, n.toNat, m⟩).1
    have ha83 : (runCuts vpclmulBodyStep n.toNat
        ⟨8, (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15).set 1 (UInt64.ofNat n.toNat),
          ((Bank16.mk y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).set 0 Vec256.zero
            |>.set 1 Vec256.zero),
          cf, o, zf, true, false, m⟩).1 =
      ⟨83, ⟨r0, 0, ptrStride r2 32 n.toNat, r3, r4, r5, ptrStride r6 32 n.toNat,
        r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨mFinal.accLo, mFinal.accHi, y2L, y3L, y4L, y5L, y6L, y7L, y8, y9, y10, y11, y12, y13, y14, y15⟩,
        cfL, oL, zfL, true, false, m⟩ := by
      simpa [mFinal, b16get_2, b16get_6, b16get_7,
        b16set_0, b16set_1, b16set_2, b16set_3, b16set_4, b16set_5, b16set_6, b16set_7] using haL
    rw [ha83, gf128BdozExit fetch hf]
    obtain ⟨hacc, _, _⟩ := asmFfiVpclmul_cuts_accum n.toNat r6 r2 r7 Vec256.zero Vec256.zero n.toNat m
    have hred : poly87Reduce256 mFinal.accLo mFinal.accHi =
        poly87Reduce256 (bdozMacAccum n.toNat m r6 r2 Vec256.zero Vec256.zero).1
          (bdozMacAccum n.toNat m r6 r2 Vec256.zero Vec256.zero).2 := by
      have h1 := congrArg Prod.fst hacc
      have h2 := congrArg Prod.snd hacc
      dsimp only at h1 h2
      rw [h1, h2]
    refine ⟨?_, by simp only [List.append_assoc, b16get_7]; rfl, rfl⟩
    refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, ?_, (by rw [ite_eq_right hn]; rfl), rfl, rfl, rfl, rfl, rfl, rfl, vpclmulExpected_field n m r6 r2⟩
    · simp only [b16get_2, b16get_6, b16get_7, ite_eq_right hn, hred]
    · intro _
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Verified decoding of the fresh symbol, including its expanded epilogue. -/
theorem gf128Bdoz_current_decode :
    (findSliceByNameBytes currentX86ExtractedSlices gf128BdozName).map
      (fun s => decodeX86Stream s.code) = some (some gf128BdozFreshProg) := by
  decide +kernel

private theorem gf128Bdoz_fetch :
    ∀ d ∈ gf128BdozFreshProg, findInstrAtPc d.offset gf128BdozFreshProg = some d := by
  have h : gf128BdozFreshProg.all
      (fun d => findInstrAtPc d.offset gf128BdozFreshProg == some d) = true := by
    decide +kernel
  rw [List.all_eq_true] at h
  intro d hd
  exact beq_iff_eq.mp (h d hd)

/-- Fresh-byte whole-kernel functional equivalence for all positive ABI counts.
Each output lane is the XOR of GF(2^128) products of the matching input lanes.
Aliasing and wrapping pointers are permitted because the only store follows all reads.
Zero counts belong to the Rust wrapper's early return and are not claimed here. -/
theorem current_gf128_tower128_bdoz_mac_vpclmul_functional
    (s : X86State) (n : Word) (fuel : Nat)
    (hn : n ≠ 0) (hpc : s.pc = 0) (hh : s.halted = false)
    (hc : s.gpr.get 1 = UInt64.ofBitVec n) (hfuel : 17 * n.toNat + 35 ≤ fuel) :
    ∃ slice, findSliceByNameBytes currentX86ExtractedSlices gf128BdozName = some slice ∧
      decodeX86Stream slice.code = some gf128BdozFreshProg ∧
      ∃ output : Vec256,
        (runX86 gf128BdozFreshProg fuel s).1.halted = true ∧
        (runX86 gf128BdozFreshProg fuel s).1.mem = writeMem256 s.mem (s.gpr.get 7) output ∧
        ∀ lane : Nat, ∀ hLane : lane < 2,
          gf128Lane output ⟨lane, hLane⟩ =
            gf128BdozFieldSum n.toNat s.mem (s.gpr.get 6) (s.gpr.get 2) ⟨lane, hLane⟩ := by
  have hp := (unrestricted_loop_refinement_sound
    (gf128BdozFreshCert (fun pc => findInstrAtPc pc gf128BdozFreshProg) gf128Bdoz_fetch
      s fuel hpc hh n hc hfuel)).1
  rw [vpclmulGuardedRun_pos _ fuel s n hn hc, ← runX86_eq_runX86Fetch] at hp
  dsimp only [VpclmulPost] at hp
  simp only [hn, ↓reduceIte] at hp
  have hdec := gf128Bdoz_current_decode
  cases hfind : findSliceByNameBytes currentX86ExtractedSlices gf128BdozName with
  | none => rw [hfind] at hdec; cases hdec
  | some slice =>
    rw [hfind] at hdec
    have hd := Option.some.inj hdec
    let acc := bdozMacAccum n.toNat s.mem (s.gpr.get 6) (s.gpr.get 2) Vec256.zero Vec256.zero
    refine ⟨slice, rfl, hd, poly87Reduce256 acc.1 acc.2, hp.1, hp.2.2.1, ?_⟩
    intro lane hLane
    exact gf128_bdozMacAccum_field n.toNat s.mem (s.gpr.get 6) (s.gpr.get 2) lane hLane

def gf128BdozWitnessState : X86State :=
  ⟨0, ⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩,
    Bank16.ofFn (fun _ => Vec256.zero), false, false, false, false, false,
    fun a => if a == 0 then 1 else 0⟩

/-- Mutating the specification to drop the product of the constant coefficients
would predict zero at byte zero, but the fresh kernel produces one. -/
theorem current_gf128_tower128_bdoz_mac_vpclmul_tooth :
    (runX86 gf128BdozFreshProg 52 gf128BdozWitnessState).1.mem 0 ≠ 0 := by
  decide +kernel

theorem current_gf128_tower128_bdoz_mac_vpclmul_inhabited :
    ∃ s : X86State, ∃ n : Word, ∃ fuel : Nat,
      n ≠ 0 ∧ s.pc = 0 ∧ s.halted = false ∧
      s.gpr.get 1 = UInt64.ofBitVec n ∧ 17 * n.toNat + 35 ≤ fuel := by
  refine ⟨gf128BdozWitnessState, 1, 52, ?_⟩
  decide +kernel

#tooth_pair current_gf128_tower128_bdoz_mac_vpclmul_functional vs current_gf128_tower128_bdoz_mac_vpclmul_tooth
#verify_inhabited current_gf128_tower128_bdoz_mac_vpclmul_functional current_gf128_tower128_bdoz_mac_vpclmul_inhabited

section Gf128BdozPclmulKernel

def gf128BdozPclmulName : List UInt8 := [0x71, 0x73, 0x61, 0x67, 0x5f, 0x61, 0x73, 0x6d, 0x5f, 0x74, 0x6f, 0x77, 0x65, 0x72, 0x31, 0x32, 0x38, 0x5f, 0x62, 0x64, 0x6f, 0x7a, 0x5f, 0x6d, 0x61, 0x63, 0x5f, 0x70, 0x63, 0x6c, 0x6d, 0x75, 0x6c]

def gf128BdozPclmulProg : List (DecodedInstr X86Instr) := [
  ⟨0, 4, .vbinOp .vpxor false 0 0 0⟩,
  ⟨4, 4, .vbinOp .vpxor false 1 1 1⟩,
  ⟨8, 4, .vbinOp .vpxor false 2 2 2⟩,
  ⟨12, 4, .vbinOp .vpxor false 3 3 3⟩,
  ⟨16, 4, .vload false 4 (.baseDisp 6 0)⟩,
  ⟨20, 4, .vload false 5 (.baseDisp 2 0)⟩,
  ⟨24, 6, .vpclmulqdq false 6 4 5 0x0⟩,
  ⟨30, 6, .vpclmulqdq false 7 4 5 0x11⟩,
  ⟨36, 6, .vpclmulqdq false 8 4 5 0x1⟩,
  ⟨42, 6, .vpclmulqdq false 9 4 5 0x10⟩,
  ⟨48, 5, .vbinOp .vpxor false 8 8 9⟩,
  ⟨53, 6, .vshiftImm .vpslldq false 9 8 0x8⟩,
  ⟨59, 6, .vshiftImm .vpsrldq false 8 8 0x8⟩,
  ⟨65, 4, .vbinOp .vpxor false 6 9 6⟩,
  ⟨69, 4, .vbinOp .vpxor false 7 8 7⟩,
  ⟨73, 4, .vbinOp .vpxor false 0 0 6⟩,
  ⟨77, 4, .vbinOp .vpxor false 1 1 7⟩,
  ⟨81, 5, .vload false 4 (.baseDisp 6 0x10)⟩,
  ⟨86, 5, .vload false 5 (.baseDisp 2 0x10)⟩,
  ⟨91, 6, .vpclmulqdq false 6 4 5 0x0⟩,
  ⟨97, 6, .vpclmulqdq false 7 4 5 0x11⟩,
  ⟨103, 6, .vpclmulqdq false 8 4 5 0x1⟩,
  ⟨109, 6, .vpclmulqdq false 9 4 5 0x10⟩,
  ⟨115, 5, .vbinOp .vpxor false 8 8 9⟩,
  ⟨120, 6, .vshiftImm .vpslldq false 9 8 0x8⟩,
  ⟨126, 6, .vshiftImm .vpsrldq false 8 8 0x8⟩,
  ⟨132, 4, .vbinOp .vpxor false 6 9 6⟩,
  ⟨136, 4, .vbinOp .vpxor false 7 8 7⟩,
  ⟨140, 4, .vbinOp .vpxor false 2 2 6⟩,
  ⟨144, 4, .vbinOp .vpxor false 3 3 7⟩,
  ⟨148, 4, .aluImm .add true 6 0x20⟩,
  ⟨152, 4, .aluImm .add true 2 0x20⟩,
  ⟨156, 3, .incDec false true 1⟩,
  ⟨159, 6, .jcc 5 16⟩,
  ⟨165, 5, .movImm false 0 0x87⟩,
  ⟨170, 5, .vmovGprToXmm true 10 0⟩,
  ⟨175, 6, .vpclmulqdq false 6 1 10 0x1⟩,
  ⟨181, 5, .vshiftImm .vpslldq false 7 6 0x8⟩,
  ⟨186, 5, .vshiftImm .vpsrldq false 8 6 0x8⟩,
  ⟨191, 4, .vbinOp .vpxor false 0 0 7⟩,
  ⟨195, 4, .vbinOp .vpxor false 1 8 1⟩,
  ⟨199, 6, .vpclmulqdq false 6 1 10 0x0⟩,
  ⟨205, 4, .vbinOp .vpxor false 0 0 6⟩,
  ⟨209, 4, .vstore false 0 (.baseDisp 7 0)⟩,
  ⟨213, 6, .vpclmulqdq false 6 3 10 0x1⟩,
  ⟨219, 5, .vshiftImm .vpslldq false 7 6 0x8⟩,
  ⟨224, 5, .vshiftImm .vpsrldq false 8 6 0x8⟩,
  ⟨229, 4, .vbinOp .vpxor false 2 2 7⟩,
  ⟨233, 4, .vbinOp .vpxor false 3 8 3⟩,
  ⟨237, 6, .vpclmulqdq false 6 3 10 0x0⟩,
  ⟨243, 4, .vbinOp .vpxor false 2 2 6⟩,
  ⟨247, 5, .vstore false 2 (.baseDisp 7 0x10)⟩,
  ⟨252, 4, .vbinOp .vpxor false 0 0 0⟩,
  ⟨256, 4, .vbinOp .vpxor false 1 1 1⟩,
  ⟨260, 4, .vbinOp .vpxor false 2 2 2⟩,
  ⟨264, 4, .vbinOp .vpxor false 3 3 3⟩,
  ⟨268, 4, .vbinOp .vpxor false 4 4 4⟩,
  ⟨272, 4, .vbinOp .vpxor false 5 5 5⟩,
  ⟨276, 4, .vbinOp .vpxor false 6 6 6⟩,
  ⟨280, 4, .vbinOp .vpxor false 7 7 7⟩,
  ⟨284, 5, .vbinOp .vpxor false 8 8 8⟩,
  ⟨289, 5, .vbinOp .vpxor false 9 9 9⟩,
  ⟨294, 5, .vbinOp .vpxor false 10 10 10⟩,
  ⟨299, 2, .aluRegReg .xorOp false 0 0⟩,
  ⟨301, 3, .vzeroall⟩,
  ⟨304, 3, .vzeroupper⟩,
  ⟨307, 2, .aluRegReg .xorOp false 7 7⟩,
  ⟨309, 2, .aluRegReg .xorOp false 6 6⟩,
  ⟨311, 2, .aluRegReg .xorOp false 2 2⟩,
  ⟨313, 2, .aluRegReg .xorOp false 1 1⟩,
  ⟨315, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨318, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨321, 3, .aluRegReg .xorOp false 10 10⟩,
  ⟨324, 3, .aluRegReg .xorOp false 11 11⟩,
  ⟨327, 2, .aluRegReg .xorOp false 0 0⟩,
  ⟨329, 1, .ret⟩
]

theorem gf128BdozPclmul_current_decode :
    (findSliceByNameBytes currentX86ExtractedSlices gf128BdozPclmulName).map
      (fun s => decodeX86Stream s.code) = some (some gf128BdozPclmulProg) := by
  decide +kernel

def gf128BdozPclmulLift (v : Vec128) : Vec256 := ⟨v.w0, v.w1, 0, 0⟩
def gf128BdozPclmulXor (a b : Vec256) : Vec256 :=
  clampVecWidth false (evalVecBin256 .vpxor a b)
def gf128BdozPclmulShiftL (a : Vec256) : Vec256 :=
  clampVecWidth false (evalVecShift256 .vpslldq a 8)
def gf128BdozPclmulShiftR (a : Vec256) : Vec256 :=
  clampVecWidth false (evalVecShift256 .vpsrldq a 8)
def gf128BdozPclmulMid (a b : Vec256) : Vec256 :=
  gf128BdozPclmulXor (gf128BdozPclmulLift (clmul64 a.w1 b.w0))
    (gf128BdozPclmulLift (clmul64 a.w0 b.w1))
def gf128BdozPclmulLo (a b : Vec256) : Vec256 :=
  gf128BdozPclmulXor (gf128BdozPclmulShiftL (gf128BdozPclmulMid a b))
    (gf128BdozPclmulLift (clmul64 a.w0 b.w0))
def gf128BdozPclmulHi (a b : Vec256) : Vec256 :=
  gf128BdozPclmulXor (gf128BdozPclmulShiftR (gf128BdozPclmulMid a b))
    (gf128BdozPclmulLift (clmul64 a.w1 b.w1))

def gf128BdozPclmulBodyVec (y : Bank16 Vec256) (a0 b0 a1 b1 : Vec256) : Bank16 Vec256 :=
  ⟨gf128BdozPclmulXor y.r0 (gf128BdozPclmulLo a0 b0),
   gf128BdozPclmulXor y.r1 (gf128BdozPclmulHi a0 b0),
   gf128BdozPclmulXor y.r2 (gf128BdozPclmulLo a1 b1),
   gf128BdozPclmulXor y.r3 (gf128BdozPclmulHi a1 b1),
   a1, b1, gf128BdozPclmulLo a1 b1, gf128BdozPclmulHi a1 b1,
   gf128BdozPclmulShiftR (gf128BdozPclmulMid a1 b1),
   gf128BdozPclmulShiftL (gf128BdozPclmulMid a1 b1),
   y.r10, y.r11, y.r12, y.r13, y.r14, y.r15⟩


def gf128BdozPclmulHalf0Vec (y : Bank16 Vec256) (a b : Vec256) : Bank16 Vec256 :=
  ⟨gf128BdozPclmulXor y.r0 (gf128BdozPclmulLo a b),
   gf128BdozPclmulXor y.r1 (gf128BdozPclmulHi a b), y.r2, y.r3,
   a, b, gf128BdozPclmulLo a b, gf128BdozPclmulHi a b,
   gf128BdozPclmulShiftR (gf128BdozPclmulMid a b),
   gf128BdozPclmulShiftL (gf128BdozPclmulMid a b),
   y.r10, y.r11, y.r12, y.r13, y.r14, y.r15⟩

def gf128BdozPclmulHalf1Vec (y : Bank16 Vec256) (a b : Vec256) : Bank16 Vec256 :=
  ⟨y.r0, y.r1, gf128BdozPclmulXor y.r2 (gf128BdozPclmulLo a b),
   gf128BdozPclmulXor y.r3 (gf128BdozPclmulHi a b),
   a, b, gf128BdozPclmulLo a b, gf128BdozPclmulHi a b,
   gf128BdozPclmulShiftR (gf128BdozPclmulMid a b),
   gf128BdozPclmulShiftL (gf128BdozPclmulMid a b),
   y.r10, y.r11, y.r12, y.r13, y.r14, y.r15⟩

private theorem gf128BdozPclmul_half0_steps
    (g : Bank16 UInt64) (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    StepsX86 gf128BdozPclmulProg 13 ⟨16, g, y, cf, o, zf, dy, false, m⟩
      ⟨81, g, gf128BdozPclmulHalf0Vec y
        (gf128BdozPclmulLift (readMem128 m g.r6))
        (gf128BdozPclmulLift (readMem128 m g.r2)), cf, o, zf, dy, false, m⟩ := by
  iterate 13
    apply StepsX86.cons rfl rfl
    · simp only [stepX86, evalX86Addr, clampVecWidth, evalVecBin256, u64_add_zero, Bool.or_false]
      rfl
  unfold gf128BdozPclmulHalf0Vec gf128BdozPclmulLo gf128BdozPclmulHi
    gf128BdozPclmulMid gf128BdozPclmulShiftL gf128BdozPclmulShiftR
    gf128BdozPclmulLift gf128BdozPclmulXor
  dsimp only [Bank16.get, Bank16.set, clampVecWidth, evalVecBin256, evalVecShift256]
  simp only [UInt64.xor_zero]
  exact StepsX86.zero _

private theorem gf128BdozPclmul_half1_steps
    (g : Bank16 UInt64) (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    StepsX86 gf128BdozPclmulProg 13 ⟨81, g, y, cf, o, zf, dy, false, m⟩
      ⟨148, g, gf128BdozPclmulHalf1Vec y
        (gf128BdozPclmulLift (readMem128 m (g.r6+16)))
        (gf128BdozPclmulLift (readMem128 m (g.r2+16))), cf, o, zf, dy, false, m⟩ := by
  iterate 13
    apply StepsX86.cons rfl rfl
    · simp only [stepX86, evalX86Addr, clampVecWidth, evalVecBin256, Bool.or_false]
      rfl
  unfold gf128BdozPclmulHalf1Vec gf128BdozPclmulLo gf128BdozPclmulHi
    gf128BdozPclmulMid gf128BdozPclmulShiftL gf128BdozPclmulShiftR
    gf128BdozPclmulLift gf128BdozPclmulXor
  dsimp only [Bank16.get, Bank16.set, clampVecWidth, evalVecBin256, evalVecShift256]
  simp only [UInt64.xor_zero]
  exact StepsX86.zero _

private theorem gf128BdozPclmul_control_steps
    (g : Bank16 UInt64) (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    StepsX86 gf128BdozPclmulProg 4 ⟨148, g, y, cf, o, zf, dy, false, m⟩
      ⟨jccPc (!((g.r1 - 1) == 0)) 16 165,
        {g with r1 := g.r1 - 1, r2 := g.r2 + 32, r6 := g.r6 + 32}, y,
        decide (g.r2.toNat + (32 : UInt64).toNat ≥ 0x10000000000000000),
        evalX86IncDecOf false true g.r1, (g.r1 - 1) == 0, dy, false, m⟩ := by
  iterate 2
    apply StepsX86.cons rfl rfl
    · rw [stepX86_addImm64]
  apply StepsX86.cons rfl rfl
  · rw [stepX86_dec64]
  apply StepsX86.cons rfl rfl
  · rw [stepX86_jnz]
  exact StepsX86.zero _

private theorem gf128BdozPclmul_body_one_iter
    (g : Bank16 UInt64) (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    StepsX86 gf128BdozPclmulProg 30
      ⟨16, g, y, cf, o, zf, dy, false, m⟩
      ⟨jccPc (!((g.r1 - 1) == 0)) 16 165,
        {g with r1 := g.r1 - 1, r2 := g.r2 + 32, r6 := g.r6 + 32},
        gf128BdozPclmulBodyVec y
          (gf128BdozPclmulLift (readMem128 m g.r6))
          (gf128BdozPclmulLift (readMem128 m g.r2))
          (gf128BdozPclmulLift (readMem128 m (g.r6+16)))
          (gf128BdozPclmulLift (readMem128 m (g.r2+16))),
        decide (g.r2.toNat + (32 : UInt64).toNat ≥ 0x10000000000000000),
        evalX86IncDecOf false true g.r1, (g.r1 - 1) == 0, dy, false, m⟩ := by
  have h0 := gf128BdozPclmul_half0_steps g y cf o zf dy m
  have h1 := gf128BdozPclmul_half1_steps g
    (gf128BdozPclmulHalf0Vec y (gf128BdozPclmulLift (readMem128 m g.r6))
      (gf128BdozPclmulLift (readMem128 m g.r2))) cf o zf dy m
  have ht := gf128BdozPclmul_control_steps g
    (gf128BdozPclmulBodyVec y (gf128BdozPclmulLift (readMem128 m g.r6))
      (gf128BdozPclmulLift (readMem128 m g.r2))
      (gf128BdozPclmulLift (readMem128 m (g.r6+16)))
      (gf128BdozPclmulLift (readMem128 m (g.r2+16)))) cf o zf dy m
  exact StepsX86_trans (StepsX86_trans h0 h1) ht

def gf128BdozPclmulIterVec : Nat → (UInt64 → UInt8) → UInt64 → UInt64 → Bank16 Vec256 → Bank16 Vec256
  | 0, _, _, _, y => y
  | n+1, m, pL, pR, y => gf128BdozPclmulIterVec n m (pL+32) (pR+32)
      (gf128BdozPclmulBodyVec y
        (gf128BdozPclmulLift (readMem128 m pL)) (gf128BdozPclmulLift (readMem128 m pR))
        (gf128BdozPclmulLift (readMem128 m (pL+16))) (gf128BdozPclmulLift (readMem128 m (pR+16))))

private theorem gf128BdozPclmul_loop_steps (k : Nat) (hk : k+1 < 2^64)
    (g : Bank16 UInt64) (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    ∃ cf' o' zf', StepsX86 gf128BdozPclmulProg (30 * (k+1))
      ⟨16, {g with r1 := UInt64.ofNat (k+1)}, y, cf, o, zf, dy, false, m⟩
      ⟨165, {g with r1 := 0, r2 := g.r2 + UInt64.ofNat (32*(k+1)), r6 := g.r6 + UInt64.ofNat (32*(k+1))},
        gf128BdozPclmulIterVec (k+1) m g.r6 g.r2 y, cf', o', zf', dy, false, m⟩ := by
  induction k generalizing g y cf o zf with
  | zero =>
    have h := gf128BdozPclmul_body_one_iter {g with r1 := 1} y cf o zf dy m
    have hd : (1 : UInt64) - 1 = 0 := by decide
    dsimp only at h
    rw [hd, u64_zero_beq_zero] at h
    exact ⟨_, _, _, h⟩
  | succ k ih =>
    have hd : UInt64.ofNat (k+1+1) - 1 = UInt64.ofNat (k+1) := by
      apply UInt64.eq_of_toBitVec_eq
      apply BitVec.eq_of_toNat_eq
      have hb : k+1 < 2^64 := by omega
      simp [UInt64.toNat_toBitVec, Nat.mod_eq_of_lt hb]
    have hz : (UInt64.ofNat (k+1) == 0) = false := by
      cases h : UInt64.ofNat (k+1) == 0
      · rfl
      · have hn := congrArg UInt64.toNat (beq_iff_eq.mp h)
        have hb : k+1 < 2^64 := by omega
        rw [show (UInt64.ofNat (k+1)).toNat = k+1 from Nat.mod_eq_of_lt hb] at hn
        change k+1 = 0 at hn
        omega
    have h := gf128BdozPclmul_body_one_iter {g with r1 := UInt64.ofNat (k+1+1)} y cf o zf dy m
    dsimp only at h
    rw [hd, hz] at h
    rw [show jccPc (!false) 16 165 = 16 from rfl] at h
    obtain ⟨cf', o', zf', hr⟩ := ih (by omega)
      {g with r2 := g.r2+32, r6 := g.r6+32}
      (gf128BdozPclmulBodyVec y (gf128BdozPclmulLift (readMem128 m g.r6))
        (gf128BdozPclmulLift (readMem128 m g.r2))
        (gf128BdozPclmulLift (readMem128 m (g.r6+16)))
        (gf128BdozPclmulLift (readMem128 m (g.r2+16))))
      (decide (g.r2.toNat + (32 : UInt64).toNat ≥ 0x10000000000000000))
      (evalX86IncDecOf false true (UInt64.ofNat (k+1+1))) false
    have hc := StepsX86_trans h hr
    have he : 30 + 30 * (k+1) = 30 * (k+1+1) := by omega
    have hp (p : UInt64) : (p+32) + UInt64.ofNat (32*(k+1)) = p + UInt64.ofNat (32*(k+1+1)) := by
      apply UInt64.eq_of_toBitVec_eq
      simp only [UInt64.toBitVec_add, BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp [UInt64.toNat_toBitVec]
      omega
    dsimp only at hc
    rw [he, hp, hp] at hc
    exact ⟨cf', o', zf', hc⟩

def gf128BdozPclmulReduce (lo hi : Vec256) : Vec128 :=
  let r1 := gf128BdozPclmulLift (clmul64 hi.w1 0x87)
  let l1 := gf128BdozPclmulXor lo (gf128BdozPclmulShiftL r1)
  let h1 := gf128BdozPclmulXor (gf128BdozPclmulShiftR r1) hi
  let r := gf128BdozPclmulXor l1 (gf128BdozPclmulLift (clmul64 h1.w0 0x87))
  ⟨r.w0, r.w1⟩

private theorem gf128BdozPclmul_exit_steps
    (g : Bank16 UInt64) (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    StepsX86 gf128BdozPclmulProg 42 ⟨165, g, y, cf, o, zf, dy, false, m⟩
      ⟨(readMem64 (writeMem128 (writeMem128 m g.r7 (gf128BdozPclmulReduce y.r0 y.r1))
          (g.r7+16) (gf128BdozPclmulReduce y.r2 y.r3)) g.r4).toNat,
        {g with r0 := 0, r1 := 0, r2 := 0, r4 := g.r4 + 8, r6 := 0, r7 := 0, r8 := 0, r9 := 0, r10 := 0, r11 := 0},
        Bank16.const Vec256.zero, false, false, true, false, true,
        writeMem128 (writeMem128 m g.r7 (gf128BdozPclmulReduce y.r0 y.r1))
          (g.r7+16) (gf128BdozPclmulReduce y.r2 y.r3)⟩ := by
  iterate 18
    apply StepsX86.cons rfl rfl
    · simp only [stepX86, evalX86Addr, clampVecWidth, evalVecBin256,
        maskGprWidth, u64_add_zero, Bool.or_false]
      rfl
  iterate 11
    apply StepsX86.cons rfl rfl
    · simp only [stepX86, clampVecWidth, evalVecBin256, u64_xor_self, Bool.or_false]
      rfl
  apply StepsX86.cons rfl rfl
  · simp only [stepX86_xorRR, mask32_xor_self, u64_zero_beq_zero]
    rfl
  apply StepsX86.cons rfl rfl
  · rw [current_vzeroall_step]
  apply StepsX86.cons rfl rfl
  · rw [current_vzeroupper_zero_step]
  iterate 9
    apply StepsX86.cons rfl rfl
    · simp only [stepX86_xorRR, mask32_xor_self, u64_zero_beq_zero]
      rfl
  apply StepsX86.cons rfl rfl
  · rfl
  unfold gf128BdozPclmulReduce gf128BdozPclmulXor gf128BdozPclmulLift
    gf128BdozPclmulShiftL gf128BdozPclmulShiftR
  exact StepsX86.zero _

def gf128BdozPclmulInitVec (y : Bank16 Vec256) : Bank16 Vec256 :=
  { y with r0 := Vec256.zero, r1 := Vec256.zero, r2 := Vec256.zero, r3 := Vec256.zero }

private theorem gf128BdozPclmul_entry_steps
    (g : Bank16 UInt64) (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    StepsX86 gf128BdozPclmulProg 4 ⟨0, g, y, cf, o, zf, dy, false, m⟩
      ⟨16, g, gf128BdozPclmulInitVec y, cf, o, zf, dy, false, m⟩ := by
  iterate 4
    apply StepsX86.cons rfl rfl
    · simp only [stepX86, clampVecWidth, evalVecBin256, u64_xor_self, Bool.or_false]
      rfl
  exact StepsX86.zero _

private theorem gf128BdozPclmul_whole_memory (k : Nat) (hk : k+1 < 2^64)
    (s : X86State) (hp : s.pc = 0) (hh : s.halted = false)
    (hn : s.gpr.r1 = UInt64.ofNat (k+1)) (extra : Nat) :
    let y := gf128BdozPclmulIterVec (k+1) s.mem s.gpr.r6 s.gpr.r2 (gf128BdozPclmulInitVec s.ymm)
    (runX86 gf128BdozPclmulProg (46 + 30*(k+1) + extra) s).1.mem =
      writeMem128 (writeMem128 s.mem s.gpr.r7 (gf128BdozPclmulReduce y.r0 y.r1))
        (s.gpr.r7+16) (gf128BdozPclmulReduce y.r2 y.r3) ∧
    (runX86 gf128BdozPclmulProg (46 + 30*(k+1) + extra) s).1.halted = true := by
  rcases s with ⟨pc, g, y, cf, o, zf, dy, halted, m⟩
  dsimp only at hp hh hn ⊢
  subst pc halted
  have he := gf128BdozPclmul_entry_steps g y cf o zf dy m
  obtain ⟨cf', o', zf', hl⟩ := gf128BdozPclmul_loop_steps k hk g (gf128BdozPclmulInitVec y) cf o zf dy m
  have hg : {g with r1 := UInt64.ofNat (k+1)} = g := by rw [←hn]
  rw [hg] at hl
  have hx := gf128BdozPclmul_exit_steps
    {g with r1 := 0, r2 := g.r2 + UInt64.ofNat (32*(k+1)), r6 := g.r6 + UInt64.ofNat (32*(k+1))}
    (gf128BdozPclmulIterVec (k+1) m g.r6 g.r2 (gf128BdozPclmulInitVec y)) cf' o' zf' dy m
  have h := (StepsX86_trans (StepsX86_trans he hl) hx).toExecReaches.run extra
  have hc : 4 + 30*(k+1) + 42 = 46 + 30*(k+1) := by omega
  rw [hc] at h
  rw [h.1, runX86_halted_fst _ _ _ rfl]
  exact ⟨rfl, rfl⟩

/-- Polynomial represented by one pair of 128-bit accumulator registers. -/
def gf128BdozPclmulPair (lo hi : Vec256) : BitVec 256 :=
  gf128Words hi.w0 hi.w1 ++ gf128Words lo.w0 lo.w1

def gf128BdozPclmulRaw (y : Bank16 Vec256) (lane : Bool) : BitVec 256 :=
  if lane then gf128BdozPclmulPair y.r2 y.r3 else gf128BdozPclmulPair y.r0 y.r1

private theorem gf128BdozPclmulShiftL_words (v : Vec256) :
    gf128BdozPclmulShiftL v = ⟨0, v.w0, 0, 0⟩ := by
  simp [gf128BdozPclmulShiftL, evalVecShift256, clampVecWidth]

private theorem gf128BdozPclmulShiftR_words (v : Vec256) :
    gf128BdozPclmulShiftR v = ⟨v.w1, 0, 0, 0⟩ := by
  simp [gf128BdozPclmulShiftR, evalVecShift256, clampVecWidth]

private theorem gf128BdozPclmul_pair_product (lo hi a b : Vec256) :
    gf128BdozPclmulPair (gf128BdozPclmulXor lo (gf128BdozPclmulLo a b))
      (gf128BdozPclmulXor hi (gf128BdozPclmulHi a b)) =
      gf128BdozPclmulPair lo hi ^^^
        gf128PolyMul ((gf128Words a.w0 a.w1).setWidth 256) (gf128Words b.w0 b.w1) := by
  rw [← gf128_clmul_four_words]
  simp only [gf128BdozPclmulLo, gf128BdozPclmulHi,
    gf128BdozPclmulShiftL_words, gf128BdozPclmulShiftR_words,
    gf128BdozPclmulMid, gf128BdozPclmulXor, gf128BdozPclmulLift,
    evalVecBin256, clampVecWidth, Bool.false_eq_true, ↓reduceIte,
    gf128BdozPclmulPair, UInt64.zero_xor, UInt64.xor_zero]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [gf128Words.public_eq_1, BitVec.getLsbD_append, UInt64.toBitVec_xor, BitVec.getLsbD_xor]
  by_cases h0 : i < 128
  · by_cases h1 : i < 64 <;> simp only [h0, h1, ↓reduceIte] <;>
      first | rfl | simp only [Bool.xor_assoc, Bool.xor_comm]
  · by_cases h1 : i-128 < 64 <;> simp only [h0, h1, ↓reduceIte] <;>
      first | rfl | simp only [Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]

private theorem gf128BdozPclmul_body_polynomial (y : Bank16 Vec256)
    (a0 b0 a1 b1 : Vec256) (lane : Bool) :
    gf128BdozPclmulRaw (gf128BdozPclmulBodyVec y a0 b0 a1 b1) lane =
      gf128BdozPclmulRaw y lane ^^^
      gf128PolyMul ((gf128Words (if lane then a1.w0 else a0.w0)
        (if lane then a1.w1 else a0.w1)).setWidth 256)
        (gf128Words (if lane then b1.w0 else b0.w0) (if lane then b1.w1 else b0.w1)) := by
  cases lane
  · exact gf128BdozPclmul_pair_product y.r0 y.r1 a0 b0
  · exact gf128BdozPclmul_pair_product y.r2 y.r3 a1 b1

/-- XOR sum of unreduced products in lane 0 or lane 1 of the 32-byte input blocks. -/
def gf128BdozPclmulPolySum : Nat → (UInt64 → UInt8) → UInt64 → UInt64 → Bool → BitVec 256
  | 0, _, _, _, _ => 0
  | n+1, m, pL, pR, lane =>
      let a := readMem128 m (pL + if lane then 16 else 0)
      let b := readMem128 m (pR + if lane then 16 else 0)
      gf128PolyMul ((gf128Words a.w0 a.w1).setWidth 256) (gf128Words b.w0 b.w1) ^^^
        gf128BdozPclmulPolySum n m (pL+32) (pR+32) lane

/-- Mathematical field dot product in one of the two independent 128-bit lanes. -/
def gf128BdozPclmulFieldSum : Nat → (UInt64 → UInt8) → UInt64 → UInt64 → Bool → BitVec 128
  | 0, _, _, _, _ => 0
  | n+1, m, pL, pR, lane =>
      let a := readMem128 m (pL + if lane then 16 else 0)
      let b := readMem128 m (pR + if lane then 16 else 0)
      gf128FieldMul (gf128Words a.w0 a.w1) (gf128Words b.w0 b.w1) ^^^
        gf128BdozPclmulFieldSum n m (pL+32) (pR+32) lane

private theorem gf128BdozPclmul_iter_polynomial (n : Nat) (m : UInt64 → UInt8)
    (pL pR : UInt64) (y : Bank16 Vec256) (lane : Bool) :
    gf128BdozPclmulRaw (gf128BdozPclmulIterVec n m pL pR y) lane =
      gf128BdozPclmulRaw y lane ^^^ gf128BdozPclmulPolySum n m pL pR lane := by
  induction n generalizing pL pR y with
  | zero => simp only [gf128BdozPclmulIterVec, gf128BdozPclmulPolySum,
      BitVec.ofNat_eq_ofNat, BitVec.xor_zero]
  | succ n ih =>
    simp only [gf128BdozPclmulIterVec, ih, gf128BdozPclmul_body_polynomial,
      gf128BdozPclmulPolySum, gf128BdozPclmulLift, BitVec.xor_assoc]
    cases lane <;> simp

private theorem gf128BdozPclmul_sum_reduce (n : Nat) (m : UInt64 → UInt8)
    (pL pR : UInt64) (lane : Bool) :
    gf128Reduce (gf128BdozPclmulPolySum n m pL pR lane) =
      gf128BdozPclmulFieldSum n m pL pR lane := by
  induction n generalizing pL pR with
  | zero => exact elf_gf128Reduce_zero
  | succ n ih =>
    simp only [gf128BdozPclmulPolySum, gf128BdozPclmulFieldSum, gf128Reduce_xor, ih, gf128FieldMul.public_eq_1]

private theorem gf128BdozPclmul_output_reduce (lo hi : Vec256) :
    gf128Words (gf128BdozPclmulReduce lo hi).w0 (gf128BdozPclmulReduce lo hi).w1 =
      gf128Reduce (gf128BdozPclmulPair lo hi) := by
  unfold gf128BdozPclmulPair
  rw [← gf128WordReduce_eq_reduce]
  simp [gf128BdozPclmulReduce, gf128BdozPclmulLift, gf128BdozPclmulXor,
    gf128BdozPclmulShiftL, gf128BdozPclmulShiftR, gf128WordReduce.public_eq_1,
    clampVecWidth, evalVecBin256, evalVecShift256, UInt64.xor_comm]

private theorem gf128BdozPclmul_output_field (n : Nat) (m : UInt64 → UInt8)
    (pL pR : UInt64) (y : Bank16 Vec256) (lane : Bool) :
    let z := gf128BdozPclmulIterVec n m pL pR (gf128BdozPclmulInitVec y)
    let output := if lane then gf128BdozPclmulReduce z.r2 z.r3 else gf128BdozPclmulReduce z.r0 z.r1
    gf128Words output.w0 output.w1 = gf128BdozPclmulFieldSum n m pL pR lane := by
  have hraw := gf128BdozPclmul_iter_polynomial n m pL pR (gf128BdozPclmulInitVec y) lane
  have hz : gf128BdozPclmulRaw (gf128BdozPclmulInitVec y) lane = 0 := by
    cases lane <;> change (gf128Words 0 0 ++ gf128Words 0 0) = (0 : BitVec 256) <;>
      (rw [elf_gf128Words_zero_zero]; decide)
  rw [hz] at hraw
  simp only [BitVec.ofNat_eq_ofNat, BitVec.zero_xor] at hraw
  have h := congrArg gf128Reduce hraw
  rw [gf128BdozPclmul_sum_reduce] at h
  cases lane <;> simpa only [gf128BdozPclmulRaw, Bool.false_eq_true, ↓reduceIte, gf128BdozPclmul_output_reduce] using h

/-- Fresh pclmul BDOZ bytes compute each lane's field dot product for every
positive ABI count. All reads precede both stores, so input/output aliasing is allowed. -/
theorem current_rlib_tower128_bdoz_mac_pclmul_functional
    (s : X86State) (k extra : Nat) (hk : k+1 < 2^64) (hp : s.pc = 0)
    (hh : s.halted = false) (hn : s.gpr.r1 = UInt64.ofNat (k+1)) :
    ∃ slice, findSliceByNameBytes currentX86ExtractedSlices gf128BdozPclmulName = some slice ∧
      decodeX86Stream slice.code = some gf128BdozPclmulProg ∧
      ∃ output0 output1 : Vec128,
        (runX86 gf128BdozPclmulProg (46 + 30*(k+1) + extra) s).1.halted = true ∧
        (runX86 gf128BdozPclmulProg (46 + 30*(k+1) + extra) s).1.mem =
          writeMem128 (writeMem128 s.mem s.gpr.r7 output0) (s.gpr.r7+16) output1 ∧
        gf128Words output0.w0 output0.w1 = gf128BdozPclmulFieldSum (k+1) s.mem s.gpr.r6 s.gpr.r2 false ∧
        gf128Words output1.w0 output1.w1 = gf128BdozPclmulFieldSum (k+1) s.mem s.gpr.r6 s.gpr.r2 true := by
  have hd := gf128BdozPclmul_current_decode
  cases hf : findSliceByNameBytes currentX86ExtractedSlices gf128BdozPclmulName with
  | none => rw [hf] at hd; contradiction
  | some slice =>
    rw [hf] at hd
    obtain ⟨hm, hh'⟩ := gf128BdozPclmul_whole_memory k hk s hp hh hn extra
    refine ⟨slice, rfl, Option.some.inj hd, _, _, hh', hm, ?_, ?_⟩
    · exact gf128BdozPclmul_output_field (k+1) s.mem s.gpr.r6 s.gpr.r2 s.ymm false
    · exact gf128BdozPclmul_output_field (k+1) s.mem s.gpr.r6 s.gpr.r2 s.ymm true

def gf128BdozPclmulWitnessState : X86State :=
  ⟨0, ⟨0, 1, 8192, 0, 0, 0, 4096, 12288, 0, 0, 0, 0, 0, 0, 0, 0⟩,
   Bank16.const Vec256.zero, false, false, false, false, false,
   fun a => if a == 4096 || a == 8192 then 1 else 0⟩

theorem gf128BdozPclmul_inhabited :
    ∃ (s : X86State) (k extra : Nat), k+1 < 2^64 ∧ s.pc = 0 ∧
      s.halted = false ∧ s.gpr.r1 = UInt64.ofNat (k+1) ∧ extra = 0 := by
  exact ⟨gf128BdozPclmulWitnessState, 0, 0, by decide, rfl, rfl, rfl, rfl⟩

theorem gf128BdozPclmul_zero_spec_tooth :
    gf128BdozPclmulFieldSum 1 gf128BdozPclmulWitnessState.mem 4096 8192 false ≠ 0 :=
  elf_gf128_one_block_ne_zero (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

#tooth_pair current_rlib_tower128_bdoz_mac_pclmul_functional vs gf128BdozPclmul_zero_spec_tooth
#verify_inhabited current_rlib_tower128_bdoz_mac_pclmul_functional gf128BdozPclmul_inhabited

end Gf128BdozPclmulKernel

/-! ### Kernel runs as Wiedemann-tower dot products -/

/-- Tower-basis dot product of `n` 16-byte block pairs: `Σ ψ⁻¹(L_i) · ψ⁻¹(R_i)` in `Tower128`. -/
def gf128PclmulTowerSum : Nat → (UInt64 → UInt8) → UInt64 → UInt64 → Tower128
  | 0, _, _, _ => towerZero 7
  | n+1, m, pL, pR =>
      towerAdd 7
        (towerMul 7
          (polyToTower128 (gf128Words (readMem128 m pL).w0 (readMem128 m pL).w1))
          (polyToTower128 (gf128Words (readMem128 m pR).w0 (readMem128 m pR).w1)))
        (gf128PclmulTowerSum n m (pL+16) (pR+16))

theorem polyToTower128_gf128PclmulFieldSum (n : Nat) (m : UInt64 → UInt8) (pL pR : UInt64) :
    polyToTower128 (gf128PclmulFieldSum n m pL pR) = gf128PclmulTowerSum n m pL pR := by
  induction n generalizing pL pR with
  | zero => exact polyToTower128_zero
  | succ n ih =>
    simp only [gf128PclmulFieldSum, gf128PclmulTowerSum, polyToTower128_gf128FieldMul_xor, ih]

/-- Public singleton equation for composing the decoded kernel with a scalar MIR product. -/
theorem gf128PclmulTowerSum_one (m : UInt64 → UInt8) (pL pR : UInt64) :
    gf128PclmulTowerSum 1 m pL pR =
      towerMul 7
        (polyToTower128 (gf128Words (readMem128 m pL).w0 (readMem128 m pL).w1))
        (polyToTower128 (gf128Words (readMem128 m pR).w0 (readMem128 m pR).w1)) := by
  simp only [gf128PclmulTowerSum, towerAdd_zero]

/-- Tower-basis dot product of `n` 32-byte block pairs (two 128-bit lanes per block). -/
def gf128VpclmulTowerSum : Nat → (UInt64 → UInt8) → UInt64 → UInt64 → Tower128
  | 0, _, _, _ => towerZero 7
  | n+1, m, pL, pR =>
      towerAdd 7
        (towerMul 7
          (polyToTower128 (gf128Words (readMem256 m pL).w0 (readMem256 m pL).w1))
          (polyToTower128 (gf128Words (readMem256 m pR).w0 (readMem256 m pR).w1)))
        (towerAdd 7
          (towerMul 7
            (polyToTower128 (gf128Words (readMem256 m pL).w2 (readMem256 m pL).w3))
            (polyToTower128 (gf128Words (readMem256 m pR).w2 (readMem256 m pR).w3)))
          (gf128VpclmulTowerSum n m (pL+32) (pR+32)))

theorem polyToTower128_gf128VpclmulFieldSum (n : Nat) (m : UInt64 → UInt8) (pL pR : UInt64) :
    polyToTower128 (gf128VpclmulFieldSum n m pL pR) = gf128VpclmulTowerSum n m pL pR := by
  induction n generalizing pL pR with
  | zero => exact polyToTower128_zero
  | succ n ih =>
    simp only [gf128VpclmulFieldSum, gf128VpclmulTowerSum, BitVec.xor_assoc,
      polyToTower128_gf128FieldMul_xor, ih]

end Gf128KernelEquivalence

end Qsag
end
