module

public import Qsag.Machine.ElfFunctionalEquiv.Gf128PclmulX86
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
attribute [local irreducible] clmul64
open SydTv

def gf128PmullName : List UInt8 := [0x71, 0x73, 0x61, 0x67, 0x5f, 0x61, 0x73, 0x6d, 0x5f, 0x67, 0x66, 0x32, 0x5f, 0x31, 0x32, 0x38, 0x5f, 0x6d, 0x75, 0x6c, 0x5f, 0x61, 0x63, 0x63, 0x5f, 0x70, 0x6d, 0x75, 0x6c, 0x6c]

def gf128PmullProg : List (DecodedInstr Arm64Instr) := [
  ⟨0, 4, .veor16b 0 0 0⟩,
  ⟨4, 4, .veor16b 1 1 1⟩,
  ⟨8, 4, .veor16b 2 2 2⟩,
  ⟨12, 4, .veor16b 22 22 22⟩,
  ⟨16, 4, .ldrQ 4 1 0⟩,
  ⟨20, 4, .ldrQ 5 2 0⟩,
  ⟨24, 4, .vpmull false 6 4 5⟩,
  ⟨28, 4, .vpmull true 7 4 5⟩,
  ⟨32, 4, .vext16b 16 4 4 8⟩,
  ⟨36, 4, .vext16b 17 5 5 8⟩,
  ⟨40, 4, .veor16b 16 16 4⟩,
  ⟨44, 4, .veor16b 17 17 5⟩,
  ⟨48, 4, .vpmull false 18 16 17⟩,
  ⟨52, 4, .veor16b 0 0 6⟩,
  ⟨56, 4, .veor16b 1 1 7⟩,
  ⟨60, 4, .veor16b 2 2 18⟩,
  ⟨64, 4, .aluImm .add true 1 1 16⟩,
  ⟨68, 4, .aluImm .add true 2 2 16⟩,
  ⟨72, 4, .aluImm .subs true 3 3 1⟩,
  ⟨76, 4, .bCond 1 16⟩,
  ⟨80, 4, .veor16b 2 2 0⟩,
  ⟨84, 4, .veor16b 2 2 1⟩,
  ⟨88, 4, .vext16b 19 22 2 8⟩,
  ⟨92, 4, .vext16b 20 2 22 8⟩,
  ⟨96, 4, .veor16b 0 0 19⟩,
  ⟨100, 4, .veor16b 1 1 20⟩,
  ⟨104, 4, .movWide false true 4 0x87 0⟩,
  ⟨108, 4, .fmovDFromX 21 4⟩,
  ⟨112, 4, .vext16b 16 1 22 8⟩,
  ⟨116, 4, .vpmull false 6 16 21⟩,
  ⟨120, 4, .vext16b 19 22 6 8⟩,
  ⟨124, 4, .vext16b 20 6 22 8⟩,
  ⟨128, 4, .veor16b 0 0 19⟩,
  ⟨132, 4, .veor16b 1 1 20⟩,
  ⟨136, 4, .vpmull false 6 1 21⟩,
  ⟨140, 4, .veor16b 0 0 6⟩,
  ⟨144, 4, .ldrQ 4 0 0⟩,
  ⟨148, 4, .veor16b 0 0 4⟩,
  ⟨152, 4, .strQ 0 0 0⟩,
  ⟨156, 4, .veor16b 0 0 0⟩,
  ⟨160, 4, .veor16b 1 1 1⟩,
  ⟨164, 4, .veor16b 2 2 2⟩,
  ⟨168, 4, .veor16b 4 4 4⟩,
  ⟨172, 4, .veor16b 5 5 5⟩,
  ⟨176, 4, .veor16b 6 6 6⟩,
  ⟨180, 4, .veor16b 7 7 7⟩,
  ⟨184, 4, .veor16b 16 16 16⟩,
  ⟨188, 4, .veor16b 17 17 17⟩,
  ⟨192, 4, .veor16b 18 18 18⟩,
  ⟨196, 4, .veor16b 19 19 19⟩,
  ⟨200, 4, .veor16b 20 20 20⟩,
  ⟨204, 4, .veor16b 21 21 21⟩,
  ⟨208, 4, .movWide false true 4 0 0⟩,
  ⟨212, 4, .ret⟩
]

/-- Fresh AArch64 object bytes decode to the program used below. -/
theorem gf128Pmull_current_decode :
    (findSliceByNameBytes currentAarch64ExtractedSlices gf128PmullName).map
      (fun s => decodeArm64Stream s.code) = some (some gf128PmullProg) := by
  decide +kernel

private theorem gf128Arm_ext8 (s : Arm64State) (pc vd vn vm : Nat) :
    (stepArm64 ⟨pc, 4, .vext16b vd vn vm 8⟩ s).1 =
      {s with pc := pc+4, vec := s.vec.set vd ⟨(s.vec.get vn).w1, (s.vec.get vm).w0⟩} := by
  change {s with pc := pc+4, vec := (s.vec.set vd
    ⟨mapBytes64 (getByte64 (s.vec.get vn).w1), mapBytes64 (getByte64 (s.vec.get vm).w0)⟩)} = _
  rw [mapBytes64_getByte64, mapBytes64_getByte64]

private theorem gf128Arm_addImm (s : Arm64State) (pc rd rn : Nat) (imm : UInt64) :
    (stepArm64 ⟨pc, 4, .aluImm .add true rd rn imm⟩ s).1 =
      {s with pc := pc+4, gpr := setArmGpr s rd (getArmGpr s rn + imm)} := by
  simp only [stepArm64, evalArmAlu, maskGprWidth, ↓reduceIte, uint64_evalAdd_eq]

private theorem gf128Arm_subsImm (s : Arm64State) (pc rd rn : Nat) (imm : UInt64) :
    (stepArm64 ⟨pc, 4, .aluImm .subs true rd rn imm⟩ s).1 =
      {s with
        pc := pc+4
        gpr := setArmGpr s rd (getArmGpr s rn - imm)
        cf := decide ((getArmGpr s rn).toNat ≥ imm.toNat)
        zf := (getArmGpr s rn - imm) == 0} := by
  simp only [stepArm64, evalArmAlu, maskGprWidth, ↓reduceIte, uint64_evalSub_eq]

private theorem gf128Arm_bne (s : Arm64State) (pc : Nat) (target : Int) (ht : 0 ≤ target) :
    (stepArm64 ⟨pc, 4, .bCond 1 target⟩ s).1 =
      {s with pc := if s.zf then pc+4 else target.toNat} := by
  cases hz : s.zf <;> simp [stepArm64, evalArmCond, hz, ht]

private theorem gf128Arm_mov87 (s : Arm64State) (pc : Nat) :
    (stepArm64 ⟨pc, 4, .movWide false true 4 0x87 0⟩ s).1 =
      {s with pc := pc+4, gpr := s.gpr.set 4 0x87} := by rfl

private theorem gf128Arm_mov0 (s : Arm64State) (pc : Nat) :
    (stepArm64 ⟨pc, 4, .movWide false true 4 0 0⟩ s).1 =
      {s with pc := pc+4, gpr := s.gpr.set 4 0} := by rfl

private theorem gf128Arm_set3123 (g : Bank32 UInt64) (a b c d : UInt64) :
    (((g.set 3 a).set 1 b).set 2 c).set 3 d = ((g.set 1 b).set 2 c).set 3 d := by rfl

private theorem gf128Arm_set1212 (g : Bank32 UInt64) (a b c d : UInt64) :
    (((g.set 1 a).set 2 b).set 1 c).set 2 d = (g.set 1 c).set 2 d := by rfl

def gf128ArmXor (a b : Vec128) : Vec128 := ⟨a.w0 ^^^ b.w0, a.w1 ^^^ b.w1⟩

def gf128ArmCross (a b : Vec128) : Vec128 := clmul64 (a.w1 ^^^ a.w0) (b.w1 ^^^ b.w0)

def gf128ArmBodyVec (v : Bank32 Vec128) (a b : Vec128) : Bank32 Vec128 :=
  let lo := clmul64 a.w0 b.w0
  let hi := clmul64 a.w1 b.w1
  let ax := gf128ArmXor ⟨a.w1, a.w0⟩ a
  let bx := gf128ArmXor ⟨b.w1, b.w0⟩ b
  let mid := gf128ArmCross a b
  ((((((((((v.set 4 a).set 5 b).set 6 lo).set 7 hi).set 16 ax).set 17 bx).set 18 mid).set
    0 (gf128ArmXor (v.get 0) lo)).set 1 (gf128ArmXor (v.get 1) hi)).set
    2 (gf128ArmXor (v.get 2) mid))


-- A common normalization set is deliberately reused across different instruction kinds.
set_option linter.unusedSimpArgs false in
private theorem gf128Arm_body_one_iter
    (g : Bank32 UInt64) (v : Bank32 Vec128) (cf zf dit : Bool) (m : UInt64 → UInt8) :
    StepsArm64 gf128PmullProg 16
      ⟨16, g, v, cf, zf, dit, false, m⟩
      ⟨if (g.get 3 - 1) == 0 then 80 else 16,
        ((g.set 1 (g.get 1+16)).set 2 (g.get 2+16)).set 3 (g.get 3-1),
        gf128ArmBodyVec v (readMem128 m (g.get 1)) (readMem128 m (g.get 2)),
        decide ((g.get 3).toNat ≥ 1), (g.get 3-1) == 0, dit, false, m⟩ := by
  iterate 4
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [stepArm64, Nat.reduceBEq, Bool.false_eq_true, eq_self, ite_false, ite_true, getArmGpr, u64_add_zero,
        Bank32.get_set_eq, Bank32.get_set_ne] <;> rfl
  iterate 2
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [gf128Arm_ext8,
        Bank32.get_set_eq, Bank32.get_set_ne] <;> rfl
  iterate 6
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [stepArm64, Nat.reduceBEq, Bool.false_eq_true, eq_self, ite_false, ite_true,
        Bank32.get_set_eq, Bank32.get_set_ne] <;> rfl
  iterate 2
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [gf128Arm_addImm, Nat.reduceBEq, Bool.false_eq_true, ite_false, getArmGpr, setArmGpr, ↓reduceIte,
        Bank32.get_set_ne] <;> rfl
  apply StepsArm64.cons rfl rfl
  · simp (disch := decide) only [gf128Arm_subsImm, Nat.reduceBEq, Bool.false_eq_true, ite_false, getArmGpr, setArmGpr, ↓reduceIte,
      Bank32.get_set_ne] <;> rfl
  apply StepsArm64.cons rfl rfl
  · rw [gf128Arm_bne _ _ _ (by decide)]
  unfold gf128ArmBodyVec gf128ArmCross gf128ArmXor
  dsimp only [getArmGpr, setArmGpr, Bank32.get, Bank32.set, Bank16.get, Bank16.set]
  exact StepsArm64.zero _

/-- The loop reads one pair per iteration and never writes memory. -/
def gf128ArmIterVec : Nat → (UInt64 → UInt8) → UInt64 → UInt64 → Bank32 Vec128 → Bank32 Vec128
  | 0, _, _, _, v => v
  | n+1, m, pL, pR, v => gf128ArmIterVec n m (pL+16) (pR+16)
      (gf128ArmBodyVec v (readMem128 m pL) (readMem128 m pR))

private theorem gf128ArmIterVec_zero (m : UInt64 → UInt8) (pL pR : UInt64)
    (v : Bank32 Vec128) : gf128ArmIterVec 0 m pL pR v = v := rfl

private theorem gf128ArmIterVec_succ (n : Nat) (m : UInt64 → UInt8) (pL pR : UInt64)
    (v : Bank32 Vec128) : gf128ArmIterVec (n+1) m pL pR v =
      gf128ArmIterVec n m (pL+16) (pR+16)
        (gf128ArmBodyVec v (readMem128 m pL) (readMem128 m pR)) := rfl

attribute [local irreducible] gf128ArmBodyVec gf128ArmIterVec

private theorem gf128Arm_loop_reaches (k : Nat) (hk : k+1 < 2^64)
    (g : Bank32 UInt64) (v : Bank32 Vec128) (cf zf dit : Bool) (m : UInt64 → UInt8) :
    ExecReachesArm64 gf128PmullProg (16 * (k+1))
      ⟨16, g.set 3 (UInt64.ofNat (k+1)), v, cf, zf, dit, false, m⟩
      ⟨80, ((g.set 1 (g.get 1 + UInt64.ofNat (16*(k+1)))).set
        2 (g.get 2 + UInt64.ofNat (16*(k+1)))).set 3 0,
        gf128ArmIterVec (k+1) m (g.get 1) (g.get 2) v, true, true, dit, false, m⟩ := by
  induction k generalizing g v cf zf with
  | zero =>
    rw [gf128ArmIterVec_succ, gf128ArmIterVec_zero]
    change ExecReachesArm64 gf128PmullProg 16
      ⟨16, g.set 3 1, v, cf, zf, dit, false, m⟩
      ⟨80, ((g.set 1 (g.get 1+16)).set 2 (g.get 2+16)).set 3 0,
        gf128ArmBodyVec v (readMem128 m (g.get 1)) (readMem128 m (g.get 2)),
        true, true, dit, false, m⟩
    have h := (gf128Arm_body_one_iter (g.set 3 1) v cf zf dit m).toExecReaches
    simpa (disch := decide) only [Bank32.get_set_eq, Bank32.get_set_ne,
      show (1 : UInt64)-1 = 0 from rfl, u64_zero_beq_zero, eq_self, ite_true,
      show decide ((1 : UInt64).toNat ≥ 1) = true from rfl,
      gf128Arm_set3123] using h
  | succ k ih =>
    have hd : UInt64.ofNat (k+1+1) - 1 = UInt64.ofNat (k+1) := by
      rw [UInt64.ofNat_add]
      apply UInt64.eq_of_toBitVec_eq
      simp
    have hz : (UInt64.ofNat (k+1) == 0) = false := by
      cases h : UInt64.ofNat (k+1) == 0
      · rfl
      · have hn := congrArg UInt64.toNat (beq_iff_eq.mp h)
        have hb : k+1 < 2^64 := by omega
        rw [show (UInt64.ofNat (k+1)).toNat = k+1 from Nat.mod_eq_of_lt hb] at hn
        simp only [UInt64.toNat_zero] at hn
        omega
    have h := (gf128Arm_body_one_iter (g.set 3 (UInt64.ofNat (k+1+1))) v cf zf dit m).toExecReaches
    simp (disch := decide) only [Bank32.get_set_eq, Bank32.get_set_ne, hd, hz,
      Bool.false_eq_true, ite_false, gf128Arm_set3123] at h
    have hr := ih (by omega) ((g.set 1 (g.get 1+16)).set 2 (g.get 2+16))
      (gf128ArmBodyVec v (readMem128 m (g.get 1)) (readMem128 m (g.get 2)))
      (decide ((UInt64.ofNat (k+1+1)).toNat ≥ 1)) false
    have hc := ExecReachesArm64_trans h hr
    have he : 16 + 16*(k+1) = 16*(k+1+1) := by omega
    have hp (p : UInt64) : (p+16) + UInt64.ofNat (16*(k+1)) = p + UInt64.ofNat (16*(k+1+1)) := by
      rw [← he, UInt64.ofNat_add 16 (16*(k+1))]
      exact UInt64.add_assoc p 16 _
    rw [gf128ArmIterVec_succ]
    simpa (disch := decide) only [he, Bank32.get_set_eq, Bank32.get_set_ne, hp,
      gf128Arm_set1212] using hc

/-- Recombine the three unreduced Karatsuba accumulators. -/
def gf128ArmProductPoly (lo hi mid : Vec128) : BitVec 256 :=
  (gf128Words lo.w0 lo.w1).setWidth 256 ^^^
    (((gf128Words mid.w0 mid.w1 ^^^ gf128Words lo.w0 lo.w1 ^^^
      gf128Words hi.w0 hi.w1).setWidth 256) <<< 64) ^^^
    ((gf128Words hi.w0 hi.w1).setWidth 256 <<< 128)

private theorem gf128ArmShuffle (a b c d e f g h i j : BitVec 256) :
    (a ^^^ b) ^^^ (((c ^^^ d) ^^^ (e ^^^ f)) ^^^ (g ^^^ h)) ^^^ (i ^^^ j) =
      (a ^^^ ((c ^^^ e) ^^^ g) ^^^ i) ^^^ (b ^^^ ((d ^^^ f) ^^^ h) ^^^ j) := by
  simp only [BitVec.xor_comm, gf128XorLeftComm]

private theorem gf128ArmProductPoly_xor (lo hi mid l h m : Vec128) :
    gf128ArmProductPoly (gf128ArmXor lo l) (gf128ArmXor hi h) (gf128ArmXor mid m) =
      gf128ArmProductPoly lo hi mid ^^^ gf128ArmProductPoly l h m := by
  simp only [gf128ArmProductPoly, gf128ArmXor, gf128Words_xor,
    BitVec.setWidth_xor, BitVec.shiftLeft_xor_distrib]
  exact gf128ArmShuffle _ _ _ _ _ _ _ _ _ _

private theorem gf128ArmProductPoly_words (lo hi mid : Vec128) :
    gf128ArmProductPoly lo hi mid =
      gf128Words (hi.w0 ^^^ (mid.w1 ^^^ lo.w1 ^^^ hi.w1)) hi.w1 ++
        gf128Words lo.w0 (lo.w1 ^^^ (mid.w0 ^^^ lo.w0 ^^^ hi.w0)) := by
  let cross := gf128ArmXor (gf128ArmXor mid lo) hi
  have hx : gf128Words cross.w0 cross.w1 = gf128Words mid.w0 mid.w1 ^^^
      gf128Words lo.w0 lo.w1 ^^^ gf128Words hi.w0 hi.w1 := by
    simp only [cross, gf128ArmXor, gf128Words_xor]
  have h := gf128FourWords_shift lo cross Vec128.zero hi
  have hz : (gf128Words 0 0).setWidth 256 = 0 := by rw [elf_gf128Words_zero_zero]; decide
  dsimp only [Vec128.zero] at h
  simp only [UInt64.xor_zero] at h
  simp only [hz, BitVec.ofNat_eq_ofNat, BitVec.xor_zero] at h
  unfold gf128ArmProductPoly
  rw [← hx]
  exact h.symm

private theorem gf128ArmProductPoly_mul (a b : Vec128) :
    gf128ArmProductPoly (clmul64 a.w0 b.w0) (clmul64 a.w1 b.w1) (gf128ArmCross a b) =
      gf128PolyMul ((gf128Words a.w0 a.w1).setWidth 256) (gf128Words b.w0 b.w1) := by
  rw [gf128ArmProductPoly_words]
  unfold gf128ArmCross
  rw [UInt64.xor_comm a.w1 a.w0, UInt64.xor_comm b.w1 b.w0]
  exact gf128_clmul_karatsuba_words a.w0 a.w1 b.w0 b.w1

/-- Mathematical XOR sum in the GCM field, in the order loaded by the kernel. -/
def gf128ArmFieldSum : Nat → (UInt64 → UInt8) → UInt64 → UInt64 → BitVec 128
  | 0, _, _, _ => 0
  | n+1, mem, pL, pR =>
    let a := readMem128 mem pL
    let b := readMem128 mem pR
    gf128FieldMul (gf128Words a.w0 a.w1) (gf128Words b.w0 b.w1) ^^^
      gf128ArmFieldSum n mem (pL+16) (pR+16)

private theorem gf128ArmIterVec_field (n : Nat) (m : UInt64 → UInt8)
    (pL pR : UInt64) (v : Bank32 Vec128) :
    gf128Reduce (gf128ArmProductPoly
      ((gf128ArmIterVec n m pL pR v).get 0)
      ((gf128ArmIterVec n m pL pR v).get 1)
      ((gf128ArmIterVec n m pL pR v).get 2)) =
    gf128Reduce (gf128ArmProductPoly (v.get 0) (v.get 1) (v.get 2)) ^^^
      gf128ArmFieldSum n m pL pR := by
  induction n generalizing pL pR v with
  | zero => simp [gf128ArmIterVec, gf128ArmFieldSum]
  | succ n ih =>
    rw [gf128ArmIterVec, ih]
    simp [gf128ArmBodyVec, Bank32.get_set_eq, Bank32.get_set_ne]
    rw [gf128ArmProductPoly_xor, gf128Reduce_xor, gf128ArmProductPoly_mul]
    simp only [gf128ArmFieldSum, gf128FieldMul.public_eq_1, BitVec.xor_assoc]

def gf128ArmReduceVec (lo hi mid : Vec128) : Vec128 :=
  let cross := gf128ArmXor (gf128ArmXor mid lo) hi
  let l : Vec128 := ⟨lo.w0, lo.w1 ^^^ cross.w0⟩
  let h : Vec128 := ⟨hi.w0 ^^^ cross.w1, hi.w1⟩
  let r1 := clmul64 h.w1 0x87
  let r0 := clmul64 (h.w0 ^^^ r1.w1) 0x87
  ⟨l.w0 ^^^ r0.w0, l.w1 ^^^ r1.w0 ^^^ r0.w1⟩

private theorem gf128ArmReduceVec_field (lo hi mid : Vec128) :
    gf128Words (gf128ArmReduceVec lo hi mid).w0 (gf128ArmReduceVec lo hi mid).w1 =
      gf128Reduce (gf128ArmProductPoly lo hi mid) := by
  rw [gf128ArmProductPoly_words, ← gf128WordReduce_eq_reduce, gf128WordReduce.public_eq_1]
  rfl

def gf128ArmCleanVec (v : Bank32 Vec128) : Bank32 Vec128 :=
  ((((((((((((v.set 0 Vec128.zero).set 1 Vec128.zero).set 2 Vec128.zero).set 4 Vec128.zero).set
    5 Vec128.zero).set 6 Vec128.zero).set 7 Vec128.zero).set 16 Vec128.zero).set
    17 Vec128.zero).set 18 Vec128.zero).set 19 Vec128.zero).set 20 Vec128.zero).set 21 Vec128.zero

set_option linter.unusedSimpArgs false in
private theorem gf128Arm_tail_reaches
    (g : Bank32 UInt64) (v : Bank32 Vec128) (cf zf dit : Bool) (m : UInt64 → UInt8)
    (hv : v.get 22 = Vec128.zero) :
    ExecReachesArm64 gf128PmullProg 33
      ⟨80, g, v, cf, zf, dit, false, m⟩
      ⟨212, g.set 4 0, gf128ArmCleanVec v, cf, zf, dit, false,
        writeMem128 m (g.get 0)
          (gf128ArmXor (gf128ArmReduceVec (v.get 0) (v.get 1) (v.get 2))
            (readMem128 m (g.get 0)))⟩ := by
  apply StepsArm64.toExecReaches
  iterate 2
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [hv, Vec128.zero, UInt64.xor_zero, UInt64.zero_xor, stepArm64, Nat.reduceBEq, Bool.false_eq_true, eq_self, ite_false, ite_true,
        Bank32.get_set_eq, Bank32.get_set_ne] <;> rfl
  iterate 2
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [hv, Vec128.zero, UInt64.xor_zero, UInt64.zero_xor, gf128Arm_ext8,
        Bank32.get_set_eq, Bank32.get_set_ne] <;> rfl
  iterate 2
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [hv, Vec128.zero, UInt64.xor_zero, UInt64.zero_xor, stepArm64,
        Bank32.get_set_eq, Bank32.get_set_ne] <;> rfl
  apply StepsArm64.cons rfl rfl
  · rw [gf128Arm_mov87]
  apply StepsArm64.cons rfl rfl
  · simp (disch := decide) only [hv, Vec128.zero, UInt64.xor_zero, UInt64.zero_xor, stepArm64, getArmGpr, Nat.reduceBEq,
      Bool.false_eq_true, ite_false, Bank32.get_set_eq, Bank32.get_set_ne] <;> rfl
  iterate 1
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [hv, Vec128.zero, UInt64.xor_zero, UInt64.zero_xor, gf128Arm_ext8,
        Bank32.get_set_eq, Bank32.get_set_ne] <;> rfl
  iterate 1
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [hv, Vec128.zero, UInt64.xor_zero, UInt64.zero_xor, stepArm64, Nat.reduceBEq, Bool.false_eq_true, eq_self, ite_false, ite_true,
        Bank32.get_set_eq, Bank32.get_set_ne] <;> rfl
  iterate 2
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [hv, Vec128.zero, UInt64.xor_zero, UInt64.zero_xor, gf128Arm_ext8,
        Bank32.get_set_eq, Bank32.get_set_ne] <;> rfl
  iterate 4
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [hv, Vec128.zero, UInt64.xor_zero, UInt64.zero_xor, stepArm64, Nat.reduceBEq, Bool.false_eq_true, eq_self, ite_false, ite_true,
        Bank32.get_set_eq, Bank32.get_set_ne] <;> rfl
  iterate 1
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [hv, Vec128.zero, UInt64.xor_zero, UInt64.zero_xor, stepArm64, Nat.reduceBEq, Bool.false_eq_true, eq_self, ite_false, ite_true, getArmGpr, u64_add_zero,
        Bank32.get_set_eq, Bank32.get_set_ne] <;> rfl
  iterate 1
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [hv, Vec128.zero, UInt64.xor_zero, UInt64.zero_xor, stepArm64, Nat.reduceBEq, Bool.false_eq_true, eq_self, ite_false, ite_true,
        Bank32.get_set_eq, Bank32.get_set_ne] <;> rfl
  iterate 1
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [hv, Vec128.zero, UInt64.xor_zero, UInt64.zero_xor, stepArm64, Nat.reduceBEq, Bool.false_eq_true, eq_self, ite_false, ite_true, getArmGpr, u64_add_zero,
        Bank32.get_set_eq, Bank32.get_set_ne] <;> rfl
  iterate 13
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [hv, Vec128.zero, UInt64.xor_zero, UInt64.zero_xor, stepArm64, Nat.reduceBEq, Bool.false_eq_true, eq_self, ite_false, ite_true, UInt64.xor_self,
        Bank32.get_set_eq, Bank32.get_set_ne] <;> rfl
  apply StepsArm64.cons rfl rfl
  · rw [gf128Arm_mov0]
  unfold gf128ArmCleanVec gf128ArmXor gf128ArmReduceVec
  dsimp only [getArmGpr, setArmGpr, Bank32.get, Bank32.set, Bank16.get, Bank16.set] at hv ⊢
  simp only [hv, Vec128.zero, UInt64.xor_zero, UInt64.zero_xor]
  exact StepsArm64.zero _

private theorem gf128ArmIterVec_keep22 (n : Nat) (m : UInt64 → UInt8)
    (pL pR : UInt64) (v : Bank32 Vec128) :
    (gf128ArmIterVec n m pL pR v).get 22 = v.get 22 := by
  induction n generalizing pL pR v with
  | zero => rw [gf128ArmIterVec_zero]
  | succ n ih =>
    rw [gf128ArmIterVec_succ, ih]
    simp [gf128ArmBodyVec, Bank32.get_set_ne]

def gf128ArmInitVec (v : Bank32 Vec128) : Bank32 Vec128 :=
  (((v.set 0 Vec128.zero).set 1 Vec128.zero).set 2 Vec128.zero).set 22 Vec128.zero

private theorem gf128Arm_entry_reaches
    (g : Bank32 UInt64) (v : Bank32 Vec128) (cf zf dit : Bool) (m : UInt64 → UInt8) :
    ExecReachesArm64 gf128PmullProg 4
      ⟨0, g, v, cf, zf, dit, false, m⟩
      ⟨16, g, gf128ArmInitVec v, cf, zf, dit, false, m⟩ := by
  apply StepsArm64.toExecReaches
  iterate 4
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [stepArm64, UInt64.xor_self,
        Bank32.get_set_ne] <;> rfl
  exact StepsArm64.zero _

private theorem gf128ArmInitVec_poly_zero (v : Bank32 Vec128) :
    gf128ArmProductPoly ((gf128ArmInitVec v).get 0) ((gf128ArmInitVec v).get 1)
      ((gf128ArmInitVec v).get 2) = 0 := by
  change gf128ArmProductPoly Vec128.zero Vec128.zero Vec128.zero = 0
  simp only [gf128ArmProductPoly, gf128Words.public_eq_1]
  decide +kernel

/-- Whole-kernel functional equivalence for every positive AArch64 ABI trip count.
The count-zero wrapper path is deliberately excluded. All reads precede the sole
store, so arbitrary overlapping input/output regions are admitted. -/
theorem current_rlib_gf128_mul_acc_pmull_functional (n : Nat) (hn : 0 < n)
    (hbound : n < 2^64) (s : Arm64State) (hpc : s.pc = 0)
    (hhalt : s.halted = false) (hcount : s.gpr.get 3 = UInt64.ofNat n) :
    ∃ slice : ElfFuncSlice,
      findSliceByNameBytes currentAarch64ExtractedSlices gf128PmullName = some slice ∧
      decodeArm64Stream slice.code = some gf128PmullProg ∧
      ∀ extra : Nat, ∃ out : Vec128,
        (runArm64 gf128PmullProg (38 + 16*n + extra) s).1.halted = true ∧
        (runArm64 gf128PmullProg (38 + 16*n + extra) s).1.pc = 212 ∧
        (runArm64 gf128PmullProg (38 + 16*n + extra) s).2.length = 38 + 16*n ∧
        (runArm64 gf128PmullProg (38 + 16*n + extra) s).1.mem =
          writeMem128 s.mem (s.gpr.get 0) out ∧
        gf128Words out.w0 out.w1 =
          gf128Words (readMem128 s.mem (s.gpr.get 0)).w0 (readMem128 s.mem (s.gpr.get 0)).w1 ^^^
            gf128ArmFieldSum n s.mem (s.gpr.get 1) (s.gpr.get 2) := by
  have hdec := gf128Pmull_current_decode
  cases hfind : findSliceByNameBytes currentAarch64ExtractedSlices gf128PmullName with
  | none => simp [hfind] at hdec
  | some slice =>
    simp only [hfind, Option.map_some, Option.some.injEq] at hdec
    refine ⟨slice, rfl, hdec, ?_⟩
    cases n with
    | zero => exact False.elim (Nat.not_lt_zero _ hn)
    | succ k =>
      rcases s with ⟨pc, g, v, cf, zf, dit, halted, m⟩
      dsimp only at hpc hhalt hcount ⊢
      subst pc
      subst halted
      have hg : g.set 3 (UInt64.ofNat (k+1)) = g := by rw [← hcount]; rfl
      have he := gf128Arm_entry_reaches g v cf zf dit m
      have hl := gf128Arm_loop_reaches k hbound g (gf128ArmInitVec v) cf zf dit m
      rw [hg] at hl
      let gEnd := ((g.set 1 (g.get 1 + UInt64.ofNat (16*(k+1)))).set
        2 (g.get 2 + UInt64.ofNat (16*(k+1)))).set 3 0
      let vEnd := gf128ArmIterVec (k+1) m (g.get 1) (g.get 2) (gf128ArmInitVec v)
      have hvEnd : vEnd.get 22 = Vec128.zero := by
        rw [gf128ArmIterVec_keep22]
        exact Bank32.get_set_eq _ _ _
      have ht := gf128Arm_tail_reaches gEnd vEnd true true dit m hvEnd
      have hfull := ExecReachesArm64_trans he (ExecReachesArm64_trans hl ht)
      have hret := ExecReachesArm64_ret hfull rfl (by rfl)
      intro extra
      have hr := hret.2.2 extra
      have hsteps : 4 + (16*(k+1) + 33) + 1 = 38 + 16*(k+1) := by omega
      rw [hsteps] at hr
      let out := gf128ArmXor (gf128ArmReduceVec (vEnd.get 0) (vEnd.get 1) (vEnd.get 2))
        (readMem128 m (g.get 0))
      refine ⟨out, ?_, ?_, hr.2, ?_, ?_⟩
      · rw [hr.1]
      · rw [hr.1]
      · rw [hr.1]
        rfl
      · change gf128Words (gf128ArmXor _ _).w0 (gf128ArmXor _ _).w1 = _
        rw [show gf128Words (gf128ArmXor
            (gf128ArmReduceVec (vEnd.get 0) (vEnd.get 1) (vEnd.get 2))
            (readMem128 m (g.get 0))).w0
            (gf128ArmXor (gf128ArmReduceVec (vEnd.get 0) (vEnd.get 1) (vEnd.get 2))
            (readMem128 m (g.get 0))).w1 =
          gf128Words (gf128ArmReduceVec (vEnd.get 0) (vEnd.get 1) (vEnd.get 2)).w0
            (gf128ArmReduceVec (vEnd.get 0) (vEnd.get 1) (vEnd.get 2)).w1 ^^^
            gf128Words (readMem128 m (g.get 0)).w0 (readMem128 m (g.get 0)).w1 from
          gf128Words_xor _ _ _ _]
        rw [gf128ArmReduceVec_field, gf128ArmIterVec_field, gf128ArmInitVec_poly_zero]
        have hz : gf128Reduce 0 = 0 := elf_gf128Reduce_zero
        rw [hz]
        simp only [BitVec.ofNat_eq_ofNat, BitVec.zero_xor, BitVec.xor_comm]


/-- A specification that discards the input product is refuted by 1·1. -/
theorem gf128_pmull_discard_product_tooth :
    gf128ArmFieldSum 1 (fun a => if a == 0 then 1 else 0) 0 0 ≠ 0 :=
  elf_gf128_one_block_ne_zero (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem gf128_pmull_functional_witness :
    ∃ (n : Nat) (s : Arm64State),
      0 < n ∧ n < 2^64 ∧ s.pc = 0 ∧ s.halted = false ∧
      s.gpr.get 3 = UInt64.ofNat n ∧
      gf128ArmFieldSum n s.mem (s.gpr.get 1) (s.gpr.get 2) = 0 := by
  refine ⟨1, ⟨0, (Bank32.const 0).set 3 1, Bank32.const Vec128.zero,
    false, false, false, false, fun _ => 0⟩, by decide, by decide, rfl, rfl, by decide +kernel, ?_⟩
  exact elf_gf128_zero_block (by decide +kernel) (by decide +kernel)

#tooth_pair current_rlib_gf128_mul_acc_pmull_functional vs gf128_pmull_discard_product_tooth
#verify_inhabited current_rlib_gf128_mul_acc_pmull_functional gf128_pmull_functional_witness

def gf128BdozPmullName : List UInt8 := [0x71, 0x73, 0x61, 0x67, 0x5f, 0x61, 0x73, 0x6d, 0x5f, 0x74, 0x6f, 0x77, 0x65, 0x72, 0x31, 0x32, 0x38, 0x5f, 0x62, 0x64, 0x6f, 0x7a, 0x5f, 0x6d, 0x61, 0x63, 0x5f, 0x70, 0x6d, 0x75, 0x6c, 0x6c]

def gf128BdozPmullProg : List (DecodedInstr Arm64Instr) := [
  ⟨0, 4, .veor16b 0 0 0⟩,
  ⟨4, 4, .veor16b 1 1 1⟩,
  ⟨8, 4, .veor16b 2 2 2⟩,
  ⟨12, 4, .veor16b 3 3 3⟩,
  ⟨16, 4, .veor16b 22 22 22⟩,
  ⟨20, 4, .ldrQ 4 1 0⟩,
  ⟨24, 4, .ldrQ 5 2 0⟩,
  ⟨28, 4, .vpmull false 6 4 5⟩,
  ⟨32, 4, .vpmull true 7 4 5⟩,
  ⟨36, 4, .vext16b 16 5 5 8⟩,
  ⟨40, 4, .vpmull false 17 4 16⟩,
  ⟨44, 4, .vpmull true 18 4 16⟩,
  ⟨48, 4, .veor16b 17 17 18⟩,
  ⟨52, 4, .vext16b 19 22 17 8⟩,
  ⟨56, 4, .vext16b 20 17 22 8⟩,
  ⟨60, 4, .veor16b 6 6 19⟩,
  ⟨64, 4, .veor16b 7 7 20⟩,
  ⟨68, 4, .veor16b 0 0 6⟩,
  ⟨72, 4, .veor16b 1 1 7⟩,
  ⟨76, 4, .ldrQ 4 1 16⟩,
  ⟨80, 4, .ldrQ 5 2 16⟩,
  ⟨84, 4, .vpmull false 6 4 5⟩,
  ⟨88, 4, .vpmull true 7 4 5⟩,
  ⟨92, 4, .vext16b 16 5 5 8⟩,
  ⟨96, 4, .vpmull false 17 4 16⟩,
  ⟨100, 4, .vpmull true 18 4 16⟩,
  ⟨104, 4, .veor16b 17 17 18⟩,
  ⟨108, 4, .vext16b 19 22 17 8⟩,
  ⟨112, 4, .vext16b 20 17 22 8⟩,
  ⟨116, 4, .veor16b 6 6 19⟩,
  ⟨120, 4, .veor16b 7 7 20⟩,
  ⟨124, 4, .veor16b 2 2 6⟩,
  ⟨128, 4, .veor16b 3 3 7⟩,
  ⟨132, 4, .aluImm .add true 1 1 32⟩,
  ⟨136, 4, .aluImm .add true 2 2 32⟩,
  ⟨140, 4, .aluImm .subs true 3 3 1⟩,
  ⟨144, 4, .bCond 1 20⟩,
  ⟨148, 4, .movWide false true 4 135 0⟩,
  ⟨152, 4, .fmovDFromX 21 4⟩,
  ⟨156, 4, .vext16b 16 1 22 8⟩,
  ⟨160, 4, .vpmull false 6 16 21⟩,
  ⟨164, 4, .vext16b 19 22 6 8⟩,
  ⟨168, 4, .vext16b 20 6 22 8⟩,
  ⟨172, 4, .veor16b 0 0 19⟩,
  ⟨176, 4, .veor16b 1 1 20⟩,
  ⟨180, 4, .vpmull false 6 1 21⟩,
  ⟨184, 4, .veor16b 0 0 6⟩,
  ⟨188, 4, .strQ 0 0 0⟩,
  ⟨192, 4, .vext16b 16 3 22 8⟩,
  ⟨196, 4, .vpmull false 6 16 21⟩,
  ⟨200, 4, .vext16b 19 22 6 8⟩,
  ⟨204, 4, .vext16b 20 6 22 8⟩,
  ⟨208, 4, .veor16b 2 2 19⟩,
  ⟨212, 4, .veor16b 3 3 20⟩,
  ⟨216, 4, .vpmull false 6 3 21⟩,
  ⟨220, 4, .veor16b 2 2 6⟩,
  ⟨224, 4, .strQ 2 0 16⟩,
  ⟨228, 4, .veor16b 0 0 0⟩,
  ⟨232, 4, .veor16b 1 1 1⟩,
  ⟨236, 4, .veor16b 2 2 2⟩,
  ⟨240, 4, .veor16b 3 3 3⟩,
  ⟨244, 4, .veor16b 4 4 4⟩,
  ⟨248, 4, .veor16b 5 5 5⟩,
  ⟨252, 4, .veor16b 6 6 6⟩,
  ⟨256, 4, .veor16b 7 7 7⟩,
  ⟨260, 4, .veor16b 16 16 16⟩,
  ⟨264, 4, .veor16b 17 17 17⟩,
  ⟨268, 4, .veor16b 18 18 18⟩,
  ⟨272, 4, .veor16b 19 19 19⟩,
  ⟨276, 4, .veor16b 20 20 20⟩,
  ⟨280, 4, .veor16b 21 21 21⟩,
  ⟨284, 4, .movWide false true 4 0 0⟩,
  ⟨288, 4, .ret⟩
]

