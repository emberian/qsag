module
/-
# Qsag.McRefine — input/output refinement of decoded `qsag-asm` machine code

Each `*_mc_refines` theorem looks a symbol up in the extracted fixture slices, decodes its bytes
with the `ElfBinaryVerify` decoders, and relates the final state of the bounded-fuel machine run
(`runX86` / `runArm64`) to a specification stated over the initial registers and memory only.
-/

public import Qsag.Machine.ElfVerify
public import Qsag.Machine.IsaCt
public import Qsag.Machine.ElfParse
import Qsag.Tactic.Prelude
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd

set_option autoImplicit false

/-- Unpack a successful "find slice, then decode" computation. -/
theorem slice_decode_x86 {slices : List ElfFuncSlice} {nm : List UInt8}
    {prog : List (DecodedInstr X86Instr)}
    (h : (findSliceByNameBytes slices nm).bind (fun sl => decodeX86Stream sl.code) = some prog) :
    ∃ slice, findSliceByNameBytes slices nm = some slice ∧ decodeX86Stream slice.code = some prog := by
  cases hf : findSliceByNameBytes slices nm with
  | none => rw [hf] at h; cases h
  | some sl => rw [hf] at h; exact ⟨sl, rfl, h⟩

theorem slice_decode_arm64 {slices : List ElfFuncSlice} {nm : List UInt8}
    {prog : List (DecodedInstr Arm64Instr)}
    (h : (findSliceByNameBytes slices nm).bind (fun sl => decodeArm64Stream sl.code) = some prog) :
    ∃ slice, findSliceByNameBytes slices nm = some slice ∧ decodeArm64Stream slice.code = some prog := by
  cases hf : findSliceByNameBytes slices nm with
  | none => rw [hf] at h; cases h
  | some sl => rw [hf] at h; exact ⟨sl, rfl, h⟩

/-! ## §6. `qsag_asm_ct_eq_32_x86_64`: 32-byte equality, straight-line -/

/-- ASCII bytes of the symbol name `qsag_asm_ct_eq_32_x86_64`. -/
@[expose] def ctEq32X86Name : List UInt8 :=
  [0x71, 0x73, 0x61, 0x67, 0x5f, 0x61, 0x73, 0x6d, 0x5f, 0x63, 0x74, 0x5f, 0x65, 0x71, 0x5f, 0x33,
   0x32, 0x5f, 0x78, 0x38, 0x36, 0x5f, 0x36, 0x34]


/-- The OR of the four XOR-ed words as the x86 kernel computes it. -/
def ctEq32WordX86 (m : UInt64 → UInt8) (a b : UInt64) : UInt64 :=
  (readMem64 m (a + 0) ^^^ readMem64 m (b + 0) ||| readMem64 m (a + 8) ^^^ readMem64 m (b + 8)) |||
    (readMem64 m (a + 16) ^^^ readMem64 m (b + 16) ||| readMem64 m (a + 24) ^^^ readMem64 m (b + 24))


/-- The preconditions of `current_ct_eq_32_x86_64_mc_refines` are satisfiable. -/
theorem ct_eq_32_x86_64_pre_inhabited : ∃ s : X86State, s.pc = 0 ∧ s.halted = false :=
  ⟨⟨0, Bank16.const 0, Bank16.const Vec256.zero, false, false, false, false, false, fun _ => 0⟩, rfl, rfl⟩

/-! ## §7. `qsag_asm_ct_eq_32_aarch64` -/

/-- ASCII bytes of the symbol name `qsag_asm_ct_eq_32_aarch64`. -/
@[expose] def ctEq32ArmName : List UInt8 :=
  [0x71, 0x73, 0x61, 0x67, 0x5f, 0x61, 0x73, 0x6d, 0x5f, 0x63, 0x74, 0x5f, 0x65, 0x71, 0x5f, 0x33,
   0x32, 0x5f, 0x61, 0x61, 0x72, 0x63, 0x68, 0x36, 0x34]

def ctEq32ArmProg : List (DecodedInstr Arm64Instr) := [
  ⟨0, 4, .ldp64 2 3 0 0⟩,
  ⟨4, 4, .ldp64 4 5 1 0⟩,
  ⟨8, 4, .aluReg .eor true 2 2 4 0 0⟩,
  ⟨12, 4, .aluReg .eor true 3 3 5 0 0⟩,
  ⟨16, 4, .aluReg .orr true 2 2 3 0 0⟩,
  ⟨20, 4, .ldp64 4 5 0 16⟩,
  ⟨24, 4, .ldp64 6 7 1 16⟩,
  ⟨28, 4, .aluReg .eor true 4 4 6 0 0⟩,
  ⟨32, 4, .aluReg .eor true 5 5 7 0 0⟩,
  ⟨36, 4, .aluReg .orr true 4 4 5 0 0⟩,
  ⟨40, 4, .aluReg .orr true 2 2 4 0 0⟩,
  ⟨44, 4, .aluReg .sub true 3 31 2 0 0⟩,
  ⟨48, 4, .aluReg .orr true 2 2 3 0 0⟩,
  ⟨52, 4, .ubfm true 0 2 63 63⟩,
  ⟨56, 4, .aluImm .eor true 0 0 1⟩,
  ⟨60, 4, .movWide false true 2 0 0⟩,
  ⟨64, 4, .movWide false true 3 0 0⟩,
  ⟨68, 4, .movWide false true 4 0 0⟩,
  ⟨72, 4, .movWide false true 5 0 0⟩,
  ⟨76, 4, .movWide false true 6 0 0⟩,
  ⟨80, 4, .movWide false true 7 0 0⟩,
  ⟨84, 4, .ret⟩]

theorem current_ctEq32Arm_decodes :
    (findSliceByNameBytes currentAarch64ExtractedSlices ctEq32ArmName).bind
      (fun sl => decodeArm64Stream sl.code) = some ctEq32ArmProg := by
  decide +kernel

/-- The OR of the four XOR-ed words as the AArch64 kernel computes it. -/
def ctEq32WordArm (m : UInt64 → UInt8) (a b : UInt64) : UInt64 :=
  (readMem64 m (a + 0) ^^^ readMem64 m (b + 0) |||
      readMem64 m (a + 0 + 8) ^^^ readMem64 m (b + 0 + 8)) |||
    (readMem64 m (a + 16) ^^^ readMem64 m (b + 16) |||
      readMem64 m (a + 16 + 8) ^^^ readMem64 m (b + 16 + 8))

theorem ctEq32Arm_run (k : Nat) (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (hi : Bank16 UInt64) (v : Bank32 Vec128) (cf zf dit : Bool) (m : UInt64 → UInt8) :
    (runArm64 ctEq32ArmProg (k + 22)
      ⟨0, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        v, cf, zf, dit, false, m⟩).1 =
      ⟨84, ⟨⟨((ctEq32WordArm m r0 r1 ||| (0 - ctEq32WordArm m r0 r1)) >>> UInt64.ofNat 63) ^^^ 1,
          r1, 0, 0, 0, 0, 0, 0, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        v, cf, zf, dit, true, m⟩ := by
  iterate 22
    refine Eq.trans (runArm64_step_fst _ _ _ _ rfl rfl) ?_
    simp only [stepArm64_ldp, stepArm64_eorRR, stepArm64_orrRR, stepArm64_subRR, stepArm64_lsr64,
      stepArm64_eorImm, stepArm64_movz, stepArm64_ret, u64_shl_zero_zero, uint64_evalSub_eq,
      armGet_31, armGet_0, armGet_1, armGet_2, armGet_3, armGet_4, armGet_5, armGet_6, armGet_7,
      armSet_0, armSet_2, armSet_3, armSet_4, armSet_5, armSet_6, armSet_7]
  refine Eq.trans (runArm64_halted_fst _ _ _ rfl) ?_
  rfl

/-- **Machine-code refinement of `qsag_asm_ct_eq_32_aarch64`.** From any entry state, at most 22
steps halt with `x0 = 1` when the 32 bytes at `x0` equal the 32 bytes at `x1` and `x0 = 0`
otherwise; memory is untouched and `x2..x7` are wiped. -/
theorem current_ct_eq_32_aarch64_mc_refines :
    ∃ slice prog, findSliceByNameBytes currentAarch64ExtractedSlices ctEq32ArmName = some slice ∧
      decodeArm64Stream slice.code = some prog ∧
      ∀ (s : Arm64State) (fuel : Nat), s.pc = 0 → s.halted = false → 22 ≤ fuel →
        (runArm64 prog fuel s).1.halted = true ∧
        (runArm64 prog fuel s).1.gpr.get 0 =
          (if ∀ i : Nat, i < 32 →
              s.mem (s.gpr.get 0 + UInt64.ofNat i) = s.mem (s.gpr.get 1 + UInt64.ofNat i)
            then 1 else 0) ∧
        (runArm64 prog fuel s).1.mem = s.mem ∧
        (∀ r : Nat, 2 ≤ r → r ≤ 7 → (runArm64 prog fuel s).1.gpr.get r = 0) := by
  obtain ⟨sl, hf, hd⟩ := slice_decode_arm64 current_ctEq32Arm_decodes
  refine ⟨sl, ctEq32ArmProg, hf, hd, ?_⟩
  intro s fuel hpc hh hfuel
  obtain ⟨pc, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
    v, cf, zf, dit, hlt, m⟩ := s
  have hpc' : pc = 0 := hpc
  have hh' : hlt = false := hh
  subst hpc' hh'
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hfuel
  rw [Nat.add_comm 22 k, ctEq32Arm_run]
  refine ⟨rfl, ?_, rfl, ?_⟩
  · show ((ctEq32WordArm m r0 r1 ||| (0 - ctEq32WordArm m r0 r1)) >>> UInt64.ofNat 63) ^^^ 1 =
      if ∀ i : Nat, i < 32 → m (r0 + UInt64.ofNat i) = m (r1 + UInt64.ofNat i) then 1 else 0
    have e8 : ∀ x : UInt64, x + 0 + 8 = x + UInt64.ofNat 8 := fun x => by rw [UInt64.add_zero]; rfl
    have e24 : ∀ x : UInt64, x + 16 + 8 = x + UInt64.ofNat 24 := fun x => by
      rw [UInt64.add_assoc]; rfl
    have hiff : ctEq32WordArm m r0 r1 = 0 ↔
        ∀ i : Nat, i < 32 → m (r0 + UInt64.ofNat i) = m (r1 + UInt64.ofNat i) :=
      xorOr4_eq_zero_iff m r0 r1 _ _ _ _ _ _ _ _ rfl (e8 r0) rfl (e24 r0) rfl (e8 r1) rfl (e24 r1)
    rw [zeroTest64]
    if hW : ctEq32WordArm m r0 r1 = 0 then
      rw [ite_eq_left hW, ite_eq_left (hiff.mp hW)]
    else
      rw [ite_eq_right hW, ite_eq_right (fun h => hW (hiff.mpr h))]
  · intro r h2 h7
    match r, h2, h7 with
    | 2, _, _ => rfl
    | 3, _, _ => rfl
    | 4, _, _ => rfl
    | 5, _, _ => rfl
    | 6, _, _ => rfl
    | 7, _, _ => rfl
    | 0, h, _ => exact absurd h (by decide)
    | 1, h, _ => exact absurd h (by decide)
    | n + 8, _, h => exact absurd h (by omega)

/-- The preconditions of `current_ct_eq_32_aarch64_mc_refines` are satisfiable. -/
theorem ct_eq_32_aarch64_pre_inhabited : ∃ s : Arm64State, s.pc = 0 ∧ s.halted = false :=
  ⟨⟨0, Bank32.const 0, Bank32.const Vec128.zero, false, false, false, false, fun _ => 0⟩, rfl, rfl⟩

/-! ## §8. `ct_memzero`: byte-granular wipe loops -/

/-- Memory after writing `0` to the `k` consecutive addresses `p, p + 1, …` (wrapping). -/
def zeroRange : Nat → (UInt64 → UInt8) → UInt64 → UInt64 → UInt8
  | 0, m, _ => m
  | k + 1, m, p => zeroRange k (writeMem8 m p 0) (p + 1)

theorem addr_succ (p : UInt64) (i : Nat) : p + 1 + UInt64.ofNat i = p + UInt64.ofNat (i + 1) := by
  have h := addr_split p 1 i
  rw [Nat.add_comm 1 i] at h
  exact h

theorem addr_zero (p : UInt64) : p + UInt64.ofNat 0 = p := UInt64.add_zero p

theorem zeroRange_outside (k : Nat) : ∀ (m : UInt64 → UInt8) (p a : UInt64),
    (∀ i : Nat, i < k → a ≠ p + UInt64.ofNat i) → zeroRange k m p a = m a := by
  induction k with
  | zero => intro m p a _; rfl
  | succ k ih =>
    intro m p a h
    show zeroRange k (writeMem8 m p 0) (p + 1) a = m a
    rw [ih (writeMem8 m p 0) (p + 1) a (fun i hi => by rw [addr_succ]; exact h (i + 1) (by omega))]
    have h0 : a ≠ p := by
      have := h 0 (by omega)
      rw [addr_zero] at this
      exact this
    exact writeMem8_ne m 0 h0

theorem zeroRange_zero_stays (k : Nat) : ∀ (m : UInt64 → UInt8) (p a : UInt64),
    m a = 0 → zeroRange k m p a = 0 := by
  induction k with
  | zero => intro m p a h; exact h
  | succ k ih =>
    intro m p a h
    show zeroRange k (writeMem8 m p 0) (p + 1) a = 0
    apply ih
    if hap : a = p then
      subst hap; exact writeMem8_eq m a 0
    else
      rw [writeMem8_ne m 0 hap]; exact h

theorem zeroRange_inside (k : Nat) : ∀ (m : UInt64 → UInt8) (p : UInt64) (i : Nat),
    i < k → zeroRange k m p (p + UInt64.ofNat i) = 0 := by
  induction k with
  | zero => intro m p i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ k ih =>
    intro m p i hi
    show zeroRange k (writeMem8 m p 0) (p + 1) (p + UInt64.ofNat i) = 0
    cases i with
    | zero =>
      apply zeroRange_zero_stays
      rw [addr_zero]
      exact writeMem8_eq m p 0
    | succ j =>
      rw [← addr_succ]
      exact ih (writeMem8 m p 0) (p + 1) j (by omega)

theorem u64_pred_toNat (c : UInt64) (k : Nat) (hc : c.toNat = k + 1 + 1) : (c - 1).toNat = k + 1 := by
  have hlt : c.toNat < 18446744073709551616 := c.toNat_lt
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  rw [UInt64.toNat_sub, h1, h64]
  omega

theorem u64_ne_zero_of_toNat_succ (c : UInt64) (k : Nat) (hc : c.toNat = k + 1) : c ≠ 0 := by
  intro h
  rw [h] at hc
  exact Nat.succ_ne_zero k hc.symm

theorem u64_one_sub_one : (1 : UInt64) - 1 = 0 := by decide

/-- ASCII bytes of the symbol name `qsag_asm_ct_memzero_x86_64`. -/
@[expose] def ctMemzeroX86Name : List UInt8 :=
  [0x71, 0x73, 0x61, 0x67, 0x5f, 0x61, 0x73, 0x6d, 0x5f, 0x63, 0x74, 0x5f, 0x6d, 0x65, 0x6d, 0x7a,
   0x65, 0x72, 0x6f, 0x5f, 0x78, 0x38, 0x36, 0x5f, 0x36, 0x34]


/-- The preconditions of `current_ct_memzero_x86_64_mc_refines` are satisfiable (length 1). -/
theorem ct_memzero_x86_64_pre_inhabited :
    ∃ s : X86State, s.pc = 0 ∧ s.halted = false ∧ 0 < (s.gpr.get 6).toNat :=
  ⟨⟨0, Bank16.const 1, Bank16.const Vec256.zero, false, false, false, false, false, fun _ => 0⟩,
    rfl, rfl, by decide⟩

/-- ASCII bytes of the symbol name `qsag_asm_ct_memzero_aarch64`. -/
@[expose] def ctMemzeroArmName : List UInt8 :=
  [0x71, 0x73, 0x61, 0x67, 0x5f, 0x61, 0x73, 0x6d, 0x5f, 0x63, 0x74, 0x5f, 0x6d, 0x65, 0x6d, 0x7a,
   0x65, 0x72, 0x6f, 0x5f, 0x61, 0x61, 0x72, 0x63, 0x68, 0x36, 0x34]

def ctMemzeroArmProg : List (DecodedInstr Arm64Instr) := [
  ⟨0, 4, .strbPost 31 0 1⟩,
  ⟨4, 4, .aluImm .subs true 1 1 1⟩,
  ⟨8, 4, .bCond 1 0⟩,
  ⟨12, 4, .dmbIsh⟩,
  ⟨16, 4, .ret⟩]


section MemzeroArm
variable {r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64} {hi : Bank16 UInt64}
  {v : Bank32 Vec128} {dit : Bool}

/-- One trip round the store loop (three instructions). -/
theorem ctMemzeroArm_body (c p : UInt64) (cf zf : Bool) (m : UInt64 → UInt8) (fuel : Nat) :
    (runArm64 ctMemzeroArmProg (fuel + 3)
      ⟨0, ⟨⟨p, c, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        v, cf, zf, dit, false, m⟩).1 =
    (runArm64 ctMemzeroArmProg fuel
      ⟨jccPc (!(c - 1 == 0)) 0 12,
        ⟨⟨p + 1, c - 1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        v, decide (c.toNat ≥ (1 : UInt64).toNat), c - 1 == 0, dit, false, writeMem8 m p 0⟩).1 := by
  iterate 3
    refine Eq.trans (runArm64_step_fst _ _ _ _ rfl rfl) ?_
    simp only [stepArm64_strbPost, stepArm64_subsImm, stepArm64_bne, uint64_evalSub_eq,
      u64_zero_toUInt8, armGet_31, armGet_0, armGet_1, armSet_0, armSet_1]

theorem ctMemzeroArm_loop (k : Nat) :
    ∀ (c p : UInt64) (cf zf : Bool) (m : UInt64 → UInt8) (fuel : Nat), c.toNat = k + 1 →
    (runArm64 ctMemzeroArmProg (3 * (k + 1) + fuel)
      ⟨0, ⟨⟨p, c, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        v, cf, zf, dit, false, m⟩).1 =
    (runArm64 ctMemzeroArmProg fuel
      ⟨12, ⟨⟨p + UInt64.ofNat (k + 1), 0, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        v, true, true, dit, false, zeroRange (k + 1) m p⟩).1 := by
  induction k with
  | zero =>
    intro c p cf zf m fuel hc
    have hc1 : c = 1 := u64_eq_of_toNat hc
    subst hc1
    rw [show 3 * (0 + 1) + fuel = fuel + 3 from by omega, ctMemzeroArm_body, u64_one_sub_one,
      u64_zero_beq_zero]
    try rfl
  | succ k ih =>
    intro c p cf zf m fuel hc
    have hc' := u64_pred_toNat c k hc
    have hne := u64_ne_zero_of_toNat_succ (c - 1) k hc'
    rw [show 3 * (k + 1 + 1) + fuel = (3 * (k + 1) + fuel) + 3 from by omega, ctMemzeroArm_body,
      beq_false_of_ne hne, show jccPc (!false) 0 12 = 0 from rfl,
      ih (c - 1) (p + 1) _ false (writeMem8 m p 0) fuel hc', addr_succ]
    try rfl

theorem ctMemzeroArm_run {r0 r1 : UInt64} {cf zf : Bool} (m : UInt64 → UInt8) (k j : Nat)
    (hn : r1.toNat = k + 1) :
    (runArm64 ctMemzeroArmProg (3 * (k + 1) + 2 + j)
      ⟨0, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        v, cf, zf, dit, false, m⟩).1 =
      ⟨16, ⟨⟨r0 + UInt64.ofNat (k + 1), 0, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        v, true, true, dit, true, zeroRange (k + 1) m r0⟩ := by
  rw [show 3 * (k + 1) + 2 + j = 3 * (k + 1) + (j + 2) from by omega,
    ctMemzeroArm_loop k r1 r0 cf zf m (j + 2) hn]
  iterate 2
    refine Eq.trans (runArm64_step_fst _ _ _ _ rfl rfl) ?_
    simp only [stepArm64_dmb, stepArm64_ret]
  exact runArm64_halted_fst _ _ _ rfl

end MemzeroArm


/-- The preconditions of `current_ct_memzero_aarch64_mc_refines` are satisfiable (length 1). -/
theorem ct_memzero_aarch64_pre_inhabited :
    ∃ s : Arm64State, s.pc = 0 ∧ s.halted = false ∧ 0 < (s.gpr.get 1).toNat :=
  ⟨⟨0, Bank32.const 1, Bank32.const Vec128.zero, false, false, false, false, fun _ => 0⟩,
    rfl, rfl, by decide⟩

/-! ## §9. `qsag_asm_ct_eq_bytes_x86_64`: variable-length equality loop -/

theorem mask32_toNat (v : UInt64) : (maskGprWidth false v).toNat = v.toNat % 4294967296 := by
  show (v &&& 0xFFFFFFFF).toNat = _
  rw [UInt64.toNat_and]
  exact Constructive.and_mask v.toNat 32

theorem mask32_of_lt (v : UInt64) (h : v.toNat < 4294967296) : maskGprWidth false v = v :=
  u64_eq_of_toNat (by rw [mask32_toNat]; exact Nat.mod_eq_of_lt h)

/-- The 32-bit XOR of two zero-extended bytes, as the loop body computes it. -/
def byteDiff (x y : UInt8) : UInt64 :=
  maskGprWidth false (maskGprWidth false x.toUInt64 ^^^ maskGprWidth false y.toUInt64)

theorem byteDiff_eq (x y : UInt8) : byteDiff x y = x.toUInt64 ^^^ y.toUInt64 := by
  have hx : x.toUInt64.toNat < 2 ^ 8 := by rw [UInt8.toNat_toUInt64]; exact x.toNat_lt
  have hy : y.toUInt64.toNat < 2 ^ 8 := by rw [UInt8.toNat_toUInt64]; exact y.toNat_lt
  have hxy : (x.toUInt64 ^^^ y.toUInt64).toNat < 2 ^ 8 := by
    rw [UInt64.toNat_xor]; exact Nat.xor_lt_two_pow hx hy
  unfold byteDiff
  rw [mask32_of_lt x.toUInt64 (by omega), mask32_of_lt y.toUInt64 (by omega), mask32_of_lt _ (by omega)]

/-- One accumulator update keeps the accumulator a byte and records any difference. -/
theorem accStep_spec (acc : UInt64) (x y : UInt8) (hacc : acc.toNat < 256) :
    (maskGprWidth false (acc ||| byteDiff x y)).toNat < 256 ∧
    (maskGprWidth false (acc ||| byteDiff x y) = 0 ↔ acc = 0 ∧ x = y) := by
  have hx : x.toUInt64.toNat < 2 ^ 8 := by rw [UInt8.toNat_toUInt64]; exact x.toNat_lt
  have hy : y.toUInt64.toNat < 2 ^ 8 := by rw [UInt8.toNat_toUInt64]; exact y.toNat_lt
  have hxy : (x.toUInt64 ^^^ y.toUInt64).toNat < 2 ^ 8 := by
    rw [UInt64.toNat_xor]; exact Nat.xor_lt_two_pow hx hy
  have hor : (acc ||| (x.toUInt64 ^^^ y.toUInt64)).toNat < 2 ^ 8 := by
    rw [UInt64.toNat_or]; exact Nat.or_lt_two_pow hacc hxy
  rw [byteDiff_eq, mask32_of_lt _ (by omega)]
  refine ⟨hor, ?_⟩
  rw [UInt64.or_eq_zero_iff, UInt64.xor_eq_zero_iff]
  constructor
  · intro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have := congrArg UInt64.toUInt8 h2
    rw [UInt8.toUInt8_toUInt64, UInt8.toUInt8_toUInt64] at this
    exact this
  · intro ⟨h1, h2⟩
    exact ⟨h1, by rw [h2]⟩

/-- The accumulator after `k` loop iterations starting from `acc`. -/
@[expose] def eqAcc : Nat → (UInt64 → UInt8) → UInt64 → UInt64 → UInt64 → UInt64
  | 0, _, _, _, acc => acc
  | k + 1, m, p, q, acc => eqAcc k m (p + 1) (q + 1) (maskGprWidth false (acc ||| byteDiff (m p) (m q)))

theorem eqAcc_spec (m : UInt64 → UInt8) (k : Nat) : ∀ (p q acc : UInt64), acc.toNat < 256 →
    (eqAcc k m p q acc).toNat < 256 ∧
    (eqAcc k m p q acc = 0 ↔
      acc = 0 ∧ ∀ i : Nat, i < k → m (p + UInt64.ofNat i) = m (q + UInt64.ofNat i)) := by
  induction k with
  | zero =>
    intro p q acc hacc
    exact ⟨hacc, fun h => ⟨h, fun i hi => absurd hi (Nat.not_lt_zero i)⟩, fun h => h.1⟩
  | succ k ih =>
    intro p q acc hacc
    obtain ⟨hlt', hz'⟩ := accStep_spec acc (m p) (m q) hacc
    obtain ⟨ih1, ih2⟩ := ih (p + 1) (q + 1) _ hlt'
    refine ⟨ih1, ?_⟩
    show eqAcc k m (p + 1) (q + 1) (maskGprWidth false (acc ||| byteDiff (m p) (m q))) = 0 ↔ _
    constructor
    · intro h0
      obtain ⟨ha, hall⟩ := ih2.mp h0
      obtain ⟨hacc0, hpq⟩ := hz'.mp ha
      refine ⟨hacc0, fun i hi => ?_⟩
      cases i with
      | zero => rw [addr_zero, addr_zero]; exact hpq
      | succ j => rw [← addr_succ, ← addr_succ]; exact hall j (by omega)
    · intro ⟨hacc0, hall⟩
      apply ih2.mpr
      refine ⟨hz'.mpr ⟨hacc0, ?_⟩, fun i hi => ?_⟩
      · have := hall 0 (by omega)
        rw [addr_zero, addr_zero] at this
        exact this
      · have := hall (i + 1) (by omega)
        rw [← addr_succ, ← addr_succ] at this
        exact this

/-- `sub eax, 1; shr eax, 31` turns a byte-sized accumulator into its zero test. -/
theorem eqTail_spec (A : UInt64) (hA : A.toNat < 256) :
    maskGprWidth false (maskGprWidth false (maskGprWidth false (UInt64.ofNat
      (((maskGprWidth false A).toNat + 0x100000000 - (maskGprWidth false 1).toNat) % 0x100000000))) >>>
        UInt64.ofNat (31 % 32)) = if A = 0 then 1 else 0 := by
  if h0 : A = 0 then
    subst h0; rw [ite_eq_left rfl]; decide
  else
    rw [ite_eq_right h0]
    have hpos : 0 < A.toNat := Nat.pos_of_ne_zero (fun h => h0 (u64_eq_of_toNat h))
    have hA' : (maskGprWidth false A).toNat = A.toNat := by rw [mask32_toNat]; omega
    have h1 : (maskGprWidth false 1).toNat = 1 := by decide
    apply u64_eq_of_toNat
    have h31 : (UInt64.ofNat (31 % 32)).toNat % 64 = 31 := by decide
    have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
    rw [mask32_toNat, UInt64.toNat_shiftRight, h31, mask32_toNat, mask32_toNat, UInt64.toNat_ofNat', hA', h1,
      Nat.shiftRight_eq_div_pow, h64]
    show _ / 2147483648 % 4294967296 = 0
    omega

/-- ASCII bytes of the symbol name `qsag_asm_ct_eq_bytes_x86_64`. -/
@[expose] def ctEqBytesX86Name : List UInt8 :=
  [0x71, 0x73, 0x61, 0x67, 0x5f, 0x61, 0x73, 0x6d, 0x5f, 0x63, 0x74, 0x5f, 0x65, 0x71, 0x5f, 0x62,
   0x79, 0x74, 0x65, 0x73, 0x5f, 0x78, 0x38, 0x36, 0x5f, 0x36, 0x34]


/-- The preconditions of `current_ct_eq_bytes_x86_64_mc_refines` are satisfiable (length 1). -/
theorem ct_eq_bytes_x86_64_pre_inhabited :
    ∃ s : X86State, s.pc = 0 ∧ s.halted = false ∧ 0 < (s.gpr.get 2).toNat :=
  ⟨⟨0, Bank16.const 1, Bank16.const Vec256.zero, false, false, false, false, false, fun _ => 0⟩,
    rfl, rfl, by decide⟩

/-! ## §10. Mutation refusal: the specifications and the NI checker reject mutated machine code -/

/-- Entry state with the given `rdi`, `rsi`, `rdx`, `rax`, every memory byte `b`, all else zero. -/
@[expose] def x86Init (rdi rsi rdx rax : UInt64) (b : UInt8) : X86State :=
  ⟨0, ⟨rax, 0, rdx, 0, 0, 0, rsi, rdi, 0, 0, 0, 0, 0, 0, 0, 0⟩, Bank16.const Vec256.zero,
    false, false, false, false, false, fun _ => b⟩

/-- Entry state with the given `x0`, `x1`, every memory byte `b`, all else zero. -/
@[expose] def armInit (x0 x1 : UInt64) (b : UInt8) : Arm64State :=
  ⟨0, ⟨⟨x0, x1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩, Bank16.const 0⟩, Bank32.const Vec128.zero,
    false, false, false, false, fun _ => b⟩

/-- Mutant of `ct_eq_32_x86_64` with the final `xor eax, 1` turned into `xor eax, 0`: it decodes,
halts, and returns `0` on two equal (all-zero) buffers, where the specification demands `1`. -/
theorem ct_eq_32_x86_64_mutant_refuted :
    ((findSliceByNameBytes currentX86ExtractedSlices ctEq32X86Name).bind
        (fun sl => decodeX86Stream (patchBytesAt sl.code 52 [0x83, 0xF0, 0x00]))).any
      (fun p => (runX86 p 28 (x86Init 0 64 0 0 0)).1.halted &&
        (runX86 p 28 (x86Init 0 64 0 0 0)).1.gpr.get 0 == 0) = true ∧
    (∀ i : Nat, i < 32 →
      (x86Init 0 64 0 0 0).mem ((x86Init 0 64 0 0 0).gpr.get 7 + UInt64.ofNat i) =
      (x86Init 0 64 0 0 0).mem ((x86Init 0 64 0 0 0).gpr.get 6 + UInt64.ofNat i)) :=
  ⟨by decide +kernel, fun _ _ => rfl⟩

/-- NI tooth: the compiled `ct_eq_32_x86_64` passes the 3-way NI checker under its contract, and
the variant whose `or rax, rcx` is replaced by `je +1; nop` (a branch on flags derived from the
secret buffers) is rejected. -/
theorem ct_eq_32_x86_64_secret_branch_rejected :
    (findSliceByNameBytes currentX86ExtractedSlices ctEq32X86Name).map
        (fun sl => (checkX86ThreeWayNI sl.code
            (mkContract "qsag_asm_ct_eq_32_x86_64" [4, 7, 6] [] [1, 2, 8]),
          checkX86ThreeWayNI (patchBytesAt sl.code 30 [0x74, 0x01, 0x90])
            (mkContract "qsag_asm_ct_eq_32_x86_64" [4, 7, 6] [] [1, 2, 8])))
      = some (true, false) := by
  decide +kernel

/-- Mutant of `ct_eq_32_aarch64` with the final `eor x0, x0, #1` turned into `nop`: it returns `0`
on two equal (all-zero) buffers, where the specification demands `1`. -/
theorem ct_eq_32_aarch64_mutant_refuted :
    ((findSliceByNameBytes currentAarch64ExtractedSlices ctEq32ArmName).bind
        (fun sl => decodeArm64Stream (patchBytesAt sl.code 56 [0x1F, 0x20, 0x03, 0xD5]))).any
      (fun p => (runArm64 p 22 (armInit 0 64 0)).1.halted &&
        (runArm64 p 22 (armInit 0 64 0)).1.gpr.get 0 == 0) = true ∧
    (∀ i : Nat, i < 32 →
      (armInit 0 64 0).mem ((armInit 0 64 0).gpr.get 0 + UInt64.ofNat i) =
      (armInit 0 64 0).mem ((armInit 0 64 0).gpr.get 1 + UInt64.ofNat i)) :=
  ⟨by decide +kernel, fun _ _ => rfl⟩

/-- NI tooth: the compiled `ct_eq_32_aarch64` passes the 3-way NI checker under its contract, and
the variant whose `lsr x0, x2, #63` is replaced by `cbz w2, +8` (a branch on the secret difference
word) is rejected. -/
theorem ct_eq_32_aarch64_secret_branch_rejected :
    (findSliceByNameBytes currentAarch64ExtractedSlices ctEq32ArmName).map
        (fun sl => (checkArm64ThreeWayNI sl.code
            (mkContract "qsag_asm_ct_eq_32_aarch64" [0, 1] [] [2, 3, 4, 5, 6, 7]),
          checkArm64ThreeWayNI (patchBytesAt sl.code 52 [0x42, 0x00, 0x00, 0x34])
            (mkContract "qsag_asm_ct_eq_32_aarch64" [0, 1] [] [2, 3, 4, 5, 6, 7])))
      = some (true, false) := by
  decide +kernel

/-- Mutant of `ct_memzero_x86_64` with `xor eax, eax` turned into `mov eax, eax`: with `rax = 0xAA`
and length 1 it halts leaving the byte at `rdi` nonzero. -/
theorem ct_memzero_x86_64_mutant_refuted :
    ((findSliceByNameBytes currentX86ExtractedSlices ctMemzeroX86Name).bind
        (fun sl => decodeX86Stream (patchBytesAt sl.code 3 [0x89, 0xC0]))).any
      (fun p => (runX86 p 33 (x86Init 16 1 0 0xAA 0x55)).1.halted &&
        (runX86 p 33 (x86Init 16 1 0 0xAA 0x55)).1.mem 16 != 0) = true := by
  decide +kernel

/-- Mutant of `ct_memzero_aarch64` with `strb wzr, [x0], #1` turned into `strb w1, [x0], #1`: with
length 1 it halts leaving the byte at `x0` equal to `1`. -/
theorem ct_memzero_aarch64_mutant_refuted :
    ((findSliceByNameBytes currentAarch64ExtractedSlices ctMemzeroArmName).bind
        (fun sl => decodeArm64Stream (patchBytesAt sl.code 0 [0x01, 0x14, 0x00, 0x38]))).any
      (fun p => (runArm64 p 5 (armInit 16 1 0x55)).1.halted &&
        (runArm64 p 5 (armInit 16 1 0x55)).1.mem 16 != 0) = true := by
  decide +kernel

/-- Mutant of `ct_eq_bytes_x86_64` with `shr eax, 31` turned into `shr eax, 30`: on two equal
one-byte buffers it returns `3`, where the specification demands `1`. -/
theorem ct_eq_bytes_x86_64_mutant_refuted :
    ((findSliceByNameBytes currentX86ExtractedSlices ctEqBytesX86Name).bind
        (fun sl => decodeX86Stream (patchBytesAt sl.code 33 [0xC1, 0xE8, 0x1E]))).any
      (fun p => (runX86 p 31 (x86Init 0 64 1 0 0)).1.halted &&
        (runX86 p 31 (x86Init 0 64 1 0 0)).1.gpr.get 0 == 3) = true ∧
    (∀ i : Nat, i < ((x86Init 0 64 1 0 0).gpr.get 2).toNat →
      (x86Init 0 64 1 0 0).mem ((x86Init 0 64 1 0 0).gpr.get 7 + UInt64.ofNat i) =
      (x86Init 0 64 1 0 0).mem ((x86Init 0 64 1 0 0).gpr.get 6 + UInt64.ofNat i)) :=
  ⟨by decide +kernel, fun _ _ => rfl⟩

/-- NI tooth: the compiled `ct_eq_bytes_x86_64` passes the 3-way NI checker under its contract, and
the variant whose `or eax, r8d` is replaced by `je +1; nop` (a branch on the flags of the secret
byte XOR) is rejected. -/
theorem ct_eq_bytes_x86_64_secret_branch_rejected :
    (findSliceByNameBytes currentX86ExtractedSlices ctEqBytesX86Name).map
        (fun sl => (checkX86ThreeWayNI sl.code
            (mkContract "qsag_asm_ct_eq_bytes_x86_64" [4, 7, 6, 2] [] [8, 9]),
          checkX86ThreeWayNI (patchBytesAt sl.code 16 [0x74, 0x01, 0x90])
            (mkContract "qsag_asm_ct_eq_bytes_x86_64" [4, 7, 6, 2] [] [8, 9])))
      = some (true, false) := by
  decide +kernel

/-! ## §11. Goldilocks field kernels (`p = 2^64 - 2^32 + 1`) -/

theorem sbb32_self (v : UInt64) (cf : Bool) :
    evalX86Alu .sbb false v v cf = (if cf then 0xFFFFFFFF else 0, cf, !cf) := by
  rw [evalX86Alu_sbb_self_congr false v 0 cf]
  cases cf <;> decide

theorem sbb64_self (v : UInt64) (cf : Bool) :
    evalX86Alu .sbb true v v cf = (if cf then 0xFFFFFFFFFFFFFFFF else 0, cf, !cf) := by
  rw [evalX86Alu_sbb_self_congr true v 0 cf]
  cases cf <;> decide

/-- Add `2^32 - 1` (the residue of `2^64`) when a carry is pending; report the new carry. -/
def foldCarry (s : UInt64) (c : Bool) : UInt64 × Bool :=
  (s + (if c then 0xFFFFFFFF else 0),
    decide (s.toNat + (if c then (0xFFFFFFFF : UInt64) else 0).toNat ≥ 0x10000000000000000))

/-- Branch-free conditional subtraction of `p`, as `add r8, r9; sbb rcx, rcx; and rcx, r9; add`. -/
def goldCanon (s : UInt64) : UInt64 :=
  s + ((if decide (s.toNat + (maskGprWidth false 4294967295).toNat ≥ 0x10000000000000000)
        then 0xFFFFFFFFFFFFFFFF else 0) &&& maskGprWidth false 4294967295)

theorem goldCanon_toNat (s : UInt64) : (goldCanon s).toNat = s.toNat % goldilocksPrime := by
  have hs : s.toNat < 18446744073709551616 := s.toNat_lt
  have hm : maskGprWidth false 4294967295 = 4294967295 := by decide
  have hE : (4294967295 : UInt64).toNat = 4294967295 := rfl
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  unfold goldCanon
  rw [hm, hE]
  show _ = s.toNat % 18446744069414584321
  if h : s.toNat + 4294967295 ≥ 18446744073709551616 then
    have hand : (0xFFFFFFFFFFFFFFFF : UInt64) &&& 4294967295 = 4294967295 := by decide
    rw [decide_eq_true h, ite_eq_left rfl, hand, UInt64.toNat_add, hE, h64]
    omega
  else
    have hand : (0 : UInt64) &&& 4294967295 = 0 := by decide
    have h0 : (0 : UInt64).toNat = 0 := rfl
    rw [decide_eq_false h, ite_eq_right (by decide), hand, UInt64.toNat_add, h0, h64]
    omega

/-- Two carry folds leave a word congruent to the full sum `s + 2^64·c` modulo `p`. -/
theorem foldCarry2_mod (s : UInt64) (c : Bool) :
    (foldCarry (foldCarry s c).1 (foldCarry s c).2).1.toNat % goldilocksPrime =
      (s.toNat + (if c then 18446744073709551616 else 0)) % goldilocksPrime := by
  have hs : s.toNat < 18446744073709551616 := s.toNat_lt
  have hE : (0xFFFFFFFF : UInt64).toNat = 4294967295 := rfl
  have h0 : (0 : UInt64).toNat = 0 := rfl
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  have hz : ∀ x : UInt64, foldCarry x false = (x, false) := by
    intro x
    have hx : x.toNat < 18446744073709551616 := x.toNat_lt
    unfold foldCarry
    rw [ite_eq_right (by decide), UInt64.add_zero, h0, decide_eq_false (by omega)]
  show _ % 18446744069414584321 = _ % 18446744069414584321
  cases c with
  | false => rw [hz s, hz s, ite_eq_right (by decide)]; rfl
  | true =>
    rw [ite_eq_left rfl]
    have hf : foldCarry s true = (s + 0xFFFFFFFF,
        decide (s.toNat + 4294967295 ≥ 18446744073709551616)) := by
      unfold foldCarry
      rw [ite_eq_left rfl, hE]
    rw [hf]
    if h : s.toNat + 4294967295 ≥ 18446744073709551616 then
      rw [decide_eq_true h]
      show (foldCarry (s + 0xFFFFFFFF) true).1.toNat % _ = _
      show ((s + 0xFFFFFFFF) + (if true then 0xFFFFFFFF else 0)).toNat % _ = _
      rw [ite_eq_left rfl, UInt64.toNat_add, UInt64.toNat_add, hE, h64]
      omega
    else
      rw [decide_eq_false h]
      show (foldCarry (s + 0xFFFFFFFF) false).1.toNat % _ = _
      rw [hz, UInt64.toNat_add, hE, h64]
      omega

/-- The value `goldilocks_add_ct` leaves in `rax`. -/
def goldAddMc (a b : UInt64) : UInt64 :=
  goldCanon (foldCarry (foldCarry (a + b) (decide (a.toNat + b.toNat ≥ 0x10000000000000000))).1
    (foldCarry (a + b) (decide (a.toNat + b.toNat ≥ 0x10000000000000000))).2).1

theorem goldAddMc_toNat (a b : UInt64) :
    (goldAddMc a b).toNat = (a.toNat + b.toNat) % goldilocksPrime := by
  have ha : a.toNat < 18446744073709551616 := a.toNat_lt
  have hb : b.toNat < 18446744073709551616 := b.toNat_lt
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  unfold goldAddMc
  rw [goldCanon_toNat, foldCarry2_mod]
  show _ % 18446744069414584321 = _ % 18446744069414584321
  if h : a.toNat + b.toNat ≥ 18446744073709551616 then
    rw [decide_eq_true h, ite_eq_left rfl, UInt64.toNat_add, h64]
    omega
  else
    rw [decide_eq_false h, ite_eq_right (by decide), UInt64.toNat_add, h64]
    omega

/-- The value `goldilocks_sub_ct` leaves in `rax`. -/
def goldSubMc (a b : UInt64) : UInt64 :=
  (goldCanon a - goldCanon b) +
    ((if decide ((goldCanon a).toNat < (goldCanon b).toNat) then 0xFFFFFFFFFFFFFFFF else 0) &&&
      18446744069414584321)

theorem goldSubMc_toNat (a b : UInt64) :
    (goldSubMc a b).toNat =
      (a.toNat + goldilocksPrime - b.toNat % goldilocksPrime) % goldilocksPrime := by
  have hx := goldCanon_toNat a
  have hy := goldCanon_toNat b
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  have hP : (18446744069414584321 : UInt64).toNat = 18446744069414584321 := rfl
  have h0 : (0 : UInt64).toNat = 0 := rfl
  unfold goldSubMc
  have hx' : (goldCanon a).toNat = a.toNat % 18446744069414584321 := hx
  have hy' : (goldCanon b).toNat = b.toNat % 18446744069414584321 := hy
  show _ = (a.toNat + 18446744069414584321 - b.toNat % 18446744069414584321) % 18446744069414584321
  if h : (goldCanon a).toNat < (goldCanon b).toNat then
    have hand : (0xFFFFFFFFFFFFFFFF : UInt64) &&& 18446744069414584321 = 18446744069414584321 := by
      decide
    rw [decide_eq_true h, ite_eq_left rfl, hand, UInt64.toNat_add, UInt64.toNat_sub, hP, h64]
    omega
  else
    have hand : (0 : UInt64) &&& 18446744069414584321 = 0 := by decide
    rw [decide_eq_false h, ite_eq_right (by decide), hand, UInt64.toNat_add, UInt64.toNat_sub, h0, h64]
    omega

/-- ASCII bytes of the symbol name `qsag_asm_goldilocks_add_ct_x86_64`. -/
@[expose] def goldAddX86Name : List UInt8 :=
  [0x71, 0x73, 0x61, 0x67, 0x5f, 0x61, 0x73, 0x6d, 0x5f, 0x67, 0x6f, 0x6c, 0x64, 0x69, 0x6c, 0x6f,
   0x63, 0x6b, 0x73, 0x5f, 0x61, 0x64, 0x64, 0x5f, 0x63, 0x74, 0x5f, 0x78, 0x38, 0x36, 0x5f, 0x36, 0x34]


/-- ASCII bytes of the symbol name `qsag_asm_goldilocks_sub_ct_x86_64`. -/
@[expose] def goldSubX86Name : List UInt8 :=
  [0x71, 0x73, 0x61, 0x67, 0x5f, 0x61, 0x73, 0x6d, 0x5f, 0x67, 0x6f, 0x6c, 0x64, 0x69, 0x6c, 0x6f,
   0x63, 0x6b, 0x73, 0x5f, 0x73, 0x75, 0x62, 0x5f, 0x63, 0x74, 0x5f, 0x78, 0x38, 0x36, 0x5f, 0x36, 0x34]


/-! ### Goldilocks multiplication: `2^64 ≡ 2^32 - 1` and `2^96 ≡ -1` reduction of a 128-bit product -/

/-- `x - y`, then subtract `2^32 - 1` when the subtraction borrowed. -/
def subBorrow (x y : UInt64) : UInt64 :=
  (x - y) - (if decide (x.toNat < y.toNat) then 0xFFFFFFFF else 0)

theorem subBorrow_mod (x y : UInt64) (hy : y.toNat < 4294967296) :
    (subBorrow x y).toNat % 18446744069414584321 =
      (x.toNat + 18446744069414584321 - y.toNat) % 18446744069414584321 := by
  have hx : x.toNat < 18446744073709551616 := x.toNat_lt
  have hE : (0xFFFFFFFF : UInt64).toNat = 4294967295 := rfl
  have h0 : (0 : UInt64).toNat = 0 := rfl
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  unfold subBorrow
  if h : x.toNat < y.toNat then
    rw [decide_eq_true h, ite_eq_left rfl, UInt64.toNat_sub, UInt64.toNat_sub, hE, h64]
    omega
  else
    rw [decide_eq_false h, ite_eq_right (by decide), UInt64.toNat_sub, UInt64.toNat_sub, h0, h64]
    omega

/-- `(hi mod 2^32) · (2^32 - 1)` as `shl 32; sub`. -/
def hiLoEps (hi : UInt64) : UInt64 :=
  (maskGprWidth false hi <<< UInt64.ofNat (32 % 64)) - maskGprWidth false hi

theorem hiLoEps_toNat (hi : UInt64) :
    (hiLoEps hi).toNat = hi.toNat % 4294967296 * 4294967295 := by
  have h32 : (UInt64.ofNat (32 % 64)).toNat % 64 = 32 := by decide
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  have h32p : (2 : Nat) ^ 32 = 4294967296 := rfl
  unfold hiLoEps
  rw [UInt64.toNat_sub, UInt64.toNat_shiftLeft, h32, mask32_toNat, Nat.shiftLeft_eq, h64, h32p]
  omega

/-- `x + y`, then add `2^32 - 1` when the addition carried. -/
def addCarry (x y : UInt64) : UInt64 :=
  (foldCarry (x + y) (decide (x.toNat + y.toNat ≥ 0x10000000000000000))).1

theorem addCarry_mod (x y : UInt64) (hy : y.toNat ≤ 18446744069414584321) :
    (addCarry x y).toNat % 18446744069414584321 = (x.toNat + y.toNat) % 18446744069414584321 := by
  have hx : x.toNat < 18446744073709551616 := x.toNat_lt
  have hE : (0xFFFFFFFF : UInt64).toNat = 4294967295 := rfl
  have h0 : (0 : UInt64).toNat = 0 := rfl
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  show ((x + y) + (if decide (x.toNat + y.toNat ≥ 18446744073709551616) then 0xFFFFFFFF else 0)).toNat %
      18446744069414584321 = _
  if h : x.toNat + y.toNat ≥ 18446744073709551616 then
    rw [decide_eq_true h, ite_eq_left rfl, UInt64.toNat_add, UInt64.toNat_add, hE, h64]
    omega
  else
    rw [decide_eq_false h, ite_eq_right (by decide), UInt64.toNat_add, UInt64.toNat_add, h0, h64]
    omega

/-- Reduction of the 128-bit value `lo + 2^64·hi` to one word congruent to it modulo `p`. -/
def mulRed (lo hi : UInt64) : UInt64 :=
  addCarry (subBorrow lo (hi >>> UInt64.ofNat (32 % 64))) (hiLoEps hi)

theorem mulRed_mod (lo hi : UInt64) :
    (mulRed lo hi).toNat % 18446744069414584321 =
      (lo.toNat + hi.toNat * 18446744073709551616) % 18446744069414584321 := by
  have hlo : lo.toNat < 18446744073709551616 := lo.toNat_lt
  have hhi : hi.toNat < 18446744073709551616 := hi.toNat_lt
  have hHH : (hi >>> UInt64.ofNat (32 % 64)).toNat = hi.toNat / 4294967296 := by
    have h32 : (UInt64.ofNat (32 % 64)).toNat % 64 = 32 := by decide
    have h32p : (2 : Nat) ^ 32 = 4294967296 := rfl
    rw [UInt64.toNat_shiftRight, h32, Nat.shiftRight_eq_div_pow, h32p]
  have hA := subBorrow_mod lo (hi >>> UInt64.ofNat (32 % 64)) (by rw [hHH]; omega)
  have hB := hiLoEps_toNat hi
  have hR := addCarry_mod (subBorrow lo (hi >>> UInt64.ofNat (32 % 64))) (hiLoEps hi)
    (by rw [hB]; omega)
  unfold mulRed
  rw [hR, hB]
  rw [hHH] at hA
  omega

/-- The value `goldilocks_mul_ct` leaves in `rax`. -/
def goldMulMc (a b : UInt64) : UInt64 :=
  goldCanon (mulRed (UInt64.ofNat ((a.toNat * b.toNat) % 0x10000000000000000))
    (UInt64.ofNat ((a.toNat * b.toNat) / 0x10000000000000000)))

theorem goldMulMc_toNat (a b : UInt64) :
    (goldMulMc a b).toNat = (a.toNat * b.toNat) % goldilocksPrime := by
  have ha : a.toNat < 18446744073709551616 := a.toNat_lt
  have hb : b.toNat < 18446744073709551616 := b.toNat_lt
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  have hprod : a.toNat * b.toNat < 18446744073709551616 * 18446744073709551616 :=
    Nat.mul_lt_mul'' ha hb
  unfold goldMulMc
  rw [goldCanon_toNat]
  show _ % 18446744069414584321 = _ % 18446744069414584321
  rw [mulRed_mod, UInt64.toNat_ofNat', UInt64.toNat_ofNat', h64]
  generalize a.toNat * b.toNat = q at hprod ⊢
  have h1 : q % 18446744073709551616 % 18446744073709551616 = q % 18446744073709551616 :=
    Nat.mod_mod _ _
  have h2 : q / 18446744073709551616 % 18446744073709551616 = q / 18446744073709551616 :=
    Nat.mod_eq_of_lt (by omega)
  have h3 : q % 18446744073709551616 + q / 18446744073709551616 * 18446744073709551616 = q := by
    omega
  rw [h1, h2, h3]

/-- ASCII bytes of the symbol name `qsag_asm_goldilocks_mul_ct_x86_64`. -/
@[expose] def goldMulX86Name : List UInt8 :=
  [0x71, 0x73, 0x61, 0x67, 0x5f, 0x61, 0x73, 0x6d, 0x5f, 0x67, 0x6f, 0x6c, 0x64, 0x69, 0x6c, 0x6f,
   0x63, 0x6b, 0x73, 0x5f, 0x6d, 0x75, 0x6c, 0x5f, 0x63, 0x74, 0x5f, 0x78, 0x38, 0x36, 0x5f, 0x36, 0x34]


/-! ### Goldilocks multiplication on `AArch64` -/

theorem armAdcZero (c : Bool) :
    UInt64.ofNat (((0 : UInt64).toNat + (0 : UInt64).toNat + (if c then 1 else 0)) %
      0x10000000000000000) = if c then 1 else 0 := by
  cases c <;> decide

theorem armSbcZero (c : Bool) :
    UInt64.ofNat (((0 : UInt64).toNat + 0x10000000000000000 * 2 - (0 : UInt64).toNat -
      (if c then 0 else 1)) % 0x10000000000000000) = if c then 0 else 0xFFFFFFFFFFFFFFFF := by
  cases c <;> decide

theorem u64_neg_cond (c : Bool) :
    (0 : UInt64) - (if c then 1 else 0) = if c then 0xFFFFFFFFFFFFFFFF else 0 := by
  cases c <;> decide

theorem movn32_zero : maskGprWidth false (~~~(0 : UInt64)) = 0xFFFFFFFF := by
  decide

theorem condAll_and_eps (c : Bool) :
    (if c then (0xFFFFFFFFFFFFFFFF : UInt64) else 0) &&& 0xFFFFFFFF = if c then 0xFFFFFFFF else 0 := by
  cases c <;> decide

theorem condNone_and_eps (c : Bool) :
    (if c then (0 : UInt64) else 0xFFFFFFFFFFFFFFFF) &&& 0xFFFFFFFF = if c then 0 else 0xFFFFFFFF := by
  cases c <;> decide

/-- `x - y`, then subtract `2^32 - 1` when the AArch64 carry flag reports a borrow. -/
def armSubBorrow (x y : UInt64) : UInt64 :=
  (x - y) - (if decide (x.toNat ≥ y.toNat) then 0 else 0xFFFFFFFF)

theorem armSubBorrow_eq (x y : UInt64) : armSubBorrow x y = subBorrow x y := by
  unfold armSubBorrow subBorrow
  if h : x.toNat < y.toNat then
    rw [decide_eq_true h, decide_eq_false (show ¬ x.toNat ≥ y.toNat by omega), ite_eq_left rfl,
      ite_eq_right (by decide)]
  else
    rw [decide_eq_false h, decide_eq_true (show x.toNat ≥ y.toNat by omega), ite_eq_left rfl,
      ite_eq_right (by decide)]

/-- The word `goldilocks_mul_ct_aarch64` holds in `x2` before the final conditional subtraction. -/
def goldMulArmPre (a b : UInt64) : UInt64 :=
  addCarry
    (armSubBorrow (UInt64.ofNat ((a.toNat * b.toNat) % 0x10000000000000000))
      (UInt64.ofNat ((a.toNat * b.toNat) / 0x10000000000000000) >>> UInt64.ofNat 32))
    (((UInt64.ofNat ((a.toNat * b.toNat) / 0x10000000000000000) &&& 4294967295) <<<
        UInt64.ofNat (64 - 32)) -
      (UInt64.ofNat ((a.toNat * b.toNat) / 0x10000000000000000) &&& 4294967295))

theorem goldMulArmPre_eq (a b : UInt64) :
    goldMulArmPre a b = mulRed (UInt64.ofNat ((a.toNat * b.toNat) % 0x10000000000000000))
      (UInt64.ofNat ((a.toNat * b.toNat) / 0x10000000000000000)) := by
  unfold goldMulArmPre
  rw [armSubBorrow_eq]
  rfl

/-- Conditional subtraction of `p` as `adds; adc; sub; and; add`. -/
def armCanon (s : UInt64) : UInt64 :=
  s + (if decide (s.toNat + (0xFFFFFFFF : UInt64).toNat ≥ 0x10000000000000000) then 0xFFFFFFFF else 0)

theorem armCanon_toNat (s : UInt64) : (armCanon s).toNat = s.toNat % goldilocksPrime := by
  have hs : s.toNat < 18446744073709551616 := s.toNat_lt
  have hE : (0xFFFFFFFF : UInt64).toNat = 4294967295 := rfl
  have h0 : (0 : UInt64).toNat = 0 := rfl
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  unfold armCanon
  rw [hE]
  show _ = s.toNat % 18446744069414584321
  if h : s.toNat + 4294967295 ≥ 18446744073709551616 then
    rw [decide_eq_true h, ite_eq_left rfl, UInt64.toNat_add, hE, h64]
    omega
  else
    rw [decide_eq_false h, ite_eq_right (by decide), UInt64.toNat_add, h0, h64]
    omega

theorem goldMulArm_toNat (a b : UInt64) :
    (armCanon (goldMulArmPre a b)).toNat = (a.toNat * b.toNat) % goldilocksPrime := by
  have h := goldMulMc_toNat a b
  unfold goldMulMc at h
  rw [goldCanon_toNat] at h
  rw [armCanon_toNat, goldMulArmPre_eq]
  exact h

/-- ASCII bytes of the symbol name `qsag_asm_goldilocks_mul_ct_aarch64`. -/
@[expose] def goldMulArmName : List UInt8 :=
  [0x71, 0x73, 0x61, 0x67, 0x5f, 0x61, 0x73, 0x6d, 0x5f, 0x67, 0x6f, 0x6c, 0x64, 0x69, 0x6c, 0x6f,
   0x63, 0x6b, 0x73, 0x5f, 0x6d, 0x75, 0x6c, 0x5f, 0x63, 0x74, 0x5f, 0x61, 0x61, 0x72, 0x63, 0x68,
   0x36, 0x34]


/-- The entry preconditions of the Goldilocks refinements are satisfiable (non-canonical inputs
`2^64 - 1` included). -/
theorem goldilocks_x86_64_pre_inhabited :
    ∃ s : X86State, s.pc = 0 ∧ s.halted = false ∧ s.gpr.get 7 = 0xFFFFFFFFFFFFFFFF :=
  ⟨⟨0, Bank16.const 0xFFFFFFFFFFFFFFFF, Bank16.const Vec256.zero, false, false, false, false, false,
    fun _ => 0⟩, rfl, rfl, rfl⟩

theorem goldilocks_aarch64_pre_inhabited :
    ∃ s : Arm64State, s.pc = 0 ∧ s.halted = false ∧ s.gpr.get 0 = 0xFFFFFFFFFFFFFFFF :=
  ⟨⟨0, Bank32.const 0xFFFFFFFFFFFFFFFF, Bank32.const Vec128.zero, false, false, false, false,
    fun _ => 0⟩, rfl, rfl, rfl⟩

/-! ### Mutation refusal for the Goldilocks kernels -/

/-- Mutant of `goldilocks_add_ct_x86_64` with `and rcx, r9` turned into `or rcx, r9`: on `1 + 1`
it halts with `rax ≠ 2 = (1 + 1) mod p`. -/
theorem goldilocks_add_ct_x86_64_mutant_refuted :
    ((findSliceByNameBytes currentX86ExtractedSlices goldAddX86Name).bind
        (fun sl => decodeX86Stream (patchBytesAt sl.code 33 [0x4C, 0x09, 0xC9]))).any
      (fun p => (runX86 p 33 (x86Init 1 1 0 0 0)).1.halted &&
        ((runX86 p 33 (x86Init 1 1 0 0 0)).1.gpr.get 0).toNat != (1 + 1) % goldilocksPrime) = true := by
  decide +kernel

/-- NI tooth: the compiled `goldilocks_add_ct_x86_64` passes the 3-way NI checker with both field
inputs secret, and the variant whose first `sbb r8d, r8d` is replaced by `jc +1; nop` (a branch on
the secret carry) is rejected. -/
theorem goldilocks_add_ct_x86_64_secret_branch_rejected :
    (findSliceByNameBytes currentX86ExtractedSlices goldAddX86Name).map
        (fun sl => (checkX86ThreeWayNI sl.code (mkContract "qsag_asm_goldilocks_add_ct_x86_64" [4]),
          checkX86ThreeWayNI (patchBytesAt sl.code 6 [0x72, 0x01, 0x90])
            (mkContract "qsag_asm_goldilocks_add_ct_x86_64" [4])))
      = some (true, false) := by
  decide +kernel

/-- Mutant of `goldilocks_sub_ct_x86_64` with `sub rax, rsi` turned into `add rax, rsi`: on `5 - 3`
it halts with `rax ≠ 2`. -/
theorem goldilocks_sub_ct_x86_64_mutant_refuted :
    ((findSliceByNameBytes currentX86ExtractedSlices goldSubX86Name).bind
        (fun sl => decodeX86Stream (patchBytesAt sl.code 39 [0x48, 0x01, 0xF0]))).any
      (fun p => (runX86 p 31 (x86Init 5 3 0 0 0)).1.halted &&
        ((runX86 p 31 (x86Init 5 3 0 0 0)).1.gpr.get 0).toNat !=
          (5 + goldilocksPrime - 3 % goldilocksPrime) % goldilocksPrime) = true := by
  decide +kernel

/-- Mutant of `goldilocks_mul_ct_x86_64` with `shr rcx, 32` turned into `shr rcx, 31`: on
`(2^64 - 1)²` it halts with `rax` different from the product modulo `p`. -/
theorem goldilocks_mul_ct_x86_64_mutant_refuted :
    ((findSliceByNameBytes currentX86ExtractedSlices goldMulX86Name).bind
        (fun sl => decodeX86Stream (patchBytesAt sl.code 11 [0x48, 0xC1, 0xE9, 0x1F]))).any
      (fun p => (runX86 p 33 (x86Init 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0 0 0)).1.halted &&
        ((runX86 p 33 (x86Init 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0 0 0)).1.gpr.get 0).toNat !=
          (0xFFFFFFFFFFFFFFFF * 0xFFFFFFFFFFFFFFFF) % goldilocksPrime) = true := by
  decide +kernel

/-- Mutant of `goldilocks_mul_ct_aarch64` with `lsr x4, x3, #32` turned into `lsr x4, x3, #31`: on
`(2^64 - 1)²` it halts with `x0` different from the product modulo `p`. -/
theorem goldilocks_mul_ct_aarch64_mutant_refuted :
    ((findSliceByNameBytes currentAarch64ExtractedSlices goldMulArmName).bind
        (fun sl => decodeArm64Stream (patchBytesAt sl.code 8 [0x64, 0xFC, 0x5F, 0xD3]))).any
      (fun p => (runArm64 p 30 (armInit 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0)).1.halted &&
        ((runArm64 p 30 (armInit 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0)).1.gpr.get 0).toNat !=
          (0xFFFFFFFFFFFFFFFF * 0xFFFFFFFFFFFFFFFF) % goldilocksPrime) = true := by
  decide +kernel

/-- NI tooth: the compiled `goldilocks_mul_ct_aarch64` passes the 3-way NI checker with both field
inputs secret, and the variant whose `sbc x7, xzr, xzr` is replaced by `b.cs +8` (a branch on the
secret borrow) is rejected. -/
theorem goldilocks_mul_ct_aarch64_secret_branch_rejected :
    (findSliceByNameBytes currentAarch64ExtractedSlices goldMulArmName).map
        (fun sl => (checkArm64ThreeWayNI sl.code (mkContract "qsag_asm_goldilocks_mul_ct_aarch64" []),
          checkArm64ThreeWayNI (patchBytesAt sl.code 24 [0x42, 0x00, 0x00, 0x54])
            (mkContract "qsag_asm_goldilocks_mul_ct_aarch64" [])))
      = some (true, false) := by
  decide +kernel


/-! ## §12. Straight-line and loop kernels of the compiled archives, with explicit instruction budgets -/

def current_ctEq32X86Prog : List (DecodedInstr X86Instr) := [
  ⟨0, 3, .loadGpr 8 true 0 (.baseDisp 7 0)⟩,
  ⟨3, 3, .aluLoad64 .xorOp 0 (.baseDisp 6 0)⟩,
  ⟨6, 4, .loadGpr 8 true 1 (.baseDisp 7 8)⟩,
  ⟨10, 4, .aluLoad64 .xorOp 1 (.baseDisp 6 8)⟩,
  ⟨14, 4, .loadGpr 8 true 2 (.baseDisp 7 16)⟩,
  ⟨18, 4, .aluLoad64 .xorOp 2 (.baseDisp 6 16)⟩,
  ⟨22, 4, .loadGpr 8 true 8 (.baseDisp 7 24)⟩,
  ⟨26, 4, .aluLoad64 .xorOp 8 (.baseDisp 6 24)⟩,
  ⟨30, 3, .aluRegReg .orOp true 0 1⟩,
  ⟨33, 3, .aluRegReg .orOp true 2 8⟩,
  ⟨36, 3, .aluRegReg .orOp true 0 2⟩,
  ⟨39, 3, .movRegReg true 1 0⟩,
  ⟨42, 3, .negReg true 1⟩,
  ⟨45, 3, .aluRegReg .orOp true 0 1⟩,
  ⟨48, 4, .shiftImm .shr true 0 63⟩,
  ⟨52, 3, .aluImm .xorOp false 0 1⟩,
  ⟨55, 2, .aluRegReg .xorOp false 1 1⟩,
  ⟨57, 2, .aluRegReg .xorOp false 2 2⟩,
  ⟨59, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨62, 2, .aluRegReg .xorOp false 7 7⟩,
  ⟨64, 2, .aluRegReg .xorOp false 6 6⟩,
  ⟨66, 2, .aluRegReg .xorOp false 2 2⟩,
  ⟨68, 2, .aluRegReg .xorOp false 1 1⟩,
  ⟨70, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨73, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨76, 3, .aluRegReg .xorOp false 10 10⟩,
  ⟨79, 3, .aluRegReg .xorOp false 11 11⟩,
  ⟨82, 1, .ret⟩]

theorem current_ctEq32X86_decodes :
    (findSliceByNameBytes currentX86ExtractedSlices ctEq32X86Name).bind (fun sl => decodeX86Stream sl.code)
      = some current_ctEq32X86Prog := by
  decide +kernel

theorem current_ctEq32X86_run (k : Nat) (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    (runX86 current_ctEq32X86Prog (k + 28)
      ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨82, ⟨maskGprWidth false (((ctEq32WordX86 m r7 r6 ||| (0 - ctEq32WordX86 m r7 r6)) >>>
              UInt64.ofNat 63) ^^^ 1), 0, 0, r3, r4, r5, 0, 0, 0, 0, 0, 0, r12, r13, r14, r15⟩,
        y, false, false, true, dy, true, m⟩ := by
  iterate 28
    refine Eq.trans (runX86_step_fst _ _ _ _ rfl rfl) ?_
    simp only [stepX86_load64, stepX86_xorLoad64, stepX86_orRR, stepX86_movRR, stepX86_neg, stepX86_shr64,
      stepX86_xorImm, stepX86_xorRR, stepX86_ret, maskGprWidth_true, mask32_xor_self, u64_zero_beq_zero,
      b16get_0, b16get_1, b16get_2, b16get_6, b16get_7, b16get_8,
      b16set_6, b16set_7, b16set_0, b16set_1, b16set_2, b16set_8]
  refine Eq.trans (runX86_halted_fst _ _ _ rfl) ?_
  rfl

theorem current_ct_eq_32_x86_64_mc_refines :
    ∃ slice prog, findSliceByNameBytes currentX86ExtractedSlices ctEq32X86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 28 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        (runX86 prog fuel s).1.gpr.get 0 =
          (if ∀ i : Nat, i < 32 →
              s.mem (s.gpr.get 7 + UInt64.ofNat i) = s.mem (s.gpr.get 6 + UInt64.ofNat i)
            then 1 else 0) ∧
        (runX86 prog fuel s).1.mem = s.mem ∧
        (runX86 prog fuel s).1.gpr.get 1 = 0 ∧ (runX86 prog fuel s).1.gpr.get 2 = 0 ∧
        (runX86 prog fuel s).1.gpr.get 8 = 0 := by
  obtain ⟨sl, hf, hd⟩ := slice_decode_x86 current_ctEq32X86_decodes
  refine ⟨sl, current_ctEq32X86Prog, hf, hd, ?_⟩
  intro s fuel hpc hh hfuel
  obtain ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
    y, cf, o, zf, dy, hlt, m⟩ := s
  have hpc' : pc = 0 := hpc
  have hh' : hlt = false := hh
  subst hpc' hh'
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hfuel
  rw [Nat.add_comm 28 k, current_ctEq32X86_run]
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
  show maskGprWidth false (((ctEq32WordX86 m r7 r6 ||| (0 - ctEq32WordX86 m r7 r6)) >>>
      UInt64.ofNat 63) ^^^ 1) =
    if ∀ i : Nat, i < 32 → m (r7 + UInt64.ofNat i) = m (r6 + UInt64.ofNat i) then 1 else 0
  have hiff : ctEq32WordX86 m r7 r6 = 0 ↔
      ∀ i : Nat, i < 32 → m (r7 + UInt64.ofNat i) = m (r6 + UInt64.ofNat i) :=
    xorOr4_eq_zero_iff m r7 r6 _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl rfl
  rw [zeroTest64_masked]
  if hW : ctEq32WordX86 m r7 r6 = 0 then
    rw [ite_eq_left hW, ite_eq_left (hiff.mp hW)]
  else
    rw [ite_eq_right hW, ite_eq_right (fun h => hW (hiff.mpr h))]

def current_goldAddX86Prog : List (DecodedInstr X86Instr) := [
  ⟨0, 3, .movRegReg true 0 7⟩,
  ⟨3, 3, .aluRegReg .add true 0 6⟩,
  ⟨6, 3, .aluRegReg .sbb false 8 8⟩,
  ⟨9, 3, .aluRegReg .add true 0 8⟩,
  ⟨12, 3, .aluRegReg .sbb false 10 10⟩,
  ⟨15, 3, .aluRegReg .add true 0 10⟩,
  ⟨18, 6, .movImm false 9 4294967295⟩,
  ⟨24, 3, .movRegReg true 8 0⟩,
  ⟨27, 3, .aluRegReg .add true 8 9⟩,
  ⟨30, 3, .aluRegReg .sbb true 1 1⟩,
  ⟨33, 3, .aluRegReg .andOp true 1 9⟩,
  ⟨36, 3, .aluRegReg .add true 0 1⟩,
  ⟨39, 2, .aluRegReg .xorOp false 1 1⟩,
  ⟨41, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨44, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨47, 3, .aluRegReg .xorOp false 10 10⟩,
  ⟨50, 2, .aluRegReg .xorOp false 7 7⟩,
  ⟨52, 2, .aluRegReg .xorOp false 6 6⟩,
  ⟨54, 2, .aluRegReg .xorOp false 2 2⟩,
  ⟨56, 2, .aluRegReg .xorOp false 1 1⟩,
  ⟨58, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨61, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨64, 3, .aluRegReg .xorOp false 10 10⟩,
  ⟨67, 3, .aluRegReg .xorOp false 11 11⟩,
  ⟨70, 1, .ret⟩]

theorem current_goldAddX86_decodes :
    (findSliceByNameBytes currentX86ExtractedSlices goldAddX86Name).bind
      (fun sl => decodeX86Stream sl.code) = some current_goldAddX86Prog := by
  decide +kernel

theorem current_goldAddX86_run (k : Nat) (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    (runX86 current_goldAddX86Prog (k + 25)
      ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨70, ⟨goldAddMc r7 r6, 0, 0, r3, r4, r5, 0, 0, 0, 0, 0, 0, r12, r13, r14, r15⟩,
        y, false, false, true, dy, true, m⟩ := by
  iterate 25
    refine Eq.trans (runX86_step_fst _ _ _ _ rfl rfl) ?_
    simp only [stepX86_movRR, stepX86_addRR64, stepX86_sbbRR, stepX86_andRR, stepX86_movImm,
      stepX86_xorRR, stepX86_ret, maskGprWidth_true, mask32_xor_self, u64_zero_beq_zero,
      sbb32_self, sbb64_self, uint64_evalAdd_eq,
      b16get_0, b16get_1, b16get_6, b16get_7, b16get_8, b16get_9, b16get_10,
      b16set_2, b16set_6, b16set_7, b16set_11, b16get_2, b16get_11, b16set_0, b16set_1, b16set_8, b16set_9, b16set_10]
  exact runX86_halted_fst _ _ _ rfl

theorem current_goldilocks_add_ct_x86_64_mc_refines :
    ∃ slice prog, findSliceByNameBytes currentX86ExtractedSlices goldAddX86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 25 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        ((runX86 prog fuel s).1.gpr.get 0).toNat =
          ((s.gpr.get 7).toNat + (s.gpr.get 6).toNat) % goldilocksPrime ∧
        (runX86 prog fuel s).1.mem = s.mem ∧
        (runX86 prog fuel s).1.gpr.get 1 = 0 ∧ (runX86 prog fuel s).1.gpr.get 8 = 0 ∧
        (runX86 prog fuel s).1.gpr.get 9 = 0 ∧ (runX86 prog fuel s).1.gpr.get 10 = 0 := by
  obtain ⟨sl, hf, hd⟩ := slice_decode_x86 current_goldAddX86_decodes
  refine ⟨sl, current_goldAddX86Prog, hf, hd, ?_⟩
  intro s fuel hpc hh hfuel
  obtain ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
    y, cf, o, zf, dy, hlt, m⟩ := s
  have hpc' : pc = 0 := hpc
  have hh' : hlt = false := hh
  subst hpc' hh'
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hfuel
  rw [Nat.add_comm 25 k, current_goldAddX86_run]
  exact ⟨rfl, goldAddMc_toNat r7 r6, rfl, rfl, rfl, rfl, rfl⟩

def current_goldSubX86Prog : List (DecodedInstr X86Instr) := [
  ⟨0, 6, .movImm false 9 4294967295⟩,
  ⟨6, 3, .movRegReg true 0 7⟩,
  ⟨9, 3, .movRegReg true 8 0⟩,
  ⟨12, 3, .aluRegReg .add true 8 9⟩,
  ⟨15, 3, .aluRegReg .sbb true 1 1⟩,
  ⟨18, 3, .aluRegReg .andOp true 1 9⟩,
  ⟨21, 3, .aluRegReg .add true 0 1⟩,
  ⟨24, 3, .movRegReg true 8 6⟩,
  ⟨27, 3, .aluRegReg .add true 8 9⟩,
  ⟨30, 3, .aluRegReg .sbb true 1 1⟩,
  ⟨33, 3, .aluRegReg .andOp true 1 9⟩,
  ⟨36, 3, .aluRegReg .add true 6 1⟩,
  ⟨39, 3, .aluRegReg .sub true 0 6⟩,
  ⟨42, 3, .aluRegReg .sbb true 8 8⟩,
  ⟨45, 10, .movImm true 10 18446744069414584321⟩,
  ⟨55, 3, .aluRegReg .andOp true 8 10⟩,
  ⟨58, 3, .aluRegReg .add true 0 8⟩,
  ⟨61, 2, .aluRegReg .xorOp false 1 1⟩,
  ⟨63, 2, .aluRegReg .xorOp false 6 6⟩,
  ⟨65, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨68, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨71, 3, .aluRegReg .xorOp false 10 10⟩,
  ⟨74, 2, .aluRegReg .xorOp false 7 7⟩,
  ⟨76, 2, .aluRegReg .xorOp false 6 6⟩,
  ⟨78, 2, .aluRegReg .xorOp false 2 2⟩,
  ⟨80, 2, .aluRegReg .xorOp false 1 1⟩,
  ⟨82, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨85, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨88, 3, .aluRegReg .xorOp false 10 10⟩,
  ⟨91, 3, .aluRegReg .xorOp false 11 11⟩,
  ⟨94, 1, .ret⟩]

theorem current_goldSubX86_decodes :
    (findSliceByNameBytes currentX86ExtractedSlices goldSubX86Name).bind
      (fun sl => decodeX86Stream sl.code) = some current_goldSubX86Prog := by
  decide +kernel

theorem current_goldSubX86_run (k : Nat) (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    (runX86 current_goldSubX86Prog (k + 31)
      ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨94, ⟨goldSubMc r7 r6, 0, 0, r3, r4, r5, 0, 0, 0, 0, 0, 0, r12, r13, r14, r15⟩,
        y, false, false, true, dy, true, m⟩ := by
  iterate 31
    refine Eq.trans (runX86_step_fst _ _ _ _ rfl rfl) ?_
    simp only [stepX86_movRR, stepX86_addRR64, stepX86_subRR64, stepX86_sbbRR, stepX86_andRR,
      stepX86_movImm, stepX86_xorRR, stepX86_ret, maskGprWidth_true, mask32_xor_self,
      u64_zero_beq_zero, sbb64_self, uint64_evalAdd_eq, uint64_evalSub_eq,
      b16get_0, b16get_1, b16get_6, b16get_7, b16get_8, b16get_9, b16get_10,
      b16set_2, b16set_7, b16set_11, b16get_2, b16get_11, b16set_0, b16set_1, b16set_6, b16set_8, b16set_9, b16set_10]
  exact runX86_halted_fst _ _ _ rfl

theorem current_goldilocks_sub_ct_x86_64_mc_refines :
    ∃ slice prog, findSliceByNameBytes currentX86ExtractedSlices goldSubX86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 31 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        ((runX86 prog fuel s).1.gpr.get 0).toNat =
          ((s.gpr.get 7).toNat + goldilocksPrime - (s.gpr.get 6).toNat % goldilocksPrime) %
            goldilocksPrime ∧
        (runX86 prog fuel s).1.mem = s.mem ∧
        (runX86 prog fuel s).1.gpr.get 1 = 0 ∧ (runX86 prog fuel s).1.gpr.get 6 = 0 ∧
        (runX86 prog fuel s).1.gpr.get 8 = 0 ∧ (runX86 prog fuel s).1.gpr.get 9 = 0 ∧
        (runX86 prog fuel s).1.gpr.get 10 = 0 := by
  obtain ⟨sl, hf, hd⟩ := slice_decode_x86 current_goldSubX86_decodes
  refine ⟨sl, current_goldSubX86Prog, hf, hd, ?_⟩
  intro s fuel hpc hh hfuel
  obtain ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
    y, cf, o, zf, dy, hlt, m⟩ := s
  have hpc' : pc = 0 := hpc
  have hh' : hlt = false := hh
  subst hpc' hh'
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hfuel
  rw [Nat.add_comm 31 k, current_goldSubX86_run]
  exact ⟨rfl, goldSubMc_toNat r7 r6, rfl, rfl, rfl, rfl, rfl, rfl⟩

def current_goldMulX86Prog : List (DecodedInstr X86Instr) := [
  ⟨0, 3, .movRegReg true 2 7⟩,
  ⟨3, 5, .mulx 1 0 6⟩,
  ⟨8, 3, .movRegReg true 2 1⟩,
  ⟨11, 4, .shiftImm .shr true 1 32⟩,
  ⟨15, 2, .movRegReg false 2 2⟩,
  ⟨17, 3, .aluRegReg .sub true 0 1⟩,
  ⟨20, 3, .aluRegReg .sbb false 8 8⟩,
  ⟨23, 3, .aluRegReg .sub true 0 8⟩,
  ⟨26, 3, .movRegReg true 9 2⟩,
  ⟨29, 4, .shiftImm .shl true 9 32⟩,
  ⟨33, 3, .aluRegReg .sub true 9 2⟩,
  ⟨36, 3, .aluRegReg .add true 0 9⟩,
  ⟨39, 3, .aluRegReg .sbb false 8 8⟩,
  ⟨42, 3, .aluRegReg .add true 0 8⟩,
  ⟨45, 6, .movImm false 9 4294967295⟩,
  ⟨51, 3, .movRegReg true 8 0⟩,
  ⟨54, 3, .aluRegReg .add true 8 9⟩,
  ⟨57, 3, .aluRegReg .sbb true 1 1⟩,
  ⟨60, 3, .aluRegReg .andOp true 1 9⟩,
  ⟨63, 3, .aluRegReg .add true 0 1⟩,
  ⟨66, 2, .aluRegReg .xorOp false 1 1⟩,
  ⟨68, 2, .aluRegReg .xorOp false 2 2⟩,
  ⟨70, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨73, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨76, 2, .aluRegReg .xorOp false 7 7⟩,
  ⟨78, 2, .aluRegReg .xorOp false 6 6⟩,
  ⟨80, 2, .aluRegReg .xorOp false 2 2⟩,
  ⟨82, 2, .aluRegReg .xorOp false 1 1⟩,
  ⟨84, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨87, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨90, 3, .aluRegReg .xorOp false 10 10⟩,
  ⟨93, 3, .aluRegReg .xorOp false 11 11⟩,
  ⟨96, 1, .ret⟩]

theorem current_goldMulX86_decodes :
    (findSliceByNameBytes currentX86ExtractedSlices goldMulX86Name).bind
      (fun sl => decodeX86Stream sl.code) = some current_goldMulX86Prog := by
  decide +kernel

theorem current_goldMulX86_run (k : Nat) (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    (runX86 current_goldMulX86Prog (k + 33)
      ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨96, ⟨goldMulMc r7 r6, 0, 0, r3, r4, r5, 0, 0, 0, 0, 0, 0, r12, r13, r14, r15⟩,
        y, false, false, true, dy, true, m⟩ := by
  iterate 33
    refine Eq.trans (runX86_step_fst _ _ _ _ rfl rfl) ?_
    simp only [stepX86_movRR, stepX86_mulx, stepX86_shr64, stepX86_shl64, stepX86_addRR64,
      stepX86_subRR64, stepX86_sbbRR, stepX86_andRR, stepX86_movImm, stepX86_xorRR, stepX86_ret,
      maskGprWidth_true, mask32_xor_self, u64_zero_beq_zero, sbb32_self, sbb64_self,
      uint64_evalAdd_eq, uint64_evalSub_eq,
      b16get_0, b16get_1, b16get_2, b16get_6, b16get_7, b16get_8, b16get_9,
      b16set_6, b16set_7, b16set_10, b16set_11, b16get_10, b16get_11, b16set_0, b16set_1, b16set_2, b16set_8, b16set_9]
  exact runX86_halted_fst _ _ _ rfl

theorem current_goldilocks_mul_ct_x86_64_mc_refines :
    ∃ slice prog, findSliceByNameBytes currentX86ExtractedSlices goldMulX86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 33 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        ((runX86 prog fuel s).1.gpr.get 0).toNat =
          ((s.gpr.get 7).toNat * (s.gpr.get 6).toNat) % goldilocksPrime ∧
        (runX86 prog fuel s).1.mem = s.mem ∧
        (runX86 prog fuel s).1.gpr.get 1 = 0 ∧ (runX86 prog fuel s).1.gpr.get 2 = 0 ∧
        (runX86 prog fuel s).1.gpr.get 8 = 0 ∧ (runX86 prog fuel s).1.gpr.get 9 = 0 := by
  obtain ⟨sl, hf, hd⟩ := slice_decode_x86 current_goldMulX86_decodes
  refine ⟨sl, current_goldMulX86Prog, hf, hd, ?_⟩
  intro s fuel hpc hh hfuel
  obtain ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
    y, cf, o, zf, dy, hlt, m⟩ := s
  have hpc' : pc = 0 := hpc
  have hh' : hlt = false := hh
  subst hpc' hh'
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hfuel
  rw [Nat.add_comm 33 k, current_goldMulX86_run]
  exact ⟨rfl, goldMulMc_toNat r7 r6, rfl, rfl, rfl, rfl, rfl⟩

def current_goldMulArmProg : List (DecodedInstr Arm64Instr) := [
  ⟨0, 4, .mulOp false 2 0 1⟩,
  ⟨4, 4, .mulOp true 3 0 1⟩,
  ⟨8, 4, .ubfm true 4 3 32 63⟩,
  ⟨12, 4, .aluImm .andOp true 5 3 4294967295⟩,
  ⟨16, 4, .movWide true false 6 0 0⟩,
  ⟨20, 4, .aluReg .subs true 2 2 4 0 0⟩,
  ⟨24, 4, .aluReg .sbc true 7 31 31 0 0⟩,
  ⟨28, 4, .aluReg .andOp true 7 7 6 0 0⟩,
  ⟨32, 4, .aluReg .sub true 2 2 7 0 0⟩,
  ⟨36, 4, .ubfm true 8 5 32 31⟩,
  ⟨40, 4, .aluReg .sub true 8 8 5 0 0⟩,
  ⟨44, 4, .aluReg .adds true 2 2 8 0 0⟩,
  ⟨48, 4, .aluReg .adc true 7 31 31 0 0⟩,
  ⟨52, 4, .aluReg .sub true 7 31 7 0 0⟩,
  ⟨56, 4, .aluReg .andOp true 7 7 6 0 0⟩,
  ⟨60, 4, .aluReg .add true 2 2 7 0 0⟩,
  ⟨64, 4, .aluReg .adds true 8 2 6 0 0⟩,
  ⟨68, 4, .aluReg .adc true 7 31 31 0 0⟩,
  ⟨72, 4, .aluReg .sub true 7 31 7 0 0⟩,
  ⟨76, 4, .aluReg .andOp true 7 7 6 0 0⟩,
  ⟨80, 4, .aluReg .add true 0 2 7 0 0⟩,
  ⟨84, 4, .movWide false true 1 0 0⟩,
  ⟨88, 4, .movWide false true 2 0 0⟩,
  ⟨92, 4, .movWide false true 3 0 0⟩,
  ⟨96, 4, .movWide false true 4 0 0⟩,
  ⟨100, 4, .movWide false true 5 0 0⟩,
  ⟨104, 4, .movWide false true 6 0 0⟩,
  ⟨108, 4, .movWide false true 7 0 0⟩,
  ⟨112, 4, .movWide false true 8 0 0⟩,
  ⟨116, 4, .ret⟩]

theorem current_goldMulArm_decodes :
    (findSliceByNameBytes currentAarch64ExtractedSlices goldMulArmName).bind
      (fun sl => decodeArm64Stream sl.code) = some current_goldMulArmProg := by
  decide +kernel

theorem current_goldMulArm_run (k : Nat) (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (hi : Bank16 UInt64) (v : Bank32 Vec128) (cf zf dit : Bool) (m : UInt64 → UInt8) :
    (runArm64 current_goldMulArmProg (k + 30)
      ⟨0, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        v, cf, zf, dit, false, m⟩).1 =
      ⟨116, ⟨⟨armCanon (goldMulArmPre r0 r1), 0, 0, 0, 0, 0, 0, 0, 0, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        v, decide ((goldMulArmPre r0 r1).toNat + (0xFFFFFFFF : UInt64).toNat ≥ 0x10000000000000000),
        goldMulArmPre r0 r1 + 0xFFFFFFFF == 0, dit, true, m⟩ := by
  iterate 30
    refine Eq.trans (runArm64_step_fst _ _ _ _ rfl rfl) ?_
    simp only [stepArm64_mul, stepArm64_umulh, stepArm64_lsr64, stepArm64_lsl32, stepArm64_andImm,
      stepArm64_andRR, stepArm64_movn32, stepArm64_addRR, stepArm64_addsRR, stepArm64_subsRR,
      stepArm64_subRR, stepArm64_adcRR, stepArm64_sbcRR, stepArm64_movz, stepArm64_ret,
      u64_shl_zero_zero, uint64_evalSub_eq, uint64_evalAdd_eq, armAdcZero, armSbcZero, u64_neg_cond,
      movn32_zero, condAll_and_eps, condNone_and_eps,
      armGet_31, armGet_0, armGet_1, armGet_2, armGet_3, armGet_4, armGet_5, armGet_6, armGet_7, armGet_8,
      armSet_1, armSet_0, armSet_2, armSet_3, armSet_4, armSet_5, armSet_6, armSet_7, armSet_8]
  exact runArm64_halted_fst _ _ _ rfl

theorem current_goldilocks_mul_ct_aarch64_mc_refines :
    ∃ slice prog, findSliceByNameBytes currentAarch64ExtractedSlices goldMulArmName = some slice ∧
      decodeArm64Stream slice.code = some prog ∧
      ∀ (s : Arm64State) (fuel : Nat), s.pc = 0 → s.halted = false → 30 ≤ fuel →
        (runArm64 prog fuel s).1.halted = true ∧
        ((runArm64 prog fuel s).1.gpr.get 0).toNat =
          ((s.gpr.get 0).toNat * (s.gpr.get 1).toNat) % goldilocksPrime ∧
        (runArm64 prog fuel s).1.mem = s.mem ∧
        (∀ r : Nat, 2 ≤ r → r ≤ 8 → (runArm64 prog fuel s).1.gpr.get r = 0) := by
  obtain ⟨sl, hf, hd⟩ := slice_decode_arm64 current_goldMulArm_decodes
  refine ⟨sl, current_goldMulArmProg, hf, hd, ?_⟩
  intro s fuel hpc hh hfuel
  obtain ⟨pc, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
    v, cf, zf, dit, hlt, m⟩ := s
  have hpc' : pc = 0 := hpc
  have hh' : hlt = false := hh
  subst hpc' hh'
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hfuel
  rw [Nat.add_comm 30 k, current_goldMulArm_run]
  refine ⟨rfl, goldMulArm_toNat r0 r1, rfl, ?_⟩
  intro r h2 h8
  match r, h2, h8 with
  | 2, _, _ => rfl
  | 3, _, _ => rfl
  | 4, _, _ => rfl
  | 5, _, _ => rfl
  | 6, _, _ => rfl
  | 7, _, _ => rfl
  | 8, _, _ => rfl
  | 0, h, _ => exact absurd h (by decide)
  | 1, h, _ => exact absurd h (by decide)
  | n + 9, _, h => exact absurd h (by omega)

/-- The 28-step budget of `current_ct_eq_32_x86_64_mc_refines` is not slack: after 20 steps the
kernel has not reached `ret`. -/
theorem current_ct_eq_32_requires_new_budget :
    (runX86 current_ctEq32X86Prog 20 (x86Init 0 0 0 0 0)).1.halted = false := by
  decide +kernel

theorem current_ctMemzeroArm_decodes :
    (findSliceByNameBytes currentAarch64ExtractedSlices ctMemzeroArmName).bind
      (fun sl => decodeArm64Stream sl.code) = some ctMemzeroArmProg := by
  decide +kernel


theorem current_ct_memzero_aarch64_mc_refines :
    ∃ slice prog, findSliceByNameBytes currentAarch64ExtractedSlices ctMemzeroArmName = some slice ∧
      decodeArm64Stream slice.code = some prog ∧
      ∀ (s : Arm64State) (fuel : Nat), s.pc = 0 → s.halted = false → 0 < (s.gpr.get 1).toNat →
        3 * (s.gpr.get 1).toNat + 2 ≤ fuel →
        (runArm64 prog fuel s).1.halted = true ∧
        (∀ i : Nat, i < (s.gpr.get 1).toNat →
          (runArm64 prog fuel s).1.mem (s.gpr.get 0 + UInt64.ofNat i) = 0) ∧
        (∀ a : UInt64, (∀ i : Nat, i < (s.gpr.get 1).toNat → a ≠ s.gpr.get 0 + UInt64.ofNat i) →
          (runArm64 prog fuel s).1.mem a = s.mem a) := by
  obtain ⟨sl, hf, hd⟩ := slice_decode_arm64 current_ctMemzeroArm_decodes
  refine ⟨sl, ctMemzeroArmProg, hf, hd, ?_⟩
  intro s fuel hpc hh hn hfuel
  obtain ⟨pc, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
    v, cf, zf, dit, hlt, m⟩ := s
  have hpc' : pc = 0 := hpc
  have hh' : hlt = false := hh
  subst hpc' hh'
  have hn' : 0 < r1.toNat := hn
  have hfuel' : 3 * r1.toNat + 2 ≤ fuel := hfuel
  obtain ⟨k, hk⟩ : ∃ k, r1.toNat = k + 1 := ⟨r1.toNat - 1, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, fuel = 3 * (k + 1) + 2 + j := ⟨fuel - (3 * (k + 1) + 2), by omega⟩
  subst hj
  rw [ctMemzeroArm_run m k j hk]
  refine ⟨rfl, ?_, ?_⟩
  · intro i hi
    have hi' : i < r1.toNat := hi
    exact zeroRange_inside (k + 1) m r0 i (by omega)
  · intro a ha
    have ha' : ∀ i : Nat, i < r1.toNat → a ≠ r0 + UInt64.ofNat i := ha
    exact zeroRange_outside (k + 1) m r0 a (fun i hi => ha' i (by omega))


def ctCurrentMemzeroX86Prog : List (DecodedInstr X86Instr) := [
  ⟨0, 3, .movRegReg true 1 6⟩,
  ⟨3, 2, .aluRegReg .xorOp false 0 0⟩,
  ⟨5, 2, .storeGpr 1 0 (.baseDisp 7 0)⟩,
  ⟨7, 3, .incDec true true 7⟩,
  ⟨10, 3, .incDec false true 1⟩,
  ⟨13, 2, .jcc 5 5⟩,
  ⟨15, 3, .mfence⟩,
  ⟨18, 2, .aluRegReg .xorOp false 7 7⟩,
  ⟨20, 2, .aluRegReg .xorOp false 6 6⟩,
  ⟨22, 2, .aluRegReg .xorOp false 2 2⟩,
  ⟨24, 2, .aluRegReg .xorOp false 1 1⟩,
  ⟨26, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨29, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨32, 3, .aluRegReg .xorOp false 10 10⟩,
  ⟨35, 3, .aluRegReg .xorOp false 11 11⟩,
  ⟨38, 2, .aluRegReg .xorOp false 0 0⟩,
  ⟨40, 1, .ret⟩]

theorem ctCurrentMemzeroX86_decodes :
    (findSliceByNameBytes currentX86ExtractedSlices ctMemzeroX86Name).bind
      (fun sl => decodeX86Stream sl.code) = some ctCurrentMemzeroX86Prog := by
  decide +kernel

section CurrentMemzeroX86
variable {r2 r3 r4 r5 r6 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64} {y : Bank16 Vec256} {cf dy : Bool}

/-- One trip round the store loop (four instructions). -/
theorem ctCurrentMemzeroX86_body (c p : UInt64) (o zf : Bool) (m : UInt64 → UInt8) (fuel : Nat) :
    (runX86 ctCurrentMemzeroX86Prog (fuel + 4)
      ⟨5, ⟨0, c, r2, r3, r4, r5, r6, p, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, m⟩).1 =
    (runX86 ctCurrentMemzeroX86Prog fuel
      ⟨jccPc (!(c - 1 == 0)) 5 15, ⟨0, c - 1, r2, r3, r4, r5, r6, p + 1, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        y, cf, evalX86IncDecOf false true c, c - 1 == 0, dy, false, writeMem8 m p 0⟩).1 := by
  iterate 4
    refine Eq.trans (runX86_step_fst _ _ _ _ rfl rfl) ?_
    simp only [stepX86_store8, stepX86_inc, stepX86_dec, stepX86_jnz, maskGprWidth_true,
      u64_add_neg_one, u64_zero_toUInt8, UInt64.add_zero, b16get_0, b16get_1, b16get_7, b16set_1, b16set_7]

/-- The whole loop, by induction on the remaining count. -/
theorem ctCurrentMemzeroX86_loop (k : Nat) : ∀ (c p : UInt64) (o zf : Bool) (m : UInt64 → UInt8) (fuel : Nat),
    c.toNat = k + 1 →
    (runX86 ctCurrentMemzeroX86Prog (4 * (k + 1) + fuel)
      ⟨5, ⟨0, c, r2, r3, r4, r5, r6, p, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, m⟩).1 =
    (runX86 ctCurrentMemzeroX86Prog fuel
      ⟨15, ⟨0, 0, r2, r3, r4, r5, r6, p + UInt64.ofNat (k + 1), r8, r9, r10, r11, r12, r13, r14, r15⟩,
        y, cf, false, true, dy, false, zeroRange (k + 1) m p⟩).1 := by
  induction k with
  | zero =>
    intro c p o zf m fuel hc
    have hc1 : c = 1 := u64_eq_of_toNat hc
    subst hc1
    rw [show 4 * (0 + 1) + fuel = fuel + 4 from by omega, ctCurrentMemzeroX86_body, u64_one_sub_one,
      u64_zero_beq_zero]
    try rfl
  | succ k ih =>
    intro c p o zf m fuel hc
    have hc' := u64_pred_toNat c k hc
    have hne := u64_ne_zero_of_toNat_succ (c - 1) k hc'
    rw [show 4 * (k + 1 + 1) + fuel = (4 * (k + 1) + fuel) + 4 from by omega, ctCurrentMemzeroX86_body,
      beq_false_of_ne hne, show jccPc (!false) 5 15 = 5 from rfl,
      ih (c - 1) (p + 1) (evalX86IncDecOf false true c) false (writeMem8 m p 0) fuel hc', addr_succ]
    try rfl

theorem ctCurrentMemzeroX86_run {r0 r1 r7 : UInt64} {o zf : Bool} (m : UInt64 → UInt8) (k j : Nat)
    (hn : r6.toNat = k + 1) :
    (runX86 ctCurrentMemzeroX86Prog (4 * (k + 1) + 13 + j)
      ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨40, ⟨0, 0, 0, r3, r4, r5, 0, 0, 0, 0, 0, 0, r12, r13, r14, r15⟩,
        y, false, false, true, dy, true, zeroRange (k + 1) m r7⟩ := by
  rw [show 4 * (k + 1) + 13 + j = (4 * (k + 1) + (j + 11)) + 2 from by omega]
  iterate 2
    refine Eq.trans (runX86_step_fst _ _ _ _ rfl rfl) ?_
    simp only [stepX86_movRR, stepX86_xorRR, maskGprWidth_true, mask32_xor_self, u64_zero_beq_zero,
      b16get_0, b16get_6, b16set_0, b16set_1]
  rw [ctCurrentMemzeroX86_loop k r6 r7 false true m (j + 11) hn]
  iterate 11
    refine Eq.trans (runX86_step_fst _ _ _ _ rfl rfl) ?_
    simp only [stepX86_mfence, stepX86_ret, stepX86_xorRR, mask32_xor_self, u64_zero_beq_zero, b16set_0, b16set_1, b16set_2, b16set_6, b16set_7, b16set_8, b16set_9, b16set_10, b16set_11]
  exact runX86_halted_fst _ _ _ rfl

end CurrentMemzeroX86

/-- **Machine-code refinement of `qsag_asm_ct_memzero_x86_64`.** For a length `n = rsi ≥ 1` (the
Rust wrapper returns early on empty buffers; the loop is bottom-tested), at most `4 n + 13` steps
halt with the `n` bytes at `rdi, rdi + 1, …` (wrapping) zero and every other byte unchanged. -/
theorem current_ct_memzero_x86_64_mc_refines :
    ∃ slice prog, findSliceByNameBytes currentX86ExtractedSlices ctMemzeroX86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 0 < (s.gpr.get 6).toNat →
        4 * (s.gpr.get 6).toNat + 13 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        (∀ i : Nat, i < (s.gpr.get 6).toNat →
          (runX86 prog fuel s).1.mem (s.gpr.get 7 + UInt64.ofNat i) = 0) ∧
        (∀ a : UInt64, (∀ i : Nat, i < (s.gpr.get 6).toNat → a ≠ s.gpr.get 7 + UInt64.ofNat i) →
          (runX86 prog fuel s).1.mem a = s.mem a) := by
  obtain ⟨sl, hf, hd⟩ := slice_decode_x86 ctCurrentMemzeroX86_decodes
  refine ⟨sl, ctCurrentMemzeroX86Prog, hf, hd, ?_⟩
  intro s fuel hpc hh hn hfuel
  obtain ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
    y, cf, o, zf, dy, hlt, m⟩ := s
  have hpc' : pc = 0 := hpc
  have hh' : hlt = false := hh
  subst hpc' hh'
  have hn' : 0 < r6.toNat := hn
  have hfuel' : 4 * r6.toNat + 13 ≤ fuel := hfuel
  obtain ⟨k, hk⟩ : ∃ k, r6.toNat = k + 1 := ⟨r6.toNat - 1, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, fuel = 4 * (k + 1) + 13 + j := ⟨fuel - (4 * (k + 1) + 13), by omega⟩
  subst hj
  rw [ctCurrentMemzeroX86_run m k j hk]
  refine ⟨rfl, ?_, ?_⟩
  · intro i hi
    have hi' : i < r6.toNat := hi
    exact zeroRange_inside (k + 1) m r7 i (by omega)
  · intro a ha
    have ha' : ∀ i : Nat, i < r6.toNat → a ≠ r7 + UInt64.ofNat i := ha
    exact zeroRange_outside (k + 1) m r7 a (fun i hi => ha' i (by omega))

def ctCurrentEqBytesX86Prog : List (DecodedInstr X86Instr) := [
  ⟨0, 2, .aluRegReg .xorOp false 0 0⟩,
  ⟨2, 3, .movRegReg true 1 2⟩,
  ⟨5, 4, .loadGpr 1 false 8 (.baseDisp 7 0)⟩,
  ⟨9, 4, .loadGpr 1 false 9 (.baseDisp 6 0)⟩,
  ⟨13, 3, .aluRegReg .xorOp false 8 9⟩,
  ⟨16, 3, .aluRegReg .orOp false 0 8⟩,
  ⟨19, 3, .incDec true true 7⟩,
  ⟨22, 3, .incDec true true 6⟩,
  ⟨25, 3, .incDec false true 1⟩,
  ⟨28, 2, .jcc 5 5⟩,
  ⟨30, 3, .aluImm .sub false 0 1⟩,
  ⟨33, 3, .shiftImm .shr false 0 31⟩,
  ⟨36, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨39, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨42, 2, .aluRegReg .xorOp false 7 7⟩,
  ⟨44, 2, .aluRegReg .xorOp false 6 6⟩,
  ⟨46, 2, .aluRegReg .xorOp false 2 2⟩,
  ⟨48, 2, .aluRegReg .xorOp false 1 1⟩,
  ⟨50, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨53, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨56, 3, .aluRegReg .xorOp false 10 10⟩,
  ⟨59, 3, .aluRegReg .xorOp false 11 11⟩,
  ⟨62, 1, .ret⟩]

theorem ctCurrentEqBytesX86_decodes :
    (findSliceByNameBytes currentX86ExtractedSlices ctEqBytesX86Name).bind
      (fun sl => decodeX86Stream sl.code) = some ctCurrentEqBytesX86Prog := by
  decide +kernel

section CurrentEqBytesX86
variable {r2 r3 r4 r5 r10 r11 r12 r13 r14 r15 : UInt64} {y : Bank16 Vec256} {dy : Bool}
  {m : UInt64 → UInt8}

/-- One trip round the compare loop (eight instructions). -/
theorem ctCurrentEqBytesX86_body (c p q acc x8 x9 : UInt64) (cf o zf : Bool) (fuel : Nat) :
    (runX86 ctCurrentEqBytesX86Prog (fuel + 8)
      ⟨5, ⟨acc, c, r2, r3, r4, r5, q, p, x8, x9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, m⟩).1 =
    (runX86 ctCurrentEqBytesX86Prog fuel
      ⟨jccPc (!(c - 1 == 0)) 5 30,
        ⟨maskGprWidth false (acc ||| byteDiff (m p) (m q)), c - 1, r2, r3, r4, r5, q + 1, p + 1,
          byteDiff (m p) (m q), maskGprWidth false (m q).toUInt64, r10, r11, r12, r13, r14, r15⟩,
        y, false, evalX86IncDecOf false true c, c - 1 == 0, dy, false, m⟩).1 := by
  iterate 8
    refine Eq.trans (runX86_step_fst _ _ _ _ rfl rfl) ?_
    simp only [stepX86_load8, stepX86_xorRR, stepX86_orRR, stepX86_inc, stepX86_dec, stepX86_jnz,
      maskGprWidth_true, u64_add_neg_one, UInt64.add_zero,
      b16get_0, b16get_1, b16get_6, b16get_7, b16get_8, b16get_9,
      b16set_0, b16set_1, b16set_6, b16set_7, b16set_8, b16set_9]
  try rfl

theorem ctCurrentEqBytesX86_loop (k : Nat) : ∀ (c p q acc x8 x9 : UInt64) (cf o zf : Bool) (fuel : Nat),
    c.toNat = k + 1 → ∃ x8' x9' : UInt64,
    (runX86 ctCurrentEqBytesX86Prog (8 * (k + 1) + fuel)
      ⟨5, ⟨acc, c, r2, r3, r4, r5, q, p, x8, x9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, m⟩).1 =
    (runX86 ctCurrentEqBytesX86Prog fuel
      ⟨30, ⟨eqAcc (k + 1) m p q acc, 0, r2, r3, r4, r5, q + UInt64.ofNat (k + 1), p + UInt64.ofNat (k + 1),
          x8', x9', r10, r11, r12, r13, r14, r15⟩,
        y, false, false, true, dy, false, m⟩).1 := by
  induction k with
  | zero =>
    intro c p q acc x8 x9 cf o zf fuel hc
    have hc1 : c = 1 := u64_eq_of_toNat hc
    subst hc1
    refine ⟨byteDiff (m p) (m q), maskGprWidth false (m q).toUInt64, ?_⟩
    rw [show 8 * (0 + 1) + fuel = fuel + 8 from by omega, ctCurrentEqBytesX86_body, u64_one_sub_one,
      u64_zero_beq_zero]
    try rfl
  | succ k ih =>
    intro c p q acc x8 x9 cf o zf fuel hc
    have hc' := u64_pred_toNat c k hc
    have hne := u64_ne_zero_of_toNat_succ (c - 1) k hc'
    obtain ⟨x8', x9', h⟩ := ih (c - 1) (p + 1) (q + 1) (maskGprWidth false (acc ||| byteDiff (m p) (m q)))
      (byteDiff (m p) (m q)) (maskGprWidth false (m q).toUInt64) false (evalX86IncDecOf false true c) false fuel hc'
    refine ⟨x8', x9', ?_⟩
    rw [show 8 * (k + 1 + 1) + fuel = (8 * (k + 1) + fuel) + 8 from by omega, ctCurrentEqBytesX86_body,
      beq_false_of_ne hne, show jccPc (!false) 5 30 = 5 from rfl, h, addr_succ, addr_succ]
    try rfl

theorem ctCurrentEqBytesX86_run {r0 r1 r6 r7 r8 r9 : UInt64} {cf o zf : Bool} (k j : Nat)
    (hn : r2.toNat = k + 1) :
    (runX86 ctCurrentEqBytesX86Prog (8 * (k + 1) + 15 + j)
      ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨62, ⟨maskGprWidth false (maskGprWidth false (maskGprWidth false (UInt64.ofNat
            (((maskGprWidth false (eqAcc (k + 1) m r7 r6 0)).toNat + 0x100000000 -
              (maskGprWidth false 1).toNat) % 0x100000000))) >>> UInt64.ofNat (31 % 32)),
          0, 0, r3, r4, r5, 0, 0, 0, 0,
          0, 0, r12, r13, r14, r15⟩,
        y, false, false, true, dy, true, m⟩ := by
  rw [show 8 * (k + 1) + 15 + j = (8 * (k + 1) + (j + 13)) + 2 from by omega]
  iterate 2
    refine Eq.trans (runX86_step_fst _ _ _ _ rfl rfl) ?_
    simp only [stepX86_movRR, stepX86_xorRR, maskGprWidth_true, mask32_xor_self, u64_zero_beq_zero,
      b16get_0, b16get_2, b16set_0, b16set_1]
  obtain ⟨x8', x9', h⟩ := ctCurrentEqBytesX86_loop (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5) (r10 := r10)
    (r11 := r11) (r12 := r12) (r13 := r13) (r14 := r14) (r15 := r15) (y := y) (dy := dy) (m := m)
    k r2 r7 r6 0 r8 r9 false false true (j + 13) hn
  rw [h]
  iterate 13
    refine Eq.trans (runX86_step_fst _ _ _ _ rfl rfl) ?_
    simp only [stepX86_subImm32, stepX86_shr32, stepX86_xorRR, stepX86_ret, mask32_xor_self,
      u64_zero_beq_zero, b16get_0, b16get_8, b16get_9, b16set_0, b16set_1, b16set_2, b16set_6, b16set_7, b16set_8, b16set_9, b16set_10, b16set_11]
  exact runX86_halted_fst _ _ _ rfl

end CurrentEqBytesX86

/-- **Machine-code refinement of `qsag_asm_ct_eq_bytes_x86_64`.** For a length `n = rdx ≥ 1` (the
Rust wrapper returns early on empty slices; the loop is bottom-tested), at most `8 n + 15` steps
halt with `rax = 1` when the `n` bytes at `rdi` equal the `n` bytes at `rsi` and `rax = 0`
otherwise (addresses wrap modulo `2^64`); memory is untouched and `r8`, `r9` are wiped. -/
theorem current_ct_eq_bytes_x86_64_mc_refines :
    ∃ slice prog, findSliceByNameBytes currentX86ExtractedSlices ctEqBytesX86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 0 < (s.gpr.get 2).toNat →
        8 * (s.gpr.get 2).toNat + 15 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        (runX86 prog fuel s).1.gpr.get 0 =
          (if ∀ i : Nat, i < (s.gpr.get 2).toNat →
              s.mem (s.gpr.get 7 + UInt64.ofNat i) = s.mem (s.gpr.get 6 + UInt64.ofNat i)
            then 1 else 0) ∧
        (runX86 prog fuel s).1.mem = s.mem ∧
        (runX86 prog fuel s).1.gpr.get 8 = 0 ∧ (runX86 prog fuel s).1.gpr.get 9 = 0 := by
  obtain ⟨sl, hf, hd⟩ := slice_decode_x86 ctCurrentEqBytesX86_decodes
  refine ⟨sl, ctCurrentEqBytesX86Prog, hf, hd, ?_⟩
  intro s fuel hpc hh hn hfuel
  obtain ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
    y, cf, o, zf, dy, hlt, m⟩ := s
  have hpc' : pc = 0 := hpc
  have hh' : hlt = false := hh
  subst hpc' hh'
  have hn' : 0 < r2.toNat := hn
  have hfuel' : 8 * r2.toNat + 15 ≤ fuel := hfuel
  obtain ⟨k, hk⟩ : ∃ k, r2.toNat = k + 1 := ⟨r2.toNat - 1, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, fuel = 8 * (k + 1) + 15 + j := ⟨fuel - (8 * (k + 1) + 15), by omega⟩
  subst hj
  rw [ctCurrentEqBytesX86_run k j hk]
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  obtain ⟨hlt, hz⟩ := eqAcc_spec m (k + 1) r7 r6 0 (by decide)
  show maskGprWidth false (maskGprWidth false (maskGprWidth false (UInt64.ofNat
      (((maskGprWidth false (eqAcc (k + 1) m r7 r6 0)).toNat + 0x100000000 -
        (maskGprWidth false 1).toNat) % 0x100000000))) >>> UInt64.ofNat (31 % 32)) =
    if ∀ i : Nat, i < r2.toNat → m (r7 + UInt64.ofNat i) = m (r6 + UInt64.ofNat i) then 1 else 0
  rw [eqTail_spec _ hlt]
  if hA : eqAcc (k + 1) m r7 r6 0 = 0 then
    rw [ite_eq_left hA, ite_eq_left (fun i hi => (hz.mp hA).2 i (by omega))]
  else
    rw [ite_eq_right hA, ite_eq_right (fun h => hA (hz.mpr ⟨rfl, fun i hi => h i (by omega)⟩))]


/-- Exact decoder regressions for the new transpose instruction forms. -/
theorem current_arm_transpose_decode_regressions :
    decodeArm64Word 0 0x4e080d27 = some (.vdup2d 7 9) ∧
    decodeArm64Word 0 0xad400400 = some (.ldpQ 0 1 0 0) ∧
    decodeArm64Word 0 0xad000400 = some (.stpQ 0 1 0 0) ∧
    decodeArm64Word 0 0x6f600410 = some (.vshift2d false 16 0 32) ∧
    decodeArm64Word 0 0x4f605610 = some (.vshift2d true 16 16 32) ∧
    decodeArm64Word 0 0x4e271e10 = some (.vand16b 16 16 7) ∧
    decodeArm64Word 0 0xad400000 = none ∧
    decodeArm64Word 0 0xad4007e0 = none := by decide +kernel

/-- USHR #64 zeros each lane, rather than applying a modulo-64 host shift. -/
theorem current_arm_ushr64_semantics (s : Arm64State) :
    (stepArm64 ⟨0, 4, .vshift2d false 0 1 64⟩ s).1.vec.get 0 = Vec128.zero := by
  simp only [stepArm64, Bank32.get_set_eq]
  rfl

/-- The fresh transpose's final PC is represented rather than silently truncated. -/
theorem current_pcmap_high_address :
    (PcMap.empty.set 4260 (1 : Nat)).get 4260 = some 1 ∧
    (PcMap.empty.set 8192 (1 : Nat)).get 8192 = none := by decide +kernel


/-- Schoolbook polynomial multiplication over F₂.  Each set bit of `b` contributes
`a * z^k`; XOR is coefficient addition.  The output width is the width of `a`,
so callers use a zero extension when they require an untruncated product. -/
def gf128PolyMulAux {w v : Nat} (a : BitVec w) (b : BitVec v) : Nat → BitVec w
  | 0 => 0
  | k + 1 => gf128PolyMulAux a b k ^^^ (if b.getLsbD k then a <<< k else 0)

def gf128PolyMul {w v : Nat} (a : BitVec w) (b : BitVec v) : BitVec w :=
  gf128PolyMulAux a b v

private theorem gf128XorLeftComm {w : Nat} (a b c : BitVec w) :
    a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc]

private theorem gf128XorCancel {w : Nat} (a b : BitVec w) :
    a ^^^ (a ^^^ b) = b := by
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

private theorem gf128XorShuffle {w : Nat} (a b c d : BitVec w) :
    (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  simp only [BitVec.xor_assoc]
  rw [← BitVec.xor_assoc b c d, BitVec.xor_comm b c, BitVec.xor_assoc]

theorem gf128PolyMulAux_xor_left {w v : Nat} (a a' : BitVec w) (b : BitVec v)
    (n : Nat) :
    gf128PolyMulAux (a ^^^ a') b n =
      gf128PolyMulAux a b n ^^^ gf128PolyMulAux a' b n := by
  induction n with
  | zero => simp [gf128PolyMulAux]
  | succ n ih =>
    simp only [gf128PolyMulAux, ih, BitVec.shiftLeft_xor_distrib]
    cases h : b.getLsbD n <;> simp [gf128XorShuffle]

theorem gf128PolyMulAux_xor_right {w v : Nat} (a : BitVec w) (b b' : BitVec v)
    (n : Nat) :
    gf128PolyMulAux a (b ^^^ b') n =
      gf128PolyMulAux a b n ^^^ gf128PolyMulAux a b' n := by
  induction n with
  | zero => simp [gf128PolyMulAux]
  | succ n ih =>
    simp only [gf128PolyMulAux, ih, BitVec.getLsbD_xor]
    cases h : b.getLsbD n <;> cases h' : b'.getLsbD n <;>
      simp [BitVec.xor_assoc, BitVec.xor_comm, gf128XorLeftComm, gf128XorCancel]

theorem gf128PolyMul_xor_left {w v : Nat} (a a' : BitVec w) (b : BitVec v) :
    gf128PolyMul (a ^^^ a') b = gf128PolyMul a b ^^^ gf128PolyMul a' b :=
  gf128PolyMulAux_xor_left a a' b v

theorem gf128PolyMul_xor_right {w v : Nat} (a : BitVec w) (b b' : BitVec v) :
    gf128PolyMul a (b ^^^ b') = gf128PolyMul a b ^^^ gf128PolyMul a b' :=
  gf128PolyMulAux_xor_right a b b' v

/-- The monic GCM modulus, including its leading z^128 term, in plain
little-endian polynomial coefficient order. -/
def gf128Modulus : BitVec 256 := 0x100000000000000000000000000000087

/-- One polynomial long-division step cancels coefficient 128+k by adding
z^k times the monic modulus.  No integer multiplication or subtraction occurs. -/
def gf128ReduceStep (k : Nat) (p : BitVec 256) : BitVec 256 :=
  if p.getLsbD (128 + k) then p ^^^ (gf128Modulus <<< k) else p

/-- Descending schoolbook polynomial long division. -/
def gf128ReduceAux : Nat → BitVec 256 → BitVec 256
  | 0, p => p
  | k + 1, p => gf128ReduceAux k (gf128ReduceStep k p)

def gf128Reduce (p : BitVec 256) : BitVec 128 :=
  (gf128ReduceAux 128 p).setWidth 128

/-- Multiplication in F₂[z]/(z^128+z^7+z²+z+1). -/
def gf128FieldMul (a b : BitVec 128) : BitVec 128 :=
  gf128Reduce (gf128PolyMul (a.setWidth 256) b)

theorem gf128ReduceStep_xor (k : Nat) (p q : BitVec 256) :
    gf128ReduceStep k (p ^^^ q) = gf128ReduceStep k p ^^^ gf128ReduceStep k q := by
  unfold gf128ReduceStep
  simp only [BitVec.getLsbD_xor]
  cases hp : p.getLsbD (128 + k) <;> cases hq : q.getLsbD (128 + k) <;>
    simp [BitVec.xor_comm, gf128XorLeftComm]

theorem gf128ReduceAux_xor (n : Nat) (p q : BitVec 256) :
    gf128ReduceAux n (p ^^^ q) = gf128ReduceAux n p ^^^ gf128ReduceAux n q := by
  induction n generalizing p q with
  | zero => rfl
  | succ n ih => simp only [gf128ReduceAux, gf128ReduceStep_xor, ih]

theorem gf128Reduce_xor (p q : BitVec 256) :
    gf128Reduce (p ^^^ q) = gf128Reduce p ^^^ gf128Reduce q := by
  simp only [gf128Reduce, gf128ReduceAux_xor, BitVec.setWidth_xor]

theorem gf128FieldMul_xor_left (a a' b : BitVec 128) :
    gf128FieldMul (a ^^^ a') b = gf128FieldMul a b ^^^ gf128FieldMul a' b := by
  simp only [gf128FieldMul, BitVec.setWidth_xor, gf128PolyMul_xor_left, gf128Reduce_xor]

theorem gf128FieldMul_xor_right (a b b' : BitVec 128) :
    gf128FieldMul a (b ^^^ b') = gf128FieldMul a b ^^^ gf128FieldMul a b' := by
  simp only [gf128FieldMul, gf128PolyMul_xor_right, gf128Reduce_xor]

/-- Interpret a low/high pair in plain little-endian coefficient order. -/
def gf128Words (lo hi : UInt64) : BitVec 128 := hi.toBitVec ++ lo.toBitVec

theorem gf128Words_xor (a b c d : UInt64) :
    gf128Words (a ^^^ c) (b ^^^ d) = gf128Words a b ^^^ gf128Words c d := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hbound
  simp only [gf128Words, BitVec.getLsbD_append, UInt64.toBitVec_xor, BitVec.getLsbD_xor]
  split <;> rfl

private theorem gf128ShiftAmount (i : Nat) (hi : i < 64) :
    ((UInt64.ofNat i).toBitVec % (64 : BitVec 64)).toNat = i := by
  simp [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt (show i < 2^64 by omega)]

private theorem gf128ClmulBit (b : UInt64) (i : Nat) (hi : i < 64) :
    (((b >>> UInt64.ofNat i) &&& 1) != 0) = b.toBitVec.getLsbD i := by
  have hm := gf128ShiftAmount i hi
  have he : ((b >>> UInt64.ofNat i) &&& 1).toBitVec =
      if b.toBitVec.getLsbD i then 1 else 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hbound
    simp only [UInt64.toBitVec_and, UInt64.toBitVec_shiftRight, UInt64.toBitVec_one,
      BitVec.ushiftRight_eq', hm, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_one]
    by_cases hj : j = 0
    · subst j; cases b.toBitVec.getLsbD i <;> simp
    · cases b.toBitVec.getLsbD i <;> simp [hj]
  cases h : b.toBitVec.getLsbD i
  · have hz : ((b >>> UInt64.ofNat i) &&& 1) = 0 :=
      UInt64.eq_of_toBitVec_eq (by simpa [h] using he)
    simp [hz]
  · have hz : ((b >>> UInt64.ofNat i) &&& 1) = 1 :=
      UInt64.eq_of_toBitVec_eq (by simpa [h] using he)
    simp [hz]

private theorem gf128ClmulShift (a : UInt64) (i : Nat) (hi : i < 64) :
    gf128Words (if i == 0 then a else a <<< UInt64.ofNat i)
      (if i > 0 then a >>> UInt64.ofNat (64-i) else 0) =
      a.toBitVec.setWidth 128 <<< i := by
  by_cases hz : i = 0
  · subst i
    apply BitVec.eq_of_getLsbD_eq
    intro j hbound
    simp only [gf128Words, BitVec.shiftLeft_zero,
      BitVec.getLsbD_append, BitVec.getLsbD_setWidth, hbound, decide_true, Bool.true_and]
    by_cases hj : j < 64
    · simp [hj]
    · simp [hj, show 64 ≤ j by omega]
  · have hp : i > 0 := by omega
    have hm := gf128ShiftAmount i hi
    have hn := gf128ShiftAmount (64-i) (by omega)
    apply BitVec.eq_of_getLsbD_eq
    intro j hbound
    simp only [gf128Words, beq_iff_eq, hz, ↓reduceIte, hp,
      UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
      BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', hm, hn,
      BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_setWidth]
    by_cases hj : j < 64
    · simp [hj, show j < 128 by omega, show j-i < 128 by omega]
    · have he : 64-i + (j - 64) = j-i := by omega
      simp only [hj, ↓reduceIte, he]
      simp [hbound, show ¬j < i by omega, show j-i < 128 by omega]

/-- Ascending schoolbook sum over an interval of multiplier coefficients. -/
def gf128PolyRange (a : BitVec 128) (b : BitVec 64) (start : Nat) : Nat → BitVec 128
  | 0 => 0
  | n+1 => (if b.getLsbD start then a <<< start else 0) ^^^
      gf128PolyRange a b (start+1) n

theorem gf128ClmulLoop_spec (n : Nat) (hn : n ≤ 64)
    (a b lo hi : UInt64) :
    gf128Words (clmul64Loop n a b lo hi).w0 (clmul64Loop n a b lo hi).w1 =
      gf128Words lo hi ^^^ gf128PolyRange (a.toBitVec.setWidth 128) b.toBitVec (64-n) n := by
  induction n generalizing lo hi with
  | zero => simp [clmul64Loop, gf128PolyRange]
  | succ n ih =>
    have hn' : n ≤ 64 := by omega
    have hi' : 63-n < 64 := by omega
    have he : 64-(n+1) = 63-n := by omega
    have hf : 64-n = 63-n+1 := by omega
    simp only [clmul64Loop]
    rw [ih hn', gf128Words_xor]
    have ht : gf128Words
        (if ((b >>> UInt64.ofNat (63-n)) &&& 1) != 0 then
          (if 63-n == 0 then a else a <<< UInt64.ofNat (63-n)) else 0)
        (if (((b >>> UInt64.ofNat (63-n)) &&& 1) != 0) && (63-n > 0) then
          a >>> UInt64.ofNat (64-(63-n)) else 0) =
        if b.toBitVec.getLsbD (63-n) then a.toBitVec.setWidth 128 <<< (63-n) else 0 := by
      rw [gf128ClmulBit b _ hi']
      cases h : b.toBitVec.getLsbD (63-n)
      · simp [gf128Words]
      · simpa using gf128ClmulShift a (63-n) hi'
    rw [ht]
    simp only [gf128PolyRange, he, hf, BitVec.xor_assoc]

private theorem gf128PolyRange_succ (a : BitVec 128) (b : BitVec 64) (n start : Nat) :
    gf128PolyRange a b start (n+1) = gf128PolyRange a b start n ^^^
      (if b.getLsbD (start+n) then a <<< (start+n) else 0) := by
  induction n generalizing start with
  | zero => simp [gf128PolyRange]
  | succ n ih =>
    change _ ^^^ gf128PolyRange a b (start+1) (n+1) =
      (_ ^^^ gf128PolyRange a b (start+1) n) ^^^ _
    rw [ih]
    simp only [Nat.add_assoc, Nat.add_comm 1 n, BitVec.xor_assoc]

private theorem gf128PolyRange_eq_aux (a : BitVec 128) (b : BitVec 64) (n : Nat) :
    gf128PolyRange a b 0 n = gf128PolyMulAux a b n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [gf128PolyRange_succ, ih, gf128PolyMulAux, Nat.zero_add]

/-- The machine primitive is exactly the 64-by-64 polynomial product over F₂,
with coefficient i represented by bit i (no reflected GCM convention). -/
theorem gf128_clmul64_polynomial (a b : UInt64) :
    gf128Words (clmul64 a b).w0 (clmul64 a b).w1 =
      gf128PolyMul (a.toBitVec.setWidth 128) b.toBitVec := by
  have h := gf128ClmulLoop_spec 64 (by omega) a b 0 0
  simpa [clmul64, gf128Words, gf128PolyRange_eq_aux, gf128PolyMul] using h

/-- Coefficients of the monomial z^n. -/
theorem gf128Basis_bit {w : Nat} (i n : Nat) (hi : i < w) :
    ((1 : BitVec w) <<< n).getLsbD i = decide (i = n) := by
  by_cases heq : i = n
  · subst n
    simp [hi]
  · by_cases hlt : i < n
    · simp [hi, hlt, heq]
    · have hsub : i - n ≠ 0 := by omega
      simp [hi, hlt, hsub, heq]

theorem gf128PolyMulAux_one_bit {w : Nat} (p : BitVec w) (n i : Nat) (hi : i < w) :
    (gf128PolyMulAux (1 : BitVec w) p n).getLsbD i =
      (p.getLsbD i && decide (i < n)) := by
  induction n with
  | zero => simp [gf128PolyMulAux]
  | succ n ih =>
    simp only [gf128PolyMulAux, BitVec.getLsbD_xor, ih]
    by_cases heq : i = n
    · subst n
      cases hp : p.getLsbD i
      · simp
      · simp only [ite_true]
        rw [gf128Basis_bit i i hi]
        simp
    · have hlt : (i < n + 1) = (i < n) := propext ⟨fun h => by omega, fun h => by omega⟩
      cases hp : p.getLsbD n
      · simp [hlt]
      · simp only [ite_true]
        rw [gf128Basis_bit i n hi]
        simp [heq, hlt]

/-- Expansion into the coefficient basis, proved by induction on the number of
coefficients rather than enumeration of the 2^w possible words. -/
theorem gf128PolyMul_one {w : Nat} (p : BitVec w) :
    gf128PolyMul (1 : BitVec w) p = p := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  change (gf128PolyMulAux (1 : BitVec w) p w).getLsbD i = _
  rw [gf128PolyMulAux_one_bit p w i hi]
  simp [hi]

/-- Two XOR-linear maps agree if they agree on the w monomials. -/
theorem gf128Linear_ext {w v : Nat} (f g : BitVec w → BitVec v)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hf : ∀ a b, f (a ^^^ b) = f a ^^^ f b)
    (hg : ∀ a b, g (a ^^^ b) = g a ^^^ g b)
    (hbasis : ∀ i, i < w → f ((1 : BitVec w) <<< i) = g ((1 : BitVec w) <<< i))
    (p : BitVec w) : f p = g p := by
  have haux : ∀ n, n ≤ w →
      f (gf128PolyMulAux (1 : BitVec w) p n) =
      g (gf128PolyMulAux (1 : BitVec w) p n) := by
    intro n
    induction n with
    | zero => intro _; simp only [gf128PolyMulAux, hf0, hg0]
    | succ n ih =>
      intro hn
      simp only [gf128PolyMulAux, hf, hg, ih (by omega)]
      cases hp : p.getLsbD n
      · exact congrArg (fun x : BitVec v => g (gf128PolyMulAux 1 p n) ^^^ x)
          (hf0.trans hg0.symm)
      · exact congrArg (fun x : BitVec v => g (gf128PolyMulAux 1 p n) ^^^ x)
          (hbasis n (by omega))
  have h := haux w (Nat.le_refl w)
  change f (gf128PolyMul 1 p) = g (gf128PolyMul 1 p) at h
  simpa only [gf128PolyMul_one] using h

/-- Replace the upper polynomial half h*z^128 by h*(z^7+z²+z+1).
This is a congruence modulo the monic GCM polynomial. -/
def gf128Fold256 (p : BitVec 256) : BitVec 256 :=
  (p.setWidth 128).setWidth 256 ^^^ gf128PolyMul (p >>> 128) (0x87 : BitVec 8)

/-- Degree drops from at most 255 to at most 134 after the first fold, and
below 128 after the second. -/
def gf128TwoFold (p : BitVec 256) : BitVec 128 :=
  (gf128Fold256 (gf128Fold256 p)).setWidth 128

theorem gf128Fold256_xor (p q : BitVec 256) :
    gf128Fold256 (p ^^^ q) = gf128Fold256 p ^^^ gf128Fold256 q := by
  simp only [gf128Fold256, BitVec.setWidth_xor, BitVec.ushiftRight_xor_distrib,
    gf128PolyMul_xor_left]
  exact gf128XorShuffle _ _ _ _

theorem gf128TwoFold_xor (p q : BitVec 256) :
    gf128TwoFold (p ^^^ q) = gf128TwoFold p ^^^ gf128TwoFold q := by
  simp only [gf128TwoFold, gf128Fold256_xor, BitVec.setWidth_xor]

private theorem gf128Reduce_twoFold_basis :
    ∀ i : Fin 256, gf128Reduce ((1 : BitVec 256) <<< i.val) =
      gf128TwoFold ((1 : BitVec 256) <<< i.val) := by
  decide +kernel

/-- Polynomial long division equals the two-fold reduction by 0x87.
The only finite check is the 256 monomials; arbitrary inputs follow from
linearity and the coefficient expansion theorem. -/
theorem gf128Reduce_eq_twoFold (p : BitVec 256) :
    gf128Reduce p = gf128TwoFold p := by
  apply gf128Linear_ext gf128Reduce gf128TwoFold
  · decide +kernel
  · decide +kernel
  · exact gf128Reduce_xor
  · exact gf128TwoFold_xor
  · intro i hi
    exact gf128Reduce_twoFold_basis ⟨i, hi⟩

/-- The word-oriented 0x87 reduction used by the carry-less multiply kernels. -/
def gf128WordReduce (lo0 lo1 hi0 hi1 : UInt64) : BitVec 128 :=
  let r1 := clmul64 hi1 0x87
  let r0 := clmul64 (hi0 ^^^ r1.w1) 0x87
  gf128Words (lo0 ^^^ r0.w0) (lo1 ^^^ r1.w0 ^^^ r0.w1)

private def gf128WordReducePoly (lo hi : BitVec 128) : BitVec 128 :=
  let r1 := gf128PolyMul ((hi.extractLsb' 64 64).setWidth 128) (0x87 : BitVec 64)
  let r0 := gf128PolyMul
    (((hi.extractLsb' 0 64) ^^^ (r1.extractLsb' 64 64)).setWidth 128) (0x87 : BitVec 64)
  lo ^^^ (r1 <<< 64) ^^^ r0

private def gf128WordReduceMap (p : BitVec 256) : BitVec 128 :=
  gf128WordReducePoly (p.extractLsb' 0 128) (p.extractLsb' 128 128)

private theorem gf128WordReduceShuffle (a b c d e f g h : BitVec 128) :
    ((a ^^^ b) ^^^ (c ^^^ d)) ^^^ ((e ^^^ f) ^^^ (g ^^^ h)) =
      ((a ^^^ c) ^^^ (e ^^^ g)) ^^^ ((b ^^^ d) ^^^ (f ^^^ h)) := by
  simp only [BitVec.xor_comm, gf128XorLeftComm]

private theorem gf128WordReduceMap_xor (p q : BitVec 256) :
    gf128WordReduceMap (p ^^^ q) = gf128WordReduceMap p ^^^ gf128WordReduceMap q := by
  simp only [gf128WordReduceMap, gf128WordReducePoly, BitVec.extractLsb'_xor,
    BitVec.setWidth_xor, gf128PolyMul_xor_left, BitVec.shiftLeft_xor_distrib]
  exact gf128WordReduceShuffle _ _ _ _ _ _ _ _

private theorem gf128WordReduceMap_basis :
    ∀ i : Fin 256, gf128WordReduceMap ((1 : BitVec 256) <<< i.val) =
      gf128Reduce ((1 : BitVec 256) <<< i.val) := by
  decide +kernel

private theorem gf128WordReduceMap_eq (p : BitVec 256) :
    gf128WordReduceMap p = gf128Reduce p := by
  apply gf128Linear_ext gf128WordReduceMap gf128Reduce
  · decide +kernel
  · decide +kernel
  · exact gf128WordReduceMap_xor
  · exact gf128Reduce_xor
  · intro i hi
    exact gf128WordReduceMap_basis ⟨i, hi⟩

private theorem gf128Words_extract_lo (lo hi : UInt64) :
    (gf128Words lo hi).extractLsb' 0 64 = lo.toBitVec :=
  BitVec.extractLsb'_append_eq_right

private theorem gf128Words_extract_hi (lo hi : UInt64) :
    (gf128Words lo hi).extractLsb' 64 64 = hi.toBitVec :=
  BitVec.extractLsb'_append_eq_left

private theorem gf128Words_shift64_xor (a b c d e f : UInt64) :
    gf128Words (a ^^^ e) (b ^^^ c ^^^ f) =
      gf128Words a b ^^^ (gf128Words c d <<< 64) ^^^ gf128Words e f := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [gf128Words, UInt64.toBitVec_xor, BitVec.getLsbD_xor,
    BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft]
  by_cases h : i < 64
  · simp [h, hi]
  · simp [h, hi, show i - 64 < 64 by omega]

private theorem gf128WordReduce_eq_poly (lo0 lo1 hi0 hi1 : UInt64) :
    gf128WordReduce lo0 lo1 hi0 hi1 =
      gf128WordReducePoly (gf128Words lo0 lo1) (gf128Words hi0 hi1) := by
  unfold gf128WordReducePoly
  rw [gf128Words_extract_hi, gf128Words_extract_lo]
  change _ = gf128Words lo0 lo1 ^^^
    (gf128PolyMul (hi1.toBitVec.setWidth 128) (0x87 : UInt64).toBitVec <<< 64) ^^^
    gf128PolyMul
      ((hi0.toBitVec ^^^ (gf128PolyMul (hi1.toBitVec.setWidth 128)
        (0x87 : UInt64).toBitVec).extractLsb' 64 64).setWidth 128) (0x87 : UInt64).toBitVec
  rw [← gf128_clmul64_polynomial hi1 0x87, gf128Words_extract_hi,
    ← UInt64.toBitVec_xor, ← gf128_clmul64_polynomial]
  exact gf128Words_shift64_xor _ _ _ _ _ _

/-- The machine word-level two-fold 0x87 reduction is exactly schoolbook
polynomial long division by z^128+z^7+z²+z+1. -/
theorem gf128WordReduce_eq_reduce (lo0 lo1 hi0 hi1 : UInt64) :
    gf128WordReduce lo0 lo1 hi0 hi1 =
      gf128Reduce (gf128Words hi0 hi1 ++ gf128Words lo0 lo1) := by
  rw [gf128WordReduce_eq_poly]
  have h := gf128WordReduceMap_eq (gf128Words hi0 hi1 ++ gf128Words lo0 lo1)
  simpa only [gf128WordReduceMap, BitVec.extractLsb'_append_eq_left,
    BitVec.extractLsb'_append_eq_right] using h

/-- Multiplication commutes with multiplying the multiplicand by a monomial. -/
theorem gf128PolyMulAux_shift_left {w v : Nat} (a : BitVec w) (b : BitVec v)
    (s n : Nat) :
    gf128PolyMulAux (a <<< s) b n = gf128PolyMulAux a b n <<< s := by
  induction n with
  | zero => simp [gf128PolyMulAux]
  | succ n ih =>
    simp only [gf128PolyMulAux, ih, BitVec.shiftLeft_xor_distrib]
    cases hb : b.getLsbD n <;>
      simp [← BitVec.shiftLeft_add, Nat.add_comm s n]

theorem gf128PolyMul_shift_left {w v : Nat} (a : BitVec w) (b : BitVec v)
    (s : Nat) :
    gf128PolyMul (a <<< s) b = gf128PolyMul a b <<< s :=
  gf128PolyMulAux_shift_left a b s v

private theorem gf128PolyMulAux_append_low {w : Nat} (a : BitVec w)
    (lo hi : BitVec 64) (n : Nat) (hn : n ≤ 64) :
    gf128PolyMulAux a (hi ++ lo) n = gf128PolyMulAux a lo n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [gf128PolyMulAux, ih (by omega), BitVec.getLsbD_append,
      show n < 64 by omega, ↓reduceIte]

private theorem gf128PolyMulAux_append_high {w : Nat} (a : BitVec w)
    (lo hi : BitVec 64) (n : Nat) :
    gf128PolyMulAux a (hi ++ lo) (64+n) =
      gf128PolyMul a lo ^^^ (gf128PolyMulAux a hi n <<< 64) := by
  induction n with
  | zero =>
    change gf128PolyMulAux a (hi ++ lo) 64 =
      gf128PolyMulAux a lo 64 ^^^ ((0 : BitVec w) <<< (64 : Nat))
    rw [gf128PolyMulAux_append_low a lo hi 64 (by omega)]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, BitVec.ofNat_eq_ofNat,
      BitVec.getLsbD_zero, Bool.and_false, Bool.xor_false]
  | succ n ih =>
    rw [show 64+(n+1) = (64+n)+1 by omega, gf128PolyMulAux, ih]
    simp only [gf128PolyMulAux, BitVec.getLsbD_append, show ¬64+n < 64 by omega,
      ↓reduceIte, Nat.add_sub_cancel_left, BitVec.shiftLeft_xor_distrib]
    cases hb : hi.getLsbD n <;>
      simp [← BitVec.shiftLeft_add, Nat.add_comm 64 n, BitVec.xor_assoc]

theorem gf128PolyMul_append_right {w : Nat} (a : BitVec w) (lo hi : BitVec 64) :
    gf128PolyMul a (hi ++ lo) =
      gf128PolyMul a lo ^^^ (gf128PolyMul a hi <<< 64) :=
  gf128PolyMulAux_append_high a lo hi 64

/-- Split the coefficient vector at z^64, with disjoint supports. -/
theorem gf128Words_split (lo hi : UInt64) :
    (gf128Words lo hi).setWidth 256 =
      lo.toBitVec.setWidth 256 ^^^ (hi.toBitVec.setWidth 256 <<< 64) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [gf128Words, BitVec.getLsbD_setWidth, BitVec.getLsbD_append,
    BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, hj, decide_true, Bool.true_and]
  by_cases hlow : j < 64
  · simp [hlow]
  · simp [hlow, show 64 ≤ j by omega, show j-64 < 256 by omega]

/-- Four schoolbook limb products, assembled at degrees 0,64,128. -/
theorem gf128_four_product_polynomial (a0 a1 b0 b1 : UInt64) :
    gf128PolyMul ((gf128Words a0 a1).setWidth 256) (gf128Words b0 b1) =
      gf128PolyMul (a0.toBitVec.setWidth 256) b0.toBitVec ^^^
      ((gf128PolyMul (a0.toBitVec.setWidth 256) b1.toBitVec ^^^
        gf128PolyMul (a1.toBitVec.setWidth 256) b0.toBitVec) <<< 64) ^^^
      (gf128PolyMul (a1.toBitVec.setWidth 256) b1.toBitVec <<< 128) := by
  rw [gf128Words_split]
  simp only [gf128Words, gf128PolyMul_append_right, gf128PolyMul_xor_left,
    gf128PolyMul_shift_left, BitVec.shiftLeft_xor_distrib, ← BitVec.shiftLeft_add]
  simp only [BitVec.xor_assoc]
  rw [gf128XorLeftComm
    (gf128PolyMul (a1.toBitVec.setWidth 256) b0.toBitVec <<< 64)
    (gf128PolyMul (a0.toBitVec.setWidth 256) b1.toBitVec <<< 64)]

private theorem gf128LimbShift_widen (a : BitVec 64) (n : Nat) (hn : n < 64) :
    ((a.setWidth 128 <<< n).setWidth 256) = a.setWidth 256 <<< n := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, hj, decide_true, Bool.true_and]
  by_cases hjn : j < n
  · simp [hjn]
  · by_cases h : j < 128
    · simp [hjn, h, show j-n < 128 by omega, show j-n < 256 by omega]
    · simp [hjn, h, show 64 ≤ j-n by omega]

private theorem gf128PolyMulAux_widen64 (a b : BitVec 64) (n : Nat) (hn : n ≤ 64) :
    (gf128PolyMulAux (a.setWidth 128) b n).setWidth 256 =
      gf128PolyMulAux (a.setWidth 256) b n := by
  induction n with
  | zero => simp [gf128PolyMulAux]
  | succ n ih =>
    simp only [gf128PolyMulAux, BitVec.setWidth_xor, ih (by omega)]
    cases hb : b.getLsbD n <;> simp [gf128LimbShift_widen a n (by omega)]

/-- Widening the primitive's complete 128-bit output loses no coefficients. -/
theorem gf128_clmul64_widen (a b : UInt64) :
    (gf128Words (clmul64 a b).w0 (clmul64 a b).w1).setWidth 256 =
      gf128PolyMul (a.toBitVec.setWidth 256) b.toBitVec := by
  rw [gf128_clmul64_polynomial]
  exact gf128PolyMulAux_widen64 a.toBitVec b.toBitVec 64 (by omega)

/-- Four machine carry-less products recombine into the complete 128-by-128
polynomial product. No quotient/reduction is hidden in this statement. -/
theorem gf128_clmul_four_product (a0 a1 b0 b1 : UInt64) :
    (gf128Words (clmul64 a0 b0).w0 (clmul64 a0 b0).w1).setWidth 256 ^^^
    (((gf128Words (clmul64 a0 b1).w0 (clmul64 a0 b1).w1).setWidth 256 ^^^
      (gf128Words (clmul64 a1 b0).w0 (clmul64 a1 b0).w1).setWidth 256) <<< 64) ^^^
    ((gf128Words (clmul64 a1 b1).w0 (clmul64 a1 b1).w1).setWidth 256 <<< 128) =
      gf128PolyMul ((gf128Words a0 a1).setWidth 256) (gf128Words b0 b1) := by
  simp only [gf128_clmul64_widen]
  exact (gf128_four_product_polynomial a0 a1 b0 b1).symm

/-- Karatsuba's third multiplication recovers the two cross terms. -/
theorem gf128_clmul_karatsuba_cross (a0 a1 b0 b1 : UInt64) :
    gf128Words (clmul64 (a0 ^^^ a1) (b0 ^^^ b1)).w0
      (clmul64 (a0 ^^^ a1) (b0 ^^^ b1)).w1 ^^^
      gf128Words (clmul64 a0 b0).w0 (clmul64 a0 b0).w1 ^^^
      gf128Words (clmul64 a1 b1).w0 (clmul64 a1 b1).w1 =
    gf128Words (clmul64 a0 b1).w0 (clmul64 a0 b1).w1 ^^^
      gf128Words (clmul64 a1 b0).w0 (clmul64 a1 b0).w1 := by
  simp only [gf128_clmul64_polynomial, UInt64.toBitVec_xor, BitVec.setWidth_xor,
    gf128PolyMul_xor_left, gf128PolyMul_xor_right]
  simp [BitVec.xor_assoc, BitVec.xor_comm, gf128XorLeftComm, gf128XorCancel]

private theorem gf128FourWords_shift (p00 p01 p10 p11 : Vec128) :
    gf128Words (p11.w0 ^^^ p01.w1 ^^^ p10.w1) p11.w1 ++
      gf128Words p00.w0 (p00.w1 ^^^ p01.w0 ^^^ p10.w0) =
    (gf128Words p00.w0 p00.w1).setWidth 256 ^^^
      (((gf128Words p01.w0 p01.w1).setWidth 256 ^^^
        (gf128Words p10.w0 p10.w1).setWidth 256) <<< 64) ^^^
      ((gf128Words p11.w0 p11.w1).setWidth 256 <<< 128) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [gf128Words, BitVec.getLsbD_append, UInt64.toBitVec_xor,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_xor,
    hj, decide_true, Bool.true_and]
  by_cases h0 : j < 64
  · simp [h0, show j < 128 by omega]
  · by_cases h1 : j < 128
    · simp [h0, h1, show j-64 < 64 by omega, show j-64 < 256 by omega]
    · by_cases h2 : j < 192
      · have he : j-64-64 = j-128 := by omega
        simp [h0, h1, he, show j-128 < 64 by omega,
          show j-64 < 256 by omega, show j-128 < 256 by omega,
          show 64 ≤ j-64 by omega, show ¬j-64 < 64 by omega, Bool.xor_comm]
      · have he : j-64-64 = j-128 := by omega
        have hf : j-128-64 = j-192 := by omega
        simp [h0, h1, he, hf, show 64 ≤ j-64 by omega, show 64 ≤ j-128 by omega,
          show j-128 < 256 by omega, show ¬ j-128 < 64 by omega,
          show ¬ j-64 < 64 by omega]

/-- The exact four-limb recombination performed by the SIMD schoolbook kernels. -/
theorem gf128_clmul_four_words (a0 a1 b0 b1 : UInt64) :
    let p00 := clmul64 a0 b0
    let p01 := clmul64 a0 b1
    let p10 := clmul64 a1 b0
    let p11 := clmul64 a1 b1
    gf128Words (p11.w0 ^^^ p01.w1 ^^^ p10.w1) p11.w1 ++
      gf128Words p00.w0 (p00.w1 ^^^ p01.w0 ^^^ p10.w0) =
      gf128PolyMul ((gf128Words a0 a1).setWidth 256) (gf128Words b0 b1) := by
  dsimp only
  rw [gf128FourWords_shift]
  exact gf128_clmul_four_product a0 a1 b0 b1

/-- Equality of coefficient vectors determines both machine limbs. -/
theorem gf128Words_inj {a0 a1 b0 b1 : UInt64}
    (h : gf128Words a0 a1 = gf128Words b0 b1) : a0 = b0 ∧ a1 = b1 := by
  constructor
  · apply UInt64.eq_of_toBitVec_eq
    have h0 := congrArg (fun x : BitVec 128 => x.extractLsb' 0 64) h
    simpa only [gf128Words, BitVec.extractLsb'_append_eq_right] using h0
  · apply UInt64.eq_of_toBitVec_eq
    have h1 := congrArg (fun x : BitVec 128 => x.extractLsb' 64 64) h
    simpa only [gf128Words, BitVec.extractLsb'_append_eq_left] using h1

/-- Three-product Karatsuba recombination at the exact machine-word boundary. -/
theorem gf128_clmul_karatsuba_words (a0 a1 b0 b1 : UInt64) :
    let p00 := clmul64 a0 b0
    let p11 := clmul64 a1 b1
    let pm := clmul64 (a0 ^^^ a1) (b0 ^^^ b1)
    let m0 := pm.w0 ^^^ p00.w0 ^^^ p11.w0
    let m1 := pm.w1 ^^^ p00.w1 ^^^ p11.w1
    gf128Words (p11.w0 ^^^ m1) p11.w1 ++ gf128Words p00.w0 (p00.w1 ^^^ m0) =
      gf128PolyMul ((gf128Words a0 a1).setWidth 256) (gf128Words b0 b1) := by
  have hc := gf128_clmul_karatsuba_cross a0 a1 b0 b1
  rw [← gf128Words_xor, ← gf128Words_xor, ← gf128Words_xor] at hc
  obtain ⟨h0, h1⟩ := gf128Words_inj hc
  dsimp only
  rw [h0, h1]
  simpa only [UInt64.xor_assoc] using gf128_clmul_four_words a0 a1 b0 b1

/-- Mutation tooth: a polynomial multiplier that drops coefficient zero is wrong. -/
theorem gf128_clmul64_polynomial_tooth :
    gf128Words (clmul64 1 1).w0 (clmul64 1 1).w1 ≠
      gf128PolyRange ((1 : BitVec 64).setWidth 128) 1 1 63 := by
  decide +kernel

/-- The bounded primitive loop theorem has reachable, nonzero inputs. -/
theorem gf128_clmul64_loop_inhabited :
    ∃ n : Nat, ∃ a b lo hi : UInt64, n ≤ 64 ∧
      gf128Words (clmul64Loop n a b lo hi).w0 (clmul64Loop n a b lo hi).w1 = 1 := by
  exact ⟨64, 1, 1, 0, 0, by decide, by decide +kernel⟩

/-- Reject a wrong modulus with the z term removed. -/
theorem gf128_reduce_modulus_tooth :
    gf128Reduce ((1 : BitVec 256) <<< 128) ≠ 0x85 := by
  decide +kernel

#tooth_pair gf128_clmul64_polynomial vs gf128_clmul64_polynomial_tooth
#tooth_pair gf128ClmulLoop_spec vs gf128_clmul64_polynomial_tooth
#verify_inhabited gf128ClmulLoop_spec gf128_clmul64_loop_inhabited
set_option maxRecDepth 4096 in
#tooth_pair gf128Reduce_eq_twoFold vs gf128_reduce_modulus_tooth


/-- Omitting the high-by-high term loses z^128. -/
theorem gf128_four_product_high_tooth :
    gf128PolyMul ((gf128Words 0 1).setWidth 256) (gf128Words 0 1) ≠
      gf128PolyMul ((gf128Words 0 0).setWidth 256) (gf128Words 0 1) := by
  decide +kernel

theorem gf128_four_product_witness :
    ∃ a0 a1 b0 b1 : UInt64,
      gf128Words a0 a1 ≠ 0 ∧ gf128Words b0 b1 ≠ 0 ∧
      gf128PolyMul ((gf128Words a0 a1).setWidth 256) (gf128Words b0 b1) =
        (1 : BitVec 256) <<< 128 := by
  exact ⟨0, 1, 0, 1, by decide +kernel⟩

/-- Treating Karatsuba's third product itself as the cross term is wrong. -/
theorem gf128_karatsuba_cross_tooth :
    gf128Words (clmul64 1 1).w0 (clmul64 1 1).w1 ≠
      gf128Words (clmul64 1 0).w0 (clmul64 1 0).w1 ^^^
        gf128Words (clmul64 0 1).w0 (clmul64 0 1).w1 := by
  decide +kernel

set_option maxRecDepth 4096 in
#tooth_pair gf128_clmul_four_words vs gf128_four_product_high_tooth
set_option maxRecDepth 4096 in
#tooth_pair gf128_clmul_karatsuba_words vs gf128_karatsuba_cross_tooth

end Qsag

public section
namespace Qsag
@[simp] theorem zeroRange_zero (m : UInt64 → UInt8) (p : UInt64) :
    zeroRange 0 m p = m := by rfl
theorem zeroRange_succ (k : Nat) (m : UInt64 → UInt8) (p : UInt64) :
    zeroRange (k+1) m p = zeroRange k (writeMem8 m p 0) (p+1) := by rfl
theorem gf128Reduce_zero_eq : gf128Reduce 0 = 0 := by decide +kernel
theorem byteDiff_unfold (x y : UInt8) : byteDiff x y =
    (maskGprWidth false (maskGprWidth false x.toUInt64 ^^^ maskGprWidth false y.toUInt64)) := by rfl
theorem gf128Words_eq (lo hi : UInt64) : gf128Words lo hi =
    (hi.toBitVec ++ lo.toBitVec) := by rfl
theorem gf128FieldMul_eq (a b : BitVec 128) : gf128FieldMul a b =
    (gf128Reduce (gf128PolyMul (a.setWidth 256) b)) := by rfl
theorem gf128WordReduce_eq (lo0 lo1 hi0 hi1 : UInt64) : gf128WordReduce lo0 lo1 hi0 hi1 =
    (let r1 := clmul64 hi1 0x87
  let r0 := clmul64 (hi0 ^^^ r1.w1) 0x87
  gf128Words (lo0 ^^^ r0.w0) (lo1 ^^^ r1.w0 ^^^ r0.w1)) := by rfl
end Qsag

/-! ## §13. Symbol bytes and byte-decoding certificates for the `Qsag.Machine.SydTv` kernels

The code bytes of the looping kernels that `Qsag.Machine.SydTv` validates, their identification with
slices of the extracted `.rlib` fixture, and the kernel-checked facts that `decodeX86One` /
`decodeArm64One` return each listed instruction at its offset. They live here because the checks
evaluate the decoder. -/

namespace Qsag

theorem ctCurrentMemzeroX86Prog_eq : ctCurrentMemzeroX86Prog = [
  ⟨0, 3, .movRegReg true 1 6⟩,
  ⟨3, 2, .aluRegReg .xorOp false 0 0⟩,
  ⟨5, 2, .storeGpr 1 0 (.baseDisp 7 0)⟩,
  ⟨7, 3, .incDec true true 7⟩,
  ⟨10, 3, .incDec false true 1⟩,
  ⟨13, 2, .jcc 5 5⟩,
  ⟨15, 3, .mfence⟩,
  ⟨18, 2, .aluRegReg .xorOp false 7 7⟩,
  ⟨20, 2, .aluRegReg .xorOp false 6 6⟩,
  ⟨22, 2, .aluRegReg .xorOp false 2 2⟩,
  ⟨24, 2, .aluRegReg .xorOp false 1 1⟩,
  ⟨26, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨29, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨32, 3, .aluRegReg .xorOp false 10 10⟩,
  ⟨35, 3, .aluRegReg .xorOp false 11 11⟩,
  ⟨38, 2, .aluRegReg .xorOp false 0 0⟩,
  ⟨40, 1, .ret⟩] := by rfl
theorem ctMemzeroArmProg_eq : ctMemzeroArmProg = [
  ⟨0, 4, .strbPost 31 0 1⟩,
  ⟨4, 4, .aluImm .subs true 1 1 1⟩,
  ⟨8, 4, .bCond 1 0⟩,
  ⟨12, 4, .dmbIsh⟩,
  ⟨16, 4, .ret⟩] := by rfl
theorem ctCurrentEqBytesX86Prog_eq : ctCurrentEqBytesX86Prog = [
  ⟨0, 2, .aluRegReg .xorOp false 0 0⟩,
  ⟨2, 3, .movRegReg true 1 2⟩,
  ⟨5, 4, .loadGpr 1 false 8 (.baseDisp 7 0)⟩,
  ⟨9, 4, .loadGpr 1 false 9 (.baseDisp 6 0)⟩,
  ⟨13, 3, .aluRegReg .xorOp false 8 9⟩,
  ⟨16, 3, .aluRegReg .orOp false 0 8⟩,
  ⟨19, 3, .incDec true true 7⟩,
  ⟨22, 3, .incDec true true 6⟩,
  ⟨25, 3, .incDec false true 1⟩,
  ⟨28, 2, .jcc 5 5⟩,
  ⟨30, 3, .aluImm .sub false 0 1⟩,
  ⟨33, 3, .shiftImm .shr false 0 31⟩,
  ⟨36, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨39, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨42, 2, .aluRegReg .xorOp false 7 7⟩,
  ⟨44, 2, .aluRegReg .xorOp false 6 6⟩,
  ⟨46, 2, .aluRegReg .xorOp false 2 2⟩,
  ⟨48, 2, .aluRegReg .xorOp false 1 1⟩,
  ⟨50, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨53, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨56, 3, .aluRegReg .xorOp false 10 10⟩,
  ⟨59, 3, .aluRegReg .xorOp false 11 11⟩,
  ⟨62, 1, .ret⟩] := by rfl
end Qsag

namespace Qsag.SydTv
open Qsag
/- Byte-decoding certificates share the implementation's public statements. The translation
validator consumes these certificates without unfolding the byte decoder. -/

theorem stepX86Full_vzeroall (off len pc : Nat) (g : Bank16 UInt64) (y : Bank16 Vec256)
    (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    stepX86 ⟨off, len, .vzeroall⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g,
        ⟨Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero,
          Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero,
          Vec256.zero, Vec256.zero⟩, cf, o, zf, false, false, m⟩,
       ⟨off, [], true⟩) := by rfl

def zeroCode : List UInt8 :=
  [0x48,0x89,0xf1,0x31,0xc0,0x88,0x07,0x48,0xff,0xc7,0x48,0xff,0xc9,0x75,0xf6,0x0f,
   0xae,0xf0,0x31,0xff,0x31,0xf6,0x31,0xd2,0x31,0xc9,0x45,0x31,0xc0,0x45,0x31,0xc9,
   0x45,0x31,0xd2,0x45,0x31,0xdb,0x31,0xc0,0xc3]

theorem zeroCode_is_rlib_slice :
    ((extractAllRlibFuncs currentX86RlibArchiveBytes)[15]?).map ElfFuncSlice.code = some zeroCode := by
  rw [currentX86_rlib_extracted_slices]; decide

theorem ctMemzeroX86_decodeOne_all :
    decodeX86Stream zeroCode = some ctCurrentMemzeroX86Prog ∧
    ctCurrentMemzeroX86Prog.all (fun d =>
      decodeX86One zeroCode d.offset == some d &&
      findInstrAtPc d.offset ctCurrentMemzeroX86Prog == some d) = true := by
  decide +kernel

def armZeroCode : List UInt8 :=
  [0x1f,0x14,0x00,0x38,0x21,0x04,0x00,0xf1,0xc1,0xff,0xff,0x54,
   0xbf,0x3b,0x03,0xd5,0xc0,0x03,0x5f,0xd6]

theorem armZeroCode_is_rlib_slice :
    ((extractAllRlibFuncs currentAarch64RlibArchiveBytes)[6]?).map ElfFuncSlice.code = some armZeroCode := by
  rw [currentAarch64_rlib_extracted_slices]; decide

theorem ctMemzeroArm_decodeOne_all :
    decodeArm64Stream armZeroCode = some ctMemzeroArmProg ∧
    ctMemzeroArmProg.all (fun d =>
      decodeArm64One armZeroCode d.offset == some d &&
      findInstrAtPc d.offset ctMemzeroArmProg == some d) = true := by
  decide +kernel

def eqBytesCode : List UInt8 :=
  [0x31,0xc0,0x48,0x89,0xd1,0x44,0x0f,0xb6,0x07,0x44,0x0f,0xb6,0x0e,0x45,0x31,0xc8,
   0x44,0x09,0xc0,0x48,0xff,0xc7,0x48,0xff,0xc6,0x48,0xff,0xc9,0x75,0xe7,0x83,0xe8,
   0x01,0xc1,0xe8,0x1f,0x45,0x31,0xc0,0x45,0x31,0xc9,0x31,0xff,0x31,0xf6,0x31,0xd2,
   0x31,0xc9,0x45,0x31,0xc0,0x45,0x31,0xc9,0x45,0x31,0xd2,0x45,0x31,0xdb,0xc3]

theorem eqBytesCode_is_rlib_slice :
    ((extractAllRlibFuncs currentX86RlibArchiveBytes)[14]?).map ElfFuncSlice.code = some eqBytesCode := by
  rw [currentX86_rlib_extracted_slices]; decide

theorem ctEqBytesX86_decodeOne_all :
    decodeX86Stream eqBytesCode = some ctCurrentEqBytesX86Prog ∧
    ctCurrentEqBytesX86Prog.all (fun d =>
      decodeX86One eqBytesCode d.offset == some d &&
      findInstrAtPc d.offset ctCurrentEqBytesX86Prog == some d) = true := by
  decide +kernel

def gfniShamirMacCode : List UInt8 :=
  [0x48,0xb8,0xce,0x78,0xbe,0x86,0x8a,0x0a,0x50,0x71,0xc4,0x61,0xf9,0x6e,0xf0,0xc4,
   0x42,0x7d,0x59,0xf6,0x48,0xb8,0x0c,0x70,0xa2,0x72,0xe0,0xf8,0xe4,0xa1,0xc4,0x61,
   0xf9,0x6e,0xf8,0xc4,0x42,0x7d,0x59,0xff,0xc5,0xf9,0x6e,0xda,0xc4,0xe2,0x7d,0x78,
   0xdb,0xc4,0xc3,0xe5,0xce,0xde,0x00,0xc5,0xfe,0x6f,0x06,0xc5,0xfe,0x6f,0x0f,0xc4,
   0xc3,0xfd,0xce,0xc6,0x00,0xc4,0xe2,0x7d,0xcf,0xd3,0xc4,0xc3,0xed,0xce,0xd7,0x00,
   0xc5,0xf5,0xef,0xca,0xc5,0xfe,0x7f,0x0f,0x48,0x83,0xc6,0x20,0x48,0x83,0xc7,0x20,
   0x48,0xff,0xc9,0x75,0xd2,0xc5,0xfd,0xef,0xc0,0xc5,0xf5,0xef,0xc9,0xc5,0xed,0xef,
   0xd2,0xc5,0xe5,0xef,0xdb,0xc4,0x41,0x0d,0xef,0xf6,0xc4,0x41,0x05,0xef,0xff,0x31,
   0xc0,0x31,0xd2,0xc5,0xfc,0x77,0xc5,0xf8,0x77,0x31,0xff,0x31,0xf6,0x31,0xd2,0x31,
   0xc9,0x45,0x31,0xc0,0x45,0x31,0xc9,0x45,0x31,0xd2,0x45,0x31,0xdb,0x31,0xc0,0xc3]

theorem gfniShamirMacCode_is_rlib_slice :
    ((extractAllRlibFuncs currentX86RlibArchiveBytes)[3]?).map ElfFuncSlice.code = some gfniShamirMacCode := by
  rw [currentX86_rlib_extracted_slices]; decide

def gfniShamirMacProg : List (DecodedInstr X86Instr) := [
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

theorem gfniShamirMac_decodeOne_all :
    decodeX86Stream gfniShamirMacCode = some gfniShamirMacProg ∧
    gfniShamirMacProg.all (fun d =>
      decodeX86One gfniShamirMacCode d.offset == some d &&
      findInstrAtPc d.offset gfniShamirMacProg == some d) = true := by
  decide +kernel

def vpclmulBdozMacCode : List UInt8 :=
  [0xc5,0xfd,0xef,0xc0,0xc5,0xf5,0xef,0xc9,0xc5,0xfe,0x6f,0x16,0xc5,0xfe,0x6f,0x1a,
   0xc4,0xe3,0x6d,0x44,0xe3,0x00,0xc4,0xe3,0x6d,0x44,0xeb,0x11,0xc4,0xe3,0x6d,0x44,
   0xf3,0x01,0xc4,0xe3,0x6d,0x44,0xfb,0x10,0xc5,0xcd,0xef,0xf7,0xc5,0xc5,0x73,0xfe,
   0x08,0xc5,0xcd,0x73,0xde,0x08,0xc5,0xdd,0xef,0xe7,0xc5,0xd5,0xef,0xee,0xc5,0xfd,
   0xef,0xc4,0xc5,0xf5,0xef,0xcd,0x48,0x83,0xc6,0x20,0x48,0x83,0xc2,0x20,0x48,0xff,
   0xc9,0x75,0xb5,0xb8,0x87,0x00,0x00,0x00,0xc4,0x61,0xf9,0x6e,0xc0,0xc4,0x42,0x7d,
   0x59,0xc0,0xc4,0xc3,0x75,0x44,0xe0,0x01,0xc5,0xd5,0x73,0xfc,0x08,0xc5,0xcd,0x73,
   0xdc,0x08,0xc5,0xfd,0xef,0xc5,0xc5,0xf5,0xef,0xce,0xc4,0xc3,0x75,0x44,0xe0,0x00,
   0xc5,0xfd,0xef,0xc4,0xc5,0xfe,0x7f,0x07,0xc5,0xfd,0xef,0xc0,0xc5,0xf5,0xef,0xc9,
   0xc5,0xed,0xef,0xd2,0xc5,0xe5,0xef,0xdb,0xc5,0xdd,0xef,0xe4,0xc5,0xd5,0xef,0xed,
   0xc5,0xcd,0xef,0xf6,0xc5,0xc5,0xef,0xff,0xc4,0x41,0x3d,0xef,0xc0,0x31,0xc0,0xc5,
   0xfc,0x77,0xc5,0xf8,0x77,0x31,0xff,0x31,0xf6,0x31,0xd2,0x31,0xc9,0x45,0x31,0xc0,
   0x45,0x31,0xc9,0x45,0x31,0xd2,0x45,0x31,0xdb,0x31,0xc0,0xc3]

theorem vpclmulBdozMacCode_is_rlib_slice :
    ((extractAllRlibFuncs currentX86RlibArchiveBytes)[6]?).map ElfFuncSlice.code = some vpclmulBdozMacCode := by
  rw [currentX86_rlib_extracted_slices]; decide

def vpclmulBdozMacProg : List (DecodedInstr X86Instr) := [
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

theorem vpclmulBdozMac_decodeOne_all :
    decodeX86Stream vpclmulBdozMacCode = some vpclmulBdozMacProg ∧
    vpclmulBdozMacProg.all (fun d =>
      decodeX86One vpclmulBdozMacCode d.offset == some d &&
      findInstrAtPc d.offset vpclmulBdozMacProg == some d) = true := by
  decide +kernel

theorem gfniShamirMacProg_eq : gfniShamirMacProg = [
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
] := by rfl
theorem vpclmulBdozMacProg_eq : vpclmulBdozMacProg = [
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
] := by rfl
end Qsag.SydTv
