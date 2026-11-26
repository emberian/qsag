module

public import Qsag.Math.Goldilocks
public import Qsag.Math.Gf2Pow128
public import Qsag.Oracle.Keccak
public import Qsag.Machine.ElfVerify
public import Qsag.Machine.ElfFixtureVerify
public import Qsag.Machine.McRefine
public import Qsag.Machine.SydTv
public import Qsag.Machine.Gf128ClmulLoopAgreement
import Qsag.Tactic.Prelude
public import Qsag.Machine.ElfFixtures
public import Qsag.Machine.ElfInvCerts
import Qsag.Tactic.AssuranceKit

public section

namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
  UInt64.instLawfulOrderOrd String.instLawfulEqOrd
  Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe
set_option autoImplicit false
set_option maxRecDepth 65536

/-! ## §1. Byte-Decoded `BitVec 64` Operational Value Semantics & Exact-Step `RET` Relation -/

/-- Canonical Goldilocks prime $p = 2^{64} - 2^{32} + 1 = 18446744069414584321$. -/
abbrev GOLDILOCKS_P : Nat := goldilocksPrime

theorem GOLDILOCKS_P_eq : GOLDILOCKS_P = 18446744069414584321 := rfl

/-- Concrete `x86_64` architectural state over `BitVec 64` general-purpose registers (`rax=0,
    rcx=1, rdx=2, rbx=3, rsp=4, rbp=5, rsi=6, rdi=7, r8..r15=8..15`) and `BitVec 64`-addressed
    byte memory. -/
structure X86BvState where
  pc : Nat
  gpr : Bank16 (BitVec 64)
  ymm : Bank16 Vec256
  cf : Bool
  ofFlag : Bool
  zf : Bool
  ymmDirty : Bool
  halted : Bool
  mem : BitVec 64 → UInt8

/-- Concrete `AArch64` architectural state over `BitVec 64` general-purpose registers (`x0..x30`,
    slot `31 = sp`/`xzr`) and `BitVec 64`-addressed byte memory. -/
structure Arm64BvState where
  pc : Nat
  gpr : Bank32 (BitVec 64)
  vec : Bank32 Vec128
  cf : Bool
  zf : Bool
  dit : Bool
  halted : Bool
  mem : BitVec 64 → UInt8

@[expose] def bank16ToU64 (b : Bank16 (BitVec 64)) : Bank16 UInt64 :=
  ⟨UInt64.ofBitVec b.r0, UInt64.ofBitVec b.r1, UInt64.ofBitVec b.r2, UInt64.ofBitVec b.r3,
   UInt64.ofBitVec b.r4, UInt64.ofBitVec b.r5, UInt64.ofBitVec b.r6, UInt64.ofBitVec b.r7,
   UInt64.ofBitVec b.r8, UInt64.ofBitVec b.r9, UInt64.ofBitVec b.r10, UInt64.ofBitVec b.r11,
   UInt64.ofBitVec b.r12, UInt64.ofBitVec b.r13, UInt64.ofBitVec b.r14, UInt64.ofBitVec b.r15⟩

@[expose] def bank16OfU64 (b : Bank16 UInt64) : Bank16 (BitVec 64) :=
  ⟨b.r0.toBitVec, b.r1.toBitVec, b.r2.toBitVec, b.r3.toBitVec,
   b.r4.toBitVec, b.r5.toBitVec, b.r6.toBitVec, b.r7.toBitVec,
   b.r8.toBitVec, b.r9.toBitVec, b.r10.toBitVec, b.r11.toBitVec,
   b.r12.toBitVec, b.r13.toBitVec, b.r14.toBitVec, b.r15.toBitVec⟩

@[expose] def bank32ToU64 (b : Bank32 (BitVec 64)) : Bank32 UInt64 :=
  ⟨bank16ToU64 b.lo, bank16ToU64 b.hi⟩

@[expose] def bank32OfU64 (b : Bank32 UInt64) : Bank32 (BitVec 64) :=
  ⟨bank16OfU64 b.lo, bank16OfU64 b.hi⟩

/-- Lossless embedding of `X86BvState` into `ElfBinaryVerify.X86State`. -/
@[expose] def X86BvState.toX86State (st : X86BvState) : X86State :=
  { pc := st.pc
    gpr := bank16ToU64 st.gpr
    ymm := st.ymm
    cf := st.cf
    ofFlag := st.ofFlag
    zf := st.zf
    ymmDirty := st.ymmDirty
    halted := st.halted
    mem := fun addr => st.mem addr.toBitVec }

/-- Lossless projection from `ElfBinaryVerify.X86State` into `X86BvState`. -/
@[expose] def X86BvState.ofX86State (s : X86State) : X86BvState :=
  { pc := s.pc
    gpr := bank16OfU64 s.gpr
    ymm := s.ymm
    cf := s.cf
    ofFlag := s.ofFlag
    zf := s.zf
    ymmDirty := s.ymmDirty
    halted := s.halted
    mem := fun addr => s.mem (UInt64.ofBitVec addr) }

/-- Lossless embedding of `Arm64BvState` into `ElfBinaryVerify.Arm64State`. -/
@[expose] def Arm64BvState.toArm64State (st : Arm64BvState) : Arm64State :=
  { pc := st.pc
    gpr := bank32ToU64 st.gpr
    vec := st.vec
    cf := st.cf
    zf := st.zf
    dit := st.dit
    halted := st.halted
    mem := fun addr => st.mem addr.toBitVec }

/-- Lossless projection from `ElfBinaryVerify.Arm64State` into `Arm64BvState`. -/
@[expose] def Arm64BvState.ofArm64State (s : Arm64State) : Arm64BvState :=
  { pc := s.pc
    gpr := bank32OfU64 s.gpr
    vec := s.vec
    cf := s.cf
    zf := s.zf
    dit := s.dit
    halted := s.halted
    mem := fun addr => s.mem (UInt64.ofBitVec addr) }

theorem X86BvState.ofX86State_toX86State (st : X86BvState) :
    X86BvState.ofX86State st.toX86State = st := by
  rcases st with ⟨pc, ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩,
    ymm, cf, ofFlag, zf, ymmDirty, halted, mem⟩
  simp [X86BvState.toX86State, X86BvState.ofX86State, bank16ToU64, bank16OfU64]

theorem X86BvState.toX86State_ofX86State (s : X86State) :
    (X86BvState.ofX86State s).toX86State = s := by
  rcases s with ⟨pc, ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15⟩,
    ymm, cf, ofFlag, zf, ymmDirty, halted, mem⟩
  simp [X86BvState.toX86State, X86BvState.ofX86State, bank16ToU64, bank16OfU64]

theorem Arm64BvState.ofArm64State_toArm64State (st : Arm64BvState) :
    Arm64BvState.ofArm64State st.toArm64State = st := by
  rcases st with ⟨pc, ⟨⟨l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15⟩,
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩⟩,
    vec, cf, zf, dit, halted, mem⟩
  simp [Arm64BvState.toArm64State, Arm64BvState.ofArm64State, bank32ToU64, bank32OfU64,
    bank16ToU64, bank16OfU64]

theorem Arm64BvState.toArm64State_ofArm64State (s : Arm64State) :
    (Arm64BvState.ofArm64State s).toArm64State = s := by
  rcases s with ⟨pc, ⟨⟨l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15⟩,
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩⟩,
    vec, cf, zf, dit, halted, mem⟩
  simp [Arm64BvState.toArm64State, Arm64BvState.ofArm64State, bank32ToU64, bank32OfU64,
    bank16ToU64, bank16OfU64]

theorem bank16OfU64_get (b : Bank16 UInt64) (i : Nat) (hi : i < 16) :
    (bank16OfU64 b).get i = (b.get i).toBitVec := by
  rcases b with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩
  match i, hi with
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl
  | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl | 7, _ => rfl
  | 8, _ => rfl | 9, _ => rfl | 10, _ => rfl | 11, _ => rfl
  | 12, _ => rfl | 13, _ => rfl | 14, _ => rfl | 15, _ => rfl
  | n + 16, h => exact absurd h (by omega)

theorem bank16ToU64_get (b : Bank16 (BitVec 64)) (i : Nat) (hi : i < 16) :
    (bank16ToU64 b).get i = UInt64.ofBitVec (b.get i) := by
  rcases b with ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩
  match i, hi with
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl
  | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl | 7, _ => rfl
  | 8, _ => rfl | 9, _ => rfl | 10, _ => rfl | 11, _ => rfl
  | 12, _ => rfl | 13, _ => rfl | 14, _ => rfl | 15, _ => rfl
  | n + 16, h => exact absurd h (by omega)

theorem bank32OfU64_get (b : Bank32 UInt64) (i : Nat) (hi : i < 32) :
    (bank32OfU64 b).get i = (b.get i).toBitVec := by
  rcases b with ⟨lo, hiB⟩
  unfold bank32OfU64 Bank32.get
  if h : i < 16 then
    rw [ite_eq_left h, ite_eq_left h]
    exact bank16OfU64_get lo i h
  else
    rw [ite_eq_right h, ite_eq_right h]
    exact bank16OfU64_get hiB (i - 16) (by omega)

theorem bank32ToU64_get (b : Bank32 (BitVec 64)) (i : Nat) (hi : i < 32) :
    (bank32ToU64 b).get i = UInt64.ofBitVec (b.get i) := by
  rcases b with ⟨lo, hiB⟩
  unfold bank32ToU64 Bank32.get
  if h : i < 16 then
    rw [ite_eq_left h, ite_eq_left h]
    exact bank16ToU64_get lo i h
  else
    rw [ite_eq_right h, ite_eq_right h]
    exact bank16ToU64_get hiB (i - 16) (by omega)

/-- System-V AMD64 ABI callee-saved GPR (`rbx=3, rbp=5, r12..r15=12..15`) and stack-pointer
    (`rsp=4`) preservation predicate over `BitVec 64` states. -/
def X86CalleeSavedPreserved (st st' : X86BvState) : Prop :=
  st'.gpr.get 3 = st.gpr.get 3 ∧
  st'.gpr.get 4 = st.gpr.get 4 + 8 ∧
  st'.gpr.get 5 = st.gpr.get 5 ∧
  st'.gpr.get 12 = st.gpr.get 12 ∧
  st'.gpr.get 13 = st.gpr.get 13 ∧
  st'.gpr.get 14 = st.gpr.get 14 ∧
  st'.gpr.get 15 = st.gpr.get 15

/-- AAPCS64 ABI callee-saved GPR (`x19..x29`, link register `x30`, slot `31 = sp`/`xzr`) and
    callee-saved NEON (`v8..v15`) preservation predicate over `BitVec 64` states. -/
def Arm64CalleeSavedPreserved (st st' : Arm64BvState) : Prop :=
  (∀ r : Nat, 19 ≤ r → r ≤ 31 → st'.gpr.get r = st.gpr.get r) ∧
  (∀ v : Nat, 8 ≤ v → v ≤ 15 → st'.vec.get v = st.vec.get v)

theorem u64_roundtrip (x : BitVec 64) : (UInt64.ofBitVec x).toBitVec = x :=
  UInt64.toBitVec_ofBitVec x

theorem mem_roundtrip (mem : BitVec 64 → UInt8) :
    (fun addr => mem (UInt64.ofBitVec addr).toBitVec) = mem := by
  funext addr
  exact congrArg mem (UInt64.toBitVec_ofBitVec addr)

theorem bank16_roundtrip (hi : Bank16 (BitVec 64)) :
    bank16OfU64 (bank16ToU64 hi) = hi := by
  rcases hi with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  simp only [bank16OfU64, bank16ToU64, UInt64.toBitVec_ofBitVec]

theorem b32get_0 {α : Type} (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : α)
    (hi : Bank16 α) :
    Bank32.get ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩ 0 = r0 := rfl
theorem b32get_1 {α : Type} (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : α)
    (hi : Bank16 α) :
    Bank32.get ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩ 1 = r1 := rfl
theorem b32get_2 {α : Type} (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : α)
    (hi : Bank16 α) :
    Bank32.get ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩ 2 = r2 := rfl

attribute [local simp]
  X86BvState.ofX86State Arm64BvState.ofArm64State bank16OfU64 bank32OfU64
  b16get_0 b16get_1 b16get_2 b16get_3 b16get_4 b16get_5 b16get_6 b16get_7
  b16get_8 b16get_9 b16get_10 b16get_11 b16get_12 b16get_13 b16get_14 b16get_15
  b32get_0 b32get_1 b32get_2

/-- Halted-pc transport for an x86 `ret`: the final pc is the return address loaded from the
    entry stack slot of the final memory. -/
theorem x86_ret_pc_of_roundtrip (s1 : X86State) (st : X86BvState)
    (hpc : s1.pc = (readMem64 s1.mem (st.toX86State.gpr.get 4)).toNat) :
    (X86BvState.ofX86State s1).pc =
      (readMem64 (X86BvState.ofX86State s1).toX86State.mem (st.toX86State.gpr.get 4)).toNat := by
  rw [X86BvState.toX86State_ofX86State]
  exact hpc

theorem x86_callee_saved_of_roundtrip
    {pc1 : Nat} {r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64}
    {u0 u1 u2 u6 u7 u8 u9 u10 u11 : UInt64}
    {y0 y1 : Bank16 Vec256} {cf0 o0 zf0 dy0 cf1 o1 zf1 dy1 h1 : Bool}
    {mem0 : BitVec 64 → UInt8} {mem1 : UInt64 → UInt8} :
    X86CalleeSavedPreserved
      ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        y0, cf0, o0, zf0, dy0, false, mem0⟩
      (X86BvState.ofX86State
        ⟨pc1, ⟨u0, u1, u2, UInt64.ofBitVec r3, UInt64.ofBitVec r4 + 8, UInt64.ofBitVec r5,
          u6, u7, u8, u9, u10, u11,
          UInt64.ofBitVec r12, UInt64.ofBitVec r13, UInt64.ofBitVec r14, UInt64.ofBitVec r15⟩,
          y1, cf1, o1, zf1, dy1, h1, mem1⟩) :=
  ⟨u64_roundtrip r3, rfl, u64_roundtrip r5,
   u64_roundtrip r12, u64_roundtrip r13, u64_roundtrip r14, u64_roundtrip r15⟩

theorem arm64_callee_saved_of_hi_vec
    {pc0 pc1 : Nat} {lo0 : Bank16 (BitVec 64)} {lo1 : Bank16 UInt64}
    {hi : Bank16 (BitVec 64)} {v : Bank32 Vec128}
    {cf0 zf0 dit0 h0 cf1 zf1 dit1 h1 : Bool}
    {mem0 : BitVec 64 → UInt8} {mem1 : UInt64 → UInt8} :
    Arm64CalleeSavedPreserved
      ⟨pc0, ⟨lo0, hi⟩, v, cf0, zf0, dit0, h0, mem0⟩
      (Arm64BvState.ofArm64State ⟨pc1, ⟨lo1, bank16ToU64 hi⟩, v, cf1, zf1, dit1, h1, mem1⟩) := by
  refine ⟨fun r hr1 _ => ?_, fun _ _ _ => rfl⟩
  have hNot16 : ¬ r < 16 := by omega
  simp only [Arm64BvState.ofArm64State, bank32OfU64, bank16_roundtrip, Bank32.get, ite_eq_right hNot16]

/-- Decode a raw `x86_64` `.text` machine-code byte slice into offset-tagged instructions. -/
@[expose] def decodeX86Slice (code : List UInt8) : Option (List (DecodedInstr X86Instr)) :=
  decodeX86Stream code

/-- Decode a `ByteArray` `x86_64` `.text` slice into offset-tagged instructions. -/
def decodeX86ByteArray (code : ByteArray) : Option (List (DecodedInstr X86Instr)) :=
  decodeX86Slice code.toList

/-- Decode a raw `AArch64` `.text` machine-code byte slice into offset-tagged instructions. -/
@[expose] def decodeArm64Slice (code : List UInt8) : Option (List (DecodedInstr Arm64Instr)) :=
  decodeArm64Stream code

/-- Decode a `ByteArray` `AArch64` `.text` slice into offset-tagged instructions. -/
def decodeArm64ByteArray (code : ByteArray) : Option (List (DecodedInstr Arm64Instr)) :=
  decodeArm64Slice code.toList

/-- Decode and execute a raw `x86_64` byte slice for `fuel` steps over `BitVec 64` state `st`,
    returning `(finalState, leakageTrace)` iff byte decoding succeeds. -/
@[expose] def execDecodedX86 (code : List UInt8) (fuel : Nat) (st : X86BvState) :
    Option (X86BvState × List StepObs) :=
  match decodeX86Slice code with
  | none => none
  | some prog =>
    let (s', trace) := runX86 prog fuel st.toX86State
    some (X86BvState.ofX86State s', trace)

/-- Decode and execute a raw `AArch64` byte slice for `fuel` steps over `BitVec 64` state `st`,
    returning `(finalState, leakageTrace)` iff byte decoding succeeds. -/
@[expose] def execDecodedArm64 (code : List UInt8) (fuel : Nat) (st : Arm64BvState) :
    Option (Arm64BvState × List StepObs) :=
  match decodeArm64Slice code with
  | none => none
  | some prog =>
    let (s', trace) := runArm64 prog fuel st.toArm64State
    some (Arm64BvState.ofArm64State s', trace)

theorem execDecodedX86_of_dec {code : List UInt8} {prog : List (DecodedInstr X86Instr)}
    (hDec : decodeX86Slice code = some prog) (fuel : Nat) (st : X86BvState) :
    execDecodedX86 code fuel st =
      some (X86BvState.ofX86State (runX86 prog fuel st.toX86State).1,
            (runX86 prog fuel st.toX86State).2) := by
  simp [execDecodedX86, hDec]

theorem execDecodedArm64_of_dec {code : List UInt8} {prog : List (DecodedInstr Arm64Instr)}
    (hDec : decodeArm64Slice code = some prog) (fuel : Nat) (st : Arm64BvState) :
    execDecodedArm64 code fuel st =
      some (Arm64BvState.ofArm64State (runArm64 prog fuel st.toArm64State).1,
            (runArm64 prog fuel st.toArm64State).2) := by
  simp [execDecodedArm64, hDec]

/-- Exact-step `x86_64` execution relation tracking both final state and exact trace step count. -/
def ExecReachesX86 (prog : List (DecodedInstr X86Instr)) (n : Nat) (s s' : X86State) : Prop :=
  ∀ extra : Nat,
    (runX86 prog (n + extra) s).1 = (runX86 prog extra s').1 ∧
    (runX86 prog (n + extra) s).2.length = n + (runX86 prog extra s').2.length

/-- Exact-step `AArch64` execution relation tracking both final state and exact trace step count. -/
def ExecReachesArm64 (prog : List (DecodedInstr Arm64Instr)) (n : Nat) (s s' : Arm64State) : Prop :=
  ∀ extra : Nat,
    (runArm64 prog (n + extra) s).1 = (runArm64 prog extra s').1 ∧
    (runArm64 prog (n + extra) s).2.length = n + (runArm64 prog extra s').2.length

theorem ExecReachesX86.run {prog : List (DecodedInstr X86Instr)} {n : Nat} {s t : X86State}
    (h : ExecReachesX86 prog n s t) (extra : Nat) :
    (runX86 prog (n + extra) s).1 = (runX86 prog extra t).1 ∧
    (runX86 prog (n + extra) s).2.length = n + (runX86 prog extra t).2.length :=
  h extra

theorem ExecReachesX86_zero (prog : List (DecodedInstr X86Instr)) (s : X86State) :
    ExecReachesX86 prog 0 s s := by
  intro extra
  simp

theorem runX86_step_pair (prog : List (DecodedInstr X86Instr)) (fuel : Nat) (s : X86State)
    (d : DecodedInstr X86Instr) (hh : s.halted = false) (hf : findInstrAtPc s.pc prog = some d) :
    runX86 prog (fuel + 1) s =
      ((runX86 prog fuel (stepX86 d s).1).1,
       (stepX86 d s).2 :: (runX86 prog fuel (stepX86 d s).1).2) := by
  simp [runX86, hh, hf]

theorem ExecReachesX86_step {prog : List (DecodedInstr X86Instr)} {s s1 : X86State}
    {d : DecodedInstr X86Instr}
    (hh : s.halted = false) (hf : findInstrAtPc s.pc prog = some d)
    (hs1 : (stepX86 d s).1 = s1) :
    ExecReachesX86 prog 1 s s1 := by
  intro extra
  rw [Nat.add_comm 1 extra, runX86_step_pair prog extra s d hh hf, hs1]
  exact ⟨rfl, by simp [Nat.add_comm]⟩

theorem ExecReachesX86_cons {prog : List (DecodedInstr X86Instr)} {k : Nat}
    {s s1 s2 : X86State} {d : DecodedInstr X86Instr}
    (hh : s.halted = false) (hf : findInstrAtPc s.pc prog = some d)
    (hs1 : (stepX86 d s).1 = s1) (hRest : ExecReachesX86 prog k s1 s2) :
    ExecReachesX86 prog (k + 1) s s2 := by
  intro extra
  rw [Nat.add_right_comm k 1 extra, runX86_step_pair prog (k + extra) s d hh hf, hs1]
  have ⟨e, l⟩ := hRest extra
  exact ⟨e, by simp [l]; omega⟩

theorem ExecReachesX86_step_ex {prog : List (DecodedInstr X86Instr)} {k : Nat}
    {s s1 : X86State} {P : X86State → Prop} {d : DecodedInstr X86Instr}
    (hh : s.halted = false) (hf : findInstrAtPc s.pc prog = some d)
    (hs1 : (stepX86 d s).1 = s1)
    (hNext : ∃ s2, ExecReachesX86 prog k s1 s2 ∧ P s2) :
    ∃ s2, ExecReachesX86 prog (k + 1) s s2 ∧ P s2 := by
  rcases hNext with ⟨s2, hr, hp⟩
  exact ⟨s2, ExecReachesX86_cons hh hf hs1 hr, hp⟩

theorem ExecReachesX86_trans {prog : List (DecodedInstr X86Instr)} {m n : Nat}
    {s0 s1 s2 : X86State}
    (h1 : ExecReachesX86 prog m s0 s1) (h2 : ExecReachesX86 prog n s1 s2) :
    ExecReachesX86 prog (m + n) s0 s2 := by
  intro extra
  rw [Nat.add_assoc]
  have ⟨e1, l1⟩ := h1 (n + extra)
  have ⟨e2, l2⟩ := h2 extra
  exact ⟨e1.trans e2, by rw [l1, l2, Nat.add_assoc]⟩

theorem runX86_halted_snd (prog : List (DecodedInstr X86Instr)) (fuel : Nat) (s : X86State)
    (hh : s.halted = true) : (runX86 prog fuel s).2 = [] := by
  cases fuel with
  | zero => rfl
  | succ k => simp [runX86, hh]

theorem ExecReachesX86_ret {prog : List (DecodedInstr X86Instr)} {k retPc retLen : Nat}
    {s sRet : X86State}
    (hPre : ExecReachesX86 prog k s sRet)
    (hh : sRet.halted = false)
    (hf : findInstrAtPc sRet.pc prog = some ⟨retPc, retLen, .ret⟩) :
    (runX86 prog k s).1 = sRet ∧
    (runX86 prog k s).1.halted = false ∧
    ∀ extra : Nat,
      (runX86 prog (k + 1 + extra) s).1 = { sRet with pc := (readMem64 sRet.mem (sRet.gpr.get 4)).toNat, gpr := sRet.gpr.set 4 (sRet.gpr.get 4 + 8), halted := true } ∧
      (runX86 prog (k + 1 + extra) s).2.length = k + 1 := by
  have h0 := (hPre 0).1
  rw [Nat.add_zero] at h0
  have hs0 : (runX86 prog 0 sRet).1 = sRet := rfl
  have hAtK : (runX86 prog k s).1 = sRet := h0.trans hs0
  have hRetStep : ExecReachesX86 prog 1 sRet { sRet with pc := (readMem64 sRet.mem (sRet.gpr.get 4)).toNat, gpr := sRet.gpr.set 4 (sRet.gpr.get 4 + 8), halted := true } :=
    ExecReachesX86_step hh hf rfl
  have hFull := ExecReachesX86_trans hPre hRetStep
  refine ⟨hAtK, hAtK.symm ▸ hh, fun extra => ?_⟩
  have ⟨ef, lf⟩ := hFull extra
  have hHaltFst : (runX86 prog extra { sRet with pc := (readMem64 sRet.mem (sRet.gpr.get 4)).toNat, gpr := sRet.gpr.set 4 (sRet.gpr.get 4 + 8), halted := true }).1 =
      { sRet with pc := (readMem64 sRet.mem (sRet.gpr.get 4)).toNat, gpr := sRet.gpr.set 4 (sRet.gpr.get 4 + 8), halted := true } := runX86_halted_fst prog extra _ rfl
  have hHaltSnd : (runX86 prog extra { sRet with pc := (readMem64 sRet.mem (sRet.gpr.get 4)).toNat, gpr := sRet.gpr.set 4 (sRet.gpr.get 4 + 8), halted := true }).2 = [] :=
    runX86_halted_snd prog extra _ rfl
  exact ⟨ef.trans hHaltFst, by rw [lf, hHaltSnd]; simp⟩

theorem ExecReachesArm64.run {prog : List (DecodedInstr Arm64Instr)} {n : Nat} {s t : Arm64State}
    (h : ExecReachesArm64 prog n s t) (extra : Nat) :
    (runArm64 prog (n + extra) s).1 = (runArm64 prog extra t).1 ∧
    (runArm64 prog (n + extra) s).2.length = n + (runArm64 prog extra t).2.length :=
  h extra

theorem ExecReachesArm64_zero (prog : List (DecodedInstr Arm64Instr)) (s : Arm64State) :
    ExecReachesArm64 prog 0 s s := by
  intro extra
  simp

theorem runArm64_step_pair (prog : List (DecodedInstr Arm64Instr)) (fuel : Nat) (s : Arm64State)
    (d : DecodedInstr Arm64Instr) (hh : s.halted = false) (hf : findInstrAtPc s.pc prog = some d) :
    runArm64 prog (fuel + 1) s =
      ((runArm64 prog fuel (stepArm64 d s).1).1,
       (stepArm64 d s).2 :: (runArm64 prog fuel (stepArm64 d s).1).2) := by
  simp [runArm64, hh, hf]

theorem ExecReachesArm64_step {prog : List (DecodedInstr Arm64Instr)} {s s1 : Arm64State}
    {d : DecodedInstr Arm64Instr}
    (hh : s.halted = false) (hf : findInstrAtPc s.pc prog = some d)
    (hs1 : (stepArm64 d s).1 = s1) :
    ExecReachesArm64 prog 1 s s1 := by
  intro extra
  rw [Nat.add_comm 1 extra, runArm64_step_pair prog extra s d hh hf, hs1]
  exact ⟨rfl, by simp [Nat.add_comm]⟩

theorem ExecReachesArm64_cons {prog : List (DecodedInstr Arm64Instr)} {k : Nat}
    {s s1 s2 : Arm64State} {d : DecodedInstr Arm64Instr}
    (hh : s.halted = false) (hf : findInstrAtPc s.pc prog = some d)
    (hs1 : (stepArm64 d s).1 = s1) (hRest : ExecReachesArm64 prog k s1 s2) :
    ExecReachesArm64 prog (k + 1) s s2 := by
  intro extra
  rw [Nat.add_right_comm k 1 extra, runArm64_step_pair prog (k + extra) s d hh hf, hs1]
  have ⟨e, l⟩ := hRest extra
  exact ⟨e, by simp [l]; omega⟩

theorem ExecReachesArm64_step_ex {prog : List (DecodedInstr Arm64Instr)} {k : Nat}
    {s s1 : Arm64State} {P : Arm64State → Prop} {d : DecodedInstr Arm64Instr}
    (hh : s.halted = false) (hf : findInstrAtPc s.pc prog = some d)
    (hs1 : (stepArm64 d s).1 = s1)
    (hNext : ∃ s2, ExecReachesArm64 prog k s1 s2 ∧ P s2) :
    ∃ s2, ExecReachesArm64 prog (k + 1) s s2 ∧ P s2 := by
  rcases hNext with ⟨s2, hr, hp⟩
  exact ⟨s2, ExecReachesArm64_cons hh hf hs1 hr, hp⟩

theorem ExecReachesArm64_trans {prog : List (DecodedInstr Arm64Instr)} {m n : Nat}
    {s0 s1 s2 : Arm64State}
    (h1 : ExecReachesArm64 prog m s0 s1) (h2 : ExecReachesArm64 prog n s1 s2) :
    ExecReachesArm64 prog (m + n) s0 s2 := by
  intro extra
  rw [Nat.add_assoc]
  have ⟨e1, l1⟩ := h1 (n + extra)
  have ⟨e2, l2⟩ := h2 extra
  exact ⟨e1.trans e2, by rw [l1, l2, Nat.add_assoc]⟩

theorem runArm64_halted_snd (prog : List (DecodedInstr Arm64Instr)) (fuel : Nat) (s : Arm64State)
    (hh : s.halted = true) : (runArm64 prog fuel s).2 = [] := by
  cases fuel with
  | zero => rfl
  | succ k => simp [runArm64, hh]

theorem ExecReachesArm64_ret {prog : List (DecodedInstr Arm64Instr)} {k retPc retLen : Nat}
    {s sRet : Arm64State}
    (hPre : ExecReachesArm64 prog k s sRet)
    (hh : sRet.halted = false)
    (hf : findInstrAtPc sRet.pc prog = some ⟨retPc, retLen, .ret⟩) :
    (runArm64 prog k s).1 = sRet ∧
    (runArm64 prog k s).1.halted = false ∧
    ∀ extra : Nat,
      (runArm64 prog (k + 1 + extra) s).1 = { sRet with halted := true } ∧
      (runArm64 prog (k + 1 + extra) s).2.length = k + 1 := by
  have h0 := (hPre 0).1
  rw [Nat.add_zero] at h0
  have hs0 : (runArm64 prog 0 sRet).1 = sRet := rfl
  have hAtK : (runArm64 prog k s).1 = sRet := h0.trans hs0
  have hRetStep : ExecReachesArm64 prog 1 sRet { sRet with halted := true } :=
    ExecReachesArm64_step hh hf rfl
  have hFull := ExecReachesArm64_trans hPre hRetStep
  refine ⟨hAtK, hAtK.symm ▸ hh, fun extra => ?_⟩
  have ⟨ef, lf⟩ := hFull extra
  have hHaltFst : (runArm64 prog extra { sRet with halted := true }).1 =
      { sRet with halted := true } := runArm64_halted_fst prog extra _ rfl
  have hHaltSnd : (runArm64 prog extra { sRet with halted := true }).2 = [] :=
    runArm64_halted_snd prog extra _ rfl
  exact ⟨ef.trans hHaltFst, by rw [lf, hHaltSnd]; simp⟩

theorem execDecodedX86_ret_of_reaches {code : List UInt8} {prog : List (DecodedInstr X86Instr)}
    {k retPc retLen pc1 : Nat} (st : X86BvState) {s0 : X86State}
    {gpr1 : Bank16 UInt64} {ymm1 : Bank16 Vec256} {cf1 o1 zf1 dy1 : Bool} {mem1 : UInt64 → UInt8}
    (hDec : decodeX86Slice code = some prog)
    (hSt : st.toX86State = s0)
    (hPre : ExecReachesX86 prog k s0 ⟨pc1, gpr1, ymm1, cf1, o1, zf1, dy1, false, mem1⟩)
    (hh : (⟨pc1, gpr1, ymm1, cf1, o1, zf1, dy1, false, mem1⟩ : X86State).halted = false)
    (hf : findInstrAtPc pc1 prog = some ⟨retPc, retLen, .ret⟩) :
    (∃ stPre trPre, execDecodedX86 code k st = some (stPre, trPre) ∧ stPre.halted = false) ∧
    ∀ extra : Nat, ∃ tr,
      execDecodedX86 code ((k + 1) + extra) st =
        some (X86BvState.ofX86State ⟨(readMem64 mem1 (gpr1.get 4)).toNat, gpr1.set 4 (gpr1.get 4 + 8), ymm1, cf1, o1, zf1, dy1, true, mem1⟩, tr) ∧
      tr.length = k + 1 := by
  subst hSt
  have ⟨_, hNotHalt, hPost⟩ := ExecReachesX86_ret hPre hh hf
  refine ⟨⟨_, _, execDecodedX86_of_dec hDec k st, ?_⟩, fun extra => ?_⟩
  · simp [X86BvState.ofX86State, hNotHalt]
  · obtain ⟨hS, hL⟩ := hPost extra
    refine ⟨_, ?_, hL⟩
    rw [execDecodedX86_of_dec hDec ((k + 1) + extra) st, hS]

theorem execDecodedArm64_ret_of_reaches {code : List UInt8} {prog : List (DecodedInstr Arm64Instr)}
    {k retPc retLen pc1 : Nat} (st : Arm64BvState) {s0 : Arm64State}
    {gpr1 : Bank32 UInt64} {vec1 : Bank32 Vec128} {cf1 zf1 dit1 : Bool} {mem1 : UInt64 → UInt8}
    (hDec : decodeArm64Slice code = some prog)
    (hSt : st.toArm64State = s0)
    (hPre : ExecReachesArm64 prog k s0 ⟨pc1, gpr1, vec1, cf1, zf1, dit1, false, mem1⟩)
    (hh : (⟨pc1, gpr1, vec1, cf1, zf1, dit1, false, mem1⟩ : Arm64State).halted = false)
    (hf : findInstrAtPc pc1 prog = some ⟨retPc, retLen, .ret⟩) :
    (∃ stPre trPre, execDecodedArm64 code k st = some (stPre, trPre) ∧ stPre.halted = false) ∧
    ∀ extra : Nat, ∃ tr,
      execDecodedArm64 code ((k + 1) + extra) st =
        some (Arm64BvState.ofArm64State ⟨pc1, gpr1, vec1, cf1, zf1, dit1, true, mem1⟩, tr) ∧
      tr.length = k + 1 := by
  subst hSt
  have ⟨_, hNotHalt, hPost⟩ := ExecReachesArm64_ret hPre hh hf
  refine ⟨⟨_, _, execDecodedArm64_of_dec hDec k st, ?_⟩, fun extra => ?_⟩
  · simp [Arm64BvState.ofArm64State, hNotHalt]
  · obtain ⟨hS, hL⟩ := hPost extra
    refine ⟨_, ?_, hL⟩
    rw [execDecodedArm64_of_dec hDec ((k + 1) + extra) st, hS]


/-- Lightweight inductive multi-step `x86_64` execution relation for compact kernel proof terms. -/
inductive StepsX86 (prog : List (DecodedInstr X86Instr)) : Nat → X86State → X86State → Prop
  | zero (s : X86State) : StepsX86 prog 0 s s
  | cons {k : Nat} {s s1 s2 : X86State} {d : DecodedInstr X86Instr} :
      s.halted = false → findInstrAtPc s.pc prog = some d →
      (stepX86 d s).1 = s1 → StepsX86 prog k s1 s2 →
      StepsX86 prog (k + 1) s s2

theorem StepsX86.toExecReaches {prog : List (DecodedInstr X86Instr)} {n : Nat} {s s' : X86State}
    (h : StepsX86 prog n s s') : ExecReachesX86 prog n s s' := by
  induction h with
  | zero s => exact ExecReachesX86_zero prog s
  | cons hh hf hs1 _ ih => exact ExecReachesX86_cons hh hf hs1 ih

theorem StepsX86_step_ex {prog : List (DecodedInstr X86Instr)} {k : Nat}
    {s s1 : X86State} {P : X86State → Prop} {d : DecodedInstr X86Instr}
    (hh : s.halted = false) (hf : findInstrAtPc s.pc prog = some d)
    (hs1 : (stepX86 d s).1 = s1)
    (hNext : ∃ s2, StepsX86 prog k s1 s2 ∧ P s2) :
    ∃ s2, StepsX86 prog (k + 1) s s2 ∧ P s2 := by
  rcases hNext with ⟨s2, hr, hp⟩
  exact ⟨s2, StepsX86.cons hh hf hs1 hr, hp⟩

/-- Lightweight inductive multi-step `AArch64` execution relation for compact kernel proof terms. -/
inductive StepsArm64 (prog : List (DecodedInstr Arm64Instr)) : Nat → Arm64State → Arm64State → Prop
  | zero (s : Arm64State) : StepsArm64 prog 0 s s
  | cons {k : Nat} {s s1 s2 : Arm64State} {d : DecodedInstr Arm64Instr} :
      s.halted = false → findInstrAtPc s.pc prog = some d →
      (stepArm64 d s).1 = s1 → StepsArm64 prog k s1 s2 →
      StepsArm64 prog (k + 1) s s2

theorem StepsArm64.toExecReaches {prog : List (DecodedInstr Arm64Instr)} {n : Nat} {s s' : Arm64State}
    (h : StepsArm64 prog n s s') : ExecReachesArm64 prog n s s' := by
  induction h with
  | zero s => exact ExecReachesArm64_zero prog s
  | cons hh hf hs1 _ ih => exact ExecReachesArm64_cons hh hf hs1 ih

theorem StepsArm64_step_ex {prog : List (DecodedInstr Arm64Instr)} {k : Nat}
    {s s1 : Arm64State} {P : Arm64State → Prop} {d : DecodedInstr Arm64Instr}
    (hh : s.halted = false) (hf : findInstrAtPc s.pc prog = some d)
    (hs1 : (stepArm64 d s).1 = s1)
    (hNext : ∃ s2, StepsArm64 prog k s1 s2 ∧ P s2) :
    ∃ s2, StepsArm64 prog (k + 1) s s2 ∧ P s2 := by
  rcases hNext with ⟨s2, hr, hp⟩
  exact ⟨s2, StepsArm64.cons hh hf hs1 hr, hp⟩

/-! ## §2. Archive-to-Member `ELF64` Provenance & Relocatable Object Builder -/

def hasElemString (s : String) : List String → Bool
  | [] => false
  | x :: xs => (x == s) || hasElemString s xs

def allDistinctStrings : List String → Bool
  | [] => true
  | x :: xs => !hasElemString x xs && allDistinctStrings xs

private theorem hasElemString_mem {s : String} {xs : List String} (h : s ∈ xs) :
    hasElemString s xs = true := by
  induction xs with
  | nil => cases h
  | cons x rest ih =>
    unfold hasElemString
    rcases List.mem_cons.mp h with rfl | hm
    · simp
    · simp [ih hm]

private theorem hasElemString_append (s : String) (xs ys : List String) :
    hasElemString s (xs ++ ys) = (hasElemString s xs || hasElemString s ys) := by
  induction xs with
  | nil => simp [hasElemString]
  | cons x rest ih =>
    simp only [List.cons_append, hasElemString, ih, Bool.or_assoc]

private theorem allDistinctStrings_append_left {xs ys : List String}
    (h : allDistinctStrings (xs ++ ys) = true) : allDistinctStrings xs = true := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [List.cons_append, allDistinctStrings, Bool.and_eq_true, Bool.not_eq_true',
      hasElemString_append, Bool.or_eq_false_iff] at h ⊢
    exact ⟨h.1.1, ih h.2⟩

private theorem allDistinctStrings_append_right {xs ys : List String}
    (h : allDistinctStrings (xs ++ ys) = true) : allDistinctStrings ys = true := by
  induction xs with
  | nil => exact h
  | cons x rest ih =>
    simp only [List.cons_append, allDistinctStrings, Bool.and_eq_true] at h
    exact ih h.2

private theorem find_slice_unique_of_distinct {fs : List ElfFuncSlice} {slice : ElfFuncSlice}
    (hDist : allDistinctStrings (fs.map ElfFuncSlice.name) = true)
    (hMem : slice ∈ fs) :
    fs.find? (fun s => s.name == slice.name) = some slice := by
  induction fs with
  | nil => cases hMem
  | cons y ys ih =>
    simp only [List.map_cons, allDistinctStrings, Bool.and_eq_true, Bool.not_eq_true'] at hDist
    rcases List.mem_cons.mp hMem with rfl | hTail
    · simp [List.find?]
    · have hNameIn : slice.name ∈ ys.map ElfFuncSlice.name := List.mem_map_of_mem hTail
      have hHas : hasElemString slice.name (ys.map ElfFuncSlice.name) = true :=
        hasElemString_mem hNameIn
      have hNe : (y.name == slice.name) = false := by
        cases hEq : (y.name == slice.name) with
        | false => rfl
        | true =>
          have hEq' : y.name = slice.name := beq_iff_eq.mp hEq
          rw [hEq', hHas] at hDist
          cases hDist.1
      simp only [List.find?, hNe, ih hDist.2 hTail]

private def rlibFoldStep (acc : List ElfFuncSlice) (m : ArMember) : List ElfFuncSlice :=
  if m.payload.slice 0 4 == elfMagicBytes then
    match extractAllElfFuncs m.payload with
    | some fs => acc ++ fs
    | none => acc
  else acc

private theorem foldl_rlibFoldStep_suffix (ms : List ArMember) (acc : List ElfFuncSlice) :
    ∃ suf, ms.foldl rlibFoldStep acc = acc ++ suf := by
  induction ms generalizing acc with
  | nil => exact ⟨[], by simp⟩
  | cons m rest ih =>
    simp only [List.foldl_cons, rlibFoldStep]
    cases hc : (m.payload.slice 0 4 == elfMagicBytes) with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih acc
    | true =>
      simp only [↓reduceIte]
      cases hFs : extractAllElfFuncs m.payload with
      | none => exact ih acc
      | some fs =>
        obtain ⟨suf, hSuf⟩ := ih (acc ++ fs)
        exact ⟨fs ++ suf, by rw [hSuf, List.append_assoc]⟩

private theorem foldl_rlibFoldStep_mem_origin (ms : List ArMember) (acc : List ElfFuncSlice)
    (slice : ElfFuncSlice) (hMem : slice ∈ ms.foldl rlibFoldStep acc) :
    slice ∈ acc ∨
    ∃ m ∈ ms, ∃ fs pre suf,
      extractAllElfFuncs m.payload = some fs ∧
      slice ∈ fs ∧
      ms.foldl rlibFoldStep acc = pre ++ fs ++ suf := by
  induction ms generalizing acc with
  | nil => exact Or.inl hMem
  | cons m rest ih =>
    simp only [List.foldl_cons] at hMem ⊢
    rcases ih (rlibFoldStep acc m) hMem with hHere | ⟨m', hm', fs, pre, suf, hExt, hIn, hEq⟩
    · simp only [rlibFoldStep] at hHere ⊢
      cases hc : (m.payload.slice 0 4 == elfMagicBytes) with
      | false =>
        simp only [hc, Bool.false_eq_true, ↓reduceIte] at hHere
        exact Or.inl hHere
      | true =>
        simp only [hc, ↓reduceIte] at hHere ⊢
        cases hFs : extractAllElfFuncs m.payload with
        | none =>
          simp only [hFs] at hHere
          exact Or.inl hHere
        | some fs =>
          simp only [hFs] at hHere ⊢
          rcases List.mem_append.mp hHere with hA | hFsMem
          · exact Or.inl hA
          · obtain ⟨suf, hSuf⟩ := foldl_rlibFoldStep_suffix rest (acc ++ fs)
            exact Or.inr ⟨m, List.mem_cons_self, fs, acc, suf, hFs, hFsMem, hSuf⟩
    · exact Or.inr ⟨m', List.mem_cons_of_mem m hm', fs, pre, suf, hExt, hIn, hEq⟩

/-- Constructive archive-to-`ELF64`-member soundness: any symbol extracted by
    `extractRlibFuncBytes` from an archive with distinct exported symbol names originates from a
    concrete `ArMember` `m ∈ parseArArchive rlib` satisfying `ArPayloadOk rlib m` and
    `extractElfFuncBytes m.payload symName = some slice`, enabling direct application of
    `checkElfFuncThreeWayNI_sound` on `m.payload`! -/
theorem extractRlibFuncBytes_member_ni_sound {rlib : Bytes} {symName : String}
    {slice : ElfFuncSlice} {c : FuncContract}
    (hDist : allDistinctStrings ((extractAllRlibFuncs rlib).map ElfFuncSlice.name) = true)
    (hExt : extractRlibFuncBytes rlib symName = some slice)
    (hSliceNI : checkElfSliceThreeWayNI slice c = true) :
    ∃ m ∈ parseArArchive rlib,
      ArPayloadOk rlib m ∧
      extractElfFuncBytes m.payload symName = some slice ∧
      checkElfFuncThreeWayNI m.payload symName c = true ∧
      ElfSliceOk m.payload slice ∧
      ElfSliceThreeWayNISafe slice c := by
  unfold extractRlibFuncBytes at hExt
  have hInAll : slice ∈ extractAllRlibFuncs rlib := List.mem_of_find?_eq_some hExt
  have hBeq : (slice.name == symName) = true := @List.find?_some ElfFuncSlice (fun (s : ElfFuncSlice) => s.name == symName) _ _ hExt
  have hNameEq : slice.name = symName := beq_iff_eq.mp hBeq
  have hFoldEq : extractAllRlibFuncs rlib = (parseArArchive rlib).foldl rlibFoldStep [] := rfl
  rw [hFoldEq] at hInAll
  rcases foldl_rlibFoldStep_mem_origin (parseArArchive rlib) [] slice hInAll with
    hEmpty | ⟨m, hm, fs, pre, suf, hElfAll, hInFs, hDecomp⟩
  · cases hEmpty
  · have hAllEq : extractAllRlibFuncs rlib = pre ++ fs ++ suf := hFoldEq.trans hDecomp
    rw [hAllEq, List.map_append, List.map_append] at hDist
    have hFsDist : allDistinctStrings (fs.map ElfFuncSlice.name) = true :=
      allDistinctStrings_append_right (allDistinctStrings_append_left hDist)
    have hFind : fs.find? (fun s => s.name == symName) = some slice := by
      rw [← hNameEq]
      exact find_slice_unique_of_distinct hFsDist hInFs
    have hMemExt : extractElfFuncBytes m.payload symName = some slice := by
      unfold extractElfFuncBytes
      rw [hElfAll]
      exact hFind
    have hMemNI : checkElfFuncThreeWayNI m.payload symName c = true := by
      unfold checkElfFuncThreeWayNI
      rw [hMemExt]
      exact hSliceNI
    obtain ⟨slice', hExt', hOk', hSafe'⟩ := checkElfFuncThreeWayNI_sound hMemNI
    have hSlEq : slice' = slice := Option.some.inj (hExt'.symm.trans hMemExt)
    subst hSlEq
    exact ⟨m, hm, parseArMember_subslice rlib m hm, hMemExt, hMemNI, hOk', hSafe'⟩


private def u16LE (v : Nat) : List UInt8 :=
  [UInt8.ofNat (v % 256), UInt8.ofNat ((v / 256) % 256)]

private def u32LE (v : Nat) : List UInt8 :=
  u16LE (v % 65536) ++ u16LE ((v / 65536) % 65536)

private def u64LE (v : Nat) : List UInt8 :=
  u32LE (v % 4294967296) ++ u32LE ((v / 4294967296) % 4294967296)

private def mkElf64ShdrBytes (shName shType shFlags shOffset shSize shLink shInfo shAlign shEntsize : Nat) :
    List UInt8 :=
  u32LE shName ++ u32LE shType ++ u64LE shFlags ++ u64LE 0 ++
  u64LE shOffset ++ u64LE shSize ++ u32LE shLink ++ u32LE shInfo ++
  u64LE shAlign ++ u64LE shEntsize

private def mkElf64SymBytes (stName stInfo stOther stShndx stValue stSize : Nat) : List UInt8 :=
  u32LE stName ++ [UInt8.ofNat stInfo, UInt8.ofNat stOther] ++ u16LE stShndx ++
  u64LE stValue ++ u64LE stSize

/-- Build a canonical `ET_REL` `ELF64` relocatable object (`Bytes`) containing a single global
    `STT_FUNC` symbol (`nameBytes`) backed by machine-code `.text` bytes `code`. -/
def mkSingleFuncElf64 (machine : Nat) (nameBytes code : List UInt8) : Bytes :=
  let shstrtab : List UInt8 :=
    [0,
     0x2e, 0x73, 0x68, 0x73, 0x74, 0x72, 0x74, 0x61, 0x62, 0,
     0x2e, 0x74, 0x65, 0x78, 0x74, 0,
     0x2e, 0x73, 0x74, 0x72, 0x74, 0x61, 0x62, 0,
     0x2e, 0x73, 0x79, 0x6d, 0x74, 0x61, 0x62, 0]
  let strtab : List UInt8 := [0] ++ nameBytes ++ [0]
  let sym0 := mkElf64SymBytes 0 0 0 0 0 0
  let sym1 := mkElf64SymBytes 1 0x12 0 2 0 code.length
  let symtab := sym0 ++ sym1
  let offShstr := 64
  let offText := offShstr + shstrtab.length
  let offStr := offText + code.length
  let offSym := offStr + strtab.length
  let offShdrs := offSym + symtab.length
  let ehdr : List UInt8 :=
    [0x7f, 0x45, 0x4c, 0x46, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++
    u16LE 1 ++ u16LE machine ++ u32LE 1 ++
    u64LE 0 ++ u64LE 0 ++ u64LE offShdrs ++
    u32LE 0 ++ u16LE 64 ++ u16LE 0 ++ u16LE 0 ++
    u16LE 64 ++ u16LE 5 ++ u16LE 1
  let sh0 := mkElf64ShdrBytes 0 0 0 0 0 0 0 0 0
  let sh1 := mkElf64ShdrBytes 1 3 0 offShstr shstrtab.length 0 0 1 0
  let sh2 := mkElf64ShdrBytes 11 1 6 offText code.length 0 0 16 0
  let sh3 := mkElf64ShdrBytes 17 3 0 offStr strtab.length 0 0 1 0
  let sh4 := mkElf64ShdrBytes 25 2 0 offSym symtab.length 3 1 8 24
  Bytes.ofList (ehdr ++ shstrtab ++ code ++ strtab ++ symtab ++ sh0 ++ sh1 ++ sh2 ++ sh3 ++ sh4)

/-- Encode a list of 32-bit little-endian `AArch64` instruction words into raw `.text` bytes. -/
def wordsToBytesLE : List Nat → List UInt8
  | [] => []
  | w :: ws => u32LE w ++ wordsToBytesLE ws

/-! ## §3. Real `.rlib` Scalar & Multi-Precision `Goldilocks` / CT Kernels -/

section ExtraStepLemmas
variable (off len pc : Nat) (g : Bank16 UInt64) (y : Bank16 Vec256) (cf o zf dy : Bool)
  (m : UInt64 → UInt8)

theorem stepX86_adcx (dst src : Nat) :
    (stepX86 ⟨off, len, .adcx dst src⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (UInt64.ofNat (((g.get dst).toNat + (g.get src).toNat +
          (if cf then 1 else 0)) % 0x10000000000000000)),
        y, decide ((g.get dst).toNat + (g.get src).toNat + (if cf then 1 else 0) ≥ 0x10000000000000000),
        o, zf, dy, false, m⟩ := by rfl

theorem stepX86_adox (dst src : Nat) :
    (stepX86 ⟨off, len, .adox dst src⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (UInt64.ofNat (((g.get dst).toNat + (g.get src).toNat +
          (if o then 1 else 0)) % 0x10000000000000000)),
        y, cf,
        decide ((g.get dst).toNat + (g.get src).toNat + (if o then 1 else 0) ≥ 0x10000000000000000),
        zf, dy, false, m⟩ := by rfl

theorem stepX86_cmovnz64 (dst src : Nat) :
    (stepX86 ⟨off, len, .cmovcc 5 true dst src⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (if !zf then g.get src else g.get dst), y, cf, o, zf, dy, false, m⟩ := by rfl

theorem stepX86_andRR64 (dst src : Nat) :
    (stepX86 ⟨off, len, .aluRegReg .andOp true dst src⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (g.get dst &&& g.get src), y, false, false,
        (g.get dst &&& g.get src) == 0, dy, false, m⟩ := by rfl

theorem stepX86_xorRR64 (dst src : Nat) :
    (stepX86 ⟨off, len, .aluRegReg .xorOp true dst src⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (g.get dst ^^^ g.get src), y, false, false,
        (g.get dst ^^^ g.get src) == 0, dy, false, m⟩ := by rfl

end ExtraStepLemmas

section ExtraArmStepLemmas
variable (off len pc : Nat) (g : Bank32 UInt64) (v : Bank32 Vec128) (cf zf dit : Bool)
  (m : UInt64 → UInt8)

theorem stepArm64_cselNe (rd rn rm : Nat) :
    (stepArm64 ⟨off, len, .csel 1 false true rd rn rm⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (if !zf then armGet g rn else armGet g rm), v, cf, zf, dit, false, m⟩ := by
  rfl

theorem stepArm64_orrImm (rd rn : Nat) (imm : UInt64) :
    (stepArm64 ⟨off, len, .aluImm .orr true rd rn imm⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (armGet g rn ||| imm), v, cf, zf, dit, false, m⟩ := by rfl

end ExtraArmStepLemmas

theorem bv_ofU64_eq_ofNat {w : UInt64} {n : Nat} (h : w.toNat = n) (hn : n < 2 ^ 64) :
    w.toBitVec = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [UInt64.toNat_toBitVec, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem mod_goldilocks_lt_u64 (n : Nat) : n % GOLDILOCKS_P < 2 ^ 64 := by
  have hp : GOLDILOCKS_P < 2 ^ 64 := by decide
  exact Nat.lt_trans (Nat.mod_lt n (by decide)) hp

/-! ### §3.1 `qsag_asm_goldilocks_add_ct_x86_64` (`N = 17`, `retPc = 50`) -/


/-! ### §3.2 `qsag_asm_goldilocks_sub_ct_x86_64` (`N = 23`, `retPc = 74`) -/


/-! ### §3.3 `qsag_asm_goldilocks_mul_ct_x86_64` (`N = 25`) & `qsag_asm_goldilocks_mul_ct_aarch64` (`N = 29`) -/


/-! ### §3.4 `qsag_asm_goldilocks_pow7_ct_x86_64` (`N = 85`, `retPc = 265`) -/


theorem goldPow7Mc_toNat (x : UInt64) :
    (goldMulMc (goldMulMc (goldMulMc (goldMulMc x x) x) (goldMulMc (goldMulMc x x) x)) x).toNat =
      (x.toNat ^ 7) % GOLDILOCKS_P := by
  rw [goldMulMc_toNat, goldMulMc_toNat, goldMulMc_toNat, goldMulMc_toNat]
  show ((((x.toNat * x.toNat % GOLDILOCKS_P) * x.toNat % GOLDILOCKS_P) *
      ((x.toNat * x.toNat % GOLDILOCKS_P) * x.toNat % GOLDILOCKS_P) % GOLDILOCKS_P) * x.toNat) %
      GOLDILOCKS_P = (x.toNat ^ 7) % GOLDILOCKS_P
  simp only [Nat.mul_mod_mod, Nat.mod_mul_mod]
  have hPow : x.toNat ^ 7 =
      ((x.toNat * x.toNat) * x.toNat) * ((x.toNat * x.toNat) * x.toNat) * x.toNat := by
    simp [Nat.pow_succ, Nat.pow_zero, Nat.mul_assoc]
  rw [hPow]


/-! ### §3.5 `qsag_asm_goldilocks_dot2_adx_x86_64` (`N = 44`, `retPc = 153`) -/


def goldDot2Mc (a0 b0 a1 b1 : UInt64) : UInt64 :=
  let p0 := a0.toNat * b0.toNat
  let p1 := a1.toNat * b1.toNat
  let lo0 := UInt64.ofNat (p0 % 0x10000000000000000)
  let hi0 := UInt64.ofNat (p0 / 0x10000000000000000)
  let lo1 := UInt64.ofNat (p1 % 0x10000000000000000)
  let hi1 := UInt64.ofNat (p1 / 0x10000000000000000)
  let sumLo := lo0.toNat + lo1.toNat
  let r8 := UInt64.ofNat (sumLo % 0x10000000000000000)
  let cf0 := decide (sumLo ≥ 0x10000000000000000)
  let sumHi := hi0.toNat + hi1.toNat + (if cf0 then 1 else 0)
  let r9 := UInt64.ofNat (sumHi % 0x10000000000000000)
  let cf1 := decide (sumHi ≥ 0x10000000000000000)
  let r11 : UInt64 := if cf1 then 18446744065119617025 else 0
  goldAddMc (mulRed r8 r9) r11

theorem u64_toNat_zero : (0 : UInt64).toNat = 0 := rfl

theorem u64_ofNat_zero_mod : UInt64.ofNat (0 % 0x10000000000000000) = 0 := rfl

theorem u64_zero_lt_264 : decide (0 ≥ 0x10000000000000000) = false := rfl

theorem u64_ofNat_b_mod (c : Bool) :
    UInt64.ofNat ((if c then 1 else 0) % 0x10000000000000000) = if c then 1 else 0 := by
  cases c <;> decide

theorem u64_b_lt_264 (c : Bool) :
    decide ((if c then 1 else 0) ≥ 0x10000000000000000) = false := by
  cases c <;> decide

theorem u64_eps2_and_mask (c : Bool) :
    (18446744065119617025 : UInt64) &&& ((0 : UInt64) - (if c then 1 else 0)) =
      if c then 18446744065119617025 else 0 := by
  cases c <;> decide


theorem goldDot2Mc_toNat (a0 b0 a1 b1 : UInt64) :
    (goldDot2Mc a0 b0 a1 b1).toNat =
      (a0.toNat * b0.toNat + a1.toNat * b1.toNat) % GOLDILOCKS_P := by
  have ha0 := a0.toNat_lt; have hb0 := b0.toNat_lt
  have ha1 := a1.toNat_lt; have hb1 := b1.toNat_lt
  have hp0 : a0.toNat * b0.toNat < 18446744073709551616 * 18446744073709551616 :=
    Nat.mul_lt_mul'' ha0 hb0
  have hp1 : a1.toNat * b1.toNat < 18446744073709551616 * 18446744073709551616 :=
    Nat.mul_lt_mul'' ha1 hb1
  unfold goldDot2Mc
  dsimp only
  rw [goldAddMc_toNat]
  generalize a0.toNat * b0.toNat = p0 at hp0 ⊢
  generalize a1.toNat * b1.toNat = p1 at hp1 ⊢
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  have hlo0 : (UInt64.ofNat (p0 % 18446744073709551616)).toNat = p0 % 18446744073709551616 := by
    rw [UInt64.toNat_ofNat', h64, Nat.mod_mod]
  have hhi0 : (UInt64.ofNat (p0 / 18446744073709551616)).toNat = p0 / 18446744073709551616 := by
    rw [UInt64.toNat_ofNat', h64, Nat.mod_eq_of_lt (by omega)]
  have hlo1 : (UInt64.ofNat (p1 % 18446744073709551616)).toNat = p1 % 18446744073709551616 := by
    rw [UInt64.toNat_ofNat', h64, Nat.mod_mod]
  have hhi1 : (UInt64.ofNat (p1 / 18446744073709551616)).toNat = p1 / 18446744073709551616 := by
    rw [UInt64.toNat_ofNat', h64, Nat.mod_eq_of_lt (by omega)]
  rw [hlo0, hlo1, hhi0, hhi1]
  let sumLo := p0 % 18446744073709551616 + p1 % 18446744073709551616
  let cf0 := decide (sumLo ≥ 18446744073709551616)
  let sumHi := p0 / 18446744073709551616 + p1 / 18446744073709551616 + (if cf0 then 1 else 0)
  let cf1 := decide (sumHi ≥ 18446744073709551616)
  have hr8 : (UInt64.ofNat (sumLo % 18446744073709551616)).toNat = sumLo % 18446744073709551616 := by
    rw [UInt64.toNat_ofNat', h64, Nat.mod_mod]
  have hr9 : (UInt64.ofNat (sumHi % 18446744073709551616)).toNat = sumHi % 18446744073709551616 := by
    rw [UInt64.toNat_ofNat', h64, Nat.mod_mod]
  have hRed := mulRed_mod (UInt64.ofNat (sumLo % 18446744073709551616))
    (UInt64.ofNat (sumHi % 18446744073709551616))
  rw [hr8, hr9] at hRed
  change ((mulRed (UInt64.ofNat (sumLo % 18446744073709551616))
            (UInt64.ofNat (sumHi % 18446744073709551616))).toNat +
          (if cf1 then (18446744065119617025 : UInt64) else 0).toNat) % 18446744069414584321 =
        (p0 + p1) % 18446744069414584321
  rw [← Nat.mod_add_mod, hRed, Nat.mod_add_mod]
  show (sumLo % 18446744073709551616 + sumHi % 18446744073709551616 * 18446744073709551616 +
      (if cf1 then (18446744065119617025 : UInt64) else 0).toNat) % 18446744069414584321 =
      (p0 + p1) % 18446744069414584321
  have hLoSplit : sumLo = sumLo % 18446744073709551616 +
      (if cf0 then 1 else 0) * 18446744073709551616 := by
    if hc0 : sumLo ≥ 18446744073709551616 then
      have hc0t : cf0 = true := decide_eq_true hc0
      rw [hc0t]; simp; omega
    else
      have hc0f : cf0 = false := decide_eq_false hc0
      rw [hc0f]; simp; omega
  have hHiSplit : sumHi = sumHi % 18446744073709551616 +
      (if cf1 then 1 else 0) * 18446744073709551616 := by
    if hc1 : sumHi ≥ 18446744073709551616 then
      have hc1t : cf1 = true := decide_eq_true hc1
      rw [hc1t]; simp; omega
    else
      have hc1f : cf1 = false := decide_eq_false hc1
      rw [hc1f]; simp; omega
  have hSumMid : p0 + p1 = sumLo % 18446744073709551616 + sumHi * 18446744073709551616 := by
    dsimp only [sumLo, sumHi] at hLoSplit ⊢
    calc p0 + p1
      _ = (p0 % 18446744073709551616 + p1 % 18446744073709551616) +
          (p0 / 18446744073709551616 + p1 / 18446744073709551616) * 18446744073709551616 := by
        rw [Nat.add_mul]; omega
      _ = (sumLo % 18446744073709551616 + (if cf0 then 1 else 0) * 18446744073709551616) +
          (p0 / 18446744073709551616 + p1 / 18446744073709551616) * 18446744073709551616 := by
        rw [← hLoSplit]
      _ = sumLo % 18446744073709551616 +
          (p0 / 18446744073709551616 + p1 / 18446744073709551616 + (if cf0 then 1 else 0)) *
            18446744073709551616 := by
        rw [Nat.add_mul, Nat.add_mul]; omega
  if hc1 : sumHi ≥ 18446744073709551616 then
    have hc1t : cf1 = true := decide_eq_true hc1
    rw [hc1t] at hHiSplit ⊢
    have hC : (if true = true then (18446744065119617025 : UInt64) else 0).toNat = 18446744065119617025 := rfl
    rw [hC]
    conv => rhs; rw [hSumMid, hHiSplit]
    have hSplit1 : (if true = true then 1 else 0) * 18446744073709551616 = 18446744073709551616 := rfl
    rw [hSplit1, Nat.add_mul, ← Nat.add_assoc]
    have hB2 : 18446744073709551616 * 18446744073709551616 =
        18446744065119617025 + 18446744078004518911 * 18446744069414584321 := rfl
    rw [hB2, ← Nat.add_assoc, Nat.add_mul_mod_self_right]
  else
    have hc1f : cf1 = false := decide_eq_false hc1
    rw [hc1f] at hHiSplit ⊢
    have h0 : (if false = true then (18446744065119617025 : UInt64) else 0).toNat = 0 := rfl
    have hSplit0 : (if false = true then 1 else 0) * 18446744073709551616 = 0 := rfl
    rw [h0, Nat.add_zero]
    conv => rhs; rw [hSumMid, hHiSplit]
    rw [hSplit0, Nat.add_zero]


/-! ### §3.6 `qsag_asm_ct_eq_32_x86_64` (`N = 20`) & `qsag_asm_ct_eq_32_aarch64` (`N = 22`) -/


/-! ### §3.7 `qsag_asm_ct_eq_32_aarch64` (`N = 22`, `retPc = 84`) -/

theorem ctEq32Arm_reaches (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (hi : Bank16 UInt64) (v : Bank32 Vec128) (cf zf dit : Bool) (m : UInt64 → UInt8) :
    ExecReachesArm64 ctEq32ArmProg 21
      ⟨0, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        v, cf, zf, dit, false, m⟩
      ⟨84, ⟨⟨((ctEq32WordArm m r0 r1 ||| (0 - ctEq32WordArm m r0 r1)) >>> UInt64.ofNat 63) ^^^ 1,
          r1, 0, 0, 0, 0, 0, 0, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        v, cf, zf, dit, false, m⟩ := by
  apply StepsArm64.toExecReaches
  iterate 21
    apply StepsArm64.cons rfl rfl
    · simp only [stepArm64_ldp, stepArm64_eorRR, stepArm64_orrRR, stepArm64_subRR, stepArm64_lsr64,
        stepArm64_eorImm, stepArm64_movz, u64_shl_zero_zero, uint64_evalSub_eq,
        armGet_31, armGet_0, armGet_1, armGet_2, armGet_3, armGet_4, armGet_5, armGet_6, armGet_7,
        armSet_0, armSet_2, armSet_3, armSet_4, armSet_5, armSet_6, armSet_7]
      rfl
  rw [ctEq32WordArm.public_eq_1]
  exact StepsArm64.zero _


/-! ## §4. Cross-ISA `ELF64` Scalar Constant-Time Kernels (`ct_select_u64`, `ct_eq_u64`, `aarch64` `goldilocks_add_ct` & `sub_ct`) -/

/-! ### §4.1 `ct_select_u64` (`x86_64` `N = 4` & `aarch64` `N = 3`) -/

/-- ASCII bytes of `"ct_select_u64"`. -/
def ctSelectSymBytes : List UInt8 :=
  [0x63, 0x74, 0x5f, 0x73, 0x65, 0x6c, 0x65, 0x63, 0x74, 0x5f, 0x75, 0x36, 0x34]

/-- Compiled `x86_64` `.text` bytes for `ct_select_u64(cond: rdi, a: rsi, b: rdx) -> rax`:
    `and rdi, rdi; mov rax, rdx; cmovnz rax, rsi; ret`. -/
def ctSelectX86Bytes : List UInt8 :=
  [0x48, 0x21, 0xFF, 0x48, 0x89, 0xD0, 0x48, 0x0F, 0x45, 0xC6, 0xC3]

def ctSelectX86Elf : Bytes :=
  Bytes.ofNat 491 0x18000000000000000800000001000000030000000000000030000000000000007b000000000000000000000000000000000000000200000019000000000000000000000000000000010000000000000000000000000000000f000000000000006c000000000000000000000000000000000000000300000011000000000000000000000000000000100000000000000000000000000000000b000000000000006100000000000000000000000000000006000000010000000b0000000000000000000000000000000100000000000000000000000000000021000000000000004000000000000000000000000000000000000000030000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b00000000000000000002001200000001000000000000000000000000000000000000000000000000003436755f7463656c65735f746300c3c6450f48d08948ff2148006261746d79732e006261747274732e00747865742e0062617472747368732e000001000500400000000000400000000000000000000000ab0000000000000000000000000000000000000001003e0001000000000000000000010102464c457f

def ctSelectX86Prog : List (DecodedInstr X86Instr) := [
  ⟨0, 3, .aluRegReg .andOp true 7 7⟩,
  ⟨3, 3, .movRegReg true 0 2⟩,
  ⟨6, 4, .cmovcc 5 true 0 6⟩,
  ⟨10, 1, .ret⟩]

/-- Compiled `AArch64` `.text` bytes for `ct_select_u64(cond: x0, a: x1, b: x2) -> x0`:
    `cmp x0, #0; csel x0, x1, x2, ne; ret`. -/
def ctSelectArmBytes : List UInt8 :=
  wordsToBytesLE [0xF100001F, 0x9A821020, 0xD65F03C0]

def ctSelectArmElf : Bytes :=
  Bytes.ofNat 492 0x18000000000000000800000001000000030000000000000030000000000000007c000000000000000000000000000000000000000200000019000000000000000000000000000000010000000000000000000000000000000f000000000000006d000000000000000000000000000000000000000300000011000000000000000000000000000000100000000000000000000000000000000c000000000000006100000000000000000000000000000006000000010000000b0000000000000000000000000000000100000000000000000000000000000021000000000000004000000000000000000000000000000000000000030000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c00000000000000000002001200000001000000000000000000000000000000000000000000000000003436755f7463656c65735f746300d65f03c09a821020f100001f006261746d79732e006261747274732e00747865742e0062617472747368732e000001000500400000000000400000000000000000000000ac000000000000000000000000000000000000000100b70001000000000000000000010102464c457f

def ctSelectArmProg : List (DecodedInstr Arm64Instr) := [
  ⟨0, 4, .aluImm .subs true 31 0 0⟩,
  ⟨4, 4, .csel 1 false true 0 1 2⟩,
  ⟨8, 4, .ret⟩]

private theorem ctSelectX86_reaches (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    ExecReachesX86 ctSelectX86Prog 3
      ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        y, cf, o, zf, dy, false, m⟩
      ⟨10, ⟨if !(r7 == 0) then r6 else r2, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        y, false, false, r7 == 0, dy, false, m⟩ := by
  cases h7 : (r7 == 0)
  · apply StepsX86.toExecReaches
    iterate 3
      apply StepsX86.cons rfl rfl
      · simp only [stepX86_andRR64, stepX86_movRR, stepX86_cmovnz64, UInt64.and_self,
          maskGprWidth_true, b16get_2, b16get_6, b16get_7, b16set_0, b16set_7, h7]
        rfl
    exact StepsX86.zero _
  · apply StepsX86.toExecReaches
    iterate 3
      apply StepsX86.cons rfl rfl
      · simp only [stepX86_andRR64, stepX86_movRR, stepX86_cmovnz64, UInt64.and_self,
          maskGprWidth_true, b16get_2, b16get_6, b16get_7, b16set_0, b16set_7, h7]
        rfl
    exact StepsX86.zero _

theorem elf_ct_select_u64_x86_64_functional_and_ct :
    ∃ slice : ElfFuncSlice,
      extractElfFuncBytes ctSelectX86Elf "ct_select_u64" = some slice ∧
      ElfSliceOk ctSelectX86Elf slice ∧
      checkElfFuncThreeWayNI ctSelectX86Elf "ct_select_u64"
        (mkContract "ct_select_u64" [4]) = true ∧
      ElfSliceThreeWayNISafe slice (mkContract "ct_select_u64" [4]) ∧
      slice.code = ctSelectX86Bytes ∧
      decodeX86Slice slice.code = some ctSelectX86Prog ∧
      ∀ (st : X86BvState), st.pc = 0 → st.halted = false →
        (∃ st3 tr3, execDecodedX86 slice.code 3 st = some (st3, tr3) ∧ st3.halted = false) ∧
        ∀ extra : Nat, ∃ st' trace,
          execDecodedX86 slice.code (4 + extra) st = some (st', trace) ∧
          st'.halted = true ∧ st'.pc = (readMem64 st'.toX86State.mem (st.toX86State.gpr.get 4)).toNat ∧ trace.length = 4 ∧
          st'.gpr.get 0 = (if st.gpr.get 7 != 0#64 then st.gpr.get 6 else st.gpr.get 2) ∧
          X86CalleeSavedPreserved st st' ∧
          st'.mem = st.mem := by
  have hNI : checkElfFuncThreeWayNI ctSelectX86Elf "ct_select_u64"
      (mkContract "ct_select_u64" [4]) = true := by decide +kernel
  obtain ⟨slice, hExt, hOk, hSafe⟩ := checkElfFuncThreeWayNI_sound hNI
  have hCode : slice.code = ctSelectX86Bytes := by
    have hC : (extractElfFuncBytes ctSelectX86Elf "ct_select_u64").map ElfFuncSlice.code =
        some ctSelectX86Bytes := by decide +kernel
    rw [hExt] at hC
    exact Option.some.inj hC
  have hDec : decodeX86Slice slice.code = some ctSelectX86Prog := by
    rw [hCode]; decide +kernel
  refine ⟨slice, hExt, hOk, hNI, hSafe, hCode, hDec, ?_⟩
  intro st hpc hh
  rcases st with ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
    y, cf, o, zf, dy, hlt, mem⟩
  dsimp only at hpc hh; subst hpc hh
  let st0 : X86BvState := ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, mem⟩
  obtain ⟨hPre, hPost⟩ := execDecodedX86_ret_of_reaches st0 hDec rfl
    (ctSelectX86_reaches (UInt64.ofBitVec r0) (UInt64.ofBitVec r1) (UInt64.ofBitVec r2)
      (UInt64.ofBitVec r3) (UInt64.ofBitVec r4) (UInt64.ofBitVec r5) (UInt64.ofBitVec r6)
      (UInt64.ofBitVec r7) (UInt64.ofBitVec r8) (UInt64.ofBitVec r9) (UInt64.ofBitVec r10)
      (UInt64.ofBitVec r11) (UInt64.ofBitVec r12) (UInt64.ofBitVec r13) (UInt64.ofBitVec r14)
      (UInt64.ofBitVec r15) y cf o zf dy (fun a => mem a.toBitVec))
    rfl rfl
  refine ⟨hPre, fun extra => ?_⟩
  obtain ⟨tr, hExec, hL⟩ := hPost extra
  refine ⟨_, tr, hExec, rfl, rfl, hL, ?_, ?_, ?_⟩
  · change (if !(UInt64.ofBitVec r7 == 0) then UInt64.ofBitVec r6 else UInt64.ofBitVec r2).toBitVec =
      (if r7 != 0#64 then r6 else r2)
    have hBeq : (UInt64.ofBitVec r7 == 0) = (r7 == 0#64) := by
      cases h : (r7 == 0#64)
      · have hne : r7 ≠ 0#64 := fun heq => by rw [heq] at h; cases h
        exact beq_false_of_ne (fun hu => hne (by simpa using congrArg UInt64.toBitVec hu))
      · have heq : r7 = 0#64 := beq_iff_eq.mp h
        subst heq; rfl
    rw [hBeq]
    unfold bne
    cases (r7 == 0#64)
    · simp only [Bool.not_false, ite_true, UInt64.toBitVec_ofBitVec]
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false, UInt64.toBitVec_ofBitVec]
  · exact x86_callee_saved_of_roundtrip
  · exact mem_roundtrip mem

private theorem u64_subs_zero_eq (x : UInt64) :
    UInt64.ofNat ((x.toNat + 0x10000000000000000 - (0 : UInt64).toNat) % 0x10000000000000000) = x := by
  apply u64_eq_of_toNat
  have hx := x.toNat_lt
  have h0 : (0 : UInt64).toNat = 0 := rfl
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  rw [UInt64.toNat_ofNat', h0, h64]
  show (x.toNat + 18446744073709551616 - 0) % 18446744073709551616 % 18446744073709551616 = x.toNat
  omega

private theorem ctSelectArm_reaches (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (hi : Bank16 UInt64) (v : Bank32 Vec128) (cf zf dit : Bool) (m : UInt64 → UInt8) :
    ExecReachesArm64 ctSelectArmProg 2
      ⟨0, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        v, cf, zf, dit, false, m⟩
      ⟨8, ⟨⟨if !(r0 == 0) then r1 else r2, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        v, decide (r0.toNat ≥ (0 : UInt64).toNat), r0 == 0, dit, false, m⟩ := by
  apply StepsArm64.toExecReaches
  iterate 2
    apply StepsArm64.cons rfl rfl
    · simp only [stepArm64_subsImm, stepArm64_cselNe, u64_subs_zero_eq,
        armGet_0, armGet_1, armGet_2, armSet_31, armSet_0]
      rfl
  exact StepsArm64.zero _

theorem elf_ct_select_u64_aarch64_functional_and_ct :
    ∃ slice : ElfFuncSlice,
      extractElfFuncBytes ctSelectArmElf "ct_select_u64" = some slice ∧
      ElfSliceOk ctSelectArmElf slice ∧
      checkElfFuncThreeWayNI ctSelectArmElf "ct_select_u64"
        (mkContract "ct_select_u64" []) = true ∧
      ElfSliceThreeWayNISafe slice (mkContract "ct_select_u64" []) ∧
      slice.code = ctSelectArmBytes ∧
      decodeArm64Slice slice.code = some ctSelectArmProg ∧
      ∀ (st : Arm64BvState), st.pc = 0 → st.halted = false →
        (∃ st2 tr2, execDecodedArm64 slice.code 2 st = some (st2, tr2) ∧ st2.halted = false) ∧
        ∀ extra : Nat, ∃ st' trace,
          execDecodedArm64 slice.code (3 + extra) st = some (st', trace) ∧
          st'.halted = true ∧ st'.pc = 8 ∧ trace.length = 3 ∧
          st'.gpr.get 0 = (if st.gpr.get 0 != 0#64 then st.gpr.get 1 else st.gpr.get 2) ∧
          Arm64CalleeSavedPreserved st st' ∧
          st'.mem = st.mem := by
  have hNI : checkElfFuncThreeWayNI ctSelectArmElf "ct_select_u64"
      (mkContract "ct_select_u64" []) = true := by decide +kernel
  obtain ⟨slice, hExt, hOk, hSafe⟩ := checkElfFuncThreeWayNI_sound hNI
  have hCode : slice.code = ctSelectArmBytes := by
    have hC : (extractElfFuncBytes ctSelectArmElf "ct_select_u64").map ElfFuncSlice.code =
        some ctSelectArmBytes := by decide +kernel
    rw [hExt] at hC
    exact Option.some.inj hC
  have hDec : decodeArm64Slice slice.code = some ctSelectArmProg := by
    rw [hCode]; decide +kernel
  refine ⟨slice, hExt, hOk, hNI, hSafe, hCode, hDec, ?_⟩
  intro st hpc hh
  rcases st with ⟨pc, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
    v, cf, zf, dit, hlt, mem⟩
  dsimp only at hpc hh; subst hpc hh
  let st0 : Arm64BvState := ⟨0, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩, v, cf, zf, dit, false, mem⟩
  obtain ⟨hPre, hPost⟩ := execDecodedArm64_ret_of_reaches st0 hDec rfl
    (ctSelectArm_reaches (UInt64.ofBitVec r0) (UInt64.ofBitVec r1) (UInt64.ofBitVec r2)
      (UInt64.ofBitVec r3) (UInt64.ofBitVec r4) (UInt64.ofBitVec r5) (UInt64.ofBitVec r6)
      (UInt64.ofBitVec r7) (UInt64.ofBitVec r8) (UInt64.ofBitVec r9) (UInt64.ofBitVec r10)
      (UInt64.ofBitVec r11) (UInt64.ofBitVec r12) (UInt64.ofBitVec r13) (UInt64.ofBitVec r14)
      (UInt64.ofBitVec r15) (bank16ToU64 hi) v cf zf dit (fun a => mem a.toBitVec))
    rfl rfl
  refine ⟨hPre, fun extra => ?_⟩
  obtain ⟨tr, hExec, hL⟩ := hPost extra
  refine ⟨_, tr, hExec, rfl, rfl, hL, ?_, ?_, ?_⟩
  · change (if !(UInt64.ofBitVec r0 == 0) then UInt64.ofBitVec r1 else UInt64.ofBitVec r2).toBitVec =
      (if r0 != 0#64 then r1 else r2)
    have hBeq : (UInt64.ofBitVec r0 == 0) = (r0 == 0#64) := by
      cases h : (r0 == 0#64)
      · have hne : r0 ≠ 0#64 := fun heq => by rw [heq] at h; cases h
        exact beq_false_of_ne (fun hu => hne (by simpa using congrArg UInt64.toBitVec hu))
      · have heq : r0 = 0#64 := beq_iff_eq.mp h
        subst heq; rfl
    rw [hBeq]
    unfold bne
    cases (r0 == 0#64)
    · simp only [Bool.not_false, ite_true, UInt64.toBitVec_ofBitVec]
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false, UInt64.toBitVec_ofBitVec]
  · exact arm64_callee_saved_of_hi_vec
  · exact mem_roundtrip mem

/-! ### §4.2 `ct_eq_u64` (`x86_64` `N = 9` & `aarch64` `N = 8`) -/

def ctEqU64SymBytes : List UInt8 :=
  [0x63, 0x74, 0x5f, 0x65, 0x71, 0x5f, 0x75, 0x36, 0x34]

def ctEqU64X86Bytes : List UInt8 :=
  [0x48, 0x89, 0xF8, 0x48, 0x31, 0xF0, 0x48, 0x89, 0xC1, 0x48, 0xF7, 0xD9,
   0x48, 0x09, 0xC8, 0x48, 0xC1, 0xE8, 0x3F, 0x83, 0xF0, 0x01, 0x31, 0xC9, 0xC3]

def ctEqU64X86Elf : Bytes :=
  Bytes.ofNat 501 0x180000000000000008000000010000000300000000000000300000000000000085000000000000000000000000000000000000000200000019000000000000000000000000000000010000000000000000000000000000000b000000000000007a0000000000000000000000000000000000000003000000110000000000000000000000000000001000000000000000000000000000000019000000000000006100000000000000000000000000000006000000010000000b0000000000000000000000000000000100000000000000000000000000000021000000000000004000000000000000000000000000000000000000030000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001900000000000000000002001200000001000000000000000000000000000000000000000000000000003436755f71655f746300c3c93101f0833fe8c148c80948d9f748c18948f03148f88948006261746d79732e006261747274732e00747865742e0062617472747368732e000001000500400000000000400000000000000000000000b50000000000000000000000000000000000000001003e0001000000000000000000010102464c457f

def ctEqU64X86Prog : List (DecodedInstr X86Instr) := [
  ⟨0, 3, .movRegReg true 0 7⟩,
  ⟨3, 3, .aluRegReg .xorOp true 0 6⟩,
  ⟨6, 3, .movRegReg true 1 0⟩,
  ⟨9, 3, .negReg true 1⟩,
  ⟨12, 3, .aluRegReg .orOp true 0 1⟩,
  ⟨15, 4, .shiftImm .shr true 0 63⟩,
  ⟨19, 3, .aluImm .xorOp false 0 1⟩,
  ⟨22, 2, .aluRegReg .xorOp false 1 1⟩,
  ⟨24, 1, .ret⟩]

def ctEqU64ArmBytes : List UInt8 :=
  wordsToBytesLE [0xCA010002, 0xCB0203E3, 0xAA030042, 0xD37FFC40,
                  0xD2400000, 0xD2800002, 0xD2800003, 0xD65F03C0]

def ctEqU64ArmElf : Bytes :=
  Bytes.ofNat 508 0x18000000000000000800000001000000030000000000000030000000000000008c000000000000000000000000000000000000000200000019000000000000000000000000000000010000000000000000000000000000000b00000000000000810000000000000000000000000000000000000003000000110000000000000000000000000000001000000000000000000000000000000020000000000000006100000000000000000000000000000006000000010000000b0000000000000000000000000000000100000000000000000000000000000021000000000000004000000000000000000000000000000000000000030000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000002001200000001000000000000000000000000000000000000000000000000003436755f71655f746300d65f03c0d2800003d2800002d2400000d37ffc40aa030042cb0203e3ca010002006261746d79732e006261747274732e00747865742e0062617472747368732e000001000500400000000000400000000000000000000000bc000000000000000000000000000000000000000100b70001000000000000000000010102464c457f

def ctEqU64ArmProg : List (DecodedInstr Arm64Instr) := [
  ⟨0, 4, .aluReg .eor true 2 0 1 0 0⟩,
  ⟨4, 4, .aluReg .sub true 3 31 2 0 0⟩,
  ⟨8, 4, .aluReg .orr true 2 2 3 0 0⟩,
  ⟨12, 4, .ubfm true 0 2 63 63⟩,
  ⟨16, 4, .aluImm .eor true 0 0 1⟩,
  ⟨20, 4, .movWide false true 2 0 0⟩,
  ⟨24, 4, .movWide false true 3 0 0⟩,
  ⟨28, 4, .ret⟩]

private theorem ctEqU64X86_reaches (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    ExecReachesX86 ctEqU64X86Prog 8
      ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        y, cf, o, zf, dy, false, m⟩
      ⟨24, ⟨maskGprWidth false ((((r7 ^^^ r6) ||| (0 - (r7 ^^^ r6))) >>> UInt64.ofNat 63) ^^^ 1),
          0, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        y, false, false, true, dy, false, m⟩ := by
  apply StepsX86.toExecReaches
  iterate 8
    apply StepsX86.cons rfl rfl
    · simp only [stepX86_movRR, stepX86_neg, stepX86_orRR, stepX86_shr64,
        stepX86_xorImm, stepX86_xorRR, maskGprWidth_true, mask32_xor_self, u64_zero_beq_zero,
        b16get_0, b16get_1, b16get_6, b16get_7, b16set_0, b16set_1]
      rfl
  exact StepsX86.zero _

theorem elf_ct_eq_u64_x86_64_functional_and_ct :
    ∃ slice : ElfFuncSlice,
      extractElfFuncBytes ctEqU64X86Elf "ct_eq_u64" = some slice ∧
      ElfSliceOk ctEqU64X86Elf slice ∧
      checkElfFuncThreeWayNI ctEqU64X86Elf "ct_eq_u64"
        (mkContract "ct_eq_u64" [4] [] [1]) = true ∧
      ElfSliceThreeWayNISafe slice (mkContract "ct_eq_u64" [4] [] [1]) ∧
      slice.code = ctEqU64X86Bytes ∧
      decodeX86Slice slice.code = some ctEqU64X86Prog ∧
      ∀ (st : X86BvState), st.pc = 0 → st.halted = false →
        (∃ st8 tr8, execDecodedX86 slice.code 8 st = some (st8, tr8) ∧ st8.halted = false) ∧
        ∀ extra : Nat, ∃ st' trace,
          execDecodedX86 slice.code (9 + extra) st = some (st', trace) ∧
          st'.halted = true ∧ st'.pc = (readMem64 st'.toX86State.mem (st.toX86State.gpr.get 4)).toNat ∧ trace.length = 9 ∧
          st'.gpr.get 0 = (if st.gpr.get 7 = st.gpr.get 6 then 1#64 else 0#64) ∧
          X86CalleeSavedPreserved st st' ∧
          st'.mem = st.mem ∧
          st'.gpr.get 1 = 0#64 := by
  have hNI : checkElfFuncThreeWayNI ctEqU64X86Elf "ct_eq_u64"
      (mkContract "ct_eq_u64" [4] [] [1]) = true := by decide +kernel
  obtain ⟨slice, hExt, hOk, hSafe⟩ := checkElfFuncThreeWayNI_sound hNI
  have hCode : slice.code = ctEqU64X86Bytes := by
    have hC : (extractElfFuncBytes ctEqU64X86Elf "ct_eq_u64").map ElfFuncSlice.code =
        some ctEqU64X86Bytes := by decide +kernel
    rw [hExt] at hC; exact Option.some.inj hC
  have hDec : decodeX86Slice slice.code = some ctEqU64X86Prog := by rw [hCode]; decide +kernel
  refine ⟨slice, hExt, hOk, hNI, hSafe, hCode, hDec, ?_⟩
  intro st hpc hh
  rcases st with ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
    y, cf, o, zf, dy, hlt, mem⟩
  dsimp only at hpc hh; subst hpc hh
  let st0 : X86BvState := ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, mem⟩
  obtain ⟨hPre, hPost⟩ := execDecodedX86_ret_of_reaches st0 hDec rfl
    (ctEqU64X86_reaches (UInt64.ofBitVec r0) (UInt64.ofBitVec r1) (UInt64.ofBitVec r2)
      (UInt64.ofBitVec r3) (UInt64.ofBitVec r4) (UInt64.ofBitVec r5) (UInt64.ofBitVec r6)
      (UInt64.ofBitVec r7) (UInt64.ofBitVec r8) (UInt64.ofBitVec r9) (UInt64.ofBitVec r10)
      (UInt64.ofBitVec r11) (UInt64.ofBitVec r12) (UInt64.ofBitVec r13) (UInt64.ofBitVec r14)
      (UInt64.ofBitVec r15) y cf o zf dy (fun a => mem a.toBitVec))
    rfl rfl
  refine ⟨hPre, fun extra => ?_⟩
  obtain ⟨tr, hExec, hL⟩ := hPost extra
  refine ⟨_, tr, hExec, rfl, rfl, hL, ?_, ?_, ?_, rfl⟩
  · change (maskGprWidth false
        ((((UInt64.ofBitVec r7 ^^^ UInt64.ofBitVec r6) |||
            (0 - (UInt64.ofBitVec r7 ^^^ UInt64.ofBitVec r6))) >>>
            UInt64.ofNat 63) ^^^ 1)).toBitVec =
      (if r7 = r6 then 1#64 else 0#64)
    rw [zeroTest64_masked]
    have hiff : UInt64.ofBitVec r7 ^^^ UInt64.ofBitVec r6 = 0 ↔ r7 = r6 := by
      rw [UInt64.xor_eq_zero_iff]
      exact ⟨fun h => by simpa using congrArg UInt64.toBitVec h, fun h => by rw [h]⟩
    if hx : UInt64.ofBitVec r7 ^^^ UInt64.ofBitVec r6 = 0 then
      rw [ite_eq_left hx, ite_eq_left (hiff.mp hx)]; rfl
    else
      rw [ite_eq_right hx, ite_eq_right (fun h => hx (hiff.mpr h))]; rfl
  · exact x86_callee_saved_of_roundtrip
  · exact mem_roundtrip mem

private theorem ctEqU64Arm_reaches (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (hi : Bank16 UInt64) (v : Bank32 Vec128) (cf zf dit : Bool) (m : UInt64 → UInt8) :
    ExecReachesArm64 ctEqU64ArmProg 7
      ⟨0, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        v, cf, zf, dit, false, m⟩
      ⟨28, ⟨⟨(((r0 ^^^ r1) ||| (0 - (r0 ^^^ r1))) >>> UInt64.ofNat 63) ^^^ 1,
          r1, 0, 0, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        v, cf, zf, dit, false, m⟩ := by
  apply StepsArm64.toExecReaches
  iterate 7
    apply StepsArm64.cons rfl rfl
    · simp only [stepArm64_eorRR, stepArm64_subRR, stepArm64_orrRR, stepArm64_lsr64,
        stepArm64_eorImm, stepArm64_movz, u64_shl_zero_zero, uint64_evalSub_eq,
        armGet_31, armGet_0, armGet_1, armGet_2, armGet_3,
        armSet_0, armSet_2, armSet_3]
      rfl
  exact StepsArm64.zero _

theorem elf_ct_eq_u64_aarch64_functional_and_ct :
    ∃ slice : ElfFuncSlice,
      extractElfFuncBytes ctEqU64ArmElf "ct_eq_u64" = some slice ∧
      ElfSliceOk ctEqU64ArmElf slice ∧
      checkElfFuncThreeWayNI ctEqU64ArmElf "ct_eq_u64"
        (mkContract "ct_eq_u64" [] [] [2, 3]) = true ∧
      ElfSliceThreeWayNISafe slice (mkContract "ct_eq_u64" [] [] [2, 3]) ∧
      slice.code = ctEqU64ArmBytes ∧
      decodeArm64Slice slice.code = some ctEqU64ArmProg ∧
      ∀ (st : Arm64BvState), st.pc = 0 → st.halted = false →
        (∃ st7 tr7, execDecodedArm64 slice.code 7 st = some (st7, tr7) ∧ st7.halted = false) ∧
        ∀ extra : Nat, ∃ st' trace,
          execDecodedArm64 slice.code (8 + extra) st = some (st', trace) ∧
          st'.halted = true ∧ st'.pc = 28 ∧ trace.length = 8 ∧
          st'.gpr.get 0 = (if st.gpr.get 0 = st.gpr.get 1 then 1#64 else 0#64) ∧
          Arm64CalleeSavedPreserved st st' ∧
          st'.mem = st.mem ∧
          st'.gpr.get 2 = 0#64 ∧ st'.gpr.get 3 = 0#64 := by
  have hNI : checkElfFuncThreeWayNI ctEqU64ArmElf "ct_eq_u64"
      (mkContract "ct_eq_u64" [] [] [2, 3]) = true := by decide +kernel
  obtain ⟨slice, hExt, hOk, hSafe⟩ := checkElfFuncThreeWayNI_sound hNI
  have hCode : slice.code = ctEqU64ArmBytes := by
    have hC : (extractElfFuncBytes ctEqU64ArmElf "ct_eq_u64").map ElfFuncSlice.code =
        some ctEqU64ArmBytes := by decide +kernel
    rw [hExt] at hC; exact Option.some.inj hC
  have hDec : decodeArm64Slice slice.code = some ctEqU64ArmProg := by rw [hCode]; decide +kernel
  refine ⟨slice, hExt, hOk, hNI, hSafe, hCode, hDec, ?_⟩
  intro st hpc hh
  rcases st with ⟨pc, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
    v, cf, zf, dit, hlt, mem⟩
  dsimp only at hpc hh; subst hpc hh
  let st0 : Arm64BvState := ⟨0, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩, v, cf, zf, dit, false, mem⟩
  obtain ⟨hPre, hPost⟩ := execDecodedArm64_ret_of_reaches st0 hDec rfl
    (ctEqU64Arm_reaches (UInt64.ofBitVec r0) (UInt64.ofBitVec r1) (UInt64.ofBitVec r2)
      (UInt64.ofBitVec r3) (UInt64.ofBitVec r4) (UInt64.ofBitVec r5) (UInt64.ofBitVec r6)
      (UInt64.ofBitVec r7) (UInt64.ofBitVec r8) (UInt64.ofBitVec r9) (UInt64.ofBitVec r10)
      (UInt64.ofBitVec r11) (UInt64.ofBitVec r12) (UInt64.ofBitVec r13) (UInt64.ofBitVec r14)
      (UInt64.ofBitVec r15) (bank16ToU64 hi) v cf zf dit (fun a => mem a.toBitVec))
    rfl rfl
  refine ⟨hPre, fun extra => ?_⟩
  obtain ⟨tr, hExec, hL⟩ := hPost extra
  refine ⟨_, tr, hExec, rfl, rfl, hL, ?_, ?_, ?_, rfl, rfl⟩
  · change ((((UInt64.ofBitVec r0 ^^^ UInt64.ofBitVec r1) |||
        (0 - (UInt64.ofBitVec r0 ^^^ UInt64.ofBitVec r1))) >>>
        UInt64.ofNat 63) ^^^ 1).toBitVec =
      (if r0 = r1 then 1#64 else 0#64)
    rw [zeroTest64]
    have hiff : UInt64.ofBitVec r0 ^^^ UInt64.ofBitVec r1 = 0 ↔ r0 = r1 := by
      rw [UInt64.xor_eq_zero_iff]
      exact ⟨fun h => by simpa using congrArg UInt64.toBitVec h, fun h => by rw [h]⟩
    if hx : UInt64.ofBitVec r0 ^^^ UInt64.ofBitVec r1 = 0 then
      rw [ite_eq_left hx, ite_eq_left (hiff.mp hx)]; rfl
    else
      rw [ite_eq_right hx, ite_eq_right (fun h => hx (hiff.mpr h))]; rfl
  · exact arm64_callee_saved_of_hi_vec
  · exact mem_roundtrip mem

/-! ### §4.3 `aarch64` `goldilocks_add_ct` (`N = 20`) & `goldilocks_sub_ct` (`N = 24`) -/

def goldAddArmSymBytes : List UInt8 :=
  [0x67, 0x6f, 0x6c, 0x64, 0x69, 0x6c, 0x6f, 0x63, 0x6b, 0x73, 0x5f, 0x61, 0x64, 0x64, 0x5f, 0x63, 0x74]

def goldAddArmBytes : List UInt8 :=
  wordsToBytesLE [0x12800006, 0xAB010002, 0x9A1F03E7, 0xCB0703E7, 0x8A0600E7,
                  0xAB070042, 0x9A1F03E7, 0xCB0703E7, 0x8A0600E7, 0x8B070042,
                  0xAB060048, 0x9A1F03E7, 0xCB0703E7, 0x8A0600E7, 0x8B070040,
                  0xD2800002, 0xD2800006, 0xD2800007, 0xD2800008, 0xD65F03C0]

def goldAddArmElf : Bytes :=
  Bytes.ofNat 564 0x1800000000000000080000000100000003000000000000003000000000000000c4000000000000000000000000000000000000000200000019000000000000000000000000000000010000000000000000000000000000001300000000000000b10000000000000000000000000000000000000003000000110000000000000000000000000000001000000000000000000000000000000050000000000000006100000000000000000000000000000006000000010000000b00000000000000000000000000000001000000000000000000000000000000210000000000000040000000000000000000000000000000000000000300000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000050000000000000000000020012000000010000000000000000000000000000000000000000000000000074635f6464615f736b636f6c69646c6f6700d65f03c0d2800008d2800007d2800006d28000028b0700408a0600e7cb0703e79a1f03e7ab0600488b0700428a0600e7cb0703e79a1f03e7ab0700428a0600e7cb0703e79a1f03e7ab01000212800006006261746d79732e006261747274732e00747865742e0062617472747368732e000001000500400000000000400000000000000000000000f4000000000000000000000000000000000000000100b70001000000000000000000010102464c457f

def goldAddArmProg : List (DecodedInstr Arm64Instr) := [
  ⟨0, 4, .movWide true false 6 0 0⟩,
  ⟨4, 4, .aluReg .adds true 2 0 1 0 0⟩,
  ⟨8, 4, .aluReg .adc true 7 31 31 0 0⟩,
  ⟨12, 4, .aluReg .sub true 7 31 7 0 0⟩,
  ⟨16, 4, .aluReg .andOp true 7 7 6 0 0⟩,
  ⟨20, 4, .aluReg .adds true 2 2 7 0 0⟩,
  ⟨24, 4, .aluReg .adc true 7 31 31 0 0⟩,
  ⟨28, 4, .aluReg .sub true 7 31 7 0 0⟩,
  ⟨32, 4, .aluReg .andOp true 7 7 6 0 0⟩,
  ⟨36, 4, .aluReg .add true 2 2 7 0 0⟩,
  ⟨40, 4, .aluReg .adds true 8 2 6 0 0⟩,
  ⟨44, 4, .aluReg .adc true 7 31 31 0 0⟩,
  ⟨48, 4, .aluReg .sub true 7 31 7 0 0⟩,
  ⟨52, 4, .aluReg .andOp true 7 7 6 0 0⟩,
  ⟨56, 4, .aluReg .add true 0 2 7 0 0⟩,
  ⟨60, 4, .movWide false true 2 0 0⟩,
  ⟨64, 4, .movWide false true 6 0 0⟩,
  ⟨68, 4, .movWide false true 7 0 0⟩,
  ⟨72, 4, .movWide false true 8 0 0⟩,
  ⟨76, 4, .ret⟩]

private def goldAddArmMc (a b : UInt64) : UInt64 :=
  armCanon (foldCarry (foldCarry (a + b) (decide (a.toNat + b.toNat ≥ 0x10000000000000000))).1
    (foldCarry (a + b) (decide (a.toNat + b.toNat ≥ 0x10000000000000000))).2).1

private theorem goldAddArmMc_toNat (a b : UInt64) :
    (goldAddArmMc a b).toNat = (a.toNat + b.toNat) % GOLDILOCKS_P := by
  have h := goldAddMc_toNat a b
  unfold goldAddMc at h
  rw [goldCanon_toNat] at h
  unfold goldAddArmMc
  rw [armCanon_toNat]
  exact h

private theorem goldAddArm_reaches (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (hi : Bank16 UInt64) (v : Bank32 Vec128) (cf zf dit : Bool) (m : UInt64 → UInt8) :
    ∃ s2, ExecReachesArm64 goldAddArmProg 19
        ⟨0, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
          v, cf, zf, dit, false, m⟩ s2 ∧
      ∃ cf' zf',
        s2 = ⟨76, ⟨⟨goldAddArmMc r0 r1, r1, 0, r3, r4, r5, 0, 0, 0, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
          v, cf', zf', dit, false, m⟩ := by
  suffices hS : ∃ s2, StepsArm64 goldAddArmProg 19
        ⟨0, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
          v, cf, zf, dit, false, m⟩ s2 ∧
      ∃ cf' zf',
        s2 = ⟨76, ⟨⟨goldAddArmMc r0 r1, r1, 0, r3, r4, r5, 0, 0, 0, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
          v, cf', zf', dit, false, m⟩ by
    rcases hS with ⟨s2, hs, hp⟩
    exact ⟨s2, hs.toExecReaches, hp⟩
  iterate 19
    apply StepsArm64_step_ex rfl rfl
    · simp only [stepArm64_movn32, stepArm64_addsRR, stepArm64_adcRR, stepArm64_subRR,
        stepArm64_andRR, stepArm64_addRR, stepArm64_movz,
        u64_shl_zero_zero, uint64_evalAdd_eq, uint64_evalSub_eq,
        armAdcZero, u64_neg_cond, movn32_zero, condAll_and_eps,
        armGet_31, armGet_0, armGet_1, armGet_2, armGet_6, armGet_7,
        armSet_0, armSet_2, armSet_6, armSet_7, armSet_8]
      rfl
  exact ⟨_, StepsArm64.zero _, _, _, rfl⟩

theorem elf_goldilocks_add_ct_aarch64_functional_and_ct :
    ∃ slice : ElfFuncSlice,
      extractElfFuncBytes goldAddArmElf "goldilocks_add_ct" = some slice ∧
      ElfSliceOk goldAddArmElf slice ∧
      checkElfFuncThreeWayNI goldAddArmElf "goldilocks_add_ct"
        (mkContract "goldilocks_add_ct" [] [] [2, 6, 7, 8]) = true ∧
      ElfSliceThreeWayNISafe slice (mkContract "goldilocks_add_ct" [] [] [2, 6, 7, 8]) ∧
      slice.code = goldAddArmBytes ∧
      decodeArm64Slice slice.code = some goldAddArmProg ∧
      ∀ (st : Arm64BvState), st.pc = 0 → st.halted = false →
        (∃ st19 tr19, execDecodedArm64 slice.code 19 st = some (st19, tr19) ∧ st19.halted = false) ∧
        ∀ extra : Nat, ∃ st' trace,
          execDecodedArm64 slice.code (20 + extra) st = some (st', trace) ∧
          st'.halted = true ∧ st'.pc = 76 ∧ trace.length = 20 ∧
          st'.gpr.get 0 =
            BitVec.ofNat 64 (((st.gpr.get 0).toNat + (st.gpr.get 1).toNat) % GOLDILOCKS_P) ∧
          Arm64CalleeSavedPreserved st st' ∧
          st'.mem = st.mem ∧
          st'.gpr.get 2 = 0#64 ∧ st'.gpr.get 6 = 0#64 ∧
          st'.gpr.get 7 = 0#64 ∧ st'.gpr.get 8 = 0#64 := by
  have hNI : checkElfFuncThreeWayNI goldAddArmElf "goldilocks_add_ct"
      (mkContract "goldilocks_add_ct" [] [] [2, 6, 7, 8]) = true := by decide +kernel
  obtain ⟨slice, hExt, hOk, hSafe⟩ := checkElfFuncThreeWayNI_sound hNI
  have hCode : slice.code = goldAddArmBytes := by
    have hC : (extractElfFuncBytes goldAddArmElf "goldilocks_add_ct").map ElfFuncSlice.code =
        some goldAddArmBytes := by decide +kernel
    rw [hExt] at hC; exact Option.some.inj hC
  have hDec : decodeArm64Slice slice.code = some goldAddArmProg := by rw [hCode]; decide +kernel
  refine ⟨slice, hExt, hOk, hNI, hSafe, hCode, hDec, ?_⟩
  intro st hpc hh
  rcases st with ⟨pc, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
    v, cf, zf, dit, hlt, mem⟩
  dsimp only at hpc hh; subst hpc hh
  let st0 : Arm64BvState := ⟨0, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩, v, cf, zf, dit, false, mem⟩
  obtain ⟨_, h19, cfa, zfa, rfl⟩ :=
    goldAddArm_reaches (UInt64.ofBitVec r0) (UInt64.ofBitVec r1) (UInt64.ofBitVec r2)
      (UInt64.ofBitVec r3) (UInt64.ofBitVec r4) (UInt64.ofBitVec r5) (UInt64.ofBitVec r6)
      (UInt64.ofBitVec r7) (UInt64.ofBitVec r8) (UInt64.ofBitVec r9) (UInt64.ofBitVec r10)
      (UInt64.ofBitVec r11) (UInt64.ofBitVec r12) (UInt64.ofBitVec r13) (UInt64.ofBitVec r14)
      (UInt64.ofBitVec r15) (bank16ToU64 hi) v cf zf dit (fun a => mem a.toBitVec)
  obtain ⟨hPre, hPost⟩ := execDecodedArm64_ret_of_reaches st0 hDec rfl h19 rfl rfl
  refine ⟨hPre, fun extra => ?_⟩
  obtain ⟨tr, hExec, hL⟩ := hPost extra
  refine ⟨_, tr, hExec, rfl, rfl, hL, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · dsimp
    apply bv_ofU64_eq_ofNat _ (mod_goldilocks_lt_u64 _)
    rw [goldAddArmMc_toNat, UInt64.toNat_ofBitVec, UInt64.toNat_ofBitVec]
  · exact arm64_callee_saved_of_hi_vec
  · exact mem_roundtrip mem

def goldSubArmSymBytes : List UInt8 :=
  [0x67, 0x6f, 0x6c, 0x64, 0x69, 0x6c, 0x6f, 0x63, 0x6b, 0x73, 0x5f, 0x73, 0x75, 0x62, 0x5f, 0x63, 0x74]

def goldSubArmBytes : List UInt8 :=
  wordsToBytesLE [0x12800006, 0xAB060008, 0x9A1F03E7, 0xCB0703E7, 0x8A0600E7, 0x8B070002,
                  0xAB060028, 0x9A1F03E7, 0xCB0703E7, 0x8A0600E7, 0x8B070023,
                  0xEB030042, 0xDA1F03E7, 0xD3607CC4, 0xB2400084, 0x8A0400E7, 0x8B070040,
                  0xD2800002, 0xD2800003, 0xD2800004, 0xD2800006, 0xD2800007, 0xD2800008,
                  0xD65F03C0]

def goldSubArmElf : Bytes :=
  Bytes.ofNat 580 0x1800000000000000080000000100000003000000000000003000000000000000d4000000000000000000000000000000000000000200000019000000000000000000000000000000010000000000000000000000000000001300000000000000c10000000000000000000000000000000000000003000000110000000000000000000000000000001000000000000000000000000000000060000000000000006100000000000000000000000000000006000000010000000b00000000000000000000000000000001000000000000000000000000000000210000000000000040000000000000000000000000000000000000000300000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000060000000000000000000020012000000010000000000000000000000000000000000000000000000000074635f6275735f736b636f6c69646c6f6700d65f03c0d2800008d2800007d2800006d2800004d2800003d28000028b0700408a0400e7b2400084d3607cc4da1f03e7eb0300428b0700238a0600e7cb0703e79a1f03e7ab0600288b0700028a0600e7cb0703e79a1f03e7ab06000812800006006261746d79732e006261747274732e00747865742e0062617472747368732e00000100050040000000000040000000000000000000000104000000000000000000000000000000000000000100b70001000000000000000000010102464c457f

def goldSubArmProg : List (DecodedInstr Arm64Instr) := [
  ⟨0, 4, .movWide true false 6 0 0⟩,
  ⟨4, 4, .aluReg .adds true 8 0 6 0 0⟩,
  ⟨8, 4, .aluReg .adc true 7 31 31 0 0⟩,
  ⟨12, 4, .aluReg .sub true 7 31 7 0 0⟩,
  ⟨16, 4, .aluReg .andOp true 7 7 6 0 0⟩,
  ⟨20, 4, .aluReg .add true 2 0 7 0 0⟩,
  ⟨24, 4, .aluReg .adds true 8 1 6 0 0⟩,
  ⟨28, 4, .aluReg .adc true 7 31 31 0 0⟩,
  ⟨32, 4, .aluReg .sub true 7 31 7 0 0⟩,
  ⟨36, 4, .aluReg .andOp true 7 7 6 0 0⟩,
  ⟨40, 4, .aluReg .add true 3 1 7 0 0⟩,
  ⟨44, 4, .aluReg .subs true 2 2 3 0 0⟩,
  ⟨48, 4, .aluReg .sbc true 7 31 31 0 0⟩,
  ⟨52, 4, .ubfm true 4 6 32 31⟩,
  ⟨56, 4, .aluImm .orr true 4 4 1⟩,
  ⟨60, 4, .aluReg .andOp true 7 7 4 0 0⟩,
  ⟨64, 4, .aluReg .add true 0 2 7 0 0⟩,
  ⟨68, 4, .movWide false true 2 0 0⟩,
  ⟨72, 4, .movWide false true 3 0 0⟩,
  ⟨76, 4, .movWide false true 4 0 0⟩,
  ⟨80, 4, .movWide false true 6 0 0⟩,
  ⟨84, 4, .movWide false true 7 0 0⟩,
  ⟨88, 4, .movWide false true 8 0 0⟩,
  ⟨92, 4, .ret⟩]

private def goldSubArmMc (a b : UInt64) : UInt64 :=
  (armCanon a - armCanon b) +
    (if decide ((armCanon a).toNat ≥ (armCanon b).toNat) then 0 else 18446744069414584321)

private theorem u64_eps_lsl32_orr1 :
    ((0xFFFFFFFF : UInt64) <<< UInt64.ofNat (64 - 32)) ||| 1 = 18446744069414584321 := by
  decide

private theorem condNone_and_p (c : Bool) :
    (if c then (0 : UInt64) else 0xFFFFFFFFFFFFFFFF) &&& 18446744069414584321 =
      if c then 0 else 18446744069414584321 := by
  cases c <;> decide

private theorem goldSubArmMc_toNat (a b : UInt64) :
    (goldSubArmMc a b).toNat =
      (a.toNat + GOLDILOCKS_P - b.toNat % GOLDILOCKS_P) % GOLDILOCKS_P := by
  have hx := armCanon_toNat a
  have hy := armCanon_toNat b
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  have hP : (18446744069414584321 : UInt64).toNat = 18446744069414584321 := rfl
  have h0 : (0 : UInt64).toNat = 0 := rfl
  unfold goldSubArmMc
  have hx' : (armCanon a).toNat = a.toNat % 18446744069414584321 := hx
  have hy' : (armCanon b).toNat = b.toNat % 18446744069414584321 := hy
  show _ = (a.toNat + 18446744069414584321 - b.toNat % 18446744069414584321) % 18446744069414584321
  if h : (armCanon a).toNat ≥ (armCanon b).toNat then
    rw [decide_eq_true h, ite_eq_left rfl, UInt64.toNat_add, UInt64.toNat_sub, h0, h64]
    omega
  else
    rw [decide_eq_false h, ite_eq_right (by decide), UInt64.toNat_add, UInt64.toNat_sub, hP, h64]
    omega

private theorem goldSubArm_reaches (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (hi : Bank16 UInt64) (v : Bank32 Vec128) (cf zf dit : Bool) (m : UInt64 → UInt8) :
    ∃ s2, ExecReachesArm64 goldSubArmProg 23
        ⟨0, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
          v, cf, zf, dit, false, m⟩ s2 ∧
      ∃ cf' zf',
        s2 = ⟨92, ⟨⟨goldSubArmMc r0 r1, r1, 0, 0, 0, r5, 0, 0, 0, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
          v, cf', zf', dit, false, m⟩ := by
  suffices hS : ∃ s2, StepsArm64 goldSubArmProg 23
        ⟨0, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
          v, cf, zf, dit, false, m⟩ s2 ∧
      ∃ cf' zf',
        s2 = ⟨92, ⟨⟨goldSubArmMc r0 r1, r1, 0, 0, 0, r5, 0, 0, 0, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
          v, cf', zf', dit, false, m⟩ by
    rcases hS with ⟨s2, hs, hp⟩
    exact ⟨s2, hs.toExecReaches, hp⟩
  iterate 23
    apply StepsArm64_step_ex rfl rfl
    · simp only [stepArm64_movn32, stepArm64_addsRR, stepArm64_adcRR, stepArm64_subRR,
        stepArm64_andRR, stepArm64_addRR, stepArm64_subsRR, stepArm64_sbcRR,
        stepArm64_lsl32, stepArm64_orrImm, stepArm64_movz,
        u64_shl_zero_zero, uint64_evalAdd_eq, uint64_evalSub_eq,
        armAdcZero, armSbcZero, u64_neg_cond, movn32_zero, condAll_and_eps,
        u64_eps_lsl32_orr1, condNone_and_p,
        armGet_31, armGet_0, armGet_1, armGet_2, armGet_3, armGet_4, armGet_6, armGet_7,
        armSet_0, armSet_2, armSet_3, armSet_4, armSet_6, armSet_7, armSet_8]
      rfl
  exact ⟨_, StepsArm64.zero _, _, _, rfl⟩

theorem elf_goldilocks_sub_ct_aarch64_functional_and_ct :
    ∃ slice : ElfFuncSlice,
      extractElfFuncBytes goldSubArmElf "goldilocks_sub_ct" = some slice ∧
      ElfSliceOk goldSubArmElf slice ∧
      checkElfFuncThreeWayNI goldSubArmElf "goldilocks_sub_ct"
        (mkContract "goldilocks_sub_ct" [] [] [2, 3, 4, 6, 7, 8]) = true ∧
      ElfSliceThreeWayNISafe slice (mkContract "goldilocks_sub_ct" [] [] [2, 3, 4, 6, 7, 8]) ∧
      slice.code = goldSubArmBytes ∧
      decodeArm64Slice slice.code = some goldSubArmProg ∧
      ∀ (st : Arm64BvState), st.pc = 0 → st.halted = false →
        (∃ st23 tr23, execDecodedArm64 slice.code 23 st = some (st23, tr23) ∧ st23.halted = false) ∧
        ∀ extra : Nat, ∃ st' trace,
          execDecodedArm64 slice.code (24 + extra) st = some (st', trace) ∧
          st'.halted = true ∧ st'.pc = 92 ∧ trace.length = 24 ∧
          st'.gpr.get 0 =
            BitVec.ofNat 64 (((st.gpr.get 0).toNat + GOLDILOCKS_P -
              (st.gpr.get 1).toNat % GOLDILOCKS_P) % GOLDILOCKS_P) ∧
          Arm64CalleeSavedPreserved st st' ∧
          st'.mem = st.mem ∧
          st'.gpr.get 2 = 0#64 ∧ st'.gpr.get 3 = 0#64 ∧ st'.gpr.get 4 = 0#64 ∧
          st'.gpr.get 6 = 0#64 ∧ st'.gpr.get 7 = 0#64 ∧ st'.gpr.get 8 = 0#64 := by
  have hNI : checkElfFuncThreeWayNI goldSubArmElf "goldilocks_sub_ct"
      (mkContract "goldilocks_sub_ct" [] [] [2, 3, 4, 6, 7, 8]) = true := by decide +kernel
  obtain ⟨slice, hExt, hOk, hSafe⟩ := checkElfFuncThreeWayNI_sound hNI
  have hCode : slice.code = goldSubArmBytes := by
    have hC : (extractElfFuncBytes goldSubArmElf "goldilocks_sub_ct").map ElfFuncSlice.code =
        some goldSubArmBytes := by decide +kernel
    rw [hExt] at hC; exact Option.some.inj hC
  have hDec : decodeArm64Slice slice.code = some goldSubArmProg := by rw [hCode]; decide +kernel
  refine ⟨slice, hExt, hOk, hNI, hSafe, hCode, hDec, ?_⟩
  intro st hpc hh
  rcases st with ⟨pc, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
    v, cf, zf, dit, hlt, mem⟩
  dsimp only at hpc hh; subst hpc hh
  let st0 : Arm64BvState := ⟨0, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩, v, cf, zf, dit, false, mem⟩
  obtain ⟨_, h23, cfa, zfa, rfl⟩ :=
    goldSubArm_reaches (UInt64.ofBitVec r0) (UInt64.ofBitVec r1) (UInt64.ofBitVec r2)
      (UInt64.ofBitVec r3) (UInt64.ofBitVec r4) (UInt64.ofBitVec r5) (UInt64.ofBitVec r6)
      (UInt64.ofBitVec r7) (UInt64.ofBitVec r8) (UInt64.ofBitVec r9) (UInt64.ofBitVec r10)
      (UInt64.ofBitVec r11) (UInt64.ofBitVec r12) (UInt64.ofBitVec r13) (UInt64.ofBitVec r14)
      (UInt64.ofBitVec r15) (bank16ToU64 hi) v cf zf dit (fun a => mem a.toBitVec)
  obtain ⟨hPre, hPost⟩ := execDecodedArm64_ret_of_reaches st0 hDec rfl h23 rfl rfl
  refine ⟨hPre, fun extra => ?_⟩
  obtain ⟨tr, hExec, hL⟩ := hPost extra
  refine ⟨_, tr, hExec, rfl, rfl, hL, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · dsimp
    apply bv_ofU64_eq_ofNat _ (mod_goldilocks_lt_u64 _)
    rw [goldSubArmMc_toNat, UInt64.toNat_ofBitVec, UInt64.toNat_ofBitVec]
  · exact arm64_callee_saved_of_hi_vec
  · exact mem_roundtrip mem

#export_eqns ExecReachesX86

theorem current_aarch64_rlib_distinct_names :
    allDistinctStrings ((extractAllRlibFuncs currentAarch64RlibArchiveBytes).map ElfFuncSlice.name) = true := by
  rw [currentAarch64_symbol_names_exact]
  decide +kernel

theorem current_x86_rlib_distinct_names :
    allDistinctStrings ((extractAllRlibFuncs currentX86RlibArchiveBytes).map ElfFuncSlice.name) = true := by
  rw [currentX86_symbol_names_exact]
  decide +kernel

#export_eqns Arm64CalleeSavedPreserved goldDot2Mc

end Qsag
end
