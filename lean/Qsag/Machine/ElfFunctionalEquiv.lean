module

public import Qsag.Math.Goldilocks
public import Qsag.Math.BinaryTower
public import Qsag.Oracle.Keccak
public import Qsag.Machine.ElfBinaryVerify
public import Qsag.Machine.ElfFixtureVerify
public import Qsag.Machine.McRefine
public import Qsag.Machine.SydTvTranslationValidation
import all Qsag.Machine.SydTvTranslationValidation
import Qsag.Math.Constructive
import all Qsag.Machine.ElfFixtureSlices
import all Qsag.Machine.ElfParse
import all Qsag.Machine.ElfInvCerts
import all Qsag.Machine.ElfBinaryVerify
import all Qsag.Machine.McRefine
import all Qsag.Math.BinaryTower
import all Qsag.Oracle.Keccak
import Qsag.Tactic.AssuranceKit

/-!
# Compiled-Byte Machine-Code Functional Equivalence & Unified CT-NI Certificates (`ElfFunctionalEquiv.lean`)

Lean 4.35 functional equivalence layer for selected historical and current compiled `.rlib` / `ELF64`
machine-code byte slices (`CompiledRlibFixtures.lean`, `ElfParse.lean`, `ElfBinaryVerify.lean`)
to canonical mathematical and cryptographic specifications (`Goldilocks.lean`, `BinaryTower.lean`,
`Keccak.lean`, `ConstantTimeIsa.lean`).
The current_ declarations bind 12 live kernels, with longer epilogue budgets where needed.
The historical declarations retain frozen challenge bindings; complete functional coverage
for all 28 live kernels remains open. Freshness is checked independently by the ELF auditor.
-/

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

def bank16ToU64 (b : Bank16 (BitVec 64)) : Bank16 UInt64 :=
  ⟨UInt64.ofBitVec b.r0, UInt64.ofBitVec b.r1, UInt64.ofBitVec b.r2, UInt64.ofBitVec b.r3,
   UInt64.ofBitVec b.r4, UInt64.ofBitVec b.r5, UInt64.ofBitVec b.r6, UInt64.ofBitVec b.r7,
   UInt64.ofBitVec b.r8, UInt64.ofBitVec b.r9, UInt64.ofBitVec b.r10, UInt64.ofBitVec b.r11,
   UInt64.ofBitVec b.r12, UInt64.ofBitVec b.r13, UInt64.ofBitVec b.r14, UInt64.ofBitVec b.r15⟩

def bank16OfU64 (b : Bank16 UInt64) : Bank16 (BitVec 64) :=
  ⟨b.r0.toBitVec, b.r1.toBitVec, b.r2.toBitVec, b.r3.toBitVec,
   b.r4.toBitVec, b.r5.toBitVec, b.r6.toBitVec, b.r7.toBitVec,
   b.r8.toBitVec, b.r9.toBitVec, b.r10.toBitVec, b.r11.toBitVec,
   b.r12.toBitVec, b.r13.toBitVec, b.r14.toBitVec, b.r15.toBitVec⟩

def bank32ToU64 (b : Bank32 (BitVec 64)) : Bank32 UInt64 :=
  ⟨bank16ToU64 b.lo, bank16ToU64 b.hi⟩

def bank32OfU64 (b : Bank32 UInt64) : Bank32 (BitVec 64) :=
  ⟨bank16OfU64 b.lo, bank16OfU64 b.hi⟩

/-- Lossless embedding of `X86BvState` into `ElfBinaryVerify.X86State`. -/
def X86BvState.toX86State (st : X86BvState) : X86State :=
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
def X86BvState.ofX86State (s : X86State) : X86BvState :=
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
def Arm64BvState.toArm64State (st : Arm64BvState) : Arm64State :=
  { pc := st.pc
    gpr := bank32ToU64 st.gpr
    vec := st.vec
    cf := st.cf
    zf := st.zf
    dit := st.dit
    halted := st.halted
    mem := fun addr => st.mem addr.toBitVec }

/-- Lossless projection from `ElfBinaryVerify.Arm64State` into `Arm64BvState`. -/
def Arm64BvState.ofArm64State (s : Arm64State) : Arm64BvState :=
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
  st'.gpr.get 4 = st.gpr.get 4 ∧
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

private theorem u64_roundtrip (x : BitVec 64) : (UInt64.ofBitVec x).toBitVec = x :=
  UInt64.toBitVec_ofBitVec x

private theorem mem_roundtrip (mem : BitVec 64 → UInt8) :
    (fun addr => mem (UInt64.ofBitVec addr).toBitVec) = mem := by
  funext addr
  exact congrArg mem (UInt64.toBitVec_ofBitVec addr)

private theorem bank16_roundtrip (hi : Bank16 (BitVec 64)) :
    bank16OfU64 (bank16ToU64 hi) = hi := by
  rcases hi with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  simp only [bank16OfU64, bank16ToU64, UInt64.toBitVec_ofBitVec]

private theorem b32get_0 {α : Type} (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : α)
    (hi : Bank16 α) :
    Bank32.get ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩ 0 = r0 := rfl
private theorem b32get_1 {α : Type} (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : α)
    (hi : Bank16 α) :
    Bank32.get ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩ 1 = r1 := rfl
private theorem b32get_2 {α : Type} (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : α)
    (hi : Bank16 α) :
    Bank32.get ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩ 2 = r2 := rfl

attribute [local simp]
  X86BvState.ofX86State Arm64BvState.ofArm64State bank16OfU64 bank32OfU64
  b16get_0 b16get_1 b16get_2 b16get_3 b16get_4 b16get_5 b16get_6 b16get_7
  b16get_8 b16get_9 b16get_10 b16get_11 b16get_12 b16get_13 b16get_14 b16get_15
  b32get_0 b32get_1 b32get_2

private theorem x86_callee_saved_of_roundtrip
    {pc1 : Nat} {r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : BitVec 64}
    {u0 u1 u2 u6 u7 u8 u9 u10 u11 : UInt64}
    {y0 y1 : Bank16 Vec256} {cf0 o0 zf0 dy0 cf1 o1 zf1 dy1 h1 : Bool}
    {mem0 : BitVec 64 → UInt8} {mem1 : UInt64 → UInt8} :
    X86CalleeSavedPreserved
      ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        y0, cf0, o0, zf0, dy0, false, mem0⟩
      (X86BvState.ofX86State
        ⟨pc1, ⟨u0, u1, u2, UInt64.ofBitVec r3, UInt64.ofBitVec r4, UInt64.ofBitVec r5,
          u6, u7, u8, u9, u10, u11,
          UInt64.ofBitVec r12, UInt64.ofBitVec r13, UInt64.ofBitVec r14, UInt64.ofBitVec r15⟩,
          y1, cf1, o1, zf1, dy1, h1, mem1⟩) :=
  ⟨u64_roundtrip r3, u64_roundtrip r4, u64_roundtrip r5,
   u64_roundtrip r12, u64_roundtrip r13, u64_roundtrip r14, u64_roundtrip r15⟩

private theorem arm64_callee_saved_of_hi_vec
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
      (runX86 prog (k + 1 + extra) s).1 = { sRet with halted := true } ∧
      (runX86 prog (k + 1 + extra) s).2.length = k + 1 := by
  have h0 := (hPre 0).1
  rw [Nat.add_zero] at h0
  have hs0 : (runX86 prog 0 sRet).1 = sRet := rfl
  have hAtK : (runX86 prog k s).1 = sRet := h0.trans hs0
  have hRetStep : ExecReachesX86 prog 1 sRet { sRet with halted := true } :=
    ExecReachesX86_step hh hf rfl
  have hFull := ExecReachesX86_trans hPre hRetStep
  refine ⟨hAtK, hAtK.symm ▸ hh, fun extra => ?_⟩
  have ⟨ef, lf⟩ := hFull extra
  have hHaltFst : (runX86 prog extra { sRet with halted := true }).1 =
      { sRet with halted := true } := runX86_halted_fst prog extra _ rfl
  have hHaltSnd : (runX86 prog extra { sRet with halted := true }).2 = [] :=
    runX86_halted_snd prog extra _ rfl
  exact ⟨ef.trans hHaltFst, by rw [lf, hHaltSnd]; simp⟩

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
        some (X86BvState.ofX86State ⟨pc1, gpr1, ymm1, cf1, o1, zf1, dy1, true, mem1⟩, tr) ∧
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

theorem x86_rlib_distinct_names :
    allDistinctStrings ((extractAllRlibFuncs x86RlibArchiveBytes).map ElfFuncSlice.name) = true := by
  rw [x86_rlib_symbol_names_exact]
  decide +kernel

theorem aarch64_rlib_distinct_names :
    allDistinctStrings ((extractAllRlibFuncs aarch64RlibArchiveBytes).map ElfFuncSlice.name) = true := by
  rw [aarch64_rlib_symbol_names_exact]
  decide +kernel

theorem extractRlibFuncBytes_x86_eq (symName : String) :
    extractRlibFuncBytes x86RlibArchiveBytes symName =
      x86ExtractedSlices.find? (fun s => s.name == symName) := by
  unfold extractRlibFuncBytes
  rw [x86_rlib_extracted_slices]

theorem extractRlibFuncBytes_aarch64_eq (symName : String) :
    extractRlibFuncBytes aarch64RlibArchiveBytes symName =
      aarch64ExtractedSlices.find? (fun s => s.name == symName) := by
  unfold extractRlibFuncBytes
  rw [aarch64_rlib_extracted_slices]

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

private theorem bv_ofU64_eq_ofNat {w : UInt64} {n : Nat} (h : w.toNat = n) (hn : n < 2 ^ 64) :
    w.toBitVec = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [UInt64.toNat_toBitVec, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

private theorem mod_goldilocks_lt_u64 (n : Nat) : n % GOLDILOCKS_P < 2 ^ 64 := by
  have hp : GOLDILOCKS_P < 2 ^ 64 := by decide
  exact Nat.lt_trans (Nat.mod_lt n (by decide)) hp

/-! ### §3.1 `qsag_asm_goldilocks_add_ct_x86_64` (`N = 17`, `retPc = 50`) -/

private theorem goldAddX86_reaches (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    ExecReachesX86 goldAddX86Prog 16
      ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        y, cf, o, zf, dy, false, m⟩
      ⟨50, ⟨goldAddMc r7 r6, 0, r2, r3, r4, r5, r6, r7, 0, 0, 0, r11, r12, r13, r14, r15⟩,
        y, false, false, true, dy, false, m⟩ := by
  apply StepsX86.toExecReaches
  iterate 16
    apply StepsX86.cons rfl rfl
    · simp only [stepX86_movRR, stepX86_addRR64, stepX86_sbbRR, stepX86_andRR, stepX86_movImm,
        stepX86_xorRR, maskGprWidth_true, mask32_xor_self, u64_zero_beq_zero,
        sbb32_self, sbb64_self, uint64_evalAdd_eq,
        b16get_0, b16get_1, b16get_6, b16get_7, b16get_8, b16get_9, b16get_10,
        b16set_0, b16set_1, b16set_8, b16set_9, b16set_10]
      rfl
  exact StepsX86.zero _

theorem rlib_goldilocks_add_ct_x86_64_functional_and_ct :
    ∃ slice m,
      extractRlibFuncBytes x86RlibArchiveBytes "qsag_asm_goldilocks_add_ct_x86_64" = some slice ∧
      m ∈ parseArArchive x86RlibArchiveBytes ∧
      ArPayloadOk x86RlibArchiveBytes m ∧
      checkElfFuncThreeWayNI m.payload "qsag_asm_goldilocks_add_ct_x86_64"
        (mkContract "qsag_asm_goldilocks_add_ct_x86_64" [4]) = true ∧
      ElfSliceThreeWayNISafe slice (mkContract "qsag_asm_goldilocks_add_ct_x86_64" [4]) ∧
      decodeX86Slice slice.code = some goldAddX86Prog ∧
      ∀ (st : X86BvState), st.pc = 0 → st.halted = false →
        (∃ st16 tr16, execDecodedX86 slice.code 16 st = some (st16, tr16) ∧ st16.halted = false) ∧
        ∀ extra : Nat, ∃ st' trace,
          execDecodedX86 slice.code (17 + extra) st = some (st', trace) ∧
          st'.halted = true ∧ st'.pc = 50 ∧ trace.length = 17 ∧
          st'.gpr.get 0 =
            BitVec.ofNat 64 (((st.gpr.get 7).toNat + (st.gpr.get 6).toNat) % GOLDILOCKS_P) ∧
          (st'.gpr.get 0).toNat =
            (Goldilocks.add (Goldilocks.ofNat (st.gpr.get 7).toNat) (Goldilocks.ofNat (st.gpr.get 6).toNat)).val ∧
          X86CalleeSavedPreserved st st' ∧
          st'.mem = st.mem ∧
          st'.gpr.get 1 = 0#64 ∧ st'.gpr.get 8 = 0#64 ∧
          st'.gpr.get 9 = 0#64 ∧ st'.gpr.get 10 = 0#64 := by
  cases hFind : x86ExtractedSlices.find? (fun s => s.name == "qsag_asm_goldilocks_add_ct_x86_64") with
  | none => exfalso; revert hFind; decide +kernel
  | some slice =>
    have hExt : extractRlibFuncBytes x86RlibArchiveBytes "qsag_asm_goldilocks_add_ct_x86_64" = some slice := by
      rw [extractRlibFuncBytes_x86_eq, hFind]
    have hNI : checkElfSliceThreeWayNI slice (mkContract "qsag_asm_goldilocks_add_ct_x86_64" [4]) = true := by
      have hCheck : ((x86ExtractedSlices.find? (fun s => s.name == "qsag_asm_goldilocks_add_ct_x86_64")).map
          (fun sl => checkElfSliceThreeWayNI sl (mkContract "qsag_asm_goldilocks_add_ct_x86_64" [4]))) =
          some true := by decide +kernel
      rw [hFind] at hCheck
      exact Option.some.inj hCheck
    have hDec : decodeX86Slice slice.code = some goldAddX86Prog := by
      have hD : (x86ExtractedSlices.find? (fun s => s.name == "qsag_asm_goldilocks_add_ct_x86_64")).bind
          (fun sl => decodeX86Slice sl.code) = some goldAddX86Prog := by decide +kernel
      rw [hFind] at hD
      exact hD
    obtain ⟨m, hm, hPay, _, hMemNI, _, hSafe⟩ :=
      extractRlibFuncBytes_member_ni_sound x86_rlib_distinct_names hExt hNI
    refine ⟨slice, m, hExt, hm, hPay, hMemNI, hSafe, hDec, ?_⟩
    intro st hpc hh
    rcases st with ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
      y, cf, o, zf, dy, hlt, mem⟩
    dsimp only at hpc hh; subst hpc hh
    let st0 : X86BvState := ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, mem⟩
    obtain ⟨hPre, hPost⟩ := execDecodedX86_ret_of_reaches st0 hDec rfl
      (goldAddX86_reaches (UInt64.ofBitVec r0) (UInt64.ofBitVec r1) (UInt64.ofBitVec r2)
        (UInt64.ofBitVec r3) (UInt64.ofBitVec r4) (UInt64.ofBitVec r5) (UInt64.ofBitVec r6)
        (UInt64.ofBitVec r7) (UInt64.ofBitVec r8) (UInt64.ofBitVec r9) (UInt64.ofBitVec r10)
        (UInt64.ofBitVec r11) (UInt64.ofBitVec r12) (UInt64.ofBitVec r13) (UInt64.ofBitVec r14)
        (UInt64.ofBitVec r15) y cf o zf dy (fun a => mem a.toBitVec))
      rfl rfl
    refine ⟨hPre, fun extra => ?_⟩
    obtain ⟨tr, hExec, hL⟩ := hPost extra
    refine ⟨_, tr, hExec, rfl, rfl, hL, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · change (goldAddMc (UInt64.ofBitVec r7) (UInt64.ofBitVec r6)).toBitVec =
        BitVec.ofNat 64 ((r7.toNat + r6.toNat) % GOLDILOCKS_P)
      apply bv_ofU64_eq_ofNat _ (mod_goldilocks_lt_u64 _)
      rw [goldAddMc_toNat, UInt64.toNat_ofBitVec, UInt64.toNat_ofBitVec]
    · change ((goldAddMc (UInt64.ofBitVec r7) (UInt64.ofBitVec r6)).toBitVec).toNat =
        (Goldilocks.add (Goldilocks.ofNat r7.toNat) (Goldilocks.ofNat r6.toNat)).val
      rw [UInt64.toNat_toBitVec, goldAddMc_toNat, UInt64.toNat_ofBitVec, UInt64.toNat_ofBitVec,
        Goldilocks.add_val, Goldilocks.ofNat, Goldilocks.ofNat, Nat.add_mod]
    · exact x86_callee_saved_of_roundtrip
    · exact mem_roundtrip mem

/-! ### §3.2 `qsag_asm_goldilocks_sub_ct_x86_64` (`N = 23`, `retPc = 74`) -/

private theorem goldSubX86_reaches (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    ExecReachesX86 goldSubX86Prog 22
      ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        y, cf, o, zf, dy, false, m⟩
      ⟨74, ⟨goldSubMc r7 r6, 0, r2, r3, r4, r5, 0, r7, 0, 0, 0, r11, r12, r13, r14, r15⟩,
        y, false, false, true, dy, false, m⟩ := by
  apply StepsX86.toExecReaches
  iterate 22
    apply StepsX86.cons rfl rfl
    · simp only [stepX86_movRR, stepX86_addRR64, stepX86_subRR64, stepX86_sbbRR, stepX86_andRR,
        stepX86_movImm, stepX86_xorRR, maskGprWidth_true, mask32_xor_self, u64_zero_beq_zero,
        sbb64_self, uint64_evalAdd_eq, uint64_evalSub_eq,
        b16get_0, b16get_1, b16get_6, b16get_7, b16get_8, b16get_9, b16get_10,
        b16set_0, b16set_1, b16set_6, b16set_8, b16set_9, b16set_10]
      rfl
  exact StepsX86.zero _

theorem rlib_goldilocks_sub_ct_x86_64_functional_and_ct :
    ∃ slice m,
      extractRlibFuncBytes x86RlibArchiveBytes "qsag_asm_goldilocks_sub_ct_x86_64" = some slice ∧
      m ∈ parseArArchive x86RlibArchiveBytes ∧
      ArPayloadOk x86RlibArchiveBytes m ∧
      checkElfFuncThreeWayNI m.payload "qsag_asm_goldilocks_sub_ct_x86_64"
        (mkContract "qsag_asm_goldilocks_sub_ct_x86_64" [4]) = true ∧
      ElfSliceThreeWayNISafe slice (mkContract "qsag_asm_goldilocks_sub_ct_x86_64" [4]) ∧
      decodeX86Slice slice.code = some goldSubX86Prog ∧
      ∀ (st : X86BvState), st.pc = 0 → st.halted = false →
        (∃ st22 tr22, execDecodedX86 slice.code 22 st = some (st22, tr22) ∧ st22.halted = false) ∧
        ∀ extra : Nat, ∃ st' trace,
          execDecodedX86 slice.code (23 + extra) st = some (st', trace) ∧
          st'.halted = true ∧ st'.pc = 74 ∧ trace.length = 23 ∧
          st'.gpr.get 0 =
            BitVec.ofNat 64 (((st.gpr.get 7).toNat + GOLDILOCKS_P -
              (st.gpr.get 6).toNat % GOLDILOCKS_P) % GOLDILOCKS_P) ∧
          (st'.gpr.get 0).toNat =
            (Goldilocks.sub (Goldilocks.ofNat (st.gpr.get 7).toNat) (Goldilocks.ofNat (st.gpr.get 6).toNat)).val ∧
          X86CalleeSavedPreserved st st' ∧
          st'.mem = st.mem ∧
          st'.gpr.get 1 = 0#64 ∧ st'.gpr.get 6 = 0#64 ∧
          st'.gpr.get 8 = 0#64 ∧ st'.gpr.get 9 = 0#64 ∧ st'.gpr.get 10 = 0#64 := by
  cases hFind : x86ExtractedSlices.find? (fun s => s.name == "qsag_asm_goldilocks_sub_ct_x86_64") with
  | none => exfalso; revert hFind; decide +kernel
  | some slice =>
    have hExt : extractRlibFuncBytes x86RlibArchiveBytes "qsag_asm_goldilocks_sub_ct_x86_64" = some slice := by
      rw [extractRlibFuncBytes_x86_eq, hFind]
    have hNI : checkElfSliceThreeWayNI slice (mkContract "qsag_asm_goldilocks_sub_ct_x86_64" [4]) = true := by
      have hCheck : ((x86ExtractedSlices.find? (fun s => s.name == "qsag_asm_goldilocks_sub_ct_x86_64")).map
          (fun sl => checkElfSliceThreeWayNI sl (mkContract "qsag_asm_goldilocks_sub_ct_x86_64" [4]))) =
          some true := by decide +kernel
      rw [hFind] at hCheck
      exact Option.some.inj hCheck
    have hDec : decodeX86Slice slice.code = some goldSubX86Prog := by
      have hD : (x86ExtractedSlices.find? (fun s => s.name == "qsag_asm_goldilocks_sub_ct_x86_64")).bind
          (fun sl => decodeX86Slice sl.code) = some goldSubX86Prog := by decide +kernel
      rw [hFind] at hD
      exact hD
    obtain ⟨m, hm, hPay, _, hMemNI, _, hSafe⟩ :=
      extractRlibFuncBytes_member_ni_sound x86_rlib_distinct_names hExt hNI
    refine ⟨slice, m, hExt, hm, hPay, hMemNI, hSafe, hDec, ?_⟩
    intro st hpc hh
    rcases st with ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
      y, cf, o, zf, dy, hlt, mem⟩
    dsimp only at hpc hh; subst hpc hh
    let st0 : X86BvState := ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, mem⟩
    obtain ⟨hPre, hPost⟩ := execDecodedX86_ret_of_reaches st0 hDec rfl
      (goldSubX86_reaches (UInt64.ofBitVec r0) (UInt64.ofBitVec r1) (UInt64.ofBitVec r2)
        (UInt64.ofBitVec r3) (UInt64.ofBitVec r4) (UInt64.ofBitVec r5) (UInt64.ofBitVec r6)
        (UInt64.ofBitVec r7) (UInt64.ofBitVec r8) (UInt64.ofBitVec r9) (UInt64.ofBitVec r10)
        (UInt64.ofBitVec r11) (UInt64.ofBitVec r12) (UInt64.ofBitVec r13) (UInt64.ofBitVec r14)
        (UInt64.ofBitVec r15) y cf o zf dy (fun a => mem a.toBitVec))
      rfl rfl
    refine ⟨hPre, fun extra => ?_⟩
    obtain ⟨tr, hExec, hL⟩ := hPost extra
    refine ⟨_, tr, hExec, rfl, rfl, hL, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
    · change (goldSubMc (UInt64.ofBitVec r7) (UInt64.ofBitVec r6)).toBitVec =
        BitVec.ofNat 64 ((r7.toNat + GOLDILOCKS_P - r6.toNat % GOLDILOCKS_P) % GOLDILOCKS_P)
      apply bv_ofU64_eq_ofNat _ (mod_goldilocks_lt_u64 _)
      rw [goldSubMc_toNat, UInt64.toNat_ofBitVec, UInt64.toNat_ofBitVec]
    · change ((goldSubMc (UInt64.ofBitVec r7) (UInt64.ofBitVec r6)).toBitVec).toNat =
        (Goldilocks.sub (Goldilocks.ofNat r7.toNat) (Goldilocks.ofNat r6.toNat)).val
      rw [UInt64.toNat_toBitVec, goldSubMc_toNat, UInt64.toNat_ofBitVec, UInt64.toNat_ofBitVec,
        Goldilocks.sub_val, Goldilocks.ofNat, Goldilocks.ofNat]
      have ha : r7.toNat < 2 ^ 64 := r7.isLt
      have hb : r6.toNat < 2 ^ 64 := r6.isLt
      show (r7.toNat + 18446744069414584321 - r6.toNat % 18446744069414584321) % 18446744069414584321 =
        (r7.toNat % 18446744069414584321 + 18446744069414584321 - r6.toNat % 18446744069414584321) % 18446744069414584321
      omega
    · exact x86_callee_saved_of_roundtrip
    · exact mem_roundtrip mem

/-! ### §3.3 `qsag_asm_goldilocks_mul_ct_x86_64` (`N = 25`) & `qsag_asm_goldilocks_mul_ct_aarch64` (`N = 29`) -/

private theorem goldMulX86_reaches (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    ExecReachesX86 goldMulX86Prog 24
      ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        y, cf, o, zf, dy, false, m⟩
      ⟨76, ⟨goldMulMc r7 r6, 0, 0, r3, r4, r5, r6, r7, 0, 0, r10, r11, r12, r13, r14, r15⟩,
        y, false, false, true, dy, false, m⟩ := by
  apply StepsX86.toExecReaches
  iterate 24
    apply StepsX86.cons rfl rfl
    · simp only [stepX86_movRR, stepX86_mulx, stepX86_shr64, stepX86_shl64, stepX86_addRR64,
        stepX86_subRR64, stepX86_sbbRR, stepX86_andRR, stepX86_movImm, stepX86_xorRR,
        maskGprWidth_true, mask32_xor_self, u64_zero_beq_zero, sbb32_self, sbb64_self,
        uint64_evalAdd_eq, uint64_evalSub_eq,
        b16get_0, b16get_1, b16get_2, b16get_6, b16get_7, b16get_8, b16get_9,
        b16set_0, b16set_1, b16set_2, b16set_8, b16set_9]
      rfl
  exact StepsX86.zero _

theorem rlib_goldilocks_mul_ct_x86_64_functional_and_ct :
    ∃ slice m,
      extractRlibFuncBytes x86RlibArchiveBytes "qsag_asm_goldilocks_mul_ct_x86_64" = some slice ∧
      m ∈ parseArArchive x86RlibArchiveBytes ∧
      ArPayloadOk x86RlibArchiveBytes m ∧
      checkElfFuncThreeWayNI m.payload "qsag_asm_goldilocks_mul_ct_x86_64"
        (mkContract "qsag_asm_goldilocks_mul_ct_x86_64" [4]) = true ∧
      ElfSliceThreeWayNISafe slice (mkContract "qsag_asm_goldilocks_mul_ct_x86_64" [4]) ∧
      decodeX86Slice slice.code = some goldMulX86Prog ∧
      ∀ (st : X86BvState), st.pc = 0 → st.halted = false →
        (∃ st24 tr24, execDecodedX86 slice.code 24 st = some (st24, tr24) ∧ st24.halted = false) ∧
        ∀ extra : Nat, ∃ st' trace,
          execDecodedX86 slice.code (25 + extra) st = some (st', trace) ∧
          st'.halted = true ∧ st'.pc = 76 ∧ trace.length = 25 ∧
          st'.gpr.get 0 =
            BitVec.ofNat 64 (((st.gpr.get 7).toNat * (st.gpr.get 6).toNat) % GOLDILOCKS_P) ∧
          (st'.gpr.get 0).toNat =
            (Goldilocks.mul (Goldilocks.ofNat (st.gpr.get 7).toNat) (Goldilocks.ofNat (st.gpr.get 6).toNat)).val ∧
          X86CalleeSavedPreserved st st' ∧
          st'.mem = st.mem ∧
          st'.gpr.get 1 = 0#64 ∧ st'.gpr.get 2 = 0#64 ∧
          st'.gpr.get 8 = 0#64 ∧ st'.gpr.get 9 = 0#64 := by
  cases hFind : x86ExtractedSlices.find? (fun s => s.name == "qsag_asm_goldilocks_mul_ct_x86_64") with
  | none => exfalso; revert hFind; decide +kernel
  | some slice =>
    have hExt : extractRlibFuncBytes x86RlibArchiveBytes "qsag_asm_goldilocks_mul_ct_x86_64" = some slice := by
      rw [extractRlibFuncBytes_x86_eq, hFind]
    have hNI : checkElfSliceThreeWayNI slice (mkContract "qsag_asm_goldilocks_mul_ct_x86_64" [4]) = true := by
      have hCheck : ((x86ExtractedSlices.find? (fun s => s.name == "qsag_asm_goldilocks_mul_ct_x86_64")).map
          (fun sl => checkElfSliceThreeWayNI sl (mkContract "qsag_asm_goldilocks_mul_ct_x86_64" [4]))) =
          some true := by decide +kernel
      rw [hFind] at hCheck
      exact Option.some.inj hCheck
    have hDec : decodeX86Slice slice.code = some goldMulX86Prog := by
      have hD : (x86ExtractedSlices.find? (fun s => s.name == "qsag_asm_goldilocks_mul_ct_x86_64")).bind
          (fun sl => decodeX86Slice sl.code) = some goldMulX86Prog := by decide +kernel
      rw [hFind] at hD
      exact hD
    obtain ⟨m, hm, hPay, _, hMemNI, _, hSafe⟩ :=
      extractRlibFuncBytes_member_ni_sound x86_rlib_distinct_names hExt hNI
    refine ⟨slice, m, hExt, hm, hPay, hMemNI, hSafe, hDec, ?_⟩
    intro st hpc hh
    rcases st with ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
      y, cf, o, zf, dy, hlt, mem⟩
    dsimp only at hpc hh; subst hpc hh
    let st0 : X86BvState := ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, mem⟩
    obtain ⟨hPre, hPost⟩ := execDecodedX86_ret_of_reaches st0 hDec rfl
      (goldMulX86_reaches (UInt64.ofBitVec r0) (UInt64.ofBitVec r1) (UInt64.ofBitVec r2)
        (UInt64.ofBitVec r3) (UInt64.ofBitVec r4) (UInt64.ofBitVec r5) (UInt64.ofBitVec r6)
        (UInt64.ofBitVec r7) (UInt64.ofBitVec r8) (UInt64.ofBitVec r9) (UInt64.ofBitVec r10)
        (UInt64.ofBitVec r11) (UInt64.ofBitVec r12) (UInt64.ofBitVec r13) (UInt64.ofBitVec r14)
        (UInt64.ofBitVec r15) y cf o zf dy (fun a => mem a.toBitVec))
      rfl rfl
    refine ⟨hPre, fun extra => ?_⟩
    obtain ⟨tr, hExec, hL⟩ := hPost extra
    refine ⟨_, tr, hExec, rfl, rfl, hL, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · change (goldMulMc (UInt64.ofBitVec r7) (UInt64.ofBitVec r6)).toBitVec =
        BitVec.ofNat 64 ((r7.toNat * r6.toNat) % GOLDILOCKS_P)
      apply bv_ofU64_eq_ofNat _ (mod_goldilocks_lt_u64 _)
      rw [goldMulMc_toNat, UInt64.toNat_ofBitVec, UInt64.toNat_ofBitVec]
    · change ((goldMulMc (UInt64.ofBitVec r7) (UInt64.ofBitVec r6)).toBitVec).toNat =
        (Goldilocks.mul (Goldilocks.ofNat r7.toNat) (Goldilocks.ofNat r6.toNat)).val
      rw [UInt64.toNat_toBitVec, goldMulMc_toNat, UInt64.toNat_ofBitVec, UInt64.toNat_ofBitVec,
        Goldilocks.mul_val, Goldilocks.ofNat, Goldilocks.ofNat, Nat.mul_mod]
    · exact x86_callee_saved_of_roundtrip
    · exact mem_roundtrip mem

private theorem goldMulArm_reaches (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (hi : Bank16 UInt64) (v : Bank32 Vec128) (cf zf dit : Bool) (m : UInt64 → UInt8) :
    ExecReachesArm64 goldMulArmProg 28
      ⟨0, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        v, cf, zf, dit, false, m⟩
      ⟨112, ⟨⟨armCanon (goldMulArmPre r0 r1), r1, 0, 0, 0, 0, 0, 0, 0, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        v, decide ((goldMulArmPre r0 r1).toNat + (0xFFFFFFFF : UInt64).toNat ≥ 0x10000000000000000),
        goldMulArmPre r0 r1 + 0xFFFFFFFF == 0, dit, false, m⟩ := by
  apply StepsArm64.toExecReaches
  iterate 28
    apply StepsArm64.cons rfl rfl
    · simp only [stepArm64_mul, stepArm64_umulh, stepArm64_lsr64, stepArm64_lsl32, stepArm64_andImm,
        stepArm64_andRR, stepArm64_movn32, stepArm64_addRR, stepArm64_addsRR, stepArm64_subsRR,
        stepArm64_subRR, stepArm64_adcRR, stepArm64_sbcRR, stepArm64_movz,
        u64_shl_zero_zero, uint64_evalSub_eq, uint64_evalAdd_eq, armAdcZero, armSbcZero, u64_neg_cond,
        movn32_zero, condAll_and_eps, condNone_and_eps,
        armGet_31, armGet_0, armGet_1, armGet_2, armGet_3, armGet_4, armGet_5, armGet_6, armGet_7, armGet_8,
        armSet_0, armSet_2, armSet_3, armSet_4, armSet_5, armSet_6, armSet_7, armSet_8]
      rfl
  exact StepsArm64.zero _

theorem rlib_goldilocks_mul_ct_aarch64_functional_and_ct :
    ∃ slice m,
      extractRlibFuncBytes aarch64RlibArchiveBytes "qsag_asm_goldilocks_mul_ct_aarch64" = some slice ∧
      m ∈ parseArArchive aarch64RlibArchiveBytes ∧
      ArPayloadOk aarch64RlibArchiveBytes m ∧
      checkElfFuncThreeWayNI m.payload "qsag_asm_goldilocks_mul_ct_aarch64"
        (mkContract "qsag_asm_goldilocks_mul_ct_aarch64" []) = true ∧
      ElfSliceThreeWayNISafe slice (mkContract "qsag_asm_goldilocks_mul_ct_aarch64" []) ∧
      decodeArm64Slice slice.code = some goldMulArmProg ∧
      ∀ (st : Arm64BvState), st.pc = 0 → st.halted = false →
        (∃ st28 tr28, execDecodedArm64 slice.code 28 st = some (st28, tr28) ∧ st28.halted = false) ∧
        ∀ extra : Nat, ∃ st' trace,
          execDecodedArm64 slice.code (29 + extra) st = some (st', trace) ∧
          st'.halted = true ∧ st'.pc = 112 ∧ trace.length = 29 ∧
          st'.gpr.get 0 =
            BitVec.ofNat 64 (((st.gpr.get 0).toNat * (st.gpr.get 1).toNat) % GOLDILOCKS_P) ∧
          (st'.gpr.get 0).toNat =
            (Goldilocks.mul (Goldilocks.ofNat (st.gpr.get 0).toNat) (Goldilocks.ofNat (st.gpr.get 1).toNat)).val ∧
          Arm64CalleeSavedPreserved st st' ∧
          st'.mem = st.mem ∧
          (∀ r : Nat, 2 ≤ r → r ≤ 8 → st'.gpr.get r = 0#64) := by
  cases hFind : aarch64ExtractedSlices.find? (fun s => s.name == "qsag_asm_goldilocks_mul_ct_aarch64") with
  | none => exfalso; revert hFind; decide +kernel
  | some slice =>
    have hExt : extractRlibFuncBytes aarch64RlibArchiveBytes "qsag_asm_goldilocks_mul_ct_aarch64" = some slice := by
      rw [extractRlibFuncBytes_aarch64_eq, hFind]
    have hNI : checkElfSliceThreeWayNI slice (mkContract "qsag_asm_goldilocks_mul_ct_aarch64" []) = true := by
      have hCheck : ((aarch64ExtractedSlices.find? (fun s => s.name == "qsag_asm_goldilocks_mul_ct_aarch64")).map
          (fun sl => checkElfSliceThreeWayNI sl (mkContract "qsag_asm_goldilocks_mul_ct_aarch64" []))) =
          some true := by decide +kernel
      rw [hFind] at hCheck
      exact Option.some.inj hCheck
    have hDec : decodeArm64Slice slice.code = some goldMulArmProg := by
      have hD : (aarch64ExtractedSlices.find? (fun s => s.name == "qsag_asm_goldilocks_mul_ct_aarch64")).bind
          (fun sl => decodeArm64Slice sl.code) = some goldMulArmProg := by decide +kernel
      rw [hFind] at hD
      exact hD
    obtain ⟨m, hm, hPay, _, hMemNI, _, hSafe⟩ :=
      extractRlibFuncBytes_member_ni_sound aarch64_rlib_distinct_names hExt hNI
    refine ⟨slice, m, hExt, hm, hPay, hMemNI, hSafe, hDec, ?_⟩
    intro st hpc hh
    rcases st with ⟨pc, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
      v, cf, zf, dit, hlt, mem⟩
    dsimp only at hpc hh; subst hpc hh
    let st0 : Arm64BvState := ⟨0, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩, v, cf, zf, dit, false, mem⟩
    obtain ⟨hPre, hPost⟩ := execDecodedArm64_ret_of_reaches st0 hDec rfl
      (goldMulArm_reaches (UInt64.ofBitVec r0) (UInt64.ofBitVec r1) (UInt64.ofBitVec r2)
        (UInt64.ofBitVec r3) (UInt64.ofBitVec r4) (UInt64.ofBitVec r5) (UInt64.ofBitVec r6)
        (UInt64.ofBitVec r7) (UInt64.ofBitVec r8) (UInt64.ofBitVec r9) (UInt64.ofBitVec r10)
        (UInt64.ofBitVec r11) (UInt64.ofBitVec r12) (UInt64.ofBitVec r13) (UInt64.ofBitVec r14)
        (UInt64.ofBitVec r15) (bank16ToU64 hi) v cf zf dit (fun a => mem a.toBitVec))
      rfl rfl
    refine ⟨hPre, fun extra => ?_⟩
    obtain ⟨tr, hExec, hL⟩ := hPost extra
    refine ⟨_, tr, hExec, rfl, rfl, hL, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp
      apply bv_ofU64_eq_ofNat _ (mod_goldilocks_lt_u64 _)
      rw [goldMulArm_toNat, UInt64.toNat_ofBitVec, UInt64.toNat_ofBitVec]
    · dsimp
      rw [UInt64.toNat_toBitVec, goldMulArm_toNat, UInt64.toNat_ofBitVec, UInt64.toNat_ofBitVec,
        Goldilocks.mul_val, Goldilocks.ofNat, Goldilocks.ofNat, Nat.mul_mod]
    · exact arm64_callee_saved_of_hi_vec
    · exact mem_roundtrip mem
    · intro r hr1 hr2
      dsimp
      match r, hr1, hr2 with
      | 2, _, _ => rfl | 3, _, _ => rfl | 4, _, _ => rfl | 5, _, _ => rfl
      | 6, _, _ => rfl | 7, _, _ => rfl | 8, _, _ => rfl
      | n + 9, _, h => exact absurd h (by omega)

/-! ### §3.4 `qsag_asm_goldilocks_pow7_ct_x86_64` (`N = 85`, `retPc = 265`) -/

def goldPow7X86Prog : List (DecodedInstr X86Instr) := [
  ⟨0, 3, .movRegReg true 11 7⟩,
  ⟨3, 6, .movImm false 10 4294967295⟩,
  ⟨9, 3, .movRegReg true 2 11⟩, ⟨12, 5, .mulx 1 0 11⟩, ⟨17, 3, .movRegReg true 2 1⟩,
  ⟨20, 4, .shiftImm .shr true 1 32⟩, ⟨24, 2, .movRegReg false 2 2⟩,
  ⟨26, 3, .aluRegReg .sub true 0 1⟩, ⟨29, 3, .aluRegReg .sbb false 8 8⟩,
  ⟨32, 3, .aluRegReg .sub true 0 8⟩, ⟨35, 3, .movRegReg true 9 2⟩,
  ⟨38, 4, .shiftImm .shl true 9 32⟩, ⟨42, 3, .aluRegReg .sub true 9 2⟩,
  ⟨45, 3, .aluRegReg .add true 0 9⟩, ⟨48, 3, .aluRegReg .sbb false 8 8⟩,
  ⟨51, 3, .aluRegReg .add true 0 8⟩, ⟨54, 3, .movRegReg true 8 0⟩,
  ⟨57, 3, .aluRegReg .add true 8 10⟩, ⟨60, 3, .aluRegReg .sbb true 1 1⟩,
  ⟨63, 3, .aluRegReg .andOp true 1 10⟩, ⟨66, 3, .aluRegReg .add true 0 1⟩,
  ⟨69, 3, .movRegReg true 2 0⟩, ⟨72, 5, .mulx 1 0 11⟩, ⟨77, 3, .movRegReg true 2 1⟩,
  ⟨80, 4, .shiftImm .shr true 1 32⟩, ⟨84, 2, .movRegReg false 2 2⟩,
  ⟨86, 3, .aluRegReg .sub true 0 1⟩, ⟨89, 3, .aluRegReg .sbb false 8 8⟩,
  ⟨92, 3, .aluRegReg .sub true 0 8⟩, ⟨95, 3, .movRegReg true 9 2⟩,
  ⟨98, 4, .shiftImm .shl true 9 32⟩, ⟨102, 3, .aluRegReg .sub true 9 2⟩,
  ⟨105, 3, .aluRegReg .add true 0 9⟩, ⟨108, 3, .aluRegReg .sbb false 8 8⟩,
  ⟨111, 3, .aluRegReg .add true 0 8⟩, ⟨114, 3, .movRegReg true 8 0⟩,
  ⟨117, 3, .aluRegReg .add true 8 10⟩, ⟨120, 3, .aluRegReg .sbb true 1 1⟩,
  ⟨123, 3, .aluRegReg .andOp true 1 10⟩, ⟨126, 3, .aluRegReg .add true 0 1⟩,
  ⟨129, 3, .movRegReg true 2 0⟩, ⟨132, 5, .mulx 1 0 0⟩, ⟨137, 3, .movRegReg true 2 1⟩,
  ⟨140, 4, .shiftImm .shr true 1 32⟩, ⟨144, 2, .movRegReg false 2 2⟩,
  ⟨146, 3, .aluRegReg .sub true 0 1⟩, ⟨149, 3, .aluRegReg .sbb false 8 8⟩,
  ⟨152, 3, .aluRegReg .sub true 0 8⟩, ⟨155, 3, .movRegReg true 9 2⟩,
  ⟨158, 4, .shiftImm .shl true 9 32⟩, ⟨162, 3, .aluRegReg .sub true 9 2⟩,
  ⟨165, 3, .aluRegReg .add true 0 9⟩, ⟨168, 3, .aluRegReg .sbb false 8 8⟩,
  ⟨171, 3, .aluRegReg .add true 0 8⟩, ⟨174, 3, .movRegReg true 8 0⟩,
  ⟨177, 3, .aluRegReg .add true 8 10⟩, ⟨180, 3, .aluRegReg .sbb true 1 1⟩,
  ⟨183, 3, .aluRegReg .andOp true 1 10⟩, ⟨186, 3, .aluRegReg .add true 0 1⟩,
  ⟨189, 3, .movRegReg true 2 0⟩, ⟨192, 5, .mulx 1 0 11⟩, ⟨197, 3, .movRegReg true 2 1⟩,
  ⟨200, 4, .shiftImm .shr true 1 32⟩, ⟨204, 2, .movRegReg false 2 2⟩,
  ⟨206, 3, .aluRegReg .sub true 0 1⟩, ⟨209, 3, .aluRegReg .sbb false 8 8⟩,
  ⟨212, 3, .aluRegReg .sub true 0 8⟩, ⟨215, 3, .movRegReg true 9 2⟩,
  ⟨218, 4, .shiftImm .shl true 9 32⟩, ⟨222, 3, .aluRegReg .sub true 9 2⟩,
  ⟨225, 3, .aluRegReg .add true 0 9⟩, ⟨228, 3, .aluRegReg .sbb false 8 8⟩,
  ⟨231, 3, .aluRegReg .add true 0 8⟩, ⟨234, 3, .movRegReg true 8 0⟩,
  ⟨237, 3, .aluRegReg .add true 8 10⟩, ⟨240, 3, .aluRegReg .sbb true 1 1⟩,
  ⟨243, 3, .aluRegReg .andOp true 1 10⟩, ⟨246, 3, .aluRegReg .add true 0 1⟩,
  ⟨249, 2, .aluRegReg .xorOp false 1 1⟩, ⟨251, 2, .aluRegReg .xorOp false 2 2⟩,
  ⟨253, 3, .aluRegReg .xorOp false 8 8⟩, ⟨256, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨259, 3, .aluRegReg .xorOp false 10 10⟩, ⟨262, 3, .aluRegReg .xorOp false 11 11⟩,
  ⟨265, 1, .ret⟩]

private theorem pow7_setup_and_b1 (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    ∃ s2, ExecReachesX86 goldPow7X86Prog 21
        ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
          y, cf, o, zf, dy, false, m⟩ s2 ∧
      ∃ r1' r2' r8' r9' cf' o' zf',
        s2 = ⟨69, ⟨goldMulMc r7 r7, r1', r2', r3, r4, r5, r6, r7, r8', r9',
          maskGprWidth false 4294967295, r7, r12, r13, r14, r15⟩,
          y, cf', o', zf', dy, false, m⟩ := by
  suffices hS : ∃ s2, StepsX86 goldPow7X86Prog 21
        ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
          y, cf, o, zf, dy, false, m⟩ s2 ∧
      ∃ r1' r2' r8' r9' cf' o' zf',
        s2 = ⟨69, ⟨goldMulMc r7 r7, r1', r2', r3, r4, r5, r6, r7, r8', r9',
          maskGprWidth false 4294967295, r7, r12, r13, r14, r15⟩,
          y, cf', o', zf', dy, false, m⟩ by
    rcases hS with ⟨s2, hs, hp⟩
    exact ⟨s2, hs.toExecReaches, hp⟩
  iterate 21
    apply StepsX86_step_ex rfl rfl
    · simp only [stepX86_movRR, stepX86_mulx, stepX86_shr64, stepX86_shl64, stepX86_addRR64,
        stepX86_subRR64, stepX86_sbbRR, stepX86_andRR, stepX86_movImm,
        maskGprWidth_true, sbb32_self, sbb64_self, uint64_evalAdd_eq, uint64_evalSub_eq,
        b16get_0, b16get_1, b16get_2, b16get_7, b16get_8, b16get_9, b16get_10, b16get_11,
        b16set_0, b16set_1, b16set_2, b16set_8, b16set_9, b16set_10, b16set_11]
      rfl
  exact ⟨_, StepsX86.zero _, _, _, _, _, _, _, _, rfl⟩

private theorem pow7_b2 (acc r1 r2 r3 r4 r5 r6 r7 r8 r9 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    ∃ s2, ExecReachesX86 goldPow7X86Prog 19
        ⟨69, ⟨acc, r1, r2, r3, r4, r5, r6, r7, r8, r9,
          maskGprWidth false 4294967295, r7, r12, r13, r14, r15⟩,
          y, cf, o, zf, dy, false, m⟩ s2 ∧
      ∃ r1' r2' r8' r9' cf' o' zf',
        s2 = ⟨129, ⟨goldMulMc acc r7, r1', r2', r3, r4, r5, r6, r7, r8', r9',
          maskGprWidth false 4294967295, r7, r12, r13, r14, r15⟩,
          y, cf', o', zf', dy, false, m⟩ := by
  suffices hS : ∃ s2, StepsX86 goldPow7X86Prog 19
        ⟨69, ⟨acc, r1, r2, r3, r4, r5, r6, r7, r8, r9,
          maskGprWidth false 4294967295, r7, r12, r13, r14, r15⟩,
          y, cf, o, zf, dy, false, m⟩ s2 ∧
      ∃ r1' r2' r8' r9' cf' o' zf',
        s2 = ⟨129, ⟨goldMulMc acc r7, r1', r2', r3, r4, r5, r6, r7, r8', r9',
          maskGprWidth false 4294967295, r7, r12, r13, r14, r15⟩,
          y, cf', o', zf', dy, false, m⟩ by
    rcases hS with ⟨s2, hs, hp⟩
    exact ⟨s2, hs.toExecReaches, hp⟩
  iterate 19
    apply StepsX86_step_ex rfl rfl
    · simp only [stepX86_movRR, stepX86_mulx, stepX86_shr64, stepX86_shl64, stepX86_addRR64,
        stepX86_subRR64, stepX86_sbbRR, stepX86_andRR,
        maskGprWidth_true, sbb32_self, sbb64_self, uint64_evalAdd_eq, uint64_evalSub_eq,
        b16get_0, b16get_1, b16get_2, b16get_8, b16get_9, b16get_10, b16get_11,
        b16set_0, b16set_1, b16set_2, b16set_8, b16set_9]
      rfl
  exact ⟨_, StepsX86.zero _, _, _, _, _, _, _, _, rfl⟩

private theorem pow7_b3 (acc r1 r2 r3 r4 r5 r6 r7 r8 r9 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    ∃ s2, ExecReachesX86 goldPow7X86Prog 19
        ⟨129, ⟨acc, r1, r2, r3, r4, r5, r6, r7, r8, r9,
          maskGprWidth false 4294967295, r7, r12, r13, r14, r15⟩,
          y, cf, o, zf, dy, false, m⟩ s2 ∧
      ∃ r1' r2' r8' r9' cf' o' zf',
        s2 = ⟨189, ⟨goldMulMc acc acc, r1', r2', r3, r4, r5, r6, r7, r8', r9',
          maskGprWidth false 4294967295, r7, r12, r13, r14, r15⟩,
          y, cf', o', zf', dy, false, m⟩ := by
  suffices hS : ∃ s2, StepsX86 goldPow7X86Prog 19
        ⟨129, ⟨acc, r1, r2, r3, r4, r5, r6, r7, r8, r9,
          maskGprWidth false 4294967295, r7, r12, r13, r14, r15⟩,
          y, cf, o, zf, dy, false, m⟩ s2 ∧
      ∃ r1' r2' r8' r9' cf' o' zf',
        s2 = ⟨189, ⟨goldMulMc acc acc, r1', r2', r3, r4, r5, r6, r7, r8', r9',
          maskGprWidth false 4294967295, r7, r12, r13, r14, r15⟩,
          y, cf', o', zf', dy, false, m⟩ by
    rcases hS with ⟨s2, hs, hp⟩
    exact ⟨s2, hs.toExecReaches, hp⟩
  iterate 19
    apply StepsX86_step_ex rfl rfl
    · simp only [stepX86_movRR, stepX86_mulx, stepX86_shr64, stepX86_shl64, stepX86_addRR64,
        stepX86_subRR64, stepX86_sbbRR, stepX86_andRR,
        maskGprWidth_true, sbb32_self, sbb64_self, uint64_evalAdd_eq, uint64_evalSub_eq,
        b16get_0, b16get_1, b16get_2, b16get_8, b16get_9, b16get_10,
        b16set_0, b16set_1, b16set_2, b16set_8, b16set_9]
      rfl
  exact ⟨_, StepsX86.zero _, _, _, _, _, _, _, _, rfl⟩

private theorem pow7_b4_and_wipe (acc r1 r2 r3 r4 r5 r6 r7 r8 r9 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    ExecReachesX86 goldPow7X86Prog 25
      ⟨189, ⟨acc, r1, r2, r3, r4, r5, r6, r7, r8, r9,
        maskGprWidth false 4294967295, r7, r12, r13, r14, r15⟩,
        y, cf, o, zf, dy, false, m⟩
      ⟨265, ⟨goldMulMc acc r7, 0, 0, r3, r4, r5, r6, r7, 0, 0, 0, 0, r12, r13, r14, r15⟩,
        y, false, false, true, dy, false, m⟩ := by
  apply StepsX86.toExecReaches
  iterate 25
    apply StepsX86.cons rfl rfl
    · simp only [stepX86_movRR, stepX86_mulx, stepX86_shr64, stepX86_shl64, stepX86_addRR64,
        stepX86_subRR64, stepX86_sbbRR, stepX86_andRR, stepX86_xorRR,
        maskGprWidth_true, mask32_xor_self, u64_zero_beq_zero, sbb32_self, sbb64_self,
        uint64_evalAdd_eq, uint64_evalSub_eq,
        b16get_0, b16get_1, b16get_2, b16get_8, b16get_9, b16get_10, b16get_11,
        b16set_0, b16set_1, b16set_2, b16set_8, b16set_9, b16set_10, b16set_11]
      rfl
  exact StepsX86.zero _

private theorem goldPow7Mc_toNat (x : UInt64) :
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

theorem rlib_goldilocks_pow7_ct_x86_64_functional_and_ct :
    ∃ slice m,
      extractRlibFuncBytes x86RlibArchiveBytes "qsag_asm_goldilocks_pow7_ct_x86_64" = some slice ∧
      m ∈ parseArArchive x86RlibArchiveBytes ∧
      ArPayloadOk x86RlibArchiveBytes m ∧
      checkElfFuncThreeWayNI m.payload "qsag_asm_goldilocks_pow7_ct_x86_64"
        (mkContract "qsag_asm_goldilocks_pow7_ct_x86_64" [4] [] [11]) = true ∧
      ElfSliceThreeWayNISafe slice
        (mkContract "qsag_asm_goldilocks_pow7_ct_x86_64" [4] [] [11]) ∧
      decodeX86Slice slice.code = some goldPow7X86Prog ∧
      ∀ (st : X86BvState), st.pc = 0 → st.halted = false →
        (∃ st84 tr84, execDecodedX86 slice.code 84 st = some (st84, tr84) ∧ st84.halted = false) ∧
        ∀ extra : Nat, ∃ st' trace,
          execDecodedX86 slice.code (85 + extra) st = some (st', trace) ∧
          st'.halted = true ∧ st'.pc = 265 ∧ trace.length = 85 ∧
          st'.gpr.get 0 = BitVec.ofNat 64 (((st.gpr.get 7).toNat ^ 7) % GOLDILOCKS_P) ∧
          X86CalleeSavedPreserved st st' ∧
          st'.mem = st.mem ∧
          st'.gpr.get 1 = 0#64 ∧ st'.gpr.get 2 = 0#64 ∧ st'.gpr.get 8 = 0#64 ∧
          st'.gpr.get 9 = 0#64 ∧ st'.gpr.get 10 = 0#64 ∧ st'.gpr.get 11 = 0#64 := by
  cases hFind : x86ExtractedSlices.find? (fun s => s.name == "qsag_asm_goldilocks_pow7_ct_x86_64") with
  | none => exfalso; revert hFind; decide +kernel
  | some slice =>
    have hExt : extractRlibFuncBytes x86RlibArchiveBytes "qsag_asm_goldilocks_pow7_ct_x86_64" = some slice := by
      rw [extractRlibFuncBytes_x86_eq, hFind]
    have hNI : checkElfSliceThreeWayNI slice
        (mkContract "qsag_asm_goldilocks_pow7_ct_x86_64" [4] [] [11]) = true := by
      have hCheck : ((x86ExtractedSlices.find? (fun s => s.name == "qsag_asm_goldilocks_pow7_ct_x86_64")).map
          (fun sl => checkElfSliceThreeWayNI sl
            (mkContract "qsag_asm_goldilocks_pow7_ct_x86_64" [4] [] [11]))) =
          some true := by decide +kernel
      rw [hFind] at hCheck
      exact Option.some.inj hCheck
    have hDec : decodeX86Slice slice.code = some goldPow7X86Prog := by
      have hD : (x86ExtractedSlices.find? (fun s => s.name == "qsag_asm_goldilocks_pow7_ct_x86_64")).bind
          (fun sl => decodeX86Slice sl.code) = some goldPow7X86Prog := by decide +kernel
      rw [hFind] at hD
      exact hD
    obtain ⟨m, hm, hPay, _, hMemNI, _, hSafe⟩ :=
      extractRlibFuncBytes_member_ni_sound x86_rlib_distinct_names hExt hNI
    refine ⟨slice, m, hExt, hm, hPay, hMemNI, hSafe, hDec, ?_⟩
    intro st hpc hh
    rcases st with ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
      y, cf, o, zf, dy, hlt, mem⟩
    dsimp only at hpc hh; subst hpc hh
    let st0 : X86BvState := ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, mem⟩
    obtain ⟨_, hb1, r1a, r2a, r8a, r9a, cfa, ofa, zfa, rfl⟩ :=
      pow7_setup_and_b1 (UInt64.ofBitVec r0) (UInt64.ofBitVec r1) (UInt64.ofBitVec r2)
        (UInt64.ofBitVec r3) (UInt64.ofBitVec r4) (UInt64.ofBitVec r5) (UInt64.ofBitVec r6)
        (UInt64.ofBitVec r7) (UInt64.ofBitVec r8) (UInt64.ofBitVec r9) (UInt64.ofBitVec r10)
        (UInt64.ofBitVec r11) (UInt64.ofBitVec r12) (UInt64.ofBitVec r13) (UInt64.ofBitVec r14)
        (UInt64.ofBitVec r15) y cf o zf dy (fun a => mem a.toBitVec)
    let u3 := UInt64.ofBitVec r3; let u4 := UInt64.ofBitVec r4
    let u5 := UInt64.ofBitVec r5; let u6 := UInt64.ofBitVec r6
    let u7 := UInt64.ofBitVec r7; let u12 := UInt64.ofBitVec r12
    let u13 := UInt64.ofBitVec r13; let u14 := UInt64.ofBitVec r14
    let u15 := UInt64.ofBitVec r15
    obtain ⟨_, hb2, r1b, r2b, r8b, r9b, cfb, ofb, zfb, rfl⟩ :=
      pow7_b2 (goldMulMc u7 u7) r1a r2a u3 u4 u5 u6 u7 r8a r9a u12 u13 u14 u15
        y cfa ofa zfa dy (fun a => mem a.toBitVec)
    obtain ⟨_, hb3, r1c, r2c, r8c, r9c, cfc, ofc, zfc, rfl⟩ :=
      pow7_b3 (goldMulMc (goldMulMc u7 u7) u7) r1b r2b u3 u4 u5 u6 u7 r8b r9b u12 u13 u14 u15
        y cfb ofb zfb dy (fun a => mem a.toBitVec)
    have hb4 :=
      pow7_b4_and_wipe (goldMulMc (goldMulMc (goldMulMc u7 u7) u7) (goldMulMc (goldMulMc u7 u7) u7))
        r1c r2c u3 u4 u5 u6 u7 r8c r9c u12 u13 u14 u15 y cfc ofc zfc dy (fun a => mem a.toBitVec)
    have h84 : ExecReachesX86 goldPow7X86Prog 84 _ _ :=
      ExecReachesX86_trans (ExecReachesX86_trans (ExecReachesX86_trans hb1 hb2) hb3) hb4
    obtain ⟨hPre, hPost⟩ := execDecodedX86_ret_of_reaches st0 hDec rfl h84 rfl rfl
    refine ⟨hPre, fun extra => ?_⟩
    obtain ⟨tr, hExec, hL⟩ := hPost extra
    refine ⟨_, tr, hExec, rfl, rfl, hL, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · change (goldMulMc (goldMulMc (goldMulMc (goldMulMc u7 u7) u7) (goldMulMc (goldMulMc u7 u7) u7)) u7).toBitVec =
        BitVec.ofNat 64 ((r7.toNat ^ 7) % GOLDILOCKS_P)
      apply bv_ofU64_eq_ofNat _ (mod_goldilocks_lt_u64 _)
      rw [goldPow7Mc_toNat, UInt64.toNat_ofBitVec]
    · exact x86_callee_saved_of_roundtrip
    · exact mem_roundtrip mem

/-! ### §3.5 `qsag_asm_goldilocks_dot2_adx_x86_64` (`N = 44`, `retPc = 153`) -/

def goldDot2X86Prog : List (DecodedInstr X86Instr) := [
  ⟨0, 3, .movRegReg true 10 2⟩,
  ⟨3, 2, .aluRegReg .xorOp false 0 0⟩,
  ⟨5, 3, .movRegReg true 2 7⟩,
  ⟨8, 5, .mulx 9 8 6⟩,
  ⟨13, 3, .movRegReg true 2 10⟩,
  ⟨16, 5, .mulx 11 10 1⟩,
  ⟨21, 6, .adcx 8 10⟩,
  ⟨27, 6, .adcx 9 11⟩,
  ⟨33, 6, .adox 0 0⟩,
  ⟨39, 6, .adcx 0 0⟩,
  ⟨45, 3, .negReg true 0⟩,
  ⟨48, 10, .movImm true 11 18446744065119617025⟩,
  ⟨58, 3, .aluRegReg .andOp true 11 0⟩,
  ⟨61, 3, .movRegReg true 0 8⟩,
  ⟨64, 3, .movRegReg true 2 9⟩,
  ⟨67, 4, .shiftImm .shr true 9 32⟩,
  ⟨71, 2, .movRegReg false 2 2⟩,
  ⟨73, 3, .aluRegReg .sub true 0 9⟩,
  ⟨76, 3, .aluRegReg .sbb false 8 8⟩,
  ⟨79, 3, .aluRegReg .sub true 0 8⟩,
  ⟨82, 3, .movRegReg true 9 2⟩,
  ⟨85, 4, .shiftImm .shl true 9 32⟩,
  ⟨89, 3, .aluRegReg .sub true 9 2⟩,
  ⟨92, 3, .aluRegReg .add true 0 9⟩,
  ⟨95, 3, .aluRegReg .sbb false 8 8⟩,
  ⟨98, 3, .aluRegReg .add true 0 8⟩,
  ⟨101, 3, .aluRegReg .add true 0 11⟩,
  ⟨104, 3, .aluRegReg .sbb false 8 8⟩,
  ⟨107, 3, .aluRegReg .add true 0 8⟩,
  ⟨110, 3, .aluRegReg .sbb false 10 10⟩,
  ⟨113, 3, .aluRegReg .add true 0 10⟩,
  ⟨116, 6, .movImm false 9 4294967295⟩,
  ⟨122, 3, .movRegReg true 8 0⟩,
  ⟨125, 3, .aluRegReg .add true 8 9⟩,
  ⟨128, 3, .aluRegReg .sbb true 1 1⟩,
  ⟨131, 3, .aluRegReg .andOp true 1 9⟩,
  ⟨134, 3, .aluRegReg .add true 0 1⟩,
  ⟨137, 2, .aluRegReg .xorOp false 1 1⟩,
  ⟨139, 2, .aluRegReg .xorOp false 2 2⟩,
  ⟨141, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨144, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨147, 3, .aluRegReg .xorOp false 10 10⟩,
  ⟨150, 3, .aluRegReg .xorOp false 11 11⟩,
  ⟨153, 1, .ret⟩]

private def goldDot2Mc (a0 b0 a1 b1 : UInt64) : UInt64 :=
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

private theorem u64_toNat_zero : (0 : UInt64).toNat = 0 := rfl

private theorem u64_ofNat_zero_mod : UInt64.ofNat (0 % 0x10000000000000000) = 0 := rfl

private theorem u64_zero_lt_264 : decide (0 ≥ 0x10000000000000000) = false := rfl

private theorem u64_ofNat_b_mod (c : Bool) :
    UInt64.ofNat ((if c then 1 else 0) % 0x10000000000000000) = if c then 1 else 0 := by
  cases c <;> decide

private theorem u64_b_lt_264 (c : Bool) :
    decide ((if c then 1 else 0) ≥ 0x10000000000000000) = false := by
  cases c <;> decide

private theorem u64_eps2_and_mask (c : Bool) :
    (18446744065119617025 : UInt64) &&& ((0 : UInt64) - (if c then 1 else 0)) =
      if c then 18446744065119617025 else 0 := by
  cases c <;> decide

private theorem goldDot2_part1 (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    let p0 := r7.toNat * r6.toNat
    let p1 := r2.toNat * r1.toNat
    let lo0 := UInt64.ofNat (p0 % 0x10000000000000000)
    let hi0 := UInt64.ofNat (p0 / 0x10000000000000000)
    let lo1 := UInt64.ofNat (p1 % 0x10000000000000000)
    let hi1 := UInt64.ofNat (p1 / 0x10000000000000000)
    let sumLo := lo0.toNat + lo1.toNat
    let r8' := UInt64.ofNat (sumLo % 0x10000000000000000)
    let cf0 := decide (sumLo ≥ 0x10000000000000000)
    let sumHi := hi0.toNat + hi1.toNat + (if cf0 then 1 else 0)
    let r9' := UInt64.ofNat (sumHi % 0x10000000000000000)
    let cf1 := decide (sumHi ≥ 0x10000000000000000)
    let r11' : UInt64 := if cf1 then 18446744065119617025 else 0
    ∃ s2, StepsX86 goldDot2X86Prog 13
        ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
          y, cf, o, zf, dy, false, m⟩ s2 ∧
      ∃ r0' zf',
        s2 = ⟨61, ⟨r0', r1, r2, r3, r4, r5, r6, r7, r8', r9', lo1, r11', r12, r13, r14, r15⟩,
          y, false, false, zf', dy, false, m⟩ := by
  dsimp only
  iterate 13
    apply StepsX86_step_ex rfl rfl
    · simp only [stepX86_movRR, stepX86_xorRR, stepX86_mulx, stepX86_adcx, stepX86_adox,
        stepX86_neg, stepX86_movImm, stepX86_andRR64,
        maskGprWidth_true, mask32_xor_self, u64_zero_beq_zero,
        u64_toNat_zero, Nat.zero_add, Nat.add_zero,
        u64_ofNat_zero_mod, u64_zero_lt_264, u64_ofNat_b_mod, u64_b_lt_264,
        u64_eps2_and_mask, Bool.false_eq_true, ite_false,
        b16get_0, b16get_1, b16get_2, b16get_6, b16get_7, b16get_8, b16get_9, b16get_10, b16get_11,
        b16set_0, b16set_2, b16set_8, b16set_9, b16set_10, b16set_11]
      rfl
  exact ⟨_, StepsX86.zero _, _, _, rfl⟩

private theorem goldDot2_part2 (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (zf dy : Bool) (m : UInt64 → UInt8) :
    ExecReachesX86 goldDot2X86Prog 30
      ⟨61, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        y, false, false, zf, dy, false, m⟩
      ⟨153, ⟨goldAddMc (mulRed r8 r9) r11, 0, 0, r3, r4, r5, r6, r7, 0, 0, 0, 0,
        r12, r13, r14, r15⟩,
        y, false, false, true, dy, false, m⟩ := by
  apply StepsX86.toExecReaches
  iterate 30
    apply StepsX86.cons rfl rfl
    · simp only [stepX86_movRR, stepX86_shr64, stepX86_shl64, stepX86_addRR64, stepX86_subRR64,
        stepX86_sbbRR, stepX86_andRR, stepX86_movImm, stepX86_xorRR,
        maskGprWidth_true, mask32_xor_self, u64_zero_beq_zero, sbb32_self, sbb64_self,
        uint64_evalAdd_eq, uint64_evalSub_eq,
        b16get_0, b16get_1, b16get_2, b16get_8, b16get_9, b16get_10, b16get_11,
        b16set_0, b16set_1, b16set_2, b16set_8, b16set_9, b16set_10, b16set_11]
      rfl
  exact StepsX86.zero _

private theorem goldDot2Mc_toNat (a0 b0 a1 b1 : UInt64) :
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

theorem rlib_goldilocks_dot2_adx_x86_64_functional_and_ct :
    ∃ slice m,
      extractRlibFuncBytes x86RlibArchiveBytes "qsag_asm_goldilocks_dot2_adx_x86_64" = some slice ∧
      m ∈ parseArArchive x86RlibArchiveBytes ∧
      ArPayloadOk x86RlibArchiveBytes m ∧
      checkElfFuncThreeWayNI m.payload "qsag_asm_goldilocks_dot2_adx_x86_64"
        (mkContract "qsag_asm_goldilocks_dot2_adx_x86_64" [4]) = true ∧
      ElfSliceThreeWayNISafe slice (mkContract "qsag_asm_goldilocks_dot2_adx_x86_64" [4]) ∧
      decodeX86Slice slice.code = some goldDot2X86Prog ∧
      ∀ (st : X86BvState), st.pc = 0 → st.halted = false →
        (∃ st43 tr43, execDecodedX86 slice.code 43 st = some (st43, tr43) ∧ st43.halted = false) ∧
        ∀ extra : Nat, ∃ st' trace,
          execDecodedX86 slice.code (44 + extra) st = some (st', trace) ∧
          st'.halted = true ∧ st'.pc = 153 ∧ trace.length = 44 ∧
          st'.gpr.get 0 = BitVec.ofNat 64
            (((st.gpr.get 7).toNat * (st.gpr.get 6).toNat +
              (st.gpr.get 2).toNat * (st.gpr.get 1).toNat) % GOLDILOCKS_P) ∧
          X86CalleeSavedPreserved st st' ∧
          st'.mem = st.mem ∧
          st'.gpr.get 1 = 0#64 ∧ st'.gpr.get 2 = 0#64 ∧ st'.gpr.get 8 = 0#64 ∧
          st'.gpr.get 9 = 0#64 ∧ st'.gpr.get 10 = 0#64 ∧ st'.gpr.get 11 = 0#64 := by
  cases hFind : x86ExtractedSlices.find? (fun s => s.name == "qsag_asm_goldilocks_dot2_adx_x86_64") with
  | none => exfalso; revert hFind; decide +kernel
  | some slice =>
    have hExt : extractRlibFuncBytes x86RlibArchiveBytes "qsag_asm_goldilocks_dot2_adx_x86_64" = some slice := by
      rw [extractRlibFuncBytes_x86_eq, hFind]
    have hNI : checkElfSliceThreeWayNI slice (mkContract "qsag_asm_goldilocks_dot2_adx_x86_64" [4]) = true := by
      have hCheck : ((x86ExtractedSlices.find? (fun s => s.name == "qsag_asm_goldilocks_dot2_adx_x86_64")).map
          (fun sl => checkElfSliceThreeWayNI sl (mkContract "qsag_asm_goldilocks_dot2_adx_x86_64" [4]))) =
          some true := by decide +kernel
      rw [hFind] at hCheck
      exact Option.some.inj hCheck
    have hDec : decodeX86Slice slice.code = some goldDot2X86Prog := by
      have hD : (x86ExtractedSlices.find? (fun s => s.name == "qsag_asm_goldilocks_dot2_adx_x86_64")).bind
          (fun sl => decodeX86Slice sl.code) = some goldDot2X86Prog := by decide +kernel
      rw [hFind] at hD
      exact hD
    obtain ⟨m, hm, hPay, _, hMemNI, _, hSafe⟩ :=
      extractRlibFuncBytes_member_ni_sound x86_rlib_distinct_names hExt hNI
    refine ⟨slice, m, hExt, hm, hPay, hMemNI, hSafe, hDec, ?_⟩
    intro st hpc hh
    rcases st with ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
      y, cf, o, zf, dy, hlt, mem⟩
    dsimp only at hpc hh; subst hpc hh
    let st0 : X86BvState := ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, mem⟩
    obtain ⟨_, hp1, r0a, zfa, rfl⟩ :=
      goldDot2_part1 (UInt64.ofBitVec r0) (UInt64.ofBitVec r1) (UInt64.ofBitVec r2)
        (UInt64.ofBitVec r3) (UInt64.ofBitVec r4) (UInt64.ofBitVec r5) (UInt64.ofBitVec r6)
        (UInt64.ofBitVec r7) (UInt64.ofBitVec r8) (UInt64.ofBitVec r9) (UInt64.ofBitVec r10)
        (UInt64.ofBitVec r11) (UInt64.ofBitVec r12) (UInt64.ofBitVec r13) (UInt64.ofBitVec r14)
        (UInt64.ofBitVec r15) y cf o zf dy (fun a => mem a.toBitVec)
    have h43 := ExecReachesX86_trans hp1.toExecReaches (goldDot2_part2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ y zfa dy (fun a => mem a.toBitVec))
    obtain ⟨hPre, hPost⟩ := execDecodedX86_ret_of_reaches st0 hDec rfl h43 rfl rfl
    refine ⟨hPre, fun extra => ?_⟩
    obtain ⟨tr, hExec, hL⟩ := hPost extra
    refine ⟨_, tr, hExec, rfl, rfl, hL, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · change (goldDot2Mc (UInt64.ofBitVec r7) (UInt64.ofBitVec r6)
          (UInt64.ofBitVec r2) (UInt64.ofBitVec r1)).toBitVec =
        BitVec.ofNat 64 ((r7.toNat * r6.toNat + r2.toNat * r1.toNat) % GOLDILOCKS_P)
      apply bv_ofU64_eq_ofNat _ (mod_goldilocks_lt_u64 _)
      rw [goldDot2Mc_toNat, UInt64.toNat_ofBitVec, UInt64.toNat_ofBitVec,
        UInt64.toNat_ofBitVec, UInt64.toNat_ofBitVec]
    · exact x86_callee_saved_of_roundtrip
    · exact mem_roundtrip mem

/-! ### §3.6 `qsag_asm_ct_eq_32_x86_64` (`N = 20`) & `qsag_asm_ct_eq_32_aarch64` (`N = 22`) -/

private theorem ctEq32X86_reaches (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    ExecReachesX86 ctEq32X86Prog 19
      ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        y, cf, o, zf, dy, false, m⟩
      ⟨62, ⟨maskGprWidth false (((ctEq32WordX86 m r7 r6 ||| (0 - ctEq32WordX86 m r7 r6)) >>>
              UInt64.ofNat 63) ^^^ 1),
          0, 0, r3, r4, r5, r6, r7, 0, r9, r10, r11, r12, r13, r14, r15⟩,
        y, false, false, true, dy, false, m⟩ := by
  apply StepsX86.toExecReaches
  iterate 19
    apply StepsX86.cons rfl rfl
    · simp only [stepX86_load64, stepX86_xorLoad64, stepX86_orRR, stepX86_movRR, stepX86_neg,
        stepX86_shr64, stepX86_xorImm, stepX86_xorRR, maskGprWidth_true, mask32_xor_self,
        u64_zero_beq_zero, b16get_0, b16get_1, b16get_2, b16get_6, b16get_7, b16get_8,
        b16set_0, b16set_1, b16set_2, b16set_8]
      rfl
  exact StepsX86.zero _

theorem rlib_ct_eq_32_x86_64_functional_and_ct :
    ∃ slice m,
      extractRlibFuncBytes x86RlibArchiveBytes "qsag_asm_ct_eq_32_x86_64" = some slice ∧
      m ∈ parseArArchive x86RlibArchiveBytes ∧
      ArPayloadOk x86RlibArchiveBytes m ∧
      checkElfFuncThreeWayNI m.payload "qsag_asm_ct_eq_32_x86_64"
        (mkContract "qsag_asm_ct_eq_32_x86_64" [4, 7, 6] [] [1, 2, 8]) = true ∧
      ElfSliceThreeWayNISafe slice
        (mkContract "qsag_asm_ct_eq_32_x86_64" [4, 7, 6] [] [1, 2, 8]) ∧
      decodeX86Slice slice.code = some ctEq32X86Prog ∧
      ∀ (st : X86BvState), st.pc = 0 → st.halted = false →
        (∃ st19 tr19, execDecodedX86 slice.code 19 st = some (st19, tr19) ∧ st19.halted = false) ∧
        ∀ extra : Nat, ∃ st' trace,
          execDecodedX86 slice.code (20 + extra) st = some (st', trace) ∧
          st'.halted = true ∧ st'.pc = 62 ∧ trace.length = 20 ∧
          st'.gpr.get 0 =
            (if ∀ i : Nat, i < 32 →
                st.mem (st.gpr.get 7 + BitVec.ofNat 64 i) =
                  st.mem (st.gpr.get 6 + BitVec.ofNat 64 i)
              then 1#64 else 0#64) ∧
          X86CalleeSavedPreserved st st' ∧
          st'.mem = st.mem ∧
          st'.gpr.get 1 = 0#64 ∧ st'.gpr.get 2 = 0#64 ∧ st'.gpr.get 8 = 0#64 := by
  cases hFind : x86ExtractedSlices.find? (fun s => s.name == "qsag_asm_ct_eq_32_x86_64") with
  | none => exfalso; revert hFind; decide +kernel
  | some slice =>
    have hExt : extractRlibFuncBytes x86RlibArchiveBytes "qsag_asm_ct_eq_32_x86_64" = some slice := by
      rw [extractRlibFuncBytes_x86_eq, hFind]
    have hNI : checkElfSliceThreeWayNI slice
        (mkContract "qsag_asm_ct_eq_32_x86_64" [4, 7, 6] [] [1, 2, 8]) = true := by
      have hCheck : ((x86ExtractedSlices.find? (fun s => s.name == "qsag_asm_ct_eq_32_x86_64")).map
          (fun sl => checkElfSliceThreeWayNI sl
            (mkContract "qsag_asm_ct_eq_32_x86_64" [4, 7, 6] [] [1, 2, 8]))) =
          some true := by decide +kernel
      rw [hFind] at hCheck
      exact Option.some.inj hCheck
    have hDec : decodeX86Slice slice.code = some ctEq32X86Prog := by
      have hD : (x86ExtractedSlices.find? (fun s => s.name == "qsag_asm_ct_eq_32_x86_64")).bind
          (fun sl => decodeX86Slice sl.code) = some ctEq32X86Prog := by decide +kernel
      rw [hFind] at hD
      exact hD
    obtain ⟨m, hm, hPay, _, hMemNI, _, hSafe⟩ :=
      extractRlibFuncBytes_member_ni_sound x86_rlib_distinct_names hExt hNI
    refine ⟨slice, m, hExt, hm, hPay, hMemNI, hSafe, hDec, ?_⟩
    intro st hpc hh
    rcases st with ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
      y, cf, o, zf, dy, hlt, mem⟩
    dsimp only at hpc hh; subst hpc hh
    let st0 : X86BvState := ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, mem⟩
    let mU : UInt64 → UInt8 := fun a => mem a.toBitVec
    obtain ⟨hPre, hPost⟩ := execDecodedX86_ret_of_reaches st0 hDec rfl
      (ctEq32X86_reaches (UInt64.ofBitVec r0) (UInt64.ofBitVec r1) (UInt64.ofBitVec r2)
        (UInt64.ofBitVec r3) (UInt64.ofBitVec r4) (UInt64.ofBitVec r5) (UInt64.ofBitVec r6)
        (UInt64.ofBitVec r7) (UInt64.ofBitVec r8) (UInt64.ofBitVec r9) (UInt64.ofBitVec r10)
        (UInt64.ofBitVec r11) (UInt64.ofBitVec r12) (UInt64.ofBitVec r13) (UInt64.ofBitVec r14)
        (UInt64.ofBitVec r15) y cf o zf dy mU)
      rfl rfl
    refine ⟨hPre, fun extra => ?_⟩
    obtain ⟨tr, hExec, hL⟩ := hPost extra
    refine ⟨_, tr, hExec, rfl, rfl, hL, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · change (maskGprWidth false
          (((ctEq32WordX86 mU (UInt64.ofBitVec r7) (UInt64.ofBitVec r6) |||
              (0 - ctEq32WordX86 mU (UInt64.ofBitVec r7) (UInt64.ofBitVec r6))) >>>
              UInt64.ofNat 63) ^^^ 1)).toBitVec =
        (if ∀ i : Nat, i < 32 →
            mem (r7 + BitVec.ofNat 64 i) = mem (r6 + BitVec.ofNat 64 i)
          then 1#64 else 0#64)
      rw [zeroTest64_masked]
      have hiff0 : ctEq32WordX86 mU (UInt64.ofBitVec r7) (UInt64.ofBitVec r6) = 0 ↔
          ∀ i : Nat, i < 32 →
            mU (UInt64.ofBitVec r7 + UInt64.ofNat i) =
              mU (UInt64.ofBitVec r6 + UInt64.ofNat i) :=
        xorOr4_eq_zero_iff mU (UInt64.ofBitVec r7) (UInt64.ofBitVec r6) _ _ _ _ _ _ _ _
          rfl rfl rfl rfl rfl rfl rfl rfl
      have hAddrEq (base : BitVec 64) (i : Nat) :
          (UInt64.ofBitVec base + UInt64.ofNat i).toBitVec = base + BitVec.ofNat 64 i := by
        rfl
      have hiff : ctEq32WordX86 mU (UInt64.ofBitVec r7) (UInt64.ofBitVec r6) = 0 ↔
          ∀ i : Nat, i < 32 → mem (r7 + BitVec.ofNat 64 i) = mem (r6 + BitVec.ofNat 64 i) := by
        simpa only [mU, hAddrEq] using hiff0
      if hW : ctEq32WordX86 mU (UInt64.ofBitVec r7) (UInt64.ofBitVec r6) = 0 then
        rw [ite_eq_left hW, ite_eq_left (hiff.mp hW)]; rfl
      else
        rw [ite_eq_right hW, ite_eq_right (fun h => hW (hiff.mpr h))]; rfl
    · exact x86_callee_saved_of_roundtrip
    · exact mem_roundtrip mem


/-! ### §3.7 `qsag_asm_ct_eq_32_aarch64` (`N = 22`, `retPc = 84`) -/

private theorem ctEq32Arm_reaches (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
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
  exact StepsArm64.zero _

/-- End-to-end byte-decoded functional equivalence + 3-way CT-NI certificate for the real
    `rustc --release` `.rlib` `qsag_asm_ct_eq_32_aarch64` kernel (`N = 22` exact steps to `RET`
    at `pc = 84`). -/
theorem rlib_ct_eq_32_aarch64_functional_and_ct :
    ∃ slice m,
      extractRlibFuncBytes aarch64RlibArchiveBytes "qsag_asm_ct_eq_32_aarch64" = some slice ∧
      m ∈ parseArArchive aarch64RlibArchiveBytes ∧
      ArPayloadOk aarch64RlibArchiveBytes m ∧
      checkElfFuncThreeWayNI m.payload "qsag_asm_ct_eq_32_aarch64"
        (mkContract "qsag_asm_ct_eq_32_aarch64" [0, 1] [] [2, 3, 4, 5, 6, 7]) = true ∧
      ElfSliceThreeWayNISafe slice
        (mkContract "qsag_asm_ct_eq_32_aarch64" [0, 1] [] [2, 3, 4, 5, 6, 7]) ∧
      decodeArm64Slice slice.code = some ctEq32ArmProg ∧
      ∀ (st : Arm64BvState), st.pc = 0 → st.halted = false →
        (∃ st21 tr21, execDecodedArm64 slice.code 21 st = some (st21, tr21) ∧ st21.halted = false) ∧
        ∀ extra : Nat, ∃ st' trace,
          execDecodedArm64 slice.code (22 + extra) st = some (st', trace) ∧
          st'.halted = true ∧ st'.pc = 84 ∧ trace.length = 22 ∧
          st'.gpr.get 0 =
            (if ∀ i : Nat, i < 32 →
                st.mem (st.gpr.get 0 + BitVec.ofNat 64 i) =
                  st.mem (st.gpr.get 1 + BitVec.ofNat 64 i)
              then 1#64 else 0#64) ∧
          Arm64CalleeSavedPreserved st st' ∧
          st'.mem = st.mem ∧
          (∀ r : Nat, 2 ≤ r → r ≤ 7 → st'.gpr.get r = 0#64) := by
  cases hFind : aarch64ExtractedSlices.find? (fun s => s.name == "qsag_asm_ct_eq_32_aarch64") with
  | none => exfalso; revert hFind; decide +kernel
  | some slice =>
    have hExt : extractRlibFuncBytes aarch64RlibArchiveBytes "qsag_asm_ct_eq_32_aarch64" = some slice := by
      rw [extractRlibFuncBytes_aarch64_eq, hFind]
    have hNI : checkElfSliceThreeWayNI slice
        (mkContract "qsag_asm_ct_eq_32_aarch64" [0, 1] [] [2, 3, 4, 5, 6, 7]) = true := by
      have hCheck : ((aarch64ExtractedSlices.find? (fun s => s.name == "qsag_asm_ct_eq_32_aarch64")).map
          (fun sl => checkElfSliceThreeWayNI sl
            (mkContract "qsag_asm_ct_eq_32_aarch64" [0, 1] [] [2, 3, 4, 5, 6, 7]))) =
          some true := by decide +kernel
      rw [hFind] at hCheck
      exact Option.some.inj hCheck
    have hDec : decodeArm64Slice slice.code = some ctEq32ArmProg := by
      have hD : (aarch64ExtractedSlices.find? (fun s => s.name == "qsag_asm_ct_eq_32_aarch64")).bind
          (fun sl => decodeArm64Slice sl.code) = some ctEq32ArmProg := by decide +kernel
      rw [hFind] at hD
      exact hD
    obtain ⟨m, hm, hPay, _, hMemNI, _, hSafe⟩ :=
      extractRlibFuncBytes_member_ni_sound aarch64_rlib_distinct_names hExt hNI
    refine ⟨slice, m, hExt, hm, hPay, hMemNI, hSafe, hDec, ?_⟩
    intro st hpc hh
    rcases st with ⟨pc, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
      v, cf, zf, dit, hlt, mem⟩
    dsimp only at hpc hh; subst hpc hh
    let st0 : Arm64BvState := ⟨0, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩, v, cf, zf, dit, false, mem⟩
    let mU : UInt64 → UInt8 := fun a => mem a.toBitVec
    obtain ⟨hPre, hPost⟩ := execDecodedArm64_ret_of_reaches st0 hDec rfl
      (ctEq32Arm_reaches (UInt64.ofBitVec r0) (UInt64.ofBitVec r1) (UInt64.ofBitVec r2)
        (UInt64.ofBitVec r3) (UInt64.ofBitVec r4) (UInt64.ofBitVec r5) (UInt64.ofBitVec r6)
        (UInt64.ofBitVec r7) (UInt64.ofBitVec r8) (UInt64.ofBitVec r9) (UInt64.ofBitVec r10)
        (UInt64.ofBitVec r11) (UInt64.ofBitVec r12) (UInt64.ofBitVec r13) (UInt64.ofBitVec r14)
        (UInt64.ofBitVec r15) (bank16ToU64 hi) v cf zf dit mU)
      rfl rfl
    refine ⟨hPre, fun extra => ?_⟩
    obtain ⟨tr, hExec, hL⟩ := hPost extra
    refine ⟨_, tr, hExec, rfl, rfl, hL, ?_, arm64_callee_saved_of_hi_vec, mem_roundtrip mem, ?_⟩
    · change (((ctEq32WordArm mU (UInt64.ofBitVec r0) (UInt64.ofBitVec r1) |||
          (0 - ctEq32WordArm mU (UInt64.ofBitVec r0) (UInt64.ofBitVec r1))) >>>
          UInt64.ofNat 63) ^^^ 1).toBitVec =
        (if ∀ i : Nat, i < 32 →
            mem (r0 + BitVec.ofNat 64 i) = mem (r1 + BitVec.ofNat 64 i)
          then 1#64 else 0#64)
      rw [zeroTest64]
      have e8 : ∀ x : UInt64, x + 0 + 8 = x + UInt64.ofNat 8 := fun x => by rw [UInt64.add_zero]; rfl
      have e24 : ∀ x : UInt64, x + 16 + 8 = x + UInt64.ofNat 24 := fun x => by rw [UInt64.add_assoc]; rfl
      have hiff0 : ctEq32WordArm mU (UInt64.ofBitVec r0) (UInt64.ofBitVec r1) = 0 ↔
          ∀ i : Nat, i < 32 →
            mU (UInt64.ofBitVec r0 + UInt64.ofNat i) =
              mU (UInt64.ofBitVec r1 + UInt64.ofNat i) :=
        xorOr4_eq_zero_iff mU (UInt64.ofBitVec r0) (UInt64.ofBitVec r1) _ _ _ _ _ _ _ _
          rfl (e8 _) rfl (e24 _) rfl (e8 _) rfl (e24 _)
      have hAddrEq (base : BitVec 64) (i : Nat) :
          (UInt64.ofBitVec base + UInt64.ofNat i).toBitVec = base + BitVec.ofNat 64 i := rfl
      have hiff : ctEq32WordArm mU (UInt64.ofBitVec r0) (UInt64.ofBitVec r1) = 0 ↔
          ∀ i : Nat, i < 32 → mem (r0 + BitVec.ofNat 64 i) = mem (r1 + BitVec.ofNat 64 i) := by
        simpa only [mU, hAddrEq] using hiff0
      if hW : ctEq32WordArm mU (UInt64.ofBitVec r0) (UInt64.ofBitVec r1) = 0 then
        rw [ite_eq_left hW, ite_eq_left (hiff.mp hW)]; rfl
      else
        rw [ite_eq_right hW, ite_eq_right (fun h => hW (hiff.mpr h))]; rfl
    · intro r hr1 hr2
      match r, hr1, hr2 with
      | 2, _, _ => rfl | 3, _, _ => rfl | 4, _, _ => rfl
      | 5, _, _ => rfl | 6, _, _ => rfl | 7, _, _ => rfl
      | 0, h, _ => exact absurd h (by decide)
      | 1, h, _ => exact absurd h (by decide)
      | n + 8, _, h => exact absurd h (by omega)

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
          st'.halted = true ∧ st'.pc = 10 ∧ trace.length = 4 ∧
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
          st'.halted = true ∧ st'.pc = 24 ∧ trace.length = 9 ∧
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


/-! ## §5. Real `.rlib` SIMD & Architectural-Control Kernels (`DIT`, `GFNI ↔ BinaryTower`, `SHA3 NEON ↔ Keccak`) -/

/-! ### §5.1 Byte-Memory Framing & `GFNI ↔ BinaryTower` $\mathbb{F}_2$-Bilinear Refinement -/

private theorem u8_toU64_bv (b : UInt8) : b.toUInt64.toBitVec = b.toBitVec.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq; simp [UInt8.toNat_toBitVec]

private theorem u64_toU8_bv (w : UInt64) : w.toUInt8.toBitVec = w.toBitVec.setWidth 8 := by
  apply BitVec.eq_of_toNat_eq; simp [UInt64.toNat_toBitVec]

private theorem getByte64_bv (w : UInt64) (i : Nat) (hi : i < 8) :
    (getByte64 w i).toBitVec = (w.toBitVec >>> (i * 8)).setWidth 8 := by
  unfold getByte64
  rw [u64_toU8_bv]
  congr 1
  have hsh : (UInt64.ofNat (i * 8)).toNat % 64 = i * 8 := by
    match i, hi with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => decide
    | n + 8, h => exact absurd h (by omega)
  change (w.toBitVec >>> ((UInt64.ofNat (i * 8)).toNat % 64)) = w.toBitVec >>> (i * 8)
  rw [hsh]

private theorem u8_shl_bit (b : UInt8) (sh : UInt64) (j : Nat) (_hj : j < 64)
    (hsh : sh.toNat ≤ 56) :
    ((b.toUInt64 <<< sh).toBitVec)[j] =
      if sh.toNat ≤ j ∧ j < sh.toNat + 8 then b.toBitVec.getLsbD (j - sh.toNat) else false := by
  have hmod : sh.toNat % 64 = sh.toNat := by omega
  change ((b.toUInt64.toBitVec <<< (sh.toNat % 64)))[j] = _
  rw [hmod, u8_toU64_bv, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth]
  by_cases h1 : j < sh.toNat
  · have h2 : ¬ (sh.toNat ≤ j ∧ j < sh.toNat + 8) := fun h => by omega
    simp [h1, h2]
  · simp only [h1, decide_false, Bool.not_false, Bool.true_and]
    by_cases h2 : j - sh.toNat < 8
    · have h3 : sh.toNat ≤ j ∧ j < sh.toNat + 8 := ⟨by omega, by omega⟩
      simp [h3]
    · have h3 : ¬ (sh.toNat ≤ j ∧ j < sh.toNat + 8) := fun h => by omega
      have hge : b.toBitVec.getLsbD (j - sh.toNat) = false :=
        BitVec.getLsbD_of_ge b.toBitVec (j - sh.toNat) (by omega)
      simp [h3, hge]

theorem getByte64_mapBytes64 (f : Nat → UInt8) (i : Nat) (hi : i < 8) :
    getByte64 (mapBytes64 f) i = f i := by
  apply UInt8.eq_of_toBitVec_eq
  rw [getByte64_bv _ i hi]
  ext r hr
  simp only [BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight]
  have hjr : i * 8 + r < 64 := by omega
  rw [BitVec.getLsbD_eq_getElem hjr]
  unfold mapBytes64
  have h0 : ∀ (b : UInt8) (j : Nat) (hj : j < 64), (b.toUInt64.toBitVec)[j] =
      if j < 8 then b.toBitVec.getLsbD j else false := by
    intro b j _hj
    rw [u8_toU64_bv, BitVec.getElem_setWidth]
    by_cases h : j < 8
    · simp [h]
    · simp [h, BitVec.getLsbD_of_ge b.toBitVec j (by omega)]
  simp only [UInt64.toBitVec_or, BitVec.getElem_or, h0,
    u8_shl_bit _ 8 _ _ (by decide), u8_shl_bit _ 16 _ _ (by decide),
    u8_shl_bit _ 24 _ _ (by decide), u8_shl_bit _ 32 _ _ (by decide),
    u8_shl_bit _ 40 _ _ (by decide), u8_shl_bit _ 48 _ _ (by decide),
    u8_shl_bit _ 56 _ _ (by decide)]
  have hsh8 : (8 : UInt64).toNat = 8 := rfl
  have hsh16 : (16 : UInt64).toNat = 16 := rfl
  have hsh24 : (24 : UInt64).toNat = 24 := rfl
  have hsh32 : (32 : UInt64).toNat = 32 := rfl
  have hsh40 : (40 : UInt64).toNat = 40 := rfl
  have hsh48 : (48 : UInt64).toNat = 48 := rfl
  have hsh56 : (56 : UInt64).toNat = 56 := rfl
  simp only [hsh8, hsh16, hsh24, hsh32, hsh40, hsh48, hsh56, ← BitVec.getLsbD_eq_getElem hr]
  match i, hi, r, hr with
  | 0, _, 0, _ | 0, _, 1, _ | 0, _, 2, _ | 0, _, 3, _ | 0, _, 4, _ | 0, _, 5, _ | 0, _, 6, _ | 0, _, 7, _
  | 1, _, 0, _ | 1, _, 1, _ | 1, _, 2, _ | 1, _, 3, _ | 1, _, 4, _ | 1, _, 5, _ | 1, _, 6, _ | 1, _, 7, _
  | 2, _, 0, _ | 2, _, 1, _ | 2, _, 2, _ | 2, _, 3, _ | 2, _, 4, _ | 2, _, 5, _ | 2, _, 6, _ | 2, _, 7, _
  | 3, _, 0, _ | 3, _, 1, _ | 3, _, 2, _ | 3, _, 3, _ | 3, _, 4, _ | 3, _, 5, _ | 3, _, 6, _ | 3, _, 7, _
  | 4, _, 0, _ | 4, _, 1, _ | 4, _, 2, _ | 4, _, 3, _ | 4, _, 4, _ | 4, _, 5, _ | 4, _, 6, _ | 4, _, 7, _
  | 5, _, 0, _ | 5, _, 1, _ | 5, _, 2, _ | 5, _, 3, _ | 5, _, 4, _ | 5, _, 5, _ | 5, _, 6, _ | 5, _, 7, _
  | 6, _, 0, _ | 6, _, 1, _ | 6, _, 2, _ | 6, _, 3, _ | 6, _, 4, _ | 6, _, 5, _ | 6, _, 6, _ | 6, _, 7, _
  | 7, _, 0, _ | 7, _, 1, _ | 7, _, 2, _ | 7, _, 3, _ | 7, _, 4, _ | 7, _, 5, _ | 7, _, 6, _ | 7, _, 7, _ =>
    simp
  | n + 8, h, _, _ => exact absurd h (by omega)
  | _, _, n + 8, h => exact absurd h (by omega)

theorem mapBytes64_getByte64 (w : UInt64) : mapBytes64 (getByte64 w) = w := by
  apply UInt64.eq_of_toBitVec_eq
  ext j hj
  have hq : j / 8 < 8 := by omega
  have hr : j % 8 < 8 := by omega
  have h1 := congrArg (fun b : UInt8 => b.toBitVec[j % 8]'hr)
    (getByte64_mapBytes64 (getByte64 w) (j / 8) hq)
  simp only [getByte64_bv _ (j / 8) hq, BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight] at h1
  rw [← BitVec.getLsbD_eq_getElem hj, ← BitVec.getLsbD_eq_getElem hj,
    show j = j / 8 * 8 + j % 8 by omega]
  exact h1

private theorem u64_add_ofNat_inj {addr : UInt64} {i j : Nat}
    (hi : i < 0x10000000000000000) (hj : j < 0x10000000000000000)
    (h : addr + UInt64.ofNat i = addr + UInt64.ofNat j) : i = j := by
  have hsub : (addr + UInt64.ofNat i) - addr = (addr + UInt64.ofNat j) - addr :=
    congrArg (· - addr) h
  have hcancel : ∀ x : UInt64, (addr + x) - addr = x := fun x => by
    apply UInt64.eq_of_toBitVec_eq
    change (addr.toBitVec + x.toBitVec) - addr.toBitVec = x.toBitVec
    rw [BitVec.add_comm, BitVec.add_sub_cancel]
  rw [hcancel, hcancel] at hsub
  have hn := congrArg UInt64.toNat hsub
  have hmod1 : (UInt64.ofNat i).toNat = i := Nat.mod_eq_of_lt hi
  have hmod2 : (UInt64.ofNat j).toNat = j := Nat.mod_eq_of_lt hj
  omega

private theorem u64_add_ofNat_assoc (addr : UInt64) (a b : Nat)
    (hab : a + b < 0x10000000000000000) :
    (addr + UInt64.ofNat a) + UInt64.ofNat b = addr + UInt64.ofNat (a + b) := by
  apply UInt64.eq_of_toBitVec_eq
  simp only [UInt64.toBitVec_add, BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have ha : (UInt64.ofNat a).toNat = a := Nat.mod_eq_of_lt (by omega)
  have hb : (UInt64.ofNat b).toNat = b := Nat.mod_eq_of_lt (by omega)
  simp [UInt64.toNat_toBitVec, ha, hb, Nat.mod_eq_of_lt hab]

theorem readMem64_eq_mapBytes64 (mem : UInt64 → UInt8) (addr : UInt64) :
    readMem64 mem addr = mapBytes64 (fun i => mem (addr + UInt64.ofNat i)) := by
  unfold readMem64 mapBytes64
  dsimp only
  have h0 : addr + UInt64.ofNat 0 = addr := by apply UInt64.eq_of_toBitVec_eq; simp
  rw [h0]
  rfl

theorem getByte64_readMem64 (mem : UInt64 → UInt8) (addr : UInt64) (i : Nat) (hi : i < 8) :
    getByte64 (readMem64 mem addr) i = mem (addr + UInt64.ofNat i) := by
  rw [readMem64_eq_mapBytes64, getByte64_mapBytes64 _ i hi]

theorem writeMem64_at (mem : UInt64 → UInt8) (addr : UInt64) (v : UInt64) (i : Nat) (hi : i < 8) :
    writeMem64 mem addr v (addr + UInt64.ofNat i) = getByte64 v i := by
  unfold writeMem64 writeMem8 getByte64
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => simp
  | n + 8, h => exact absurd h (by omega)

theorem writeMem64_outside (mem : UInt64 → UInt8) (addr : UInt64) (v : UInt64) (a : UInt64)
    (ha : ∀ i : Nat, i < 8 → a ≠ addr + UInt64.ofNat i) :
    writeMem64 mem addr v a = mem a := by
  have ha0 : a ≠ addr := by
    have h0 : addr + UInt64.ofNat 0 = addr := by apply UInt64.eq_of_toBitVec_eq; simp
    simpa [h0] using ha 0 (by decide)
  have ha1 : a ≠ addr + 1 := ha 1 (by decide)
  have ha2 : a ≠ addr + 2 := ha 2 (by decide)
  have ha3 : a ≠ addr + 3 := ha 3 (by decide)
  have ha4 : a ≠ addr + 4 := ha 4 (by decide)
  have ha5 : a ≠ addr + 5 := ha 5 (by decide)
  have ha6 : a ≠ addr + 6 := ha 6 (by decide)
  have ha7 : a ≠ addr + 7 := ha 7 (by decide)
  unfold writeMem64 writeMem8
  simp [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7]

theorem readMem64_writeMem64_same (mem : UInt64 → UInt8) (addr v : UInt64) :
    readMem64 (writeMem64 mem addr v) addr = v := by
  rw [readMem64_eq_mapBytes64]
  conv => rhs; rw [← mapBytes64_getByte64 v]
  unfold mapBytes64
  simp only [writeMem64_at mem addr v 0 (by decide), writeMem64_at mem addr v 1 (by decide),
    writeMem64_at mem addr v 2 (by decide), writeMem64_at mem addr v 3 (by decide),
    writeMem64_at mem addr v 4 (by decide), writeMem64_at mem addr v 5 (by decide),
    writeMem64_at mem addr v 6 (by decide), writeMem64_at mem addr v 7 (by decide)]

theorem readMem64_writeMem64_disjoint (mem : UInt64 → UInt8) (a1 a2 v : UInt64)
    (hd : ∀ i j : Nat, i < 8 → j < 8 → a1 + UInt64.ofNat i ≠ a2 + UInt64.ofNat j) :
    readMem64 (writeMem64 mem a2 v) a1 = readMem64 mem a1 := by
  rw [readMem64_eq_mapBytes64, readMem64_eq_mapBytes64]
  unfold mapBytes64
  simp only [writeMem64_outside mem a2 v _ (hd 0 · (by decide)),
    writeMem64_outside mem a2 v _ (hd 1 · (by decide)),
    writeMem64_outside mem a2 v _ (hd 2 · (by decide)),
    writeMem64_outside mem a2 v _ (hd 3 · (by decide)),
    writeMem64_outside mem a2 v _ (hd 4 · (by decide)),
    writeMem64_outside mem a2 v _ (hd 5 · (by decide)),
    writeMem64_outside mem a2 v _ (hd 6 · (by decide)),
    writeMem64_outside mem a2 v _ (hd 7 · (by decide))]

theorem writeMem256_at (mem : UInt64 → UInt8) (addr : UInt64) (v : Vec256) (k : Nat) (hk : k < 32) :
    writeMem256 mem addr v (addr + UInt64.ofNat k) =
      if k < 8 then getByte64 v.w0 k
      else if k < 16 then getByte64 v.w1 (k - 8)
      else if k < 24 then getByte64 v.w2 (k - 16)
      else getByte64 v.w3 (k - 24) := by
  unfold writeMem256
  change writeMem64 (writeMem64 (writeMem64 (writeMem64 mem addr v.w0)
    (addr + UInt64.ofNat 8) v.w1) (addr + UInt64.ofNat 16) v.w2)
    (addr + UInt64.ofNat 24) v.w3 (addr + UInt64.ofNat k) = _
  have hout : ∀ (base : Nat) (_hbase : base ≤ 24) (_hlt : k < base)
      (m : UInt64 → UInt8) (w : UInt64),
      writeMem64 m (addr + UInt64.ofNat base) w (addr + UInt64.ofNat k) = m (addr + UInt64.ofNat k) := by
    intro base _hbase _hlt m w
    apply writeMem64_outside
    intro i _hi heq
    rw [u64_add_ofNat_assoc addr base i (by omega)] at heq
    have := u64_add_ofNat_inj (by omega) (by omega) heq
    omega
  by_cases h0 : k < 8
  · rw [hout 24 (by decide) (by omega), hout 16 (by decide) (by omega), hout 8 (by decide) (by omega)]
    rw [writeMem64_at mem addr v.w0 k h0]
    simp [h0]
  · by_cases h1 : k < 16
    · rw [hout 24 (by decide) (by omega), hout 16 (by decide) (by omega)]
      have hk8 : addr + UInt64.ofNat k = (addr + UInt64.ofNat 8) + UInt64.ofNat (k - 8) := by
        rw [u64_add_ofNat_assoc addr 8 (k - 8) (by omega), show 8 + (k - 8) = k by omega]
      rw [hk8, writeMem64_at _ (addr + UInt64.ofNat 8) v.w1 (k - 8) (by omega)]
      simp [h0, h1]
    · by_cases h2 : k < 24
      · rw [hout 24 (by decide) (by omega)]
        have hk16 : addr + UInt64.ofNat k = (addr + UInt64.ofNat 16) + UInt64.ofNat (k - 16) := by
          rw [u64_add_ofNat_assoc addr 16 (k - 16) (by omega), show 16 + (k - 16) = k by omega]
        rw [hk16, writeMem64_at _ (addr + UInt64.ofNat 16) v.w2 (k - 16) (by omega)]
        simp [h0, h1, h2]
      · have hk24 : addr + UInt64.ofNat k = (addr + UInt64.ofNat 24) + UInt64.ofNat (k - 24) := by
          rw [u64_add_ofNat_assoc addr 24 (k - 24) (by omega), show 24 + (k - 24) = k by omega]
        rw [hk24, writeMem64_at _ (addr + UInt64.ofNat 24) v.w3 (k - 24) (by omega)]
        simp [h0, h1, h2]

theorem writeMem256_outside (mem : UInt64 → UInt8) (addr : UInt64) (v : Vec256) (a : UInt64)
    (ha : ∀ k : Nat, k < 32 → a ≠ addr + UInt64.ofNat k) :
    writeMem256 mem addr v a = mem a := by
  unfold writeMem256
  change writeMem64 (writeMem64 (writeMem64 (writeMem64 mem addr v.w0)
    (addr + UInt64.ofNat 8) v.w1) (addr + UInt64.ofNat 16) v.w2)
    (addr + UInt64.ofNat 24) v.w3 a = mem a
  have hout : ∀ (base : Nat) (_hb : base ≤ 24) (m : UInt64 → UInt8) (w : UInt64),
      writeMem64 m (addr + UInt64.ofNat base) w a = m a := by
    intro base _hb m w
    apply writeMem64_outside
    intro i _hi heq
    rw [u64_add_ofNat_assoc addr base i (by omega)] at heq
    exact ha (base + i) (by omega) heq
  rw [hout 24 (by decide), hout 16 (by decide), hout 8 (by decide)]
  exact writeMem64_outside mem addr v.w0 a (fun i hi => ha i (by omega))

theorem writeMem128_outside (mem : UInt64 → UInt8) (addr : UInt64) (v : Vec128) (a : UInt64)
    (ha : ∀ k : Nat, k < 16 → a ≠ addr + UInt64.ofNat k) :
    writeMem128 mem addr v a = mem a := by
  unfold writeMem128
  rw [writeMem64_outside _ (addr + 8) v.w1 a (fun i _hi heq => by
    change a = (addr + UInt64.ofNat 8) + UInt64.ofNat i at heq
    rw [u64_add_ofNat_assoc addr 8 i (by omega)] at heq
    exact ha (8 + i) (by omega) heq)]
  exact writeMem64_outside mem addr v.w0 a (fun i hi => ha i (by omega))

theorem readMem64_writeMem128_lo (mem : UInt64 → UInt8) (addr : UInt64) (v : Vec128) :
    readMem64 (writeMem128 mem addr v) addr = v.w0 := by
  unfold writeMem128
  rw [readMem64_writeMem64_disjoint _ addr (addr + 8) v.w1 (fun i j _hi _hj heq => by
    change addr + UInt64.ofNat i = (addr + UInt64.ofNat 8) + UInt64.ofNat j at heq
    rw [u64_add_ofNat_assoc addr 8 j (by omega)] at heq
    have := u64_add_ofNat_inj (by omega) (by omega) heq
    omega)]
  exact readMem64_writeMem64_same mem addr v.w0

theorem readMem64_writeMem128_hi (mem : UInt64 → UInt8) (addr : UInt64) (v : Vec128) :
    readMem64 (writeMem128 mem addr v) (addr + 8) = v.w1 := by
  unfold writeMem128
  exact readMem64_writeMem64_same _ (addr + 8) v.w1

theorem readMem64_writeMem128_disjoint (mem : UInt64 → UInt8) (a1 a2 : UInt64) (v : Vec128)
    (hd : ∀ i k : Nat, i < 8 → k < 16 → a1 + UInt64.ofNat i ≠ a2 + UInt64.ofNat k) :
    readMem64 (writeMem128 mem a2 v) a1 = readMem64 mem a1 := by
  rw [readMem64_eq_mapBytes64, readMem64_eq_mapBytes64]
  unfold mapBytes64
  simp only [writeMem128_outside mem a2 v _ (hd 0 · (by decide)),
    writeMem128_outside mem a2 v _ (hd 1 · (by decide)),
    writeMem128_outside mem a2 v _ (hd 2 · (by decide)),
    writeMem128_outside mem a2 v _ (hd 3 · (by decide)),
    writeMem128_outside mem a2 v _ (hd 4 · (by decide)),
    writeMem128_outside mem a2 v _ (hd 5 · (by decide)),
    writeMem128_outside mem a2 v _ (hd 6 · (by decide)),
    writeMem128_outside mem a2 v _ (hd 7 · (by decide))]

/-- Forward basis-change matrix $T \in \mathbb{F}_2^{8 \times 8}$ mapping Wiedemann tower
    `GF(2^8)` (`BinaryTower` level `3`) into Intel GFNI Rijndael $\mathbb{F}_2[z]/(z^8+z^4+z^3+z+1)$. -/
def gfniTowerToRijndaelMat : UInt64 := 0x71500a8a86be78ce

/-- Inverse basis-change matrix $T^{-1} \in \mathbb{F}_2^{8 \times 8}$ mapping Intel GFNI Rijndael
    back into Wiedemann tower `GF(2^8)` (`BinaryTower` level `3`). -/
def gfniRijndaelToTowerMat : UInt64 := 0xa1e4f8e072a2700c

/-- Single-lane GFNI Wiedemann tower multiplication $T^{-1}(T(x) \cdot_{\text{Rijndael}} T(y))$. -/
def gfniTowerMulByte (x y : UInt8) : UInt8 :=
  gfniAffineByte
    (gfniMulByte (gfniAffineByte x gfniTowerToRijndaelMat 0)
                 (gfniAffineByte y gfniTowerToRijndaelMat 0))
    gfniRijndaelToTowerMat 0

private theorem u8_and_xor_left (a b m : UInt8) : (a ^^^ b) &&& m = (a &&& m) ^^^ (b &&& m) := by
  apply UInt8.eq_of_toBitVec_eq
  ext i hi
  simp only [UInt8.toBitVec_and, UInt8.toBitVec_xor, BitVec.getElem_and, BitVec.getElem_xor]
  cases m.toBitVec[i] <;> simp

private theorem u8_and_xor_right (x m1 m2 : UInt8) : x &&& (m1 ^^^ m2) = (x &&& m1) ^^^ (x &&& m2) := by
  apply UInt8.eq_of_toBitVec_eq
  ext i hi
  simp only [UInt8.toBitVec_and, UInt8.toBitVec_xor, BitVec.getElem_and, BitVec.getElem_xor]
  cases x.toBitVec[i] <;> simp

private theorem u8_ushr_xor (a b k : UInt8) : (a ^^^ b) >>> k = (a >>> k) ^^^ (b >>> k) := by
  apply UInt8.eq_of_toBitVec_eq
  change (a.toBitVec ^^^ b.toBitVec) >>> (k.toNat % 8) =
    (a.toBitVec >>> (k.toNat % 8)) ^^^ (b.toBitVec >>> (k.toNat % 8))
  exact BitVec.ushiftRight_xor_distrib a.toBitVec b.toBitVec (k.toNat % 8)

private theorem u8_shl_xor_fwd (a b k : UInt8) : (a ^^^ b) <<< k = (a <<< k) ^^^ (b <<< k) := by
  apply UInt8.eq_of_toBitVec_eq
  change (a.toBitVec ^^^ b.toBitVec) <<< (k.toNat % 8) =
    (a.toBitVec <<< (k.toNat % 8)) ^^^ (b.toBitVec <<< (k.toNat % 8))
  exact BitVec.shiftLeft_xor_distrib a.toBitVec b.toBitVec (k.toNat % 8)

private theorem elf_u8_xor_assoc (a b c : UInt8) : (a ^^^ b) ^^^ c = a ^^^ (b ^^^ c) := by
  apply UInt8.eq_of_toBitVec_eq; simp [BitVec.xor_assoc]

private theorem u8_xor_four (a b c d : UInt8) : (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  apply UInt8.eq_of_toBitVec_eq
  ext i hi
  simp only [UInt8.toBitVec_xor, BitVec.getElem_xor]
  cases a.toBitVec[i] <;> cases b.toBitVec[i] <;> cases c.toBitVec[i] <;> cases d.toBitVec[i] <;> rfl

private theorem u8_xor8_pair (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    (a0 ^^^ b0) ^^^ (a1 ^^^ b1) ^^^ (a2 ^^^ b2) ^^^ (a3 ^^^ b3) ^^^
    (a4 ^^^ b4) ^^^ (a5 ^^^ b5) ^^^ (a6 ^^^ b6) ^^^ (a7 ^^^ b7) =
      (a0 ^^^ a1 ^^^ a2 ^^^ a3 ^^^ a4 ^^^ a5 ^^^ a6 ^^^ a7) ^^^
      (b0 ^^^ b1 ^^^ b2 ^^^ b3 ^^^ b4 ^^^ b5 ^^^ b6 ^^^ b7) := by
  rw [u8_xor_four a0 b0 a1 b1]
  rw [u8_xor_four (a0 ^^^ a1) (b0 ^^^ b1) a2 b2]
  rw [u8_xor_four (a0 ^^^ a1 ^^^ a2) (b0 ^^^ b1 ^^^ b2) a3 b3]
  rw [u8_xor_four (a0 ^^^ a1 ^^^ a2 ^^^ a3) (b0 ^^^ b1 ^^^ b2 ^^^ b3) a4 b4]
  rw [u8_xor_four (a0 ^^^ a1 ^^^ a2 ^^^ a3 ^^^ a4) (b0 ^^^ b1 ^^^ b2 ^^^ b3 ^^^ b4) a5 b5]
  rw [u8_xor_four (a0 ^^^ a1 ^^^ a2 ^^^ a3 ^^^ a4 ^^^ a5) (b0 ^^^ b1 ^^^ b2 ^^^ b3 ^^^ b4 ^^^ b5) a6 b6]
  rw [u8_xor_four (a0 ^^^ a1 ^^^ a2 ^^^ a3 ^^^ a4 ^^^ a5 ^^^ a6)
      (b0 ^^^ b1 ^^^ b2 ^^^ b3 ^^^ b4 ^^^ b5 ^^^ b6) a7 b7]

private theorem elf_u8_xor_self (a : UInt8) : a ^^^ a = 0 := by
  apply UInt8.eq_of_toBitVec_eq; simp

private theorem u8_and_ff (x : UInt8) : x &&& 0xFF = x := by
  rcases x with ⟨⟨n⟩⟩; revert n; decide +kernel

private theorem u8_basis_decomp (x : UInt8) :
    x = (x &&& 0x01) ^^^ (x &&& 0x02) ^^^ (x &&& 0x04) ^^^ (x &&& 0x08) ^^^
        (x &&& 0x10) ^^^ (x &&& 0x20) ^^^ (x &&& 0x40) ^^^ (x &&& 0x80) := by
  have hff : (0xFF : UInt8) = 0x01 ^^^ 0x02 ^^^ 0x04 ^^^ 0x08 ^^^ 0x10 ^^^ 0x20 ^^^ 0x40 ^^^ 0x80 := by decide
  have hx := (u8_and_ff x).symm
  rw [hff] at hx
  simpa only [u8_and_xor_right] using hx

private theorem u8_bit_cases (x m : UInt8)
    (hm : m = 0x01 ∨ m = 0x02 ∨ m = 0x04 ∨ m = 0x08 ∨ m = 0x10 ∨ m = 0x20 ∨ m = 0x40 ∨ m = 0x80) :
    x &&& m = 0 ∨ x &&& m = m := by
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (rcases x with ⟨⟨n⟩⟩; revert n; decide +kernel)

private theorem parityByte_xor (a b : UInt8) : parityByte (a ^^^ b) = parityByte a ^^^ parityByte b := by
  have hy : (a ^^^ b) ^^^ ((a ^^^ b) >>> 4) = (a ^^^ (a >>> 4)) ^^^ (b ^^^ (b >>> 4)) := by
    rw [u8_ushr_xor, u8_xor_four]
  let ya := a ^^^ (a >>> 4); let yb := b ^^^ (b >>> 4)
  have hz : (ya ^^^ yb) ^^^ ((ya ^^^ yb) >>> 2) = (ya ^^^ (ya >>> 2)) ^^^ (yb ^^^ (yb >>> 2)) := by
    rw [u8_ushr_xor, u8_xor_four]
  let za := ya ^^^ (ya >>> 2); let zb := yb ^^^ (yb >>> 2)
  have hw : (za ^^^ zb) ^^^ ((za ^^^ zb) >>> 1) = (za ^^^ (za >>> 1)) ^^^ (zb ^^^ (zb >>> 1)) := by
    rw [u8_ushr_xor, u8_xor_four]
  unfold parityByte; dsimp only
  rw [hy, hz, hw, u8_and_xor_left]

private theorem gfniAffine_t2r_eq (x : UInt8) :
    gfniAffineByte x gfniTowerToRijndaelMat 0 =
      ((parityByte (x &&& 0x71)) <<< 0) ^^^ ((parityByte (x &&& 0x50)) <<< 1) ^^^
      ((parityByte (x &&& 0x0a)) <<< 2) ^^^ ((parityByte (x &&& 0x8a)) <<< 3) ^^^
      ((parityByte (x &&& 0x86)) <<< 4) ^^^ ((parityByte (x &&& 0xbe)) <<< 5) ^^^
      ((parityByte (x &&& 0x78)) <<< 6) ^^^ ((parityByte (x &&& 0xce)) <<< 7) := by
  rcases x with ⟨⟨n⟩⟩; revert n; decide +kernel

private theorem gfniAffine_r2t_eq (x : UInt8) :
    gfniAffineByte x gfniRijndaelToTowerMat 0 =
      ((parityByte (x &&& 0xa1)) <<< 0) ^^^ ((parityByte (x &&& 0xe4)) <<< 1) ^^^
      ((parityByte (x &&& 0xf8)) <<< 2) ^^^ ((parityByte (x &&& 0xe0)) <<< 3) ^^^
      ((parityByte (x &&& 0x72)) <<< 4) ^^^ ((parityByte (x &&& 0xa2)) <<< 5) ^^^
      ((parityByte (x &&& 0x70)) <<< 6) ^^^ ((parityByte (x &&& 0x0c)) <<< 7) := by
  rcases x with ⟨⟨n⟩⟩; revert n; decide +kernel

private theorem gfniAffine_t2r_xor (a b : UInt8) :
    gfniAffineByte (a ^^^ b) gfniTowerToRijndaelMat 0 =
      gfniAffineByte a gfniTowerToRijndaelMat 0 ^^^ gfniAffineByte b gfniTowerToRijndaelMat 0 := by
  simp only [gfniAffine_t2r_eq, u8_and_xor_left, parityByte_xor, u8_shl_xor_fwd]
  exact u8_xor8_pair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

private theorem gfniAffine_r2t_xor (a b : UInt8) :
    gfniAffineByte (a ^^^ b) gfniRijndaelToTowerMat 0 =
      gfniAffineByte a gfniRijndaelToTowerMat 0 ^^^ gfniAffineByte b gfniRijndaelToTowerMat 0 := by
  simp only [gfniAffine_r2t_eq, u8_and_xor_left, parityByte_xor, u8_shl_xor_fwd]
  exact u8_xor8_pair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

private theorem xtimeRijndael_xor (a b : UInt8) :
    xtimeRijndael (a ^^^ b) = xtimeRijndael a ^^^ xtimeRijndael b := by
  unfold xtimeRijndael; dsimp only
  rw [u8_shl_xor_fwd, u8_and_xor_left]
  rcases u8_bit_cases a 0x80 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))) with ha | ha <;>
  rcases u8_bit_cases b 0x80 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))) with hb | hb
  · rw [ha, hb]; simp
  · rw [ha, hb]; simp; exact elf_u8_xor_assoc _ _ _
  · rw [ha, hb]; simp
    apply UInt8.eq_of_toBitVec_eq; ext i hi; simp only [UInt8.toBitVec_xor, BitVec.getElem_xor]
    cases (a <<< 1).toBitVec[i] <;> cases (b <<< 1).toBitVec[i] <;> cases (0x1B : UInt8).toBitVec[i] <;> rfl
  · rw [ha, hb, elf_u8_xor_self]; simp
    rw [u8_xor_four, elf_u8_xor_self]; apply UInt8.eq_of_toBitVec_eq; simp

private theorem gfniMulByte_xor_left (a1 a2 b : UInt8) :
    gfniMulByte (a1 ^^^ a2) b = gfniMulByte a1 b ^^^ gfniMulByte a2 b := by
  have hIf : ∀ (c : Bool) (u v : UInt8),
      (if c then u ^^^ v else 0) = (if c then u else 0) ^^^ (if c then v else 0) := by
    intro c u v; cases c <;> simp
  unfold gfniMulByte
  simp only [xtimeRijndael_xor, hIf]
  exact u8_xor8_pair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

private theorem gfniMulByte_xor_right (a b1 b2 : UInt8) :
    gfniMulByte a (b1 ^^^ b2) = gfniMulByte a b1 ^^^ gfniMulByte a b2 := by
  have hPick : ∀ (i : UInt8) (ai : UInt8),
      (if ((((b1 ^^^ b2) >>> i) &&& 1) != 0) then ai else 0) =
        (if (((b1 >>> i) &&& 1) != 0) then ai else 0) ^^^ (if (((b2 >>> i) &&& 1) != 0) then ai else 0) := by
    intro i ai
    rw [u8_ushr_xor, u8_and_xor_left]
    rcases u8_bit_cases (b1 >>> i) 0x01 (Or.inl rfl) with h1 | h1 <;>
    rcases u8_bit_cases (b2 >>> i) 0x01 (Or.inl rfl) with h2 | h2 <;>
    (rw [h1, h2]; simp)
  unfold gfniMulByte
  simp only [hPick]
  exact u8_xor8_pair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

private theorem gfniTowerMulByte_zero_left (y : UInt8) : gfniTowerMulByte 0 y = 0 := by
  rcases y with ⟨⟨n⟩⟩; revert n; decide +kernel

private theorem gfniTowerMulByte_zero_right (x : UInt8) : gfniTowerMulByte x 0 = 0 := by
  rcases x with ⟨⟨n⟩⟩; revert n; decide +kernel

private theorem gfniTowerMulByte_xor_left (x1 x2 y : UInt8) :
    gfniTowerMulByte (x1 ^^^ x2) y = gfniTowerMulByte x1 y ^^^ gfniTowerMulByte x2 y := by
  unfold gfniTowerMulByte
  rw [gfniAffine_t2r_xor, gfniMulByte_xor_left, gfniAffine_r2t_xor]

private theorem gfniTowerMulByte_xor_right (x y1 y2 : UInt8) :
    gfniTowerMulByte x (y1 ^^^ y2) = gfniTowerMulByte x y1 ^^^ gfniTowerMulByte x y2 := by
  unfold gfniTowerMulByte
  rw [gfniAffine_t2r_xor, gfniMulByte_xor_right, gfniAffine_r2t_xor]

private theorem unpackTower_xor (k : Nat) (x y : TowerBitVec k) :
    unpackTower k (x ^^^ y) = towerAdd k (unpackTower k x) (unpackTower k y) := by
  apply packTower_injective k
  rw [packTower_unpackTower, packTower_add, packTower_unpackTower, packTower_unpackTower]

private theorem mulExec_eq_pack_towerMul (k : Nat) (x y : TowerBitVec k) :
    mulExec k x y = packTower k (towerMul k (unpackTower k x) (unpackTower k y)) := by
  have hx := (packTower_unpackTower k x).symm
  have hy := (packTower_unpackTower k y).symm
  conv => lhs; rw [hx, hy, mulExec_refines]

private theorem mulExec3_zero_left (y : BitVec 8) : mulExec 3 0#8 y = 0#8 := by
  change mulExec 3 (0 : TowerBitVec 3) y = 0
  rw [mulExec_eq_pack_towerMul, unpackTower_zero, towerMul_comm, towerMul_zero, packTower_zero]

private theorem mulExec3_zero_right (x : BitVec 8) : mulExec 3 x 0#8 = 0#8 := by
  change mulExec 3 x (0 : TowerBitVec 3) = 0
  rw [mulExec_eq_pack_towerMul, unpackTower_zero, towerMul_zero, packTower_zero]

private theorem mulExec3_xor_left (x1 x2 y : BitVec 8) :
    mulExec 3 (x1 ^^^ x2) y = mulExec 3 x1 y ^^^ mulExec 3 x2 y := by
  rw [mulExec_eq_pack_towerMul, unpackTower_xor, towerAdd_mul_distrib, packTower_add,
      ← mulExec_eq_pack_towerMul, ← mulExec_eq_pack_towerMul]

private theorem mulExec3_xor_right (x y1 y2 : BitVec 8) :
    mulExec 3 x (y1 ^^^ y2) = mulExec 3 x y1 ^^^ mulExec 3 x y2 := by
  rw [mulExec_eq_pack_towerMul, unpackTower_xor, towerMul_add_distrib, packTower_add,
      ← mulExec_eq_pack_towerMul, ← mulExec_eq_pack_towerMul]

private theorem gfniTowerMulByte_gen_eq (mx : UInt8)
    (hmx : mx = 0x01 ∨ mx = 0x02 ∨ mx = 0x04 ∨ mx = 0x08 ∨ mx = 0x10 ∨ mx = 0x20 ∨ mx = 0x40 ∨ mx = 0x80)
    (y : UInt8) :
    (gfniTowerMulByte mx y).toBitVec = mulExec 3 mx.toBitVec y.toBitVec := by
  have hBit : ∀ (my : UInt8),
      my = 0x01 ∨ my = 0x02 ∨ my = 0x04 ∨ my = 0x08 ∨ my = 0x10 ∨ my = 0x20 ∨ my = 0x40 ∨ my = 0x80 →
      (gfniTowerMulByte mx (y &&& my)).toBitVec = mulExec 3 mx.toBitVec (y &&& my).toBitVec := by
    intro my hmy
    rcases u8_bit_cases y my hmy with h0 | h1
    · rw [h0, gfniTowerMulByte_zero_right]; simp [mulExec3_zero_right]
    · rw [h1]
      rcases hmx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hmy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide +kernel
  conv => lhs; rw [u8_basis_decomp y]
  conv => rhs; rw [u8_basis_decomp y]
  simp only [gfniTowerMulByte_xor_right, UInt8.toBitVec_xor, mulExec3_xor_right,
    hBit 0x01 (Or.inl rfl),
    hBit 0x02 (Or.inr (Or.inl rfl)),
    hBit 0x04 (Or.inr (Or.inr (Or.inl rfl))),
    hBit 0x08 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
    hBit 0x10 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),
    hBit 0x20 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))),
    hBit 0x40 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))),
    hBit 0x80 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))]

/-- Exact $\mathbb{F}_2$-bilinear isomorphism theorem (`0 native_decide`, `0 bv_decide`):
    Intel GFNI Rijndael multiplication conjugated by `gfniTowerToRijndaelMat` /
    `gfniRijndaelToTowerMat` equals `BinaryTower.mulExec 3` for every byte pair `(x, y)`. -/
theorem gfniTowerMulByte_eq_mulExec (x y : UInt8) :
    (gfniTowerMulByte x y).toBitVec = mulExec 3 x.toBitVec y.toBitVec := by
  have hBit : ∀ (mx : UInt8),
      mx = 0x01 ∨ mx = 0x02 ∨ mx = 0x04 ∨ mx = 0x08 ∨ mx = 0x10 ∨ mx = 0x20 ∨ mx = 0x40 ∨ mx = 0x80 →
      (gfniTowerMulByte (x &&& mx) y).toBitVec = mulExec 3 (x &&& mx).toBitVec y.toBitVec := by
    intro mx hmx
    rcases u8_bit_cases x mx hmx with h0 | h1
    · rw [h0, gfniTowerMulByte_zero_left]; simp [mulExec3_zero_left]
    · rw [h1]; exact gfniTowerMulByte_gen_eq mx hmx y
  conv => lhs; rw [u8_basis_decomp x]
  conv => rhs; rw [u8_basis_decomp x]
  simp only [gfniTowerMulByte_xor_left, UInt8.toBitVec_xor, mulExec3_xor_left,
    hBit 0x01 (Or.inl rfl),
    hBit 0x02 (Or.inr (Or.inl rfl)),
    hBit 0x04 (Or.inr (Or.inr (Or.inl rfl))),
    hBit 0x08 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
    hBit 0x10 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),
    hBit 0x20 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))),
    hBit 0x40 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))),
    hBit 0x80 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))]

/-- `Spec ↔ Exec` refinement connecting GFNI machine instructions directly to `BinaryTower.towerMul 3`. -/
theorem gfniTowerMulByte_simulates_binaryTower (x y : UInt8) :
    Simulates 3 (towerMul 3 (unpackTower 3 x.toBitVec) (unpackTower 3 y.toBitVec))
      (gfniTowerMulByte x y).toBitVec := by
  rw [gfniTowerMulByte_eq_mulExec]
  exact Simulates.mul 3 (packTower_unpackTower 3 x.toBitVec) (packTower_unpackTower 3 y.toBitVec)

/-! ### §5.2 `qsag_asm_enable_dit_aarch64` (`N = 3`, `retPc = 8`) -/

def enableDitArmProg : List (DecodedInstr Arm64Instr) := [
  ⟨0, 4, .msrDit 1⟩,
  ⟨4, 4, .isb⟩,
  ⟨8, 4, .ret⟩
]

private theorem enableDitArm_reaches (g : Bank32 UInt64) (v : Bank32 Vec128)
    (cf zf dit : Bool) (m : UInt64 → UInt8) :
    ExecReachesArm64 enableDitArmProg 2
      ⟨0, g, v, cf, zf, dit, false, m⟩
      ⟨8, g, v, cf, zf, true, false, m⟩ := by
  apply StepsArm64.toExecReaches
  exact StepsArm64.cons rfl rfl rfl (StepsArm64.cons rfl rfl rfl (StepsArm64.zero _))

theorem rlib_enable_dit_aarch64_functional_and_ct :
    ∃ slice m,
      extractRlibFuncBytes aarch64RlibArchiveBytes "qsag_asm_enable_dit_aarch64" = some slice ∧
      m ∈ parseArArchive aarch64RlibArchiveBytes ∧
      ArPayloadOk aarch64RlibArchiveBytes m ∧
      checkElfFuncThreeWayNI m.payload "qsag_asm_enable_dit_aarch64"
        (mkContract "qsag_asm_enable_dit_aarch64" []) = true ∧
      ElfSliceThreeWayNISafe slice (mkContract "qsag_asm_enable_dit_aarch64" []) ∧
      decodeArm64Slice slice.code = some enableDitArmProg ∧
      ∀ (st : Arm64BvState), st.pc = 0 → st.halted = false →
        (∃ st2 tr2, execDecodedArm64 slice.code 2 st = some (st2, tr2) ∧ st2.halted = false) ∧
        ∀ extra : Nat, ∃ st' trace,
          execDecodedArm64 slice.code (3 + extra) st = some (st', trace) ∧
          st'.halted = true ∧ st'.pc = 8 ∧ trace.length = 3 ∧
          st'.dit = true ∧
          st'.gpr = st.gpr ∧
          st'.vec = st.vec ∧
          st'.cf = st.cf ∧ st'.zf = st.zf ∧
          Arm64CalleeSavedPreserved st st' ∧
          st'.mem = st.mem := by
  cases hFind : aarch64ExtractedSlices.find? (fun s => s.name == "qsag_asm_enable_dit_aarch64") with
  | none => exfalso; revert hFind; decide +kernel
  | some slice =>
    have hExt : extractRlibFuncBytes aarch64RlibArchiveBytes "qsag_asm_enable_dit_aarch64" = some slice := by
      rw [extractRlibFuncBytes_aarch64_eq, hFind]
    have hNI : checkElfSliceThreeWayNI slice (mkContract "qsag_asm_enable_dit_aarch64" []) = true := by
      have hCheck : ((aarch64ExtractedSlices.find? (fun s => s.name == "qsag_asm_enable_dit_aarch64")).map
          (fun sl => checkElfSliceThreeWayNI sl (mkContract "qsag_asm_enable_dit_aarch64" []))) =
          some true := by decide +kernel
      rw [hFind] at hCheck
      exact Option.some.inj hCheck
    have hDec : decodeArm64Slice slice.code = some enableDitArmProg := by
      have hD : (aarch64ExtractedSlices.find? (fun s => s.name == "qsag_asm_enable_dit_aarch64")).bind
          (fun sl => decodeArm64Slice sl.code) = some enableDitArmProg := by decide +kernel
      rw [hFind] at hD
      exact hD
    obtain ⟨m, hm, hPay, _, hMemNI, _, hSafe⟩ :=
      extractRlibFuncBytes_member_ni_sound aarch64_rlib_distinct_names hExt hNI
    refine ⟨slice, m, hExt, hm, hPay, hMemNI, hSafe, hDec, ?_⟩
    intro st hpc hh
    rcases st with ⟨pc, ⟨lo, hi⟩, v, cf, zf, dit, hlt, mem⟩
    dsimp only at hpc hh; subst hpc hh
    let st0 : Arm64BvState := ⟨0, ⟨lo, hi⟩, v, cf, zf, dit, false, mem⟩
    obtain ⟨hPre, hPost⟩ := execDecodedArm64_ret_of_reaches st0 hDec rfl
      (enableDitArm_reaches (bank32ToU64 ⟨lo, hi⟩) v cf zf dit (fun a => mem a.toBitVec)) rfl rfl
    refine ⟨hPre, fun extra => ?_⟩
    obtain ⟨tr, hExec, hL⟩ := hPost extra
    refine ⟨_, tr, hExec, rfl, rfl, hL, rfl, ?_, rfl, rfl, rfl, arm64_callee_saved_of_hi_vec, mem_roundtrip mem⟩
    show (⟨bank16OfU64 (bank16ToU64 lo), bank16OfU64 (bank16ToU64 hi)⟩ : Bank32 (BitVec 64)) = ⟨lo, hi⟩
    rw [bank16_roundtrip, bank16_roundtrip]

/-! ### §5.3 `qsag_asm_gf256_shamir_mul_gfni` (`x86_64` AVX2 + GFNI `BinaryTower` Shamir Multiplication & Loop) -/

def gf256MulGfniProg : List (DecodedInstr X86Instr) := [
  ⟨0, 10, .movImm true 0 0x71500a8a86be78ce⟩,
  ⟨10, 5, .vmovGprToXmm true 14 0⟩,
  ⟨15, 5, .vpbroadcast true true 14 14⟩,
  ⟨20, 10, .movImm true 0 0xa1e4f8e072a2700c⟩,
  ⟨30, 5, .vmovGprToXmm true 15 0⟩,
  ⟨35, 5, .vpbroadcast true true 15 15⟩,
  ⟨40, 4, .vload true 0 (.baseDisp 6 0)⟩,
  ⟨44, 4, .vload true 1 (.baseDisp 2 0)⟩,
  ⟨48, 6, .vgf2p8affineqb true 0 0 14 0⟩,
  ⟨54, 6, .vgf2p8affineqb true 1 1 14 0⟩,
  ⟨60, 5, .vbinOp .vgf2p8mulb true 2 0 1⟩,
  ⟨65, 6, .vgf2p8affineqb true 2 2 15 0⟩,
  ⟨71, 4, .vstore true 2 (.baseDisp 7 0)⟩,
  ⟨75, 4, .aluImm .add true 6 32⟩,
  ⟨79, 4, .aluImm .add true 2 32⟩,
  ⟨83, 4, .aluImm .add true 7 32⟩,
  ⟨87, 3, .incDec false true 1⟩,
  ⟨90, 2, .jcc 5 40⟩,
  ⟨92, 4, .vbinOp .vpxor true 0 0 0⟩,
  ⟨96, 4, .vbinOp .vpxor true 1 1 1⟩,
  ⟨100, 4, .vbinOp .vpxor true 2 2 2⟩,
  ⟨104, 5, .vbinOp .vpxor true 14 14 14⟩,
  ⟨109, 5, .vbinOp .vpxor true 15 15 15⟩,
  ⟨114, 3, .vzeroupper⟩,
  ⟨117, 1, .ret⟩
]

def gf256MulGfniCoreProg : List (DecodedInstr X86Instr) :=
  gf256MulGfniProg.take 23

def gf256MulGfniVec (vA vB : Vec256) : Vec256 :=
  let mT2R : Vec256 := ⟨gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat⟩
  let mR2T : Vec256 := ⟨gfniRijndaelToTowerMat, gfniRijndaelToTowerMat, gfniRijndaelToTowerMat, gfniRijndaelToTowerMat⟩
  gfniAffineVec256 (mapBytesVec256 (gfniAffineVec256 vA mT2R 0) (gfniAffineVec256 vB mT2R 0) gfniMulByte) mR2T 0

def gf256MulGfniStepMem (mem : UInt64 → UInt8) (dst srcA srcB : UInt64) : UInt64 → UInt8 :=
  writeMem256 mem dst (gf256MulGfniVec (readMem256 mem srcA) (readMem256 mem srcB))

def gf256MulGfniIterMem : Nat → (UInt64 → UInt8) → UInt64 → UInt64 → UInt64 → (UInt64 → UInt8)
  | 0, mem, _, _, _ => mem
  | k + 1, mem, dst, srcA, srcB =>
    gf256MulGfniIterMem k (gf256MulGfniStepMem mem dst srcA srcB) (dst + 32) (srcA + 32) (srcB + 32)

private theorem gf256MulGfniVec_lane_byte (vA vB : Vec256) (r : Nat) (hr : r < 8) :
    getByte64 (gf256MulGfniVec vA vB).w0 r =
        gfniTowerMulByte (getByte64 vA.w0 r) (getByte64 vB.w0 r) ∧
    getByte64 (gf256MulGfniVec vA vB).w1 r =
        gfniTowerMulByte (getByte64 vA.w1 r) (getByte64 vB.w1 r) ∧
    getByte64 (gf256MulGfniVec vA vB).w2 r =
        gfniTowerMulByte (getByte64 vA.w2 r) (getByte64 vB.w2 r) ∧
    getByte64 (gf256MulGfniVec vA vB).w3 r =
        gfniTowerMulByte (getByte64 vA.w3 r) (getByte64 vB.w3 r) := by
  unfold gf256MulGfniVec gfniAffineVec256 mapBytesVec256 gfniTowerMulByte
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    rw [getByte64_mapBytes64 _ r hr, getByte64_mapBytes64 _ r hr,
        getByte64_mapBytes64 _ r hr, getByte64_mapBytes64 _ r hr]

theorem gf256MulGfniStepMem_at (mem : UInt64 → UInt8) (dst srcA srcB : UInt64) (k : Nat) (hk : k < 32) :
    gf256MulGfniStepMem mem dst srcA srcB (dst + UInt64.ofNat k) =
      gfniTowerMulByte (mem (srcA + UInt64.ofNat k)) (mem (srcB + UInt64.ofNat k)) := by
  unfold gf256MulGfniStepMem
  rw [writeMem256_at _ dst _ k hk]
  by_cases h0 : k < 8
  · simp only [h0, ↓reduceIte]
    rw [(gf256MulGfniVec_lane_byte _ _ k h0).1]
    unfold readMem256; dsimp only
    rw [getByte64_readMem64 mem srcA k h0, getByte64_readMem64 mem srcB k h0]
  · by_cases h1 : k < 16
    · simp only [h0, h1, ↓reduceIte]
      rw [(gf256MulGfniVec_lane_byte _ _ (k - 8) (by omega)).2.1]
      unfold readMem256; dsimp only
      rw [getByte64_readMem64 mem (srcA + 8) (k - 8) (by omega),
          getByte64_readMem64 mem (srcB + 8) (k - 8) (by omega)]
      have ha : (srcA + 8) + UInt64.ofNat (k - 8) = srcA + UInt64.ofNat k := by
        change (srcA + UInt64.ofNat 8) + UInt64.ofNat (k - 8) = srcA + UInt64.ofNat k
        rw [u64_add_ofNat_assoc srcA 8 (k - 8) (by omega), show 8 + (k - 8) = k by omega]
      have hb : (srcB + 8) + UInt64.ofNat (k - 8) = srcB + UInt64.ofNat k := by
        change (srcB + UInt64.ofNat 8) + UInt64.ofNat (k - 8) = srcB + UInt64.ofNat k
        rw [u64_add_ofNat_assoc srcB 8 (k - 8) (by omega), show 8 + (k - 8) = k by omega]
      rw [ha, hb]
    · by_cases h2 : k < 24
      · simp only [h0, h1, h2, ↓reduceIte]
        rw [(gf256MulGfniVec_lane_byte _ _ (k - 16) (by omega)).2.2.1]
        unfold readMem256; dsimp only
        rw [getByte64_readMem64 mem (srcA + 16) (k - 16) (by omega),
            getByte64_readMem64 mem (srcB + 16) (k - 16) (by omega)]
        have ha : (srcA + 16) + UInt64.ofNat (k - 16) = srcA + UInt64.ofNat k := by
          change (srcA + UInt64.ofNat 16) + UInt64.ofNat (k - 16) = srcA + UInt64.ofNat k
          rw [u64_add_ofNat_assoc srcA 16 (k - 16) (by omega), show 16 + (k - 16) = k by omega]
        have hb : (srcB + 16) + UInt64.ofNat (k - 16) = srcB + UInt64.ofNat k := by
          change (srcB + UInt64.ofNat 16) + UInt64.ofNat (k - 16) = srcB + UInt64.ofNat k
          rw [u64_add_ofNat_assoc srcB 16 (k - 16) (by omega), show 16 + (k - 16) = k by omega]
        rw [ha, hb]
      · simp only [h0, h1, h2, ↓reduceIte]
        rw [(gf256MulGfniVec_lane_byte _ _ (k - 24) (by omega)).2.2.2]
        unfold readMem256; dsimp only
        rw [getByte64_readMem64 mem (srcA + 24) (k - 24) (by omega),
            getByte64_readMem64 mem (srcB + 24) (k - 24) (by omega)]
        have ha : (srcA + 24) + UInt64.ofNat (k - 24) = srcA + UInt64.ofNat k := by
          change (srcA + UInt64.ofNat 24) + UInt64.ofNat (k - 24) = srcA + UInt64.ofNat k
          rw [u64_add_ofNat_assoc srcA 24 (k - 24) (by omega), show 24 + (k - 24) = k by omega]
        have hb : (srcB + 24) + UInt64.ofNat (k - 24) = srcB + UInt64.ofNat k := by
          change (srcB + UInt64.ofNat 24) + UInt64.ofNat (k - 24) = srcB + UInt64.ofNat k
          rw [u64_add_ofNat_assoc srcB 24 (k - 24) (by omega), show 24 + (k - 24) = k by omega]
        rw [ha, hb]

theorem gf256MulGfniStepMem_outside (mem : UInt64 → UInt8) (dst srcA srcB a : UInt64)
    (ha : ∀ k : Nat, k < 32 → a ≠ dst + UInt64.ofNat k) :
    gf256MulGfniStepMem mem dst srcA srcB a = mem a :=
  writeMem256_outside mem dst _ a ha

theorem gf256MulGfniIterMem_outside (n : Nat) (mem : UInt64 → UInt8) (dst srcA srcB a : UInt64)
    (hn : 32 * n ≤ 0x10000000000000000)
    (ha : ∀ idx : Nat, idx < 32 * n → a ≠ dst + UInt64.ofNat idx) :
    gf256MulGfniIterMem n mem dst srcA srcB a = mem a := by
  induction n generalizing mem dst srcA srcB with
  | zero => rfl
  | succ k ih =>
    unfold gf256MulGfniIterMem
    rw [ih _ (dst + 32) (srcA + 32) (srcB + 32) (by omega) (fun idx hidx heq => by
      change a = (dst + UInt64.ofNat 32) + UInt64.ofNat idx at heq
      rw [u64_add_ofNat_assoc dst 32 idx (by omega)] at heq
      exact ha (32 + idx) (by omega) heq)]
    exact gf256MulGfniStepMem_outside mem dst srcA srcB a (fun j hj => ha j (by omega))

theorem gf256MulGfniIterMem_at (n : Nat) (mem : UInt64 → UInt8) (dst srcA srcB : UInt64)
    (hn : 32 * n ≤ 0x10000000000000000)
    (hDisjA : ∀ i j : Nat, i < 32 * n → j < 32 * n → dst + UInt64.ofNat i ≠ srcA + UInt64.ofNat j)
    (hDisjB : ∀ i j : Nat, i < 32 * n → j < 32 * n → dst + UInt64.ofNat i ≠ srcB + UInt64.ofNat j)
    (idx : Nat) (hidx : idx < 32 * n) :
    gf256MulGfniIterMem n mem dst srcA srcB (dst + UInt64.ofNat idx) =
      gfniTowerMulByte (mem (srcA + UInt64.ofNat idx)) (mem (srcB + UInt64.ofNat idx)) := by
  induction n generalizing mem dst srcA srcB idx with
  | zero => exact absurd hidx (by omega)
  | succ k ih =>
    unfold gf256MulGfniIterMem
    by_cases hFirst : idx < 32
    · rw [gf256MulGfniIterMem_outside k _ (dst + 32) (srcA + 32) (srcB + 32) _ (by omega)
        (fun j hj heq => by
          change dst + UInt64.ofNat idx = (dst + UInt64.ofNat 32) + UInt64.ofNat j at heq
          rw [u64_add_ofNat_assoc dst 32 j (by omega)] at heq
          have := u64_add_ofNat_inj (by omega) (by omega) heq
          omega)]
      exact gf256MulGfniStepMem_at mem dst srcA srcB idx hFirst
    · have hAddr : dst + UInt64.ofNat idx = (dst + 32) + UInt64.ofNat (idx - 32) := by
        change dst + UInt64.ofNat idx = (dst + UInt64.ofNat 32) + UInt64.ofNat (idx - 32)
        rw [u64_add_ofNat_assoc dst 32 (idx - 32) (by omega), show 32 + (idx - 32) = idx by omega]
      rw [hAddr, ih (gf256MulGfniStepMem mem dst srcA srcB) (dst + 32) (srcA + 32) (srcB + 32) (by omega)
        (fun i j hi hj heq => by
          change (dst + UInt64.ofNat 32) + UInt64.ofNat i = (srcA + UInt64.ofNat 32) + UInt64.ofNat j at heq
          rw [u64_add_ofNat_assoc dst 32 i (by omega), u64_add_ofNat_assoc srcA 32 j (by omega)] at heq
          exact hDisjA (32 + i) (32 + j) (by omega) (by omega) heq)
        (fun i j hi hj heq => by
          change (dst + UInt64.ofNat 32) + UInt64.ofNat i = (srcB + UInt64.ofNat 32) + UInt64.ofNat j at heq
          rw [u64_add_ofNat_assoc dst 32 i (by omega), u64_add_ofNat_assoc srcB 32 j (by omega)] at heq
          exact hDisjB (32 + i) (32 + j) (by omega) (by omega) heq)
        (idx - 32) (by omega)]
      have hA : (srcA + 32) + UInt64.ofNat (idx - 32) = srcA + UInt64.ofNat idx := by
        change (srcA + UInt64.ofNat 32) + UInt64.ofNat (idx - 32) = srcA + UInt64.ofNat idx
        rw [u64_add_ofNat_assoc srcA 32 (idx - 32) (by omega), show 32 + (idx - 32) = idx by omega]
      have hB : (srcB + 32) + UInt64.ofNat (idx - 32) = srcB + UInt64.ofNat idx := by
        change (srcB + UInt64.ofNat 32) + UInt64.ofNat (idx - 32) = srcB + UInt64.ofNat idx
        rw [u64_add_ofNat_assoc srcB 32 (idx - 32) (by omega), show 32 + (idx - 32) = idx by omega]
      rw [hA, hB,
          gf256MulGfniStepMem_outside mem dst srcA srcB (srcA + UInt64.ofNat idx)
            (fun j hj heq => hDisjA j idx (by omega) hidx heq.symm),
          gf256MulGfniStepMem_outside mem dst srcA srcB (srcB + UInt64.ofNat idx)
            (fun j hj heq => hDisjB j idx (by omega) hidx heq.symm)]

private theorem stepX86_addImm64 (off len pc dst : Nat) (imm : UInt64)
    (g : Bank16 UInt64) (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    (stepX86 ⟨off, len, .aluImm .add true dst imm⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (g.get dst + imm), y,
        decide ((g.get dst).toNat + imm.toNat ≥ 0x10000000000000000),
        evalX86AluOf .add true (g.get dst) imm cf,
        (g.get dst + imm) == 0, dy, false, m⟩ := by
  have h : (stepX86 ⟨off, len, .aluImm .add true dst imm⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len,
        g.set dst (UInt64.ofNat (((g.get dst).toNat + imm.toNat) % 0x10000000000000000)), y,
        decide ((g.get dst).toNat + imm.toNat ≥ 0x10000000000000000),
        evalX86AluOf .add true (g.get dst) imm cf,
        UInt64.ofNat (((g.get dst).toNat + imm.toNat) % 0x10000000000000000) == 0,
        dy, false, m⟩ := by rfl
  rw [h, uint64_evalAdd_eq]

private theorem stepX86_dec64 (off len pc dst : Nat)
    (g : Bank16 UInt64) (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    (stepX86 ⟨off, len, .incDec false true dst⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (g.get dst - 1), y, cf, evalX86IncDecOf false true (g.get dst),
        (g.get dst - 1) == 0, dy, false, m⟩ := by
  have hsub : g.get dst + (0 - 1) = g.get dst - 1 := by
    apply UInt64.eq_of_toBitVec_eq; simp [BitVec.sub_eq_add_neg]
  simp only [stepX86_dec, maskGprWidth_true, hsub]

private theorem elf_u64_xor_self (x : UInt64) : x ^^^ x = 0 := by
  apply UInt64.eq_of_toBitVec_eq; simp

private theorem u64_add_zero (x : UInt64) : x + 0 = x := by
  apply UInt64.eq_of_toBitVec_eq; simp

private theorem gf256MulGfniBody_one_iter
    (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 : Vec256)
    (cf o zf : Bool) (m : UInt64 → UInt8) :
    let mT2R : Vec256 := ⟨gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat⟩
    let mR2T : Vec256 := ⟨gfniRijndaelToTowerMat, gfniRijndaelToTowerMat, gfniRijndaelToTowerMat, gfniRijndaelToTowerMat⟩
    StepsX86 gf256MulGfniCoreProg 12
      ⟨40, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, mT2R, mR2T⟩,
        cf, o, zf, true, false, m⟩
      ⟨jccPc (!((r1 - 1) == 0)) 40 92,
        ⟨r0, r1 - 1, r2 + 32, r3, r4, r5, r6 + 32, r7 + 32, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨gfniAffineVec256 (readMem256 m r6) mT2R 0,
          gfniAffineVec256 (readMem256 m r2) mT2R 0,
          gf256MulGfniVec (readMem256 m r6) (readMem256 m r2),
          y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, mT2R, mR2T⟩,
        decide (r7.toNat + (32 : UInt64).toNat ≥ 0x10000000000000000),
        evalX86IncDecOf false true r1,
        (r1 - 1) == 0, true, false, gf256MulGfniStepMem m r7 r6 r2⟩ := by
  dsimp only
  iterate 7
    apply StepsX86.cons rfl rfl
    · simp only [stepX86, evalX86Addr, clampVecWidth, evalVecBin256,
        u64_add_zero, b16get_2, b16get_6, b16get_7]
      rfl
  iterate 3
    apply StepsX86.cons rfl rfl
    · rw [stepX86_addImm64]
  apply StepsX86.cons rfl rfl
  · rw [stepX86_dec64]
  apply StepsX86.cons rfl rfl
  · rw [stepX86_jnz]
  exact StepsX86.zero _

private theorem StepsX86_trans {prog : List (DecodedInstr X86Instr)} {m n : Nat}
    {s0 s1 s2 : X86State} (h1 : StepsX86 prog m s0 s1) (h2 : StepsX86 prog n s1 s2) :
    StepsX86 prog (m + n) s0 s2 := by
  induction h1 with
  | zero _ => simpa using h2
  | cons hh hf hs1 _ ih =>
    rw [Nat.succ_add]
    exact StepsX86.cons hh hf hs1 (ih h2)

private theorem gf256MulGfniLoop_steps (k : Nat) (hk : k + 1 < 0x10000000000000000)
    (r0 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 : Vec256)
    (cf o zf : Bool) (m : UInt64 → UInt8) :
    let mT2R : Vec256 := ⟨gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat⟩
    let mR2T : Vec256 := ⟨gfniRijndaelToTowerMat, gfniRijndaelToTowerMat, gfniRijndaelToTowerMat, gfniRijndaelToTowerMat⟩
    ∃ cf' o' zf',
      StepsX86 gf256MulGfniCoreProg (17 + 12 * k)
        ⟨40, ⟨r0, UInt64.ofNat (k + 1), r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
          ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, mT2R, mR2T⟩,
          cf, o, zf, true, false, m⟩
        ⟨114,
          ⟨r0, 0, r2 + UInt64.ofNat (32 * (k + 1)), r3, r4, r5,
            r6 + UInt64.ofNat (32 * (k + 1)), r7 + UInt64.ofNat (32 * (k + 1)),
            r8, r9, r10, r11, r12, r13, r14, r15⟩,
          ⟨Vec256.zero, Vec256.zero, Vec256.zero, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13,
            Vec256.zero, Vec256.zero⟩,
          cf', o', zf', true, false, gf256MulGfniIterMem (k + 1) m r7 r6 r2⟩ := by
  induction k generalizing r2 r6 r7 y0 y1 y2 cf o zf m with
  | zero =>
    dsimp only
    have h1 : UInt64.ofNat 1 - 1 = 0 := by decide
    have hIter := gf256MulGfniBody_one_iter r0 (UInt64.ofNat 1) r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
      y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 cf o zf m
    dsimp only at hIter
    rw [h1, u64_zero_beq_zero] at hIter
    rw [show jccPc (!true) 40 92 = 92 from rfl] at hIter
    have hEpi : StepsX86 gf256MulGfniCoreProg 5
        ⟨92, ⟨r0, 0, r2 + 32, r3, r4, r5, r6 + 32, r7 + 32, r8, r9, r10, r11, r12, r13, r14, r15⟩,
          ⟨gfniAffineVec256 (readMem256 m r6) ⟨gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat⟩ 0,
            gfniAffineVec256 (readMem256 m r2) ⟨gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat⟩ 0,
            gf256MulGfniVec (readMem256 m r6) (readMem256 m r2),
            y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13,
            ⟨gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat⟩,
            ⟨gfniRijndaelToTowerMat, gfniRijndaelToTowerMat, gfniRijndaelToTowerMat, gfniRijndaelToTowerMat⟩⟩,
          decide (r7.toNat + (32 : UInt64).toNat ≥ 0x10000000000000000),
          evalX86IncDecOf false true (UInt64.ofNat 1),
          true, true, false, gf256MulGfniStepMem m r7 r6 r2⟩
        ⟨114, ⟨r0, 0, r2 + 32, r3, r4, r5, r6 + 32, r7 + 32, r8, r9, r10, r11, r12, r13, r14, r15⟩,
          ⟨Vec256.zero, Vec256.zero, Vec256.zero, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13,
            Vec256.zero, Vec256.zero⟩,
          decide (r7.toNat + (32 : UInt64).toNat ≥ 0x10000000000000000),
          evalX86IncDecOf false true (UInt64.ofNat 1),
          true, true, false, gf256MulGfniStepMem m r7 r6 r2⟩ := by
      iterate 5
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
    have hIter := gf256MulGfniBody_one_iter r0 (UInt64.ofNat (j + 1 + 1)) r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
      y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 cf o zf m
    dsimp only at hIter
    rw [hDec, hNz] at hIter
    rw [show jccPc (!false) 40 92 = 40 from rfl] at hIter
    obtain ⟨cf', o', zf', hRest⟩ := ih (by omega) (r2 + 32) (r6 + 32) (r7 + 32)
      (gfniAffineVec256 (readMem256 m r6) ⟨gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat⟩ 0)
      (gfniAffineVec256 (readMem256 m r2) ⟨gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat⟩ 0)
      (gf256MulGfniVec (readMem256 m r6) (readMem256 m r2))
      (decide (r7.toNat + (32 : UInt64).toNat ≥ 0x10000000000000000))
      (evalX86IncDecOf false true (UInt64.ofNat (j + 1 + 1))) false (gf256MulGfniStepMem m r7 r6 r2)
    have hComb := StepsX86_trans hIter hRest
    have hStepEq : 12 + (17 + 12 * j) = 17 + 12 * (j + 1) := by omega
    have hAddPtr : ∀ p : UInt64, (p + 32) + UInt64.ofNat (32 * (j + 1)) = p + UInt64.ofNat (32 * (j + 1 + 1)) := by
      intro p
      apply UInt64.eq_of_toBitVec_eq
      simp only [UInt64.toBitVec_add, BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp [UInt64.toNat_toBitVec]
      omega
    rw [hStepEq, hAddPtr r2, hAddPtr r6, hAddPtr r7] at hComb
    exact ⟨cf', o', zf', hComb⟩

private theorem gf256MulGfniCore_reaches (k : Nat) (hk : k + 1 < 0x10000000000000000)
    (r0 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Vec256)
    (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    ∃ cf' o' zf',
      StepsX86 gf256MulGfniCoreProg (23 + 12 * k)
        ⟨0, ⟨r0, UInt64.ofNat (k + 1), r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
          ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
          cf, o, zf, dy, false, m⟩
        ⟨114,
          ⟨gfniRijndaelToTowerMat, 0, r2 + UInt64.ofNat (32 * (k + 1)), r3, r4, r5,
            r6 + UInt64.ofNat (32 * (k + 1)), r7 + UInt64.ofNat (32 * (k + 1)),
            r8, r9, r10, r11, r12, r13, r14, r15⟩,
          ⟨Vec256.zero, Vec256.zero, Vec256.zero, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13,
            Vec256.zero, Vec256.zero⟩,
          cf', o', zf', true, false, gf256MulGfniIterMem (k + 1) m r7 r6 r2⟩ := by
  have hPrologue : StepsX86 gf256MulGfniCoreProg 6
      ⟨0, ⟨r0, UInt64.ofNat (k + 1), r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
        cf, o, zf, dy, false, m⟩
      ⟨40, ⟨gfniRijndaelToTowerMat, UInt64.ofNat (k + 1), r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13,
          ⟨gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat⟩,
          ⟨gfniRijndaelToTowerMat, gfniRijndaelToTowerMat, gfniRijndaelToTowerMat, gfniRijndaelToTowerMat⟩⟩,
        cf, o, zf, true, false, m⟩ := by
    iterate 6
      apply StepsX86.cons rfl rfl
      · simp only [stepX86, maskGprWidth_true, b16get_0, b16set_0, Bool.or_true]
        rfl
    exact StepsX86.zero _
  obtain ⟨cf', o', zf', hLoop⟩ := gf256MulGfniLoop_steps k hk gfniRijndaelToTowerMat
    r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
    y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 cf o zf m
  have hComb := StepsX86_trans hPrologue hLoop
  have hEq : 6 + (17 + 12 * k) = 23 + 12 * k := by omega
  rw [hEq] at hComb
  exact ⟨cf', o', zf', hComb⟩

def progPreservesNonRet (prog1 prog2 : List (DecodedInstr X86Instr)) : Bool :=
  prog1.all fun d => d.instr == .ret || findInstrAtPc d.offset prog2 == some d

private theorem findInstrAtPc_mem_and_offset {I : Type} {pc : Nat} {prog : List (DecodedInstr I)}
    {d : DecodedInstr I} (h : findInstrAtPc pc prog = some d) :
    d ∈ prog ∧ d.offset = pc := by
  induction prog with
  | nil => simp [findInstrAtPc] at h
  | cons hd tl ih =>
    unfold findInstrAtPc at h
    by_cases hpc : hd.offset == pc
    · rw [ite_eq_left hpc] at h
      cases h
      exact ⟨List.Mem.head _, beq_iff_eq.mp hpc⟩
    · rw [ite_eq_right hpc] at h
      obtain ⟨hm, ho⟩ := ih h
      exact ⟨List.Mem.tail _ hm, ho⟩

theorem ExecReachesX86_transfer_nonret {prog1 prog2 : List (DecodedInstr X86Instr)} {k : Nat}
    {s sRet : X86State}
    (hPres : progPreservesNonRet prog1 prog2 = true)
    (hReach : ExecReachesX86 prog1 k s sRet)
    (hhRet : sRet.halted = false) :
    ExecReachesX86 prog2 k s sRet := by
  induction k generalizing s with
  | zero =>
    have h0 := (hReach 0).1
    simp only [runX86] at h0
    subst h0
    exact ExecReachesX86_zero prog2 _
  | succ k ih =>
    have hh : s.halted = false := by
      cases hs : s.halted
      · rfl
      · have h0 := (hReach 0).1
        rw [Nat.add_zero, runX86_halted_fst prog1 (k + 1) s hs] at h0
        change s = sRet at h0
        rw [← h0, hs] at hhRet
        cases hhRet
    cases hf1 : findInstrAtPc s.pc prog1 with
    | none =>
      have h0 := (hReach 0).1
      simp only [runX86, hh, hf1] at h0
      rw [← h0] at hhRet
      cases hhRet
    | some d =>
      have hNotRet : d.instr ≠ .ret := by
        intro hIr
        rcases d with ⟨off, len, instr⟩
        dsimp only at hIr; subst hIr
        have h0 := (hReach 0).1
        simp only [runX86, hh, hf1, stepX86] at h0
        rw [runX86_halted_fst prog1 k _ rfl] at h0
        rw [← h0] at hhRet
        cases hhRet
      obtain ⟨hdMem, hdOff⟩ := findInstrAtPc_mem_and_offset hf1
      have hAll := List.all_eq_true.mp hPres d hdMem
      have hBeqFalse : (d.instr == .ret) = false := by
        cases h : d.instr == .ret
        · rfl
        · exact absurd (beq_iff_eq.mp h) hNotRet
      rw [hBeqFalse, Bool.false_or] at hAll
      have hf2 : findInstrAtPc s.pc prog2 = some d := by
        rw [← hdOff]; exact beq_iff_eq.mp hAll
      have hRest : ExecReachesX86 prog1 k (stepX86 d s).1 sRet := by
        intro extra
        have ⟨he, hl⟩ := hReach extra
        rw [Nat.add_right_comm k 1 extra] at he hl
        simp only [runX86, hh, hf1] at he hl
        exact ⟨he, by simp at hl; omega⟩
      exact ExecReachesX86_cons hh hf2 rfl (ih hRest)

private theorem gf256MulGfni_reaches_full (k : Nat) (hk : k + 1 < 0x10000000000000000)
    (r0 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Vec256)
    (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    ∃ cf' o' zf',
      ExecReachesX86 gf256MulGfniProg (24 + 12 * k)
        ⟨0, ⟨r0, UInt64.ofNat (k + 1), r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
          ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
          cf, o, zf, dy, false, m⟩
        ⟨117,
          ⟨gfniRijndaelToTowerMat, 0, r2 + UInt64.ofNat (32 * (k + 1)), r3, r4, r5,
            r6 + UInt64.ofNat (32 * (k + 1)), r7 + UInt64.ofNat (32 * (k + 1)),
            r8, r9, r10, r11, r12, r13, r14, r15⟩,
          ⟨Vec256.zero, Vec256.zero, Vec256.zero,
            ⟨y3.w0, y3.w1, 0, 0⟩, ⟨y4.w0, y4.w1, 0, 0⟩, ⟨y5.w0, y5.w1, 0, 0⟩,
            ⟨y6.w0, y6.w1, 0, 0⟩, ⟨y7.w0, y7.w1, 0, 0⟩, ⟨y8.w0, y8.w1, 0, 0⟩,
            ⟨y9.w0, y9.w1, 0, 0⟩, ⟨y10.w0, y10.w1, 0, 0⟩, ⟨y11.w0, y11.w1, 0, 0⟩,
            ⟨y12.w0, y12.w1, 0, 0⟩, ⟨y13.w0, y13.w1, 0, 0⟩,
            Vec256.zero, Vec256.zero⟩,
          cf', o', zf', false, false, gf256MulGfniIterMem (k + 1) m r7 r6 r2⟩ := by
  obtain ⟨cf', o', zf', hCore⟩ := gf256MulGfniCore_reaches k hk
    r0 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
    y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 cf o zf dy m
  have hPres : progPreservesNonRet gf256MulGfniCoreProg gf256MulGfniProg = true := by decide +kernel
  have hTrans := ExecReachesX86_transfer_nonret hPres hCore.toExecReaches rfl
  have hVzu : ExecReachesX86 gf256MulGfniProg 1
      ⟨114,
        ⟨gfniRijndaelToTowerMat, 0, r2 + UInt64.ofNat (32 * (k + 1)), r3, r4, r5,
          r6 + UInt64.ofNat (32 * (k + 1)), r7 + UInt64.ofNat (32 * (k + 1)),
          r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨Vec256.zero, Vec256.zero, Vec256.zero, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13,
          Vec256.zero, Vec256.zero⟩,
        cf', o', zf', true, false, gf256MulGfniIterMem (k + 1) m r7 r6 r2⟩
      ⟨117,
        ⟨gfniRijndaelToTowerMat, 0, r2 + UInt64.ofNat (32 * (k + 1)), r3, r4, r5,
          r6 + UInt64.ofNat (32 * (k + 1)), r7 + UInt64.ofNat (32 * (k + 1)),
          r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨Vec256.zero, Vec256.zero, Vec256.zero,
          ⟨y3.w0, y3.w1, 0, 0⟩, ⟨y4.w0, y4.w1, 0, 0⟩, ⟨y5.w0, y5.w1, 0, 0⟩,
          ⟨y6.w0, y6.w1, 0, 0⟩, ⟨y7.w0, y7.w1, 0, 0⟩, ⟨y8.w0, y8.w1, 0, 0⟩,
          ⟨y9.w0, y9.w1, 0, 0⟩, ⟨y10.w0, y10.w1, 0, 0⟩, ⟨y11.w0, y11.w1, 0, 0⟩,
          ⟨y12.w0, y12.w1, 0, 0⟩, ⟨y13.w0, y13.w1, 0, 0⟩,
          Vec256.zero, Vec256.zero⟩,
        cf', o', zf', false, false, gf256MulGfniIterMem (k + 1) m r7 r6 r2⟩ :=
    ExecReachesX86_step rfl rfl rfl
  have hFull := ExecReachesX86_trans hTrans hVzu
  have hStepEq : (23 + 12 * k) + 1 = 24 + 12 * k := by omega
  rw [hStepEq] at hFull
  exact ⟨cf', o', zf', hFull⟩

/-- End-to-end single-block (`rcx = 1#64`, 32 lanes) byte-decoded functional equivalence and 3-way
    CT-NI certificate for `qsag_asm_gf256_shamir_mul_gfni` (`N = 25`, `retPc = 117`), refining
    every output byte against `BinaryTower.towerMul 3` via `Simulates 3` with zero aliasing or
    wraparound preconditions. -/
theorem rlib_gf256_shamir_mul_gfni_functional_and_ct :
    ∃ slice m,
      extractRlibFuncBytes x86RlibArchiveBytes "qsag_asm_gf256_shamir_mul_gfni" = some slice ∧
      m ∈ parseArArchive x86RlibArchiveBytes ∧
      ArPayloadOk x86RlibArchiveBytes m ∧
      checkElfFuncThreeWayNI m.payload "qsag_asm_gf256_shamir_mul_gfni"
        (mkContract "qsag_asm_gf256_shamir_mul_gfni" [4, 7, 6, 2, 1]) = true ∧
      ElfSliceThreeWayNISafe slice (mkContract "qsag_asm_gf256_shamir_mul_gfni" [4, 7, 6, 2, 1]) ∧
      decodeX86Slice slice.code = some gf256MulGfniProg ∧
      ∀ (st : X86BvState), st.pc = 0 → st.halted = false → st.gpr.get 1 = 1#64 →
        (∃ st24 tr24, execDecodedX86 slice.code 24 st = some (st24, tr24) ∧ st24.halted = false) ∧
        ∀ extra : Nat, ∃ st' trace,
          execDecodedX86 slice.code (25 + extra) st = some (st', trace) ∧
          st'.halted = true ∧ st'.pc = 117 ∧ trace.length = 25 ∧
          st'.ymmDirty = false ∧
          st'.gpr.get 1 = 0#64 ∧
          st'.gpr.get 7 = st.gpr.get 7 + 32#64 ∧
          st'.gpr.get 6 = st.gpr.get 6 + 32#64 ∧
          st'.gpr.get 2 = st.gpr.get 2 + 32#64 ∧
          st'.ymm.get 0 = Vec256.zero ∧ st'.ymm.get 1 = Vec256.zero ∧
          st'.ymm.get 2 = Vec256.zero ∧ st'.ymm.get 14 = Vec256.zero ∧
          st'.ymm.get 15 = Vec256.zero ∧
          X86CalleeSavedPreserved st st' ∧
          (∀ k : Nat, k < 32 →
            st'.mem (st.gpr.get 7 + BitVec.ofNat 64 k) =
              gfniTowerMulByte (st.mem (st.gpr.get 6 + BitVec.ofNat 64 k))
                               (st.mem (st.gpr.get 2 + BitVec.ofNat 64 k)) ∧
            Simulates 3
              (towerMul 3 (unpackTower 3 (st.mem (st.gpr.get 6 + BitVec.ofNat 64 k)).toBitVec)
                          (unpackTower 3 (st.mem (st.gpr.get 2 + BitVec.ofNat 64 k)).toBitVec))
              (st'.mem (st.gpr.get 7 + BitVec.ofNat 64 k)).toBitVec) ∧
          (∀ a : BitVec 64, (∀ k : Nat, k < 32 → a ≠ st.gpr.get 7 + BitVec.ofNat 64 k) →
            st'.mem a = st.mem a) := by
  cases hFind : x86ExtractedSlices.find? (fun s => s.name == "qsag_asm_gf256_shamir_mul_gfni") with
  | none => exfalso; revert hFind; decide +kernel
  | some slice =>
    have hExt : extractRlibFuncBytes x86RlibArchiveBytes "qsag_asm_gf256_shamir_mul_gfni" = some slice := by
      rw [extractRlibFuncBytes_x86_eq, hFind]
    have hNI : checkElfSliceThreeWayNI slice (mkContract "qsag_asm_gf256_shamir_mul_gfni" [4, 7, 6, 2, 1]) = true := by
      have hCheck : ((x86ExtractedSlices.find? (fun s => s.name == "qsag_asm_gf256_shamir_mul_gfni")).map
          (fun sl => checkElfSliceThreeWayNI sl (mkContract "qsag_asm_gf256_shamir_mul_gfni" [4, 7, 6, 2, 1]))) =
          some true := by decide +kernel
      rw [hFind] at hCheck
      exact Option.some.inj hCheck
    have hDec : decodeX86Slice slice.code = some gf256MulGfniProg := by
      have hD : (x86ExtractedSlices.find? (fun s => s.name == "qsag_asm_gf256_shamir_mul_gfni")).bind
          (fun sl => decodeX86Slice sl.code) = some gf256MulGfniProg := by decide +kernel
      rw [hFind] at hD
      exact hD
    obtain ⟨m, hm, hPay, _, hMemNI, _, hSafe⟩ :=
      extractRlibFuncBytes_member_ni_sound x86_rlib_distinct_names hExt hNI
    refine ⟨slice, m, hExt, hm, hPay, hMemNI, hSafe, hDec, ?_⟩
    intro st hpc hh hrcx
    rcases st with ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
      ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
      cf, o, zf, dy, hlt, mem⟩
    dsimp only at hpc hh; subst hpc hh
    have hr1 : r1 = 1#64 := hrcx; subst hr1
    let st0 : X86BvState :=
      ⟨0, ⟨r0, 1#64, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
       ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
       cf, o, zf, dy, false, mem⟩
    obtain ⟨cf', o', zf', hR⟩ := gf256MulGfni_reaches_full 0 (by decide)
      (UInt64.ofBitVec r0) (UInt64.ofBitVec r2) (UInt64.ofBitVec r3) (UInt64.ofBitVec r4)
      (UInt64.ofBitVec r5) (UInt64.ofBitVec r6) (UInt64.ofBitVec r7) (UInt64.ofBitVec r8)
      (UInt64.ofBitVec r9) (UInt64.ofBitVec r10) (UInt64.ofBitVec r11) (UInt64.ofBitVec r12)
      (UInt64.ofBitVec r13) (UInt64.ofBitVec r14) (UInt64.ofBitVec r15)
      y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 cf o zf dy (fun a => mem a.toBitVec)
    obtain ⟨hPre, hPost⟩ := execDecodedX86_ret_of_reaches st0 hDec rfl hR rfl rfl
    refine ⟨hPre, fun extra => ?_⟩
    obtain ⟨tr, hExec, hL⟩ := hPost extra
    have hAdd32 : ∀ x : BitVec 64, (UInt64.ofBitVec x + UInt64.ofNat 32).toBitVec = x + 32#64 := by
      intro x; simp [UInt64.toBitVec_add]
    have hOfNatBv : ∀ (x : BitVec 64) (k : Nat), k < 32 →
        (UInt64.ofBitVec x + UInt64.ofNat k) = UInt64.ofBitVec (x + BitVec.ofNat 64 k) := by
      intro x k _
      apply UInt64.eq_of_toBitVec_eq
      simp only [UInt64.toBitVec_add]
      congr 1
    refine ⟨_, tr, hExec, rfl, rfl, hL, rfl, rfl, hAdd32 r7, hAdd32 r6, hAdd32 r2,
      rfl, rfl, rfl, rfl, rfl, x86_callee_saved_of_roundtrip, ?_, ?_⟩
    · intro k hk
      dsimp only [X86BvState.ofX86State, gf256MulGfniIterMem]
      simp only [b16get_7, b16get_6, b16get_2]
      rw [← hOfNatBv r7 k hk, gf256MulGfniStepMem_at _ _ _ _ k hk]
      have hA : ((UInt64.ofBitVec r6 + UInt64.ofNat k).toBitVec) = r6 + BitVec.ofNat 64 k := by
        rw [hOfNatBv r6 k hk, u64_roundtrip]
      have hB : ((UInt64.ofBitVec r2 + UInt64.ofNat k).toBitVec) = r2 + BitVec.ofNat 64 k := by
        rw [hOfNatBv r2 k hk, u64_roundtrip]
      rw [hA, hB]
      exact ⟨rfl, gfniTowerMulByte_simulates_binaryTower _ _⟩
    · intro a ha
      dsimp only [X86BvState.ofX86State, gf256MulGfniIterMem]
      rw [gf256MulGfniStepMem_outside _ _ _ _ (UInt64.ofBitVec a) (fun k hk heq => by
        rw [hOfNatBv r7 k hk] at heq
        have hb := congrArg UInt64.toBitVec heq
        rw [u64_roundtrip, u64_roundtrip] at hb
        exact ha k hk hb), u64_roundtrip]

/-- Multi-block inductive backward-`JNZ` loop functional equivalence for
    `qsag_asm_gf256_shamir_mul_gfni`: for every block count `k + 1` (`32 * (k + 1) ≤ 2^64`),
    execution halts in exact step count `N = 25 + 12 * k` with every byte `idx < 32 * (k + 1)`
    simulating `BinaryTower.towerMul 3` whenever output `[dst, dst + 32*(k+1))` is disjoint from
    inputs. -/
theorem rlib_gf256_shamir_mul_gfni_loop_functional :
    ∃ slice,
      extractRlibFuncBytes x86RlibArchiveBytes "qsag_asm_gf256_shamir_mul_gfni" = some slice ∧
      ElfSliceThreeWayNISafe slice (mkContract "qsag_asm_gf256_shamir_mul_gfni" [4, 7, 6, 2, 1]) ∧
      ∀ (k : Nat), 32 * (k + 1) ≤ 0x10000000000000000 →
      ∀ (st : X86BvState), st.pc = 0 → st.halted = false →
        st.gpr.get 1 = BitVec.ofNat 64 (k + 1) →
        ∀ extra : Nat, ∃ st' trace,
          execDecodedX86 slice.code ((25 + 12 * k) + extra) st = some (st', trace) ∧
          st'.halted = true ∧ st'.pc = 117 ∧ trace.length = 25 + 12 * k ∧
          st'.ymmDirty = false ∧
          st'.gpr.get 1 = 0#64 ∧
          st'.gpr.get 7 = st.gpr.get 7 + BitVec.ofNat 64 (32 * (k + 1)) ∧
          st'.gpr.get 6 = st.gpr.get 6 + BitVec.ofNat 64 (32 * (k + 1)) ∧
          st'.gpr.get 2 = st.gpr.get 2 + BitVec.ofNat 64 (32 * (k + 1)) ∧
          X86CalleeSavedPreserved st st' ∧
          ((∀ i j : Nat, i < 32 * (k + 1) → j < 32 * (k + 1) →
              st.gpr.get 7 + BitVec.ofNat 64 i ≠ st.gpr.get 6 + BitVec.ofNat 64 j ∧
              st.gpr.get 7 + BitVec.ofNat 64 i ≠ st.gpr.get 2 + BitVec.ofNat 64 j) →
            (∀ idx : Nat, idx < 32 * (k + 1) →
              Simulates 3
                (towerMul 3 (unpackTower 3 (st.mem (st.gpr.get 6 + BitVec.ofNat 64 idx)).toBitVec)
                            (unpackTower 3 (st.mem (st.gpr.get 2 + BitVec.ofNat 64 idx)).toBitVec))
                (st'.mem (st.gpr.get 7 + BitVec.ofNat 64 idx)).toBitVec)) ∧
          (∀ a : BitVec 64, (∀ idx : Nat, idx < 32 * (k + 1) → a ≠ st.gpr.get 7 + BitVec.ofNat 64 idx) →
            st'.mem a = st.mem a) := by
  obtain ⟨slice, _, hExt, _, _, _, hSafe, hDec, _⟩ := rlib_gf256_shamir_mul_gfni_functional_and_ct
  refine ⟨slice, hExt, hSafe, fun k hk st hpc hh hrcx extra => ?_⟩
  rcases st with ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
    ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
    cf, o, zf, dy, hlt, mem⟩
  dsimp only at hpc hh; subst hpc hh
  have hr1 : r1 = BitVec.ofNat 64 (k + 1) := hrcx; subst hr1
  have hr1U : UInt64.ofBitVec (BitVec.ofNat 64 (k + 1)) = UInt64.ofNat (k + 1) := by
    apply UInt64.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq
    simp [UInt64.toNat_toBitVec, Nat.mod_eq_of_lt (show k + 1 < 0x10000000000000000 by omega)]
  let st0 : X86BvState :=
    ⟨0, ⟨r0, BitVec.ofNat 64 (k + 1), r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
     ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
     cf, o, zf, dy, false, mem⟩
  obtain ⟨cf', o', zf', hR⟩ := gf256MulGfni_reaches_full k (by omega)
    (UInt64.ofBitVec r0) (UInt64.ofBitVec r2) (UInt64.ofBitVec r3) (UInt64.ofBitVec r4)
    (UInt64.ofBitVec r5) (UInt64.ofBitVec r6) (UInt64.ofBitVec r7) (UInt64.ofBitVec r8)
    (UInt64.ofBitVec r9) (UInt64.ofBitVec r10) (UInt64.ofBitVec r11) (UInt64.ofBitVec r12)
    (UInt64.ofBitVec r13) (UInt64.ofBitVec r14) (UInt64.ofBitVec r15)
    y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 cf o zf dy (fun a => mem a.toBitVec)
  have hSt0 : st0.toX86State =
      ⟨0, ⟨UInt64.ofBitVec r0, UInt64.ofNat (k + 1), UInt64.ofBitVec r2, UInt64.ofBitVec r3,
           UInt64.ofBitVec r4, UInt64.ofBitVec r5, UInt64.ofBitVec r6, UInt64.ofBitVec r7,
           UInt64.ofBitVec r8, UInt64.ofBitVec r9, UInt64.ofBitVec r10, UInt64.ofBitVec r11,
           UInt64.ofBitVec r12, UInt64.ofBitVec r13, UInt64.ofBitVec r14, UInt64.ofBitVec r15⟩,
       ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
       cf, o, zf, dy, false, fun a => mem a.toBitVec⟩ := by
    simp [st0, X86BvState.toX86State, bank16ToU64, hr1U]
  obtain ⟨_, hPost⟩ := execDecodedX86_ret_of_reaches st0 hDec hSt0 hR rfl rfl
  have hStepN : (24 + 12 * k) + 1 = 25 + 12 * k := by omega
  obtain ⟨tr, hExec, hL⟩ := hPost extra
  rw [hStepN] at hExec hL
  have hOfNatBv : ∀ (x : BitVec 64) (mNat : Nat), mNat ≤ 0x10000000000000000 →
      (mNat < 0x10000000000000000 ∨ mNat = 0x10000000000000000) →
      (UInt64.ofBitVec x + UInt64.ofNat mNat).toBitVec = x + BitVec.ofNat 64 mNat := by
    intro x mNat _ _
    simp only [UInt64.toBitVec_add]
    congr 1
  have hOfNatU : ∀ (x : BitVec 64) (idx : Nat), idx < 32 * (k + 1) →
      UInt64.ofBitVec (x + BitVec.ofNat 64 idx) = UInt64.ofBitVec x + UInt64.ofNat idx := by
    intro x idx hidx
    apply UInt64.eq_of_toBitVec_eq
    rw [u64_roundtrip, hOfNatBv x idx (by omega) (Or.inl (by omega))]
  refine ⟨_, tr, hExec, rfl, rfl, hL, rfl, rfl,
    hOfNatBv r7 (32 * (k + 1)) hk (by omega),
    hOfNatBv r6 (32 * (k + 1)) hk (by omega),
    hOfNatBv r2 (32 * (k + 1)) hk (by omega),
    x86_callee_saved_of_roundtrip, ?_, ?_⟩
  · intro hDisj idx hidx
    dsimp only [X86BvState.ofX86State]
    simp only [b16get_7, b16get_6, b16get_2]
    rw [hOfNatU r7 idx hidx]
    rw [gf256MulGfniIterMem_at (k + 1) _ _ _ _ hk
      (fun i j hi hj heq => by
        have hb := congrArg UInt64.toBitVec heq
        rw [hOfNatBv r7 i (by omega) (Or.inl (by omega)),
            hOfNatBv r6 j (by omega) (Or.inl (by omega))] at hb
        exact (hDisj i j hi hj).1 hb)
      (fun i j hi hj heq => by
        have hb := congrArg UInt64.toBitVec heq
        rw [hOfNatBv r7 i (by omega) (Or.inl (by omega)),
            hOfNatBv r2 j (by omega) (Or.inl (by omega))] at hb
        exact (hDisj i j hi hj).2 hb)
      idx hidx]
    rw [hOfNatBv r6 idx (by omega) (Or.inl (by omega)),
        hOfNatBv r2 idx (by omega) (Or.inl (by omega))]
    exact gfniTowerMulByte_simulates_binaryTower _ _
  · intro a ha
    dsimp only [X86BvState.ofX86State]
    rw [gf256MulGfniIterMem_outside (k + 1) _ _ _ _ (UInt64.ofBitVec a) hk
      (fun idx hidx heq => by
        have hb := congrArg UInt64.toBitVec heq
        rw [u64_roundtrip, hOfNatBv r7 idx (by omega) (Or.inl (by omega))] at hb
        exact ha idx hidx hb), u64_roundtrip]

/-! ### §5.4 `qsag_asm_keccak_sha3_neon` (`AArch64` SHA3 NEON `EOR` + `BCAX` 2-Share Keccak $\chi$ Rows 0 & 1) -/

def keccakSha3NeonProg : List (DecodedInstr Arm64Instr) := [
  ⟨0, 4, .ldrQ 0 1 0⟩, ⟨4, 4, .ldrQ 1 1 16⟩, ⟨8, 4, .ldrQ 2 1 32⟩,
  ⟨12, 4, .ldrQ 3 1 48⟩, ⟨16, 4, .ldrQ 4 1 64⟩,
  ⟨20, 4, .ldrQ 5 2 0⟩, ⟨24, 4, .ldrQ 6 2 16⟩, ⟨28, 4, .ldrQ 7 2 32⟩,
  ⟨32, 4, .veor16b 0 0 5⟩, ⟨36, 4, .veor16b 1 1 6⟩, ⟨40, 4, .veor16b 2 2 7⟩,
  ⟨44, 4, .ldrQ 5 2 48⟩, ⟨48, 4, .ldrQ 6 2 64⟩,
  ⟨52, 4, .veor16b 3 3 5⟩, ⟨56, 4, .veor16b 4 4 6⟩,
  ⟨60, 4, .vbcax16b 16 0 2 1⟩, ⟨64, 4, .vbcax16b 17 1 3 2⟩,
  ⟨68, 4, .vbcax16b 18 2 4 3⟩, ⟨72, 4, .vbcax16b 19 3 0 4⟩, ⟨76, 4, .vbcax16b 20 4 1 0⟩,
  ⟨80, 4, .strQ 16 0 0⟩, ⟨84, 4, .strQ 17 0 16⟩, ⟨88, 4, .strQ 18 0 32⟩,
  ⟨92, 4, .strQ 19 0 48⟩, ⟨96, 4, .strQ 20 0 64⟩,
  ⟨100, 4, .veor16b 0 0 0⟩, ⟨104, 4, .veor16b 1 1 1⟩, ⟨108, 4, .veor16b 2 2 2⟩,
  ⟨112, 4, .veor16b 3 3 3⟩, ⟨116, 4, .veor16b 4 4 4⟩, ⟨120, 4, .veor16b 5 5 5⟩,
  ⟨124, 4, .veor16b 6 6 6⟩, ⟨128, 4, .veor16b 7 7 7⟩,
  ⟨132, 4, .veor16b 16 16 16⟩, ⟨136, 4, .veor16b 17 17 17⟩, ⟨140, 4, .veor16b 18 18 18⟩,
  ⟨144, 4, .veor16b 19 19 19⟩, ⟨148, 4, .veor16b 20 20 20⟩,
  ⟨152, 4, .ret⟩
]

def keccakNeonOutMem (mem : UInt64 → UInt8) (outPtr s0Ptr s1Ptr : UInt64) : UInt64 → UInt8 :=
  let u0 := readMem128 mem s0Ptr
  let u1 := readMem128 mem (s0Ptr + 16)
  let u2 := readMem128 mem (s0Ptr + 32)
  let u3 := readMem128 mem (s0Ptr + 48)
  let u4 := readMem128 mem (s0Ptr + 64)
  let w0 := readMem128 mem s1Ptr
  let w1 := readMem128 mem (s1Ptr + 16)
  let w2 := readMem128 mem (s1Ptr + 32)
  let w3 := readMem128 mem (s1Ptr + 48)
  let w4 := readMem128 mem (s1Ptr + 64)
  let a0 : Vec128 := ⟨u0.w0 ^^^ w0.w0, u0.w1 ^^^ w0.w1⟩
  let a1 : Vec128 := ⟨u1.w0 ^^^ w1.w0, u1.w1 ^^^ w1.w1⟩
  let a2 : Vec128 := ⟨u2.w0 ^^^ w2.w0, u2.w1 ^^^ w2.w1⟩
  let a3 : Vec128 := ⟨u3.w0 ^^^ w3.w0, u3.w1 ^^^ w3.w1⟩
  let a4 : Vec128 := ⟨u4.w0 ^^^ w4.w0, u4.w1 ^^^ w4.w1⟩
  let c0 : Vec128 := ⟨a0.w0 ^^^ (a2.w0 &&& (~~~a1.w0)), a0.w1 ^^^ (a2.w1 &&& (~~~a1.w1))⟩
  let c1 : Vec128 := ⟨a1.w0 ^^^ (a3.w0 &&& (~~~a2.w0)), a1.w1 ^^^ (a3.w1 &&& (~~~a2.w1))⟩
  let c2 : Vec128 := ⟨a2.w0 ^^^ (a4.w0 &&& (~~~a3.w0)), a2.w1 ^^^ (a4.w1 &&& (~~~a3.w1))⟩
  let c3 : Vec128 := ⟨a3.w0 ^^^ (a0.w0 &&& (~~~a4.w0)), a3.w1 ^^^ (a0.w1 &&& (~~~a4.w1))⟩
  let c4 : Vec128 := ⟨a4.w0 ^^^ (a1.w0 &&& (~~~a0.w0)), a4.w1 ^^^ (a1.w1 &&& (~~~a0.w1))⟩
  let m0 := writeMem128 mem outPtr c0
  let m1 := writeMem128 m0 (outPtr + 16) c1
  let m2 := writeMem128 m1 (outPtr + 32) c2
  let m3 := writeMem128 m2 (outPtr + 48) c3
  writeMem128 m3 (outPtr + 64) c4

private theorem keccakSha3Neon_reaches
    (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64) (hi : Bank16 UInt64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : Vec128)
    (v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 : Vec128)
    (cf zf dit : Bool) (m : UInt64 → UInt8) :
    ExecReachesArm64 keccakSha3NeonProg 38
      ⟨0, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        ⟨⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15⟩,
         ⟨v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31⟩⟩,
        cf, zf, dit, false, m⟩
      ⟨152, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        ⟨⟨Vec128.zero, Vec128.zero, Vec128.zero, Vec128.zero,
          Vec128.zero, Vec128.zero, Vec128.zero, Vec128.zero,
          v8, v9, v10, v11, v12, v13, v14, v15⟩,
         ⟨Vec128.zero, Vec128.zero, Vec128.zero, Vec128.zero, Vec128.zero,
          v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31⟩⟩,
        cf, zf, dit, false, keccakNeonOutMem m r0 r1 r2⟩ := by
  apply StepsArm64.toExecReaches
  iterate 38
    apply StepsArm64.cons rfl rfl
    · simp only [stepArm64, getArmGpr, u64_add_zero, elf_u64_xor_self]
      rfl
  exact StepsArm64.zero _

private theorem u64_bcax_eq_chi (x z y : UInt64) :
    x ^^^ (z &&& (~~~y)) = x ^^^ ((~~~y) &&& z) := by
  apply UInt64.eq_of_toBitVec_eq; simp [BitVec.and_comm]

theorem keccakNeonOutMem_lanes (mem : UInt64 → UInt8) (outPtr s0Ptr s1Ptr : UInt64)
    (K : KState)
    (ha0 : K.a0 = readMem64 mem s0Ptr ^^^ readMem64 mem s1Ptr)
    (ha1 : K.a1 = readMem64 mem (s0Ptr + 16) ^^^ readMem64 mem (s1Ptr + 16))
    (ha2 : K.a2 = readMem64 mem (s0Ptr + 32) ^^^ readMem64 mem (s1Ptr + 32))
    (ha3 : K.a3 = readMem64 mem (s0Ptr + 48) ^^^ readMem64 mem (s1Ptr + 48))
    (ha4 : K.a4 = readMem64 mem (s0Ptr + 64) ^^^ readMem64 mem (s1Ptr + 64))
    (ha5 : K.a5 = readMem64 mem (s0Ptr + 8) ^^^ readMem64 mem (s1Ptr + 8))
    (ha6 : K.a6 = readMem64 mem (s0Ptr + 24) ^^^ readMem64 mem (s1Ptr + 24))
    (ha7 : K.a7 = readMem64 mem (s0Ptr + 40) ^^^ readMem64 mem (s1Ptr + 40))
    (ha8 : K.a8 = readMem64 mem (s0Ptr + 56) ^^^ readMem64 mem (s1Ptr + 56))
    (ha9 : K.a9 = readMem64 mem (s0Ptr + 72) ^^^ readMem64 mem (s1Ptr + 72)) :
    let m' := keccakNeonOutMem mem outPtr s0Ptr s1Ptr
    readMem64 m' outPtr = (chiS K).a0 ∧
    readMem64 m' (outPtr + 16) = (chiS K).a1 ∧
    readMem64 m' (outPtr + 32) = (chiS K).a2 ∧
    readMem64 m' (outPtr + 48) = (chiS K).a3 ∧
    readMem64 m' (outPtr + 64) = (chiS K).a4 ∧
    readMem64 m' (outPtr + 8) = (chiS K).a5 ∧
    readMem64 m' (outPtr + 24) = (chiS K).a6 ∧
    readMem64 m' (outPtr + 40) = (chiS K).a7 ∧
    readMem64 m' (outPtr + 56) = (chiS K).a8 ∧
    readMem64 m' (outPtr + 72) = (chiS K).a9 := by
  dsimp only
  have hDisj : ∀ (off1 off2 : Nat) (a1 a2 : UInt64) (_h1 : off1 ≤ 72) (_h2 : off2 ≤ 64)
      (_hd : off1 + 8 ≤ off2 ∨ off2 + 16 ≤ off1)
      (_e1 : a1 = outPtr + UInt64.ofNat off1) (_e2 : a2 = outPtr + UInt64.ofNat off2)
      (m : UInt64 → UInt8) (v : Vec128),
      readMem64 (writeMem128 m a2 v) a1 = readMem64 m a1 := by
    intro off1 off2 a1 a2 _h1 _h2 _hd e1 e2 m v
    subst e1 e2
    apply readMem64_writeMem128_disjoint
    intro i k _hi _hk heq
    rw [u64_add_ofNat_assoc outPtr off1 i (by omega),
        u64_add_ofNat_assoc outPtr off2 k (by omega)] at heq
    have := u64_add_ofNat_inj (by omega) (by omega) heq
    omega
  have hp0 : outPtr = outPtr + UInt64.ofNat 0 := by apply UInt64.eq_of_toBitVec_eq; simp
  have h16_8 : (outPtr + 16) + 8 = outPtr + 24 := by
    change (outPtr + UInt64.ofNat 16) + UInt64.ofNat 8 = outPtr + UInt64.ofNat 24
    exact u64_add_ofNat_assoc outPtr 16 8 (by decide)
  have h32_8 : (outPtr + 32) + 8 = outPtr + 40 := by
    change (outPtr + UInt64.ofNat 32) + UInt64.ofNat 8 = outPtr + UInt64.ofNat 40
    exact u64_add_ofNat_assoc outPtr 32 8 (by decide)
  have h48_8 : (outPtr + 48) + 8 = outPtr + 56 := by
    change (outPtr + UInt64.ofNat 48) + UInt64.ofNat 8 = outPtr + UInt64.ofNat 56
    exact u64_add_ofNat_assoc outPtr 48 8 (by decide)
  have h64_8 : (outPtr + 64) + 8 = outPtr + 72 := by
    change (outPtr + UInt64.ofNat 64) + UInt64.ofNat 8 = outPtr + UInt64.ofNat 72
    exact u64_add_ofNat_assoc outPtr 64 8 (by decide)
  have hs16_8 : ∀ p : UInt64, (p + 16) + 8 = p + 24 := fun p => by
    change (p + UInt64.ofNat 16) + UInt64.ofNat 8 = p + UInt64.ofNat 24
    exact u64_add_ofNat_assoc p 16 8 (by decide)
  have hs32_8 : ∀ p : UInt64, (p + 32) + 8 = p + 40 := fun p => by
    change (p + UInt64.ofNat 32) + UInt64.ofNat 8 = p + UInt64.ofNat 40
    exact u64_add_ofNat_assoc p 32 8 (by decide)
  have hs48_8 : ∀ p : UInt64, (p + 48) + 8 = p + 56 := fun p => by
    change (p + UInt64.ofNat 48) + UInt64.ofNat 8 = p + UInt64.ofNat 56
    exact u64_add_ofNat_assoc p 48 8 (by decide)
  have hs64_8 : ∀ p : UInt64, (p + 64) + 8 = p + 72 := fun p => by
    change (p + UInt64.ofNat 64) + UInt64.ofNat 8 = p + UInt64.ofNat 72
    exact u64_add_ofNat_assoc p 64 8 (by decide)
  unfold keccakNeonOutMem chiS readMem128
  dsimp only
  simp only [hs16_8, hs32_8, hs48_8, hs64_8,
    ← ha0, ← ha1, ← ha2, ← ha3, ← ha4, ← ha5, ← ha6, ← ha7, ← ha8, ← ha9,
    u64_bcax_eq_chi]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hDisj 0 64 outPtr (outPtr + 64) (by decide) (by decide) (by omega) hp0 rfl,
        hDisj 0 48 outPtr (outPtr + 48) (by decide) (by decide) (by omega) hp0 rfl,
        hDisj 0 32 outPtr (outPtr + 32) (by decide) (by decide) (by omega) hp0 rfl,
        hDisj 0 16 outPtr (outPtr + 16) (by decide) (by decide) (by omega) hp0 rfl,
        readMem64_writeMem128_lo]
  · rw [hDisj 16 64 (outPtr + 16) (outPtr + 64) (by decide) (by decide) (by omega) rfl rfl,
        hDisj 16 48 (outPtr + 16) (outPtr + 48) (by decide) (by decide) (by omega) rfl rfl,
        hDisj 16 32 (outPtr + 16) (outPtr + 32) (by decide) (by decide) (by omega) rfl rfl,
        readMem64_writeMem128_lo]
  · rw [hDisj 32 64 (outPtr + 32) (outPtr + 64) (by decide) (by decide) (by omega) rfl rfl,
        hDisj 32 48 (outPtr + 32) (outPtr + 48) (by decide) (by decide) (by omega) rfl rfl,
        readMem64_writeMem128_lo]
  · rw [hDisj 48 64 (outPtr + 48) (outPtr + 64) (by decide) (by decide) (by omega) rfl rfl,
        readMem64_writeMem128_lo]
  · exact readMem64_writeMem128_lo _ (outPtr + 64) _
  · rw [hDisj 8 64 (outPtr + 8) (outPtr + 64) (by decide) (by decide) (by omega) rfl rfl,
        hDisj 8 48 (outPtr + 8) (outPtr + 48) (by decide) (by decide) (by omega) rfl rfl,
        hDisj 8 32 (outPtr + 8) (outPtr + 32) (by decide) (by decide) (by omega) rfl rfl,
        hDisj 8 16 (outPtr + 8) (outPtr + 16) (by decide) (by decide) (by omega) rfl rfl]
    exact readMem64_writeMem128_hi _ outPtr _
  · rw [hDisj 24 64 (outPtr + 24) (outPtr + 64) (by decide) (by decide) (by omega) rfl rfl,
        hDisj 24 48 (outPtr + 24) (outPtr + 48) (by decide) (by decide) (by omega) rfl rfl,
        hDisj 24 32 (outPtr + 24) (outPtr + 32) (by decide) (by decide) (by omega) rfl rfl,
        ← h16_8]
    exact readMem64_writeMem128_hi _ (outPtr + 16) _
  · rw [hDisj 40 64 (outPtr + 40) (outPtr + 64) (by decide) (by decide) (by omega) rfl rfl,
        hDisj 40 48 (outPtr + 40) (outPtr + 48) (by decide) (by decide) (by omega) rfl rfl,
        ← h32_8]
    exact readMem64_writeMem128_hi _ (outPtr + 32) _
  · rw [hDisj 56 64 (outPtr + 56) (outPtr + 64) (by decide) (by decide) (by omega) rfl rfl,
        ← h48_8]
    exact readMem64_writeMem128_hi _ (outPtr + 48) _
  · rw [← h64_8]
    exact readMem64_writeMem128_hi _ (outPtr + 64) _

theorem keccakNeonOutMem_outside (mem : UInt64 → UInt8) (outPtr s0Ptr s1Ptr a : UInt64)
    (ha : ∀ k : Nat, k < 80 → a ≠ outPtr + UInt64.ofNat k) :
    keccakNeonOutMem mem outPtr s0Ptr s1Ptr a = mem a := by
  unfold keccakNeonOutMem
  dsimp only
  have hout : ∀ (base : Nat) (_hb : base ≤ 64) (m : UInt64 → UInt8) (v : Vec128),
      writeMem128 m (outPtr + UInt64.ofNat base) v a = m a := by
    intro base _hb m v
    apply writeMem128_outside
    intro k _hk heq
    rw [u64_add_ofNat_assoc outPtr base k (by omega)] at heq
    exact ha (base + k) (by omega) heq
  change writeMem128 (writeMem128 (writeMem128 (writeMem128 (writeMem128 mem outPtr _)
    (outPtr + UInt64.ofNat 16) _) (outPtr + UInt64.ofNat 32) _)
    (outPtr + UInt64.ofNat 48) _) (outPtr + UInt64.ofNat 64) _ a = mem a
  rw [hout 64 (by decide), hout 48 (by decide), hout 32 (by decide), hout 16 (by decide)]
  exact writeMem128_outside mem outPtr _ a (fun k hk => ha k (by omega))

/-- End-to-end byte-decoded functional equivalence + 3-way CT-NI certificate for
    `qsag_asm_keccak_sha3_neon` (`N = 39`, `retPc = 152`), connecting the compiled `AArch64`
    SHA3 NEON `EOR` + `BCAX` byte slice directly to `Keccak.chiS` (Rows 0 & 1) and bitwise
    `Keccak.keccakChiBit` (`chiWordBit_eq_keccakChiBit`), with full NEON scratch wiping and zero
    aliasing/wraparound preconditions. -/
theorem rlib_keccak_sha3_neon_functional_and_ct :
    ∃ slice m,
      extractRlibFuncBytes aarch64RlibArchiveBytes "qsag_asm_keccak_sha3_neon" = some slice ∧
      m ∈ parseArArchive aarch64RlibArchiveBytes ∧
      ArPayloadOk aarch64RlibArchiveBytes m ∧
      checkElfFuncThreeWayNI m.payload "qsag_asm_keccak_sha3_neon"
        (mkContract "qsag_asm_keccak_sha3_neon" [0, 1, 2]) = true ∧
      ElfSliceThreeWayNISafe slice (mkContract "qsag_asm_keccak_sha3_neon" [0, 1, 2]) ∧
      decodeArm64Slice slice.code = some keccakSha3NeonProg ∧
      ∀ (st : Arm64BvState), st.pc = 0 → st.halted = false →
        (∃ st38 tr38, execDecodedArm64 slice.code 38 st = some (st38, tr38) ∧ st38.halted = false) ∧
        ∀ extra : Nat, ∃ st' trace,
          execDecodedArm64 slice.code (39 + extra) st = some (st', trace) ∧
          st'.halted = true ∧ st'.pc = 152 ∧ trace.length = 39 ∧
          st'.gpr = st.gpr ∧
          Arm64CalleeSavedPreserved st st' ∧
          (∀ vIdx : Nat, (vIdx < 8 ∨ (16 ≤ vIdx ∧ vIdx ≤ 20)) → st'.vec.get vIdx = Vec128.zero) ∧
          (∀ (K : KState),
            let memU := fun a : UInt64 => st.mem a.toBitVec
            let memU' := fun a : UInt64 => st'.mem a.toBitVec
            let outP := UInt64.ofBitVec (st.gpr.get 0)
            let s0P := UInt64.ofBitVec (st.gpr.get 1)
            let s1P := UInt64.ofBitVec (st.gpr.get 2)
            K.a0 = readMem64 memU s0P ^^^ readMem64 memU s1P →
            K.a1 = readMem64 memU (s0P + 16) ^^^ readMem64 memU (s1P + 16) →
            K.a2 = readMem64 memU (s0P + 32) ^^^ readMem64 memU (s1P + 32) →
            K.a3 = readMem64 memU (s0P + 48) ^^^ readMem64 memU (s1P + 48) →
            K.a4 = readMem64 memU (s0P + 64) ^^^ readMem64 memU (s1P + 64) →
            K.a5 = readMem64 memU (s0P + 8) ^^^ readMem64 memU (s1P + 8) →
            K.a6 = readMem64 memU (s0P + 24) ^^^ readMem64 memU (s1P + 24) →
            K.a7 = readMem64 memU (s0P + 40) ^^^ readMem64 memU (s1P + 40) →
            K.a8 = readMem64 memU (s0P + 56) ^^^ readMem64 memU (s1P + 56) →
            K.a9 = readMem64 memU (s0P + 72) ^^^ readMem64 memU (s1P + 72) →
              readMem64 memU' outP = (chiS K).a0 ∧
              readMem64 memU' (outP + 16) = (chiS K).a1 ∧
              readMem64 memU' (outP + 32) = (chiS K).a2 ∧
              readMem64 memU' (outP + 48) = (chiS K).a3 ∧
              readMem64 memU' (outP + 64) = (chiS K).a4 ∧
              readMem64 memU' (outP + 8) = (chiS K).a5 ∧
              readMem64 memU' (outP + 24) = (chiS K).a6 ∧
              readMem64 memU' (outP + 40) = (chiS K).a7 ∧
              readMem64 memU' (outP + 56) = (chiS K).a8 ∧
              readMem64 memU' (outP + 72) = (chiS K).a9 ∧
              (∀ bit : Nat, bit < 64 →
                (readMem64 memU' outP).toBitVec.getLsbD bit =
                  keccakChiBit (K.a0.toBitVec.getLsbD bit) (K.a1.toBitVec.getLsbD bit) (K.a2.toBitVec.getLsbD bit))) ∧
          (∀ a : BitVec 64, (∀ k : Nat, k < 80 → a ≠ st.gpr.get 0 + BitVec.ofNat 64 k) →
            st'.mem a = st.mem a) := by
  cases hFind : aarch64ExtractedSlices.find? (fun s => s.name == "qsag_asm_keccak_sha3_neon") with
  | none => exfalso; revert hFind; decide +kernel
  | some slice =>
    have hExt : extractRlibFuncBytes aarch64RlibArchiveBytes "qsag_asm_keccak_sha3_neon" = some slice := by
      rw [extractRlibFuncBytes_aarch64_eq, hFind]
    have hNI : checkElfSliceThreeWayNI slice (mkContract "qsag_asm_keccak_sha3_neon" [0, 1, 2]) = true := by
      have hCheck : ((aarch64ExtractedSlices.find? (fun s => s.name == "qsag_asm_keccak_sha3_neon")).map
          (fun sl => checkElfSliceThreeWayNI sl (mkContract "qsag_asm_keccak_sha3_neon" [0, 1, 2]))) =
          some true := by decide +kernel
      rw [hFind] at hCheck
      exact Option.some.inj hCheck
    have hDec : decodeArm64Slice slice.code = some keccakSha3NeonProg := by
      have hD : (aarch64ExtractedSlices.find? (fun s => s.name == "qsag_asm_keccak_sha3_neon")).bind
          (fun sl => decodeArm64Slice sl.code) = some keccakSha3NeonProg := by decide +kernel
      rw [hFind] at hD
      exact hD
    obtain ⟨m, hm, hPay, _, hMemNI, _, hSafe⟩ :=
      extractRlibFuncBytes_member_ni_sound aarch64_rlib_distinct_names hExt hNI
    refine ⟨slice, m, hExt, hm, hPay, hMemNI, hSafe, hDec, ?_⟩
    intro st hpc hh
    rcases st with ⟨pc,
      ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
      ⟨⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15⟩,
       ⟨v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31⟩⟩,
      cf, zf, dit, hlt, mem⟩
    dsimp only at hpc hh; subst hpc hh
    let st0 : Arm64BvState :=
      ⟨0, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        ⟨⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15⟩,
         ⟨v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31⟩⟩,
        cf, zf, dit, false, mem⟩
    have hR := keccakSha3Neon_reaches
      (UInt64.ofBitVec r0) (UInt64.ofBitVec r1) (UInt64.ofBitVec r2) (UInt64.ofBitVec r3)
      (UInt64.ofBitVec r4) (UInt64.ofBitVec r5) (UInt64.ofBitVec r6) (UInt64.ofBitVec r7)
      (UInt64.ofBitVec r8) (UInt64.ofBitVec r9) (UInt64.ofBitVec r10) (UInt64.ofBitVec r11)
      (UInt64.ofBitVec r12) (UInt64.ofBitVec r13) (UInt64.ofBitVec r14) (UInt64.ofBitVec r15)
      (bank16ToU64 hi) v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
      v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 cf zf dit
      (fun a => mem a.toBitVec)
    obtain ⟨hPre, hPost⟩ := execDecodedArm64_ret_of_reaches st0 hDec rfl hR rfl rfl
    refine ⟨hPre, fun extra => ?_⟩
    obtain ⟨tr, hExec, hL⟩ := hPost extra
    refine ⟨_, tr, hExec, rfl, rfl, hL, ?_, ?_, ?_, ?_, ?_⟩
    · exact congrArg (Bank32.mk _) (bank16_roundtrip hi)
    · refine ⟨fun r hr1 _ => ?_, fun vIdx hv1 hv2 => ?_⟩
      · have hNot16 : ¬ r < 16 := by omega
        simp only [Arm64BvState.ofArm64State, bank32OfU64, bank16_roundtrip, Bank32.get, ite_eq_right hNot16]
      · match vIdx, hv1, hv2 with
        | 8, _, _ | 9, _, _ | 10, _, _ | 11, _, _ | 12, _, _ | 13, _, _ | 14, _, _ | 15, _, _ => rfl
        | n + 16, _, h => exact absurd h (by omega)
        | 0, h, _ | 1, h, _ | 2, h, _ | 3, h, _ | 4, h, _ | 5, h, _ | 6, h, _ | 7, h, _ => exact absurd h (by omega)
    · intro vIdx hv
      rcases hv with hlt8 | ⟨hge16, hle20⟩
      · match vIdx, hlt8 with
        | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl
        | n + 8, h => exact absurd h (by omega)
      · match vIdx, hge16, hle20 with
        | 16, _, _ | 17, _, _ | 18, _, _ | 19, _, _ | 20, _, _ => rfl
        | n + 21, _, h => exact absurd h (by omega)
        | 0, h, _ | 1, h, _ | 2, h, _ | 3, h, _ | 4, h, _ | 5, h, _ | 6, h, _ | 7, h, _
        | 8, h, _ | 9, h, _ | 10, h, _ | 11, h, _ | 12, h, _ | 13, h, _ | 14, h, _ | 15, h, _ =>
          exact absurd h (by omega)
    · intro K
      dsimp only
      intro ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8 ha9
      obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ :=
        keccakNeonOutMem_lanes (fun x => mem x.toBitVec) (UInt64.ofBitVec r0)
          (UInt64.ofBitVec r1) (UInt64.ofBitVec r2) K ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8 ha9
      refine ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, fun bit hbit => ?_⟩
      exact (congrArg (fun w : UInt64 => w.toBitVec.getLsbD bit) c0).trans
        (chiWordBit_eq_keccakChiBit K.a0 K.a1 K.a2 bit hbit)
    · intro a ha
      dsimp only [Arm64BvState.ofArm64State, b32get_0]
      rw [keccakNeonOutMem_outside _ _ _ _ (UInt64.ofBitVec a) (fun k hk heq => by
        have hb := congrArg UInt64.toBitVec heq
        rw [u64_roundtrip] at hb
        have hOfNat : (UInt64.ofBitVec r0 + UInt64.ofNat k).toBitVec = r0 + BitVec.ofNat 64 k := by
          simp only [UInt64.toBitVec_add]
          congr 1
        rw [hOfNat] at hb
        exact ha k hk hb), u64_roundtrip]


/-! Fresh archive bindings for unchanged AArch64 semantic bodies. -/

theorem current_aarch64_rlib_distinct_names :
    allDistinctStrings ((extractAllRlibFuncs currentAarch64RlibArchiveBytes).map ElfFuncSlice.name) = true := by
  rw [currentAarch64_symbol_names_exact]
  decide +kernel

theorem current_extractRlibFuncBytes_aarch64_eq (symName : String) :
    extractRlibFuncBytes currentAarch64RlibArchiveBytes symName =
      currentAarch64ExtractedSlices.find? (fun s => s.name == symName) := by
  unfold extractRlibFuncBytes
  rw [currentAarch64_rlib_extracted_slices]

theorem current_rlib_ct_eq_32_aarch64_functional_and_ct :
    ∃ slice m,
      extractRlibFuncBytes currentAarch64RlibArchiveBytes "qsag_asm_ct_eq_32_aarch64" = some slice ∧
      m ∈ parseArArchive currentAarch64RlibArchiveBytes ∧
      ArPayloadOk currentAarch64RlibArchiveBytes m ∧
      checkElfFuncThreeWayNI m.payload "qsag_asm_ct_eq_32_aarch64"
        (mkContract "qsag_asm_ct_eq_32_aarch64" [0, 1] [] [2, 3, 4, 5, 6, 7]) = true ∧
      ElfSliceThreeWayNISafe slice
        (mkContract "qsag_asm_ct_eq_32_aarch64" [0, 1] [] [2, 3, 4, 5, 6, 7]) ∧
      decodeArm64Slice slice.code = some ctEq32ArmProg ∧
      ∀ (st : Arm64BvState), st.pc = 0 → st.halted = false →
        (∃ st21 tr21, execDecodedArm64 slice.code 21 st = some (st21, tr21) ∧ st21.halted = false) ∧
        ∀ extra : Nat, ∃ st' trace,
          execDecodedArm64 slice.code (22 + extra) st = some (st', trace) ∧
          st'.halted = true ∧ st'.pc = 84 ∧ trace.length = 22 ∧
          st'.gpr.get 0 =
            (if ∀ i : Nat, i < 32 →
                st.mem (st.gpr.get 0 + BitVec.ofNat 64 i) =
                  st.mem (st.gpr.get 1 + BitVec.ofNat 64 i)
              then 1#64 else 0#64) ∧
          Arm64CalleeSavedPreserved st st' ∧
          st'.mem = st.mem ∧
          (∀ r : Nat, 2 ≤ r → r ≤ 7 → st'.gpr.get r = 0#64) := by
  cases hFind : currentAarch64ExtractedSlices.find? (fun s => s.name == "qsag_asm_ct_eq_32_aarch64") with
  | none => exfalso; revert hFind; decide +kernel
  | some slice =>
    have hExt : extractRlibFuncBytes currentAarch64RlibArchiveBytes "qsag_asm_ct_eq_32_aarch64" = some slice := by
      rw [current_extractRlibFuncBytes_aarch64_eq, hFind]
    have hNI : checkElfSliceThreeWayNI slice
        (mkContract "qsag_asm_ct_eq_32_aarch64" [0, 1] [] [2, 3, 4, 5, 6, 7]) = true := by
      have hCheck : ((currentAarch64ExtractedSlices.find? (fun s => s.name == "qsag_asm_ct_eq_32_aarch64")).map
          (fun sl => checkElfSliceThreeWayNI sl
            (mkContract "qsag_asm_ct_eq_32_aarch64" [0, 1] [] [2, 3, 4, 5, 6, 7]))) =
          some true := by decide +kernel
      rw [hFind] at hCheck
      exact Option.some.inj hCheck
    have hDec : decodeArm64Slice slice.code = some ctEq32ArmProg := by
      have hD : (currentAarch64ExtractedSlices.find? (fun s => s.name == "qsag_asm_ct_eq_32_aarch64")).bind
          (fun sl => decodeArm64Slice sl.code) = some ctEq32ArmProg := by decide +kernel
      rw [hFind] at hD
      exact hD
    obtain ⟨m, hm, hPay, _, hMemNI, _, hSafe⟩ :=
      extractRlibFuncBytes_member_ni_sound current_aarch64_rlib_distinct_names hExt hNI
    refine ⟨slice, m, hExt, hm, hPay, hMemNI, hSafe, hDec, ?_⟩
    intro st hpc hh
    rcases st with ⟨pc, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
      v, cf, zf, dit, hlt, mem⟩
    dsimp only at hpc hh; subst hpc hh
    let st0 : Arm64BvState := ⟨0, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩, v, cf, zf, dit, false, mem⟩
    let mU : UInt64 → UInt8 := fun a => mem a.toBitVec
    obtain ⟨hPre, hPost⟩ := execDecodedArm64_ret_of_reaches st0 hDec rfl
      (ctEq32Arm_reaches (UInt64.ofBitVec r0) (UInt64.ofBitVec r1) (UInt64.ofBitVec r2)
        (UInt64.ofBitVec r3) (UInt64.ofBitVec r4) (UInt64.ofBitVec r5) (UInt64.ofBitVec r6)
        (UInt64.ofBitVec r7) (UInt64.ofBitVec r8) (UInt64.ofBitVec r9) (UInt64.ofBitVec r10)
        (UInt64.ofBitVec r11) (UInt64.ofBitVec r12) (UInt64.ofBitVec r13) (UInt64.ofBitVec r14)
        (UInt64.ofBitVec r15) (bank16ToU64 hi) v cf zf dit mU)
      rfl rfl
    refine ⟨hPre, fun extra => ?_⟩
    obtain ⟨tr, hExec, hL⟩ := hPost extra
    refine ⟨_, tr, hExec, rfl, rfl, hL, ?_, arm64_callee_saved_of_hi_vec, mem_roundtrip mem, ?_⟩
    · change (((ctEq32WordArm mU (UInt64.ofBitVec r0) (UInt64.ofBitVec r1) |||
          (0 - ctEq32WordArm mU (UInt64.ofBitVec r0) (UInt64.ofBitVec r1))) >>>
          UInt64.ofNat 63) ^^^ 1).toBitVec =
        (if ∀ i : Nat, i < 32 →
            mem (r0 + BitVec.ofNat 64 i) = mem (r1 + BitVec.ofNat 64 i)
          then 1#64 else 0#64)
      rw [zeroTest64]
      have e8 : ∀ x : UInt64, x + 0 + 8 = x + UInt64.ofNat 8 := fun x => by rw [UInt64.add_zero]; rfl
      have e24 : ∀ x : UInt64, x + 16 + 8 = x + UInt64.ofNat 24 := fun x => by rw [UInt64.add_assoc]; rfl
      have hiff0 : ctEq32WordArm mU (UInt64.ofBitVec r0) (UInt64.ofBitVec r1) = 0 ↔
          ∀ i : Nat, i < 32 →
            mU (UInt64.ofBitVec r0 + UInt64.ofNat i) =
              mU (UInt64.ofBitVec r1 + UInt64.ofNat i) :=
        xorOr4_eq_zero_iff mU (UInt64.ofBitVec r0) (UInt64.ofBitVec r1) _ _ _ _ _ _ _ _
          rfl (e8 _) rfl (e24 _) rfl (e8 _) rfl (e24 _)
      have hAddrEq (base : BitVec 64) (i : Nat) :
          (UInt64.ofBitVec base + UInt64.ofNat i).toBitVec = base + BitVec.ofNat 64 i := rfl
      have hiff : ctEq32WordArm mU (UInt64.ofBitVec r0) (UInt64.ofBitVec r1) = 0 ↔
          ∀ i : Nat, i < 32 → mem (r0 + BitVec.ofNat 64 i) = mem (r1 + BitVec.ofNat 64 i) := by
        simpa only [mU, hAddrEq] using hiff0
      if hW : ctEq32WordArm mU (UInt64.ofBitVec r0) (UInt64.ofBitVec r1) = 0 then
        rw [ite_eq_left hW, ite_eq_left (hiff.mp hW)]; rfl
      else
        rw [ite_eq_right hW, ite_eq_right (fun h => hW (hiff.mpr h))]; rfl
    · intro r hr1 hr2
      match r, hr1, hr2 with
      | 2, _, _ => rfl | 3, _, _ => rfl | 4, _, _ => rfl
      | 5, _, _ => rfl | 6, _, _ => rfl | 7, _, _ => rfl
      | 0, h, _ => exact absurd h (by decide)
      | 1, h, _ => exact absurd h (by decide)
      | n + 8, _, h => exact absurd h (by omega)

theorem current_rlib_enable_dit_aarch64_functional_and_ct :
    ∃ slice m,
      extractRlibFuncBytes currentAarch64RlibArchiveBytes "qsag_asm_enable_dit_aarch64" = some slice ∧
      m ∈ parseArArchive currentAarch64RlibArchiveBytes ∧
      ArPayloadOk currentAarch64RlibArchiveBytes m ∧
      checkElfFuncThreeWayNI m.payload "qsag_asm_enable_dit_aarch64"
        (mkContract "qsag_asm_enable_dit_aarch64" []) = true ∧
      ElfSliceThreeWayNISafe slice (mkContract "qsag_asm_enable_dit_aarch64" []) ∧
      decodeArm64Slice slice.code = some enableDitArmProg ∧
      ∀ (st : Arm64BvState), st.pc = 0 → st.halted = false →
        (∃ st2 tr2, execDecodedArm64 slice.code 2 st = some (st2, tr2) ∧ st2.halted = false) ∧
        ∀ extra : Nat, ∃ st' trace,
          execDecodedArm64 slice.code (3 + extra) st = some (st', trace) ∧
          st'.halted = true ∧ st'.pc = 8 ∧ trace.length = 3 ∧
          st'.dit = true ∧
          st'.gpr = st.gpr ∧
          st'.vec = st.vec ∧
          st'.cf = st.cf ∧ st'.zf = st.zf ∧
          Arm64CalleeSavedPreserved st st' ∧
          st'.mem = st.mem := by
  cases hFind : currentAarch64ExtractedSlices.find? (fun s => s.name == "qsag_asm_enable_dit_aarch64") with
  | none => exfalso; revert hFind; decide +kernel
  | some slice =>
    have hExt : extractRlibFuncBytes currentAarch64RlibArchiveBytes "qsag_asm_enable_dit_aarch64" = some slice := by
      rw [current_extractRlibFuncBytes_aarch64_eq, hFind]
    have hNI : checkElfSliceThreeWayNI slice (mkContract "qsag_asm_enable_dit_aarch64" []) = true := by
      have hCheck : ((currentAarch64ExtractedSlices.find? (fun s => s.name == "qsag_asm_enable_dit_aarch64")).map
          (fun sl => checkElfSliceThreeWayNI sl (mkContract "qsag_asm_enable_dit_aarch64" []))) =
          some true := by decide +kernel
      rw [hFind] at hCheck
      exact Option.some.inj hCheck
    have hDec : decodeArm64Slice slice.code = some enableDitArmProg := by
      have hD : (currentAarch64ExtractedSlices.find? (fun s => s.name == "qsag_asm_enable_dit_aarch64")).bind
          (fun sl => decodeArm64Slice sl.code) = some enableDitArmProg := by decide +kernel
      rw [hFind] at hD
      exact hD
    obtain ⟨m, hm, hPay, _, hMemNI, _, hSafe⟩ :=
      extractRlibFuncBytes_member_ni_sound current_aarch64_rlib_distinct_names hExt hNI
    refine ⟨slice, m, hExt, hm, hPay, hMemNI, hSafe, hDec, ?_⟩
    intro st hpc hh
    rcases st with ⟨pc, ⟨lo, hi⟩, v, cf, zf, dit, hlt, mem⟩
    dsimp only at hpc hh; subst hpc hh
    let st0 : Arm64BvState := ⟨0, ⟨lo, hi⟩, v, cf, zf, dit, false, mem⟩
    obtain ⟨hPre, hPost⟩ := execDecodedArm64_ret_of_reaches st0 hDec rfl
      (enableDitArm_reaches (bank32ToU64 ⟨lo, hi⟩) v cf zf dit (fun a => mem a.toBitVec)) rfl rfl
    refine ⟨hPre, fun extra => ?_⟩
    obtain ⟨tr, hExec, hL⟩ := hPost extra
    refine ⟨_, tr, hExec, rfl, rfl, hL, rfl, ?_, rfl, rfl, rfl, arm64_callee_saved_of_hi_vec, mem_roundtrip mem⟩
    show (⟨bank16OfU64 (bank16ToU64 lo), bank16OfU64 (bank16ToU64 hi)⟩ : Bank32 (BitVec 64)) = ⟨lo, hi⟩
    rw [bank16_roundtrip, bank16_roundtrip]

theorem current_rlib_keccak_sha3_neon_functional_and_ct :
    ∃ slice m,
      extractRlibFuncBytes currentAarch64RlibArchiveBytes "qsag_asm_keccak_sha3_neon" = some slice ∧
      m ∈ parseArArchive currentAarch64RlibArchiveBytes ∧
      ArPayloadOk currentAarch64RlibArchiveBytes m ∧
      checkElfFuncThreeWayNI m.payload "qsag_asm_keccak_sha3_neon"
        (mkContract "qsag_asm_keccak_sha3_neon" [0, 1, 2]) = true ∧
      ElfSliceThreeWayNISafe slice (mkContract "qsag_asm_keccak_sha3_neon" [0, 1, 2]) ∧
      decodeArm64Slice slice.code = some keccakSha3NeonProg ∧
      ∀ (st : Arm64BvState), st.pc = 0 → st.halted = false →
        (∃ st38 tr38, execDecodedArm64 slice.code 38 st = some (st38, tr38) ∧ st38.halted = false) ∧
        ∀ extra : Nat, ∃ st' trace,
          execDecodedArm64 slice.code (39 + extra) st = some (st', trace) ∧
          st'.halted = true ∧ st'.pc = 152 ∧ trace.length = 39 ∧
          st'.gpr = st.gpr ∧
          Arm64CalleeSavedPreserved st st' ∧
          (∀ vIdx : Nat, (vIdx < 8 ∨ (16 ≤ vIdx ∧ vIdx ≤ 20)) → st'.vec.get vIdx = Vec128.zero) ∧
          (∀ (K : KState),
            let memU := fun a : UInt64 => st.mem a.toBitVec
            let memU' := fun a : UInt64 => st'.mem a.toBitVec
            let outP := UInt64.ofBitVec (st.gpr.get 0)
            let s0P := UInt64.ofBitVec (st.gpr.get 1)
            let s1P := UInt64.ofBitVec (st.gpr.get 2)
            K.a0 = readMem64 memU s0P ^^^ readMem64 memU s1P →
            K.a1 = readMem64 memU (s0P + 16) ^^^ readMem64 memU (s1P + 16) →
            K.a2 = readMem64 memU (s0P + 32) ^^^ readMem64 memU (s1P + 32) →
            K.a3 = readMem64 memU (s0P + 48) ^^^ readMem64 memU (s1P + 48) →
            K.a4 = readMem64 memU (s0P + 64) ^^^ readMem64 memU (s1P + 64) →
            K.a5 = readMem64 memU (s0P + 8) ^^^ readMem64 memU (s1P + 8) →
            K.a6 = readMem64 memU (s0P + 24) ^^^ readMem64 memU (s1P + 24) →
            K.a7 = readMem64 memU (s0P + 40) ^^^ readMem64 memU (s1P + 40) →
            K.a8 = readMem64 memU (s0P + 56) ^^^ readMem64 memU (s1P + 56) →
            K.a9 = readMem64 memU (s0P + 72) ^^^ readMem64 memU (s1P + 72) →
              readMem64 memU' outP = (chiS K).a0 ∧
              readMem64 memU' (outP + 16) = (chiS K).a1 ∧
              readMem64 memU' (outP + 32) = (chiS K).a2 ∧
              readMem64 memU' (outP + 48) = (chiS K).a3 ∧
              readMem64 memU' (outP + 64) = (chiS K).a4 ∧
              readMem64 memU' (outP + 8) = (chiS K).a5 ∧
              readMem64 memU' (outP + 24) = (chiS K).a6 ∧
              readMem64 memU' (outP + 40) = (chiS K).a7 ∧
              readMem64 memU' (outP + 56) = (chiS K).a8 ∧
              readMem64 memU' (outP + 72) = (chiS K).a9 ∧
              (∀ bit : Nat, bit < 64 →
                (readMem64 memU' outP).toBitVec.getLsbD bit =
                  keccakChiBit (K.a0.toBitVec.getLsbD bit) (K.a1.toBitVec.getLsbD bit) (K.a2.toBitVec.getLsbD bit))) ∧
          (∀ a : BitVec 64, (∀ k : Nat, k < 80 → a ≠ st.gpr.get 0 + BitVec.ofNat 64 k) →
            st'.mem a = st.mem a) := by
  cases hFind : currentAarch64ExtractedSlices.find? (fun s => s.name == "qsag_asm_keccak_sha3_neon") with
  | none => exfalso; revert hFind; decide +kernel
  | some slice =>
    have hExt : extractRlibFuncBytes currentAarch64RlibArchiveBytes "qsag_asm_keccak_sha3_neon" = some slice := by
      rw [current_extractRlibFuncBytes_aarch64_eq, hFind]
    have hNI : checkElfSliceThreeWayNI slice (mkContract "qsag_asm_keccak_sha3_neon" [0, 1, 2]) = true := by
      have hCheck : ((currentAarch64ExtractedSlices.find? (fun s => s.name == "qsag_asm_keccak_sha3_neon")).map
          (fun sl => checkElfSliceThreeWayNI sl (mkContract "qsag_asm_keccak_sha3_neon" [0, 1, 2]))) =
          some true := by decide +kernel
      rw [hFind] at hCheck
      exact Option.some.inj hCheck
    have hDec : decodeArm64Slice slice.code = some keccakSha3NeonProg := by
      have hD : (currentAarch64ExtractedSlices.find? (fun s => s.name == "qsag_asm_keccak_sha3_neon")).bind
          (fun sl => decodeArm64Slice sl.code) = some keccakSha3NeonProg := by decide +kernel
      rw [hFind] at hD
      exact hD
    obtain ⟨m, hm, hPay, _, hMemNI, _, hSafe⟩ :=
      extractRlibFuncBytes_member_ni_sound current_aarch64_rlib_distinct_names hExt hNI
    refine ⟨slice, m, hExt, hm, hPay, hMemNI, hSafe, hDec, ?_⟩
    intro st hpc hh
    rcases st with ⟨pc,
      ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
      ⟨⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15⟩,
       ⟨v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31⟩⟩,
      cf, zf, dit, hlt, mem⟩
    dsimp only at hpc hh; subst hpc hh
    let st0 : Arm64BvState :=
      ⟨0, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        ⟨⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15⟩,
         ⟨v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31⟩⟩,
        cf, zf, dit, false, mem⟩
    have hR := keccakSha3Neon_reaches
      (UInt64.ofBitVec r0) (UInt64.ofBitVec r1) (UInt64.ofBitVec r2) (UInt64.ofBitVec r3)
      (UInt64.ofBitVec r4) (UInt64.ofBitVec r5) (UInt64.ofBitVec r6) (UInt64.ofBitVec r7)
      (UInt64.ofBitVec r8) (UInt64.ofBitVec r9) (UInt64.ofBitVec r10) (UInt64.ofBitVec r11)
      (UInt64.ofBitVec r12) (UInt64.ofBitVec r13) (UInt64.ofBitVec r14) (UInt64.ofBitVec r15)
      (bank16ToU64 hi) v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15
      v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 cf zf dit
      (fun a => mem a.toBitVec)
    obtain ⟨hPre, hPost⟩ := execDecodedArm64_ret_of_reaches st0 hDec rfl hR rfl rfl
    refine ⟨hPre, fun extra => ?_⟩
    obtain ⟨tr, hExec, hL⟩ := hPost extra
    refine ⟨_, tr, hExec, rfl, rfl, hL, ?_, ?_, ?_, ?_, ?_⟩
    · exact congrArg (Bank32.mk _) (bank16_roundtrip hi)
    · refine ⟨fun r hr1 _ => ?_, fun vIdx hv1 hv2 => ?_⟩
      · have hNot16 : ¬ r < 16 := by omega
        simp only [Arm64BvState.ofArm64State, bank32OfU64, bank16_roundtrip, Bank32.get, ite_eq_right hNot16]
      · match vIdx, hv1, hv2 with
        | 8, _, _ | 9, _, _ | 10, _, _ | 11, _, _ | 12, _, _ | 13, _, _ | 14, _, _ | 15, _, _ => rfl
        | n + 16, _, h => exact absurd h (by omega)
        | 0, h, _ | 1, h, _ | 2, h, _ | 3, h, _ | 4, h, _ | 5, h, _ | 6, h, _ | 7, h, _ => exact absurd h (by omega)
    · intro vIdx hv
      rcases hv with hlt8 | ⟨hge16, hle20⟩
      · match vIdx, hlt8 with
        | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl
        | n + 8, h => exact absurd h (by omega)
      · match vIdx, hge16, hle20 with
        | 16, _, _ | 17, _, _ | 18, _, _ | 19, _, _ | 20, _, _ => rfl
        | n + 21, _, h => exact absurd h (by omega)
        | 0, h, _ | 1, h, _ | 2, h, _ | 3, h, _ | 4, h, _ | 5, h, _ | 6, h, _ | 7, h, _
        | 8, h, _ | 9, h, _ | 10, h, _ | 11, h, _ | 12, h, _ | 13, h, _ | 14, h, _ | 15, h, _ =>
          exact absurd h (by omega)
    · intro K
      dsimp only
      intro ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8 ha9
      obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ :=
        keccakNeonOutMem_lanes (fun x => mem x.toBitVec) (UInt64.ofBitVec r0)
          (UInt64.ofBitVec r1) (UInt64.ofBitVec r2) K ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8 ha9
      refine ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, fun bit hbit => ?_⟩
      exact (congrArg (fun w : UInt64 => w.toBitVec.getLsbD bit) c0).trans
        (chiWordBit_eq_keccakChiBit K.a0 K.a1 K.a2 bit hbit)
    · intro a ha
      dsimp only [Arm64BvState.ofArm64State, b32get_0]
      rw [keccakNeonOutMem_outside _ _ _ _ (UInt64.ofBitVec a) (fun k hk heq => by
        have hb := congrArg UInt64.toBitVec heq
        rw [u64_roundtrip] at hb
        have hOfNat : (UInt64.ofBitVec r0 + UInt64.ofNat k).toBitVec = r0 + BitVec.ofNat 64 k := by
          simp only [UInt64.toBitVec_add]
          congr 1
        rw [hOfNat] at hb
        exact ha k hk hb), u64_roundtrip]

theorem current_ct_eq_32_x86_64_functional_and_ct :
    ∃ slice prog, findSliceByNameBytes currentX86ExtractedSlices ctEq32X86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ElfSliceThreeWayNISafe slice currentX86SymbolContracts[13] ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 28 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        (runX86 prog fuel s).1.gpr.get 0 =
          (if ∀ i : Nat, i < 32 →
              s.mem (s.gpr.get 7 + UInt64.ofNat i) = s.mem (s.gpr.get 6 + UInt64.ofNat i)
            then 1 else 0) ∧
        (runX86 prog fuel s).1.mem = s.mem ∧
        (runX86 prog fuel s).1.gpr.get 1 = 0 ∧ (runX86 prog fuel s).1.gpr.get 2 = 0 ∧
        (runX86 prog fuel s).1.gpr.get 8 = 0  := by
  obtain ⟨slice, prog, hf, hd, hfun⟩ := current_ct_eq_32_x86_64_mc_refines
  have he : findSliceByNameBytes currentX86ExtractedSlices ctEq32X86Name =
      some currentX86ExtractedSlices[13] := by decide +kernel
  have hs : slice = currentX86ExtractedSlices[13] := Option.some.inj (hf.symm.trans he)
  refine ⟨slice, prog, hf, hd, ?_, hfun⟩
  rw [hs]
  apply checkElfSliceWithCert_sound (cert := currentX86InvCerts[13])
  exact currentX86_symbol_13_certificate


theorem current_goldilocks_add_ct_x86_64_functional_and_ct :
    ∃ slice prog, findSliceByNameBytes currentX86ExtractedSlices goldAddX86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ElfSliceThreeWayNISafe slice currentX86SymbolContracts[9] ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 25 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        ((runX86 prog fuel s).1.gpr.get 0).toNat =
          ((s.gpr.get 7).toNat + (s.gpr.get 6).toNat) % goldilocksPrime ∧
        (runX86 prog fuel s).1.mem = s.mem ∧
        (runX86 prog fuel s).1.gpr.get 1 = 0 ∧ (runX86 prog fuel s).1.gpr.get 8 = 0 ∧
        (runX86 prog fuel s).1.gpr.get 9 = 0 ∧ (runX86 prog fuel s).1.gpr.get 10 = 0  := by
  obtain ⟨slice, prog, hf, hd, hfun⟩ := current_goldilocks_add_ct_x86_64_mc_refines
  have he : findSliceByNameBytes currentX86ExtractedSlices goldAddX86Name =
      some currentX86ExtractedSlices[9] := by decide +kernel
  have hs : slice = currentX86ExtractedSlices[9] := Option.some.inj (hf.symm.trans he)
  refine ⟨slice, prog, hf, hd, ?_, hfun⟩
  rw [hs]
  apply checkElfSliceWithCert_sound (cert := currentX86InvCerts[9])
  exact currentX86_symbol_09_certificate


theorem current_goldilocks_sub_ct_x86_64_functional_and_ct :
    ∃ slice prog, findSliceByNameBytes currentX86ExtractedSlices goldSubX86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ElfSliceThreeWayNISafe slice currentX86SymbolContracts[10] ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 31 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        ((runX86 prog fuel s).1.gpr.get 0).toNat =
          ((s.gpr.get 7).toNat + goldilocksPrime - (s.gpr.get 6).toNat % goldilocksPrime) %
            goldilocksPrime ∧
        (runX86 prog fuel s).1.mem = s.mem ∧
        (runX86 prog fuel s).1.gpr.get 1 = 0 ∧ (runX86 prog fuel s).1.gpr.get 6 = 0 ∧
        (runX86 prog fuel s).1.gpr.get 8 = 0 ∧ (runX86 prog fuel s).1.gpr.get 9 = 0 ∧
        (runX86 prog fuel s).1.gpr.get 10 = 0  := by
  obtain ⟨slice, prog, hf, hd, hfun⟩ := current_goldilocks_sub_ct_x86_64_mc_refines
  have he : findSliceByNameBytes currentX86ExtractedSlices goldSubX86Name =
      some currentX86ExtractedSlices[10] := by decide +kernel
  have hs : slice = currentX86ExtractedSlices[10] := Option.some.inj (hf.symm.trans he)
  refine ⟨slice, prog, hf, hd, ?_, hfun⟩
  rw [hs]
  apply checkElfSliceWithCert_sound (cert := currentX86InvCerts[10])
  exact currentX86_symbol_10_certificate


theorem current_goldilocks_mul_ct_x86_64_functional_and_ct :
    ∃ slice prog, findSliceByNameBytes currentX86ExtractedSlices goldMulX86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ElfSliceThreeWayNISafe slice currentX86SymbolContracts[8] ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 33 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        ((runX86 prog fuel s).1.gpr.get 0).toNat =
          ((s.gpr.get 7).toNat * (s.gpr.get 6).toNat) % goldilocksPrime ∧
        (runX86 prog fuel s).1.mem = s.mem ∧
        (runX86 prog fuel s).1.gpr.get 1 = 0 ∧ (runX86 prog fuel s).1.gpr.get 2 = 0 ∧
        (runX86 prog fuel s).1.gpr.get 8 = 0 ∧ (runX86 prog fuel s).1.gpr.get 9 = 0  := by
  obtain ⟨slice, prog, hf, hd, hfun⟩ := current_goldilocks_mul_ct_x86_64_mc_refines
  have he : findSliceByNameBytes currentX86ExtractedSlices goldMulX86Name =
      some currentX86ExtractedSlices[8] := by decide +kernel
  have hs : slice = currentX86ExtractedSlices[8] := Option.some.inj (hf.symm.trans he)
  refine ⟨slice, prog, hf, hd, ?_, hfun⟩
  rw [hs]
  apply checkElfSliceWithCert_sound (cert := currentX86InvCerts[8])
  exact currentX86_symbol_08_certificate


theorem current_goldilocks_mul_ct_aarch64_functional_and_ct :
    ∃ slice prog, findSliceByNameBytes currentAarch64ExtractedSlices goldMulArmName = some slice ∧
      decodeArm64Stream slice.code = some prog ∧
      ElfSliceThreeWayNISafe slice currentAarch64SymbolContracts[4] ∧
      ∀ (s : Arm64State) (fuel : Nat), s.pc = 0 → s.halted = false → 30 ≤ fuel →
        (runArm64 prog fuel s).1.halted = true ∧
        ((runArm64 prog fuel s).1.gpr.get 0).toNat =
          ((s.gpr.get 0).toNat * (s.gpr.get 1).toNat) % goldilocksPrime ∧
        (runArm64 prog fuel s).1.mem = s.mem ∧
        (∀ r : Nat, 2 ≤ r → r ≤ 8 → (runArm64 prog fuel s).1.gpr.get r = 0)  := by
  obtain ⟨slice, prog, hf, hd, hfun⟩ := current_goldilocks_mul_ct_aarch64_mc_refines
  have he : findSliceByNameBytes currentAarch64ExtractedSlices goldMulArmName =
      some currentAarch64ExtractedSlices[4] := by decide +kernel
  have hs : slice = currentAarch64ExtractedSlices[4] := Option.some.inj (hf.symm.trans he)
  refine ⟨slice, prog, hf, hd, ?_, hfun⟩
  rw [hs]
  apply checkElfSliceWithCert_sound (cert := currentAarch64InvCerts[4])
  exact currentAarch64_symbol_04_certificate


theorem current_ct_memzero_x86_64_functional_and_ct :
    ∃ slice prog, findSliceByNameBytes currentX86ExtractedSlices ctMemzeroX86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ElfSliceThreeWayNISafe slice currentX86SymbolContracts[15] ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 0 < (s.gpr.get 6).toNat →
        4 * (s.gpr.get 6).toNat + 13 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        (∀ i : Nat, i < (s.gpr.get 6).toNat →
          (runX86 prog fuel s).1.mem (s.gpr.get 7 + UInt64.ofNat i) = 0) ∧
        (∀ a : UInt64, (∀ i : Nat, i < (s.gpr.get 6).toNat → a ≠ s.gpr.get 7 + UInt64.ofNat i) →
          (runX86 prog fuel s).1.mem a = s.mem a)  := by
  obtain ⟨slice, prog, hf, hd, hfun⟩ := current_ct_memzero_x86_64_mc_refines
  have he : findSliceByNameBytes currentX86ExtractedSlices ctMemzeroX86Name =
      some currentX86ExtractedSlices[15] := by decide +kernel
  have hs : slice = currentX86ExtractedSlices[15] := Option.some.inj (hf.symm.trans he)
  refine ⟨slice, prog, hf, hd, ?_, hfun⟩
  rw [hs]
  apply checkElfSliceWithCert_sound (cert := currentX86InvCerts[15])
  exact currentX86_symbol_15_certificate


theorem current_ct_memzero_aarch64_functional_and_ct :
    ∃ slice prog, findSliceByNameBytes currentAarch64ExtractedSlices ctMemzeroArmName = some slice ∧
      decodeArm64Stream slice.code = some prog ∧
      ElfSliceThreeWayNISafe slice currentAarch64SymbolContracts[6] ∧
      ∀ (s : Arm64State) (fuel : Nat), s.pc = 0 → s.halted = false → 0 < (s.gpr.get 1).toNat →
        3 * (s.gpr.get 1).toNat + 2 ≤ fuel →
        (runArm64 prog fuel s).1.halted = true ∧
        (∀ i : Nat, i < (s.gpr.get 1).toNat →
          (runArm64 prog fuel s).1.mem (s.gpr.get 0 + UInt64.ofNat i) = 0) ∧
        (∀ a : UInt64, (∀ i : Nat, i < (s.gpr.get 1).toNat → a ≠ s.gpr.get 0 + UInt64.ofNat i) →
          (runArm64 prog fuel s).1.mem a = s.mem a)  := by
  obtain ⟨slice, prog, hf, hd, hfun⟩ := current_ct_memzero_aarch64_mc_refines
  have he : findSliceByNameBytes currentAarch64ExtractedSlices ctMemzeroArmName =
      some currentAarch64ExtractedSlices[6] := by decide +kernel
  have hs : slice = currentAarch64ExtractedSlices[6] := Option.some.inj (hf.symm.trans he)
  refine ⟨slice, prog, hf, hd, ?_, hfun⟩
  rw [hs]
  apply checkElfSliceWithCert_sound (cert := currentAarch64InvCerts[6])
  exact currentAarch64_symbol_06_certificate


theorem current_x86_rlib_distinct_names :
    allDistinctStrings ((extractAllRlibFuncs currentX86RlibArchiveBytes).map ElfFuncSlice.name) = true := by
  rw [currentX86_symbol_names_exact]
  decide +kernel

theorem current_extractRlibFuncBytes_x86_eq (symName : String) :
    extractRlibFuncBytes currentX86RlibArchiveBytes symName =
      currentX86ExtractedSlices.find? (fun s => s.name == symName) := by
  unfold extractRlibFuncBytes
  rw [currentX86_rlib_extracted_slices]

def current_gf256MulGfniProg : List (DecodedInstr X86Instr) := [
  ⟨0, 10, .movImm true 0 0x71500a8a86be78ce⟩,
  ⟨10, 5, .vmovGprToXmm true 14 0⟩,
  ⟨15, 5, .vpbroadcast true true 14 14⟩,
  ⟨20, 10, .movImm true 0 0xa1e4f8e072a2700c⟩,
  ⟨30, 5, .vmovGprToXmm true 15 0⟩,
  ⟨35, 5, .vpbroadcast true true 15 15⟩,
  ⟨40, 4, .vload true 0 (.baseDisp 6 0)⟩,
  ⟨44, 4, .vload true 1 (.baseDisp 2 0)⟩,
  ⟨48, 6, .vgf2p8affineqb true 0 0 14 0⟩,
  ⟨54, 6, .vgf2p8affineqb true 1 1 14 0⟩,
  ⟨60, 5, .vbinOp .vgf2p8mulb true 2 0 1⟩,
  ⟨65, 6, .vgf2p8affineqb true 2 2 15 0⟩,
  ⟨71, 4, .vstore true 2 (.baseDisp 7 0)⟩,
  ⟨75, 4, .aluImm .add true 6 32⟩,
  ⟨79, 4, .aluImm .add true 2 32⟩,
  ⟨83, 4, .aluImm .add true 7 32⟩,
  ⟨87, 3, .incDec false true 1⟩,
  ⟨90, 2, .jcc 5 40⟩,
  ⟨92, 4, .vbinOp .vpxor true 0 0 0⟩,
  ⟨96, 4, .vbinOp .vpxor true 1 1 1⟩,
  ⟨100, 4, .vbinOp .vpxor true 2 2 2⟩,
  ⟨104, 5, .vbinOp .vpxor true 14 14 14⟩,
  ⟨109, 5, .vbinOp .vpxor true 15 15 15⟩,
  ⟨114, 3, .vzeroall⟩,
  ⟨117, 3, .vzeroupper⟩,
  ⟨120, 2, .aluRegReg .xorOp false 7 7⟩,
  ⟨122, 2, .aluRegReg .xorOp false 6 6⟩,
  ⟨124, 2, .aluRegReg .xorOp false 2 2⟩,
  ⟨126, 2, .aluRegReg .xorOp false 1 1⟩,
  ⟨128, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨131, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨134, 3, .aluRegReg .xorOp false 10 10⟩,
  ⟨137, 3, .aluRegReg .xorOp false 11 11⟩,
  ⟨140, 2, .aluRegReg .xorOp false 0 0⟩,
  ⟨142, 1, .ret⟩
]

private theorem current_vzeroall_step (off len pc : Nat) (g : Bank16 UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    (stepX86 ⟨off, len, .vzeroall⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g, Bank16.const Vec256.zero, cf, o, zf, false, false, m⟩ := rfl

private theorem current_vzeroupper_zero_step (off len pc : Nat) (g : Bank16 UInt64)
    (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    (stepX86 ⟨off, len, .vzeroupper⟩
      ⟨pc, g, Bank16.const Vec256.zero, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g, Bank16.const Vec256.zero, cf, o, zf, false, false, m⟩ := rfl

private theorem current_gf256MulGfni_reaches_full (k : Nat) (hk : k + 1 < 0x10000000000000000)
    (r0 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Vec256)
    (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    ∃ cf' o' zf',
      ExecReachesX86 current_gf256MulGfniProg (34 + 12 * k)
        ⟨0, ⟨r0, UInt64.ofNat (k + 1), r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
          ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
          cf, o, zf, dy, false, m⟩
        ⟨142,
          ⟨0, 0, 0, r3, r4, r5, 0, 0, 0, 0, 0, 0, r12, r13, r14, r15⟩,
          Bank16.const Vec256.zero,
          cf', o', zf', false, false, gf256MulGfniIterMem (k + 1) m r7 r6 r2⟩ := by
  obtain ⟨cf', o', zf', hCore⟩ := gf256MulGfniCore_reaches k hk
    r0 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
    y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 cf o zf dy m
  have hPres : progPreservesNonRet gf256MulGfniCoreProg current_gf256MulGfniProg = true := by decide +kernel
  have hTrans := ExecReachesX86_transfer_nonret hPres hCore.toExecReaches rfl
  have hTail : ExecReachesX86 current_gf256MulGfniProg 11
      ⟨114,
        ⟨gfniRijndaelToTowerMat, 0, r2 + UInt64.ofNat (32 * (k + 1)), r3, r4, r5,
          r6 + UInt64.ofNat (32 * (k + 1)), r7 + UInt64.ofNat (32 * (k + 1)),
          r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨Vec256.zero, Vec256.zero, Vec256.zero, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13,
          Vec256.zero, Vec256.zero⟩,
        cf', o', zf', true, false, gf256MulGfniIterMem (k + 1) m r7 r6 r2⟩
        ⟨142,
          ⟨0, 0, 0, r3, r4, r5, 0, 0, 0, 0, 0, 0, r12, r13, r14, r15⟩,
          Bank16.const Vec256.zero,
          false, false, true, false, false, gf256MulGfniIterMem (k + 1) m r7 r6 r2⟩ := by
    apply StepsX86.toExecReaches
    iterate 11
      apply StepsX86.cons rfl rfl
      · simp only [current_vzeroall_step, current_vzeroupper_zero_step, stepX86_xorRR, mask32_xor_self, u64_zero_beq_zero,
          b16set_0, b16set_1, b16set_2, b16set_6, b16set_7,
          b16set_8, b16set_9, b16set_10, b16set_11]
        rfl
    exact StepsX86.zero _
  have hFull := ExecReachesX86_trans hTrans hTail
  have hStepEq : (23 + 12 * k) + 11 = 34 + 12 * k := by omega
  rw [hStepEq] at hFull
  exact ⟨false, false, true, hFull⟩


theorem current_rlib_gf256_shamir_mul_gfni_functional_and_ct :
    ∃ slice m,
      extractRlibFuncBytes currentX86RlibArchiveBytes "qsag_asm_gf256_shamir_mul_gfni" = some slice ∧
      m ∈ parseArArchive currentX86RlibArchiveBytes ∧
      ArPayloadOk currentX86RlibArchiveBytes m ∧
      checkElfFuncThreeWayNI m.payload "qsag_asm_gf256_shamir_mul_gfni"
        (mkContract "qsag_asm_gf256_shamir_mul_gfni" [4, 7, 6, 2, 1]) = true ∧
      ElfSliceThreeWayNISafe slice (mkContract "qsag_asm_gf256_shamir_mul_gfni" [4, 7, 6, 2, 1]) ∧
      decodeX86Slice slice.code = some current_gf256MulGfniProg ∧
      ∀ (st : X86BvState), st.pc = 0 → st.halted = false → st.gpr.get 1 = 1#64 →
        (∃ st24 tr24, execDecodedX86 slice.code 34 st = some (st24, tr24) ∧ st24.halted = false) ∧
        ∀ extra : Nat, ∃ st' trace,
          execDecodedX86 slice.code (35 + extra) st = some (st', trace) ∧
          st'.halted = true ∧ st'.pc = 142 ∧ trace.length = 35 ∧
          st'.ymmDirty = false ∧
          st'.gpr.get 1 = 0#64 ∧
          st'.gpr.get 7 = 0#64 ∧
          st'.gpr.get 6 = 0#64 ∧
          st'.gpr.get 2 = 0#64 ∧
          st'.ymm.get 0 = Vec256.zero ∧ st'.ymm.get 1 = Vec256.zero ∧
          st'.ymm.get 2 = Vec256.zero ∧ st'.ymm.get 14 = Vec256.zero ∧
          st'.ymm.get 15 = Vec256.zero ∧
          X86CalleeSavedPreserved st st' ∧
          (∀ k : Nat, k < 32 →
            st'.mem (st.gpr.get 7 + BitVec.ofNat 64 k) =
              gfniTowerMulByte (st.mem (st.gpr.get 6 + BitVec.ofNat 64 k))
                               (st.mem (st.gpr.get 2 + BitVec.ofNat 64 k)) ∧
            Simulates 3
              (towerMul 3 (unpackTower 3 (st.mem (st.gpr.get 6 + BitVec.ofNat 64 k)).toBitVec)
                          (unpackTower 3 (st.mem (st.gpr.get 2 + BitVec.ofNat 64 k)).toBitVec))
              (st'.mem (st.gpr.get 7 + BitVec.ofNat 64 k)).toBitVec) ∧
          (∀ a : BitVec 64, (∀ k : Nat, k < 32 → a ≠ st.gpr.get 7 + BitVec.ofNat 64 k) →
            st'.mem a = st.mem a) := by
  cases hFind : currentX86ExtractedSlices.find? (fun s => s.name == "qsag_asm_gf256_shamir_mul_gfni") with
  | none => exfalso; revert hFind; decide +kernel
  | some slice =>
    have hExt : extractRlibFuncBytes currentX86RlibArchiveBytes "qsag_asm_gf256_shamir_mul_gfni" = some slice := by
      rw [current_extractRlibFuncBytes_x86_eq, hFind]
    have hNI : checkElfSliceThreeWayNI slice (mkContract "qsag_asm_gf256_shamir_mul_gfni" [4, 7, 6, 2, 1]) = true := by
      have hCheck : ((currentX86ExtractedSlices.find? (fun s => s.name == "qsag_asm_gf256_shamir_mul_gfni")).map
          (fun sl => checkElfSliceThreeWayNI sl (mkContract "qsag_asm_gf256_shamir_mul_gfni" [4, 7, 6, 2, 1]))) =
          some true := by decide +kernel
      rw [hFind] at hCheck
      exact Option.some.inj hCheck
    have hDec : decodeX86Slice slice.code = some current_gf256MulGfniProg := by
      have hD : (currentX86ExtractedSlices.find? (fun s => s.name == "qsag_asm_gf256_shamir_mul_gfni")).bind
          (fun sl => decodeX86Slice sl.code) = some current_gf256MulGfniProg := by decide +kernel
      rw [hFind] at hD
      exact hD
    obtain ⟨m, hm, hPay, _, hMemNI, _, hSafe⟩ :=
      extractRlibFuncBytes_member_ni_sound current_x86_rlib_distinct_names hExt hNI
    refine ⟨slice, m, hExt, hm, hPay, hMemNI, hSafe, hDec, ?_⟩
    intro st hpc hh hrcx
    rcases st with ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
      ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
      cf, o, zf, dy, hlt, mem⟩
    dsimp only at hpc hh; subst hpc hh
    have hr1 : r1 = 1#64 := hrcx; subst hr1
    let st0 : X86BvState :=
      ⟨0, ⟨r0, 1#64, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
       ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
       cf, o, zf, dy, false, mem⟩
    obtain ⟨cf', o', zf', hR⟩ := current_gf256MulGfni_reaches_full 0 (by decide)
      (UInt64.ofBitVec r0) (UInt64.ofBitVec r2) (UInt64.ofBitVec r3) (UInt64.ofBitVec r4)
      (UInt64.ofBitVec r5) (UInt64.ofBitVec r6) (UInt64.ofBitVec r7) (UInt64.ofBitVec r8)
      (UInt64.ofBitVec r9) (UInt64.ofBitVec r10) (UInt64.ofBitVec r11) (UInt64.ofBitVec r12)
      (UInt64.ofBitVec r13) (UInt64.ofBitVec r14) (UInt64.ofBitVec r15)
      y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 cf o zf dy (fun a => mem a.toBitVec)
    obtain ⟨hPre, hPost⟩ := execDecodedX86_ret_of_reaches st0 hDec rfl hR rfl rfl
    refine ⟨hPre, fun extra => ?_⟩
    obtain ⟨tr, hExec, hL⟩ := hPost extra
    have hOfNatBv : ∀ (x : BitVec 64) (k : Nat), k < 32 →
        (UInt64.ofBitVec x + UInt64.ofNat k) = UInt64.ofBitVec (x + BitVec.ofNat 64 k) := by
      intro x k _
      apply UInt64.eq_of_toBitVec_eq
      simp only [UInt64.toBitVec_add]
      congr 1
    refine ⟨_, tr, hExec, rfl, rfl, hL, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, x86_callee_saved_of_roundtrip, ?_, ?_⟩
    · intro k hk
      dsimp only [X86BvState.ofX86State, gf256MulGfniIterMem]
      simp only [b16get_7, b16get_6, b16get_2]
      rw [← hOfNatBv r7 k hk, gf256MulGfniStepMem_at _ _ _ _ k hk]
      have hA : ((UInt64.ofBitVec r6 + UInt64.ofNat k).toBitVec) = r6 + BitVec.ofNat 64 k := by
        rw [hOfNatBv r6 k hk, u64_roundtrip]
      have hB : ((UInt64.ofBitVec r2 + UInt64.ofNat k).toBitVec) = r2 + BitVec.ofNat 64 k := by
        rw [hOfNatBv r2 k hk, u64_roundtrip]
      rw [hA, hB]
      exact ⟨rfl, gfniTowerMulByte_simulates_binaryTower _ _⟩
    · intro a ha
      dsimp only [X86BvState.ofX86State, gf256MulGfniIterMem]
      rw [gf256MulGfniStepMem_outside _ _ _ _ (UInt64.ofBitVec a) (fun k hk heq => by
        rw [hOfNatBv r7 k hk] at heq
        have hb := congrArg UInt64.toBitVec heq
        rw [u64_roundtrip, u64_roundtrip] at hb
        exact ha k hk hb), u64_roundtrip]

theorem current_rlib_gf256_shamir_mul_gfni_loop_functional :
    ∃ slice,
      extractRlibFuncBytes currentX86RlibArchiveBytes "qsag_asm_gf256_shamir_mul_gfni" = some slice ∧
      ElfSliceThreeWayNISafe slice (mkContract "qsag_asm_gf256_shamir_mul_gfni" [4, 7, 6, 2, 1]) ∧
      ∀ (k : Nat), 32 * (k + 1) ≤ 0x10000000000000000 →
      ∀ (st : X86BvState), st.pc = 0 → st.halted = false →
        st.gpr.get 1 = BitVec.ofNat 64 (k + 1) →
        ∀ extra : Nat, ∃ st' trace,
          execDecodedX86 slice.code ((35 + 12 * k) + extra) st = some (st', trace) ∧
          st'.halted = true ∧ st'.pc = 142 ∧ trace.length = 35 + 12 * k ∧
          st'.ymmDirty = false ∧
          st'.gpr.get 1 = 0#64 ∧
          st'.gpr.get 7 = 0#64 ∧
          st'.gpr.get 6 = 0#64 ∧
          st'.gpr.get 2 = 0#64 ∧
          X86CalleeSavedPreserved st st' ∧
          ((∀ i j : Nat, i < 32 * (k + 1) → j < 32 * (k + 1) →
              st.gpr.get 7 + BitVec.ofNat 64 i ≠ st.gpr.get 6 + BitVec.ofNat 64 j ∧
              st.gpr.get 7 + BitVec.ofNat 64 i ≠ st.gpr.get 2 + BitVec.ofNat 64 j) →
            (∀ idx : Nat, idx < 32 * (k + 1) →
              Simulates 3
                (towerMul 3 (unpackTower 3 (st.mem (st.gpr.get 6 + BitVec.ofNat 64 idx)).toBitVec)
                            (unpackTower 3 (st.mem (st.gpr.get 2 + BitVec.ofNat 64 idx)).toBitVec))
                (st'.mem (st.gpr.get 7 + BitVec.ofNat 64 idx)).toBitVec)) ∧
          (∀ a : BitVec 64, (∀ idx : Nat, idx < 32 * (k + 1) → a ≠ st.gpr.get 7 + BitVec.ofNat 64 idx) →
            st'.mem a = st.mem a) := by
  obtain ⟨slice, _, hExt, _, _, _, hSafe, hDec, _⟩ := current_rlib_gf256_shamir_mul_gfni_functional_and_ct
  refine ⟨slice, hExt, hSafe, fun k hk st hpc hh hrcx extra => ?_⟩
  rcases st with ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
    ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
    cf, o, zf, dy, hlt, mem⟩
  dsimp only at hpc hh; subst hpc hh
  have hr1 : r1 = BitVec.ofNat 64 (k + 1) := hrcx; subst hr1
  have hr1U : UInt64.ofBitVec (BitVec.ofNat 64 (k + 1)) = UInt64.ofNat (k + 1) := by
    apply UInt64.eq_of_toBitVec_eq; apply BitVec.eq_of_toNat_eq
    simp [UInt64.toNat_toBitVec, Nat.mod_eq_of_lt (show k + 1 < 0x10000000000000000 by omega)]
  let st0 : X86BvState :=
    ⟨0, ⟨r0, BitVec.ofNat 64 (k + 1), r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
     ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
     cf, o, zf, dy, false, mem⟩
  obtain ⟨cf', o', zf', hR⟩ := current_gf256MulGfni_reaches_full k (by omega)
    (UInt64.ofBitVec r0) (UInt64.ofBitVec r2) (UInt64.ofBitVec r3) (UInt64.ofBitVec r4)
    (UInt64.ofBitVec r5) (UInt64.ofBitVec r6) (UInt64.ofBitVec r7) (UInt64.ofBitVec r8)
    (UInt64.ofBitVec r9) (UInt64.ofBitVec r10) (UInt64.ofBitVec r11) (UInt64.ofBitVec r12)
    (UInt64.ofBitVec r13) (UInt64.ofBitVec r14) (UInt64.ofBitVec r15)
    y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 cf o zf dy (fun a => mem a.toBitVec)
  have hSt0 : st0.toX86State =
      ⟨0, ⟨UInt64.ofBitVec r0, UInt64.ofNat (k + 1), UInt64.ofBitVec r2, UInt64.ofBitVec r3,
           UInt64.ofBitVec r4, UInt64.ofBitVec r5, UInt64.ofBitVec r6, UInt64.ofBitVec r7,
           UInt64.ofBitVec r8, UInt64.ofBitVec r9, UInt64.ofBitVec r10, UInt64.ofBitVec r11,
           UInt64.ofBitVec r12, UInt64.ofBitVec r13, UInt64.ofBitVec r14, UInt64.ofBitVec r15⟩,
       ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
       cf, o, zf, dy, false, fun a => mem a.toBitVec⟩ := by
    simp [st0, X86BvState.toX86State, bank16ToU64, hr1U]
  obtain ⟨_, hPost⟩ := execDecodedX86_ret_of_reaches st0 hDec hSt0 hR rfl rfl
  have hStepN : (34 + 12 * k) + 1 = 35 + 12 * k := by omega
  obtain ⟨tr, hExec, hL⟩ := hPost extra
  rw [hStepN] at hExec hL
  have hOfNatBv : ∀ (x : BitVec 64) (mNat : Nat), mNat ≤ 0x10000000000000000 →
      (mNat < 0x10000000000000000 ∨ mNat = 0x10000000000000000) →
      (UInt64.ofBitVec x + UInt64.ofNat mNat).toBitVec = x + BitVec.ofNat 64 mNat := by
    intro x mNat _ _
    simp only [UInt64.toBitVec_add]
    congr 1
  have hOfNatU : ∀ (x : BitVec 64) (idx : Nat), idx < 32 * (k + 1) →
      UInt64.ofBitVec (x + BitVec.ofNat 64 idx) = UInt64.ofBitVec x + UInt64.ofNat idx := by
    intro x idx hidx
    apply UInt64.eq_of_toBitVec_eq
    rw [u64_roundtrip, hOfNatBv x idx (by omega) (Or.inl (by omega))]
  refine ⟨_, tr, hExec, rfl, rfl, hL, rfl, rfl,
    rfl,
    rfl,
    rfl,
    x86_callee_saved_of_roundtrip, ?_, ?_⟩
  · intro hDisj idx hidx
    dsimp only [X86BvState.ofX86State]
    simp only [b16get_7, b16get_6, b16get_2]
    rw [hOfNatU r7 idx hidx]
    rw [gf256MulGfniIterMem_at (k + 1) _ _ _ _ hk
      (fun i j hi hj heq => by
        have hb := congrArg UInt64.toBitVec heq
        rw [hOfNatBv r7 i (by omega) (Or.inl (by omega)),
            hOfNatBv r6 j (by omega) (Or.inl (by omega))] at hb
        exact (hDisj i j hi hj).1 hb)
      (fun i j hi hj heq => by
        have hb := congrArg UInt64.toBitVec heq
        rw [hOfNatBv r7 i (by omega) (Or.inl (by omega)),
            hOfNatBv r2 j (by omega) (Or.inl (by omega))] at hb
        exact (hDisj i j hi hj).2 hb)
      idx hidx]
    rw [hOfNatBv r6 idx (by omega) (Or.inl (by omega)),
        hOfNatBv r2 idx (by omega) (Or.inl (by omega))]
    exact gfniTowerMulByte_simulates_binaryTower _ _
  · intro a ha
    dsimp only [X86BvState.ofX86State]
    rw [gf256MulGfniIterMem_outside (k + 1) _ _ _ _ (UInt64.ofBitVec a) hk
      (fun idx hidx heq => by
        have hb := congrArg UInt64.toBitVec heq
        rw [u64_roundtrip, hOfNatBv r7 idx (by omega) (Or.inl (by omega))] at hb
        exact ha idx hidx hb), u64_roundtrip]

theorem current_ct_eq_bytes_x86_64_functional_and_ct :
    ∃ slice prog, findSliceByNameBytes currentX86ExtractedSlices ctEqBytesX86Name = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ElfSliceThreeWayNISafe slice currentX86SymbolContracts[14] ∧
      ∀ (s : X86State) (fuel : Nat), s.pc = 0 → s.halted = false → 0 < (s.gpr.get 2).toNat →
        8 * (s.gpr.get 2).toNat + 15 ≤ fuel →
        (runX86 prog fuel s).1.halted = true ∧
        (runX86 prog fuel s).1.gpr.get 0 =
          (if ∀ i : Nat, i < (s.gpr.get 2).toNat →
              s.mem (s.gpr.get 7 + UInt64.ofNat i) = s.mem (s.gpr.get 6 + UInt64.ofNat i)
            then 1 else 0) ∧
        (runX86 prog fuel s).1.mem = s.mem ∧
        (runX86 prog fuel s).1.gpr.get 8 = 0 ∧ (runX86 prog fuel s).1.gpr.get 9 = 0 := by
  obtain ⟨slice, prog, hf, hd, hfun⟩ := current_ct_eq_bytes_x86_64_mc_refines
  have he : findSliceByNameBytes currentX86ExtractedSlices ctEqBytesX86Name =
      some currentX86ExtractedSlices[14] := by decide +kernel
  have hs : slice = currentX86ExtractedSlices[14] := Option.some.inj (hf.symm.trans he)
  refine ⟨slice, prog, hf, hd, ?_, hfun⟩
  rw [hs]
  apply checkElfSliceWithCert_sound (cert := currentX86InvCerts[14])
  exact currentX86_symbol_14_certificate


/-! Fresh Goldilocks pow7 and dot2: arithmetic, full wipe epilogues, and archive bindings. -/

def current_goldPow7X86Prog : List (DecodedInstr X86Instr) := [
  ⟨0, 3, .movRegReg true 11 7⟩,
  ⟨3, 6, .movImm false 10 4294967295⟩,
  ⟨9, 3, .movRegReg true 2 11⟩, ⟨12, 5, .mulx 1 0 11⟩, ⟨17, 3, .movRegReg true 2 1⟩,
  ⟨20, 4, .shiftImm .shr true 1 32⟩, ⟨24, 2, .movRegReg false 2 2⟩,
  ⟨26, 3, .aluRegReg .sub true 0 1⟩, ⟨29, 3, .aluRegReg .sbb false 8 8⟩,
  ⟨32, 3, .aluRegReg .sub true 0 8⟩, ⟨35, 3, .movRegReg true 9 2⟩,
  ⟨38, 4, .shiftImm .shl true 9 32⟩, ⟨42, 3, .aluRegReg .sub true 9 2⟩,
  ⟨45, 3, .aluRegReg .add true 0 9⟩, ⟨48, 3, .aluRegReg .sbb false 8 8⟩,
  ⟨51, 3, .aluRegReg .add true 0 8⟩, ⟨54, 3, .movRegReg true 8 0⟩,
  ⟨57, 3, .aluRegReg .add true 8 10⟩, ⟨60, 3, .aluRegReg .sbb true 1 1⟩,
  ⟨63, 3, .aluRegReg .andOp true 1 10⟩, ⟨66, 3, .aluRegReg .add true 0 1⟩,
  ⟨69, 3, .movRegReg true 2 0⟩, ⟨72, 5, .mulx 1 0 11⟩, ⟨77, 3, .movRegReg true 2 1⟩,
  ⟨80, 4, .shiftImm .shr true 1 32⟩, ⟨84, 2, .movRegReg false 2 2⟩,
  ⟨86, 3, .aluRegReg .sub true 0 1⟩, ⟨89, 3, .aluRegReg .sbb false 8 8⟩,
  ⟨92, 3, .aluRegReg .sub true 0 8⟩, ⟨95, 3, .movRegReg true 9 2⟩,
  ⟨98, 4, .shiftImm .shl true 9 32⟩, ⟨102, 3, .aluRegReg .sub true 9 2⟩,
  ⟨105, 3, .aluRegReg .add true 0 9⟩, ⟨108, 3, .aluRegReg .sbb false 8 8⟩,
  ⟨111, 3, .aluRegReg .add true 0 8⟩, ⟨114, 3, .movRegReg true 8 0⟩,
  ⟨117, 3, .aluRegReg .add true 8 10⟩, ⟨120, 3, .aluRegReg .sbb true 1 1⟩,
  ⟨123, 3, .aluRegReg .andOp true 1 10⟩, ⟨126, 3, .aluRegReg .add true 0 1⟩,
  ⟨129, 3, .movRegReg true 2 0⟩, ⟨132, 5, .mulx 1 0 0⟩, ⟨137, 3, .movRegReg true 2 1⟩,
  ⟨140, 4, .shiftImm .shr true 1 32⟩, ⟨144, 2, .movRegReg false 2 2⟩,
  ⟨146, 3, .aluRegReg .sub true 0 1⟩, ⟨149, 3, .aluRegReg .sbb false 8 8⟩,
  ⟨152, 3, .aluRegReg .sub true 0 8⟩, ⟨155, 3, .movRegReg true 9 2⟩,
  ⟨158, 4, .shiftImm .shl true 9 32⟩, ⟨162, 3, .aluRegReg .sub true 9 2⟩,
  ⟨165, 3, .aluRegReg .add true 0 9⟩, ⟨168, 3, .aluRegReg .sbb false 8 8⟩,
  ⟨171, 3, .aluRegReg .add true 0 8⟩, ⟨174, 3, .movRegReg true 8 0⟩,
  ⟨177, 3, .aluRegReg .add true 8 10⟩, ⟨180, 3, .aluRegReg .sbb true 1 1⟩,
  ⟨183, 3, .aluRegReg .andOp true 1 10⟩, ⟨186, 3, .aluRegReg .add true 0 1⟩,
  ⟨189, 3, .movRegReg true 2 0⟩, ⟨192, 5, .mulx 1 0 11⟩, ⟨197, 3, .movRegReg true 2 1⟩,
  ⟨200, 4, .shiftImm .shr true 1 32⟩, ⟨204, 2, .movRegReg false 2 2⟩,
  ⟨206, 3, .aluRegReg .sub true 0 1⟩, ⟨209, 3, .aluRegReg .sbb false 8 8⟩,
  ⟨212, 3, .aluRegReg .sub true 0 8⟩, ⟨215, 3, .movRegReg true 9 2⟩,
  ⟨218, 4, .shiftImm .shl true 9 32⟩, ⟨222, 3, .aluRegReg .sub true 9 2⟩,
  ⟨225, 3, .aluRegReg .add true 0 9⟩, ⟨228, 3, .aluRegReg .sbb false 8 8⟩,
  ⟨231, 3, .aluRegReg .add true 0 8⟩, ⟨234, 3, .movRegReg true 8 0⟩,
  ⟨237, 3, .aluRegReg .add true 8 10⟩, ⟨240, 3, .aluRegReg .sbb true 1 1⟩,
  ⟨243, 3, .aluRegReg .andOp true 1 10⟩, ⟨246, 3, .aluRegReg .add true 0 1⟩,
  ⟨249, 2, .aluRegReg .xorOp false 1 1⟩, ⟨251, 2, .aluRegReg .xorOp false 2 2⟩,
  ⟨253, 3, .aluRegReg .xorOp false 8 8⟩, ⟨256, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨259, 3, .aluRegReg .xorOp false 10 10⟩, ⟨262, 3, .aluRegReg .xorOp false 11 11⟩,
  ⟨265, 2, .aluRegReg .xorOp false 7 7⟩,
  ⟨267, 2, .aluRegReg .xorOp false 6 6⟩,
  ⟨269, 2, .aluRegReg .xorOp false 2 2⟩,
  ⟨271, 2, .aluRegReg .xorOp false 1 1⟩,
  ⟨273, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨276, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨279, 3, .aluRegReg .xorOp false 10 10⟩,
  ⟨282, 3, .aluRegReg .xorOp false 11 11⟩,
  ⟨285, 1, .ret⟩]

private theorem current_pow7_setup_and_b1 (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    ∃ s2, ExecReachesX86 current_goldPow7X86Prog 21
        ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
          y, cf, o, zf, dy, false, m⟩ s2 ∧
      ∃ r1' r2' r8' r9' cf' o' zf',
        s2 = ⟨69, ⟨goldMulMc r7 r7, r1', r2', r3, r4, r5, r6, r7, r8', r9',
          maskGprWidth false 4294967295, r7, r12, r13, r14, r15⟩,
          y, cf', o', zf', dy, false, m⟩ := by
  suffices hS : ∃ s2, StepsX86 current_goldPow7X86Prog 21
        ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
          y, cf, o, zf, dy, false, m⟩ s2 ∧
      ∃ r1' r2' r8' r9' cf' o' zf',
        s2 = ⟨69, ⟨goldMulMc r7 r7, r1', r2', r3, r4, r5, r6, r7, r8', r9',
          maskGprWidth false 4294967295, r7, r12, r13, r14, r15⟩,
          y, cf', o', zf', dy, false, m⟩ by
    rcases hS with ⟨s2, hs, hp⟩
    exact ⟨s2, hs.toExecReaches, hp⟩
  iterate 21
    apply StepsX86_step_ex rfl rfl
    · simp only [stepX86_movRR, stepX86_mulx, stepX86_shr64, stepX86_shl64, stepX86_addRR64,
        stepX86_subRR64, stepX86_sbbRR, stepX86_andRR, stepX86_movImm,
        maskGprWidth_true, sbb32_self, sbb64_self, uint64_evalAdd_eq, uint64_evalSub_eq,
        b16get_0, b16get_1, b16get_2, b16get_7, b16get_8, b16get_9, b16get_10, b16get_11,
        b16set_0, b16set_1, b16set_2, b16set_8, b16set_9, b16set_10, b16set_11]
      rfl
  exact ⟨_, StepsX86.zero _, _, _, _, _, _, _, _, rfl⟩

private theorem current_pow7_b2 (acc r1 r2 r3 r4 r5 r6 r7 r8 r9 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    ∃ s2, ExecReachesX86 current_goldPow7X86Prog 19
        ⟨69, ⟨acc, r1, r2, r3, r4, r5, r6, r7, r8, r9,
          maskGprWidth false 4294967295, r7, r12, r13, r14, r15⟩,
          y, cf, o, zf, dy, false, m⟩ s2 ∧
      ∃ r1' r2' r8' r9' cf' o' zf',
        s2 = ⟨129, ⟨goldMulMc acc r7, r1', r2', r3, r4, r5, r6, r7, r8', r9',
          maskGprWidth false 4294967295, r7, r12, r13, r14, r15⟩,
          y, cf', o', zf', dy, false, m⟩ := by
  suffices hS : ∃ s2, StepsX86 current_goldPow7X86Prog 19
        ⟨69, ⟨acc, r1, r2, r3, r4, r5, r6, r7, r8, r9,
          maskGprWidth false 4294967295, r7, r12, r13, r14, r15⟩,
          y, cf, o, zf, dy, false, m⟩ s2 ∧
      ∃ r1' r2' r8' r9' cf' o' zf',
        s2 = ⟨129, ⟨goldMulMc acc r7, r1', r2', r3, r4, r5, r6, r7, r8', r9',
          maskGprWidth false 4294967295, r7, r12, r13, r14, r15⟩,
          y, cf', o', zf', dy, false, m⟩ by
    rcases hS with ⟨s2, hs, hp⟩
    exact ⟨s2, hs.toExecReaches, hp⟩
  iterate 19
    apply StepsX86_step_ex rfl rfl
    · simp only [stepX86_movRR, stepX86_mulx, stepX86_shr64, stepX86_shl64, stepX86_addRR64,
        stepX86_subRR64, stepX86_sbbRR, stepX86_andRR,
        maskGprWidth_true, sbb32_self, sbb64_self, uint64_evalAdd_eq, uint64_evalSub_eq,
        b16get_0, b16get_1, b16get_2, b16get_8, b16get_9, b16get_10, b16get_11,
        b16set_0, b16set_1, b16set_2, b16set_8, b16set_9]
      rfl
  exact ⟨_, StepsX86.zero _, _, _, _, _, _, _, _, rfl⟩

private theorem current_pow7_b3 (acc r1 r2 r3 r4 r5 r6 r7 r8 r9 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    ∃ s2, ExecReachesX86 current_goldPow7X86Prog 19
        ⟨129, ⟨acc, r1, r2, r3, r4, r5, r6, r7, r8, r9,
          maskGprWidth false 4294967295, r7, r12, r13, r14, r15⟩,
          y, cf, o, zf, dy, false, m⟩ s2 ∧
      ∃ r1' r2' r8' r9' cf' o' zf',
        s2 = ⟨189, ⟨goldMulMc acc acc, r1', r2', r3, r4, r5, r6, r7, r8', r9',
          maskGprWidth false 4294967295, r7, r12, r13, r14, r15⟩,
          y, cf', o', zf', dy, false, m⟩ := by
  suffices hS : ∃ s2, StepsX86 current_goldPow7X86Prog 19
        ⟨129, ⟨acc, r1, r2, r3, r4, r5, r6, r7, r8, r9,
          maskGprWidth false 4294967295, r7, r12, r13, r14, r15⟩,
          y, cf, o, zf, dy, false, m⟩ s2 ∧
      ∃ r1' r2' r8' r9' cf' o' zf',
        s2 = ⟨189, ⟨goldMulMc acc acc, r1', r2', r3, r4, r5, r6, r7, r8', r9',
          maskGprWidth false 4294967295, r7, r12, r13, r14, r15⟩,
          y, cf', o', zf', dy, false, m⟩ by
    rcases hS with ⟨s2, hs, hp⟩
    exact ⟨s2, hs.toExecReaches, hp⟩
  iterate 19
    apply StepsX86_step_ex rfl rfl
    · simp only [stepX86_movRR, stepX86_mulx, stepX86_shr64, stepX86_shl64, stepX86_addRR64,
        stepX86_subRR64, stepX86_sbbRR, stepX86_andRR,
        maskGprWidth_true, sbb32_self, sbb64_self, uint64_evalAdd_eq, uint64_evalSub_eq,
        b16get_0, b16get_1, b16get_2, b16get_8, b16get_9, b16get_10,
        b16set_0, b16set_1, b16set_2, b16set_8, b16set_9]
      rfl
  exact ⟨_, StepsX86.zero _, _, _, _, _, _, _, _, rfl⟩

private theorem current_pow7_b4_and_wipe (acc r1 r2 r3 r4 r5 r6 r7 r8 r9 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    ExecReachesX86 current_goldPow7X86Prog 33
      ⟨189, ⟨acc, r1, r2, r3, r4, r5, r6, r7, r8, r9,
        maskGprWidth false 4294967295, r7, r12, r13, r14, r15⟩,
        y, cf, o, zf, dy, false, m⟩
      ⟨285, ⟨goldMulMc acc r7, 0, 0, r3, r4, r5, 0, 0, 0, 0, 0, 0, r12, r13, r14, r15⟩,
        y, false, false, true, dy, false, m⟩ := by
  apply StepsX86.toExecReaches
  iterate 33
    apply StepsX86.cons rfl rfl
    · simp only [stepX86_movRR, stepX86_mulx, stepX86_shr64, stepX86_shl64, stepX86_addRR64,
        stepX86_subRR64, stepX86_sbbRR, stepX86_andRR, stepX86_xorRR,
        maskGprWidth_true, mask32_xor_self, u64_zero_beq_zero, sbb32_self, sbb64_self,
        uint64_evalAdd_eq, uint64_evalSub_eq,
        b16get_0, b16get_1, b16get_2, b16get_8, b16get_9, b16get_10, b16get_11,
        b16set_6, b16set_7, b16get_6, b16get_7, b16set_0, b16set_1, b16set_2, b16set_8, b16set_9, b16set_10, b16set_11]
      rfl
  exact StepsX86.zero _

theorem current_rlib_goldilocks_pow7_ct_x86_64_functional_and_ct (st : X86BvState) (hpc : st.pc = 0) (hh : st.halted = false) :
    ∃ slice m,
      extractRlibFuncBytes currentX86RlibArchiveBytes "qsag_asm_goldilocks_pow7_ct_x86_64" = some slice ∧
      m ∈ parseArArchive currentX86RlibArchiveBytes ∧
      ArPayloadOk currentX86RlibArchiveBytes m ∧
      checkElfFuncThreeWayNI m.payload "qsag_asm_goldilocks_pow7_ct_x86_64"
        currentX86SymbolContracts[11] = true ∧
      ElfSliceThreeWayNISafe slice
        currentX86SymbolContracts[11] ∧
      decodeX86Slice slice.code = some current_goldPow7X86Prog ∧
        (∃ st84 tr84, execDecodedX86 slice.code 92 st = some (st84, tr84) ∧ st84.halted = false) ∧
        ∀ extra : Nat, ∃ st' trace,
          execDecodedX86 slice.code (93 + extra) st = some (st', trace) ∧
          st'.halted = true ∧ st'.pc = 285 ∧ trace.length = 93 ∧
          st'.gpr.get 0 = BitVec.ofNat 64 (((st.gpr.get 7).toNat ^ 7) % GOLDILOCKS_P) ∧
          X86CalleeSavedPreserved st st' ∧
          st'.mem = st.mem ∧
          st'.gpr.get 1 = 0#64 ∧ st'.gpr.get 2 = 0#64 ∧ st'.gpr.get 8 = 0#64 ∧
          st'.gpr.get 9 = 0#64 ∧ st'.gpr.get 10 = 0#64 ∧ st'.gpr.get 11 = 0#64 ∧ st'.gpr.get 6 = 0#64 ∧ st'.gpr.get 7 = 0#64 := by
  cases hFind : currentX86ExtractedSlices.find? (fun s => s.name == "qsag_asm_goldilocks_pow7_ct_x86_64") with
  | none => exfalso; revert hFind; decide +kernel
  | some slice =>
    have hExt : extractRlibFuncBytes currentX86RlibArchiveBytes "qsag_asm_goldilocks_pow7_ct_x86_64" = some slice := by
      rw [current_extractRlibFuncBytes_x86_eq, hFind]
    have hNI : checkElfSliceThreeWayNI slice
        currentX86SymbolContracts[11] = true := by
      have hCheck : ((currentX86ExtractedSlices.find? (fun s => s.name == "qsag_asm_goldilocks_pow7_ct_x86_64")).map
          (fun sl => checkElfSliceThreeWayNI sl
            currentX86SymbolContracts[11])) =
          some true := by decide +kernel
      rw [hFind] at hCheck
      exact Option.some.inj hCheck
    have hDec : decodeX86Slice slice.code = some current_goldPow7X86Prog := by
      have hD : (currentX86ExtractedSlices.find? (fun s => s.name == "qsag_asm_goldilocks_pow7_ct_x86_64")).bind
          (fun sl => decodeX86Slice sl.code) = some current_goldPow7X86Prog := by decide +kernel
      rw [hFind] at hD
      exact hD
    obtain ⟨m, hm, hPay, _, hMemNI, _, hSafe⟩ :=
      extractRlibFuncBytes_member_ni_sound current_x86_rlib_distinct_names hExt hNI
    refine ⟨slice, m, hExt, hm, hPay, hMemNI, hSafe, hDec, ?_⟩
    rcases st with ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
      y, cf, o, zf, dy, hlt, mem⟩
    dsimp only at hpc hh; subst hpc hh
    let st0 : X86BvState := ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, mem⟩
    obtain ⟨_, hb1, r1a, r2a, r8a, r9a, cfa, ofa, zfa, rfl⟩ :=
      current_pow7_setup_and_b1 (UInt64.ofBitVec r0) (UInt64.ofBitVec r1) (UInt64.ofBitVec r2)
        (UInt64.ofBitVec r3) (UInt64.ofBitVec r4) (UInt64.ofBitVec r5) (UInt64.ofBitVec r6)
        (UInt64.ofBitVec r7) (UInt64.ofBitVec r8) (UInt64.ofBitVec r9) (UInt64.ofBitVec r10)
        (UInt64.ofBitVec r11) (UInt64.ofBitVec r12) (UInt64.ofBitVec r13) (UInt64.ofBitVec r14)
        (UInt64.ofBitVec r15) y cf o zf dy (fun a => mem a.toBitVec)
    let u3 := UInt64.ofBitVec r3; let u4 := UInt64.ofBitVec r4
    let u5 := UInt64.ofBitVec r5; let u6 := UInt64.ofBitVec r6
    let u7 := UInt64.ofBitVec r7; let u12 := UInt64.ofBitVec r12
    let u13 := UInt64.ofBitVec r13; let u14 := UInt64.ofBitVec r14
    let u15 := UInt64.ofBitVec r15
    obtain ⟨_, hb2, r1b, r2b, r8b, r9b, cfb, ofb, zfb, rfl⟩ :=
      current_pow7_b2 (goldMulMc u7 u7) r1a r2a u3 u4 u5 u6 u7 r8a r9a u12 u13 u14 u15
        y cfa ofa zfa dy (fun a => mem a.toBitVec)
    obtain ⟨_, hb3, r1c, r2c, r8c, r9c, cfc, ofc, zfc, rfl⟩ :=
      current_pow7_b3 (goldMulMc (goldMulMc u7 u7) u7) r1b r2b u3 u4 u5 u6 u7 r8b r9b u12 u13 u14 u15
        y cfb ofb zfb dy (fun a => mem a.toBitVec)
    have hb4 :=
      current_pow7_b4_and_wipe (goldMulMc (goldMulMc (goldMulMc u7 u7) u7) (goldMulMc (goldMulMc u7 u7) u7))
        r1c r2c u3 u4 u5 u6 u7 r8c r9c u12 u13 u14 u15 y cfc ofc zfc dy (fun a => mem a.toBitVec)
    have h84 : ExecReachesX86 current_goldPow7X86Prog 92 _ _ :=
      ExecReachesX86_trans (ExecReachesX86_trans (ExecReachesX86_trans hb1 hb2) hb3) hb4
    obtain ⟨hPre, hPost⟩ := execDecodedX86_ret_of_reaches st0 hDec rfl h84 rfl rfl
    refine ⟨hPre, fun extra => ?_⟩
    obtain ⟨tr, hExec, hL⟩ := hPost extra
    refine ⟨_, tr, hExec, rfl, rfl, hL, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · change (goldMulMc (goldMulMc (goldMulMc (goldMulMc u7 u7) u7) (goldMulMc (goldMulMc u7 u7) u7)) u7).toBitVec =
        BitVec.ofNat 64 ((r7.toNat ^ 7) % GOLDILOCKS_P)
      apply bv_ofU64_eq_ofNat _ (mod_goldilocks_lt_u64 _)
      rw [goldPow7Mc_toNat, UInt64.toNat_ofBitVec]
    · exact x86_callee_saved_of_roundtrip
    · exact mem_roundtrip mem


def current_goldDot2X86Prog : List (DecodedInstr X86Instr) := [
  ⟨0, 3, .movRegReg true 10 2⟩,
  ⟨3, 2, .aluRegReg .xorOp false 0 0⟩,
  ⟨5, 3, .movRegReg true 2 7⟩,
  ⟨8, 5, .mulx 9 8 6⟩,
  ⟨13, 3, .movRegReg true 2 10⟩,
  ⟨16, 5, .mulx 11 10 1⟩,
  ⟨21, 6, .adcx 8 10⟩,
  ⟨27, 6, .adcx 9 11⟩,
  ⟨33, 6, .adox 0 0⟩,
  ⟨39, 6, .adcx 0 0⟩,
  ⟨45, 3, .negReg true 0⟩,
  ⟨48, 10, .movImm true 11 18446744065119617025⟩,
  ⟨58, 3, .aluRegReg .andOp true 11 0⟩,
  ⟨61, 3, .movRegReg true 0 8⟩,
  ⟨64, 3, .movRegReg true 2 9⟩,
  ⟨67, 4, .shiftImm .shr true 9 32⟩,
  ⟨71, 2, .movRegReg false 2 2⟩,
  ⟨73, 3, .aluRegReg .sub true 0 9⟩,
  ⟨76, 3, .aluRegReg .sbb false 8 8⟩,
  ⟨79, 3, .aluRegReg .sub true 0 8⟩,
  ⟨82, 3, .movRegReg true 9 2⟩,
  ⟨85, 4, .shiftImm .shl true 9 32⟩,
  ⟨89, 3, .aluRegReg .sub true 9 2⟩,
  ⟨92, 3, .aluRegReg .add true 0 9⟩,
  ⟨95, 3, .aluRegReg .sbb false 8 8⟩,
  ⟨98, 3, .aluRegReg .add true 0 8⟩,
  ⟨101, 3, .aluRegReg .add true 0 11⟩,
  ⟨104, 3, .aluRegReg .sbb false 8 8⟩,
  ⟨107, 3, .aluRegReg .add true 0 8⟩,
  ⟨110, 3, .aluRegReg .sbb false 10 10⟩,
  ⟨113, 3, .aluRegReg .add true 0 10⟩,
  ⟨116, 6, .movImm false 9 4294967295⟩,
  ⟨122, 3, .movRegReg true 8 0⟩,
  ⟨125, 3, .aluRegReg .add true 8 9⟩,
  ⟨128, 3, .aluRegReg .sbb true 1 1⟩,
  ⟨131, 3, .aluRegReg .andOp true 1 9⟩,
  ⟨134, 3, .aluRegReg .add true 0 1⟩,
  ⟨137, 2, .aluRegReg .xorOp false 1 1⟩,
  ⟨139, 2, .aluRegReg .xorOp false 2 2⟩,
  ⟨141, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨144, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨147, 3, .aluRegReg .xorOp false 10 10⟩,
  ⟨150, 3, .aluRegReg .xorOp false 11 11⟩,
  ⟨153, 2, .aluRegReg .xorOp false 7 7⟩,
  ⟨155, 2, .aluRegReg .xorOp false 6 6⟩,
  ⟨157, 2, .aluRegReg .xorOp false 2 2⟩,
  ⟨159, 2, .aluRegReg .xorOp false 1 1⟩,
  ⟨161, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨164, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨167, 3, .aluRegReg .xorOp false 10 10⟩,
  ⟨170, 3, .aluRegReg .xorOp false 11 11⟩,
  ⟨173, 1, .ret⟩]

private theorem current_goldDot2_part1 (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    let p0 := r7.toNat * r6.toNat
    let p1 := r2.toNat * r1.toNat
    let lo0 := UInt64.ofNat (p0 % 0x10000000000000000)
    let hi0 := UInt64.ofNat (p0 / 0x10000000000000000)
    let lo1 := UInt64.ofNat (p1 % 0x10000000000000000)
    let hi1 := UInt64.ofNat (p1 / 0x10000000000000000)
    let sumLo := lo0.toNat + lo1.toNat
    let r8' := UInt64.ofNat (sumLo % 0x10000000000000000)
    let cf0 := decide (sumLo ≥ 0x10000000000000000)
    let sumHi := hi0.toNat + hi1.toNat + (if cf0 then 1 else 0)
    let r9' := UInt64.ofNat (sumHi % 0x10000000000000000)
    let cf1 := decide (sumHi ≥ 0x10000000000000000)
    let r11' : UInt64 := if cf1 then 18446744065119617025 else 0
    ∃ s2, StepsX86 current_goldDot2X86Prog 13
        ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
          y, cf, o, zf, dy, false, m⟩ s2 ∧
      ∃ r0' zf',
        s2 = ⟨61, ⟨r0', r1, r2, r3, r4, r5, r6, r7, r8', r9', lo1, r11', r12, r13, r14, r15⟩,
          y, false, false, zf', dy, false, m⟩ := by
  dsimp only
  iterate 13
    apply StepsX86_step_ex rfl rfl
    · simp only [stepX86_movRR, stepX86_xorRR, stepX86_mulx, stepX86_adcx, stepX86_adox,
        stepX86_neg, stepX86_movImm, stepX86_andRR64,
        maskGprWidth_true, mask32_xor_self, u64_zero_beq_zero,
        u64_toNat_zero, Nat.zero_add, Nat.add_zero,
        u64_ofNat_zero_mod, u64_zero_lt_264, u64_ofNat_b_mod, u64_b_lt_264,
        u64_eps2_and_mask, Bool.false_eq_true, ite_false,
        b16get_0, b16get_1, b16get_2, b16get_6, b16get_7, b16get_8, b16get_9, b16get_10, b16get_11,
        b16set_0, b16set_2, b16set_8, b16set_9, b16set_10, b16set_11]
      rfl
  exact ⟨_, StepsX86.zero _, _, _, rfl⟩

private theorem current_goldDot2_part2 (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (zf dy : Bool) (m : UInt64 → UInt8) :
    ExecReachesX86 current_goldDot2X86Prog 38
      ⟨61, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        y, false, false, zf, dy, false, m⟩
      ⟨173, ⟨goldAddMc (mulRed r8 r9) r11, 0, 0, r3, r4, r5, 0, 0, 0, 0, 0, 0,
        r12, r13, r14, r15⟩,
        y, false, false, true, dy, false, m⟩ := by
  apply StepsX86.toExecReaches
  iterate 38
    apply StepsX86.cons rfl rfl
    · simp only [stepX86_movRR, stepX86_shr64, stepX86_shl64, stepX86_addRR64, stepX86_subRR64,
        stepX86_sbbRR, stepX86_andRR, stepX86_movImm, stepX86_xorRR,
        maskGprWidth_true, mask32_xor_self, u64_zero_beq_zero, sbb32_self, sbb64_self,
        uint64_evalAdd_eq, uint64_evalSub_eq,
        b16get_0, b16get_1, b16get_2, b16get_8, b16get_9, b16get_10, b16get_11,
        b16set_6, b16set_7, b16get_6, b16get_7, b16set_0, b16set_1, b16set_2, b16set_8, b16set_9, b16set_10, b16set_11]
      rfl
  exact StepsX86.zero _

theorem current_rlib_goldilocks_dot2_adx_x86_64_functional_and_ct (st : X86BvState) (hpc : st.pc = 0) (hh : st.halted = false) :
    ∃ slice m,
      extractRlibFuncBytes currentX86RlibArchiveBytes "qsag_asm_goldilocks_dot2_adx_x86_64" = some slice ∧
      m ∈ parseArArchive currentX86RlibArchiveBytes ∧
      ArPayloadOk currentX86RlibArchiveBytes m ∧
      checkElfFuncThreeWayNI m.payload "qsag_asm_goldilocks_dot2_adx_x86_64"
        currentX86SymbolContracts[12] = true ∧
      ElfSliceThreeWayNISafe slice currentX86SymbolContracts[12] ∧
      decodeX86Slice slice.code = some current_goldDot2X86Prog ∧
        (∃ st43 tr43, execDecodedX86 slice.code 51 st = some (st43, tr43) ∧ st43.halted = false) ∧
        ∀ extra : Nat, ∃ st' trace,
          execDecodedX86 slice.code (52 + extra) st = some (st', trace) ∧
          st'.halted = true ∧ st'.pc = 173 ∧ trace.length = 52 ∧
          st'.gpr.get 0 = BitVec.ofNat 64
            (((st.gpr.get 7).toNat * (st.gpr.get 6).toNat +
              (st.gpr.get 2).toNat * (st.gpr.get 1).toNat) % GOLDILOCKS_P) ∧
          X86CalleeSavedPreserved st st' ∧
          st'.mem = st.mem ∧
          st'.gpr.get 1 = 0#64 ∧ st'.gpr.get 2 = 0#64 ∧ st'.gpr.get 8 = 0#64 ∧
          st'.gpr.get 9 = 0#64 ∧ st'.gpr.get 10 = 0#64 ∧ st'.gpr.get 11 = 0#64 ∧ st'.gpr.get 6 = 0#64 ∧ st'.gpr.get 7 = 0#64 := by
  cases hFind : currentX86ExtractedSlices.find? (fun s => s.name == "qsag_asm_goldilocks_dot2_adx_x86_64") with
  | none => exfalso; revert hFind; decide +kernel
  | some slice =>
    have hExt : extractRlibFuncBytes currentX86RlibArchiveBytes "qsag_asm_goldilocks_dot2_adx_x86_64" = some slice := by
      rw [current_extractRlibFuncBytes_x86_eq, hFind]
    have hNI : checkElfSliceThreeWayNI slice currentX86SymbolContracts[12] = true := by
      have hCheck : ((currentX86ExtractedSlices.find? (fun s => s.name == "qsag_asm_goldilocks_dot2_adx_x86_64")).map
          (fun sl => checkElfSliceThreeWayNI sl currentX86SymbolContracts[12])) =
          some true := by decide +kernel
      rw [hFind] at hCheck
      exact Option.some.inj hCheck
    have hDec : decodeX86Slice slice.code = some current_goldDot2X86Prog := by
      have hD : (currentX86ExtractedSlices.find? (fun s => s.name == "qsag_asm_goldilocks_dot2_adx_x86_64")).bind
          (fun sl => decodeX86Slice sl.code) = some current_goldDot2X86Prog := by decide +kernel
      rw [hFind] at hD
      exact hD
    obtain ⟨m, hm, hPay, _, hMemNI, _, hSafe⟩ :=
      extractRlibFuncBytes_member_ni_sound current_x86_rlib_distinct_names hExt hNI
    refine ⟨slice, m, hExt, hm, hPay, hMemNI, hSafe, hDec, ?_⟩
    rcases st with ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
      y, cf, o, zf, dy, hlt, mem⟩
    dsimp only at hpc hh; subst hpc hh
    let st0 : X86BvState := ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, mem⟩
    obtain ⟨_, hp1, r0a, zfa, rfl⟩ :=
      current_goldDot2_part1 (UInt64.ofBitVec r0) (UInt64.ofBitVec r1) (UInt64.ofBitVec r2)
        (UInt64.ofBitVec r3) (UInt64.ofBitVec r4) (UInt64.ofBitVec r5) (UInt64.ofBitVec r6)
        (UInt64.ofBitVec r7) (UInt64.ofBitVec r8) (UInt64.ofBitVec r9) (UInt64.ofBitVec r10)
        (UInt64.ofBitVec r11) (UInt64.ofBitVec r12) (UInt64.ofBitVec r13) (UInt64.ofBitVec r14)
        (UInt64.ofBitVec r15) y cf o zf dy (fun a => mem a.toBitVec)
    have h43 := ExecReachesX86_trans hp1.toExecReaches (current_goldDot2_part2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ y zfa dy (fun a => mem a.toBitVec))
    obtain ⟨hPre, hPost⟩ := execDecodedX86_ret_of_reaches st0 hDec rfl h43 rfl rfl
    refine ⟨hPre, fun extra => ?_⟩
    obtain ⟨tr, hExec, hL⟩ := hPost extra
    refine ⟨_, tr, hExec, rfl, rfl, hL, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · change (goldDot2Mc (UInt64.ofBitVec r7) (UInt64.ofBitVec r6)
          (UInt64.ofBitVec r2) (UInt64.ofBitVec r1)).toBitVec =
        BitVec.ofNat 64 ((r7.toNat * r6.toNat + r2.toNat * r1.toNat) % GOLDILOCKS_P)
      apply bv_ofU64_eq_ofNat _ (mod_goldilocks_lt_u64 _)
      rw [goldDot2Mc_toNat, UInt64.toNat_ofBitVec, UInt64.toNat_ofBitVec,
        UInt64.toNat_ofBitVec, UInt64.toNat_ofBitVec]
    · exact x86_callee_saved_of_roundtrip
    · exact mem_roundtrip mem



/-- Concrete entry state satisfying both execution premises. -/
theorem current_rlib_goldilocks_pow7_ct_x86_64_inhabited :
    ∃ st : X86BvState, st.pc = 0 ∧ st.halted = false := by
  exact ⟨X86BvState.ofX86State (x86Init 2 0 0 0 0), rfl, rfl⟩

/-- The fresh decoded machine rejects the wrong result at a concrete input. -/
theorem current_rlib_goldilocks_pow7_ct_x86_64_tooth :
    (execDecodedX86 currentX86ExtractedSlices[11].code 93
      (X86BvState.ofX86State (x86Init 2 0 0 0 0))).map
        (fun p => (p.1.gpr.get 0).toNat) ≠ some 2 := by
  decide +kernel

#tooth_pair current_rlib_goldilocks_pow7_ct_x86_64_functional_and_ct vs current_rlib_goldilocks_pow7_ct_x86_64_tooth
#verify_inhabited current_rlib_goldilocks_pow7_ct_x86_64_functional_and_ct current_rlib_goldilocks_pow7_ct_x86_64_inhabited

/-- Concrete entry state satisfying both execution premises. -/
theorem current_rlib_goldilocks_dot2_adx_x86_64_inhabited :
    ∃ st : X86BvState, st.pc = 0 ∧ st.halted = false := by
  exact ⟨X86BvState.ofX86State (x86Init 1 1 0 0 0), rfl, rfl⟩

/-- The fresh decoded machine rejects the wrong result at a concrete input. -/
theorem current_rlib_goldilocks_dot2_adx_x86_64_tooth :
    (execDecodedX86 currentX86ExtractedSlices[12].code 52
      (X86BvState.ofX86State (x86Init 1 1 0 0 0))).map
        (fun p => (p.1.gpr.get 0).toNat) ≠ some 0 := by
  decide +kernel

#tooth_pair current_rlib_goldilocks_dot2_adx_x86_64_functional_and_ct vs current_rlib_goldilocks_dot2_adx_x86_64_tooth
#verify_inhabited current_rlib_goldilocks_dot2_adx_x86_64_functional_and_ct current_rlib_goldilocks_dot2_adx_x86_64_inhabited


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
        result.1.halted = true ∧ result.1.pc = 159 ∧
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
    exact Simulates.add 3 (packTower_unpackTower 3 _)
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
  have hone : ((runX86 prog 40 gf256MacGfniWitnessState).1.mem 0).toBitVec = 1#8 := hb.symm
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
        result.1.halted = true ∧ result.1.pc = 490 ∧
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
  have hone : ((runX86 prog 121 gf256MulAvx2WitnessState).1.mem 384).toBitVec = 1#8 := hb.symm
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

