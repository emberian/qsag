module

public import Qsag.Math.Goldilocks
public import Qsag.Math.Gf2Pow128
public import Qsag.Oracle.Keccak
public import Qsag.Machine.ElfVerify
public import Qsag.Machine.ElfFixtureVerify
public import Qsag.Machine.McRefine
public import Qsag.Machine.SydTv
import Qsag.Tactic.Prelude
public import Qsag.Machine.ElfFixtures
public import Qsag.Machine.ElfInvCerts
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


/-! ### §3.2 `qsag_asm_goldilocks_sub_ct_x86_64` (`N = 23`, `retPc = 74`) -/


/-! ### §3.3 `qsag_asm_goldilocks_mul_ct_x86_64` (`N = 25`) & `qsag_asm_goldilocks_mul_ct_aarch64` (`N = 29`) -/


/-! ### §3.4 `qsag_asm_goldilocks_pow7_ct_x86_64` (`N = 85`, `retPc = 265`) -/


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


/-! ### §3.5 `qsag_asm_goldilocks_dot2_adx_x86_64` (`N = 44`, `retPc = 153`) -/


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


/-! ### §3.6 `qsag_asm_ct_eq_32_x86_64` (`N = 20`) & `qsag_asm_ct_eq_32_aarch64` (`N = 22`) -/


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
        result.1.halted = true ∧ result.1.pc = 554 ∧
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
    exact Simulates.add 3 (packTower_unpackTower 3 _)
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
  have hone : ((runX86 prog 135 gf256MacAvx2WitnessState).1.mem 384).toBitVec = 1#8 := hb.symm
  intro heq
  have hzero := congrArg UInt8.toBitVec heq
  rw [hone] at hzero
  exact (by decide : (1#8 : BitVec 8) ≠ (gfniTowerMulByte 1 0).toBitVec) hzero

#tooth_pair current_gf256_shamir_mac_avx2_loop_functional vs gf256MacAvx2_overwrite_tooth
#verify_inhabited current_gf256_shamir_mac_avx2_loop_functional gf256MacAvx2_inhabited


end


section KeccakMpcFreshVerification
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def keccakChiMpcName : List UInt8 := [113, 115, 97, 103, 95, 97, 115, 109, 95, 107, 101, 99, 99, 97, 107, 95, 99, 104, 105, 95, 109, 112, 99, 95, 97, 118, 120, 50]

def keccakChiMpcProg : List (DecodedInstr X86Instr) := [
  ⟨0, 4, .vload true 0 (.baseDisp 6 0)⟩,
  ⟨4, 5, .vload true 1 (.baseDisp 6 32)⟩,
  ⟨9, 5, .vload true 2 (.baseDisp 6 64)⟩,
  ⟨14, 5, .vload true 3 (.baseDisp 6 96)⟩,
  ⟨19, 8, .vload true 4 (.baseDisp 6 128)⟩,
  ⟨27, 4, .vload true 5 (.baseDisp 2 0)⟩,
  ⟨31, 5, .vload true 6 (.baseDisp 2 32)⟩,
  ⟨36, 5, .vload true 7 (.baseDisp 2 64)⟩,
  ⟨41, 5, .vload true 8 (.baseDisp 2 96)⟩,
  ⟨46, 8, .vload true 9 (.baseDisp 2 128)⟩,
  ⟨54, 4, .vbinOp .vpxor true 10 2 7⟩,
  ⟨58, 4, .vbinOp .vpand true 10 10 1⟩,
  ⟨62, 4, .vbinOp .vpand true 11 6 2⟩,
  ⟨66, 5, .vbinOp .vpxor true 10 10 11⟩,
  ⟨71, 4, .vbinOp .vpxor true 11 0 2⟩,
  ⟨75, 5, .vbinOp .vpxor true 10 10 11⟩,
  ⟨80, 4, .vpxorLoad256 10 10 (.baseDisp 1 0)⟩,
  ⟨84, 4, .vstore true 10 (.baseDisp 7 0)⟩,
  ⟨88, 4, .vbinOp .vpxor true 10 8 3⟩,
  ⟨92, 4, .vbinOp .vpand true 10 10 2⟩,
  ⟨96, 4, .vbinOp .vpand true 11 7 3⟩,
  ⟨100, 5, .vbinOp .vpxor true 10 10 11⟩,
  ⟨105, 4, .vbinOp .vpxor true 11 1 3⟩,
  ⟨109, 5, .vbinOp .vpxor true 10 10 11⟩,
  ⟨114, 5, .vpxorLoad256 10 10 (.baseDisp 1 32)⟩,
  ⟨119, 5, .vstore true 10 (.baseDisp 7 32)⟩,
  ⟨124, 4, .vbinOp .vpxor true 10 9 4⟩,
  ⟨128, 4, .vbinOp .vpand true 10 10 3⟩,
  ⟨132, 4, .vbinOp .vpand true 11 8 4⟩,
  ⟨136, 5, .vbinOp .vpxor true 10 10 11⟩,
  ⟨141, 4, .vbinOp .vpxor true 11 2 4⟩,
  ⟨145, 5, .vbinOp .vpxor true 10 10 11⟩,
  ⟨150, 5, .vpxorLoad256 10 10 (.baseDisp 1 64)⟩,
  ⟨155, 5, .vstore true 10 (.baseDisp 7 64)⟩,
  ⟨160, 4, .vbinOp .vpxor true 10 0 5⟩,
  ⟨164, 4, .vbinOp .vpand true 10 10 4⟩,
  ⟨168, 4, .vbinOp .vpand true 11 9 0⟩,
  ⟨172, 5, .vbinOp .vpxor true 10 10 11⟩,
  ⟨177, 4, .vbinOp .vpxor true 11 3 0⟩,
  ⟨181, 5, .vbinOp .vpxor true 10 10 11⟩,
  ⟨186, 5, .vpxorLoad256 10 10 (.baseDisp 1 96)⟩,
  ⟨191, 5, .vstore true 10 (.baseDisp 7 96)⟩,
  ⟨196, 4, .vbinOp .vpxor true 10 1 6⟩,
  ⟨200, 4, .vbinOp .vpand true 10 10 0⟩,
  ⟨204, 4, .vbinOp .vpand true 11 5 1⟩,
  ⟨208, 5, .vbinOp .vpxor true 10 10 11⟩,
  ⟨213, 4, .vbinOp .vpxor true 11 4 1⟩,
  ⟨217, 5, .vbinOp .vpxor true 10 10 11⟩,
  ⟨222, 8, .vpxorLoad256 10 10 (.baseDisp 1 128)⟩,
  ⟨230, 8, .vstore true 10 (.baseDisp 7 128)⟩,
  ⟨238, 4, .vbinOp .vpxor true 0 0 0⟩,
  ⟨242, 4, .vbinOp .vpxor true 1 1 1⟩,
  ⟨246, 4, .vbinOp .vpxor true 2 2 2⟩,
  ⟨250, 4, .vbinOp .vpxor true 3 3 3⟩,
  ⟨254, 4, .vbinOp .vpxor true 4 4 4⟩,
  ⟨258, 4, .vbinOp .vpxor true 5 5 5⟩,
  ⟨262, 4, .vbinOp .vpxor true 6 6 6⟩,
  ⟨266, 4, .vbinOp .vpxor true 7 7 7⟩,
  ⟨270, 5, .vbinOp .vpxor true 8 8 8⟩,
  ⟨275, 5, .vbinOp .vpxor true 9 9 9⟩,
  ⟨280, 5, .vbinOp .vpxor true 10 10 10⟩,
  ⟨285, 5, .vbinOp .vpxor true 11 11 11⟩,
  ⟨290, 3, .vzeroall⟩,
  ⟨293, 3, .vzeroupper⟩,
  ⟨296, 2, .aluRegReg .xorOp false 7 7⟩,
  ⟨298, 2, .aluRegReg .xorOp false 6 6⟩,
  ⟨300, 2, .aluRegReg .xorOp false 2 2⟩,
  ⟨302, 2, .aluRegReg .xorOp false 1 1⟩,
  ⟨304, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨307, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨310, 3, .aluRegReg .xorOp false 10 10⟩,
  ⟨313, 3, .aluRegReg .xorOp false 11 11⟩,
  ⟨316, 2, .aluRegReg .xorOp false 0 0⟩,
  ⟨318, 1, .ret⟩
]

theorem keccakChiMpc_decoded :
    (findSliceByNameBytes currentX86ExtractedSlices keccakChiMpcName).bind
      (fun sl => decodeX86Stream sl.code) = some keccakChiMpcProg := by decide +kernel


/-- One party's RSS share of a Keccak chi gate. `a,b,c` belong to its first
share, and `bNext,cNext` to the next party's share; `r` is its zero-share mask. -/
def keccakChiMpcShareWord (a b c bNext cNext r : UInt64) : UInt64 :=
  (((c ^^^ cNext) &&& b) ^^^ (bNext &&& c)) ^^^ (a ^^^ c) ^^^ r

private theorem keccakChiMpc_bool_identity :
    ∀ (a0 a1 a2 b0 b1 b2 c0 c1 c2 r0 r1 r2 : Bool),
    ((((((c0 ^^ c1) && b0) ^^ (b1 && c0)) ^^ (a0 ^^ c0)) ^^ r0) ^^
    (((((c1 ^^ c2) && b1) ^^ (b2 && c1)) ^^ (a1 ^^ c1)) ^^ r1) ^^
    (((((c2 ^^ c0) && b2) ^^ (b0 && c2)) ^^ (a2 ^^ c2)) ^^ r2)) =
      (keccakChiBit (a0 ^^ a1 ^^ a2) (b0 ^^ b1 ^^ b2) (c0 ^^ c1 ^^ c2) ^^
        (r0 ^^ r1 ^^ r2)) := by
  decide +kernel

/-- Three cyclic RSS parties reconstruct ordinary chi, with all masks exposed. -/
theorem keccakChiMpcShareWord_reconstruct
    (a0 a1 a2 b0 b1 b2 c0 c1 c2 r0 r1 r2 : UInt64)
    (hr : r0 ^^^ r1 ^^^ r2 = 0) :
    keccakChiMpcShareWord a0 b0 c0 b1 c1 r0 ^^^
      keccakChiMpcShareWord a1 b1 c1 b2 c2 r1 ^^^
      keccakChiMpcShareWord a2 b2 c2 b0 c0 r2 =
    (a0 ^^^ a1 ^^^ a2) ^^^ ((~~~(b0 ^^^ b1 ^^^ b2)) &&& (c0 ^^^ c1 ^^^ c2)) := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hm := congrArg (fun x : UInt64 => x.toBitVec.getLsbD i) hr
  simp only [UInt64.toBitVec_xor, BitVec.getLsbD_xor] at hm
  have hzero : (0 : UInt64).toBitVec.getLsbD i = false := by simp
  rw [hzero] at hm
  rw [chiWordBit_eq_keccakChiBit _ _ _ i hi]
  simp only [keccakChiMpcShareWord, UInt64.toBitVec_xor, UInt64.toBitVec_and,
    BitVec.getLsbD_xor, BitVec.getLsbD_and]
  rw [keccakChiMpc_bool_identity, hm, Bool.xor_false]

/-- All 64 bits of each reconstructed word are the canonical boolean chi gate. -/
theorem keccakChiMpcShareWord_reconstruct_bit
    (a0 a1 a2 b0 b1 b2 c0 c1 c2 r0 r1 r2 : UInt64)
    (hr : r0 ^^^ r1 ^^^ r2 = 0) (i : Nat) (hi : i < 64) :
    (keccakChiMpcShareWord a0 b0 c0 b1 c1 r0 ^^^
      keccakChiMpcShareWord a1 b1 c1 b2 c2 r1 ^^^
      keccakChiMpcShareWord a2 b2 c2 b0 c0 r2).toBitVec.getLsbD i =
    keccakChiBit ((a0 ^^^ a1 ^^^ a2).toBitVec.getLsbD i)
      ((b0 ^^^ b1 ^^^ b2).toBitVec.getLsbD i)
      ((c0 ^^^ c1 ^^^ c2).toBitVec.getLsbD i) := by
  rw [keccakChiMpcShareWord_reconstruct _ _ _ _ _ _ _ _ _ _ _ _ hr]
  exact chiWordBit_eq_keccakChiBit _ _ _ i hi

/-- The five 256-bit vectors are five chi row coordinates, each containing four
independent 64-bit words. They are not two XOR-reconstructed shares of a state. -/
def keccakChiMpcRowWord (s t r : Nat → Nat → UInt64) (x q : Nat) : UInt64 :=
  keccakChiMpcShareWord (s x q) (s ((x + 1) % 5) q) (s ((x + 2) % 5) q)
    (t ((x + 1) % 5) q) (t ((x + 2) % 5) q) (r x q)

/-- Embed any one of the four independent input rows in the first row of a
Keccak state. The unused rows are zero and stay zero under chi. -/
def keccakChiMpcRowState (s : Nat → Nat → UInt64) (q : Nat) : KState :=
  ⟨s 0 q, s 1 q, s 2 q, s 3 q, s 4 q,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Every one of the four rows (all 5 × 256 boolean gates) reconstructs to
`Keccak.chiS`; masks may vary independently between coordinates and words. -/
theorem keccakChiMpcRow_reconstruct
    (s0 s1 s2 r0 r1 r2 : Nat → Nat → UInt64)
    (hr : ∀ x q : Nat, x < 5 → q < 4 → r0 x q ^^^ r1 x q ^^^ r2 x q = 0)
    (q : Nat) (hq : q < 4) :
    keccakChiMpcRowState (fun x j =>
      keccakChiMpcRowWord s0 s1 r0 x j ^^^ keccakChiMpcRowWord s1 s2 r1 x j ^^^
        keccakChiMpcRowWord s2 s0 r2 x j) q =
    chiS (keccakChiMpcRowState (fun x j => s0 x j ^^^ s1 x j ^^^ s2 x j) q) := by
  unfold keccakChiMpcRowState chiS keccakChiMpcRowWord
  dsimp only
  congr 1
  all_goals first
    | exact keccakChiMpcShareWord_reconstruct _ _ _ _ _ _ _ _ _ _ _ _ (hr _ q (by decide) hq)
    | rfl

/-- Omitting the linear `c` contribution is a wrong specification: even a
single set input bit with zero neighbours must survive the NOT term. -/
theorem keccakChiMpcShareWord_tooth :
    keccakChiMpcShareWord 0 0 1 0 0 0 ≠ (0 : UInt64) := by
  decide +kernel

theorem keccakChiMpcRow_inhabited :
    ∃ (s0 s1 s2 r0 r1 r2 : Nat → Nat → UInt64) (q : Nat),
      (∀ x j : Nat, x < 5 → j < 4 → r0 x j ^^^ r1 x j ^^^ r2 x j = 0) ∧
      q < 4 ∧ keccakChiMpcRowState s0 q = zeroKState ∧
      keccakChiMpcRowState s1 q = zeroKState ∧ keccakChiMpcRowState s2 q = zeroKState := by
  refine ⟨(fun _ _ => 0), (fun _ _ => 0), (fun _ _ => 0),
    (fun _ _ => 0), (fun _ _ => 0), (fun _ _ => 0), 0, ?_, by decide, rfl, rfl, rfl⟩
  intro _ _ _ _
  change (0 : UInt64) ^^^ 0 ^^^ 0 = 0
  decide +kernel

#tooth_pair keccakChiMpcRow_reconstruct vs keccakChiMpcShareWord_tooth
#verify_inhabited keccakChiMpcRow_reconstruct keccakChiMpcRow_inhabited

theorem keccakChiMpc_readMem64_writeMem256_disjoint
    (mem : UInt64 → UInt8) (a1 a2 : UInt64) (v : Vec256)
    (hd : ∀ i k : Nat, i < 8 → k < 32 → a1 + UInt64.ofNat i ≠ a2 + UInt64.ofNat k) :
    readMem64 (writeMem256 mem a2 v) a1 = readMem64 mem a1 := by
  rw [readMem64_eq_mapBytes64, readMem64_eq_mapBytes64]
  unfold mapBytes64
  simp only [writeMem256_outside mem a2 v _ (hd 0 · (by decide)),
    writeMem256_outside mem a2 v _ (hd 1 · (by decide)),
    writeMem256_outside mem a2 v _ (hd 2 · (by decide)),
    writeMem256_outside mem a2 v _ (hd 3 · (by decide)),
    writeMem256_outside mem a2 v _ (hd 4 · (by decide)),
    writeMem256_outside mem a2 v _ (hd 5 · (by decide)),
    writeMem256_outside mem a2 v _ (hd 6 · (by decide)),
    writeMem256_outside mem a2 v _ (hd 7 · (by decide))]

theorem keccakChiMpc_readMem256_writeMem256_disjoint
    (mem : UInt64 → UInt8) (a1 a2 : UInt64) (v : Vec256)
    (hd : ∀ i k : Nat, i < 32 → k < 32 → a1 + UInt64.ofNat i ≠ a2 + UInt64.ofNat k) :
    readMem256 (writeMem256 mem a2 v) a1 = readMem256 mem a1 := by
  have h (off : Nat) (ho : off ≤ 24) :
      readMem64 (writeMem256 mem a2 v) (a1 + UInt64.ofNat off) =
        readMem64 mem (a1 + UInt64.ofNat off) := by
    apply keccakChiMpc_readMem64_writeMem256_disjoint
    intro i k hi hk heq
    rw [u64_add_ofNat_assoc a1 off i (by omega)] at heq
    exact hd (off + i) k (by omega) hk heq
  unfold readMem256
  have h0 := h 0 (by decide)
  have hz : UInt64.ofNat 0 = (0 : UInt64) := by decide +kernel
  rw [hz, UInt64.add_zero] at h0
  have h8 : UInt64.ofNat 8 = (8 : UInt64) := by decide +kernel
  have h16 : UInt64.ofNat 16 = (16 : UInt64) := by decide +kernel
  have h24 : UInt64.ofNat 24 = (24 : UInt64) := by decide +kernel
  rw [← h8, ← h16, ← h24]
  rw [h0, h 8 (by decide), h 16 (by decide), h 24 (by decide)]

theorem keccakChiMpc_readMem256_writeMem256_same
    (mem : UInt64 → UInt8) (a : UInt64) (v : Vec256) :
    readMem256 (writeMem256 mem a v) a = v := by
  have hd (o1 o2 : Nat) (h1 : o1 ≤ 24) (h2 : o2 ≤ 24)
      (hne : o1 + 8 ≤ o2 ∨ o2 + 8 ≤ o1)
      (m : UInt64 → UInt8) (w : UInt64) :
      readMem64 (writeMem64 m (a + UInt64.ofNat o2) w) (a + UInt64.ofNat o1) =
        readMem64 m (a + UInt64.ofNat o1) := by
    apply readMem64_writeMem64_disjoint
    intro i j hi hj heq
    rw [u64_add_ofNat_assoc a o1 i (by omega),
      u64_add_ofNat_assoc a o2 j (by omega)] at heq
    have := u64_add_ofNat_inj (by omega) (by omega) heq
    omega
  have hd0 (o2 : Nat) (h2 : o2 ≤ 24) (hne : 8 ≤ o2)
      (m : UInt64 → UInt8) (w : UInt64) :
      readMem64 (writeMem64 m (a + UInt64.ofNat o2) w) a = readMem64 m a := by
    have hz : UInt64.ofNat 0 = (0 : UInt64) := by decide +kernel
    simpa only [hz, UInt64.add_zero] using hd 0 o2 (by decide) h2 (Or.inl hne) m w
  unfold readMem256 writeMem256
  dsimp only
  have h8 : UInt64.ofNat 8 = (8 : UInt64) := by decide +kernel
  have h16 : UInt64.ofNat 16 = (16 : UInt64) := by decide +kernel
  have h24 : UInt64.ofNat 24 = (24 : UInt64) := by decide +kernel
  rw [← h8, ← h16, ← h24]
  rw [hd0 24 (by decide) (by decide), hd0 16 (by decide) (by decide),
    hd0 8 (by decide) (by decide), readMem64_writeMem64_same,
    hd 8 24 (by decide) (by decide) (by omega),
    hd 8 16 (by decide) (by decide) (by omega), readMem64_writeMem64_same,
    hd 16 24 (by decide) (by decide) (by omega), readMem64_writeMem64_same,
    readMem64_writeMem64_same]


/-- Output stores may alias the two input share rows (which are loaded first),
but not the mask row, which is read incrementally. -/
def keccakChiMpcSeparated (dst mask : UInt64) : Prop :=
  ∀ i j : Nat, i < 160 → j < 160 → dst + UInt64.ofNat i ≠ mask + UInt64.ofNat j

private theorem keccakChiMpc_maskRead (mem : UInt64 → UInt8) (dst mask : UInt64)
    (h : keccakChiMpcSeparated dst mask) (i j : Nat) (hi : i ≤ 128) (hj : j ≤ 128)
    (v : Vec256) :
    readMem256 (writeMem256 mem (dst + UInt64.ofNat i) v) (mask + UInt64.ofNat j) =
      readMem256 mem (mask + UInt64.ofNat j) := by
  apply keccakChiMpc_readMem256_writeMem256_disjoint
  intro k l hk hl he
  rw [u64_add_ofNat_assoc mask j k (by omega),
    u64_add_ofNat_assoc dst i l (by omega)] at he
  exact h (i + l) (j + k) (by omega) (by omega) he.symm

/-- Four independent words of a single RSS output coordinate. -/
def keccakChiMpcShareVec (a b c bn cn r : Vec256) : Vec256 :=
  ⟨keccakChiMpcShareWord a.w0 b.w0 c.w0 bn.w0 cn.w0 r.w0,
   keccakChiMpcShareWord a.w1 b.w1 c.w1 bn.w1 cn.w1 r.w1,
   keccakChiMpcShareWord a.w2 b.w2 c.w2 bn.w2 cn.w2 r.w2,
   keccakChiMpcShareWord a.w3 b.w3 c.w3 bn.w3 cn.w3 r.w3⟩

def keccakChiMpcOutVec (mem : UInt64 → UInt8) (s0 s1 mask : UInt64) (x : Nat) : Vec256 :=
  keccakChiMpcShareVec (readMem256 mem (s0 + UInt64.ofNat (32 * x)))
    (readMem256 mem (s0 + UInt64.ofNat (32 * ((x + 1) % 5))))
    (readMem256 mem (s0 + UInt64.ofNat (32 * ((x + 2) % 5))))
    (readMem256 mem (s1 + UInt64.ofNat (32 * ((x + 1) % 5))))
    (readMem256 mem (s1 + UInt64.ofNat (32 * ((x + 2) % 5))))
    (readMem256 mem (mask + UInt64.ofNat (32 * x)))

/-- The entire 160-byte RSS chi output, all five coordinates and all four words. -/
def keccakChiMpcOutMem (mem : UInt64 → UInt8) (dst s0 s1 mask : UInt64) : UInt64 → UInt8 :=
  let m0 := writeMem256 mem (dst + 0) (keccakChiMpcOutVec mem s0 s1 mask 0)
  let m1 := writeMem256 m0 (dst + 32) (keccakChiMpcOutVec mem s0 s1 mask 1)
  let m2 := writeMem256 m1 (dst + 64) (keccakChiMpcOutVec mem s0 s1 mask 2)
  let m3 := writeMem256 m2 (dst + 96) (keccakChiMpcOutVec mem s0 s1 mask 3)
  let m4 := writeMem256 m3 (dst + 128) (keccakChiMpcOutVec mem s0 s1 mask 4)
  m4

private theorem keccakChiMpc_xor_comm (a b : UInt64) : a ^^^ b = b ^^^ a := by
  apply UInt64.eq_of_toBitVec_eq
  simp only [UInt64.toBitVec_xor, BitVec.xor_comm]

private theorem keccakChiMpc_loads (g : Bank16 UInt64) (y : Bank16 Vec256)
    (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    ExecReachesX86 keccakChiMpcProg 10
      ⟨0, g, y, cf, o, zf, dy, false, m⟩
      ⟨54, g, ⟨readMem256 m (g.get 6 + 0), readMem256 m (g.get 6 + 32), readMem256 m (g.get 6 + 64), readMem256 m (g.get 6 + 96), readMem256 m (g.get 6 + 128), readMem256 m (g.get 2 + 0), readMem256 m (g.get 2 + 32), readMem256 m (g.get 2 + 64), readMem256 m (g.get 2 + 96), readMem256 m (g.get 2 + 128), y.get 10, y.get 11, y.get 12, y.get 13, y.get 14, y.get 15⟩, cf, o, zf, true, false, m⟩ := by
  apply StepsX86.toExecReaches
  iterate 10
    apply StepsX86.cons rfl rfl
    · simp only [ite_true, ite_false, stepX86, evalX86Addr, clampVecWidth, Bank16.set, Bank16.get, Bool.or_true]
      rfl
  exact StepsX86.zero _

private theorem keccakChiMpc_lane0 (g : Bank16 UInt64)
    (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 t10 t11 y12 y13 y14 y15 : Vec256)
    (cf o zf : Bool) (m : UInt64 → UInt8) :
    ExecReachesX86 keccakChiMpcProg 8
      ⟨54, g, ⟨a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, t10, t11, y12, y13, y14, y15⟩, cf, o, zf, true, false, m⟩
      ⟨88, g, ⟨a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, (keccakChiMpcShareVec a0 a1 a2 b1 b2 (readMem256 m (g.get 1 + 0))), (evalVecBin256 .vpxor a0 a2), y12, y13, y14, y15⟩, cf, o, zf, true, false, (writeMem256 m (g.get 7 + 0) (keccakChiMpcShareVec a0 a1 a2 b1 b2 (readMem256 m (g.get 1 + 0))))⟩ := by
  apply StepsX86.toExecReaches
  iterate 8
    apply StepsX86.cons rfl rfl
    · simp only [ite_true, ite_false, stepX86, evalX86Addr, clampVecWidth, Bank16.set, Bank16.get, evalVecBin256]
      rfl
  simp only [keccakChiMpcShareVec, keccakChiMpcShareWord, evalVecBin256]

  exact StepsX86.zero _

private theorem keccakChiMpc_lane1 (g : Bank16 UInt64)
    (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 t10 t11 y12 y13 y14 y15 : Vec256)
    (cf o zf : Bool) (m : UInt64 → UInt8) :
    ExecReachesX86 keccakChiMpcProg 8
      ⟨88, g, ⟨a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, t10, t11, y12, y13, y14, y15⟩, cf, o, zf, true, false, m⟩
      ⟨124, g, ⟨a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, (keccakChiMpcShareVec a1 a2 a3 b2 b3 (readMem256 m (g.get 1 + 32))), (evalVecBin256 .vpxor a1 a3), y12, y13, y14, y15⟩, cf, o, zf, true, false, (writeMem256 m (g.get 7 + 32) (keccakChiMpcShareVec a1 a2 a3 b2 b3 (readMem256 m (g.get 1 + 32))))⟩ := by
  apply StepsX86.toExecReaches
  iterate 8
    apply StepsX86.cons rfl rfl
    · simp only [ite_true, ite_false, stepX86, evalX86Addr, clampVecWidth, Bank16.set, Bank16.get, evalVecBin256]
      rfl
  simp only [keccakChiMpcShareVec, keccakChiMpcShareWord, evalVecBin256]

  rw [keccakChiMpc_xor_comm b3.w0 a3.w0]
  rw [keccakChiMpc_xor_comm b3.w1 a3.w1]
  rw [keccakChiMpc_xor_comm b3.w2 a3.w2]
  rw [keccakChiMpc_xor_comm b3.w3 a3.w3]
  exact StepsX86.zero _

private theorem keccakChiMpc_lane2 (g : Bank16 UInt64)
    (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 t10 t11 y12 y13 y14 y15 : Vec256)
    (cf o zf : Bool) (m : UInt64 → UInt8) :
    ExecReachesX86 keccakChiMpcProg 8
      ⟨124, g, ⟨a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, t10, t11, y12, y13, y14, y15⟩, cf, o, zf, true, false, m⟩
      ⟨160, g, ⟨a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, (keccakChiMpcShareVec a2 a3 a4 b3 b4 (readMem256 m (g.get 1 + 64))), (evalVecBin256 .vpxor a2 a4), y12, y13, y14, y15⟩, cf, o, zf, true, false, (writeMem256 m (g.get 7 + 64) (keccakChiMpcShareVec a2 a3 a4 b3 b4 (readMem256 m (g.get 1 + 64))))⟩ := by
  apply StepsX86.toExecReaches
  iterate 8
    apply StepsX86.cons rfl rfl
    · simp only [ite_true, ite_false, stepX86, evalX86Addr, clampVecWidth, Bank16.set, Bank16.get, evalVecBin256]
      rfl
  simp only [keccakChiMpcShareVec, keccakChiMpcShareWord, evalVecBin256]

  rw [keccakChiMpc_xor_comm b4.w0 a4.w0]
  rw [keccakChiMpc_xor_comm b4.w1 a4.w1]
  rw [keccakChiMpc_xor_comm b4.w2 a4.w2]
  rw [keccakChiMpc_xor_comm b4.w3 a4.w3]
  exact StepsX86.zero _

private theorem keccakChiMpc_lane3 (g : Bank16 UInt64)
    (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 t10 t11 y12 y13 y14 y15 : Vec256)
    (cf o zf : Bool) (m : UInt64 → UInt8) :
    ExecReachesX86 keccakChiMpcProg 8
      ⟨160, g, ⟨a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, t10, t11, y12, y13, y14, y15⟩, cf, o, zf, true, false, m⟩
      ⟨196, g, ⟨a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, (keccakChiMpcShareVec a3 a4 a0 b4 b0 (readMem256 m (g.get 1 + 96))), (evalVecBin256 .vpxor a3 a0), y12, y13, y14, y15⟩, cf, o, zf, true, false, (writeMem256 m (g.get 7 + 96) (keccakChiMpcShareVec a3 a4 a0 b4 b0 (readMem256 m (g.get 1 + 96))))⟩ := by
  apply StepsX86.toExecReaches
  iterate 8
    apply StepsX86.cons rfl rfl
    · simp only [ite_true, ite_false, stepX86, evalX86Addr, clampVecWidth, Bank16.set, Bank16.get, evalVecBin256]
      rfl
  simp only [keccakChiMpcShareVec, keccakChiMpcShareWord, evalVecBin256]

  exact StepsX86.zero _

private theorem keccakChiMpc_lane4 (g : Bank16 UInt64)
    (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 t10 t11 y12 y13 y14 y15 : Vec256)
    (cf o zf : Bool) (m : UInt64 → UInt8) :
    ExecReachesX86 keccakChiMpcProg 8
      ⟨196, g, ⟨a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, t10, t11, y12, y13, y14, y15⟩, cf, o, zf, true, false, m⟩
      ⟨238, g, ⟨a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, (keccakChiMpcShareVec a4 a0 a1 b0 b1 (readMem256 m (g.get 1 + 128))), (evalVecBin256 .vpxor a4 a1), y12, y13, y14, y15⟩, cf, o, zf, true, false, (writeMem256 m (g.get 7 + 128) (keccakChiMpcShareVec a4 a0 a1 b0 b1 (readMem256 m (g.get 1 + 128))))⟩ := by
  apply StepsX86.toExecReaches
  iterate 8
    apply StepsX86.cons rfl rfl
    · simp only [ite_true, ite_false, stepX86, evalX86Addr, clampVecWidth, Bank16.set, Bank16.get, evalVecBin256]
      rfl
  simp only [keccakChiMpcShareVec, keccakChiMpcShareWord, evalVecBin256]

  exact StepsX86.zero _

private theorem keccakChiMpc_cleanup
    (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf : Bool) (m : UInt64 → UInt8) :
    ExecReachesX86 keccakChiMpcProg 24
      ⟨238, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, true, false, m⟩
      ⟨318, ⟨0, 0, 0, r3, r4, r5, 0, 0, 0, 0, 0, 0, r12, r13, r14, r15⟩, Bank16.const Vec256.zero, false, false, true, false, true, m⟩ := by
  apply StepsX86.toExecReaches
  iterate 12
    apply StepsX86.cons rfl rfl
    · simp only [ite_true, ite_false, stepX86, evalX86Addr, clampVecWidth, Bank16.set, Bank16.get,
        evalVecBin256, u64_xor_self]
      rfl
  iterate 11
    apply StepsX86.cons rfl rfl
    · simp only [current_vzeroall_step, current_vzeroupper_zero_step, stepX86_xorRR,
        mask32_xor_self, u64_zero_beq_zero,
        b16set_0, b16set_1, b16set_2, b16set_6, b16set_7,
        b16set_8, b16set_9, b16set_10, b16set_11]
      rfl
  apply StepsX86.cons rfl rfl rfl
  exact StepsX86.zero _

private theorem keccakChiMpc_reaches
    (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8)
    (h : keccakChiMpcSeparated r7 r1) :
    ExecReachesX86 keccakChiMpcProg 74
      ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, m⟩
      ⟨318, ⟨0, 0, 0, r3, r4, r5, 0, 0, 0, 0, 0, 0, r12, r13, r14, r15⟩, Bank16.const Vec256.zero, false, false, true, false, true, (keccakChiMpcOutMem m r7 r6 r2 r1)⟩ := by
  let g : Bank16 UInt64 := ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩

  let a0 := readMem256 m (r6 + 0)
  let a1 := readMem256 m (r6 + 32)
  let a2 := readMem256 m (r6 + 64)
  let a3 := readMem256 m (r6 + 96)
  let a4 := readMem256 m (r6 + 128)
  let b0 := readMem256 m (r2 + 0)
  let b1 := readMem256 m (r2 + 32)
  let b2 := readMem256 m (r2 + 64)
  let b3 := readMem256 m (r2 + 96)
  let b4 := readMem256 m (r2 + 128)
  let v0 := keccakChiMpcShareVec a0 a1 a2 b1 b2 (readMem256 m (r1 + 0))
  let t0 := evalVecBin256 .vpxor a0 a2
  let m0 := writeMem256 m (r7 + 0) v0
  let v1 := keccakChiMpcShareVec a1 a2 a3 b2 b3 (readMem256 m (r1 + 32))
  let t1 := evalVecBin256 .vpxor a1 a3
  let m1 := writeMem256 m0 (r7 + 32) v1
  let v2 := keccakChiMpcShareVec a2 a3 a4 b3 b4 (readMem256 m (r1 + 64))
  let t2 := evalVecBin256 .vpxor a2 a4
  let m2 := writeMem256 m1 (r7 + 64) v2
  let v3 := keccakChiMpcShareVec a3 a4 a0 b4 b0 (readMem256 m (r1 + 96))
  let t3 := evalVecBin256 .vpxor a3 a0
  let m3 := writeMem256 m2 (r7 + 96) v3
  let v4 := keccakChiMpcShareVec a4 a0 a1 b0 b1 (readMem256 m (r1 + 128))
  let t4 := evalVecBin256 .vpxor a4 a1
  let m4 := writeMem256 m3 (r7 + 128) v4
  have hn0 : UInt64.ofNat 0 = (0 : UInt64) := by decide +kernel
  have hn32 : UInt64.ofNat 32 = (32 : UInt64) := by decide +kernel
  have hn64 : UInt64.ofNat 64 = (64 : UInt64) := by decide +kernel
  have hn96 : UInt64.ofNat 96 = (96 : UInt64) := by decide +kernel
  have hn128 : UInt64.ofNat 128 = (128 : UInt64) := by decide +kernel
  have hr0_1 (mm : UInt64 → UInt8) (v : Vec256) :
      readMem256 (writeMem256 mm (r7 + 0) v) (r1 + 32) = readMem256 mm (r1 + 32) := by
    simpa only [hn0, hn32] using
      keccakChiMpc_maskRead mm r7 r1 h 0 32 (by decide) (by decide) v
  have hr0_2 (mm : UInt64 → UInt8) (v : Vec256) :
      readMem256 (writeMem256 mm (r7 + 0) v) (r1 + 64) = readMem256 mm (r1 + 64) := by
    simpa only [hn0, hn64] using
      keccakChiMpc_maskRead mm r7 r1 h 0 64 (by decide) (by decide) v
  have hr1_2 (mm : UInt64 → UInt8) (v : Vec256) :
      readMem256 (writeMem256 mm (r7 + 32) v) (r1 + 64) = readMem256 mm (r1 + 64) := by
    simpa only [hn32, hn64] using
      keccakChiMpc_maskRead mm r7 r1 h 32 64 (by decide) (by decide) v
  have hr0_3 (mm : UInt64 → UInt8) (v : Vec256) :
      readMem256 (writeMem256 mm (r7 + 0) v) (r1 + 96) = readMem256 mm (r1 + 96) := by
    simpa only [hn0, hn96] using
      keccakChiMpc_maskRead mm r7 r1 h 0 96 (by decide) (by decide) v
  have hr1_3 (mm : UInt64 → UInt8) (v : Vec256) :
      readMem256 (writeMem256 mm (r7 + 32) v) (r1 + 96) = readMem256 mm (r1 + 96) := by
    simpa only [hn32, hn96] using
      keccakChiMpc_maskRead mm r7 r1 h 32 96 (by decide) (by decide) v
  have hr2_3 (mm : UInt64 → UInt8) (v : Vec256) :
      readMem256 (writeMem256 mm (r7 + 64) v) (r1 + 96) = readMem256 mm (r1 + 96) := by
    simpa only [hn64, hn96] using
      keccakChiMpc_maskRead mm r7 r1 h 64 96 (by decide) (by decide) v
  have hr0_4 (mm : UInt64 → UInt8) (v : Vec256) :
      readMem256 (writeMem256 mm (r7 + 0) v) (r1 + 128) = readMem256 mm (r1 + 128) := by
    simpa only [hn0, hn128] using
      keccakChiMpc_maskRead mm r7 r1 h 0 128 (by decide) (by decide) v
  have hr1_4 (mm : UInt64 → UInt8) (v : Vec256) :
      readMem256 (writeMem256 mm (r7 + 32) v) (r1 + 128) = readMem256 mm (r1 + 128) := by
    simpa only [hn32, hn128] using
      keccakChiMpc_maskRead mm r7 r1 h 32 128 (by decide) (by decide) v
  have hr2_4 (mm : UInt64 → UInt8) (v : Vec256) :
      readMem256 (writeMem256 mm (r7 + 64) v) (r1 + 128) = readMem256 mm (r1 + 128) := by
    simpa only [hn64, hn128] using
      keccakChiMpc_maskRead mm r7 r1 h 64 128 (by decide) (by decide) v
  have hr3_4 (mm : UInt64 → UInt8) (v : Vec256) :
      readMem256 (writeMem256 mm (r7 + 96) v) (r1 + 128) = readMem256 mm (r1 + 128) := by
    simpa only [hn96, hn128] using
      keccakChiMpc_maskRead mm r7 r1 h 96 128 (by decide) (by decide) v
  have hp := keccakChiMpc_loads g y cf o zf dy m
  have he0 := keccakChiMpc_lane0 g a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 (y.get 10) (y.get 11) (y.get 12) (y.get 13) (y.get 14) (y.get 15) cf o zf m
  have he1 := keccakChiMpc_lane1 g a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 v0 t0 (y.get 12) (y.get 13) (y.get 14) (y.get 15) cf o zf m0
  simp only [g, Bank16.get, m0, hr0_1] at he1
  have he2 := keccakChiMpc_lane2 g a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 v1 t1 (y.get 12) (y.get 13) (y.get 14) (y.get 15) cf o zf m1
  simp only [g, Bank16.get, m0, m1, hr1_2, hr0_2] at he2
  have he3 := keccakChiMpc_lane3 g a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 v2 t2 (y.get 12) (y.get 13) (y.get 14) (y.get 15) cf o zf m2
  simp only [g, Bank16.get, m0, m1, m2, hr2_3, hr1_3, hr0_3] at he3
  have he4 := keccakChiMpc_lane4 g a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 v3 t3 (y.get 12) (y.get 13) (y.get 14) (y.get 15) cf o zf m3
  simp only [g, Bank16.get, m0, m1, m2, m3, hr3_4, hr2_4, hr1_4, hr0_4] at he4
  have ht := keccakChiMpc_cleanup r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 ⟨a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, v4, t4, (y.get 12), (y.get 13), (y.get 14), (y.get 15)⟩ cf o zf m4
  have hall := ExecReachesX86_trans hp (ExecReachesX86_trans he0 (ExecReachesX86_trans he1
    (ExecReachesX86_trans he2 (ExecReachesX86_trans he3 (ExecReachesX86_trans he4 ht)))))
  have hm4 : m4 = keccakChiMpcOutMem m r7 r6 r2 r1 := by
    simp only [m4, m3, m2, m1, m0, v0, v1, v2, v3, v4,
      a0, a1, a2, a3, a4, b0, b1, b2, b3, b4, keccakChiMpcOutMem, keccakChiMpcOutVec]
    simp only [hn0, hn32, hn64, hn96, hn128]
  rw [hm4] at hall
  exact hall


/-- Entry and aliasing preconditions, with no restriction on secret data or registers. -/
def keccakChiMpcInitial (s : X86State) : Prop :=
  s.pc = 0 ∧ s.halted = false ∧ keccakChiMpcSeparated (s.gpr.get 7) (s.gpr.get 1)

/-- Fresh AVX2 execution computes every byte of all five 256-bit RSS chi shares. -/
theorem keccakChiMpc_current_functional (s : X86State) (h : keccakChiMpcInitial s) :
    ∃ slice prog,
      findSliceByNameBytes currentX86ExtractedSlices
        keccakChiMpcName = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ extra : Nat,
        (runX86 prog (74 + extra) s).1.halted = true ∧
        (runX86 prog (74 + extra) s).1.mem =
          keccakChiMpcOutMem s.mem (s.gpr.get 7) (s.gpr.get 6) (s.gpr.get 2) (s.gpr.get 1) := by
  have hd := keccakChiMpc_decoded
  cases hf : findSliceByNameBytes currentX86ExtractedSlices
      keccakChiMpcName with
  | none => rw [hf] at hd; contradiction
  | some slice =>
    rw [hf] at hd
    refine ⟨slice, keccakChiMpcProg, rfl, hd, ?_⟩
    rcases s with ⟨pc, ⟨r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15⟩,
      y, cf, o, zf, dy, hlt, mem⟩
    rcases h with ⟨hp, hh, hdisj⟩
    dsimp only at hp hh
    subst pc hlt
    intro extra
    have he := (keccakChiMpc_reaches r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11
      r12 r13 r14 r15 y cf o zf dy mem hdisj extra).1
    let t : X86State :=
      ⟨318, ⟨0, 0, 0, r3, r4, r5, 0, 0, 0, 0, 0, 0, r12, r13, r14, r15⟩,
        Bank16.const Vec256.zero, false, false, true, false, true,
        keccakChiMpcOutMem mem r7 r6 r2 r1⟩
    rw [runX86_halted_fst keccakChiMpcProg extra t rfl] at he
    rw [he]
    exact ⟨rfl, rfl⟩

theorem keccakChiMpc_inhabited : ∃ s : X86State, keccakChiMpcInitial s := by
  refine ⟨⟨0, Bank16.ofFn (fun i => if i == 1 then 256 else 0),
    Bank16.const Vec256.zero, false, false, false, false, false, fun _ => 0⟩,
    rfl, rfl, ?_⟩
  change keccakChiMpcSeparated 0 256
  intro i j hi hj he
  have hn := congrArg UInt64.toNat he
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat, UInt64.toNat_ofNat'] at hn
  omega

/-- The wrong specification that always writes zero fails on a single set input bit. -/
theorem keccakChiMpc_current_tooth :
    keccakChiMpcOutMem (fun a => if a == 64 then 1 else 0) 1024 0 256 512 1024 ≠ 0 := by
  decide +kernel

#tooth_pair keccakChiMpc_current_functional vs keccakChiMpc_current_tooth
#verify_inhabited keccakChiMpc_current_functional keccakChiMpc_inhabited

/-- Select one of the four 64-bit words of a vector (`q < 4` at callers). -/
def keccakChiMpcVecWord (v : Vec256) : Nat → UInt64
  | 0 => v.w0
  | 1 => v.w1
  | 2 => v.w2
  | _ => v.w3

def keccakChiMpcReadRows (mem : UInt64 → UInt8) (ptr : UInt64) (x q : Nat) : UInt64 :=
  keccakChiMpcVecWord (readMem256 mem (ptr + UInt64.ofNat (32 * x))) q

theorem keccakChiMpcOutVec_word (mem : UInt64 → UInt8) (s0 s1 mask : UInt64) (x q : Nat) :
    keccakChiMpcVecWord (keccakChiMpcOutVec mem s0 s1 mask x) q =
      keccakChiMpcRowWord (keccakChiMpcReadRows mem s0)
        (keccakChiMpcReadRows mem s1) (keccakChiMpcReadRows mem mask) x q := by
  match q with
  | 0 | 1 | 2 | _ + 3 => rfl

/-- All five vector stores read back in their entirety, including wrapping
addresses; distinct offsets below 160 remain distinct modulo 2^64. -/
theorem keccakChiMpcOutMem_readback (mem : UInt64 → UInt8) (dst s0 s1 mask : UInt64)
    (x : Nat) (hx : x < 5) :
    readMem256 (keccakChiMpcOutMem mem dst s0 s1 mask)
      (dst + UInt64.ofNat (32 * x)) = keccakChiMpcOutVec mem s0 s1 mask x := by
  have hd (o1 o2 : Nat) (h1 : o1 ≤ 128) (h2 : o2 ≤ 128)
      (hgap : o1 + 32 ≤ o2 ∨ o2 + 32 ≤ o1)
      (m : UInt64 → UInt8) (v : Vec256) :
      readMem256 (writeMem256 m (dst + UInt64.ofNat o2) v) (dst + UInt64.ofNat o1) =
        readMem256 m (dst + UInt64.ofNat o1) := by
    apply keccakChiMpc_readMem256_writeMem256_disjoint
    intro i j hi hj heq
    rw [u64_add_ofNat_assoc dst o1 i (by omega),
      u64_add_ofNat_assoc dst o2 j (by omega)] at heq
    have := u64_add_ofNat_inj (by omega) (by omega) heq
    omega
  unfold keccakChiMpcOutMem
  dsimp only
  have hn0 : UInt64.ofNat 0 = (0 : UInt64) := by decide +kernel
  have hn32 : UInt64.ofNat 32 = (32 : UInt64) := by decide +kernel
  have hn64 : UInt64.ofNat 64 = (64 : UInt64) := by decide +kernel
  have hn96 : UInt64.ofNat 96 = (96 : UInt64) := by decide +kernel
  have hn128 : UInt64.ofNat 128 = (128 : UInt64) := by decide +kernel
  rw [← hn0, ← hn32, ← hn64, ← hn96, ← hn128]
  match x, hx with
  | 0, _ =>
    rw [hd 0 128 (by decide) (by decide) (by omega),
      hd 0 96 (by decide) (by decide) (by omega),
      hd 0 64 (by decide) (by decide) (by omega),
      hd 0 32 (by decide) (by decide) (by omega),
      keccakChiMpc_readMem256_writeMem256_same]
  | 1, _ =>
    rw [hd 32 128 (by decide) (by decide) (by omega),
      hd 32 96 (by decide) (by decide) (by omega),
      hd 32 64 (by decide) (by decide) (by omega),
      keccakChiMpc_readMem256_writeMem256_same]
  | 2, _ =>
    rw [hd 64 128 (by decide) (by decide) (by omega),
      hd 64 96 (by decide) (by decide) (by omega),
      keccakChiMpc_readMem256_writeMem256_same]
  | 3, _ =>
    rw [hd 96 128 (by decide) (by decide) (by omega),
      keccakChiMpc_readMem256_writeMem256_same]
  | 4, _ => exact keccakChiMpc_readMem256_writeMem256_same _ _ _
  | _ + 5, h => omega

theorem keccakChiMpcOutMem_readRows (mem : UInt64 → UInt8) (dst s0 s1 mask : UInt64)
    (x q : Nat) (hx : x < 5) :
    keccakChiMpcReadRows (keccakChiMpcOutMem mem dst s0 s1 mask) dst x q =
      keccakChiMpcRowWord (keccakChiMpcReadRows mem s0)
        (keccakChiMpcReadRows mem s1) (keccakChiMpcReadRows mem mask) x q := by
  unfold keccakChiMpcReadRows
  rw [keccakChiMpcOutMem_readback _ _ _ _ _ x hx]
  exact keccakChiMpcOutVec_word mem s0 s1 mask x q

/-- Cyclic replicated shares agree only on the 160 bytes actually read, with no
constraints on unrelated memory, scratch registers, or output values. -/
def keccakChiMpcSharesMatch (s t : X86State) : Prop :=
  ∀ x q : Nat, x < 5 → q < 4 →
    keccakChiMpcReadRows s.mem (s.gpr.get 2) x q =
      keccakChiMpcReadRows t.mem (t.gpr.get 6) x q

def keccakChiMpcMasksZero (s0 s1 s2 : X86State) : Prop :=
  ∀ x q : Nat, x < 5 → q < 4 →
    keccakChiMpcReadRows s0.mem (s0.gpr.get 1) x q ^^^
      keccakChiMpcReadRows s1.mem (s1.gpr.get 1) x q ^^^
      keccakChiMpcReadRows s2.mem (s2.gpr.get 1) x q = 0

/-- The mathematical reconstruction of all five stored vectors, independent of
machine scheduling. This composes the byte-memory readback with the RSS identity. -/
theorem keccakChiMpcOutMem_reconstruct
    (s0 s1 s2 : X86State)
    (h01 : keccakChiMpcSharesMatch s0 s1)
    (h12 : keccakChiMpcSharesMatch s1 s2)
    (h20 : keccakChiMpcSharesMatch s2 s0)
    (hm : keccakChiMpcMasksZero s0 s1 s2) (q : Nat) (hq : q < 4) :
    keccakChiMpcRowState (fun x j =>
      keccakChiMpcReadRows
        (keccakChiMpcOutMem s0.mem (s0.gpr.get 7) (s0.gpr.get 6) (s0.gpr.get 2) (s0.gpr.get 1))
        (s0.gpr.get 7) x j ^^^
      keccakChiMpcReadRows
        (keccakChiMpcOutMem s1.mem (s1.gpr.get 7) (s1.gpr.get 6) (s1.gpr.get 2) (s1.gpr.get 1))
        (s1.gpr.get 7) x j ^^^
      keccakChiMpcReadRows
        (keccakChiMpcOutMem s2.mem (s2.gpr.get 7) (s2.gpr.get 6) (s2.gpr.get 2) (s2.gpr.get 1))
        (s2.gpr.get 7) x j) q =
    chiS (keccakChiMpcRowState (fun x j =>
      keccakChiMpcReadRows s0.mem (s0.gpr.get 6) x j ^^^
      keccakChiMpcReadRows s1.mem (s1.gpr.get 6) x j ^^^
      keccakChiMpcReadRows s2.mem (s2.gpr.get 6) x j) q) := by
  let a0 := keccakChiMpcReadRows s0.mem (s0.gpr.get 6)
  let a1 := keccakChiMpcReadRows s1.mem (s1.gpr.get 6)
  let a2 := keccakChiMpcReadRows s2.mem (s2.gpr.get 6)
  let r0 := keccakChiMpcReadRows s0.mem (s0.gpr.get 1)
  let r1 := keccakChiMpcReadRows s1.mem (s1.gpr.get 1)
  let r2 := keccakChiMpcReadRows s2.mem (s2.gpr.get 1)
  have ho (s t : X86State) (hst : keccakChiMpcSharesMatch s t) (x : Nat) (hx : x < 5) :
      keccakChiMpcReadRows
        (keccakChiMpcOutMem s.mem (s.gpr.get 7) (s.gpr.get 6) (s.gpr.get 2) (s.gpr.get 1))
        (s.gpr.get 7) x q =
      keccakChiMpcRowWord (keccakChiMpcReadRows s.mem (s.gpr.get 6))
        (keccakChiMpcReadRows t.mem (t.gpr.get 6)) (keccakChiMpcReadRows s.mem (s.gpr.get 1)) x q := by
    rw [keccakChiMpcOutMem_readRows _ _ _ _ _ x q hx]
    unfold keccakChiMpcRowWord
    rw [hst ((x + 1) % 5) q (Nat.mod_lt _ (by decide)) hq,
      hst ((x + 2) % 5) q (Nat.mod_lt _ (by decide)) hq]
  have hrecon := keccakChiMpcRow_reconstruct a0 a1 a2 r0 r1 r2 hm q hq
  calc
    _ = keccakChiMpcRowState (fun x j =>
          keccakChiMpcRowWord a0 a1 r0 x j ^^^ keccakChiMpcRowWord a1 a2 r1 x j ^^^
            keccakChiMpcRowWord a2 a0 r2 x j) q := by
      unfold keccakChiMpcRowState
      dsimp only
      congr 1
      all_goals rw [ho s0 s1 h01 _ (by decide), ho s1 s2 h12 _ (by decide),
        ho s2 s0 h20 _ (by decide)]
    _ = _ := hrecon


/-- Fresh machine-code RSS chi reconstruction for all 1,280 gates: three
cyclic-party executions halt and their complete four rows reconstruct `chiS`.
Only the input replicated shares and correlated masks are related. -/
theorem keccakChiMpc_current_reconstruct
    (s0 s1 s2 : X86State)
    (h0 : keccakChiMpcInitial s0) (h1 : keccakChiMpcInitial s1) (h2 : keccakChiMpcInitial s2)
    (h01 : keccakChiMpcSharesMatch s0 s1)
    (h12 : keccakChiMpcSharesMatch s1 s2)
    (h20 : keccakChiMpcSharesMatch s2 s0)
    (hm : keccakChiMpcMasksZero s0 s1 s2) :
    ∃ slice prog,
      findSliceByNameBytes currentX86ExtractedSlices keccakChiMpcName = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      ∀ extra : Nat,
        (runX86 prog (74 + extra) s0).1.halted = true ∧
        (runX86 prog (74 + extra) s1).1.halted = true ∧
        (runX86 prog (74 + extra) s2).1.halted = true ∧
        ∀ q : Nat, q < 4 →
          keccakChiMpcRowState (fun x j =>
            keccakChiMpcReadRows (runX86 prog (74 + extra) s0).1.mem (s0.gpr.get 7) x j ^^^
            keccakChiMpcReadRows (runX86 prog (74 + extra) s1).1.mem (s1.gpr.get 7) x j ^^^
            keccakChiMpcReadRows (runX86 prog (74 + extra) s2).1.mem (s2.gpr.get 7) x j) q =
          chiS (keccakChiMpcRowState (fun x j =>
            keccakChiMpcReadRows s0.mem (s0.gpr.get 6) x j ^^^
            keccakChiMpcReadRows s1.mem (s1.gpr.get 6) x j ^^^
            keccakChiMpcReadRows s2.mem (s2.gpr.get 6) x j) q) := by
  obtain ⟨sl0, p0, hf0, hd0, he0⟩ := keccakChiMpc_current_functional s0 h0
  obtain ⟨sl1, p1, hf1, hd1, he1⟩ := keccakChiMpc_current_functional s1 h1
  obtain ⟨sl2, p2, hf2, hd2, he2⟩ := keccakChiMpc_current_functional s2 h2
  have hs1 : sl1 = sl0 := Option.some.inj (hf1.symm.trans hf0)
  have hs2 : sl2 = sl0 := Option.some.inj (hf2.symm.trans hf0)
  subst sl1 sl2
  have hp1 : p1 = p0 := Option.some.inj (hd1.symm.trans hd0)
  have hp2 : p2 = p0 := Option.some.inj (hd2.symm.trans hd0)
  subst p1 p2
  refine ⟨sl0, p0, hf0, hd0, ?_⟩
  intro extra
  obtain ⟨hh0, he0⟩ := he0 extra
  obtain ⟨hh1, he1⟩ := he1 extra
  obtain ⟨hh2, he2⟩ := he2 extra
  refine ⟨hh0, hh1, hh2, ?_⟩
  intro q hq
  rw [he0, he1, he2]
  exact keccakChiMpcOutMem_reconstruct s0 s1 s2 h01 h12 h20 hm q hq

/-- A concrete valid party: disjoint output/mask buffers and zero input shares. -/
def keccakChiMpcZeroParty : X86State :=
  ⟨0, Bank16.ofFn (fun i => if i == 1 then 256 else 0),
    Bank16.const Vec256.zero, false, false, false, false, false, fun _ => 0⟩

theorem keccakChiMpc_reconstruct_inhabited :
    ∃ s0 s1 s2 : X86State,
      keccakChiMpcInitial s0 ∧ keccakChiMpcInitial s1 ∧ keccakChiMpcInitial s2 ∧
      keccakChiMpcSharesMatch s0 s1 ∧ keccakChiMpcSharesMatch s1 s2 ∧
      keccakChiMpcSharesMatch s2 s0 ∧ keccakChiMpcMasksZero s0 s1 s2 := by
  have hi : keccakChiMpcInitial keccakChiMpcZeroParty := by
    refine ⟨rfl, rfl, ?_⟩
    change keccakChiMpcSeparated 0 256
    intro i j hi hj he
    have hn := congrArg UInt64.toNat he
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat, UInt64.toNat_ofNat'] at hn
    omega
  have hs : keccakChiMpcSharesMatch keccakChiMpcZeroParty keccakChiMpcZeroParty := by
    intro x q _ _
    rfl
  have hz (p : UInt64) (x q : Nat) (hq : q < 4) :
      keccakChiMpcReadRows (fun _ => 0) p x q = 0 := by
    unfold keccakChiMpcReadRows readMem256 readMem64
    dsimp only
    match q, hq with
    | 0, _ | 1, _ | 2, _ | 3, _ =>
      dsimp only [keccakChiMpcVecWord]
      decide +kernel
    | n + 4, h => omega
  refine ⟨keccakChiMpcZeroParty, keccakChiMpcZeroParty, keccakChiMpcZeroParty,
    hi, hi, hi, hs, hs, hs, ?_⟩
  intro x q _ hq
  change keccakChiMpcReadRows (fun _ => 0) 256 x q ^^^
    keccakChiMpcReadRows (fun _ => 0) 256 x q ^^^
    keccakChiMpcReadRows (fun _ => 0) 256 x q = 0
  rw [hz _ _ _ hq]
  decide +kernel

/-- The zero-output specification is refuted by a nonzero reconstructed row. -/
theorem keccakChiMpc_reconstruct_tooth :
    chiS (keccakChiMpcRowState (fun x _ => if x == 2 then 1 else 0) 0) ≠ zeroKState := by
  decide +kernel

#tooth_pair keccakChiMpc_current_reconstruct vs keccakChiMpc_reconstruct_tooth
#verify_inhabited keccakChiMpc_current_reconstruct keccakChiMpc_reconstruct_inhabited

end KeccakMpcFreshVerification

section KeccakThetaRhoFreshVerification
set_option linter.unusedSimpArgs false

/-! Full two-sponge theta/rho/pi kernel. -/

def keccakThetaRhoProg : List (DecodedInstr Arm64Instr) := [
  ⟨0, 4, .ldrQ 0 1 0⟩,
  ⟨4, 4, .ldrQ 5 1 80⟩,
  ⟨8, 4, .ldrQ 6 1 160⟩,
  ⟨12, 4, .veor3_16b 0 0 5 6⟩,
  ⟨16, 4, .ldrQ 5 1 240⟩,
  ⟨20, 4, .ldrQ 6 1 320⟩,
  ⟨24, 4, .veor3_16b 0 0 5 6⟩,
  ⟨28, 4, .ldrQ 1 1 16⟩,
  ⟨32, 4, .ldrQ 5 1 96⟩,
  ⟨36, 4, .ldrQ 6 1 176⟩,
  ⟨40, 4, .veor3_16b 1 1 5 6⟩,
  ⟨44, 4, .ldrQ 5 1 256⟩,
  ⟨48, 4, .ldrQ 6 1 336⟩,
  ⟨52, 4, .veor3_16b 1 1 5 6⟩,
  ⟨56, 4, .ldrQ 2 1 32⟩,
  ⟨60, 4, .ldrQ 5 1 112⟩,
  ⟨64, 4, .ldrQ 6 1 192⟩,
  ⟨68, 4, .veor3_16b 2 2 5 6⟩,
  ⟨72, 4, .ldrQ 5 1 272⟩,
  ⟨76, 4, .ldrQ 6 1 352⟩,
  ⟨80, 4, .veor3_16b 2 2 5 6⟩,
  ⟨84, 4, .ldrQ 3 1 48⟩,
  ⟨88, 4, .ldrQ 5 1 128⟩,
  ⟨92, 4, .ldrQ 6 1 208⟩,
  ⟨96, 4, .veor3_16b 3 3 5 6⟩,
  ⟨100, 4, .ldrQ 5 1 288⟩,
  ⟨104, 4, .ldrQ 6 1 368⟩,
  ⟨108, 4, .veor3_16b 3 3 5 6⟩,
  ⟨112, 4, .ldrQ 4 1 64⟩,
  ⟨116, 4, .ldrQ 5 1 144⟩,
  ⟨120, 4, .ldrQ 6 1 224⟩,
  ⟨124, 4, .veor3_16b 4 4 5 6⟩,
  ⟨128, 4, .ldrQ 5 1 304⟩,
  ⟨132, 4, .ldrQ 6 1 384⟩,
  ⟨136, 4, .veor3_16b 4 4 5 6⟩,
  ⟨140, 4, .vrax1_2d 16 4 1⟩,
  ⟨144, 4, .vrax1_2d 17 0 2⟩,
  ⟨148, 4, .vrax1_2d 18 1 3⟩,
  ⟨152, 4, .vrax1_2d 19 2 4⟩,
  ⟨156, 4, .vrax1_2d 20 3 0⟩,
  ⟨160, 4, .ldrQ 0 1 0⟩,
  ⟨164, 4, .vxar_2d 0 0 16 0⟩,
  ⟨168, 4, .strQ 0 0 0⟩,
  ⟨172, 4, .ldrQ 0 1 16⟩,
  ⟨176, 4, .vxar_2d 0 0 17 63⟩,
  ⟨180, 4, .strQ 0 0 160⟩,
  ⟨184, 4, .ldrQ 0 1 32⟩,
  ⟨188, 4, .vxar_2d 0 0 18 2⟩,
  ⟨192, 4, .strQ 0 0 320⟩,
  ⟨196, 4, .ldrQ 0 1 48⟩,
  ⟨200, 4, .vxar_2d 0 0 19 36⟩,
  ⟨204, 4, .strQ 0 0 80⟩,
  ⟨208, 4, .ldrQ 0 1 64⟩,
  ⟨212, 4, .vxar_2d 0 0 20 37⟩,
  ⟨216, 4, .strQ 0 0 240⟩,
  ⟨220, 4, .ldrQ 0 1 80⟩,
  ⟨224, 4, .vxar_2d 0 0 16 28⟩,
  ⟨228, 4, .strQ 0 0 256⟩,
  ⟨232, 4, .ldrQ 0 1 96⟩,
  ⟨236, 4, .vxar_2d 0 0 17 20⟩,
  ⟨240, 4, .strQ 0 0 16⟩,
  ⟨244, 4, .ldrQ 0 1 112⟩,
  ⟨248, 4, .vxar_2d 0 0 18 58⟩,
  ⟨252, 4, .strQ 0 0 176⟩,
  ⟨256, 4, .ldrQ 0 1 128⟩,
  ⟨260, 4, .vxar_2d 0 0 19 9⟩,
  ⟨264, 4, .strQ 0 0 336⟩,
  ⟨268, 4, .ldrQ 0 1 144⟩,
  ⟨272, 4, .vxar_2d 0 0 20 44⟩,
  ⟨276, 4, .strQ 0 0 96⟩,
  ⟨280, 4, .ldrQ 0 1 160⟩,
  ⟨284, 4, .vxar_2d 0 0 16 61⟩,
  ⟨288, 4, .strQ 0 0 112⟩,
  ⟨292, 4, .ldrQ 0 1 176⟩,
  ⟨296, 4, .vxar_2d 0 0 17 54⟩,
  ⟨300, 4, .strQ 0 0 272⟩,
  ⟨304, 4, .ldrQ 0 1 192⟩,
  ⟨308, 4, .vxar_2d 0 0 18 21⟩,
  ⟨312, 4, .strQ 0 0 32⟩,
  ⟨316, 4, .ldrQ 0 1 208⟩,
  ⟨320, 4, .vxar_2d 0 0 19 39⟩,
  ⟨324, 4, .strQ 0 0 192⟩,
  ⟨328, 4, .ldrQ 0 1 224⟩,
  ⟨332, 4, .vxar_2d 0 0 20 25⟩,
  ⟨336, 4, .strQ 0 0 352⟩,
  ⟨340, 4, .ldrQ 0 1 240⟩,
  ⟨344, 4, .vxar_2d 0 0 16 23⟩,
  ⟨348, 4, .strQ 0 0 368⟩,
  ⟨352, 4, .ldrQ 0 1 256⟩,
  ⟨356, 4, .vxar_2d 0 0 17 19⟩,
  ⟨360, 4, .strQ 0 0 128⟩,
  ⟨364, 4, .ldrQ 0 1 272⟩,
  ⟨368, 4, .vxar_2d 0 0 18 49⟩,
  ⟨372, 4, .strQ 0 0 288⟩,
  ⟨376, 4, .ldrQ 0 1 288⟩,
  ⟨380, 4, .vxar_2d 0 0 19 43⟩,
  ⟨384, 4, .strQ 0 0 48⟩,
  ⟨388, 4, .ldrQ 0 1 304⟩,
  ⟨392, 4, .vxar_2d 0 0 20 56⟩,
  ⟨396, 4, .strQ 0 0 208⟩,
  ⟨400, 4, .ldrQ 0 1 320⟩,
  ⟨404, 4, .vxar_2d 0 0 16 46⟩,
  ⟨408, 4, .strQ 0 0 224⟩,
  ⟨412, 4, .ldrQ 0 1 336⟩,
  ⟨416, 4, .vxar_2d 0 0 17 62⟩,
  ⟨420, 4, .strQ 0 0 384⟩,
  ⟨424, 4, .ldrQ 0 1 352⟩,
  ⟨428, 4, .vxar_2d 0 0 18 3⟩,
  ⟨432, 4, .strQ 0 0 144⟩,
  ⟨436, 4, .ldrQ 0 1 368⟩,
  ⟨440, 4, .vxar_2d 0 0 19 8⟩,
  ⟨444, 4, .strQ 0 0 304⟩,
  ⟨448, 4, .ldrQ 0 1 384⟩,
  ⟨452, 4, .vxar_2d 0 0 20 50⟩,
  ⟨456, 4, .strQ 0 0 64⟩,
  ⟨460, 4, .veor16b 0 0 0⟩,
  ⟨464, 4, .veor16b 1 1 1⟩,
  ⟨468, 4, .veor16b 2 2 2⟩,
  ⟨472, 4, .veor16b 3 3 3⟩,
  ⟨476, 4, .veor16b 4 4 4⟩,
  ⟨480, 4, .veor16b 5 5 5⟩,
  ⟨484, 4, .veor16b 6 6 6⟩,
  ⟨488, 4, .veor16b 16 16 16⟩,
  ⟨492, 4, .veor16b 17 17 17⟩,
  ⟨496, 4, .veor16b 18 18 18⟩,
  ⟨500, 4, .veor16b 19 19 19⟩,
  ⟨504, 4, .veor16b 20 20 20⟩,
  ⟨508, 4, .ret⟩]

def keccakThetaRhoName : List UInt8 := [113, 115, 97, 103, 95, 97, 115, 109, 95, 107, 101, 99, 99, 97, 107, 95, 116, 104, 101, 116, 97, 95, 114, 104, 111, 95, 115, 104, 97, 51, 95, 110, 101, 111, 110]

theorem keccakThetaRho_decode :
    (findSliceByNameBytes currentAarch64ExtractedSlices keccakThetaRhoName).bind
      (fun s => decodeArm64Slice s.code) = some keccakThetaRhoProg := by decide +kernel

/-- Bytewise disjoint input and output regions, including modular addresses. -/
def keccakThetaRhoDisjoint (outPtr inPtr : UInt64) : Prop :=
  ∀ i j : Nat, i < 400 → j < 400 →
    inPtr + UInt64.ofNat i ≠ outPtr + UInt64.ofNat j

theorem keccakThetaRho_readWrite (outPtr inPtr : UInt64)
    (hd : keccakThetaRhoDisjoint outPtr inPtr)
    (m : UInt64 → UInt8) (v : Vec128) (i j : Nat) (hi : i ≤ 384) (hj : j ≤ 384) :
    readMem128 (writeMem128 m (outPtr + UInt64.ofNat j) v) (inPtr + UInt64.ofNat i) =
      readMem128 m (inPtr + UInt64.ofNat i) := by
  unfold readMem128
  congr 1
  · apply readMem64_writeMem128_disjoint
    intro a b ha hb he
    rw [u64_add_ofNat_assoc inPtr i a (by omega),
      u64_add_ofNat_assoc outPtr j b (by omega)] at he
    exact hd (i+a) (j+b) (by omega) (by omega) he
  · apply readMem64_writeMem128_disjoint
    intro a b ha hb he
    change ((inPtr + UInt64.ofNat i) + UInt64.ofNat 8) + UInt64.ofNat a = _ at he
    rw [u64_add_ofNat_assoc inPtr i 8 (by omega),
      u64_add_ofNat_assoc inPtr (i+8) a (by omega),
      u64_add_ofNat_assoc outPtr j b (by omega)] at he
    exact hd (i+8+a) (j+b) (by omega) (by omega) he

def keccakThetaRhoLoad (m : UInt64 → UInt8) (p : UInt64) (block : Nat) : KState :=
  ⟨(if block == 0 then (readMem128 m (p + 0)).w0 else (readMem128 m (p + 0)).w1),
   (if block == 0 then (readMem128 m (p + 16)).w0 else (readMem128 m (p + 16)).w1),
   (if block == 0 then (readMem128 m (p + 32)).w0 else (readMem128 m (p + 32)).w1),
   (if block == 0 then (readMem128 m (p + 48)).w0 else (readMem128 m (p + 48)).w1),
   (if block == 0 then (readMem128 m (p + 64)).w0 else (readMem128 m (p + 64)).w1),
   (if block == 0 then (readMem128 m (p + 80)).w0 else (readMem128 m (p + 80)).w1),
   (if block == 0 then (readMem128 m (p + 96)).w0 else (readMem128 m (p + 96)).w1),
   (if block == 0 then (readMem128 m (p + 112)).w0 else (readMem128 m (p + 112)).w1),
   (if block == 0 then (readMem128 m (p + 128)).w0 else (readMem128 m (p + 128)).w1),
   (if block == 0 then (readMem128 m (p + 144)).w0 else (readMem128 m (p + 144)).w1),
   (if block == 0 then (readMem128 m (p + 160)).w0 else (readMem128 m (p + 160)).w1),
   (if block == 0 then (readMem128 m (p + 176)).w0 else (readMem128 m (p + 176)).w1),
   (if block == 0 then (readMem128 m (p + 192)).w0 else (readMem128 m (p + 192)).w1),
   (if block == 0 then (readMem128 m (p + 208)).w0 else (readMem128 m (p + 208)).w1),
   (if block == 0 then (readMem128 m (p + 224)).w0 else (readMem128 m (p + 224)).w1),
   (if block == 0 then (readMem128 m (p + 240)).w0 else (readMem128 m (p + 240)).w1),
   (if block == 0 then (readMem128 m (p + 256)).w0 else (readMem128 m (p + 256)).w1),
   (if block == 0 then (readMem128 m (p + 272)).w0 else (readMem128 m (p + 272)).w1),
   (if block == 0 then (readMem128 m (p + 288)).w0 else (readMem128 m (p + 288)).w1),
   (if block == 0 then (readMem128 m (p + 304)).w0 else (readMem128 m (p + 304)).w1),
   (if block == 0 then (readMem128 m (p + 320)).w0 else (readMem128 m (p + 320)).w1),
   (if block == 0 then (readMem128 m (p + 336)).w0 else (readMem128 m (p + 336)).w1),
   (if block == 0 then (readMem128 m (p + 352)).w0 else (readMem128 m (p + 352)).w1),
   (if block == 0 then (readMem128 m (p + 368)).w0 else (readMem128 m (p + 368)).w1),
   (if block == 0 then (readMem128 m (p + 384)).w0 else (readMem128 m (p + 384)).w1)⟩

def keccakThetaRhoOut (m : UInt64 → UInt8) (outPtr inPtr : UInt64) : UInt64 → UInt8 :=
  let k0 := rhoPiS (thetaS (keccakThetaRhoLoad m inPtr 0))
  let k1 := rhoPiS (thetaS (keccakThetaRhoLoad m inPtr 1))
  let m1 := writeMem128 m (outPtr + 0) ⟨k0.a0, k1.a0⟩
  let m2 := writeMem128 m1 (outPtr + 160) ⟨k0.a10, k1.a10⟩
  let m3 := writeMem128 m2 (outPtr + 320) ⟨k0.a20, k1.a20⟩
  let m4 := writeMem128 m3 (outPtr + 80) ⟨k0.a5, k1.a5⟩
  let m5 := writeMem128 m4 (outPtr + 240) ⟨k0.a15, k1.a15⟩
  let m6 := writeMem128 m5 (outPtr + 256) ⟨k0.a16, k1.a16⟩
  let m7 := writeMem128 m6 (outPtr + 16) ⟨k0.a1, k1.a1⟩
  let m8 := writeMem128 m7 (outPtr + 176) ⟨k0.a11, k1.a11⟩
  let m9 := writeMem128 m8 (outPtr + 336) ⟨k0.a21, k1.a21⟩
  let m10 := writeMem128 m9 (outPtr + 96) ⟨k0.a6, k1.a6⟩
  let m11 := writeMem128 m10 (outPtr + 112) ⟨k0.a7, k1.a7⟩
  let m12 := writeMem128 m11 (outPtr + 272) ⟨k0.a17, k1.a17⟩
  let m13 := writeMem128 m12 (outPtr + 32) ⟨k0.a2, k1.a2⟩
  let m14 := writeMem128 m13 (outPtr + 192) ⟨k0.a12, k1.a12⟩
  let m15 := writeMem128 m14 (outPtr + 352) ⟨k0.a22, k1.a22⟩
  let m16 := writeMem128 m15 (outPtr + 368) ⟨k0.a23, k1.a23⟩
  let m17 := writeMem128 m16 (outPtr + 128) ⟨k0.a8, k1.a8⟩
  let m18 := writeMem128 m17 (outPtr + 288) ⟨k0.a18, k1.a18⟩
  let m19 := writeMem128 m18 (outPtr + 48) ⟨k0.a3, k1.a3⟩
  let m20 := writeMem128 m19 (outPtr + 208) ⟨k0.a13, k1.a13⟩
  let m21 := writeMem128 m20 (outPtr + 224) ⟨k0.a14, k1.a14⟩
  let m22 := writeMem128 m21 (outPtr + 384) ⟨k0.a24, k1.a24⟩
  let m23 := writeMem128 m22 (outPtr + 144) ⟨k0.a9, k1.a9⟩
  let m24 := writeMem128 m23 (outPtr + 304) ⟨k0.a19, k1.a19⟩
  let m25 := writeMem128 m24 (outPtr + 64) ⟨k0.a4, k1.a4⟩
  m25

theorem keccakThetaRho_or_comm (a b : UInt64) : a ||| b = b ||| a := by
  apply UInt64.eq_of_toBitVec_eq
  simp only [UInt64.toBitVec_or, BitVec.or_comm]


def keccakThetaRhoPerm (i : Nat) : Nat := i / 5 + 5 * ((2 * (i % 5) + 3 * (i / 5)) % 5)

def keccakThetaRhoRor : Nat → Nat
  | 0 => 0
  | 1 => 63
  | 2 => 2
  | 3 => 36
  | 4 => 37
  | 5 => 28
  | 6 => 20
  | 7 => 58
  | 8 => 9
  | 9 => 44
  | 10 => 61
  | 11 => 54
  | 12 => 21
  | 13 => 39
  | 14 => 25
  | 15 => 23
  | 16 => 19
  | 17 => 49
  | 18 => 43
  | 19 => 56
  | 20 => 46
  | 21 => 62
  | 22 => 3
  | 23 => 8
  | 24 => 50
  | _ => 0

def keccakThetaRhoGet (k : KState) : Nat → UInt64
  | 0 => k.a0
  | 1 => k.a1
  | 2 => k.a2
  | 3 => k.a3
  | 4 => k.a4
  | 5 => k.a5
  | 6 => k.a6
  | 7 => k.a7
  | 8 => k.a8
  | 9 => k.a9
  | 10 => k.a10
  | 11 => k.a11
  | 12 => k.a12
  | 13 => k.a13
  | 14 => k.a14
  | 15 => k.a15
  | 16 => k.a16
  | 17 => k.a17
  | 18 => k.a18
  | 19 => k.a19
  | 20 => k.a20
  | 21 => k.a21
  | 22 => k.a22
  | 23 => k.a23
  | _ => k.a24

def keccakThetaRhoVec (m : UInt64 → UInt8) (p : UInt64) (i : Nat) : Vec128 :=
  ⟨keccakThetaRhoGet (rhoPiS (thetaS (keccakThetaRhoLoad m p 0))) (keccakThetaRhoPerm i),
   keccakThetaRhoGet (rhoPiS (thetaS (keccakThetaRhoLoad m p 1))) (keccakThetaRhoPerm i)⟩

def keccakThetaRhoD (m : UInt64 → UInt8) (p : UInt64) (x : Nat) : Vec128 :=
  let c00 := (readMem128 m (p + 0)).w0 ^^^ (readMem128 m (p + 80)).w0 ^^^ (readMem128 m (p + 160)).w0 ^^^ (readMem128 m (p + 240)).w0 ^^^ (readMem128 m (p + 320)).w0
  let c01 := (readMem128 m (p + 0)).w1 ^^^ (readMem128 m (p + 80)).w1 ^^^ (readMem128 m (p + 160)).w1 ^^^ (readMem128 m (p + 240)).w1 ^^^ (readMem128 m (p + 320)).w1
  let c10 := (readMem128 m (p + 16)).w0 ^^^ (readMem128 m (p + 96)).w0 ^^^ (readMem128 m (p + 176)).w0 ^^^ (readMem128 m (p + 256)).w0 ^^^ (readMem128 m (p + 336)).w0
  let c11 := (readMem128 m (p + 16)).w1 ^^^ (readMem128 m (p + 96)).w1 ^^^ (readMem128 m (p + 176)).w1 ^^^ (readMem128 m (p + 256)).w1 ^^^ (readMem128 m (p + 336)).w1
  let c20 := (readMem128 m (p + 32)).w0 ^^^ (readMem128 m (p + 112)).w0 ^^^ (readMem128 m (p + 192)).w0 ^^^ (readMem128 m (p + 272)).w0 ^^^ (readMem128 m (p + 352)).w0
  let c21 := (readMem128 m (p + 32)).w1 ^^^ (readMem128 m (p + 112)).w1 ^^^ (readMem128 m (p + 192)).w1 ^^^ (readMem128 m (p + 272)).w1 ^^^ (readMem128 m (p + 352)).w1
  let c30 := (readMem128 m (p + 48)).w0 ^^^ (readMem128 m (p + 128)).w0 ^^^ (readMem128 m (p + 208)).w0 ^^^ (readMem128 m (p + 288)).w0 ^^^ (readMem128 m (p + 368)).w0
  let c31 := (readMem128 m (p + 48)).w1 ^^^ (readMem128 m (p + 128)).w1 ^^^ (readMem128 m (p + 208)).w1 ^^^ (readMem128 m (p + 288)).w1 ^^^ (readMem128 m (p + 368)).w1
  let c40 := (readMem128 m (p + 64)).w0 ^^^ (readMem128 m (p + 144)).w0 ^^^ (readMem128 m (p + 224)).w0 ^^^ (readMem128 m (p + 304)).w0 ^^^ (readMem128 m (p + 384)).w0
  let c41 := (readMem128 m (p + 64)).w1 ^^^ (readMem128 m (p + 144)).w1 ^^^ (readMem128 m (p + 224)).w1 ^^^ (readMem128 m (p + 304)).w1 ^^^ (readMem128 m (p + 384)).w1
  match x with
  | 0 => ⟨c40 ^^^ rotlK c10 1 63, c41 ^^^ rotlK c11 1 63⟩
  | 1 => ⟨c00 ^^^ rotlK c20 1 63, c01 ^^^ rotlK c21 1 63⟩
  | 2 => ⟨c10 ^^^ rotlK c30 1 63, c11 ^^^ rotlK c31 1 63⟩
  | 3 => ⟨c20 ^^^ rotlK c40 1 63, c21 ^^^ rotlK c41 1 63⟩
  | 4 => ⟨c30 ^^^ rotlK c00 1 63, c31 ^^^ rotlK c01 1 63⟩
  | _ => Vec128.zero

def keccakThetaRhoXar (a b : Vec128) (imm : Nat) : Vec128 :=
  let r (x : UInt64) := if imm % 64 == 0 then x
    else (x >>> UInt64.ofNat (imm % 64)) ||| (x <<< UInt64.ofNat (64 - imm % 64))
  ⟨r (a.w0 ^^^ b.w0), r (a.w1 ^^^ b.w1)⟩

def keccakThetaRhoPrefix (m : UInt64 → UInt8) (outPtr inPtr : UInt64) : Nat → (UInt64 → UInt8)
  | 0 => m
  | n+1 => writeMem128 (keccakThetaRhoPrefix m outPtr inPtr n)
      (outPtr + UInt64.ofNat (16 * keccakThetaRhoPerm n)) (keccakThetaRhoVec m inPtr n)

theorem keccakThetaRhoPerm_bound (i : Nat) (hi : i < 25) :
    16 * keccakThetaRhoPerm i ≤ 384 := by
  unfold keccakThetaRhoPerm
  have hm := Nat.mod_lt (2 * (i % 5) + 3 * (i / 5)) (by decide : 0 < 5)
  omega

theorem keccakThetaRhoPrefix_read (m : UInt64 → UInt8) (outPtr inPtr : UInt64)
    (hd : keccakThetaRhoDisjoint outPtr inPtr) (n : Nat) (hn : n ≤ 25)
    (i : Nat) (hi : i ≤ 384) :
    readMem128 (keccakThetaRhoPrefix m outPtr inPtr n) (inPtr + UInt64.ofNat i) =
      readMem128 m (inPtr + UInt64.ofNat i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [keccakThetaRhoPrefix, keccakThetaRho_readWrite outPtr inPtr hd _ _ i
      (16 * keccakThetaRhoPerm n) hi (keccakThetaRhoPerm_bound n (by omega))]
    exact ih (by omega)

theorem keccakThetaRhoPrefix_full (m : UInt64 → UInt8) (outPtr inPtr : UInt64) :
    keccakThetaRhoPrefix m outPtr inPtr 25 = keccakThetaRhoOut m outPtr inPtr := by rfl

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 800000 in
theorem keccakThetaRho_math (m : UInt64 → UInt8) (p : UInt64) (n : Nat) (hn : n < 25) :
    keccakThetaRhoXar (readMem128 m (p + UInt64.ofNat (16 * n)))
      (keccakThetaRhoD m p (n % 5)) (keccakThetaRhoRor n) = keccakThetaRhoVec m p n := by
  match n, hn with
  | 0, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 1, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 2, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 3, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 4, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 5, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 6, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 7, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 8, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 9, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 10, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 11, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 12, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 13, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 14, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 15, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 16, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 17, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 18, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 19, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 20, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 21, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 22, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 23, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | 24, _ =>
    simp [keccakThetaRhoXar, keccakThetaRhoD, keccakThetaRhoRor, keccakThetaRhoVec,
      keccakThetaRhoPerm, keccakThetaRhoGet, keccakThetaRhoLoad, thetaS, rhoPiS, rotlK,
      keccakThetaRho_or_comm]
  | n+25, hn => omega

def keccakThetaRhoInv (s t : Arm64State) (n : Nat) : Prop :=
  t.pc = 160 + 12*n ∧ t.gpr = s.gpr ∧ t.halted = false ∧
  (∀ x : Nat, x < 5 → t.vec.get (16+x) = keccakThetaRhoD s.mem (s.gpr.get 1) x) ∧
  t.mem = keccakThetaRhoPrefix s.mem (s.gpr.get 0) (s.gpr.get 1) n

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
theorem keccakThetaRho_parity (s : Arm64State) (hp : s.pc = 0) (hh : s.halted = false) :
    ∃ t, StepsArm64 keccakThetaRhoProg 40 s t ∧ keccakThetaRhoInv s t 0 := by
  rcases s with ⟨pc, ⟨⟨r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15⟩, hi⟩,
    ⟨⟨v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15⟩,
      ⟨v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31⟩⟩,
    cf,zf,dit,hlt,mem⟩
  dsimp only at hp hh
  subst pc hlt
  iterate 40
    apply StepsArm64_step_ex rfl rfl
    · conv =>
        lhs
        simp [stepArm64, getArmGpr, Bank32.get, Bank32.set, Bank16.get, Bank16.set]
      all_goals rfl
  refine ⟨_, StepsArm64.zero _, rfl, rfl, rfl, ?_, rfl⟩
  intro x hx
  match x, hx with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ =>
    simp [keccakThetaRhoD, rotlK, Bank32.get, Bank16.get]
  | x+5, hx => omega

theorem keccakThetaRho_fetch (n : Nat) (hn : n < 25) :
    findInstrAtPc (160+12*n) keccakThetaRhoProg =
      some ⟨160+12*n, 4, .ldrQ 0 1 (UInt64.ofNat (16*n))⟩ ∧
    findInstrAtPc (160+12*n+4) keccakThetaRhoProg =
      some ⟨160+12*n+4, 4, .vxar_2d 0 0 (16+n%5) (keccakThetaRhoRor n)⟩ ∧
    findInstrAtPc (160+12*n+8) keccakThetaRhoProg =
      some ⟨160+12*n+8, 4, .strQ 0 0 (UInt64.ofNat (16*keccakThetaRhoPerm n))⟩ := by
  have hall : ∀ n : Fin 25,
    findInstrAtPc (160+12*n.val) keccakThetaRhoProg =
      some ⟨160+12*n.val, 4, .ldrQ 0 1 (UInt64.ofNat (16*n.val))⟩ ∧
    findInstrAtPc (160+12*n.val+4) keccakThetaRhoProg =
      some ⟨160+12*n.val+4, 4, .vxar_2d 0 0 (16+n.val%5) (keccakThetaRhoRor n.val)⟩ ∧
    findInstrAtPc (160+12*n.val+8) keccakThetaRhoProg =
      some ⟨160+12*n.val+8, 4, .strQ 0 0 (UInt64.ofNat (16*keccakThetaRhoPerm n.val))⟩ := by decide +kernel
  exact hall ⟨n, hn⟩

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 800000 in
theorem keccakThetaRho_block (s t : Arm64State) (n : Nat) (hn : n < 25)
    (hd : keccakThetaRhoDisjoint (s.gpr.get 0) (s.gpr.get 1))
    (h : keccakThetaRhoInv s t n) :
    ∃ u, StepsArm64 keccakThetaRhoProg 3 t u ∧ keccakThetaRhoInv s u (n+1) := by
  rcases t with ⟨pc,gpr,vec,cf,zf,dit,hlt,mem⟩
  rcases h with ⟨hp,hg,hh,hv,hm⟩
  dsimp only at hp hg hh hv hm
  subst pc gpr hlt mem
  have hmod : n % 5 < 5 := Nat.mod_lt n (by decide)
  have hvn := hv (n%5) hmod
  have hmath := keccakThetaRho_math s.mem (s.gpr.get 1) n hn
  dsimp only [keccakThetaRhoXar] at hmath
  have hf := keccakThetaRho_fetch n hn
  have hget1 : ∀ st : Arm64State, getArmGpr st 1 = st.gpr.get 1 := fun _ => rfl
  have hget0 : ∀ st : Arm64State, getArmGpr st 0 = st.gpr.get 0 := fun _ => rfl
  apply StepsArm64_step_ex rfl hf.1
  · conv =>
      lhs
      simp only [stepArm64, hget1]
      rw [keccakThetaRhoPrefix_read s.mem (s.gpr.get 0) (s.gpr.get 1) hd n (by omega)
        (16*n) (by omega)]
    all_goals rfl
  apply StepsArm64_step_ex rfl hf.2.1
  · conv =>
      lhs
      simp (disch := omega) only [stepArm64, Bank32.get_set_eq, Bank32.get_set_ne, hvn]
      rw [hmath]
    all_goals rfl
  apply StepsArm64_step_ex rfl (by simpa only [Nat.add_assoc] using hf.2.2)
  · conv =>
      lhs
      simp only [stepArm64, hget0, Bank32.get_set_eq]
    all_goals rfl
  refine ⟨_, StepsArm64.zero _, ?_, rfl, rfl, ?_, rfl⟩
  · dsimp only
    omega
  · intro x hx
    dsimp only
    simp (disch := omega) only [Bank32.get_set_ne]
    exact hv x hx

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 400000 in
theorem keccakThetaRho_wipe (s : Arm64State) (hp : s.pc = 460) (hh : s.halted = false) :
    ∃ t, StepsArm64 keccakThetaRhoProg 13 s t ∧ t.halted = true ∧ t.mem = s.mem := by
  rcases s with ⟨pc,gpr,⟨⟨v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15⟩,
    ⟨v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31⟩⟩,cf,zf,dit,hlt,mem⟩
  dsimp only at hp hh
  subst pc hlt
  iterate 13
    apply StepsArm64_step_ex rfl rfl
    · conv =>
        lhs
        simp [stepArm64, Bank32.get, Bank32.set, Bank16.get, Bank16.set]
      all_goals rfl
  exact ⟨_, StepsArm64.zero _, rfl, rfl⟩

theorem keccakThetaRho_steps_trans {m n : Nat} {s t u : Arm64State}
    (h : StepsArm64 keccakThetaRhoProg m s t)
    (h' : StepsArm64 keccakThetaRhoProg n t u) :
    StepsArm64 keccakThetaRhoProg (m+n) s u := by
  induction h with
  | zero => simpa only [Nat.zero_add] using h'
  | cons hh hf hs h ih =>
    simpa only [Nat.add_right_comm] using StepsArm64.cons hh hf hs (ih h')

theorem keccakThetaRho_blocks (s t : Arm64State)
    (hd : keccakThetaRhoDisjoint (s.gpr.get 0) (s.gpr.get 1))
    (n : Nat) (hn : n ≤ 25) (h : keccakThetaRhoInv s t 0) :
    ∃ u, StepsArm64 keccakThetaRhoProg (3*n) t u ∧ keccakThetaRhoInv s u n := by
  induction n with
  | zero => exact ⟨t, StepsArm64.zero _, h⟩
  | succ n ih =>
    obtain ⟨u, hu, hi⟩ := ih (by omega)
    obtain ⟨v, hv, hi'⟩ := keccakThetaRho_block s u n (by omega) hd hi
    refine ⟨v, ?_, hi'⟩
    simpa only [Nat.mul_add, Nat.mul_one] using keccakThetaRho_steps_trans hu hv

theorem keccakThetaRho_steps (s : Arm64State)
    (hp : s.pc = 0) (hh : s.halted = false)
    (hd : keccakThetaRhoDisjoint (s.gpr.get 0) (s.gpr.get 1)) :
    ∃ t, StepsArm64 keccakThetaRhoProg 128 s t ∧ t.halted = true ∧
      t.mem = keccakThetaRhoOut s.mem (s.gpr.get 0) (s.gpr.get 1) := by
  obtain ⟨s40, h40, hi⟩ := keccakThetaRho_parity s hp hh
  obtain ⟨s115, h75, hi'⟩ := keccakThetaRho_blocks s s40 hd 25 (by decide) hi
  obtain ⟨s128, h13, hh', hm⟩ := keccakThetaRho_wipe s115 hi'.1 hi'.2.2.1
  refine ⟨s128, keccakThetaRho_steps_trans (keccakThetaRho_steps_trans h40 h75) h13, hh', ?_⟩
  rw [hm, hi'.2.2.2.2, keccakThetaRhoPrefix_full]

/-- Complete ABI preconditions: entry PC, live machine, disjoint 400-byte buffers. -/
def keccakThetaRhoInitial (s : Arm64State) : Prop :=
  s.pc = 0 ∧ s.halted = false ∧ keccakThetaRhoDisjoint (s.gpr.get 0) (s.gpr.get 1)

/-- Fresh decoded machine code computes theta, rho and pi on both full Keccak states.
`keccakThetaRhoOut` writes all 25 lanes of each state and preserves every other byte. -/
theorem keccakThetaRho_current_functional (s : Arm64State) (h : keccakThetaRhoInitial s) :
    ∃ slice prog,
      findSliceByNameBytes currentAarch64ExtractedSlices keccakThetaRhoName = some slice ∧
      decodeArm64Slice slice.code = some prog ∧
      ∀ extra : Nat,
        (runArm64 prog (128 + extra) s).1.halted = true ∧
        (runArm64 prog (128 + extra) s).1.mem =
          keccakThetaRhoOut s.mem (s.gpr.get 0) (s.gpr.get 1) := by
  have hd := keccakThetaRho_decode
  cases hf : findSliceByNameBytes currentAarch64ExtractedSlices keccakThetaRhoName with
  | none => rw [hf] at hd; contradiction
  | some slice =>
    rw [hf] at hd
    refine ⟨slice, keccakThetaRhoProg, rfl, hd, ?_⟩
    obtain ⟨t, ht, hh, hm⟩ := keccakThetaRho_steps s h.1 h.2.1 h.2.2
    intro extra
    have he := (ht.toExecReaches extra).1
    rw [runArm64_halted_fst keccakThetaRhoProg extra t hh] at he
    rw [he]
    exact ⟨hh, hm⟩

theorem keccakThetaRho_inhabited : ∃ s : Arm64State, keccakThetaRhoInitial s := by
  refine ⟨⟨0, Bank32.ofFn (fun i => if i == 1 then 1024 else 0),
    Bank32.const Vec128.zero, false, false, false, false, fun _ => 0⟩, rfl, rfl, ?_⟩
  change keccakThetaRhoDisjoint 0 1024
  intro i j hi hj he
  have hn := congrArg UInt64.toNat he
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat, UInt64.toNat_ofNat'] at hn
  omega

/-- A wrong implementation omitting theta cannot satisfy the full-state specification. -/
theorem keccakThetaRho_tooth :
    rhoPiS (thetaS { zeroKState with a1 := 1 }) ≠
      rhoPiS { zeroKState with a1 := 1 } := by decide +kernel

#tooth_pair keccakThetaRho_current_functional vs keccakThetaRho_tooth
#verify_inhabited keccakThetaRho_current_functional keccakThetaRho_inhabited

end KeccakThetaRhoFreshVerification

section Keccak4xFreshVerification
set_option linter.unusedSimpArgs false
def keccak4xName : List UInt8 := [113, 115, 97, 103, 95, 97, 115, 109, 95, 107, 101, 99, 99, 97, 107, 95, 102, 49, 54, 48, 48, 95, 97, 118, 120, 50, 95, 52, 120]

def keccak4xProg : List (DecodedInstr X86Instr) := [
  ⟨0, 1, .pushReg 5⟩,
  ⟨1, 3, .movRegReg true 5 4⟩,
  ⟨4, 4, .aluImm .andOp true 4 18446744073709551584⟩,
  ⟨8, 7, .aluImm .sub true 4 832⟩,
  ⟨15, 5, .movImm false 1 24⟩,
  ⟨20, 4, .vload true 0 (.baseDisp 7 0)⟩,
  ⟨24, 8, .vpxorLoad256 0 0 (.baseDisp 7 160)⟩,
  ⟨32, 8, .vpxorLoad256 0 0 (.baseDisp 7 320)⟩,
  ⟨40, 8, .vpxorLoad256 0 0 (.baseDisp 7 480)⟩,
  ⟨48, 8, .vpxorLoad256 0 0 (.baseDisp 7 640)⟩,
  ⟨56, 5, .vload true 1 (.baseDisp 7 32)⟩,
  ⟨61, 8, .vpxorLoad256 1 1 (.baseDisp 7 192)⟩,
  ⟨69, 8, .vpxorLoad256 1 1 (.baseDisp 7 352)⟩,
  ⟨77, 8, .vpxorLoad256 1 1 (.baseDisp 7 512)⟩,
  ⟨85, 8, .vpxorLoad256 1 1 (.baseDisp 7 672)⟩,
  ⟨93, 5, .vload true 2 (.baseDisp 7 64)⟩,
  ⟨98, 8, .vpxorLoad256 2 2 (.baseDisp 7 224)⟩,
  ⟨106, 8, .vpxorLoad256 2 2 (.baseDisp 7 384)⟩,
  ⟨114, 8, .vpxorLoad256 2 2 (.baseDisp 7 544)⟩,
  ⟨122, 8, .vpxorLoad256 2 2 (.baseDisp 7 704)⟩,
  ⟨130, 5, .vload true 3 (.baseDisp 7 96)⟩,
  ⟨135, 8, .vpxorLoad256 3 3 (.baseDisp 7 256)⟩,
  ⟨143, 8, .vpxorLoad256 3 3 (.baseDisp 7 416)⟩,
  ⟨151, 8, .vpxorLoad256 3 3 (.baseDisp 7 576)⟩,
  ⟨159, 8, .vpxorLoad256 3 3 (.baseDisp 7 736)⟩,
  ⟨167, 8, .vload true 4 (.baseDisp 7 128)⟩,
  ⟨175, 8, .vpxorLoad256 4 4 (.baseDisp 7 288)⟩,
  ⟨183, 8, .vpxorLoad256 4 4 (.baseDisp 7 448)⟩,
  ⟨191, 8, .vpxorLoad256 4 4 (.baseDisp 7 608)⟩,
  ⟨199, 8, .vpxorLoad256 4 4 (.baseDisp 7 768)⟩,
  ⟨207, 5, .vshiftImm .vpsllq true 10 1 1⟩,
  ⟨212, 5, .vshiftImm .vpsrlq true 11 1 63⟩,
  ⟨217, 5, .vbinOp .vpor true 10 10 11⟩,
  ⟨222, 4, .vbinOp .vpxor true 5 10 4⟩,
  ⟨226, 5, .vshiftImm .vpsllq true 10 2 1⟩,
  ⟨231, 5, .vshiftImm .vpsrlq true 11 2 63⟩,
  ⟨236, 5, .vbinOp .vpor true 10 10 11⟩,
  ⟨241, 4, .vbinOp .vpxor true 6 10 0⟩,
  ⟨245, 5, .vshiftImm .vpsllq true 10 3 1⟩,
  ⟨250, 5, .vshiftImm .vpsrlq true 11 3 63⟩,
  ⟨255, 5, .vbinOp .vpor true 10 10 11⟩,
  ⟨260, 4, .vbinOp .vpxor true 7 10 1⟩,
  ⟨264, 5, .vshiftImm .vpsllq true 10 4 1⟩,
  ⟨269, 5, .vshiftImm .vpsrlq true 11 4 63⟩,
  ⟨274, 5, .vbinOp .vpor true 10 10 11⟩,
  ⟨279, 4, .vbinOp .vpxor true 8 10 2⟩,
  ⟨283, 5, .vshiftImm .vpsllq true 10 0 1⟩,
  ⟨288, 5, .vshiftImm .vpsrlq true 11 0 63⟩,
  ⟨293, 5, .vbinOp .vpor true 10 10 11⟩,
  ⟨298, 4, .vbinOp .vpxor true 9 10 3⟩,
  ⟨302, 4, .vpxorLoad256 0 5 (.baseDisp 7 0)⟩,
  ⟨306, 5, .vstore true 0 (.baseDisp 4 0)⟩,
  ⟨311, 5, .vpxorLoad256 0 6 (.baseDisp 7 32)⟩,
  ⟨316, 5, .vshiftImm .vpsllq true 1 0 1⟩,
  ⟨321, 5, .vshiftImm .vpsrlq true 2 0 63⟩,
  ⟨326, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨330, 9, .vstore true 0 (.baseDisp 4 320)⟩,
  ⟨339, 5, .vpxorLoad256 0 7 (.baseDisp 7 64)⟩,
  ⟨344, 5, .vshiftImm .vpsllq true 1 0 62⟩,
  ⟨349, 5, .vshiftImm .vpsrlq true 2 0 2⟩,
  ⟨354, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨358, 9, .vstore true 0 (.baseDisp 4 640)⟩,
  ⟨367, 5, .vpxorLoad256 0 8 (.baseDisp 7 96)⟩,
  ⟨372, 5, .vshiftImm .vpsllq true 1 0 28⟩,
  ⟨377, 5, .vshiftImm .vpsrlq true 2 0 36⟩,
  ⟨382, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨386, 9, .vstore true 0 (.baseDisp 4 160)⟩,
  ⟨395, 8, .vpxorLoad256 0 9 (.baseDisp 7 128)⟩,
  ⟨403, 5, .vshiftImm .vpsllq true 1 0 27⟩,
  ⟨408, 5, .vshiftImm .vpsrlq true 2 0 37⟩,
  ⟨413, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨417, 9, .vstore true 0 (.baseDisp 4 480)⟩,
  ⟨426, 8, .vpxorLoad256 0 5 (.baseDisp 7 160)⟩,
  ⟨434, 5, .vshiftImm .vpsllq true 1 0 36⟩,
  ⟨439, 5, .vshiftImm .vpsrlq true 2 0 28⟩,
  ⟨444, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨448, 9, .vstore true 0 (.baseDisp 4 512)⟩,
  ⟨457, 8, .vpxorLoad256 0 6 (.baseDisp 7 192)⟩,
  ⟨465, 5, .vshiftImm .vpsllq true 1 0 44⟩,
  ⟨470, 5, .vshiftImm .vpsrlq true 2 0 20⟩,
  ⟨475, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨479, 6, .vstore true 0 (.baseDisp 4 32)⟩,
  ⟨485, 8, .vpxorLoad256 0 7 (.baseDisp 7 224)⟩,
  ⟨493, 5, .vshiftImm .vpsllq true 1 0 6⟩,
  ⟨498, 5, .vshiftImm .vpsrlq true 2 0 58⟩,
  ⟨503, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨507, 9, .vstore true 0 (.baseDisp 4 352)⟩,
  ⟨516, 8, .vpxorLoad256 0 8 (.baseDisp 7 256)⟩,
  ⟨524, 5, .vshiftImm .vpsllq true 1 0 55⟩,
  ⟨529, 5, .vshiftImm .vpsrlq true 2 0 9⟩,
  ⟨534, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨538, 9, .vstore true 0 (.baseDisp 4 672)⟩,
  ⟨547, 8, .vpxorLoad256 0 9 (.baseDisp 7 288)⟩,
  ⟨555, 5, .vshiftImm .vpsllq true 1 0 20⟩,
  ⟨560, 5, .vshiftImm .vpsrlq true 2 0 44⟩,
  ⟨565, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨569, 9, .vstore true 0 (.baseDisp 4 192)⟩,
  ⟨578, 8, .vpxorLoad256 0 5 (.baseDisp 7 320)⟩,
  ⟨586, 5, .vshiftImm .vpsllq true 1 0 3⟩,
  ⟨591, 5, .vshiftImm .vpsrlq true 2 0 61⟩,
  ⟨596, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨600, 9, .vstore true 0 (.baseDisp 4 224)⟩,
  ⟨609, 8, .vpxorLoad256 0 6 (.baseDisp 7 352)⟩,
  ⟨617, 5, .vshiftImm .vpsllq true 1 0 10⟩,
  ⟨622, 5, .vshiftImm .vpsrlq true 2 0 54⟩,
  ⟨627, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨631, 9, .vstore true 0 (.baseDisp 4 544)⟩,
  ⟨640, 8, .vpxorLoad256 0 7 (.baseDisp 7 384)⟩,
  ⟨648, 5, .vshiftImm .vpsllq true 1 0 43⟩,
  ⟨653, 5, .vshiftImm .vpsrlq true 2 0 21⟩,
  ⟨658, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨662, 6, .vstore true 0 (.baseDisp 4 64)⟩,
  ⟨668, 8, .vpxorLoad256 0 8 (.baseDisp 7 416)⟩,
  ⟨676, 5, .vshiftImm .vpsllq true 1 0 25⟩,
  ⟨681, 5, .vshiftImm .vpsrlq true 2 0 39⟩,
  ⟨686, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨690, 9, .vstore true 0 (.baseDisp 4 384)⟩,
  ⟨699, 8, .vpxorLoad256 0 9 (.baseDisp 7 448)⟩,
  ⟨707, 5, .vshiftImm .vpsllq true 1 0 39⟩,
  ⟨712, 5, .vshiftImm .vpsrlq true 2 0 25⟩,
  ⟨717, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨721, 9, .vstore true 0 (.baseDisp 4 704)⟩,
  ⟨730, 8, .vpxorLoad256 0 5 (.baseDisp 7 480)⟩,
  ⟨738, 5, .vshiftImm .vpsllq true 1 0 41⟩,
  ⟨743, 5, .vshiftImm .vpsrlq true 2 0 23⟩,
  ⟨748, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨752, 9, .vstore true 0 (.baseDisp 4 736)⟩,
  ⟨761, 8, .vpxorLoad256 0 6 (.baseDisp 7 512)⟩,
  ⟨769, 5, .vshiftImm .vpsllq true 1 0 45⟩,
  ⟨774, 5, .vshiftImm .vpsrlq true 2 0 19⟩,
  ⟨779, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨783, 9, .vstore true 0 (.baseDisp 4 256)⟩,
  ⟨792, 8, .vpxorLoad256 0 7 (.baseDisp 7 544)⟩,
  ⟨800, 5, .vshiftImm .vpsllq true 1 0 15⟩,
  ⟨805, 5, .vshiftImm .vpsrlq true 2 0 49⟩,
  ⟨810, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨814, 9, .vstore true 0 (.baseDisp 4 576)⟩,
  ⟨823, 8, .vpxorLoad256 0 8 (.baseDisp 7 576)⟩,
  ⟨831, 5, .vshiftImm .vpsllq true 1 0 21⟩,
  ⟨836, 5, .vshiftImm .vpsrlq true 2 0 43⟩,
  ⟨841, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨845, 6, .vstore true 0 (.baseDisp 4 96)⟩,
  ⟨851, 8, .vpxorLoad256 0 9 (.baseDisp 7 608)⟩,
  ⟨859, 5, .vshiftImm .vpsllq true 1 0 8⟩,
  ⟨864, 5, .vshiftImm .vpsrlq true 2 0 56⟩,
  ⟨869, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨873, 9, .vstore true 0 (.baseDisp 4 416)⟩,
  ⟨882, 8, .vpxorLoad256 0 5 (.baseDisp 7 640)⟩,
  ⟨890, 5, .vshiftImm .vpsllq true 1 0 18⟩,
  ⟨895, 5, .vshiftImm .vpsrlq true 2 0 46⟩,
  ⟨900, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨904, 9, .vstore true 0 (.baseDisp 4 448)⟩,
  ⟨913, 8, .vpxorLoad256 0 6 (.baseDisp 7 672)⟩,
  ⟨921, 5, .vshiftImm .vpsllq true 1 0 2⟩,
  ⟨926, 5, .vshiftImm .vpsrlq true 2 0 62⟩,
  ⟨931, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨935, 9, .vstore true 0 (.baseDisp 4 768)⟩,
  ⟨944, 8, .vpxorLoad256 0 7 (.baseDisp 7 704)⟩,
  ⟨952, 5, .vshiftImm .vpsllq true 1 0 61⟩,
  ⟨957, 5, .vshiftImm .vpsrlq true 2 0 3⟩,
  ⟨962, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨966, 9, .vstore true 0 (.baseDisp 4 288)⟩,
  ⟨975, 8, .vpxorLoad256 0 8 (.baseDisp 7 736)⟩,
  ⟨983, 5, .vshiftImm .vpsllq true 1 0 56⟩,
  ⟨988, 5, .vshiftImm .vpsrlq true 2 0 8⟩,
  ⟨993, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨997, 9, .vstore true 0 (.baseDisp 4 608)⟩,
  ⟨1006, 8, .vpxorLoad256 0 9 (.baseDisp 7 768)⟩,
  ⟨1014, 5, .vshiftImm .vpsllq true 1 0 14⟩,
  ⟨1019, 5, .vshiftImm .vpsrlq true 2 0 50⟩,
  ⟨1024, 4, .vbinOp .vpor true 0 1 2⟩,
  ⟨1028, 9, .vstore true 0 (.baseDisp 4 128)⟩,
  ⟨1037, 5, .vload true 0 (.baseDisp 4 0)⟩,
  ⟨1042, 6, .vload true 1 (.baseDisp 4 32)⟩,
  ⟨1048, 6, .vload true 2 (.baseDisp 4 64)⟩,
  ⟨1054, 6, .vload true 3 (.baseDisp 4 96)⟩,
  ⟨1060, 9, .vload true 4 (.baseDisp 4 128)⟩,
  ⟨1069, 4, .vbinOp .vpandn true 5 1 2⟩,
  ⟨1073, 4, .vbinOp .vpxor true 5 0 5⟩,
  ⟨1077, 5, .vpbroadcastLoad64 10 (.baseDisp 6 0)⟩,
  ⟨1082, 4, .vbinOp .vpxor true 5 10 5⟩,
  ⟨1086, 4, .vstore true 5 (.baseDisp 7 0)⟩,
  ⟨1090, 4, .vbinOp .vpandn true 6 2 3⟩,
  ⟨1094, 4, .vbinOp .vpxor true 6 1 6⟩,
  ⟨1098, 5, .vstore true 6 (.baseDisp 7 32)⟩,
  ⟨1103, 4, .vbinOp .vpandn true 7 3 4⟩,
  ⟨1107, 4, .vbinOp .vpxor true 7 2 7⟩,
  ⟨1111, 5, .vstore true 7 (.baseDisp 7 64)⟩,
  ⟨1116, 4, .vbinOp .vpandn true 8 4 0⟩,
  ⟨1120, 4, .vbinOp .vpxor true 8 8 3⟩,
  ⟨1124, 5, .vstore true 8 (.baseDisp 7 96)⟩,
  ⟨1129, 4, .vbinOp .vpandn true 9 0 1⟩,
  ⟨1133, 4, .vbinOp .vpxor true 9 9 4⟩,
  ⟨1137, 8, .vstore true 9 (.baseDisp 7 128)⟩,
  ⟨1145, 9, .vload true 0 (.baseDisp 4 160)⟩,
  ⟨1154, 9, .vload true 1 (.baseDisp 4 192)⟩,
  ⟨1163, 9, .vload true 2 (.baseDisp 4 224)⟩,
  ⟨1172, 9, .vload true 3 (.baseDisp 4 256)⟩,
  ⟨1181, 9, .vload true 4 (.baseDisp 4 288)⟩,
  ⟨1190, 4, .vbinOp .vpandn true 5 1 2⟩,
  ⟨1194, 4, .vbinOp .vpxor true 5 0 5⟩,
  ⟨1198, 8, .vstore true 5 (.baseDisp 7 160)⟩,
  ⟨1206, 4, .vbinOp .vpandn true 6 2 3⟩,
  ⟨1210, 4, .vbinOp .vpxor true 6 1 6⟩,
  ⟨1214, 8, .vstore true 6 (.baseDisp 7 192)⟩,
  ⟨1222, 4, .vbinOp .vpandn true 7 3 4⟩,
  ⟨1226, 4, .vbinOp .vpxor true 7 2 7⟩,
  ⟨1230, 8, .vstore true 7 (.baseDisp 7 224)⟩,
  ⟨1238, 4, .vbinOp .vpandn true 8 4 0⟩,
  ⟨1242, 4, .vbinOp .vpxor true 8 8 3⟩,
  ⟨1246, 8, .vstore true 8 (.baseDisp 7 256)⟩,
  ⟨1254, 4, .vbinOp .vpandn true 9 0 1⟩,
  ⟨1258, 4, .vbinOp .vpxor true 9 9 4⟩,
  ⟨1262, 8, .vstore true 9 (.baseDisp 7 288)⟩,
  ⟨1270, 9, .vload true 0 (.baseDisp 4 320)⟩,
  ⟨1279, 9, .vload true 1 (.baseDisp 4 352)⟩,
  ⟨1288, 9, .vload true 2 (.baseDisp 4 384)⟩,
  ⟨1297, 9, .vload true 3 (.baseDisp 4 416)⟩,
  ⟨1306, 9, .vload true 4 (.baseDisp 4 448)⟩,
  ⟨1315, 4, .vbinOp .vpandn true 5 1 2⟩,
  ⟨1319, 4, .vbinOp .vpxor true 5 0 5⟩,
  ⟨1323, 8, .vstore true 5 (.baseDisp 7 320)⟩,
  ⟨1331, 4, .vbinOp .vpandn true 6 2 3⟩,
  ⟨1335, 4, .vbinOp .vpxor true 6 1 6⟩,
  ⟨1339, 8, .vstore true 6 (.baseDisp 7 352)⟩,
  ⟨1347, 4, .vbinOp .vpandn true 7 3 4⟩,
  ⟨1351, 4, .vbinOp .vpxor true 7 2 7⟩,
  ⟨1355, 8, .vstore true 7 (.baseDisp 7 384)⟩,
  ⟨1363, 4, .vbinOp .vpandn true 8 4 0⟩,
  ⟨1367, 4, .vbinOp .vpxor true 8 8 3⟩,
  ⟨1371, 8, .vstore true 8 (.baseDisp 7 416)⟩,
  ⟨1379, 4, .vbinOp .vpandn true 9 0 1⟩,
  ⟨1383, 4, .vbinOp .vpxor true 9 9 4⟩,
  ⟨1387, 8, .vstore true 9 (.baseDisp 7 448)⟩,
  ⟨1395, 9, .vload true 0 (.baseDisp 4 480)⟩,
  ⟨1404, 9, .vload true 1 (.baseDisp 4 512)⟩,
  ⟨1413, 9, .vload true 2 (.baseDisp 4 544)⟩,
  ⟨1422, 9, .vload true 3 (.baseDisp 4 576)⟩,
  ⟨1431, 9, .vload true 4 (.baseDisp 4 608)⟩,
  ⟨1440, 4, .vbinOp .vpandn true 5 1 2⟩,
  ⟨1444, 4, .vbinOp .vpxor true 5 0 5⟩,
  ⟨1448, 8, .vstore true 5 (.baseDisp 7 480)⟩,
  ⟨1456, 4, .vbinOp .vpandn true 6 2 3⟩,
  ⟨1460, 4, .vbinOp .vpxor true 6 1 6⟩,
  ⟨1464, 8, .vstore true 6 (.baseDisp 7 512)⟩,
  ⟨1472, 4, .vbinOp .vpandn true 7 3 4⟩,
  ⟨1476, 4, .vbinOp .vpxor true 7 2 7⟩,
  ⟨1480, 8, .vstore true 7 (.baseDisp 7 544)⟩,
  ⟨1488, 4, .vbinOp .vpandn true 8 4 0⟩,
  ⟨1492, 4, .vbinOp .vpxor true 8 8 3⟩,
  ⟨1496, 8, .vstore true 8 (.baseDisp 7 576)⟩,
  ⟨1504, 4, .vbinOp .vpandn true 9 0 1⟩,
  ⟨1508, 4, .vbinOp .vpxor true 9 9 4⟩,
  ⟨1512, 8, .vstore true 9 (.baseDisp 7 608)⟩,
  ⟨1520, 9, .vload true 0 (.baseDisp 4 640)⟩,
  ⟨1529, 9, .vload true 1 (.baseDisp 4 672)⟩,
  ⟨1538, 9, .vload true 2 (.baseDisp 4 704)⟩,
  ⟨1547, 9, .vload true 3 (.baseDisp 4 736)⟩,
  ⟨1556, 9, .vload true 4 (.baseDisp 4 768)⟩,
  ⟨1565, 4, .vbinOp .vpandn true 5 1 2⟩,
  ⟨1569, 4, .vbinOp .vpxor true 5 0 5⟩,
  ⟨1573, 8, .vstore true 5 (.baseDisp 7 640)⟩,
  ⟨1581, 4, .vbinOp .vpandn true 6 2 3⟩,
  ⟨1585, 4, .vbinOp .vpxor true 6 1 6⟩,
  ⟨1589, 8, .vstore true 6 (.baseDisp 7 672)⟩,
  ⟨1597, 4, .vbinOp .vpandn true 7 3 4⟩,
  ⟨1601, 4, .vbinOp .vpxor true 7 2 7⟩,
  ⟨1605, 8, .vstore true 7 (.baseDisp 7 704)⟩,
  ⟨1613, 4, .vbinOp .vpandn true 8 4 0⟩,
  ⟨1617, 4, .vbinOp .vpxor true 8 8 3⟩,
  ⟨1621, 8, .vstore true 8 (.baseDisp 7 736)⟩,
  ⟨1629, 4, .vbinOp .vpandn true 9 0 1⟩,
  ⟨1633, 4, .vbinOp .vpxor true 9 9 4⟩,
  ⟨1637, 8, .vstore true 9 (.baseDisp 7 768)⟩,
  ⟨1645, 4, .aluImm .add true 6 8⟩,
  ⟨1649, 2, .incDec false false 1⟩,
  ⟨1651, 6, .jcc 5 20⟩,
  ⟨1657, 4, .vbinOp .vpxor true 0 0 0⟩,
  ⟨1661, 5, .movImm false 1 25⟩,
  ⟨1666, 3, .movRegReg true 0 4⟩,
  ⟨1669, 4, .vstore true 0 (.baseDisp 0 0)⟩,
  ⟨1673, 4, .aluImm .add true 0 32⟩,
  ⟨1677, 2, .incDec false false 1⟩,
  ⟨1679, 2, .jcc 5 1669⟩,
  ⟨1681, 4, .vbinOp .vpxor true 1 1 1⟩,
  ⟨1685, 4, .vbinOp .vpxor true 2 2 2⟩,
  ⟨1689, 4, .vbinOp .vpxor true 3 3 3⟩,
  ⟨1693, 4, .vbinOp .vpxor true 4 4 4⟩,
  ⟨1697, 4, .vbinOp .vpxor true 5 5 5⟩,
  ⟨1701, 4, .vbinOp .vpxor true 6 6 6⟩,
  ⟨1705, 4, .vbinOp .vpxor true 7 7 7⟩,
  ⟨1709, 5, .vbinOp .vpxor true 8 8 8⟩,
  ⟨1714, 5, .vbinOp .vpxor true 9 9 9⟩,
  ⟨1719, 5, .vbinOp .vpxor true 10 10 10⟩,
  ⟨1724, 5, .vbinOp .vpxor true 11 11 11⟩,
  ⟨1729, 3, .vzeroall⟩,
  ⟨1732, 3, .vzeroupper⟩,
  ⟨1735, 3, .movRegReg true 4 5⟩,
  ⟨1738, 1, .popReg 5⟩,
  ⟨1739, 2, .aluRegReg .xorOp false 7 7⟩,
  ⟨1741, 2, .aluRegReg .xorOp false 6 6⟩,
  ⟨1743, 2, .aluRegReg .xorOp false 2 2⟩,
  ⟨1745, 2, .aluRegReg .xorOp false 1 1⟩,
  ⟨1747, 3, .aluRegReg .xorOp false 8 8⟩,
  ⟨1750, 3, .aluRegReg .xorOp false 9 9⟩,
  ⟨1753, 3, .aluRegReg .xorOp false 10 10⟩,
  ⟨1756, 3, .aluRegReg .xorOp false 11 11⟩,
  ⟨1759, 2, .aluRegReg .xorOp false 0 0⟩,
  ⟨1761, 1, .ret⟩
]

theorem keccak4x_decoded :
    (findSliceByNameBytes currentX86ExtractedSlices keccak4xName).bind
      (fun sl => decodeX86Stream sl.code) = some keccak4xProg := by decide +kernel

theorem keccak4x_instruction_count : keccak4xProg.length = 309 := by rfl

/-- One of the four words in an interleaved AVX2 Keccak lane. -/
def keccak4xWord (v : Vec256) : Nat → UInt64
  | 0 => v.w0 | 1 => v.w1 | 2 => v.w2 | _ => v.w3

/-- All 25 coordinates of any one of the four independent sponges. -/
def keccak4xLaneState (v : Nat → Vec256) (q : Nat) : KState :=
  ⟨keccak4xWord (v 0) q, keccak4xWord (v 1) q, keccak4xWord (v 2) q, keccak4xWord (v 3) q, keccak4xWord (v 4) q, keccak4xWord (v 5) q, keccak4xWord (v 6) q, keccak4xWord (v 7) q, keccak4xWord (v 8) q, keccak4xWord (v 9) q, keccak4xWord (v 10) q, keccak4xWord (v 11) q, keccak4xWord (v 12) q, keccak4xWord (v 13) q, keccak4xWord (v 14) q, keccak4xWord (v 15) q, keccak4xWord (v 16) q, keccak4xWord (v 17) q, keccak4xWord (v 18) q, keccak4xWord (v 19) q, keccak4xWord (v 20) q, keccak4xWord (v 21) q, keccak4xWord (v 22) q, keccak4xWord (v 23) q, keccak4xWord (v 24) q⟩

def keccak4xXor (a b : Vec256) : Vec256 :=
  ⟨a.w0 ^^^ b.w0, a.w1 ^^^ b.w1, a.w2 ^^^ b.w2, a.w3 ^^^ b.w3⟩

def keccak4xRotl (a : Vec256) (k j : UInt64) : Vec256 :=
  ⟨rotlK a.w0 k j, rotlK a.w1 k j, rotlK a.w2 k j, rotlK a.w3 k j⟩

def keccak4xColumn (v : Nat → Vec256) (x : Nat) : Vec256 :=
  keccak4xXor (keccak4xXor (keccak4xXor (keccak4xXor (v x) (v (x+5)))
    (v (x+10))) (v (x+15))) (v (x+20))

def keccak4xD (v : Nat → Vec256) (x : Nat) : Vec256 :=
  keccak4xXor (keccak4xColumn v ((x+4)%5)) (keccak4xRotl (keccak4xColumn v ((x+1)%5)) 1 63)

def keccak4xTheta (v : Nat → Vec256) (i : Nat) : Vec256 :=
  keccak4xXor (v i) (keccak4xD v (i%5))

def keccak4xRhoPi (v : Nat → Vec256) : Nat → Vec256
  | 0 => v 0
  | 1 => keccak4xRotl (v 6) 44 20
  | 2 => keccak4xRotl (v 12) 43 21
  | 3 => keccak4xRotl (v 18) 21 43
  | 4 => keccak4xRotl (v 24) 14 50
  | 5 => keccak4xRotl (v 3) 28 36
  | 6 => keccak4xRotl (v 9) 20 44
  | 7 => keccak4xRotl (v 10) 3 61
  | 8 => keccak4xRotl (v 16) 45 19
  | 9 => keccak4xRotl (v 22) 61 3
  | 10 => keccak4xRotl (v 1) 1 63
  | 11 => keccak4xRotl (v 7) 6 58
  | 12 => keccak4xRotl (v 13) 25 39
  | 13 => keccak4xRotl (v 19) 8 56
  | 14 => keccak4xRotl (v 20) 18 46
  | 15 => keccak4xRotl (v 4) 27 37
  | 16 => keccak4xRotl (v 5) 36 28
  | 17 => keccak4xRotl (v 11) 10 54
  | 18 => keccak4xRotl (v 17) 15 49
  | 19 => keccak4xRotl (v 23) 56 8
  | 20 => keccak4xRotl (v 2) 62 2
  | 21 => keccak4xRotl (v 8) 55 9
  | 22 => keccak4xRotl (v 14) 39 25
  | 23 => keccak4xRotl (v 15) 41 23
  | 24 => keccak4xRotl (v 21) 2 62
  | _ => Vec256.zero

def keccak4xChiVec (a b c : Vec256) : Vec256 :=
  ⟨a.w0 ^^^ ((~~~b.w0) &&& c.w0), a.w1 ^^^ ((~~~b.w1) &&& c.w1),
   a.w2 ^^^ ((~~~b.w2) &&& c.w2), a.w3 ^^^ ((~~~b.w3) &&& c.w3)⟩

def keccak4xChi (v : Nat → Vec256) (i : Nat) : Vec256 :=
  keccak4xChiVec (v i) (v (5*(i/5) + (i+1)%5)) (v (5*(i/5) + (i+2)%5))

/-- SIMD round specification, acting on every word of every one of the 25 lanes. -/
def keccak4xRoundVec (v : Nat → Vec256) (rc : UInt64) (i : Nat) : Vec256 :=
  let c := keccak4xChi (keccak4xRhoPi (keccak4xTheta v)) i
  if i == 0 then keccak4xXor c ⟨rc,rc,rc,rc⟩ else c

/-- SIMD representation commutes with the canonical Keccak round on all four sponges. -/
theorem keccak4xRoundVec_reconstruct (v : Nat → Vec256) (rc : UInt64)
    (q : Nat) (hq : q < 4) :
    keccak4xLaneState (keccak4xRoundVec v rc) q = roundS (keccak4xLaneState v q) rc := by
  match q, hq with
  | 0, _ | 1, _ | 2, _ | 3, _ => rfl
  | n+4, h => exact False.elim (by omega)

theorem keccak4xRoundVec_tooth :
    keccak4xLaneState (keccak4xRoundVec (fun _ => Vec256.zero) 1) 0 ≠ zeroKState := by
  decide +kernel

theorem keccak4xRoundVec_inhabited :
    ∃ (v : Nat → Vec256) (rc : UInt64) (q : Nat),
      q < 4 ∧ keccak4xLaneState v q = zeroKState ∧ rc = 0 := by
  exact ⟨fun _ => Vec256.zero, 0, 0, by decide, rfl, rfl⟩

#tooth_pair keccak4xRoundVec_reconstruct vs keccak4xRoundVec_tooth
#verify_inhabited keccak4xRoundVec_reconstruct keccak4xRoundVec_inhabited

/-- Initial lane memory, in the machine's four-word interleaved layout. -/
def keccak4xSource (mem : UInt64 → UInt8) (p : UInt64) : Nat → Vec256
  | 0 => readMem256 mem (p + 0)
  | 1 => readMem256 mem (p + 32)
  | 2 => readMem256 mem (p + 64)
  | 3 => readMem256 mem (p + 96)
  | 4 => readMem256 mem (p + 128)
  | 5 => readMem256 mem (p + 160)
  | 6 => readMem256 mem (p + 192)
  | 7 => readMem256 mem (p + 224)
  | 8 => readMem256 mem (p + 256)
  | 9 => readMem256 mem (p + 288)
  | 10 => readMem256 mem (p + 320)
  | 11 => readMem256 mem (p + 352)
  | 12 => readMem256 mem (p + 384)
  | 13 => readMem256 mem (p + 416)
  | 14 => readMem256 mem (p + 448)
  | 15 => readMem256 mem (p + 480)
  | 16 => readMem256 mem (p + 512)
  | 17 => readMem256 mem (p + 544)
  | 18 => readMem256 mem (p + 576)
  | 19 => readMem256 mem (p + 608)
  | 20 => readMem256 mem (p + 640)
  | 21 => readMem256 mem (p + 672)
  | 22 => readMem256 mem (p + 704)
  | 23 => readMem256 mem (p + 736)
  | 24 => readMem256 mem (p + 768)
  | _ => Vec256.zero

private theorem keccak4x_u64xor_comm (a b : UInt64) : a ^^^ b = b ^^^ a := by
  apply UInt64.eq_of_toBitVec_eq
  simp only [UInt64.toBitVec_xor, BitVec.xor_comm]


set_option maxHeartbeats 1000000 in
/-- The first 45 round-body instructions compute all five theta corrections,
for every word of all four interleaved sponges, without changing memory. -/
theorem keccak4x_parity_steps
    (g : Bank16 UInt64) (y : Bank16 Vec256) (cf ofl zf dy : Bool) (mem : UInt64 → UInt8) :
    ∃ t, StepsX86 keccak4xProg 45 ⟨20,g,y,cf,ofl,zf,dy,false,mem⟩ t ∧
      t.pc = 302 ∧ t.halted = false ∧ t.gpr = g ∧ t.mem = mem ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = keccak4xD (keccak4xSource mem (g.get 7)) x) := by
  have h1 : UInt64.ofNat 1 = (1 : UInt64) := by decide +kernel
  have h63 : UInt64.ofNat 63 = (63 : UInt64) := by decide +kernel
  iterate 45
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        simp [stepX86, evalX86Addr, Bank16.get, Bank16.set, clampVecWidth,
          evalVecBin256, evalVecShift256, h1, h63]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, rfl, ?_⟩
  intro x hx
  match x, hx with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ =>
    simp [keccak4xD, keccak4xColumn, keccak4xSource, keccak4xRotl,
      keccak4xXor, rotlK, Bank16.get, keccak4x_u64xor_comm]
  | n+5, h => exact False.elim (by omega)


/-- Source-to-destination lane permutation used by the compiled rho/pi stores. -/
def keccak4xPerm : Nat → Nat
  | 0 => 0
  | 1 => 10
  | 2 => 20
  | 3 => 5
  | 4 => 15
  | 5 => 16
  | 6 => 1
  | 7 => 11
  | 8 => 21
  | 9 => 6
  | 10 => 7
  | 11 => 17
  | 12 => 2
  | 13 => 12
  | 14 => 22
  | 15 => 23
  | 16 => 8
  | 17 => 18
  | 18 => 3
  | 19 => 13
  | 20 => 14
  | 21 => 24
  | 22 => 9
  | 23 => 19
  | 24 => 4
  | _ => 0

def keccak4xPermInv : Nat → Nat
  | 0 => 0
  | 1 => 6
  | 2 => 12
  | 3 => 18
  | 4 => 24
  | 5 => 3
  | 6 => 9
  | 7 => 10
  | 8 => 16
  | 9 => 22
  | 10 => 1
  | 11 => 7
  | 12 => 13
  | 13 => 19
  | 14 => 20
  | 15 => 4
  | 16 => 5
  | 17 => 11
  | 18 => 17
  | 19 => 23
  | 20 => 2
  | 21 => 8
  | 22 => 14
  | 23 => 15
  | 24 => 21
  | _ => 0

theorem keccak4x_perm_lt (i : Nat) (hi : i < 25) : keccak4xPerm i < 25 := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ => decide +kernel
  | n+25, h => exact False.elim (by omega)

theorem keccak4x_permInv_lt (i : Nat) (hi : i < 25) : keccak4xPermInv i < 25 := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ => decide +kernel
  | n+25, h => exact False.elim (by omega)

theorem keccak4x_perm_leftInv (i : Nat) (hi : i < 25) : keccak4xPermInv (keccak4xPerm i) = i := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ => decide +kernel
  | n+25, h => exact False.elim (by omega)

theorem keccak4x_perm_rightInv (i : Nat) (hi : i < 25) : keccak4xPerm (keccak4xPermInv i) = i := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ => decide +kernel
  | n+25, h => exact False.elim (by omega)

def keccak4xRhoRot (a : Vec256) : Nat → Vec256
  | 0 => a
  | 1 => keccak4xRotl a 1 63
  | 2 => keccak4xRotl a 62 2
  | 3 => keccak4xRotl a 28 36
  | 4 => keccak4xRotl a 27 37
  | 5 => keccak4xRotl a 36 28
  | 6 => keccak4xRotl a 44 20
  | 7 => keccak4xRotl a 6 58
  | 8 => keccak4xRotl a 55 9
  | 9 => keccak4xRotl a 20 44
  | 10 => keccak4xRotl a 3 61
  | 11 => keccak4xRotl a 10 54
  | 12 => keccak4xRotl a 43 21
  | 13 => keccak4xRotl a 25 39
  | 14 => keccak4xRotl a 39 25
  | 15 => keccak4xRotl a 41 23
  | 16 => keccak4xRotl a 45 19
  | 17 => keccak4xRotl a 15 49
  | 18 => keccak4xRotl a 21 43
  | 19 => keccak4xRotl a 8 56
  | 20 => keccak4xRotl a 18 46
  | 21 => keccak4xRotl a 2 62
  | 22 => keccak4xRotl a 61 3
  | 23 => keccak4xRotl a 56 8
  | 24 => keccak4xRotl a 14 50
  | _ => Vec256.zero

theorem keccak4x_rho_mapping (v : Nat → Vec256) (i : Nat) (hi : i < 25) :
    keccak4xRhoRot (keccak4xTheta v i) i =
      keccak4xRhoPi (keccak4xTheta v) (keccak4xPerm i) := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ => rfl
  | n+25, h => exact False.elim (by omega)

/-- Modular disjointness: valid even when a region wraps around the address space. -/
def keccak4xDisjoint (a : UInt64) (n : Nat) (b : UInt64) (m : Nat) : Prop :=
  ∀ i j : Nat, i < n → j < m → a + UInt64.ofNat i ≠ b + UInt64.ofNat j

/-- Scratch writes are ordered exactly as rho/pi visits the source lanes. -/
def keccak4xScratchPrefix (m : UInt64 → UInt8) (sp : UInt64) (v : Nat → Vec256) : Nat → (UInt64 → UInt8)
  | 0 => m
  | n+1 => writeMem256 (keccak4xScratchPrefix m sp v n)
      (sp + UInt64.ofNat (32 * keccak4xPerm n)) (keccak4xRhoPi (keccak4xTheta v) (keccak4xPerm n))

private theorem keccak4x_read256_write_other (m : UInt64 → UInt8) (p : UInt64)
    (i j : Nat) (hi : i < 25) (hj : j < 25) (hne : i ≠ j) (v : Vec256) :
    readMem256 (writeMem256 m (p + UInt64.ofNat (32*i)) v) (p + UInt64.ofNat (32*j)) =
      readMem256 m (p + UInt64.ofNat (32*j)) := by
  apply keccakChiMpc_readMem256_writeMem256_disjoint
  intro a b ha hb he
  rw [u64_add_ofNat_assoc p (32*j) a (by omega),
    u64_add_ofNat_assoc p (32*i) b (by omega)] at he
  have := u64_add_ofNat_inj (by omega) (by omega) he
  omega

theorem keccak4xScratchPrefix_read (m : UInt64 → UInt8) (sp : UInt64) (v : Nat → Vec256)
    (n : Nat) (hn : n ≤ 25) (j : Nat) (hj : j < 25) :
    readMem256 (keccak4xScratchPrefix m sp v n) (sp + UInt64.ofNat (32*j)) =
      if keccak4xPermInv j < n then keccak4xRhoPi (keccak4xTheta v) j
      else readMem256 m (sp + UInt64.ofNat (32*j)) := by
  induction n with
  | zero => simp [keccak4xScratchPrefix]
  | succ n ih =>
    have hlt : n < 25 := by omega
    rw [keccak4xScratchPrefix]
    by_cases he : keccak4xPerm n = j
    · rw [he, keccakChiMpc_readMem256_writeMem256_same]
      have hinv : keccak4xPermInv j = n := by
        rw [← he]
        exact keccak4x_perm_leftInv n hlt
      simp [hinv]
    · rw [keccak4x_read256_write_other _ sp (keccak4xPerm n) j
        (keccak4x_perm_lt n hlt) hj he, ih (by omega)]
      have hne : keccak4xPermInv j ≠ n := by
        intro e
        have hperm := congrArg keccak4xPerm e
        rw [keccak4x_perm_rightInv j hj] at hperm
        exact he hperm.symm
      by_cases hl : keccak4xPermInv j < n
      · rw [ite_eq_left hl, ite_eq_left (by omega)]
      · rw [ite_eq_right hl, ite_eq_right (by omega)]

theorem keccak4xScratchPrefix_complete (m : UInt64 → UInt8) (sp : UInt64)
    (v : Nat → Vec256) (j : Nat) (hj : j < 25) :
    readMem256 (keccak4xScratchPrefix m sp v 25) (sp + UInt64.ofNat (32*j)) =
      keccak4xRhoPi (keccak4xTheta v) j := by
  rw [keccak4xScratchPrefix_read _ _ _ 25 (by decide) j hj,
    ite_eq_left (keccak4x_permInv_lt j hj)]

/-- Rho/pi scratch writes preserve every input-state vector. -/
theorem keccak4xScratchPrefix_input (m : UInt64 → UInt8) (sp p : UInt64)
    (v : Nat → Vec256) (hd : keccak4xDisjoint p 800 sp 800)
    (n : Nat) (hn : n ≤ 25) (j : Nat) (hj : j < 25) :
    readMem256 (keccak4xScratchPrefix m sp v n) (p + UInt64.ofNat (32*j)) =
      readMem256 m (p + UInt64.ofNat (32*j)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [keccak4xScratchPrefix]
    have hlt := keccak4x_perm_lt n (by omega)
    rw [keccakChiMpc_readMem256_writeMem256_disjoint]
    · exact ih (by omega)
    · intro a b ha hb he
      rw [u64_add_ofNat_assoc p (32*j) a (by omega),
        u64_add_ofNat_assoc sp (32*keccak4xPerm n) b (by omega)] at he
      exact hd (32*j+a) (32*keccak4xPerm n+b) (by omega) (by omega) he

theorem keccak4xSource_eq (m : UInt64 → UInt8) (p : UInt64) (j : Nat) (hj : j < 25) :
    keccak4xSource m p j = readMem256 m (p + UInt64.ofNat (32*j)) := by
  match j, hj with
  | 0, _ =>
    change readMem256 m (p + 0) = readMem256 m (p + UInt64.ofNat (32*0))
    have h : UInt64.ofNat (32*0) = (0 : UInt64) := by decide +kernel
    rw [h]
  | 1, _ =>
    change readMem256 m (p + 32) = readMem256 m (p + UInt64.ofNat (32*1))
    have h : UInt64.ofNat (32*1) = (32 : UInt64) := by decide +kernel
    rw [h]
  | 2, _ =>
    change readMem256 m (p + 64) = readMem256 m (p + UInt64.ofNat (32*2))
    have h : UInt64.ofNat (32*2) = (64 : UInt64) := by decide +kernel
    rw [h]
  | 3, _ =>
    change readMem256 m (p + 96) = readMem256 m (p + UInt64.ofNat (32*3))
    have h : UInt64.ofNat (32*3) = (96 : UInt64) := by decide +kernel
    rw [h]
  | 4, _ =>
    change readMem256 m (p + 128) = readMem256 m (p + UInt64.ofNat (32*4))
    have h : UInt64.ofNat (32*4) = (128 : UInt64) := by decide +kernel
    rw [h]
  | 5, _ =>
    change readMem256 m (p + 160) = readMem256 m (p + UInt64.ofNat (32*5))
    have h : UInt64.ofNat (32*5) = (160 : UInt64) := by decide +kernel
    rw [h]
  | 6, _ =>
    change readMem256 m (p + 192) = readMem256 m (p + UInt64.ofNat (32*6))
    have h : UInt64.ofNat (32*6) = (192 : UInt64) := by decide +kernel
    rw [h]
  | 7, _ =>
    change readMem256 m (p + 224) = readMem256 m (p + UInt64.ofNat (32*7))
    have h : UInt64.ofNat (32*7) = (224 : UInt64) := by decide +kernel
    rw [h]
  | 8, _ =>
    change readMem256 m (p + 256) = readMem256 m (p + UInt64.ofNat (32*8))
    have h : UInt64.ofNat (32*8) = (256 : UInt64) := by decide +kernel
    rw [h]
  | 9, _ =>
    change readMem256 m (p + 288) = readMem256 m (p + UInt64.ofNat (32*9))
    have h : UInt64.ofNat (32*9) = (288 : UInt64) := by decide +kernel
    rw [h]
  | 10, _ =>
    change readMem256 m (p + 320) = readMem256 m (p + UInt64.ofNat (32*10))
    have h : UInt64.ofNat (32*10) = (320 : UInt64) := by decide +kernel
    rw [h]
  | 11, _ =>
    change readMem256 m (p + 352) = readMem256 m (p + UInt64.ofNat (32*11))
    have h : UInt64.ofNat (32*11) = (352 : UInt64) := by decide +kernel
    rw [h]
  | 12, _ =>
    change readMem256 m (p + 384) = readMem256 m (p + UInt64.ofNat (32*12))
    have h : UInt64.ofNat (32*12) = (384 : UInt64) := by decide +kernel
    rw [h]
  | 13, _ =>
    change readMem256 m (p + 416) = readMem256 m (p + UInt64.ofNat (32*13))
    have h : UInt64.ofNat (32*13) = (416 : UInt64) := by decide +kernel
    rw [h]
  | 14, _ =>
    change readMem256 m (p + 448) = readMem256 m (p + UInt64.ofNat (32*14))
    have h : UInt64.ofNat (32*14) = (448 : UInt64) := by decide +kernel
    rw [h]
  | 15, _ =>
    change readMem256 m (p + 480) = readMem256 m (p + UInt64.ofNat (32*15))
    have h : UInt64.ofNat (32*15) = (480 : UInt64) := by decide +kernel
    rw [h]
  | 16, _ =>
    change readMem256 m (p + 512) = readMem256 m (p + UInt64.ofNat (32*16))
    have h : UInt64.ofNat (32*16) = (512 : UInt64) := by decide +kernel
    rw [h]
  | 17, _ =>
    change readMem256 m (p + 544) = readMem256 m (p + UInt64.ofNat (32*17))
    have h : UInt64.ofNat (32*17) = (544 : UInt64) := by decide +kernel
    rw [h]
  | 18, _ =>
    change readMem256 m (p + 576) = readMem256 m (p + UInt64.ofNat (32*18))
    have h : UInt64.ofNat (32*18) = (576 : UInt64) := by decide +kernel
    rw [h]
  | 19, _ =>
    change readMem256 m (p + 608) = readMem256 m (p + UInt64.ofNat (32*19))
    have h : UInt64.ofNat (32*19) = (608 : UInt64) := by decide +kernel
    rw [h]
  | 20, _ =>
    change readMem256 m (p + 640) = readMem256 m (p + UInt64.ofNat (32*20))
    have h : UInt64.ofNat (32*20) = (640 : UInt64) := by decide +kernel
    rw [h]
  | 21, _ =>
    change readMem256 m (p + 672) = readMem256 m (p + UInt64.ofNat (32*21))
    have h : UInt64.ofNat (32*21) = (672 : UInt64) := by decide +kernel
    rw [h]
  | 22, _ =>
    change readMem256 m (p + 704) = readMem256 m (p + UInt64.ofNat (32*22))
    have h : UInt64.ofNat (32*22) = (704 : UInt64) := by decide +kernel
    rw [h]
  | 23, _ =>
    change readMem256 m (p + 736) = readMem256 m (p + UInt64.ofNat (32*23))
    have h : UInt64.ofNat (32*23) = (736 : UInt64) := by decide +kernel
    rw [h]
  | 24, _ =>
    change readMem256 m (p + 768) = readMem256 m (p + UInt64.ofNat (32*24))
    have h : UInt64.ofNat (32*24) = (768 : UInt64) := by decide +kernel
    rw [h]
  | n+25, h => exact False.elim (by omega)

theorem keccak4xLaneState_congr (v w : Nat → Vec256)
    (h : ∀ j : Nat, j < 25 → v j = w j) (q : Nat) :
    keccak4xLaneState v q = keccak4xLaneState w q := by
  unfold keccak4xLaneState
  simp only [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide), h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide), h 12 (by decide), h 13 (by decide), h 14 (by decide), h 15 (by decide), h 16 (by decide), h 17 (by decide), h 18 (by decide), h 19 (by decide), h 20 (by decide), h 21 (by decide), h 22 (by decide), h 23 (by decide), h 24 (by decide)]

/-- The public round-constant read survives all rho/pi scratch writes. -/
theorem keccak4xScratchPrefix_constant (m : UInt64 → UInt8) (sp rp : UInt64)
    (v : Nat → Vec256) (hd : keccak4xDisjoint rp 8 sp 800)
    (n : Nat) (hn : n ≤ 25) :
    readMem64 (keccak4xScratchPrefix m sp v n) rp = readMem64 m rp := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [keccak4xScratchPrefix]
    have hlt := keccak4x_perm_lt n (by omega)
    rw [keccakChiMpc_readMem64_writeMem256_disjoint]
    · exact ih (by omega)
    · intro a b ha hb he
      rw [u64_add_ofNat_assoc sp (32*keccak4xPerm n) b (by omega)] at he
      exact hd a (32*keccak4xPerm n+b) ha (by omega) he

/-- Final state writes are ordered in chi row order. -/
def keccak4xStatePrefix (m : UInt64 → UInt8) (p : UInt64)
    (v : Nat → Vec256) (rc : UInt64) : Nat → (UInt64 → UInt8)
  | 0 => m
  | n+1 => writeMem256 (keccak4xStatePrefix m p v rc n)
      (p + UInt64.ofNat (32*n)) (keccak4xRoundVec v rc n)

theorem keccak4xStatePrefix_read (m : UInt64 → UInt8) (p : UInt64)
    (v : Nat → Vec256) (rc : UInt64) (n : Nat) (hn : n ≤ 25) (j : Nat) (hj : j < 25) :
    readMem256 (keccak4xStatePrefix m p v rc n) (p + UInt64.ofNat (32*j)) =
      if j < n then keccak4xRoundVec v rc j
      else readMem256 m (p + UInt64.ofNat (32*j)) := by
  induction n with
  | zero => simp [keccak4xStatePrefix]
  | succ n ih =>
    rw [keccak4xStatePrefix]
    by_cases he : n = j
    · rw [he, keccakChiMpc_readMem256_writeMem256_same]
      simp
    · rw [keccak4x_read256_write_other _ p n j (by omega) hj he, ih (by omega)]
      by_cases hl : j < n
      · rw [ite_eq_left hl, ite_eq_left (by omega)]
      · rw [ite_eq_right hl, ite_eq_right (by omega)]

/-- State writes do not disturb the 25 rho/pi scratch vectors needed by later rows. -/
theorem keccak4xStatePrefix_scratch (m : UInt64 → UInt8) (p sp : UInt64)
    (v : Nat → Vec256) (rc : UInt64) (hd : keccak4xDisjoint sp 800 p 800)
    (n : Nat) (hn : n ≤ 25) (j : Nat) (hj : j < 25) :
    readMem256 (keccak4xStatePrefix m p v rc n) (sp + UInt64.ofNat (32*j)) =
      readMem256 m (sp + UInt64.ofNat (32*j)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [keccak4xStatePrefix]
    rw [keccakChiMpc_readMem256_writeMem256_disjoint]
    · exact ih (by omega)
    · intro a b ha hb he
      rw [u64_add_ofNat_assoc sp (32*j) a (by omega),
        u64_add_ofNat_assoc p (32*n) b (by omega)] at he
      exact hd (32*j+a) (32*n+b) (by omega) (by omega) he

/-- Whole-memory specification of one round, including its scratch-buffer effects. -/
def keccak4xRoundMem (m : UInt64 → UInt8) (p sp rp : UInt64) : UInt64 → UInt8 :=
  let v := keccak4xSource m p
  keccak4xStatePrefix (keccak4xScratchPrefix m sp v 25) p v (readMem64 m rp) 25

/-- Full readback of the round memory specification, all 25 lanes of all four states. -/
theorem keccak4xRoundMem_readback (m : UInt64 → UInt8) (p sp rp : UInt64)
    (q : Nat) (hq : q < 4) :
    keccak4xLaneState (keccak4xSource (keccak4xRoundMem m p sp rp) p) q =
      roundS (keccak4xLaneState (keccak4xSource m p) q) (readMem64 m rp) := by
  calc
    _ = keccak4xLaneState (keccak4xRoundVec (keccak4xSource m p) (readMem64 m rp)) q := by
      apply keccak4xLaneState_congr
      intro j hj
      rw [keccak4xSource_eq _ _ j hj]
      unfold keccak4xRoundMem
      rw [keccak4xStatePrefix_read _ _ _ _ 25 (by decide) j hj, ite_eq_left hj]
    _ = _ := keccak4xRoundVec_reconstruct _ _ q hq

def keccak4xOffset : Nat → UInt64
  | 0 => 0
  | 1 => 32
  | 2 => 64
  | 3 => 96
  | 4 => 128
  | 5 => 160
  | 6 => 192
  | 7 => 224
  | 8 => 256
  | 9 => 288
  | 10 => 320
  | 11 => 352
  | 12 => 384
  | 13 => 416
  | 14 => 448
  | 15 => 480
  | 16 => 512
  | 17 => 544
  | 18 => 576
  | 19 => 608
  | 20 => 640
  | 21 => 672
  | 22 => 704
  | 23 => 736
  | 24 => 768
  | _ => 0

theorem keccak4xOffset_eq (i : Nat) (hi : i < 25) :
    keccak4xOffset i = UInt64.ofNat (32*i) := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ | 24, _ => decide +kernel
  | n+25, h => exact False.elim (by omega)

def keccak4xRhoPc : Nat → Nat
  | 0 => 302
  | 1 => 311
  | 2 => 339
  | 3 => 367
  | 4 => 395
  | 5 => 426
  | 6 => 457
  | 7 => 485
  | 8 => 516
  | 9 => 547
  | 10 => 578
  | 11 => 609
  | 12 => 640
  | 13 => 668
  | 14 => 699
  | 15 => 730
  | 16 => 761
  | 17 => 792
  | 18 => 823
  | 19 => 851
  | 20 => 882
  | 21 => 913
  | 22 => 944
  | 23 => 975
  | 24 => 1006
  | 25 => 1037
  | _ => 1037

def keccak4xRhoCount (i : Nat) : Nat := if i == 0 then 2 else 5

theorem keccak4x_rho0_steps (s : X86State) (hp : s.pc = 302) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 5 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 0) = a) :
    ∃ t, StepsX86 keccak4xProg 2 s t ∧
      t.pc = 311 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 0)
        (keccak4xRhoRot (keccak4xXor d a) 0) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  iterate 2
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho1_steps (s : X86State) (hp : s.pc = 311) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 6 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 32) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 339 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 320)
        (keccak4xRhoRot (keccak4xXor d a) 1) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 1 = (1 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 63 = (63 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho2_steps (s : X86State) (hp : s.pc = 339) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 7 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 64) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 367 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 640)
        (keccak4xRhoRot (keccak4xXor d a) 2) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 62 = (62 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 2 = (2 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho3_steps (s : X86State) (hp : s.pc = 367) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 8 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 96) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 395 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 160)
        (keccak4xRhoRot (keccak4xXor d a) 3) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 28 = (28 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 36 = (36 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho4_steps (s : X86State) (hp : s.pc = 395) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 9 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 128) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 426 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 480)
        (keccak4xRhoRot (keccak4xXor d a) 4) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 27 = (27 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 37 = (37 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho5_steps (s : X86State) (hp : s.pc = 426) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 5 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 160) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 457 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 512)
        (keccak4xRhoRot (keccak4xXor d a) 5) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 36 = (36 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 28 = (28 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho6_steps (s : X86State) (hp : s.pc = 457) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 6 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 192) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 485 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 32)
        (keccak4xRhoRot (keccak4xXor d a) 6) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 44 = (44 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 20 = (20 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho7_steps (s : X86State) (hp : s.pc = 485) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 7 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 224) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 516 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 352)
        (keccak4xRhoRot (keccak4xXor d a) 7) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 6 = (6 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 58 = (58 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho8_steps (s : X86State) (hp : s.pc = 516) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 8 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 256) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 547 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 672)
        (keccak4xRhoRot (keccak4xXor d a) 8) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 55 = (55 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 9 = (9 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho9_steps (s : X86State) (hp : s.pc = 547) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 9 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 288) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 578 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 192)
        (keccak4xRhoRot (keccak4xXor d a) 9) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 20 = (20 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 44 = (44 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho10_steps (s : X86State) (hp : s.pc = 578) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 5 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 320) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 609 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 224)
        (keccak4xRhoRot (keccak4xXor d a) 10) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 3 = (3 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 61 = (61 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho11_steps (s : X86State) (hp : s.pc = 609) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 6 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 352) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 640 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 544)
        (keccak4xRhoRot (keccak4xXor d a) 11) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 10 = (10 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 54 = (54 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho12_steps (s : X86State) (hp : s.pc = 640) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 7 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 384) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 668 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 64)
        (keccak4xRhoRot (keccak4xXor d a) 12) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 43 = (43 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 21 = (21 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho13_steps (s : X86State) (hp : s.pc = 668) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 8 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 416) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 699 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 384)
        (keccak4xRhoRot (keccak4xXor d a) 13) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 25 = (25 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 39 = (39 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho14_steps (s : X86State) (hp : s.pc = 699) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 9 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 448) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 730 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 704)
        (keccak4xRhoRot (keccak4xXor d a) 14) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 39 = (39 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 25 = (25 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho15_steps (s : X86State) (hp : s.pc = 730) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 5 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 480) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 761 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 736)
        (keccak4xRhoRot (keccak4xXor d a) 15) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 41 = (41 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 23 = (23 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho16_steps (s : X86State) (hp : s.pc = 761) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 6 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 512) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 792 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 256)
        (keccak4xRhoRot (keccak4xXor d a) 16) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 45 = (45 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 19 = (19 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho17_steps (s : X86State) (hp : s.pc = 792) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 7 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 544) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 823 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 576)
        (keccak4xRhoRot (keccak4xXor d a) 17) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 15 = (15 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 49 = (49 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho18_steps (s : X86State) (hp : s.pc = 823) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 8 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 576) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 851 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 96)
        (keccak4xRhoRot (keccak4xXor d a) 18) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 21 = (21 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 43 = (43 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho19_steps (s : X86State) (hp : s.pc = 851) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 9 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 608) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 882 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 416)
        (keccak4xRhoRot (keccak4xXor d a) 19) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 8 = (8 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 56 = (56 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho20_steps (s : X86State) (hp : s.pc = 882) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 5 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 640) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 913 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 448)
        (keccak4xRhoRot (keccak4xXor d a) 20) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 18 = (18 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 46 = (46 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho21_steps (s : X86State) (hp : s.pc = 913) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 6 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 672) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 944 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 768)
        (keccak4xRhoRot (keccak4xXor d a) 21) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 2 = (2 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 62 = (62 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho22_steps (s : X86State) (hp : s.pc = 944) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 7 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 704) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 975 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 288)
        (keccak4xRhoRot (keccak4xXor d a) 22) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 61 = (61 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 3 = (3 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho23_steps (s : X86State) (hp : s.pc = 975) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 8 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 736) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 1006 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 608)
        (keccak4xRhoRot (keccak4xXor d a) 23) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 56 = (56 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 8 = (8 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho24_steps (s : X86State) (hp : s.pc = 1006) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get 9 = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + 768) = a) :
    ∃ t, StepsX86 keccak4xProg 5 s t ∧
      t.pc = 1037 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + 128)
        (keccak4xRhoRot (keccak4xXor d a) 24) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh hd ha
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at hd ha
  have hk : UInt64.ofNat 14 = (14 : UInt64) := by decide +kernel
  have hj : UInt64.ofNat 50 = (50 : UInt64) := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, hd, ha]
        simp [evalVecBin256, evalVecShift256, hk, hj]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [keccak4xRhoRot, keccak4xRotl, keccak4xXor, rotlK, UInt64.add_zero, Bank16.get]
  · intro x hx
    match x, hx with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ => simp [Bank16.get, hd]
    | n+5, h => exact False.elim (by omega)

theorem keccak4x_rho_steps (s : X86State) (i : Nat) (hi : i < 25)
    (hp : s.pc = keccak4xRhoPc i) (hh : s.halted = false)
    (a d : Vec256) (hd : s.ymm.get (5+i%5) = d)
    (ha : readMem256 s.mem (s.gpr.get 7 + keccak4xOffset i) = a) :
    ∃ t, StepsX86 keccak4xProg (keccak4xRhoCount i) s t ∧
      t.pc = keccak4xRhoPc (i+1) ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = writeMem256 s.mem (s.gpr.get 4 + keccak4xOffset (keccak4xPerm i))
        (keccak4xRhoRot (keccak4xXor d a) i) ∧
      (∀ x : Nat, x < 5 → t.ymm.get (5+x) = s.ymm.get (5+x)) := by
  match i, hi with
  | 0, _ => exact keccak4x_rho0_steps s hp hh a d hd ha
  | 1, _ => exact keccak4x_rho1_steps s hp hh a d hd ha
  | 2, _ => exact keccak4x_rho2_steps s hp hh a d hd ha
  | 3, _ => exact keccak4x_rho3_steps s hp hh a d hd ha
  | 4, _ => exact keccak4x_rho4_steps s hp hh a d hd ha
  | 5, _ => exact keccak4x_rho5_steps s hp hh a d hd ha
  | 6, _ => exact keccak4x_rho6_steps s hp hh a d hd ha
  | 7, _ => exact keccak4x_rho7_steps s hp hh a d hd ha
  | 8, _ => exact keccak4x_rho8_steps s hp hh a d hd ha
  | 9, _ => exact keccak4x_rho9_steps s hp hh a d hd ha
  | 10, _ => exact keccak4x_rho10_steps s hp hh a d hd ha
  | 11, _ => exact keccak4x_rho11_steps s hp hh a d hd ha
  | 12, _ => exact keccak4x_rho12_steps s hp hh a d hd ha
  | 13, _ => exact keccak4x_rho13_steps s hp hh a d hd ha
  | 14, _ => exact keccak4x_rho14_steps s hp hh a d hd ha
  | 15, _ => exact keccak4x_rho15_steps s hp hh a d hd ha
  | 16, _ => exact keccak4x_rho16_steps s hp hh a d hd ha
  | 17, _ => exact keccak4x_rho17_steps s hp hh a d hd ha
  | 18, _ => exact keccak4x_rho18_steps s hp hh a d hd ha
  | 19, _ => exact keccak4x_rho19_steps s hp hh a d hd ha
  | 20, _ => exact keccak4x_rho20_steps s hp hh a d hd ha
  | 21, _ => exact keccak4x_rho21_steps s hp hh a d hd ha
  | 22, _ => exact keccak4x_rho22_steps s hp hh a d hd ha
  | 23, _ => exact keccak4x_rho23_steps s hp hh a d hd ha
  | 24, _ => exact keccak4x_rho24_steps s hp hh a d hd ha
  | n+25, h => exact False.elim (by omega)

private theorem keccak4xXor_comm (a b : Vec256) : keccak4xXor a b = keccak4xXor b a := by
  cases a
  cases b
  unfold keccak4xXor
  congr 1 <;> exact keccak4x_u64xor_comm _ _

/-- The progressively filled rho/pi scratch area and the five live theta corrections. -/
structure keccak4xRhoInv (mem : UInt64 → UInt8) (g : Bank16 UInt64) (n : Nat) (s : X86State) : Prop where
  pc : s.pc = keccak4xRhoPc n
  halted : s.halted = false
  gpr : s.gpr = g
  memory : s.mem = keccak4xScratchPrefix mem (g.get 4) (keccak4xSource mem (g.get 7)) n
  corrections : ∀ x : Nat, x < 5 → s.ymm.get (5+x) = keccak4xD (keccak4xSource mem (g.get 7)) x

private theorem keccak4x_rho_value (v : Nat → Vec256) (n : Nat) (hn : n < 25) :
    keccak4xRhoRot (keccak4xXor (keccak4xD v (n%5)) (v n)) n =
      keccak4xRhoPi (keccak4xTheta v) (keccak4xPerm n) := by
  rw [keccak4xXor_comm]
  exact keccak4x_rho_mapping v n hn

theorem keccak4xRhoInv_step (mem : UInt64 → UInt8) (g : Bank16 UInt64)
    (hd : keccak4xDisjoint (g.get 7) 800 (g.get 4) 800)
    (n : Nat) (hn : n < 25) (s : X86State) (h : keccak4xRhoInv mem g n s) :
    ∃ t, StepsX86 keccak4xProg (keccak4xRhoCount n) s t ∧ keccak4xRhoInv mem g (n+1) t := by
  let v := keccak4xSource mem (g.get 7)
  have ha : readMem256 s.mem (s.gpr.get 7 + keccak4xOffset n) = v n := by
    rw [h.gpr, h.memory, keccak4xOffset_eq n hn,
      keccak4xScratchPrefix_input mem (g.get 4) (g.get 7) v hd n (by omega) n hn]
    exact (keccak4xSource_eq mem (g.get 7) n hn).symm
  obtain ⟨t, ht, hp, hh, hg, hm, hv⟩ := keccak4x_rho_steps s n hn h.pc h.halted
    (v n) (keccak4xD v (n%5)) (h.corrections (n%5) (Nat.mod_lt _ (by decide))) ha
  refine ⟨t, ht, hp, hh, hg.trans h.gpr, ?_, ?_⟩
  · rw [hm, h.gpr, h.memory, keccak4xOffset_eq (keccak4xPerm n) (keccak4x_perm_lt n hn),
      keccak4x_rho_value v n hn]
    rfl
  · intro x hx
    rw [hv x hx]
    exact h.corrections x hx

def keccak4xRhoFuel : Nat → Nat
  | 0 => 0
  | n+1 => keccak4xRhoFuel n + keccak4xRhoCount n

theorem keccak4xRhoInv_iter (mem : UInt64 → UInt8) (g : Bank16 UInt64)
    (hd : keccak4xDisjoint (g.get 7) 800 (g.get 4) 800)
    (s : X86State) (h : keccak4xRhoInv mem g 0 s) (n : Nat) (hn : n ≤ 25) :
    ∃ t, StepsX86 keccak4xProg (keccak4xRhoFuel n) s t ∧ keccak4xRhoInv mem g n t := by
  induction n with
  | zero => exact ⟨s, StepsX86.zero _, h⟩
  | succ n ih =>
    obtain ⟨t, ht, hi⟩ := ih (by omega)
    obtain ⟨u, hu, hiu⟩ := keccak4xRhoInv_step mem g hd n (by omega) t hi
    exact ⟨u, StepsX86_trans ht hu, hiu⟩

theorem keccak4xRhoFuel_full : keccak4xRhoFuel 25 = 122 := by decide +kernel

/-- The 167-instruction theta/rho/pi prefix on four complete Keccak states. -/
theorem keccak4x_theta_rho_pi_steps (g : Bank16 UInt64) (y : Bank16 Vec256)
    (cf ofl zf dy : Bool) (mem : UInt64 → UInt8)
    (hd : keccak4xDisjoint (g.get 7) 800 (g.get 4) 800) :
    ∃ t, StepsX86 keccak4xProg 167 ⟨20,g,y,cf,ofl,zf,dy,false,mem⟩ t ∧
      t.pc = 1037 ∧ t.halted = false ∧ t.gpr = g ∧
      t.mem = keccak4xScratchPrefix mem (g.get 4) (keccak4xSource mem (g.get 7)) 25 := by
  obtain ⟨t, ht, hp, hh, hg, hm, hv⟩ := keccak4x_parity_steps g y cf ofl zf dy mem
  have hi : keccak4xRhoInv mem g 0 t := ⟨hp, hh, hg, hm, hv⟩
  obtain ⟨u, hu, hiu⟩ := keccak4xRhoInv_iter mem g hd t hi 25 (by decide)
  rw [keccak4xRhoFuel_full] at hu
  exact ⟨u, StepsX86_trans ht hu, hiu.pc, hiu.halted, hiu.gpr, hiu.memory⟩

def keccak4xRowMem0 (m : UInt64 → UInt8) (p : UInt64) (a0 a1 a2 a3 a4 : Vec256) (rc : UInt64) : UInt64 → UInt8 :=
  let c0 := keccak4xXor (keccak4xChiVec a0 a1 a2) ⟨rc,rc,rc,rc⟩
  let c1 := keccak4xChiVec a1 a2 a3
  let c2 := keccak4xChiVec a2 a3 a4
  let c3 := keccak4xChiVec a3 a4 a0
  let c4 := keccak4xChiVec a4 a0 a1
  let m0 := writeMem256 m (p + 0) c0
  let m1 := writeMem256 m0 (p + 32) c1
  let m2 := writeMem256 m1 (p + 64) c2
  let m3 := writeMem256 m2 (p + 96) c3
  let m4 := writeMem256 m3 (p + 128) c4
  m4

set_option maxHeartbeats 500000 in
theorem keccak4x_row0_steps (s : X86State) (hp : s.pc = 1037) (hh : s.halted = false)
    (a0 a1 a2 a3 a4 : Vec256) (rc : UInt64)
    (h0 : readMem256 s.mem (s.gpr.get 4 + 0) = a0)
    (h1 : readMem256 s.mem (s.gpr.get 4 + 32) = a1)
    (h2 : readMem256 s.mem (s.gpr.get 4 + 64) = a2)
    (h3 : readMem256 s.mem (s.gpr.get 4 + 96) = a3)
    (h4 : readMem256 s.mem (s.gpr.get 4 + 128) = a4)
    (hr : readMem64 s.mem (s.gpr.get 6 + 0) = rc)
    : ∃ t, StepsX86 keccak4xProg 22 s t ∧
      t.pc = 1145 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = keccak4xRowMem0 s.mem (s.gpr.get 7) a0 a1 a2 a3 a4 rc := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh h0 h1 h2 h3 h4 hr
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at h0 h1 h2 h3 h4 hr
  have hc3_0 := keccak4x_u64xor_comm ((~~~a4.w0) &&& a0.w0) a3.w0
  have hc3_1 := keccak4x_u64xor_comm ((~~~a4.w1) &&& a0.w1) a3.w1
  have hc3_2 := keccak4x_u64xor_comm ((~~~a4.w2) &&& a0.w2) a3.w2
  have hc3_3 := keccak4x_u64xor_comm ((~~~a4.w3) &&& a0.w3) a3.w3
  have hc4_0 := keccak4x_u64xor_comm ((~~~a0.w0) &&& a1.w0) a4.w0
  have hc4_1 := keccak4x_u64xor_comm ((~~~a0.w1) &&& a1.w1) a4.w1
  have hc4_2 := keccak4x_u64xor_comm ((~~~a0.w2) &&& a1.w2) a4.w2
  have hc4_3 := keccak4x_u64xor_comm ((~~~a0.w3) &&& a1.w3) a4.w3
  have hrc0 := keccak4x_u64xor_comm rc (a0.w0 ^^^ ((~~~a1.w0) &&& a2.w0))
  have hrc1 := keccak4x_u64xor_comm rc (a0.w1 ^^^ ((~~~a1.w1) &&& a2.w1))
  have hrc2 := keccak4x_u64xor_comm rc (a0.w2 ^^^ ((~~~a1.w2) &&& a2.w2))
  have hrc3 := keccak4x_u64xor_comm rc (a0.w3 ^^^ ((~~~a1.w3) &&& a2.w3))
  iterate 22
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, h0, h1, h2, h3, h4, hr]
        simp only [evalVecBin256, hc3_0, hc3_1, hc3_2, hc3_3, hc4_0, hc4_1, hc4_2, hc4_3, hrc0, hrc1, hrc2, hrc3]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_⟩
  simp only [keccak4xRowMem0, keccak4xChiVec, keccak4xXor, UInt64.add_zero, Bank16.get]

def keccak4xRowMem1 (m : UInt64 → UInt8) (p : UInt64) (a0 a1 a2 a3 a4 : Vec256) (_rc : UInt64) : UInt64 → UInt8 :=
  let c0 := keccak4xChiVec a0 a1 a2
  let c1 := keccak4xChiVec a1 a2 a3
  let c2 := keccak4xChiVec a2 a3 a4
  let c3 := keccak4xChiVec a3 a4 a0
  let c4 := keccak4xChiVec a4 a0 a1
  let m0 := writeMem256 m (p + 160) c0
  let m1 := writeMem256 m0 (p + 192) c1
  let m2 := writeMem256 m1 (p + 224) c2
  let m3 := writeMem256 m2 (p + 256) c3
  let m4 := writeMem256 m3 (p + 288) c4
  m4

set_option maxHeartbeats 500000 in
theorem keccak4x_row1_steps (s : X86State) (hp : s.pc = 1145) (hh : s.halted = false)
    (a0 a1 a2 a3 a4 : Vec256) (rc : UInt64)
    (h0 : readMem256 s.mem (s.gpr.get 4 + 160) = a0)
    (h1 : readMem256 s.mem (s.gpr.get 4 + 192) = a1)
    (h2 : readMem256 s.mem (s.gpr.get 4 + 224) = a2)
    (h3 : readMem256 s.mem (s.gpr.get 4 + 256) = a3)
    (h4 : readMem256 s.mem (s.gpr.get 4 + 288) = a4)
    : ∃ t, StepsX86 keccak4xProg 20 s t ∧
      t.pc = 1270 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = keccak4xRowMem1 s.mem (s.gpr.get 7) a0 a1 a2 a3 a4 rc := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh h0 h1 h2 h3 h4
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at h0 h1 h2 h3 h4
  have hc3_0 := keccak4x_u64xor_comm ((~~~a4.w0) &&& a0.w0) a3.w0
  have hc3_1 := keccak4x_u64xor_comm ((~~~a4.w1) &&& a0.w1) a3.w1
  have hc3_2 := keccak4x_u64xor_comm ((~~~a4.w2) &&& a0.w2) a3.w2
  have hc3_3 := keccak4x_u64xor_comm ((~~~a4.w3) &&& a0.w3) a3.w3
  have hc4_0 := keccak4x_u64xor_comm ((~~~a0.w0) &&& a1.w0) a4.w0
  have hc4_1 := keccak4x_u64xor_comm ((~~~a0.w1) &&& a1.w1) a4.w1
  have hc4_2 := keccak4x_u64xor_comm ((~~~a0.w2) &&& a1.w2) a4.w2
  have hc4_3 := keccak4x_u64xor_comm ((~~~a0.w3) &&& a1.w3) a4.w3
  iterate 20
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, h0, h1, h2, h3, h4]
        simp only [evalVecBin256, hc3_0, hc3_1, hc3_2, hc3_3, hc4_0, hc4_1, hc4_2, hc4_3]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_⟩
  simp only [keccak4xRowMem1, keccak4xChiVec, keccak4xXor, UInt64.add_zero, Bank16.get]

def keccak4xRowMem2 (m : UInt64 → UInt8) (p : UInt64) (a0 a1 a2 a3 a4 : Vec256) (_rc : UInt64) : UInt64 → UInt8 :=
  let c0 := keccak4xChiVec a0 a1 a2
  let c1 := keccak4xChiVec a1 a2 a3
  let c2 := keccak4xChiVec a2 a3 a4
  let c3 := keccak4xChiVec a3 a4 a0
  let c4 := keccak4xChiVec a4 a0 a1
  let m0 := writeMem256 m (p + 320) c0
  let m1 := writeMem256 m0 (p + 352) c1
  let m2 := writeMem256 m1 (p + 384) c2
  let m3 := writeMem256 m2 (p + 416) c3
  let m4 := writeMem256 m3 (p + 448) c4
  m4

set_option maxHeartbeats 500000 in
theorem keccak4x_row2_steps (s : X86State) (hp : s.pc = 1270) (hh : s.halted = false)
    (a0 a1 a2 a3 a4 : Vec256) (rc : UInt64)
    (h0 : readMem256 s.mem (s.gpr.get 4 + 320) = a0)
    (h1 : readMem256 s.mem (s.gpr.get 4 + 352) = a1)
    (h2 : readMem256 s.mem (s.gpr.get 4 + 384) = a2)
    (h3 : readMem256 s.mem (s.gpr.get 4 + 416) = a3)
    (h4 : readMem256 s.mem (s.gpr.get 4 + 448) = a4)
    : ∃ t, StepsX86 keccak4xProg 20 s t ∧
      t.pc = 1395 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = keccak4xRowMem2 s.mem (s.gpr.get 7) a0 a1 a2 a3 a4 rc := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh h0 h1 h2 h3 h4
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at h0 h1 h2 h3 h4
  have hc3_0 := keccak4x_u64xor_comm ((~~~a4.w0) &&& a0.w0) a3.w0
  have hc3_1 := keccak4x_u64xor_comm ((~~~a4.w1) &&& a0.w1) a3.w1
  have hc3_2 := keccak4x_u64xor_comm ((~~~a4.w2) &&& a0.w2) a3.w2
  have hc3_3 := keccak4x_u64xor_comm ((~~~a4.w3) &&& a0.w3) a3.w3
  have hc4_0 := keccak4x_u64xor_comm ((~~~a0.w0) &&& a1.w0) a4.w0
  have hc4_1 := keccak4x_u64xor_comm ((~~~a0.w1) &&& a1.w1) a4.w1
  have hc4_2 := keccak4x_u64xor_comm ((~~~a0.w2) &&& a1.w2) a4.w2
  have hc4_3 := keccak4x_u64xor_comm ((~~~a0.w3) &&& a1.w3) a4.w3
  iterate 20
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, h0, h1, h2, h3, h4]
        simp only [evalVecBin256, hc3_0, hc3_1, hc3_2, hc3_3, hc4_0, hc4_1, hc4_2, hc4_3]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_⟩
  simp only [keccak4xRowMem2, keccak4xChiVec, keccak4xXor, UInt64.add_zero, Bank16.get]

def keccak4xRowMem3 (m : UInt64 → UInt8) (p : UInt64) (a0 a1 a2 a3 a4 : Vec256) (_rc : UInt64) : UInt64 → UInt8 :=
  let c0 := keccak4xChiVec a0 a1 a2
  let c1 := keccak4xChiVec a1 a2 a3
  let c2 := keccak4xChiVec a2 a3 a4
  let c3 := keccak4xChiVec a3 a4 a0
  let c4 := keccak4xChiVec a4 a0 a1
  let m0 := writeMem256 m (p + 480) c0
  let m1 := writeMem256 m0 (p + 512) c1
  let m2 := writeMem256 m1 (p + 544) c2
  let m3 := writeMem256 m2 (p + 576) c3
  let m4 := writeMem256 m3 (p + 608) c4
  m4

set_option maxHeartbeats 500000 in
theorem keccak4x_row3_steps (s : X86State) (hp : s.pc = 1395) (hh : s.halted = false)
    (a0 a1 a2 a3 a4 : Vec256) (rc : UInt64)
    (h0 : readMem256 s.mem (s.gpr.get 4 + 480) = a0)
    (h1 : readMem256 s.mem (s.gpr.get 4 + 512) = a1)
    (h2 : readMem256 s.mem (s.gpr.get 4 + 544) = a2)
    (h3 : readMem256 s.mem (s.gpr.get 4 + 576) = a3)
    (h4 : readMem256 s.mem (s.gpr.get 4 + 608) = a4)
    : ∃ t, StepsX86 keccak4xProg 20 s t ∧
      t.pc = 1520 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = keccak4xRowMem3 s.mem (s.gpr.get 7) a0 a1 a2 a3 a4 rc := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh h0 h1 h2 h3 h4
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at h0 h1 h2 h3 h4
  have hc3_0 := keccak4x_u64xor_comm ((~~~a4.w0) &&& a0.w0) a3.w0
  have hc3_1 := keccak4x_u64xor_comm ((~~~a4.w1) &&& a0.w1) a3.w1
  have hc3_2 := keccak4x_u64xor_comm ((~~~a4.w2) &&& a0.w2) a3.w2
  have hc3_3 := keccak4x_u64xor_comm ((~~~a4.w3) &&& a0.w3) a3.w3
  have hc4_0 := keccak4x_u64xor_comm ((~~~a0.w0) &&& a1.w0) a4.w0
  have hc4_1 := keccak4x_u64xor_comm ((~~~a0.w1) &&& a1.w1) a4.w1
  have hc4_2 := keccak4x_u64xor_comm ((~~~a0.w2) &&& a1.w2) a4.w2
  have hc4_3 := keccak4x_u64xor_comm ((~~~a0.w3) &&& a1.w3) a4.w3
  iterate 20
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, h0, h1, h2, h3, h4]
        simp only [evalVecBin256, hc3_0, hc3_1, hc3_2, hc3_3, hc4_0, hc4_1, hc4_2, hc4_3]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_⟩
  simp only [keccak4xRowMem3, keccak4xChiVec, keccak4xXor, UInt64.add_zero, Bank16.get]

def keccak4xRowMem4 (m : UInt64 → UInt8) (p : UInt64) (a0 a1 a2 a3 a4 : Vec256) (_rc : UInt64) : UInt64 → UInt8 :=
  let c0 := keccak4xChiVec a0 a1 a2
  let c1 := keccak4xChiVec a1 a2 a3
  let c2 := keccak4xChiVec a2 a3 a4
  let c3 := keccak4xChiVec a3 a4 a0
  let c4 := keccak4xChiVec a4 a0 a1
  let m0 := writeMem256 m (p + 640) c0
  let m1 := writeMem256 m0 (p + 672) c1
  let m2 := writeMem256 m1 (p + 704) c2
  let m3 := writeMem256 m2 (p + 736) c3
  let m4 := writeMem256 m3 (p + 768) c4
  m4

set_option maxHeartbeats 500000 in
theorem keccak4x_row4_steps (s : X86State) (hp : s.pc = 1520) (hh : s.halted = false)
    (a0 a1 a2 a3 a4 : Vec256) (rc : UInt64)
    (h0 : readMem256 s.mem (s.gpr.get 4 + 640) = a0)
    (h1 : readMem256 s.mem (s.gpr.get 4 + 672) = a1)
    (h2 : readMem256 s.mem (s.gpr.get 4 + 704) = a2)
    (h3 : readMem256 s.mem (s.gpr.get 4 + 736) = a3)
    (h4 : readMem256 s.mem (s.gpr.get 4 + 768) = a4)
    : ∃ t, StepsX86 keccak4xProg 20 s t ∧
      t.pc = 1645 ∧ t.halted = false ∧ t.gpr = s.gpr ∧
      t.mem = keccak4xRowMem4 s.mem (s.gpr.get 7) a0 a1 a2 a3 a4 rc := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh h0 h1 h2 h3 h4
  subst pc hlt
  simp only [Bank16.get, UInt64.add_zero] at h0 h1 h2 h3 h4
  have hc3_0 := keccak4x_u64xor_comm ((~~~a4.w0) &&& a0.w0) a3.w0
  have hc3_1 := keccak4x_u64xor_comm ((~~~a4.w1) &&& a0.w1) a3.w1
  have hc3_2 := keccak4x_u64xor_comm ((~~~a4.w2) &&& a0.w2) a3.w2
  have hc3_3 := keccak4x_u64xor_comm ((~~~a4.w3) &&& a0.w3) a3.w3
  have hc4_0 := keccak4x_u64xor_comm ((~~~a0.w0) &&& a1.w0) a4.w0
  have hc4_1 := keccak4x_u64xor_comm ((~~~a0.w1) &&& a1.w1) a4.w1
  have hc4_2 := keccak4x_u64xor_comm ((~~~a0.w2) &&& a1.w2) a4.w2
  have hc4_3 := keccak4x_u64xor_comm ((~~~a0.w3) &&& a1.w3) a4.w3
  iterate 20
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        dsimp only [stepX86, evalX86Addr, clampVecWidth, Bank16.get, Bank16.set]
        simp only [ite_true, ite_false, UInt64.add_zero, h0, h1, h2, h3, h4]
        simp only [evalVecBin256, hc3_0, hc3_1, hc3_2, hc3_3, hc4_0, hc4_1, hc4_2, hc4_3]
      all_goals rfl
  refine ⟨_, StepsX86.zero _, rfl, rfl, rfl, ?_⟩
  simp only [keccak4xRowMem4, keccak4xChiVec, keccak4xXor, UInt64.add_zero, Bank16.get]


private theorem keccak4xDisjoint_symm (a b : UInt64) (n m : Nat)
    (h : keccak4xDisjoint a n b m) : keccak4xDisjoint b m a n := by
  intro i j hi hj he
  exact h j i hj hi he.symm

theorem keccak4xRowMem0_prefix (m : UInt64 → UInt8) (p : UInt64) (v : Nat → Vec256) (rc : UInt64) :
    keccak4xRowMem0 (keccak4xStatePrefix m p v rc 0) p
      (keccak4xRhoPi (keccak4xTheta v) 0) (keccak4xRhoPi (keccak4xTheta v) 1) (keccak4xRhoPi (keccak4xTheta v) 2) (keccak4xRhoPi (keccak4xTheta v) 3) (keccak4xRhoPi (keccak4xTheta v) 4) rc =
    keccak4xStatePrefix m p v rc 5 := by
  have h0 : UInt64.ofNat (32*0) = (0 : UInt64) := by decide +kernel
  have h1 : UInt64.ofNat (32*1) = (32 : UInt64) := by decide +kernel
  have h2 : UInt64.ofNat (32*2) = (64 : UInt64) := by decide +kernel
  have h3 : UInt64.ofNat (32*3) = (96 : UInt64) := by decide +kernel
  have h4 : UInt64.ofNat (32*4) = (128 : UInt64) := by decide +kernel
  conv =>
    rhs
    rw [keccak4xStatePrefix, keccak4xStatePrefix, keccak4xStatePrefix,
      keccak4xStatePrefix, keccak4xStatePrefix]
  simp [keccak4xRowMem0, keccak4xRoundVec, keccak4xChi, h0, h1, h2, h3, h4]

theorem keccak4xRowMem1_prefix (m : UInt64 → UInt8) (p : UInt64) (v : Nat → Vec256) (rc : UInt64) :
    keccak4xRowMem1 (keccak4xStatePrefix m p v rc 5) p
      (keccak4xRhoPi (keccak4xTheta v) 5) (keccak4xRhoPi (keccak4xTheta v) 6) (keccak4xRhoPi (keccak4xTheta v) 7) (keccak4xRhoPi (keccak4xTheta v) 8) (keccak4xRhoPi (keccak4xTheta v) 9) rc =
    keccak4xStatePrefix m p v rc 10 := by
  have h0 : UInt64.ofNat (32*5) = (160 : UInt64) := by decide +kernel
  have h1 : UInt64.ofNat (32*6) = (192 : UInt64) := by decide +kernel
  have h2 : UInt64.ofNat (32*7) = (224 : UInt64) := by decide +kernel
  have h3 : UInt64.ofNat (32*8) = (256 : UInt64) := by decide +kernel
  have h4 : UInt64.ofNat (32*9) = (288 : UInt64) := by decide +kernel
  conv =>
    rhs
    rw [keccak4xStatePrefix, keccak4xStatePrefix, keccak4xStatePrefix,
      keccak4xStatePrefix, keccak4xStatePrefix]
  simp [keccak4xRowMem1, keccak4xRoundVec, keccak4xChi, h0, h1, h2, h3, h4]

theorem keccak4xRowMem2_prefix (m : UInt64 → UInt8) (p : UInt64) (v : Nat → Vec256) (rc : UInt64) :
    keccak4xRowMem2 (keccak4xStatePrefix m p v rc 10) p
      (keccak4xRhoPi (keccak4xTheta v) 10) (keccak4xRhoPi (keccak4xTheta v) 11) (keccak4xRhoPi (keccak4xTheta v) 12) (keccak4xRhoPi (keccak4xTheta v) 13) (keccak4xRhoPi (keccak4xTheta v) 14) rc =
    keccak4xStatePrefix m p v rc 15 := by
  have h0 : UInt64.ofNat (32*10) = (320 : UInt64) := by decide +kernel
  have h1 : UInt64.ofNat (32*11) = (352 : UInt64) := by decide +kernel
  have h2 : UInt64.ofNat (32*12) = (384 : UInt64) := by decide +kernel
  have h3 : UInt64.ofNat (32*13) = (416 : UInt64) := by decide +kernel
  have h4 : UInt64.ofNat (32*14) = (448 : UInt64) := by decide +kernel
  conv =>
    rhs
    rw [keccak4xStatePrefix, keccak4xStatePrefix, keccak4xStatePrefix,
      keccak4xStatePrefix, keccak4xStatePrefix]
  simp [keccak4xRowMem2, keccak4xRoundVec, keccak4xChi, h0, h1, h2, h3, h4]

theorem keccak4xRowMem3_prefix (m : UInt64 → UInt8) (p : UInt64) (v : Nat → Vec256) (rc : UInt64) :
    keccak4xRowMem3 (keccak4xStatePrefix m p v rc 15) p
      (keccak4xRhoPi (keccak4xTheta v) 15) (keccak4xRhoPi (keccak4xTheta v) 16) (keccak4xRhoPi (keccak4xTheta v) 17) (keccak4xRhoPi (keccak4xTheta v) 18) (keccak4xRhoPi (keccak4xTheta v) 19) rc =
    keccak4xStatePrefix m p v rc 20 := by
  have h0 : UInt64.ofNat (32*15) = (480 : UInt64) := by decide +kernel
  have h1 : UInt64.ofNat (32*16) = (512 : UInt64) := by decide +kernel
  have h2 : UInt64.ofNat (32*17) = (544 : UInt64) := by decide +kernel
  have h3 : UInt64.ofNat (32*18) = (576 : UInt64) := by decide +kernel
  have h4 : UInt64.ofNat (32*19) = (608 : UInt64) := by decide +kernel
  conv =>
    rhs
    rw [keccak4xStatePrefix, keccak4xStatePrefix, keccak4xStatePrefix,
      keccak4xStatePrefix, keccak4xStatePrefix]
  simp [keccak4xRowMem3, keccak4xRoundVec, keccak4xChi, h0, h1, h2, h3, h4]

theorem keccak4xRowMem4_prefix (m : UInt64 → UInt8) (p : UInt64) (v : Nat → Vec256) (rc : UInt64) :
    keccak4xRowMem4 (keccak4xStatePrefix m p v rc 20) p
      (keccak4xRhoPi (keccak4xTheta v) 20) (keccak4xRhoPi (keccak4xTheta v) 21) (keccak4xRhoPi (keccak4xTheta v) 22) (keccak4xRhoPi (keccak4xTheta v) 23) (keccak4xRhoPi (keccak4xTheta v) 24) rc =
    keccak4xStatePrefix m p v rc 25 := by
  have h0 : UInt64.ofNat (32*20) = (640 : UInt64) := by decide +kernel
  have h1 : UInt64.ofNat (32*21) = (672 : UInt64) := by decide +kernel
  have h2 : UInt64.ofNat (32*22) = (704 : UInt64) := by decide +kernel
  have h3 : UInt64.ofNat (32*23) = (736 : UInt64) := by decide +kernel
  have h4 : UInt64.ofNat (32*24) = (768 : UInt64) := by decide +kernel
  conv =>
    rhs
    rw [keccak4xStatePrefix, keccak4xStatePrefix, keccak4xStatePrefix,
      keccak4xStatePrefix, keccak4xStatePrefix]
  simp [keccak4xRowMem4, keccak4xRoundVec, keccak4xChi, h0, h1, h2, h3, h4]

def keccak4xRowPc : Nat → Nat
  | 0 => 1037 | 1 => 1145 | 2 => 1270 | 3 => 1395 | 4 => 1520 | _ => 1645

def keccak4xRowCount (r : Nat) : Nat := if r == 0 then 22 else 20

structure keccak4xRowInv (mem : UInt64 → UInt8) (g : Bank16 UInt64) (r : Nat) (s : X86State) : Prop where
  pc : s.pc = keccak4xRowPc r
  halted : s.halted = false
  gpr : s.gpr = g
  memory : s.mem = keccak4xStatePrefix
    (keccak4xScratchPrefix mem (g.get 4) (keccak4xSource mem (g.get 7)) 25)
    (g.get 7) (keccak4xSource mem (g.get 7)) (readMem64 mem (g.get 6)) (5*r)

theorem keccak4xRowInv_read (mem : UInt64 → UInt8) (g : Bank16 UInt64)
    (hd : keccak4xDisjoint (g.get 7) 800 (g.get 4) 800)
    (r : Nat) (hr : r ≤ 5) (s : X86State) (h : keccak4xRowInv mem g r s)
    (j : Nat) (hj : j < 25) :
    readMem256 s.mem (s.gpr.get 4 + keccak4xOffset j) =
      keccak4xRhoPi (keccak4xTheta (keccak4xSource mem (g.get 7))) j := by
  rw [h.gpr, h.memory, keccak4xOffset_eq j hj,
    keccak4xStatePrefix_scratch _ _ _ _ _
      (keccak4xDisjoint_symm _ _ _ _ hd) (5*r) (by omega) j hj,
    keccak4xScratchPrefix_complete _ _ _ j hj]

theorem keccak4xRowInv_step (mem : UInt64 → UInt8) (g : Bank16 UInt64)
    (hd : keccak4xDisjoint (g.get 7) 800 (g.get 4) 800)
    (hc : keccak4xDisjoint (g.get 6) 8 (g.get 4) 800)
    (r : Nat) (hr : r < 5) (s : X86State) (h : keccak4xRowInv mem g r s) :
    ∃ t, StepsX86 keccak4xProg (keccak4xRowCount r) s t ∧ keccak4xRowInv mem g (r+1) t := by
  let v := keccak4xSource mem (g.get 7)
  have hread := keccak4xRowInv_read mem g hd r (by omega) s h
  match r, hr with
  | 0, _ =>
    have hconst : readMem64 s.mem (s.gpr.get 6 + 0) = readMem64 mem (g.get 6) := by
      rw [UInt64.add_zero, h.gpr, h.memory]
      exact keccak4xScratchPrefix_constant mem (g.get 4) (g.get 6) v hc 25 (by decide)
    obtain ⟨t, ht, hp, hh, hg, hm⟩ := keccak4x_row0_steps s h.pc h.halted
      (keccak4xRhoPi (keccak4xTheta v) 0) (keccak4xRhoPi (keccak4xTheta v) 1) (keccak4xRhoPi (keccak4xTheta v) 2) (keccak4xRhoPi (keccak4xTheta v) 3) (keccak4xRhoPi (keccak4xTheta v) 4) (readMem64 mem (g.get 6))
      (hread 0 (by decide)) (hread 1 (by decide)) (hread 2 (by decide)) (hread 3 (by decide)) (hread 4 (by decide)) hconst
    refine ⟨t, ht, hp, hh, hg.trans h.gpr, ?_⟩
    rw [hm, h.gpr, h.memory, keccak4xRowMem0_prefix]
  | 1, _ =>
    obtain ⟨t, ht, hp, hh, hg, hm⟩ := keccak4x_row1_steps s h.pc h.halted
      (keccak4xRhoPi (keccak4xTheta v) 5) (keccak4xRhoPi (keccak4xTheta v) 6) (keccak4xRhoPi (keccak4xTheta v) 7) (keccak4xRhoPi (keccak4xTheta v) 8) (keccak4xRhoPi (keccak4xTheta v) 9) (readMem64 mem (g.get 6))
      (hread 5 (by decide)) (hread 6 (by decide)) (hread 7 (by decide)) (hread 8 (by decide)) (hread 9 (by decide))
    refine ⟨t, ht, hp, hh, hg.trans h.gpr, ?_⟩
    rw [hm, h.gpr, h.memory, keccak4xRowMem1_prefix]
  | 2, _ =>
    obtain ⟨t, ht, hp, hh, hg, hm⟩ := keccak4x_row2_steps s h.pc h.halted
      (keccak4xRhoPi (keccak4xTheta v) 10) (keccak4xRhoPi (keccak4xTheta v) 11) (keccak4xRhoPi (keccak4xTheta v) 12) (keccak4xRhoPi (keccak4xTheta v) 13) (keccak4xRhoPi (keccak4xTheta v) 14) (readMem64 mem (g.get 6))
      (hread 10 (by decide)) (hread 11 (by decide)) (hread 12 (by decide)) (hread 13 (by decide)) (hread 14 (by decide))
    refine ⟨t, ht, hp, hh, hg.trans h.gpr, ?_⟩
    rw [hm, h.gpr, h.memory, keccak4xRowMem2_prefix]
  | 3, _ =>
    obtain ⟨t, ht, hp, hh, hg, hm⟩ := keccak4x_row3_steps s h.pc h.halted
      (keccak4xRhoPi (keccak4xTheta v) 15) (keccak4xRhoPi (keccak4xTheta v) 16) (keccak4xRhoPi (keccak4xTheta v) 17) (keccak4xRhoPi (keccak4xTheta v) 18) (keccak4xRhoPi (keccak4xTheta v) 19) (readMem64 mem (g.get 6))
      (hread 15 (by decide)) (hread 16 (by decide)) (hread 17 (by decide)) (hread 18 (by decide)) (hread 19 (by decide))
    refine ⟨t, ht, hp, hh, hg.trans h.gpr, ?_⟩
    rw [hm, h.gpr, h.memory, keccak4xRowMem3_prefix]
  | 4, _ =>
    obtain ⟨t, ht, hp, hh, hg, hm⟩ := keccak4x_row4_steps s h.pc h.halted
      (keccak4xRhoPi (keccak4xTheta v) 20) (keccak4xRhoPi (keccak4xTheta v) 21) (keccak4xRhoPi (keccak4xTheta v) 22) (keccak4xRhoPi (keccak4xTheta v) 23) (keccak4xRhoPi (keccak4xTheta v) 24) (readMem64 mem (g.get 6))
      (hread 20 (by decide)) (hread 21 (by decide)) (hread 22 (by decide)) (hread 23 (by decide)) (hread 24 (by decide))
    refine ⟨t, ht, hp, hh, hg.trans h.gpr, ?_⟩
    rw [hm, h.gpr, h.memory, keccak4xRowMem4_prefix]
  | n+5, hh => exact False.elim (by omega)

def keccak4xRowFuel : Nat → Nat
  | 0 => 0
  | r+1 => keccak4xRowFuel r + keccak4xRowCount r

theorem keccak4xRowInv_iter (mem : UInt64 → UInt8) (g : Bank16 UInt64)
    (hd : keccak4xDisjoint (g.get 7) 800 (g.get 4) 800)
    (hc : keccak4xDisjoint (g.get 6) 8 (g.get 4) 800)
    (s : X86State) (h : keccak4xRowInv mem g 0 s) (r : Nat) (hr : r ≤ 5) :
    ∃ t, StepsX86 keccak4xProg (keccak4xRowFuel r) s t ∧ keccak4xRowInv mem g r t := by
  induction r with
  | zero => exact ⟨s, StepsX86.zero _, h⟩
  | succ r ih =>
    obtain ⟨t, ht, hi⟩ := ih (by omega)
    obtain ⟨u, hu, hiu⟩ := keccak4xRowInv_step mem g hd hc r (by omega) t hi
    exact ⟨u, StepsX86_trans ht hu, hiu⟩

theorem keccak4xRowFuel_full : keccak4xRowFuel 5 = 102 := by decide +kernel

/-- Every instruction computing one round, stopping before public counter maintenance. -/
theorem keccak4x_round_steps (g : Bank16 UInt64) (y : Bank16 Vec256)
    (cf ofl zf dy : Bool) (mem : UInt64 → UInt8)
    (hd : keccak4xDisjoint (g.get 7) 800 (g.get 4) 800)
    (hc : keccak4xDisjoint (g.get 6) 8 (g.get 4) 800) :
    ∃ t, StepsX86 keccak4xProg 269 ⟨20,g,y,cf,ofl,zf,dy,false,mem⟩ t ∧
      t.pc = 1645 ∧ t.halted = false ∧ t.gpr = g ∧
      t.mem = keccak4xRoundMem mem (g.get 7) (g.get 4) (g.get 6) := by
  obtain ⟨t, ht, hp, hh, hg, hm⟩ := keccak4x_theta_rho_pi_steps g y cf ofl zf dy mem hd
  have hi : keccak4xRowInv mem g 0 t := ⟨hp, hh, hg, hm⟩
  obtain ⟨u, hu, hiu⟩ := keccak4xRowInv_iter mem g hd hc t hi 5 (by decide)
  rw [keccak4xRowFuel_full] at hu
  exact ⟨u, StepsX86_trans ht hu, hiu.pc, hiu.halted, hiu.gpr, hiu.memory⟩

/-- Entry to the decoded round body after the prologue, with honest buffer separation.
The selected public table word may be any UInt64; round selection is handled by the loop. -/
def keccak4xRoundEntry (s : X86State) : Prop :=
  s.pc = 20 ∧ s.halted = false ∧
    keccak4xDisjoint (s.gpr.get 7) 800 (s.gpr.get 4) 800 ∧
    keccak4xDisjoint (s.gpr.get 6) 8 (s.gpr.get 4) 800

/-- Fresh bytes execute one mathematical Keccak round on all 100 interleaved words.
This theorem stops at PC1645, before the three counter-maintenance instructions;
it is a round-body lemma, not the complete 24-round function theorem. -/
theorem keccak4x_current_round (s : X86State) (h : keccak4xRoundEntry s) :
    ∃ slice prog,
      findSliceByNameBytes currentX86ExtractedSlices keccak4xName = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      (runX86 prog 269 s).1.pc = 1645 ∧ (runX86 prog 269 s).1.halted = false ∧
      (runX86 prog 269 s).1.gpr = s.gpr ∧
      (runX86 prog 269 s).1.mem =
        keccak4xRoundMem s.mem (s.gpr.get 7) (s.gpr.get 4) (s.gpr.get 6) ∧
      (∀ q : Nat, q < 4 →
        keccak4xLaneState (keccak4xSource (runX86 prog 269 s).1.mem (s.gpr.get 7)) q =
          roundS (keccak4xLaneState (keccak4xSource s.mem (s.gpr.get 7)) q)
            (readMem64 s.mem (s.gpr.get 6))) := by
  have hd := keccak4x_decoded
  cases hf : findSliceByNameBytes currentX86ExtractedSlices keccak4xName with
  | none => rw [hf] at hd; cases hd
  | some slice =>
    rw [hf] at hd
    refine ⟨slice, keccak4xProg, rfl, hd, ?_⟩
    rcases s with ⟨pc,g,y,cf,ofl,zf,dy,hlt,mem⟩
    rcases h with ⟨hp, hh, hds, hcs⟩
    dsimp only at hp hh
    subst pc hlt
    obtain ⟨t, ht, hp, hh, hg, hm⟩ := keccak4x_round_steps g y cf ofl zf dy mem hds hcs
    have he := (ht.toExecReaches 0).1
    change (runX86 keccak4xProg 269 _).1 = t at he
    rw [he]
    refine ⟨hp, hh, hg, hm, ?_⟩
    intro q hq
    rw [hm]
    exact keccak4xRoundMem_readback mem (g.get 7) (g.get 4) (g.get 6) q hq

theorem keccak4x_round_inhabited : ∃ s : X86State, keccak4xRoundEntry s := by
  refine ⟨⟨20, Bank16.ofFn (fun i => if i == 4 then 1024 else if i == 6 then 2048 else 0),
    Bank16.const Vec256.zero, false, false, false, false, false, fun _ => 0⟩,
    rfl, rfl, ?_, ?_⟩
  · change keccak4xDisjoint 0 800 1024 800
    intro i j hi hj he
    have hn := congrArg UInt64.toNat he
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat, UInt64.toNat_ofNat'] at hn
    omega
  · change keccak4xDisjoint 2048 8 1024 800
    intro i j hi hj he
    have hn := congrArg UInt64.toNat he
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat, UInt64.toNat_ofNat'] at hn
    omega

theorem keccak4x_round_tooth : roundS zeroKState 1 ≠ zeroKState := by decide +kernel

#tooth_pair keccak4x_current_round vs keccak4x_round_tooth
#verify_inhabited keccak4x_current_round keccak4x_round_inhabited

theorem keccak4xScratchPrefix_outside (mem : UInt64 → UInt8) (sp : UInt64)
    (v : Nat → Vec256) (n : Nat) (hn : n ≤ 25) (a : UInt64)
    (ha : ∀ j : Nat, j < 800 → a ≠ sp + UInt64.ofNat j) :
    keccak4xScratchPrefix mem sp v n a = mem a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [keccak4xScratchPrefix, writeMem256_outside]
    · exact ih (by omega)
    · intro k hk he
      have hp := keccak4x_perm_lt n (by omega)
      rw [u64_add_ofNat_assoc sp (32*keccak4xPerm n) k (by omega)] at he
      exact ha (32*keccak4xPerm n+k) (by omega) he

theorem keccak4xStatePrefix_outside (mem : UInt64 → UInt8) (p : UInt64)
    (v : Nat → Vec256) (rc : UInt64) (n : Nat) (hn : n ≤ 25) (a : UInt64)
    (ha : ∀ j : Nat, j < 800 → a ≠ p + UInt64.ofNat j) :
    keccak4xStatePrefix mem p v rc n a = mem a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [keccak4xStatePrefix, writeMem256_outside]
    · exact ih (by omega)
    · intro k hk he
      rw [u64_add_ofNat_assoc p (32*n) k (by omega)] at he
      exact ha (32*n+k) (by omega) he

theorem keccak4xRoundMem_outside (mem : UInt64 → UInt8) (p sp rp a : UInt64)
    (hp : ∀ j : Nat, j < 800 → a ≠ p + UInt64.ofNat j)
    (hs : ∀ j : Nat, j < 800 → a ≠ sp + UInt64.ofNat j) :
    keccak4xRoundMem mem p sp rp a = mem a := by
  unfold keccak4xRoundMem
  rw [keccak4xStatePrefix_outside _ _ _ _ 25 (by decide) a hp,
    keccak4xScratchPrefix_outside _ _ _ 25 (by decide) a hs]

/-- Exact architectural DEC32 result, ZF and OF for the bounded public counters
used by the 24-round loop and the 25-vector scratch wipe. -/
theorem keccak4x_dec32_small (k : Nat) (hk : k < 25) :
    maskGprWidth false (maskGprWidth false (UInt64.ofNat (k + 1)) + (0 - 1)) = UInt64.ofNat k ∧
    (UInt64.ofNat k == 0) = decide (k = 0) ∧
    evalX86IncDecOf false false (UInt64.ofNat (k + 1)) = false := by
  have h : ∀ k : Fin 25,
      maskGprWidth false (maskGprWidth false (UInt64.ofNat (k.val + 1)) + (0 - 1)) = UInt64.ofNat k.val ∧
      (UInt64.ofNat k.val == 0) = decide (k.val = 0) ∧
      evalX86IncDecOf false false (UInt64.ofNat (k.val + 1)) = false := by
    decide +kernel
  exact h ⟨k, hk⟩

theorem keccak4x_control_steps (s : X86State) (k : Nat) (hk : k < 25)
    (hp : s.pc = 1645) (hh : s.halted = false)
    (hc : s.gpr.get 1 = UInt64.ofNat (k + 1)) :
    ∃ t, StepsX86 keccak4xProg 3 s t ∧
      t.pc = (if k = 0 then 1657 else 20) ∧ t.halted = false ∧
      t.gpr = (s.gpr.set 6 (s.gpr.get 6 + 8)).set 1 (UInt64.ofNat k) ∧
      t.mem = s.mem ∧ t.ymm = s.ymm := by
  rcases s with ⟨pc, g, y, cf, ofl, zf, dy, halted, mem⟩
  dsimp only at hp hh hc
  subst pc halted
  obtain ⟨hdec, hzf, hof⟩ := keccak4x_dec32_small k hk
  suffices he : ∃ t, StepsX86 keccak4xProg 3
      ⟨1645,g,y,cf,ofl,zf,dy,false,mem⟩ t ∧
      t.pc = (if k = 0 then 1657 else 20) ∧ t.halted = false ∧
      t.gpr = (g.set 6 (g.get 6 + 8)).set 1 (UInt64.ofNat k) ∧
      t.mem = mem ∧ t.ymm = y by exact he
  apply StepsX86_step_ex rfl rfl
  · simp only [stepX86, ite_true, ite_false, evalX86Alu, maskGprWidth_true,
      uint64_evalAdd_eq]
    rfl
  apply StepsX86_step_ex rfl rfl
  · simp only [stepX86_dec, Bank16.get, Bank16.set] at hc ⊢
    simp only [hc, hdec, hzf, hof]
    rfl
  apply StepsX86_step_ex rfl rfl
  · rw [stepX86_jnz]
  refine ⟨_, StepsX86.zero _, ?_, rfl, rfl, rfl, rfl⟩
  cases k with
  | zero => rfl
  | succ k =>
    simp only [Nat.succ_ne_zero, decide_false, Bool.not_false, jccPc, ite_true, ite_false]
    rfl

/-- The public register invariant. The counter and RC pointer are explicit;
all other registers retain their values from the loop's entry bank. -/
def keccak4xLoopBank (g : Bank16 UInt64) (table : UInt64) (i k : Nat) : Bank16 UInt64 :=
  ⟨g.r0, UInt64.ofNat k, g.r2, g.r3, g.r4, g.r5,
    table + UInt64.ofNat (8*i), g.r7, g.r8, g.r9, g.r10, g.r11, g.r12, g.r13, g.r14, g.r15⟩

theorem keccak4xLoopBank_get1 (g : Bank16 UInt64) (table : UInt64) (i k : Nat) :
    (keccak4xLoopBank g table i k).get 1 = UInt64.ofNat k := by rfl

theorem keccak4xLoopBank_get4 (g : Bank16 UInt64) (table : UInt64) (i k : Nat) :
    (keccak4xLoopBank g table i k).get 4 = g.get 4 := by rfl

theorem keccak4xLoopBank_get6 (g : Bank16 UInt64) (table : UInt64) (i k : Nat) :
    (keccak4xLoopBank g table i k).get 6 = table + UInt64.ofNat (8*i) := by rfl

theorem keccak4xLoopBank_get7 (g : Bank16 UInt64) (table : UInt64) (i k : Nat) :
    (keccak4xLoopBank g table i k).get 7 = g.get 7 := by rfl

def keccak4xCanonicalTable (mem : UInt64 → UInt8) (table : UInt64) : Prop :=
  ∀ j : Nat, j < 24 → readMem64 mem (table + UInt64.ofNat (8*j)) = keccakRoundConstants.getD j 0

/-- Each finite canonical suffix exposes precisely the next round constant. -/
theorem keccak4x_constants_drop (i : Nat) (hi : i < 24) :
    keccakRoundConstants.drop i =
      keccakRoundConstants.getD i 0 :: keccakRoundConstants.drop (i+1) := by
  have h : ∀ i : Fin 24, keccakRoundConstants.drop i.val =
      keccakRoundConstants.getD i.val 0 :: keccakRoundConstants.drop (i.val+1) := by
    decide +kernel
  exact h ⟨i, hi⟩

theorem keccak4x_constants_drop24 : keccakRoundConstants.drop 24 = [] := by decide +kernel

theorem keccak4xLoopBank_advance (g : Bank16 UInt64) (table : UInt64)
    (i k : Nat) (hi : i < 24) :
    ((keccak4xLoopBank g table i (k+1)).set 6
      ((keccak4xLoopBank g table i (k+1)).get 6 + 8)).set 1 (UInt64.ofNat k) =
      keccak4xLoopBank g table (i+1) k := by
  have h8 : UInt64.ofNat 8 = (8 : UInt64) := by decide +kernel
  have hp : (table + UInt64.ofNat (8*i)) + 8 = table + UInt64.ofNat (8*(i+1)) := by
    rw [← h8, u64_add_ofNat_assoc table (8*i) 8 (by omega)]
    congr 1
  simp only [keccak4xLoopBank, Bank16.get, Bank16.set, hp]

/-- The entire public RC table survives a round, not merely the word just read. -/
theorem keccak4xCanonicalTable_after_round (mem : UInt64 → UInt8)
    (p sp table current : UInt64)
    (hp : keccak4xDisjoint table 192 p 800)
    (hs : keccak4xDisjoint table 192 sp 800)
    (ht : keccak4xCanonicalTable mem table) :
    keccak4xCanonicalTable (keccak4xRoundMem mem p sp current) table := by
  intro j hj
  have hb (off : Nat) (hoff : off < 192) :
      keccak4xRoundMem mem p sp current (table + UInt64.ofNat off) =
        mem (table + UInt64.ofNat off) := by
    exact keccak4xRoundMem_outside mem p sp current _
      (fun n hn => hp off n hoff hn) (fun n hn => hs off n hoff hn)
  have hbyte (k : Nat) (hk : k < 8) :
      keccak4xRoundMem mem p sp current ((table + UInt64.ofNat (8*j)) + UInt64.ofNat k) =
        mem ((table + UInt64.ofNat (8*j)) + UInt64.ofNat k) := by
    rw [u64_add_ofNat_assoc table (8*j) k (by omega)]
    exact hb (8*j+k) (by omega)
  have hword : readMem64 (keccak4xRoundMem mem p sp current) (table + UInt64.ofNat (8*j)) =
      readMem64 mem (table + UInt64.ofNat (8*j)) := by
    rw [readMem64_eq_mapBytes64, readMem64_eq_mapBytes64]
    unfold mapBytes64
    simp only [hbyte 0 (by decide), hbyte 1 (by decide), hbyte 2 (by decide), hbyte 3 (by decide),
      hbyte 4 (by decide), hbyte 5 (by decide), hbyte 6 (by decide), hbyte 7 (by decide)]
  exact hword.trans (ht j hj)

/-- Bounded remaining-round induction. A zero remaining count starts at the
post-branch exit PC1657; it never pretends that a zero counter at PC20 executes
zero rounds. Every positive stage executes the decoded 269-instruction round
and all three public counter instructions. -/
theorem keccak4x_loop_steps (k : Nat) :
    ∀ (g : Bank16 UInt64) (table : UInt64) (i : Nat) (s : X86State),
    i + k = 24 → s.pc = (if k = 0 then 1657 else 20) → s.halted = false →
    s.gpr = keccak4xLoopBank g table i k →
    keccak4xDisjoint (g.get 7) 800 (g.get 4) 800 →
    keccak4xDisjoint table 192 (g.get 7) 800 →
    keccak4xDisjoint table 192 (g.get 4) 800 →
    keccak4xCanonicalTable s.mem table →
    ∃ t, StepsX86 keccak4xProg (272*k) s t ∧
      t.pc = 1657 ∧ t.halted = false ∧ t.gpr = keccak4xLoopBank g table 24 0 ∧
      (∀ a : UInt64,
        (∀ j : Nat, j < 800 → a ≠ g.get 7 + UInt64.ofNat j) →
        (∀ j : Nat, j < 800 → a ≠ g.get 4 + UInt64.ofNat j) → t.mem a = s.mem a) ∧
      (∀ q : Nat, q < 4 →
        keccak4xLaneState (keccak4xSource t.mem (g.get 7)) q =
          (keccakRoundConstants.drop i).foldl roundS
            (keccak4xLaneState (keccak4xSource s.mem (g.get 7)) q)) := by
  induction k with
  | zero =>
    intro g table i s hi hp hh hg hd htp hts ht
    have hi24 : i = 24 := by omega
    subst i
    refine ⟨s, StepsX86.zero _, ?_, hh, hg, ?_, ?_⟩
    · simpa only [ite_true] using hp
    · intro a _ _; rfl
    · intro q _
      rw [keccak4x_constants_drop24]
      rfl
  | succ k ih =>
    intro g table i s hcount hp hh hg hd htp hts ht
    have hik : i < 24 := by omega
    have hk : k < 25 := by omega
    have hpc : s.pc = 20 := by simpa only [Nat.succ_ne_zero, ite_false] using hp
    have hrc : keccak4xDisjoint (table + UInt64.ofNat (8*i)) 8 (g.get 4) 800 := by
      intro a b ha hb he
      rw [u64_add_ofNat_assoc table (8*i) a (by omega)] at he
      exact hts (8*i+a) b (by omega) hb he
    have hr : ∃ t, StepsX86 keccak4xProg 269 s t ∧
        t.pc = 1645 ∧ t.halted = false ∧ t.gpr = keccak4xLoopBank g table i (k+1) ∧
        t.mem = keccak4xRoundMem s.mem (g.get 7) (g.get 4) (table + UInt64.ofNat (8*i)) := by
      rcases s with ⟨pc, gs, ys, cf, ofl, zf, dy, halted, mem⟩
      dsimp only at hpc hh hg
      subst pc halted gs
      simpa only [keccak4xLoopBank_get4, keccak4xLoopBank_get6, keccak4xLoopBank_get7] using
        keccak4x_round_steps (keccak4xLoopBank g table i (k+1)) ys cf ofl zf dy mem
          (by simpa only [keccak4xLoopBank_get4, keccak4xLoopBank_get7] using hd)
          (by simpa only [keccak4xLoopBank_get4, keccak4xLoopBank_get6] using hrc)
    obtain ⟨r, hr, hrp, hrh, hrg, hrm⟩ := hr
    obtain ⟨u, hcontrol, hup, huh, hug, hum, _⟩ :=
      keccak4x_control_steps r k hk hrp hrh (by rw [hrg, keccak4xLoopBank_get1])
    have hug' : u.gpr = keccak4xLoopBank g table (i+1) k := by
      rw [hug, hrg, keccak4xLoopBank_advance g table i k hik]
    have hum' : u.mem = keccak4xRoundMem s.mem (g.get 7) (g.get 4)
        (table + UInt64.ofNat (8*i)) := hum.trans hrm
    have hut : keccak4xCanonicalTable u.mem table := by
      rw [hum']
      exact keccak4xCanonicalTable_after_round _ _ _ _ _ htp hts ht
    obtain ⟨t, hloop, htp', hth, htg, hout, hmath⟩ :=
      ih g table (i+1) u (by omega) hup huh hug' hd htp hts hut
    have hsteps := StepsX86_trans (StepsX86_trans hr hcontrol) hloop
    have hlen : 269 + 3 + 272*k = 272*(k+1) := by omega
    rw [hlen] at hsteps
    refine ⟨t, hsteps, htp', hth, htg, ?_, ?_⟩
    · intro a hap has
      rw [hout a hap has, hum']
      exact keccak4xRoundMem_outside _ _ _ _ a hap has
    · intro q hq
      rw [hmath q hq, hum', keccak4xRoundMem_readback _ _ _ _ q hq, ht i hik,
        keccak4x_constants_drop i hik]
      rfl

/-- Exactly the 24 rounds allowed by the kernel ABI: 6,528 decoded instructions
between the prologue and epilogue, computing the full permutation on all four states. -/
theorem keccak4x_loop24_steps (g : Bank16 UInt64) (table : UInt64) (s : X86State)
    (hp : s.pc = 20) (hh : s.halted = false)
    (hg : s.gpr = keccak4xLoopBank g table 0 24)
    (hd : keccak4xDisjoint (g.get 7) 800 (g.get 4) 800)
    (htp : keccak4xDisjoint table 192 (g.get 7) 800)
    (hts : keccak4xDisjoint table 192 (g.get 4) 800)
    (ht : keccak4xCanonicalTable s.mem table) :
    ∃ t, StepsX86 keccak4xProg 6528 s t ∧
      t.pc = 1657 ∧ t.halted = false ∧ t.gpr = keccak4xLoopBank g table 24 0 ∧
      (∀ a : UInt64,
        (∀ j : Nat, j < 800 → a ≠ g.get 7 + UInt64.ofNat j) →
        (∀ j : Nat, j < 800 → a ≠ g.get 4 + UInt64.ofNat j) → t.mem a = s.mem a) ∧
      (∀ q : Nat, q < 4 →
        keccak4xLaneState (keccak4xSource t.mem (g.get 7)) q =
          keccakF1600 (keccak4xLaneState (keccak4xSource s.mem (g.get 7)) q)) := by
  simpa only [List.drop_zero, keccakF1600] using
    keccak4x_loop_steps 24 g table 0 s (by decide) hp hh hg hd htp hts ht

/-- The actual aligned 832-byte frame selected by the five-instruction prologue. -/
def keccak4xStackBase (g : Bank16 UInt64) : UInt64 :=
  ((g.get 4 - 8) &&& 0xffffffffffffffe0) - 832

def keccak4xSavedBp (g : Bank16 UInt64) : UInt64 := g.get 4 - 8

def keccak4xPrologueGpr (g : Bank16 UInt64) : Bank16 UInt64 :=
  ((g.set 4 (keccak4xStackBase g)).set 5 (keccak4xSavedBp g)).set 1 24

def keccak4xPrologueMem (mem : UInt64 → UInt8) (g : Bank16 UInt64) : UInt64 → UInt8 :=
  writeMem64 mem (keccak4xSavedBp g) (g.get 5)

set_option linter.unusedSimpArgs false in
/-- Entry prologue, including the saved caller frame pointer. -/
theorem keccak4x_prologue_steps (g : Bank16 UInt64) (y : Bank16 Vec256)
    (cf ofl zf dy : Bool) (mem : UInt64 → UInt8) :
    ∃ t, StepsX86 keccak4xProg 5 ⟨0,g,y,cf,ofl,zf,dy,false,mem⟩ t ∧
      t.pc = 20 ∧ t.halted = false ∧ t.gpr = keccak4xPrologueGpr g ∧ t.ymm = y ∧
      t.mem = keccak4xPrologueMem mem g := by
  have h24 : maskGprWidth false 24 = 24 := by decide +kernel
  iterate 5
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        simp only [stepX86, evalX86Alu, maskGprWidth_true, h24, uint64_evalSub_eq, ite_true, ite_false,
          Bank16.get, Bank16.set]
      all_goals rfl
  exact ⟨_, StepsX86.zero _, rfl, rfl, rfl, rfl, rfl⟩

private theorem keccak4x_read256_write64_disjoint (mem : UInt64 → UInt8)
    (a b w : UInt64)
    (hd : ∀ i j : Nat, i < 32 → j < 8 → a + UInt64.ofNat i ≠ b + UInt64.ofNat j) :
    readMem256 (writeMem64 mem b w) a = readMem256 mem a := by
  have h (off : Nat) (ho : off ≤ 24) :
      readMem64 (writeMem64 mem b w) (a + UInt64.ofNat off) = readMem64 mem (a + UInt64.ofNat off) := by
    apply readMem64_writeMem64_disjoint
    intro i j hi hj he
    rw [u64_add_ofNat_assoc a off i (by omega)] at he
    exact hd (off+i) j (by omega) hj he
  have h0 := h 0 (by decide)
  have e0 : UInt64.ofNat 0 = (0 : UInt64) := by decide +kernel
  have e8 : UInt64.ofNat 8 = (8 : UInt64) := by decide +kernel
  have e16 : UInt64.ofNat 16 = (16 : UInt64) := by decide +kernel
  have e24 : UInt64.ofNat 24 = (24 : UInt64) := by decide +kernel
  rw [e0, UInt64.add_zero] at h0
  unfold readMem256
  rw [← e8, ← e16, ← e24, h0, h 8 (by decide), h 16 (by decide), h 24 (by decide)]

theorem keccak4xPrologueMem_source (mem : UInt64 → UInt8) (g : Bank16 UInt64)
    (hd : keccak4xDisjoint (g.get 7) 800 (keccak4xSavedBp g) 8)
    (j : Nat) (hj : j < 25) :
    keccak4xSource (keccak4xPrologueMem mem g) (g.get 7) j = keccak4xSource mem (g.get 7) j := by
  rw [keccak4xSource_eq _ _ j hj, keccak4xSource_eq _ _ j hj]
  unfold keccak4xPrologueMem
  apply keccak4x_read256_write64_disjoint
  intro i k hi hk he
  rw [u64_add_ofNat_assoc (g.get 7) (32*j) i (by omega)] at he
  exact hd (32*j+i) k (by omega) hk he

theorem keccak4xPrologueMem_table (mem : UInt64 → UInt8) (g : Bank16 UInt64)
    (hd : keccak4xDisjoint (g.get 6) 192 (keccak4xSavedBp g) 8)
    (j : Nat) (hj : j < 24) :
    readMem64 (keccak4xPrologueMem mem g) (g.get 6 + UInt64.ofNat (8*j)) =
      readMem64 mem (g.get 6 + UInt64.ofNat (8*j)) := by
  unfold keccak4xPrologueMem
  apply readMem64_writeMem64_disjoint
  intro i k hi hk he
  rw [u64_add_ofNat_assoc (g.get 6) (8*j) i (by omega)] at he
  exact hd (8*j+i) k (by omega) hk he


/-- Ascending stores performed by the scratch-wipe loop. -/
def keccak4xWipePrefix (m : UInt64 → UInt8) (sp : UInt64) : Nat → (UInt64 → UInt8)
  | 0 => m
  | n+1 => writeMem256 (keccak4xWipePrefix m sp n)
      (sp + UInt64.ofNat (32*n)) Vec256.zero

theorem keccak4xWipePrefix_outside (m : UInt64 → UInt8) (sp : UInt64)
    (n : Nat) (hn : n ≤ 25) (a : UInt64)
    (ha : ∀ i : Nat, i < 32*n → a ≠ sp + UInt64.ofNat i) :
    keccak4xWipePrefix m sp n a = m a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [keccak4xWipePrefix, writeMem256_outside]
    · exact ih (by omega) (fun i hi => ha i (by omega))
    · intro i hi he
      rw [u64_add_ofNat_assoc sp (32*n) i (by omega)] at he
      exact ha (32*n+i) (by omega) he

theorem keccak4xWipePrefix_saved (m : UInt64 → UInt8) (sp bp : UInt64)
    (hd : keccak4xDisjoint bp 8 sp 800) (n : Nat) (hn : n ≤ 25) :
    readMem64 (keccak4xWipePrefix m sp n) bp = readMem64 m bp := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [keccak4xWipePrefix, keccakChiMpc_readMem64_writeMem256_disjoint]
    · exact ih (by omega)
    · intro i j hi hj he
      rw [u64_add_ofNat_assoc sp (32*n) j (by omega)] at he
      exact hd i (32*n+j) hi (by omega) he

theorem keccak4xWipePrefix_source (m : UInt64 → UInt8) (sp p : UInt64)
    (hd : keccak4xDisjoint p 800 sp 800) (n : Nat) (hn : n ≤ 25)
    (j : Nat) (hj : j < 25) :
    keccak4xSource (keccak4xWipePrefix m sp n) p j = keccak4xSource m p j := by
  rw [keccak4xSource_eq _ _ j hj, keccak4xSource_eq _ _ j hj]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [keccak4xWipePrefix, keccakChiMpc_readMem256_writeMem256_disjoint]
    · exact ih (by omega)
    · intro i k hi hk he
      rw [u64_add_ofNat_assoc p (32*j) i (by omega),
        u64_add_ofNat_assoc sp (32*n) k (by omega)] at he
      exact hd (32*j+i) (32*n+k) (by omega) (by omega) he

set_option linter.unusedSimpArgs false in
theorem keccak4x_epilogue_init (s : X86State) (hp : s.pc = 1657) (hh : s.halted = false) :
    ∃ t, StepsX86 keccak4xProg 3 s t ∧ t.pc = 1669 ∧ t.halted = false ∧
      t.gpr = (s.gpr.set 1 25).set 0 (s.gpr.get 4) ∧
      t.ymm = s.ymm.set 0 Vec256.zero ∧ t.mem = s.mem := by
  rcases s with ⟨pc, ⟨r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15⟩,
    y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh
  subst pc hlt
  have h25 : maskGprWidth false 25 = 25 := by decide +kernel
  iterate 3
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        simp only [stepX86, evalVecBin256, clampVecWidth, ite_true, ite_false,
          u64_xor_self, h25, maskGprWidth_true, Bank16.get, Bank16.set]
      all_goals rfl
  exact ⟨_, StepsX86.zero _, rfl, rfl, rfl, rfl, rfl⟩

set_option linter.unusedSimpArgs false in
theorem keccak4x_wipe_body (s : X86State) (k : Nat) (hk : k < 25)
    (hp : s.pc = 1669) (hh : s.halted = false)
    (hc : s.gpr.get 1 = UInt64.ofNat (k+1)) (hy : s.ymm.get 0 = Vec256.zero) :
    ∃ t, StepsX86 keccak4xProg 4 s t ∧
      t.pc = (if k = 0 then 1681 else 1669) ∧ t.halted = false ∧
      t.gpr = (s.gpr.set 0 (s.gpr.get 0 + 32)).set 1 (UInt64.ofNat k) ∧
      t.ymm = s.ymm ∧ t.mem = writeMem256 s.mem (s.gpr.get 0) Vec256.zero := by
  rcases s with ⟨pc, ⟨r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15⟩,
    y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh
  change r1 = UInt64.ofNat (k+1) at hc
  change y.r0 = Vec256.zero at hy
  subst pc hlt r1
  obtain ⟨hdec,hzf,hof⟩ := keccak4x_dec32_small k hk
  apply StepsX86_step_ex rfl rfl
  · conv =>
      lhs
      simp only [stepX86, evalX86Addr, ite_true, Bank16.get, UInt64.add_zero, hy]
    all_goals rfl
  apply StepsX86_step_ex rfl rfl
  · conv =>
      lhs
      simp only [stepX86_addImm64, Bank16.get, Bank16.set]
    all_goals rfl
  apply StepsX86_step_ex rfl rfl
  · conv =>
      lhs
      simp only [stepX86_dec, Bank16.get, Bank16.set, hdec, hzf, hof]
    all_goals rfl
  apply StepsX86_step_ex rfl rfl
  · conv =>
      lhs
      rw [stepX86_jnz]
    all_goals rfl
  refine ⟨_, StepsX86.zero _, ?_, rfl, rfl, rfl, rfl⟩
  cases k with
  | zero => simp [jccPc]
  | succ k => simp [jccPc]

/-- The scalar ABI result after restoring the caller's stack frame. -/
def keccak4xRestoredGpr (g : Bank16 UInt64) (m : UInt64 → UInt8) : Bank16 UInt64 :=
  ⟨0,0,0,g.get 3,g.get 5 + 8,readMem64 m (g.get 5),0,0,0,0,0,0,
    g.get 12,g.get 13,g.get 14,g.get 15⟩

set_option linter.unusedSimpArgs false in
theorem keccak4x_epilogue_cleanup (s : X86State) (hp : s.pc = 1681) (hh : s.halted = false) :
    ∃ t, StepsX86 keccak4xProg 25 s t ∧ t.pc = 1761 ∧ t.halted = true ∧
      t.gpr = keccak4xRestoredGpr s.gpr s.mem ∧ t.ymm = Bank16.const Vec256.zero ∧
      t.ymmDirty = false ∧ t.mem = s.mem := by
  rcases s with ⟨pc, ⟨r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15⟩,
    y,cf,ofl,zf,dy,hlt,mem⟩
  dsimp only at hp hh
  subst pc hlt
  iterate 11
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        simp only [stepX86, evalVecBin256, clampVecWidth, ite_true, ite_false,
          u64_xor_self, Bank16.get, Bank16.set]
      all_goals rfl
  iterate 2
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        simp only [current_vzeroall_step, current_vzeroupper_zero_step]
      all_goals rfl
  apply StepsX86_step_ex rfl rfl
  · conv =>
      lhs
      simp only [stepX86_movRR, maskGprWidth_true, Bank16.get, Bank16.set]
    all_goals rfl
  apply StepsX86_step_ex rfl rfl
  · conv =>
      lhs
      simp only [stepX86, Bank16.get, Bank16.set]
    all_goals rfl
  iterate 9
    apply StepsX86_step_ex rfl rfl
    · conv =>
        lhs
        simp only [stepX86_xorRR, mask32_xor_self, u64_zero_beq_zero, Bank16.get, Bank16.set]
      all_goals rfl
  apply StepsX86_step_ex rfl rfl rfl
  exact ⟨_, StepsX86.zero _, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Loop invariant after `i` of the fixed 25 scratch-vector stores. -/
def keccak4xWipeInv (s t : X86State) (i : Nat) : Prop :=
  t.pc = (if i < 25 then 1669 else 1681) ∧ t.halted = false ∧
  t.gpr = (s.gpr.set 0 (s.gpr.get 0 + UInt64.ofNat (32*i))).set 1 (UInt64.ofNat (25-i)) ∧
  t.ymm = s.ymm ∧ t.mem = keccak4xWipePrefix s.mem (s.gpr.get 0) i

theorem keccak4x_wipe_advance (s t : X86State) (i : Nat) (hi : i < 25)
    (hy : s.ymm.get 0 = Vec256.zero) (h : keccak4xWipeInv s t i) :
    ∃ u, StepsX86 keccak4xProg 4 t u ∧ keccak4xWipeInv s u (i+1) := by
  have hp : t.pc = 1669 := h.1.trans (ite_eq_left hi)
  have hc : t.gpr.get 1 = UInt64.ofNat ((24-i)+1) := by
    rw [h.2.2.1]
    change UInt64.ofNat (25-i) = UInt64.ofNat ((24-i)+1)
    congr 1
    omega
  have hy' : t.ymm.get 0 = Vec256.zero := by rw [h.2.2.2.1]; exact hy
  obtain ⟨u, hu, hup, huh, hug, huy, hum⟩ :=
    keccak4x_wipe_body t (24-i) (by omega) hp h.2.1 hc hy'
  refine ⟨u, hu, ?_, huh, ?_, huy.trans h.2.2.2.1, ?_⟩
  · rw [hup]
    by_cases he : i+1 < 25
    · rw [ite_eq_right (by omega), ite_eq_left he]
    · rw [ite_eq_left (by omega), ite_eq_right he]
  · rw [hug, h.2.2.1]
    have e32 : UInt64.ofNat 32 = (32 : UInt64) := by decide +kernel
    have ha : (s.gpr.get 0 + UInt64.ofNat (32*i)) + 32 =
        s.gpr.get 0 + UInt64.ofNat (32*(i+1)) := by
      rw [← e32, u64_add_ofNat_assoc _ (32*i) 32 (by omega),
        show 32*i+32 = 32*(i+1) from by omega]
    change (s.gpr.set 0 ((s.gpr.get 0 + UInt64.ofNat (32*i)) + 32)).set 1
        (UInt64.ofNat (24-i)) = _
    rw [ha, show 24-i = 25-(i+1) from by omega]
  · rw [hum, h.2.2.2.2, h.2.2.1]
    rfl

theorem keccak4x_wipe_prefix_steps (s : X86State) (hp : s.pc = 1669)
    (hh : s.halted = false) (hc : s.gpr.get 1 = 25) (hy : s.ymm.get 0 = Vec256.zero)
    (i : Nat) (hi : i ≤ 25) :
    ∃ t, StepsX86 keccak4xProg (4*i) s t ∧ keccak4xWipeInv s t i := by
  induction i with
  | zero =>
    refine ⟨s, StepsX86.zero _, ?_, hh, ?_, rfl, rfl⟩
    · simpa using hp
    · have e0 : UInt64.ofNat 0 = (0 : UInt64) := by decide +kernel
      have e25 : UInt64.ofNat 25 = (25 : UInt64) := by decide +kernel
      have hs0 (g : Bank16 UInt64) : g.set 0 (g.get 0) = g := by cases g; rfl
      have hs1 (g : Bank16 UInt64) : g.set 1 (g.get 1) = g := by cases g; rfl
      change s.gpr = (s.gpr.set 0 (s.gpr.get 0 + UInt64.ofNat 0)).set 1 (UInt64.ofNat 25)
      rw [e0, e25, UInt64.add_zero, hs0, ← hc, hs1]
  | succ i ih =>
    obtain ⟨t, ht, hit⟩ := ih (by omega)
    obtain ⟨u, hu, hiu⟩ := keccak4x_wipe_advance s t i (by omega) hy hit
    refine ⟨u, ?_, hiu⟩
    simpa only [Nat.mul_add, Nat.mul_one] using StepsX86_trans ht hu

/-- The complete epilogue executes the 25-iteration wipe, restores the saved frame,
and executes all vector/scalar cleanup instructions and RET. -/
theorem keccak4x_epilogue_steps (s : X86State) (hp : s.pc = 1657) (hh : s.halted = false)
    (hd : keccak4xDisjoint (s.gpr.get 5) 8 (s.gpr.get 4) 800) :
    ∃ t, StepsX86 keccak4xProg 128 s t ∧ t.pc = 1761 ∧ t.halted = true ∧
      t.gpr = keccak4xRestoredGpr s.gpr s.mem ∧ t.ymm = Bank16.const Vec256.zero ∧
      t.ymmDirty = false ∧ t.mem = keccak4xWipePrefix s.mem (s.gpr.get 4) 25 := by
  obtain ⟨a, ha, hap, hah, hag, hay, ham⟩ := keccak4x_epilogue_init s hp hh
  have hac : a.gpr.get 1 = 25 := by rw [hag]; rfl
  have hay0 : a.ymm.get 0 = Vec256.zero := by rw [hay]; exact Bank16.get_set_eq _ _ _
  obtain ⟨b, hb, hib⟩ := keccak4x_wipe_prefix_steps a hap hah hac hay0 25 (by decide)
  have hbp : b.pc = 1681 := hib.1
  obtain ⟨t, ht, htp, hth, htg, hty, htd, htm⟩ := keccak4x_epilogue_cleanup b hbp hib.2.1
  refine ⟨t, StepsX86_trans (StepsX86_trans ha hb) ht, htp, hth, ?_, hty, htd, ?_⟩
  · rw [htg, hib.2.2.1, hib.2.2.2.2, hag, ham]
    change keccak4xRestoredGpr s.gpr (keccak4xWipePrefix s.mem (s.gpr.get 4) 25) = _
    unfold keccak4xRestoredGpr
    rw [keccak4xWipePrefix_saved _ _ _ hd 25 (by decide)]
  · rw [htm, hib.2.2.2.2, ham, hag]
    rfl

/-- Every byte in the wiped prefix is zero; addresses may wrap modulo 2^64. -/
theorem keccak4xWipePrefix_zero (m : UInt64 → UInt8) (sp : UInt64)
    (n : Nat) (hn : n ≤ 25) (i : Nat) (hi : i < 32*n) :
    keccak4xWipePrefix m sp n (sp + UInt64.ofNat i) = 0 := by
  induction n with
  | zero => exact False.elim (by omega)
  | succ n ih =>
    rw [keccak4xWipePrefix]
    by_cases hlow : i < 32*n
    · rw [writeMem256_outside]
      · exact ih (by omega) hlow
      · intro k hk he
        rw [u64_add_ofNat_assoc sp (32*n) k (by omega)] at he
        have he' := u64_add_ofNat_inj (by omega) (by omega) he
        omega
    · have hrange : i-32*n < 32 := by omega
      have haddr : sp + UInt64.ofNat i =
          (sp + UInt64.ofNat (32*n)) + UInt64.ofNat (i-32*n) := by
        rw [u64_add_ofNat_assoc sp (32*n) (i-32*n) (by omega),
          show 32*n+(i-32*n) = i from by omega]
      rw [haddr, writeMem256_at _ _ _ _ hrange]
      simp [Vec256.zero, getByte64]

theorem keccak4xWipePrefix_states (m : UInt64 → UInt8) (sp p : UInt64)
    (hd : keccak4xDisjoint p 800 sp 800) (q : Nat) :
    keccak4xLaneState (keccak4xSource (keccak4xWipePrefix m sp 25) p) q =
      keccak4xLaneState (keccak4xSource m p) q := by
  apply keccak4xLaneState_congr
  exact fun j hj => keccak4xWipePrefix_source m sp p hd 25 (by decide) j hj

/-- ABI entry conditions: the state, public constants, aligned scratch frame,
and saved frame pointer occupy disjoint byte ranges. -/
structure keccak4xFullEntry (s : X86State) : Prop where
  pc : s.pc = 0
  live : s.halted = false
  stateScratch : keccak4xDisjoint (s.gpr.get 7) 800 (keccak4xStackBase s.gpr) 800
  tableState : keccak4xDisjoint (s.gpr.get 6) 192 (s.gpr.get 7) 800
  tableScratch : keccak4xDisjoint (s.gpr.get 6) 192 (keccak4xStackBase s.gpr) 800
  stateSaved : keccak4xDisjoint (s.gpr.get 7) 800 (keccak4xSavedBp s.gpr) 8
  tableSaved : keccak4xDisjoint (s.gpr.get 6) 192 (keccak4xSavedBp s.gpr) 8
  savedScratch : keccak4xDisjoint (keccak4xSavedBp s.gpr) 8 (keccak4xStackBase s.gpr) 800
  constants : keccak4xCanonicalTable s.mem (s.gpr.get 6)

theorem keccak4x_full_steps (s : X86State) (h : keccak4xFullEntry s) :
    ∃ t, StepsX86 keccak4xProg 6661 s t ∧ t.pc = 1761 ∧ t.halted = true ∧
      t.ymm = Bank16.const Vec256.zero ∧ t.ymmDirty = false ∧
      (∀ q : Nat, q < 4 →
        keccak4xLaneState (keccak4xSource t.mem (s.gpr.get 7)) q =
          keccakF1600 (keccak4xLaneState (keccak4xSource s.mem (s.gpr.get 7)) q)) := by
  rcases s with ⟨pc,g,y,cf,ofl,zf,dy,halted,mem⟩
  have hp := h.pc
  have hh := h.live
  dsimp only at hp hh
  subst pc halted
  obtain ⟨a, ha, hap, hah, hag, hay, ham⟩ := keccak4x_prologue_steps g y cf ofl zf dy mem
  have he : keccak4xPrologueGpr g =
      keccak4xLoopBank (keccak4xPrologueGpr g) (g.get 6) 0 24 := by
    cases g
    simp [keccak4xPrologueGpr, keccak4xLoopBank, Bank16.get, Bank16.set]
  have hat : keccak4xCanonicalTable a.mem (g.get 6) := by
    intro j hj
    rw [ham, keccak4xPrologueMem_table mem g h.tableSaved j hj]
    exact h.constants j hj
  obtain ⟨b, hb, hbp, hbh, hbg, hbm, hbf⟩ :=
    keccak4x_loop24_steps (keccak4xPrologueGpr g) (g.get 6) a hap hah
      (hag.trans he) h.stateScratch h.tableState h.tableScratch hat
  have hbd : keccak4xDisjoint (b.gpr.get 5) 8 (b.gpr.get 4) 800 := by
    rw [hbg]
    exact h.savedScratch
  obtain ⟨t, ht, htp, hth, htg, hty, htd, htm⟩ := keccak4x_epilogue_steps b hbp hbh hbd
  refine ⟨t, StepsX86_trans (StepsX86_trans ha hb) ht, htp, hth, hty, htd, ?_⟩
  intro q hq
  rw [htm, hbg]
  change keccak4xLaneState (keccak4xSource
    (keccak4xWipePrefix b.mem (keccak4xStackBase g) 25) (g.get 7)) q = _
  rw [keccak4xWipePrefix_states _ _ _ h.stateScratch q]
  have hf := hbf q hq
  change keccak4xLaneState (keccak4xSource b.mem (g.get 7)) q =
    keccakF1600 (keccak4xLaneState (keccak4xSource a.mem (g.get 7)) q) at hf
  rw [hf, ham]
  congr 1
  apply keccak4xLaneState_congr
  exact fun j hj => keccak4xPrologueMem_source mem g h.stateSaved j hj

/-- The fresh 309-instruction symbol executes all 24 rounds on each of its four
interleaved 25-lane states, then wipes its vector scratch and returns. -/
theorem current_rlib_keccak_f1600_avx2_4x_functional (s : X86State)
    (h : keccak4xFullEntry s) :
    ∃ slice prog,
      findSliceByNameBytes currentX86ExtractedSlices keccak4xName = some slice ∧
      decodeX86Stream slice.code = some prog ∧
      (runX86 prog 6661 s).1.pc = 1761 ∧ (runX86 prog 6661 s).1.halted = true ∧
      (runX86 prog 6661 s).1.ymm = Bank16.const Vec256.zero ∧
      (runX86 prog 6661 s).1.ymmDirty = false ∧
      (∀ q : Nat, q < 4 →
        keccak4xLaneState (keccak4xSource (runX86 prog 6661 s).1.mem (s.gpr.get 7)) q =
          keccakF1600 (keccak4xLaneState (keccak4xSource s.mem (s.gpr.get 7)) q)) := by
  have hd := keccak4x_decoded
  cases hf : findSliceByNameBytes currentX86ExtractedSlices keccak4xName with
  | none => rw [hf] at hd; cases hd
  | some slice =>
    rw [hf] at hd
    refine ⟨slice, keccak4xProg, rfl, hd, ?_⟩
    obtain ⟨t, ht, hp, hh, hy, hdy, hout⟩ := keccak4x_full_steps s h
    have he := (ht.toExecReaches 0).1
    change (runX86 keccak4xProg 6661 s).1 = t at he
    rw [he]
    exact ⟨hp, hh, hy, hdy, hout⟩

/-- A concrete public constant table, independent of all state bytes. -/
def keccak4xWitnessMem (a : UInt64) : UInt8 :=
  if a.toNat < 192 then
    getByte64 (keccakRoundConstants.getD (a.toNat / 8) 0) (a.toNat % 8)
  else 0

theorem keccak4xWitnessMem_table : keccak4xCanonicalTable keccak4xWitnessMem 0 := by
  have hf : ∀ j : Fin 24,
      readMem64 keccak4xWitnessMem (0 + UInt64.ofNat (8*j.val)) =
        keccakRoundConstants.getD j.val 0 := by decide +kernel
  exact fun j hj => hf ⟨j,hj⟩

theorem keccak4x_full_inhabited : ∃ s : X86State, keccak4xFullEntry s := by
  refine ⟨⟨0, Bank16.ofFn (fun i => if i == 4 then 4096 else if i == 7 then 1024 else 0),
    Bank16.const Vec256.zero, false, false, false, false, false, keccak4xWitnessMem⟩,
    rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change keccak4xDisjoint 1024 800 3232 800
    intro i j hi hj he
    have hn := congrArg UInt64.toNat he
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat, UInt64.toNat_ofNat'] at hn
    omega
  · change keccak4xDisjoint 0 192 1024 800
    intro i j hi hj he
    have hn := congrArg UInt64.toNat he
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat, UInt64.toNat_ofNat'] at hn
    omega
  · change keccak4xDisjoint 0 192 3232 800
    intro i j hi hj he
    have hn := congrArg UInt64.toNat he
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat, UInt64.toNat_ofNat'] at hn
    omega
  · change keccak4xDisjoint 1024 800 4088 8
    intro i j hi hj he
    have hn := congrArg UInt64.toNat he
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat, UInt64.toNat_ofNat'] at hn
    omega
  · change keccak4xDisjoint 0 192 4088 8
    intro i j hi hj he
    have hn := congrArg UInt64.toNat he
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat, UInt64.toNat_ofNat'] at hn
    omega
  · change keccak4xDisjoint 4088 8 3232 800
    intro i j hi hj he
    have hn := congrArg UInt64.toNat he
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat, UInt64.toNat_ofNat'] at hn
    omega
  · exact keccak4xWitnessMem_table

theorem keccak4x_full_tooth : keccakF1600 zeroKState ≠ zeroKState := by decide +kernel

#tooth_pair current_rlib_keccak_f1600_avx2_4x_functional vs keccak4x_full_tooth
#verify_inhabited current_rlib_keccak_f1600_avx2_4x_functional keccak4x_full_inhabited

end Keccak4xFreshVerification

section Gf128KernelEquivalence

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
      ⟨211, {g with r0 := 0},
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
  have h := (StepsX86_trans (StepsX86_trans he hl) hx).toExecReaches extra
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
  simp only [gf128Words, BitVec.getLsbD_append, UInt64.toBitVec_xor, BitVec.getLsbD_xor]
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
  | zero => change gf128Reduce 0 = 0; decide +kernel
  | succ n ih =>
    simp only [gf128PclmulPolySum, gf128PclmulFieldSum, gf128Reduce_xor, ih, gf128FieldMul]

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
    evalVecBin256, evalVecShift256, clampVecWidth, gf128WordReduce,
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
    simp [gf128PclmulRaw, gf128PclmulInitVec, Vec256.zero, gf128Words]
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
    gf128PclmulFieldSum 1 gf128PclmulWitnessState.mem 4096 8192 ≠ 0 := by
  decide +kernel

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
      ⟨241, {g with r0 := 0},
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
  have h := (StepsX86_trans (StepsX86_trans he hl) hx).toExecReaches extra
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
  simp only [gf128VpclmulRawWords, gf128Words, BitVec.getLsbD_append,
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
  | zero => change gf128Reduce 0 = 0; decide +kernel
  | succ n ih =>
    simp only [gf128VpclmulPolySum, gf128VpclmulFieldSum, gf128Reduce_xor, ih, gf128FieldMul]

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
      gf128PclmulXor, evalVecBin256, evalVecShift256, clampVecWidth, Vec256.zero, gf128Words]
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
    gf128VpclmulFieldSum 1 gf128PclmulWitnessState.mem 4096 8192 ≠ 0 := by
  decide +kernel

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

def gf128BdozExitObs (outPtr : UInt64) : List StepObs :=
  [⟨83, [], true⟩, ⟨88, [], true⟩, ⟨93, [], true⟩, ⟨98, [], true⟩, ⟨104, [], true⟩,
   ⟨109, [], true⟩, ⟨114, [], true⟩, ⟨118, [], true⟩, ⟨122, [], true⟩, ⟨128, [], true⟩,
   ⟨132, [(outPtr, 32)], true⟩, ⟨136, [], true⟩, ⟨140, [], true⟩, ⟨144, [], true⟩,
   ⟨148, [], true⟩, ⟨152, [], true⟩, ⟨156, [], true⟩, ⟨160, [], true⟩, ⟨164, [], true⟩,
   ⟨168, [], true⟩, ⟨173, [], true⟩, ⟨175, [], true⟩, ⟨178, [], true⟩, ⟨181, [], true⟩, ⟨183, [], true⟩, ⟨185, [], true⟩, ⟨187, [], true⟩, ⟨189, [], true⟩, ⟨192, [], true⟩, ⟨195, [], true⟩, ⟨198, [], true⟩, ⟨201, [], true⟩, ⟨203, [], true⟩]

def gf128BdozAsmFfiRun (n : Word) (baseL baseR outP : UInt64) (mem : UInt64 → UInt8) :
    AsmFfiBdozMac × List StepObs :=
  if n = 0 then
    (⟨baseL, baseR, outP, Vec256.zero, Vec256.zero, 0, mem⟩,
     [⟨0, [], true⟩])
  else
    let loop := runCuts asmFfiVpclmulBodyStep n.toNat ⟨baseL, baseR, outP, Vec256.zero, Vec256.zero, n.toNat, mem⟩
    let red := poly87Reduce256 loop.1.accLo loop.1.accHi
    ({ loop.1 with mem := writeMem256 mem outP red },
     vpclmulEntryObs ++ loop.2 ++ gf128BdozExitObs outP)

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
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vbinOp256, b16get_1, vpxor_self, b16set_1, vpclmulEntryObs]
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
  simp only [stepX86Full_jnz, vpclmulBodyStep, vpclmulBodyObs,
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
      (⟨203, ⟨0, 0, 0, r3, r4, r5, 0, 0, 0, 0, 0, 0, r12, r13, r14, r15⟩,
        ⟨Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero⟩,
        false, false, true, false, true, writeMem256 m outP (poly87Reduce256 lo hi)⟩,
       gf128BdozExitObs outP) := by
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
  simp only [stepX86Full_ret, poly87Reduce256, gf128BdozExitObs]
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
  | zero => intro v a m fuel _ _; simp [runCuts]
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
    simp [runCuts, List.append_assoc]

def gf128BdozFreshCert (fetch : Nat → Option (DecodedInstr X86Instr))
    (hf : ∀ d ∈ gf128BdozFreshProg, fetch d.offset = some d)
    (s₀ : X86State) (fuel : Nat) (hpc : s₀.pc = 0) (hh : s₀.halted = false)
    (n : Word) (hcount : s₀.gpr.get 1 = UInt64.ofBitVec n)
    (hfuel : 17 * n.toNat + 35 ≤ fuel) :
    UnrestrictedLoopCert X86State AsmFfiBdozMac n
      (vpclmulGuardedRun fetch fuel)
      (fun m => gf128BdozAsmFfiRun n m.lhsPtr m.rhsPtr m.outPtr m.mem)
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
  exitSchedule := gf128BdozExitObs (s₀.gpr.get 7)
  zero_cut := by
    intro hz; subst hz
    have hg0 : (s₀.gpr.get 1 == 0) = true := by simp [hcount]
    dsimp only [vpclmulGuardedRun, gf128BdozAsmFfiRun]
    rw [ite_eq_left hg0, ite_eq_left rfl]
    obtain ⟨_, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, _, _, _, _, _, _, _⟩ := s₀
    have hr1 : r1 = 0 := hcount
    refine ⟨⟨rfl, rfl, rfl, rfl, hr1, rfl, fun h => absurd rfl h, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      vpclmulExpected_field 0 (fun _ => 0) 0 0⟩, rfl, rfl⟩
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
    refine ⟨?_, by simp [List.append_assoc, b16get_7], rfl⟩
    refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, vpclmulExpected_field n m r6 r2⟩
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
      ⟨329, {g with r0 := 0, r1 := 0, r2 := 0, r6 := 0, r7 := 0, r8 := 0, r9 := 0, r10 := 0, r11 := 0},
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
  have h := (StepsX86_trans (StepsX86_trans he hl) hx).toExecReaches extra
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
  simp only [gf128Words, BitVec.getLsbD_append, UInt64.toBitVec_xor, BitVec.getLsbD_xor]
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
  | zero => change gf128Reduce 0 = 0; decide +kernel
  | succ n ih =>
    simp only [gf128BdozPclmulPolySum, gf128BdozPclmulFieldSum, gf128Reduce_xor, ih, gf128FieldMul]

private theorem gf128BdozPclmul_output_reduce (lo hi : Vec256) :
    gf128Words (gf128BdozPclmulReduce lo hi).w0 (gf128BdozPclmulReduce lo hi).w1 =
      gf128Reduce (gf128BdozPclmulPair lo hi) := by
  unfold gf128BdozPclmulPair
  rw [← gf128WordReduce_eq_reduce]
  simp [gf128BdozPclmulReduce, gf128BdozPclmulLift, gf128BdozPclmulXor,
    gf128BdozPclmulShiftL, gf128BdozPclmulShiftR, gf128WordReduce,
    clampVecWidth, evalVecBin256, evalVecShift256, UInt64.xor_comm]

private theorem gf128BdozPclmul_output_field (n : Nat) (m : UInt64 → UInt8)
    (pL pR : UInt64) (y : Bank16 Vec256) (lane : Bool) :
    let z := gf128BdozPclmulIterVec n m pL pR (gf128BdozPclmulInitVec y)
    let output := if lane then gf128BdozPclmulReduce z.r2 z.r3 else gf128BdozPclmulReduce z.r0 z.r1
    gf128Words output.w0 output.w1 = gf128BdozPclmulFieldSum n m pL pR lane := by
  have hraw := gf128BdozPclmul_iter_polynomial n m pL pR (gf128BdozPclmulInitVec y) lane
  have hz : gf128BdozPclmulRaw (gf128BdozPclmulInitVec y) lane = 0 := by
    cases lane <;> change (gf128Words 0 0 ++ gf128Words 0 0) = (0 : BitVec 256) <;> decide +kernel
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
    gf128BdozPclmulFieldSum 1 gf128BdozPclmulWitnessState.mem 4096 8192 false ≠ 0 := by
  decide +kernel

#tooth_pair current_rlib_tower128_bdoz_mac_pclmul_functional vs gf128BdozPclmul_zero_spec_tooth
#verify_inhabited current_rlib_tower128_bdoz_mac_pclmul_functional gf128BdozPclmul_inhabited

end Gf128BdozPclmulKernel

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
  have hz : (gf128Words 0 0).setWidth 256 = 0 := by decide +kernel
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
    simp only [gf128ArmFieldSum, gf128FieldMul, BitVec.xor_assoc]

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
  rw [gf128ArmProductPoly_words]
  exact gf128WordReduce_eq_reduce lo.w0 (lo.w1 ^^^ (mid.w0 ^^^ lo.w0 ^^^ hi.w0))
    (hi.w0 ^^^ (mid.w1 ^^^ lo.w1 ^^^ hi.w1)) hi.w1

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
        have hz : gf128Reduce 0 = 0 := by decide +kernel
        rw [hz]
        simp only [BitVec.ofNat_eq_ofNat, BitVec.zero_xor, BitVec.xor_comm]


/-- A specification that discards the input product is refuted by 1·1. -/
theorem gf128_pmull_discard_product_tooth :
    gf128ArmFieldSum 1 (fun a => if a == 0 then 1 else 0) 0 0 ≠ 0 := by
  decide +kernel

theorem gf128_pmull_functional_witness :
    ∃ (n : Nat) (s : Arm64State),
      0 < n ∧ n < 2^64 ∧ s.pc = 0 ∧ s.halted = false ∧
      s.gpr.get 3 = UInt64.ofNat n ∧
      gf128ArmFieldSum n s.mem (s.gpr.get 1) (s.gpr.get 2) = 0 := by
  refine ⟨1, ⟨0, (Bank32.const 0).set 3 1, Bank32.const Vec128.zero,
    false, false, false, false, fun _ => 0⟩, ?_⟩
  decide +kernel

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

theorem gf128BdozPmull_current_decode :
    (findSliceByNameBytes currentAarch64ExtractedSlices gf128BdozPmullName).map
      (fun s => decodeArm64Stream s.code) = some (some gf128BdozPmullProg) := by
  decide +kernel

def gf128ArmBdozLo (a b : Vec128) : Vec128 :=
  let p := clmul64 a.w0 b.w0
  let c := gf128ArmXor (clmul64 a.w0 b.w1) (clmul64 a.w1 b.w0)
  ⟨p.w0, p.w1 ^^^ c.w0⟩

def gf128ArmBdozHi (a b : Vec128) : Vec128 :=
  let p := clmul64 a.w1 b.w1
  let c := gf128ArmXor (clmul64 a.w0 b.w1) (clmul64 a.w1 b.w0)
  ⟨p.w0 ^^^ c.w1, p.w1⟩

/-- The four-product polynomial represented by one accumulator pair. -/
def gf128ArmBdozPoly (lo hi : Vec128) : BitVec 256 :=
  gf128Words hi.w0 hi.w1 ++ gf128Words lo.w0 lo.w1

private theorem gf128ArmBdozPoly_xor (lo hi l h : Vec128) :
    gf128ArmBdozPoly (gf128ArmXor lo l) (gf128ArmXor hi h) =
      gf128ArmBdozPoly lo hi ^^^ gf128ArmBdozPoly l h := by
  simp only [gf128ArmBdozPoly, gf128ArmXor, gf128Words_xor]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_xor]
  split <;> rfl

private theorem gf128ArmBdozPoly_mul (a b : Vec128) :
    gf128ArmBdozPoly (gf128ArmBdozLo a b) (gf128ArmBdozHi a b) =
      gf128PolyMul ((gf128Words a.w0 a.w1).setWidth 256) (gf128Words b.w0 b.w1) := by
  simpa only [gf128ArmBdozPoly, gf128ArmBdozLo, gf128ArmBdozHi, gf128ArmXor,
    UInt64.xor_assoc] using gf128_clmul_four_words a.w0 a.w1 b.w0 b.w1

/-- One lane's fourteen-instruction register update. -/
def gf128ArmBdozLaneVec (v : Bank32 Vec128) (a b : Vec128) (rLo rHi : Nat) : Bank32 Vec128 :=
  let p := clmul64 a.w0 b.w0
  let q := clmul64 a.w1 b.w1
  let cross0 := clmul64 a.w0 b.w1
  let cross1 := clmul64 a.w1 b.w0
  let mid := gf128ArmXor cross0 cross1
  let l := gf128ArmBdozLo a b
  let h := gf128ArmBdozHi a b
  let v := ((((v.set 4 a).set 5 b).set 6 p).set 7 q).set 16 ⟨b.w1, b.w0⟩
  let v := (((v.set 17 cross0).set 18 cross1).set 17 mid).set 19 ⟨0, mid.w0⟩
  let v := ((v.set 20 ⟨mid.w1, 0⟩).set 6 l).set 7 h
  (v.set rLo (gf128ArmXor (v.get rLo) l)).set rHi (gf128ArmXor (v.get rHi) h)

def gf128ArmBdozBodyVec (v : Bank32 Vec128) (mem : UInt64 → UInt8) (pL pR : UInt64) : Bank32 Vec128 :=
  let v := gf128ArmBdozLaneVec v (readMem128 mem pL) (readMem128 mem pR) 0 1
  gf128ArmBdozLaneVec v (readMem128 mem (pL+16)) (readMem128 mem (pR+16)) 2 3

def gf128ArmBdozIterVec : Nat → (UInt64 → UInt8) → UInt64 → UInt64 → Bank32 Vec128 → Bank32 Vec128
  | 0, _, _, _, v => v
  | n+1, mem, pL, pR, v => gf128ArmBdozIterVec n mem (pL+32) (pR+32)
      (gf128ArmBdozBodyVec v mem pL pR)

/-- XOR of one fixed 128-bit lane from each 32-byte input block. -/
def gf128ArmBdozFieldSum (laneOff : UInt64) : Nat → (UInt64 → UInt8) → UInt64 → UInt64 → BitVec 128
  | 0, _, _, _ => 0
  | n+1, mem, pL, pR =>
    let a := readMem128 mem (pL+laneOff)
    let b := readMem128 mem (pR+laneOff)
    gf128FieldMul (gf128Words a.w0 a.w1) (gf128Words b.w0 b.w1) ^^^
      gf128ArmBdozFieldSum laneOff n mem (pL+32) (pR+32)

section Gf128BdozArmProof
-- Shared instruction-normalization lists intentionally cover multiple opcodes.
set_option linter.unusedSimpArgs false

private theorem gf128BdozArm_lane0_reaches
    (g : Bank32 UInt64) (v : Bank32 Vec128) (cf zf dit : Bool) (m : UInt64 → UInt8)
    (hv : v.get 22 = Vec128.zero) :
    ExecReachesArm64 gf128BdozPmullProg 14
      ⟨20, g, v, cf, zf, dit, false, m⟩
      ⟨76, g, gf128ArmBdozLaneVec v (readMem128 m (g.get 1))
        (readMem128 m (g.get 2)) 0 1, cf, zf, dit, false, m⟩ := by
  apply StepsArm64.toExecReaches
  iterate 4
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [stepArm64, getArmGpr, Nat.reduceBEq,
        Bool.false_eq_true, eq_self, ite_false, ite_true, u64_add_zero,
        Bank32.get_set_eq, Bank32.get_set_ne, UInt64.xor_zero, UInt64.zero_xor] <;> rfl
  iterate 1
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [gf128Arm_ext8, Bank32.get_set_eq,
        Bank32.get_set_ne, hv, Vec128.zero] <;> rfl
  iterate 3
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [stepArm64, getArmGpr, Nat.reduceBEq,
        Bool.false_eq_true, eq_self, ite_false, ite_true, u64_add_zero,
        Bank32.get_set_eq, Bank32.get_set_ne, UInt64.xor_zero, UInt64.zero_xor] <;> rfl
  iterate 2
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [gf128Arm_ext8, Bank32.get_set_eq,
        Bank32.get_set_ne, hv, Vec128.zero] <;> rfl
  iterate 4
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [stepArm64, getArmGpr, Nat.reduceBEq,
        Bool.false_eq_true, eq_self, ite_false, ite_true, u64_add_zero,
        Bank32.get_set_eq, Bank32.get_set_ne, UInt64.xor_zero, UInt64.zero_xor] <;> rfl
  unfold gf128ArmBdozLaneVec gf128ArmBdozLo gf128ArmBdozHi gf128ArmXor
  simp (disch := decide) only [Bank32.get_set_eq, Bank32.get_set_ne,
    UInt64.xor_zero, UInt64.zero_xor]
  exact StepsArm64.zero _

private theorem gf128BdozArm_lane1_reaches
    (g : Bank32 UInt64) (v : Bank32 Vec128) (cf zf dit : Bool) (m : UInt64 → UInt8)
    (hv : v.get 22 = Vec128.zero) :
    ExecReachesArm64 gf128BdozPmullProg 14
      ⟨76, g, v, cf, zf, dit, false, m⟩
      ⟨132, g, gf128ArmBdozLaneVec v (readMem128 m (g.get 1+16))
        (readMem128 m (g.get 2+16)) 2 3, cf, zf, dit, false, m⟩ := by
  apply StepsArm64.toExecReaches
  iterate 4
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [stepArm64, getArmGpr, Nat.reduceBEq,
        Bool.false_eq_true, eq_self, ite_false, ite_true, u64_add_zero,
        Bank32.get_set_eq, Bank32.get_set_ne, UInt64.xor_zero, UInt64.zero_xor] <;> rfl
  iterate 1
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [gf128Arm_ext8, Bank32.get_set_eq,
        Bank32.get_set_ne, hv, Vec128.zero] <;> rfl
  iterate 3
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [stepArm64, getArmGpr, Nat.reduceBEq,
        Bool.false_eq_true, eq_self, ite_false, ite_true, u64_add_zero,
        Bank32.get_set_eq, Bank32.get_set_ne, UInt64.xor_zero, UInt64.zero_xor] <;> rfl
  iterate 2
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [gf128Arm_ext8, Bank32.get_set_eq,
        Bank32.get_set_ne, hv, Vec128.zero] <;> rfl
  iterate 4
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [stepArm64, getArmGpr, Nat.reduceBEq,
        Bool.false_eq_true, eq_self, ite_false, ite_true, u64_add_zero,
        Bank32.get_set_eq, Bank32.get_set_ne, UInt64.xor_zero, UInt64.zero_xor] <;> rfl
  unfold gf128ArmBdozLaneVec gf128ArmBdozLo gf128ArmBdozHi gf128ArmXor
  simp (disch := decide) only [Bank32.get_set_eq, Bank32.get_set_ne,
    UInt64.xor_zero, UInt64.zero_xor]
  exact StepsArm64.zero _

private theorem gf128BdozArm_control_reaches
    (g : Bank32 UInt64) (v : Bank32 Vec128) (cf zf dit : Bool) (m : UInt64 → UInt8) :
    ExecReachesArm64 gf128BdozPmullProg 4
      ⟨132, g, v, cf, zf, dit, false, m⟩
      ⟨if (g.get 3 - 1) == 0 then 148 else 20,
        ((g.set 1 (g.get 1+32)).set 2 (g.get 2+32)).set 3 (g.get 3-1), v,
        decide ((g.get 3).toNat ≥ 1), (g.get 3-1) == 0, dit, false, m⟩ := by
  apply StepsArm64.toExecReaches
  iterate 2
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [gf128Arm_addImm, getArmGpr, setArmGpr,
        Nat.reduceBEq, Bool.false_eq_true, eq_self, ite_false, ite_true,
        Bank32.get_set_ne] <;> rfl
  apply StepsArm64.cons rfl rfl
  · simp (disch := decide) only [gf128Arm_subsImm, getArmGpr, setArmGpr,
      Nat.reduceBEq, Bool.false_eq_true, eq_self, ite_false, ite_true,
      Bank32.get_set_ne] <;> rfl
  apply StepsArm64.cons rfl rfl
  · rw [gf128Arm_bne _ _ _ (by decide)]
  exact StepsArm64.zero _

private theorem gf128BdozArm_lane_keep22 (v : Bank32 Vec128) (a b : Vec128)
    (rLo rHi : Nat) (hLo : rLo < 4) (hHi : rHi < 4) :
    (gf128ArmBdozLaneVec v a b rLo rHi).get 22 = v.get 22 := by
  simp (disch := omega) only [gf128ArmBdozLaneVec, Bank32.get_set_ne]

private theorem gf128BdozArm_body_reaches
    (g : Bank32 UInt64) (v : Bank32 Vec128) (cf zf dit : Bool) (m : UInt64 → UInt8)
    (hv : v.get 22 = Vec128.zero) :
    ExecReachesArm64 gf128BdozPmullProg 32
      ⟨20, g, v, cf, zf, dit, false, m⟩
      ⟨if (g.get 3 - 1) == 0 then 148 else 20,
        ((g.set 1 (g.get 1+32)).set 2 (g.get 2+32)).set 3 (g.get 3-1),
        gf128ArmBdozBodyVec v m (g.get 1) (g.get 2),
        decide ((g.get 3).toNat ≥ 1), (g.get 3-1) == 0, dit, false, m⟩ := by
  have h0 := gf128BdozArm_lane0_reaches g v cf zf dit m hv
  have hv' : (gf128ArmBdozLaneVec v (readMem128 m (g.get 1))
      (readMem128 m (g.get 2)) 0 1).get 22 = Vec128.zero := by
    rw [gf128BdozArm_lane_keep22 _ _ _ _ _ (by decide) (by decide), hv]
  have h1 := gf128BdozArm_lane1_reaches g _ cf zf dit m hv'
  exact ExecReachesArm64_trans h0 (ExecReachesArm64_trans h1
    (gf128BdozArm_control_reaches g _ cf zf dit m))

private theorem gf128BdozArm_body_keep22 (v : Bank32 Vec128) (m : UInt64 → UInt8) (pL pR : UInt64) :
    (gf128ArmBdozBodyVec v m pL pR).get 22 = v.get 22 := by
  unfold gf128ArmBdozBodyVec
  rw [gf128BdozArm_lane_keep22 _ _ _ _ _ (by decide) (by decide),
    gf128BdozArm_lane_keep22 _ _ _ _ _ (by decide) (by decide)]

private theorem gf128BdozArm_iter_keep22 (n : Nat) (m : UInt64 → UInt8)
    (pL pR : UInt64) (v : Bank32 Vec128) :
    (gf128ArmBdozIterVec n m pL pR v).get 22 = v.get 22 := by
  induction n generalizing pL pR v with
  | zero => rfl
  | succ n ih => rw [gf128ArmBdozIterVec, ih, gf128BdozArm_body_keep22]

private theorem gf128BdozArm_body_get0 (v : Bank32 Vec128) (m : UInt64 → UInt8) (pL pR : UInt64) :
    (gf128ArmBdozBodyVec v m pL pR).get 0 =
      gf128ArmXor (v.get 0) (gf128ArmBdozLo
        (readMem128 m (pL+0)) (readMem128 m (pR+0))) := by
  simp (disch := decide) only [gf128ArmBdozBodyVec, gf128ArmBdozLaneVec,
    Bank32.get_set_eq, Bank32.get_set_ne, UInt64.add_zero]

private theorem gf128BdozArm_body_get1 (v : Bank32 Vec128) (m : UInt64 → UInt8) (pL pR : UInt64) :
    (gf128ArmBdozBodyVec v m pL pR).get 1 =
      gf128ArmXor (v.get 1) (gf128ArmBdozHi
        (readMem128 m (pL+0)) (readMem128 m (pR+0))) := by
  simp (disch := decide) only [gf128ArmBdozBodyVec, gf128ArmBdozLaneVec,
    Bank32.get_set_eq, Bank32.get_set_ne, UInt64.add_zero]

private theorem gf128BdozArm_body_get2 (v : Bank32 Vec128) (m : UInt64 → UInt8) (pL pR : UInt64) :
    (gf128ArmBdozBodyVec v m pL pR).get 2 =
      gf128ArmXor (v.get 2) (gf128ArmBdozLo
        (readMem128 m (pL+16)) (readMem128 m (pR+16))) := by
  simp (disch := decide) only [gf128ArmBdozBodyVec, gf128ArmBdozLaneVec,
    Bank32.get_set_eq, Bank32.get_set_ne, UInt64.add_zero]

private theorem gf128BdozArm_body_get3 (v : Bank32 Vec128) (m : UInt64 → UInt8) (pL pR : UInt64) :
    (gf128ArmBdozBodyVec v m pL pR).get 3 =
      gf128ArmXor (v.get 3) (gf128ArmBdozHi
        (readMem128 m (pL+16)) (readMem128 m (pR+16))) := by
  simp (disch := decide) only [gf128ArmBdozBodyVec, gf128ArmBdozLaneVec,
    Bank32.get_set_eq, Bank32.get_set_ne, UInt64.add_zero]

private theorem gf128BdozArm_iter_field0 (n : Nat) (m : UInt64 → UInt8)
    (pL pR : UInt64) (v : Bank32 Vec128) :
    gf128Reduce (gf128ArmBdozPoly ((gf128ArmBdozIterVec n m pL pR v).get 0)
      ((gf128ArmBdozIterVec n m pL pR v).get 1)) =
      gf128Reduce (gf128ArmBdozPoly (v.get 0) (v.get 1)) ^^^
        gf128ArmBdozFieldSum 0 n m pL pR := by
  induction n generalizing pL pR v with
  | zero => simp [gf128ArmBdozIterVec, gf128ArmBdozFieldSum]
  | succ n ih =>
    rw [gf128ArmBdozIterVec, ih, gf128BdozArm_body_get0, gf128BdozArm_body_get1,
      gf128ArmBdozPoly_xor, gf128Reduce_xor, gf128ArmBdozPoly_mul]
    simp only [gf128ArmBdozFieldSum, gf128FieldMul, BitVec.xor_assoc]

private theorem gf128BdozArm_iter_field1 (n : Nat) (m : UInt64 → UInt8)
    (pL pR : UInt64) (v : Bank32 Vec128) :
    gf128Reduce (gf128ArmBdozPoly ((gf128ArmBdozIterVec n m pL pR v).get 2)
      ((gf128ArmBdozIterVec n m pL pR v).get 3)) =
      gf128Reduce (gf128ArmBdozPoly (v.get 2) (v.get 3)) ^^^
        gf128ArmBdozFieldSum 16 n m pL pR := by
  induction n generalizing pL pR v with
  | zero => simp [gf128ArmBdozIterVec, gf128ArmBdozFieldSum]
  | succ n ih =>
    rw [gf128ArmBdozIterVec, ih, gf128BdozArm_body_get2, gf128BdozArm_body_get3,
      gf128ArmBdozPoly_xor, gf128Reduce_xor, gf128ArmBdozPoly_mul]
    simp only [gf128ArmBdozFieldSum, gf128FieldMul, BitVec.xor_assoc]

private theorem gf128BdozArm_iter_succ (n : Nat) (m : UInt64 → UInt8)
    (pL pR : UInt64) (v : Bank32 Vec128) :
    gf128ArmBdozIterVec (n+1) m pL pR v =
      gf128ArmBdozIterVec n m (pL+32) (pR+32) (gf128ArmBdozBodyVec v m pL pR) := rfl

private theorem gf128BdozArm_iter_zero (m : UInt64 → UInt8)
    (pL pR : UInt64) (v : Bank32 Vec128) : gf128ArmBdozIterVec 0 m pL pR v = v := rfl

attribute [local irreducible] gf128ArmBdozBodyVec gf128ArmBdozIterVec

private theorem gf128BdozArm_loop_reaches (k : Nat) (hk : k+1 < 2^64)
    (g : Bank32 UInt64) (v : Bank32 Vec128) (cf zf dit : Bool) (m : UInt64 → UInt8) (hv : v.get 22 = Vec128.zero) :
    ExecReachesArm64 gf128BdozPmullProg (32 * (k+1))
      ⟨20, g.set 3 (UInt64.ofNat (k+1)), v, cf, zf, dit, false, m⟩
      ⟨148, ((g.set 1 (g.get 1 + UInt64.ofNat (32*(k+1)))).set
        2 (g.get 2 + UInt64.ofNat (32*(k+1)))).set 3 0,
        gf128ArmBdozIterVec (k+1) m (g.get 1) (g.get 2) v, true, true, dit, false, m⟩ := by
  induction k generalizing g v cf zf with
  | zero =>
    rw [gf128BdozArm_iter_succ, gf128BdozArm_iter_zero]
    change ExecReachesArm64 gf128BdozPmullProg 32
      ⟨20, g.set 3 1, v, cf, zf, dit, false, m⟩
      ⟨148, ((g.set 1 (g.get 1+32)).set 2 (g.get 2+32)).set 3 0,
        gf128ArmBdozBodyVec v m (g.get 1) (g.get 2), true, true, dit, false, m⟩
    have h := (gf128BdozArm_body_reaches (g.set 3 1) v cf zf dit m hv)
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
    have h := (gf128BdozArm_body_reaches (g.set 3 (UInt64.ofNat (k+1+1))) v cf zf dit m hv)
    simp (disch := decide) only [Bank32.get_set_eq, Bank32.get_set_ne, hd, hz,
      Bool.false_eq_true, ite_false, gf128Arm_set3123] at h
    have hvbody : (gf128ArmBdozBodyVec v m (g.get 1) (g.get 2)).get 22 = Vec128.zero := by
      rw [gf128BdozArm_body_keep22, hv]
    have hr := ih (by omega) ((g.set 1 (g.get 1+32)).set 2 (g.get 2+32))
      (gf128ArmBdozBodyVec v m (g.get 1) (g.get 2))
      (decide ((UInt64.ofNat (k+1+1)).toNat ≥ 1)) false hvbody
    have hc := ExecReachesArm64_trans h hr
    have he : 32 + 32*(k+1) = 32*(k+1+1) := by omega
    have hp (p : UInt64) : (p+32) + UInt64.ofNat (32*(k+1)) = p + UInt64.ofNat (32*(k+1+1)) := by
      rw [← he, UInt64.ofNat_add 32 (32*(k+1))]
      exact UInt64.add_assoc p 32 _
    rw [gf128BdozArm_iter_succ]
    simpa (disch := decide) only [he, Bank32.get_set_eq, Bank32.get_set_ne, hp,
      gf128Arm_set1212] using hc

def gf128BdozArmReduceVec (lo hi : Vec128) : Vec128 :=
  let r1 := clmul64 hi.w1 0x87
  let r0 := clmul64 (hi.w0 ^^^ r1.w1) 0x87
  ⟨lo.w0 ^^^ r0.w0, lo.w1 ^^^ r1.w0 ^^^ r0.w1⟩

private theorem gf128BdozArmReduceVec_field (lo hi : Vec128) :
    gf128Words (gf128BdozArmReduceVec lo hi).w0 (gf128BdozArmReduceVec lo hi).w1 =
      gf128Reduce (gf128ArmBdozPoly lo hi) :=
  gf128WordReduce_eq_reduce lo.w0 lo.w1 hi.w0 hi.w1

def gf128BdozArmReduceLaneVec (v : Bank32 Vec128) (rLo rHi : Nat) : Bank32 Vec128 :=
  let lo := v.get rLo
  let hi := v.get rHi
  let r1 := clmul64 hi.w1 0x87
  let r0 := clmul64 (hi.w0 ^^^ r1.w1) 0x87
  let v := (((v.set 16 ⟨hi.w1, 0⟩).set 6 r1).set 19 ⟨0, r1.w0⟩).set 20 ⟨r1.w1, 0⟩
  let v := (v.set rLo ⟨lo.w0, lo.w1 ^^^ r1.w0⟩).set rHi ⟨hi.w0 ^^^ r1.w1, hi.w1⟩
  (v.set 6 r0).set rLo (gf128BdozArmReduceVec lo hi)

private theorem gf128BdozArm_tailprep_reaches
    (g : Bank32 UInt64) (v : Bank32 Vec128) (cf zf dit : Bool) (m : UInt64 → UInt8) :
    ExecReachesArm64 gf128BdozPmullProg 2
      ⟨148, g, v, cf, zf, dit, false, m⟩
      ⟨156, g.set 4 0x87, v.set 21 ⟨0x87, 0⟩, cf, zf, dit, false, m⟩ := by
  apply StepsArm64.toExecReaches
  apply StepsArm64.cons rfl rfl
  · rw [gf128Arm_mov87]
  apply StepsArm64.cons rfl rfl
  · simp (disch := decide) only [stepArm64, getArmGpr, Nat.reduceBEq,
      Bool.false_eq_true, eq_self, ite_false, ite_true,
      Bank32.get_set_eq, Bank32.get_set_ne] <;> rfl
  exact StepsArm64.zero _
private theorem gf128BdozArm_reduce0_reaches
    (g : Bank32 UInt64) (v : Bank32 Vec128) (cf zf dit : Bool) (m : UInt64 → UInt8)
    (hv : v.get 22 = Vec128.zero) (h21 : v.get 21 = ⟨0x87, 0⟩) :
    ExecReachesArm64 gf128BdozPmullProg 9
      ⟨156, g, v, cf, zf, dit, false, m⟩
      ⟨192, g, gf128BdozArmReduceLaneVec v 0 1, cf, zf, dit, false,
        writeMem128 m (g.get 0+0) (gf128BdozArmReduceVec (v.get 0) (v.get 1))⟩ := by
  apply StepsArm64.toExecReaches
  iterate 1
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [gf128Arm_ext8,
        Bank32.get_set_eq, Bank32.get_set_ne, hv, Vec128.zero] <;> rfl
  iterate 1
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [stepArm64, Bank32.get_set_eq, Bank32.get_set_ne,
        h21] <;> rfl
  iterate 2
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [gf128Arm_ext8,
        Bank32.get_set_eq, Bank32.get_set_ne, hv, Vec128.zero] <;> rfl
  iterate 2
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [stepArm64, Bank32.get_set_eq, Bank32.get_set_ne,
        UInt64.xor_zero, UInt64.zero_xor] <;> rfl
  iterate 1
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [stepArm64, Bank32.get_set_eq, Bank32.get_set_ne,
        h21] <;> rfl
  iterate 1
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [stepArm64, Bank32.get_set_eq, Bank32.get_set_ne,
        UInt64.xor_zero, UInt64.zero_xor] <;> rfl
  apply StepsArm64.cons rfl rfl
  · simp (disch := decide) only [stepArm64, getArmGpr, Nat.reduceBEq,
      Bool.false_eq_true, eq_self, ite_false, ite_true, u64_add_zero,
      Bank32.get_set_eq, Bank32.get_set_ne] <;> rfl
  unfold gf128BdozArmReduceLaneVec gf128BdozArmReduceVec
  simp (disch := decide) only [Bank32.get_set_eq, Bank32.get_set_ne,
    UInt64.xor_zero, UInt64.zero_xor, UInt64.add_zero]
  exact StepsArm64.zero _

private theorem gf128BdozArm_reduce1_reaches
    (g : Bank32 UInt64) (v : Bank32 Vec128) (cf zf dit : Bool) (m : UInt64 → UInt8)
    (hv : v.get 22 = Vec128.zero) (h21 : v.get 21 = ⟨0x87, 0⟩) :
    ExecReachesArm64 gf128BdozPmullProg 9
      ⟨192, g, v, cf, zf, dit, false, m⟩
      ⟨228, g, gf128BdozArmReduceLaneVec v 2 3, cf, zf, dit, false,
        writeMem128 m (g.get 0+16) (gf128BdozArmReduceVec (v.get 2) (v.get 3))⟩ := by
  apply StepsArm64.toExecReaches
  iterate 1
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [gf128Arm_ext8,
        Bank32.get_set_eq, Bank32.get_set_ne, hv, Vec128.zero] <;> rfl
  iterate 1
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [stepArm64, Bank32.get_set_eq, Bank32.get_set_ne,
        h21] <;> rfl
  iterate 2
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [gf128Arm_ext8,
        Bank32.get_set_eq, Bank32.get_set_ne, hv, Vec128.zero] <;> rfl
  iterate 2
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [stepArm64, Bank32.get_set_eq, Bank32.get_set_ne,
        UInt64.xor_zero, UInt64.zero_xor] <;> rfl
  iterate 1
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [stepArm64, Bank32.get_set_eq, Bank32.get_set_ne,
        h21] <;> rfl
  iterate 1
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [stepArm64, Bank32.get_set_eq, Bank32.get_set_ne,
        UInt64.xor_zero, UInt64.zero_xor] <;> rfl
  apply StepsArm64.cons rfl rfl
  · simp (disch := decide) only [stepArm64, getArmGpr, Nat.reduceBEq,
      Bool.false_eq_true, eq_self, ite_false, ite_true, u64_add_zero,
      Bank32.get_set_eq, Bank32.get_set_ne] <;> rfl
  unfold gf128BdozArmReduceLaneVec gf128BdozArmReduceVec
  simp (disch := decide) only [Bank32.get_set_eq, Bank32.get_set_ne,
    UInt64.xor_zero, UInt64.zero_xor, UInt64.add_zero]
  exact StepsArm64.zero _

def gf128BdozArmCleanVec (v : Bank32 Vec128) : Bank32 Vec128 :=
  ((((((((((((((v.set 0 Vec128.zero).set 1 Vec128.zero).set 2 Vec128.zero).set 3 Vec128.zero).set 4 Vec128.zero).set 5 Vec128.zero).set 6 Vec128.zero).set 7 Vec128.zero).set 16 Vec128.zero).set 17 Vec128.zero).set 18 Vec128.zero).set 19 Vec128.zero).set 20 Vec128.zero).set 21 Vec128.zero)

private theorem gf128BdozArm_clean_reaches
    (g : Bank32 UInt64) (v : Bank32 Vec128) (cf zf dit : Bool) (m : UInt64 → UInt8) :
    ExecReachesArm64 gf128BdozPmullProg 15
      ⟨228, g, v, cf, zf, dit, false, m⟩
      ⟨288, g.set 4 0, gf128BdozArmCleanVec v, cf, zf, dit, false, m⟩ := by
  apply StepsArm64.toExecReaches
  iterate 14
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [stepArm64, UInt64.xor_self,
        Bank32.get_set_eq, Bank32.get_set_ne] <;> rfl
  apply StepsArm64.cons rfl rfl
  · rw [gf128Arm_mov0]
  exact StepsArm64.zero _

private theorem gf128BdozArm_reduce0_keep (v : Bank32 Vec128) :
    (gf128BdozArmReduceLaneVec v 0 1).get 2 = v.get 2 ∧
    (gf128BdozArmReduceLaneVec v 0 1).get 3 = v.get 3 ∧
    (gf128BdozArmReduceLaneVec v 0 1).get 21 = v.get 21 ∧
    (gf128BdozArmReduceLaneVec v 0 1).get 22 = v.get 22 := by
  simp (disch := decide) only [gf128BdozArmReduceLaneVec, Bank32.get_set_ne,
    and_self]

attribute [local irreducible] gf128BdozArmReduceLaneVec

private theorem gf128BdozArm_tail_reaches
    (g : Bank32 UInt64) (v : Bank32 Vec128) (cf zf dit : Bool) (m : UInt64 → UInt8)
    (hv : v.get 22 = Vec128.zero) :
    ∃ g' v', ExecReachesArm64 gf128BdozPmullProg 35
      ⟨148, g, v, cf, zf, dit, false, m⟩
      ⟨288, g', v', cf, zf, dit, false,
        writeMem128 (writeMem128 m (g.get 0) (gf128BdozArmReduceVec (v.get 0) (v.get 1)))
          (g.get 0+16) (gf128BdozArmReduceVec (v.get 2) (v.get 3))⟩ := by
  let v1 := v.set 21 ⟨0x87, 0⟩
  let g1 := g.set 4 0x87
  have hv1 : v1.get 22 = Vec128.zero := by
    simpa [v1, Bank32.get_set_ne] using hv
  have hc1 : v1.get 21 = ⟨0x87, 0⟩ := Bank32.get_set_eq _ _ _
  have hp := gf128BdozArm_tailprep_reaches g v cf zf dit m
  have h0 := gf128BdozArm_reduce0_reaches g1 v1 cf zf dit m hv1 hc1
  let v2 := gf128BdozArmReduceLaneVec v1 0 1
  let m1 := writeMem128 m (g1.get 0+0) (gf128BdozArmReduceVec (v1.get 0) (v1.get 1))
  have hk := gf128BdozArm_reduce0_keep v1
  have hv2 : v2.get 22 = Vec128.zero := hk.2.2.2.trans hv1
  have hc2 : v2.get 21 = ⟨0x87, 0⟩ := hk.2.2.1.trans hc1
  have h1 := gf128BdozArm_reduce1_reaches g1 v2 cf zf dit m1 hv2 hc2
  have hclean := gf128BdozArm_clean_reaches g1 (gf128BdozArmReduceLaneVec v2 2 3)
    cf zf dit (writeMem128 m1 (g1.get 0+16) (gf128BdozArmReduceVec (v2.get 2) (v2.get 3)))
  have h := ExecReachesArm64_trans hp (ExecReachesArm64_trans h0 (ExecReachesArm64_trans h1 hclean))
  have hm : writeMem128 m1 (g1.get 0+16) (gf128BdozArmReduceVec (v2.get 2) (v2.get 3)) =
      writeMem128 (writeMem128 m (g.get 0) (gf128BdozArmReduceVec (v.get 0) (v.get 1)))
        (g.get 0+16) (gf128BdozArmReduceVec (v.get 2) (v.get 3)) := by
    rw [show v2.get 2 = v1.get 2 from hk.1, show v2.get 3 = v1.get 3 from hk.2.1]
    simp (disch := decide) only [m1, g1, v1, Bank32.get_set_ne, UInt64.add_zero]
  refine ⟨g1.set 4 0, gf128BdozArmCleanVec (gf128BdozArmReduceLaneVec v2 2 3), ?_⟩
  rw [hm] at h
  exact h

def gf128BdozArmInitVec (v : Bank32 Vec128) : Bank32 Vec128 :=
  ((((v.set 0 Vec128.zero).set 1 Vec128.zero).set 2 Vec128.zero).set 3 Vec128.zero).set 22 Vec128.zero

private theorem gf128BdozArm_entry_reaches
    (g : Bank32 UInt64) (v : Bank32 Vec128) (cf zf dit : Bool) (m : UInt64 → UInt8) :
    ExecReachesArm64 gf128BdozPmullProg 5
      ⟨0, g, v, cf, zf, dit, false, m⟩
      ⟨20, g, gf128BdozArmInitVec v, cf, zf, dit, false, m⟩ := by
  apply StepsArm64.toExecReaches
  iterate 5
    apply StepsArm64.cons rfl rfl
    · simp (disch := decide) only [stepArm64, UInt64.xor_self,
        Bank32.get_set_eq, Bank32.get_set_ne] <;> rfl
  exact StepsArm64.zero _

private theorem gf128BdozArm_init_zero (v : Bank32 Vec128) :
    gf128ArmBdozPoly ((gf128BdozArmInitVec v).get 0) ((gf128BdozArmInitVec v).get 1) = 0 ∧
    gf128ArmBdozPoly ((gf128BdozArmInitVec v).get 2) ((gf128BdozArmInitVec v).get 3) = 0 := by
  change gf128ArmBdozPoly Vec128.zero Vec128.zero = 0 ∧
    gf128ArmBdozPoly Vec128.zero Vec128.zero = 0
  decide +kernel

/-- Fresh-byte two-lane polynomial MAC on AArch64, for every positive 64-bit ABI
count. The two output lanes are independent XOR sums of field products.
All reads precede both stores, so input/output aliasing and pointer wrapping
are admitted; the zero-count wrapper return is not modelled as kernel execution. -/
theorem current_rlib_gf128_tower128_bdoz_mac_pmull_functional
    (n : Nat) (hn : 0 < n) (hbound : n < 2^64) (s : Arm64State)
    (hpc : s.pc = 0) (hh : s.halted = false) (hc : s.gpr.get 3 = UInt64.ofNat n) :
    ∃ slice : ElfFuncSlice,
      findSliceByNameBytes currentAarch64ExtractedSlices gf128BdozPmullName = some slice ∧
      decodeArm64Stream slice.code = some gf128BdozPmullProg ∧
      ∀ extra : Nat, ∃ out0 out1 : Vec128,
        (runArm64 gf128BdozPmullProg (41 + 32*n + extra) s).1.halted = true ∧
        (runArm64 gf128BdozPmullProg (41 + 32*n + extra) s).1.pc = 288 ∧
        (runArm64 gf128BdozPmullProg (41 + 32*n + extra) s).2.length = 41 + 32*n ∧
        (runArm64 gf128BdozPmullProg (41 + 32*n + extra) s).1.mem =
          writeMem128 (writeMem128 s.mem (s.gpr.get 0) out0) (s.gpr.get 0+16) out1 ∧
        gf128Words out0.w0 out0.w1 = gf128ArmBdozFieldSum 0 n s.mem (s.gpr.get 1) (s.gpr.get 2) ∧
        gf128Words out1.w0 out1.w1 = gf128ArmBdozFieldSum 16 n s.mem (s.gpr.get 1) (s.gpr.get 2) := by
  have hdec := gf128BdozPmull_current_decode
  cases hfind : findSliceByNameBytes currentAarch64ExtractedSlices gf128BdozPmullName with
  | none => simp [hfind] at hdec
  | some slice =>
    simp only [hfind, Option.map_some, Option.some.injEq] at hdec
    refine ⟨slice, rfl, hdec, ?_⟩
    cases n with
    | zero => exact False.elim (Nat.not_lt_zero 0 hn)
    | succ k =>
      rcases s with ⟨pc, g, v, cf, zf, dit, halted, m⟩
      dsimp only at hpc hh hc ⊢
      subst pc
      subst halted
      have hg : g.set 3 (UInt64.ofNat (k+1)) = g := by rw [← hc]; rfl
      have he := gf128BdozArm_entry_reaches g v cf zf dit m
      have hv : (gf128BdozArmInitVec v).get 22 = Vec128.zero := Bank32.get_set_eq _ _ _
      have hl := gf128BdozArm_loop_reaches k hbound g (gf128BdozArmInitVec v) cf zf dit m hv
      rw [hg] at hl
      let gEnd := ((g.set 1 (g.get 1 + UInt64.ofNat (32*(k+1)))).set
        2 (g.get 2 + UInt64.ofNat (32*(k+1)))).set 3 0
      let vEnd := gf128ArmBdozIterVec (k+1) m (g.get 1) (g.get 2) (gf128BdozArmInitVec v)
      have hvEnd : vEnd.get 22 = Vec128.zero := by
        rw [gf128BdozArm_iter_keep22]
        exact hv
      obtain ⟨g', v', ht⟩ := gf128BdozArm_tail_reaches gEnd vEnd true true dit m hvEnd
      have hfull := ExecReachesArm64_trans he (ExecReachesArm64_trans hl ht)
      have hret := ExecReachesArm64_ret hfull rfl (by rfl)
      intro extra
      have hr := hret.2.2 extra
      have hsteps : 5 + (32*(k+1) + 35) + 1 = 41 + 32*(k+1) := by omega
      rw [hsteps] at hr
      let out0 := gf128BdozArmReduceVec (vEnd.get 0) (vEnd.get 1)
      let out1 := gf128BdozArmReduceVec (vEnd.get 2) (vEnd.get 3)
      refine ⟨out0, out1, ?_, ?_, hr.2, ?_, ?_, ?_⟩
      · rw [hr.1]
      · rw [hr.1]
      · rw [hr.1]
        rfl
      · change gf128Words (gf128BdozArmReduceVec _ _).w0 (gf128BdozArmReduceVec _ _).w1 = _
        rw [gf128BdozArmReduceVec_field, gf128BdozArm_iter_field0, (gf128BdozArm_init_zero v).1]
        have hz : gf128Reduce 0 = 0 := by decide +kernel
        rw [hz]
        simp only [BitVec.ofNat_eq_ofNat, BitVec.zero_xor]
      · change gf128Words (gf128BdozArmReduceVec _ _).w0 (gf128BdozArmReduceVec _ _).w1 = _
        rw [gf128BdozArmReduceVec_field, gf128BdozArm_iter_field1, (gf128BdozArm_init_zero v).2]
        have hz : gf128Reduce 0 = 0 := by decide +kernel
        rw [hz]
        simp only [BitVec.ofNat_eq_ofNat, BitVec.zero_xor]

end Gf128BdozArmProof

def gf128BdozArmWitness : Arm64State :=
  ⟨0, (Bank32.const 0).set 3 1, Bank32.const Vec128.zero,
    false, false, false, false, fun a => if a == 0 then 1 else 0⟩

/-- Dropping the constant-coefficient product contradicts the actual fresh run. -/
theorem current_rlib_gf128_tower128_bdoz_mac_pmull_tooth :
    (runArm64 gf128BdozPmullProg 73 gf128BdozArmWitness).1.mem 0 ≠ 0 := by
  decide +kernel

theorem current_rlib_gf128_tower128_bdoz_mac_pmull_inhabited :
    ∃ n : Nat, ∃ s : Arm64State,
      0 < n ∧ n < 2^64 ∧ s.pc = 0 ∧ s.halted = false ∧ s.gpr.get 3 = UInt64.ofNat n := by
  refine ⟨1, gf128BdozArmWitness, ?_⟩
  decide +kernel

#tooth_pair current_rlib_gf128_tower128_bdoz_mac_pmull_functional vs current_rlib_gf128_tower128_bdoz_mac_pmull_tooth
#verify_inhabited current_rlib_gf128_tower128_bdoz_mac_pmull_functional current_rlib_gf128_tower128_bdoz_mac_pmull_inhabited

end Gf128KernelEquivalence

end Qsag
