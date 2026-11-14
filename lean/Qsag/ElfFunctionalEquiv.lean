module

public import Qsag.Goldilocks
public import Qsag.BinaryTower
public import Qsag.Keccak
public import Qsag.ElfBinaryVerify
public import Qsag.ElfFixtureVerify
public import Qsag.McRefine
import all Qsag.ElfParse
import all Qsag.ElfBinaryVerify
import all Qsag.McRefine
import all Qsag.BinaryTower
import all Qsag.Keccak

/-!
# Compiled-Byte Machine-Code Functional Equivalence & Unified CT-NI Certificates (`ElfFunctionalEquiv.lean`)

Lean 4.35 functional equivalence layer for selected historical compiled `.rlib` / `ELF64`
machine-code byte slices (`CompiledRlibFixtures.lean`, `ElfParse.lean`, `ElfBinaryVerify.lean`)
to canonical mathematical and cryptographic specifications (`Goldilocks.lean`, `BinaryTower.lean`,
`Keccak.lean`, `ConstantTimeIsa.lean`).
These byte-pinned results do not establish freshness against the current assembly source;
renewed fixture certification is required for that claim.
-/

public section

namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
  UInt64.instLawfulOrderOrd String.instLawfulEqOrd
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
    (stepArm64 ⟨off, len, .csel 1 false rd rn rm⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
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

