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
  ⟨4, 4, .csel 1 false 0 1 2⟩,
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

private theorem u8_xor_assoc (a b c : UInt8) : (a ^^^ b) ^^^ c = a ^^^ (b ^^^ c) := by
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

private theorem u8_xor_self (a : UInt8) : a ^^^ a = 0 := by
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
  · rw [ha, hb]; simp; exact u8_xor_assoc _ _ _
  · rw [ha, hb]; simp
    apply UInt8.eq_of_toBitVec_eq; ext i hi; simp only [UInt8.toBitVec_xor, BitVec.getElem_xor]
    cases (a <<< 1).toBitVec[i] <;> cases (b <<< 1).toBitVec[i] <;> cases (0x1B : UInt8).toBitVec[i] <;> rfl
  · rw [ha, hb, u8_xor_self]; simp
    rw [u8_xor_four, u8_xor_self]; apply UInt8.eq_of_toBitVec_eq; simp

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

