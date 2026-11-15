module
public import Qsag.ElfBinaryVerify
import all Qsag.ElfBinaryVerify
import Qsag.Tactic.AssuranceKit
public section
open Qsag

/-! Pure execution and regression-vector layer used by the JSON cosimulation
executable. The executable imports this implementation directly. JSON parsing
and IO belong to the untrusted harness, outside the proof-module axiom audit. -/
namespace IsaCosim

def requireSome {α : Type} (message : String) : Option α → Except String α
  | some x => .ok x
  | none => .error message

def hexNat (width n : Nat) : String :=
  String.ofList ((List.range width).reverse.map fun i =>
    ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f'][(n >>> (4*i)) % 16]!)

def parseHex (s : String) : Except String Nat := do
  if s.isEmpty then throw "empty hexadecimal integer"
  (s.toUTF8.toList.map (fun b => Char.ofNat b.toNat)).foldlM (fun n c => do
    let v ← if '0' ≤ c && c ≤ '9' then pure (c.toNat - 48)
      else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 87)
      else if 'A' ≤ c && c ≤ 'F' then pure (c.toNat - 55)
      else throw "invalid hexadecimal digit"
    pure (16*n + v)) 0

def bytes (s : String) : Except String (List UInt8) := do
  let cs := (s.toUTF8.toList.map (fun b => Char.ofNat b.toNat)).toArray
  if cs.size % 2 != 0 then throw "odd hexadecimal byte string"
  (List.range (cs.size / 2)).mapM fun i => do
    return UInt8.ofNat (← parseHex (String.ofList [cs[2*i]!, cs[2*i+1]!]))

/-- Arithmetic status bits: CF/PF/AF/ZF/SF/OF. Undefined bits are tracked,
not assigned an invented silicon value. Preserved non-status bits stay exact. -/
structure Flags where
  value : Nat
  valid : Nat := 0xffffffffffffffff

def bit (x k : Nat) : Bool := x &&& (2^k) != 0

def putFlags (f : Flags) (mask value : Nat) : Flags :=
  ⟨(f.value &&& (0xffffffffffffffff - mask)) ||| (value &&& mask), f.valid ||| mask⟩

def undefFlags (f : Flags) (mask : Nat) : Flags :=
  { f with valid := f.valid &&& (0xffffffffffffffff - mask) }

def szp (r w : Nat) : Nat :=
  (if r == 0 then 64 else 0) + (if bit r (w-1) then 128 else 0) +
  (if ((List.range 8).filter (bit r)).length % 2 == 0 then 4 else 0)

def signed (x w : Nat) : Int :=
  if bit x (w-1) then (x : Int) - (2^w : Nat) else x

def aluFlags (f : Flags) (op : X86AluOp) (wide : Bool) (a b : UInt64) : Flags := Id.run do
  let w := if wide then 64 else 32
  let bound := 2^w
  let a := a.toNat % bound
  let b := b.toNat % bound
  let c := if bit f.value 0 then 1 else 0
  let (r, cf, _) := evalX86Alu op wide (UInt64.ofNat a) (UInt64.ofNat b) (bit f.value 0)
  if op == .imul2 then
    let prod := signed a w * signed b w
    let overflow := !(@decide (prod = signed r.toNat w) (Int.decEq _ _))
    return undefFlags (putFlags f 0x801 (if overflow then 0x801 else 0)) 0xd4
  if op == .andOp || op == .orOp || op == .xorOp then
    return undefFlags (putFlags f 0x8c5 (szp r.toNat w)) 0x10
  let sub := op == .sub || op == .sbb
  let carry := if op == .adc || op == .sbb then c else 0
  let exact := if sub then signed a w - signed b w - carry else signed a w + signed b w + carry
  let overflow := !(@decide (exact = signed r.toNat w) (Int.decEq _ _))
  let af := bit (a ^^^ b ^^^ r.toNat) 4
  return putFlags f 0x8d5 (szp r.toNat w + (if cf then 1 else 0) +
    (if af then 16 else 0) + (if overflow then 2048 else 0))

def condition (cc : Nat) (f : Flags) : Except String Bool := do
  let mask := match cc / 2 with
    | 0 => 0x800 | 1 => 1 | 2 => 64 | 3 => 65
    | 4 => 128 | 5 => 4 | 6 => 0x880 | _ => 0x8c0
  if f.valid &&& mask != mask then throw "condition consumes architecturally undefined flags"
  let v := match cc / 2 with
    | 0 => bit f.value 11 | 1 => bit f.value 0 | 2 => bit f.value 6
    | 3 => bit f.value 0 || bit f.value 6
    | 4 => bit f.value 7 | 5 => bit f.value 2
    | 6 => bit f.value 7 != bit f.value 11
    | _ => bit f.value 6 || (bit f.value 7 != bit f.value 11)
  return if cc % 2 == 0 then v else !v

/-- Execute one decoded `X86Instr` via the canonical `ElfBinaryVerify.stepX86`
without overriding any GPR, YMM, memory, or PC output, while tracking `PF/AF/SF`
and undefined-flag masks and asserting agreement with `stepX86`'s `(cf, zf, ofFlag)`
on every architecturally defined bit. -/
def step (d : DecodedInstr X86Instr) (st : X86State) (f : Flags) : Except String (X86State × Flags) := do
  match d.instr with
  | .aluRegReg op _ _ _ | .aluImm op _ _ _ | .aluLoad64 op _ _ =>
    if (op == .adc || op == .sbb) && f.valid &&& 1 == 0 then
      throw "arithmetic consumes undefined CF"
  | .adcx .. => if f.valid &&& 1 == 0 then throw "ADCX consumes undefined CF"
  | .adox .. => if f.valid &&& 2048 == 0 then throw "ADOX consumes undefined OF"
  | _ => pure ()
  let out := (stepX86 d st).1
  let mut flags := f
  match d.instr with
  | .aluRegReg op wide dst src => flags := aluFlags f op wide (st.gpr.get dst) (st.gpr.get src)
  | .aluImm op wide dst imm => flags := aluFlags f op wide (st.gpr.get dst) imm
  | .aluLoad64 op dst addr =>
    flags := aluFlags f op true (st.gpr.get dst) (readMem64 st.mem (evalX86Addr st (d.offset+d.byteLen) addr))
  | .testRegReg wide r1 r2 => flags := aluFlags f .andOp wide (st.gpr.get r1) (st.gpr.get r2)
  | .cmpRegReg wide dst src => flags := aluFlags f .sub wide (st.gpr.get dst) (st.gpr.get src)
  | .cmpImm wide dst imm => flags := aluFlags f .sub wide (st.gpr.get dst) imm
  | .negReg wide dst => flags := aluFlags f .sub wide 0 (st.gpr.get dst)
  | .incDec inc wide dst =>
    flags := putFlags (aluFlags f (if inc then .add else .sub) wide (st.gpr.get dst) 1) 1 f.value
    flags := { flags with valid := (flags.valid &&& 0xfffffffffffffffe) ||| (f.valid &&& 1) }
  | .mulOneOp _ _ _ =>
    if out.cf != out.ofFlag then throw "stepX86 MUL/IMUL CF != OF"
    flags := undefFlags (putFlags f 0x801 (if out.cf then 0x801 else 0)) 0xd4
  | .shiftImm kind wide dst cnt =>
    let w := if wide then 64 else 32
    let c := cnt % w
    if c != 0 then
      let r := (out.gpr.get dst).toNat
      flags := putFlags f 1 (if out.cf then 1 else 0)
      if kind == .shl || kind == .shr || kind == .sar then
        flags := undefFlags (putFlags flags 0xc4 (szp r w)) 16
      flags := if c == 1 then putFlags flags 2048 (if out.ofFlag then 2048 else 0) else undefFlags flags 2048
  | .cmovcc cc _ _ _ =>
    let cond ← condition cc f
    if evalX86Cond cc st != cond then throw "stepX86 CMOVcc condition mismatch"
  | .setcc cc _ =>
    let cond ← condition cc f
    if evalX86Cond cc st != cond then throw "stepX86 SETcc condition mismatch"
  | .jcc cc target =>
    let cond ← condition cc f
    if target < 0 then throw "Jcc negative target out of slice"
    if evalX86Cond cc st != cond then throw "stepX86 Jcc condition mismatch"
  | .jmpRel target =>
    if target < 0 then throw "JMP negative target out of slice"
  | .adcx .. => flags := putFlags f 1 (if out.cf then 1 else 0)
  | .adox .. => flags := putFlags f 2048 (if out.ofFlag then 2048 else 0)
  | .ret => throw "RET is a function boundary; compare before RET"
  | .divRem _ | .indirectBr _ | .varShiftCl _ _ | .vpgather _ _ =>
    throw "instruction is classified but lacks executable semantics"
  | _ => pure ()
  if (flags.valid &&& 1 != 0) && out.cf != bit flags.value 0 then
    throw "raw stepX86 CF diverges from architectural RFLAGS"
  if (flags.valid &&& 64 != 0) && out.zf != bit flags.value 6 then
    throw "raw stepX86 ZF diverges from architectural RFLAGS"
  if (flags.valid &&& 2048 != 0) && out.ofFlag != bit flags.value 11 then
    throw "raw stepX86 OF diverges from architectural RFLAGS"
  return (out, flags)

/-- Single-instruction probes for encodings whose architectural meaning needs state that
`X86State` does not carry: `CMOVcc` / `SETcc` on condition codes outside `{2,3,4,5}` (they read
`SF` / `PF`), high-byte `AH..BH` `SETcc`, and legacy non-VEX `PCLMULQDQ` (which preserves bits
`[255:128]`, unlike the VEX form the verified decoder models). `run` consults this layer only for
a byte string that `decodeX86Stream` rejects as a whole, so any code the verified decoder accepts
(every certified kernel) executes through `stepX86` alone. -/
def extra (bs : List UInt8) (st : X86State) (f : Flags) : Option (Except String (X86State × Flags × Nat)) := Id.run do
  let rex := (bs.headD 0).toNat
  let hasRex := 0x40 ≤ rex && rex ≤ 0x4f
  let p := if hasRex then 1 else 0
  let rex := if hasRex then rex else 0
  let wide := rex &&& 8 != 0
  let op := (bs.getD p 0).toNat
  let op2 := (bs.getD (p+1) 0).toNat
  let modrm := (bs.getD (p+2) 0).toNat
  let reg := modrm % 8 + (rex % 2)*8
  if op == 0x0f && 0x40 ≤ op2 && op2 ≤ 0x4f && modrm ≥ 0xc0 && bs.length ≥ p+3 then
    return some do
      let dst := (modrm/8)%8 + ((rex/4)%2)*8
      let v := if ← condition (op2-0x40) f then st.gpr.get reg else st.gpr.get dst
      return ({ st with pc := st.pc+p+3, gpr := st.gpr.set dst (maskGprWidth wide v) }, f, p+3)
  if op == 0x0f && 0x90 ≤ op2 && op2 ≤ 0x9f && modrm ≥ 0xc0 && bs.length ≥ p+3 then
    return some do
      let v := if ← condition (op2-0x90) f then 1 else 0
      let high := !hasRex && reg ≥ 4
      let dst := if high then reg-4 else reg
      let shift := if high then 8 else 0
      let old := (st.gpr.get dst).toNat
      let value := (old &&& (0xffffffffffffffff - (255 <<< shift))) ||| (v <<< shift)
      return ({ st with gpr := st.gpr.set dst (UInt64.ofNat value), pc := st.pc+p+3 }, f, p+3)
  if bs.take 4 == [0x66, 0x0f, 0x3a, 0x44] && bs.length ≥ 6 then
    let m := (bs.getD 4 0).toNat
    if m ≥ 0xc0 then
      let dst := (m/8)%8
      let src := m%8
      let d : DecodedInstr X86Instr := ⟨st.pc, 6, .vpclmulqdq false dst dst src (bs.getD 5 0)⟩
      let out := (stepX86 d st).1
      let old := st.ymm.get dst
      let v := out.ymm.get dst
      return some (.ok ({ out with ymm := out.ymm.set dst { v with w2 := old.w2, w3 := old.w3 } }, f, 6))
  return none

def runWith (allowExtra : Bool) (fuel : Nat) (code : List UInt8) (st : X86State) (f : Flags) :
    Except String (X86State × Flags × List Nat) :=
  if st.pc == code.length then pure (st, f, [])
  else if st.pc > code.length then .error s!"program counter {st.pc} escaped slice length {code.length}"
  else match fuel with
  | 0 => .error "instruction fuel exhausted"
  | n+1 => do
    let bs := code.drop st.pc
    let (out, flags) ← match decodeX86InstrAt st.pc bs with
      | some d => step d st f
      | none =>
        if !allowExtra then .error s!"instruction at {st.pc} is outside the verified decoder"
        else match extra bs st f with
        | some result => do let (out, flags, _) ← result; pure (out, flags)
        | none => .error s!"unsupported instruction at {st.pc}"
    let (finalOut, finalFlags, pcs) ← runWith allowExtra n code out flags
    pure (finalOut, finalFlags, out.pc :: pcs)

/-- Cosimulate `code`. The `extra` probe layer is enabled exactly when the verified stream
decoder rejects `code`. -/
def run (fuel : Nat) (code : List UInt8) (st : X86State) (f : Flags) :
    Except String (X86State × Flags × List Nat) :=
  runWith (decodeX86Stream code).isNone fuel code st f

/-- Code accepted by the verified decoder never reaches the `extra` probe layer. -/
theorem run_verified_code_is_strict (fuel : Nat) (code : List UInt8) (st : X86State) (f : Flags)
    (prog : List (DecodedInstr X86Instr)) (h : decodeX86Stream code = some prog) :
    run fuel code st f = runWith false fuel code st f := by
  unfold run
  rw [h]
  rfl

structure EdgeVector where
  name : String
  code : List UInt8
  rax : UInt64 := 0
  rcx : UInt64 := 0
  rdx : UInt64 := 0
  initFlags : Nat := 0x202
  expRax : UInt64
  expRcx : UInt64 := 0
  expRdx : UInt64 := 0
  expValidMask : Nat
  expFlags : Nat

def edgeCaseVectors : List EdgeVector := [
  ⟨"mul64_zero_lhs", [0x48, 0xf7, 0xe1], 0, 0xdeadbeefcafebabe, 0x1122334455667788, 0xad7,
    0, 0xdeadbeefcafebabe, 0, 0xffffffffffffff2b, 0x202⟩,
  ⟨"mul64_zero_rhs", [0x48, 0xf7, 0xe1], 0xffffffffffffffff, 0, 0x99, 0xad7,
    0, 0, 0, 0xffffffffffffff2b, 0x202⟩,
  ⟨"mul64_neg1_neg1_unsigned", [0x48, 0xf7, 0xe1], 0xffffffffffffffff, 0xffffffffffffffff, 0, 0x202,
    1, 0xffffffffffffffff, 0xfffffffffffffffe, 0xffffffffffffff2b, 0xa03⟩,
  ⟨"imul64_1op_neg1_neg1_signed", [0x48, 0xf7, 0xe9], 0xffffffffffffffff, 0xffffffffffffffff, 0x7777, 0xad7,
    1, 0xffffffffffffffff, 0, 0xffffffffffffff2b, 0x202⟩,
  ⟨"imul64_2op_neg1_neg1_signed", [0x48, 0x0f, 0xaf, 0xc1], 0xffffffffffffffff, 0xffffffffffffffff, 0x123456789abcdef0, 0xad7,
    1, 0xffffffffffffffff, 0x123456789abcdef0, 0xffffffffffffff2b, 0x202⟩,
  ⟨"imul64_2op_zero_neg1", [0x48, 0x0f, 0xaf, 0xc1], 0, 0xffffffffffffffff, 0x42, 0xad7,
    0, 0xffffffffffffffff, 0x42, 0xffffffffffffff2b, 0x202⟩,
  ⟨"imul64_1op_min_neg1_overflow", [0x48, 0xf7, 0xe9], 0x8000000000000000, 0xffffffffffffffff, 0, 0x202,
    0x8000000000000000, 0xffffffffffffffff, 0, 0xffffffffffffff2b, 0xa03⟩,
  ⟨"mul32_neg1_neg1_unsigned", [0xf7, 0xe1], 0xdeadbeefffffffff, 0xcafebabeffffffff, 0xffffffff00000000, 0x202,
    1, 0xcafebabeffffffff, 0xfffffffe, 0xffffffffffffff2b, 0xa03⟩,
  ⟨"imul32_1op_neg1_neg1_signed", [0xf7, 0xe9], 0xdeadbeefffffffff, 0xcafebabeffffffff, 0xffffffff00000000, 0xad7,
    1, 0xcafebabeffffffff, 0, 0xffffffffffffff2b, 0x202⟩,
  ⟨"shl64_c1_cnt1_of1", [0x48, 0xc1, 0xe0, 0x01], 0x4000000000000000, 0, 0, 0x202,
    0x8000000000000000, 0, 0, 0xffffffffffffffef, 0xa86⟩,
  ⟨"shl64_d1_cnt1_of1", [0x48, 0xd1, 0xe0], 0x4000000000000000, 0, 0, 0x202,
    0x8000000000000000, 0, 0, 0xffffffffffffffef, 0xa86⟩,
  ⟨"shl64_d1_cnt1_cf1_of0", [0x48, 0xd1, 0xe0], 0xc000000000000000, 0, 0, 0xad7,
    0x8000000000000000, 0, 0, 0xffffffffffffffef, 0x287⟩,
  ⟨"shr64_c1_cnt1_cf1_of1", [0x48, 0xc1, 0xe8, 0x01], 0x8000000000000001, 0, 0, 0x202,
    0x4000000000000000, 0, 0, 0xffffffffffffffef, 0xa07⟩,
  ⟨"shr64_d1_cnt1_cf1_of1", [0x48, 0xd1, 0xe8], 0x8000000000000001, 0, 0, 0x202,
    0x4000000000000000, 0, 0, 0xffffffffffffffef, 0xa07⟩,
  ⟨"ror64_c1_cnt1_preserves_szpaf", [0x48, 0xc1, 0xc8, 0x01], 1, 0, 0, 0x2d6,
    0x8000000000000000, 0, 0, 0xffffffffffffffff, 0xad7⟩,
  ⟨"ror64_d1_cnt1_preserves_szpaf", [0x48, 0xd1, 0xc8], 1, 0, 0, 0x2d6,
    0x8000000000000000, 0, 0, 0xffffffffffffffff, 0xad7⟩,
  ⟨"rol64_d1_cnt1_cf1_of1", [0x48, 0xd1, 0xc0], 0x8000000000000000, 0, 0, 0x2d6,
    1, 0, 0, 0xffffffffffffffff, 0xad7⟩,
  ⟨"sar64_c1_cnt1_of0", [0x48, 0xc1, 0xf8, 0x01], 0x8000000000000001, 0, 0, 0xad7,
    0xc000000000000000, 0, 0, 0xffffffffffffffef, 0x287⟩,
  ⟨"sar64_d1_cnt1_of0", [0x48, 0xd1, 0xf8], 0x8000000000000001, 0, 0, 0xad7,
    0xc000000000000000, 0, 0, 0xffffffffffffffef, 0x287⟩,
  ⟨"shl64_cnt2_undef_of", [0x48, 0xc1, 0xe0, 0x02], 0x6000000000000000, 0, 0, 0x202,
    0x8000000000000000, 0, 0, 0xfffffffffffff7ef, 0x287⟩,
  ⟨"shr64_cnt63_undef_of", [0x48, 0xc1, 0xe8, 0x3f], 0xc000000000000000, 0, 0, 0xad7,
    1, 0, 0, 0xfffffffffffff7ef, 0x203⟩,
  ⟨"ror64_cnt13_undef_of_preserves_szpaf", [0x48, 0xc1, 0xc8, 0x0d], 0x0000000000001000, 0, 0, 0x2d6,
    0x8000000000000000, 0, 0, 0xfffffffffffff7ff, 0x2d7⟩,
  ⟨"shl64_cnt0_noop", [0x48, 0xc1, 0xe0, 0x00], 0x8000000000000001, 0, 0, 0xad7,
    0x8000000000000001, 0, 0, 0xffffffffffffffff, 0xad7⟩,
  ⟨"shl64_cnt64_masks_to_zero", [0x48, 0xc1, 0xe0, 0x40], 0x8000000000000001, 0, 0, 0xad7,
    0x8000000000000001, 0, 0, 0xffffffffffffffff, 0xad7⟩,
  ⟨"ror64_cnt64_masks_to_zero", [0x48, 0xc1, 0xc8, 0x40], 0xfeedfacecafebabe, 0, 0, 0x202,
    0xfeedfacecafebabe, 0, 0, 0xffffffffffffffff, 0x202⟩,
  ⟨"shl32_cnt32_masks_to_zero_zext", [0xc1, 0xe0, 0x20], 0xdeadbeef12345678, 0, 0, 0xad7,
    0x0000000012345678, 0, 0, 0xffffffffffffffff, 0xad7⟩,
  ⟨"shl64_cnt32_shifts_by_32", [0x48, 0xc1, 0xe0, 0x20], 0x0000000180000000, 0, 0, 0x202,
    0x8000000000000000, 0, 0, 0xfffffffffffff7ef, 0x287⟩,
  ⟨"shl64_cnt65_masks_to_one_defines_of", [0x48, 0xc1, 0xe0, 0x41], 0x4000000000000000, 0, 0, 0x202,
    0x8000000000000000, 0, 0, 0xffffffffffffffef, 0xa86⟩,
  ⟨"seed0x51a_case37_mul64", [0x48, 0xf7, 0xe1], 0xffffffffffffffff, 0x8000000000000000, 0, 0x203,
    0x8000000000000000, 0x8000000000000000, 0x7fffffffffffffff, 0xffffffffffffff2b, 0xa03⟩,
  ⟨"seed0x51a_case38_shl64_1", [0x48, 0xc1, 0xe0, 0x01], 0x8000000000000000, 0xffffffff00000000, 0, 0xa42,
    0, 0xffffffff00000000, 0, 0xffffffffffffffef, 0xa47⟩,
  ⟨"seed0x51a_case39_shr64_1", [0x48, 0xc1, 0xe8, 0x01], 0xffffffff00000000, 0xffffffff00000001, 0, 0x202,
    0x7fffffff80000000, 0xffffffff00000001, 0, 0xffffffffffffffef, 0xa06⟩,
  ⟨"seed0x51a_case40_ror64_1", [0x48, 0xc1, 0xc8, 0x01], 0xffffffff00000001, 1, 0, 0xa02,
    0xffffffff80000000, 1, 0, 0xffffffffffffffff, 0x203⟩,
  ⟨"seed0x51a_case78_mul64", [0x48, 0xf7, 0xe1], 0, 0xffffffffffffffff, 0, 0xa42,
    0, 0xffffffffffffffff, 0, 0xffffffffffffff2b, 0x202⟩,
  ⟨"seed0x51a_case79_shl64_1", [0x48, 0xc1, 0xe0, 0x01], 0xffffffffffffffff, 0x8000000000000000, 0, 0x242,
    0xfffffffffffffffe, 0x8000000000000000, 0, 0xffffffffffffffef, 0x283⟩,
  ⟨"seed0x51a_case80_shr64_1", [0x48, 0xc1, 0xe8, 0x01], 0x8000000000000000, 0xffffffff00000000, 0, 0x243,
    0x4000000000000000, 0xffffffff00000000, 0, 0xffffffffffffffef, 0xa06⟩,
  ⟨"seed0x51a_case81_ror64_1", [0x48, 0xc1, 0xc8, 0x01], 0xffffffff00000000, 0xffffffff00000001, 0, 0x243,
    0x7fffffff80000000, 0xffffffff00000001, 0, 0xffffffffffffffff, 0xa42⟩,
  ⟨"cmove32_untaken_zero_extends_dst", [0x0f, 0x44, 0xc1], 0xdeadbeef12345678, 0x9999999987654321, 0, 0x202,
    0x0000000012345678, 0x9999999987654321, 0, 0xffffffffffffffff, 0x202⟩,
  ⟨"cmove32_taken_zero_extends_src", [0x0f, 0x44, 0xc1], 0xdeadbeef12345678, 0x9999999987654321, 0, 0x242,
    0x0000000087654321, 0x9999999987654321, 0, 0xffffffffffffffff, 0x242⟩,
  ⟨"inc64_max_pos_sets_of_preserves_cf", [0x48, 0xff, 0xc0], 0x7fffffffffffffff, 0, 0, 0x203,
    0x8000000000000000, 0, 0, 0xffffffffffffffff, 0xa97⟩,
  ⟨"dec64_min_neg_sets_of_preserves_cf", [0x48, 0xff, 0xc8], 0x8000000000000000, 0, 0, 0x202,
    0x7fffffffffffffff, 0, 0, 0xffffffffffffffff, 0xa16⟩,
  ⟨"bswap64_rax", [0x48, 0x0f, 0xc8], 0x0123456789abcdef, 0, 0, 0x202,
    0xefcdab8967452301, 0, 0, 0xffffffffffffffff, 0x202⟩,
  ⟨"bswap32_eax_zext", [0x0f, 0xc8], 0xdeadbeef01234567, 0, 0, 0x202,
    0x0000000067452301, 0, 0, 0xffffffffffffffff, 0x202⟩,
  ⟨"setb_al_preserves_upper56", [0x0f, 0x92, 0xc0], 0x11223344556677ff, 0, 0, 0x203,
    0x1122334455667701, 0, 0, 0xffffffffffffffff, 0x203⟩,
  ⟨"test64_clears_cf_of", [0x48, 0x85, 0xc8], 0xf0, 0x0f, 0, 0xad7,
    0xf0, 0x0f, 0, 0xffffffffffffffef, 0x246⟩,
  ⟨"cmp32_signed_overflow", [0x39, 0xc8], 0x80000000, 1, 0, 0x202,
    0x80000000, 1, 0, 0xffffffffffffffff, 0xa16⟩
]

def checkEdgeVector (v : EdgeVector) : Bool :=
  let gpr := ((Bank16.ofFn fun _ => (0 : UInt64)).set 0 v.rax).set 1 v.rcx |>.set 2 v.rdx
  let st : X86State := {
    pc := 0, gpr := gpr, ymm := Bank16.ofFn fun _ => Vec256.zero,
    cf := v.initFlags &&& 1 != 0, ofFlag := v.initFlags &&& 2048 != 0,
    zf := v.initFlags &&& 64 != 0, ymmDirty := false, halted := false,
    mem := fun _ => 0 }
  match run 4 v.code st { value := v.initFlags } with
  | .error _ => false
  | .ok (out, flags, pcs) =>
    pcs == [v.code.length] &&
    out.pc == v.code.length &&
    out.gpr.get 0 == v.expRax &&
    out.gpr.get 1 == v.expRcx &&
    out.gpr.get 2 == v.expRdx &&
    flags.valid == v.expValidMask &&
    (flags.value &&& flags.valid) == (v.expFlags &&& v.expValidMask)

theorem rflags_edge_vectors_verified :
    edgeCaseVectors.all checkEdgeVector = true := by decide +kernel


theorem verified_prefix_mutation_rejected :
    ∃ code : List UInt8, decodeX86Stream code = none ∧
      decodeX86Stream (code.drop 1) = some [⟨0, 1, .ret⟩] := by
  exact ⟨[0xf2, 0xc3], by decide +kernel⟩

theorem strict_code_inhabited :
    ∃ code prog, decodeX86Stream code = some prog := ⟨[0xc3], [⟨0, 1, .ret⟩], by decide +kernel⟩

#tooth_pair run_verified_code_is_strict vs verified_prefix_mutation_rejected
#verify_inhabited run_verified_code_is_strict strict_code_inhabited

end IsaCosim
