module
public import Lean
public import Qsag.ElfBinaryVerify
import all Qsag.ElfBinaryVerify
public section
open Lean Qsag

/-! Streaming JSON execution of the binary decoder and operational semantics.
Hex integers are most-significant digit first; memory and instruction strings
are bytes in address order. The adapter tracks all six arithmetic status flags.
`modeled_rflags_mask` excludes only architecturally undefined output bits;
all preserved flags and all registers/memory are compared exactly.
-/
namespace IsaCosim

def requireSome {α : Type} (message : String) : Option α → Except String α
  | some x => .ok x
  | none => .error message

def hexNat (width n : Nat) : String :=
  String.ofList ((List.range width).reverse.map fun i =>
    "0123456789abcdef".toList[(n >>> (4*i)) % 16]!)

def parseHex (s : String) : Except String Nat := do
  if s.isEmpty then throw "empty hexadecimal integer"
  s.toList.foldlM (fun n c => do
    let v ← if '0' ≤ c && c ≤ '9' then pure (c.toNat - 48)
      else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 87)
      else if 'A' ≤ c && c ≤ 'F' then pure (c.toNat - 55)
      else throw "invalid hexadecimal digit"
    pure (16*n + v)) 0

def bytes (s : String) : Except String (List UInt8) := do
  let cs := s.toList.toArray
  if cs.size % 2 != 0 then throw "odd hexadecimal byte string"
  (List.range (cs.size / 2)).mapM fun i => do
    return UInt8.ofNat (← parseHex (String.ofList [cs[2*i]!, cs[2*i+1]!]))

def fieldHex (j : Json) (key : String) : Except String Nat := do
  parseHex (← (← j.getObjVal? key).getStr?)

def bank (j : Json) (key : String) (digits : Nat) : Except String (Array Nat) := do
  let a ← (← j.getObjVal? key).getArr?
  if a.size != 16 then throw s!"{key}: expected 16 registers"
  a.mapM fun v => do
    let s ← v.getStr?
    if s.length != digits then throw s!"{key}: wrong register width"
    parseHex s

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
    let overflow := prod != signed r.toNat w
    return undefFlags (putFlags f 0x801 (if overflow then 0x801 else 0)) 0xd4
  if op == .andOp || op == .orOp || op == .xorOp then
    return undefFlags (putFlags f 0x8c5 (szp r.toNat w)) 0x10
  let sub := op == .sub || op == .sbb
  let carry := if op == .adc || op == .sbb then c else 0
  let exact := if sub then signed a w - signed b w - carry else signed a w + signed b w + carry
  let overflow := exact != signed r.toNat w
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

/-- Adapter corrections are intentionally local: this executable is a differential
oracle, not an extension of the shared proof theorems. -/
def step (d : DecodedInstr X86Instr) (st : X86State) (f : Flags) : Except String (X86State × Flags) := do
  match d.instr with
  | .aluRegReg op _ _ _ | .aluImm op _ _ _ | .aluLoad64 op _ _ =>
    if (op == .adc || op == .sbb) && f.valid &&& 1 == 0 then
      throw "arithmetic consumes undefined CF"
  | .adcx .. => if f.valid &&& 1 == 0 then throw "ADCX consumes undefined CF"
  | .adox .. => if f.valid &&& 2048 == 0 then throw "ADOX consumes undefined OF"
  | _ => pure ()
  let mut out := (stepX86 d st).1
  let mut flags := f
  match d.instr with
  | .aluRegReg op wide dst src => flags := aluFlags f op wide (st.gpr.get dst) (st.gpr.get src)
  | .aluImm op wide dst imm => flags := aluFlags f op wide (st.gpr.get dst) imm
  | .aluLoad64 op dst addr =>
    flags := aluFlags f op true (st.gpr.get dst) (readMem64 st.mem (evalX86Addr st (d.offset+d.byteLen) addr))
  | .negReg wide dst => flags := aluFlags f .sub wide 0 (st.gpr.get dst)
  | .incDec inc wide dst =>
    flags := putFlags (aluFlags f (if inc then .add else .sub) wide (st.gpr.get dst) 1) 1 f.value
    flags := { flags with valid := (flags.valid &&& 0xfffffffffffffffe) ||| (f.valid &&& 1) }
  | .mulOneOp sg wide src =>
    let w := if wide then 64 else 32
    let a := (st.gpr.get 0).toNat % 2^w
    let b := (st.gpr.get src).toNat % 2^w
    let prod := if sg then signed a w * signed b w else (a*b : Nat)
    let raw := (prod % (2^(2*w) : Nat)).toNat
    let lo := raw % 2^w
    let overflow := if sg then prod != signed lo w else raw / 2^w != 0
    out := { out with gpr := (out.gpr.set 0 (UInt64.ofNat lo)).set 2 (UInt64.ofNat (raw / 2^w)) }
    flags := undefFlags (putFlags f 0x801 (if overflow then 0x801 else 0)) 0xd4
  | .shiftImm kind wide dst cnt =>
    let w := if wide then 64 else 32
    let c := cnt % w
    if c != 0 then
      let a := (st.gpr.get dst).toNat % 2^w
      let r := (out.gpr.get dst).toNat
      let cf := match kind with
        | .shl => bit a (w-c) | .shr => bit a (c-1)
        | .rol => bit r 0 | .ror => bit r (w-1)
      let of := match kind with
        | .shl | .rol => bit r (w-1) != cf
        | .shr => bit a (w-1) | .ror => bit r (w-1) != bit r (w-2)
      flags := putFlags f 1 (if cf then 1 else 0)
      if kind == .shl || kind == .shr then
        flags := undefFlags (putFlags flags 0xc4 (szp r w)) 16
      flags := if c == 1 then putFlags flags 2048 (if of then 2048 else 0) else undefFlags flags 2048
  | .cmovcc cc wide dst src =>
    let v := if ← condition cc f then st.gpr.get src else st.gpr.get dst
    out := { out with gpr := out.gpr.set dst (maskGprWidth wide v) }
  | .jcc cc target =>
    out := { out with pc := if ← condition cc f then target.toNat else d.offset+d.byteLen }
  | .adcx .. => flags := putFlags f 1 (if out.cf then 1 else 0)
  | .adox .. => flags := putFlags f 2048 (if out.ofFlag then 2048 else 0)
  | .ret => throw "RET is a function boundary; compare before RET"
  | .divRem _ | .indirectBr _ | .varShiftCl _ _ | .vpgather _ _ =>
    throw "instruction is classified but lacks executable semantics"
  | _ => pure ()
  return ({ out with cf := bit flags.value 0, zf := bit flags.value 6, ofFlag := bit flags.value 11 }, flags)

/-- Small additional register encodings absent from the shared decoder: SAR,
SETcc, BSWAP and legacy PCLMULQDQ. Decode only the exact supported forms. -/
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
  if op == 0x0f && 0xc8 ≤ op2 && op2 ≤ 0xcf && bs.length ≥ p+2 then
    let dst := op2-0xc8+(rex%2)*8
    let n := if wide then 8 else 4
    let a := (st.gpr.get dst).toNat
    let r := (List.range n).foldl (fun v i => v*256 + ((a >>> (8*i)) &&& 255)) 0
    return some (.ok ({ st with pc := st.pc+p+2, gpr := st.gpr.set dst (UInt64.ofNat r) }, f, p+2))
  if op == 0xd1 && op2 ≥ 0xc0 && bs.length ≥ p+2 then
    let dst := op2%8+(rex%2)*8
    let digit := (op2/8)%8
    if digit == 7 then
      let w := if wide then 64 else 32
      let a := (st.gpr.get dst).toNat % 2^w
      let r := ((signed a w / 2) % (2^w : Nat)).toNat
      let f1 := undefFlags (putFlags f 0xc5 (szp r w + if bit a 0 then 1 else 0)) 16
      let flags := putFlags f1 2048 0
      return some (.ok ({ st with pc := st.pc+p+2, gpr := st.gpr.set dst (UInt64.ofNat r), cf := bit flags.value 0, zf := bit flags.value 6, ofFlag := false }, flags, p+2))
    let sk? : Option X86ShiftKind := match digit with
      | 0 => some .rol | 1 => some .ror | 4 => some .shl | 5 => some .shr | _ => none
    if let some sk := sk? then
      return some do
        let (out, flags) ← step ⟨st.pc, p+2, .shiftImm sk wide dst 1⟩ st f
        return (out, flags, p+2)
  if op == 0xc1 && op2 / 8 == 31 && bs.length ≥ p+3 then
    let dst := op2%8+(rex%2)*8
    let w := if wide then 64 else 32
    let c := modrm % w
    let a := (st.gpr.get dst).toNat % 2^w
    let r := ((signed a w / (2^c : Nat)) % (2^w : Nat)).toNat
    let flags := if c == 0 then f else
      let f := undefFlags (putFlags f 0xc5 (szp r w + if bit a (c-1) then 1 else 0)) 16
      if c == 1 then putFlags f 2048 0 else undefFlags f 2048
    return some (.ok ({ st with pc := st.pc+p+3, gpr := st.gpr.set dst (UInt64.ofNat r), cf := bit flags.value 0, zf := bit flags.value 6, ofFlag := bit flags.value 11 }, flags, p+3))
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

def run (fuel : Nat) (code : List UInt8) (st : X86State) (f : Flags) : Except String (X86State × Flags × Nat) :=
  if st.pc == code.length then pure (st, f, 0)
  else match fuel with
  | 0 => .error "instruction fuel exhausted"
  | n+1 => do
    let bs := code.drop st.pc
    let (out, flags) ← match extra bs st f with
      | some result => do let (out, flags, _) ← result; pure (out, flags)
      | none => do
        let d ← requireSome s!"unsupported instruction at {st.pc}" (decodeX86InstrAt st.pc bs)
        step d st f
    let (out, flags, count) ← run n code out flags
    pure (out, flags, count+1)

def evaluate (j : Json) : Except String Json := do
  let code ← bytes (← (← j.getObjVal? "insn_bytes_or_kernel").getStr?)
  let gs ← bank j "initial_gprs" 16
  let ys ← bank j "initial_ymms" 64
  let flags ← fieldHex j "initial_rflags"
  let base ← fieldHex j "stack_base"
  let mem := (← bytes (← (← j.getObjVal? "stack_mem").getStr?)).toArray
  let st : X86State := {
    pc := 0, gpr := Bank16.ofFn (fun i => UInt64.ofNat gs[i]!)
    ymm := Bank16.ofFn (fun i =>
      let n := ys[i]!
      ⟨UInt64.ofNat n, UInt64.ofNat (n >>> 64), UInt64.ofNat (n >>> 128), UInt64.ofNat (n >>> 192)⟩)
    cf := flags &&& 1 != 0, ofFlag := flags &&& 2048 != 0, zf := flags &&& 64 != 0
    ymmDirty := false, halted := false
    mem := fun a => if base ≤ a.toNat && a.toNat < base + mem.size then
      mem.getD (a.toNat - base) 0 else 0 }
  let (out, finalFlags, steps) ← run 100000 code st { value := flags }
  let f := finalFlags.value
  return Json.mkObj [
    ("steps", toJson steps),
    ("gprs", toJson ((List.range 16).map fun i => hexNat 16 (out.gpr.get i).toNat)),
    ("ymms", toJson ((List.range 16).map fun i =>
      let v := out.ymm.get i
      hexNat 16 v.w3.toNat ++ hexNat 16 v.w2.toNat ++ hexNat 16 v.w1.toNat ++ hexNat 16 v.w0.toNat)),
    ("rflags", toJson (hexNat 16 f)),
    ("modeled_rflags_mask", toJson (hexNat 16 finalFlags.valid)),
    ("stack_mem", toJson (String.join ((List.range mem.size).map fun i =>
      hexNat 2 (out.mem (UInt64.ofNat (base+i))).toNat)))]

/-- Architectural RFLAGS and GPR edge-case vectors covering `count = 0`, `count = 1`
(`0xC1` and `0xD1`), `count > 1`, `count = 32`, `count = 64`, `count = 65`, `0 * x`,
unsigned vs signed `(-1) * (-1)`, and `MIN_INT * (-1)`. -/
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
    0x8000000000000000, 0, 0, 0xffffffffffffffef, 0xa86⟩
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
  | .ok (out, flags, steps) =>
    steps == 1 &&
    out.gpr.get 0 == v.expRax &&
    out.gpr.get 1 == v.expRcx &&
    out.gpr.get 2 == v.expRdx &&
    flags.valid == v.expValidMask &&
    (flags.value &&& flags.valid) == (v.expFlags &&& v.expValidMask)

theorem rflags_edge_vectors_verified :
    edgeCaseVectors.all checkEdgeVector = true := by decide +kernel

end IsaCosim

def main (args : List String) : IO UInt32 := do
  if args == ["--self-test"] then
    for v in IsaCosim.edgeCaseVectors do
      if !IsaCosim.checkEdgeVector v then
        throw (IO.userError s!"edge-case vector failed: {v.name}")
    IO.println s!"isa-cosim self-test ok ({IsaCosim.edgeCaseVectors.length} RFLAGS edge vectors)"
    return 0
  if let ["--elf", path] := args then
    let data ← IO.FS.readBinFile path
    let source : Bytes := ⟨data.size, fun i => data[i]!⟩
    match extractExecutableElfFuncs source with
    | none => throw (IO.userError "invalid or unsupported ELF image")
    | some fs =>
      for f in fs do
        let decoded := if f.machine == elfMachineX86_64 then (decodeX86Stream f.code).isSome
          else if f.machine == elfMachineAArch64 then (decodeArm64Stream f.code).isSome else false
        IO.println ((Json.mkObj [("symbol", toJson f.name), ("bytes", toJson f.symSize),
          ("decoded", toJson decoded)]).compress)
      return 0
  let input ← match args with
    | [] => IO.getStdin
    | [path] => do pure (IO.FS.Stream.ofHandle (← IO.FS.Handle.mk path .read))
    | _ => throw (IO.userError "usage: isa-cosim [json-lines-file]")
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let result := Json.parse line >>= IsaCosim.evaluate
    let reply := match result with
      | .ok j => j
      | .error e => Json.mkObj [("error", toJson e)]
    output.putStrLn reply.compress
    output.flush
  return 0
