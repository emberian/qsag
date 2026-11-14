module
/-
# Qsag.ElfBinaryVerify — Compiled `.rlib` / `ELF64` Machine-Code Parser, 3-Way Constant-Time NI & ABI Checker

Pure Lean 4.35 binary verification engine (`0 sorry`, `0` custom axioms, `0 native_decide`, `LAW-M1`):
1. **Parser (`Qsag.ElfParse`):** the `GNU ar` + `ELF64` parser, its subslice theorems and the
   extraction certificates for both compiled archives live in `Qsag.ElfParse`; this file consumes
   the normalized slices through `x86_rlib_extracted_slices` / `aarch64_rlib_extracted_slices`.
2. **§3–§4 (`x86_64` & `AArch64` Machine-Code Decoders + Operational Semantics):** Decodes variable-length
   `x86_64` (`REX`, `VEX2`/`VEX3`, `0x66`/`0xF3`, `ModRM`/`SIB`, `AVX2`/`GFNI`/`VPCLMULQDQ`/`BMI2`/`ADX`)
   and fixed-width 32-bit little-endian `AArch64` (`ARMv8.4-A+SHA3+PMULL+DIT`) machine code directly from
   the compiled `.rlib` `.text` bytes, with explicit classification of forbidden variable-time opcodes.
3. **§5 (3-Way Hardware Constant-Time Noninterference + ABI Hygiene):** Relational abstract-origin +
   invariant verifier `checkElfFuncThreeWayNI` with machine-checked soundness theorem
   `checkElfFuncThreeWayNI_sound` (`PC-NI`, `Mem-NI`, `DOIT-NI`, callee-saved preservation, `vzeroupper`,
   and scratch vector register zeroization before `ret`), discharged via kernel `decide` across all 16
   `x86_64` and all 7 `aarch64` symbols (`23` symbols, `1,298` machine instructions), one kernel
   certificate per symbol.
4. **Mutation tests:** Negative checker tests accompany the structural and noninterference
   proofs. Input-output refinement of selected decoded kernels is in `Qsag.McRefine`.
-/

public import Qsag.Goldilocks
public import Qsag.Keccak
public import Qsag.BinaryTower
public import Qsag.CompiledRlibFixtures
public import Qsag.ElfFixtureSlices
public import Qsag.ElfParse
import all Qsag.ElfParse

public section
namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd

set_option autoImplicit false
set_option maxRecDepth 65536

/-! ## §3. Constant-Depth Register Banks & `x86_64` Machine-Code Decoder + Semantics -/

/-- Flat 16-slot register bank (`O(1)` WHNF depth, zero `Array` bounds proof obligations). -/
structure Bank16 (α : Type) where
  r0  : α
  r1  : α
  r2  : α
  r3  : α
  r4  : α
  r5  : α
  r6  : α
  r7  : α
  r8  : α
  r9  : α
  r10 : α
  r11 : α
  r12 : α
  r13 : α
  r14 : α
  r15 : α
  deriving DecidableEq, Repr

def Bank16.const {α : Type} (v : α) : Bank16 α :=
  ⟨v, v, v, v, v, v, v, v, v, v, v, v, v, v, v, v⟩

def Bank16.ofFn {α : Type} (f : Nat → α) : Bank16 α :=
  ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12, f 13, f 14, f 15⟩

def Bank16.get {α : Type} (b : Bank16 α) : Nat → α
  | 0  => b.r0  | 1  => b.r1  | 2  => b.r2  | 3  => b.r3
  | 4  => b.r4  | 5  => b.r5  | 6  => b.r6  | 7  => b.r7
  | 8  => b.r8  | 9  => b.r9  | 10 => b.r10 | 11 => b.r11
  | 12 => b.r12 | 13 => b.r13 | 14 => b.r14 | _  => b.r15

def Bank16.set {α : Type} (b : Bank16 α) (idx : Nat) (v : α) : Bank16 α :=
  match idx with
  | 0  => { b with r0  := v } | 1  => { b with r1  := v }
  | 2  => { b with r2  := v } | 3  => { b with r3  := v }
  | 4  => { b with r4  := v } | 5  => { b with r5  := v }
  | 6  => { b with r6  := v } | 7  => { b with r7  := v }
  | 8  => { b with r8  := v } | 9  => { b with r9  := v }
  | 10 => { b with r10 := v } | 11 => { b with r11 := v }
  | 12 => { b with r12 := v } | 13 => { b with r13 := v }
  | 14 => { b with r14 := v } | _  => { b with r15 := v }

def Bank16.allIdx {α : Type} (p : Nat → α → Bool) (b : Bank16 α) : Bool :=
  p 0 b.r0 && p 1 b.r1 && p 2 b.r2 && p 3 b.r3 &&
  p 4 b.r4 && p 5 b.r5 && p 6 b.r6 && p 7 b.r7 &&
  p 8 b.r8 && p 9 b.r9 && p 10 b.r10 && p 11 b.r11 &&
  p 12 b.r12 && p 13 b.r13 && p 14 b.r14 && p 15 b.r15

/-- Flat 32-slot register bank for `AArch64` `x0..x30` and `v0..v31`. -/
structure Bank32 (α : Type) where
  lo : Bank16 α
  hi : Bank16 α
  deriving DecidableEq, Repr

def Bank32.const {α : Type} (v : α) : Bank32 α :=
  ⟨Bank16.const v, Bank16.const v⟩

def Bank32.ofFn {α : Type} (f : Nat → α) : Bank32 α :=
  ⟨Bank16.ofFn f, Bank16.ofFn (fun i => f (i + 16))⟩

def Bank32.get {α : Type} (b : Bank32 α) (idx : Nat) : α :=
  if idx < 16 then b.lo.get idx else b.hi.get (idx - 16)

def Bank32.set {α : Type} (b : Bank32 α) (idx : Nat) (v : α) : Bank32 α :=
  if idx < 16 then { b with lo := b.lo.set idx v } else { b with hi := b.hi.set (idx - 16) v }

def Bank32.allIdx {α : Type} (p : Nat → α → Bool) (b : Bank32 α) : Bool :=
  b.lo.allIdx p && b.hi.allIdx (fun i v => p (i + 16) v)

/-- 128-bit SIMD register (`xmm` / NEON `q` / `v.16b`). -/
structure Vec128 where
  w0 : UInt64
  w1 : UInt64
  deriving DecidableEq, Repr

def Vec128.zero : Vec128 := ⟨0, 0⟩

/-- 256-bit SIMD register (`ymm0..ymm15`). -/
structure Vec256 where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
  deriving DecidableEq, Repr

def Vec256.zero : Vec256 := ⟨0, 0, 0, 0⟩

/-- Hardware leakage observation emitted at each executed machine instruction (`§5`). -/
structure StepObs where
  pc : Nat
  memAccesses : List (UInt64 × Nat)
  isDoitSafe : Bool
  deriving DecidableEq, Repr

/-- Decoded machine instruction paired with its exact byte offset and byte length in `.text`. -/
structure DecodedInstr (Instr : Type) where
  offset : Nat
  byteLen : Nat
  instr : Instr
  deriving DecidableEq, Repr

def signExt8To64 (b : UInt8) : UInt64 :=
  if b.toNat < 128 then UInt64.ofNat b.toNat else 0 - UInt64.ofNat (256 - b.toNat)

def signExt32To64 (w : UInt32) : UInt64 :=
  if w.toNat < 0x80000000 then UInt64.ofNat w.toNat else 0 - UInt64.ofNat (0x100000000 - w.toNat)

def signExt8ToInt (b : UInt8) : Int :=
  if b.toNat < 128 then Int.ofNat b.toNat else Int.ofNat b.toNat - 256

def signExt32ToInt (w : UInt32) : Int :=
  if w.toNat < 0x80000000 then Int.ofNat w.toNat else Int.ofNat w.toNat - 0x100000000

/-- Effective address modes in `x86_64` `ModRM` + `SIB` decoding. -/
inductive X86MemAddr where
  | baseDisp (base : Nat) (disp : UInt64)
  | absDisp (disp : UInt64)
  | ripDisp (disp : UInt64)
  | indexedSib (baseOpt : Option Nat) (idx : Nat) (scaleShift : Nat) (disp : UInt64)
  deriving DecidableEq, Repr

inductive X86AluOp where
  | add | adc | sub | sbb | andOp | orOp | xorOp | imul2
  deriving DecidableEq, Repr

inductive X86ShiftKind where
  | shl | shr | rol | ror
  deriving DecidableEq, Repr

inductive X86VecBinOp where
  | vpxor | vpand | vpandn | vpor | vpaddb | vpcmpgtb | vpshufb | vgf2p8mulb
  deriving DecidableEq, Repr

inductive X86VecShiftKind where
  | vpsllq | vpsrlq | vpsrlw | vpslldq | vpsrldq
  | vpshufd | vextracti128
  deriving DecidableEq, Repr

/-- Decoded `x86_64` instruction covering all 16 `qsag_asm` `.rlib` kernels + forbidden variable-time classes. -/
inductive X86Instr where
  | nop
  | mfence
  | pushReg (reg : Nat)
  | popReg (reg : Nat)
  | ret
  | movRegReg (is64 : Bool) (dst src : Nat)
  | movImm (is64 : Bool) (dst : Nat) (imm : UInt64)
  | loadGpr (widthBytes : Nat) (is64 : Bool) (dst : Nat) (addr : X86MemAddr)
  | storeGpr (widthBytes : Nat) (src : Nat) (addr : X86MemAddr)
  | aluRegReg (op : X86AluOp) (is64 : Bool) (dst src : Nat)
  | aluLoad64 (op : X86AluOp) (dst : Nat) (addr : X86MemAddr)
  | aluImm (op : X86AluOp) (is64 : Bool) (dst : Nat) (imm : UInt64)
  | incDec (isInc : Bool) (is64 : Bool) (dst : Nat)
  | negReg (is64 : Bool) (dst : Nat)
  | mulOneOp (isSigned : Bool) (is64 : Bool) (src : Nat)
  | shiftImm (kind : X86ShiftKind) (is64 : Bool) (dst : Nat) (cnt : Nat)
  | cmovcc (cc : Nat) (is64 : Bool) (dst src : Nat)
  | mulx (hiDst loDst src : Nat)
  | adcx (dst src : Nat)
  | adox (dst src : Nat)
  | jcc (cc : Nat) (targetPc : Int)
  | jmpRel (targetPc : Int)
  | indirectBr (digit : Nat)
  | divRem (isSigned : Bool)
  | varShiftCl (digit : Nat) (dst : Nat)
  | vzeroupper
  | vzeroall
  | vload (is256 : Bool) (dst : Nat) (addr : X86MemAddr)
  | vstore (is256 : Bool) (src : Nat) (addr : X86MemAddr)
  | vmovGprToXmm (is64 : Bool) (dstVec srcGpr : Nat)
  | vpbroadcast (isQword : Bool) (dst srcVec : Nat)
  | vpbroadcastLoad64 (dst : Nat) (addr : X86MemAddr)
  | vbinOp (op : X86VecBinOp) (is256 : Bool) (dst src1 src2 : Nat)
  | vpxorLoad256 (dst src1 : Nat) (addr : X86MemAddr)
  | vpxorLoad128 (dst src1 : Nat) (addr : X86MemAddr)
  | vshiftImm (kind : X86VecShiftKind) (is256 : Bool) (dst src : Nat) (imm : Nat)
  | vpclmulqdq (is256 : Bool) (dst src1 src2 : Nat) (imm : UInt8)
  | vgf2p8affineqb (is256 : Bool) (dst src1 src2 : Nat) (imm : UInt8)
  | vperm2i128 (dst src1 src2 : Nat) (imm : UInt8)
  | vpgather (op : UInt8) (addr : X86MemAddr)
  deriving DecidableEq, Repr

/-- Decoded `ModRM` + optional `SIB` + optional `disp8`/`disp32` operand. -/
inductive ModRMOperand where
  | reg (r : Nat)
  | mem (addr : X86MemAddr)
  deriving DecidableEq, Repr

def readU32LE? : List UInt8 → Option UInt32
  | b0 :: b1 :: b2 :: b3 :: _ =>
    some (b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24))
  | _ => none

def readU64LE? : List UInt8 → Option UInt64
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: _ =>
    some (b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24) |||
          (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) ||| (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56))
  | _ => none

def decodeX86ModRM (bs : List UInt8) (rexR rexX rexB : Nat) : Option (Nat × ModRMOperand × Nat) := do
  let m ← bs[0]?
  let mod := (m.toNat >>> 6) &&& 3
  let regField := ((m.toNat >>> 3) &&& 7) + rexR * 8
  let rmLow := m.toNat &&& 7
  if mod == 3 then
    pure (regField, .reg (rmLow + rexB * 8), 1)
  else if rmLow == 4 then
    let sib ← bs[1]?
    let scale := (sib.toNat >>> 6) &&& 3
    let idxLow := (sib.toNat >>> 3) &&& 7
    let baseLow := sib.toNat &&& 7
    let idxReg := idxLow + rexX * 8
    let hasIdx := !(idxLow == 4 && rexX == 0)
    if mod == 0 && baseLow == 5 then
      let disp32 ← readU32LE? (bs.drop 2)
      let disp := signExt32To64 disp32
      let addr := if hasIdx then .indexedSib none idxReg scale disp else .absDisp disp
      pure (regField, .mem addr, 6)
    else if mod == 0 then
      let baseReg := baseLow + rexB * 8
      let addr := if hasIdx then .indexedSib (some baseReg) idxReg scale 0 else .baseDisp baseReg 0
      pure (regField, .mem addr, 2)
    else if mod == 1 then
      let d8 ← bs[2]?
      let disp := signExt8To64 d8
      let baseReg := baseLow + rexB * 8
      let addr := if hasIdx then .indexedSib (some baseReg) idxReg scale disp else .baseDisp baseReg disp
      pure (regField, .mem addr, 3)
    else
      let d32 ← readU32LE? (bs.drop 2)
      let disp := signExt32To64 d32
      let baseReg := baseLow + rexB * 8
      let addr := if hasIdx then .indexedSib (some baseReg) idxReg scale disp else .baseDisp baseReg disp
      pure (regField, .mem addr, 6)
  else if mod == 0 && rmLow == 5 then
    let d32 ← readU32LE? (bs.drop 1)
    pure (regField, .mem (.ripDisp (signExt32To64 d32)), 5)
  else if mod == 0 then
    pure (regField, .mem (.baseDisp (rmLow + rexB * 8) 0), 1)
  else if mod == 1 then
    let d8 ← bs[1]?
    pure (regField, .mem (.baseDisp (rmLow + rexB * 8) (signExt8To64 d8)), 2)
  else
    let d32 ← readU32LE? (bs.drop 1)
    pure (regField, .mem (.baseDisp (rmLow + rexB * 8) (signExt32To64 d32)), 5)

def stripX86LegacyPrefixes : Nat → List UInt8 → Bool → Bool → Bool → (Nat × List UInt8 × Bool × Bool × Bool)
  | 0, bs, p66, pf2, pf3 => (0, bs, p66, pf2, pf3)
  | fuel + 1, b :: rest, p66, pf2, pf3 =>
    if b == 0x66 then
      let (k, r, q66, qf2, qf3) := stripX86LegacyPrefixes fuel rest true pf2 pf3
      (k + 1, r, q66, qf2, qf3)
    else if b == 0xF2 then
      let (k, r, q66, qf2, qf3) := stripX86LegacyPrefixes fuel rest p66 true pf3
      (k + 1, r, q66, qf2, qf3)
    else if b == 0xF3 then
      let (k, r, q66, qf2, qf3) := stripX86LegacyPrefixes fuel rest p66 pf2 true
      (k + 1, r, q66, qf2, qf3)
    else if b == 0x2E then
      let (k, r, q66, qf2, qf3) := stripX86LegacyPrefixes fuel rest p66 pf2 pf3
      (k + 1, r, q66, qf2, qf3)
    else
      (0, b :: rest, p66, pf2, pf3)
  | _, [], p66, pf2, pf3 => (0, [], p66, pf2, pf3)

def decodeAluDigit? : Nat → Option X86AluOp
  | 0 => some .add
  | 1 => some .orOp
  | 2 => some .adc
  | 3 => some .sbb
  | 4 => some .andOp
  | 5 => some .sub
  | 6 => some .xorOp
  | _ => none

def decodeShiftDigit? : Nat → Option X86ShiftKind
  | 0 => some .rol
  | 1 => some .ror
  | 4 => some .shl
  | 5 => some .shr
  | _ => none

/-- Decode one variable-length `x86_64` instruction at byte offset `pc`. -/
def decodeX86InstrAt (pc : Nat) (bs : List UInt8) : Option (DecodedInstr X86Instr) := do
  let (prefLen, rest0, p66, _pf2, pf3) := stripX86LegacyPrefixes 4 bs false false false
  let b0 ← rest0[0]?
  let (rexLen, rex, rest) :=
    if 0x40 ≤ b0 && b0 ≤ 0x4F then (1, b0.toNat, rest0.drop 1) else (0, 0, rest0)
  let rexW := ((rex >>> 3) &&& 1) == 1
  let rexR := (rex >>> 2) &&& 1
  let rexX := (rex >>> 1) &&& 1
  let rexB := rex &&& 1
  let op ← rest[0]?
  let hdrLen := prefLen + rexLen
  -- Scalar 16-bit partial writes are not represented by the Boolean width model.
  if p66 && !rexW && op != 0x0F then return ← none
  if op == 0xC5 || op == 0xC4 then
    let (vexLen, vexR, vexX, vexB, mmmmm, vexW, vvvReg, vexL, pp, afterVex) ←
      if op == 0xC5 then do
        let v1 ← rest[1]?
        let r := 1 - ((v1.toNat >>> 7) &&& 1)
        let vvv := 15 - ((v1.toNat >>> 3) &&& 0xF)
        let l := ((v1.toNat >>> 2) &&& 1) == 1
        let p := v1.toNat &&& 3
        pure (2, r, 0, 0, 1, false, vvv, l, p, rest.drop 2)
      else do
        let v1 ← rest[1]?
        let v2 ← rest[2]?
        let r := 1 - ((v1.toNat >>> 7) &&& 1)
        let x := 1 - ((v1.toNat >>> 6) &&& 1)
        let b := 1 - ((v1.toNat >>> 5) &&& 1)
        let m := v1.toNat &&& 0x1F
        let w := ((v2.toNat >>> 7) &&& 1) == 1
        let vvv := 15 - ((v2.toNat >>> 3) &&& 0xF)
        let l := ((v2.toNat >>> 2) &&& 1) == 1
        let p := v2.toNat &&& 3
        pure (3, r, x, b, m, w, vvv, l, p, rest.drop 3)
    let vop ← afterVex[0]?
    if mmmmm == 1 && pp == 0 && vop == 0x77 then
      pure ⟨pc, hdrLen + vexLen + 1, if vexL then .vzeroall else .vzeroupper⟩
    else
      let (regF, opnd, mLen) ← decodeX86ModRM (afterVex.drop 1) vexR vexX vexB
      let baseLen := hdrLen + vexLen + 1 + mLen
      if mmmmm == 2 && pp == 1 && (vop == 0x90 || vop == 0x91 || vop == 0x92 || vop == 0x93) then
        match opnd with
        | .mem addr => pure ⟨pc, baseLen, .vpgather vop addr⟩
        | .reg _ => none
      else if mmmmm == 2 && pp == 3 && vexW && vop == 0xF6 then
        match opnd with
        | .reg src => pure ⟨pc, baseLen, .mulx regF vvvReg src⟩
        | .mem _ => none
      else if mmmmm == 1 && (pp == 1 || pp == 2) && vop == 0x6F then
        match opnd with
        | .mem addr => pure ⟨pc, baseLen, .vload vexL regF addr⟩
        | .reg _ => none
      else if mmmmm == 1 && (pp == 1 || pp == 2) && vop == 0x7F then
        match opnd with
        | .mem addr => pure ⟨pc, baseLen, .vstore vexL regF addr⟩
        | .reg _ => none
      else if mmmmm == 1 && pp == 1 && vop == 0x6E then
        match opnd with
        | .reg srcGpr => pure ⟨pc, baseLen, .vmovGprToXmm vexW regF srcGpr⟩
        | .mem _ => none
      else if mmmmm == 2 && pp == 1 && (vop == 0x59 || vop == 0x78) then
        match opnd with
        | .reg srcVec => pure ⟨pc, baseLen, .vpbroadcast (vop == 0x59) regF srcVec⟩
        | .mem addr =>
          if vop == 0x59 && vexL then pure ⟨pc, baseLen, .vpbroadcastLoad64 regF addr⟩ else none
      else if mmmmm == 1 && pp == 1 && vop == 0xEF then
        match opnd with
        | .reg src2 => pure ⟨pc, baseLen, .vbinOp .vpxor vexL regF vvvReg src2⟩
        | .mem addr =>
          pure ⟨pc, baseLen, if vexL then .vpxorLoad256 regF vvvReg addr else .vpxorLoad128 regF vvvReg addr⟩
      else if mmmmm == 1 && pp == 1 && (vop == 0xDB || vop == 0xDF || vop == 0xEB || vop == 0xFC || vop == 0x64) then
        match opnd with
        | .reg src2 =>
          let bop : X86VecBinOp :=
            if vop == 0xDB then .vpand
            else if vop == 0xDF then .vpandn
            else if vop == 0xEB then .vpor
            else if vop == 0xFC then .vpaddb
            else .vpcmpgtb
          pure ⟨pc, baseLen, .vbinOp bop vexL regF vvvReg src2⟩
        | .mem _ => none
      else if mmmmm == 2 && pp == 1 && (vop == 0x00 || vop == 0xCF) then
        match opnd with
        | .reg src2 =>
          let bop : X86VecBinOp := if vop == 0x00 then .vpshufb else .vgf2p8mulb
          pure ⟨pc, baseLen, .vbinOp bop vexL regF vvvReg src2⟩
        | .mem _ => none
      else if mmmmm == 1 && pp == 1 && vop == 0x70 then
        let imm ← afterVex[1 + mLen]?
        match opnd with
        | .reg src => pure ⟨pc, baseLen + 1, .vshiftImm .vpshufd vexL regF src imm.toNat⟩
        | .mem _ => none
      else if mmmmm == 3 && pp == 1 && vexL && vop == 0x39 then
        let imm ← afterVex[1 + mLen]?
        match opnd with
        | .reg dst => pure ⟨pc, baseLen + 1, .vshiftImm .vextracti128 false dst regF imm.toNat⟩
        | .mem _ => none
      else if mmmmm == 1 && pp == 1 && (vop == 0x71 || vop == 0x73) then
        let imm8 ← afterVex[1 + mLen]?
        let digit := regF &&& 7
        match opnd with
        | .reg srcVec =>
          let sk? : Option X86VecShiftKind :=
            if vop == 0x71 && digit == 2 then some .vpsrlw
            else if vop == 0x73 && digit == 2 then some .vpsrlq
            else if vop == 0x73 && digit == 6 then some .vpsllq
            else if vop == 0x73 && digit == 3 then some .vpsrldq
            else if vop == 0x73 && digit == 7 then some .vpslldq
            else none
          let sk ← sk?
          pure ⟨pc, baseLen + 1, .vshiftImm sk vexL vvvReg srcVec imm8.toNat⟩
        | .mem _ => none
      else if mmmmm == 3 && pp == 1 && (vop == 0x44 || vop == 0xCE || vop == 0x46) then
        let imm8 ← afterVex[1 + mLen]?
        match opnd with
        | .reg src2 =>
          if vop == 0x44 then
            pure ⟨pc, baseLen + 1, .vpclmulqdq vexL regF vvvReg src2 imm8⟩
          else if vop == 0xCE then
            pure ⟨pc, baseLen + 1, .vgf2p8affineqb vexL regF vvvReg src2 imm8⟩
          else
            pure ⟨pc, baseLen + 1, .vperm2i128 regF vvvReg src2 imm8⟩
        | .mem _ => none
      else
        none
  else if op == 0x90 && rexB == 0 && !p66 then
    pure ⟨pc, hdrLen + 1, .nop⟩
  else if op == 0xC3 then
    pure ⟨pc, hdrLen + 1, .ret⟩
  else if 0x50 ≤ op && op ≤ 0x57 then
    pure ⟨pc, hdrLen + 1, .pushReg ((op.toNat - 0x50) + rexB * 8)⟩
  else if 0x58 ≤ op && op ≤ 0x5F then
    pure ⟨pc, hdrLen + 1, .popReg ((op.toNat - 0x58) + rexB * 8)⟩
  else if 0xB8 ≤ op && op ≤ 0xBF then
    let dst := (op.toNat - 0xB8) + rexB * 8
    if rexW then
      let imm64 ← readU64LE? (rest.drop 1)
      pure ⟨pc, hdrLen + 9, .movImm true dst imm64⟩
    else
      let imm32 ← readU32LE? (rest.drop 1)
      pure ⟨pc, hdrLen + 5, .movImm false dst (UInt64.ofNat imm32.toNat)⟩
  else if op == 0x89 then
    let (src, opnd, mLen) ← decodeX86ModRM (rest.drop 1) rexR rexX rexB
    match opnd with
    | .reg dst => pure ⟨pc, hdrLen + 1 + mLen, .movRegReg rexW dst src⟩
    | .mem addr =>
      if rexW then pure ⟨pc, hdrLen + 1 + mLen, .storeGpr 8 src addr⟩ else none
  else if op == 0x88 then
    let (src, opnd, mLen) ← decodeX86ModRM (rest.drop 1) rexR rexX rexB
    match opnd with
    | .mem addr => pure ⟨pc, hdrLen + 1 + mLen, .storeGpr 1 src addr⟩
    | .reg _ => none
  else if op == 0x8B then
    let (dst, opnd, mLen) ← decodeX86ModRM (rest.drop 1) rexR rexX rexB
    match opnd with
    | .reg src => pure ⟨pc, hdrLen + 1 + mLen, .movRegReg rexW dst src⟩
    | .mem addr =>
      if rexW then pure ⟨pc, hdrLen + 1 + mLen, .loadGpr 8 true dst addr⟩ else none
  else if op == 0x01 || op == 0x09 || op == 0x11 || op == 0x19 || op == 0x21 || op == 0x29 || op == 0x31 then
    let (src, opnd, mLen) ← decodeX86ModRM (rest.drop 1) rexR rexX rexB
    let aop : X86AluOp :=
      if op == 0x01 then .add
      else if op == 0x09 then .orOp
      else if op == 0x11 then .adc
      else if op == 0x19 then .sbb
      else if op == 0x21 then .andOp
      else if op == 0x29 then .sub
      else .xorOp
    match opnd with
    | .reg dst => pure ⟨pc, hdrLen + 1 + mLen, .aluRegReg aop rexW dst src⟩
    | .mem _ => none
  else if op == 0x33 then
    let (dst, opnd, mLen) ← decodeX86ModRM (rest.drop 1) rexR rexX rexB
    match opnd with
    | .reg src => pure ⟨pc, hdrLen + 1 + mLen, .aluRegReg .xorOp rexW dst src⟩
    | .mem addr =>
      if rexW then pure ⟨pc, hdrLen + 1 + mLen, .aluLoad64 .xorOp dst addr⟩ else none
  else if op == 0x81 then
    let (regF, opnd, mLen) ← decodeX86ModRM (rest.drop 1) rexR rexX rexB
    let aop ← decodeAluDigit? (regF &&& 7)
    let imm32 ← readU32LE? (rest.drop (1 + mLen))
    match opnd with
    | .reg dst =>
      let imm := if rexW then signExt32To64 imm32 else UInt64.ofNat imm32.toNat
      pure ⟨pc, hdrLen + 1 + mLen + 4, .aluImm aop rexW dst imm⟩
    | .mem _ => none
  else if op == 0x83 then
    let (regF, opnd, mLen) ← decodeX86ModRM (rest.drop 1) rexR rexX rexB
    let aop ← decodeAluDigit? (regF &&& 7)
    let imm8 ← rest[1 + mLen]?
    match opnd with
    | .reg dst =>
      let imm := signExt8To64 imm8
      pure ⟨pc, hdrLen + 1 + mLen + 1, .aluImm aop rexW dst imm⟩
    | .mem _ => none
  else if op == 0xC1 then
    let (regF, opnd, mLen) ← decodeX86ModRM (rest.drop 1) rexR rexX rexB
    let sk ← decodeShiftDigit? (regF &&& 7)
    let imm8 ← rest[1 + mLen]?
    match opnd with
    | .reg dst => pure ⟨pc, hdrLen + 1 + mLen + 1, .shiftImm sk rexW dst imm8.toNat⟩
    | .mem _ => none
  else if op == 0xD3 then
    let (regF, opnd, mLen) ← decodeX86ModRM (rest.drop 1) rexR rexX rexB
    match opnd with
    | .reg dst => pure ⟨pc, hdrLen + 1 + mLen, .varShiftCl (regF &&& 7) dst⟩
    | .mem _ => none
  else if op == 0xF7 then
    let (regF, opnd, mLen) ← decodeX86ModRM (rest.drop 1) rexR rexX rexB
    let digit := regF &&& 7
    if digit == 6 || digit == 7 then
      pure ⟨pc, hdrLen + 1 + mLen, .divRem (digit == 7)⟩
    else
      match opnd with
      | .reg r =>
        if digit == 3 then pure ⟨pc, hdrLen + 1 + mLen, .negReg rexW r⟩
        else if digit == 4 || digit == 5 then pure ⟨pc, hdrLen + 1 + mLen, .mulOneOp (digit == 5) rexW r⟩
        else none
      | .mem _ => none
  else if op == 0xFF then
    let (regF, opnd, mLen) ← decodeX86ModRM (rest.drop 1) rexR rexX rexB
    let digit := regF &&& 7
    if digit == 2 || digit == 4 then
      pure ⟨pc, hdrLen + 1 + mLen, .indirectBr digit⟩
    else
      match opnd with
      | .reg dst =>
        if digit == 0 || digit == 1 then
          pure ⟨pc, hdrLen + 1 + mLen, .incDec (digit == 0) rexW dst⟩
        else none
      | .mem _ => none
  else if 0x70 ≤ op && op ≤ 0x7F then
    if op < 0x72 || 0x75 < op then return ← none
    let rel8 ← rest[1]?
    let nextPc := Int.ofNat (pc + hdrLen + 2)
    pure ⟨pc, hdrLen + 2, .jcc (op.toNat - 0x70) (nextPc + signExt8ToInt rel8)⟩
  else if op == 0xEB then
    let rel8 ← rest[1]?
    let nextPc := Int.ofNat (pc + hdrLen + 2)
    pure ⟨pc, hdrLen + 2, .jmpRel (nextPc + signExt8ToInt rel8)⟩
  else if op == 0xE9 then
    let rel32 ← readU32LE? (rest.drop 1)
    let nextPc := Int.ofNat (pc + hdrLen + 5)
    pure ⟨pc, hdrLen + 5, .jmpRel (nextPc + signExt32ToInt rel32)⟩
  else if op == 0x0F then
    let op2 ← rest[1]?
    if op2 == 0x1F then
      let (_, _, mLen) ← decodeX86ModRM (rest.drop 2) rexR rexX rexB
      pure ⟨pc, hdrLen + 2 + mLen, .nop⟩
    else if op2 == 0xAE then
      let m ← rest[2]?
      if m == 0xF0 then pure ⟨pc, hdrLen + 3, .mfence⟩ else none
    else if op2 == 0xB6 then
      if p66 && !rexW then return ← none
      let (dst, opnd, mLen) ← decodeX86ModRM (rest.drop 2) rexR rexX rexB
      match opnd with
      | .mem addr => pure ⟨pc, hdrLen + 2 + mLen, .loadGpr 1 rexW dst addr⟩
      | .reg _ => none
    else if op2 == 0xAF then
      if p66 && !rexW then return ← none
      let (dst, opnd, mLen) ← decodeX86ModRM (rest.drop 2) rexR rexX rexB
      match opnd with
      | .reg src => pure ⟨pc, hdrLen + 2 + mLen, .aluRegReg .imul2 rexW dst src⟩
      | .mem _ => none
    else if 0x40 ≤ op2 && op2 ≤ 0x4F then
      if op2 < 0x42 || 0x45 < op2 || (p66 && !rexW) then return ← none
      let (dst, opnd, mLen) ← decodeX86ModRM (rest.drop 2) rexR rexX rexB
      match opnd with
      | .reg src => pure ⟨pc, hdrLen + 2 + mLen, .cmovcc (op2.toNat - 0x40) rexW dst src⟩
      | .mem _ => none
    else if 0x80 ≤ op2 && op2 ≤ 0x8F then
      if op2 < 0x82 || 0x85 < op2 then return ← none
      let rel32 ← readU32LE? (rest.drop 2)
      let nextPc := Int.ofNat (pc + hdrLen + 6)
      pure ⟨pc, hdrLen + 6, .jcc (op2.toNat - 0x80) (nextPc + signExt32ToInt rel32)⟩
    else if op2 == 0x38 then
      let op3 ← rest[2]?
      if op3 == 0xF6 && rexW then
        let (dst, opnd, mLen) ← decodeX86ModRM (rest.drop 3) rexR rexX rexB
        match opnd with
        | .reg src =>
          if p66 && !pf3 then pure ⟨pc, hdrLen + 3 + mLen, .adcx dst src⟩
          else if pf3 && !p66 then pure ⟨pc, hdrLen + 3 + mLen, .adox dst src⟩
          else none
        | .mem _ => none
      else none
    else none
  else
    none

def dropExact? : Nat → List UInt8 → Option (List UInt8)
  | 0, bs => some bs
  | _ + 1, [] => none
  | k + 1, _ :: rest => dropExact? k rest

def decodeX86Loop : Nat → Nat → List UInt8 → List (DecodedInstr X86Instr) → Option (List (DecodedInstr X86Instr))
  | _, _, [], acc => some acc.reverse
  | 0, _, _ :: _, _ => none
  | fuel + 1, pc, bs, acc =>
    match decodeX86InstrAt pc bs with
    | none => none
    | some d =>
      if d.byteLen == 0 then none
      else match dropExact? d.byteLen bs with
      | none => none
      | some rest => decodeX86Loop fuel (pc + d.byteLen) rest (d :: acc)

/-- Decode an entire `.text` symbol byte slice into an `x86_64` instruction stream. -/
def decodeX86Stream (code : List UInt8) : Option (List (DecodedInstr X86Instr)) :=
  decodeX86Loop (lenTR code) 0 code []

/-- Concrete `x86_64` machine state (`RAX..R15`, `YMM0..YMM15`, `CF/OF/ZF`, `ymmDirty`, byte memory). -/
structure X86State where
  pc : Nat
  gpr : Bank16 UInt64
  ymm : Bank16 Vec256
  cf : Bool
  ofFlag : Bool
  zf : Bool
  ymmDirty : Bool
  halted : Bool
  mem : UInt64 → UInt8

def readMem64 (mem : UInt64 → UInt8) (addr : UInt64) : UInt64 :=
  (mem addr).toUInt64 |||
  ((mem (addr + 1)).toUInt64 <<< 8) |||
  ((mem (addr + 2)).toUInt64 <<< 16) |||
  ((mem (addr + 3)).toUInt64 <<< 24) |||
  ((mem (addr + 4)).toUInt64 <<< 32) |||
  ((mem (addr + 5)).toUInt64 <<< 40) |||
  ((mem (addr + 6)).toUInt64 <<< 48) |||
  ((mem (addr + 7)).toUInt64 <<< 56)

def writeMem8 (mem : UInt64 → UInt8) (addr : UInt64) (b : UInt8) : UInt64 → UInt8 :=
  fun a => if a == addr then b else mem a

def writeMem64 (mem : UInt64 → UInt8) (addr : UInt64) (v : UInt64) : UInt64 → UInt8 :=
  let m0 := writeMem8 mem addr v.toUInt8
  let m1 := writeMem8 m0 (addr + 1) (v >>> 8).toUInt8
  let m2 := writeMem8 m1 (addr + 2) (v >>> 16).toUInt8
  let m3 := writeMem8 m2 (addr + 3) (v >>> 24).toUInt8
  let m4 := writeMem8 m3 (addr + 4) (v >>> 32).toUInt8
  let m5 := writeMem8 m4 (addr + 5) (v >>> 40).toUInt8
  let m6 := writeMem8 m5 (addr + 6) (v >>> 48).toUInt8
  writeMem8 m6 (addr + 7) (v >>> 56).toUInt8

def readMem128 (mem : UInt64 → UInt8) (addr : UInt64) : Vec128 :=
  ⟨readMem64 mem addr, readMem64 mem (addr + 8)⟩

def writeMem128 (mem : UInt64 → UInt8) (addr : UInt64) (v : Vec128) : UInt64 → UInt8 :=
  writeMem64 (writeMem64 mem addr v.w0) (addr + 8) v.w1

def readMem256 (mem : UInt64 → UInt8) (addr : UInt64) : Vec256 :=
  ⟨readMem64 mem addr, readMem64 mem (addr + 8), readMem64 mem (addr + 16), readMem64 mem (addr + 24)⟩

def writeMem256 (mem : UInt64 → UInt8) (addr : UInt64) (v : Vec256) : UInt64 → UInt8 :=
  let m0 := writeMem64 mem addr v.w0
  let m1 := writeMem64 m0 (addr + 8) v.w1
  let m2 := writeMem64 m1 (addr + 16) v.w2
  writeMem64 m2 (addr + 24) v.w3

def evalX86Addr (s : X86State) (nextPc : Nat) : X86MemAddr → UInt64
  | .baseDisp base disp => s.gpr.get base + disp
  | .absDisp disp => disp
  | .ripDisp disp => UInt64.ofNat nextPc + disp
  | .indexedSib baseOpt idx scale disp =>
    let bVal := match baseOpt with | some b => s.gpr.get b | none => 0
    bVal + (s.gpr.get idx <<< UInt64.ofNat scale) + disp

def maskGprWidth (is64 : Bool) (v : UInt64) : UInt64 :=
  if is64 then v else v &&& 0xFFFFFFFF

/-- Parity of an 8-bit byte (`GFNI` `VGF2P8AFFINEQB` dot-product helper). -/
def parityByte (x : UInt8) : UInt8 :=
  let y := x ^^^ (x >>> 4)
  let z := y ^^^ (y >>> 2)
  (z ^^^ (z >>> 1)) &&& 1

/-- Exact Intel SDM `VGF2P8AFFINEQB` byte operation: $M \cdot x \oplus b$ over $\mathbb{F}_2^8$. -/
def gfniAffineByte (x : UInt8) (mat : UInt64) (imm : UInt8) : UInt8 :=
  let bitAt (i : Nat) : UInt8 :=
    let row := (mat >>> UInt64.ofNat ((7 - i) * 8)).toUInt8
    ((parityByte (x &&& row)) ^^^ ((imm >>> UInt8.ofNat i) &&& 1)) <<< UInt8.ofNat i
  bitAt 0 ||| bitAt 1 ||| bitAt 2 ||| bitAt 3 ||| bitAt 4 ||| bitAt 5 ||| bitAt 6 ||| bitAt 7

def xtimeRijndael (a : UInt8) : UInt8 :=
  let shifted := a <<< 1
  if (a &&& 0x80) != 0 then shifted ^^^ 0x1B else shifted

/-- Exact Intel SDM `VGF2P8MULB` byte multiplication in $\mathbb{F}_2[z]/(z^8 + z^4 + z^3 + z + 1)$. -/
def gfniMulByte (a b : UInt8) : UInt8 :=
  let a0 := a
  let a1 := xtimeRijndael a0
  let a2 := xtimeRijndael a1
  let a3 := xtimeRijndael a2
  let a4 := xtimeRijndael a3
  let a5 := xtimeRijndael a4
  let a6 := xtimeRijndael a5
  let a7 := xtimeRijndael a6
  let pick (i : Nat) (ai : UInt8) : UInt8 := if ((b >>> UInt8.ofNat i) &&& 1) != 0 then ai else 0
  pick 0 a0 ^^^ pick 1 a1 ^^^ pick 2 a2 ^^^ pick 3 a3 ^^^
  pick 4 a4 ^^^ pick 5 a5 ^^^ pick 6 a6 ^^^ pick 7 a7

def mapBytes64 (f : Nat → UInt8) : UInt64 :=
  (f 0).toUInt64 |||
  ((f 1).toUInt64 <<< 8) |||
  ((f 2).toUInt64 <<< 16) |||
  ((f 3).toUInt64 <<< 24) |||
  ((f 4).toUInt64 <<< 32) |||
  ((f 5).toUInt64 <<< 40) |||
  ((f 6).toUInt64 <<< 48) |||
  ((f 7).toUInt64 <<< 56)

def getByte64 (w : UInt64) (i : Nat) : UInt8 :=
  (w >>> UInt64.ofNat (i * 8)).toUInt8

def mapBytesVec256 (v1 v2 : Vec256) (f : UInt8 → UInt8 → UInt8) : Vec256 :=
  ⟨mapBytes64 (fun i => f (getByte64 v1.w0 i) (getByte64 v2.w0 i)),
   mapBytes64 (fun i => f (getByte64 v1.w1 i) (getByte64 v2.w1 i)),
   mapBytes64 (fun i => f (getByte64 v1.w2 i) (getByte64 v2.w2 i)),
   mapBytes64 (fun i => f (getByte64 v1.w3 i) (getByte64 v2.w3 i))⟩

def gfniAffineVec256 (src mat : Vec256) (imm : UInt8) : Vec256 :=
  ⟨mapBytes64 (fun i => gfniAffineByte (getByte64 src.w0 i) mat.w0 imm),
   mapBytes64 (fun i => gfniAffineByte (getByte64 src.w1 i) mat.w1 imm),
   mapBytes64 (fun i => gfniAffineByte (getByte64 src.w2 i) mat.w2 imm),
   mapBytes64 (fun i => gfniAffineByte (getByte64 src.w3 i) mat.w3 imm)⟩

def clmul64Loop : Nat → UInt64 → UInt64 → UInt64 → UInt64 → Vec128
  | 0, _, _, lo, hi => ⟨lo, hi⟩
  | k + 1, a, b, lo, hi =>
    let i := 63 - k
    let bitSet := ((b >>> UInt64.ofNat i) &&& 1) != 0
    let termLo := if bitSet then (if i == 0 then a else a <<< UInt64.ofNat i) else 0
    let termHi := if bitSet && i > 0 then a >>> UInt64.ofNat (64 - i) else 0
    clmul64Loop k a b (lo ^^^ termLo) (hi ^^^ termHi)

def clmul64 (a b : UInt64) : Vec128 :=
  clmul64Loop 64 a b 0 0

/-- Regression for the low polynomial coefficient, previously skipped by the loop. -/
theorem clmul64_one_one : clmul64 1 1 = ⟨1, 0⟩ := by decide +kernel

theorem clmul64_one_two : clmul64 1 2 = ⟨2, 0⟩ := by decide +kernel

def evalX86Cond (cc : Nat) (s : X86State) : Bool :=
  if cc == 2 then s.cf
  else if cc == 3 then !s.cf
  else if cc == 4 then s.zf
  else if cc == 5 then !s.zf
  else s.cf

def evalX86Alu (op : X86AluOp) (is64 : Bool) (a b : UInt64) (cfIn : Bool) : (UInt64 × Bool × Bool) :=
  let bound : Nat := if is64 then 0x10000000000000000 else 0x100000000
  let an := (maskGprWidth is64 a).toNat
  let bn := (maskGprWidth is64 b).toNat
  let cin := if cfIn then 1 else 0
  match op with
  | .add =>
    let sum := an + bn
    let res := maskGprWidth is64 (UInt64.ofNat (sum % bound))
    (res, sum ≥ bound, res == 0)
  | .adc =>
    let sum := an + bn + cin
    let res := maskGprWidth is64 (UInt64.ofNat (sum % bound))
    (res, sum ≥ bound, res == 0)
  | .sub =>
    let borrow := an < bn
    let diff := (an + bound - bn) % bound
    let res := maskGprWidth is64 (UInt64.ofNat diff)
    (res, borrow, res == 0)
  | .sbb =>
    let borrow := an < bn + cin
    let diff := (an + bound * 2 - bn - cin) % bound
    let res := maskGprWidth is64 (UInt64.ofNat diff)
    (res, borrow, res == 0)
  | .andOp =>
    let res := maskGprWidth is64 (a &&& b)
    (res, false, res == 0)
  | .orOp =>
    let res := maskGprWidth is64 (a ||| b)
    (res, false, res == 0)
  | .xorOp =>
    let res := maskGprWidth is64 (a ^^^ b)
    (res, false, res == 0)
  | .imul2 =>
    let prod := (an * bn) % bound
    let res := maskGprWidth is64 (UInt64.ofNat prod)
    (res, an * bn ≥ bound, res == 0)

def evalVecBin256 (op : X86VecBinOp) (v1 v2 : Vec256) : Vec256 :=
  match op with
  | .vpxor => ⟨v1.w0 ^^^ v2.w0, v1.w1 ^^^ v2.w1, v1.w2 ^^^ v2.w2, v1.w3 ^^^ v2.w3⟩
  | .vpand => ⟨v1.w0 &&& v2.w0, v1.w1 &&& v2.w1, v1.w2 &&& v2.w2, v1.w3 &&& v2.w3⟩
  | .vpandn => ⟨(~~~v1.w0) &&& v2.w0, (~~~v1.w1) &&& v2.w1, (~~~v1.w2) &&& v2.w2, (~~~v1.w3) &&& v2.w3⟩
  | .vpor => ⟨v1.w0 ||| v2.w0, v1.w1 ||| v2.w1, v1.w2 ||| v2.w2, v1.w3 ||| v2.w3⟩
  | .vpaddb => mapBytesVec256 v1 v2 (fun x y => x + y)
  | .vpcmpgtb =>
    mapBytesVec256 v1 v2 (fun x y =>
      let sx := signExt8ToInt x
      let sy := signExt8ToInt y
      if sx > sy then 0xFF else 0x00)
  | .vpshufb =>
    let shufLane (tbl0 tbl1 idx0 idx1 : UInt64) : (UInt64 × UInt64) :=
      let pickByte (c : UInt8) : UInt8 :=
        if (c &&& 0x80) != 0 then 0
        else
          let k := (c &&& 0x0F).toNat
          if k < 8 then getByte64 tbl0 k else getByte64 tbl1 (k - 8)
      (mapBytes64 (fun i => pickByte (getByte64 idx0 i)),
       mapBytes64 (fun i => pickByte (getByte64 idx1 i)))
    let (r0, r1) := shufLane v1.w0 v1.w1 v2.w0 v2.w1
    let (r2, r3) := shufLane v1.w2 v1.w3 v2.w2 v2.w3
    ⟨r0, r1, r2, r3⟩
  | .vgf2p8mulb => mapBytesVec256 v1 v2 gfniMulByte

def evalVecShift256 (sk : X86VecShiftKind) (v : Vec256) (imm : Nat) : Vec256 :=
  match sk with
  | .vpsllq =>
    if imm ≥ 64 then Vec256.zero
    else let sh := UInt64.ofNat imm; ⟨v.w0 <<< sh, v.w1 <<< sh, v.w2 <<< sh, v.w3 <<< sh⟩
  | .vpsrlq =>
    if imm ≥ 64 then Vec256.zero
    else let sh := UInt64.ofNat imm; ⟨v.w0 >>> sh, v.w1 >>> sh, v.w2 >>> sh, v.w3 >>> sh⟩
  | .vpsrlw =>
    let shw (w : UInt64) : UInt64 :=
      if imm ≥ 16 then 0
      else
        let mask16 : UInt64 := (0xFFFF >>> UInt64.ofNat imm)
        let repMask := mask16 ||| (mask16 <<< 16) ||| (mask16 <<< 32) ||| (mask16 <<< 48)
        (w >>> UInt64.ofNat imm) &&& repMask
    ⟨shw v.w0, shw v.w1, shw v.w2, shw v.w3⟩
  | .vpslldq =>
    if imm == 0 then v
    else if imm < 8 then
      let sh := UInt64.ofNat (8 * imm)
      let back := UInt64.ofNat (64 - 8 * imm)
      ⟨v.w0 <<< sh, (v.w1 <<< sh) ||| (v.w0 >>> back),
       v.w2 <<< sh, (v.w3 <<< sh) ||| (v.w2 >>> back)⟩
    else if imm < 16 then
      ⟨0, v.w0 <<< UInt64.ofNat (8 * (imm - 8)), 0, v.w2 <<< UInt64.ofNat (8 * (imm - 8))⟩
    else Vec256.zero
  | .vpsrldq =>
    if imm == 0 then v
    else if imm < 8 then
      let sh := UInt64.ofNat (8 * imm)
      let back := UInt64.ofNat (64 - 8 * imm)
      ⟨(v.w0 >>> sh) ||| (v.w1 <<< back), v.w1 >>> sh,
       (v.w2 >>> sh) ||| (v.w3 <<< back), v.w3 >>> sh⟩
    else if imm < 16 then
      ⟨v.w1 >>> UInt64.ofNat (8 * (imm - 8)), 0, v.w3 >>> UInt64.ofNat (8 * (imm - 8)), 0⟩
    else Vec256.zero
  | .vpshufd =>
    let pick (lo hi : UInt64) (i : Nat) :=
      let k := (imm >>> (2*i)) &&& 3
      ((if k < 2 then lo else hi) >>> UInt64.ofNat (32 * (k % 2))) &&& 0xffffffff
    ⟨pick v.w0 v.w1 0 ||| (pick v.w0 v.w1 1 <<< 32),
     pick v.w0 v.w1 2 ||| (pick v.w0 v.w1 3 <<< 32),
     pick v.w2 v.w3 0 ||| (pick v.w2 v.w3 1 <<< 32),
     pick v.w2 v.w3 2 ||| (pick v.w2 v.w3 3 <<< 32)⟩
  | .vextracti128 =>
    if imm % 2 == 0 then ⟨v.w0, v.w1, 0, 0⟩ else ⟨v.w2, v.w3, 0, 0⟩

def clampVecWidth (is256 : Bool) (v : Vec256) : Vec256 :=
  if is256 then v else ⟨v.w0, v.w1, 0, 0⟩

def findInstrAtPc {Instr : Type} (pc : Nat) : List (DecodedInstr Instr) → Option (DecodedInstr Instr)
  | [] => none
  | d :: ds => if d.offset == pc then some d else findInstrAtPc pc ds

def x86ShiftPreservesZf (sk : X86ShiftKind) (is64 : Bool) (cnt : Nat) : Bool :=
  cnt % (if is64 then 64 else 32) == 0 ||
    match sk with
    | .rol | .ror => true
    | _ => false

/-- Small-step `x86_64` operational semantics emitting `StepObs` (`pc`, `(addr, bytes)`, `isDoitSafe`). -/
def stepX86 (d : DecodedInstr X86Instr) (s : X86State) : (X86State × StepObs) :=
  let nextPc := d.offset + d.byteLen
  match d.instr with
  | .nop | .mfence =>
    ({ s with pc := nextPc }, ⟨d.offset, [], true⟩)
  | .pushReg r =>
    let sp' := s.gpr.get 4 - 8
    let mem' := writeMem64 s.mem sp' (s.gpr.get r)
    ({ s with pc := nextPc, gpr := s.gpr.set 4 sp', mem := mem' }, ⟨d.offset, [(sp', 8)], true⟩)
  | .popReg r =>
    let sp := s.gpr.get 4
    let v := readMem64 s.mem sp
    let gpr' := (s.gpr.set 4 (sp + 8)).set r v
    ({ s with pc := nextPc, gpr := gpr' }, ⟨d.offset, [(sp, 8)], true⟩)
  | .ret =>
    ({ s with halted := true }, ⟨d.offset, [], true⟩)
  | .movRegReg is64 dst src =>
    let v := maskGprWidth is64 (s.gpr.get src)
    ({ s with pc := nextPc, gpr := s.gpr.set dst v }, ⟨d.offset, [], true⟩)
  | .movImm is64 dst imm =>
    let v := maskGprWidth is64 imm
    ({ s with pc := nextPc, gpr := s.gpr.set dst v }, ⟨d.offset, [], true⟩)
  | .loadGpr wBytes is64 dst addr =>
    let ea := evalX86Addr s nextPc addr
    let raw := if wBytes == 1 then (s.mem ea).toUInt64 else readMem64 s.mem ea
    let v := maskGprWidth is64 raw
    ({ s with pc := nextPc, gpr := s.gpr.set dst v }, ⟨d.offset, [(ea, wBytes)], true⟩)
  | .storeGpr wBytes src addr =>
    let ea := evalX86Addr s nextPc addr
    let mem' := if wBytes == 1 then writeMem8 s.mem ea (s.gpr.get src).toUInt8
                else writeMem64 s.mem ea (s.gpr.get src)
    ({ s with pc := nextPc, mem := mem' }, ⟨d.offset, [(ea, wBytes)], true⟩)
  | .aluRegReg op is64 dst src =>
    let (res, cf', zf') := evalX86Alu op is64 (s.gpr.get dst) (s.gpr.get src) s.cf
    let of' := if op == .andOp || op == .orOp || op == .xorOp then false else s.ofFlag
    ({ s with pc := nextPc, gpr := s.gpr.set dst res, cf := cf', ofFlag := of', zf := zf' }, ⟨d.offset, [], true⟩)
  | .aluLoad64 op dst addr =>
    let ea := evalX86Addr s nextPc addr
    let mval := readMem64 s.mem ea
    let (res, cf', zf') := evalX86Alu op true (s.gpr.get dst) mval s.cf
    let of' := if op == .andOp || op == .orOp || op == .xorOp then false else s.ofFlag
    ({ s with pc := nextPc, gpr := s.gpr.set dst res, cf := cf', ofFlag := of', zf := zf' }, ⟨d.offset, [(ea, 8)], true⟩)
  | .aluImm op is64 dst imm =>
    let (res, cf', zf') := evalX86Alu op is64 (s.gpr.get dst) imm s.cf
    let of' := if op == .andOp || op == .orOp || op == .xorOp then false else s.ofFlag
    ({ s with pc := nextPc, gpr := s.gpr.set dst res, cf := cf', ofFlag := of', zf := zf' }, ⟨d.offset, [], true⟩)
  | .incDec isInc is64 dst =>
    let delta : UInt64 := if isInc then 1 else 0 - 1
    let res := maskGprWidth is64 (maskGprWidth is64 (s.gpr.get dst) + delta)
    ({ s with pc := nextPc, gpr := s.gpr.set dst res, zf := res == 0 }, ⟨d.offset, [], true⟩)
  | .negReg is64 dst =>
    let cur := maskGprWidth is64 (s.gpr.get dst)
    let res := maskGprWidth is64 (0 - cur)
    ({ s with pc := nextPc, gpr := s.gpr.set dst res, cf := cur != 0, zf := res == 0 }, ⟨d.offset, [], true⟩)
  | .mulOneOp _isSigned is64 src =>
    let a := (maskGprWidth is64 (s.gpr.get 0)).toNat
    let b := (maskGprWidth is64 (s.gpr.get src)).toNat
    let prod := a * b
    let lo := maskGprWidth is64 (UInt64.ofNat (prod % 0x10000000000000000))
    let hi := maskGprWidth is64 (UInt64.ofNat (prod / 0x10000000000000000))
    ({ s with pc := nextPc, gpr := (s.gpr.set 0 lo).set 2 hi }, ⟨d.offset, [], true⟩)
  | .shiftImm sk is64 dst cnt =>
    let w := if is64 then 64 else 32
    let c := cnt % w
    let cur := maskGprWidth is64 (s.gpr.get dst)
    let res :=
      match sk with
      | .shl => maskGprWidth is64 (cur <<< UInt64.ofNat c)
      | .shr => maskGprWidth is64 (cur >>> UInt64.ofNat c)
      | .rol =>
        if c == 0 then cur
        else maskGprWidth is64 ((cur <<< UInt64.ofNat c) ||| (cur >>> UInt64.ofNat (w - c)))
      | .ror =>
        if c == 0 then cur
        else maskGprWidth is64 ((cur >>> UInt64.ofNat c) ||| (cur <<< UInt64.ofNat (w - c)))
    ({ s with pc := nextPc, gpr := s.gpr.set dst res, zf := if x86ShiftPreservesZf sk is64 cnt then s.zf else res == 0 }, ⟨d.offset, [], true⟩)
  | .cmovcc cc is64 dst src =>
    let taken := evalX86Cond cc s
    let gpr' := if taken then s.gpr.set dst (maskGprWidth is64 (s.gpr.get src)) else s.gpr
    ({ s with pc := nextPc, gpr := gpr' }, ⟨d.offset, [], true⟩)
  | .mulx hiDst loDst src =>
    let prod := (s.gpr.get 2).toNat * (s.gpr.get src).toNat
    let lo := UInt64.ofNat (prod % 0x10000000000000000)
    let hi := UInt64.ofNat (prod / 0x10000000000000000)
    let gpr' := (s.gpr.set loDst lo).set hiDst hi
    ({ s with pc := nextPc, gpr := gpr' }, ⟨d.offset, [], true⟩)
  | .adcx dst src =>
    let sum := (s.gpr.get dst).toNat + (s.gpr.get src).toNat + (if s.cf then 1 else 0)
    let res := UInt64.ofNat (sum % 0x10000000000000000)
    ({ s with pc := nextPc, gpr := s.gpr.set dst res, cf := sum ≥ 0x10000000000000000 }, ⟨d.offset, [], true⟩)
  | .adox dst src =>
    let sum := (s.gpr.get dst).toNat + (s.gpr.get src).toNat + (if s.ofFlag then 1 else 0)
    let res := UInt64.ofNat (sum % 0x10000000000000000)
    ({ s with pc := nextPc, gpr := s.gpr.set dst res, ofFlag := sum ≥ 0x10000000000000000 }, ⟨d.offset, [], true⟩)
  | .jcc cc targetPc =>
    let taken := evalX86Cond cc s
    let tgt := if taken && targetPc ≥ 0 then targetPc.toNat else nextPc
    ({ s with pc := tgt }, ⟨d.offset, [], true⟩)
  | .jmpRel targetPc =>
    let tgt := if targetPc ≥ 0 then targetPc.toNat else nextPc
    ({ s with pc := tgt }, ⟨d.offset, [], true⟩)
  | .indirectBr _ | .divRem _ | .varShiftCl _ _ =>
    ({ s with halted := true }, ⟨d.offset, [], false⟩)
  | .vpgather _ addr =>
    let ea := evalX86Addr s nextPc addr
    ({ s with halted := true }, ⟨d.offset, [(ea, 32)], false⟩)
  | .vzeroupper =>
    let ymm' := Bank16.ofFn (fun i => let v := s.ymm.get i; ⟨v.w0, v.w1, 0, 0⟩)
    ({ s with pc := nextPc, ymm := ymm', ymmDirty := false }, ⟨d.offset, [], true⟩)
  | .vzeroall =>
    ({ s with pc := nextPc, ymm := Bank16.ofFn (fun _ => Vec256.zero), ymmDirty := false },
      ⟨d.offset, [], true⟩)
  | .vload is256 dst addr =>
    let ea := evalX86Addr s nextPc addr
    let v := if is256 then readMem256 s.mem ea
             else let q := readMem128 s.mem ea; ⟨q.w0, q.w1, 0, 0⟩
    ({ s with pc := nextPc, ymm := s.ymm.set dst v, ymmDirty := s.ymmDirty || is256 },
     ⟨d.offset, [(ea, if is256 then 32 else 16)], true⟩)
  | .vstore is256 src addr =>
    let ea := evalX86Addr s nextPc addr
    let v := s.ymm.get src
    let mem' := if is256 then writeMem256 s.mem ea v else writeMem128 s.mem ea ⟨v.w0, v.w1⟩
    ({ s with pc := nextPc, mem := mem' }, ⟨d.offset, [(ea, if is256 then 32 else 16)], true⟩)
  | .vmovGprToXmm is64 dstVec srcGpr =>
    let v := maskGprWidth is64 (s.gpr.get srcGpr)
    ({ s with pc := nextPc, ymm := s.ymm.set dstVec ⟨v, 0, 0, 0⟩ }, ⟨d.offset, [], true⟩)
  | .vpbroadcast isQword dst srcVec =>
    let sv := s.ymm.get srcVec
    let w := if isQword then sv.w0 else mapBytes64 (fun _ => sv.w0.toUInt8)
    ({ s with pc := nextPc, ymm := s.ymm.set dst ⟨w, w, w, w⟩, ymmDirty := true }, ⟨d.offset, [], true⟩)
  | .vpbroadcastLoad64 dst addr =>
    let ea := evalX86Addr s nextPc addr
    let w := readMem64 s.mem ea
    ({ s with pc := nextPc, ymm := s.ymm.set dst ⟨w, w, w, w⟩, ymmDirty := true }, ⟨d.offset, [(ea, 8)], true⟩)
  | .vbinOp op is256 dst src1 src2 =>
    let res := clampVecWidth is256 (evalVecBin256 op (s.ymm.get src1) (s.ymm.get src2))
    ({ s with pc := nextPc, ymm := s.ymm.set dst res, ymmDirty := s.ymmDirty || is256 }, ⟨d.offset, [], true⟩)
  | .vpxorLoad128 dst src1 addr =>
    let ea := evalX86Addr s nextPc addr
    let mvec := readMem128 s.mem ea
    let res := clampVecWidth false (evalVecBin256 .vpxor (s.ymm.get src1) ⟨mvec.w0, mvec.w1, 0, 0⟩)
    ({ s with pc := nextPc, ymm := s.ymm.set dst res }, ⟨d.offset, [(ea, 16)], true⟩)
  | .vpxorLoad256 dst src1 addr =>
    let ea := evalX86Addr s nextPc addr
    let mvec := readMem256 s.mem ea
    let res := evalVecBin256 .vpxor (s.ymm.get src1) mvec
    ({ s with pc := nextPc, ymm := s.ymm.set dst res, ymmDirty := true }, ⟨d.offset, [(ea, 32)], true⟩)
  | .vshiftImm sk is256 dst src imm =>
    let res := clampVecWidth is256 (evalVecShift256 sk (s.ymm.get src) imm)
    ({ s with pc := nextPc, ymm := s.ymm.set dst res, ymmDirty := s.ymmDirty || is256 }, ⟨d.offset, [], true⟩)
  | .vpclmulqdq is256 dst src1 src2 imm =>
    let v1 := s.ymm.get src1
    let v2 := s.ymm.get src2
    let selLo1 := if (imm &&& 0x01) == 0 then v1.w0 else v1.w1
    let selLo2 := if (imm &&& 0x10) == 0 then v2.w0 else v2.w1
    let pLo := clmul64 selLo1 selLo2
    let pHi := if is256 then
                 let selHi1 := if (imm &&& 0x01) == 0 then v1.w2 else v1.w3
                 let selHi2 := if (imm &&& 0x10) == 0 then v2.w2 else v2.w3
                 clmul64 selHi1 selHi2
               else Vec128.zero
    ({ s with pc := nextPc, ymm := s.ymm.set dst ⟨pLo.w0, pLo.w1, pHi.w0, pHi.w1⟩, ymmDirty := s.ymmDirty || is256 },
     ⟨d.offset, [], true⟩)
  | .vgf2p8affineqb is256 dst src1 src2 imm =>
    let res := clampVecWidth is256 (gfniAffineVec256 (s.ymm.get src1) (s.ymm.get src2) imm)
    ({ s with pc := nextPc, ymm := s.ymm.set dst res, ymmDirty := s.ymmDirty || is256 }, ⟨d.offset, [], true⟩)
  | .vperm2i128 dst src1 src2 imm =>
    let v1 := s.ymm.get src1
    let v2 := s.ymm.get src2
    let pick128 (sel : UInt8) : Vec128 :=
      if (sel &&& 0x08) != 0 then Vec128.zero
      else match (sel &&& 0x03).toNat with
      | 0 => ⟨v1.w0, v1.w1⟩
      | 1 => ⟨v1.w2, v1.w3⟩
      | 2 => ⟨v2.w0, v2.w1⟩
      | _ => ⟨v2.w2, v2.w3⟩
    let lo := pick128 (imm &&& 0x0F)
    let hi := pick128 ((imm >>> 4) &&& 0x0F)
    ({ s with pc := nextPc, ymm := s.ymm.set dst ⟨lo.w0, lo.w1, hi.w0, hi.w1⟩, ymmDirty := true }, ⟨d.offset, [], true⟩)

/-- Bounded-fuel `x86_64` execution returning the final state and leakage trace `List StepObs`. -/
def runX86 (prog : List (DecodedInstr X86Instr)) : Nat → X86State → (X86State × List StepObs)
  | 0, s => (s, [])
  | fuel + 1, s =>
    if s.halted then (s, [])
    else match findInstrAtPc s.pc prog with
    | none => ({ s with halted := true }, [])
    | some d =>
      let (s', obs) := stepX86 d s
      let (sFinal, restObs) := runX86 prog fuel s'
      (sFinal, obs :: restObs)

/-! ## §4. Fixed-Width 32-Bit `AArch64` Machine-Code Decoder + Semantics -/

inductive Arm64AluOp where
  | add | adds | sub | subs | adc | sbc | andOp | orr | eor | bic
  deriving DecidableEq, Repr

/-- Decoded `AArch64` instruction covering all 7 `qsag_asm` `.rlib` kernels + forbidden variable-time classes. -/
inductive Arm64Instr where
  | nop
  | msrDit (imm : Nat)
  | isb
  | dmbIsh
  | ret
  | aluReg (op : Arm64AluOp) (is64 : Bool) (rd rn rm shiftKind shiftAmt : Nat)
  | aluImm (op : Arm64AluOp) (is64 : Bool) (rd rn : Nat) (imm : UInt64)
  | movWide (isMovn : Bool) (is64 : Bool) (rd : Nat) (imm16 shift : Nat)
  | ubfm (is64 : Bool) (rd rn immr imms : Nat)
  | mulOp (isUmulh : Bool) (rd rn rm : Nat)
  | csel (cond : Nat) (isInv : Bool) (rd rn rm : Nat)
  | ldp64 (rt1 rt2 rn : Nat) (offBytes : UInt64)
  | stp64 (rt1 rt2 rn : Nat) (offBytes : UInt64)
  | strbPost (rt rn : Nat) (postOff : UInt64)
  | ldrQ (rt rn : Nat) (offBytes : UInt64)
  | strQ (rt rn : Nat) (offBytes : UInt64)
  | fmovDFromX (vd xn : Nat)
  | veor16b (vd vn vm : Nat)
  | vbcax16b (vd vn vm va : Nat)
  | veor3_16b (vd vn vm va : Nat)
  | vrax1_2d (vd vn vm : Nat)
  | vxar_2d (vd vn vm imm6 : Nat)
  | vpmull (isHigh : Bool) (vd vn vm : Nat)
  | vtrn (is128 second : Bool) (elementBytes vd vn vm : Nat)
  | vext16b (vd vn vm imm4 : Nat)
  | bCond (cond : Nat) (targetPc : Int)
  | cbzOrTbz (word : UInt32)
  | udivOrSdiv (word : UInt32)
  | varShiftReg (word : UInt32)
  | regOffsetMem (word : UInt32)
  deriving DecidableEq, Repr

/-- ARMv8-A `DecodeBitMasks` logical immediate decoder (`N:immr:imms` $\to$ 64-bit replicated bitmask). -/
def decodeArm64BitmaskImm (is64 : Bool) (nBit immr imms : Nat) : Option UInt64 :=
  let len? : Option Nat :=
    if nBit == 1 then (if is64 then some 6 else none)
    else if (imms &&& 0x20) == 0 then some 5
    else if (imms &&& 0x10) == 0 then some 4
    else if (imms &&& 0x08) == 0 then some 3
    else if (imms &&& 0x04) == 0 then some 2
    else if (imms &&& 0x02) == 0 then some 1
    else none
  match len? with
  | none => none
  | some len =>
    let esize := 1 <<< len
    let levels := esize - 1
    let s := imms &&& levels
    let r := immr &&& levels
    if s == levels then none
    else
      let ones : UInt64 := if s + 1 == 64 then 0 - 1 else (1 <<< UInt64.ofNat (s + 1)) - 1
      let rMod := r % esize
      let maskElem : UInt64 := if esize == 64 then 0 - 1 else (1 <<< UInt64.ofNat esize) - 1
      let rotElem :=
        if rMod == 0 then ones
        else ((ones >>> UInt64.ofNat rMod) ||| (ones <<< UInt64.ofNat (esize - rMod))) &&& maskElem
      let rep32 :=
        if esize == 2 then rotElem * 0x5555555555555555
        else if esize == 4 then rotElem * 0x1111111111111111
        else if esize == 8 then rotElem * 0x0101010101010101
        else if esize == 16 then rotElem * 0x0001000100010001
        else if esize == 32 then rotElem ||| (rotElem <<< 32)
        else rotElem
      some (maskGprWidth is64 rep32)

/-- Decode a single 32-bit little-endian `AArch64` instruction word at byte offset `pc`. -/
def decodeArm64Word (pc : Nat) (w : UInt32) : Option Arm64Instr :=
  let wn := w.toNat
  let rd := wn &&& 0x1F
  let rn := (wn >>> 5) &&& 0x1F
  let rm := (wn >>> 16) &&& 0x1F
  let ra := (wn >>> 10) &&& 0x1F
  let is64 := ((wn >>> 31) &&& 1) == 1
  if w == 0xD503201F then some .nop
  else if w == 0xD503415F then some (.msrDit 1)
  else if w == 0xD503405F then some (.msrDit 0)
  else if w == 0xD5033FDF then some .isb
  else if w == 0xD5033BBF then some .dmbIsh
  else if w == 0xD65F03C0 then some .ret
  -- Forbidden CBZ/CBNZ (`x34..x35`) & TBZ/TBNZ (`x36..x37`)
  else if (wn &&& 0x7C000000) == 0x34000000 then some (.cbzOrTbz w)
  -- Conditional branch `B.cond` (`01010100 imm19 0 cond`)
  else if (wn &&& 0xFF000010) == 0x54000000 then
    let cond := wn &&& 0xF
    let imm19 := (wn >>> 5) &&& 0x7FFFF
    let signed19 : Int := if imm19 < 0x40000 then Int.ofNat imm19 else Int.ofNat imm19 - 0x80000
    if cond < 4 then some (.bCond cond (Int.ofNat pc + signed19 * 4)) else none
  -- Forbidden UDIV / SDIV (`x011010110 Rm 00001x Rn Rd`)
  else if (wn &&& 0x7FE0FC00) == 0x1AC00800 then some (.udivOrSdiv w)
  -- Forbidden variable shift `LSLV/LSRV/ASRV/RORV` (`x011010110 Rm 0010xx Rn Rd`)
  else if (wn &&& 0x7FE0F000) == 0x1AC02000 then some (.varShiftReg w)
  -- Forbidden register-offset `LDR/STR [Xn, Xm]`
  else if (wn &&& 0x3B200C00) == 0x38200800 then some (.regOffsetMem w)
  -- `MUL Xd, Xn, Xm` (`0x9B007C00`) & `UMULH Xd, Xn, Xm` (`0x9BC07C00`)
  else if (wn &&& 0xFFE0FC00) == 0x9B007C00 then some (.mulOp false rd rn rm)
  else if (wn &&& 0xFFE0FC00) == 0x9BC07C00 then some (.mulOp true rd rn rm)
  -- `ADC` (`0x9A000000`) & `SBC`/`NGC` (`0xDA000000`)
  else if (wn &&& 0x7FE0FC00) == 0x1A000000 then some (.aluReg .adc is64 rd rn rm 0 0)
  else if (wn &&& 0x7FE0FC00) == 0x5A000000 then some (.aluReg .sbc is64 rd rn rm 0 0)
  -- `CSEL` / `CSINV` (`CSETM`)
  else if (wn &&& 0x7FE00C00) == 0x1A800000 then
    let cond := (wn >>> 12) &&& 0xF
    if cond < 4 then some (.csel cond false rd rn rm) else none
  else if (wn &&& 0x7FE00C00) == 0x5A800000 then
    let cond := (wn >>> 12) &&& 0xF
    if cond < 4 then some (.csel cond true rd rn rm) else none
  -- Add/Sub immediate (`x0010001 sh imm12 Rn Rd`)
  else if (wn &&& 0x1F800000) == 0x11000000 then
    let opc := (wn >>> 29) &&& 3
    let sh := ((wn >>> 22) &&& 1) * 12
    let imm12 := ((wn >>> 10) &&& 0xFFF) <<< sh
    let aop : Arm64AluOp :=
      if opc == 0 then .add else if opc == 1 then .adds else if opc == 2 then .sub else .subs
    if rn == 31 || ((opc == 0 || opc == 2) && rd == 31) then none
    else some (.aluImm aop is64 rd rn (UInt64.ofNat imm12))
  -- Add/Sub shifted register (`xx001011 shift 0 Rm imm6 Rn Rd`)
  else if (wn &&& 0x1F200000) == 0x0B000000 then
    let opc := (wn >>> 29) &&& 3
    let shiftKind := (wn >>> 22) &&& 3
    let shiftAmt := (wn >>> 10) &&& 0x3F
    let aop : Arm64AluOp :=
      if opc == 0 then .add else if opc == 1 then .adds else if opc == 2 then .sub else .subs
    some (.aluReg aop is64 rd rn rm shiftKind shiftAmt)
  -- Logical shifted register (`xx001010 shift N Rm imm6 Rn Rd`)
  else if (wn &&& 0x1F000000) == 0x0A000000 then
    let opc := (wn >>> 29) &&& 3
    let nInv := ((wn >>> 21) &&& 1) == 1
    let shiftKind := (wn >>> 22) &&& 3
    let shiftAmt := (wn >>> 10) &&& 0x3F
    if opc == 0 && !nInv then some (.aluReg .andOp is64 rd rn rm shiftKind shiftAmt)
    else if opc == 0 && nInv then some (.aluReg .bic is64 rd rn rm shiftKind shiftAmt)
    else if opc == 1 && !nInv then some (.aluReg .orr is64 rd rn rm shiftKind shiftAmt)
    else if opc == 2 && !nInv then some (.aluReg .eor is64 rd rn rm shiftKind shiftAmt)
    else none
  -- Move wide immediate `MOVN` (`opc=0`) / `MOVZ` (`opc=2`): `xx100101 hw imm16 Rd`
  else if (wn &&& 0x1F800000) == 0x12800000 then
    let opc := (wn >>> 29) &&& 3
    let hw := ((wn >>> 21) &&& 3) * 16
    let imm16 := (wn >>> 5) &&& 0xFFFF
    if opc == 0 || opc == 2 then some (.movWide (opc == 0) is64 rd imm16 hw) else none
  -- Logical immediate (`xx100100 N immr imms Rn Rd`)
  else if (wn &&& 0x1F800000) == 0x12000000 then
    let opc := (wn >>> 29) &&& 3
    let nBit := (wn >>> 22) &&& 1
    let immr := (wn >>> 16) &&& 0x3F
    let imms := (wn >>> 10) &&& 0x3F
    match decodeArm64BitmaskImm is64 nBit immr imms with
    | none => none
    | some imm =>
      if rd == 31 then none
      else if opc == 0 then some (.aluImm .andOp is64 rd rn imm)
      else if opc == 1 then some (.aluImm .orr is64 rd rn imm)
      else if opc == 2 then some (.aluImm .eor is64 rd rn imm)
      else none
  -- `UBFM` (`LSL`/`LSR` immediate): `x10100110 N immr imms Rn Rd`
  else if (wn &&& 0x7F800000) == 0x53000000 then
    let immr := (wn >>> 16) &&& 0x3F
    let imms := (wn >>> 10) &&& 0x3F
    let n := (wn >>> 22) &&& 1
    if (is64 && n == 1) || (!is64 && n == 0 && immr < 32 && imms < 32) then
      some (.ubfm is64 rd rn immr imms)
    else none
  -- `LDP` / `STP` 64-bit signed offset (`101010010 L imm7 Rt2 Rn Rt1`)
  else if (wn &&& 0xFFC00000) == 0xA9400000 || (wn &&& 0xFFC00000) == 0xA9000000 then
    let isLoad := ((wn >>> 22) &&& 1) == 1
    let imm7 := (wn >>> 15) &&& 0x7F
    let off64 : UInt64 :=
      if imm7 < 64 then UInt64.ofNat (imm7 * 8) else 0 - UInt64.ofNat ((128 - imm7) * 8)
    if rn == 31 then none
    else if isLoad then some (.ldp64 rd ra rn off64) else some (.stp64 rd ra rn off64)
  -- `STRB Wt, [Xn], #imm9` post-index (`00111000000 imm9 01 Rn Rt`)
  else if (wn &&& 0xFFE00C00) == 0x38000400 then
    let imm9 := (wn >>> 12) &&& 0x1FF
    let off64 : UInt64 :=
      if imm9 < 256 then UInt64.ofNat imm9 else 0 - UInt64.ofNat (512 - imm9)
    if rn == 31 then none else some (.strbPost rd rn off64)
  -- `LDR Qrt, [Xrn, #imm12*16]` (`0x3DC00000`) & `STR Qrt, [Xrn, #imm12*16]` (`0x3D800000`)
  else if (wn &&& 0xFFC00000) == 0x3DC00000 then
    let imm12 := (wn >>> 10) &&& 0xFFF
    if rn == 31 then none else some (.ldrQ rd rn (UInt64.ofNat (imm12 * 16)))
  else if (wn &&& 0xFFC00000) == 0x3D800000 then
    let imm12 := (wn >>> 10) &&& 0xFFF
    if rn == 31 then none else some (.strQ rd rn (UInt64.ofNat (imm12 * 16)))
  -- `FMOV Dd, Xn` (`0x9E670000`)
  else if (wn &&& 0xFFFFFC00) == 0x9E670000 then
    some (.fmovDFromX rd rn)
  -- `EOR Vd.16B, Vn.16B, Vm.16B` (`0x6E201C00`)
  else if (wn &&& 0xFFE0FC00) == 0x6E201C00 then
    some (.veor16b rd rn rm)
  -- `EOR3` (`0xCE000000`), `BCAX` (`0xCE200000`), `RAX1` (`0xCE608C00`), `XAR` (`0xCE800000`)
  else if (wn &&& 0xFFE08000) == 0xCE000000 then
    some (.veor3_16b rd rn rm ra)
  else if (wn &&& 0xFFE08000) == 0xCE200000 then
    some (.vbcax16b rd rn rm ra)
  else if (wn &&& 0xFFE0FC00) == 0xCE608C00 then
    some (.vrax1_2d rd rn rm)
  else if (wn &&& 0xFFE00000) == 0xCE800000 then
    let imm6 := (wn >>> 10) &&& 0x3F
    some (.vxar_2d rd rn rm imm6)
  -- `PMULL Vd.1Q, Vn.1D, Vm.1D` (`0x0EE0E000`) & `PMULL2 Vd.1Q, Vn.2D, Vm.2D` (`0x4EE0E000`)
  else if (wn &&& 0xBFE0FC00) == 0x0EE0E000 then
    some (.vpmull (((wn >>> 30) &&& 1) == 1) rd rn rm)
  -- TRN1/TRN2: interleave even/odd elements, following LNSym's exec_trn.
  else if (wn &&& 0xBF20BC00) == 0x0E002800 then
    let q := ((wn >>> 30) &&& 1) == 1
    let size := (wn >>> 22) &&& 3
    if !q && size == 3 then none
    else some (.vtrn q (((wn >>> 14) &&& 1) == 1) (1 <<< size) rd rn rm)
  -- `EXT Vd.16B, Vn.16B, Vm.16B, #imm4` (`0x6E000000`)
  else if (wn &&& 0xFFE08400) == 0x6E000000 then
    let imm4 := (wn >>> 11) &&& 0xF
    some (.vext16b rd rn rm imm4)
  else
    none

def decodeArm64Loop : Nat → List UInt8 → List (DecodedInstr Arm64Instr) → Option (List (DecodedInstr Arm64Instr))
  | _, [], acc => some acc.reverse
  | pc, b0 :: b1 :: b2 :: b3 :: rest, acc =>
    let w : UInt32 := b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)
    match decodeArm64Word pc w with
    | none => none
    | some ins => decodeArm64Loop (pc + 4) rest (⟨pc, 4, ins⟩ :: acc)
  | _, _ :: _, _ => none

/-- Decode an entire `.text` symbol byte slice into a 32-bit `AArch64` instruction stream. -/
def decodeArm64Stream (code : List UInt8) : Option (List (DecodedInstr Arm64Instr)) :=
  decodeArm64Loop 0 code []

/-- Concrete `AArch64` machine state (`X0..X30` + `XZR`, `V0..V31`, `NZCV` flags, `DIT`, byte memory). -/
structure Arm64State where
  pc : Nat
  gpr : Bank32 UInt64
  vec : Bank32 Vec128
  cf : Bool
  zf : Bool
  dit : Bool
  halted : Bool
  mem : UInt64 → UInt8

def getArmGpr (s : Arm64State) (r : Nat) : UInt64 :=
  if r == 31 then 0 else s.gpr.get r

def setArmGpr (s : Arm64State) (r : Nat) (v : UInt64) : Bank32 UInt64 :=
  if r == 31 then s.gpr else s.gpr.set r v

def applyArmShift (is64 : Bool) (v : UInt64) (kind amt : Nat) : UInt64 :=
  let v' := maskGprWidth is64 v
  let w := if is64 then 64 else 32
  let c := amt % w
  if c == 0 then v'
  else if kind == 0 then maskGprWidth is64 (v' <<< UInt64.ofNat c)
  else if kind == 1 then maskGprWidth is64 (v' >>> UInt64.ofNat c)
  else maskGprWidth is64 ((v' >>> UInt64.ofNat c) ||| (v' <<< UInt64.ofNat (w - c)))

def evalArmAlu (op : Arm64AluOp) (is64 : Bool) (a b : UInt64) (cfIn zfIn : Bool) : (UInt64 × Bool × Bool) :=
  let bound : Nat := if is64 then 0x10000000000000000 else 0x100000000
  let an := (maskGprWidth is64 a).toNat
  let bn := (maskGprWidth is64 b).toNat
  let cin := if cfIn then 1 else 0
  let invBorrow := if cfIn then 0 else 1
  match op with
  | .add => (maskGprWidth is64 (UInt64.ofNat ((an + bn) % bound)), cfIn, zfIn)
  | .adds =>
    let sum := an + bn
    let res := maskGprWidth is64 (UInt64.ofNat (sum % bound))
    (res, sum ≥ bound, res == 0)
  | .sub => (maskGprWidth is64 (UInt64.ofNat ((an + bound - bn) % bound)), cfIn, zfIn)
  | .subs =>
    let res := maskGprWidth is64 (UInt64.ofNat ((an + bound - bn) % bound))
    (res, an ≥ bn, res == 0)
  | .adc =>
    let res := maskGprWidth is64 (UInt64.ofNat ((an + bn + cin) % bound))
    (res, cfIn, zfIn)
  | .sbc =>
    let res := maskGprWidth is64 (UInt64.ofNat ((an + bound * 2 - bn - invBorrow) % bound))
    (res, cfIn, zfIn)
  | .andOp => (maskGprWidth is64 (a &&& b), cfIn, zfIn)
  | .orr => (maskGprWidth is64 (a ||| b), cfIn, zfIn)
  | .eor => (maskGprWidth is64 (a ^^^ b), cfIn, zfIn)
  | .bic => (maskGprWidth is64 (a &&& (~~~b)), cfIn, zfIn)

def evalArmCond (cond : Nat) (s : Arm64State) : Bool :=
  if cond == 0 then s.zf
  else if cond == 1 then !s.zf
  else if cond == 2 then s.cf
  else if cond == 3 then !s.cf
  else s.cf

/-- Small-step `AArch64` operational semantics emitting `StepObs` (`pc`, `(addr, bytes)`, `isDoitSafe`). -/
