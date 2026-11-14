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
   certificate per historical symbol. New source archives additionally pin all five bitslice
   exports; their provenance alone is not a CT or functional-refinement certificate.
   Frame refinements specialize the 0x340-byte Keccak frame and its 0x320-byte wipe loop.
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
  | testRegReg (is64 : Bool) (r1 r2 : Nat)
  | cmpRegReg (is64 : Bool) (dst src : Nat)
  | cmpImm (is64 : Bool) (dst : Nat) (imm : UInt64)
  | lea (is64 : Bool) (dst : Nat) (addr : X86MemAddr)
  | storeImm8 (addr : X86MemAddr) (imm : UInt8)
  | notReg (is64 : Bool) (dst : Nat)
  | setcc (cc : Nat) (dst : Nat)
  | bswap (is64 : Bool) (dst : Nat)
  | sseMovdquLoad (dst : Nat) (addr : X86MemAddr)
  | ssePcmpeqb (dst src : Nat)
  | ssePand (dst src : Nat)
  | ssePmovmskb (dst src : Nat)
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
  let (prefLen, rest0, p66, _pf2, pf3) := stripX86LegacyPrefixes 12 bs false false false
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
  else if op == 0x35 then
    let imm32 ← readU32LE? (rest.drop 1)
    let imm := if rexW then signExt32To64 imm32 else UInt64.ofNat imm32.toNat
    pure ⟨pc, hdrLen + 5, .aluImm .xorOp rexW 0 imm⟩
  else if op == 0x39 then
    let (src, opnd, mLen) ← decodeX86ModRM (rest.drop 1) rexR rexX rexB
    match opnd with
    | .reg dst => pure ⟨pc, hdrLen + 1 + mLen, .cmpRegReg rexW dst src⟩
    | .mem _ => none
  else if op == 0x3B then
    let (dst, opnd, mLen) ← decodeX86ModRM (rest.drop 1) rexR rexX rexB
    match opnd with
    | .reg src => pure ⟨pc, hdrLen + 1 + mLen, .cmpRegReg rexW dst src⟩
    | .mem _ => none
  else if op == 0x85 then
    let (r2, opnd, mLen) ← decodeX86ModRM (rest.drop 1) rexR rexX rexB
    match opnd with
    | .reg r1 => pure ⟨pc, hdrLen + 1 + mLen, .testRegReg rexW r1 r2⟩
    | .mem _ => none
  else if op == 0x8D then
    let (dst, opnd, mLen) ← decodeX86ModRM (rest.drop 1) rexR rexX rexB
    match opnd with
    | .mem addr => pure ⟨pc, hdrLen + 1 + mLen, .lea rexW dst addr⟩
    | .reg _ => none
  else if op == 0x81 then
    let (regF, opnd, mLen) ← decodeX86ModRM (rest.drop 1) rexR rexX rexB
    let imm32 ← readU32LE? (rest.drop (1 + mLen))
    let imm := if rexW then signExt32To64 imm32 else UInt64.ofNat imm32.toNat
    match opnd with
    | .reg dst =>
      if (regF &&& 7) == 7 then
        pure ⟨pc, hdrLen + 1 + mLen + 4, .cmpImm rexW dst imm⟩
      else do
        let aop ← decodeAluDigit? (regF &&& 7)
        pure ⟨pc, hdrLen + 1 + mLen + 4, .aluImm aop rexW dst imm⟩
    | .mem _ => none
  else if op == 0x83 then
    let (regF, opnd, mLen) ← decodeX86ModRM (rest.drop 1) rexR rexX rexB
    let imm8 ← rest[1 + mLen]?
    let imm := signExt8To64 imm8
    match opnd with
    | .reg dst =>
      if (regF &&& 7) == 7 then
        pure ⟨pc, hdrLen + 1 + mLen + 1, .cmpImm rexW dst imm⟩
      else do
        let aop ← decodeAluDigit? (regF &&& 7)
        pure ⟨pc, hdrLen + 1 + mLen + 1, .aluImm aop rexW dst imm⟩
    | .mem _ => none
  else if op == 0xC6 then
    let (regF, opnd, mLen) ← decodeX86ModRM (rest.drop 1) rexR rexX rexB
    if (regF &&& 7) != 0 then none
    else
      let imm8 ← rest[1 + mLen]?
      match opnd with
      | .mem addr => pure ⟨pc, hdrLen + 1 + mLen + 1, .storeImm8 addr imm8⟩
      | .reg _ => none
  else if op == 0xC1 then
    let (regF, opnd, mLen) ← decodeX86ModRM (rest.drop 1) rexR rexX rexB
    let sk ← decodeShiftDigit? (regF &&& 7)
    let imm8 ← rest[1 + mLen]?
    match opnd with
    | .reg dst => pure ⟨pc, hdrLen + 1 + mLen + 1, .shiftImm sk rexW dst imm8.toNat⟩
    | .mem _ => none
  else if op == 0xD1 then
    let (regF, opnd, mLen) ← decodeX86ModRM (rest.drop 1) rexR rexX rexB
    let sk ← decodeShiftDigit? (regF &&& 7)
    match opnd with
    | .reg dst => pure ⟨pc, hdrLen + 1 + mLen, .shiftImm sk rexW dst 1⟩
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
        if digit == 2 then pure ⟨pc, hdrLen + 1 + mLen, .notReg rexW r⟩
        else if digit == 3 then pure ⟨pc, hdrLen + 1 + mLen, .negReg rexW r⟩
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
    else if 0x90 ≤ op2 && op2 ≤ 0x9F then
      if op2 < 0x92 || 0x95 < op2 || (p66 && !rexW) then return ← none
      let (_, opnd, mLen) ← decodeX86ModRM (rest.drop 2) rexR rexX rexB
      match opnd with
      | .reg dst =>
        if rexLen == 0 && dst ≥ 4 then none
        else pure ⟨pc, hdrLen + 2 + mLen, .setcc (op2.toNat - 0x90) dst⟩
      | .mem _ => none
    else if 0xC8 ≤ op2 && op2 ≤ 0xCF && !p66 && !pf3 then
      pure ⟨pc, hdrLen + 2, .bswap rexW ((op2.toNat - 0xC8) + rexB * 8)⟩
    else if op2 == 0x6F && pf3 && !p66 then
      let (dst, opnd, mLen) ← decodeX86ModRM (rest.drop 2) rexR rexX rexB
      match opnd with
      | .mem addr => pure ⟨pc, hdrLen + 2 + mLen, .sseMovdquLoad dst addr⟩
      | .reg _ => none
    else if op2 == 0x74 && p66 && !pf3 then
      let (dst, opnd, mLen) ← decodeX86ModRM (rest.drop 2) rexR rexX rexB
      match opnd with
      | .reg src => pure ⟨pc, hdrLen + 2 + mLen, .ssePcmpeqb dst src⟩
      | .mem _ => none
    else if op2 == 0xDB && p66 && !pf3 then
      let (dst, opnd, mLen) ← decodeX86ModRM (rest.drop 2) rexR rexX rexB
      match opnd with
      | .reg src => pure ⟨pc, hdrLen + 2 + mLen, .ssePand dst src⟩
      | .mem _ => none
    else if op2 == 0xD7 && p66 && !pf3 then
      let (dst, opnd, mLen) ← decodeX86ModRM (rest.drop 2) rexR rexX rexB
      match opnd with
      | .reg src => pure ⟨pc, hdrLen + 2 + mLen, .ssePmovmskb dst src⟩
      | .mem _ => none
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

/-- Condition codes with modelled semantics: `2` (`B`, `CF`), `3` (`AE`, `!CF`), `4` (`E`, `ZF`)
    and `5` (`NE`, `!ZF`). Every other code reads `SF`, `PF`, or a combination of flags that the
    state does not carry. `decodeX86InstrAt` produces only these four codes for `jcc` and
    `cmovcc`, and `transferX86Instr` rejects any instruction whose code is outside this set. -/
def x86CondSupported (cc : Nat) : Bool :=
  cc == 2 || cc == 3 || cc == 4 || cc == 5

/-- Concrete condition evaluation for the supported codes `{2, 3, 4, 5}`. An unsupported code
    evaluates to `false` (not taken); such an instruction is never accepted by the checker
    (`x86CondIsPublic_supported`, `tooth_x86_jcc_unsupported_cc_rejected`,
    `tooth_x86_cmovcc_unsupported_cc_rejected`). -/
def evalX86Cond (cc : Nat) (s : X86State) : Bool :=
  if cc == 2 then s.cf
  else if cc == 3 then !s.cf
  else if cc == 4 then s.zf
  else if cc == 5 then !s.zf
  else false

/-- Two's-complement value of the `w`-bit pattern `n < bound`, where `bound = 2 ^ w`. -/
def signedOfBound (bound n : Nat) : Int :=
  if 2 * n < bound then (n : Int) else (n : Int) - (bound : Int)

/-- Signed two's-complement range check `v ∉ [-bound / 2, bound / 2)` for `bound = 2 ^ w`. -/
def signedOutOfBounds (bound : Nat) (v : Int) : Bool :=
  decide (2 * v < -(bound : Int)) || decide ((bound : Int) ≤ 2 * v)

/-- `CF = OF` after a signed multiply of two `w`-bit patterns (`bound = 2 ^ w`): set exactly when
    the signed product lies outside `[-bound / 2, bound / 2)`, that is, when sign-extending the
    truncated result does not give back the product. -/
def imulSignedOverflow (bound an bn : Nat) : Bool :=
  signedOutOfBounds bound (signedOfBound bound an * signedOfBound bound bn)

/-- Architectural Intel SDM signed-overflow flag (`OF`) for scalar `ALU` operations at width `w ∈ {32, 64}`. -/
def evalX86AluOf (op : X86AluOp) (is64 : Bool) (a b : UInt64) (cfIn : Bool) : Bool :=
  let bound : Nat := if is64 then 0x10000000000000000 else 0x100000000
  let an := (maskGprWidth is64 a).toNat
  let bn := (maskGprWidth is64 b).toNat
  let sa := signedOfBound bound an
  let sb := signedOfBound bound bn
  let cin : Int := if cfIn then 1 else 0
  match op with
  | .add => signedOutOfBounds bound (sa + sb)
  | .adc => signedOutOfBounds bound (sa + sb + cin)
  | .sub => signedOutOfBounds bound (sa - sb)
  | .sbb => signedOutOfBounds bound (sa - sb - cin)
  | .andOp | .orOp | .xorOp => false
  | .imul2 => imulSignedOverflow bound an bn

/-- Architectural signed-overflow flag (`OF`) for `INC` / `DEC` at width `w ∈ {32, 64}`. -/
def evalX86IncDecOf (isInc is64 : Bool) (v : UInt64) : Bool :=
  let cur := maskGprWidth is64 v
  if isInc then cur == (if is64 then 0x7FFFFFFFFFFFFFFF else 0x7FFFFFFF)
  else cur == (if is64 then 0x8000000000000000 else 0x80000000)

/-- Byte-swap helper for 32-bit and 64-bit `BSWAP`. -/
def evalX86Bswap (is64 : Bool) (v : UInt64) : UInt64 :=
  if is64 then
    ((v &&& 0x00000000000000FF) <<< (56 : UInt64)) |||
    ((v &&& 0x000000000000FF00) <<< (40 : UInt64)) |||
    ((v &&& 0x0000000000FF0000) <<< (24 : UInt64)) |||
    ((v &&& 0x00000000FF000000) <<< (8 : UInt64))  |||
    ((v >>> (8 : UInt64))  &&& 0x00000000FF000000) |||
    ((v >>> (24 : UInt64)) &&& 0x0000000000FF0000) |||
    ((v >>> (40 : UInt64)) &&& 0x000000000000FF00) |||
    ((v >>> (56 : UInt64)) &&& 0x00000000000000FF)
  else
    ((v &&& 0x000000FF) <<< (24 : UInt64)) |||
    ((v &&& 0x0000FF00) <<< (8 : UInt64))  |||
    ((v >>> (8 : UInt64))  &&& 0x0000FF00) |||
    ((v >>> (24 : UInt64)) &&& 0x000000FF)

/-- 16-bit byte-MSB mask extracted by `PMOVMSKB r32, xmm`. -/
def evalPmovmskb128 (v : Vec256) : UInt64 :=
  let bitFrom (w : UInt64) (byteIdx outBit : Nat) : UInt64 :=
    (((w >>> UInt64.ofNat (byteIdx * 8 + 7)) &&& 1) <<< UInt64.ofNat outBit)
  bitFrom v.w0 0 0 ||| bitFrom v.w0 1 1 ||| bitFrom v.w0 2 2 ||| bitFrom v.w0 3 3 |||
  bitFrom v.w0 4 4 ||| bitFrom v.w0 5 5 ||| bitFrom v.w0 6 6 ||| bitFrom v.w0 7 7 |||
  bitFrom v.w1 0 8 ||| bitFrom v.w1 1 9 ||| bitFrom v.w1 2 10 ||| bitFrom v.w1 3 11 |||
  bitFrom v.w1 4 12 ||| bitFrom v.w1 5 13 ||| bitFrom v.w1 6 14 ||| bitFrom v.w1 7 15

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
    -- The low `w` bits of the product do not depend on signedness; `CF` (and `OF`, which
    -- `stepX86` sets equal to it) report signed overflow. `ZF` is architecturally undefined
    -- after `IMUL`; the value here is a function of the operands only.
    let prod := (an * bn) % bound
    let res := maskGprWidth is64 (UInt64.ofNat prod)
    (res, imulSignedOverflow bound an bn, res == 0)

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

/-- Architectural result + `(CF, OF, ZF)` for immediate shifts and rotates (`c == 0` preserves flags;
    `c > 0` sets architectural `CF` and `c == 1` `OF`; for `c > 1`, `OF` is architecturally undefined
    on hardware and given a deterministic pure formula here while `transferX86Instr` forgets `ofPub`). -/
def evalX86Shift (sk : X86ShiftKind) (is64 : Bool) (v : UInt64) (cnt : Nat)
    (cfIn ofIn zfIn : Bool) : (UInt64 × Bool × Bool × Bool) :=
  let w := if is64 then 64 else 32
  let c := cnt % w
  let cur := maskGprWidth is64 v
  if c == 0 then
    (cur, cfIn, ofIn, zfIn)
  else
    let msbMask : UInt64 := if is64 then 0x8000000000000000 else 0x80000000
    let nextMsbMask : UInt64 := if is64 then 0x4000000000000000 else 0x40000000
    match sk with
    | .shl =>
      let res := maskGprWidth is64 (cur <<< UInt64.ofNat c)
      let cf' := ((cur >>> UInt64.ofNat (w - c)) &&& 1) != 0
      let of' := ((res &&& msbMask) != 0) != cf'
      (res, cf', of', res == 0)
    | .shr =>
      let res := maskGprWidth is64 (cur >>> UInt64.ofNat c)
      let cf' := ((cur >>> UInt64.ofNat (c - 1)) &&& 1) != 0
      let of' := (cur &&& msbMask) != 0
      (res, cf', of', res == 0)
    | .rol =>
      let res := maskGprWidth is64 ((cur <<< UInt64.ofNat c) ||| (cur >>> UInt64.ofNat (w - c)))
      let cf' := (res &&& 1) != 0
      let of' := ((res &&& msbMask) != 0) != cf'
      (res, cf', of', zfIn)
    | .ror =>
      let res := maskGprWidth is64 ((cur >>> UInt64.ofNat c) ||| (cur <<< UInt64.ofNat (w - c)))
      let cf' := (res &&& msbMask) != 0
      let of' := cf' != ((res &&& nextMsbMask) != 0)
      (res, cf', of', zfIn)

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
    let a := s.gpr.get dst
    let b := s.gpr.get src
    let (res, cf', zf') := evalX86Alu op is64 a b s.cf
    let of' := evalX86AluOf op is64 a b s.cf
    ({ s with pc := nextPc, gpr := s.gpr.set dst res, cf := cf', ofFlag := of', zf := zf' }, ⟨d.offset, [], true⟩)
  | .aluLoad64 op dst addr =>
    let ea := evalX86Addr s nextPc addr
    let a := s.gpr.get dst
    let mval := readMem64 s.mem ea
    let (res, cf', zf') := evalX86Alu op true a mval s.cf
    let of' := evalX86AluOf op true a mval s.cf
    ({ s with pc := nextPc, gpr := s.gpr.set dst res, cf := cf', ofFlag := of', zf := zf' }, ⟨d.offset, [(ea, 8)], true⟩)
  | .aluImm op is64 dst imm =>
    let a := s.gpr.get dst
    let (res, cf', zf') := evalX86Alu op is64 a imm s.cf
    let of' := evalX86AluOf op is64 a imm s.cf
    ({ s with pc := nextPc, gpr := s.gpr.set dst res, cf := cf', ofFlag := of', zf := zf' }, ⟨d.offset, [], true⟩)
  | .incDec isInc is64 dst =>
    let cur := s.gpr.get dst
    let delta : UInt64 := if isInc then 1 else 0 - 1
    let res := maskGprWidth is64 (maskGprWidth is64 cur + delta)
    let of' := evalX86IncDecOf isInc is64 cur
    ({ s with pc := nextPc, gpr := s.gpr.set dst res, ofFlag := of', zf := res == 0 }, ⟨d.offset, [], true⟩)
  | .negReg is64 dst =>
    let cur := maskGprWidth is64 (s.gpr.get dst)
    let res := maskGprWidth is64 (0 - cur)
    let of' := cur == (if is64 then 0x8000000000000000 else 0x80000000)
    ({ s with pc := nextPc, gpr := s.gpr.set dst res, cf := cur != 0, ofFlag := of', zf := res == 0 }, ⟨d.offset, [], true⟩)
  | .mulOneOp isSigned is64 src =>
    -- `MUL` / `IMUL` with one operand: `rDX:rAX := rAX * src` at the operand width `w`. `raw` is
    -- the `2w`-bit product pattern (two's complement when signed). `CF = OF` is set when the
    -- upper half is significant: nonzero for `MUL`, not the sign extension of the lower half for
    -- `IMUL`.
    let bound : Nat := if is64 then 0x10000000000000000 else 0x100000000
    let a := (maskGprWidth is64 (s.gpr.get 0)).toNat
    let b := (maskGprWidth is64 (s.gpr.get src)).toNat
    let raw : Nat :=
      if isSigned then
        ((signedOfBound bound a * signedOfBound bound b) % ((bound * bound : Nat) : Int)).toNat
      else a * b
    let lo := maskGprWidth is64 (UInt64.ofNat (raw % bound))
    let hi := maskGprWidth is64 (UInt64.ofNat (raw / bound))
    let ovf := if isSigned then imulSignedOverflow bound a b else decide (raw / bound ≠ 0)
    ({ s with pc := nextPc, gpr := (s.gpr.set 0 lo).set 2 hi, cf := ovf, ofFlag := ovf },
      ⟨d.offset, [], true⟩)
  | .shiftImm sk is64 dst cnt =>
    let (res, cf', of', zf') := evalX86Shift sk is64 (s.gpr.get dst) cnt s.cf s.ofFlag s.zf
    ({ s with pc := nextPc, gpr := s.gpr.set dst res, cf := cf', ofFlag := of', zf := zf' }, ⟨d.offset, [], true⟩)
  | .cmovcc cc is64 dst src =>
    -- `X86State` has no `DOITM` bit, so the observation cannot depend on the mode: `true` here
    -- means "data-operand-independent when `DOITM` is set". The mode assumption is carried by
    -- `FuncContract.doitEnabled`, and `transferX86Instr` rejects `cmovcc` without it.
    -- Per Intel SDM, 32-bit `CMOVcc` in 64-bit mode zero-extends `dst[31:0]` into `dst[63:0]`
    -- even when the condition is false (`!taken`).
    let taken := evalX86Cond cc s
    let chosen := if taken then s.gpr.get src else s.gpr.get dst
    let gpr' := s.gpr.set dst (maskGprWidth is64 chosen)
    ({ s with pc := nextPc, gpr := gpr' }, ⟨d.offset, [], true⟩)
  | .testRegReg is64 r1 r2 =>
    let res := maskGprWidth is64 ((s.gpr.get r1) &&& (s.gpr.get r2))
    ({ s with pc := nextPc, cf := false, ofFlag := false, zf := res == 0 }, ⟨d.offset, [], true⟩)
  | .cmpRegReg is64 dst src =>
    let a := s.gpr.get dst
    let b := s.gpr.get src
    let (_, cf', zf') := evalX86Alu .sub is64 a b false
    let of' := evalX86AluOf .sub is64 a b false
    ({ s with pc := nextPc, cf := cf', ofFlag := of', zf := zf' }, ⟨d.offset, [], true⟩)
  | .cmpImm is64 dst imm =>
    let a := s.gpr.get dst
    let (_, cf', zf') := evalX86Alu .sub is64 a imm false
    let of' := evalX86AluOf .sub is64 a imm false
    ({ s with pc := nextPc, cf := cf', ofFlag := of', zf := zf' }, ⟨d.offset, [], true⟩)
  | .lea is64 dst addr =>
    let v := maskGprWidth is64 (evalX86Addr s nextPc addr)
    ({ s with pc := nextPc, gpr := s.gpr.set dst v }, ⟨d.offset, [], true⟩)
  | .storeImm8 addr imm =>
    let ea := evalX86Addr s nextPc addr
    ({ s with pc := nextPc, mem := writeMem8 s.mem ea imm }, ⟨d.offset, [(ea, 1)], true⟩)
  | .notReg is64 dst =>
    let res := maskGprWidth is64 (~~~(s.gpr.get dst))
    ({ s with pc := nextPc, gpr := s.gpr.set dst res }, ⟨d.offset, [], true⟩)
  | .setcc cc dst =>
    let taken := evalX86Cond cc s
    let cur := s.gpr.get dst
    let v := (cur &&& 0xFFFFFFFFFFFFFF00) ||| (if taken then 1 else 0)
    ({ s with pc := nextPc, gpr := s.gpr.set dst v }, ⟨d.offset, [], true⟩)
  | .bswap is64 dst =>
    let res := evalX86Bswap is64 (s.gpr.get dst)
    ({ s with pc := nextPc, gpr := s.gpr.set dst res }, ⟨d.offset, [], true⟩)
  | .sseMovdquLoad dst addr =>
    let ea := evalX86Addr s nextPc addr
    let q := readMem128 s.mem ea
    let old := s.ymm.get dst
    ({ s with pc := nextPc, ymm := s.ymm.set dst ⟨q.w0, q.w1, old.w2, old.w3⟩ },
     ⟨d.offset, [(ea, 16)], true⟩)
  | .ssePcmpeqb dst src =>
    let vd := s.ymm.get dst
    let vs := s.ymm.get src
    let eqWord (w1 w2 : UInt64) : UInt64 :=
      mapBytes64 (fun i => if getByte64 w1 i == getByte64 w2 i then 0xFF else 0x00)
    ({ s with pc := nextPc, ymm := s.ymm.set dst ⟨eqWord vd.w0 vs.w0, eqWord vd.w1 vs.w1, vd.w2, vd.w3⟩ },
     ⟨d.offset, [], true⟩)
  | .ssePand dst src =>
    let vd := s.ymm.get dst
    let vs := s.ymm.get src
    ({ s with pc := nextPc, ymm := s.ymm.set dst ⟨vd.w0 &&& vs.w0, vd.w1 &&& vs.w1, vd.w2, vd.w3⟩ },
     ⟨d.offset, [], true⟩)
  | .ssePmovmskb dst src =>
    let mask := evalPmovmskb128 (s.ymm.get src)
    ({ s with pc := nextPc, gpr := s.gpr.set dst mask }, ⟨d.offset, [], true⟩)
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
def stepArm64 (d : DecodedInstr Arm64Instr) (s : Arm64State) : (Arm64State × StepObs) :=
  let nextPc := d.offset + 4
  match d.instr with
  | .nop | .isb | .dmbIsh =>
    ({ s with pc := nextPc }, ⟨d.offset, [], true⟩)
  | .msrDit imm =>
    ({ s with pc := nextPc, dit := imm != 0 }, ⟨d.offset, [], true⟩)
  | .ret =>
    ({ s with halted := true }, ⟨d.offset, [], true⟩)
  | .aluReg op is64 rd rn rm sk sa =>
    let b := applyArmShift is64 (getArmGpr s rm) sk sa
    let (res, cf', zf') := evalArmAlu op is64 (getArmGpr s rn) b s.cf s.zf
    ({ s with pc := nextPc, gpr := setArmGpr s rd res, cf := cf', zf := zf' }, ⟨d.offset, [], true⟩)
  | .aluImm op is64 rd rn imm =>
    let (res, cf', zf') := evalArmAlu op is64 (getArmGpr s rn) imm s.cf s.zf
    ({ s with pc := nextPc, gpr := setArmGpr s rd res, cf := cf', zf := zf' }, ⟨d.offset, [], true⟩)
  | .movWide isMovn is64 rd imm16 sh =>
    let shifted := UInt64.ofNat imm16 <<< UInt64.ofNat sh
    let raw := if isMovn then ~~~shifted else shifted
    let res := maskGprWidth is64 raw
    ({ s with pc := nextPc, gpr := setArmGpr s rd res }, ⟨d.offset, [], true⟩)
  | .ubfm is64 rd rn immr imms =>
    let w := if is64 then 64 else 32
    let src := maskGprWidth is64 (getArmGpr s rn)
    let res :=
      if imms + 1 == w then maskGprWidth is64 (src >>> UInt64.ofNat immr)
      else if imms + 1 == immr then maskGprWidth is64 (src <<< UInt64.ofNat (w - immr))
      else
        let width := if immr ≤ imms then imms - immr + 1 else imms + 1
        let mask : UInt64 := if width ≥ 64 then 0 - 1 else (1 <<< UInt64.ofNat width) - 1
        if immr ≤ imms then maskGprWidth is64 ((src >>> UInt64.ofNat immr) &&& mask)
        else maskGprWidth is64 ((src &&& mask) <<< UInt64.ofNat (w - immr))
    ({ s with pc := nextPc, gpr := setArmGpr s rd res }, ⟨d.offset, [], true⟩)
  | .mulOp isUmulh rd rn rm =>
    let prod := (getArmGpr s rn).toNat * (getArmGpr s rm).toNat
    let res := if isUmulh then UInt64.ofNat (prod / 0x10000000000000000)
               else UInt64.ofNat (prod % 0x10000000000000000)
    ({ s with pc := nextPc, gpr := setArmGpr s rd res }, ⟨d.offset, [], s.dit⟩)
  | .csel cond isInv rd rn rm =>
    let taken := evalArmCond cond s
    let v := if taken then getArmGpr s rn
             else if isInv then ~~~(getArmGpr s rm) else getArmGpr s rm
    ({ s with pc := nextPc, gpr := setArmGpr s rd v }, ⟨d.offset, [], s.dit⟩)
  | .ldp64 rt1 rt2 rn off =>
    let ea := getArmGpr s rn + off
    let v1 := readMem64 s.mem ea
    let v2 := readMem64 s.mem (ea + 8)
    let s1 := { s with gpr := setArmGpr s rt1 v1 }
    ({ s1 with pc := nextPc, gpr := setArmGpr s1 rt2 v2 }, ⟨d.offset, [(ea, 8), (ea + 8, 8)], true⟩)
  | .stp64 rt1 rt2 rn off =>
    let ea := getArmGpr s rn + off
    let m1 := writeMem64 s.mem ea (getArmGpr s rt1)
    let m2 := writeMem64 m1 (ea + 8) (getArmGpr s rt2)
    ({ s with pc := nextPc, mem := m2 }, ⟨d.offset, [(ea, 8), (ea + 8, 8)], true⟩)
  | .strbPost rt rn postOff =>
    let ea := getArmGpr s rn
    let m' := writeMem8 s.mem ea (getArmGpr s rt).toUInt8
    ({ s with pc := nextPc, gpr := setArmGpr s rn (ea + postOff), mem := m' }, ⟨d.offset, [(ea, 1)], true⟩)
  | .ldrQ rt rn off =>
    let ea := getArmGpr s rn + off
    let v := readMem128 s.mem ea
    ({ s with pc := nextPc, vec := s.vec.set rt v }, ⟨d.offset, [(ea, 16)], true⟩)
  | .strQ rt rn off =>
    let ea := getArmGpr s rn + off
    let m' := writeMem128 s.mem ea (s.vec.get rt)
    ({ s with pc := nextPc, mem := m' }, ⟨d.offset, [(ea, 16)], true⟩)
  | .fmovDFromX vd xn =>
    ({ s with pc := nextPc, vec := s.vec.set vd ⟨getArmGpr s xn, 0⟩ }, ⟨d.offset, [], true⟩)
  | .veor16b vd vn vm =>
    let a := s.vec.get vn; let b := s.vec.get vm
    ({ s with pc := nextPc, vec := s.vec.set vd ⟨a.w0 ^^^ b.w0, a.w1 ^^^ b.w1⟩ }, ⟨d.offset, [], true⟩)
  | .vbcax16b vd vn vm va =>
    let n := s.vec.get vn; let m := s.vec.get vm; let a := s.vec.get va
    ({ s with pc := nextPc, vec := s.vec.set vd ⟨n.w0 ^^^ (m.w0 &&& (~~~a.w0)), n.w1 ^^^ (m.w1 &&& (~~~a.w1))⟩ },
     ⟨d.offset, [], true⟩)
  | .veor3_16b vd vn vm va =>
    let n := s.vec.get vn; let m := s.vec.get vm; let a := s.vec.get va
    ({ s with pc := nextPc, vec := s.vec.set vd ⟨n.w0 ^^^ m.w0 ^^^ a.w0, n.w1 ^^^ m.w1 ^^^ a.w1⟩ },
     ⟨d.offset, [], true⟩)
  | .vrax1_2d vd vn vm =>
    let n := s.vec.get vn; let m := s.vec.get vm
    let rol1 (x : UInt64) := (x <<< 1) ||| (x >>> 63)
    ({ s with pc := nextPc, vec := s.vec.set vd ⟨n.w0 ^^^ rol1 m.w0, n.w1 ^^^ rol1 m.w1⟩ }, ⟨d.offset, [], true⟩)
  | .vxar_2d vd vn vm imm6 =>
    let n := s.vec.get vn; let m := s.vec.get vm
    let ror (x : UInt64) :=
      let c := imm6 % 64
      if c == 0 then x else (x >>> UInt64.ofNat c) ||| (x <<< UInt64.ofNat (64 - c))
    ({ s with pc := nextPc, vec := s.vec.set vd ⟨ror (n.w0 ^^^ m.w0), ror (n.w1 ^^^ m.w1)⟩ }, ⟨d.offset, [], true⟩)
  | .vpmull isHigh vd vn vm =>
    let n := s.vec.get vn; let m := s.vec.get vm
    let p := if isHigh then clmul64 n.w1 m.w1 else clmul64 n.w0 m.w0
    ({ s with pc := nextPc, vec := s.vec.set vd p }, ⟨d.offset, [], s.dit⟩)
  | .vtrn is128 second elementBytes vd vn vm =>
    let n := s.vec.get vn; let m := s.vec.get vm
    let pick (i : Nat) : UInt8 :=
      let elem := i / elementBytes
      let src := if elem % 2 == 0 then n else m
      let k := (2 * (elem / 2) + (if second then 1 else 0)) * elementBytes + i % elementBytes
      if k < 8 then getByte64 src.w0 k else getByte64 src.w1 (k - 8)
    let out : Vec128 := ⟨mapBytes64 pick, if is128 then mapBytes64 (fun i => pick (i+8)) else 0⟩
    ({ s with pc := nextPc, vec := s.vec.set vd out }, ⟨d.offset, [], true⟩)
  | .vext16b vd vn vm imm4 =>
    let n := s.vec.get vn; let m := s.vec.get vm
    let getB (k : Nat) : UInt8 :=
      if k < 8 then getByte64 n.w0 k
      else if k < 16 then getByte64 n.w1 (k - 8)
      else if k < 24 then getByte64 m.w0 (k - 16)
      else getByte64 m.w1 (k - 24)
    let out : Vec128 :=
      ⟨mapBytes64 (fun i => getB (imm4 + i)), mapBytes64 (fun i => getB (imm4 + 8 + i))⟩
    ({ s with pc := nextPc, vec := s.vec.set vd out }, ⟨d.offset, [], true⟩)
  | .bCond cond targetPc =>
    let taken := evalArmCond cond s
    let tgt := if taken && targetPc ≥ 0 then targetPc.toNat else nextPc
    ({ s with pc := tgt }, ⟨d.offset, [], true⟩)
  | .cbzOrTbz _ | .udivOrSdiv _ | .varShiftReg _ | .regOffsetMem _ =>
    ({ s with halted := true }, ⟨d.offset, [], false⟩)

/-- Bounded-fuel `AArch64` execution returning the final state and leakage trace `List StepObs`. -/
def runArm64 (prog : List (DecodedInstr Arm64Instr)) : Nat → Arm64State → (Arm64State × List StepObs)
  | 0, s => (s, [])
  | fuel + 1, s =>
    if s.halted then (s, [])
    else match findInstrAtPc s.pc prog with
    | none => ({ s with halted := true }, [])
    | some d =>
      let (s', obs) := stepArm64 d s
      let (sFinal, restObs) := runArm64 prog fuel s'
      (sFinal, obs :: restObs)

/-! ## §5. 3-Way Hardware Constant-Time Noninterference & ABI Hygiene Verifier -/

/-- 3-level 16-way radix map (`0 .. 4095`) giving `O(1)` 3-step PC lookup in kernel `decide`. -/
structure PcMap (α : Type) where
  root : Bank16 (Option (Bank16 (Option (Bank16 (Option α)))))

def PcMap.empty {α : Type} : PcMap α :=
  ⟨Bank16.const none⟩

def PcMap.get {α : Type} (m : PcMap α) (pc : Nat) : Option α :=
  if pc ≥ 4096 then none
  else
    match Bank16.get m.root (pc / 256) with
    | none => none
    | some p1 =>
      match Bank16.get p1 ((pc / 16) % 16) with
      | none => none
      | some p0 => Bank16.get p0 (pc % 16)

def PcMap.set {α : Type} (m : PcMap α) (pc : Nat) (v : α) : PcMap α :=
  if pc ≥ 4096 then m
  else
    let i2 := pc / 256
    let i1 := (pc / 16) % 16
    let i0 := pc % 16
    let p1 := match Bank16.get m.root i2 with | some b => b | none => Bank16.const none
    let p0 := match Bank16.get p1 i1 with | some b => b | none => Bank16.const none
    let p0' := Bank16.set p0 i0 (some v)
    let p1' := Bank16.set p1 i1 (some p0')
    ⟨Bank16.set m.root i2 (some p1')⟩

def PcMap.all {α : Type} (pred : Nat → α → Bool) (m : PcMap α) : Bool :=
  Bank16.allIdx (fun i2 opt1 =>
    match opt1 with
    | none => true
    | some p1 =>
      Bank16.allIdx (fun i1 opt0 =>
        match opt0 with
        | none => true
        | some p0 =>
          Bank16.allIdx (fun i0 optV =>
            match optV with
            | none => true
            | some v => pred (i2 * 256 + i1 * 16 + i0) v) p0) p1) m.root

/-- Function-level constant-time & ABI hygiene contract $\Gamma$.

    `doitEnabled` records whether the contract assumes the processor runs the function in
    data-operand-independent-timing mode (`IA32_UARCH_MISC_CTL[DOITM] = 1` on `x86_64`). User-mode
    code cannot change that bit, so it is an assumption about the execution environment and not
    part of `X86State`. The `x86_64` checker consults it: `transferX86Instr` rejects `cmovcc`
    when it is `false`. `AArch64` tracks `PSTATE.DIT` in its machine state instead. -/
structure FuncContract where
  symName : String
  pubGprs : List Nat
  pubMemRegions : List (Nat × Nat)
  wipedScratchGprs : List Nat
  usesRbpFrame : Bool
  outPtrReg : Nat
  outBytes : Nat
  doitEnabled : Bool := true
  deriving DecidableEq, Repr

/-- Abstract origin lattice for `x86_64` GPRs tracking relational publicity + callee-saved/frame origins. -/
inductive RegOrigin where
  | initSame (r : Nat)
  | initOwn  (r : Nat)
  | spMinus8
  | spAligned32
  | frameSp
  | zeroConst
  | constVal (c : UInt64)
  | pubVal
  | secretVal
  deriving DecidableEq, Repr

def RegOrigin.isPublic : RegOrigin → Bool
  | .initSame _ | .spMinus8 | .spAligned32 | .frameSp | .zeroConst | .constVal _ | .pubVal => true
  | .initOwn _ | .secretVal => false

def RegOrigin.le (a b : RegOrigin) : Bool :=
  a == b || b == .secretVal || (b == .pubVal && a.isPublic)

def RegOrigin.join (a b : RegOrigin) : RegOrigin :=
  if a == b then a
  else if a.isPublic && b.isPublic then .pubVal
  else .secretVal

/-- Abstract origin lattice for SIMD vector registers (`ymm0..ymm15` / `v0..v31`). -/
inductive VecOrigin where
  | initVec (r : Nat)
  | zeroConst
  | pubVal
  | secretVal
  deriving DecidableEq, Repr

def VecOrigin.isPublic : VecOrigin → Bool
  | .zeroConst | .pubVal => true
  | .initVec _ | .secretVal => false

def VecOrigin.le (a b : VecOrigin) : Bool :=
  a == b || b == .secretVal || (b == .pubVal && a.isPublic)

def VecOrigin.join (a b : VecOrigin) : VecOrigin :=
  if a == b then a
  else if a.isPublic && b.isPublic then .pubVal
  else .secretVal

/-- Abstract relational state at a single `x86_64` PC. -/
structure X86AbsState where
  gpr : Bank16 RegOrigin
  ymm : Bank16 VecOrigin
  cfPub : Bool
  ofPub : Bool
  zfPub : Bool
  ymmDirty : Bool
  memUnmodified : Bool
  rbpSaved : Bool
  stackZeroLoop : Nat
  deriving DecidableEq, Repr

def X86AbsState.le (a b : X86AbsState) : Bool :=
  a.gpr.allIdx (fun i oa => oa.le (b.gpr.get i)) &&
  a.ymm.allIdx (fun i va => va.le (b.ymm.get i)) &&
  (!b.cfPub || a.cfPub) &&
  (!b.ofPub || a.ofPub) &&
  (!b.zfPub || a.zfPub) &&
  (b.ymmDirty || !a.ymmDirty) &&
  (!b.memUnmodified || a.memUnmodified) &&
  (!b.rbpSaved || a.rbpSaved) &&
  (b.stackZeroLoop == 0 || a.stackZeroLoop == b.stackZeroLoop)

def X86AbsState.join (a b : X86AbsState) : X86AbsState :=
  { gpr := Bank16.ofFn (fun i => RegOrigin.join (a.gpr.get i) (b.gpr.get i))
    ymm := Bank16.ofFn (fun i => VecOrigin.join (a.ymm.get i) (b.ymm.get i))
    cfPub := a.cfPub && b.cfPub
    ofPub := a.ofPub && b.ofPub
    zfPub := a.zfPub && b.zfPub
    ymmDirty := a.ymmDirty || b.ymmDirty
    memUnmodified := a.memUnmodified && b.memUnmodified
    rbpSaved := a.rbpSaved && b.rbpSaved
    stackZeroLoop := if a.stackZeroLoop == b.stackZeroLoop then a.stackZeroLoop else 0 }

def isX86CalleeSavedGpr (r : Nat) : Bool :=
  r == 3 || r == 5 || r == 12 || r == 13 || r == 14 || r == 15

def initX86AbsState (c : FuncContract) : X86AbsState :=
  { gpr := Bank16.ofFn (fun r =>
      if r ∈ c.pubGprs then .initSame r
      else if isX86CalleeSavedGpr r then .initOwn r
      else .secretVal)
    ymm := Bank16.ofFn VecOrigin.initVec
    cfPub := false
    ofPub := false
    zfPub := false
    ymmDirty := false
    memUnmodified := true
    rbpSaved := false
    stackZeroLoop := 0 }

def x86AddrIsPublic (st : X86AbsState) : X86MemAddr → Bool
  | .baseDisp base _ => (st.gpr.get base).isPublic
  | .absDisp _ => true
  | .ripDisp _ => true
  | .indexedSib baseOpt idx _ _ =>
    (st.gpr.get idx).isPublic && match baseOpt with | none => true | some b => (st.gpr.get b).isPublic

def isInPubMemRegion (c : FuncContract) (st : X86AbsState) (addr : X86MemAddr) (widthBytes : Nat) : Bool :=
  if !st.memUnmodified then false
  else match addr with
  | .baseDisp base disp =>
    match st.gpr.get base with
    | .initSame r =>
      r ∈ c.pubGprs &&
      c.pubMemRegions.any (fun (ptrReg, regionLen) =>
        ptrReg == r && disp.toNat + widthBytes ≤ regionLen)
    | _ => false
  | _ => false

def storePreservesSavedRbp (c : FuncContract) (st : X86AbsState) (addr : X86MemAddr) (widthBytes : Nat) : Bool :=
  if !st.rbpSaved then false
  else if !c.usesRbpFrame then false
  else match addr with
  | .baseDisp base disp =>
    if st.gpr.get base == .frameSp && disp.toNat + widthBytes ≤ 0x320 then true
    else if st.gpr.get base == .initSame c.outPtrReg &&
            c.outBytes == 0x320 && disp.toNat + widthBytes ≤ 0x320 then true
    else if base == 0 && disp == 0 && widthBytes == 32 && st.stackZeroLoop == 1 then true
    else false
  | _ => false

/-- Publicity of a condition code, fail-closed: codes `2, 3` read `CF`, codes `4, 5` read `ZF`,
    and every other code is treated as secret-dependent because it reads flags the abstract
    state does not track (`SF`, `PF`, or `CF` and `ZF` together). -/
def x86CondIsPublic (cc : Nat) (st : X86AbsState) : Bool :=
  if cc == 2 || cc == 3 then st.cfPub
  else if cc == 4 || cc == 5 then st.zfPub
  else false

/-- A condition code can be classified public only if its semantics are modelled. -/
theorem x86CondIsPublic_supported {cc : Nat} {st : X86AbsState}
    (h : x86CondIsPublic cc st = true) : x86CondSupported cc = true := by
  unfold x86CondIsPublic at h
  unfold x86CondSupported
  by_cases c2 : cc == 2 <;> by_cases c3 : cc == 3 <;> by_cases c4 : cc == 4 <;>
    by_cases c5 : cc == 5 <;> simp_all

def x86AddrRegsValid : X86MemAddr → Bool
  | .baseDisp base _ => base < 16
  | .absDisp _ => true
  | .ripDisp _ => true
  | .indexedSib baseOpt idx _ _ =>
    idx < 16 && match baseOpt with | none => true | some b => b < 16

def x86InstrRegsValid : X86Instr → Bool
  | .nop | .mfence | .ret | .vzeroupper | .vzeroall | .jcc _ _ | .jmpRel _ | .indirectBr _ | .divRem _ => true
  | .pushReg r | .popReg r | .movImm _ r _ | .aluImm _ _ r _ | .cmpImm _ r _ | .incDec _ _ r
  | .negReg _ r | .notReg _ r | .setcc _ r | .bswap _ r | .mulOneOp _ _ r | .shiftImm _ _ r _ | .varShiftCl _ r => r < 16
  | .movRegReg _ d s | .aluRegReg _ _ d s | .testRegReg _ d s | .cmpRegReg _ d s | .cmovcc _ _ d s | .adcx d s | .adox d s
  | .ssePcmpeqb d s | .ssePand d s | .ssePmovmskb d s
  | .vmovGprToXmm _ d s | .vpbroadcast _ d s | .vshiftImm _ _ d s _ => d < 16 && s < 16
  | .mulx h l s | .vbinOp _ _ h l s | .vpclmulqdq _ h l s _
  | .vgf2p8affineqb _ h l s _ | .vperm2i128 h l s _ => h < 16 && l < 16 && s < 16
  | .loadGpr w _ r a | .storeGpr w r a => (w == 1 || w == 8) && r < 16 && x86AddrRegsValid a
  | .lea _ r a | .sseMovdquLoad r a
  | .aluLoad64 _ r a
  | .vload _ r a | .vstore _ r a | .vpbroadcastLoad64 r a => r < 16 && x86AddrRegsValid a
  | .storeImm8 a _ => x86AddrRegsValid a
  | .vpxorLoad128 d s a | .vpxorLoad256 d s a => d < 16 && s < 16 && x86AddrRegsValid a
  | .vpgather _ a => x86AddrRegsValid a

/-- Abstract transfer function for one `x86_64` instruction, returning successor `(pc, state)` pairs,
    or `none` if any constant-time (`PC-NI`, `Mem-NI`, `DOIT-NI`) or ABI hygiene rule is violated. -/
def transferX86Instr (c : FuncContract) (d : DecodedInstr X86Instr) (st : X86AbsState) :
    Option (List (Nat × X86AbsState)) :=
  if !x86InstrRegsValid d.instr then none
  else
  let nextPc := d.offset + d.byteLen
  let stNoLoop := { st with stackZeroLoop := 0 }
  match d.instr with
  | .nop | .mfence =>
    some [(nextPc, stNoLoop)]
  | .pushReg r =>
    if c.usesRbpFrame && r == 5 && st.gpr.get 4 == .initSame 4 && st.gpr.get 5 == .initOwn 5 &&
       4 ∈ c.pubGprs && !st.rbpSaved then
      some [(nextPc, { stNoLoop with
        gpr := st.gpr.set 4 .spMinus8
        memUnmodified := false
        rbpSaved := true })]
    else none
  | .popReg r =>
    if c.usesRbpFrame && r == 5 && st.gpr.get 4 == .spMinus8 && st.rbpSaved then
      some [(nextPc, { stNoLoop with
        gpr := (st.gpr.set 4 (.initSame 4)).set 5 (.initOwn 5) })]
    else none
  | .ret =>
    let spOk := st.gpr.get 4 == .initSame 4 && 4 ∈ c.pubGprs
    let calleeOk :=
      (st.gpr.get 3).le (.initOwn 3) || st.gpr.get 3 == .initSame 3
    let allCalleeOk :=
      calleeOk &&
      ([3, 5, 12, 13, 14, 15].all (fun r =>
        st.gpr.get r == .initOwn r || st.gpr.get r == .initSame r))
    let ymmClean := !st.ymmDirty
    let vecWiped := st.ymm.allIdx (fun _ vo => vo != .secretVal && vo != .pubVal)
    let gprWiped := c.wipedScratchGprs.all (fun r => st.gpr.get r == .zeroConst)
    if spOk && allCalleeOk && ymmClean && vecWiped && gprWiped then some [] else none
  | .movRegReg is64 dst src =>
    if is64 && dst == 0 && src == 4 && st.gpr.get 4 == .frameSp &&
       st.gpr.get 1 == .constVal 25 then
      some [(nextPc, { stNoLoop with
        gpr := (st.gpr.set 0 .pubVal).set 1 .pubVal
        stackZeroLoop := 1 })]
    else
      let orig :=
        if is64 then st.gpr.get src
        else if (st.gpr.get src).isPublic then .pubVal else .secretVal
      some [(nextPc, { stNoLoop with gpr := st.gpr.set dst orig })]
  | .movImm is64 dst imm =>
    let v := maskGprWidth is64 imm
    let orig : RegOrigin := if v == 0 then .zeroConst else .constVal v
    some [(nextPc, { stNoLoop with gpr := st.gpr.set dst orig })]
  | .loadGpr wBytes _is64 dst addr =>
    if !x86AddrIsPublic st addr then none
    else
      let orig : RegOrigin := if isInPubMemRegion c st addr wBytes then .pubVal else .secretVal
      some [(nextPc, { stNoLoop with gpr := st.gpr.set dst orig })]
  | .storeGpr wBytes _src addr =>
    if !x86AddrIsPublic st addr then none
    else
      let rbpOk := if st.rbpSaved then storePreservesSavedRbp c st addr wBytes else false
      some [(nextPc, { stNoLoop with memUnmodified := false, rbpSaved := rbpOk })]
  | .aluRegReg op _is64 dst src =>
    if op == .xorOp && dst == src then
      some [(nextPc, { stNoLoop with
        gpr := st.gpr.set dst .zeroConst
        cfPub := true, ofPub := true, zfPub := true })]
    else if op == .sbb && dst == src then
      let resOrig : RegOrigin := if st.cfPub then .pubVal else .secretVal
      some [(nextPc, { stNoLoop with
        gpr := st.gpr.set dst resOrig
        cfPub := st.cfPub, zfPub := st.cfPub })]
    else
      let aPub := (st.gpr.get dst).isPublic
      let bPub := (st.gpr.get src).isPublic
      let carryNeed := if op == .adc || op == .sbb then st.cfPub else true
      let bothPub := aPub && bPub && carryNeed
      let of' := if op == .andOp || op == .orOp || op == .xorOp then true else false
      some [(nextPc, { stNoLoop with
        gpr := st.gpr.set dst (if bothPub then .pubVal else .secretVal)
        cfPub := bothPub, ofPub := of', zfPub := bothPub })]
  | .aluLoad64 op dst addr =>
    if !x86AddrIsPublic st addr then none
    else
      let mPub := isInPubMemRegion c st addr 8
      let bothPub := (st.gpr.get dst).isPublic && mPub &&
                     (if op == .adc || op == .sbb then st.cfPub else true)
      let of' := if op == .andOp || op == .orOp || op == .xorOp then true else false
      some [(nextPc, { stNoLoop with
        gpr := st.gpr.set dst (if bothPub then .pubVal else .secretVal)
        cfPub := bothPub, ofPub := of', zfPub := bothPub })]
  | .aluImm op is64 dst imm =>
    if is64 && op == .andOp && dst == 4 && imm == 0xFFFFFFFFFFFFFFE0 && st.gpr.get 4 == .spMinus8 then
      some [(nextPc, { stNoLoop with
        gpr := st.gpr.set 4 .spAligned32
        cfPub := true, ofPub := true, zfPub := true })]
    else if is64 && op == .sub && dst == 4 && imm == 0x340 && st.gpr.get 4 == .spAligned32 then
      some [(nextPc, { stNoLoop with
        gpr := st.gpr.set 4 .frameSp
        cfPub := true, ofPub := false, zfPub := true })]
    else if is64 && op == .add && dst == 0 && imm == 0x20 && st.stackZeroLoop == 1 then
      some [(nextPc, { st with
        gpr := st.gpr.set 0 .pubVal
        cfPub := true, ofPub := false, zfPub := true
        stackZeroLoop := 2 })]
    else
      let aPub := (st.gpr.get dst).isPublic
      let carryNeed := if op == .adc || op == .sbb then st.cfPub else true
      let bothPub := aPub && carryNeed
      let of' := if op == .andOp || op == .orOp || op == .xorOp then true else false
      some [(nextPc, { stNoLoop with
        gpr := st.gpr.set dst (if bothPub then .pubVal else .secretVal)
        cfPub := bothPub, ofPub := of', zfPub := bothPub })]
  | .incDec isInc is64 dst =>
    if !isInc && !is64 && dst == 1 && st.stackZeroLoop == 2 then
      some [(nextPc, { st with
        gpr := st.gpr.set 1 .pubVal
        ofPub := true
        zfPub := true
        stackZeroLoop := 3 })]
    else
      let p := (st.gpr.get dst).isPublic
      some [(nextPc, { stNoLoop with
        gpr := st.gpr.set dst (if p then .pubVal else .secretVal)
        ofPub := p
        zfPub := p })]
  | .negReg _is64 dst =>
    let p := (st.gpr.get dst).isPublic
    some [(nextPc, { stNoLoop with
      gpr := st.gpr.set dst (if p then .pubVal else .secretVal)
      cfPub := p, ofPub := p, zfPub := p })]
  | .mulOneOp _isSigned _is64 src =>
    let p := (st.gpr.get 0).isPublic && (st.gpr.get src).isPublic
    let o : RegOrigin := if p then .pubVal else .secretVal
    some [(nextPc, { stNoLoop with
      gpr := (st.gpr.set 0 o).set 2 o
      cfPub := false, ofPub := false, zfPub := false })]
  | .shiftImm sk is64 dst cnt =>
    let p := (st.gpr.get dst).isPublic
    some [(nextPc, { stNoLoop with
      gpr := st.gpr.set dst (if p then .pubVal else .secretVal)
      cfPub := false, ofPub := false,
      zfPub := if x86ShiftPreservesZf sk is64 cnt then st.zfPub else p })]
  | .cmovcc cc _is64 dst src =>
    -- Rejected unless the condition code is modelled and the contract assumes `DOITM`:
    -- `CMOVcc` is data-operand-independent only in that mode.
    if !x86CondSupported cc || !c.doitEnabled then none
    else
      let cPub := x86CondIsPublic cc st
      let p := cPub && (st.gpr.get dst).isPublic && (st.gpr.get src).isPublic
      some [(nextPc, { stNoLoop with gpr := st.gpr.set dst (if p then .pubVal else .secretVal) })]
  | .testRegReg _is64 r1 r2 =>
    let p := (st.gpr.get r1).isPublic && (st.gpr.get r2).isPublic
    some [(nextPc, { stNoLoop with cfPub := true, ofPub := true, zfPub := p })]
  | .cmpRegReg _is64 dst src =>
    let p := (st.gpr.get dst).isPublic && (st.gpr.get src).isPublic
    some [(nextPc, { stNoLoop with cfPub := p, ofPub := p, zfPub := p })]
  | .cmpImm _is64 dst _imm =>
    let p := (st.gpr.get dst).isPublic
    some [(nextPc, { stNoLoop with cfPub := p, ofPub := p, zfPub := p })]
  | .lea _is64 dst addr =>
    let p := x86AddrIsPublic st addr
    some [(nextPc, { stNoLoop with gpr := st.gpr.set dst (if p then .pubVal else .secretVal) })]
  | .storeImm8 addr _imm =>
    if !x86AddrIsPublic st addr then none
    else
      let rbpOk := if st.rbpSaved then storePreservesSavedRbp c st addr 1 else false
      some [(nextPc, { stNoLoop with memUnmodified := false, rbpSaved := rbpOk })]
  | .notReg _is64 dst =>
    let p := (st.gpr.get dst).isPublic
    some [(nextPc, { stNoLoop with gpr := st.gpr.set dst (if p then .pubVal else .secretVal) })]
  | .setcc cc dst =>
    if !x86CondSupported cc then none
    else
      let p := x86CondIsPublic cc st && (st.gpr.get dst).isPublic
      some [(nextPc, { stNoLoop with gpr := st.gpr.set dst (if p then .pubVal else .secretVal) })]
  | .bswap _is64 dst =>
    let p := (st.gpr.get dst).isPublic
    some [(nextPc, { stNoLoop with gpr := st.gpr.set dst (if p then .pubVal else .secretVal) })]
  | .sseMovdquLoad dst addr =>
    if !x86AddrIsPublic st addr then none
    else
      some [(nextPc, { stNoLoop with ymm := st.ymm.set dst .secretVal })]
  | .ssePcmpeqb dst _src =>
    some [(nextPc, { stNoLoop with ymm := st.ymm.set dst .secretVal })]
  | .ssePand dst _src =>
    some [(nextPc, { stNoLoop with ymm := st.ymm.set dst .secretVal })]
  | .ssePmovmskb dst src =>
    let p := (st.ymm.get src).isPublic
    some [(nextPc, { stNoLoop with gpr := st.gpr.set dst (if p then .pubVal else .secretVal) })]
  | .mulx hiDst loDst src =>
    let p := (st.gpr.get 2).isPublic && (st.gpr.get src).isPublic
    let o : RegOrigin := if p then .pubVal else .secretVal
    some [(nextPc, { stNoLoop with gpr := (st.gpr.set loDst o).set hiDst o })]
  | .adcx dst src =>
    let p := (st.gpr.get dst).isPublic && (st.gpr.get src).isPublic && st.cfPub
    some [(nextPc, { stNoLoop with
      gpr := st.gpr.set dst (if p then .pubVal else .secretVal)
      cfPub := p })]
  | .adox dst src =>
    let p := (st.gpr.get dst).isPublic && (st.gpr.get src).isPublic && st.ofPub
    some [(nextPc, { stNoLoop with
      gpr := st.gpr.set dst (if p then .pubVal else .secretVal)
      ofPub := p })]
  | .jcc cc targetPc =>
    if !x86CondIsPublic cc st || targetPc < 0 || targetPc.toNat ≥ 4096 then none
    else if st.stackZeroLoop == 3 && cc == 5 then
      some [(targetPc.toNat, { st with stackZeroLoop := 1 }), (nextPc, stNoLoop)]
    else
      some [(targetPc.toNat, stNoLoop), (nextPc, stNoLoop)]
  | .jmpRel targetPc =>
    if targetPc < 0 || targetPc.toNat ≥ 4096 then none
    else some [(targetPc.toNat, stNoLoop)]
  | .indirectBr _ | .divRem _ | .varShiftCl _ _ | .vpgather _ _ =>
    none
  | .vzeroupper =>
    let ymmPreserved := Bank16.ofFn (fun i =>
      match st.ymm.get i with
      | .zeroConst => VecOrigin.zeroConst
      | .pubVal => VecOrigin.pubVal
      | .initVec r => VecOrigin.initVec r
      | .secretVal => VecOrigin.secretVal)
    some [(nextPc, { stNoLoop with ymm := ymmPreserved, ymmDirty := false })]
  | .vzeroall =>
    some [(nextPc, { stNoLoop with ymm := Bank16.ofFn (fun _ => .zeroConst), ymmDirty := false })]
  | .vload is256 dst addr =>
    if !x86AddrIsPublic st addr then none
    else
      let w := if is256 then 32 else 16
      let vo : VecOrigin := if isInPubMemRegion c st addr w then .pubVal else .secretVal
      some [(nextPc, { stNoLoop with
        ymm := st.ymm.set dst vo
        ymmDirty := st.ymmDirty || is256 })]
  | .vstore is256 _src addr =>
    if !x86AddrIsPublic st addr then none
    else
      let w := if is256 then 32 else 16
      let rbpOk := if st.rbpSaved then storePreservesSavedRbp c st addr w else false
      let nextLoop := if st.stackZeroLoop == 1 && addr == .baseDisp 0 0 && is256 then 1 else 0
      some [(nextPc, { st with
        memUnmodified := false
        rbpSaved := rbpOk
        stackZeroLoop := nextLoop })]
  | .vmovGprToXmm _is64 dstVec srcGpr =>
    let vo : VecOrigin :=
      if st.gpr.get srcGpr == .zeroConst then .zeroConst
      else if (st.gpr.get srcGpr).isPublic then .pubVal
      else .secretVal
    some [(nextPc, { stNoLoop with ymm := st.ymm.set dstVec vo })]
  | .vpbroadcast _isQword dst srcVec =>
    let svo := st.ymm.get srcVec
    let vo : VecOrigin :=
      if svo == .zeroConst then .zeroConst else if svo.isPublic then .pubVal else .secretVal
    some [(nextPc, { stNoLoop with ymm := st.ymm.set dst vo, ymmDirty := true })]
  | .vpbroadcastLoad64 dst addr =>
    if !x86AddrIsPublic st addr then none
    else
      let vo : VecOrigin := if isInPubMemRegion c st addr 8 then .pubVal else .secretVal
      some [(nextPc, { stNoLoop with ymm := st.ymm.set dst vo, ymmDirty := true })]
  | .vbinOp op is256 dst src1 src2 =>
    if op == .vpxor && src1 == src2 then
      some [(nextPc, { stNoLoop with
        ymm := st.ymm.set dst .zeroConst
        ymmDirty := st.ymmDirty || is256 })]
    else
      let p := (st.ymm.get src1).isPublic && (st.ymm.get src2).isPublic
      some [(nextPc, { stNoLoop with
        ymm := st.ymm.set dst (if p then .pubVal else .secretVal)
        ymmDirty := st.ymmDirty || is256 })]
  | .vpxorLoad128 dst src1 addr =>
    if !x86AddrIsPublic st addr then none
    else
      let p := (st.ymm.get src1).isPublic && isInPubMemRegion c st addr 16
      some [(nextPc, { stNoLoop with
        ymm := st.ymm.set dst (if p then .pubVal else .secretVal)
        ymmDirty := st.ymmDirty })]
  | .vpxorLoad256 dst src1 addr =>
    if !x86AddrIsPublic st addr then none
    else
      let p := (st.ymm.get src1).isPublic && isInPubMemRegion c st addr 32
      some [(nextPc, { stNoLoop with
        ymm := st.ymm.set dst (if p then .pubVal else .secretVal)
        ymmDirty := true })]
  | .vshiftImm _sk is256 dst src _imm =>
    let svo := st.ymm.get src
    let vo : VecOrigin :=
      if svo == .zeroConst then .zeroConst else if svo.isPublic then .pubVal else .secretVal
    some [(nextPc, { stNoLoop with
      ymm := st.ymm.set dst vo
      ymmDirty := st.ymmDirty || is256 })]
  | .vpclmulqdq is256 dst src1 src2 _imm =>
    let p := (st.ymm.get src1).isPublic && (st.ymm.get src2).isPublic
    some [(nextPc, { stNoLoop with
      ymm := st.ymm.set dst (if p then .pubVal else .secretVal)
      ymmDirty := st.ymmDirty || is256 })]
  | .vgf2p8affineqb is256 dst src1 src2 _imm =>
    let p := (st.ymm.get src1).isPublic && (st.ymm.get src2).isPublic
    some [(nextPc, { stNoLoop with
      ymm := st.ymm.set dst (if p then .pubVal else .secretVal)
      ymmDirty := st.ymmDirty || is256 })]
  | .vperm2i128 dst src1 src2 _imm =>
    let p := (st.ymm.get src1).isPublic && (st.ymm.get src2).isPublic
    some [(nextPc, { stNoLoop with
      ymm := st.ymm.set dst (if p then .pubVal else .secretVal)
      ymmDirty := true })]

def mergeX86Succs (inv : PcMap X86AbsState) : List (Nat × X86AbsState) → PcMap X86AbsState
  | [] => inv
  | (pc, stNew) :: rest =>
    let merged := match inv.get pc with
      | none => stNew
      | some stOld => X86AbsState.join stOld stNew
    mergeX86Succs (inv.set pc merged) rest

def propagateX86Pass (c : FuncContract) : List (DecodedInstr X86Instr) → PcMap X86AbsState → Option (PcMap X86AbsState)
  | [], inv => some inv
  | d :: ds, inv =>
    match inv.get d.offset with
    | none => propagateX86Pass c ds inv
    | some st =>
      match transferX86Instr c d st with
      | none => none
      | some succs => propagateX86Pass c ds (mergeX86Succs inv succs)

def buildProgMap {Instr : Type} : List (DecodedInstr Instr) → PcMap (DecodedInstr Instr)
  | [] => PcMap.empty
  | d :: ds => (buildProgMap ds).set d.offset d

def inferX86Invariant (prog : List (DecodedInstr X86Instr)) (c : FuncContract) : Option (PcMap X86AbsState) := do
  let inv0 := PcMap.empty.set 0 (initX86AbsState c)
  let inv1 ← propagateX86Pass c prog inv0
  let inv2 ← propagateX86Pass c prog inv1
  let inv3 ← propagateX86Pass c prog inv2
  propagateX86Pass c prog inv3

def verifyX86Invariant (prog : List (DecodedInstr X86Instr)) (c : FuncContract) (inv : PcMap X86AbsState) : Bool :=
  let progMap := buildProgMap prog
  let entryOk := match inv.get 0 with
    | none => false
    | some st0 => (initX86AbsState c).le st0
  entryOk &&
  inv.all (fun pc st =>
    match progMap.get pc with
    | none => false
    | some d =>
      match transferX86Instr c d st with
      | none => false
      | some succs =>
        succs.all (fun (npc, nst) =>
          match inv.get npc with
          | none => false
          | some dstSt => nst.le dstSt))

/-- Certified `x86_64` 3-Way Constant-Time NI + ABI Hygiene verifier. -/
def checkX86ThreeWayNI (code : List UInt8) (c : FuncContract) : Bool :=
  match decodeX86Stream code with
  | none => false
  | some prog =>
    match prog with
    | [] => false
    | _ :: _ =>
      match inferX86Invariant prog c with
      | none => false
      | some inv => verifyX86Invariant prog c inv

/-! ### `AArch64` Abstract Domain, Invariant Synthesis & Deductive Certificate Checker -/

inductive ArmRegOrigin where
  | initSame (r : Nat)
  | initOwn  (r : Nat)
  | zeroConst
  | pubVal
  | secretVal
  deriving DecidableEq, Repr

def ArmRegOrigin.isPublic : ArmRegOrigin → Bool
  | .initSame _ | .zeroConst | .pubVal => true
  | .initOwn _ | .secretVal => false

def ArmRegOrigin.le (a b : ArmRegOrigin) : Bool :=
  a == b || b == .secretVal || (b == .pubVal && a.isPublic)

def ArmRegOrigin.join (a b : ArmRegOrigin) : ArmRegOrigin :=
  if a == b then a
  else if a.isPublic && b.isPublic then .pubVal
  else .secretVal

structure Arm64AbsState where
  dit : Bool := true
  gpr : Bank32 ArmRegOrigin
  vec : Bank32 VecOrigin
  cfPub : Bool
  zfPub : Bool
  deriving DecidableEq, Repr

def Arm64AbsState.le (a b : Arm64AbsState) : Bool :=
  (a.dit == b.dit) && a.gpr.allIdx (fun i oa => oa.le (b.gpr.get i)) &&
  a.vec.allIdx (fun i va => va.le (b.vec.get i)) &&
  (!b.cfPub || a.cfPub) &&
  (!b.zfPub || a.zfPub)

def Arm64AbsState.join (a b : Arm64AbsState) : Arm64AbsState :=
  { dit := a.dit && b.dit
    gpr := Bank32.ofFn (fun i => ArmRegOrigin.join (a.gpr.get i) (b.gpr.get i))
    vec := Bank32.ofFn (fun i => VecOrigin.join (a.vec.get i) (b.vec.get i))
    cfPub := a.cfPub && b.cfPub
    zfPub := a.zfPub && b.zfPub }

def isArm64CalleeSavedGpr (r : Nat) : Bool :=
  19 ≤ r && r ≤ 30

def isArm64CalleeSavedVec (v : Nat) : Bool :=
  8 ≤ v && v ≤ 15

def initArm64AbsState (c : FuncContract) : Arm64AbsState :=
  { gpr := Bank32.ofFn (fun r =>
      if r == 31 then .zeroConst
      else if r ∈ c.pubGprs then .initSame r
      else if isArm64CalleeSavedGpr r then .initOwn r
      else .secretVal)
    vec := Bank32.ofFn VecOrigin.initVec
    cfPub := false
    zfPub := false }

def getArmAbsGpr (st : Arm64AbsState) (r : Nat) : ArmRegOrigin :=
  if r == 31 then .zeroConst else st.gpr.get r

def setArmAbsGpr (st : Arm64AbsState) (r : Nat) (o : ArmRegOrigin) : Bank32 ArmRegOrigin :=
  if r == 31 then st.gpr else st.gpr.set r o

def armCondIsPublic (cond : Nat) (st : Arm64AbsState) : Bool :=
  if cond == 0 || cond == 1 then st.zfPub else st.cfPub

def arm64InstrRegsValid : Arm64Instr → Bool
  | .nop | .msrDit _ | .isb | .dmbIsh | .ret | .bCond _ _
  | .cbzOrTbz _ | .udivOrSdiv _ | .varShiftReg _ | .regOffsetMem _ => true
  | .movWide _ _ rd _ _ => rd < 32
  | .aluImm _ _ rd rn _ | .ubfm _ rd rn _ _ | .strbPost rd rn _
  | .ldrQ rd rn _ | .strQ rd rn _ | .fmovDFromX rd rn => rd < 32 && rn < 32
  | .aluReg _ _ rd rn rm _ _ | .mulOp _ rd rn rm | .csel _ _ rd rn rm
  | .ldp64 rd rn rm _ | .stp64 rd rn rm _ | .veor16b rd rn rm
  | .vtrn _ _ _ rd rn rm | .vrax1_2d rd rn rm | .vxar_2d rd rn rm _ | .vpmull _ rd rn rm | .vext16b rd rn rm _ =>
    rd < 32 && rn < 32 && rm < 32
  | .vbcax16b vd vn vm va | .veor3_16b vd vn vm va =>
    vd < 32 && vn < 32 && vm < 32 && va < 32

def armRequiresDit : Arm64Instr → Bool
  | .mulOp _ _ _ _ | .csel _ _ _ _ _ | .vpmull _ _ _ _ => true
  | _ => false

def transferArm64Instr (c : FuncContract) (d : DecodedInstr Arm64Instr) (st : Arm64AbsState) :
    Option (List (Nat × Arm64AbsState)) :=
  if armRequiresDit d.instr && !st.dit then none
  else if !arm64InstrRegsValid d.instr then none
  else
  let nextPc := d.offset + 4
  match d.instr with
  | .msrDit imm => some [(nextPc, { st with dit := imm != 0 })]
  | .nop | .isb | .dmbIsh =>
    some [(nextPc, st)]
  | .ret =>
    let calleeGprOk :=
      [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30].all (fun r =>
        st.gpr.get r == .initOwn r || st.gpr.get r == .initSame r)
    let calleeVecOk :=
      [8, 9, 10, 11, 12, 13, 14, 15].all (fun v => st.vec.get v == .initVec v)
    let vecWiped := st.vec.allIdx (fun _ vo => vo != .secretVal && vo != .pubVal)
    let gprWiped := c.wipedScratchGprs.all (fun r => r < 32 && getArmAbsGpr st r == .zeroConst)
    if calleeGprOk && calleeVecOk && vecWiped && gprWiped then some [] else none
  | .aluReg op _is64 rd rn rm _sk sa =>
    if op == .eor && rn == rm && sa == 0 then
      some [(nextPc, { st with gpr := setArmAbsGpr st rd .zeroConst })]
    else
      let aPub := (getArmAbsGpr st rn).isPublic
      let bPub := (getArmAbsGpr st rm).isPublic
      let cNeed := if op == .adc || op == .sbc then st.cfPub else true
      let p := aPub && bPub && cNeed
      let setsFlags := op == .adds || op == .subs
      some [(nextPc, { st with
        gpr := setArmAbsGpr st rd (if p then .pubVal else .secretVal)
        cfPub := if setsFlags then p else st.cfPub
        zfPub := if setsFlags then p else st.zfPub })]
  | .aluImm op _is64 rd rn _imm =>
    let cNeed := if op == .adc || op == .sbc then st.cfPub else true
    let p := (getArmAbsGpr st rn).isPublic && cNeed
    let setsFlags := op == .adds || op == .subs
    some [(nextPc, { st with
      gpr := setArmAbsGpr st rd (if p then .pubVal else .secretVal)
      cfPub := if setsFlags then p else st.cfPub
      zfPub := if setsFlags then p else st.zfPub })]
  | .movWide isMovn _is64 rd imm16 _sh =>
    let o : ArmRegOrigin := if !isMovn && imm16 == 0 then .zeroConst else .pubVal
    some [(nextPc, { st with gpr := setArmAbsGpr st rd o })]
  | .ubfm _is64 rd rn _immr _imms =>
    let p := (getArmAbsGpr st rn).isPublic
    some [(nextPc, { st with gpr := setArmAbsGpr st rd (if p then .pubVal else .secretVal) })]
  | .mulOp _isUmulh rd rn rm =>
    let p := (getArmAbsGpr st rn).isPublic && (getArmAbsGpr st rm).isPublic
    some [(nextPc, { st with gpr := setArmAbsGpr st rd (if p then .pubVal else .secretVal) })]
  | .csel cond _isInv rd rn rm =>
    let p := armCondIsPublic cond st && (getArmAbsGpr st rn).isPublic && (getArmAbsGpr st rm).isPublic
    some [(nextPc, { st with gpr := setArmAbsGpr st rd (if p then .pubVal else .secretVal) })]
  | .ldp64 rt1 rt2 rn _off =>
    if !(getArmAbsGpr st rn).isPublic then none
    else
      let s1 := setArmAbsGpr st rt1 .secretVal
      some [(nextPc, { st with gpr := if rt2 == 31 then s1 else s1.set rt2 .secretVal })]
  | .stp64 _rt1 _rt2 rn _off =>
    if !(getArmAbsGpr st rn).isPublic then none else some [(nextPc, st)]
  | .strbPost _rt rn _postOff =>
    if !(getArmAbsGpr st rn).isPublic then none
    else some [(nextPc, { st with gpr := setArmAbsGpr st rn .pubVal })]
  | .ldrQ rt rn _off =>
    if !(getArmAbsGpr st rn).isPublic then none
    else some [(nextPc, { st with vec := st.vec.set rt .secretVal })]
  | .strQ _rt rn _off =>
    if !(getArmAbsGpr st rn).isPublic then none else some [(nextPc, st)]
  | .fmovDFromX vd xn =>
    let o := getArmAbsGpr st xn
    let vo : VecOrigin :=
      if o == .zeroConst then .zeroConst else if o.isPublic then .pubVal else .secretVal
    some [(nextPc, { st with vec := st.vec.set vd vo })]
  | .veor16b vd vn vm =>
    if vn == vm then
      some [(nextPc, { st with vec := st.vec.set vd .zeroConst })]
    else
      let p := (st.vec.get vn).isPublic && (st.vec.get vm).isPublic
      some [(nextPc, { st with vec := st.vec.set vd (if p then .pubVal else .secretVal) })]
  | .vbcax16b vd vn vm va | .veor3_16b vd vn vm va =>
    let p := (st.vec.get vn).isPublic && (st.vec.get vm).isPublic && (st.vec.get va).isPublic
    some [(nextPc, { st with vec := st.vec.set vd (if p then .pubVal else .secretVal) })]
  | .vtrn _ _ _ vd vn vm | .vrax1_2d vd vn vm | .vxar_2d vd vn vm _ | .vpmull _ vd vn vm | .vext16b vd vn vm _ =>
    let p := (st.vec.get vn).isPublic && (st.vec.get vm).isPublic
    some [(nextPc, { st with vec := st.vec.set vd (if p then .pubVal else .secretVal) })]
  | .bCond cond targetPc =>
    if !armCondIsPublic cond st || targetPc < 0 || targetPc.toNat ≥ 4096 then none
    else some [(targetPc.toNat, st), (nextPc, st)]
  | .cbzOrTbz _ | .udivOrSdiv _ | .varShiftReg _ | .regOffsetMem _ =>
    none

def mergeArm64Succs (inv : PcMap Arm64AbsState) : List (Nat × Arm64AbsState) → PcMap Arm64AbsState
  | [] => inv
  | (pc, stNew) :: rest =>
    let merged := match inv.get pc with
      | none => stNew
      | some stOld => Arm64AbsState.join stOld stNew
    mergeArm64Succs (inv.set pc merged) rest

def propagateArm64Pass (c : FuncContract) :
    List (DecodedInstr Arm64Instr) → PcMap Arm64AbsState → Option (PcMap Arm64AbsState)
  | [], inv => some inv
  | d :: ds, inv =>
    match inv.get d.offset with
    | none => propagateArm64Pass c ds inv
    | some st =>
      match transferArm64Instr c d st with
      | none => none
      | some succs => propagateArm64Pass c ds (mergeArm64Succs inv succs)

def inferArm64Invariant (prog : List (DecodedInstr Arm64Instr)) (c : FuncContract) :
    Option (PcMap Arm64AbsState) :=
  let inv0 := PcMap.empty.set 0 (initArm64AbsState c)
  match propagateArm64Pass c prog inv0 with
  | none => none
  | some inv1 => propagateArm64Pass c prog inv1

def verifyArm64Invariant (prog : List (DecodedInstr Arm64Instr)) (c : FuncContract)
    (inv : PcMap Arm64AbsState) : Bool :=
  let progMap := buildProgMap prog
  let entryOk := match inv.get 0 with
    | none => false
    | some st0 => (initArm64AbsState c).le st0
  entryOk &&
  inv.all (fun pc st =>
    match progMap.get pc with
    | none => false
    | some d =>
      match transferArm64Instr c d st with
      | none => false
      | some succs =>
        succs.all (fun (npc, nst) =>
          match inv.get npc with
          | none => false
          | some dstSt => nst.le dstSt))

/-- Certified `AArch64` 3-Way Constant-Time NI + ABI Hygiene verifier. -/
def checkArm64ThreeWayNI (code : List UInt8) (c : FuncContract) : Bool :=
  match decodeArm64Stream code with
  | none => false
  | some prog =>
    match prog with
    | [] => false
    | _ :: _ =>
      match inferArm64Invariant prog c with
      | none => false
      | some inv => verifyArm64Invariant prog c inv

/-- Unified `ELF64` binary symbol 3-Way Constant-Time NI + ABI Hygiene verifier (`EM_X86_64` & `EM_AARCH64`). -/
def checkElfSliceThreeWayNI (slice : ElfFuncSlice) (c : FuncContract) : Bool :=
  if slice.machine == elfMachineX86_64 then
    checkX86ThreeWayNI slice.code c
  else if slice.machine == elfMachineAArch64 then
    checkArm64ThreeWayNI slice.code c
  else
    false

def checkElfFuncThreeWayNI (elfBytes : Bytes) (symName : String) (c : FuncContract) : Bool :=
  match extractElfFuncBytes elfBytes symName with
  | none => false
  | some slice => checkElfSliceThreeWayNI slice c

/-! ### Exact Contracts & Kernel `decide` Discharges for All 23 Compiled `.rlib` Symbols -/

def mkContract (name : String) (pubGprs : List Nat)
    (pubMem : List (Nat × Nat) := []) (wipedGprs : List Nat := [])
    (usesRbp : Bool := false) (outPtr : Nat := 0) (outBytes : Nat := 0)
    (doitEnabled : Bool := true) : FuncContract :=
  ⟨name, pubGprs, pubMem, wipedGprs, usesRbp, outPtr, outBytes, doitEnabled⟩

def x86SymbolContracts : List FuncContract := [
  mkContract "qsag_asm_keccak_f1600_avx2_4x"        [4, 7, 6]       []           []        true 7 0x320,
  mkContract "qsag_asm_keccak_chi_mpc_avx2"         [4, 7, 6, 2, 1] []           [],
  mkContract "qsag_asm_gf256_shamir_mul_gfni"       [4, 7, 6, 2, 1] []           [],
  mkContract "qsag_asm_gf256_shamir_mac_gfni"       [4, 7, 6, 1]    []           [],
  mkContract "qsag_asm_gf256_shamir_mul_avx2"       [4, 7, 6, 2, 1, 8] [(8, 0x80)] [],
  mkContract "qsag_asm_gf256_shamir_mac_avx2"       [4, 7, 6, 1, 8] [(8, 0xA0)]  [],
  mkContract "qsag_asm_tower128_bdoz_mac_vpclmul"   [4, 7, 6, 2, 1] []           [],
  mkContract "qsag_asm_tower128_bdoz_mac_pclmul"    [4, 7, 6, 2, 1] []           [],
  mkContract "qsag_asm_goldilocks_mul_ct_x86_64"    [4]             []           [],
  mkContract "qsag_asm_goldilocks_add_ct_x86_64"    [4]             []           [],
  mkContract "qsag_asm_goldilocks_sub_ct_x86_64"    [4]             []           [],
  mkContract "qsag_asm_goldilocks_pow7_ct_x86_64"   [4]             []           [11],
  mkContract "qsag_asm_goldilocks_dot2_adx_x86_64"  [4]             []           [],
  mkContract "qsag_asm_ct_eq_32_x86_64"             [4, 7, 6]       []           [1, 2, 8],
  mkContract "qsag_asm_ct_eq_bytes_x86_64"          [4, 7, 6, 2]    []           [8, 9],
  mkContract "qsag_asm_ct_memzero_x86_64"           [4, 7, 6]       []           []
]

def aarch64SymbolContracts : List FuncContract := [
  mkContract "qsag_asm_enable_dit_aarch64"          [],
  mkContract "qsag_asm_keccak_sha3_neon"            [0, 1, 2],
  mkContract "qsag_asm_keccak_theta_rho_sha3_neon"  [0, 1],
  mkContract "qsag_asm_tower128_bdoz_mac_pmull"     [0, 1, 2, 3],
  mkContract "qsag_asm_goldilocks_mul_ct_aarch64"   [],
  mkContract "qsag_asm_ct_eq_32_aarch64"            [0, 1]          []           [2, 3, 4, 5, 6, 7],
  mkContract "qsag_asm_ct_memzero_aarch64"          [0, 1]
]

def verifySliceContractList : List ElfFuncSlice → List FuncContract → Bool
  | [], [] => true
  | s :: ss, c :: cs =>
    (s.name == c.symName) && checkElfSliceThreeWayNI s c && verifySliceContractList ss cs
  | _, _ => false

def verifyAllRlibContracts (rlib : Bytes) (contracts : List FuncContract) : Bool :=
  verifySliceContractList (extractAllRlibFuncs rlib) contracts

/-! ### Mutation / Negative Teeth (`#tooth` Equivalents on Real & Mutated Machine-Code Streams) -/

def patchBytesAt (bs : List UInt8) (off : Nat) (patch : List UInt8) : List UInt8 :=
  takeTR off bs ++ patch ++ bs.drop (off + patch.length)

def findSliceByNameBytes (slices : List ElfFuncSlice) (target : List UInt8) : Option ElfFuncSlice :=
  slices.find? (fun s => s.nameBytes == target)

/-- **Negative Tooth 1 (`mutant_secret_branch_rejected`):**
    A conditional jump (`74 01` = `je +1`) after `sub rax, rsi` (`48 89 f8; 48 29 f0`) on secret
    Goldilocks field inputs `(rdi, rsi)` is immediately rejected (`false`) by `checkX86ThreeWayNI`. -/
theorem mutant_secret_branch_rejected :
    checkX86ThreeWayNI
      [0x48, 0x89, 0xF8, 0x48, 0x29, 0xF0, 0x74, 0x01, 0x90, 0xC3]
      (mkContract "mutant_secret_branch" [4]) = false := by
  decide +kernel

/-- REX.B changes opcode 90 into an exchange, never a no-op. -/
theorem rex_b_exchange_not_nop : decodeX86InstrAt 0 [0x41, 0x90] = none := by
  decide +kernel

/-- Unsupported partial writes cannot be treated as full-register zeroization. -/
theorem partial_write_xor_rejected :
    decodeX86InstrAt 0 [0x66, 0x31, 0xFF] = none := by decide +kernel

/-- Signed/overflow conditions require flags absent from the current model. -/
theorem x86_overflow_branch_rejected :
    decodeX86InstrAt 0 [0x70, 0x00] = none := by decide +kernel

theorem arm_signed_branch_rejected :
    decodeArm64Word 0 0x5400000B = none := by decide +kernel

/-- Unsigned/equality conditions remain supported. -/
theorem arm_equal_branch_supported :
    decodeArm64Word 0 0x54000000 = some (.bCond 0 0) := by decide +kernel

/-- SP-using instructions are rejected until SP has a distinct state component. -/
theorem arm_stack_pointer_add_rejected :
    decodeArm64Word 0 0x910003E0 = none := by decide +kernel

theorem arm_stack_pointer_load_rejected :
    decodeArm64Word 0 0x3DC003E0 = none := by decide +kernel

/-- Register 31 is still accepted where the architecture means XZR. -/
theorem arm_zero_register_supported :
    decodeArm64Word 0 0xAA1F03E0 = some (.aluReg .orr true 0 31 31 0 0) := by
  decide +kernel

/-- Rotating a public register cannot make the incoming secret zero flag public. -/
theorem mutant_rotate_secret_zero_flag_rejected :
    checkX86ThreeWayNI [0x48, 0xC1, 0xC7, 0x01, 0x74, 0x01, 0x90, 0xC3]
      (mkContract "rotate_secret_flag" [4, 7]) = false := by
  decide +kernel

/-- **Negative Tooth 2 (`mutant_secret_lut_rejected`):**
    A secret-indexed memory table lookup `movzx eax, byte ptr [rdi + rsi*1]` (`0f b6 04 37; c3`)
    with public table base `rdi` and secret index `rsi` is immediately rejected (`false`). -/
theorem mutant_secret_lut_rejected :
    checkX86ThreeWayNI
      [0x0F, 0xB6, 0x04, 0x37, 0xC3]
      (mkContract "mutant_secret_lut" [4, 7]) = false := by
  decide +kernel

/-- **Negative Tooth 3 (`mutant_variable_shift_rejected`):**
    Both `x86_64` variable shift `shl rax, cl` (`48 d3 e0; c3`) and `AArch64` variable shift
    `lslv x0, x0, x1` (`0x9AC12000; ret`) violate `DOIT-NI` and are immediately rejected (`false`). -/
theorem mutant_variable_shift_rejected :
    checkX86ThreeWayNI [0x48, 0xD3, 0xE0, 0xC3] (mkContract "mutant_shl_cl" [4]) = false ∧
    checkArm64ThreeWayNI
      [0x00, 0x20, 0xC1, 0x9A, 0xC0, 0x03, 0x5F, 0xD6]
      (mkContract "mutant_lslv" []) = false := by
  decide +kernel

/-- **Negative Tooth 4 (`mutant_udiv_rejected`):**
    Both `x86_64` hardware division `div rsi` (`48 f7 f6; c3`) and `AArch64` `udiv x0, x0, x1`
    (`0x9AC10800; ret`) violate `DOIT-NI` and are immediately rejected (`false`). -/
theorem mutant_udiv_rejected :
    checkX86ThreeWayNI [0x48, 0xF7, 0xF6, 0xC3] (mkContract "mutant_div" [4]) = false ∧
    checkArm64ThreeWayNI
      [0x00, 0x08, 0xC1, 0x9A, 0xC0, 0x03, 0x5F, 0xD6]
      (mkContract "mutant_udiv" []) = false := by
  decide +kernel

/-! ### §5b. Deductive Soundness Proofs (`checkElfFuncThreeWayNI_sound`) & Inhabitedness Witnesses -/

private theorem fin16_elim {P : Nat → Prop} {i : Nat} (hi : i < 16)
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3)
    (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7)
    (h8 : P 8) (h9 : P 9) (h10 : P 10) (h11 : P 11)
    (h12 : P 12) (h13 : P 13) (h14 : P 14) (h15 : P 15) : P i := by
  match i with
  | 0 => exact h0 | 1 => exact h1 | 2 => exact h2 | 3 => exact h3
  | 4 => exact h4 | 5 => exact h5 | 6 => exact h6 | 7 => exact h7
  | 8 => exact h8 | 9 => exact h9 | 10 => exact h10 | 11 => exact h11
  | 12 => exact h12 | 13 => exact h13 | 14 => exact h14 | 15 => exact h15
  | _ + 16 => exact False.elim (by omega)

theorem Bank16.get_const {α : Type} (v : α) (i : Nat) :
    (Bank16.const v).get i = v := by
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 => rfl
  | _ + 15 => rfl

theorem Bank16.get_ofFn {α : Type} (f : Nat → α) {i : Nat} (hi : i < 16) :
    (Bank16.ofFn f).get i = f i :=
  fin16_elim (P := fun i => (Bank16.ofFn f).get i = f i)
    hi rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem Bank16.get_set_eq {α : Type} (b : Bank16 α) (i : Nat) (v : α) :
    (b.set i v).get i = v := by
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 => rfl
  | _ + 15 => rfl

theorem Bank16.get_set_ne {α : Type} (b : Bank16 α) {i j : Nat} (v : α)
    (hi : i < 16) (hj : j < 16) (hne : i ≠ j) :
    (b.set i v).get j = b.get j := by
  revert hne
  refine fin16_elim (P := fun i => i ≠ j → (b.set i v).get j = b.get j) hi
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    (refine fin16_elim (P := fun j => _ ≠ j → (b.set _ v).get j = b.get j) hj
       ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (intro hne; first | exact absurd rfl hne | rfl))

theorem Bank16.allIdx_get {α : Type} {p : Nat → α → Bool} {b : Bank16 α}
    (h : b.allIdx p = true) {i : Nat} (hi : i < 16) :
    p i (b.get i) = true := by
  unfold Bank16.allIdx at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩,
    h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩
  exact fin16_elim (P := fun i => p i (b.get i) = true)
    hi h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15

theorem Bank32.get_const {α : Type} (v : α) (i : Nat) :
    (Bank32.const v).get i = v := by
  unfold Bank32.const Bank32.get
  split <;> exact Bank16.get_const v _

theorem Bank32.get_ofFn {α : Type} (f : Nat → α) {i : Nat} (hi : i < 32) :
    (Bank32.ofFn f).get i = f i := by
  unfold Bank32.ofFn Bank32.get
  split
  · rename_i hlt
    exact Bank16.get_ofFn f hlt
  · rename_i hge
    rw [Bank16.get_ofFn (fun k => f (k + 16)) (by omega)]
    exact congrArg f (by omega)

theorem Bank32.get_set_eq {α : Type} (b : Bank32 α) (i : Nat) (v : α) :
    (b.set i v).get i = v := by
  unfold Bank32.set Bank32.get
  split <;> simp [*, Bank16.get_set_eq]

theorem Bank32.get_set_ne {α : Type} (b : Bank32 α) {i j : Nat} (v : α)
    (hi : i < 32) (hj : j < 32) (hne : i ≠ j) :
    (b.set i v).get j = b.get j := by
  unfold Bank32.set Bank32.get
  by_cases hi16 : i < 16 <;> by_cases hj16 : j < 16 <;> simp only [hi16, hj16, ↓reduceIte]
  · exact Bank16.get_set_ne b.lo v hi16 hj16 hne
  · exact Bank16.get_set_ne b.hi v (by omega) (by omega) (by omega)

theorem Bank32.allIdx_get {α : Type} {p : Nat → α → Bool} {b : Bank32 α}
    (h : b.allIdx p = true) {i : Nat} (hi : i < 32) :
    p i (b.get i) = true := by
  unfold Bank32.allIdx at h
  rw [Bool.and_eq_true] at h
  unfold Bank32.get
  split
  · rename_i hlt
    exact Bank16.allIdx_get h.1 hlt
  · rename_i hge
    have hHi := Bank16.allIdx_get h.2 (i := i - 16) (by omega)
    have hEq : i - 16 + 16 = i := by omega
    simpa only [hEq] using hHi

theorem PcMap.empty_get {α : Type} (pc : Nat) :
    (PcMap.empty : PcMap α).get pc = none := by
  unfold PcMap.empty PcMap.get
  split
  · rfl
  · rw [Bank16.get_const]

theorem PcMap.get_some_lt {α : Type} {m : PcMap α} {pc : Nat} {v : α}
    (h : m.get pc = some v) : pc < 4096 := by
  unfold PcMap.get at h
  split at h
  · cases h
  · omega

theorem PcMap.get_set_eq {α : Type} (m : PcMap α) {pc : Nat} (v : α) (hpc : pc < 4096) :
    (m.set pc v).get pc = some v := by
  have hge : ¬(pc ≥ 4096) := by intro h; omega
  unfold PcMap.set PcMap.get
  simp only [hge, ↓reduceIte, Bank16.get_set_eq]

theorem PcMap.get_set_ne {α : Type} (m : PcMap α) {pc q : Nat} (v : α)
    (hq : q < 4096) (hne : pc ≠ q) :
    (m.set pc v).get q = m.get q := by
  have hqge : ¬(q ≥ 4096) := by intro h; omega
  by_cases hpc : pc ≥ 4096
  · unfold PcMap.set; simp [hpc]
  · unfold PcMap.set PcMap.get
    simp only [hpc, hqge, ↓reduceIte]
    have hi2p : pc / 256 < 16 := by omega
    have hi2q : q / 256 < 16 := by omega
    have hi1p : (pc / 16) % 16 < 16 := by omega
    have hi1q : (q / 16) % 16 < 16 := by omega
    have hi0p : pc % 16 < 16 := by omega
    have hi0q : q % 16 < 16 := by omega
    by_cases h2 : pc / 256 = q / 256
    · rw [← h2, Bank16.get_set_eq]
      dsimp only
      by_cases h1 : (pc / 16) % 16 = (q / 16) % 16
      · have h0ne : pc % 16 ≠ q % 16 := by omega
        rw [← h1, Bank16.get_set_eq]
        dsimp only
        rw [Bank16.get_set_ne _ _ hi0p hi0q h0ne]
        cases hm2 : m.root.get (pc / 256) with
        | none => simp [Bank16.get_const]
        | some b1 =>
          dsimp only
          cases hm1 : b1.get ((pc / 16) % 16) with
          | none => simp [Bank16.get_const]
          | some b0 => rfl
      · rw [Bank16.get_set_ne _ _ hi1p hi1q h1]
        cases hm2 : m.root.get (pc / 256) with
        | none => simp [Bank16.get_const]
        | some b1 => rfl
    · rw [Bank16.get_set_ne _ _ hi2p hi2q h2]

theorem PcMap.all_get {α : Type} {pred : Nat → α → Bool} {m : PcMap α}
    (hAll : m.all pred = true) {pc : Nat} {v : α} (hGet : m.get pc = some v) :
    pred pc v = true := by
  have hlt : pc < 4096 := PcMap.get_some_lt hGet
  have hge : ¬(pc ≥ 4096) := by intro h; omega
  unfold PcMap.get at hGet
  simp only [hge, ↓reduceIte] at hGet
  unfold PcMap.all at hAll
  have h2 := Bank16.allIdx_get hAll (i := pc / 256) (by omega)
  cases hm2 : Bank16.get m.root (pc / 256) with
  | none => simp [hm2] at hGet
  | some p1 =>
    simp only [hm2] at hGet h2
    have h1 := Bank16.allIdx_get h2 (i := (pc / 16) % 16) (by omega)
    cases hm1 : Bank16.get p1 ((pc / 16) % 16) with
    | none => simp [hm1] at hGet
    | some p0 =>
      simp only [hm1] at hGet h1
      have h0 := Bank16.allIdx_get h1 (i := pc % 16) (by omega)
      simp only [hGet] at h0
      have hIdx : (pc / 256) * 256 + ((pc / 16) % 16) * 16 + (pc % 16) = pc := by omega
      simpa only [hIdx] using h0

theorem buildProgMap_get_eq {Instr : Type} (prog : List (DecodedInstr Instr))
    {pc : Nat} (hpc : pc < 4096) :
    (buildProgMap prog).get pc = findInstrAtPc pc prog := by
  induction prog with
  | nil => exact PcMap.empty_get pc
  | cons d ds ih =>
    unfold buildProgMap findInstrAtPc
    by_cases heq : d.offset = pc
    · subst heq
      simp [PcMap.get_set_eq _ _ hpc]
    · have hbeq : (d.offset == pc) = false := beq_false_of_ne heq
      rw [PcMap.get_set_ne _ _ hpc heq, hbeq]
      simp [ih]

/-! #### Memory Read-Over-Write & Disjointness Lemmas -/

theorem writeMem8_eq (mem : UInt64 → UInt8) (addr : UInt64) (b : UInt8) :
    writeMem8 mem addr b addr = b := by
  change (if addr == addr then b else mem addr) = b
  have h : (addr == addr) = true := by
    change (addr.toBitVec == addr.toBitVec) = true
    exact beq_self_eq_true _
  rw [h]
  rfl

theorem writeMem8_ne (mem : UInt64 → UInt8) {addr q : UInt64} (b : UInt8) (hne : q ≠ addr) :
    writeMem8 mem addr b q = mem q := by
  unfold writeMem8
  have hbf : (q == addr) = false := beq_false_of_ne hne
  rw [hbf]
  rfl

theorem writeMem64_ne (mem : UInt64 → UInt8) {addr q : UInt64} (v : UInt64)
    (hDisj : ∀ j : Nat, j < 8 → q ≠ addr + UInt64.ofNat j) :
    writeMem64 mem addr v q = mem q := by
  unfold writeMem64
  have h0 : q ≠ addr := by simpa using hDisj 0 (by omega)
  have h1 : q ≠ addr + 1 := hDisj 1 (by omega)
  have h2 : q ≠ addr + 2 := hDisj 2 (by omega)
  have h3 : q ≠ addr + 3 := hDisj 3 (by omega)
  have h4 : q ≠ addr + 4 := hDisj 4 (by omega)
  have h5 : q ≠ addr + 5 := hDisj 5 (by omega)
  have h6 : q ≠ addr + 6 := hDisj 6 (by omega)
  have h7 : q ≠ addr + 7 := hDisj 7 (by omega)
  simp only [writeMem8_ne _ _ h7, writeMem8_ne _ _ h6, writeMem8_ne _ _ h5, writeMem8_ne _ _ h4,
    writeMem8_ne _ _ h3, writeMem8_ne _ _ h2, writeMem8_ne _ _ h1, writeMem8_ne _ _ h0]

private theorem uint64_eq_of_toNat_eq {a b : UInt64} (h : a.toNat = b.toNat) : a = b :=
  UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)

theorem writeMem128_ne (mem : UInt64 → UInt8) {addr q : UInt64} (v : Vec128)
    (hDisj : ∀ j : Nat, j < 16 → q ≠ addr + UInt64.ofNat j) :
    writeMem128 mem addr v q = mem q := by
  unfold writeMem128
  rw [writeMem64_ne _ _ (fun j hj => by
        have := hDisj (8 + j) (by omega)
        have hAdd : addr + 8 + UInt64.ofNat j = addr + UInt64.ofNat (8 + j) := by
          apply uint64_eq_of_toNat_eq
          have h8 : (8 : UInt64).toNat = 8 := rfl
          simp only [UInt64.toNat_add, UInt64.toNat_ofNat', h8, Nat.add_mod_mod, Nat.mod_add_mod]
          congr 1; omega
        rwa [hAdd]),
      writeMem64_ne _ _ (fun j hj => hDisj j (by omega))]

theorem writeMem256_ne (mem : UInt64 → UInt8) {addr q : UInt64} (v : Vec256)
    (hDisj : ∀ j : Nat, j < 32 → q ≠ addr + UInt64.ofNat j) :
    writeMem256 mem addr v q = mem q := by
  unfold writeMem256
  have hOff (base : Nat) (hbase : base + 8 ≤ 32) :
      ∀ j : Nat, j < 8 → q ≠ addr + UInt64.ofNat base + UInt64.ofNat j := by
    intro j hj
    have hEq : addr + UInt64.ofNat base + UInt64.ofNat j = addr + UInt64.ofNat (base + j) := by
      apply uint64_eq_of_toNat_eq
      simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.add_mod_mod, Nat.mod_add_mod]
      congr 1; omega
    rw [hEq]
    exact hDisj (base + j) (by omega)
  have h8 : ∀ j : Nat, j < 8 → q ≠ addr + 8 + UInt64.ofNat j := hOff 8 (by omega)
  have h16 : ∀ j : Nat, j < 8 → q ≠ addr + 16 + UInt64.ofNat j := hOff 16 (by omega)
  have h24 : ∀ j : Nat, j < 8 → q ≠ addr + 24 + UInt64.ofNat j := hOff 24 (by omega)
  rw [writeMem64_ne _ _ h24,
      writeMem64_ne _ _ h16,
      writeMem64_ne _ _ h8,
      writeMem64_ne _ _ (fun j hj => hDisj j (by omega))]

theorem readMem64_congr {m1 m2 : UInt64 → UInt8} {addr : UInt64}
    (h : ∀ j : Nat, j < 8 → m1 (addr + UInt64.ofNat j) = m2 (addr + UInt64.ofNat j)) :
    readMem64 m1 addr = readMem64 m2 addr := by
  have h0 : m1 addr = m2 addr := by simpa using h 0 (by omega)
  have h1 : m1 (addr + 1) = m2 (addr + 1) := h 1 (by omega)
  have h2 : m1 (addr + 2) = m2 (addr + 2) := h 2 (by omega)
  have h3 : m1 (addr + 3) = m2 (addr + 3) := h 3 (by omega)
  have h4 : m1 (addr + 4) = m2 (addr + 4) := h 4 (by omega)
  have h5 : m1 (addr + 5) = m2 (addr + 5) := h 5 (by omega)
  have h6 : m1 (addr + 6) = m2 (addr + 6) := h 6 (by omega)
  have h7 : m1 (addr + 7) = m2 (addr + 7) := h 7 (by omega)
  unfold readMem64
  rw [h0, h1, h2, h3, h4, h5, h6, h7]

private theorem addr_off_ne (addr a b : UInt64) (hne : a ≠ b) :
    addr + a ≠ addr + b := by
  intro hEq
  have hSub : (addr + a) - addr = (addr + b) - addr := congrArg (· - addr) hEq
  have hCancel (x : UInt64) : (addr + x) - addr = x := by
    apply uint64_eq_of_toNat_eq
    have hx := x.toNat_lt
    have hd := addr.toNat_lt
    have h64 : (2 : Nat) ^ 64 = 0x10000000000000000 := rfl
    simp only [UInt64.toNat_sub, UInt64.toNat_add, h64]
    omega
  rw [hCancel a, hCancel b] at hSub
  exact hne hSub

private theorem addr_ne_add_pos (addr b : UInt64) (hb : (0 : UInt64) ≠ b) :
    addr ≠ addr + b := by
  have h0 : addr + 0 = addr := by
    apply uint64_eq_of_toNat_eq
    have hd := addr.toNat_lt
    have hZ : (0 : UInt64).toNat = 0 := rfl
    have h64 : (2 : Nat) ^ 64 = 0x10000000000000000 := rfl
    simp only [UInt64.toNat_add, hZ, h64]
    omega
  intro hEq
  exact addr_off_ne addr 0 b hb (h0.trans hEq)

private theorem toUInt8_toUInt64_eq_and (w : UInt64) :
    w.toUInt8.toUInt64 = (w &&& (0xFF : UInt64)) := by
  apply uint64_eq_of_toNat_eq
  have h1 : w.toUInt8.toUInt64.toNat = w.toNat % 256 := by
    change (UInt8.ofNat w.toNat).toNat = w.toNat % 256
    exact UInt8.toNat_ofNat'
  have h2 : (w &&& (0xFF : UInt64)).toNat = w.toNat % 256 := by
    rw [UInt64.toNat_and]
    change w.toNat &&& (2 ^ 8 - 1) = w.toNat % 256
    exact Constructive.and_mask w.toNat 8
  exact h1.trans h2.symm

private def checkMaskFFBits : Bool :=
  (List.range 64).all (fun i => (0xFF : UInt64).toBitVec.getLsbD i == decide (i < 8))

private theorem checkMaskFFBits_true : checkMaskFFBits = true := by decide

private theorem mask_ff_getLsbD_lt (k : Nat) (hk : k < 64) :
    (0xFF : UInt64).toBitVec.getLsbD k = decide (k < 8) := by
  have h := List.all_eq_true.mp checkMaskFFBits_true k (List.mem_range.mpr hk)
  exact beq_iff_eq.mp h

private theorem uint64_shiftRight_getLsbD (v sh : UInt64) (k : Nat) :
    (v >>> sh).toBitVec.getLsbD k = v.toBitVec.getLsbD (sh.toNat % 64 + k) := by
  simp only [BitVec.getLsbD, show (v >>> sh).toBitVec.toNat = (v >>> sh).toNat from rfl,
    show v.toBitVec.toNat = v.toNat from rfl, UInt64.toNat_shiftRight,
    Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add]

private theorem byte_slot_getLsbD (v sh : UInt64) (i : Nat) (hi : i < 64) (hsh : sh.toNat ≤ 56) :
    (((v >>> sh).toUInt8.toUInt64) <<< sh).toBitVec.getLsbD i =
      if sh.toNat ≤ i ∧ i < sh.toNat + 8 then v.toBitVec.getLsbD i else false := by
  have hMod : sh.toNat % 64 = sh.toNat := Nat.mod_eq_of_lt (by omega)
  have h64Nat : (64 : BitVec 64).toNat = 64 := rfl
  have hShNat : (sh.toBitVec % 64).toNat = sh.toNat := by
    rw [BitVec.toNat_umod, h64Nat]
    exact hMod
  rw [toUInt8_toUInt64_eq_and, UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq', hShNat,
      BitVec.getLsbD_shiftLeft]
  simp only [hi, decide_true, Bool.true_and, UInt64.toBitVec_and, BitVec.getLsbD_and,
    uint64_shiftRight_getLsbD, hMod]
  have hSub64 : i - sh.toNat < 64 := by omega
  rw [mask_ff_getLsbD_lt (i - sh.toNat) hSub64]
  if hLow : i < sh.toNat then
    have hNot : ¬(sh.toNat ≤ i ∧ i < sh.toNat + 8) := by intro h; omega
    simp only [decide_eq_true hLow, hNot, ↓reduceIte]
    rfl
  else if hHigh : i < sh.toNat + 8 then
    have hSub : i - sh.toNat < 8 := by omega
    have hYes : sh.toNat ≤ i ∧ i < sh.toNat + 8 := ⟨by omega, hHigh⟩
    have hAdd : sh.toNat + (i - sh.toNat) = i := by omega
    simp only [decide_eq_false hLow, decide_eq_true hSub, hYes, and_self, hAdd, ↓reduceIte]
    cases v.toBitVec.getLsbD i <;> rfl
  else
    have hSub : ¬(i - sh.toNat < 8) := by intro h; omega
    have hNot : ¬(sh.toNat ≤ i ∧ i < sh.toNat + 8) := by intro h; omega
    simp only [decide_eq_false hLow, decide_eq_false hSub, hNot, ↓reduceIte]
    cases v.toBitVec.getLsbD (sh.toNat + (i - sh.toNat)) <;> rfl

private theorem byte_reassemble_u64 (v : UInt64) :
    v.toUInt8.toUInt64 |||
    ((v >>> 8).toUInt8.toUInt64 <<< 8) |||
    ((v >>> 16).toUInt8.toUInt64 <<< 16) |||
    ((v >>> 24).toUInt8.toUInt64 <<< 24) |||
    ((v >>> 32).toUInt8.toUInt64 <<< 32) |||
    ((v >>> 40).toUInt8.toUInt64 <<< 40) |||
    ((v >>> 48).toUInt8.toUInt64 <<< 48) |||
    ((v >>> 56).toUInt8.toUInt64 <<< 56) = v := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt64.toBitVec_or, BitVec.getLsbD_or]
  rw [byte_slot_getLsbD v 8 i hi (by decide),
      byte_slot_getLsbD v 16 i hi (by decide),
      byte_slot_getLsbD v 24 i hi (by decide),
      byte_slot_getLsbD v 32 i hi (by decide),
      byte_slot_getLsbD v 40 i hi (by decide),
      byte_slot_getLsbD v 48 i hi (by decide),
      byte_slot_getLsbD v 56 i hi (by decide),
      toUInt8_toUInt64_eq_and v]
  simp only [UInt64.toBitVec_and, BitVec.getLsbD_and, mask_ff_getLsbD_lt i hi,
    show (8 : UInt64).toNat = 8 from rfl, show (16 : UInt64).toNat = 16 from rfl,
    show (24 : UInt64).toNat = 24 from rfl, show (32 : UInt64).toNat = 32 from rfl,
    show (40 : UInt64).toNat = 40 from rfl, show (48 : UInt64).toNat = 48 from rfl,
    show (56 : UInt64).toNat = 56 from rfl]
  if c0 : i < 8 then
    have n1 : ¬(8 ≤ i ∧ i < 16) := by intro h; omega
    have n2 : ¬(16 ≤ i ∧ i < 24) := by intro h; omega
    have n3 : ¬(24 ≤ i ∧ i < 32) := by intro h; omega
    have n4 : ¬(32 ≤ i ∧ i < 40) := by intro h; omega
    have n5 : ¬(40 ≤ i ∧ i < 48) := by intro h; omega
    have n6 : ¬(48 ≤ i ∧ i < 56) := by intro h; omega
    have n7 : ¬(56 ≤ i ∧ i < 64) := by intro h; omega
    simp only [decide_eq_true c0, n1, n2, n3, n4, n5, n6, n7, ↓reduceIte]
    cases v.toBitVec.getLsbD i <;> rfl
  else if c1 : i < 16 then
    have y1 : 8 ≤ i ∧ i < 16 := by constructor <;> omega
    have n2 : ¬(16 ≤ i ∧ i < 24) := by intro h; omega
    have n3 : ¬(24 ≤ i ∧ i < 32) := by intro h; omega
    have n4 : ¬(32 ≤ i ∧ i < 40) := by intro h; omega
    have n5 : ¬(40 ≤ i ∧ i < 48) := by intro h; omega
    have n6 : ¬(48 ≤ i ∧ i < 56) := by intro h; omega
    have n7 : ¬(56 ≤ i ∧ i < 64) := by intro h; omega
    simp only [decide_eq_false c0, y1, n2, n3, n4, n5, n6, n7, and_self, ↓reduceIte]
    cases v.toBitVec.getLsbD i <;> rfl
  else if c2 : i < 24 then
    have n1 : ¬(8 ≤ i ∧ i < 16) := by intro h; omega
    have y2 : 16 ≤ i ∧ i < 24 := by constructor <;> omega
    have n3 : ¬(24 ≤ i ∧ i < 32) := by intro h; omega
    have n4 : ¬(32 ≤ i ∧ i < 40) := by intro h; omega
    have n5 : ¬(40 ≤ i ∧ i < 48) := by intro h; omega
    have n6 : ¬(48 ≤ i ∧ i < 56) := by intro h; omega
    have n7 : ¬(56 ≤ i ∧ i < 64) := by intro h; omega
    simp only [decide_eq_false c0, n1, y2, n3, n4, n5, n6, n7, and_self, ↓reduceIte]
    cases v.toBitVec.getLsbD i <;> rfl
  else if c3 : i < 32 then
    have n1 : ¬(8 ≤ i ∧ i < 16) := by intro h; omega
    have n2 : ¬(16 ≤ i ∧ i < 24) := by intro h; omega
    have y3 : 24 ≤ i ∧ i < 32 := by constructor <;> omega
    have n4 : ¬(32 ≤ i ∧ i < 40) := by intro h; omega
    have n5 : ¬(40 ≤ i ∧ i < 48) := by intro h; omega
    have n6 : ¬(48 ≤ i ∧ i < 56) := by intro h; omega
    have n7 : ¬(56 ≤ i ∧ i < 64) := by intro h; omega
    simp only [decide_eq_false c0, n1, n2, y3, n4, n5, n6, n7, and_self, ↓reduceIte]
    cases v.toBitVec.getLsbD i <;> rfl
  else if c4 : i < 40 then
    have n1 : ¬(8 ≤ i ∧ i < 16) := by intro h; omega
    have n2 : ¬(16 ≤ i ∧ i < 24) := by intro h; omega
    have n3 : ¬(24 ≤ i ∧ i < 32) := by intro h; omega
    have y4 : 32 ≤ i ∧ i < 40 := by constructor <;> omega
    have n5 : ¬(40 ≤ i ∧ i < 48) := by intro h; omega
    have n6 : ¬(48 ≤ i ∧ i < 56) := by intro h; omega
    have n7 : ¬(56 ≤ i ∧ i < 64) := by intro h; omega
    simp only [decide_eq_false c0, n1, n2, n3, y4, n5, n6, n7, and_self, ↓reduceIte]
    cases v.toBitVec.getLsbD i <;> rfl
  else if c5 : i < 48 then
    have n1 : ¬(8 ≤ i ∧ i < 16) := by intro h; omega
    have n2 : ¬(16 ≤ i ∧ i < 24) := by intro h; omega
    have n3 : ¬(24 ≤ i ∧ i < 32) := by intro h; omega
    have n4 : ¬(32 ≤ i ∧ i < 40) := by intro h; omega
    have y5 : 40 ≤ i ∧ i < 48 := by constructor <;> omega
    have n6 : ¬(48 ≤ i ∧ i < 56) := by intro h; omega
    have n7 : ¬(56 ≤ i ∧ i < 64) := by intro h; omega
    simp only [decide_eq_false c0, n1, n2, n3, n4, y5, n6, n7, and_self, ↓reduceIte]
    cases v.toBitVec.getLsbD i <;> rfl
  else if c6 : i < 56 then
    have n1 : ¬(8 ≤ i ∧ i < 16) := by intro h; omega
    have n2 : ¬(16 ≤ i ∧ i < 24) := by intro h; omega
    have n3 : ¬(24 ≤ i ∧ i < 32) := by intro h; omega
    have n4 : ¬(32 ≤ i ∧ i < 40) := by intro h; omega
    have n5 : ¬(40 ≤ i ∧ i < 48) := by intro h; omega
    have y6 : 48 ≤ i ∧ i < 56 := by constructor <;> omega
    have n7 : ¬(56 ≤ i ∧ i < 64) := by intro h; omega
    simp only [decide_eq_false c0, n1, n2, n3, n4, n5, y6, n7, and_self, ↓reduceIte]
    cases v.toBitVec.getLsbD i <;> rfl
  else
    have n1 : ¬(8 ≤ i ∧ i < 16) := by intro h; omega
    have n2 : ¬(16 ≤ i ∧ i < 24) := by intro h; omega
    have n3 : ¬(24 ≤ i ∧ i < 32) := by intro h; omega
    have n4 : ¬(32 ≤ i ∧ i < 40) := by intro h; omega
    have n5 : ¬(40 ≤ i ∧ i < 48) := by intro h; omega
    have n6 : ¬(48 ≤ i ∧ i < 56) := by intro h; omega
    have y7 : 56 ≤ i ∧ i < 64 := by constructor <;> omega
    simp only [decide_eq_false c0, n1, n2, n3, n4, n5, n6, y7, and_self, ↓reduceIte]
    cases v.toBitVec.getLsbD i <;> rfl

theorem readMem64_writeMem64_self (mem : UInt64 → UInt8) (addr v : UInt64) :
    readMem64 (writeMem64 mem addr v) addr = v := by
  let m0 := writeMem8 mem addr v.toUInt8
  let m1 := writeMem8 m0 (addr + 1) (v >>> 8).toUInt8
  let m2 := writeMem8 m1 (addr + 2) (v >>> 16).toUInt8
  let m3 := writeMem8 m2 (addr + 3) (v >>> 24).toUInt8
  let m4 := writeMem8 m3 (addr + 4) (v >>> 32).toUInt8
  let m5 := writeMem8 m4 (addr + 5) (v >>> 40).toUInt8
  let m6 := writeMem8 m5 (addr + 6) (v >>> 48).toUInt8
  let m7 := writeMem8 m6 (addr + 7) (v >>> 56).toUInt8
  change readMem64 m7 addr = v
  have b7 : m7 (addr + 7) = (v >>> 56).toUInt8 := writeMem8_eq _ _ _
  have b6 : m7 (addr + 6) = (v >>> 48).toUInt8 := by
    dsimp only [m7, m6]
    rw [writeMem8_ne _ _ (addr_off_ne addr 6 7 (by decide))]; exact writeMem8_eq _ _ _
  have b5 : m7 (addr + 5) = (v >>> 40).toUInt8 := by
    dsimp only [m7, m6, m5]
    rw [writeMem8_ne _ _ (addr_off_ne addr 5 7 (by decide)),
        writeMem8_ne _ _ (addr_off_ne addr 5 6 (by decide))]; exact writeMem8_eq _ _ _
  have b4 : m7 (addr + 4) = (v >>> 32).toUInt8 := by
    dsimp only [m7, m6, m5, m4]
    rw [writeMem8_ne _ _ (addr_off_ne addr 4 7 (by decide)),
        writeMem8_ne _ _ (addr_off_ne addr 4 6 (by decide)),
        writeMem8_ne _ _ (addr_off_ne addr 4 5 (by decide))]; exact writeMem8_eq _ _ _
  have b3 : m7 (addr + 3) = (v >>> 24).toUInt8 := by
    dsimp only [m7, m6, m5, m4, m3]
    rw [writeMem8_ne _ _ (addr_off_ne addr 3 7 (by decide)),
        writeMem8_ne _ _ (addr_off_ne addr 3 6 (by decide)),
        writeMem8_ne _ _ (addr_off_ne addr 3 5 (by decide)),
        writeMem8_ne _ _ (addr_off_ne addr 3 4 (by decide))]; exact writeMem8_eq _ _ _
  have b2 : m7 (addr + 2) = (v >>> 16).toUInt8 := by
    dsimp only [m7, m6, m5, m4, m3, m2]
    rw [writeMem8_ne _ _ (addr_off_ne addr 2 7 (by decide)),
        writeMem8_ne _ _ (addr_off_ne addr 2 6 (by decide)),
        writeMem8_ne _ _ (addr_off_ne addr 2 5 (by decide)),
        writeMem8_ne _ _ (addr_off_ne addr 2 4 (by decide)),
        writeMem8_ne _ _ (addr_off_ne addr 2 3 (by decide))]; exact writeMem8_eq _ _ _
  have b1 : m7 (addr + 1) = (v >>> 8).toUInt8 := by
    dsimp only [m7, m6, m5, m4, m3, m2, m1]
    rw [writeMem8_ne _ _ (addr_off_ne addr 1 7 (by decide)),
        writeMem8_ne _ _ (addr_off_ne addr 1 6 (by decide)),
        writeMem8_ne _ _ (addr_off_ne addr 1 5 (by decide)),
        writeMem8_ne _ _ (addr_off_ne addr 1 4 (by decide)),
        writeMem8_ne _ _ (addr_off_ne addr 1 3 (by decide)),
        writeMem8_ne _ _ (addr_off_ne addr 1 2 (by decide))]; exact writeMem8_eq _ _ _
  have b0 : m7 addr = v.toUInt8 := by
    dsimp only [m7, m6, m5, m4, m3, m2, m1, m0]
    rw [writeMem8_ne _ _ (addr_ne_add_pos addr 7 (by decide)),
        writeMem8_ne _ _ (addr_ne_add_pos addr 6 (by decide)),
        writeMem8_ne _ _ (addr_ne_add_pos addr 5 (by decide)),
        writeMem8_ne _ _ (addr_ne_add_pos addr 4 (by decide)),
        writeMem8_ne _ _ (addr_ne_add_pos addr 3 (by decide)),
        writeMem8_ne _ _ (addr_ne_add_pos addr 2 (by decide)),
        writeMem8_ne _ _ (addr_ne_add_pos addr 1 (by decide))]; exact writeMem8_eq _ _ _
  unfold readMem64
  rw [b0, b1, b2, b3, b4, b5, b6, b7]
  exact byte_reassemble_u64 v

private def checkAlign32MaskBits : Bool :=
  (List.range 64).all (fun i =>
    (0xFFFFFFFFFFFFFFE0 : UInt64).toBitVec.getLsbD i == decide (5 ≤ i))

private theorem checkAlign32MaskBits_true : checkAlign32MaskBits = true := by decide

private theorem align32_eq_shift (x : UInt64) :
    (x &&& (0xFFFFFFFFFFFFFFE0 : UInt64)) = (x >>> 5) <<< 5 := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h5 : (5 : UInt64).toBitVec % 64 = BitVec.ofNat 64 5 := by decide
  have hMaskBit : (0xFFFFFFFFFFFFFFE0 : UInt64).toBitVec.getLsbD i = decide (5 ≤ i) :=
    beq_iff_eq.mp (List.all_eq_true.mp checkAlign32MaskBits_true i (List.mem_range.mpr hi))
  rw [UInt64.toBitVec_and, BitVec.getLsbD_and, hMaskBit,
      UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq', h5, BitVec.toNat_ofNat]
  simp only [show 5 % 64 = 5 from rfl, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and,
    uint64_shiftRight_getLsbD, show (5 : UInt64).toNat % 64 = 5 from rfl]
  if hlt : i < 5 then
    have hge : ¬(5 ≤ i) := by intro h; omega
    rw [decide_eq_true hlt, decide_eq_false hge]
    cases x.toBitVec.getLsbD i <;> rfl
  else
    have hge : 5 ≤ i := by omega
    have hAdd : 5 + (i - 5) = i := by omega
    rw [decide_eq_false hlt, decide_eq_true hge, hAdd]
    cases x.toBitVec.getLsbD i <;> rfl

private theorem align32_toNat (x : UInt64) :
    (x &&& (0xFFFFFFFFFFFFFFE0 : UInt64)).toNat = (x.toNat / 32) * 32 := by
  rw [align32_eq_shift]
  have hlt : (x.toNat / 32) * 32 < 2 ^ 64 := by have := x.toNat_lt; omega
  simp [UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hlt]

private theorem uint64_evalAdd_eq (a b : UInt64) :
    UInt64.ofNat ((a.toNat + b.toNat) % 0x10000000000000000) = a + b := by
  apply uint64_eq_of_toNat_eq
  have h64 : (2 : Nat) ^ 64 = 0x10000000000000000 := rfl
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat', h64, Nat.mod_mod]

private theorem uint64_evalSub_eq (a b : UInt64) :
    UInt64.ofNat ((a.toNat + 0x10000000000000000 - b.toNat) % 0x10000000000000000) = a - b := by
  apply uint64_eq_of_toNat_eq
  have ha := a.toNat_lt; have hb := b.toNat_lt
  have h64 : (2 : Nat) ^ 64 = 0x10000000000000000 := rfl
  simp only [UInt64.toNat_sub, UInt64.toNat_ofNat', h64]; omega

/-! #### `x86_64` & `AArch64` Relational Contracts, Hygiene Postconditions & Inhabitedness Witnesses -/

/-- Well-formed frame non-aliasing precondition when `c.usesRbpFrame = true`:
    `rsp` has `0x400` bytes of downward stack headroom and the caller's output buffer
    `[outPtr .. outPtr + outBytes)` does not overlap the callee's saved-`rbp` slot `[rsp - 8 .. rsp)`. -/
def X86FramePrecond (c : FuncContract) (s₀ : X86State) : Prop :=
  c.usesRbpFrame = false ∨
  (c.outPtrReg < 16 ∧
   0x400 ≤ (s₀.gpr.get 4).toNat ∧
   ∀ j k : Nat, j < c.outBytes → k < 8 →
     s₀.gpr.get c.outPtrReg + UInt64.ofNat j ≠ (s₀.gpr.get 4 - 8) + UInt64.ofNat k)

/-- Initial `x86_64` relational contract $\Gamma(s_1, s_2)$:
    both executions start at `pc = 0` with clean upper `YMM` state, agree on public GPRs (`len`, pointers, `rsp`)
    and static public LUT regions (`pubMemRegions`), while secret memory and secret GPRs are arbitrary. -/
def X86ContractInit (c : FuncContract) (s₁ s₂ : X86State) : Prop :=
  s₁.pc = 0 ∧ s₂.pc = 0 ∧
  s₁.halted = false ∧ s₂.halted = false ∧
  s₁.ymmDirty = false ∧ s₂.ymmDirty = false ∧
  (∀ r ∈ c.pubGprs, r < 16 ∧ s₁.gpr.get r = s₂.gpr.get r) ∧
  (∀ regLen ∈ c.pubMemRegions,
     regLen.1 < 16 ∧
     ∀ off : Nat, off < regLen.2 →
       s₁.mem (s₁.gpr.get regLen.1 + UInt64.ofNat off) =
       s₂.mem (s₂.gpr.get regLen.1 + UInt64.ofNat off)) ∧
  X86FramePrecond c s₁ ∧ X86FramePrecond c s₂

/-- System V AMD64 ABI & Epilogue Zeroization postcondition upon `ret`. -/
def X86ExitHygiene (c : FuncContract) (s₁₀ s₂₀ s₁ s₂ : X86State) : Prop :=
  (s₁.gpr.get 4 = s₁₀.gpr.get 4 ∧ s₂.gpr.get 4 = s₂₀.gpr.get 4) ∧
  (∀ r ∈ [3, 5, 12, 13, 14, 15],
     s₁.gpr.get r = s₁₀.gpr.get r ∧ s₂.gpr.get r = s₂₀.gpr.get r) ∧
  (s₁.ymmDirty = false ∧ s₂.ymmDirty = false) ∧
  (∀ i : Nat, i < 16 →
     (s₁.ymm.get i = Vec256.zero ∧ s₂.ymm.get i = Vec256.zero) ∨
     (∃ r : Nat, r < 16 ∧
       ((s₁.ymm.get i = s₁₀.ymm.get r ∧ s₂.ymm.get i = s₂₀.ymm.get r) ∨
        (s₁.ymm.get i = ⟨(s₁₀.ymm.get r).w0, (s₁₀.ymm.get r).w1, 0, 0⟩ ∧
         s₂.ymm.get i = ⟨(s₂₀.ymm.get r).w0, (s₂₀.ymm.get r).w1, 0, 0⟩)))) ∧
  (∀ r ∈ c.wipedScratchGprs, s₁.gpr.get r = 0 ∧ s₂.gpr.get r = 0)

/-- Initial `AArch64` relational contract $\Gamma(s_1, s_2)$:
    both executions start at `pc = 0`, agree on public GPRs (`x0..x3` pointers / lengths),
    while secret memory, secret GPRs, and caller NEON contents are completely arbitrary. -/
def Arm64ContractInit (c : FuncContract) (s₁ s₂ : Arm64State) : Prop :=
  s₁.pc = 0 ∧ s₂.pc = 0 ∧
  s₁.halted = false ∧ s₂.halted = false ∧
  s₁.dit = true ∧ s₂.dit = true ∧
  (∀ r ∈ c.pubGprs, r < 31 ∧ s₁.gpr.get r = s₂.gpr.get r)

/-- AAPCS64 ABI & NEON Epilogue Zeroization postcondition upon `ret`. -/
def Arm64ExitHygiene (c : FuncContract) (s₁₀ s₂₀ s₁ s₂ : Arm64State) : Prop :=
  (∀ r ∈ [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30],
     s₁.gpr.get r = s₁₀.gpr.get r ∧ s₂.gpr.get r = s₂₀.gpr.get r) ∧
  (∀ v ∈ [8, 9, 10, 11, 12, 13, 14, 15],
     s₁.vec.get v = s₁₀.vec.get v ∧ s₂.vec.get v = s₂₀.vec.get v) ∧
  (∀ v : Nat, v < 32 →
     (s₁.vec.get v = Vec128.zero ∧ s₂.vec.get v = Vec128.zero) ∨
     (∃ r : Nat, r < 32 ∧ s₁.vec.get v = s₁₀.vec.get r ∧ s₂.vec.get v = s₂₀.vec.get r)) ∧
  (∀ r ∈ c.wipedScratchGprs, getArmGpr s₁ r = 0 ∧ getArmGpr s₂ r = 0)

/-- **Anti-Vacuity / Inhabitedness Witness (`lean/uninhabited-premise-risk`) for `X86ContractInit`:**
    Every well-indexed `FuncContract` (including all 16 `x86SymbolContracts`) admits concrete
    pairs of initial states `(s₁, s₂)` with distinct secret memory (`0xAA ≠ 0x55` above `0x200000`)
    satisfying `X86ContractInit c s₁ s₂`. -/
theorem x86_contract_init_inhabited (c : FuncContract)
    (hPubLt : ∀ r ∈ c.pubGprs, r < 16)
    (hMemLt : ∀ regLen ∈ c.pubMemRegions, regLen.1 < 16 ∧ regLen.2 ≤ 0x10000)
    (hOutLt : c.outPtrReg < 16)
    (hOutSz : c.outBytes ≤ 0x10000) :
    ∃ s₁ s₂ : X86State,
      s₁.mem 0x200000 ≠ s₂.mem 0x200000 ∧ X86ContractInit c s₁ s₂ := by
  let gpr0 : Bank16 UInt64 := Bank16.ofFn (fun r => if r == 4 then 0x80000 else 0x10000)
  let s₁ : X86State := {
    pc := 0, gpr := gpr0, ymm := Bank16.const Vec256.zero,
    cf := false, ofFlag := false, zf := false, ymmDirty := false, halted := false,
    mem := fun a => if a.toNat < 0x100000 then 0x11 else 0xAA
  }
  let s₂ : X86State := { s₁ with
    mem := fun a => if a.toNat < 0x100000 then 0x11 else 0x55
  }
  refine ⟨s₁, s₂, by decide, ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩⟩
  · intro r hr; exact ⟨hPubLt r hr, rfl⟩
  · intro regLen hrl
    rcases hMemLt regLen hrl with ⟨hr16, hlen⟩
    refine ⟨hr16, fun off hoff => ?_⟩
    have hBase : (gpr0.get regLen.1).toNat ≤ 0x80000 := by
      rw [Bank16.get_ofFn _ hr16]; split <;> decide
    have hAddrLt : (gpr0.get regLen.1 + UInt64.ofNat off).toNat < 0x100000 := by
      have hSumLt : (gpr0.get regLen.1).toNat + off < 2 ^ 64 := by omega
      simp [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hSumLt]; omega
    dsimp only [s₁, s₂]
    simp only [hAddrLt, ↓reduceIte]
  · by_cases hUse : c.usesRbpFrame = false
    · exact Or.inl hUse
    · right
      have h4 : 0x400 ≤ (s₁.gpr.get 4).toNat := by decide
      refine ⟨hOutLt, h4, fun j k hj hk => ?_⟩
      intro hEq
      have hNat := congrArg UInt64.toNat hEq
      have hOutVal : (s₁.gpr.get c.outPtrReg).toNat = 0x10000 ∨ (s₁.gpr.get c.outPtrReg).toNat = 0x80000 := by
        change (gpr0.get c.outPtrReg).toNat = 0x10000 ∨ (gpr0.get c.outPtrReg).toNat = 0x80000
        rw [Bank16.get_ofFn _ hOutLt]
        split
        · exact Or.inr (by decide)
        · exact Or.inl (by decide)
      have hSpSub : (s₁.gpr.get 4 - 8).toNat = 0x7FFF8 := by decide
      have hRhs : ((s₁.gpr.get 4 - 8) + UInt64.ofNat k).toNat = 0x7FFF8 + k := by
        have hlt : 0x7FFF8 + k < 2 ^ 64 := by omega
        simp [UInt64.toNat_add, hSpSub, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]
      rcases hOutVal with h10 | h80
      · have hLhs : (s₁.gpr.get c.outPtrReg + UInt64.ofNat j).toNat = 0x10000 + j := by
          have hlt : 0x10000 + j < 2 ^ 64 := by omega
          simp [UInt64.toNat_add, h10, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]
        rw [hLhs, hRhs] at hNat; omega
      · have hLhs : (s₁.gpr.get c.outPtrReg + UInt64.ofNat j).toNat = 0x80000 + j := by
          have hlt : 0x80000 + j < 2 ^ 64 := by omega
          simp [UInt64.toNat_add, h80, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]
        rw [hLhs, hRhs] at hNat; omega
  · by_cases hUse : c.usesRbpFrame = false
    · exact Or.inl hUse
    · right
      have h4 : 0x400 ≤ (s₂.gpr.get 4).toNat := by decide
      refine ⟨hOutLt, h4, fun j k hj hk => ?_⟩
      intro hEq
      have hNat := congrArg UInt64.toNat hEq
      have hOutVal : (s₂.gpr.get c.outPtrReg).toNat = 0x10000 ∨ (s₂.gpr.get c.outPtrReg).toNat = 0x80000 := by
        change (gpr0.get c.outPtrReg).toNat = 0x10000 ∨ (gpr0.get c.outPtrReg).toNat = 0x80000
        rw [Bank16.get_ofFn _ hOutLt]
        split
        · exact Or.inr (by decide)
        · exact Or.inl (by decide)
      have hSpSub : (s₂.gpr.get 4 - 8).toNat = 0x7FFF8 := by decide
      have hRhs : ((s₂.gpr.get 4 - 8) + UInt64.ofNat k).toNat = 0x7FFF8 + k := by
        have hlt : 0x7FFF8 + k < 2 ^ 64 := by omega
        simp [UInt64.toNat_add, hSpSub, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]
      rcases hOutVal with h10 | h80
      · have hLhs : (s₂.gpr.get c.outPtrReg + UInt64.ofNat j).toNat = 0x10000 + j := by
          have hlt : 0x10000 + j < 2 ^ 64 := by omega
          simp [UInt64.toNat_add, h10, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]
        rw [hLhs, hRhs] at hNat; omega
      · have hLhs : (s₂.gpr.get c.outPtrReg + UInt64.ofNat j).toNat = 0x80000 + j := by
          have hlt : 0x80000 + j < 2 ^ 64 := by omega
          simp [UInt64.toNat_add, h80, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]
        rw [hLhs, hRhs] at hNat; omega

/-- **Anti-Vacuity / Inhabitedness Witness (`lean/uninhabited-premise-risk`) for `Arm64ContractInit`:**
    Every `AArch64` `FuncContract` with `pubGprs ⊆ 0..30` admits concrete pairs `(s₁, s₂)`
    with distinct secret memory (`0xAA ≠ 0x55`) satisfying `Arm64ContractInit c s₁ s₂`. -/
theorem aarch64_contract_init_inhabited (c : FuncContract)
    (hPubLt : ∀ r ∈ c.pubGprs, r < 31) :
    ∃ s₁ s₂ : Arm64State,
      s₁.mem 0x10000 ≠ s₂.mem 0x10000 ∧ Arm64ContractInit c s₁ s₂ := by
  let s₁ : Arm64State := {
    pc := 0, gpr := Bank32.const 0x4000, vec := Bank32.const Vec128.zero,
    cf := false, zf := false, dit := true, halted := false,
    mem := fun _ => 0xAA
  }
  let s₂ : Arm64State := { s₁ with mem := fun _ => 0x55 }
  exact ⟨s₁, s₂, by decide, ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun r hr => ⟨hPubLt r hr, rfl⟩⟩⟩

/-! #### Inductive Relational Invariant & Step Soundness for `x86_64` -/

private def x86FrameSpVal (rsp₀ : UInt64) : UInt64 :=
  ((rsp₀ - 8) &&& 0xFFFFFFFFFFFFFFE0) - 0x340

private def RelX86Gpr (s₁₀ s₂₀ : X86State) (orig : RegOrigin) (v₁ v₂ : UInt64) : Prop :=
  match orig with
  | .initSame r => r < 16 ∧ v₁ = s₁₀.gpr.get r ∧ v₂ = s₂₀.gpr.get r ∧ v₁ = v₂
  | .initOwn r => r < 16 ∧ v₁ = s₁₀.gpr.get r ∧ v₂ = s₂₀.gpr.get r
  | .spMinus8 => v₁ = s₁₀.gpr.get 4 - 8 ∧ v₂ = s₂₀.gpr.get 4 - 8 ∧ v₁ = v₂
  | .spAligned32 =>
      v₁ = (s₁₀.gpr.get 4 - 8) &&& 0xFFFFFFFFFFFFFFE0 ∧
      v₂ = (s₂₀.gpr.get 4 - 8) &&& 0xFFFFFFFFFFFFFFE0 ∧ v₁ = v₂
  | .frameSp =>
      v₁ = x86FrameSpVal (s₁₀.gpr.get 4) ∧
      v₂ = x86FrameSpVal (s₂₀.gpr.get 4) ∧ v₁ = v₂
  | .zeroConst => v₁ = 0 ∧ v₂ = 0
  | .constVal k => v₁ = k ∧ v₂ = k
  | .pubVal => v₁ = v₂
  | .secretVal => True

private theorem RelX86Gpr_public_eq {s₁₀ s₂₀ : X86State} {orig : RegOrigin} {v₁ v₂ : UInt64}
    (hRel : RelX86Gpr s₁₀ s₂₀ orig v₁ v₂) (hPub : orig.isPublic = true) :
    v₁ = v₂ := by
  cases orig with
  | initSame _ => exact hRel.2.2.2
  | initOwn _ => cases hPub
  | spMinus8 => exact hRel.2.2
  | spAligned32 => exact hRel.2.2
  | frameSp => exact hRel.2.2
  | zeroConst => exact hRel.1.trans hRel.2.symm
  | constVal _ => exact hRel.1.trans hRel.2.symm
  | pubVal => exact hRel
  | secretVal => cases hPub

private theorem RelX86Gpr_mono {s₁₀ s₂₀ : X86State} {a b : RegOrigin} {v₁ v₂ : UInt64}
    (hRel : RelX86Gpr s₁₀ s₂₀ a v₁ v₂) (hle : a.le b = true) :
    RelX86Gpr s₁₀ s₂₀ b v₁ v₂ := by
  unfold RegOrigin.le at hle
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hle
  rcases hle with (rfl | rfl) | ⟨rfl, hPub⟩
  · exact hRel
  · trivial
  · exact RelX86Gpr_public_eq hRel hPub

private def RelX86Vec (s₁₀ s₂₀ : X86State) (vo : VecOrigin) (v₁ v₂ : Vec256) : Prop :=
  match vo with
  | .initVec r =>
      r < 16 ∧
      ((v₁ = s₁₀.ymm.get r ∧ v₂ = s₂₀.ymm.get r) ∨
       (v₁ = ⟨(s₁₀.ymm.get r).w0, (s₁₀.ymm.get r).w1, 0, 0⟩ ∧
        v₂ = ⟨(s₂₀.ymm.get r).w0, (s₂₀.ymm.get r).w1, 0, 0⟩))
  | .zeroConst => v₁ = Vec256.zero ∧ v₂ = Vec256.zero
  | .pubVal => v₁ = v₂
  | .secretVal => True

private theorem RelX86Vec_public_eq {s₁₀ s₂₀ : X86State} {vo : VecOrigin} {v₁ v₂ : Vec256}
    (hRel : RelX86Vec s₁₀ s₂₀ vo v₁ v₂) (hPub : vo.isPublic = true) :
    v₁ = v₂ := by
  cases vo <;> simp [VecOrigin.isPublic, RelX86Vec] at hPub hRel
  · rw [hRel.1, hRel.2]
  · exact hRel

private theorem RelX86Vec_mono {s₁₀ s₂₀ : X86State} {a b : VecOrigin} {v₁ v₂ : Vec256}
    (hRel : RelX86Vec s₁₀ s₂₀ a v₁ v₂) (hle : a.le b = true) :
    RelX86Vec s₁₀ s₂₀ b v₁ v₂ := by
  unfold VecOrigin.le at hle
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hle
  rcases hle with (rfl | rfl) | ⟨rfl, hPub⟩
  · exact hRel
  · trivial
  · exact RelX86Vec_public_eq hRel hPub

private def RelX86Loop (s₁₀ s₂₀ s₁ s₂ : X86State) (loopSt : Nat) : Prop :=
  if loopSt == 0 then True
  else if loopSt == 1 then
    x86FrameSpVal (s₁₀.gpr.get 4) = x86FrameSpVal (s₂₀.gpr.get 4) ∧
    ∃ k : Nat, 1 ≤ k ∧ k ≤ 25 ∧
      s₁.gpr.get 1 = UInt64.ofNat k ∧ s₂.gpr.get 1 = UInt64.ofNat k ∧
      s₁.gpr.get 0 = x86FrameSpVal (s₁₀.gpr.get 4) + UInt64.ofNat ((25 - k) * 32) ∧
      s₂.gpr.get 0 = x86FrameSpVal (s₂₀.gpr.get 4) + UInt64.ofNat ((25 - k) * 32)
  else if loopSt == 2 then
    x86FrameSpVal (s₁₀.gpr.get 4) = x86FrameSpVal (s₂₀.gpr.get 4) ∧
    ∃ k : Nat, 1 ≤ k ∧ k ≤ 25 ∧
      s₁.gpr.get 1 = UInt64.ofNat k ∧ s₂.gpr.get 1 = UInt64.ofNat k ∧
      s₁.gpr.get 0 = x86FrameSpVal (s₁₀.gpr.get 4) + UInt64.ofNat ((26 - k) * 32) ∧
      s₂.gpr.get 0 = x86FrameSpVal (s₂₀.gpr.get 4) + UInt64.ofNat ((26 - k) * 32)
  else if loopSt == 3 then
    x86FrameSpVal (s₁₀.gpr.get 4) = x86FrameSpVal (s₂₀.gpr.get 4) ∧
    ∃ k' : Nat, k' ≤ 24 ∧
      s₁.gpr.get 1 = UInt64.ofNat k' ∧ s₂.gpr.get 1 = UInt64.ofNat k' ∧
      s₁.gpr.get 0 = x86FrameSpVal (s₁₀.gpr.get 4) + UInt64.ofNat ((25 - k') * 32) ∧
      s₂.gpr.get 0 = x86FrameSpVal (s₂₀.gpr.get 4) + UInt64.ofNat ((25 - k') * 32) ∧
      s₁.zf = (k' == 0) ∧ s₂.zf = (k' == 0)
  else False

private def RelX86 (s₁₀ s₂₀ : X86State) (st : X86AbsState) (s₁ s₂ : X86State) : Prop :=
  s₁.pc = s₂.pc ∧
  s₁.halted = false ∧ s₂.halted = false ∧
  (∀ r : Nat, r < 16 → RelX86Gpr s₁₀ s₂₀ (st.gpr.get r) (s₁.gpr.get r) (s₂.gpr.get r)) ∧
  (∀ i : Nat, i < 16 → RelX86Vec s₁₀ s₂₀ (st.ymm.get i) (s₁.ymm.get i) (s₂.ymm.get i)) ∧
  (st.cfPub = true → s₁.cf = s₂.cf) ∧
  (st.ofPub = true → s₁.ofFlag = s₂.ofFlag) ∧
  (st.zfPub = true → s₁.zf = s₂.zf) ∧
  (st.ymmDirty = false → s₁.ymmDirty = false ∧ s₂.ymmDirty = false) ∧
  (st.memUnmodified = true → s₁.mem = s₁₀.mem ∧ s₂.mem = s₂₀.mem) ∧
  (st.rbpSaved = true →
     s₁₀.gpr.get 4 = s₂₀.gpr.get 4 ∧
     readMem64 s₁.mem (s₁₀.gpr.get 4 - 8) = s₁₀.gpr.get 5 ∧
     readMem64 s₂.mem (s₂₀.gpr.get 4 - 8) = s₂₀.gpr.get 5) ∧
  RelX86Loop s₁₀ s₂₀ s₁ s₂ st.stackZeroLoop

private theorem RelX86_mono {s₁₀ s₂₀ s₁ s₂ : X86State} {a b : X86AbsState}
    (hRel : RelX86 s₁₀ s₂₀ a s₁ s₂) (hle : a.le b = true) :
    RelX86 s₁₀ s₂₀ b s₁ s₂ := by
  unfold X86AbsState.le at hle
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hle
  rcases hle with ⟨⟨⟨⟨⟨⟨⟨⟨hGpr, hYmm⟩, hCf⟩, hOf⟩, hZf⟩, hDirty⟩, hMem⟩, hRbp⟩, hLoop⟩
  rcases hRel with ⟨hPc, hH1, hH2, rGpr, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp, rLoop⟩
  refine ⟨hPc, hH1, hH2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr; exact RelX86Gpr_mono (rGpr r hr) (Bank16.allIdx_get hGpr hr)
  · intro i hi; exact RelX86Vec_mono (rYmm i hi) (Bank16.allIdx_get hYmm hi)
  · intro hb; exact hCf.elim (fun hbf => nomatch hbf.symm.trans hb) (fun ha => rCf ha)
  · intro hb; exact hOf.elim (fun hbf => nomatch hbf.symm.trans hb) (fun ha => rOf ha)
  · intro hb; exact hZf.elim (fun hbf => nomatch hbf.symm.trans hb) (fun ha => rZf ha)
  · intro hb; exact hDirty.elim (fun hbt => nomatch hbt.symm.trans hb) (fun ha => rDirty ha)
  · intro hb; exact hMem.elim (fun hbf => nomatch hbf.symm.trans hb) (fun ha => rMem ha)
  · intro hb; exact hRbp.elim (fun hbf => nomatch hbf.symm.trans hb) (fun ha => rRbp ha)
  · rcases hLoop with hb0 | heq
    · simp [RelX86Loop, hb0]
    · rwa [← heq]

private theorem RelX86_init {c : FuncContract} {s₁ s₂ : X86State}
    (hInit : X86ContractInit c s₁ s₂) :
    RelX86 s₁ s₂ (initX86AbsState c) s₁ s₂ := by
  rcases hInit with ⟨hpc1, hpc2, hh1, hh2, hd1, hd2, hPubGprs, _, _, _⟩
  refine ⟨by omega, hh1, hh2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    unfold initX86AbsState
    rw [Bank16.get_ofFn _ hr]
    split
    · rename_i hMemPub
      exact ⟨hr, rfl, rfl, (hPubGprs r hMemPub).2⟩
    · split
      · exact ⟨hr, rfl, rfl⟩
      · trivial
  · intro i hi
    unfold initX86AbsState
    rw [Bank16.get_ofFn _ hi]
    exact ⟨hi, Or.inl ⟨rfl, rfl⟩⟩
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro _; exact ⟨hd1, hd2⟩
  · intro _; exact ⟨rfl, rfl⟩
  · intro h; cases h
  · simp [initX86AbsState, RelX86Loop]

private theorem evalX86Alu_congr (op : X86AluOp) (is64 : Bool)
    {a₁ a₂ b₁ b₂ : UInt64} {cf₁ cf₂ : Bool}
    (ha : a₁ = a₂) (hb : b₁ = b₂)
    (hcf : (if op == .adc || op == .sbb then true else false) = true → cf₁ = cf₂) :
    evalX86Alu op is64 a₁ b₁ cf₁ = evalX86Alu op is64 a₂ b₂ cf₂ := by
  subst ha hb
  cases op <;> simp_all [evalX86Alu]

private theorem evalX86AluOf_congr (op : X86AluOp) (is64 : Bool)
    {a₁ a₂ b₁ b₂ : UInt64} {cf₁ cf₂ : Bool}
    (ha : a₁ = a₂) (hb : b₁ = b₂)
    (hcf : (if op == .adc || op == .sbb then true else false) = true → cf₁ = cf₂) :
    evalX86AluOf op is64 a₁ b₁ cf₁ = evalX86AluOf op is64 a₂ b₂ cf₂ := by
  subst ha hb
  cases op <;> simp_all [evalX86AluOf]

private theorem evalX86AluOf_sbb_self (is64 : Bool) (v : UInt64) (cf : Bool) :
    evalX86AluOf .sbb is64 v v cf = false := by
  dsimp only [evalX86AluOf, signedOutOfBounds]
  rw [Int.sub_self]
  cases is64 <;> cases cf <;> decide

private theorem evalX86Shift_fst_congr (sk : X86ShiftKind) (is64 : Bool) {v₁ v₂ : UInt64} (cnt : Nat)
    (cf₁ of₁ zf₁ cf₂ of₂ zf₂ : Bool) (hv : v₁ = v₂) :
    (evalX86Shift sk is64 v₁ cnt cf₁ of₁ zf₁).1 = (evalX86Shift sk is64 v₂ cnt cf₂ of₂ zf₂).1 := by
  subst hv
  cases is64 <;> cases sk <;> (dsimp only [evalX86Shift]; split <;> rfl)

private theorem evalX86Shift_zf (sk : X86ShiftKind) (is64 : Bool) (v : UInt64) (cnt : Nat)
    (cf of_ zf : Bool) :
    (evalX86Shift sk is64 v cnt cf of_ zf).2.2.2 =
      if x86ShiftPreservesZf sk is64 cnt then zf
      else (evalX86Shift sk is64 v cnt cf of_ zf).1 == 0 := by
  cases is64 <;> cases sk <;> (dsimp only [evalX86Shift, x86ShiftPreservesZf]; split <;> rename_i hc0 <;> simp [hc0])

private theorem evalX86Addr_public_eq {s₁₀ s₂₀ s₁ s₂ : X86State} {st : X86AbsState}
    {addr : X86MemAddr} (nextPc : Nat)
    (hAddrOk : x86AddrIsPublic st addr = true)
    (hRegsOk : x86AddrRegsValid addr = true)
    (hGpr : ∀ r < 16, RelX86Gpr s₁₀ s₂₀ (st.gpr.get r) (s₁.gpr.get r) (s₂.gpr.get r)) :
    evalX86Addr s₁ nextPc addr = evalX86Addr s₂ nextPc addr := by
  cases addr with
  | baseDisp base disp =>
    simp only [x86AddrIsPublic, x86AddrRegsValid, decide_eq_true_eq] at hAddrOk hRegsOk
    rw [evalX86Addr, evalX86Addr, RelX86Gpr_public_eq (hGpr base hRegsOk) hAddrOk]
  | ripDisp disp => rfl
  | absDisp disp => rfl
  | indexedSib baseOpt idx scale disp =>
    cases baseOpt with
    | none =>
      simp only [x86AddrIsPublic, x86AddrRegsValid, Bool.and_true, decide_eq_true_eq] at hAddrOk hRegsOk
      have hIdx := RelX86Gpr_public_eq (hGpr idx hRegsOk) hAddrOk
      simp [evalX86Addr, hIdx]
    | some b =>
      simp only [x86AddrIsPublic, x86AddrRegsValid, Bool.and_eq_true, decide_eq_true_eq] at hAddrOk hRegsOk
      have hIdx := RelX86Gpr_public_eq (hGpr idx hRegsOk.1) hAddrOk.1
      have hBase := RelX86Gpr_public_eq (hGpr b hRegsOk.2) hAddrOk.2
      simp [evalX86Addr, hIdx, hBase]

private theorem isInPubMemRegion_bytes_eq {c : FuncContract} {s₁₀ s₂₀ s₁ s₂ : X86State}
    {st : X86AbsState} {addr : X86MemAddr} {wBytes : Nat} (nextPc : Nat)
    (hInit : X86ContractInit c s₁₀ s₂₀)
    (hRel : RelX86 s₁₀ s₂₀ st s₁ s₂)
    (hRegsOk : x86AddrRegsValid addr = true)
    (hIn : isInPubMemRegion c st addr wBytes = true) :
    ∀ j : Nat, j < wBytes →
      s₁.mem (evalX86Addr s₁ nextPc addr + UInt64.ofNat j) =
      s₂.mem (evalX86Addr s₂ nextPc addr + UInt64.ofNat j) := by
  rcases hRel with ⟨_, _, _, rGpr, _, _, _, _, _, rMem, _, _⟩
  unfold isInPubMemRegion at hIn
  cases hMemUnmod : st.memUnmodified
  · simp [hMemUnmod] at hIn
  · simp only [hMemUnmod, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hIn
    cases addr with
    | ripDisp _ => cases hIn
    | absDisp _ => cases hIn
    | indexedSib _ _ _ _ => cases hIn
    | baseDisp base disp =>
      simp only [x86AddrRegsValid, decide_eq_true_eq] at hRegsOk
      cases hOrig : st.gpr.get base <;> simp only [hOrig] at hIn <;> try contradiction
      case initSame r =>
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at hIn
        rcases hIn with ⟨hrPub, ⟨⟨ptrReg, regionLen⟩, hRegMem, hPtrEq, hBound⟩⟩
        subst hPtrEq
        rcases rMem hMemUnmod with ⟨hm1, hm2⟩
        have hBaseRel := rGpr base hRegsOk
        rw [hOrig] at hBaseRel
        rcases hBaseRel with ⟨_, hb1, hb2, _⟩
        rcases hInit with ⟨_, _, _, _, _, _, _, hPubMem, _, _⟩
        have hByte := (hPubMem (ptrReg, regionLen) hRegMem).2
        intro j hj
        have hAdd (x : UInt64) :
            x + disp + UInt64.ofNat j = x + UInt64.ofNat (disp.toNat + j) := by
          apply uint64_eq_of_toNat_eq
          simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.add_mod_mod, Nat.mod_add_mod]
          congr 1; omega
        rw [hm1, hm2, evalX86Addr, evalX86Addr, hb1, hb2, hAdd, hAdd]
        exact hByte (disp.toNat + j) (by omega)

private theorem frameSp_store_disjoint_spSlot {rsp₀ disp : UInt64} {wBytes : Nat}
    (hHeadroom : 0x400 ≤ rsp₀.toNat)
    (hDispBound : disp.toNat + wBytes ≤ 0x320) :
    ∀ j k : Nat, j < wBytes → k < 8 →
      (rsp₀ - 8) + UInt64.ofNat k ≠ x86FrameSpVal rsp₀ + disp + UInt64.ofNat j := by
  intro j k hj hk hEq
  have hRspLt := rsp₀.toNat_lt
  have hPow : (2 : Nat) ^ 64 = 0x10000000000000000 := rfl
  have hSpSlot : (rsp₀ - 8).toNat = rsp₀.toNat - 8 := by
    have h8 : (8 : UInt64).toNat = 8 := rfl
    simp only [UInt64.toNat_sub, h8, hPow]; omega
  have hAlign : ((rsp₀ - 8) &&& (0xFFFFFFFFFFFFFFE0 : UInt64)).toNat = ((rsp₀.toNat - 8) / 32) * 32 := by
    rw [align32_toNat, hSpSlot]
  have hFsp : (x86FrameSpVal rsp₀).toNat = ((rsp₀.toNat - 8) / 32) * 32 - 0x340 := by
    unfold x86FrameSpVal
    have h340 : (0x340 : UInt64).toNat = 0x340 := rfl
    simp only [UInt64.toNat_sub, hAlign, h340, hPow]; omega
  have hLhs : ((rsp₀ - 8) + UInt64.ofNat k).toNat = rsp₀.toNat - 8 + k := by
    simp only [UInt64.toNat_add, hSpSlot, UInt64.toNat_ofNat', hPow]; omega
  have hAdd1 : (x86FrameSpVal rsp₀ + disp).toNat = (x86FrameSpVal rsp₀).toNat + disp.toNat := by
    simp only [UInt64.toNat_add, hFsp, hPow]; omega
  have hRhs : (x86FrameSpVal rsp₀ + disp + UInt64.ofNat j).toNat =
      (x86FrameSpVal rsp₀).toNat + disp.toNat + j := by
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', hAdd1, hFsp, hPow]; omega
  have hNat := congrArg UInt64.toNat hEq
  rw [hLhs, hRhs, hFsp] at hNat
  omega

private theorem storePreservesSavedRbp_disjoint {c : FuncContract} {s₁₀ s₂₀ s₁ s₂ : X86State}
    {st : X86AbsState} {addr : X86MemAddr} {wBytes : Nat} (nextPc : Nat)
    (hInit : X86ContractInit c s₁₀ s₂₀)
    (hRel : RelX86 s₁₀ s₂₀ st s₁ s₂)
    (hRegsOk : x86AddrRegsValid addr = true)
    (hKeep : storePreservesSavedRbp c st addr wBytes = true) :
    (∀ j k : Nat, j < wBytes → k < 8 →
       (s₁₀.gpr.get 4 - 8) + UInt64.ofNat k ≠ evalX86Addr s₁ nextPc addr + UInt64.ofNat j) ∧
    (∀ j k : Nat, j < wBytes → k < 8 →
       (s₂₀.gpr.get 4 - 8) + UInt64.ofNat k ≠ evalX86Addr s₂ nextPc addr + UInt64.ofNat j) := by
  rcases hRel with ⟨_, _, _, rGpr, _, _, _, _, _, _, _, rLoop⟩
  unfold storePreservesSavedRbp at hKeep
  cases hRbp : st.rbpSaved
  · simp [hRbp] at hKeep
  · cases hUse : c.usesRbpFrame
    · simp [hRbp, hUse] at hKeep
    · simp only [hRbp, hUse, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hKeep
      rcases hInit with ⟨_, _, _, _, _, _, _, _, hFp1, hFp2⟩
      have hFp1' : c.outPtrReg < 16 ∧ 0x400 ≤ (s₁₀.gpr.get 4).toNat ∧
          ∀ j k : Nat, j < c.outBytes → k < 8 →
            s₁₀.gpr.get c.outPtrReg + UInt64.ofNat j ≠ (s₁₀.gpr.get 4 - 8) + UInt64.ofNat k :=
        hFp1.elim (fun hFalse => nomatch hUse.symm.trans hFalse) id
      have hFp2' : c.outPtrReg < 16 ∧ 0x400 ≤ (s₂₀.gpr.get 4).toNat ∧
          ∀ j k : Nat, j < c.outBytes → k < 8 →
            s₂₀.gpr.get c.outPtrReg + UInt64.ofNat j ≠ (s₂₀.gpr.get 4 - 8) + UInt64.ofNat k :=
        hFp2.elim (fun hFalse => nomatch hUse.symm.trans hFalse) id
      cases addr with
      | ripDisp _ => cases hKeep
      | absDisp _ => cases hKeep
      | indexedSib _ _ _ _ => cases hKeep
      | baseDisp base disp =>
        simp only [x86AddrRegsValid, decide_eq_true_eq] at hRegsOk
        by_cases hc1 : (st.gpr.get base == .frameSp && decide (disp.toNat + wBytes ≤ 0x320)) = true
        · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc1
          have hBRel := rGpr base hRegsOk
          rw [hc1.1] at hBRel
          rcases hBRel with ⟨hb1, hb2, _⟩
          refine ⟨fun j k hj hk => ?_, fun j k hj hk => ?_⟩
          · rw [evalX86Addr, hb1]
            exact frameSp_store_disjoint_spSlot hFp1'.2.1 hc1.2 j k hj hk
          · rw [evalX86Addr, hb2]
            exact frameSp_store_disjoint_spSlot hFp2'.2.1 hc1.2 j k hj hk
        · simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hKeep
          by_cases hc2 : (st.gpr.get base == .initSame c.outPtrReg &&
              c.outBytes == 0x320 && decide (disp.toNat + wBytes ≤ 0x320)) = true
          · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc2
            rcases hc2 with ⟨⟨hOrig, hOutSz⟩, hDisp⟩
            have hBRel := rGpr base hRegsOk
            rw [hOrig] at hBRel
            rcases hBRel with ⟨_, hb1, hb2, _⟩
            have hAdd (x : UInt64) (j : Nat) :
                x + disp + UInt64.ofNat j = x + UInt64.ofNat (disp.toNat + j) := by
              apply uint64_eq_of_toNat_eq
              simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.add_mod_mod, Nat.mod_add_mod]
              congr 1; omega
            refine ⟨fun j k hj hk hEq => ?_, fun j k hj hk hEq => ?_⟩
            · rw [evalX86Addr, hb1, hAdd] at hEq
              exact hFp1'.2.2 (disp.toNat + j) k (by omega) hk hEq.symm
            · rw [evalX86Addr, hb2, hAdd] at hEq
              exact hFp2'.2.2 (disp.toNat + j) k (by omega) hk hEq.symm
          · simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hKeep
            by_cases hc3 : (base == 0 && disp == 0 && wBytes == 32 && st.stackZeroLoop == 1) = true
            · simp only [Bool.and_eq_true, beq_iff_eq] at hc3
              rcases hc3 with ⟨⟨⟨rfl, rfl⟩, rfl⟩, hLoop1⟩
              unfold RelX86Loop at rLoop
              simp only [hLoop1, show (1 == 0) = false from rfl, beq_self_eq_true, ↓reduceIte] at rLoop
              rcases rLoop with ⟨_, ⟨m, hm1, hm25, _, _, ha1, ha2⟩⟩
              have hAdd0 (x : UInt64) : x + 0 = x := by
                apply UInt64.eq_of_toBitVec_eq; simp
              have hDispM : (UInt64.ofNat ((25 - m) * 32)).toNat + 32 ≤ 0x320 := by
                have hlt : (25 - m) * 32 < 2 ^ 64 := by omega
                simp [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]; omega
              refine ⟨fun j k hj hk => ?_, fun j k hj hk => ?_⟩
              · rw [evalX86Addr, ha1, hAdd0]
                exact frameSp_store_disjoint_spSlot hFp1'.2.1 hDispM j k hj hk
              · rw [evalX86Addr, ha2, hAdd0]
                exact frameSp_store_disjoint_spSlot hFp2'.2.1 hDispM j k hj hk
            · simp [hc3] at hKeep

private def checkLoopDecHelper : Bool :=
  (List.range 26).all (fun k =>
    if k == 0 then true
    else
      let res := maskGprWidth false (maskGprWidth false (UInt64.ofNat k) + (0 - 1))
      let ofFlag := evalX86IncDecOf false false (UInt64.ofNat k)
      (res == UInt64.ofNat (k - 1)) && ((res == 0) == (k - 1 == 0)) && !ofFlag)

private theorem checkLoopDecHelper_true : checkLoopDecHelper = true := by decide

private theorem loop_dec_ecx_step {k : Nat} (hk1 : 1 ≤ k) (hk25 : k ≤ 25) :
    let res := maskGprWidth false (maskGprWidth false (UInt64.ofNat k) + (0 - 1))
    res = UInt64.ofNat (k - 1) ∧ (res == 0) = (k - 1 == 0) ∧
      evalX86IncDecOf false false (UInt64.ofNat k) = false := by
  have hHelper := checkLoopDecHelper_true
  unfold checkLoopDecHelper at hHelper
  have hMem : k ∈ List.range 26 := List.mem_range.mpr (by omega)
  have hAll := List.all_eq_true.mp hHelper k hMem
  have hk0 : (k == 0) = false := beq_false_of_ne (by omega)
  simp only [hk0, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hAll
  exact ⟨hAll.1.1, hAll.1.2, hAll.2⟩

private theorem RelX86Gpr_set {s₁₀ s₂₀ : X86State} {g : Bank16 RegOrigin} {b₁ b₂ : Bank16 UInt64}
    {dst : Nat} {orig : RegOrigin} {v₁ v₂ : UInt64}
    (hd : dst < 16)
    (hOld : ∀ r < 16, RelX86Gpr s₁₀ s₂₀ (g.get r) (b₁.get r) (b₂.get r))
    (hNew : RelX86Gpr s₁₀ s₂₀ orig v₁ v₂) :
    ∀ r < 16, RelX86Gpr s₁₀ s₂₀ ((g.set dst orig).get r) ((b₁.set dst v₁).get r) ((b₂.set dst v₂).get r) := by
  intro r hr
  by_cases heq : r = dst
  · subst heq; simp only [Bank16.get_set_eq]; exact hNew
  · rw [Bank16.get_set_ne _ _ hd hr (Ne.symm heq),
        Bank16.get_set_ne _ _ hd hr (Ne.symm heq),
        Bank16.get_set_ne _ _ hd hr (Ne.symm heq)]
    exact hOld r hr

private theorem RelX86Vec_set {s₁₀ s₂₀ : X86State} {ym : Bank16 VecOrigin} {b₁ b₂ : Bank16 Vec256}
    {dst : Nat} {vo : VecOrigin} {v₁ v₂ : Vec256}
    (hd : dst < 16)
    (hOld : ∀ i < 16, RelX86Vec s₁₀ s₂₀ (ym.get i) (b₁.get i) (b₂.get i))
    (hNew : RelX86Vec s₁₀ s₂₀ vo v₁ v₂) :
    ∀ i < 16, RelX86Vec s₁₀ s₂₀ ((ym.set dst vo).get i) ((b₁.set dst v₁).get i) ((b₂.set dst v₂).get i) := by
  intro i hi
  by_cases heq : i = dst
  · subst heq; simp only [Bank16.get_set_eq]; exact hNew
  · rw [Bank16.get_set_ne _ _ hd hi (Ne.symm heq),
        Bank16.get_set_ne _ _ hd hi (Ne.symm heq),
        Bank16.get_set_ne _ _ hd hi (Ne.symm heq)]
    exact hOld i hi

private theorem readMem128_congr {m1 m2 : UInt64 → UInt8} {addr : UInt64}
    (h : ∀ j : Nat, j < 16 → m1 (addr + UInt64.ofNat j) = m2 (addr + UInt64.ofNat j)) :
    readMem128 m1 addr = readMem128 m2 addr := by
  have h8 : readMem64 m1 (addr + 8) = readMem64 m2 (addr + 8) := by
    apply readMem64_congr; intro j hj
    have hAdd : addr + 8 + UInt64.ofNat j = addr + UInt64.ofNat (8 + j) := by
      apply uint64_eq_of_toNat_eq
      have h8v : (8 : UInt64).toNat = 8 := rfl
      simp only [UInt64.toNat_add, UInt64.toNat_ofNat', h8v, Nat.add_mod_mod, Nat.mod_add_mod]
      congr 1; omega
    rw [hAdd]; exact h (8 + j) (by omega)
  unfold readMem128
  rw [readMem64_congr (fun j hj => h j (by omega)), h8]

private theorem readMem256_congr {m1 m2 : UInt64 → UInt8} {addr : UInt64}
    (h : ∀ j : Nat, j < 32 → m1 (addr + UInt64.ofNat j) = m2 (addr + UInt64.ofNat j)) :
    readMem256 m1 addr = readMem256 m2 addr := by
  have hSlot (base : Nat) (hb : base + 8 ≤ 32) :
      readMem64 m1 (addr + UInt64.ofNat base) = readMem64 m2 (addr + UInt64.ofNat base) := by
    apply readMem64_congr; intro j hj
    have hAdd : addr + UInt64.ofNat base + UInt64.ofNat j = addr + UInt64.ofNat (base + j) := by
      apply uint64_eq_of_toNat_eq
      simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.add_mod_mod, Nat.mod_add_mod]
      congr 1; omega
    rw [hAdd]; exact h (base + j) (by omega)
  have h0 := readMem64_congr (fun j hj => h j (by omega))
  have h8 : readMem64 m1 (addr + 8) = readMem64 m2 (addr + 8) := hSlot 8 (by omega)
  have h16 : readMem64 m1 (addr + 16) = readMem64 m2 (addr + 16) := hSlot 16 (by omega)
  have h24 : readMem64 m1 (addr + 24) = readMem64 m2 (addr + 24) := hSlot 24 (by omega)
  unfold readMem256
  rw [h0, h8, h16, h24]

private theorem evalX86Cond_public_eq {st : X86AbsState} {s₁ s₂ : X86State} {cc : Nat}
    (hPub : x86CondIsPublic cc st = true)
    (rCf : st.cfPub = true → s₁.cf = s₂.cf)
    (rZf : st.zfPub = true → s₁.zf = s₂.zf) :
    evalX86Cond cc s₁ = evalX86Cond cc s₂ := by
  unfold x86CondIsPublic at hPub
  unfold evalX86Cond
  by_cases c2 : cc == 2
  · simp [c2] at hPub ⊢; exact rCf hPub
  · by_cases c3 : cc == 3
    · simp [c2, c3] at hPub ⊢; exact rCf hPub
    · by_cases c4 : cc == 4
      · simp [c2, c3, c4] at hPub ⊢; exact rZf hPub
      · by_cases c5 : cc == 5
        · simp [c2, c3, c4, c5] at hPub ⊢; exact rZf hPub
        · simp [c2, c3, c4, c5] at hPub

private theorem evalX86Alu_xor_self (is64 : Bool) (v : UInt64) (cf : Bool) :
    evalX86Alu .xorOp is64 v v cf = (0, false, true) := by
  unfold evalX86Alu maskGprWidth
  have hxor : v ^^^ v = 0 := by apply UInt64.eq_of_toBitVec_eq; simp
  cases is64 <;> simp only [hxor] <;> rfl

private theorem maskGprWidth_toNat_lt (is64 : Bool) (v : UInt64) :
    (maskGprWidth is64 v).toNat < (if is64 then 0x10000000000000000 else 0x100000000) := by
  cases is64
  · unfold maskGprWidth
    simp only [Bool.false_eq_true, ↓reduceIte, UInt64.toNat_and]
    have h32 : (0xFFFFFFFF : UInt64).toNat = 0xFFFFFFFF := rfl
    rw [h32]
    have := @Nat.and_le_right v.toNat 0xFFFFFFFF
    omega
  · unfold maskGprWidth
    simpa using v.toNat_lt

private theorem evalX86Alu_sbb_self_congr (is64 : Bool) (v₁ v₂ : UInt64) (cf : Bool) :
    evalX86Alu .sbb is64 v₁ v₁ cf = evalX86Alu .sbb is64 v₂ v₂ cf := by
  have h1 := maskGprWidth_toNat_lt is64 v₁
  have h2 := maskGprWidth_toNat_lt is64 v₂
  unfold evalX86Alu
  cases cf <;> cases is64 <;> simp only [↓reduceIte, Bool.false_eq_true, Nat.add_zero, Nat.sub_zero] at h1 h2 ⊢
  · have e1 : (maskGprWidth false v₁).toNat + 0x100000000 * 2 - (maskGprWidth false v₁).toNat =
        0x100000000 * 2 := by omega
    have e2 : (maskGprWidth false v₂).toNat + 0x100000000 * 2 - (maskGprWidth false v₂).toNat =
        0x100000000 * 2 := by omega
    have l1 : decide ((maskGprWidth false v₁).toNat < (maskGprWidth false v₁).toNat) = false :=
      decide_eq_false (by omega)
    have l2 : decide ((maskGprWidth false v₂).toNat < (maskGprWidth false v₂).toNat) = false :=
      decide_eq_false (by omega)
    rw [l1, l2, e1, e2]
  · unfold maskGprWidth at h1 h2 ⊢
    simp only [↓reduceIte] at h1 h2 ⊢
    have e1 : v₁.toNat + 0x10000000000000000 * 2 - v₁.toNat = 0x10000000000000000 * 2 := by omega
    have e2 : v₂.toNat + 0x10000000000000000 * 2 - v₂.toNat = 0x10000000000000000 * 2 := by omega
    have l1 : decide (v₁.toNat < v₁.toNat) = false := decide_eq_false (by omega)
    have l2 : decide (v₂.toNat < v₂.toNat) = false := decide_eq_false (by omega)
    rw [l1, l2, e1, e2]
  · have l1 : decide ((maskGprWidth false v₁).toNat < (maskGprWidth false v₁).toNat + 1) = true :=
      decide_eq_true (by omega)
    have l2 : decide ((maskGprWidth false v₂).toNat < (maskGprWidth false v₂).toNat + 1) = true :=
      decide_eq_true (by omega)
    have e1 : (maskGprWidth false v₁).toNat + 0x100000000 * 2 - (maskGprWidth false v₁).toNat - 1 =
        0x100000000 * 2 - 1 := by omega
    have e2 : (maskGprWidth false v₂).toNat + 0x100000000 * 2 - (maskGprWidth false v₂).toNat - 1 =
        0x100000000 * 2 - 1 := by omega
    rw [l1, l2, e1, e2]
  · unfold maskGprWidth at h1 h2 ⊢
    simp only [↓reduceIte] at h1 h2 ⊢
    have l1 : decide (v₁.toNat < v₁.toNat + 1) = true := decide_eq_true (by omega)
    have l2 : decide (v₂.toNat < v₂.toNat + 1) = true := decide_eq_true (by omega)
    have e1 : v₁.toNat + 0x10000000000000000 * 2 - v₁.toNat - 1 = 0x10000000000000000 * 2 - 1 := by omega
    have e2 : v₂.toNat + 0x10000000000000000 * 2 - v₂.toNat - 1 = 0x10000000000000000 * 2 - 1 := by omega
    rw [l1, l2, e1, e2]

private theorem evalVecShift256_zero (sk : X86VecShiftKind) (is256 : Bool) (imm : Nat) :
    clampVecWidth is256 (evalVecShift256 sk Vec256.zero imm) = Vec256.zero := by
  have hzL (c : UInt64) : (0 : UInt64) <<< c = 0 := by apply UInt64.eq_of_toBitVec_eq; simp
  have hzR (c : UInt64) : (0 : UInt64) >>> c = 0 := by apply UInt64.eq_of_toBitVec_eq; simp
  have hzA (m : UInt64) : (0 : UInt64) &&& m = 0 := by apply UInt64.eq_of_toBitVec_eq; simp
  unfold evalVecShift256 clampVecWidth Vec256.zero
  cases sk <;> cases is256 <;> simp [hzL, hzR, hzA] <;>
    repeat' split <;> simp_all [hzL, hzR, hzA]

private theorem uint64_add_zero (x : UInt64) : x + 0 = x := by
  apply UInt64.eq_of_toBitVec_eq; simp

private theorem findInstrAtPc_offset {Instr : Type} {pc : Nat} {prog : List (DecodedInstr Instr)}
    {d : DecodedInstr Instr} (h : findInstrAtPc pc prog = some d) :
    d.offset = pc := by
  induction prog with
  | nil => cases h
  | cons x xs ih =>
    unfold findInstrAtPc at h
    by_cases heq : x.offset == pc
    · simp [heq] at h; subst h; exact beq_iff_eq.mp heq
    · simp [heq] at h; exact ih h

private theorem transferX86Instr_step_sound {c : FuncContract}
    {s₁₀ s₂₀ s₁ s₂ : X86State} {d : DecodedInstr X86Instr}
    {st : X86AbsState} {succs : List (Nat × X86AbsState)}
    (hInit : X86ContractInit c s₁₀ s₂₀)
    (hRel : RelX86 s₁₀ s₂₀ st s₁ s₂)
    (_hPcEq : s₁.pc = d.offset)
    (hTr : transferX86Instr c d st = some succs) :
    let (s₁', obs₁) := stepX86 d s₁
    let (s₂', obs₂) := stepX86 d s₂
    obs₁ = obs₂ ∧
    obs₁.isDoitSafe = true ∧
    ((s₁'.halted = true ∧ s₂'.halted = true ∧ X86ExitHygiene c s₁₀ s₂₀ s₁' s₂') ∨
     (∃ nst : X86AbsState, (s₁'.pc, nst) ∈ succs ∧ RelX86 s₁₀ s₂₀ nst s₁' s₂')) := by
  cases hValid : x86InstrRegsValid d.instr
  · unfold transferX86Instr at hTr; simp [hValid] at hTr
  · rcases hRel with ⟨hPc12, hH1, hH2, rGpr, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp, rLoop⟩
    have hRelFull : RelX86 s₁₀ s₂₀ st s₁ s₂ :=
      ⟨hPc12, hH1, hH2, rGpr, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp, rLoop⟩
    cases hIns : d.instr <;>
      unfold transferX86Instr at hTr <;>
      rw [hIns] at hTr hValid <;>
      simp only [hValid, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr <;>
      simp only [x86InstrRegsValid, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hValid
    case nop =>
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp,
        by simp [RelX86Loop]⟩
    case mfence =>
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp,
        by simp [RelX86Loop]⟩
    case pushReg reg =>
      by_cases hPushOk : (c.usesRbpFrame && reg == 5 && st.gpr.get 4 == .initSame 4 &&
          st.gpr.get 5 == .initOwn 5 && decide (4 ∈ c.pubGprs) && !st.rbpSaved) = true
      · simp only [hPushOk, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at hPushOk
        rcases hPushOk with ⟨⟨⟨⟨⟨_, rfl⟩, hSp4⟩, hBp5⟩, _⟩, _⟩
        have r4 := rGpr 4 (by omega); rw [hSp4] at r4; rcases r4 with ⟨_, hs1_4, hs2_4, h4eq⟩
        have r5 := rGpr 5 (by omega); rw [hBp5] at r5; rcases r5 with ⟨_, hs1_5, hs2_5⟩
        have hSpEq0 : s₁₀.gpr.get 4 = s₂₀.gpr.get 4 := by rw [← hs1_4, ← hs2_4, h4eq]
        simp only [stepX86, hIns, hs1_4, hs2_4, hs1_5, hs2_5, ← hSpEq0, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2,
          RelX86Gpr_set (by omega) rGpr ⟨rfl, hSpEq0 ▸ rfl, rfl⟩,
          rYmm, rCf, rOf, rZf, rDirty, (fun h => nomatch h), ?_, by simp [RelX86Loop]⟩
        intro _
        exact ⟨hSpEq0, readMem64_writeMem64_self _ _ _, hSpEq0 ▸ readMem64_writeMem64_self _ _ _⟩
      · have hF : (c.usesRbpFrame && reg == 5 && st.gpr.get 4 == .initSame 4 &&
            st.gpr.get 5 == .initOwn 5 && decide (4 ∈ c.pubGprs) && !st.rbpSaved) = false :=
          Bool.eq_false_iff.mpr hPushOk
        simp only [hF, Bool.false_eq_true, ↓reduceIte] at hTr; cases hTr
    case popReg reg =>
      by_cases hPopOk : (c.usesRbpFrame && reg == 5 && st.gpr.get 4 == .spMinus8 && st.rbpSaved) = true
      · simp only [hPopOk, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [Bool.and_eq_true, beq_iff_eq] at hPopOk
        rcases hPopOk with ⟨⟨⟨_, rfl⟩, hSp4⟩, hRbpSaved⟩
        have r4 := rGpr 4 (by omega); rw [hSp4] at r4; rcases r4 with ⟨hs1_4, hs2_4, h4eq⟩
        rcases rRbp hRbpSaved with ⟨hSp0Eq, hMem5_1, hMem5_2⟩
        have hAdd8 (x : UInt64) : (x - 8) + 8 = x := by
          apply UInt64.eq_of_toBitVec_eq; simp
        simp only [stepX86, hIns, hs1_4, hs2_4, ← hSp0Eq, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm, rCf, rOf, rZf, rDirty, rMem,
          fun _ => ⟨hSp0Eq, hMem5_1, hSp0Eq ▸ hMem5_2⟩, by simp [RelX86Loop]⟩
        refine RelX86Gpr_set (by omega)
          (RelX86Gpr_set (by omega) rGpr ⟨by omega, hAdd8 _, hSp0Eq ▸ hAdd8 _, rfl⟩)
          ⟨by omega, hMem5_1, by rwa [hSp0Eq]⟩
      · have hF : (c.usesRbpFrame && reg == 5 && st.gpr.get 4 == .spMinus8 && st.rbpSaved) = false :=
          Bool.eq_false_iff.mpr hPopOk
        simp only [hF, Bool.false_eq_true, ↓reduceIte] at hTr; cases hTr
    case ret =>
      by_cases hRetOk : ((st.gpr.get 4 == .initSame 4 && decide (4 ∈ c.pubGprs)) &&
          (((st.gpr.get 3).le (.initOwn 3) || st.gpr.get 3 == .initSame 3) &&
           [3, 5, 12, 13, 14, 15].all (fun r => st.gpr.get r == .initOwn r || st.gpr.get r == .initSame r)) &&
          !st.ymmDirty &&
          st.ymm.allIdx (fun _ vo => vo != .secretVal && vo != .pubVal) &&
          c.wipedScratchGprs.all (fun r => st.gpr.get r == .zeroConst)) = true
      · simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq,
          List.all_eq_true] at hRetOk
        rcases hRetOk with ⟨⟨⟨⟨⟨hSp4, _⟩, ⟨_, hCallee⟩⟩, hClean⟩, hVecWiped⟩, hGprWiped⟩
        simp only [stepX86, hIns, true_and]
        left
        refine ⟨?_, ?_, rDirty hClean, ?_, ?_⟩
        · have r4 := rGpr 4 (by omega); rw [hSp4] at r4; exact ⟨r4.2.1, r4.2.2.1⟩
        · intro r hr
          have hcr := hCallee r hr
          have hr16 : r < 16 := by simp at hr; omega
          have rr := rGpr r hr16
          rcases hcr with hOwn | hSame
          · rw [hOwn] at rr; exact rr.2
          · rw [hSame] at rr; exact ⟨rr.2.1, rr.2.2.1⟩
        · intro i hi
          have hNotSec := Bank16.allIdx_get hVecWiped hi
          simp only [Bool.and_eq_true, bne_iff_ne] at hNotSec
          have rv := rYmm i hi
          cases hVo : st.ymm.get i <;> rw [hVo] at rv hNotSec
          · exact Or.inr ⟨_, rv.1, rv.2⟩
          · exact Or.inl rv
          · exact absurd rfl hNotSec.2
          · exact absurd rfl hNotSec.1
        · intro r hr
          have hZ := hGprWiped r hr
          by_cases hr16 : r < 16
          · have rr := rGpr r hr16; rw [hZ] at rr; exact rr
          · have h15 : ∀ {α : Type} (b : Bank16 α), b.get r = b.get 15 := fun b => by
              match r with
              | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 => exact False.elim (by omega)
              | _ + 15 => rfl
            have rr := rGpr 15 (by omega)
            rw [h15 st.gpr] at hZ; rw [hZ] at rr
            rw [h15 s₁.gpr, h15 s₂.gpr]; exact rr
      · have hF : ((st.gpr.get 4 == .initSame 4 && decide (4 ∈ c.pubGprs)) &&
            (((st.gpr.get 3).le (.initOwn 3) || st.gpr.get 3 == .initSame 3) &&
             [3, 5, 12, 13, 14, 15].all (fun r => st.gpr.get r == .initOwn r || st.gpr.get r == .initSame r)) &&
            !st.ymmDirty &&
            st.ymm.allIdx (fun _ vo => vo != .secretVal && vo != .pubVal) &&
            c.wipedScratchGprs.all (fun r => st.gpr.get r == .zeroConst)) = false :=
          Bool.eq_false_iff.mpr hRetOk
        simp only [hF, Bool.false_eq_true, ↓reduceIte] at hTr; cases hTr
    case movRegReg is64 dst src =>
      rcases hValid with ⟨hd16, hs16⟩
      by_cases hInitLoop : (is64 && dst == 0 && src == 4 && st.gpr.get 4 == .frameSp &&
          st.gpr.get 1 == .constVal 25) = true
      · simp only [hInitLoop, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [Bool.and_eq_true, beq_iff_eq] at hInitLoop
        rcases hInitLoop with ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, hSpFsp⟩, hRcx25⟩
        have r4 := rGpr 4 (by omega); rw [hSpFsp] at r4; rcases r4 with ⟨h4_1, h4_2, h4eq⟩
        have r1 := rGpr 1 (by omega); rw [hRcx25] at r1; rcases r1 with ⟨h1_1, h1_2⟩
        simp only [stepX86, hIns, maskGprWidth, ↓reduceIte, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp, ?_⟩
        · intro r hr
          by_cases hr1 : r = 1
          · subst hr1
            rw [Bank16.get_set_eq, Bank16.get_set_ne _ _ (by omega) (by omega) (by omega),
                Bank16.get_set_ne _ _ (by omega) (by omega) (by omega)]
            simp [RelX86Gpr, h1_1, h1_2]
          · rw [Bank16.get_set_ne _ _ (by omega) hr (Ne.symm hr1)]
            exact RelX86Gpr_set (by omega) rGpr (by simp [RelX86Gpr, h4eq]) r hr
        · unfold RelX86Loop
          simp only [show (1 == 0) = false from rfl, beq_self_eq_true, ↓reduceIte]
          have hFspEq : x86FrameSpVal (s₁₀.gpr.get 4) = x86FrameSpVal (s₂₀.gpr.get 4) := by
            rw [← h4_1, ← h4_2, h4eq]
          refine ⟨hFspEq, 25, by omega, by omega, ?_, ?_, ?_, ?_⟩
          · rw [Bank16.get_set_ne _ _ (by omega) (by omega) (by omega)]; exact h1_1
          · rw [Bank16.get_set_ne _ _ (by omega) (by omega) (by omega)]; exact h1_2
          · simp only [Bank16.get_set_eq, Nat.sub_self, Nat.zero_mul]
            exact h4_1.trans (uint64_add_zero _).symm
          · simp only [Bank16.get_set_eq, Nat.sub_self, Nat.zero_mul]
            exact h4_2.trans (uint64_add_zero _).symm
      · simp only [hInitLoop, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [stepX86, hIns, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp,
          by simp [RelX86Loop]⟩
        apply RelX86Gpr_set hd16 rGpr
        cases is64
        · simp only [Bool.false_eq_true, ↓reduceIte]
          by_cases hPub : (st.gpr.get src).isPublic = true
          · simp only [hPub, ↓reduceIte, RelX86Gpr]
            rw [RelX86Gpr_public_eq (rGpr src hs16) hPub]
          · simp [hPub, RelX86Gpr]
        · simp only [↓reduceIte, maskGprWidth]
          exact rGpr src hs16
    case movImm is64 dst imm =>
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp,
        by simp [RelX86Loop]⟩
      apply RelX86Gpr_set hValid rGpr
      by_cases hz : (maskGprWidth is64 imm == 0) = true
      · simp only [hz, ↓reduceIte, RelX86Gpr]; exact ⟨beq_iff_eq.mp hz, beq_iff_eq.mp hz⟩
      · simp [hz, RelX86Gpr]
    case loadGpr wBytes is64 dst addr =>
      rcases hValid with ⟨⟨hw18, hd16⟩, hAddrReg⟩
      cases hAddrPub : x86AddrIsPublic st addr
      · simp [hAddrPub] at hTr
      · simp only [hAddrPub, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hEaEq := evalX86Addr_public_eq (d.offset + d.byteLen) hAddrPub hAddrReg rGpr
        simp only [stepX86, hIns, hEaEq, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp,
          by simp [RelX86Loop]⟩
        apply RelX86Gpr_set hd16 rGpr
        by_cases hIn : isInPubMemRegion c st addr wBytes = true
        · simp only [hIn, ↓reduceIte, RelX86Gpr]
          have hBytes := isInPubMemRegion_bytes_eq (d.offset + d.byteLen) hInit hRelFull hAddrReg hIn
          rcases hw18 with rfl | rfl
          · have hb0 := hBytes 0 (by omega)
            rw [hEaEq] at hb0
            have h0 : (evalX86Addr s₂ (d.offset + d.byteLen) addr + UInt64.ofNat 0) =
                evalX86Addr s₂ (d.offset + d.byteLen) addr := uint64_add_zero _
            rw [h0] at hb0
            simp [hb0]
          · have hR64 : readMem64 s₁.mem (evalX86Addr s₂ (d.offset + d.byteLen) addr) =
                readMem64 s₂.mem (evalX86Addr s₂ (d.offset + d.byteLen) addr) := by
              apply readMem64_congr; intro j hj
              simpa only [← hEaEq] using hBytes j hj
            simp [show (8 == 1) = false from rfl, hR64]
        · simp [hIn, RelX86Gpr]
    case storeGpr wBytes src addr =>
      rcases hValid with ⟨⟨hw18, hs16⟩, hAddrReg⟩
      cases hAddrPub : x86AddrIsPublic st addr
      · simp [hAddrPub] at hTr
      · simp only [hAddrPub, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hEaEq := evalX86Addr_public_eq (d.offset + d.byteLen) hAddrPub hAddrReg rGpr
        simp only [stepX86, hIns, hEaEq, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, rYmm, rCf, rOf, rZf, rDirty,
          (fun h => nomatch h), ?_, by simp [RelX86Loop]⟩
        intro hRbpOk
        cases hRbpB : st.rbpSaved
        · simp [hRbpB] at hRbpOk
        · simp only [hRbpB, ↓reduceIte] at hRbpOk
          rcases rRbp hRbpB with ⟨hSp0Eq, hM1, hM2⟩
          rcases storePreservesSavedRbp_disjoint (d.offset + d.byteLen) hInit hRelFull hAddrReg hRbpOk
            with ⟨hDisj1, hDisj2⟩
          refine ⟨hSp0Eq, ?_, ?_⟩
          · rw [hEaEq] at hDisj1
            rcases hw18 with rfl | rfl
            · simp only [beq_self_eq_true, ↓reduceIte]
              rw [readMem64_congr (fun k hk =>
                writeMem8_ne _ _ (by simpa [uint64_add_zero] using hDisj1 0 k (by omega) hk))]
              exact hM1
            · simp only [show (8 == 1) = false from rfl, Bool.false_eq_true, ↓reduceIte]
              rw [readMem64_congr (fun k hk => writeMem64_ne _ _ (fun j hj => hDisj1 j k hj hk))]
              exact hM1
          · rcases hw18 with rfl | rfl
            · simp only [beq_self_eq_true, ↓reduceIte]
              rw [readMem64_congr (fun k hk =>
                writeMem8_ne _ _ (by simpa [uint64_add_zero] using hDisj2 0 k (by omega) hk))]
              exact hM2
            · simp only [show (8 == 1) = false from rfl, Bool.false_eq_true, ↓reduceIte]
              rw [readMem64_congr (fun k hk => writeMem64_ne _ _ (fun j hj => hDisj2 j k hj hk))]
              exact hM2
    case aluRegReg op is64 dst src =>
      rcases hValid with ⟨hd16, hs16⟩
      by_cases hXorSelf : (op == .xorOp && dst == src) = true
      · simp only [hXorSelf, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [Bool.and_eq_true, beq_iff_eq] at hXorSelf
        rcases hXorSelf with ⟨rfl, rfl⟩
        simp only [stepX86, hIns, evalX86Alu_xor_self, evalX86AluOf, true_and]
        exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2,
          RelX86Gpr_set hd16 rGpr ⟨rfl, rfl⟩,
          rYmm, fun _ => rfl, fun _ => rfl, fun _ => rfl, rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
      · simp only [hXorSelf, Bool.false_eq_true, ↓reduceIte] at hTr
        by_cases hSbbSelf : (op == .sbb && dst == src) = true
        · simp only [hSbbSelf, ↓reduceIte] at hTr
          injection hTr with hS; subst hS
          simp only [Bool.and_eq_true, beq_iff_eq] at hSbbSelf
          rcases hSbbSelf with ⟨rfl, rfl⟩
          simp only [stepX86, hIns, evalX86AluOf_sbb_self, true_and]
          refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm, ?_, (fun _ => rfl), ?_, rDirty, rMem, rRbp,
            by simp [RelX86Loop]⟩
          · apply RelX86Gpr_set hd16 rGpr
            by_cases hCfB : st.cfPub = true
            · simp only [hCfB, ↓reduceIte, RelX86Gpr]
              rw [rCf hCfB, evalX86Alu_sbb_self_congr]
            · simp [hCfB, RelX86Gpr]
          · intro hCfB
            rw [rCf hCfB, evalX86Alu_sbb_self_congr]
          · intro hCfB
            rw [rCf hCfB, evalX86Alu_sbb_self_congr]
        · simp only [hSbbSelf, Bool.false_eq_true, ↓reduceIte] at hTr
          injection hTr with hS; subst hS
          simp only [stepX86, hIns, true_and]
          have hAluEq : ((st.gpr.get dst).isPublic && (st.gpr.get src).isPublic &&
              (if op == .adc || op == .sbb then st.cfPub else true)) = true →
              evalX86Alu op is64 (s₁.gpr.get dst) (s₁.gpr.get src) s₁.cf =
              evalX86Alu op is64 (s₂.gpr.get dst) (s₂.gpr.get src) s₂.cf := by
            intro hBoth
            simp only [Bool.and_eq_true] at hBoth
            exact evalX86Alu_congr op is64
              (RelX86Gpr_public_eq (rGpr dst hd16) hBoth.1.1)
              (RelX86Gpr_public_eq (rGpr src hs16) hBoth.1.2)
              (fun hNeed => rCf (by
                by_cases hc : (op == .adc || op == .sbb) = true
                · simpa [hc] using hBoth.2
                · simp [hc] at hNeed))
          refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm,
            (fun hb => congrArg (fun t => t.2.1) (hAluEq hb)),
            (fun hOfB => by
              cases op <;> simp [evalX86AluOf] at hOfB ⊢),
            (fun hb => congrArg (fun t => t.2.2) (hAluEq hb)),
            rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
          apply RelX86Gpr_set hd16 rGpr
          by_cases hb : ((st.gpr.get dst).isPublic && (st.gpr.get src).isPublic &&
              (if op == .adc || op == .sbb then st.cfPub else true)) = true
          · simp only [hb, ↓reduceIte, RelX86Gpr]
            exact congrArg Prod.fst (hAluEq hb)
          · simp only [hb, Bool.false_eq_true, ↓reduceIte, RelX86Gpr]
    case aluLoad64 op dst addr =>
      rcases hValid with ⟨hd16, hAddrReg⟩
      cases hAddrPub : x86AddrIsPublic st addr
      · simp [hAddrPub] at hTr
      · simp only [hAddrPub, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hEaEq := evalX86Addr_public_eq (d.offset + d.byteLen) hAddrPub hAddrReg rGpr
        simp only [stepX86, hIns, hEaEq, true_and]
        have hAluEq : ((st.gpr.get dst).isPublic && isInPubMemRegion c st addr 8 &&
            (if op == .adc || op == .sbb then st.cfPub else true)) = true →
            evalX86Alu op true (s₁.gpr.get dst) (readMem64 s₁.mem (evalX86Addr s₂ (d.offset + d.byteLen) addr)) s₁.cf =
            evalX86Alu op true (s₂.gpr.get dst) (readMem64 s₂.mem (evalX86Addr s₂ (d.offset + d.byteLen) addr)) s₂.cf := by
          intro hBoth
          simp only [Bool.and_eq_true] at hBoth
          have hBytes := isInPubMemRegion_bytes_eq (d.offset + d.byteLen) hInit hRelFull hAddrReg hBoth.1.2
          have hMemEq : readMem64 s₁.mem (evalX86Addr s₂ (d.offset + d.byteLen) addr) =
              readMem64 s₂.mem (evalX86Addr s₂ (d.offset + d.byteLen) addr) :=
            readMem64_congr (fun j hj => by simpa only [← hEaEq] using hBytes j hj)
          exact evalX86Alu_congr op true
            (RelX86Gpr_public_eq (rGpr dst hd16) hBoth.1.1) hMemEq
            (fun hNeed => rCf (by
              by_cases hc : (op == .adc || op == .sbb) = true
              · simpa [hc] using hBoth.2
              · simp [hc] at hNeed))
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm,
          (fun hb => congrArg (fun t => t.2.1) (hAluEq hb)),
          (fun hOfB => by
            cases op <;> simp [evalX86AluOf] at hOfB ⊢),
          (fun hb => congrArg (fun t => t.2.2) (hAluEq hb)),
          rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
        apply RelX86Gpr_set hd16 rGpr
        by_cases hb : ((st.gpr.get dst).isPublic && isInPubMemRegion c st addr 8 &&
            (if op == .adc || op == .sbb then st.cfPub else true)) = true
        · simp only [hb, ↓reduceIte, RelX86Gpr]
          exact congrArg Prod.fst (hAluEq hb)
        · simp only [hb, Bool.false_eq_true, ↓reduceIte, RelX86Gpr]
    case aluImm op is64 dst imm =>
      by_cases hc1 : (is64 && op == .andOp && dst == 4 && imm == 0xFFFFFFFFFFFFFFE0 && st.gpr.get 4 == .spMinus8) = true
      · simp only [hc1, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [Bool.and_eq_true, beq_iff_eq] at hc1
        rcases hc1 with ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hSp4⟩
        have r4 := rGpr 4 (by omega); rw [hSp4] at r4; rcases r4 with ⟨h4_1, h4_2, h4eq⟩
        simp only [stepX86, hIns, evalX86Alu, evalX86AluOf, maskGprWidth, ↓reduceIte, true_and]
        exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2,
          RelX86Gpr_set (by omega) rGpr ⟨congrArg (· &&& 0xFFFFFFFFFFFFFFE0) h4_1,
            congrArg (· &&& 0xFFFFFFFFFFFFFFE0) h4_2, congrArg (· &&& 0xFFFFFFFFFFFFFFE0) h4eq⟩,
          rYmm, (fun _ => rfl), (fun _ => rfl), (fun _ => by rw [h4eq]), rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
      · simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hTr
        by_cases hc2 : (is64 && op == .sub && dst == 4 && imm == 0x340 && st.gpr.get 4 == .spAligned32) = true
        · simp only [hc2, ↓reduceIte] at hTr
          injection hTr with hS; subst hS
          simp only [Bool.and_eq_true, beq_iff_eq] at hc2
          rcases hc2 with ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hSp4⟩
          have r4 := rGpr 4 (by omega); rw [hSp4] at r4; rcases r4 with ⟨h4_1, h4_2, h4eq⟩
          simp only [stepX86, hIns, evalX86Alu, maskGprWidth, ↓reduceIte, uint64_evalSub_eq, true_and]
          exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2,
            RelX86Gpr_set (by omega) rGpr ⟨by rw [x86FrameSpVal, ← h4_1], by rw [x86FrameSpVal, ← h4_2],
              congrArg (· - 0x340) h4eq⟩,
            rYmm, (fun _ => by rw [h4eq]), (fun h => nomatch h), (fun _ => by rw [h4eq]),
            rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
        · simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hTr
          by_cases hc3 : (is64 && op == .add && dst == 0 && imm == 0x20 && st.stackZeroLoop == 1) = true
          · simp only [hc3, ↓reduceIte] at hTr
            injection hTr with hS; subst hS
            simp only [Bool.and_eq_true, beq_iff_eq] at hc3
            rcases hc3 with ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hLoop1⟩
            unfold RelX86Loop at rLoop
            simp only [hLoop1, show (1 == 0) = false from rfl, beq_self_eq_true, ↓reduceIte] at rLoop
            rcases rLoop with ⟨hFspEq, k, hk1, hk25, hk1_1, hk1_2, ha0_1, ha0_2⟩
            have h0eq : s₁.gpr.get 0 = s₂.gpr.get 0 := by rw [ha0_1, ha0_2, hFspEq]
            simp only [stepX86, hIns, evalX86Alu, maskGprWidth, ↓reduceIte, uint64_evalAdd_eq, true_and]
            refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2,
              RelX86Gpr_set (by omega) rGpr (congrArg (· + 0x20) h0eq),
              rYmm, (fun _ => by rw [h0eq]), (fun h => nomatch h), (fun _ => by rw [h0eq]), rDirty, rMem, rRbp, ?_⟩
            unfold RelX86Loop
            simp only [show (2 == 0) = false from rfl, show (2 == 1) = false from rfl, beq_self_eq_true, ↓reduceIte]
            have hStep32 (base : UInt64) :
                (base + UInt64.ofNat ((25 - k) * 32)) + 0x20 = base + UInt64.ofNat ((26 - k) * 32) := by
              apply uint64_eq_of_toNat_eq
              have h20 : (0x20 : UInt64).toNat = 32 := rfl
              have hMul : (25 - k) * 32 + 32 = (26 - k) * 32 := by omega
              simp only [UInt64.toNat_add, UInt64.toNat_ofNat', h20, Nat.add_mod_mod, Nat.mod_add_mod,
                Nat.add_assoc, hMul]
            refine ⟨hFspEq, k, hk1, hk25, ?_, ?_, ?_, ?_⟩
            · rw [Bank16.get_set_ne _ _ (by omega) (by omega) (by omega)]; exact hk1_1
            · rw [Bank16.get_set_ne _ _ (by omega) (by omega) (by omega)]; exact hk1_2
            · simp only [Bank16.get_set_eq, ha0_1, hStep32]
            · simp only [Bank16.get_set_eq, ha0_2, hStep32]
          · simp only [hc3, Bool.false_eq_true, ↓reduceIte] at hTr
            injection hTr with hS; subst hS
            simp only [stepX86, hIns, true_and]
            have hAluEq : ((st.gpr.get dst).isPublic &&
                (if op == .adc || op == .sbb then st.cfPub else true)) = true →
                evalX86Alu op is64 (s₁.gpr.get dst) imm s₁.cf =
                evalX86Alu op is64 (s₂.gpr.get dst) imm s₂.cf := by
              intro hBoth
              simp only [Bool.and_eq_true] at hBoth
              exact evalX86Alu_congr op is64
                (RelX86Gpr_public_eq (rGpr dst hValid) hBoth.1) rfl
                (fun hNeed => rCf (by
                  by_cases hc : (op == .adc || op == .sbb) = true
                  · simpa [hc] using hBoth.2
                  · simp [hc] at hNeed))
            refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm,
              (fun hb => congrArg (fun t => t.2.1) (hAluEq hb)),
              (fun hOfB => by
                cases op <;> simp [evalX86AluOf] at hOfB ⊢),
              (fun hb => congrArg (fun t => t.2.2) (hAluEq hb)),
              rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
            apply RelX86Gpr_set hValid rGpr
            by_cases hb : ((st.gpr.get dst).isPublic &&
                (if op == .adc || op == .sbb then st.cfPub else true)) = true
            · simp only [hb, ↓reduceIte, RelX86Gpr]
              exact congrArg Prod.fst (hAluEq hb)
            · simp only [hb, Bool.false_eq_true, ↓reduceIte, RelX86Gpr]
    case incDec isInc is64 dst =>
      by_cases hcLoop : (!isInc && !is64 && dst == 1 && st.stackZeroLoop == 2) = true
      · simp only [hcLoop, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hcLoop
        rcases hcLoop with ⟨⟨⟨rfl, rfl⟩, rfl⟩, hLoop2⟩
        unfold RelX86Loop at rLoop
        simp only [hLoop2, show (2 == 0) = false from rfl, show (2 == 1) = false from rfl,
          beq_self_eq_true, ↓reduceIte] at rLoop
        rcases rLoop with ⟨hFspEq, k, hk1, hk25, hk1_1, hk1_2, ha0_1, ha0_2⟩
        rcases loop_dec_ecx_step hk1 hk25 with ⟨hDecVal, hDecZf, hDecOf⟩
        simp only [stepX86, hIns, Bool.false_eq_true, ↓reduceIte, hk1_1, hk1_2, hDecVal, hDecOf, true_and]
        have hZfEq : (UInt64.ofNat (k - 1) == (0 : UInt64)) = (k - 1 == 0) := by
          simpa only [hDecVal] using hDecZf
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2,
          RelX86Gpr_set (by omega) rGpr rfl,
          rYmm, rCf, fun _ => rfl, fun _ => rfl, rDirty, rMem, rRbp, ?_⟩
        unfold RelX86Loop
        simp only [show (3 == 0) = false from rfl, show (3 == 1) = false from rfl,
          show (3 == 2) = false from rfl, beq_self_eq_true, ↓reduceIte]
        have hSubEq : 26 - k = 25 - (k - 1) := by omega
        refine ⟨hFspEq, k - 1, by omega,
          by simp [Bank16.get_set_eq], by simp [Bank16.get_set_eq], ?_, ?_, hZfEq, hZfEq⟩
        · rw [Bank16.get_set_ne _ _ (by omega) (by omega) (by omega), ha0_1, hSubEq]
        · rw [Bank16.get_set_ne _ _ (by omega) (by omega) (by omega), ha0_2, hSubEq]
      · simp only [hcLoop, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [stepX86, hIns, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm, rCf,
          (fun hp => by rw [RelX86Gpr_public_eq (rGpr dst hValid) hp]),
          (fun hp => by rw [RelX86Gpr_public_eq (rGpr dst hValid) hp]),
          rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
        apply RelX86Gpr_set hValid rGpr
        by_cases hp : (st.gpr.get dst).isPublic = true
        · simp only [hp, ↓reduceIte, RelX86Gpr]; rw [RelX86Gpr_public_eq (rGpr dst hValid) hp]
        · simp [hp, RelX86Gpr]
    case negReg is64 dst =>
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm,
        (fun hp => by rw [RelX86Gpr_public_eq (rGpr dst hValid) hp]),
        (fun hp => by rw [RelX86Gpr_public_eq (rGpr dst hValid) hp]),
        (fun hp => by rw [RelX86Gpr_public_eq (rGpr dst hValid) hp]),
        rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
      apply RelX86Gpr_set hValid rGpr
      by_cases hp : (st.gpr.get dst).isPublic = true
      · simp only [hp, ↓reduceIte, RelX86Gpr]; rw [RelX86Gpr_public_eq (rGpr dst hValid) hp]
      · simp [hp, RelX86Gpr]
    case mulOneOp isSigned is64 src =>
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      have hBothEq : ((st.gpr.get 0).isPublic && (st.gpr.get src).isPublic) = true →
          s₁.gpr.get 0 = s₂.gpr.get 0 ∧ s₁.gpr.get src = s₂.gpr.get src := by
        intro hp; simp only [Bool.and_eq_true] at hp
        exact ⟨RelX86Gpr_public_eq (rGpr 0 (by omega)) hp.1, RelX86Gpr_public_eq (rGpr src hValid) hp.2⟩
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm,
        (fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h),
        rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
      apply RelX86Gpr_set (by omega)
      · apply RelX86Gpr_set (by omega) rGpr
        by_cases hp : ((st.gpr.get 0).isPublic && (st.gpr.get src).isPublic) = true
        · simp only [hp, ↓reduceIte, RelX86Gpr]; rcases hBothEq hp with ⟨e0, es⟩; simp [e0, es]
        · simp [hp, RelX86Gpr]
      · by_cases hp : ((st.gpr.get 0).isPublic && (st.gpr.get src).isPublic) = true
        · simp only [hp, ↓reduceIte, RelX86Gpr]; rcases hBothEq hp with ⟨e0, es⟩; simp [e0, es]
        · simp [hp, RelX86Gpr]
    case shiftImm sk is64 dst cnt =>
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm,
        (fun h => nomatch h), (fun h => nomatch h),
        (fun hp => by
          rw [evalX86Shift_zf, evalX86Shift_zf]
          by_cases hPres : x86ShiftPreservesZf sk is64 cnt = true
          · simp only [hPres, ↓reduceIte] at hp ⊢
            exact rZf hp
          · simp only [hPres, Bool.false_eq_true, ↓reduceIte] at hp ⊢
            rw [evalX86Shift_fst_congr sk is64 cnt _ _ _ _ _ _
              (RelX86Gpr_public_eq (rGpr dst hValid) hp)]),
        rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
      apply RelX86Gpr_set hValid rGpr
      by_cases hp : (st.gpr.get dst).isPublic = true
      · simp only [hp, ↓reduceIte, RelX86Gpr]
        exact evalX86Shift_fst_congr sk is64 cnt _ _ _ _ _ _
          (RelX86Gpr_public_eq (rGpr dst hValid) hp)
      · simp [hp, RelX86Gpr]
    case cmovcc cc is64 dst src =>
      rcases hValid with ⟨hd16, hs16⟩
      have hGate : ¬ ((!x86CondSupported cc || !c.doitEnabled) = true) := by
        intro hG; simp [hG] at hTr
      simp only [hGate] at hTr
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp,
        by simp [RelX86Loop]⟩
      apply RelX86Gpr_set hd16 rGpr
      by_cases hp : (x86CondIsPublic cc st && (st.gpr.get dst).isPublic && (st.gpr.get src).isPublic) = true
      · simp only [hp, ↓reduceIte, RelX86Gpr]
        simp only [Bool.and_eq_true] at hp
        rw [evalX86Cond_public_eq hp.1.1 rCf rZf,
            RelX86Gpr_public_eq (rGpr src hs16) hp.2,
            RelX86Gpr_public_eq (rGpr dst hd16) hp.1.2]
      · simp [hp, RelX86Gpr]
    case testRegReg is64 r1 r2 =>
      rcases hValid with ⟨hr1, hr2⟩
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, rYmm,
        (fun _ => rfl), (fun _ => rfl),
        (fun hp => by
          simp only [Bool.and_eq_true] at hp
          rw [RelX86Gpr_public_eq (rGpr r1 hr1) hp.1, RelX86Gpr_public_eq (rGpr r2 hr2) hp.2]),
        rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
    case cmpRegReg is64 dst src =>
      rcases hValid with ⟨hd16, hs16⟩
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      have hBoth : ((st.gpr.get dst).isPublic && (st.gpr.get src).isPublic) = true →
          s₁.gpr.get dst = s₂.gpr.get dst ∧ s₁.gpr.get src = s₂.gpr.get src := by
        intro hp; simp only [Bool.and_eq_true] at hp
        exact ⟨RelX86Gpr_public_eq (rGpr dst hd16) hp.1, RelX86Gpr_public_eq (rGpr src hs16) hp.2⟩
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, rYmm,
        (fun hp => by rcases hBoth hp with ⟨e1, e2⟩; rw [e1, e2]),
        (fun hp => by rcases hBoth hp with ⟨e1, e2⟩; rw [e1, e2]),
        (fun hp => by rcases hBoth hp with ⟨e1, e2⟩; rw [e1, e2]),
        rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
    case cmpImm is64 dst imm =>
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, rYmm,
        (fun hp => by rw [RelX86Gpr_public_eq (rGpr dst hValid) hp]),
        (fun hp => by rw [RelX86Gpr_public_eq (rGpr dst hValid) hp]),
        (fun hp => by rw [RelX86Gpr_public_eq (rGpr dst hValid) hp]),
        rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
    case lea is64 dst addr =>
      rcases hValid with ⟨hd16, hAddrReg⟩
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp,
        by simp [RelX86Loop]⟩
      apply RelX86Gpr_set hd16 rGpr
      by_cases hp : x86AddrIsPublic st addr = true
      · simp only [hp, ↓reduceIte, RelX86Gpr]
        rw [evalX86Addr_public_eq (d.offset + d.byteLen) hp hAddrReg rGpr]
      · simp [hp, RelX86Gpr]
    case storeImm8 addr imm =>
      cases hAddrPub : x86AddrIsPublic st addr
      · simp [hAddrPub] at hTr
      · simp only [hAddrPub, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hEaEq := evalX86Addr_public_eq (d.offset + d.byteLen) hAddrPub hValid rGpr
        simp only [stepX86, hIns, hEaEq, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, rYmm, rCf, rOf, rZf, rDirty,
          (fun h => nomatch h), ?_, by simp [RelX86Loop]⟩
        intro hRbpOk
        cases hRbpB : st.rbpSaved
        · simp [hRbpB] at hRbpOk
        · simp only [hRbpB, ↓reduceIte] at hRbpOk
          rcases rRbp hRbpB with ⟨hSp0Eq, hM1, hM2⟩
          rcases storePreservesSavedRbp_disjoint (d.offset + d.byteLen) hInit hRelFull hValid hRbpOk
            with ⟨hDisj1, hDisj2⟩
          refine ⟨hSp0Eq, ?_, ?_⟩
          · rw [hEaEq] at hDisj1
            rw [readMem64_congr (fun k hk =>
              writeMem8_ne _ _ (by simpa [uint64_add_zero] using hDisj1 0 k (by omega) hk))]
            exact hM1
          · rw [readMem64_congr (fun k hk =>
              writeMem8_ne _ _ (by simpa [uint64_add_zero] using hDisj2 0 k (by omega) hk))]
            exact hM2
    case notReg is64 dst =>
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp,
        by simp [RelX86Loop]⟩
      apply RelX86Gpr_set hValid rGpr
      by_cases hp : (st.gpr.get dst).isPublic = true
      · simp only [hp, ↓reduceIte, RelX86Gpr]; rw [RelX86Gpr_public_eq (rGpr dst hValid) hp]
      · simp [hp, RelX86Gpr]
    case setcc cc dst =>
      cases hSup : x86CondSupported cc
      · simp [hSup] at hTr
      · simp only [hSup, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [stepX86, hIns, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp,
          by simp [RelX86Loop]⟩
        apply RelX86Gpr_set hValid rGpr
        by_cases hp : (x86CondIsPublic cc st && (st.gpr.get dst).isPublic) = true
        · simp only [hp, ↓reduceIte, RelX86Gpr]
          simp only [Bool.and_eq_true] at hp
          rw [evalX86Cond_public_eq hp.1 rCf rZf, RelX86Gpr_public_eq (rGpr dst hValid) hp.2]
        · simp [hp, RelX86Gpr]
    case bswap is64 dst =>
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp,
        by simp [RelX86Loop]⟩
      apply RelX86Gpr_set hValid rGpr
      by_cases hp : (st.gpr.get dst).isPublic = true
      · simp only [hp, ↓reduceIte, RelX86Gpr]; rw [RelX86Gpr_public_eq (rGpr dst hValid) hp]
      · simp [hp, RelX86Gpr]
    case sseMovdquLoad dst addr =>
      rcases hValid with ⟨hd16, hAddrReg⟩
      cases hAddrPub : x86AddrIsPublic st addr
      · simp [hAddrPub] at hTr
      · simp only [hAddrPub, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hEaEq := evalX86Addr_public_eq (d.offset + d.byteLen) hAddrPub hAddrReg rGpr
        simp only [stepX86, hIns, hEaEq, true_and]
        exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr,
          RelX86Vec_set hd16 rYmm trivial, rCf, rOf, rZf, rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
    case ssePcmpeqb dst src =>
      rcases hValid with ⟨hd16, _⟩
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr,
        RelX86Vec_set hd16 rYmm trivial, rCf, rOf, rZf, rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
    case ssePand dst src =>
      rcases hValid with ⟨hd16, _⟩
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr,
        RelX86Vec_set hd16 rYmm trivial, rCf, rOf, rZf, rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
    case ssePmovmskb dst src =>
      rcases hValid with ⟨hd16, hs16⟩
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp,
        by simp [RelX86Loop]⟩
      apply RelX86Gpr_set hd16 rGpr
      by_cases hp : (st.ymm.get src).isPublic = true
      · simp only [hp, ↓reduceIte, RelX86Gpr]; rw [RelX86Vec_public_eq (rYmm src hs16) hp]
      · simp [hp, RelX86Gpr]
    case mulx hiDst loDst src =>
      rcases hValid with ⟨⟨hhi16, hlo16⟩, hs16⟩
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      have hBothEq : ((st.gpr.get 2).isPublic && (st.gpr.get src).isPublic) = true →
          s₁.gpr.get 2 = s₂.gpr.get 2 ∧ s₁.gpr.get src = s₂.gpr.get src := by
        intro hp; simp only [Bool.and_eq_true] at hp
        exact ⟨RelX86Gpr_public_eq (rGpr 2 (by omega)) hp.1, RelX86Gpr_public_eq (rGpr src hs16) hp.2⟩
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp,
        by simp [RelX86Loop]⟩
      apply RelX86Gpr_set hhi16
      · apply RelX86Gpr_set hlo16 rGpr
        by_cases hp : ((st.gpr.get 2).isPublic && (st.gpr.get src).isPublic) = true
        · simp only [hp, ↓reduceIte, RelX86Gpr]; rcases hBothEq hp with ⟨e2, es⟩; simp [e2, es]
        · simp [hp, RelX86Gpr]
      · by_cases hp : ((st.gpr.get 2).isPublic && (st.gpr.get src).isPublic) = true
        · simp only [hp, ↓reduceIte, RelX86Gpr]; rcases hBothEq hp with ⟨e2, es⟩; simp [e2, es]
        · simp [hp, RelX86Gpr]
    case adcx dst src =>
      rcases hValid with ⟨hd16, hs16⟩
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      have hEq : ((st.gpr.get dst).isPublic && (st.gpr.get src).isPublic && st.cfPub) = true →
          s₁.gpr.get dst = s₂.gpr.get dst ∧ s₁.gpr.get src = s₂.gpr.get src ∧ s₁.cf = s₂.cf := by
        intro hp; simp only [Bool.and_eq_true] at hp
        exact ⟨RelX86Gpr_public_eq (rGpr dst hd16) hp.1.1,
               RelX86Gpr_public_eq (rGpr src hs16) hp.1.2, rCf hp.2⟩
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm,
        (fun hp => by rcases hEq hp with ⟨ed, es, ec⟩; simp [ed, es, ec]),
        rOf, rZf, rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
      apply RelX86Gpr_set hd16 rGpr
      by_cases hp : ((st.gpr.get dst).isPublic && (st.gpr.get src).isPublic && st.cfPub) = true
      · simp only [hp, ↓reduceIte, RelX86Gpr]; rcases hEq hp with ⟨ed, es, ec⟩; simp [ed, es, ec]
      · simp [hp, RelX86Gpr]
    case adox dst src =>
      rcases hValid with ⟨hd16, hs16⟩
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      have hEq : ((st.gpr.get dst).isPublic && (st.gpr.get src).isPublic && st.ofPub) = true →
          s₁.gpr.get dst = s₂.gpr.get dst ∧ s₁.gpr.get src = s₂.gpr.get src ∧ s₁.ofFlag = s₂.ofFlag := by
        intro hp; simp only [Bool.and_eq_true] at hp
        exact ⟨RelX86Gpr_public_eq (rGpr dst hd16) hp.1.1,
               RelX86Gpr_public_eq (rGpr src hs16) hp.1.2, rOf hp.2⟩
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm, rCf,
        (fun hp => by rcases hEq hp with ⟨ed, es, eo⟩; simp [ed, es, eo]),
        rZf, rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
      apply RelX86Gpr_set hd16 rGpr
      by_cases hp : ((st.gpr.get dst).isPublic && (st.gpr.get src).isPublic && st.ofPub) = true
      · simp only [hp, ↓reduceIte, RelX86Gpr]; rcases hEq hp with ⟨ed, es, eo⟩; simp [ed, es, eo]
      · simp [hp, RelX86Gpr]
    case jcc cc targetPc =>
      by_cases hBad : (!x86CondIsPublic cc st || decide (targetPc < 0) || decide (targetPc.toNat ≥ 4096)) = true
      · simp [hBad] at hTr
      · simp only [hBad, Bool.false_eq_true, ↓reduceIte] at hTr
        simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, not_or, Bool.not_eq_false] at hBad
        rcases hBad with ⟨⟨hCondPub, hNotNeg⟩, _⟩
        have hGe0 : targetPc ≥ 0 := by omega
        have hCondEq := evalX86Cond_public_eq hCondPub rCf rZf
        by_cases hLoop3 : (st.stackZeroLoop == 3 && cc == 5) = true
        · simp only [hLoop3, ↓reduceIte] at hTr
          injection hTr with hS; subst hS
          simp only [Bool.and_eq_true, beq_iff_eq] at hLoop3
          rcases hLoop3 with ⟨hSt3, rfl⟩
          unfold RelX86Loop at rLoop
          simp only [hSt3, show (3 == 0) = false from rfl, show (3 == 1) = false from rfl,
            show (3 == 2) = false from rfl, beq_self_eq_true, ↓reduceIte] at rLoop
          rcases rLoop with ⟨hFspEq, k', hk'24, hk1, hk2, ha1, ha2, hzf1, hzf2⟩
          simp only [stepX86, hIns, decide_eq_true hGe0, Bool.and_true, true_and]
          by_cases hTaken : evalX86Cond 5 s₁ = true
          · have hTaken2 : evalX86Cond 5 s₂ = true := hCondEq ▸ hTaken
            simp only [hTaken, hTaken2, ↓reduceIte]
            have hk'Pos : 1 ≤ k' := by
              unfold evalX86Cond at hTaken
              simp only [show (5 == 2) = false from rfl, show (5 == 3) = false from rfl,
                show (5 == 4) = false from rfl, Bool.false_eq_true, beq_self_eq_true, ↓reduceIte, hzf1,
                Bool.not_eq_true', beq_eq_false_iff_ne] at hTaken
              omega
            refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp, ?_⟩
            unfold RelX86Loop
            simp only [show (1 == 0) = false from rfl, beq_self_eq_true, ↓reduceIte]
            exact ⟨hFspEq, k', hk'Pos, by omega, hk1, hk2, ha1, ha2⟩
          · have hTakenF1 : evalX86Cond 5 s₁ = false := Bool.eq_false_iff.mpr hTaken
            have hTakenF2 : evalX86Cond 5 s₂ = false := hCondEq ▸ hTakenF1
            simp only [hTakenF1, hTakenF2, Bool.false_eq_true, ↓reduceIte]
            exact Or.inr ⟨_, List.Mem.tail _ (List.Mem.head _), rfl, hH1, hH2, rGpr, rYmm, rCf, rOf, rZf,
              rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
        · simp only [hLoop3, Bool.false_eq_true, ↓reduceIte] at hTr
          injection hTr with hS; subst hS
          simp only [stepX86, hIns, decide_eq_true hGe0, Bool.and_true, true_and]
          by_cases hTaken : evalX86Cond cc s₁ = true
          · have hTaken2 : evalX86Cond cc s₂ = true := hCondEq ▸ hTaken
            simp only [hTaken, hTaken2, ↓reduceIte]
            exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp,
              by simp [RelX86Loop]⟩
          · have hTakenF1 : evalX86Cond cc s₁ = false := Bool.eq_false_iff.mpr hTaken
            have hTakenF2 : evalX86Cond cc s₂ = false := hCondEq ▸ hTakenF1
            simp only [hTakenF1, hTakenF2, Bool.false_eq_true, ↓reduceIte]
            exact Or.inr ⟨_, List.Mem.tail _ (List.Mem.head _), rfl, hH1, hH2, rGpr, rYmm, rCf, rOf, rZf,
              rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
    case jmpRel targetPc =>
      by_cases hBad : (decide (targetPc < 0) || decide (targetPc.toNat ≥ 4096)) = true
      · simp [hBad] at hTr
      · simp only [hBad, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hBad
        have hGe0 : targetPc ≥ 0 := by omega
        simp only [stepX86, hIns, hGe0, ↓reduceIte, true_and]
        exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp,
          by simp [RelX86Loop]⟩
    case indirectBr _ => cases hTr
    case divRem _ => cases hTr
    case varShiftCl _ _ => cases hTr
    case vpgather _ _ => cases hTr
    case vzeroall =>
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, ?_, rCf, rOf, rZf,
        fun _ => ⟨rfl, rfl⟩, rMem, rRbp, by simp [RelX86Loop]⟩
      intro i hi
      rw [Bank16.get_ofFn _ hi, Bank16.get_ofFn _ hi]
      exact ⟨rfl, rfl⟩
    case vzeroupper =>
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, ?_, rCf, rOf, rZf,
        fun _ => ⟨rfl, rfl⟩, rMem, rRbp, by simp [RelX86Loop]⟩
      intro i hi
      rw [Bank16.get_ofFn _ hi, Bank16.get_ofFn _ hi, Bank16.get_ofFn _ hi]
      have rv := rYmm i hi
      cases hVo : st.ymm.get i <;> rw [hVo] at rv
      · rcases rv with ⟨hr, (⟨e1, e2⟩ | ⟨e1, e2⟩)⟩
        · exact ⟨hr, Or.inr ⟨by rw [e1], by rw [e2]⟩⟩
        · exact ⟨hr, Or.inr ⟨by rw [e1], by rw [e2]⟩⟩
      · rcases rv with ⟨e1, e2⟩
        simp [e1, e2, Vec256.zero, RelX86Vec]
      · simp only [RelX86Vec] at rv ⊢; rw [rv]
      · trivial
    case vload is256 dst addr =>
      rcases hValid with ⟨hd16, hAddrReg⟩
      cases hAddrPub : x86AddrIsPublic st addr
      · simp [hAddrPub] at hTr
      · simp only [hAddrPub, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hEaEq := evalX86Addr_public_eq (d.offset + d.byteLen) hAddrPub hAddrReg rGpr
        simp only [stepX86, hIns, hEaEq, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, ?_, rCf, rOf, rZf, ?_, rMem, rRbp,
          by simp [RelX86Loop]⟩
        · apply RelX86Vec_set hd16 rYmm
          by_cases hIn : isInPubMemRegion c st addr (if is256 then 32 else 16) = true
          · simp only [hIn, ↓reduceIte, RelX86Vec]
            have hBytes := isInPubMemRegion_bytes_eq (d.offset + d.byteLen) hInit hRelFull hAddrReg hIn
            cases is256
            · simp only [Bool.false_eq_true, ↓reduceIte] at hBytes ⊢
              rw [readMem128_congr (fun j hj => by simpa only [← hEaEq] using hBytes j hj)]
            · simp only [↓reduceIte] at hBytes ⊢
              exact readMem256_congr (fun j hj => by simpa only [← hEaEq] using hBytes j hj)
          · simp [hIn, RelX86Vec]
        · intro hClean
          simp only [Bool.or_eq_false_iff] at hClean
          rcases rDirty hClean.1 with ⟨d1, d2⟩
          simp [d1, d2, hClean.2]
    case vstore is256 src addr =>
      rcases hValid with ⟨hs16, hAddrReg⟩
      cases hAddrPub : x86AddrIsPublic st addr
      · simp [hAddrPub] at hTr
      · simp only [hAddrPub, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hEaEq := evalX86Addr_public_eq (d.offset + d.byteLen) hAddrPub hAddrReg rGpr
        simp only [stepX86, hIns, hEaEq, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, rYmm, rCf, rOf, rZf, rDirty,
          (fun h => nomatch h), ?_, ?_⟩
        · intro hRbpOk
          cases hRbpB : st.rbpSaved
          · simp [hRbpB] at hRbpOk
          · simp only [hRbpB, ↓reduceIte] at hRbpOk
            rcases rRbp hRbpB with ⟨hSp0Eq, hM1, hM2⟩
            rcases storePreservesSavedRbp_disjoint (d.offset + d.byteLen) hInit hRelFull hAddrReg hRbpOk
              with ⟨hDisj1, hDisj2⟩
            refine ⟨hSp0Eq, ?_, ?_⟩
            · rw [hEaEq] at hDisj1
              cases is256
              · simp only [Bool.false_eq_true, ↓reduceIte] at hDisj1 ⊢
                rw [readMem64_congr (fun k hk => writeMem128_ne _ _ (fun j hj => hDisj1 j k hj hk))]
                exact hM1
              · simp only [↓reduceIte] at hDisj1 ⊢
                rw [readMem64_congr (fun k hk => writeMem256_ne _ _ (fun j hj => hDisj1 j k hj hk))]
                exact hM1
            · cases is256
              · simp only [Bool.false_eq_true, ↓reduceIte] at hDisj2 ⊢
                rw [readMem64_congr (fun k hk => writeMem128_ne _ _ (fun j hj => hDisj2 j k hj hk))]
                exact hM2
              · simp only [↓reduceIte] at hDisj2 ⊢
                rw [readMem64_congr (fun k hk => writeMem256_ne _ _ (fun j hj => hDisj2 j k hj hk))]
                exact hM2
        · by_cases hKeepLoop : (st.stackZeroLoop == 1 && addr == .baseDisp 0 0 && is256) = true
          · simp only [hKeepLoop, ↓reduceIte]
            simp only [Bool.and_eq_true, beq_iff_eq] at hKeepLoop
            have hL1 := hKeepLoop.1.1
            unfold RelX86Loop at rLoop ⊢
            simpa only [hL1] using rLoop
          · simp [hKeepLoop, RelX86Loop]
    case vmovGprToXmm is64 dstVec srcGpr =>
      rcases hValid with ⟨hd16, hs16⟩
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, ?_, rCf, rOf, rZf, rDirty, rMem, rRbp,
        by simp [RelX86Loop]⟩
      apply RelX86Vec_set hd16 rYmm
      by_cases hz : (st.gpr.get srcGpr == .zeroConst) = true
      · simp only [hz, ↓reduceIte, RelX86Vec]
        have rs := rGpr srcGpr hs16
        rw [beq_iff_eq.mp hz] at rs
        rcases rs with ⟨r1, r2⟩
        have hm0 : maskGprWidth is64 0 = 0 := by cases is64 <;> rfl
        simp [r1, r2, hm0, Vec256.zero]
      · simp only [hz, Bool.false_eq_true, ↓reduceIte]
        by_cases hp : (st.gpr.get srcGpr).isPublic = true
        · simp only [hp, ↓reduceIte, RelX86Vec]
          rw [RelX86Gpr_public_eq (rGpr srcGpr hs16) hp]
        · simp [hp, RelX86Vec]
    case vpbroadcast isQword dst srcVec =>
      rcases hValid with ⟨hd16, hs16⟩
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, ?_, rCf, rOf, rZf,
        (fun h => nomatch h), rMem, rRbp, by simp [RelX86Loop]⟩
      apply RelX86Vec_set hd16 rYmm
      by_cases hz : (st.ymm.get srcVec == .zeroConst) = true
      · simp only [hz, ↓reduceIte, RelX86Vec]
        have rv := rYmm srcVec hs16
        rw [beq_iff_eq.mp hz] at rv
        rcases rv with ⟨r1, r2⟩
        have hmb0 : mapBytes64 (fun _ => 0) = 0 := by decide
        cases isQword
        · simp [r1, r2, Vec256.zero, hmb0]
        · simp [r1, r2, Vec256.zero]
      · simp only [hz, Bool.false_eq_true, ↓reduceIte]
        by_cases hp : (st.ymm.get srcVec).isPublic = true
        · simp only [hp, ↓reduceIte, RelX86Vec]
          rw [RelX86Vec_public_eq (rYmm srcVec hs16) hp]
        · simp [hp, RelX86Vec]
    case vpbroadcastLoad64 dst addr =>
      rcases hValid with ⟨hd16, hAddrReg⟩
      cases hAddrPub : x86AddrIsPublic st addr
      · simp [hAddrPub] at hTr
      · simp only [hAddrPub, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hEaEq := evalX86Addr_public_eq (d.offset + d.byteLen) hAddrPub hAddrReg rGpr
        simp only [stepX86, hIns, hEaEq, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, ?_, rCf, rOf, rZf,
          (fun h => nomatch h), rMem, rRbp, by simp [RelX86Loop]⟩
        apply RelX86Vec_set hd16 rYmm
        by_cases hIn : isInPubMemRegion c st addr 8 = true
        · simp only [hIn, ↓reduceIte, RelX86Vec]
          have hBytes := isInPubMemRegion_bytes_eq (d.offset + d.byteLen) hInit hRelFull hAddrReg hIn
          rw [readMem64_congr (fun j hj => by simpa only [← hEaEq] using hBytes j hj)]
        · simp [hIn, RelX86Vec]
    case vbinOp op is256 dst src1 src2 =>
      rcases hValid with ⟨⟨hd16, hs1⟩, hs2⟩
      by_cases hSelf : (op == .vpxor && src1 == src2) = true
      · simp only [hSelf, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [Bool.and_eq_true, beq_iff_eq] at hSelf
        rcases hSelf with ⟨rfl, rfl⟩
        have hXorZ (v : Vec256) : clampVecWidth is256 (evalVecBin256 .vpxor v v) = Vec256.zero := by
          have hx (w : UInt64) : w ^^^ w = 0 := by apply UInt64.eq_of_toBitVec_eq; simp
          cases is256 <;> simp [evalVecBin256, clampVecWidth, Vec256.zero, hx]
        simp only [stepX86, hIns, hXorZ, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr,
          RelX86Vec_set hd16 rYmm ⟨rfl, rfl⟩,
          rCf, rOf, rZf, ?_, rMem, rRbp, by simp [RelX86Loop]⟩
        intro hClean
        simp only [Bool.or_eq_false_iff] at hClean
        rcases rDirty hClean.1 with ⟨d1, d2⟩
        simp [d1, d2, hClean.2]
      · simp only [hSelf, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [stepX86, hIns, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, ?_, rCf, rOf, rZf, ?_, rMem, rRbp,
          by simp [RelX86Loop]⟩
        · apply RelX86Vec_set hd16 rYmm
          by_cases hp : ((st.ymm.get src1).isPublic && (st.ymm.get src2).isPublic) = true
          · simp only [hp, ↓reduceIte, RelX86Vec]
            simp only [Bool.and_eq_true] at hp
            rw [RelX86Vec_public_eq (rYmm src1 hs1) hp.1, RelX86Vec_public_eq (rYmm src2 hs2) hp.2]
          · simp [hp, RelX86Vec]
        · intro hClean
          simp only [Bool.or_eq_false_iff] at hClean
          rcases rDirty hClean.1 with ⟨d1, d2⟩
          simp [d1, d2, hClean.2]
    case vpxorLoad128 dst src1 addr =>
      rcases hValid with ⟨⟨hd16, hs1⟩, hAddrReg⟩
      cases hAddrPub : x86AddrIsPublic st addr
      · simp [hAddrPub] at hTr
      · simp only [hAddrPub, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hEaEq := evalX86Addr_public_eq (d.offset + d.byteLen) hAddrPub hAddrReg rGpr
        simp only [stepX86, hIns, hEaEq, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, ?_, rCf, rOf, rZf,
          rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
        apply RelX86Vec_set hd16 rYmm
        by_cases hp : ((st.ymm.get src1).isPublic && isInPubMemRegion c st addr 16) = true
        · simp only [hp, ↓reduceIte, RelX86Vec]
          simp only [Bool.and_eq_true] at hp
          have hBytes := isInPubMemRegion_bytes_eq (d.offset + d.byteLen) hInit hRelFull hAddrReg hp.2
          rw [RelX86Vec_public_eq (rYmm src1 hs1) hp.1,
              readMem128_congr (fun j hj => by simpa only [← hEaEq] using hBytes j hj)]
        · simp [hp, RelX86Vec]
    case vpxorLoad256 dst src1 addr =>
      rcases hValid with ⟨⟨hd16, hs1⟩, hAddrReg⟩
      cases hAddrPub : x86AddrIsPublic st addr
      · simp [hAddrPub] at hTr
      · simp only [hAddrPub, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hEaEq := evalX86Addr_public_eq (d.offset + d.byteLen) hAddrPub hAddrReg rGpr
        simp only [stepX86, hIns, hEaEq, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, ?_, rCf, rOf, rZf,
          (fun h => nomatch h), rMem, rRbp, by simp [RelX86Loop]⟩
        apply RelX86Vec_set hd16 rYmm
        by_cases hp : ((st.ymm.get src1).isPublic && isInPubMemRegion c st addr 32) = true
        · simp only [hp, ↓reduceIte, RelX86Vec]
          simp only [Bool.and_eq_true] at hp
          have hBytes := isInPubMemRegion_bytes_eq (d.offset + d.byteLen) hInit hRelFull hAddrReg hp.2
          rw [RelX86Vec_public_eq (rYmm src1 hs1) hp.1,
              readMem256_congr (fun j hj => by simpa only [← hEaEq] using hBytes j hj)]
        · simp [hp, RelX86Vec]
    case vshiftImm sk is256 dst src imm =>
      rcases hValid with ⟨hd16, hs16⟩
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, ?_, rCf, rOf, rZf, ?_, rMem, rRbp,
        by simp [RelX86Loop]⟩
      · apply RelX86Vec_set hd16 rYmm
        by_cases hz : (st.ymm.get src == .zeroConst) = true
        · simp only [hz, ↓reduceIte, RelX86Vec]
          have rv := rYmm src hs16
          rw [beq_iff_eq.mp hz] at rv
          rcases rv with ⟨r1, r2⟩
          rw [r1, r2, evalVecShift256_zero]
          exact ⟨rfl, rfl⟩
        · simp only [hz, Bool.false_eq_true, ↓reduceIte]
          by_cases hp : (st.ymm.get src).isPublic = true
          · simp only [hp, ↓reduceIte, RelX86Vec]
            rw [RelX86Vec_public_eq (rYmm src hs16) hp]
          · simp [hp, RelX86Vec]
      · intro hClean
        simp only [Bool.or_eq_false_iff] at hClean
        rcases rDirty hClean.1 with ⟨d1, d2⟩
        simp [d1, d2, hClean.2]
    case vpclmulqdq is256 dst src1 src2 imm =>
      rcases hValid with ⟨⟨hd16, hs1⟩, hs2⟩
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, ?_, rCf, rOf, rZf, ?_, rMem, rRbp,
        by simp [RelX86Loop]⟩
      · apply RelX86Vec_set hd16 rYmm
        by_cases hp : ((st.ymm.get src1).isPublic && (st.ymm.get src2).isPublic) = true
        · simp only [hp, ↓reduceIte, RelX86Vec]
          simp only [Bool.and_eq_true] at hp
          rw [RelX86Vec_public_eq (rYmm src1 hs1) hp.1, RelX86Vec_public_eq (rYmm src2 hs2) hp.2]
        · simp [hp, RelX86Vec]
      · intro hClean
        simp only [Bool.or_eq_false_iff] at hClean
        rcases rDirty hClean.1 with ⟨d1, d2⟩
        simp [d1, d2, hClean.2]
    case vgf2p8affineqb is256 dst src1 src2 imm =>
      rcases hValid with ⟨⟨hd16, hs1⟩, hs2⟩
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, ?_, rCf, rOf, rZf, ?_, rMem, rRbp,
        by simp [RelX86Loop]⟩
      · apply RelX86Vec_set hd16 rYmm
        by_cases hp : ((st.ymm.get src1).isPublic && (st.ymm.get src2).isPublic) = true
        · simp only [hp, ↓reduceIte, RelX86Vec]
          simp only [Bool.and_eq_true] at hp
          rw [RelX86Vec_public_eq (rYmm src1 hs1) hp.1, RelX86Vec_public_eq (rYmm src2 hs2) hp.2]
        · simp [hp, RelX86Vec]
      · intro hClean
        simp only [Bool.or_eq_false_iff] at hClean
        rcases rDirty hClean.1 with ⟨d1, d2⟩
        simp [d1, d2, hClean.2]
    case vperm2i128 dst src1 src2 imm =>
      rcases hValid with ⟨⟨hd16, hs1⟩, hs2⟩
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, ?_, rCf, rOf, rZf,
        (fun h => nomatch h), rMem, rRbp, by simp [RelX86Loop]⟩
      apply RelX86Vec_set hd16 rYmm
      by_cases hp : ((st.ymm.get src1).isPublic && (st.ymm.get src2).isPublic) = true
      · simp only [hp, ↓reduceIte, RelX86Vec]
        simp only [Bool.and_eq_true] at hp
        rw [RelX86Vec_public_eq (rYmm src1 hs1) hp.1, RelX86Vec_public_eq (rYmm src2 hs2) hp.2]
      · simp [hp, RelX86Vec]

private theorem runX86_of_halted (prog : List (DecodedInstr X86Instr)) (fuel : Nat)
    {s : X86State} (hHalt : s.halted = true) :
    runX86 prog fuel s = (s, []) := by
  cases fuel with
  | zero => rfl
  | succ k => simp [runX86, hHalt]

private theorem runX86_invariant_sound {c : FuncContract}
    {prog : List (DecodedInstr X86Instr)} {inv : PcMap X86AbsState}
    {s₁₀ s₂₀ : X86State}
    (hInit : X86ContractInit c s₁₀ s₂₀)
    (hAll : inv.all (fun pc st =>
      match (buildProgMap prog).get pc with
      | none => false
      | some d =>
        match transferX86Instr c d st with
        | none => false
        | some succs =>
          succs.all (fun (npc, nst) =>
            match inv.get npc with
            | none => false
            | some dstSt => nst.le dstSt)) = true) :
    ∀ (fuel : Nat) {s₁ s₂ : X86State} {st : X86AbsState},
      inv.get s₁.pc = some st →
      RelX86 s₁₀ s₂₀ st s₁ s₂ →
      let (s₁f, tr₁) := runX86 prog fuel s₁
      let (s₂f, tr₂) := runX86 prog fuel s₂
      tr₁ = tr₂ ∧
      (∀ obs ∈ tr₁, obs.isDoitSafe = true) ∧
      ((s₁f.halted = true ∧ s₂f.halted = true ∧ X86ExitHygiene c s₁₀ s₂₀ s₁f s₂f) ∨
       (s₁f.halted = false ∧ s₂f.halted = false))
  | 0, s₁, s₂, st, _, hRel =>
    ⟨rfl, (fun _ h => nomatch h), Or.inr ⟨hRel.2.1, hRel.2.2.1⟩⟩
  | fuel + 1, s₁, s₂, st, hInvPc, hRel => by
    have hPcLt : s₁.pc < 4096 := PcMap.get_some_lt hInvPc
    have hPred := PcMap.all_get hAll hInvPc
    rw [buildProgMap_get_eq prog hPcLt] at hPred
    cases hFind : findInstrAtPc s₁.pc prog with
    | none => simp [hFind] at hPred
    | some d =>
      simp only [hFind] at hPred
      cases hTr : transferX86Instr c d st with
      | none => simp [hTr] at hPred
      | some succs =>
        simp only [hTr, List.all_eq_true] at hPred
        have hFind2 : findInstrAtPc s₂.pc prog = some d := hRel.1 ▸ hFind
        have hOffEq : s₁.pc = d.offset := (findInstrAtPc_offset hFind).symm
        have hStep := transferX86Instr_step_sound hInit hRel hOffEq hTr
        rcases stp1 : stepX86 d s₁ with ⟨s₁', obs₁⟩
        rcases stp2 : stepX86 d s₂ with ⟨s₂', obs₂⟩
        simp only [stp1, stp2] at hStep
        rcases hStep with ⟨hObsEq, hDoit, hExitOrCont⟩
        simp only [runX86, hRel.2.1, hRel.2.2.1, Bool.false_eq_true, ↓reduceIte, hFind, hFind2, stp1, stp2]
        rcases hExitOrCont with ⟨hh1', hh2', hHyg⟩ | ⟨nst, hMemSucc, hRel'⟩
        · rw [runX86_of_halted prog fuel hh1', runX86_of_halted prog fuel hh2']
          refine ⟨congrArg (· :: []) hObsEq, ?_, Or.inl ⟨hh1', hh2', hHyg⟩⟩
          intro o ho; simp at ho; subst ho; exact hDoit
        · have hSuccOk := hPred (s₁'.pc, nst) hMemSucc
          cases hInvNext : inv.get s₁'.pc with
          | none => simp [hInvNext] at hSuccOk
          | some dstSt =>
            simp only [hInvNext] at hSuccOk
            have hRelDst := RelX86_mono hRel' hSuccOk
            have ih := runX86_invariant_sound hInit hAll fuel hInvNext hRelDst
            rcases hr1 : runX86 prog fuel s₁' with ⟨s₁f, tr₁⟩
            rcases hr2 : runX86 prog fuel s₂' with ⟨s₂f, tr₂⟩
            simp only [hr1, hr2] at ih
            rcases ih with ⟨hTrEq, hTrDoit, hPost⟩
            refine ⟨by rw [hObsEq, hTrEq], ?_, hPost⟩
            intro o ho
            rcases List.mem_cons.mp ho with rfl | hRest
            · exact hDoit
            · exact hTrDoit o hRest

/-- **3-Way Hardware Constant-Time Noninterference + System V ABI Hygiene Soundness (`x86_64`):**
    Whenever `checkX86ThreeWayNI code c = true`, for ANY two initial machine states `(s₁, s₂)`
    satisfying `X86ContractInit c s₁ s₂` (with arbitrary secret memory & secret registers) and
    ANY execution fuel `fuel`:
    1. **`PC-NI` & `Mem-NI`:** `tr₁ = tr₂` (every executed PC and `(addr, width)` memory access matches),
    2. **`DOIT-NI`:** Every executed instruction has `obs.isDoitSafe = true`. For `cmovcc` this
       flag means "data-operand-independent when `DOITM` is set": `X86State` carries no `DOITM`
       bit, and the checker accepts `cmovcc` only under a contract with `c.doitEnabled = true`
       (`tooth_x86_cmovcc_rejected_without_doit`). The guarantee for such a stream is therefore
       conditional on the processor running it in that mode,
    3. **`ABI & Epilogue Zeroization`:** If execution halts (`ret`), both states halt together and
       satisfy `X86ExitHygiene c s₁ s₂ s₁f s₂f` (`rsp` & `rbx, rbp, r12..r15` preserved,
       `ymmDirty = false` via `vzeroupper`, scratch `ymm` secrets wiped, scratch GPRs wiped). -/
theorem checkX86ThreeWayNI_sound {code : List UInt8} {c : FuncContract}
    (hCheck : checkX86ThreeWayNI code c = true)
    {s₁ s₂ : X86State} (hInit : X86ContractInit c s₁ s₂) (fuel : Nat) :
    ∃ prog : List (DecodedInstr X86Instr),
      decodeX86Stream code = some prog ∧
      let (s₁f, tr₁) := runX86 prog fuel s₁
      let (s₂f, tr₂) := runX86 prog fuel s₂
      tr₁ = tr₂ ∧
      (∀ obs ∈ tr₁, obs.isDoitSafe = true) ∧
      ((s₁f.halted = true ∧ s₂f.halted = true ∧ X86ExitHygiene c s₁ s₂ s₁f s₂f) ∨
       (s₁f.halted = false ∧ s₂f.halted = false)) := by
  unfold checkX86ThreeWayNI at hCheck
  cases hDec : decodeX86Stream code with
  | none => simp [hDec] at hCheck
  | some prog =>
    simp only [hDec] at hCheck
    cases prog with
    | nil => simp at hCheck
    | cons d0 ds =>
      cases hInf : inferX86Invariant (d0 :: ds) c with
      | none => simp [hInf] at hCheck
      | some inv =>
        simp only [hInf, verifyX86Invariant, Bool.and_eq_true] at hCheck
        rcases hCheck with ⟨hEntry, hAll⟩
        cases hInv0 : inv.get 0 with
        | none => simp [hInv0] at hEntry
        | some st0 =>
          simp only [hInv0] at hEntry
          have hRel0 := RelX86_mono (RelX86_init hInit) hEntry
          have hInvS1 : inv.get s₁.pc = some st0 := hInit.1 ▸ hInv0
          exact ⟨d0 :: ds, rfl, runX86_invariant_sound hInit hAll fuel hInvS1 hRel0⟩


/-! #### Inductive Relational Invariant & Step Soundness for `AArch64` -/

private def RelArmGpr (s₁₀ s₂₀ : Arm64State) (orig : ArmRegOrigin) (v₁ v₂ : UInt64) : Prop :=
  match orig with
  | .initSame r => r < 31 ∧ v₁ = s₁₀.gpr.get r ∧ v₂ = s₂₀.gpr.get r ∧ v₁ = v₂
  | .initOwn r => r < 31 ∧ v₁ = s₁₀.gpr.get r ∧ v₂ = s₂₀.gpr.get r
  | .zeroConst => v₁ = 0 ∧ v₂ = 0
  | .pubVal => v₁ = v₂
  | .secretVal => True

private theorem RelArmGpr_public_eq {s₁₀ s₂₀ : Arm64State} {orig : ArmRegOrigin} {v₁ v₂ : UInt64}
    (hRel : RelArmGpr s₁₀ s₂₀ orig v₁ v₂) (hPub : orig.isPublic = true) :
    v₁ = v₂ := by
  cases orig with
  | initSame _ => exact hRel.2.2.2
  | initOwn _ => cases hPub
  | zeroConst => exact hRel.1.trans hRel.2.symm
  | pubVal => exact hRel
  | secretVal => cases hPub

private theorem RelArmGpr_mono {s₁₀ s₂₀ : Arm64State} {a b : ArmRegOrigin} {v₁ v₂ : UInt64}
    (hRel : RelArmGpr s₁₀ s₂₀ a v₁ v₂) (hle : a.le b = true) :
    RelArmGpr s₁₀ s₂₀ b v₁ v₂ := by
  unfold ArmRegOrigin.le at hle
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hle
  rcases hle with (rfl | rfl) | ⟨rfl, hPub⟩
  · exact hRel
  · trivial
  · exact RelArmGpr_public_eq hRel hPub

private def RelArmVec (s₁₀ s₂₀ : Arm64State) (vo : VecOrigin) (v₁ v₂ : Vec128) : Prop :=
  match vo with
  | .initVec r => r < 32 ∧ v₁ = s₁₀.vec.get r ∧ v₂ = s₂₀.vec.get r
  | .zeroConst => v₁ = Vec128.zero ∧ v₂ = Vec128.zero
  | .pubVal => v₁ = v₂
  | .secretVal => True

private theorem RelArmVec_public_eq {s₁₀ s₂₀ : Arm64State} {vo : VecOrigin} {v₁ v₂ : Vec128}
    (hRel : RelArmVec s₁₀ s₂₀ vo v₁ v₂) (hPub : vo.isPublic = true) :
    v₁ = v₂ := by
  cases vo <;> simp [VecOrigin.isPublic, RelArmVec] at hPub hRel
  · rw [hRel.1, hRel.2]
  · exact hRel

private theorem RelArmVec_mono {s₁₀ s₂₀ : Arm64State} {a b : VecOrigin} {v₁ v₂ : Vec128}
    (hRel : RelArmVec s₁₀ s₂₀ a v₁ v₂) (hle : a.le b = true) :
    RelArmVec s₁₀ s₂₀ b v₁ v₂ := by
  unfold VecOrigin.le at hle
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hle
  rcases hle with (rfl | rfl) | ⟨rfl, hPub⟩
  · exact hRel
  · trivial
  · exact RelArmVec_public_eq hRel hPub

private def RelArm64 (s₁₀ s₂₀ : Arm64State) (st : Arm64AbsState) (s₁ s₂ : Arm64State) : Prop :=
  s₁.pc = s₂.pc ∧
  s₁.halted = false ∧ s₂.halted = false ∧
  s₁.dit = st.dit ∧ s₂.dit = st.dit ∧
  (∀ r : Nat, r < 31 → RelArmGpr s₁₀ s₂₀ (st.gpr.get r) (s₁.gpr.get r) (s₂.gpr.get r)) ∧
  (∀ v : Nat, v < 32 → RelArmVec s₁₀ s₂₀ (st.vec.get v) (s₁.vec.get v) (s₂.vec.get v)) ∧
  (st.cfPub = true → s₁.cf = s₂.cf) ∧
  (st.zfPub = true → s₁.zf = s₂.zf)

private theorem RelArm64_mono {s₁₀ s₂₀ s₁ s₂ : Arm64State} {a b : Arm64AbsState}
    (hRel : RelArm64 s₁₀ s₂₀ a s₁ s₂) (hle : a.le b = true) :
    RelArm64 s₁₀ s₂₀ b s₁ s₂ := by
  unfold Arm64AbsState.le at hle
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hle
  rcases hle with ⟨⟨⟨⟨hDit, hGpr⟩, hVec⟩, hCf⟩, hZf⟩
  rcases hRel with ⟨hPc, hH1, hH2, rDit1, rDit2, rGpr, rVec, rCf, rZf⟩
  refine ⟨hPc, hH1, hH2, rDit1.trans (beq_iff_eq.mp hDit), rDit2.trans (beq_iff_eq.mp hDit), ?_, ?_, ?_, ?_⟩
  · intro r hr; exact RelArmGpr_mono (rGpr r hr) (Bank32.allIdx_get hGpr (by omega))
  · intro v hv; exact RelArmVec_mono (rVec v hv) (Bank32.allIdx_get hVec hv)
  · intro hb; exact hCf.elim (fun hbf => nomatch hbf.symm.trans hb) (fun ha => rCf ha)
  · intro hb; exact hZf.elim (fun hbf => nomatch hbf.symm.trans hb) (fun ha => rZf ha)

private theorem RelArm64_init {c : FuncContract} {s₁ s₂ : Arm64State}
    (hInit : Arm64ContractInit c s₁ s₂) :
    RelArm64 s₁ s₂ (initArm64AbsState c) s₁ s₂ := by
  rcases hInit with ⟨hpc1, hpc2, hh1, hh2, hd1, hd2, hPubGprs⟩
  refine ⟨by omega, hh1, hh2, hd1, hd2, ?_, ?_, (fun h => nomatch h), (fun h => nomatch h)⟩
  · intro r hr
    unfold initArm64AbsState
    rw [Bank32.get_ofFn _ (by omega)]
    have hne31 : (r == 31) = false := beq_false_of_ne (by omega)
    simp only [hne31, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i hMem
      exact ⟨hr, rfl, rfl, (hPubGprs r hMem).2⟩
    · split
      · exact ⟨hr, rfl, rfl⟩
      · trivial
  · intro v hv
    unfold initArm64AbsState
    rw [Bank32.get_ofFn _ hv]
    exact ⟨hv, rfl, rfl⟩

private theorem getArmGpr_rel {s₁₀ s₂₀ s₁ s₂ : Arm64State} {st : Arm64AbsState} {r : Nat}
    (hr : r < 32)
    (rGpr : ∀ i < 31, RelArmGpr s₁₀ s₂₀ (st.gpr.get i) (s₁.gpr.get i) (s₂.gpr.get i)) :
    RelArmGpr s₁₀ s₂₀ (getArmAbsGpr st r) (getArmGpr s₁ r) (getArmGpr s₂ r) := by
  unfold getArmAbsGpr getArmGpr
  by_cases h31 : r == 31
  · simp [h31, RelArmGpr]
  · simp only [h31, Bool.false_eq_true, ↓reduceIte]
    have hne : r ≠ 31 := fun h => h31 (beq_iff_eq.mpr h)
    exact rGpr r (by omega)

private theorem setArmGpr_rel {s₁₀ s₂₀ s₁ s₂ : Arm64State} {st : Arm64AbsState}
    {rd : Nat} {orig : ArmRegOrigin} {v₁ v₂ : UInt64}
    (_hrd : rd < 32)
    (rGpr : ∀ i < 31, RelArmGpr s₁₀ s₂₀ (st.gpr.get i) (s₁.gpr.get i) (s₂.gpr.get i))
    (hNew : RelArmGpr s₁₀ s₂₀ orig v₁ v₂) :
    ∀ i < 31, RelArmGpr s₁₀ s₂₀ ((setArmAbsGpr st rd orig).get i)
      ((setArmGpr s₁ rd v₁).get i) ((setArmGpr s₂ rd v₂).get i) := by
  intro i hi
  unfold setArmAbsGpr setArmGpr
  by_cases h31 : rd == 31
  · simp only [h31, ↓reduceIte]; exact rGpr i hi
  · simp only [h31, Bool.false_eq_true, ↓reduceIte]
    have hrd31 : rd < 31 := by
      have hne : rd ≠ 31 := fun h => h31 (beq_iff_eq.mpr h)
      omega
    by_cases heq : i = rd
    · subst heq; simp only [Bank32.get_set_eq]; exact hNew
    · rw [Bank32.get_set_ne _ _ (by omega) (by omega) (Ne.symm heq),
          Bank32.get_set_ne _ _ (by omega) (by omega) (Ne.symm heq),
          Bank32.get_set_ne _ _ (by omega) (by omega) (Ne.symm heq)]
      exact rGpr i hi

private theorem RelArmVec_set {s₁₀ s₂₀ : Arm64State} {vc : Bank32 VecOrigin} {b₁ b₂ : Bank32 Vec128}
    {vd : Nat} {vo : VecOrigin} {v₁ v₂ : Vec128}
    (hvd : vd < 32)
    (hOld : ∀ i < 32, RelArmVec s₁₀ s₂₀ (vc.get i) (b₁.get i) (b₂.get i))
    (hNew : RelArmVec s₁₀ s₂₀ vo v₁ v₂) :
    ∀ i < 32, RelArmVec s₁₀ s₂₀ ((vc.set vd vo).get i) ((b₁.set vd v₁).get i) ((b₂.set vd v₂).get i) := by
  intro i hi
  by_cases heq : i = vd
  · subst heq; simp only [Bank32.get_set_eq]; exact hNew
  · rw [Bank32.get_set_ne _ _ hvd hi (Ne.symm heq),
        Bank32.get_set_ne _ _ hvd hi (Ne.symm heq),
        Bank32.get_set_ne _ _ hvd hi (Ne.symm heq)]
    exact hOld i hi

private theorem evalArmCond_public_eq {st : Arm64AbsState} {s₁ s₂ : Arm64State} {cond : Nat}
    (hPub : armCondIsPublic cond st = true)
    (rCf : st.cfPub = true → s₁.cf = s₂.cf)
    (rZf : st.zfPub = true → s₁.zf = s₂.zf) :
    evalArmCond cond s₁ = evalArmCond cond s₂ := by
  unfold armCondIsPublic at hPub
  unfold evalArmCond
  by_cases c0 : cond == 0
  · simp [c0] at hPub ⊢; exact rZf hPub
  · by_cases c1 : cond == 1
    · simp [c0, c1] at hPub ⊢; exact rZf hPub
    · by_cases c2 : cond == 2
      · simp [c0, c1, c2] at hPub ⊢; exact rCf hPub
      · by_cases c3 : cond == 3
        · simp [c0, c1, c2, c3] at hPub ⊢; exact rCf hPub
        · simp [c0, c1, c2, c3] at hPub ⊢; exact rCf hPub

private theorem arm_eor_self_zero (is64 : Bool) (v : UInt64) (sk : Nat) (cf zf : Bool) :
    evalArmAlu .eor is64 v (applyArmShift is64 v sk 0) cf zf = (0, cf, zf) := by
  unfold applyArmShift evalArmAlu maskGprWidth
  cases is64
  · simp only [Bool.false_eq_true, ↓reduceIte, show 0 % 32 = 0 from rfl, beq_self_eq_true]
    have hz : (v ^^^ (v &&& 0xFFFFFFFF)) &&& 0xFFFFFFFF = 0 := by
      apply UInt64.eq_of_toBitVec_eq
      rw [UInt64.toBitVec_and, UInt64.toBitVec_xor, UInt64.toBitVec_and]
      apply BitVec.eq_of_getLsbD_eq; intro i _hi
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor]
      rw [show (0 : UInt64).toBitVec = 0#64 from rfl, BitVec.getLsbD_zero]
      cases v.toBitVec.getLsbD i <;>
        cases (0xFFFFFFFF : UInt64).toBitVec.getLsbD i <;> rfl
    simp [hz]
  · simp only [↓reduceIte, show 0 % 64 = 0 from rfl, beq_self_eq_true]
    have hz : v ^^^ v = 0 := by apply UInt64.eq_of_toBitVec_eq; simp
    simp [hz]

private theorem evalArmAlu_res_flags {op : Arm64AluOp} {is64 : Bool}
    {a₁ b₁ : UInt64} {cf₁ zf₁ : Bool} :
    (evalArmAlu op is64 a₁ b₁ cf₁ zf₁).2 =
      (if op == .adds || op == .subs then
         ((evalArmAlu op is64 a₁ b₁ cf₁ zf₁).2.1, (evalArmAlu op is64 a₁ b₁ cf₁ zf₁).2.2)
       else (cf₁, zf₁)) := by
  cases op <;> rfl

private theorem evalArmAlu_pub_congr (op : Arm64AluOp) (is64 : Bool)
    {a₁ a₂ b₁ b₂ : UInt64} {cf₁ cf₂ zf₁ zf₂ : Bool}
    (ha : a₁ = a₂) (hb : b₁ = b₂)
    (hcf : (if op == .adc || op == .sbc then true else false) = true → cf₁ = cf₂) :
    (evalArmAlu op is64 a₁ b₁ cf₁ zf₁).1 = (evalArmAlu op is64 a₂ b₂ cf₂ zf₂).1 ∧
    ((op == .adds || op == .subs) = true →
      (evalArmAlu op is64 a₁ b₁ cf₁ zf₁).2.1 = (evalArmAlu op is64 a₂ b₂ cf₂ zf₂).2.1 ∧
      (evalArmAlu op is64 a₁ b₁ cf₁ zf₁).2.2 = (evalArmAlu op is64 a₂ b₂ cf₂ zf₂).2.2) := by
  subst ha hb
  cases op <;> simp_all [evalArmAlu]

private theorem transferArm64Instr_step_sound {c : FuncContract}
    {s₁₀ s₂₀ s₁ s₂ : Arm64State} {d : DecodedInstr Arm64Instr}
    {st : Arm64AbsState} {succs : List (Nat × Arm64AbsState)}
    (hRel : RelArm64 s₁₀ s₂₀ st s₁ s₂)
    (_hPcEq : s₁.pc = d.offset)
    (hTr : transferArm64Instr c d st = some succs) :
    let (s₁', obs₁) := stepArm64 d s₁
    let (s₂', obs₂) := stepArm64 d s₂
    obs₁ = obs₂ ∧
    obs₁.isDoitSafe = true ∧
    ((s₁'.halted = true ∧ s₂'.halted = true ∧ Arm64ExitHygiene c s₁₀ s₂₀ s₁' s₂') ∨
     (∃ nst : Arm64AbsState, (s₁'.pc, nst) ∈ succs ∧ RelArm64 s₁₀ s₂₀ nst s₁' s₂')) := by
  by_cases hGate : (armRequiresDit d.instr && !st.dit) = true
  · simp [transferArm64Instr, hGate] at hTr
  have hAllowed : armRequiresDit d.instr = true → st.dit = true := by
    intro h
    cases hd : st.dit
    · simp [h, hd] at hGate
    · rfl
  cases hValid : arm64InstrRegsValid d.instr
  · unfold transferArm64Instr at hTr; simp [hGate, hValid] at hTr
  · rcases hRel with ⟨hPc12, hH1, hH2, rDit1, rDit2, rGpr, rVec, rCf, rZf⟩
    cases hIns : d.instr <;>
      unfold transferArm64Instr at hTr <;>
      simp only [hGate, Bool.false_eq_true, ↓reduceIte] at hTr <;>
      rw [hIns] at hTr hValid <;>
      simp only [hValid, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr <;>
      simp only [arm64InstrRegsValid, Bool.and_eq_true, decide_eq_true_eq] at hValid
    case nop =>
      injection hTr with hS; subst hS; simp only [stepArm64, hIns, true_and]
      exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, rVec, rCf, rZf⟩
    case msrDit imm =>
      injection hTr with hS; subst hS; simp only [stepArm64, hIns, true_and]
      exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rfl, rfl, rGpr, rVec, rCf, rZf⟩
    case isb =>
      injection hTr with hS; subst hS; simp only [stepArm64, hIns, true_and]
      exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, rVec, rCf, rZf⟩
    case dmbIsh =>
      injection hTr with hS; subst hS; simp only [stepArm64, hIns, true_and]
      exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, rVec, rCf, rZf⟩
    case ret =>
      by_cases hRetOk : (([19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30].all (fun r =>
            st.gpr.get r == .initOwn r || st.gpr.get r == .initSame r)) &&
          ([8, 9, 10, 11, 12, 13, 14, 15].all (fun v => st.vec.get v == .initVec v)) &&
          st.vec.allIdx (fun _ vo => vo != .secretVal && vo != .pubVal) &&
          c.wipedScratchGprs.all (fun r => decide (r < 32) && getArmAbsGpr st r == .zeroConst)) = true
      · simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
          List.all_eq_true] at hRetOk
        rcases hRetOk with ⟨⟨⟨hCalleeGpr, hCalleeVec⟩, hVecWiped⟩, hGprWiped⟩
        simp only [stepArm64, hIns, true_and]
        left
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro r hr
          have hcr := hCalleeGpr r hr
          have hr31 : r < 31 := by simp at hr; omega
          have rr := rGpr r hr31
          rcases hcr with hOwn | hSame
          · rw [hOwn] at rr; exact rr.2
          · rw [hSame] at rr; exact ⟨rr.2.1, rr.2.2.1⟩
        · intro v hv
          have hcv := hCalleeVec v hv
          have hv32 : v < 32 := by simp at hv; omega
          have rv := rVec v hv32
          rw [hcv] at rv
          exact rv.2
        · intro v hv
          have hNotSec := Bank32.allIdx_get hVecWiped hv
          simp only [Bool.and_eq_true, bne_iff_ne] at hNotSec
          have rv := rVec v hv
          cases hVo : st.vec.get v <;> rw [hVo] at rv hNotSec
          · exact Or.inr ⟨_, rv.1, rv.2⟩
          · exact Or.inl rv
          · exact absurd rfl hNotSec.2
          · exact absurd rfl hNotSec.1
        · intro r hr
          rcases hGprWiped r hr with ⟨hr32, hZ⟩
          have rr := getArmGpr_rel hr32 rGpr
          rw [hZ] at rr
          exact rr
      · have hF : (([19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30].all (fun r =>
              st.gpr.get r == .initOwn r || st.gpr.get r == .initSame r)) &&
            ([8, 9, 10, 11, 12, 13, 14, 15].all (fun v => st.vec.get v == .initVec v)) &&
            st.vec.allIdx (fun _ vo => vo != .secretVal && vo != .pubVal) &&
            c.wipedScratchGprs.all (fun r => decide (r < 32) && getArmAbsGpr st r == .zeroConst)) = false :=
          Bool.eq_false_iff.mpr hRetOk
        simp only [hF, Bool.false_eq_true, ↓reduceIte] at hTr; cases hTr
    case aluReg op is64 rd rn rm sk sa =>
      rcases hValid with ⟨⟨hd32, hn32⟩, hm32⟩
      by_cases hEorSelf : (op == .eor && rn == rm && sa == 0) = true
      · simp only [hEorSelf, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [Bool.and_eq_true, beq_iff_eq] at hEorSelf
        rcases hEorSelf with ⟨⟨rfl, rfl⟩, rfl⟩
        simp only [stepArm64, hIns, arm_eor_self_zero, true_and]
        exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2,
          setArmGpr_rel hd32 rGpr ⟨rfl, rfl⟩, rVec, rCf, rZf⟩
      · simp only [hEorSelf, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [stepArm64, hIns, true_and]
        have hCongr : ((getArmAbsGpr st rn).isPublic && (getArmAbsGpr st rm).isPublic &&
            (if op == .adc || op == .sbc then st.cfPub else true)) = true →
            (evalArmAlu op is64 (getArmGpr s₁ rn) (applyArmShift is64 (getArmGpr s₁ rm) sk sa) s₁.cf s₁.zf).1 =
            (evalArmAlu op is64 (getArmGpr s₂ rn) (applyArmShift is64 (getArmGpr s₂ rm) sk sa) s₂.cf s₂.zf).1 ∧
            ((op == .adds || op == .subs) = true →
              (evalArmAlu op is64 (getArmGpr s₁ rn) (applyArmShift is64 (getArmGpr s₁ rm) sk sa) s₁.cf s₁.zf).2.1 =
              (evalArmAlu op is64 (getArmGpr s₂ rn) (applyArmShift is64 (getArmGpr s₂ rm) sk sa) s₂.cf s₂.zf).2.1 ∧
              (evalArmAlu op is64 (getArmGpr s₁ rn) (applyArmShift is64 (getArmGpr s₁ rm) sk sa) s₁.cf s₁.zf).2.2 =
              (evalArmAlu op is64 (getArmGpr s₂ rn) (applyArmShift is64 (getArmGpr s₂ rm) sk sa) s₂.cf s₂.zf).2.2) := by
          intro hp; simp only [Bool.and_eq_true] at hp
          have en := RelArmGpr_public_eq (getArmGpr_rel hn32 rGpr) hp.1.1
          have em := RelArmGpr_public_eq (getArmGpr_rel hm32 rGpr) hp.1.2
          exact evalArmAlu_pub_congr op is64 en (congrArg (fun x => applyArmShift is64 x sk sa) em)
            (fun hNeed => rCf (by
              by_cases hc : (op == .adc || op == .sbc) = true
              · simpa [hc] using hp.2
              · simp [hc] at hNeed))
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, ?_, rVec, ?_, ?_⟩
        · apply setArmGpr_rel hd32 rGpr
          by_cases hp : ((getArmAbsGpr st rn).isPublic && (getArmAbsGpr st rm).isPublic &&
              (if op == .adc || op == .sbc then st.cfPub else true)) = true
          · simp only [hp, ↓reduceIte, RelArmGpr]; exact (hCongr hp).1
          · simp only [hp, Bool.false_eq_true, ↓reduceIte, RelArmGpr]
        · by_cases hSf : (op == .adds || op == .subs) = true
          · simp only [hSf, ↓reduceIte]; intro hp; exact ((hCongr hp).2 hSf).1
          · simp only [hSf, Bool.false_eq_true, ↓reduceIte]
            intro hCfB
            have hKeep1 := @evalArmAlu_res_flags op is64 (getArmGpr s₁ rn)
              (applyArmShift is64 (getArmGpr s₁ rm) sk sa) s₁.cf s₁.zf
            have hKeep2 := @evalArmAlu_res_flags op is64 (getArmGpr s₂ rn)
              (applyArmShift is64 (getArmGpr s₂ rm) sk sa) s₂.cf s₂.zf
            simp only [hSf, Bool.false_eq_true, ↓reduceIte] at hKeep1 hKeep2
            rw [congrArg Prod.fst hKeep1, congrArg Prod.fst hKeep2, rCf hCfB]
        · by_cases hSf : (op == .adds || op == .subs) = true
          · simp only [hSf, ↓reduceIte]; intro hp; exact ((hCongr hp).2 hSf).2
          · simp only [hSf, Bool.false_eq_true, ↓reduceIte]
            intro hZfB
            have hKeep1 := @evalArmAlu_res_flags op is64 (getArmGpr s₁ rn)
              (applyArmShift is64 (getArmGpr s₁ rm) sk sa) s₁.cf s₁.zf
            have hKeep2 := @evalArmAlu_res_flags op is64 (getArmGpr s₂ rn)
              (applyArmShift is64 (getArmGpr s₂ rm) sk sa) s₂.cf s₂.zf
            simp only [hSf, Bool.false_eq_true, ↓reduceIte] at hKeep1 hKeep2
            rw [congrArg Prod.snd hKeep1, congrArg Prod.snd hKeep2, rZf hZfB]
    case aluImm op is64 rd rn imm =>
      rcases hValid with ⟨hd32, hn32⟩
      injection hTr with hS; subst hS
      simp only [stepArm64, hIns, true_and]
      have hCongr : ((getArmAbsGpr st rn).isPublic &&
          (if op == .adc || op == .sbc then st.cfPub else true)) = true →
          (evalArmAlu op is64 (getArmGpr s₁ rn) imm s₁.cf s₁.zf).1 =
          (evalArmAlu op is64 (getArmGpr s₂ rn) imm s₂.cf s₂.zf).1 ∧
          ((op == .adds || op == .subs) = true →
            (evalArmAlu op is64 (getArmGpr s₁ rn) imm s₁.cf s₁.zf).2.1 =
            (evalArmAlu op is64 (getArmGpr s₂ rn) imm s₂.cf s₂.zf).2.1 ∧
            (evalArmAlu op is64 (getArmGpr s₁ rn) imm s₁.cf s₁.zf).2.2 =
            (evalArmAlu op is64 (getArmGpr s₂ rn) imm s₂.cf s₂.zf).2.2) := by
        intro hp; simp only [Bool.and_eq_true] at hp
        exact evalArmAlu_pub_congr op is64 (RelArmGpr_public_eq (getArmGpr_rel hn32 rGpr) hp.1) rfl
          (fun hNeed => rCf (by
            by_cases hc : (op == .adc || op == .sbc) = true
            · simpa [hc] using hp.2
            · simp [hc] at hNeed))
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, ?_, rVec, ?_, ?_⟩
      · apply setArmGpr_rel hd32 rGpr
        by_cases hp : ((getArmAbsGpr st rn).isPublic &&
            (if op == .adc || op == .sbc then st.cfPub else true)) = true
        · simp only [hp, ↓reduceIte, RelArmGpr]; exact (hCongr hp).1
        · simp only [hp, Bool.false_eq_true, ↓reduceIte, RelArmGpr]
      · by_cases hSf : (op == .adds || op == .subs) = true
        · simp only [hSf, ↓reduceIte]; intro hp; exact ((hCongr hp).2 hSf).1
        · simp only [hSf, Bool.false_eq_true, ↓reduceIte]
          intro hCfB
          have hKeep1 := @evalArmAlu_res_flags op is64 (getArmGpr s₁ rn) imm s₁.cf s₁.zf
          have hKeep2 := @evalArmAlu_res_flags op is64 (getArmGpr s₂ rn) imm s₂.cf s₂.zf
          simp only [hSf, Bool.false_eq_true, ↓reduceIte] at hKeep1 hKeep2
          rw [congrArg Prod.fst hKeep1, congrArg Prod.fst hKeep2, rCf hCfB]
      · by_cases hSf : (op == .adds || op == .subs) = true
        · simp only [hSf, ↓reduceIte]; intro hp; exact ((hCongr hp).2 hSf).2
        · simp only [hSf, Bool.false_eq_true, ↓reduceIte]
          intro hZfB
          have hKeep1 := @evalArmAlu_res_flags op is64 (getArmGpr s₁ rn) imm s₁.cf s₁.zf
          have hKeep2 := @evalArmAlu_res_flags op is64 (getArmGpr s₂ rn) imm s₂.cf s₂.zf
          simp only [hSf, Bool.false_eq_true, ↓reduceIte] at hKeep1 hKeep2
          rw [congrArg Prod.snd hKeep1, congrArg Prod.snd hKeep2, rZf hZfB]
    case movWide isMovn is64 rd imm16 sh =>
      injection hTr with hS; subst hS
      simp only [stepArm64, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, ?_, rVec, rCf, rZf⟩
      apply setArmGpr_rel hValid rGpr
      by_cases hz : (!isMovn && imm16 == 0) = true
      · simp only [hz, ↓reduceIte, RelArmGpr]
        simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hz
        rcases hz with ⟨rfl, rfl⟩
        have hSh0 : (0 : UInt64) <<< UInt64.ofNat sh = 0 := by apply UInt64.eq_of_toBitVec_eq; simp
        have hm0 : maskGprWidth is64 0 = 0 := by cases is64 <;> rfl
        simp [hSh0, hm0]
      · simp [hz, RelArmGpr]
    case ubfm is64 rd rn immr imms =>
      rcases hValid with ⟨hd32, hn32⟩
      injection hTr with hS; subst hS
      simp only [stepArm64, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, ?_, rVec, rCf, rZf⟩
      apply setArmGpr_rel hd32 rGpr
      by_cases hp : (getArmAbsGpr st rn).isPublic = true
      · simp only [hp, ↓reduceIte, RelArmGpr]; rw [RelArmGpr_public_eq (getArmGpr_rel hn32 rGpr) hp]
      · simp [hp, RelArmGpr]
    case mulOp isUmulh rd rn rm =>
      have hd : st.dit = true := hAllowed (by simp [hIns, armRequiresDit])
      rcases hValid with ⟨⟨hd32, hn32⟩, hm32⟩
      injection hTr with hS; subst hS
      simp only [stepArm64, hIns, rDit1, rDit2, hd, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rfl, rfl, ?_, rVec, rCf, rZf⟩
      apply setArmGpr_rel hd32 rGpr
      by_cases hp : ((getArmAbsGpr st rn).isPublic && (getArmAbsGpr st rm).isPublic) = true
      · simp only [hp, ↓reduceIte, RelArmGpr]
        simp only [Bool.and_eq_true] at hp
        rw [RelArmGpr_public_eq (getArmGpr_rel hn32 rGpr) hp.1,
            RelArmGpr_public_eq (getArmGpr_rel hm32 rGpr) hp.2]
      · simp [hp, RelArmGpr]
    case csel cond isInv rd rn rm =>
      have hd : st.dit = true := hAllowed (by simp [hIns, armRequiresDit])
      rcases hValid with ⟨⟨hd32, hn32⟩, hm32⟩
      injection hTr with hS; subst hS
      simp only [stepArm64, hIns, rDit1, rDit2, hd, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rfl, rfl, ?_, rVec, rCf, rZf⟩
      apply setArmGpr_rel hd32 rGpr
      by_cases hp : (armCondIsPublic cond st && (getArmAbsGpr st rn).isPublic && (getArmAbsGpr st rm).isPublic) = true
      · simp only [hp, ↓reduceIte, RelArmGpr]
        simp only [Bool.and_eq_true] at hp
        rw [evalArmCond_public_eq hp.1.1 rCf rZf,
            RelArmGpr_public_eq (getArmGpr_rel hn32 rGpr) hp.1.2,
            RelArmGpr_public_eq (getArmGpr_rel hm32 rGpr) hp.2]
      · simp [hp, RelArmGpr]
    case ldp64 rt1 rt2 rn off =>
      rcases hValid with ⟨⟨ht1, ht2⟩, hn32⟩
      cases hPub : (getArmAbsGpr st rn).isPublic
      · simp [hPub] at hTr
      · simp only [hPub, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hRnEq := RelArmGpr_public_eq (getArmGpr_rel hn32 rGpr) hPub
        simp only [stepArm64, hIns, hRnEq, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, ?_, rVec, rCf, rZf⟩
        have r1 := setArmGpr_rel ht1 rGpr (orig := .secretVal)
          (v₁ := readMem64 s₁.mem (getArmGpr s₂ rn + off))
          (v₂ := readMem64 s₂.mem (getArmGpr s₂ rn + off)) trivial
        exact setArmGpr_rel (st := { st with gpr := setArmAbsGpr st rt1 .secretVal })
          (s₁ := { s₁ with gpr := setArmGpr s₁ rt1 (readMem64 s₁.mem (getArmGpr s₂ rn + off)) })
          (s₂ := { s₂ with gpr := setArmGpr s₂ rt1 (readMem64 s₂.mem (getArmGpr s₂ rn + off)) })
          ht2 r1 trivial
    case stp64 rt1 rt2 rn off =>
      rcases hValid with ⟨⟨_, _⟩, hn32⟩
      cases hPub : (getArmAbsGpr st rn).isPublic
      · simp [hPub] at hTr
      · simp only [hPub, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hRnEq := RelArmGpr_public_eq (getArmGpr_rel hn32 rGpr) hPub
        simp only [stepArm64, hIns, hRnEq, true_and]
        exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, rVec, rCf, rZf⟩
    case strbPost rt rn postOff =>
      rcases hValid with ⟨_, hn32⟩
      cases hPub : (getArmAbsGpr st rn).isPublic
      · simp [hPub] at hTr
      · simp only [hPub, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hRnEq := RelArmGpr_public_eq (getArmGpr_rel hn32 rGpr) hPub
        simp only [stepArm64, hIns, hRnEq, true_and]
        exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, setArmGpr_rel hn32 rGpr rfl, rVec, rCf, rZf⟩
    case ldrQ rt rn off =>
      rcases hValid with ⟨ht32, hn32⟩
      cases hPub : (getArmAbsGpr st rn).isPublic
      · simp [hPub] at hTr
      · simp only [hPub, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hRnEq := RelArmGpr_public_eq (getArmGpr_rel hn32 rGpr) hPub
        simp only [stepArm64, hIns, hRnEq, true_and]
        exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, RelArmVec_set ht32 rVec trivial, rCf, rZf⟩
    case strQ rt rn off =>
      rcases hValid with ⟨_, hn32⟩
      cases hPub : (getArmAbsGpr st rn).isPublic
      · simp [hPub] at hTr
      · simp only [hPub, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hRnEq := RelArmGpr_public_eq (getArmGpr_rel hn32 rGpr) hPub
        simp only [stepArm64, hIns, hRnEq, true_and]
        exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, rVec, rCf, rZf⟩
    case fmovDFromX vd xn =>
      rcases hValid with ⟨hvd, hxn⟩
      injection hTr with hS; subst hS
      simp only [stepArm64, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, ?_, rCf, rZf⟩
      apply RelArmVec_set hvd rVec
      by_cases hz : (getArmAbsGpr st xn == .zeroConst) = true
      · simp only [hz, ↓reduceIte, RelArmVec]
        have rx := getArmGpr_rel hxn rGpr
        rw [beq_iff_eq.mp hz] at rx
        rcases rx with ⟨x1, x2⟩
        simp [x1, x2, Vec128.zero]
      · simp only [hz, Bool.false_eq_true, ↓reduceIte]
        by_cases hp : (getArmAbsGpr st xn).isPublic = true
        · simp only [hp, ↓reduceIte, RelArmVec]
          rw [RelArmGpr_public_eq (getArmGpr_rel hxn rGpr) hp]
        · simp [hp, RelArmVec]
    case veor16b vd vn vm =>
      rcases hValid with ⟨⟨hvd, hvn⟩, hvm⟩
      by_cases hSelf : (vn == vm) = true
      · simp only [hSelf, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hEq := beq_iff_eq.mp hSelf; subst hEq
        have hx (w : UInt64) : w ^^^ w = 0 := by apply UInt64.eq_of_toBitVec_eq; simp
        simp only [stepArm64, hIns, hx, true_and]
        exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr,
          RelArmVec_set hvd rVec ⟨rfl, rfl⟩, rCf, rZf⟩
      · simp only [hSelf, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [stepArm64, hIns, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, ?_, rCf, rZf⟩
        apply RelArmVec_set hvd rVec
        by_cases hp : ((st.vec.get vn).isPublic && (st.vec.get vm).isPublic) = true
        · simp only [hp, ↓reduceIte, RelArmVec]
          simp only [Bool.and_eq_true] at hp
          rw [RelArmVec_public_eq (rVec vn hvn) hp.1, RelArmVec_public_eq (rVec vm hvm) hp.2]
        · simp [hp, RelArmVec]
    case vbcax16b vd vn vm va =>
      rcases hValid with ⟨⟨⟨hvd, hvn⟩, hvm⟩, hva⟩
      injection hTr with hS; subst hS
      simp only [stepArm64, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, ?_, rCf, rZf⟩
      apply RelArmVec_set hvd rVec
      by_cases hp : ((st.vec.get vn).isPublic && (st.vec.get vm).isPublic && (st.vec.get va).isPublic) = true
      · simp only [hp, ↓reduceIte, RelArmVec]
        simp only [Bool.and_eq_true] at hp
        rw [RelArmVec_public_eq (rVec vn hvn) hp.1.1,
            RelArmVec_public_eq (rVec vm hvm) hp.1.2,
            RelArmVec_public_eq (rVec va hva) hp.2]
      · simp [hp, RelArmVec]
    case veor3_16b vd vn vm va =>
      rcases hValid with ⟨⟨⟨hvd, hvn⟩, hvm⟩, hva⟩
      injection hTr with hS; subst hS
      simp only [stepArm64, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, ?_, rCf, rZf⟩
      apply RelArmVec_set hvd rVec
      by_cases hp : ((st.vec.get vn).isPublic && (st.vec.get vm).isPublic && (st.vec.get va).isPublic) = true
      · simp only [hp, ↓reduceIte, RelArmVec]
        simp only [Bool.and_eq_true] at hp
        rw [RelArmVec_public_eq (rVec vn hvn) hp.1.1,
            RelArmVec_public_eq (rVec vm hvm) hp.1.2,
            RelArmVec_public_eq (rVec va hva) hp.2]
      · simp [hp, RelArmVec]
    case vrax1_2d vd vn vm =>
      rcases hValid with ⟨⟨hvd, hvn⟩, hvm⟩
      injection hTr with hS; subst hS
      simp only [stepArm64, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, ?_, rCf, rZf⟩
      apply RelArmVec_set hvd rVec
      by_cases hp : ((st.vec.get vn).isPublic && (st.vec.get vm).isPublic) = true
      · simp only [hp, ↓reduceIte, RelArmVec]
        simp only [Bool.and_eq_true] at hp
        rw [RelArmVec_public_eq (rVec vn hvn) hp.1, RelArmVec_public_eq (rVec vm hvm) hp.2]
      · simp [hp, RelArmVec]
    case vxar_2d vd vn vm imm6 =>
      rcases hValid with ⟨⟨hvd, hvn⟩, hvm⟩
      injection hTr with hS; subst hS
      simp only [stepArm64, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, ?_, rCf, rZf⟩
      apply RelArmVec_set hvd rVec
      by_cases hp : ((st.vec.get vn).isPublic && (st.vec.get vm).isPublic) = true
      · simp only [hp, ↓reduceIte, RelArmVec]
        simp only [Bool.and_eq_true] at hp
        rw [RelArmVec_public_eq (rVec vn hvn) hp.1, RelArmVec_public_eq (rVec vm hvm) hp.2]
      · simp [hp, RelArmVec]
    case vpmull isHigh vd vn vm =>
      have hd : st.dit = true := hAllowed (by simp [hIns, armRequiresDit])
      rcases hValid with ⟨⟨hvd, hvn⟩, hvm⟩
      injection hTr with hS; subst hS
      simp only [stepArm64, hIns, rDit1, rDit2, hd, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rfl, rfl, rGpr, ?_, rCf, rZf⟩
      apply RelArmVec_set hvd rVec
      by_cases hp : ((st.vec.get vn).isPublic && (st.vec.get vm).isPublic) = true
      · simp only [hp, ↓reduceIte, RelArmVec]
        simp only [Bool.and_eq_true] at hp
        rw [RelArmVec_public_eq (rVec vn hvn) hp.1, RelArmVec_public_eq (rVec vm hvm) hp.2]
      · simp [hp, RelArmVec]
    case vtrn is128 second elementBytes vd vn vm =>
      rcases hValid with ⟨⟨hvd, hvn⟩, hvm⟩
      injection hTr with hS; subst hS
      simp only [stepArm64, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, ?_, rCf, rZf⟩
      apply RelArmVec_set hvd rVec
      by_cases hp : ((st.vec.get vn).isPublic && (st.vec.get vm).isPublic) = true
      · simp only [hp, ↓reduceIte, RelArmVec]
        simp only [Bool.and_eq_true] at hp
        rw [RelArmVec_public_eq (rVec vn hvn) hp.1, RelArmVec_public_eq (rVec vm hvm) hp.2]
      · simp [hp, RelArmVec]
    case vext16b vd vn vm imm4 =>
      rcases hValid with ⟨⟨hvd, hvn⟩, hvm⟩
      injection hTr with hS; subst hS
      simp only [stepArm64, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, ?_, rCf, rZf⟩
      apply RelArmVec_set hvd rVec
      by_cases hp : ((st.vec.get vn).isPublic && (st.vec.get vm).isPublic) = true
      · simp only [hp, ↓reduceIte, RelArmVec]
        simp only [Bool.and_eq_true] at hp
        rw [RelArmVec_public_eq (rVec vn hvn) hp.1, RelArmVec_public_eq (rVec vm hvm) hp.2]
      · simp [hp, RelArmVec]
    case bCond cond targetPc =>
      by_cases hBad : (!armCondIsPublic cond st || decide (targetPc < 0) || decide (targetPc.toNat ≥ 4096)) = true
      · simp [hBad] at hTr
      · simp only [hBad, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, not_or, Bool.not_eq_false] at hBad
        rcases hBad with ⟨⟨hCondPub, hNotNeg⟩, _⟩
        have hGe0 : targetPc ≥ 0 := by omega
        have hCondEq := evalArmCond_public_eq hCondPub rCf rZf
        simp only [stepArm64, hIns, decide_eq_true hGe0, Bool.and_true, true_and]
        by_cases hTaken : evalArmCond cond s₁ = true
        · have hTaken2 : evalArmCond cond s₂ = true := hCondEq ▸ hTaken
          simp only [hTaken, hTaken2, ↓reduceIte]
          exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, rVec, rCf, rZf⟩
        · have hTakenF1 : evalArmCond cond s₁ = false := Bool.eq_false_iff.mpr hTaken
          have hTakenF2 : evalArmCond cond s₂ = false := hCondEq ▸ hTakenF1
          simp only [hTakenF1, hTakenF2, Bool.false_eq_true, ↓reduceIte]
          exact Or.inr ⟨_, List.Mem.tail _ (List.Mem.head _), rfl, hH1, hH2, rDit1, rDit2, rGpr, rVec, rCf, rZf⟩
    case cbzOrTbz _ => cases hTr
    case udivOrSdiv _ => cases hTr
    case varShiftReg _ => cases hTr
    case regOffsetMem _ => cases hTr

private theorem runArm64_of_halted (prog : List (DecodedInstr Arm64Instr)) (fuel : Nat)
    {s : Arm64State} (hHalt : s.halted = true) :
    runArm64 prog fuel s = (s, []) := by
  cases fuel with
  | zero => rfl
  | succ k => simp [runArm64, hHalt]

private theorem runArm64_invariant_sound {c : FuncContract}
    {prog : List (DecodedInstr Arm64Instr)} {inv : PcMap Arm64AbsState}
    {s₁₀ s₂₀ : Arm64State}
    (hAll : inv.all (fun pc st =>
      match (buildProgMap prog).get pc with
      | none => false
      | some d =>
        match transferArm64Instr c d st with
        | none => false
        | some succs =>
          succs.all (fun (npc, nst) =>
            match inv.get npc with
            | none => false
            | some dstSt => nst.le dstSt)) = true) :
    ∀ (fuel : Nat) {s₁ s₂ : Arm64State} {st : Arm64AbsState},
      inv.get s₁.pc = some st →
      RelArm64 s₁₀ s₂₀ st s₁ s₂ →
      let (s₁f, tr₁) := runArm64 prog fuel s₁
      let (s₂f, tr₂) := runArm64 prog fuel s₂
      tr₁ = tr₂ ∧
      (∀ obs ∈ tr₁, obs.isDoitSafe = true) ∧
      ((s₁f.halted = true ∧ s₂f.halted = true ∧ Arm64ExitHygiene c s₁₀ s₂₀ s₁f s₂f) ∨
       (s₁f.halted = false ∧ s₂f.halted = false))
  | 0, s₁, s₂, st, _, hRel =>
    ⟨rfl, (fun _ h => nomatch h), Or.inr ⟨hRel.2.1, hRel.2.2.1⟩⟩
  | fuel + 1, s₁, s₂, st, hInvPc, hRel => by
    have hPcLt : s₁.pc < 4096 := PcMap.get_some_lt hInvPc
    have hPred := PcMap.all_get hAll hInvPc
    rw [buildProgMap_get_eq prog hPcLt] at hPred
    cases hFind : findInstrAtPc s₁.pc prog with
    | none => simp [hFind] at hPred
    | some d =>
      simp only [hFind] at hPred
      cases hTr : transferArm64Instr c d st with
      | none => simp [hTr] at hPred
      | some succs =>
        simp only [hTr, List.all_eq_true] at hPred
        have hFind2 : findInstrAtPc s₂.pc prog = some d := hRel.1 ▸ hFind
        have hOffEq : s₁.pc = d.offset := (findInstrAtPc_offset hFind).symm
        have hStep := transferArm64Instr_step_sound hRel hOffEq hTr
        rcases stp1 : stepArm64 d s₁ with ⟨s₁', obs₁⟩
        rcases stp2 : stepArm64 d s₂ with ⟨s₂', obs₂⟩
        simp only [stp1, stp2] at hStep
        rcases hStep with ⟨hObsEq, hDoit, hExitOrCont⟩
        simp only [runArm64, hRel.2.1, hRel.2.2.1, Bool.false_eq_true, ↓reduceIte, hFind, hFind2, stp1, stp2]
        rcases hExitOrCont with ⟨hh1', hh2', hHyg⟩ | ⟨nst, hMemSucc, hRel'⟩
        · rw [runArm64_of_halted prog fuel hh1', runArm64_of_halted prog fuel hh2']
          refine ⟨congrArg (· :: []) hObsEq, ?_, Or.inl ⟨hh1', hh2', hHyg⟩⟩
          intro o ho; simp at ho; subst ho; exact hDoit
        · have hSuccOk := hPred (s₁'.pc, nst) hMemSucc
          cases hInvNext : inv.get s₁'.pc with
          | none => simp [hInvNext] at hSuccOk
          | some dstSt =>
            simp only [hInvNext] at hSuccOk
            have hRelDst := RelArm64_mono hRel' hSuccOk
            have ih := runArm64_invariant_sound hAll fuel hInvNext hRelDst
            rcases hr1 : runArm64 prog fuel s₁' with ⟨s₁f, tr₁⟩
            rcases hr2 : runArm64 prog fuel s₂' with ⟨s₂f, tr₂⟩
            simp only [hr1, hr2] at ih
            rcases ih with ⟨hTrEq, hTrDoit, hPost⟩
            refine ⟨by rw [hObsEq, hTrEq], ?_, hPost⟩
            intro o ho
            rcases List.mem_cons.mp ho with rfl | hRest
            · exact hDoit
            · exact hTrDoit o hRest

/-- **3-Way Hardware Constant-Time Noninterference + AAPCS64 ABI Hygiene Soundness (`AArch64`):**
    Whenever `checkArm64ThreeWayNI code c = true`, for ANY two initial machine states `(s₁, s₂)`
    satisfying `Arm64ContractInit c s₁ s₂` and ANY execution fuel `fuel`:
    1. **`PC-NI` & `Mem-NI`:** `tr₁ = tr₂` (every executed PC and `(addr, width)` memory access matches),
    2. **`DOIT-NI`:** Every executed instruction has `obs.isDoitSafe = true`,
    3. **`ABI & Epilogue Zeroization`:** If execution halts (`ret`), both states halt together and
       satisfy `Arm64ExitHygiene c s₁ s₂ s₁f s₂f` (`x19..x30` & `v8..v15` preserved, scratch NEON
       `v0..v7, v16..v31` secret registers wiped, scratch GPRs wiped). -/
theorem checkArm64ThreeWayNI_sound {code : List UInt8} {c : FuncContract}
    (hCheck : checkArm64ThreeWayNI code c = true)
    {s₁ s₂ : Arm64State} (hInit : Arm64ContractInit c s₁ s₂) (fuel : Nat) :
    ∃ prog : List (DecodedInstr Arm64Instr),
      decodeArm64Stream code = some prog ∧
      let (s₁f, tr₁) := runArm64 prog fuel s₁
      let (s₂f, tr₂) := runArm64 prog fuel s₂
      tr₁ = tr₂ ∧
      (∀ obs ∈ tr₁, obs.isDoitSafe = true) ∧
      ((s₁f.halted = true ∧ s₂f.halted = true ∧ Arm64ExitHygiene c s₁ s₂ s₁f s₂f) ∨
       (s₁f.halted = false ∧ s₂f.halted = false)) := by
  unfold checkArm64ThreeWayNI at hCheck
  cases hDec : decodeArm64Stream code with
  | none => simp [hDec] at hCheck
  | some prog =>
    simp only [hDec] at hCheck
    cases prog with
    | nil => simp at hCheck
    | cons d0 ds =>
      cases hInf : inferArm64Invariant (d0 :: ds) c with
      | none => simp [hInf] at hCheck
      | some inv =>
        simp only [hInf, verifyArm64Invariant, Bool.and_eq_true] at hCheck
        rcases hCheck with ⟨hEntry, hAll⟩
        cases hInv0 : inv.get 0 with
        | none => simp [hInv0] at hEntry
        | some st0 =>
          simp only [hInv0] at hEntry
          have hRel0 := RelArm64_mono (RelArm64_init hInit) hEntry
          have hInvS1 : inv.get s₁.pc = some st0 := hInit.1 ▸ hInv0
          exact ⟨d0 :: ds, rfl, runArm64_invariant_sound hAll fuel hInvS1 hRel0⟩

/-- Unified 3-Way Constant-Time NI + ABI Hygiene semantic postcondition for an `ELF64` `.text` slice. -/
def ElfSliceThreeWayNISafe (slice : ElfFuncSlice) (c : FuncContract) : Prop :=
  (slice.machine = elfMachineX86_64 ∧
   ∀ (s₁ s₂ : X86State), X86ContractInit c s₁ s₂ → ∀ (fuel : Nat),
     ∃ prog : List (DecodedInstr X86Instr),
       decodeX86Stream slice.code = some prog ∧
       let (s₁f, tr₁) := runX86 prog fuel s₁
       let (s₂f, tr₂) := runX86 prog fuel s₂
       tr₁ = tr₂ ∧
       (∀ obs ∈ tr₁, obs.isDoitSafe = true) ∧
       ((s₁f.halted = true ∧ s₂f.halted = true ∧ X86ExitHygiene c s₁ s₂ s₁f s₂f) ∨
        (s₁f.halted = false ∧ s₂f.halted = false))) ∨
  (slice.machine = elfMachineAArch64 ∧
   ∀ (s₁ s₂ : Arm64State), Arm64ContractInit c s₁ s₂ → ∀ (fuel : Nat),
     ∃ prog : List (DecodedInstr Arm64Instr),
       decodeArm64Stream slice.code = some prog ∧
       let (s₁f, tr₁) := runArm64 prog fuel s₁
       let (s₂f, tr₂) := runArm64 prog fuel s₂
       tr₁ = tr₂ ∧
       (∀ obs ∈ tr₁, obs.isDoitSafe = true) ∧
       ((s₁f.halted = true ∧ s₂f.halted = true ∧ Arm64ExitHygiene c s₁ s₂ s₁f s₂f) ∨
        (s₁f.halted = false ∧ s₂f.halted = false)))

theorem checkElfSliceThreeWayNI_sound {slice : ElfFuncSlice} {c : FuncContract}
    (hCheck : checkElfSliceThreeWayNI slice c = true) :
    ElfSliceThreeWayNISafe slice c := by
  unfold checkElfSliceThreeWayNI at hCheck
  by_cases hx : slice.machine == elfMachineX86_64
  · simp only [hx, ↓reduceIte] at hCheck
    exact Or.inl ⟨beq_iff_eq.mp hx, fun _ _ hInit fuel => checkX86ThreeWayNI_sound hCheck hInit fuel⟩
  · simp only [hx, Bool.false_eq_true, ↓reduceIte] at hCheck
    by_cases ha : slice.machine == elfMachineAArch64
    · simp only [ha, ↓reduceIte] at hCheck
      exact Or.inr ⟨beq_iff_eq.mp ha, fun _ _ hInit fuel => checkArm64ThreeWayNI_sound hCheck hInit fuel⟩
    · simp [ha] at hCheck

/-- **Master `ELF64` Binary 3-Way Constant-Time NI + ABI Hygiene Soundness Theorem (`§5`):**
    If `checkElfFuncThreeWayNI elfBytes symName c = true`, then `symName` resolves inside `elfBytes`
    to a valid `.text` subslice `slice` (`extractElfFuncBytes_in_text_section`) whose decoded
    machine-code semantics satisfies `PC-NI`, `Mem-NI`, `DOIT-NI`, callee-saved preservation, and
    epilogue scratch register zeroization (`ElfSliceThreeWayNISafe slice c`)! -/
theorem checkElfFuncThreeWayNI_sound {elfBytes : Bytes} {symName : String} {c : FuncContract}
    (hCheck : checkElfFuncThreeWayNI elfBytes symName c = true) :
    ∃ slice : ElfFuncSlice,
      extractElfFuncBytes elfBytes symName = some slice ∧
      ElfSliceOk elfBytes slice ∧
      ElfSliceThreeWayNISafe slice c := by
  unfold checkElfFuncThreeWayNI at hCheck
  cases hExt : extractElfFuncBytes elfBytes symName with
  | none => simp [hExt] at hCheck
  | some slice =>
    simp only [hExt] at hCheck
    exact ⟨slice, rfl, extractElfFuncBytes_in_text_section elfBytes symName slice hExt,
      checkElfSliceThreeWayNI_sound hCheck⟩

/-! ### Certificate-checked verification: the invariant is supplied, never inferred in the kernel -/

/-- `x86_64` check against a supplied invariant: decode, then verify inductiveness. Inference is
    not on the trusted path; `verifyX86Invariant` alone carries soundness. -/
def checkX86WithInv (code : List UInt8) (c : FuncContract) (inv : PcMap X86AbsState) : Bool :=
  match decodeX86Stream code with
  | none => false
  | some prog =>
    match prog with
    | [] => false
    | _ :: _ => verifyX86Invariant prog c inv

/-- `AArch64` check against a supplied invariant. -/
def checkArm64WithInv (code : List UInt8) (c : FuncContract) (inv : PcMap Arm64AbsState) : Bool :=
  match decodeArm64Stream code with
  | none => false
  | some prog =>
    match prog with
    | [] => false
    | _ :: _ => verifyArm64Invariant prog c inv

theorem checkX86WithInv_sound {code : List UInt8} {c : FuncContract} {inv : PcMap X86AbsState}
    (hCheck : checkX86WithInv code c inv = true)
    {s₁ s₂ : X86State} (hInit : X86ContractInit c s₁ s₂) (fuel : Nat) :
    ∃ prog : List (DecodedInstr X86Instr),
      decodeX86Stream code = some prog ∧
      let (s₁f, tr₁) := runX86 prog fuel s₁
      let (s₂f, tr₂) := runX86 prog fuel s₂
      tr₁ = tr₂ ∧
      (∀ obs ∈ tr₁, obs.isDoitSafe = true) ∧
      ((s₁f.halted = true ∧ s₂f.halted = true ∧ X86ExitHygiene c s₁ s₂ s₁f s₂f) ∨
       (s₁f.halted = false ∧ s₂f.halted = false)) := by
  unfold checkX86WithInv at hCheck
  cases hDec : decodeX86Stream code with
  | none => simp [hDec] at hCheck
  | some prog =>
    simp only [hDec] at hCheck
    cases prog with
    | nil => simp at hCheck
    | cons d0 ds =>
      simp only [verifyX86Invariant, Bool.and_eq_true] at hCheck
      rcases hCheck with ⟨hEntry, hAll⟩
      cases hInv0 : inv.get 0 with
      | none => simp [hInv0] at hEntry
      | some st0 =>
        simp only [hInv0] at hEntry
        have hRel0 := RelX86_mono (RelX86_init hInit) hEntry
        have hInvS1 : inv.get s₁.pc = some st0 := hInit.1 ▸ hInv0
        exact ⟨d0 :: ds, rfl, runX86_invariant_sound hInit hAll fuel hInvS1 hRel0⟩

theorem checkArm64WithInv_sound {code : List UInt8} {c : FuncContract} {inv : PcMap Arm64AbsState}
    (hCheck : checkArm64WithInv code c inv = true)
    {s₁ s₂ : Arm64State} (hInit : Arm64ContractInit c s₁ s₂) (fuel : Nat) :
    ∃ prog : List (DecodedInstr Arm64Instr),
      decodeArm64Stream code = some prog ∧
      let (s₁f, tr₁) := runArm64 prog fuel s₁
      let (s₂f, tr₂) := runArm64 prog fuel s₂
      tr₁ = tr₂ ∧
      (∀ obs ∈ tr₁, obs.isDoitSafe = true) ∧
      ((s₁f.halted = true ∧ s₂f.halted = true ∧ Arm64ExitHygiene c s₁ s₂ s₁f s₂f) ∨
       (s₁f.halted = false ∧ s₂f.halted = false)) := by
  unfold checkArm64WithInv at hCheck
  cases hDec : decodeArm64Stream code with
  | none => simp [hDec] at hCheck
  | some prog =>
    simp only [hDec] at hCheck
    cases prog with
    | nil => simp at hCheck
    | cons d0 ds =>
      simp only [verifyArm64Invariant, Bool.and_eq_true] at hCheck
      rcases hCheck with ⟨hEntry, hAll⟩
      cases hInv0 : inv.get 0 with
      | none => simp [hInv0] at hEntry
      | some st0 =>
        simp only [hInv0] at hEntry
        have hRel0 := RelArm64_mono (RelArm64_init hInit) hEntry
        have hInvS1 : inv.get s₁.pc = some st0 := hInit.1 ▸ hInv0
        exact ⟨d0 :: ds, rfl, runArm64_invariant_sound hAll fuel hInvS1 hRel0⟩

/-- An invariant certificate for one symbol. -/
inductive InvCert where
  | x86 (inv : PcMap X86AbsState)
  | arm (inv : PcMap Arm64AbsState)

/-- Architecture-dispatching certificate check for one slice. -/
def checkElfSliceWithCert (slice : ElfFuncSlice) (c : FuncContract) : InvCert → Bool
  | .x86 inv => slice.machine == elfMachineX86_64 && checkX86WithInv slice.code c inv
  | .arm inv => slice.machine == elfMachineAArch64 && checkArm64WithInv slice.code c inv

theorem checkElfSliceWithCert_sound {slice : ElfFuncSlice} {c : FuncContract} {cert : InvCert}
    (hCheck : checkElfSliceWithCert slice c cert = true) :
    ElfSliceThreeWayNISafe slice c := by
  cases cert with
  | x86 inv =>
    simp only [checkElfSliceWithCert, Bool.and_eq_true, beq_iff_eq] at hCheck
    exact Or.inl ⟨hCheck.1, fun _ _ hInit fuel => checkX86WithInv_sound hCheck.2 hInit fuel⟩
  | arm inv =>
    simp only [checkElfSliceWithCert, Bool.and_eq_true, beq_iff_eq] at hCheck
    exact Or.inr ⟨hCheck.1, fun _ _ hInit fuel => checkArm64WithInv_sound hCheck.2 hInit fuel⟩

/-- The check for the `i`-th slice against the `i`-th contract and the `i`-th certificate. -/
def certSliceAt (slices : List ElfFuncSlice) (contracts : List FuncContract)
    (certs : List InvCert) (i : Nat) : Bool :=
  match slices[i]?, contracts[i]?, certs[i]? with
  | some s, some c, some k => (s.name == c.symName) && checkElfSliceWithCert s c k
  | _, _, _ => false

/-- Per-index certificate checks give the name match and the semantic postcondition at every index. -/
theorem certSliceAt_sound {slices : List ElfFuncSlice} {contracts : List FuncContract}
    {certs : List InvCert}
    (hAt : ∀ i, i < slices.length → certSliceAt slices contracts certs i = true)
    (i : Nat) (hs : i < slices.length) (hc : i < contracts.length) :
    slices[i].name = contracts[i].symName ∧ ElfSliceThreeWayNISafe slices[i] contracts[i] := by
  have h := hAt i hs
  unfold certSliceAt at h
  rw [List.getElem?_eq_getElem hs, List.getElem?_eq_getElem hc] at h
  cases hk : certs[i]? with
  | none => rw [hk] at h; cases h
  | some k =>
    rw [hk] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h.1, checkElfSliceWithCert_sound h.2⟩

/-- An empty certificate proves nothing: the entry state is missing. -/
theorem empty_certificate_rejected (code : List UInt8) (c : FuncContract) :
    checkX86WithInv code c PcMap.empty = false := by
  unfold checkX86WithInv
  cases decodeX86Stream code with
  | none => rfl
  | some prog =>
    cases prog with
    | nil => rfl
    | cons d ds => rfl

/-! Semantic anchors. The baseless address distinction follows `Ea.base` /
`Ea.index` in jyh/x86lean (`X86/Syntax.lean`, Apache-2.0). UBFM's
nonwrapping extraction and wrapping insertion follow the ASL-derived
`exec_bitfield` in leanprover/LNSym (`Arm/Insts/DPI/Bitfield.lean`,
Amazon.com, Inc. or its affiliates, Apache-2.0). These are local anchors,
not a claim that either upstream repository was imported or proved equivalent.
-/
theorem tooth_sib_absolute_decode :
    decodeX86ModRM [0x04, 0x25, 0xff, 0xff, 0xff, 0xff] 0 0 0 =
      some (0, .mem (.absDisp 0xffffffffffffffff), 6) := by decide +kernel

theorem tooth_sib_absolute_independent (s t : X86State) (pc : Nat) (d : UInt32) :
    evalX86Addr s pc (.absDisp (signExt32To64 d)) = signExt32To64 d ∧
    evalX86Addr s pc (.absDisp (signExt32To64 d)) =
      evalX86Addr t pc (.absDisp (signExt32To64 d)) := ⟨rfl, rfl⟩

theorem tooth_ubfm_extract (s : Arm64State) :
    (stepArm64 ⟨0, 4, .ubfm true 0 1 4 7⟩ s).1.gpr.get 0 =
      ((s.gpr.get 1 >>> 4) &&& 15) := by rfl

theorem tooth_ubfm_insert (s : Arm64State) :
    (stepArm64 ⟨0, 4, .ubfm true 0 1 12 3⟩ s).1.gpr.get 0 =
      ((s.gpr.get 1 &&& 15) <<< 52) := by rfl

theorem tooth_ubfm_illegal_n : decodeArm64Word 0 0xD3001C20 = none := by decide +kernel

theorem tooth_dit_sensitive_mul (s : Arm64State) :
    (stepArm64 ⟨0, 4, .mulOp false 2 0 1⟩ s).2.isDoitSafe = s.dit := by rfl

theorem tooth_msr_dit_clears (s : Arm64State) :
    (stepArm64 ⟨0, 4, .msrDit 0⟩ s).1.dit = false := by rfl

theorem tooth_dit_disabled_rejected (c : FuncContract) (st : Arm64AbsState) :
    transferArm64Instr c ⟨0, 4, .mulOp false 2 0 1⟩ { st with dit := false } = none := by rfl

/-- `#tooth`: without the `DOITM` assumption in the contract, `cmovcc` (here `cmove rax, rcx`) is
    rejected in every abstract state, whatever the publicity of its condition and operands. -/
theorem tooth_x86_cmovcc_rejected_without_doit (c : FuncContract) (st : X86AbsState) :
    transferX86Instr { c with doitEnabled := false } ⟨0, 4, .cmovcc 4 true 0 1⟩ st = none := by rfl

/-- With the `DOITM` assumption the same instruction is accepted. -/
theorem x86_cmovcc_accepted_with_doit (c : FuncContract) (st : X86AbsState) :
    (transferX86Instr { c with doitEnabled := true } ⟨0, 4, .cmovcc 4 true 0 1⟩ st).isSome =
      true := by rfl

/-- `#tooth`: a `cmovcc` whose condition code is outside `{2, 3, 4, 5}` (here `cmovo`, code `0`)
    is rejected under every contract and abstract state. -/
theorem tooth_x86_cmovcc_unsupported_cc_rejected (c : FuncContract) (st : X86AbsState) :
    transferX86Instr c ⟨0, 4, .cmovcc 0 true 0 1⟩ st = none := by rfl

/-- `#tooth`: a `jcc` whose condition code is outside `{2, 3, 4, 5}` (here `jo`, code `0`; also
    `js`, code `8`) is rejected under every contract and abstract state, including states in which
    every tracked flag is public. -/
theorem tooth_x86_jcc_unsupported_cc_rejected (c : FuncContract) (st : X86AbsState) :
    transferX86Instr c ⟨0, 2, .jcc 0 0⟩ st = none ∧
    transferX86Instr c ⟨0, 2, .jcc 8 0⟩ { st with cfPub := true, zfPub := true, ofPub := true } =
      none := ⟨by rfl, by rfl⟩

/-- Signed-multiply flags. `(-1) * 2 = -2` fits in 64 bits, so `CF` is clear although the unsigned
    product exceeds `2^64`; `2^62 * 2 = 2^63` does not fit in a signed 64-bit word, so `CF` is set
    although the unsigned product is below `2^64`. -/
theorem evalX86Alu_imul2_signed_overflow :
    evalX86Alu .imul2 true 0xFFFFFFFFFFFFFFFF 2 false = (0xFFFFFFFFFFFFFFFE, false, false) ∧
    evalX86Alu .imul2 true 0x4000000000000000 2 false = (0x8000000000000000, true, false) := by
  decide +kernel

/-- `#tooth`: the unsigned-overflow reading (`an * bn ≥ 2^64`) disagrees with the signed flag on
    both vectors of `evalX86Alu_imul2_signed_overflow`. -/
theorem tooth_imul2_flag_is_not_unsigned_overflow :
    imulSignedOverflow (2 ^ 64) 0xFFFFFFFFFFFFFFFF 2 ≠
      decide (0xFFFFFFFFFFFFFFFF * 2 ≥ 2 ^ 64) ∧
    imulSignedOverflow (2 ^ 64) 0x4000000000000000 2 ≠
      decide (0x4000000000000000 * 2 ≥ 2 ^ 64) := by
  decide +kernel

/-- Two-operand `imul` writes the same value to `CF` and `OF`. -/
theorem stepX86_imul2_cf_eq_of (is64 : Bool) (dst src : Nat) (s : X86State) :
    (stepX86 ⟨0, 4, .aluRegReg .imul2 is64 dst src⟩ s).1.cf =
      (stepX86 ⟨0, 4, .aluRegReg .imul2 is64 dst src⟩ s).1.ofFlag := by rfl

/-- One-operand `mul` / `imul` writes the same value to `CF` and `OF`. -/
theorem stepX86_mulOneOp_cf_eq_of (isSigned is64 : Bool) (src : Nat) (s : X86State) :
    (stepX86 ⟨0, 3, .mulOneOp isSigned is64 src⟩ s).1.cf =
      (stepX86 ⟨0, 3, .mulOneOp isSigned is64 src⟩ s).1.ofFlag := by rfl

/-- One-operand multiply vectors on the helper level: unsigned `0xFFFFFFFF * 2` at 32 bits has a
    nonzero upper half (`EDX = 1`), while the signed reading `(-1) * 2 = -2` does not overflow. -/
theorem mulOneOp_32bit_flag_vectors :
    (0xFFFFFFFF * 2) / 0x100000000 = 1 ∧
    imulSignedOverflow 0x100000000 0xFFFFFFFF 2 = false ∧
    imulSignedOverflow 0x100000000 0x40000000 2 = true := by
  decide +kernel

/-- Immediate arithmetic right shift is outside the decoder's supported subset. -/
theorem tooth_x86_sar_rejected :
    decodeX86Stream [0x48, 0xc1, 0xf8, 0x01, 0xc3] = none := by decide +kernel

/-- Every shift/rotate forgets CF/OF publicity, including zero counts. This conservative
    transfer prevents subsequent carry/overflow consumers from treating secret flags as public. -/
theorem x86_shift_flag_taint (c : FuncContract) (st : X86AbsState)
    (sk : X86ShiftKind) (is64 : Bool) (dst cnt : Nat) (hdst : dst < 16) :
    (transferX86Instr c ⟨0, 4, .shiftImm sk is64 dst cnt⟩ st).map
      (fun xs => xs.map (fun x => (x.2.cfPub, x.2.ofPub))) = some [(false, false)] := by
  simp [transferX86Instr, x86InstrRegsValid, hdst]

/-- Effective count zero preserves all tracked flags. -/
theorem x86_shift_zero_flags (s : X86State) (sk : X86ShiftKind) (is64 : Bool) (dst : Nat) :
    let t := (stepX86 ⟨0, 4, .shiftImm sk is64 dst 0⟩ s).1
    t.cf = s.cf ∧ t.ofFlag = s.ofFlag ∧ t.zf = s.zf := by
  cases is64 <;> cases sk <;> simp [stepX86, evalX86Shift]

/-- Executed one-operand multiply: the unsigned high half and signed sign extension differ. -/
theorem x86_mulOneOp_executed_vectors :
    let s : X86State := ⟨0, ((Bank16.const 0).set 0 0xffffffff).set 1 2,
      Bank16.const Vec256.zero, false, false, false, false, false, fun _ => 0⟩
    let u := (stepX86 ⟨0, 3, .mulOneOp false false 1⟩ s).1
    let i := (stepX86 ⟨0, 3, .mulOneOp true false 1⟩ s).1
    u.gpr.get 0 = 0xfffffffe ∧ u.gpr.get 2 = 1 ∧ u.cf = true ∧ u.ofFlag = true ∧
    i.gpr.get 0 = 0xfffffffe ∧ i.gpr.get 2 = 0xffffffff ∧ i.cf = false ∧ i.ofFlag = false := by
  decide +kernel

/-- A carry branch after a multiply or shift of secret input is rejected. -/
theorem tooth_x86_secret_arithmetic_flags_rejected :
    checkX86ThreeWayNI [0x48, 0x0f, 0xaf, 0xc1, 0x72, 0x00, 0xc3]
      (mkContract "imul_flags" [4]) = false ∧
    checkX86ThreeWayNI [0x48, 0xf7, 0xe1, 0x72, 0x00, 0xc3]
      (mkContract "mul_flags" [4]) = false ∧
    checkX86ThreeWayNI [0x48, 0xc1, 0xe0, 0x01, 0x72, 0x00, 0xc3]
      (mkContract "shift_flags" [4]) = false := by
  decide +kernel

/-- Rotations preserve ZF taint even when their register operand is public. -/
theorem x86_rotate_preserves_zf_taint (c : FuncContract) (st : X86AbsState)
    (is64 : Bool) (dst cnt : Nat) (hdst : dst < 16) :
    (transferX86Instr c ⟨0, 4, .shiftImm .ror is64 dst cnt⟩ st).map
      (fun xs => xs.map (fun x => x.2.zfPub)) = some [st.zfPub] := by
  simp [transferX86Instr, x86InstrRegsValid, hdst, x86ShiftPreservesZf]

/-- A public rotate does not erase secret ZF from an earlier operation. -/
theorem tooth_x86_rotate_cannot_launder_secret_zf :
    checkX86ThreeWayNI
      [0x48, 0x83, 0xc0, 0x01, 0x48, 0xc1, 0xc9, 0x01, 0x74, 0x00, 0xc3]
      (mkContract "rotate_zf" [4, 1]) = false := by decide +kernel

/-- `#tooth`: `xor r8d, r8d; inc rax; adox r8, r9; mov rcx, [rdi + r8*8]; ret` (`45 31 c0; 48 ff c0;
    f3 4d 0f 38 f6 c1; 4a 8b 0c c7; c3`) leaks the signed overflow of secret `rax` (`0` vs
    `0x7fffffffffffffff`) into the memory load address (`rdi` vs `rdi + 8`) and is rejected (`false`)
    by `checkX86ThreeWayNI`. -/
theorem tooth_x86_inc_adox_secret_overflow_rejected :
    let code : List UInt8 :=
      [0x45, 0x31, 0xC0, 0x48, 0xFF, 0xC0, 0xF3, 0x4D, 0x0F, 0x38, 0xF6, 0xC1,
       0x4A, 0x8B, 0x0C, 0xC7, 0xC3]
    checkX86ThreeWayNI code (mkContract "inc_adox_leak" [4, 7, 8, 9]) = false ∧
    (match decodeX86Stream code with
     | none => false
     | some prog =>
       let mkS (rax : UInt64) : X86State :=
         ⟨0, ((Bank16.const 0).set 7 0x1000).set 0 rax, Bank16.const Vec256.zero,
          false, false, false, false, false, fun _ => 0⟩
       (runX86 prog 8 (mkS 0)).2 != (runX86 prog 8 (mkS 0x7FFFFFFFFFFFFFFF)).2) = true := by
  decide +kernel

/-- `#tooth`: 32-bit `cmove eax, ecx` (`0f 44 c1`) zero-extends `eax` into `rax` even when `ZF = 0`
    (condition false), clearing bits `63:32` of `rax` exactly per Intel SDM. -/
theorem tooth_x86_cmovcc_32bit_untaken_zero_extends :
    let s : X86State :=
      ⟨0, ((Bank16.const 0).set 0 0xDEADBEEF12345678).set 1 0x99999999,
       Bank16.const Vec256.zero, false, false, false, false, false, fun _ => 0⟩
    (stepX86 ⟨0, 3, .cmovcc 4 false 0 1⟩ s).1.gpr.get 0 = 0x0000000012345678 := by
  decide +kernel

end Qsag
