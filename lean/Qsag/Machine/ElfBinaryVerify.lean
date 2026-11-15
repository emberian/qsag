module
/-
# Qsag.Machine.ElfBinaryVerify — Compiled `.rlib` / `ELF64` Machine-Code Parser, 3-Way Constant-Time NI & ABI Checker

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
   certificate per historical symbol. The current archive certificates in ElfFixtureVerify additionally cover all 28 live
   exports (including the five bitslice kernels); CT does not imply functional refinement.
   Frame refinements specialize the 0x340-byte Keccak frame and its 0x320-byte wipe loop.
4. **Mutation tests:** Negative checker tests accompany the structural and noninterference
   proofs. Input-output refinement of selected decoded kernels is in `Qsag.McRefine`.
-/

public import Qsag.Math.Goldilocks
public import Qsag.Oracle.Keccak
public import Qsag.Math.BinaryTower
public import Qsag.Machine.CompiledRlibFixtures
public import Qsag.Machine.ElfFixtureSlices
public import Qsag.Machine.ElfParse
import all Qsag.Machine.ElfParse

import Qsag.Tactic.AssuranceKit
public section
namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
  UInt64.instLawfulOrderOrd Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe

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
  | shl | shr | rol | ror | sar
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
  | vpbroadcast (isQword is256 : Bool) (dst srcVec : Nat)
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
  | 7 => some .sar
  | _ => none

/-- Decode one variable-length `x86_64` instruction at byte offset `pc`, before the
    architectural 15-byte length cap that `decodeX86InstrAt` applies to the result. -/
def decodeX86InstrAtUncapped (pc : Nat) (bs : List UInt8) : Option (DecodedInstr X86Instr) := do
  let (prefLen, rest0, p66, pf2, pf3) := stripX86LegacyPrefixes 12 bs false false false
  -- No supported encoding takes `0xF2` (`REPNE` / mandatory-prefix escape): it selects a
  -- different instruction in every opcode map decoded below, so it is rejected, never dropped.
  if pf2 then return ← none
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
    -- `66` / `F3` / `REX` in front of a VEX prefix raise `#UD`.
    if p66 || pf3 || rexLen != 0 then return ← none
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
        | .reg srcVec => pure ⟨pc, baseLen, .vpbroadcast (vop == 0x59) vexL regF srcVec⟩
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

/-- Decode one `x86_64` instruction at byte offset `pc`. An instruction longer than 15 bytes
    (redundant prefixes included) raises `#UD` and is rejected. -/
def decodeX86InstrAt (pc : Nat) (bs : List UInt8) : Option (DecodedInstr X86Instr) :=
  (decodeX86InstrAtUncapped pc bs).bind fun d => if d.byteLen ≤ 15 then some d else none

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
    | .sar =>
      -- The vacated high `c` bits take the sign bit; `OF = 0` for a 1-bit `SAR`.
      let signFill : UInt64 :=
        if (cur &&& msbMask) != 0 then maskGprWidth is64 ((0 - 1 : UInt64) <<< UInt64.ofNat (w - c)) else 0
      let res := (cur >>> UInt64.ofNat c) ||| signFill
      let cf' := ((cur >>> UInt64.ofNat (c - 1)) &&& 1) != 0
      (res, cf', false, res == 0)

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
  | .vpbroadcast isQword is256 dst srcVec =>
    let sv := s.ymm.get srcVec
    let w := if isQword then sv.w0 else mapBytes64 (fun _ => sv.w0.toUInt8)
    -- `VEX.L = 0` writes `xmm` and zeroes bits `[255:128]`; `VEX.L = 1` writes all of `ymm`.
    ({ s with pc := nextPc, ymm := s.ymm.set dst (clampVecWidth is256 ⟨w, w, w, w⟩),
              ymmDirty := s.ymmDirty || is256 }, ⟨d.offset, [], true⟩)
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

/-- Decoded `AArch64` instruction covering all 9 current `qsag_asm` `.rlib` kernels + forbidden variable-time classes. -/
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
  | csel (cond : Nat) (isInv : Bool) (is64 : Bool) (rd rn rm : Nat)
  | ldp64 (rt1 rt2 rn : Nat) (offBytes : UInt64)
  | stp64 (rt1 rt2 rn : Nat) (offBytes : UInt64)
  | strbPost (rt rn : Nat) (postOff : UInt64)
  | ldpQ (rt1 rt2 rn : Nat) (offBytes : UInt64)
  | stpQ (rt1 rt2 rn : Nat) (offBytes : UInt64)
  | vdup2d (vd xn : Nat)
  | vand16b (vd vn vm : Nat)
  | vshift2d (left : Bool) (vd vn amount : Nat)
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
    if cond < 4 then some (.csel cond false is64 rd rn rm) else none
  else if (wn &&& 0x7FE00C00) == 0x5A800000 then
    let cond := (wn >>> 12) &&& 0xF
    if cond < 4 then some (.csel cond true is64 rd rn rm) else none
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
    -- `shift == 0b11` is reserved for Add/Sub, and `imm6 ≥ 32` is unallocated when `sf = 0`.
    if shiftKind == 3 || (!is64 && shiftAmt ≥ 32) then none
    else some (.aluReg aop is64 rd rn rm shiftKind shiftAmt)
  -- Logical shifted register (`xx001010 shift N Rm imm6 Rn Rd`)
  else if (wn &&& 0x1F000000) == 0x0A000000 then
    let opc := (wn >>> 29) &&& 3
    let nInv := ((wn >>> 21) &&& 1) == 1
    let shiftKind := (wn >>> 22) &&& 3
    let shiftAmt := (wn >>> 10) &&& 0x3F
    if !is64 && shiftAmt ≥ 32 then none
    else if opc == 0 && !nInv then some (.aluReg .andOp is64 rd rn rm shiftKind shiftAmt)
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
  -- Offset-only paired Q accesses; SP and duplicate load destinations are rejected.
  else if (wn &&& 0xFFC00000) == 0xAD400000 || (wn &&& 0xFFC00000) == 0xAD000000 then
    let isLoad := ((wn >>> 22) &&& 1) == 1
    let imm7 := (wn >>> 15) &&& 0x7F
    let off : UInt64 := if imm7 < 64 then UInt64.ofNat (imm7 * 16)
                       else 0 - UInt64.ofNat ((128 - imm7) * 16)
    if rn == 31 || (isLoad && rd == ra) then none
    else if isLoad then some (.ldpQ rd ra rn off) else some (.stpQ rd ra rn off)
  -- DUP Vd.2D, Xn; only the 64-bit element arrangement.
  else if (wn &&& 0xFFFFFC00) == 0x4E080C00 then some (.vdup2d rd rn)
  else if (wn &&& 0xFFE0FC00) == 0x4E201C00 then some (.vand16b rd rn rm)
  -- SHL/USHR Vd.2D, Vn.2D, #imm. Bit 22 selects 64-bit lanes.
  else if (wn &&& 0xFFC0FC00) == 0x4F405400 then
    some (.vshift2d true rd rn ((wn >>> 16) &&& 63))
  else if (wn &&& 0xFFC0FC00) == 0x6F400400 then
    some (.vshift2d false rd rn (64 - ((wn >>> 16) &&& 63)))
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
  else if kind == 2 then
    -- `ASR`: the vacated high `c` bits take the sign bit (bit `w - 1`) of the `w`-bit operand.
    let fill : UInt64 :=
      if (v' >>> UInt64.ofNat (w - 1)) &&& 1 == 1
      then maskGprWidth is64 ((0 - 1 : UInt64) <<< UInt64.ofNat (w - c)) else 0
    (v' >>> UInt64.ofNat c) ||| fill
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
  | .csel cond isInv is64 rd rn rm =>
    let taken := evalArmCond cond s
    let v := if taken then getArmGpr s rn
             else if isInv then ~~~(getArmGpr s rm) else getArmGpr s rm
    -- `sf = 0` writes the 32-bit result zero-extended into `Xd`; `sf = 1` writes all 64 bits.
    ({ s with pc := nextPc, gpr := setArmGpr s rd (maskGprWidth is64 v) }, ⟨d.offset, [], s.dit⟩)
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
  | .ldpQ rt1 rt2 rn off =>
    let ea := getArmGpr s rn + off
    let v1 := readMem128 s.mem ea
    let v2 := readMem128 s.mem (ea + 16)
    ({ s with pc := nextPc, vec := (s.vec.set rt1 v1).set rt2 v2 },
      ⟨d.offset, [(ea, 16), (ea + 16, 16)], true⟩)
  | .stpQ rt1 rt2 rn off =>
    let ea := getArmGpr s rn + off
    let m := writeMem128 (writeMem128 s.mem ea (s.vec.get rt1)) (ea + 16) (s.vec.get rt2)
    ({ s with pc := nextPc, mem := m }, ⟨d.offset, [(ea, 16), (ea + 16, 16)], true⟩)
  | .vdup2d vd xn =>
    ({ s with pc := nextPc, vec := s.vec.set vd ⟨getArmGpr s xn, getArmGpr s xn⟩ },
      ⟨d.offset, [], true⟩)
  | .vand16b vd vn vm =>
    let a := s.vec.get vn; let b := s.vec.get vm
    ({ s with pc := nextPc, vec := s.vec.set vd ⟨a.w0 &&& b.w0, a.w1 &&& b.w1⟩ },
      ⟨d.offset, [], true⟩)
  | .vshift2d left vd vn amount =>
    let a := s.vec.get vn
    -- UInt64 shifts mask their count; ISA USHR #64 instead yields zero.
    let shift (v : UInt64) := if amount ≥ 64 then 0
      else if left then v <<< UInt64.ofNat amount else v >>> UInt64.ofNat amount
    ({ s with pc := nextPc, vec := s.vec.set vd ⟨shift a.w0, shift a.w1⟩ },
      ⟨d.offset, [], true⟩)
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

/-- 3-level 32×16×16 radix map (`0 .. 8191`) giving `O(1)` 3-step PC lookup in kernel `decide`. -/
structure PcMap (α : Type) where
  root : Bank32 (Option (Bank16 (Option (Bank16 (Option α)))))

def PcMap.empty {α : Type} : PcMap α :=
  ⟨Bank32.const none⟩

def PcMap.get {α : Type} (m : PcMap α) (pc : Nat) : Option α :=
  if pc ≥ 8192 then none
  else
    match Bank32.get m.root (pc / 256) with
    | none => none
    | some p1 =>
      match Bank16.get p1 ((pc / 16) % 16) with
      | none => none
      | some p0 => Bank16.get p0 (pc % 16)

def PcMap.set {α : Type} (m : PcMap α) (pc : Nat) (v : α) : PcMap α :=
  if pc ≥ 8192 then m
  else
    let i2 := pc / 256
    let i1 := (pc / 16) % 16
    let i0 := pc % 16
    let p1 := match Bank32.get m.root i2 with | some b => b | none => Bank16.const none
    let p0 := match Bank16.get p1 i1 with | some b => b | none => Bank16.const none
    let p0' := Bank16.set p0 i0 (some v)
    let p1' := Bank16.set p1 i1 (some p0')
    ⟨Bank32.set m.root i2 (some p1')⟩

def PcMap.all {α : Type} (pred : Nat → α → Bool) (m : PcMap α) : Bool :=
  Bank32.allIdx (fun i2 opt1 =>
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
  | .vmovGprToXmm _ d s | .vpbroadcast _ _ d s | .vshiftImm _ _ d s _ => d < 16 && s < 16
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
  -- Used by the epilogue steps that write no memory: a completed frame wipe (`4`) stays valid.
  let stKeep := { st with stackZeroLoop := if st.stackZeroLoop == 4 then 4 else 0 }
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
      some [(nextPc, { stKeep with
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
    -- A frame-allocating kernel may only return once its spill area has been wiped.
    let frameOk := !c.usesRbpFrame || st.stackZeroLoop == 4
    if spOk && allCalleeOk && ymmClean && vecWiped && gprWiped && frameOk then some [] else none
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
      some [(nextPc, { stKeep with gpr := st.gpr.set dst orig })]
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
      some [(nextPc, { stKeep with
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
    else if is64 && op == .add && dst == 0 && imm == 0x20 && st.stackZeroLoop == 5 then
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
    if !x86CondIsPublic cc st || targetPc < 0 || targetPc.toNat ≥ 8192 then none
    else if st.stackZeroLoop == 3 && cc == 5 then
      some [(targetPc.toNat, { st with stackZeroLoop := 1 }), (nextPc, { st with stackZeroLoop := 4 })]
    else
      some [(targetPc.toNat, stNoLoop), (nextPc, stNoLoop)]
  | .jmpRel targetPc =>
    if targetPc < 0 || targetPc.toNat ≥ 8192 then none
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
    some [(nextPc, { stKeep with ymm := ymmPreserved, ymmDirty := false })]
  | .vzeroall =>
    some [(nextPc, { stKeep with ymm := Bank16.ofFn (fun _ => .zeroConst), ymmDirty := false })]
  | .vload is256 dst addr =>
    if !x86AddrIsPublic st addr then none
    else
      let w := if is256 then 32 else 16
      let vo : VecOrigin := if isInPubMemRegion c st addr w then .pubVal else .secretVal
      some [(nextPc, { stNoLoop with
        ymm := st.ymm.set dst vo
        ymmDirty := st.ymmDirty || is256 })]
  | .vstore is256 src addr =>
    if !x86AddrIsPublic st addr then none
    else
      let w := if is256 then 32 else 16
      let rbpOk := if st.rbpSaved then storePreservesSavedRbp c st addr w else false
      let nextLoop :=
        if st.stackZeroLoop == 1 && addr == .baseDisp 0 0 && is256 && st.ymm.get src == .zeroConst
        then 5 else 0
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
  | .vpbroadcast _isQword is256 dst srcVec =>
    let svo := st.ymm.get srcVec
    let vo : VecOrigin :=
      if svo == .zeroConst then .zeroConst else if svo.isPublic then .pubVal else .secretVal
    some [(nextPc, { stNoLoop with ymm := st.ymm.set dst vo, ymmDirty := st.ymmDirty || is256 })]
  | .vpbroadcastLoad64 dst addr =>
    if !x86AddrIsPublic st addr then none
    else
      let vo : VecOrigin := if isInPubMemRegion c st addr 8 then .pubVal else .secretVal
      some [(nextPc, { stNoLoop with ymm := st.ymm.set dst vo, ymmDirty := true })]
  | .vbinOp op is256 dst src1 src2 =>
    if op == .vpxor && src1 == src2 then
      some [(nextPc, { stKeep with
        ymm := st.ymm.set dst .zeroConst
        ymmDirty := st.ymmDirty || is256 })]
    else
      let p := (st.ymm.get src1).isPublic && (st.ymm.get src2).isPublic
      some [(nextPc, { stKeep with
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
  { dit := c.doitEnabled
    gpr := Bank32.ofFn (fun r =>
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
  | .ldrQ rd rn _ | .strQ rd rn _ | .fmovDFromX rd rn | .vdup2d rd rn
  | .vshift2d _ rd rn _ => rd < 32 && rn < 32
  | .aluReg _ _ rd rn rm _ _ | .mulOp _ rd rn rm | .csel _ _ _ rd rn rm
  | .ldp64 rd rn rm _ | .stp64 rd rn rm _ | .veor16b rd rn rm
  | .ldpQ rd rn rm _ | .stpQ rd rn rm _ | .vand16b rd rn rm
  | .vtrn _ _ _ rd rn rm | .vrax1_2d rd rn rm | .vxar_2d rd rn rm _ | .vpmull _ rd rn rm | .vext16b rd rn rm _ =>
    rd < 32 && rn < 32 && rm < 32
  | .vbcax16b vd vn vm va | .veor3_16b vd vn vm va =>
    vd < 32 && vn < 32 && vm < 32 && va < 32

def armRequiresDit : Arm64Instr → Bool
  | .mulOp _ _ _ _ | .csel _ _ _ _ _ _ | .vpmull _ _ _ _ => true
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
  | .csel cond _isInv _is64 rd rn rm =>
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
  | .ldpQ rt1 rt2 rn _off =>
    if !(getArmAbsGpr st rn).isPublic then none
    else some [(nextPc, { st with vec := (st.vec.set rt1 .secretVal).set rt2 .secretVal })]
  | .stpQ _rt1 _rt2 rn _off =>
    if !(getArmAbsGpr st rn).isPublic then none else some [(nextPc, st)]
  | .vshift2d _ vd vn _ =>
    some [(nextPc, { st with vec := st.vec.set vd (if (st.vec.get vn).isPublic then .pubVal else .secretVal) })]
  | .ldrQ rt rn _off =>
    if !(getArmAbsGpr st rn).isPublic then none
    else some [(nextPc, { st with vec := st.vec.set rt .secretVal })]
  | .strQ _rt rn _off =>
    if !(getArmAbsGpr st rn).isPublic then none else some [(nextPc, st)]
  | .fmovDFromX vd xn | .vdup2d vd xn =>
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
  | .vand16b vd vn vm | .vtrn _ _ _ vd vn vm | .vrax1_2d vd vn vm | .vxar_2d vd vn vm _ | .vpmull _ vd vn vm | .vext16b vd vn vm _ =>
    let p := (st.vec.get vn).isPublic && (st.vec.get vm).isPublic
    some [(nextPc, { st with vec := st.vec.set vd (if p then .pubVal else .secretVal) })]
  | .bCond cond targetPc =>
    if !armCondIsPublic cond st || targetPc < 0 || targetPc.toNat ≥ 8192 then none
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

 /-- Live archive contracts. Pointer/count inputs are public; loaded data remain secret. -/
def currentX86SymbolContracts : List FuncContract :=
  x86SymbolContracts ++ [
    mkContract "qsag_asm_transpose64x256_avx2" [4, 7],
    mkContract "qsag_asm_gf2_128_mul_acc_pclmul" [4, 7, 6, 2, 1],
    mkContract "qsag_asm_gf2_128_mul_acc_vpclmul" [4, 7, 6, 2, 1]]

def currentAarch64SymbolContracts : List FuncContract :=
  aarch64SymbolContracts ++ [
    mkContract "qsag_asm_transpose64x256_neon" [0],
    mkContract "qsag_asm_gf2_128_mul_acc_pmull" [0, 1, 2, 3]]

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
  · rw [Bank32.get_const]

theorem PcMap.get_some_lt {α : Type} {m : PcMap α} {pc : Nat} {v : α}
    (h : m.get pc = some v) : pc < 8192 := by
  unfold PcMap.get at h
  split at h
  · cases h
  · omega

theorem PcMap.get_set_eq {α : Type} (m : PcMap α) {pc : Nat} (v : α) (hpc : pc < 8192) :
    (m.set pc v).get pc = some v := by
  have hge : ¬(pc ≥ 8192) := by intro h; omega
  unfold PcMap.set PcMap.get
  simp only [hge, ↓reduceIte, Bank32.get_set_eq, Bank16.get_set_eq]

theorem PcMap.get_set_ne {α : Type} (m : PcMap α) {pc q : Nat} (v : α)
    (hq : q < 8192) (hne : pc ≠ q) :
    (m.set pc v).get q = m.get q := by
  have hqge : ¬(q ≥ 8192) := by intro h; omega
  by_cases hpc : pc ≥ 8192
  · unfold PcMap.set; simp [hpc]
  · unfold PcMap.set PcMap.get
    simp only [hpc, hqge, ↓reduceIte]
    have hi2p : pc / 256 < 32 := by omega
    have hi2q : q / 256 < 32 := by omega
    have hi1p : (pc / 16) % 16 < 16 := by omega
    have hi1q : (q / 16) % 16 < 16 := by omega
    have hi0p : pc % 16 < 16 := by omega
    have hi0q : q % 16 < 16 := by omega
    by_cases h2 : pc / 256 = q / 256
    · rw [← h2, Bank32.get_set_eq]
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
    · rw [Bank32.get_set_ne _ _ hi2p hi2q h2]

theorem PcMap.all_get {α : Type} {pred : Nat → α → Bool} {m : PcMap α}
    (hAll : m.all pred = true) {pc : Nat} {v : α} (hGet : m.get pc = some v) :
    pred pc v = true := by
  have hlt : pc < 8192 := PcMap.get_some_lt hGet
  have hge : ¬(pc ≥ 8192) := by intro h; omega
  unfold PcMap.get at hGet
  simp only [hge, ↓reduceIte] at hGet
  unfold PcMap.all at hAll
  have h2 := Bank32.allIdx_get hAll (i := pc / 256) (by omega)
  cases hm2 : Bank32.get m.root (pc / 256) with
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
    {pc : Nat} (hpc : pc < 8192) :
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

