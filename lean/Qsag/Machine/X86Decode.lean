module
public import Qsag.Machine.X86Syntax
import Qsag.Tactic.AssuranceKit
public section
namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
  UInt64.instLawfulOrderOrd Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe
set_option autoImplicit false
set_option maxRecDepth 65536

@[expose] def readU32LE? : List UInt8 → Option UInt32
  | b0 :: b1 :: b2 :: b3 :: _ =>
    some (b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24))
  | _ => none

@[expose] def readU64LE? : List UInt8 → Option UInt64
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: _ =>
    some (b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24) |||
          (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) ||| (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56))
  | _ => none

@[expose] def decodeX86ModRM (bs : List UInt8) (rexR rexX rexB : Nat) : Option (Nat × ModRMOperand × Nat) := do
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

@[expose] def stripX86LegacyPrefixes : Nat → List UInt8 → Bool → Bool → Bool → (Nat × List UInt8 × Bool × Bool × Bool)
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

@[expose] def decodeAluDigit? : Nat → Option X86AluOp
  | 0 => some .add
  | 1 => some .orOp
  | 2 => some .adc
  | 3 => some .sbb
  | 4 => some .andOp
  | 5 => some .sub
  | 6 => some .xorOp
  | _ => none

@[expose] def decodeShiftDigit? : Nat → Option X86ShiftKind
  | 0 => some .rol
  | 1 => some .ror
  | 4 => some .shl
  | 5 => some .shr
  | 7 => some .sar
  | _ => none

/-- Decode one variable-length `x86_64` instruction at byte offset `pc`, before the
    architectural 15-byte length cap that `decodeX86InstrAt` applies to the result. -/
@[expose] def decodeX86InstrAtUncapped (pc : Nat) (bs : List UInt8) : Option (DecodedInstr X86Instr) := do
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
@[expose] def decodeX86InstrAt (pc : Nat) (bs : List UInt8) : Option (DecodedInstr X86Instr) :=
  (decodeX86InstrAtUncapped pc bs).bind fun d => if d.byteLen ≤ 15 then some d else none

@[expose] def dropExact? : Nat → List UInt8 → Option (List UInt8)
  | 0, bs => some bs
  | _ + 1, [] => none
  | k + 1, _ :: rest => dropExact? k rest

@[expose] def decodeX86Loop : Nat → Nat → List UInt8 → List (DecodedInstr X86Instr) → Option (List (DecodedInstr X86Instr))
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
@[expose] def decodeX86Stream (code : List UInt8) : Option (List (DecodedInstr X86Instr)) :=
  decodeX86Loop (code.length) 0 code []

/- Concrete `x86_64` machine state (`RAX..R15`, `YMM0..YMM15`, `CF/OF/ZF`, `ymmDirty`, byte memory). -/
end Qsag
