module
public import Qsag.Machine.X86AluEval
import Qsag.Tactic.AssuranceKit
public section
namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
  UInt64.instLawfulOrderOrd Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe
set_option autoImplicit false
set_option maxRecDepth 65536

@[expose] def evalVecBin256 (op : X86VecBinOp) (v1 v2 : Vec256) : Vec256 :=
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

@[expose] def evalVecShift256 (sk : X86VecShiftKind) (v : Vec256) (imm : Nat) : Vec256 :=
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

@[expose] def clampVecWidth (is256 : Bool) (v : Vec256) : Vec256 :=
  if is256 then v else ⟨v.w0, v.w1, 0, 0⟩

@[expose] def findInstrAtPc {Instr : Type} (pc : Nat) : List (DecodedInstr Instr) → Option (DecodedInstr Instr)
  | [] => none
  | d :: ds => if d.offset == pc then some d else findInstrAtPc pc ds

@[expose] def x86ShiftPreservesZf (sk : X86ShiftKind) (is64 : Bool) (cnt : Nat) : Bool :=
  cnt % (if is64 then 64 else 32) == 0 ||
    match sk with
    | .rol | .ror => true
    | _ => false

/-- Architectural result + `(CF, OF, ZF)` for immediate shifts and rotates (`c == 0` preserves flags;
    `c > 0` sets architectural `CF` and `c == 1` `OF`; for `c > 1`, `OF` is architecturally undefined
    on hardware and given a deterministic pure formula here while `transferX86Instr` forgets `ofPub`). -/
@[expose] def evalX86Shift (sk : X86ShiftKind) (is64 : Bool) (v : UInt64) (cnt : Nat)
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

/- Small-step `x86_64` operational semantics emitting `StepObs` (`pc`, `(addr, bytes)`, `isDoitSafe`). -/
end Qsag
