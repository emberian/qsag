module
public import Qsag.Machine.X86SimdArith
import Qsag.Tactic.AssuranceKit
public section
namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
  UInt64.instLawfulOrderOrd Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe
set_option autoImplicit false
set_option maxRecDepth 65536

@[expose] def x86CondSupported (cc : Nat) : Bool :=
  cc == 2 || cc == 3 || cc == 4 || cc == 5

/-- Concrete condition evaluation for the supported codes `{2, 3, 4, 5}`. An unsupported code
    evaluates to `false` (not taken); such an instruction is never accepted by the checker
    (`x86CondIsPublic_supported`, `tooth_x86_jcc_unsupported_cc_rejected`,
    `tooth_x86_cmovcc_unsupported_cc_rejected`). -/
@[expose] def evalX86Cond (cc : Nat) (s : X86State) : Bool :=
  if cc == 2 then s.cf
  else if cc == 3 then !s.cf
  else if cc == 4 then s.zf
  else if cc == 5 then !s.zf
  else false

/-- Two's-complement value of the `w`-bit pattern `n < bound`, where `bound = 2 ^ w`. -/
@[expose] def signedOfBound (bound n : Nat) : Int :=
  if 2 * n < bound then (n : Int) else (n : Int) - (bound : Int)

/-- Signed two's-complement range check `v ∉ [-bound / 2, bound / 2)` for `bound = 2 ^ w`. -/
@[expose] def signedOutOfBounds (bound : Nat) (v : Int) : Bool :=
  decide (2 * v < -(bound : Int)) || decide ((bound : Int) ≤ 2 * v)

/-- `CF = OF` after a signed multiply of two `w`-bit patterns (`bound = 2 ^ w`): set exactly when
    the signed product lies outside `[-bound / 2, bound / 2)`, that is, when sign-extending the
    truncated result does not give back the product. -/
@[expose] def imulSignedOverflow (bound an bn : Nat) : Bool :=
  signedOutOfBounds bound (signedOfBound bound an * signedOfBound bound bn)

/-- Architectural Intel SDM signed-overflow flag (`OF`) for scalar `ALU` operations at width `w ∈ {32, 64}`. -/
@[expose] def evalX86AluOf (op : X86AluOp) (is64 : Bool) (a b : UInt64) (cfIn : Bool) : Bool :=
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
@[expose] def evalX86IncDecOf (isInc is64 : Bool) (v : UInt64) : Bool :=
  let cur := maskGprWidth is64 v
  if isInc then cur == (if is64 then 0x7FFFFFFFFFFFFFFF else 0x7FFFFFFF)
  else cur == (if is64 then 0x8000000000000000 else 0x80000000)

/-- Byte-swap helper for 32-bit and 64-bit `BSWAP`. -/
@[expose] def evalX86Bswap (is64 : Bool) (v : UInt64) : UInt64 :=
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
@[expose] def evalPmovmskb128 (v : Vec256) : UInt64 :=
  let bitFrom (w : UInt64) (byteIdx outBit : Nat) : UInt64 :=
    (((w >>> UInt64.ofNat (byteIdx * 8 + 7)) &&& 1) <<< UInt64.ofNat outBit)
  bitFrom v.w0 0 0 ||| bitFrom v.w0 1 1 ||| bitFrom v.w0 2 2 ||| bitFrom v.w0 3 3 |||
  bitFrom v.w0 4 4 ||| bitFrom v.w0 5 5 ||| bitFrom v.w0 6 6 ||| bitFrom v.w0 7 7 |||
  bitFrom v.w1 0 8 ||| bitFrom v.w1 1 9 ||| bitFrom v.w1 2 10 ||| bitFrom v.w1 3 11 |||
  bitFrom v.w1 4 12 ||| bitFrom v.w1 5 13 ||| bitFrom v.w1 6 14 ||| bitFrom v.w1 7 15

@[expose] def evalX86Alu (op : X86AluOp) (is64 : Bool) (a b : UInt64) (cfIn : Bool) : (UInt64 × Bool × Bool) :=
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


end Qsag
