module
public import Qsag.Machine.X86Memory
import Qsag.Tactic.AssuranceKit
public section
namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
  UInt64.instLawfulOrderOrd Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe
set_option autoImplicit false
set_option maxRecDepth 65536

@[expose] def parityByte (x : UInt8) : UInt8 :=
  let y := x ^^^ (x >>> 4)
  let z := y ^^^ (y >>> 2)
  (z ^^^ (z >>> 1)) &&& 1

/-- Exact Intel SDM `VGF2P8AFFINEQB` byte operation: $M \cdot x \oplus b$ over $\mathbb{F}_2^8$. -/
@[expose] def gfniAffineByte (x : UInt8) (mat : UInt64) (imm : UInt8) : UInt8 :=
  let bitAt (i : Nat) : UInt8 :=
    let row := (mat >>> UInt64.ofNat ((7 - i) * 8)).toUInt8
    ((parityByte (x &&& row)) ^^^ ((imm >>> UInt8.ofNat i) &&& 1)) <<< UInt8.ofNat i
  bitAt 0 ||| bitAt 1 ||| bitAt 2 ||| bitAt 3 ||| bitAt 4 ||| bitAt 5 ||| bitAt 6 ||| bitAt 7

@[expose] def xtimeRijndael (a : UInt8) : UInt8 :=
  let shifted := a <<< 1
  if (a &&& 0x80) != 0 then shifted ^^^ 0x1B else shifted

/-- Exact Intel SDM `VGF2P8MULB` byte multiplication in $\mathbb{F}_2[z]/(z^8 + z^4 + z^3 + z + 1)$. -/
@[expose] def gfniMulByte (a b : UInt8) : UInt8 :=
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

@[expose] def mapBytes64 (f : Nat → UInt8) : UInt64 :=
  (f 0).toUInt64 |||
  ((f 1).toUInt64 <<< 8) |||
  ((f 2).toUInt64 <<< 16) |||
  ((f 3).toUInt64 <<< 24) |||
  ((f 4).toUInt64 <<< 32) |||
  ((f 5).toUInt64 <<< 40) |||
  ((f 6).toUInt64 <<< 48) |||
  ((f 7).toUInt64 <<< 56)

@[expose] def getByte64 (w : UInt64) (i : Nat) : UInt8 :=
  (w >>> UInt64.ofNat (i * 8)).toUInt8

@[expose] def mapBytesVec256 (v1 v2 : Vec256) (f : UInt8 → UInt8 → UInt8) : Vec256 :=
  ⟨mapBytes64 (fun i => f (getByte64 v1.w0 i) (getByte64 v2.w0 i)),
   mapBytes64 (fun i => f (getByte64 v1.w1 i) (getByte64 v2.w1 i)),
   mapBytes64 (fun i => f (getByte64 v1.w2 i) (getByte64 v2.w2 i)),
   mapBytes64 (fun i => f (getByte64 v1.w3 i) (getByte64 v2.w3 i))⟩

@[expose] def gfniAffineVec256 (src mat : Vec256) (imm : UInt8) : Vec256 :=
  ⟨mapBytes64 (fun i => gfniAffineByte (getByte64 src.w0 i) mat.w0 imm),
   mapBytes64 (fun i => gfniAffineByte (getByte64 src.w1 i) mat.w1 imm),
   mapBytes64 (fun i => gfniAffineByte (getByte64 src.w2 i) mat.w2 imm),
   mapBytes64 (fun i => gfniAffineByte (getByte64 src.w3 i) mat.w3 imm)⟩

@[expose] def clmul64Loop : Nat → UInt64 → UInt64 → UInt64 → UInt64 → Vec128
  | 0, _, _, lo, hi => ⟨lo, hi⟩
  | k + 1, a, b, lo, hi =>
    let i := 63 - k
    let bitSet := ((b >>> UInt64.ofNat i) &&& 1) != 0
    let termLo := if bitSet then (if i == 0 then a else a <<< UInt64.ofNat i) else 0
    let termHi := if bitSet && i > 0 then a >>> UInt64.ofNat (64 - i) else 0
    clmul64Loop k a b (lo ^^^ termLo) (hi ^^^ termHi)

@[expose] def clmul64 (a b : UInt64) : Vec128 :=
  clmul64Loop 64 a b 0 0

/-- Regression for the low polynomial coefficient, previously skipped by the loop. -/
theorem clmul64_one_one : clmul64 1 1 = ⟨1, 0⟩ := by rfl

theorem clmul64_one_two : clmul64 1 2 = ⟨2, 0⟩ := by rfl

/- Condition codes with modelled semantics: `2` (`B`, `CF`), `3` (`AE`, `!CF`), `4` (`E`, `ZF`)
    and `5` (`NE`, `!ZF`). Every other code reads `SF`, `PF`, or a combination of flags that the
    state does not carry. `decodeX86InstrAt` produces only these four codes for `jcc` and
    `cmovcc`, and `transferX86Instr` rejects any instruction whose code is outside this set. -/
end Qsag
