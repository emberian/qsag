module
public import Aeneas
public import QsagVerified.Types
public import QsagVerified.Funs
public import Qsag.Keccak
public import Qsag.BinaryTower

public section
namespace qsag_verified.proofs
open Aeneas Aeneas.Std Result ControlFlow Error
open qsag_verified
set_option maxRecDepth 4096

@[expose]
def GoldilocksP : Nat := 18446744069414584321

@[expose]
def pureMulT1 (a b : Std.U8) : Std.U8 :=
  let a_lo := a &&& 1#u8
  let a_hi := ⟨a.bv >>> 1⟩ &&& 1#u8
  let b_lo := b &&& 1#u8
  let b_hi := ⟨b.bv >>> 1⟩ &&& 1#u8
  let p := a_lo &&& b_lo
  let q := a_hi &&& b_hi
  let r := (a_lo ^^^ a_hi) &&& (b_lo ^^^ b_hi)
  (p ^^^ q) ||| ⟨(r ^^^ p).bv <<< 1⟩

@[expose]
def pureScaleXT1 (a : Std.U8) : Std.U8 :=
  let lo := a &&& 1#u8
  let hi := ⟨a.bv >>> 1⟩ &&& 1#u8
  hi ||| ⟨(lo ^^^ hi).bv <<< 1⟩

@[expose]
def pureMulT2 (a b : Std.U8) : Std.U8 :=
  let a_lo := a &&& 3#u8
  let a_hi := ⟨a.bv >>> 2⟩ &&& 3#u8
  let b_lo := b &&& 3#u8
  let b_hi := ⟨b.bv >>> 2⟩ &&& 3#u8
  let p := pureMulT1 a_lo b_lo
  let q := pureMulT1 a_hi b_hi
  let r := pureMulT1 (a_lo ^^^ a_hi) (b_lo ^^^ b_hi)
  let hi := ((r ^^^ p) ^^^ q) ^^^ pureScaleXT1 q
  (p ^^^ q) ||| ⟨hi.bv <<< 2⟩

@[expose]
def pureScaleXT2 (a : Std.U8) : Std.U8 :=
  let lo := a &&& 3#u8
  let hi := ⟨a.bv >>> 2⟩ &&& 3#u8
  hi ||| ⟨(lo ^^^ pureScaleXT1 hi).bv <<< 2⟩

@[expose]
def pureGf256Mul (a b : Std.U8) : Std.U8 :=
  let a_lo := a &&& 15#u8
  let a_hi := ⟨a.bv >>> 4⟩ &&& 15#u8
  let b_lo := b &&& 15#u8
  let b_hi := ⟨b.bv >>> 4⟩ &&& 15#u8
  let p := pureMulT2 a_lo b_lo
  let q := pureMulT2 a_hi b_hi
  let r := pureMulT2 (a_lo ^^^ a_hi) (b_lo ^^^ b_hi)
  let hi := ((r ^^^ p) ^^^ q) ^^^ pureScaleXT2 q
  (p ^^^ q) ||| ⟨hi.bv <<< 4⟩

@[expose]
def pureGf256Inv (a : Std.U8) : Std.U8 :=
  let a2 := pureGf256Mul a a
  let a4 := pureGf256Mul a2 a2
  let a6 := pureGf256Mul a4 a2
  let a8 := pureGf256Mul a4 a4
  let a14 := pureGf256Mul a8 a6
  let a16 := pureGf256Mul a8 a8
  let a32 := pureGf256Mul a16 a16
  let a64 := pureGf256Mul a32 a32
  let a128 := pureGf256Mul a64 a64
  pureGf256Mul (pureGf256Mul (pureGf256Mul a128 a64)
    (pureGf256Mul a32 a16)) a14

@[expose]
def natPrefixSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => natPrefixSum f n + f n

@[expose]
def wotsChecksumNat (digits : Std.Array Std.U8 32#usize) : Nat :=
  natPrefixSum (fun k => 15 - (digits.val.getD k 0#u8).val % 16) 32

@[expose] def pureScaleXT3 (a : Std.U8) : Std.U8 :=
  let lo := a &&& 15#u8
  let hi := (⟨a.bv >>> 4⟩ : Std.U8) &&& 15#u8
  hi ||| ⟨(lo ^^^ pureScaleXT2 hi).bv <<< 4⟩

@[expose] def pureMulT4 (a b : Std.U16) : Std.U16 :=
  let alo : Std.U8 := UScalar.cast .U8 (a &&& 255#u16)
  let ahi : Std.U8 := UScalar.cast .U8 ((⟨a.bv >>> 8⟩ : Std.U16) &&& 255#u16)
  let blo : Std.U8 := UScalar.cast .U8 (b &&& 255#u16)
  let bhi : Std.U8 := UScalar.cast .U8 ((⟨b.bv >>> 8⟩ : Std.U16) &&& 255#u16)
  let p := pureGf256Mul alo blo
  let q := pureGf256Mul ahi bhi
  let r := pureGf256Mul (alo ^^^ ahi) (blo ^^^ bhi)
  let sx := pureScaleXT3 q
  ⟨(UScalar.cast .U16 (p ^^^ q)).bv ||| ((UScalar.cast .U16 (r ^^^ p ^^^ q ^^^ sx)).bv <<< 8)⟩

@[expose] def pureScaleXT4 (a : Std.U16) : Std.U16 :=
  let hi : Std.U8 := UScalar.cast .U8 ((⟨a.bv >>> 8⟩ : Std.U16) &&& 255#u16)
  let sx := pureScaleXT3 hi
  ⟨(UScalar.cast .U16 hi).bv ||| ((UScalar.cast .U16 ((UScalar.cast .U8 (a &&& 255#u16)) ^^^ sx)).bv <<< 8)⟩

end qsag_verified.proofs
