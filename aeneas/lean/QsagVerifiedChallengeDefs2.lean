module
public import Aeneas
public import QsagVerified.Types
public import QsagVerified.Funs
public import Qsag.Oracle.Keccak
public import Qsag.Math.Gf2Pow128
public import QsagVerifiedChallengeDefs1

public section
namespace qsag_verified.proofs
open Aeneas Aeneas.Std Result ControlFlow Error
open qsag_verified
set_option maxRecDepth 4096

@[expose] def pureMulT5 (a b : Std.U32) : Std.U32 :=
  let alo : Std.U16 := UScalar.cast .U16 (a &&& 65535#u32)
  let ahi : Std.U16 := UScalar.cast .U16 ((⟨a.bv >>> 16⟩ : Std.U32) &&& 65535#u32)
  let blo : Std.U16 := UScalar.cast .U16 (b &&& 65535#u32)
  let bhi : Std.U16 := UScalar.cast .U16 ((⟨b.bv >>> 16⟩ : Std.U32) &&& 65535#u32)
  let p := pureMulT4 alo blo
  let q := pureMulT4 ahi bhi
  let r := pureMulT4 (alo ^^^ ahi) (blo ^^^ bhi)
  let sx := pureScaleXT4 q
  ⟨(UScalar.cast .U32 (p ^^^ q)).bv ||| ((UScalar.cast .U32 (r ^^^ p ^^^ q ^^^ sx)).bv <<< 16)⟩

@[expose] def pureScaleXT5 (a : Std.U32) : Std.U32 :=
  let hi : Std.U16 := UScalar.cast .U16 ((⟨a.bv >>> 16⟩ : Std.U32) &&& 65535#u32)
  let sx := pureScaleXT4 hi
  ⟨(UScalar.cast .U32 hi).bv ||| ((UScalar.cast .U32 ((UScalar.cast .U16 (a &&& 65535#u32)) ^^^ sx)).bv <<< 16)⟩

@[expose] def pureMulT6 (a b : Std.U64) : Std.U64 :=
  let alo : Std.U32 := UScalar.cast .U32 (a &&& 4294967295#u64)
  let ahi : Std.U32 := UScalar.cast .U32 ((⟨a.bv >>> 32⟩ : Std.U64) &&& 4294967295#u64)
  let blo : Std.U32 := UScalar.cast .U32 (b &&& 4294967295#u64)
  let bhi : Std.U32 := UScalar.cast .U32 ((⟨b.bv >>> 32⟩ : Std.U64) &&& 4294967295#u64)
  let p := pureMulT5 alo blo
  let q := pureMulT5 ahi bhi
  let r := pureMulT5 (alo ^^^ ahi) (blo ^^^ bhi)
  let sx := pureScaleXT5 q
  ⟨(UScalar.cast .U64 (p ^^^ q)).bv ||| ((UScalar.cast .U64 (r ^^^ p ^^^ q ^^^ sx)).bv <<< 32)⟩

@[expose] def pureScaleXT6 (a : Std.U64) : Std.U64 :=
  let hi : Std.U32 := UScalar.cast .U32 ((⟨a.bv >>> 32⟩ : Std.U64) &&& 4294967295#u64)
  let sx := pureScaleXT5 hi
  ⟨(UScalar.cast .U64 hi).bv ||| ((UScalar.cast .U64 ((UScalar.cast .U32 (a &&& 4294967295#u64)) ^^^ sx)).bv <<< 32)⟩

@[expose] def pureTower128Mul (a b : Std.U128) : Std.U128 :=
  let alo : Std.U64 := UScalar.cast .U64 (a &&& 18446744073709551615#u128)
  let ahi : Std.U64 := UScalar.cast .U64 ((⟨a.bv >>> 64⟩ : Std.U128) &&& 18446744073709551615#u128)
  let blo : Std.U64 := UScalar.cast .U64 (b &&& 18446744073709551615#u128)
  let bhi : Std.U64 := UScalar.cast .U64 ((⟨b.bv >>> 64⟩ : Std.U128) &&& 18446744073709551615#u128)
  let p := pureMulT6 alo blo
  let q := pureMulT6 ahi bhi
  let r := pureMulT6 (alo ^^^ ahi) (blo ^^^ bhi)
  let sx := pureScaleXT6 q
  ⟨(UScalar.cast .U128 (p ^^^ q)).bv ||| ((UScalar.cast .U128 (r ^^^ p ^^^ q ^^^ sx)).bv <<< 64)⟩

@[expose]
def bdozMaskedSum (batch : tower.BdozCommittedBatchOpening2Lane) (item : tower.BdozWireOpening2Lane) : tower.Tower128 :=
  batch.mask_value ^^^ pureTower128Mul item.chal_weight (UScalar.cast .U128 item.opened_value)

@[expose]
def bdozFoldedKey (batch : tower.BdozCommittedBatchOpening2Lane) (item : tower.BdozWireOpening2Lane) (lane : Nat) : tower.Tower128 :=
  batch.mask_key_lanes.val.getD lane 0#u128 ^^^ pureTower128Mul item.chal_weight (item.key_lanes.val.getD lane 0#u128)

@[expose]
def bdozExpectedMacLanes (session : tower.BdozVerifierSession2Lane)
    (batch : tower.BdozCommittedBatchOpening2Lane) (item : tower.BdozWireOpening2Lane) : Std.Array tower.Tower128 2#usize :=
  Std.Array.make 2#usize [
    bdozFoldedKey batch item 0 ^^^ pureTower128Mul (session.alpha_lanes.val.getD 0 0#u128) (bdozMaskedSum batch item),
    bdozFoldedKey batch item 1 ^^^ pureTower128Mul (session.alpha_lanes.val.getD 1 0#u128) (bdozMaskedSum batch item)]

@[expose]
def pureHornerGf256Prefix (coeffs : List tower.Gf256) (x : tower.Gf256) :
    Nat → tower.Gf256 → tower.Gf256
  | 0, acc => acc
  | n + 1, acc => pureHornerGf256Prefix coeffs x n
      (pureGf256Mul acc x ^^^ coeffs.getD n 0#u8)

@[expose]
def pureHornerGf256 (coeffs : List tower.Gf256) (x : tower.Gf256) : tower.Gf256 :=
  pureHornerGf256Prefix coeffs x coeffs.length 0#u8

@[expose]
def pureHornerGoldilocksPrefix (coeffs : List goldilocks.Goldilocks) (x : Nat) :
    Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => pureHornerGoldilocksPrefix coeffs x n
      ((acc % GoldilocksP * (x % GoldilocksP) +
        (coeffs.getD n 0#u64).val % GoldilocksP) % GoldilocksP)

@[expose]
def pureHornerGoldilocks (coeffs : List goldilocks.Goldilocks) (x : Nat) : Nat :=
  pureHornerGoldilocksPrefix coeffs x coeffs.length 0


abbrev OpeningGuard := opening_guard.ConsumingOpeningGuard2Lane
abbrev OpeningPermit := opening_guard.OpeningReleasePermit

abbrev OpeningInput := Array Std.U8 32#usize × Array Std.U8 32#usize × Array Std.U128 2#usize

def openingLaneSum (xs : List OpeningInput) (k : Nat) : Std.U128 :=
  xs.foldl (fun acc x => acc ^^^ x.2.2.val.getD k 0#u128) 0#u128

def openingAbsorbAll (s : OpeningGuard) : List OpeningInput → Result OpeningGuard
  | [] => .ok s
  | x :: xs =>
    Result.bind (opening_guard.ConsumingOpeningGuard2Lane.absorb_opening s x.1 x.2.1 x.2.2)
      fun s' => openingAbsorbAll s' xs

def openingRound (sid : Array Std.U8 32#usize) (round : Std.U64)
    (binding : Array Std.U8 32#usize) (n : Std.U64) (xs : List OpeningInput)
    (sid' : Array Std.U8 32#usize) (round' : Std.U64) (binding' : Array Std.U8 32#usize) :
    Result (OpeningGuard × Option OpeningPermit) :=
  Result.bind (opening_guard.ConsumingOpeningGuard2Lane.new sid round binding n) fun s0 =>
    Result.bind (openingAbsorbAll s0 xs) fun s1 =>
      opening_guard.ConsumingOpeningGuard2Lane.verify_once s1 sid' round' binding'

def u8Bytes (xs : List Std.U8) : List UInt8 := xs.map (fun b => UInt8.ofBitVec b.bv)

end qsag_verified.proofs
