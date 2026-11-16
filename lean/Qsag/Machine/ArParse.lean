module
public import Qsag.Machine.ElfBytes
import Qsag.Tactic.AssuranceKit
public section
namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
  UInt64.instLawfulOrderOrd Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe
set_option autoImplicit false
set_option maxRecDepth 65536
/-! ## §2. `GNU ar` (`.rlib`) parser & subslice soundness -/

/-- Parsed member of a `GNU ar` (`.rlib`) archive with exact byte-offset provenance. -/
structure ArMember where
  name : String
  payloadOffset : Nat
  payloadSize : Nat
  payload : Bytes

@[expose] def arMagicBytes : List UInt8 :=
  [0x21, 0x3c, 0x61, 0x72, 0x63, 0x68, 0x3e, 0x0a]

@[expose] def elfMagicBytes : List UInt8 :=
  [0x7f, 0x45, 0x4c, 0x46]

@[expose] def parseAsciiDecLoop : List UInt8 → Nat → Bool → Option Nat
  | [], acc, seen => if seen then some acc else none
  | b :: bs, acc, seen =>
    if b == 0x20 then
      if seen then
        if bs.all (· == 0x20) then some acc else none
      else
        parseAsciiDecLoop bs acc false
    else if 0x30 ≤ b && b ≤ 0x39 then
      parseAsciiDecLoop bs (acc * 10 + (b.toNat - 48)) true
    else
      none

@[expose] def parseAsciiDec (bs : List UInt8) : Option Nat :=
  parseAsciiDecLoop bs 0 false

@[expose] def bytesToAsciiString (bs : List UInt8) : String :=
  String.ofList (bs.map (fun b => Char.ofNat b.toNat))

@[expose] def takeUntilByte (stop : UInt8) : List UInt8 → List UInt8
  | [] => []
  | b :: bs => if b == stop then [] else b :: takeUntilByte stop bs

@[expose] def rstripSpaces (bs : List UInt8) : List UInt8 :=
  (bs.reverse.dropWhile (· == 0x20)).reverse

@[expose] def rstripSlash (bs : List UInt8) : List UInt8 :=
  match bs.reverse with
  | 0x2f :: rest => rest.reverse
  | _ => bs

@[expose] def resolveArMemberName (rawField : List UInt8) (extNames : List UInt8) : String :=
  let trimmed := rstripSpaces rawField
  match trimmed with
  | 0x2f :: rest =>
    match rest with
    | [] => "/"
    | 0x2f :: _ => "//"
    | _ =>
      match parseAsciiDec rest with
      | some off =>
        let slice := takeUntilByte 0x0a (extNames.drop off)
        bytesToAsciiString (rstripSlash slice)
      | none => bytesToAsciiString (rstripSlash trimmed)
  | _ => bytesToAsciiString (rstripSlash trimmed)

/-- Walk member headers from byte offset `pos`. The GNU `//` extended-name member is consumed as
    the name table for later members; every other member is recorded with its payload window. -/
@[expose] def parseArLoop (bytes : Bytes) : Nat → Nat → List UInt8 → List ArMember → List ArMember
  | 0, _, _, acc => acc.reverse
  | fuel + 1, pos, extNames, acc =>
    if pos + 60 ≤ bytes.len then
      let hdr := bytes.slice pos 60
      if hdr.drop 58 == [0x60, 0x0a] then
        match parseAsciiDec (takeTR 10 (hdr.drop 48)) with
        | none => acc.reverse
        | some sz =>
          if pos + 60 + sz ≤ bytes.len then
            let payload : Bytes := (bytes.drop (pos + 60)).take sz
            let rawName := takeTR 16 hdr
            let nextPos := pos + (60 + sz + (sz % 2))
            if rstripSpaces rawName == [0x2f, 0x2f] then
              parseArLoop bytes fuel nextPos payload.toList acc
            else
              let m : ArMember := {
                name := resolveArMemberName rawName extNames
                payloadOffset := pos + 60
                payloadSize := sz
                payload := payload
              }
              parseArLoop bytes fuel nextPos extNames (m :: acc)
          else acc.reverse
      else acc.reverse
    else acc.reverse

/-- Validate the entire archive envelope before exposing any parsed prefix.
Odd payloads require their alignment byte; truncated headers and trailing junk fail closed. -/
@[expose] def validArEnvelope (bytes : Bytes) : Nat → Nat → Bool
  | 0, pos => decide (bytes.len ≤ pos)
  | fuel + 1, pos =>
    if bytes.len ≤ pos then true
    else if bytes.len < pos + 60 then false
    else
      let hdr := bytes.slice pos 60
      if hdr.drop 58 != [0x60, 0x0a] then false
      else match parseAsciiDec (takeTR 10 (hdr.drop 48)) with
      | none => false
      | some sz =>
        let step := 60 + sz + sz % 2
        if sz % 2 == 1 && !(decide (pos + 60 + sz < bytes.len) && bytes.get (pos + 60 + sz) == 0x0a) then false
        else if pos + step ≤ bytes.len then validArEnvelope bytes fuel (pos + step) else false

/-- Parse a `GNU ar` (`.rlib`) archive into its non-`//` member windows. -/
@[expose] def parseArArchive (rlib : Bytes) : List ArMember :=
  if decide (8 ≤ rlib.len) && rlib.slice 0 8 == arMagicBytes && validArEnvelope rlib rlib.len 8 then
    parseArLoop rlib rlib.len 8 [] []
  else
    []

/- A member's payload is exactly the window `[payloadOffset, payloadOffset + payloadSize)` of
    the archive. -/
end Qsag
