-- SPDX-License-Identifier: Apache-2.0 OR MIT
-- Generator for `lean_pack256_limbs56.jsonl`: evaluates the live `Qsag.pack256ToLimbs56` and
-- `Qsag.migrationNullifierInput` and prints one JSON object per line. Run from `lean/`:
--   lake env lean --run ../validation/tests/fixtures/lean_pack256_limbs56.gen.lean

import Qsag.Protocol.Migration.ActiveMigrationZeroTest

namespace Pack256Limbs56Oracle

open Qsag

def hex256 (x : Nat) : String :=
  let digits := Nat.toDigits 16 (x % 2 ^ 256)
  String.ofList (List.replicate (64 - digits.length) '0' ++ digits)

def jsonNats (xs : List Nat) : String :=
  "[" ++ String.intercalate "," (xs.map fun n => "\"" ++ toString n ++ "\"") ++ "]"

def limbs (x : Nat) : List Nat :=
  (List.finRange 5).map fun k => (pack256ToLimbs56 (BitVec.ofNat 256 x) k).val

def packRow (kind : String) (x : Nat) : String :=
  "{\"kind\":\"" ++ kind ++ "\",\"x\":\"" ++ hex256 x ++ "\",\"limbs\":" ++ jsonNats (limbs x) ++ "}"

/-- `count` values of the 256-bit affine recurrence `x ↦ a * x + c`, from `seed`. -/
def affineWalk (count : Nat) (seed : Nat) : List Nat :=
  let a := 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95
  let c := 0xd1b54a32d192ed03c2b2ae3d27d4eb4f165667b19e3779f9ff51afd7ed558ccd
  (List.range count).foldl
    (fun (acc : List Nat × Nat) _ =>
      let next := (a * acc.2 + c) % 2 ^ 256
      (acc.1 ++ [next], next))
    ([], seed) |>.1

/-- Byte `i` (big-endian position) holds `i + 1`: any byte permutation changes the value. -/
def byteRamp : Nat :=
  (List.range 32).foldl (fun acc i => acc * 256 + (i + 1)) 0

def byteRampReversed : Nat :=
  (List.range 32).foldl (fun acc i => acc * 256 + (32 - i)) 0

def packInputs : List (String × Nat) :=
  [("zero", 0), ("ones", 2 ^ 256 - 1), ("end_bytes", 2 ^ 248 + 1),
   ("byte_ramp", byteRamp), ("byte_ramp_reversed", byteRampReversed)]
  ++ (List.range 256).map (fun i => ("bit", 2 ^ i))
  ++ (List.range 256).map (fun i => ("clear_bit", 2 ^ 256 - 1 - 2 ^ i))
  ++ (List.range 255).map (fun i => ("adjacent_bits", 3 * 2 ^ i))
  ++ (List.range 32).map (fun j => ("byte_ff", 0xff * 2 ^ (8 * j)))
  ++ (List.range 257).map (fun i => ("low_run", 2 ^ i - 1))
  ++ (affineWalk 64 1).map (fun x => ("walk", x))

def groupName : ScalarGroup → String
  | .Secp256k1 => "secp256k1"
  | .Ed25519 => "ed25519"

def nullifierRow (group : ScalarGroup) (s domain : Nat) : String :=
  let input := (List.finRange 11).map fun i =>
    (migrationNullifierInput group (BitVec.ofNat 256 s) (BitVec.ofNat 256 domain) i).val
  "{\"kind\":\"nullifier_input\",\"group\":\"" ++ groupName group ++ "\",\"s\":\"" ++ hex256 s
    ++ "\",\"domain\":\"" ++ hex256 domain ++ "\",\"input\":" ++ jsonNats input ++ "}"

/-- Scalars below `2^252`, so each is canonical for both subgroups. -/
def nullifierScalars : List Nat :=
  [1, 2 ^ 248 + 1, byteRamp % 2 ^ 252] ++ (affineWalk 5 7).map (· % 2 ^ 252)

def nullifierDomains : List Nat :=
  [0, byteRampReversed] ++ affineWalk 2 11

def main : IO Unit := do
  for (kind, x) in packInputs do
    IO.println (packRow kind x)
  for group in [ScalarGroup.Secp256k1, ScalarGroup.Ed25519] do
    for s in nullifierScalars do
      for domain in nullifierDomains do
        IO.println (nullifierRow group s domain)

end Pack256Limbs56Oracle

def main : IO Unit := Pack256Limbs56Oracle.main
