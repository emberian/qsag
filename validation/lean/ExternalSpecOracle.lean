-- SPDX-License-Identifier: Apache-2.0 OR MIT
-- Standalone Lean 4 executable specification oracle for external differential validation.
-- Evaluates live definitions in `Qsag.*` without modifying any library module in `lean/`.

import Qsag.Math.Goldilocks
import Qsag.Oracle.Poseidon2
import Qsag.Oracle.Keccak
import Qsag.Protocol.Signing.Fips205
import Qsag.Math.BinaryTower
import Qsag.Protocol.Aggregation.SuccinctAggregationIop
import Qsag.Protocol.Migration.ActiveMigrationZeroTest
import Qsag.Machine.ConstantTimeIsa

namespace ExternalSpecOracle

open Qsag

-- Curve parameters matching `lean/Qsag/PallasAndBlsMigration.lean` (inlined here so the
-- standalone oracle evaluates `Qsag.rcbSmul` cleanly even when proof-only modules are in flight).
def p_pallas : Nat := 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001
def p_bls381 : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
def r_bls381 : Nat := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
def orchardSpendAuthG : Weierstrass.Point :=
  some (0x375523b328f1d6063b8d187c3e5f445f0c7f0ce37b70a10c8d1a7284b875c963,
        0x1ad0357fdf1a66db7b10bcfcfed624fbdfc914fec005bdd84ce33e817b0c3bc9)
def bls381G1 : Weierstrass.Point :=
  some (0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb,
        0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1)

def hexDigit (n : Nat) : Char :=
  let d := n % 16
  if d < 10 then Char.ofNat (48 + d) else Char.ofNat (87 + d)

def bytesToHex (bs : List UInt8) : String :=
  String.ofList (bs.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])

def natToHexPad (widthBytes : Nat) (n : Nat) : String :=
  let bs := (List.range widthBytes).reverse.map fun i => UInt8.ofNat ((n / (256 ^ i)) % 256)
  bytesToHex bs

def natToLeHexPad (widthBytes : Nat) (n : Nat) : String :=
  let bs := (List.range widthBytes).map fun i => UInt8.ofNat ((n / (256 ^ i)) % 256)
  bytesToHex bs

def asciiBytes (s : String) : List UInt8 :=
  s.toUTF8.toList

def jsonStrList (xs : List String) : String :=
  "[" ++ String.intercalate ", " (xs.map fun s => "\"" ++ s ++ "\"") ++ "]"

def jsonNatStrList (xs : List Nat) : String :=
  jsonStrList (xs.map toString)

def powMod (fuel base exp modulus : Nat) : Nat :=
  match fuel with
  | 0 => 1 % modulus
  | k + 1 =>
    if exp == 0 then 1 % modulus
    else
      let half := powMod k base (exp / 2) modulus
      let sq := (half * half) % modulus
      if exp % 2 == 1 then (sq * (base % modulus)) % modulus else sq

structure RcbProjPoint where
  x : Nat
  y : Nat
  z : Nat

def toRcbProj : Weierstrass.Point → RcbProjPoint
  | none => ⟨0, 1, 0⟩
  | some (x, y) => ⟨x, y, 1⟩

def rcbAdd (p b3 : Nat) (P Q : RcbProjPoint) : RcbProjPoint :=
  let addM := fun u v => (u + v) % p
  let subM := fun u v => (u + p - (v % p)) % p
  let mulM := fun u v => (u * v) % p
  let t0 := mulM P.x Q.x
  let t1 := mulM P.y Q.y
  let zz := mulM P.z Q.z
  let t3 := subM (mulM (addM P.x P.y) (addM Q.x Q.y)) (addM t0 t1)
  let t4 := subM (mulM (addM P.y P.z) (addM Q.y Q.z)) (addM t1 zz)
  let y30 := subM (mulM (addM P.x P.z) (addM Q.x Q.z)) (addM t0 zz)
  let t03 := (3 * t0) % p
  let t2 := mulM b3 zz
  let z30 := addM t1 t2
  let t1s := subM t1 t2
  let cross := mulM b3 y30
  ⟨subM (mulM t3 t1s) (mulM t4 cross),
   addM (mulM t1s z30) (mulM cross t03),
   addM (mulM z30 t4) (mulM t03 t3)⟩

def rcbSmulFuel (p b3 : Nat) (base : RcbProjPoint) : Nat → Nat → RcbProjPoint
  | 0, _ => ⟨0, 1, 0⟩
  | fuel + 1, k =>
    if k == 0 then ⟨0, 1, 0⟩
    else
      let half := rcbSmulFuel p b3 base fuel (k / 2)
      let dbl := rcbAdd p b3 half half
      if k % 2 == 1 then rcbAdd p b3 dbl base else dbl

def rcbSmul (p b3 : Nat) (base : RcbProjPoint) (k : Nat) : RcbProjPoint :=
  rcbSmulFuel p b3 base 256 k

def projToAffine (p : Nat) (pt : RcbProjPoint) : Nat × Nat :=
  let zInv := powMod 384 (pt.z % p) (p - 2) p
  (((pt.x % p) * zInv) % p, ((pt.y % p) * zInv) % p)

def extPow (x : GoldilocksExt4) (n : Nat) : GoldilocksExt4 :=
  (List.range 64).foldl (fun acc i =>
    let acc := GoldilocksExt4.mul acc acc
    if n / 2 ^ (63 - i) % 2 == 1 then GoldilocksExt4.mul acc x else acc) GoldilocksExt4.one

def state12FromList (xs : List Nat) : Poseidon2State12 :=
  let g := fun i => Goldilocks.ofNat (xs.getD i 0)
  ⟨⟨g 0, g 1, g 2, g 3⟩, ⟨g 4, g 5, g 6, g 7⟩, ⟨g 8, g 9, g 10, g 11⟩⟩

def sha3_256Bytes (input : List UInt8) : List UInt8 :=
  squeezeXofAux 32 (absorbPadded (padForRate input 0x06))

def keccak256Bytes (input : List UInt8) : List UInt8 :=
  squeezeXofAux 32 (absorbPadded (padForRate input 0x01))

def padRate72 (bytes : List UInt8) (suffix : UInt8) : List UInt8 :=
  let count := 72 - bytes.length % 72
  if count = 1 then
    bytes ++ [suffix ^^^ (0x80 : UInt8)]
  else
    bytes ++ [suffix] ++ List.replicate (count - 2) 0 ++ [0x80]

def xorRate72 (s : KState) (block : List UInt8) : KState :=
  { s with
    a0 := s.a0 ^^^ loadLe64 block 0
    a1 := s.a1 ^^^ loadLe64 block 1
    a2 := s.a2 ^^^ loadLe64 block 2
    a3 := s.a3 ^^^ loadLe64 block 3
    a4 := s.a4 ^^^ loadLe64 block 4
    a5 := s.a5 ^^^ loadLe64 block 5
    a6 := s.a6 ^^^ loadLe64 block 6
    a7 := s.a7 ^^^ loadLe64 block 7
    a8 := s.a8 ^^^ loadLe64 block 8 }

def absorbBlocks72 : Nat → KState → List UInt8 → KState
  | 0, s, _ => s
  | k + 1, s, rest =>
    absorbBlocks72 k (keccakF1600 (xorRate72 s (rest.take 72))) (rest.drop 72)

def sha3_512Bytes (input : List UInt8) : List UInt8 :=
  squeezeXofAux 64 (absorbBlocks72 ((padRate72 input 0x06).length / 72) zeroKState (padRate72 input 0x06))

def main : IO Unit := do
  -- 1. Goldilocks base field & quartic extension edge vectors
  let glEdgeInputs : List (Nat × Nat) := [
    (0, 0),
    (1, 1),
    (0xFFFFFFFF, 0xFFFFFFFF),
    (0x100000000, 0xFFFFFFFF00000000),
    (0xFFFFFFFF00000000, 0xFFFFFFFF00000000),
    (0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF),
    (0x123456789ABCDEF0, 0xFEDCBA9876543213)
  ]
  let glJsonRows := glEdgeInputs.map fun (aRaw, bRaw) =>
    let a := Goldilocks.ofNat aRaw
    let b := Goldilocks.ofNat bRaw
    let addV := (Goldilocks.add a b).val
    let subV := (Goldilocks.sub a b).val
    let mulV := (Goldilocks.mul a b).val
    let invA := (Goldilocks.inv a).val
    let pow7A := (sbox7 a).val
    "{" ++
      s!"\"a_raw\":\"{aRaw}\",\"b_raw\":\"{bRaw}\"," ++
      s!"\"a_canon\":\"{a.val}\",\"b_canon\":\"{b.val}\"," ++
      s!"\"add\":\"{addV}\",\"sub\":\"{subV}\",\"mul\":\"{mulV}\"," ++
      s!"\"inv_a\":\"{invA}\",\"pow7_a\":\"{pow7A}\"" ++
    "}"

  let ext4Samples : List (List Nat × List Nat) := [
    ([0, 0, 0, 0], [1, 0, 0, 0]),
    ([1, 2, 3, 4], [5, 6, 7, 8]),
    ([0xFFFFFFFF00000000, 0xFFFFFFFF, 0x100000000, 7],
     [0xCAFEBABE12345678, 0x0FEDCBA987654321, 42, 99])
  ]
  let mkExt4 := fun (ls : List Nat) =>
    (⟨⟨Goldilocks.ofNat (ls.getD 0 0), Goldilocks.ofNat (ls.getD 1 0)⟩,
      ⟨Goldilocks.ofNat (ls.getD 2 0), Goldilocks.ofNat (ls.getD 3 0)⟩⟩ : GoldilocksExt4)
  let ext4Limbs := fun (x : GoldilocksExt4) =>
    [x.c0.c0.val, x.c0.c1.val, x.c1.c0.val, x.c1.c1.val]
  let ext4Rows := ext4Samples.map fun (xs, ys) =>
    let x := mkExt4 xs
    let y := mkExt4 ys
    let m := GoldilocksExt4.mul x y
    let invX := GoldilocksExt4.inv x
    let frobX := extPow x goldilocksPrime
    "{" ++
      s!"\"x\":{jsonNatStrList (ext4Limbs x)}," ++
      s!"\"y\":{jsonNatStrList (ext4Limbs y)}," ++
      s!"\"mul\":{jsonNatStrList (ext4Limbs m)}," ++
      s!"\"inv_x\":{jsonNatStrList (ext4Limbs invX)}," ++
      s!"\"frob_x\":{jsonNatStrList (ext4Limbs frobX)}" ++
    "}"

  -- 2. Poseidon2 width-12 & width-16 forward + inverse + sponge hash32
  let p12Inputs : List (List Nat) := [
    List.replicate 12 0,
    List.range 12,
    (List.range 12).map fun i => (0x9E3779B97F4A7C15 * (i + 1)) % goldilocksPrime,
    [0xFFFFFFFF00000000, 1, 2, 0xFFFFFFFF, 0x100000000, 7, 42, 99, 123456789, 987654321, 55, 0]
  ]
  let p12Rows ← p12Inputs.mapM fun words => do
    let st := state12FromList words
    let fwd := poseidon2Perm12 st
    let back := poseidon2Perm12Inv fwd
    if back.toList.map (·.val) != st.toList.map (·.val) then
      throw (IO.userError "Poseidon2-12 inverse mismatch in Lean spec")
    let invOfIn := poseidon2Perm12Inv st
    let reFwd := poseidon2Perm12 invOfIn
    if reFwd.toList.map (·.val) != st.toList.map (·.val) then
      throw (IO.userError "Poseidon2-12 right-inverse mismatch in Lean spec")
    pure ("{" ++
      s!"\"input\":{jsonNatStrList (st.toList.map (·.val))}," ++
      s!"\"perm\":{jsonNatStrList (fwd.toList.map (·.val))}," ++
      s!"\"inv\":{jsonNatStrList (invOfIn.toList.map (·.val))}" ++
    "}")

  let pHashLens : List Nat := [0, 1, 7, 8, 55, 56, 57, 136]
  let pHashRows := pHashLens.map fun len =>
    let msg := (List.range len).map fun i => UInt8.ofNat ((i * 37 + 11) % 256)
    "{" ++
      s!"\"msg_hex\":\"{bytesToHex msg}\"," ++
      s!"\"poseidon2_hash32_hex\":\"{bytesToHex (poseidon2Hash32 msg)}\"" ++
    "}"

  -- 3. Keccak / SHA3 / SHAKE256 / cSHAKE256 across rate boundaries
  let spongeLens : List Nat := [0, 1, 63, 64, 65, 71, 72, 73, 135, 136, 137, 271, 272, 273]
  let spongeRows := spongeLens.map fun len =>
    let msg := (List.range len).map fun i => UInt8.ofNat ((i * 29 + 5) % 256)
    let custom := asciiBytes "QSAG.EXTERNAL.SPEC"
    "{" ++
      s!"\"len\":{len}," ++
      s!"\"msg_hex\":\"{bytesToHex msg}\"," ++
      s!"\"sha3_256_hex\":\"{bytesToHex (sha3_256Bytes msg)}\"," ++
      s!"\"sha3_512_hex\":\"{bytesToHex (sha3_512Bytes msg)}\"," ++
      s!"\"keccak256_hex\":\"{bytesToHex (keccak256Bytes msg)}\"," ++
      s!"\"shake256_64_hex\":\"{bytesToHex (shake256Xof 64 msg)}\"," ++
      s!"\"cshake256_64_hex\":\"{bytesToHex (cshake256Xof 64 custom msg)}\"" ++
    "}"

  -- 4. BinaryTower T_3 (GF(2^8)) + ConstantTimeIsa GFNI isomorphism & T_7 (GF(2^128))
  let gf256Pairs : List (Nat × Nat) := [
    (0x00, 0x53), (0x01, 0xCA), (0x53, 0xCA), (0xFF, 0xFF), (0x80, 0x80), (0xA5, 0x3C)
  ]
  let gf256Rows ← gf256Pairs.mapM fun (a, b) => do
    let ta := unpackTower 3 (BitVec.ofNat 8 a)
    let tb := unpackTower 3 (BitVec.ofNat 8 b)
    let tMul := (packTower 3 (towerMul 3 ta tb)).toNat
    let tInv := (packTower 3 (towerInv 3 ta)).toNat
    let isaMul := (Qsag.ConstantTimeIsa.gfniT3MulByte (BitVec.ofNat 8 a) (BitVec.ofNat 8 b)).toNat
    let phiA := (Qsag.ConstantTimeIsa.gfniPhi (BitVec.ofNat 8 a)).toNat
    let phiB := (Qsag.ConstantTimeIsa.gfniPhi (BitVec.ofNat 8 b)).toNat
    if tMul != isaMul then
      throw (IO.userError "GFNI T3 isomorphism mismatch in Lean spec")
    pure ("{" ++
      s!"\"a\":{a},\"b\":{b},\"t3_mul\":{tMul},\"t3_inv_a\":{tInv}," ++
      s!"\"phi_a\":{phiA},\"phi_b\":{phiB}" ++
    "}")

  let t7Pairs : List (Nat × Nat) := [
    (0, 1),
    (1, 0xCAFEBABE00000001DEADBEEF87654321),
    (0x0123456789ABCDEFFEDCBA9876543210, 0xCAFEBABE00000001DEADBEEF87654321),
    ((2 ^ 128) - 1, (2 ^ 127) + 12345)
  ]
  let t7Rows := t7Pairs.map fun (a, b) =>
    let ta := unpackTower 7 (BitVec.ofNat 128 a)
    let tb := unpackTower 7 (BitVec.ofNat 128 b)
    let m := (packTower 7 (towerMul 7 ta tb)).toNat
    let invA := (packTower 7 (towerInv 7 ta)).toNat
    "{" ++
      s!"\"a_le_hex\":\"{natToLeHexPad 16 a}\"," ++
      s!"\"b_le_hex\":\"{natToLeHexPad 16 b}\"," ++
      s!"\"mul_le_hex\":\"{natToLeHexPad 16 m}\"," ++
      s!"\"inv_a_le_hex\":\"{natToLeHexPad 16 invA}\"" ++
    "}"

  -- 5. Elliptic-curve scalar multiples via verified Lean `rcbSmul` (secp256k1, Pallas, BLS12-381)
  let scalars : List Nat := [
    1,
    2,
    42,
    0xDEADBEEFCAFEBABE0123456789ABCDEF112233445566778899AABBCCDDEEFF01 % r_bls381
  ]
  let secpRows := scalars.map fun k =>
    let proj := rcbSmul Weierstrass.SECP256K1_FIELD_P 21 (toRcbProj Weierstrass.secp256k1G) k
    let (ax, ay) := projToAffine Weierstrass.SECP256K1_FIELD_P proj
    let negK := (secpNegScalar (BitVec.ofNat 256 k)).toNat
    "{" ++
      s!"\"scalar_be_hex\":\"{natToHexPad 32 k}\"," ++
      s!"\"neg_scalar_be_hex\":\"{natToHexPad 32 negK}\"," ++
      s!"\"x_be_hex\":\"{natToHexPad 32 ax}\"," ++
      s!"\"y_be_hex\":\"{natToHexPad 32 ay}\"" ++
    "}"

  let pallasRows := scalars.map fun k =>
    let projSpend := rcbSmul p_pallas 15 (toRcbProj orchardSpendAuthG) k
    let (sx, sy) := projToAffine p_pallas projSpend
    let mutCompressed :=
      let bs := (List.range 32).map fun i => UInt8.ofNat ((sx / (256 ^ i)) % 256)
      let top := (bs.getD 31 0) ||| (if sy % 2 == 1 then (0x80 : UInt8) else 0)
      bs.take 31 ++ [top]
    "{" ++
      s!"\"scalar_le_hex\":\"{natToLeHexPad 32 k}\"," ++
      s!"\"spend_auth_x_le_hex\":\"{natToLeHexPad 32 sx}\"," ++
      s!"\"spend_auth_y_le_hex\":\"{natToLeHexPad 32 sy}\"," ++
      s!"\"spend_auth_compressed_hex\":\"{bytesToHex mutCompressed}\"" ++
    "}"

  let blsRows := scalars.map fun k =>
    let proj := rcbSmul p_bls381 12 (toRcbProj bls381G1) k
    let (bx, byCoord) := projToAffine p_bls381 proj
    let yLexLargest := decide (2 * byCoord > p_bls381)
    let xBe := (List.range 48).reverse.map fun i => UInt8.ofNat ((bx / (256 ^ i)) % 256)
    let b0 := (xBe.getD 0 0) ||| (0x80 : UInt8) ||| (if yLexLargest then (0x20 : UInt8) else 0)
    let comp48 := [b0] ++ xBe.drop 1
    "{" ++
      s!"\"scalar_be_hex\":\"{natToHexPad 32 k}\"," ++
      s!"\"x_be_hex\":\"{natToHexPad 48 bx}\"," ++
      s!"\"y_be_hex\":\"{natToHexPad 48 byCoord}\"," ++
      s!"\"g1_compressed_48_hex\":\"{bytesToHex comp48}\"" ++
    "}"

  -- 6. NIST FIPS 205 SLH-DSA-SHAKE-128f full Lean-generated keypair + signature with context
  let skSeed := (List.range 16).map fun i => UInt8.ofNat (0x21 + i * 3)
  let skPrf  := (List.range 16).map fun i => UInt8.ofNat (0x61 + i * 5)
  let pkSeed := (List.range 16).map fun i => UInt8.ofNat (0x91 + i * 7)
  let ctx    := asciiBytes "lean-fips205-ctx"
  let msg    := asciiBytes "lean-spec-cross-checked-by-upstream-fips205"
  let (slhSk, slhPk) := slhKeygenInternal slhDsaShake128f skSeed skPrf pkSeed
  let optRand := pkSeed
  let sig ← match slhSignPure slhDsaShake128f msg ctx slhSk optRand with
    | some s => pure s
    | none => throw (IO.userError "slhSignPure returned none")
  if !(slhVerifyPure slhDsaShake128f msg sig ctx slhPk) then
    throw (IO.userError "slhVerifyPure rejected Lean signature")
  let sigWire := encodeSlhSig sig
  let pkWire  := slhPk.pkSeed ++ slhPk.pkRoot
  let skWire  := slhSk.skSeed ++ slhSk.skPrf ++ slhPk.pkSeed ++ slhPk.pkRoot

  -- 7. NIST FIPS 205 SLH-DSA-SHAKE-128s (`m = 30 = 21 + 7 + 2`) `H_msg` + index-splitting
  --    regression vector (`slhDsaShake128s_wellFormed`, `tooth_slhDsaShake128s_m34_rejected`)
  let pkRoot128s := (List.range 16).map fun i => UInt8.ofNat (0xA5 + i * 3)
  let msg128s := asciiBytes "lean-fips205-128s-m30-hmsg-oracle"
  let ctx128s := asciiBytes "fips205-128s-ctx"
  let mPrime128s ← match encodePureMsgPrime ctx128s msg128s with
    | some mp => pure mp
    | none => throw (IO.userError "encodePureMsgPrime returned none")
  let rRand128s := fipsPrfMsg slhDsaShake128s.n skPrf optRand mPrime128s
  let digest128s := fipsHMsg slhDsaShake128s.m rRand128s pkSeed pkRoot128s mPrime128s
  if digest128s.length != 30 then
    throw (IO.userError s!"expected 30-byte 128s H_msg, got {digest128s.length}")
  let (md128s, idxTree128s, idxLeaf128s) := fipsSplitDigest slhDsaShake128s digest128s
  let forsIndices128s := base2b md128s slhDsaShake128s.a slhDsaShake128s.k
  let forsLeaf0_128s :=
    fipsForsNode slhDsaShake128s skSeed pkSeed idxTree128s idxLeaf128s 0 (forsIndices128s.getD 0 0)

  -- 8. Ed25519 RFC 8032 clamping & SLIP-0010 scalar normalization mod `ED25519_ORDER_L`
  let edRawInputs : List Nat := [
    0,
    (2 ^ 256) - 1,
    ED25519_ORDER_L,
    ED25519_ORDER_L + 7,
    0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7,
    0x8000000000000000000000000000000000000000000000000000000000000007
  ]
  let edRows := edRawInputs.map fun rawNat =>
    let rawBv : BitVec 256 := BitVec.ofNat 256 rawNat
    let clampedNat := (clampEd25519Bytes32 rawBv).toNat
    let normNat := (normalizeSlip0010Ed25519Scalar rawBv).toNat
    "{" ++
      s!"\"raw_le_hex\":\"{natToLeHexPad 32 rawNat}\"," ++
      s!"\"clamped_le_hex\":\"{natToLeHexPad 32 clampedNat}\"," ++
      s!"\"normalized_mod_l_le_hex\":\"{natToLeHexPad 32 normNat}\"" ++
    "}"

  IO.println "{"
  IO.println "  \"generator\": \"lean-4.35.0-ExternalSpecOracle\","
  IO.println ("  \"goldilocks_edges\": [" ++ String.intercalate ", " glJsonRows ++ "],")
  IO.println ("  \"goldilocks_ext4\": [" ++ String.intercalate ", " ext4Rows ++ "],")
  IO.println ("  \"poseidon2_12\": [" ++ String.intercalate ", " p12Rows ++ "],")
  IO.println ("  \"poseidon2_hash32\": [" ++ String.intercalate ", " pHashRows ++ "],")
  IO.println ("  \"sponges\": [" ++ String.intercalate ", " spongeRows ++ "],")
  IO.println ("  \"gf256_tower_gfni\": [" ++ String.intercalate ", " gf256Rows ++ "],")
  IO.println ("  \"tower128\": [" ++ String.intercalate ", " t7Rows ++ "],")
  IO.println ("  \"secp256k1_smul\": [" ++ String.intercalate ", " secpRows ++ "],")
  IO.println ("  \"pallas_orchard_smul\": [" ++ String.intercalate ", " pallasRows ++ "],")
  IO.println ("  \"bls12_381_g1_smul\": [" ++ String.intercalate ", " blsRows ++ "],")
  IO.println ("  \"ed25519_clamp_slip0010\": [" ++ String.intercalate ", " edRows ++ "],")
  IO.println "  \"fips205_slh_dsa_shake_128s_hmsg\": {"
  IO.println s!"    \"m_bytes\": {slhDsaShake128s.m},"
  IO.println s!"    \"md_bytes\": {slhDsaShake128s.mdBytes},"
  IO.println s!"    \"tree_bytes\": {slhDsaShake128s.treeBytes},"
  IO.println s!"    \"leaf_bytes\": {slhDsaShake128s.leafBytes},"
  IO.println s!"    \"sk_seed_hex\": \"{bytesToHex skSeed}\","
  IO.println s!"    \"sk_prf_hex\": \"{bytesToHex skPrf}\","
  IO.println s!"    \"pk_seed_hex\": \"{bytesToHex pkSeed}\","
  IO.println s!"    \"pk_root_hex\": \"{bytesToHex pkRoot128s}\","
  IO.println s!"    \"opt_rand_hex\": \"{bytesToHex optRand}\","
  IO.println s!"    \"ctx_hex\": \"{bytesToHex ctx128s}\","
  IO.println s!"    \"msg_hex\": \"{bytesToHex msg128s}\","
  IO.println s!"    \"r_rand_hex\": \"{bytesToHex rRand128s}\","
  IO.println s!"    \"h_msg_30_hex\": \"{bytesToHex digest128s}\","
  IO.println s!"    \"md_21_hex\": \"{bytesToHex md128s}\","
  IO.println s!"    \"idx_tree\": \"{idxTree128s}\","
  IO.println s!"    \"idx_leaf\": {idxLeaf128s},"
  IO.println ("    \"fors_indices\": " ++ jsonNatStrList forsIndices128s ++ ",")
  IO.println s!"    \"fors_leaf0_hex\": \"{bytesToHex forsLeaf0_128s}\""
  IO.println "  },"
  IO.println "  \"fips205_slh_dsa_shake_128f\": {"
  IO.println s!"    \"sk_seed_hex\": \"{bytesToHex skSeed}\","
  IO.println s!"    \"sk_prf_hex\": \"{bytesToHex skPrf}\","
  IO.println s!"    \"pk_seed_hex\": \"{bytesToHex pkSeed}\","
  IO.println s!"    \"opt_rand_hex\": \"{bytesToHex optRand}\","
  IO.println s!"    \"ctx_hex\": \"{bytesToHex ctx}\","
  IO.println s!"    \"msg_hex\": \"{bytesToHex msg}\","
  IO.println s!"    \"pk_hex\": \"{bytesToHex pkWire}\","
  IO.println s!"    \"sk_hex\": \"{bytesToHex skWire}\","
  IO.println s!"    \"sig_hex\": \"{bytesToHex sigWire}\""
  IO.println "  }"
  IO.println "}"

end ExternalSpecOracle

def main : IO Unit := ExternalSpecOracle.main
