module
/- Executable cross-language vectors. No golden answers or reimplemented primitives.
   Run scripts/cross_kat_runner.py --build on Linux; the canonical qsag-kat target builds this module.
   --cross-kat wire format: JSON Lines records [request, result], numeric values are decimal strings,
   byte strings are lowercase hex, field-extension limbs are c0.c0,c0.c1,c1.c0,c1.c1. -/
public import Qsag.BinaryTower
public import Qsag.Fips205
public import Qsag.SuccinctAggregationIop
public section
open Qsag
namespace CrossKat
private def csv (xs : List Nat) : String := String.intercalate "," (xs.map toString)
private def hex (bs : List UInt8) : String := String.ofList (bs.flatMap fun b =>
  ["0123456789abcdef".toList[b.toNat / 16]!, "0123456789abcdef".toList[b.toNat % 16]!])
private def seqBytes (n : Nat) : List UInt8 := (List.range n).map UInt8.ofNat
private def lane (n : Nat) : Lane4 :=
  ⟨Goldilocks.ofNat n, Goldilocks.ofNat (n+1), Goldilocks.ofNat (n+2), Goldilocks.ofNat (n+3)⟩
private def laneOut (x : Lane4) : String := csv [x.x0.val,x.x1.val,x.x2.val,x.x3.val]
private def e2Out (x : GoldilocksExt2) : String := csv [x.c0.val,x.c1.val]
private def e4Out (x : GoldilocksExt4) : String := csv [x.c0.c0.val,x.c0.c1.val,x.c1.c0.val,x.c1.c1.val]
private def emit (request result : String) : IO Unit :=
  IO.println ("[\"" ++ request ++ "\",\"" ++ result ++ "\"]")
-- JSON Lines keeps even the largest sponge vectors independently inspectable.
def run : IO Unit := do
  for a in [0,1,7,0x123456789abcdef0,18446744069414584320,18446744073709551615] do
    let b := 0xcafebabe12345678
    let x := Goldilocks.ofNat a
    let y := Goldilocks.ofNat b
    for (op,z) in [("add",Goldilocks.add x y),("sub",Goldilocks.sub x y),
                  ("mul",Goldilocks.mul x y),("inv",Goldilocks.inv x)] do
      emit s!"gold {op} {a} {b}" (toString z.val)
    let x2 : GoldilocksExt2 := ⟨x,y⟩
    let y2 : GoldilocksExt2 := ⟨Goldilocks.ofNat 17,Goldilocks.ofNat 31⟩
    for (op,z) in [("add",GoldilocksExt2.add x2 y2),("sub",GoldilocksExt2.sub x2 y2),
                  ("mul",GoldilocksExt2.mul x2 y2),("inv",GoldilocksExt2.inv x2)] do
      emit s!"ext2 {op} {a},{b} 17,31" (e2Out z)
    let x4 : GoldilocksExt4 := ⟨x2,y2⟩
    let y4 : GoldilocksExt4 := ⟨y2,x2⟩
    for (op,z) in [("add",GoldilocksExt4.add x4 y4),("sub",GoldilocksExt4.sub x4 y4),
                  ("mul",GoldilocksExt4.mul x4 y4),("inv",GoldilocksExt4.inv x4)] do
      emit s!"ext4 {op} {a},{b},17,31 17,31,{a},{b}" (e4Out z)
  emit "ext2 inv 0,0 0,0" (e2Out (GoldilocksExt2.inv GoldilocksExt2.zero))
  emit "ext4 inv 0,0,0,0 0,0,0,0" (e4Out (GoldilocksExt4.inv GoldilocksExt4.zero))
  for k in [3,4,5,6,7] do
    let width := 2^k
    for a in [0,1,0x53,2^(width-1),2^width-1,0x0123456789abcdeffedcba9876543210 % 2^width] do
      let b := 0xcafebabe00000001deadbeef87654321 % 2^width
      let x := unpackTower k (BitVec.ofNat width a)
      let y := unpackTower k (BitVec.ofNat width b)
      emit s!"tower mul {k} {a} {b}" (toString (packTower k (towerMul k x y)).toNat)
      emit s!"tower inv {k} {a} {b}" (toString (packTower k (towerInv k x)).toNat)
  for n in [0,1,135,136,137,271,272,273] do
    let msg := seqBytes n
    for outLen in [32,136,273] do
      emit s!"shake {outLen} {hex msg}" (hex (shake256Xof outLen msg))
      for custom in [[],[0,255],seqBytes 140] do
        emit s!"cshake {outLen} {hex custom} {hex msg}" (hex (cshake256Xof outLen custom msg))
  for n in [0,1,0x8000000000000000,0xffffffffffffffe0] do
    let word := fun i => UInt64.ofNat (if n == 0 then 0 else n+i)
    let st : KState :=
      ⟨word 0,word 1,word 2,word 3,word 4,word 5,word 6,word 7,word 8,word 9,word 10,word 11,word 12,word 13,word 14,word 15,word 16,word 17,word 18,word 19,word 20,word 21,word 22,word 23,word 24⟩
    let out := keccakF1600 st
    -- All 25 lanes, including capacity, serialized little endian.
    let lanes := [out.a0,out.a1,out.a2,out.a3,out.a4,out.a5,out.a6,out.a7,out.a8,out.a9,
      out.a10,out.a11,out.a12,out.a13,out.a14,out.a15,out.a16,out.a17,out.a18,out.a19,
      out.a20,out.a21,out.a22,out.a23,out.a24]
    emit s!"keccak {n}" (csv (lanes.map UInt64.toNat))
  for n in [0,1,18446744069414584315] do
    let a := lane n
    let b := lane (n+4)
    let c := lane (n+8)
    emit s!"poseidon {n}" (csv ((poseidon2Perm12 ⟨a,b,c⟩).toList.map (·.val)))
    emit s!"compress {n}" (laneOut (poseidon2Compress12FF a b c))
    emit s!"tree {n}" (laneOut (merkleNodeHash (Goldilocks.ofNat 42) c 1 0x123456789abcdef0 3 7 a b))
  for n in [16,24,32] do
    for value in [0,27,255] do
      let msg := List.replicate n (UInt8.ofNat value)
      emit s!"wotsplus {n} {value}" (csv (fipsWotsDigits (2*n) msg))
  for value in [0,26,27,255] do
    let msg := List.replicate 32 (UInt8.ofNat value)
    let digits := extractBaseWDigits 4 128 msg
    emit s!"wotsc {value}" (csv digits ++ ";" ++ toString (checkTargetSum 4 128 192 digits))
  for ty in [FipsAdrsType.wotsHash,.wotsPk,.tree,.forsTree,.forsRoots,.wotsPrf,.forsPrf] do
    for tree in [0,0x10000000000000001,2^96-1] do
      emit s!"adrs {ty.toCode} {tree}" (hex (encodeFips205Adrs (mkFipsAdrs 0x12345678 tree ty 0x87654321 0xffffffff 0xabcdef01)))
end CrossKat

-- Preserve the canonical JSON suite and FIPS 205 export interface as well as
-- the differential JSON Lines protocol, under one executable and Lake target.
namespace CanonicalKat

private def hexDigit (n : Nat) : Char :=
  let d := n % 16
  if d < 10 then Char.ofNat ('0'.toNat + d)
  else Char.ofNat ('a'.toNat + (d - 10))

private def byteToHex (b : UInt8) : String :=
  let v := b.toNat
  String.ofList [hexDigit (v / 16), hexDigit (v % 16)]

private def bytesToHex (bs : List UInt8) : String :=
  String.join (bs.map byteToHex)

private def asciiBytes (s : String) : List UInt8 :=
  s.toUTF8.toList

private def bitVec256FromBeBytes (bs : List UInt8) : BitVec 256 :=
  -- Pack 32 little-endian-indexed bytes `bs[0..32]` so `extractLsb' (8*i) 8 = bs[i]`.
  let rec go (idx : Nat) (rem : List UInt8) (acc : Nat) : Nat :=
    match rem with
    | [] => acc
    | b :: rest => go (idx + 1) rest (acc + b.toNat * (2 ^ (8 * idx)))
  BitVec.ofNat 256 (go 0 (bs.take 32) 0)

def run (args : List String) : IO Unit := do
  -- 1. SHAKE256 & cSHAKE256 vectors
  let shakeEmpty := bytesToHex (Qsag.shake256Xof 32 [])
  let shakeAbc   := bytesToHex (Qsag.shake256Xof 32 [0x61, 0x62, 0x63])
  let shake64In  := (List.range 64).map UInt8.ofNat
  let shakeSeq64 := bytesToHex (Qsag.shake256Xof 64 shake64In)
  let cshakeDom  := asciiBytes "QSAG.KAT.v1"
  let cshakeMsg  := asciiBytes "quantum-signature-aggregation"
  let cshakeOut  := bytesToHex (Qsag.cshake256Xof 32 cshakeDom cshakeMsg)

  -- 2. Goldilocks & GoldilocksExt2 vectors
  let gA := Qsag.Goldilocks.ofNat 0xFFFFFFFF00000000 -- p - 1 = -1
  let gB := Qsag.Goldilocks.ofNat 0x123456789ABCDEF0
  let gAdd := Qsag.Goldilocks.add gA gB
  let gSub := Qsag.Goldilocks.sub gA gB
  let gMul := Qsag.Goldilocks.mul gA gB
  let gInvB := Qsag.Goldilocks.inv gB
  let gPow7B := Qsag.sbox7 gB

  let eA : Qsag.GoldilocksExt2 := ⟨Qsag.Goldilocks.ofNat 0xCAFEBABE12345678, Qsag.Goldilocks.ofNat 0x0FEDCBA987654321⟩
  let eB : Qsag.GoldilocksExt2 := ⟨Qsag.Goldilocks.ofNat 0x1122334455667788, Qsag.Goldilocks.ofNat 0x99AABBCCDDEEFF00⟩
  let eMul : Qsag.GoldilocksExt2 := Qsag.CommRingOps.mul eA eB
  let eInvA : Qsag.GoldilocksExt2 := Qsag.GoldilocksExt2.inv eA

  -- 3. BinaryTower (GF(2^8) = T_3 and Tower128 = T_7) vectors
  let t3a := Qsag.unpackTower 3 (BitVec.ofNat 8 0x53)
  let t3b := Qsag.unpackTower 3 (BitVec.ofNat 8 0xCA)
  let t3Mul := (Qsag.packTower 3 (Qsag.towerMul 3 t3a t3b)).toNat
  let t3InvA := (Qsag.packTower 3 (Qsag.towerInv 3 t3a)).toNat

  let t7aBits : BitVec 128 := BitVec.ofNat 128 0x0123456789ABCDEF_FEDCBA9876543210
  let t7bBits : BitVec 128 := BitVec.ofNat 128 0xCAFEBABE00000001_deadbeef87654321
  let t7a := Qsag.unpackTower 7 t7aBits
  let t7b := Qsag.unpackTower 7 t7bBits
  let t7Mul := (Qsag.packTower 7 (Qsag.towerMul 7 t7a t7b)).toNat
  let t7InvA := (Qsag.packTower 7 (Qsag.towerInv 7 t7a)).toNat

  -- 4. Poseidon2 width-12 Goldilocks permutation & sponge vectors
  let pZeroPerm := (Qsag.poseidon2Perm12 ⟨Qsag.lane4Zero, Qsag.lane4Zero, Qsag.lane4Zero⟩).toList.map (·.val)
  let pSeqIn : Qsag.Poseidon2State12 :=
    ⟨⟨Qsag.Goldilocks.ofNat 0, Qsag.Goldilocks.ofNat 1, Qsag.Goldilocks.ofNat 2, Qsag.Goldilocks.ofNat 3⟩,
     ⟨Qsag.Goldilocks.ofNat 4, Qsag.Goldilocks.ofNat 5, Qsag.Goldilocks.ofNat 6, Qsag.Goldilocks.ofNat 7⟩,
     ⟨Qsag.Goldilocks.ofNat 8, Qsag.Goldilocks.ofNat 9, Qsag.Goldilocks.ofNat 10, Qsag.Goldilocks.ofNat 11⟩⟩
  let pSeqPerm := (Qsag.poseidon2Perm12 pSeqIn).toList.map (·.val)
  let pHashEmpty := bytesToHex (Qsag.poseidon2Hash32 [])
  let pHashZero1 := bytesToHex (Qsag.poseidon2Hash32 [0x00])
  let pHash123   := bytesToHex (Qsag.poseidon2Hash32 [0x01, 0x02, 0x03])
  let pHashLabel := bytesToHex (Qsag.poseidon2Hash32 (asciiBytes "qsag-poseidon2-kat"))

  -- 5. Aggregation Digest5 & BaseFold quartet vectors
  let rawDigestBytes := Qsag.shake256Xof 32 [0x61, 0x62, 0x63]
  let d5 := Qsag.digest5FromBitVec256 (bitVec256FromBeBytes rawDigestBytes)
  let q0 : Qsag.GoldilocksExt2 := ⟨Qsag.Goldilocks.ofNat 11, Qsag.Goldilocks.ofNat 22⟩
  let q1 : Qsag.GoldilocksExt2 := ⟨Qsag.Goldilocks.ofNat 33, Qsag.Goldilocks.ofNat 44⟩
  let q2 : Qsag.GoldilocksExt2 := ⟨Qsag.Goldilocks.ofNat 55, Qsag.Goldilocks.ofNat 66⟩
  let q3 : Qsag.GoldilocksExt2 := ⟨Qsag.Goldilocks.ofNat 77, Qsag.Goldilocks.ofNat 88⟩
  let ra : Qsag.GoldilocksExt2 := ⟨Qsag.Goldilocks.ofNat 9, Qsag.Goldilocks.ofNat 5⟩
  let rb : Qsag.GoldilocksExt2 := ⟨Qsag.Goldilocks.ofNat 13, Qsag.Goldilocks.ofNat 7⟩
  let bfFold := Qsag.basefoldQuartet q0 q1 q2 q3 ra rb

  -- 6. NIST FIPS 205 SLH-DSA-SHAKE-128f deterministic keygen + pure sign + verify
  let skSeed16 := (List.range 16).map (fun i => UInt8.ofNat (0x10 + i))
  let skPrf16  := (List.range 16).map (fun i => UInt8.ofNat (0x30 + i))
  let pkSeed16 := (List.range 16).map (fun i => UInt8.ofNat (0x50 + i))
  let (slhSk, slhPk) := Qsag.slhKeygenInternal Qsag.slhDsaShake128f skSeed16 skPrf16 pkSeed16
  let slhMsg := asciiBytes "qsag-fips205-kat"
  let slhSigOpt := Qsag.slhSignPure Qsag.slhDsaShake128f slhMsg [] slhSk pkSeed16
  let slhSig ← match slhSigOpt with
    | some s => pure s
    | none   => throw (IO.userError "slhSignPure unexpectedly returned none")
  let slhOk := Qsag.slhVerifyPure Qsag.slhDsaShake128f slhMsg slhSig [] slhPk
  if !slhOk then
    throw (IO.userError "FIDELITY FAILURE: slhVerifyPure returned false on Lean KAT!")
  let slhSigWire := Qsag.encodeSlhSig slhSig
  let slhPkWire  := slhPk.pkSeed ++ slhPk.pkRoot
  let slhSkWire  := slhSk.skSeed ++ slhSk.skPrf ++ slhPk.pkSeed ++ slhPk.pkRoot
  let slhSigShake := bytesToHex (Qsag.shake256Xof 32 slhSigWire)
  let slhSigHead64 := bytesToHex (slhSigWire.take 64)
  let slhSigTail64 := bytesToHex (slhSigWire.drop (slhSigWire.length - 64))

  match args with
  | ["--dump-fips205", outDir] =>
    IO.FS.writeBinFile (System.FilePath.mk (outDir ++ "/pk.bin")) (ByteArray.mk slhPkWire.toArray)
    IO.FS.writeBinFile (System.FilePath.mk (outDir ++ "/sk.bin")) (ByteArray.mk slhSkWire.toArray)
    IO.FS.writeBinFile (System.FilePath.mk (outDir ++ "/msg.bin")) (ByteArray.mk slhMsg.toArray)
    IO.FS.writeBinFile (System.FilePath.mk (outDir ++ "/sig.bin")) (ByteArray.mk slhSigWire.toArray)
  | _ => pure ()

  let fmtNatList (xs : List Nat) : String :=
    "[" ++ String.intercalate ", " (xs.map (fun x => "\"" ++ toString x ++ "\"")) ++ "]"

  let keccakZero := Qsag.keccakF1600 Qsag.zeroKState
  let keccakZeroLanes := [keccakZero.a0.toNat, keccakZero.a1.toNat, keccakZero.a2.toNat, keccakZero.a3.toNat, keccakZero.a4.toNat, keccakZero.a5.toNat, keccakZero.a6.toNat, keccakZero.a7.toNat, keccakZero.a8.toNat, keccakZero.a9.toNat, keccakZero.a10.toNat, keccakZero.a11.toNat, keccakZero.a12.toNat, keccakZero.a13.toNat, keccakZero.a14.toNat, keccakZero.a15.toNat, keccakZero.a16.toNat, keccakZero.a17.toNat, keccakZero.a18.toNat, keccakZero.a19.toNat, keccakZero.a20.toNat, keccakZero.a21.toNat, keccakZero.a22.toNat, keccakZero.a23.toNat, keccakZero.a24.toNat]
  let ext4Kat := Qsag.GoldilocksExt4.ofLimbs (Qsag.Goldilocks.ofNat 0)
    (Qsag.Goldilocks.ofNat 1) (Qsag.Goldilocks.ofNat 2) (Qsag.Goldilocks.ofNat 3)
  let hybridBound := Qsag.buildHybridBoundMessage (List.replicate 32 1)
    [2, 3] (List.replicate 64 4) [5, 0]
  let canopyLeaf0 := Qsag.shake256Xof 32 [0]
  let canopyLeaf1 := Qsag.shake256Xof 32 [1]
  let canopyNode := fun (i : Nat) (l r : List UInt8) =>
    Qsag.cshake256Xof 32 (asciiBytes "QSAG.PCS.CANOPY/v2")
      ([0] ++ (List.range 4).map (fun j => UInt8.ofNat (i / 256^j)) ++ l ++ r)
  let canopyRoot := fun (n : Nat) (top : List UInt8) =>
    Qsag.cshake256Xof 32 (asciiBytes "QSAG.PCS.CANOPY/v2") ([1, UInt8.ofNat n] ++ top)
  let canopyCommit := canopyRoot 1 (canopyNode 1 canopyLeaf0 canopyLeaf1)
  let canopyConcreteOk := Qsag.verifyCanopyMultiproof canopyNode canopyRoot
    1 canopyCommit [(0, canopyLeaf0)] [canopyLeaf1]
  if !canopyConcreteOk then throw (IO.userError "Concrete Canopy KAT failed")
  let canopyOk := Qsag.verifyCanopyMultiproof Qsag.canopyToyNodeHash Qsag.canopyToyRootHash
    3 Qsag.canopyToyCommitment Qsag.canopyToyLeaves Qsag.canopyToyProof
  let canopyExtra := Qsag.verifyCanopyMultiproof Qsag.canopyToyNodeHash Qsag.canopyToyRootHash
    3 Qsag.canopyToyCommitment Qsag.canopyToyLeaves (Qsag.canopyToyProof ++ [0])
  if !canopyOk || canopyExtra then throw (IO.userError "Canopy KAT failed")
  IO.println "{"
  IO.println "  \"suite\": \"qsag-kat-v1\","
  IO.println "  \"generator\": \"lean-4.35.0-Qsag\","
  IO.println s!"  \"keccak_f1600_zero_lanes\": {fmtNatList keccakZeroLanes},"
  IO.println s!"  \"ext4_canonical_0123\": \"{bytesToHex (Qsag.encodeExt4Bytes32 ext4Kat)}\","
  IO.println s!"  \"hybrid_bound_hex\": \"{bytesToHex hybridBound}\","
  IO.println s!"  \"canopy_depth1_root\": \"{bytesToHex canopyCommit}\","
  IO.println s!"  \"canopy_depth1_leaf0\": \"{bytesToHex canopyLeaf0}\","
  IO.println s!"  \"canopy_depth1_sibling1\": \"{bytesToHex canopyLeaf1}\","
  IO.println s!"  \"canopy_depth1_index0_accept\": {canopyConcreteOk},"
  IO.println s!"  \"canopy_toy_valid\": {canopyOk},"
  IO.println s!"  \"canopy_toy_extra_sibling\": {canopyExtra},"
  IO.println s!"  \"shake256_seq272_200\": \"{bytesToHex (Qsag.shake256Xof 200 ((List.range 272).map UInt8.ofNat))}\","
  IO.println s!"  \"cshake256_seq168_200\": \"{bytesToHex (Qsag.cshake256Xof 200 [0, 255] ((List.range 168).map UInt8.ofNat))}\","
  IO.println s!"  \"fips205_adrs\": \"{bytesToHex (Qsag.encodeFips205Adrs (Qsag.mkFipsAdrs 1 0x10000000000000001 .forsTree 2 3 4))}\","
  IO.println "  \"keccak\": {"
  IO.println s!"    \"shake256_empty_32\": \"{shakeEmpty}\","
  IO.println s!"    \"shake256_abc_32\": \"{shakeAbc}\","
  IO.println s!"    \"shake256_seq64_64\": \"{shakeSeq64}\","
  IO.println s!"    \"cshake256_custom_32\": \"{cshakeOut}\""
  IO.println "  },"
  IO.println "  \"goldilocks\": {"
  IO.println "    \"prime\": \"18446744069414584321\","
  IO.println s!"    \"a\": \"{gA.val}\","
  IO.println s!"    \"b\": \"{gB.val}\","
  IO.println s!"    \"add_ab\": \"{gAdd.val}\","
  IO.println s!"    \"sub_ab\": \"{gSub.val}\","
  IO.println s!"    \"mul_ab\": \"{gMul.val}\","
  IO.println s!"    \"inv_b\": \"{gInvB.val}\","
  IO.println s!"    \"sbox7_b\": \"{gPow7B.val}\","
  IO.println s!"    \"ext2_mul_c0\": \"{eMul.c0.val}\","
  IO.println s!"    \"ext2_mul_c1\": \"{eMul.c1.val}\","
  IO.println s!"    \"ext2_inv_a_c0\": \"{eInvA.c0.val}\","
  IO.println s!"    \"ext2_inv_a_c1\": \"{eInvA.c1.val}\""
  IO.println "  },"
  IO.println "  \"binary_tower\": {"
  IO.println s!"    \"gf256_a\": {0x53},"
  IO.println s!"    \"gf256_b\": {0xCA},"
  IO.println s!"    \"gf256_mul\": {t3Mul},"
  IO.println s!"    \"gf256_inv_a\": {t3InvA},"
  IO.println s!"    \"tower128_a_dec\": \"{t7aBits.toNat}\","
  IO.println s!"    \"tower128_b_dec\": \"{t7bBits.toNat}\","
  IO.println s!"    \"tower128_mul_dec\": \"{t7Mul}\","
  IO.println s!"    \"tower128_inv_a_dec\": \"{t7InvA}\""
  IO.println "  },"
  IO.println "  \"poseidon2_goldilocks_12\": {"
  IO.println s!"    \"perm_zero\": {fmtNatList pZeroPerm},"
  IO.println s!"    \"perm_seq_0_11\": {fmtNatList pSeqPerm},"
  IO.println s!"    \"hash32_empty\": \"{pHashEmpty}\","
  IO.println s!"    \"hash32_00\": \"{pHashZero1}\","
  IO.println s!"    \"hash32_010203\": \"{pHash123}\","
  IO.println s!"    \"hash32_label\": \"{pHashLabel}\""
  IO.println "  },"
  IO.println "  \"aggregation\": {"
  IO.println s!"    \"digest5_shake256_abc_le\": [\"{d5.limb0.val}\", \"{d5.limb1.val}\", \"{d5.limb2.val}\", \"{d5.limb3.val}\", \"{d5.limb4.val}\"],"
  IO.println s!"    \"basefold_quartet_c0\": \"{bfFold.c0.val}\","
  IO.println s!"    \"basefold_quartet_c1\": \"{bfFold.c1.val}\""
  IO.println "  },"
  IO.println "  \"fips205_slh_dsa_shake_128f\": {"
  IO.println s!"    \"sk_seed_hex\": \"{bytesToHex skSeed16}\","
  IO.println s!"    \"sk_prf_hex\": \"{bytesToHex skPrf16}\","
  IO.println s!"    \"pk_seed_hex\": \"{bytesToHex pkSeed16}\","
  IO.println s!"    \"pk_hex\": \"{bytesToHex slhPkWire}\","
  IO.println "    \"msg_ascii\": \"qsag-fips205-kat\","
  IO.println "    \"ctx_hex\": \"\","
  IO.println s!"    \"sig_bytes\": {slhSigWire.length},"
  IO.println s!"    \"lean_verify_pure\": true,"
  IO.println s!"    \"sig_shake256_32\": \"{slhSigShake}\","
  IO.println s!"    \"sig_head_64_hex\": \"{slhSigHead64}\","
  IO.println s!"    \"sig_tail_64_hex\": \"{slhSigTail64}\""
  IO.println "  }"
  IO.println "}"

end CanonicalKat

def main (args : List String) : IO Unit := do
  match args with
  | ["--cross-kat"] => CrossKat.run
  | [] => CanonicalKat.run []
  | ["--dump-fips205", outDir] =>
    IO.FS.createDirAll outDir
    CanonicalKat.run args
  | _ => throw (IO.userError "usage: qsag-kat [--cross-kat | --dump-fips205 DIR]")
