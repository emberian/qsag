module
/-
# `KatGen` — Deterministic Known-Answer Test (KAT) Vector Generator for `qsag`

Emits canonical JSON test vectors derived directly from the verified Lean 4.35 specifications
(`Qsag.Goldilocks`, `Qsag.BinaryTower`, `Qsag.Keccak`, `Qsag.Poseidon2`, `Qsag.Fips205`,
`Qsag.Aggregation`), and optionally dumps binary `SLH-DSA-SHAKE-128f` artifacts (`--dump-fips205 <dir>`)
for cross-verification against OpenSSL 3.5.
-/

public import Qsag.Goldilocks
public import Qsag.BinaryTower
public import Qsag.Keccak
public import Qsag.Poseidon2
public import Qsag.Fips205
public import Qsag.Aggregation
public import Qsag.SuccinctAggregationIop

public section

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

def main (args : List String) : IO Unit := do
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
