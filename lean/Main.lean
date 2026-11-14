module
/- Executable cross-language vectors. No golden answers or reimplemented primitives.
   Run scripts/cross_kat_runner.py --build on Linux; the existing KatGen target is preserved.
   Wire format: JSON array of [request, result], numeric values are decimal strings,
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
  for n in [0,1,136,200] do
    let st := xorRate136 zeroKState (seqBytes n)
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
  for value in [0,27,28,255] do
    let msg := List.replicate 32 (UInt8.ofNat value)
    let digits := extractBaseWDigits 4 128 msg
    emit s!"wotsc {value}" (csv digits ++ ";" ++ toString (checkTargetSum 4 128 192 digits))
  for ty in [FipsAdrsType.wotsHash,.wotsPk,.tree,.forsTree,.forsRoots,.wotsPrf,.forsPrf] do
    for tree in [0,0x10000000000000001,2^96-1] do
      emit s!"adrs {ty.toCode} {tree}" (hex (encodeFips205Adrs (mkFipsAdrs 0x12345678 tree ty 0x87654321 0xffffffff 0xabcdef01)))
end CrossKat

def main : IO Unit := CrossKat.run
