import Qsag.HashSigs
import Qsag.Fips205
import Qsag.BinaryTower
import Qsag.SuccinctAggregationIop
import Qsag.ThresholdMlDsaAndToprf
import Qsag.JortsBeltLatchAndQuorumSwitching
import Qsag.PosixCrashWal

/- Streaming protocol: tab-separated operation and arguments; bytes are lowercase hex,
   integers decimal, lists comma-separated. One response per line; errors do not stop the stream.
   Wrappers call the live specifications. Poseidon2 is width 12 in this repository. -/
namespace SpecOracle
open Qsag

def hex (bs : List UInt8) : String :=
  String.ofList (bs.flatMap fun b =>
    ["0123456789abcdef".toList[b.toNat / 16]!, "0123456789abcdef".toList[b.toNat % 16]!])

def unhex (s : String) : Except String (List UInt8) := do
  let cs := s.toList
  if cs.length % 2 != 0 then throw "odd hex length"
  let ns ← cs.mapM fun c =>
    if '0' ≤ c && c ≤ '9' then pure (c.toNat - 48)
    else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 87)
    else throw "invalid hex"
  return (List.range (ns.length / 2)).map fun i => UInt8.ofNat (16 * ns[2*i]! + ns[2*i+1]!)

def requireSome (x : Option α) (message : String) : Except String α :=
  match x with
  | some a => .ok a
  | none => .error message

def nat (s : String) : Except String Nat := requireSome s.toNat? "invalid integer"
def nums (s : String) : Except String (List Nat) :=
  if s.isEmpty then pure [] else (s.splitOn ",").mapM nat

def csv (ns : List Nat) : String := String.intercalate "," (ns.map toString)
def bool (b : Bool) : String := if b then "true" else "false"

def canopyNode (i : Nat) (l r : List UInt8) : List UInt8 :=
  cshake256Xof 32 "QSAG.PCS.CANOPY/v2".toUTF8.toList
    ([0] ++ (List.range 4).map (fun j => UInt8.ofNat (i / 256^j)) ++ l ++ r)
def canopyRoot (n : Nat) (t : List UInt8) : List UInt8 :=
  cshake256Xof 32 "QSAG.PCS.CANOPY/v2".toUTF8.toList ([1, UInt8.ofNat n] ++ t)

def walEvent (s : String) : Except String MultiCrashWalEvent := do
  match s with
  | "sign" => return .signAtomic 1 [42] {}
  | "hold" => return .beginReserveHoldLock 1 [42] {}
  | "finish" => return .finishSignFromHold
  | "contend" => return .contenderSignAttempt 2 [43]
  | "panic" => return .kernelPanic
  | "power" => return .powerLoss .revertToNand .dropAllVolatile []
  | "unlink" => return .unlinkLockSidecar
  | "delete" => return .deleteWalRecord
  | _ => throw "unknown WAL event"

/-- Binary exponentiation using the executable extension multiplication. -/
def extPow (x : GoldilocksExt4) (n : Nat) : GoldilocksExt4 :=
  (List.range 64).foldl (fun acc i =>
    let acc := GoldilocksExt4.mul acc acc
    if n / 2^(63-i) % 2 == 1 then GoldilocksExt4.mul acc x else acc) GoldilocksExt4.one

def latchTrace (events : String) : Except String String := do
  let mut st := BeltLatchNodeState.init 12 64
  let mut out := []
  for event in events.splitOn "," do
    if event == "crash" then st := beltLatchCrashAndRecover st
    else if event == "fail" then st := { st with failNextPersist := true }
    else
      let fields ← (event.splitOn ":").mapM nat
      if fields.length != 4 then throw "latch event arity"
      let record : BeltLatchRecord := ⟨UInt64.ofNat fields[0]!,
        BitVec.ofNat 256 fields[1]!, BitVec.ofNat 256 fields[2]!, [UInt8.ofNat fields[3]!]⟩
      match beltLatchBindStep st record with
      | .accepted next _ => st := next; out := out ++ ["true"]
      | .rejected next _ => st := next; out := out ++ ["false"]
  return String.intercalate "," out ++ ";" ++ toString st.nextEpoch ++ ";" ++ bool st.walPoisoned

def eval (args : List String) : Except String String := do
  match args with
  -- Current production ledger uses authenticated snapshots, not CRC. This
  -- adapter table models post-authentication availability of generations 2/1.
  | ["ledger", a, b, anchor] =>
    let a ← nat a
    let b ← nat b
    let anchor ← nat anchor
    if a == 0 && anchor ≤ 2 then return "2"
    else if b == 0 && anchor ≤ 1 then return "1"
    else return "reject"
  | ["latchtrace", events] => latchTrace events
  | ["poseidonhash", m] => return hex (poseidon2Hash32 (← unhex m))
  | ["binary", level, op, a, b] =>
    let k ← nat level
    if k != 3 && k != 7 then throw "tower level"
    let x := unpackTower k (BitVec.ofNat (2^k) (← nat a))
    let y := unpackTower k (BitVec.ofNat (2^k) (← nat b))
    let z ← match op with
      | "add" => pure (towerAdd k x y)
      | "mul" => pure (towerMul k x y)
      | "square" => pure (towerMul k x x)
      | "inv" => pure (towerInv k x)
      | _ => throw "binary operation"
    return toString (packTower k z).toNat
  | ["rounding", r, z, hint] =>
    let r := Fq204.ofNat (← nat r)
    let z := Fq204.ofNat (← nat z)
    let a := power2Round r
    let b := decompose r
    return String.intercalate "," [toString a.1, toString a.2, toString b.1,
      toString b.2, bool (makeHint z r), toString (useHint ((← nat hint) == 1) r)]
  | ["hem", v0, v1, x, theta, alpha, beta] =>
    let dec := fun s => do requireSome (decodeExt4Bytes32 (← unhex s)) "extension"
    let v0 ← dec v0
    let v1 ← dec v1
    let x := Goldilocks.ofNat (← nat x)
    let theta ← dec theta
    let alpha ← dec alpha
    let beta ← dec beta
    let half := Goldilocks.inv (Goldilocks.ofNat 2)
    let even := GoldilocksExt4.mul (GoldilocksExt4.add v0 v1) (GoldilocksExt4.embedBase half)
    let odd := GoldilocksExt4.mul (GoldilocksExt4.sub v0 v1)
      (GoldilocksExt4.embedBase (Goldilocks.mul half (Goldilocks.inv x)))
    let mix := GoldilocksExt4.add even (GoldilocksExt4.mul theta odd)
    return hex (encodeExt4Bytes32 (GoldilocksExt4.add odd
      (GoldilocksExt4.mul (GoldilocksExt4.add alpha
        (GoldilocksExt4.mul beta (GoldilocksExt4.embedBase (Goldilocks.mul x x)))) mix)))
  | ["shake" , n, m] => return hex (shake256Xof (← nat n) (← unhex m))
  | ["cshake", n, d, m] => return hex (cshake256Xof (← nat n) (← unhex d) (← unhex m))
  | ["sha3", m] => return hex (squeezeXofAux 32 (absorbPadded (padForRate (← unhex m) 6)))
  | ["gold", op, a, b] =>
    let x := Goldilocks.ofNat (← nat a)
    let y := Goldilocks.ofNat (← nat b)
    let z ← match op with
      | "add" => pure (Goldilocks.add x y)
      | "sub" => pure (Goldilocks.sub x y)
      | "mul" => pure (Goldilocks.mul x y)
      | "square" => pure (Goldilocks.mul x x)
      | "inv" => pure (Goldilocks.inv x)
      | _ => throw "unknown field operation"
    return toString z.val
  | ["extdecode", a] => return match decodeExt4Bytes32 (← unhex a) with
      | none => "reject"
      | some x => hex (encodeExt4Bytes32 x)
  | ["ext", op, a, b] =>
    let x ← requireSome (decodeExt4Bytes32 (← unhex a)) "noncanonical extension"
    let y ← requireSome (decodeExt4Bytes32 (← unhex b)) "noncanonical extension"
    let z ← match op with
      | "add" => pure (GoldilocksExt4.add x y)
      | "sub" => pure (GoldilocksExt4.sub x y)
      | "square" => pure (GoldilocksExt4.mul x x)
      | "frobenius" => pure (extPow x 18446744069414584321)
      | "mul" => pure (GoldilocksExt4.mul x y)
      | "inv" => pure (GoldilocksExt4.inv x)
      | _ => throw "unknown extension operation"
    return hex (encodeExt4Bytes32 z)
  | ["tower", a, b] =>
    let x := unpackTower 7 (BitVec.ofNat 128 (← nat a))
    let y := unpackTower 7 (BitVec.ofNat 128 (← nat b))
    return toString (packTower 7 (towerMul 7 x y)).toNat
  | ["wots", m] =>
    let d ← requireSome (extractBaseWDigitsChecked 4 128 (← unhex m)) "digest length"
    return csv d ++ ";" ++ bool (checkTargetSum 4 128 192 d)
  | ["hybrid", id, p, q, m] =>
    return hex (buildHybridBoundMessage (← unhex id) (← unhex p) (← unhex q) (← unhex m))
  | ["fors", seed, tree, kp, j, u, secret] =>
    return hex (forsIndexedLeafHash cshake256Suite (← unhex seed) (UInt64.ofNat (← nat tree))
      (← nat kp) (← nat j) (← nat u) (← unhex secret))
  | ["forsnode", seed, tree, kp, height, index, left, right] =>
    let adrs : HashAdrs := ⟨0, UInt64.ofNat (← nat tree), .forsTree,
      UInt32.ofNat (← nat kp), UInt32.ofNat (← nat height), UInt32.ofNat (← nat index)⟩
    return hex (thNodeH cshake256Suite (← unhex seed) adrs (← unhex left) (← unhex right))
  | ["adrs", layer, tree, ty, kp, f5, f6] =>
    let t ← match (← nat ty) with
      | 0 => pure FipsAdrsType.wotsHash
      | 1 => pure .wotsPk
      | 2 => pure .tree
      | 3 => pure .forsTree
      | 4 => pure .forsRoots
      | 5 => pure .wotsPrf
      | 6 => pure .forsPrf
      | _ => throw "address type"
    return hex (encodeFips205Adrs (mkFipsAdrs (← nat layer) (← nat tree) t
      (← nat kp) (← nat f5) (← nat f6)))
  | ["canopy", depth, root, indices, hashes, siblings] =>
    let ix ← nums indices
    let hs ← if hashes.isEmpty then pure [] else (hashes.splitOn ",").mapM unhex
    let ss ← if siblings.isEmpty then pure [] else (siblings.splitOn ",").mapM unhex
    if ix.length != hs.length then throw "leaf count"
    return bool (verifyCanopyMultiproof canopyNode canopyRoot (← nat depth) (← unhex root) (ix.zip hs) ss)
  | ["wal", events] =>
    let mac := fun k m => cshake256Xof 32 k m
    let s ← requireSome (initProvisionedCustodyState 1 ⟨[119]⟩ .beltLatch
      (List.replicate 32 1) (List.replicate 32 2) 10000 mac [3]) "provision"
    let es ← (events.splitOn ",").mapM walEvent
    let mut st := s
    let mut accepted := []
    for e in es do
      let (next, receipt) := stepMultiCrashCustody mac [3] st e
      accepted := accepted ++ [bool receipt.isSome]
      st := next
    return String.intercalate "," accepted ++ ";" ++ csv (st.emittedReceipts.map (·.epoch)) ++
      ";" ++ toString st.ghostWatermark ++ ";" ++ bool st.activeHold.isSome
  | ["keccak", words] =>
    let ns ← nums words
    if ns.length != 25 then throw "state width"
    let w := fun i => UInt64.ofNat ns[i]!
    let s := keccakF1600 ⟨w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7, w 8, w 9, w 10, w 11, w 12, w 13, w 14, w 15, w 16, w 17, w 18, w 19, w 20, w 21, w 22, w 23, w 24⟩
    return csv [s.a0.toNat, s.a1.toNat, s.a2.toNat, s.a3.toNat, s.a4.toNat, s.a5.toNat, s.a6.toNat, s.a7.toNat, s.a8.toNat, s.a9.toNat, s.a10.toNat, s.a11.toNat, s.a12.toNat, s.a13.toNat, s.a14.toNat, s.a15.toNat, s.a16.toNat, s.a17.toNat, s.a18.toNat, s.a19.toNat, s.a20.toNat, s.a21.toNat, s.a22.toNat, s.a23.toNat, s.a24.toNat]
  | ["poseidon", words] =>
    let ns ← nums words
    if ns.length != 12 then throw "state width"
    let w := fun i => Goldilocks.ofNat ns[i]!
    let s := poseidon2Perm12 ⟨⟨w 0, w 1, w 2, w 3⟩, ⟨w 4, w 5, w 6, w 7⟩, ⟨w 8, w 9, w 10, w 11⟩⟩
    return csv (s.toList.map (·.val))
  | _ => throw "unknown operation or arity"

end SpecOracle

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let line := (line.dropEndWhile fun c => c == '\n' || c == '\r').toString
    let result := match SpecOracle.eval (line.splitOn "\t") with
      | .ok s => s
      | .error e => "error:" ++ e
    stdout.putStrLn result
    stdout.flush
