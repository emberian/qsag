import Qsag.Exec.SpecOracle
import Qsag.Math.QuinticExt5
import Qsag.Protocol.Signing.HashSigs
import Qsag.Protocol.Signing.Fips205
import Qsag.Math.Gf2Pow128
import Qsag.Protocol.Aggregation.SuccinctAggregationIop
import Qsag.Protocol.Threshold.ThresholdMlDsaAndToprf
import Qsag.Custody.JortsBeltLatchAndQuorumSwitching
import Qsag.Exec.PosixCrashWal
import Qsag.Protocol.Aggregation.Poseidon2AlgebraicAndRecursiveHem

/- Streaming protocol: tab-separated operation and arguments; bytes are lowercase hex,
   integers decimal, lists comma-separated. One response per line; errors do not stop the stream.
   Wrappers call the live specifications in `Qsag.*` and `Qsag.SpecOracle.*` with zero classical
   decoding dependencies. -/
namespace SpecOracle
open Qsag

-- The wire protocol is ASCII. Reading bytes avoids the UTF-8 decoder's classical proofs.
def asciiChars (s : String) : List Char :=
  s.toUTF8.toList.map (fun b => Char.ofNat b.toNat)

def splitAscii (s : String) (delimiter : Char) : List String :=
  ((asciiChars s).splitOn delimiter).map String.ofList

def hexDigit (n : Nat) : Char :=
  let v := n % 16
  if v < 10 then Char.ofNat (48 + v) else Char.ofNat (87 + v)

def hex (bs : List UInt8) : String :=
  String.ofList (bs.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])

def unhex (s : String) : Except String (List UInt8) := do
  let cs := asciiChars s
  if cs.length % 2 != 0 then throw "odd hex length"
  let ns ← cs.mapM fun c =>
    if '0' ≤ c && c ≤ '9' then pure (c.toNat - 48)
    else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 87)
    else throw "invalid hex"
  return (List.range (ns.length / 2)).map fun i =>
    UInt8.ofNat (16 * ns.getD (2 * i) 0 + ns.getD (2 * i + 1) 0)

def requireSome {α : Type} (x : Option α) (message : String) : Except String α :=
  match x with
  | some a => .ok a
  | none => .error message

def nat (s : String) : Except String Nat := do
  let bytes := s.toUTF8.toList
  if bytes.isEmpty then throw "invalid integer"
  bytes.foldlM (fun acc b =>
    if 48 ≤ b.toNat && b.toNat ≤ 57 then pure (10 * acc + b.toNat - 48)
    else throw "invalid integer") 0

def nums (s : String) : Except String (List Nat) :=
  if s.isEmpty then pure [] else (splitAscii s ',').mapM nat

def csv (ns : List Nat) : String := String.intercalate "," (ns.map toString)
def bool (b : Bool) : String := if b then "true" else "false"

def canopyDomainBytes : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2e, 0x50, 0x43, 0x53,
   0x2e, 0x43, 0x41, 0x4e, 0x4f, 0x50, 0x59, 0x2f, 0x76, 0x32]

def canopyNode (i : Nat) (l r : List UInt8) : List UInt8 :=
  cshake256Xof 32 canopyDomainBytes
    ([0] ++ (List.range 4).map (fun j => UInt8.ofNat (i / 256^j)) ++ l ++ r)
def canopyRoot (n : Nat) (t : List UInt8) : List UInt8 :=
  cshake256Xof 32 canopyDomainBytes ([1, UInt8.ofNat n] ++ t)

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

def posixBurnEvent (s : String) : Except String Qsag.SpecOracle.PosixBurnEvent := do
  match splitAscii s ':' with
  | ["retain"] => return .retain
  | ["reopen"] => return .reopen
  | ["trunc"] => return .trunc
  | ["flip"] => return .flip
  | ["copy"] => return .copy
  | ["tear", k] => return .tear (← nat k)
  | ["res", p, e] => return .reserve (← nat p) (← nat e)
  | _ => throw "unknown posixburn event"

def fsBeltWalEvent (s : String) : Except String Qsag.SpecOracle.FsBeltWalEvent := do
  match s with
  | "retain" => return .retain
  | "crash" => return .crash
  | "rollback" => return .rollback
  | "corrupt" => return .corrupt
  | "rmlock" => return .rmlock
  | _ =>
    let fields ← (splitAscii s ':').mapM nat
    if fields.length != 4 then throw "fsbeltwal event arity"
    let mByte := UInt8.ofNat (fields.getD 1 0)
    let sByte := UInt8.ofNat (fields.getD 2 0)
    let dByte := UInt8.ofNat (fields.getD 3 0)
    let rep32 := fun (b : UInt8) =>
      BitVec.ofNat 256 ((List.range 32).foldl (fun acc _ => acc * 256 + b.toNat) 0)
    return .bind ⟨UInt64.ofNat (fields.getD 0 0), rep32 mByte, rep32 sByte, [dByte]⟩

/-- Binary exponentiation using the executable extension multiplication. -/
def latchTrace (events : String) : Except String String := do
  let mut st := BeltLatchNodeState.init 12 64
  let mut out := []
  for event in splitAscii events ',' do
    if event == "crash" then st := beltLatchCrashAndRecover st
    else if event == "fail" then st := { st with failNextPersist := true }
    else
      let fields ← (splitAscii event ':').mapM nat
      if fields.length != 4 then throw "latch event arity"
      let record : BeltLatchRecord := ⟨UInt64.ofNat (fields.getD 0 0),
        BitVec.ofNat 256 (fields.getD 1 0), BitVec.ofNat 256 (fields.getD 2 0),
        [UInt8.ofNat (fields.getD 3 0)]⟩
      let (next, tag) := match beltLatchBindStep st record with
        | .accepted next .fresh => (next, "fresh")
        | .accepted next .replay => (next, "replay")
        | .rejected next .walPoisoned => (next, "poisoned")
        | .rejected next .epochAlreadyBound => (next, "bound")
        | .rejected next .retrySaltMismatch => (next, "salt")
        | .rejected next .digitsMismatch => (next, "digits")
        | .rejected next .epochConsumed => (next, "consumed")
        | .rejected next .epochExhausted => (next, "exhausted")
        | .rejected next .jumpWindowExceeded => (next, "jump")
        | .rejected next .walIoFailure => (next, "wal")
        | .rejected next _ => (next, "other")
      st := next
      out := out ++ [tag]
  return String.intercalate "," out ++ ";" ++ toString st.nextEpoch ++ ";" ++ bool st.walPoisoned

private def readU64Le (bs : List UInt8) (off : Nat) : Nat :=
  (List.range 8).foldl (fun acc k => acc + (bs.getD (off + k) 0).toNat * (256 ^ k)) 0

private def writeU64Le (x : Nat) : List UInt8 :=
  (List.range 8).map (fun k => UInt8.ofNat ((x / (256 ^ k)) % 256))

def decodeFp5Bytes40 (bs : List UInt8) : Option QuinticGoldilocks :=
  if bs.length != 40 then none else
    let w0 := readU64Le bs 0
    let w1 := readU64Le bs 8
    let w2 := readU64Le bs 16
    let w3 := readU64Le bs 24
    let w4 := readU64Le bs 32
    if h : w0 < goldilocksPrime ∧ w1 < goldilocksPrime ∧ w2 < goldilocksPrime ∧
           w3 < goldilocksPrime ∧ w4 < goldilocksPrime then
      some ⟨⟨w0, h.1⟩, ⟨w1, h.2.1⟩, ⟨w2, h.2.2.1⟩, ⟨w3, h.2.2.2.1⟩, ⟨w4, h.2.2.2.2⟩⟩
    else none

def encodeFp5Bytes40 (x : QuinticGoldilocks) : List UInt8 :=
  writeU64Le x.c0.val ++ writeU64Le x.c1.val ++ writeU64Le x.c2.val ++
    writeU64Le x.c3.val ++ writeU64Le x.c4.val

def hemDuetFoldFp5 (v0 v1 : QuinticGoldilocks) (invTwoY0 invTwo : Goldilocks)
    (alpha : QuinticGoldilocks) : QuinticGoldilocks :=
  let even := QuinticGoldilocks.mul (QuinticGoldilocks.add v0 v1) (QuinticGoldilocks.ofBase invTwo)
  let odd := QuinticGoldilocks.mul (QuinticGoldilocks.sub v0 v1) (QuinticGoldilocks.ofBase invTwoY0)
  QuinticGoldilocks.add odd (QuinticGoldilocks.mul alpha even)

def hemAffineDuetFoldFp5 (v0 v1 : QuinticGoldilocks) (x : Goldilocks)
    (theta alpha beta : QuinticGoldilocks) : QuinticGoldilocks :=
  let half := Goldilocks.inv (Goldilocks.ofNat 2)
  let invTwoX := Goldilocks.mul half (Goldilocks.inv x)
  let even := QuinticGoldilocks.mul (QuinticGoldilocks.add v0 v1) (QuinticGoldilocks.ofBase half)
  let odd := QuinticGoldilocks.mul (QuinticGoldilocks.sub v0 v1) (QuinticGoldilocks.ofBase invTwoX)
  let mixed := QuinticGoldilocks.add even (QuinticGoldilocks.mul theta odd)
  let chal := QuinticGoldilocks.add alpha
    (QuinticGoldilocks.mul beta (QuinticGoldilocks.ofBase (Goldilocks.mul x x)))
  QuinticGoldilocks.add odd (QuinticGoldilocks.mul chal mixed)

def hemBridgeClaimStepFp5
    (eval0 eval1 eval2 eval3 eval4 claim phi theta alpha beta : QuinticGoldilocks) : QuinticGoldilocks :=
  let f := QuinticGoldilocks.add eval0 (QuinticGoldilocks.mul phi eval1)
  let g := QuinticGoldilocks.add eval2 (QuinticGoldilocks.mul phi (QuinticGoldilocks.sub claim eval0))
  let core := QuinticGoldilocks.add g (QuinticGoldilocks.mul alpha
    (QuinticGoldilocks.add f (QuinticGoldilocks.mul theta g)))
  let shift := QuinticGoldilocks.mul beta (QuinticGoldilocks.add eval3 (QuinticGoldilocks.mul theta eval4))
  QuinticGoldilocks.add core shift

def formatQuorumOpt (opt : Option Qsag.SpecOracle.QuorumConfig) : String :=
  match opt with
  | none => "reject"
  | some cfg => csv [cfg.t, cfg.n, cfg.f, cfg.q]

def eval (args : List String) : Except String String := do
  match args with
  | ["ledger", a, b, anchor] =>
    return match Qsag.SpecOracle.ledgerRecovery (← nat a) (← nat b) (← nat anchor) with
      | some generation => toString generation
      | none => "reject"
  | ["quorum", t, n, f, q] =>
    return bool (Qsag.SpecOracle.QuorumConfig.withQuorum
      (← nat t) (← nat n) (← nat f) (← nat q)).isSome
  | ["quorumnew", t, n, f] =>
    return formatQuorumOpt (Qsag.SpecOracle.QuorumConfig.new (← nat t) (← nat n) (← nat f))
  | ["quorumtight", t] =>
    return formatQuorumOpt (Qsag.SpecOracle.QuorumConfig.tight (← nat t))
  | ["wotsgeneric", digest] =>
    return bool (Qsag.SpecOracle.wotsParamsAccepts 127 1 192 (← unhex digest))
  | ["wotsgeneric", chains, zeroDigits, targetSum, digest] =>
    return bool (Qsag.SpecOracle.wotsParamsAccepts
      (← nat chains) (← nat zeroDigits) (← nat targetSum) (← unhex digest))
  | ["latchtrace", events] => latchTrace events
  | ["posixburn", events] =>
    let evs ← if events.isEmpty then pure [] else (splitAscii events ',').mapM posixBurnEvent
    return String.intercalate "," (Qsag.SpecOracle.posixBurnTrace evs)
  | ["fsbeltwal", events] =>
    let evs ← if events.isEmpty then pure [] else (splitAscii events ',').mapM fsBeltWalEvent
    return String.intercalate "," (Qsag.SpecOracle.fsBeltWalTrace evs)
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
    let dec := fun s => do return (← requireSome (decodeFp5Bytes40 (← unhex s)) "extension")
    return hex (encodeFp5Bytes40 (hemAffineDuetFoldFp5
      (← dec v0) (← dec v1) (Goldilocks.ofNat (← nat x))
      (← dec theta) (← dec alpha) (← dec beta)))
  | ["cosetfold", v0, v1, invTwoY0, invTwo, alpha] =>
    let dec := fun s => do return (← requireSome (decodeFp5Bytes40 (← unhex s)) "extension")
    return hex (encodeFp5Bytes40 (hemDuetFoldFp5
      (← dec v0) (← dec v1)
      (Goldilocks.ofNat (← nat invTwoY0)) (Goldilocks.ofNat (← nat invTwo))
      (← dec alpha)))
  | ["cwyzbridge", eval0, eval1, eval2, eval3, eval4, claim, phi, theta, alpha, beta] =>
    let dec := fun s => do return (← requireSome (decodeFp5Bytes40 (← unhex s)) "extension")
    return hex (encodeFp5Bytes40 (hemBridgeClaimStepFp5
      (← dec eval0) (← dec eval1) (← dec eval2) (← dec eval3) (← dec eval4)
      (← dec claim) (← dec phi) (← dec theta) (← dec alpha) (← dec beta)))
  | ["shake", n, m] => return hex (shake256Xof (← nat n) (← unhex m))
  | ["cshake", n, d, m] => return hex (cshake256Xof (← nat n) (← unhex d) (← unhex m))
  | ["sha3", m] => return hex (Qsag.SpecOracle.sha3_256Bytes (← unhex m))
  | ["sha3_512", m] => return hex (Qsag.SpecOracle.sha3_512Bytes (← unhex m))
  | ["keccak256", m] => return hex (Qsag.SpecOracle.keccak256Bytes (← unhex m))
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
  | ["extdecode", a] => return match decodeFp5Bytes40 (← unhex a) with
      | none => "reject"
      | some x => hex (encodeFp5Bytes40 x)
  | ["ext", op, a, b] =>
    let x ← requireSome (decodeFp5Bytes40 (← unhex a)) "noncanonical extension"
    let y ← requireSome (decodeFp5Bytes40 (← unhex b)) "noncanonical extension"
    let z ← match op with
      | "add" => pure (QuinticGoldilocks.add x y)
      | "sub" => pure (QuinticGoldilocks.sub x y)
      | "square" => pure (QuinticGoldilocks.mul x x)
      | "frobenius" => pure (QuinticGoldilocks.frob x)
      | "mul" => pure (QuinticGoldilocks.mul x y)
      | "inv" => pure (QuinticGoldilocks.inv x)
      | _ => throw "unknown extension operation"
    return hex (encodeFp5Bytes40 z)
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
    let hs ← if hashes.isEmpty then pure [] else (splitAscii hashes ',').mapM unhex
    let ss ← if siblings.isEmpty then pure [] else (splitAscii siblings ',').mapM unhex
    if ix.length != hs.length then throw "leaf count"
    return bool (verifyCanopyMultiproof canopyNode canopyRoot (← nat depth) (← unhex root) (ix.zip hs) ss)
  | ["wal", events] =>
    let mac := fun k m => cshake256Xof 32 k m
    let s ← requireSome (initProvisionedCustodyState 1 ⟨[119]⟩ .beltLatch
      (List.replicate 32 1) (List.replicate 32 2) 10000 mac [3]) "provision"
    let es ← (splitAscii events ',').mapM walEvent
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
    let w := fun i => UInt64.ofNat (ns.getD i 0)
    let s := keccakF1600 ⟨w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7, w 8, w 9, w 10, w 11, w 12,
      w 13, w 14, w 15, w 16, w 17, w 18, w 19, w 20, w 21, w 22, w 23, w 24⟩
    return csv [s.a0.toNat, s.a1.toNat, s.a2.toNat, s.a3.toNat, s.a4.toNat, s.a5.toNat,
      s.a6.toNat, s.a7.toNat, s.a8.toNat, s.a9.toNat, s.a10.toNat, s.a11.toNat, s.a12.toNat,
      s.a13.toNat, s.a14.toNat, s.a15.toNat, s.a16.toNat, s.a17.toNat, s.a18.toNat, s.a19.toNat,
      s.a20.toNat, s.a21.toNat, s.a22.toNat, s.a23.toNat, s.a24.toNat]
  | ["poseidon", words] =>
    let ns ← nums words
    if ns.length != 12 then throw "state width"
    let w := fun i => Goldilocks.ofNat (ns.getD i 0)
    let s := poseidon2Perm12 ⟨⟨w 0, w 1, w 2, w 3⟩, ⟨w 4, w 5, w 6, w 7⟩, ⟨w 8, w 9, w 10, w 11⟩⟩
    return csv (s.toList.map (·.val))
  | ["poseidon16", words] =>
    let ns ← nums words
    if ns.length != 16 then throw "state width"
    let st := Qsag.SpecOracle.LegacyPoseidon16.Poseidon2State16.ofList (ns.map Goldilocks.ofNat)
    return csv ((Qsag.SpecOracle.LegacyPoseidon16.Poseidon2State16.toList (Qsag.SpecOracle.LegacyPoseidon16.poseidon2Perm16 st)).map (·.val))
  | ["poseidon16inv", words] =>
    let ns ← nums words
    if ns.length != 16 then throw "state width"
    let st := Qsag.SpecOracle.LegacyPoseidon16.Poseidon2State16.ofList (ns.map Goldilocks.ofNat)
    return csv ((Qsag.SpecOracle.LegacyPoseidon16.Poseidon2State16.toList (Qsag.SpecOracle.LegacyPoseidon16.poseidon2Perm16Inv st)).map (·.val))
  | ["poseidon16me", op, words] =>
    let ns ← nums words
    if ns.length != 16 then throw "state width"
    let st := Qsag.SpecOracle.LegacyPoseidon16.Poseidon2State16.ofList (ns.map Goldilocks.ofNat)
    let out ← match op with
      | "fwd" => pure (applyME16 st)
      | "inv" => pure (applyME16Inv st)
      | _ => throw "unknown me16 op"
    return csv ((Qsag.SpecOracle.LegacyPoseidon16.Poseidon2State16.toList out).map (·.val))
  | _ => throw "unknown operation or arity"

end SpecOracle

private partial def runOracleStream (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let line := String.ofList (((SpecOracle.asciiChars line).reverse.dropWhile
    (fun c => c == '\n' || c == '\r')).reverse)
  let result := match SpecOracle.eval (SpecOracle.splitAscii line '\t') with
    | .ok s => s
    | .error e => "error:" ++ e
  stdout.putStrLn result
  stdout.flush
  runOracleStream stdin stdout

def main : IO Unit := do
  runOracleStream (← IO.getStdin) (← IO.getStdout)
