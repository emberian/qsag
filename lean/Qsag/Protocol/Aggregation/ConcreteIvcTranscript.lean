module
public import Qsag.Protocol.Aggregation.ConcreteIvcWire
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.MultiDepthQrom
open Qsag
attribute [-instance] Fin.instLinearOrderPackage
set_option autoImplicit false

def registryLeaf {n : Nat} (id threshold : Nat) (roster : Fin n → AggValidatorPk) : Spec.Bytes :=
  -- "IVC-REG-LEAF"
  encodeMultiFrame [[73, 86, 67, 45, 82, 69, 71, 45, 76, 69, 65, 70], leb128 id, leb128 threshold,
    encodeMultiFrame ((List.finRange n).map fun i => encodeAggValidatorPkBytes (roster i))]

def registryBranch (level : Nat) (l r : Spec.Bytes) : Spec.Bytes :=
  -- "IVC-REG-NODE"
  encodeMultiFrame [[73, 86, 67, 45, 82, 69, 71, 45, 78, 79, 68, 69], leb128 level, l, r]

def registryWalk (ro : Spec.Bytes → Spec.Bytes) :
    Nat → Nat → Spec.Bytes → List Spec.Bytes → Spec.Bytes
  | _, _, leaf, [] => leaf
  | level, index, cur, sibling :: rest =>
    let (l, r) := if index % 2 = 0 then (cur, sibling) else (sibling, cur)
    registryWalk ro (level + 1) (index / 2)
      (ro (registryBranch level l r)) rest

def registryRootFor {n : Nat} (ro : Spec.Bytes → Spec.Bytes) (s : ExtractedLeafShard n) : Spec.Bytes :=
  registryWalk ro 0 s.shardId (ro (registryLeaf s.shardId s.threshold s.stmt.roster)) s.registryAuthPath

def registryMember {n : Nat} (ro : Spec.Bytes → Spec.Bytes) (root : Spec.Bytes)
    (s : ExtractedLeafShard n) : Bool :=
  s.registryAuthPath.length == 64 && decide (s.shardId < 2 ^ 64) &&
    decide (registryRootFor ro s = root)

theorem registryMember_rootFor {n : Nat} (ro : Spec.Bytes → Spec.Bytes) (s : ExtractedLeafShard n)
    (h : s.registryAuthPath.length = 64) (hi : s.shardId < 2 ^ 64) :
    registryMember ro (registryRootFor ro s) s = true := by simp [registryMember,h,hi]

#verify_constructive registryMember_rootFor

/-- Build the sparse directory bottom-up. Each level stores only occupied addresses. -/
def buildRegistry {n : Nat} (ro : Spec.Bytes → Spec.Bytes) (shards : List (ExtractedLeafShard n)) :
    Option (Spec.Bytes × List (ExtractedLeafShard n)) := do
  guard (!shards.isEmpty && (shards.map ExtractedLeafShard.shardId).eraseDups.length == shards.length)
  guard (shards.all fun s => decide (s.shardId < 2 ^ 64))
  let mut nodes := shards.map fun s => (s.shardId, ro (registryLeaf s.shardId s.threshold s.stmt.roster))
  -- "IVC-REG-EMPTY"
  let mut empty := ro (encodeMultiFrame [[73, 86, 67, 45, 82, 69, 71, 45, 69, 77, 80, 84, 89]])
  let mut paths := shards.map fun s => (s.shardId, ([] : List Spec.Bytes))
  for level in [:64] do
    let lookup (j : Nat) := (nodes.lookup j).getD empty
    paths := paths.map fun (j,path) => (j/2, lookup (j ^^^ 1) :: path)
    let parents := (nodes.map fun (j,_) => j/2).eraseDups
    nodes := parents.map fun j => (j, ro (registryBranch level (lookup (2*j)) (lookup (2*j+1))))
    empty := ro (registryBranch level empty empty)
  let root ← nodes.lookup 0
  return (root, shards.zipWith (fun s (_,rev) => {s with registryAuthPath := rev.reverse}) paths)

namespace NodeWire

abbrev B := Spec.Bytes

@[expose] def nat (x : Nat) : B :=
  let rec go : Nat → Nat → B
    | 0, _ => []
    | _, 0 => []
    | fuel + 1, k + 1 => UInt8.ofNat ((k + 1) % 256) :: go fuel ((k + 1) / 256)
  go x x

@[expose] def statement (s : IvcTreeStatement) : B :=
  encodeMultiFrame [s.policyRegistryRoot, nat s.epochFloor, nat s.lo, nat s.hi,
    nat s.totalQuorums, s.message]

def readStatement (b : B) : Option IvcTreeStatement := do
  let [root, ep, lo, hi, count, msg] ← decodeMultiFrameBytes b | none
  return ⟨root, decodeNatLeBytes ep, decodeNatLeBytes lo, decodeNatLeBytes hi,
    decodeNatLeBytes count, msg⟩

@[expose] def words (xs : List Goldilocks) : B := xs.flatMap goldilocksToBytesLE

@[expose] def chunks {α : Type} (width : Nat) (xs : List α) : List (List α) :=
  let rec go : Nat → List α → List (List α)
    | 0, _ | _, [] => []
    | fuel + 1, ys => ys.take width :: go fuel (ys.drop width)
  go ((xs.length + width - 1) / width) xs

@[expose] def readWords (bs : B) : Option (List Goldilocks) :=
  (chunks 8 bs).mapM fun chunk =>
    if chunk.length == 8 then
      let x := decodeNatLeBytes chunk
      if h : x < goldilocksPrime then some ⟨x, h⟩ else none
    else none

private def readWord (bs : B) : Option Goldilocks := do
  guard (bs.length == 8)
  let x := decodeNatLeBytes bs
  if h : x < goldilocksPrime then some ⟨x, h⟩ else none

def readLane : List Goldilocks → Option Lane4
  | [a,b,c,d] => some ⟨a,b,c,d⟩
  | _ => none

def readState (xs : List Goldilocks) : Option Poseidon2State12 := do
  let [a,b,c] ← (chunks 4 xs).mapM readLane | none
  return ⟨a,b,c⟩

def readPk (bs : B) : Option AggValidatorPk := do
  let head :: rest := bs | none
  let profile ← match head.toNat with
    | 1 => some AggSigProfile.xmssPoseidon2
    | 2 => some AggSigProfile.corduroyPoseidon2
    | _ => none
  let xs ← (chunks 8 rest).mapM (fun chunk => readWord chunk.reverse)
  let [seed, root] ← (chunks 4 xs).mapM readLane | none
  return ⟨profile, seed, root⟩

def row (r : StepOpRow) : B :=
  encodeMultiFrame [words r.stIn.toList, words (r.initExtSbox.flatMap Poseidon2State12.toList),
    words r.intSbox, words (r.termExtSbox.flatMap Poseidon2State12.toList),
    words r.prevState, words r.nextState, words r.aux]

def readRow (bs : B) : Option StepOpRow := do
  let [st, init, ints, term, prev, next, aux] ← decodeMultiFrameBytes bs | none
  return ⟨← readState (← readWords st), ← (chunks 12 (← readWords init)).mapM readState,
    ← readWords ints, ← (chunks 12 (← readWords term)).mapM readState,
    ← readWords prev, ← readWords next, ← readWords aux⟩

def shard {n : Nat} (s : ExtractedLeafShard n) : B :=
  encodeMultiFrame [nat s.shardId, nat s.threshold, nat s.quorumCount,
    encodeMultiFrame ((List.finRange n).map fun i => encodeAggValidatorPkBytes (s.stmt.roster i)),
    nat s.stmt.bitmap.toNat, s.stmt.message, encodeMultiFrame (s.rows.map row),
    encodeMultiFrame s.registryAuthPath]

def readShard (n : Nat) (bs : B) : Option (ExtractedLeafShard n) := do
  let [id, thr, q, keys, mask, msg, rows, path] ← decodeMultiFrameBytes bs | none
  let roster ← (← decodeMultiFrameBytes keys).mapM readPk
  if h : roster.length = n then
    let sigRows ← (← decodeMultiFrameBytes rows).mapM readRow
    return ⟨decodeNatLeBytes id, decodeNatLeBytes thr, decodeNatLeBytes q,
      ⟨fun i => roster[i.val]'(h ▸ i.isLt), BitVec.ofNat n (decodeNatLeBytes mask), msg⟩,
      sigRows, ← decodeMultiFrameBytes path⟩
  else none

@[expose] def digest (r : Poseidon2Gl24.Digest7) : B :=
  words [r.d0,r.d1,r.d2,r.d3,r.d4,r.d5,r.d6]

private def readStages : List IvcStageGeom → List Goldilocks →
    Option (List FixedStagePayload × List Goldilocks)
  | [], rest => some ([], rest)
  | g :: gs, ws => do
    let [a,b,c,d,e,f,h] := ws.take 7 | none
    let rest := ws.drop 7
    let ood := rest.take (5 * g.oodLen)
    let rest := rest.drop ood.length
    let folds := rest.take (25 * g.stepVars)
    let rest := rest.drop folds.length
    let fibers := rest.take (g.queries * g.fiberLen)
    let rest := rest.drop fibers.length
    let siblings := rest.take (7 * g.frontierSiblings)
    let (tail, leftover) ← readStages gs (rest.drop siblings.length)
    return (⟨⟨a,b,c,d,e,f,h⟩, ood, folds, fibers, siblings⟩ :: tail, leftover)

def readProof (p : IvcWhirParams) (bs : B) : Option (FixedShapeWhirProof p) := do
  guard (bs.length == p.openingByteLen && bs.take 8 == ivcWireMagic)
  let nonce := BitVec.ofNat 256 (decodeNatLeBytes ((bs.drop 8).take 32))
  let root := BitVec.ofNat 448 (decodeNatLeBytes ((bs.drop 40).take 56))
  let (stages, rest) ← readStages p.stages (← readWords (bs.drop 96))
  let last := 5 * (2 ^ p.earlyStopVars + 2)
  let proof : FixedShapeWhirProof p :=
    ⟨nonce, root, rest.drop (5 + last), stages, rest.take 5, (rest.drop 5).take last⟩
  guard proof.wellFormed
  return proof

def node {p : IvcWhirParams} {n : Nat} : CommittedIvcNodeWitness p n → B
  | .leaf s => encodeMultiFrame [[0], shard s]
  | .parent l r pl pr fold => encodeMultiFrame [[1], statement l, statement r,
      encodeFixedShapeWhirProof pl, encodeFixedShapeWhirProof pr, words fold]

def readNode (p : IvcWhirParams) (n : Nat) (bs : B) : Option (CommittedIvcNodeWitness p n) := do
  match ← decodeMultiFrameBytes bs with
  | [tag, s] =>
    guard (tag == [0])
    return .leaf (← readShard n s)
  | [tag, l, r, pl, pr, fold] =>
    guard (tag == [1])
    guard (fold.length == 40 * (3 * (2*p.logCells+3) + 1))
    return .parent (← readStatement l) (← readStatement r)
      (← readProof p pl) (← readProof p pr) (← readWords fold)
  | _ => none

end NodeWire

def nodeCommitmentInput (profile : AggSigProfile) (d : Nat)
    (stmt : IvcTreeStatement) (nonce : BitVec 256) (payload : Spec.Bytes) : Spec.Bytes :=
  -- "QSAG-IVC-NODE-v1"
  encodeMultiFrame [[81, 83, 65, 71, 45, 73, 86, 67, 45, 78, 79, 68, 69, 45, 118, 49],
    [if profile == .xmssPoseidon2 then 1 else 2], leb128 d, NodeWire.statement stmt,
    encodeNatLeBytes 32 nonce.toNat, payload]

private def decodePayload (p : IvcWhirParams) (n : Nat) (input : Spec.Bytes) :=
  do
    let fields ← decodeMultiFrameBytes input
    NodeWire.readNode p n (← fields.getLast?)

private def decodeEntry {p : IvcWhirParams} (n : Nat) (profile : AggSigProfile)
    (ro : Spec.Bytes → Spec.Bytes) (d : Nat) (stmt : IvcTreeStatement)
    (pi : FixedShapeWhirProof p) (entry : Spec.Bytes × Spec.Bytes) : Option (CommittedIvcNodeWitness p n) :=
  if entry.2 = encodeNatLeBytes 56 pi.witnessCommitRoot.toNat ∧ ro entry.1 = entry.2 then
    match decodePayload p n entry.1 with
    | some w => if entry.1 = nodeCommitmentInput profile d stmt pi.stage0Nonce (NodeWire.node w)
        then some w else none
    | none => none
  else none

def extractIvcStepFromTranscript {p : IvcWhirParams} (n : Nat) (profile : AggSigProfile)
    (ro : Spec.Bytes → Spec.Bytes) (T : QromQueryTranscript) (d : Nat) (stmt : IvcTreeStatement)
    (pi : FixedShapeWhirProof p) : Option (CommittedIvcNodeWitness p n) :=
  T.findSome? (decodeEntry n profile ro d stmt pi)

theorem extractIvcStepFromTranscript_recorded {p : IvcWhirParams} {n : Nat} (profile : AggSigProfile)
    (ro : Spec.Bytes → Spec.Bytes) (T : QromQueryTranscript) (d : Nat) (stmt : IvcTreeStatement)
    (pi : FixedShapeWhirProof p) (w : CommittedIvcNodeWitness p n)
    (h : extractIvcStepFromTranscript n profile ro T d stmt pi = some w) :
    let input := nodeCommitmentInput profile d stmt pi.stage0Nonce (NodeWire.node w)
    let output := encodeNatLeBytes 56 pi.witnessCommitRoot.toNat
    (input,output) ∈ T ∧ ro input = output := by
  dsimp only
  unfold extractIvcStepFromTranscript at h
  induction T with
  | nil => cases h
  | cons e es ih =>
    cases hd : decodeEntry n profile ro d stmt pi e with
    | none =>
      obtain ⟨hm, ho⟩ := ih (by simpa [List.findSome?,hd] using h)
      exact ⟨List.mem_cons_of_mem _ hm,ho⟩
    | some v =>
      have hv : v = w := by simpa [List.findSome?,hd] using h
      subst v
      unfold decodeEntry at hd
      split at hd
      · rename_i hb
        split at hd
        · split at hd
          · rename_i hi
            cases hd
            exact ⟨by rw [← hi, ← hb.1]; exact List.mem_cons_self, by rw [← hi, ← hb.1, hb.2]⟩
          · cases hd
        · cases hd
      · cases hd

theorem extractIvcStepFromTranscript_nil {p : IvcWhirParams} (n : Nat) (profile : AggSigProfile)
    (ro : Spec.Bytes → Spec.Bytes) (d : Nat) (stmt : IvcTreeStatement) (pi : FixedShapeWhirProof p) :
    extractIvcStepFromTranscript n profile ro [] d stmt pi = none := by simp [extractIvcStepFromTranscript]

#verify_constructive extractIvcStepFromTranscript_recorded extractIvcStepFromTranscript_nil
end Qsag.MultiDepthQrom
end
