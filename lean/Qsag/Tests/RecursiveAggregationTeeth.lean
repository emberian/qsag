module
public import Qsag.Math.GoldilocksBase
public import Qsag.Protocol.Aggregation.ConcreteIvcDepth2Cert
meta import Qsag.Protocol.Aggregation.ConcreteIvcDepth2Cert
meta import Qsag.Protocol.Aggregation.MultiDepthRecursiveQromExtractor
/- Recursive commitment framing and assignment-recovery checks. -/
public import Qsag.Protocol.Aggregation.Poseidon2AlgebraicAndRecursiveHem
public import Qsag.Protocol.Aggregation.RecursivePoseidon2WhirSoundness
public import Qsag.Oracle.FiatShamir
public import Qsag.Protocol.Aggregation.Aggregation
public import Qsag.Oracle.Poseidon2
public import Qsag.Oracle.Keccak
public import Qsag.Math.Goldilocks
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

open Aggregation RoundPoly

set_option autoImplicit false

#verify_constructive Qsag.tooth_noncanonical_shard_header_collides_and_is_rejected
  Qsag.inhabited_canonical_shard_headers
  Qsag.tooth_frame_boundary_is_encoded

#tooth_pair Qsag.leafShardHeaderPreimage_injective vs Qsag.tooth_noncanonical_shard_header_collides_and_is_rejected

#tooth_pair Qsag.fsTranscriptBlocks_injective vs Qsag.tooth_frame_boundary_is_encoded


open MultiDepthQrom MultiDepthQrom.Depth2Cert MultiDepthQrom.IvcAlgebra in
/-- The reference R1CS prover records its SHAKE256 calls while constructing a
    fresh proof. It receives one private wire and never hashes a node witness. -/
def checkIvcAssignmentRecovery (wire : Goldilocks) : IO Unit := do
  let ro := shake256Xof 56
  let some arg := parseArgument 5 rootPi.algebraWords | throw (IO.userError "missing fixture accumulator")
  let some (pi, trace) := (proveR1csArgument fastEnv.profile fastEnv.cfg ro 2 rootStmt
    rootPi.witnessCommitRoot arg.acc [42] [wire]).run {} | throw (IO.userError "R1CS prover rejected the wire")
  unless verifyConcreteIvcRoot fastEnv.profile fastEnv.cfg ro 2 rootStmt pi do
    throw (IO.userError "R1CS verifier rejected the public proof")
  let log := trace.reverseLog.reverse
  let some z := recoverIvcAssignment fastEnv ro log 2 rootStmt pi | throw (IO.userError "codeword recovery failed")
  let hash := ro (encodeMultiFrame [[73,86,67,45,77,65,84,82,73,88,45,80,79,73,78,84], arg.acc.encode])
  let some inputs := fixedPublicCells fastEnv.cfg (argumentPublicFrame rootStmt hash rootPi.witnessCommitRoot)
    | throw (IO.userError "public cells did not fit")
  unless z.toList == Goldilocks.one :: inputs ++ [wire] do
    throw (IO.userError "decoded wires differ from the prover's assignment")
  unless (recoverIvcAssignment fastEnv ro [] 2 rootStmt pi).isNone do
    throw (IO.userError "empty recording yielded a decoded assignment")
  IO.println s!"IVC verification and codeword recovery: {z.size} matching wires from {log.length} SHAKE256 queries"

private def checkBothAssignments : IO Unit := do
  checkIvcAssignmentRecovery .zero
  checkIvcAssignmentRecovery .one

#eval checkBothAssignments

#eval show IO Unit from do
  unless MultiDepthQrom.realDepth2AcceptsAndExtracts do
    throw (IO.userError "depth-two verification or extraction failed")
  IO.println "Depth-two root accepted and all four leaves extracted"

end Qsag
end
