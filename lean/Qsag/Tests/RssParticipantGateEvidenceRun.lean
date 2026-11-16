module
public import Qsag.Spec.Encoding
meta import Qsag.Spec.Encoding
public import Qsag.Oracle.Keccak
meta import Qsag.Oracle.Keccak
public import Qsag.Exec.RssParticipantGateBatches
meta import Qsag.Exec.RssParticipantGateBatches
public import Qsag.Exec.RssSigningTreeCache
meta import Qsag.Exec.RssSigningTreeCache
public import Qsag.Exec.RssParticipantGateProducer
meta import Qsag.Exec.RssParticipantGateProducer
public import Qsag.Exec.RssParticipantGateEvidence
meta import Qsag.Exec.RssParticipantGateEvidence
public import Qsag.Exec.RssParticipantGateChecks
meta import Qsag.Exec.RssParticipantGateChecks
public import Qsag.Exec.RssSigningBackend
meta import Qsag.Exec.RssSigningBackend
public import Qsag.Exec.RssSigningHashCalls
meta import Qsag.Exec.RssSigningHashCalls
public import Qsag.Exec.RssProductionProfile
meta import Qsag.Exec.RssProductionProfile
public import Qsag.Exec.RssParticipantMachine
meta import Qsag.Exec.RssParticipantMachine
public import Qsag.Exec.RssParticipantKeccak
meta import Qsag.Exec.RssParticipantKeccak
public import Qsag.Protocol.Threshold.ThresholdMpc
meta import Qsag.Protocol.Threshold.ThresholdMpc
public section
open Qsag Qsag.RssParticipant Qsag.RssParticipant.GateChecks

private def material : RssProduction.Material :=
  { seed := ⟨List.replicate 32 0x17, List.replicate 32 0x29, List.replicate 32 0x43⟩
    prf := ⟨List.replicate 32 0x51, List.replicate 32 0x62, List.replicate 32 0x73⟩
    pkSeed := List.replicate 32 0x91
    seedWf := by simp [RssByteShares.WellFormed]
    prfWf := by simp [RssByteShares.WellFormed]
    seedWidth := by simp
    prfWidth := by simp
    pkWidth := by simp }

private def tape (cut subcall round lane : Nat) : RssPrfZeroSeeds :=
  ⟨UInt64.ofNat (17 + cut + 3 * subcall + 7 * round + lane),
   UInt64.ofNat (29 + 3 * cut + 5 * subcall + 11 * round + lane),
   UInt64.ofNat (41 + 7 * cut + 11 * subcall + 13 * round + lane)⟩

private def editFirstRound (answer : RssSigning.UnverifiedAnswer)
    (edit : RoundEvidence → RoundEvidence) : RssSigning.UnverifiedAnswer :=
  match answer.evidence with
  | [] => answer
  | h :: hs =>
    match h.nodes.n0.evidence with
    | [] => answer
    | r :: rs =>
      { answer with evidence :=
        { h with nodes := { h.nodes with n0 := { h.nodes.n0 with evidence := edit r :: rs } } } :: hs }

private def editFirstGate (r : RoundEvidence) (edit : GateRecord → GateRecord) : RoundEvidence :=
  match r.gates with
  | [] => r
  | g :: gs => { r with gates := edit g :: gs }

private def require (b : Bool) (message : String) : IO Unit := do
  unless b do throw (IO.userError message)

def Qsag.RssParticipant.GateChecks.runGateEvidenceChecks : IO Unit := do
  let answer := RssSigning.queryRun ⟨[81, 83, 65, 71]⟩ material 9
    (.wotsChain 0 0 0 1 2) tape
  let some gates := extractAnswer answer | throw (IO.userError "honest evidence extraction failed")
  require (decide (answer.evidence.length = 3 ∧ 0 < gates.length)) "missing intermediate cSHAKE evidence"
  require (gates.all fun g => decide (relation g.records.1 g.records.2.1 g.records.2.2))
    "honest extracted relation failed"
  require ((answerTable 14 answer).isSome && (answerTable 1 answer).isNone)
    "table capacity check failed"
  require (gates.all fun g => decide (g.cut = 9 ∧ g.subcall < 3 ∧ g.lane < 25))
    "gate coordinate mismatch"
  let badProduct := editFirstRound answer fun r =>
    editFirstGate r fun g => { g with product := g.product ^^^ 1 }
  let some badGates := extractAnswer badProduct
    | throw (IO.userError "product validation incorrectly folded into structural extraction")
  require (!(badGates.all fun g => decide (relation g.records.1 g.records.2.1 g.records.2.2)))
    "tampered retained product disappeared"
  let badReplica := editFirstRound answer fun r =>
    editFirstGate r fun g => { g with lhsNext := g.lhsNext ^^^ 1 }
  require ((extractAnswer badReplica).isNone) "operand replica inconsistency accepted"
  let badReceived := editFirstRound answer fun r =>
    { r with receivedOutput := { r.receivedOutput with a0 := r.receivedOutput.a0 ^^^ 1 } }
  require ((extractAnswer badReceived).isNone) "received output inconsistency accepted"
  let start := initialNodes [1] zeroRssKState [0] 0
  let honest := honestRound start (tape 0 0 0)
  let wrongShare := { (roundNetwork zeroRssKState 0 (tape 0 0 0)).s1 with
    a0 := (roundNetwork zeroRssKState 0 (tape 0 0 0)).s1.a0 ^^^ 1 }
  let badNode := receive (prepare start.n0 (mask0 (tape 0 0 0))).1 ⟨1, 0, [1], 0, wrongShare⟩
  require ((extractRounds 0 0 badNode.evidence honest.n1.evidence honest.n2.evidence).isNone)
    "actual authenticated wrong-value delivery survived evidence consistency"
  let plan : RssSigning.LeafTree (List RssSigning.Query) 1 :=
    .node (.leaf [.prfMsg [7] [9]]) (.leaf [.forsLeaf 0 0 0 0])
  let grouped := RssSigning.produceTree ⟨[81, 83, 65, 71]⟩ material tape 50 plan
  let some groupedGates := extractTree grouped
    | throw (IO.userError "actual grouped producer evidence failed extraction")
  require (decide (grouped.nextInvocation = 52 ∧ (treeHashes grouped.batches).length = 3))
    "grouped evidence omitted a query/subcall or reused invocation"
  require (groupedGates.all fun g => decide
    (relation g.records.1 g.records.2.1 g.records.2.2 ∧ 50 ≤ g.cut ∧ g.cut < 52))
    "grouped gate relation or coordinate failed"
  IO.println s!"Grouped extraction: two actual tree leaves, three cSHAKE calls, {groupedGates.length} word gates and distinct invocation labels passed"
  IO.println s!"Exact gate extraction: {answer.evidence.length} actual cSHAKE calls, {gates.length} indexed word gates; honest relations, table capacity, tampered product retention, replica mismatch, and authenticated wrong-value rejection passed"
end

#eval Qsag.RssParticipant.GateChecks.runGateEvidenceChecks
