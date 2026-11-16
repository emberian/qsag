module
public import Qsag.Exec.RssParticipantGateProducer
public import Qsag.Exec.RssSigningTreeCache
public import Qsag.Exec.RssParticipantGateEvidence
public import Qsag.Exec.RssParticipantGateWeights
public import Qsag.Exec.RssSigningBatches
public import Qsag.Exec.RssSigningBackend
public import Qsag.Exec.RssSigningHashCalls
public import Qsag.Protocol.Threshold.Rss256TernaryRound
import Qsag.Tactic.AssuranceKit

/-! Structural lift from actual grouped query/tree producers to their complete
retained gate evidence. No answer is reconstructed or released by this module.
The active packed64 verifier and private consistency protocol remain separate. -/
public section
namespace Qsag.RssParticipant.GateChecks
open Rss256ProductProof
set_option autoImplicit false
set_option maxRecDepth 8192

@[expose] def batchHashes (batch : RssSigning.UnverifiedBatch) : List RssSigning.HashEvidence :=
  batch.computations.flatMap RssSigning.UnverifiedAnswer.evidence

@[expose] def treeHashes : {height : Nat} → RssSigning.LeafTree RssSigning.UnverifiedBatch height →
    List RssSigning.HashEvidence
  | 0, .leaf batch => batchHashes batch
  | _ + 1, .node left right => treeHashes left ++ treeHashes right

@[expose] def extractBatch (batch : RssSigning.UnverifiedBatch) : Option (List IndexedGate) :=
  extractHashes (batchHashes batch)

@[expose] def extractTree {height : Nat} (tree : RssSigning.UnverifiedTree height) : Option (List IndexedGate) :=
  extractHashes (treeHashes tree.batches)

theorem produceBatch_historyGood (prepared : RssSigning.Prepared) (material : RssProduction.Material)
    (tape : RssSigning.ParticipantTape) (first : Nat) (queries : List RssSigning.Query) :
    ∀ h ∈ batchHashes (RssSigning.produceBatch prepared material tape first queries),
      HistoryGood h.nodes := by
  induction queries generalizing first with
  | nil => simp [batchHashes, RssSigning.produceBatch]
  | cons query queries ih =>
    intro h hm
    simp only [batchHashes, RssSigning.produceBatch, List.flatMap_cons, List.mem_append] at hm
    rcases hm with hm | hm
    · exact queryRun_historyGood prepared material first query tape h hm
    · exact ih (first + 1) h hm

theorem produceTree_historyGood (prepared : RssSigning.Prepared) (material : RssProduction.Material)
    (tape : RssSigning.ParticipantTape) {height : Nat}
    (plan : RssSigning.LeafTree (List RssSigning.Query) height) (first : Nat) :
    ∀ h ∈ treeHashes (RssSigning.produceTree prepared material tape first plan).batches,
      HistoryGood h.nodes := by
  induction plan generalizing first with
  | leaf queries => exact produceBatch_historyGood prepared material tape first queries
  | node left right ihl ihr =>
    intro h hm
    simp only [RssSigning.produceTree, treeHashes, List.mem_append] at hm
    rcases hm with hm | hm
    · exact ihl first h hm
    · exact ihr _ h hm

theorem produceBatch_gate_extraction (prepared : RssSigning.Prepared) (material : RssProduction.Material)
    (tape : RssSigning.ParticipantTape) (first : Nat) (queries : List RssSigning.Query) :
    ∃ gates, extractBatch (RssSigning.produceBatch prepared material tape first queries) = some gates ∧
      ∀ g ∈ gates, relation g.records.1 g.records.2.1 g.records.2.2 := by
  exact extractHashes_of_historyGood _ (produceBatch_historyGood prepared material tape first queries)

theorem produceTree_gate_extraction (prepared : RssSigning.Prepared) (material : RssProduction.Material)
    (tape : RssSigning.ParticipantTape) {height : Nat}
    (plan : RssSigning.LeafTree (List RssSigning.Query) height) (first : Nat) :
    ∃ gates, extractTree (RssSigning.produceTree prepared material tape first plan) = some gates ∧
      ∀ g ∈ gates, relation g.records.1 g.records.2.1 g.records.2.2 := by
  exact extractHashes_of_historyGood _ (produceTree_historyGood prepared material tape plan first)

@[expose] def groupTable (depth : Nat) (hashes : List RssSigning.HashEvidence) : Option (GateTable depth) := do
  let gates ← extractHashes hashes
  if gates.length ≤ 2 ^ depth then some (indexedTable depth gates) else none

@[expose] def groupWeightAccept (depth : Nat) (hashes : List RssSigning.HashEvidence)
    (gs : ChallengeTuple depth) : Bool :=
  match groupTable depth hashes with
  | none => false
  | some table => decide (weightEval gs (claimedCoeffs table) = weightEval gs (trueCoeffs table))

theorem group_weighted_complete (hashes : List RssSigning.HashEvidence)
    (hh : ∀ h ∈ hashes, HistoryGood h.nodes) (depth : Nat) (gates : List IndexedGate)
    (he : extractHashes hashes = some gates) (hcap : gates.length ≤ 2 ^ depth)
    (gs : ChallengeTuple depth) : groupWeightAccept depth hashes gs = true := by
  obtain ⟨produced, hp, hv⟩ := extractHashes_of_historyGood hashes hh
  rw [he] at hp
  have heq := Option.some.inj hp
  subst produced
  have ht := indexedTable_valid depth gates hv
  simp [groupWeightAccept, groupTable, he, hcap,
    validTable_weighted_claim_eq depth (indexedTable depth gates) ht gs]

theorem produceBatch_weighted_complete (prepared : RssSigning.Prepared) (material : RssProduction.Material)
    (tape : RssSigning.ParticipantTape) (first : Nat) (queries : List RssSigning.Query)
    (depth : Nat) (gates : List IndexedGate)
    (he : extractBatch (RssSigning.produceBatch prepared material tape first queries) = some gates)
    (hcap : gates.length ≤ 2 ^ depth) (gs : ChallengeTuple depth) :
    groupWeightAccept depth (batchHashes (RssSigning.produceBatch prepared material tape first queries)) gs = true := by
  exact group_weighted_complete _ (produceBatch_historyGood prepared material tape first queries)
    depth gates he hcap gs

theorem produceTree_weighted_complete (prepared : RssSigning.Prepared) (material : RssProduction.Material)
    (tape : RssSigning.ParticipantTape) {height : Nat}
    (plan : RssSigning.LeafTree (List RssSigning.Query) height) (first : Nat)
    (depth : Nat) (gates : List IndexedGate)
    (he : extractTree (RssSigning.produceTree prepared material tape first plan) = some gates)
    (hcap : gates.length ≤ 2 ^ depth) (gs : ChallengeTuple depth) :
    groupWeightAccept depth (treeHashes (RssSigning.produceTree prepared material tape first plan).batches) gs = true := by
  exact group_weighted_complete _ (produceTree_historyGood prepared material tape plan first)
    depth gates he hcap gs

/-- For a malicious retained group, the invalid index is in the exact extracted
query/tree evidence. Structural inconsistency never reaches this weighted check. -/
theorem group_bad_gate_weight_bound (depth : Nat) (hashes : List RssSigning.HashEvidence)
    (gates : List IndexedGate) (hextract : extractHashes hashes = some gates)
    (hcap : gates.length ≤ 2 ^ depth)
    (hbad : ∃ i, i < gates.length ∧
      let g := (gates.map IndexedGate.records).getD i zeroTriple
      ¬ relation g.1 g.2.1 g.2.2)
    (S : List Tower128) (hS : S.Nodup) :
    ((challengeTuples S depth).filter (groupWeightAccept depth hashes)).length ≤
      weightBadBound S.length depth := by
  have hi : ¬ gateTableValid (indexedTable depth gates) := by
    intro hv
    rcases hbad with ⟨i, hi, hbad⟩
    exact hbad ((tabulateGates_valid_iff depth _).mp hv i (by omega))
  have he : groupTable depth hashes = some (indexedTable depth gates) := by
    simp [groupTable, hextract, hcap]
  have hp : groupWeightAccept depth hashes = fun gs => decide
      (weightEval gs (claimedCoeffs (indexedTable depth gates)) =
        weightEval gs (trueCoeffs (indexedTable depth gates))) := by
    funext gs
    simp [groupWeightAccept, he]
  rw [hp]
  exact invalid_weighted_claim_equal_le depth (indexedTable depth gates) hi S hS

#verify_constructive produceBatch_historyGood produceTree_historyGood produceBatch_gate_extraction
  produceTree_gate_extraction group_weighted_complete produceBatch_weighted_complete
  produceTree_weighted_complete group_bad_gate_weight_bound
end Qsag.RssParticipant.GateChecks
end
