module
public import Qsag.RssParticipantGateEvidence
import all Qsag.RssParticipantGateEvidence
import all Qsag.RssParticipantMachine
import all Qsag.RssParticipantKeccak
import all Qsag.RssParticipantSponge
import all Qsag.RssSigningBackend
import all Qsag.RssSigningHashCalls
import all Qsag.ThresholdMpc
import Qsag.Tactic.AssuranceKit

/-! Preservation of checked extraction through the actual honest participant
producer and demand-driven signing backend. This proves origin/completeness of
the gate table, not acceptance of malicious network executions. -/
public section
namespace Qsag.RssParticipant.GateChecks
set_option autoImplicit false
set_option maxRecDepth 8192

def HistoryGood (nodes : Nodes) : Prop :=
  Aligned3 goodRound nodes.n0.evidence nodes.n1.evidence nodes.n2.evidence

def producedRound (cursor : Nat) (s : RssKState) (rc : UInt64)
    (r : Nat → RssPrfZeroSeeds) : RoundEvidence × RoundEvidence × RoundEvidence :=
  let out := roundNetwork s rc r
  (⟨cursor, rc, gateRecords (linearLocal ⟨s.s0, s.s1⟩) (mask0 r), out.s0, out.s1⟩,
   ⟨cursor, rc, gateRecords (linearLocal ⟨s.s1, s.s2⟩) (mask1 r), out.s1, out.s2⟩,
   ⟨cursor, rc, gateRecords (linearLocal ⟨s.s2, s.s0⟩) (mask2 r), out.s2, out.s0⟩)

theorem producedRound_good (cursor : Nat) (s : RssKState) (rc : UInt64)
    (r : Nat → RssPrfZeroSeeds) :
    goodRound (producedRound cursor s rc r).1
      (producedRound cursor s rc r).2.1 (producedRound cursor s rc r).2.2 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [producedRound, roundLinked]
  · exact honest_gate_records_aligned
      ⟨rhoPiS (thetaS s.s0), rhoPiS (thetaS s.s1), rhoPiS (thetaS s.s2)⟩ r
  · rfl

theorem honestRound_retains_produced (nodes : Nodes) (binding : List UInt8)
    (s : RssKState) (rc : UInt64) (rcs : List UInt64) (cursor : Nat)
    (r : Nat → RssPrfZeroSeeds) (h : Represents nodes binding s (rc :: rcs) cursor) :
    (honestRound nodes r).n0.evidence = nodes.n0.evidence ++ [(producedRound cursor s rc r).1] ∧
    (honestRound nodes r).n1.evidence = nodes.n1.evidence ++ [(producedRound cursor s rc r).2.1] ∧
    (honestRound nodes r).n2.evidence = nodes.n2.evidence ++ [(producedRound cursor s rc r).2.2] := by
  rcases h with ⟨h0, h1, h2, hb0, hb1, hb2, hc0, hc1, hc2,
    hr0, hr1, hr2, hp0, hp1, hp2⟩
  simp [honestRound, prepare, receiveOptional, receive, h0, h1, h2,
    hb0, hb1, hb2, hc0, hc1, hc2, hr0, hr1, hr2, hp0, hp1, hp2,
    nextParty, previousParty, producedRound, roundNetwork]

theorem Aligned3.snoc {A : Type} {P : A → A → A → Prop}
    {as bs cs : List A} (h : Aligned3 P as bs cs) {a b c : A} (habc : P a b c) :
    Aligned3 P (as ++ [a]) (bs ++ [b]) (cs ++ [c]) := by
  induction h with
  | nil => exact .cons habc .nil
  | cons hp _ ih => exact .cons hp ih

theorem honestRound_historyGood (nodes : Nodes) (binding : List UInt8)
    (s : RssKState) (rc : UInt64) (rcs : List UInt64) (cursor : Nat)
    (r : Nat → RssPrfZeroSeeds) (h : Represents nodes binding s (rc :: rcs) cursor)
    (hg : HistoryGood nodes) : HistoryGood (honestRound nodes r) := by
  obtain ⟨h0, h1, h2⟩ := honestRound_retains_produced nodes binding s rc rcs cursor r h
  unfold HistoryGood
  rw [h0, h1, h2]
  exact hg.snoc (producedRound_good cursor s rc r)

theorem runHonestRounds_historyGood (rcs : List UInt64) (nodes : Nodes)
    (binding : List UInt8) (s : RssKState) (cursor : Nat)
    (tape : Nat → Nat → RssPrfZeroSeeds) (h : Represents nodes binding s rcs cursor)
    (hg : HistoryGood nodes) :
    HistoryGood (runHonestRounds rcs.length nodes tape) := by
  induction rcs generalizing nodes s cursor with
  | nil => exact hg
  | cons rc rcs ih =>
    have hc : nodes.n0.cursor = cursor := h.2.2.2.2.2.2.1
    have hr := honestRound_represents nodes binding s rc rcs cursor (tape cursor) h
    have hh := honestRound_historyGood nodes binding s rc rcs cursor (tape cursor) h hg
    simpa only [List.length_cons, runHonestRounds, hc] using
      ih (honestRound nodes (tape cursor)) (roundNetwork s rc (tape cursor)) (cursor + 1) hr hh

theorem absorbNodes_historyGood (nodes : Nodes) (binding : List UInt8)
    (s : RssKState) (cursor : Nat) (block : RssByteShares)
    (h : Represents nodes binding s [] cursor) (hg : HistoryGood nodes) :
    HistoryGood (absorbNodes nodes block) := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, hr0, hr1, hr2, hp0, hp1, hp2⟩
  simpa only [HistoryGood, absorbNodes, absorbNode, hp0, hp1, hp2, hr0, hr1, hr2] using hg

theorem absorbParticipantBlocks_historyGood (n : Nat) (nodes : Nodes) (binding : List UInt8)
    (s : RssKState) (rest : RssByteShares) (cursor : Nat)
    (tape : Nat → Nat → RssPrfZeroSeeds) (h : Represents nodes binding s [] cursor)
    (hg : HistoryGood nodes) : HistoryGood (absorbParticipantBlocks n nodes rest tape) := by
  induction n generalizing nodes s rest cursor with
  | zero => exact hg
  | succ n ih =>
    have ha := absorbNodes_represents nodes binding s cursor (rssTakeShares shake256RateBytes rest) h
    have hag := absorbNodes_historyGood nodes binding s cursor (rssTakeShares shake256RateBytes rest) h hg
    have hp := runHonestRounds_represents keccakRoundConstants _ binding _ cursor tape ha
    have hpg := runHonestRounds_historyGood keccakRoundConstants _ binding _ cursor tape ha hag
    exact ih _ _ (rssDropShares shake256RateBytes rest)
      (cursor + keccakRoundConstants.length) hp hpg

theorem cshakeNodes_historyGood (binding customization : List UInt8) (input : RssByteShares)
    (tape : Nat → Nat → RssPrfZeroSeeds) :
    HistoryGood (cshakeNodes binding customization input tape) := by
  apply absorbParticipantBlocks_historyGood _ _ binding zeroRssKState _ 0 tape
    (initialNodes_represents binding zeroRssKState [] 0)
  exact Aligned3.nil

theorem preparedHash_historyGood (prepared : RssSigning.Prepared) (cut subcall : Nat)
    (query : RssSigning.Query) (input : RssByteShares) (tape : RssSigning.ParticipantTape) :
    HistoryGood (RssSigning.hashRunPrepared prepared cut subcall query input tape).1.nodes := by
  exact cshakeNodes_historyGood _ _ _ _

theorem chain_historyGood (prepared : RssSigning.Prepared) (pkSeed : List UInt8)
    (cut : Nat) (query : RssSigning.Query) (layer : UInt32) (tree : UInt64)
    (kp chainIndex subcall step remaining : Nat) (current : RssByteShares)
    (tape : RssSigning.ParticipantTape) :
    ∀ h ∈ (RssSigning.chain prepared pkSeed cut query layer tree kp chainIndex
      subcall step remaining current tape).evidence, HistoryGood h.nodes := by
  induction remaining generalizing subcall step current with
  | zero => simp [RssSigning.chain]
  | succ remaining ih =>
    intro h hm
    simp only [RssSigning.chain, List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact preparedHash_historyGood _ _ _ _ _ _
    · exact ih (subcall + 1) (step + 1) _ h hm

theorem queryRun_historyGood (prepared : RssSigning.Prepared) (material : RssProduction.Material)
    (cut : Nat) (query : RssSigning.Query) (tape : RssSigning.ParticipantTape) :
    ∀ h ∈ (RssSigning.queryRun prepared material cut query tape).evidence, HistoryGood h.nodes := by
  cases query <;> intro h hm <;> simp only [RssSigning.queryRun, List.mem_cons, List.not_mem_nil,
    or_false] at hm
  · subst h; exact preparedHash_historyGood _ _ _ _ _ _
  · rcases hm with rfl | hm
    · exact preparedHash_historyGood _ _ _ _ _ _
    · exact chain_historyGood _ _ _ _ _ _ _ _ _ _ _ _ _ h hm
  · subst h; exact preparedHash_historyGood _ _ _ _ _ _
  · rcases hm with rfl | rfl <;> exact preparedHash_historyGood _ _ _ _ _ _

theorem extractHashes_of_historyGood (hs : List RssSigning.HashEvidence)
    (hh : ∀ h ∈ hs, HistoryGood h.nodes) :
    ∃ gates, extractHashes hs = some gates ∧
      ∀ g ∈ gates, relation g.records.1 g.records.2.1 g.records.2.2 := by
  induction hs with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons h hs ih =>
    obtain ⟨head, hhead, hp⟩ := extractRounds_of_aligned h.cut h.subcall (hh h (by simp))
    obtain ⟨tail, htail, htp⟩ := ih (fun x hx => hh x (by simp [hx]))
    refine ⟨head ++ tail, by simp [extractHashes, extractHash, hhead, htail], ?_⟩
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hp g hg
    · exact htp g hg

/-- Universal honest producer-to-extraction theorem for the concrete reached
query. Includes every intermediate cSHAKE's gates; opens no intermediate output. -/
theorem queryRun_gate_extraction (prepared : RssSigning.Prepared) (material : RssProduction.Material)
    (cut : Nat) (query : RssSigning.Query) (tape : RssSigning.ParticipantTape) :
    ∃ gates, extractAnswer (RssSigning.queryRun prepared material cut query tape) = some gates ∧
      ∀ g ∈ gates, relation g.records.1 g.records.2.1 g.records.2.2 := by
  exact extractHashes_of_historyGood _ (queryRun_historyGood prepared material cut query tape)

/-- Every exact padded table compiled from an actual honest query passes the
initial weighted relation check for every weight tuple, without releasing a cut. -/
theorem queryRun_weighted_complete (prepared : RssSigning.Prepared) (material : RssProduction.Material)
    (cut : Nat) (query : RssSigning.Query) (tape : RssSigning.ParticipantTape)
    (depth : Nat) (gates : List IndexedGate)
    (he : extractAnswer (RssSigning.queryRun prepared material cut query tape) = some gates)
    (hcap : gates.length ≤ 2 ^ depth) (gs : Rss256ProductProof.ChallengeTuple depth) :
    answerWeightAccept depth (RssSigning.queryRun prepared material cut query tape) gs = true := by
  obtain ⟨produced, hp, hv⟩ := queryRun_gate_extraction prepared material cut query tape
  rw [he] at hp
  have heq := Option.some.inj hp
  subst produced
  have ht := indexedTable_valid depth gates hv
  simp [answerWeightAccept, answerTable, he, hcap,
    validTable_weighted_claim_eq depth (indexedTable depth gates) ht gs]

#verify_constructive producedRound_good honestRound_retains_produced Aligned3.snoc
  honestRound_historyGood runHonestRounds_historyGood absorbNodes_historyGood
  absorbParticipantBlocks_historyGood cshakeNodes_historyGood preparedHash_historyGood
  chain_historyGood queryRun_historyGood extractHashes_of_historyGood queryRun_gate_extraction
  queryRun_weighted_complete
end Qsag.RssParticipant.GateChecks
end
