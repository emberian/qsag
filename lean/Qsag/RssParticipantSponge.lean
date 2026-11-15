module
public import Qsag.RssParticipantMachine
import all Qsag.RssParticipantMachine
import all Qsag.ThresholdMpc
import Qsag.Tactic.AssuranceKit

/-!
Party-local cSHAKE absorption with the addressed24-round protocol. The round
cursor is global across blocks; neither transcripts nor mask coordinates reset
at a block boundary. This slice covers outputs up to the136-byte rate, including
all32-byte secret PRF/chain operations of the production RSS oracle. It retains
unverified gate evidence; extracting output below is a correctness observer, not
an authorized opening. Active proof/commit-open is a separate protocol phase.
-/

public section
namespace Qsag.RssParticipant
set_option autoImplicit false

/-- Absorption sees this participant's two local input shares only. -/
def absorbNode (node : Node) (own next : List UInt8) : Node :=
  match node.phase, node.remaining with
  | .ready view, [] =>
      { node with
        phase := .ready ⟨xorRate136 view.own own, xorRate136 view.next next⟩
        remaining := keccakRoundConstants }
  | _, _ => abortNode node

def absorbNodes (nodes : Nodes) (block : RssByteShares) : Nodes :=
  ⟨absorbNode nodes.n0 block.b0 block.b1,
   absorbNode nodes.n1 block.b1 block.b2,
   absorbNode nodes.n2 block.b2 block.b0⟩

theorem absorbNodes_represents (nodes : Nodes) (binding : List UInt8)
    (s : RssKState) (cursor : Nat) (block : RssByteShares)
    (h : Represents nodes binding s [] cursor) :
    Represents (absorbNodes nodes block) binding (mpcXorRate136Rss s block)
      keccakRoundConstants cursor := by
  rcases h with ⟨h0, h1, h2, hb0, hb1, hb2, hc0, hc1, hc2,
    hr0, hr1, hr2, hp0, hp1, hp2⟩
  simp [absorbNodes, absorbNode, h0, h1, h2, hb0, hb1, hb2, hc0, hc1, hc2,
    hr0, hr1, hr2, hp0, hp1, hp2, Represents, mpcXorRate136Rss]

def absorbParticipantBlocks : Nat → Nodes → RssByteShares →
    (Nat → Nat → RssPrfZeroSeeds) → Nodes
  | 0, nodes, _, _ => nodes
  | n + 1, nodes, rest, tape =>
      let next := runHonestRounds keccakRoundConstants.length
        (absorbNodes nodes (rssTakeShares shake256RateBytes rest)) tape
      absorbParticipantBlocks n next (rssDropShares shake256RateBytes rest) tape

/-- Arithmetic specification of the same node driver; no reconstructed state is
passed into any node transition. -/
def absorbArithmetic : Nat → Nat → RssKState → RssByteShares →
    (Nat → Nat → RssPrfZeroSeeds) → RssKState
  | 0, _, s, _, _ => s
  | n + 1, cursor, s, rest, tape =>
      let next := roundsNetwork keccakRoundConstants cursor
        (mpcXorRate136Rss s (rssTakeShares shake256RateBytes rest)) tape
      absorbArithmetic n (cursor + keccakRoundConstants.length) next
        (rssDropShares shake256RateBytes rest) tape

theorem absorbParticipantBlocks_represents (n : Nat) (nodes : Nodes) (binding : List UInt8)
    (s : RssKState) (rest : RssByteShares) (cursor : Nat)
    (tape : Nat → Nat → RssPrfZeroSeeds)
    (h : Represents nodes binding s [] cursor) :
    Represents (absorbParticipantBlocks n nodes rest tape) binding
      (absorbArithmetic n cursor s rest tape) [] (cursor + n * keccakRoundConstants.length) := by
  induction n generalizing nodes s rest cursor with
  | zero => simpa [absorbParticipantBlocks, absorbArithmetic] using h
  | succ n ih =>
    have ha := absorbNodes_represents nodes binding s cursor
      (rssTakeShares shake256RateBytes rest) h
    have hp := runHonestRounds_represents keccakRoundConstants _ binding _ cursor tape ha
    have hi := ih _ _ (rssDropShares shake256RateBytes rest)
      (cursor + keccakRoundConstants.length) hp
    simpa [absorbParticipantBlocks, absorbArithmetic, Nat.succ_mul,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi

theorem absorbArithmetic_simulates (n cursor : Nat) (s : RssKState) (rest : RssByteShares)
    (tape : Nat → Nat → RssPrfZeroSeeds) (hWf : rest.WellFormed) :
    reconstructRssKState (absorbArithmetic n cursor s rest tape) =
      absorbBlocks n (reconstructRssKState s) (reconstructRssBytes rest) := by
  induction n generalizing cursor s rest with
  | zero => rw [absorbBlocks_zero]; rfl
  | succ n ih =>
    have hTakeWf : (rssTakeShares shake256RateBytes rest).WellFormed :=
      ⟨by simp [rssTakeShares, hWf.1], by simp [rssTakeShares, hWf.2]⟩
    have hDropWf : (rssDropShares shake256RateBytes rest).WellFormed :=
      ⟨by simp [rssDropShares, hWf.1], by simp [rssDropShares, hWf.2]⟩
    have hTakeRec : reconstructRssBytes (rssTakeShares shake256RateBytes rest) =
        (reconstructRssBytes rest).take shake256RateBytes := by
      unfold reconstructRssBytes rssTakeShares
      dsimp only
      rw [zipXor_take, zipXor_take]
    have hDropRec : reconstructRssBytes (rssDropShares shake256RateBytes rest) =
        (reconstructRssBytes rest).drop shake256RateBytes := by
      unfold reconstructRssBytes rssDropShares
      dsimp only
      rw [zipXor_drop, zipXor_drop]
    simp only [absorbArithmetic]
    rw [absorbBlocks_succ, ih _ _ _ hDropWf, reconstruct_roundsNetwork,
      ← keccakF1600_eq, reconstructRssKState_mpcXorRate136Rss _ hTakeWf,
      hTakeRec, hDropRec]

/-- Local byte projection remains secret-shared until a later authorized cut. -/
def localRateOutput (node : Node) (outLen : Nat) : Option (List UInt8) := do
  let state ← primaryOutput node
  pure ((rateBlockBytes state).take outLen)

def rateOutputShares (nodes : Nodes) (outLen : Nat) : Option RssByteShares := do
  let a ← localRateOutput nodes.n0 outLen
  let b ← localRateOutput nodes.n1 outLen
  let c ← localRateOutput nodes.n2 outLen
  pure ⟨a, b, c⟩

theorem rateOutputShares_represents (nodes : Nodes) (binding : List UInt8)
    (s : RssKState) (cursor : Nat) (outLen : Nat)
    (h : Represents nodes binding s [] cursor) :
    rateOutputShares nodes outLen = some (rssTakeShares outLen
      ⟨rateBlockBytes s.s0, rateBlockBytes s.s1, rateBlockBytes s.s2⟩) := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, hp0, hp1, hp2⟩
  simp [rateOutputShares, localRateOutput, primaryOutput, hp0, hp1, hp2, rssTakeShares]

theorem reconstruct_rateOutput (s : RssKState) (outLen : Nat) :
    reconstructRssBytes (rssTakeShares outLen
      ⟨rateBlockBytes s.s0, rateBlockBytes s.s1, rateBlockBytes s.s2⟩) =
      (rateBlockBytes (reconstructRssKState s)).take outLen := by
  unfold rssTakeShares reconstructRssBytes reconstructRssKState
  dsimp only
  rw [zipXor_take, zipXor_take, rateBlockBytes_xor, rateBlockBytes_xor]

def framedInput (customization : List UInt8) (input : RssByteShares) : RssByteShares :=
  if customization = [] then input
  else rssAppendShares (rssPublicBytes (customizationPrefix customization)) input

def paddedInput (customization : List UInt8) (input : RssByteShares) : RssByteShares :=
  rssPadForRate (framedInput customization input) (if customization = [] then 0x1f else 0x04)

def cshakeNodes (binding customization : List UInt8) (input : RssByteShares)
    (tape : Nat → Nat → RssPrfZeroSeeds) : Nodes :=
  let padded := paddedInput customization input
  absorbParticipantBlocks (padded.b0.length / shake256RateBytes)
    (initialNodes binding zeroRssKState [] 0) padded tape

/-- Total protocol result includes every pending gate witness; output extraction
is partial and limited to the first rate block. -/
def cshakeParticipant (outLen : Nat) (binding customization : List UInt8)
    (input : RssByteShares) (tape : Nat → Nat → RssPrfZeroSeeds) :
    Nodes × Option RssByteShares :=
  let nodes := cshakeNodes binding customization input tape
  (nodes, if outLen ≤ shake256RateBytes then rateOutputShares nodes outLen else none)

/-- Node-machine absorption computes the same state as the existing shared cSHAKE
absorption, although its individual shares use a different χ convention. -/
theorem cshakeNodes_refines_absorption (binding customization : List UInt8)
    (input : RssByteShares) (tape : Nat → Nat → RssPrfZeroSeeds)
    (hWf : input.WellFormed) :
    reconstructedOutput (cshakeNodes binding customization input tape) =
      some (reconstructRssKState (mpcAbsorbPaddedRss (paddedInput customization input)
        (fun _ => tape))) := by
  have hf : (framedInput customization input).WellFormed := by
    unfold framedInput
    split
    · exact hWf
    · exact rssAppendShares_wellFormed (rssPublicBytes_wellFormed _) hWf
  have hp : (paddedInput customization input).WellFormed :=
    rssPadForRate_wellFormed hf (if customization = [] then 0x1f else 0x04)
  have h := absorbParticipantBlocks_represents
    ((paddedInput customization input).b0.length / shake256RateBytes)
    (initialNodes binding zeroRssKState [] 0) binding zeroRssKState
    (paddedInput customization input) 0 tape
    (initialNodes_represents binding zeroRssKState [] 0)
  unfold cshakeNodes
  rw [represents_output _ _ _ _ _ h]
  congr 1
  rw [absorbArithmetic_simulates _ _ _ _ _ hp]
  unfold mpcAbsorbPaddedRss
  rw [mpcAbsorbBlocksRss_simulates _ _ _ _ _ hp]

theorem small_squeeze_reconstruction (outLen : Nat) (s : RssKState)
    (tape : Nat → Nat → Nat → RssPrfZeroSeeds) (h : outLen ≤ 136) :
    reconstructRssBytes (mpcSqueezeFuelSharedRss outLen outLen 0 s tape) =
      (rateBlockBytes (reconstructRssKState s)).take outLen := by
  cases outLen with
  | zero => simp [mpcSqueezeFuelSharedRss, reconstructRssBytes]
  | succ n =>
    simp only [mpcSqueezeFuelSharedRss, h, ↓reduceIte]
    exact reconstruct_rateOutput s (n + 1)

/-- Actual participant execution, with its retained local gate witnesses, has the
same reconstructed first-rate-block output as the existing production cSHAKE
computation. The second tape may be arbitrary: this is correctness, not a claim
that either tape has an ideal distribution or that local transcripts are equal. -/
theorem cshakeParticipant_refines_existing (outLen : Nat) (binding customization : List UInt8)
    (input : RssByteShares) (localTape : Nat → Nat → RssPrfZeroSeeds)
    (oldTape : Nat → Nat → Nat → RssPrfZeroSeeds) (hWf : input.WellFormed)
    (hLen : outLen ≤ shake256RateBytes) :
    ((cshakeParticipant outLen binding customization input localTape).2.map reconstructRssBytes) =
      some (reconstructRssBytes (mpcCshake256SharedRss outLen customization input oldTape)) := by
  have hf : (framedInput customization input).WellFormed := by
    unfold framedInput
    split
    · exact hWf
    · exact rssAppendShares_wellFormed (rssPublicBytes_wellFormed _) hWf
  have hp : (paddedInput customization input).WellFormed :=
    rssPadForRate_wellFormed hf (if customization = [] then 0x1f else 0x04)
  have h := absorbParticipantBlocks_represents
    ((paddedInput customization input).b0.length / shake256RateBytes)
    (initialNodes binding zeroRssKState [] 0) binding zeroRssKState
    (paddedInput customization input) 0 localTape
    (initialNodes_represents binding zeroRssKState [] 0)
  simp only [cshakeParticipant, hLen, ↓reduceIte, cshakeNodes]
  rw [rateOutputShares_represents _ _ _ _ _ h]
  simp only [Option.map_some, reconstruct_rateOutput]
  unfold mpcCshake256SharedRss
  change some ((rateBlockBytes (reconstructRssKState
    (absorbArithmetic ((paddedInput customization input).b0.length / shake256RateBytes)
      0 zeroRssKState (paddedInput customization input) localTape))).take outLen) =
    some (reconstructRssBytes (mpcSqueezeFuelSharedRss outLen outLen 0
      (mpcAbsorbPaddedRss (paddedInput customization input) (fun b => oldTape (2 * b)))
      (fun q => oldTape (2 * q + 1))))
  rw [small_squeeze_reconstruction _ _ _ hLen]
  rw [absorbArithmetic_simulates _ _ _ _ _ hp]
  unfold mpcAbsorbPaddedRss
  rw [mpcAbsorbBlocksRss_simulates _ _ _ _ _ hp]

#verify_constructive absorbNodes_represents absorbParticipantBlocks_represents
  absorbArithmetic_simulates rateOutputShares_represents reconstruct_rateOutput
  cshakeNodes_refines_absorption small_squeeze_reconstruction cshakeParticipant_refines_existing

end Qsag.RssParticipant
