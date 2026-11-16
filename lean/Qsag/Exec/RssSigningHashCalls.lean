module
public import Qsag.Exec.RssSigningProgram
public import Qsag.Exec.RssParticipantBinding
import all Qsag.Exec.RssSigningProgram
import all Qsag.Exec.RssParticipantBinding
import all Qsag.Exec.RssParticipantSponge
import all Qsag.Exec.RssParticipantMachine
import all Qsag.Protocol.Threshold.ThresholdMpc
import all Qsag.Protocol.Signing.HashSigs
import Qsag.Tactic.AssuranceKit

/-!
Concrete secret-shared cSHAKE calls for the resumable signer. The outer cut index,
inner hash index, global round and lane form distinct tape coordinates. Every
hash call retains actual participant states and gate evidence. The output is
still secret-shared and unverified; no active-check/opening capability is minted.
-/
public section
namespace Qsag.RssSigning
open RssParticipant
set_option autoImplicit false

abbrev ParticipantTape := Nat → Nat → Nat → Nat → RssPrfZeroSeeds

def queryEncoding : Query → Bytes
  | .prfMsg rand mu => encodeMultiFrame [[0], rand, mu]
  | .wotsChain layer tree kp chain steps =>
      encodeMultiFrame [[1], leb128 layer.toNat, leb128 tree.toNat,
        leb128 kp, leb128 chain, leb128 steps]
  | .forsReveal tree kp j u => encodeMultiFrame [[2], leb128 tree.toNat, leb128 kp, leb128 j, leb128 u]
  | .forsLeaf tree kp j u => encodeMultiFrame [[3], leb128 tree.toNat, leb128 kp, leb128 j, leb128 u]

def hashPhase (query : Query) (subcall : Nat) : Bytes :=
  encodeMultiFrame ["QSAG.RSS.SECRET-HASH/v1".toUTF8.data.toList, queryEncoding query, leb128 subcall]

theorem hashPhase_subcall {query query' : Query} {i j : Nat}
    (h : hashPhase query i = hashPhase query' j) : i = j := by
  have hf := encodeMultiFrame_injective h
  simp only [List.cons.injEq] at hf
  exact (leb128_prefix_inj (show leb128 i ++ [] = leb128 j ++ [] by
    simpa using hf.2.2.1)).1

structure HashEvidence where
  cut : Nat
  subcall : Nat
  query : Query
  nodes : Nodes

/-- The default is unreachable for this concrete honest32-byte driver; the
following theorem proves an actual `some` result for every input. It is not a
conversion from an active protocol abort into successful empty bytes. -/
def hashRun (profile : RssProduction.Profile) (request : SessionScheduleReq)
    (cut subcall : Nat) (query : Query) (input : RssByteShares) (tape : ParticipantTape) :
    HashEvidence × RssByteShares :=
  let result := cshakeForRequest profile request cut (hashPhase query subcall)
    pqCshakeSuiteCustom input (tape cut subcall)
  (⟨cut, subcall, query, result.1⟩, result.2.getD ⟨[], [], []⟩)

/-- Public request payload is prepared once, before the demand-driven execution;
otherwise repeatedly deriving enrollment inside each label would dominate runtime. -/
structure Prepared where
  payload : Bytes

def preparePublic (profile : RssProduction.Profile) (request : SessionScheduleReq) : Prepared :=
  ⟨RssProduction.payload profile request⟩

def hashRunPrepared (prepared : Prepared) (cut subcall : Nat) (query : Query)
    (input : RssByteShares) (tape : ParticipantTape) : HashEvidence × RssByteShares :=
  let binding := encodeMultiFrame ["QSAG.RSS.PARTICIPANT/v1".toUTF8.data.toList,
    prepared.payload, leb128 cut, hashPhase query subcall]
  let result := cshakeParticipant 32 binding pqCshakeSuiteCustom input (tape cut subcall)
  (⟨cut, subcall, query, result.1⟩, result.2.getD ⟨[], [], []⟩)

theorem hashRunPrepared_eq (profile : RssProduction.Profile) (request : SessionScheduleReq)
    (cut subcall : Nat) (query : Query) (input : RssByteShares) (tape : ParticipantTape) :
    hashRunPrepared (preparePublic profile request) cut subcall query input tape =
      hashRun profile request cut subcall query input tape := by rfl

theorem cshake32_has_output (profile : RssProduction.Profile) (request : SessionScheduleReq)
    (cut subcall : Nat) (query : Query) (input : RssByteShares) (tape : ParticipantTape) :
    ∃ output, (cshakeForRequest profile request cut (hashPhase query subcall)
      pqCshakeSuiteCustom input (tape cut subcall)).2 = some output ∧ output.WellFormed := by
  let binding := invocationBinding profile request cut (hashPhase query subcall)
  let padded := paddedInput pqCshakeSuiteCustom input
  let state := absorbArithmetic (padded.b0.length / shake256RateBytes) 0 zeroRssKState
    padded (tape cut subcall)
  have h := absorbParticipantBlocks_represents (padded.b0.length / shake256RateBytes)
    (initialNodes binding zeroRssKState [] 0) binding zeroRssKState padded 0 (tape cut subcall)
    (initialNodes_represents binding zeroRssKState [] 0)
  refine ⟨rssTakeShares 32 ⟨rateBlockBytes state.s0, rateBlockBytes state.s1,
    rateBlockBytes state.s2⟩, ?_, ?_⟩
  · simp only [cshakeForRequest, cshakeParticipant, show 32 ≤ shake256RateBytes by rw [shake256RateBytes_eq]; decide,
      ↓reduceIte, cshakeNodes]
    exact rateOutputShares_represents _ _ _ _ _ h
  · simp [RssByteShares.WellFormed, rssTakeShares, rateBlockBytes_length]

theorem hashRun_is_actual_output (profile : RssProduction.Profile) (request : SessionScheduleReq)
    (cut subcall : Nat) (query : Query) (input : RssByteShares) (tape : ParticipantTape) :
    (cshakeForRequest profile request cut (hashPhase query subcall)
      pqCshakeSuiteCustom input (tape cut subcall)).2 =
        some (hashRun profile request cut subcall query input tape).2 ∧
    (hashRun profile request cut subcall query input tape).2.WellFormed := by
  obtain ⟨output, ho, hw⟩ := cshake32_has_output profile request cut subcall query input tape
  simp only [hashRun, ho, Option.getD_some]
  exact ⟨by trivial, hw⟩

theorem hashRun_reconstructs (profile : RssProduction.Profile) (request : SessionScheduleReq)
    (cut subcall : Nat) (query : Query) (input : RssByteShares) (tape : ParticipantTape)
    (hw : input.WellFormed) :
    reconstructRssBytes (hashRun profile request cut subcall query input tape).2 =
      cshake256Xof 32 pqCshakeSuiteCustom (reconstructRssBytes input) := by
  have h := cshakeForRequest_refines_existing profile request cut (hashPhase query subcall)
    pqCshakeSuiteCustom input (tape cut subcall) (fun _ => tape cut subcall) hw
  rw [(hashRun_is_actual_output profile request cut subcall query input tape).1,
    Option.map_some] at h
  have hr := (reconstructRssBytes_mpcCshake256SharedRss 32 pqCshakeSuiteCustom hw
    (fun _ => tape cut subcall)).2
  exact (Option.some.inj h).trans hr

/-- Distinct nested calls have distinct labels, even if they use the same round
number and happen to compute equal output bytes. -/
theorem hash_binding_injective (profile : RssProduction.Profile) (request : SessionScheduleReq)
    (cut cut' subcall subcall' : Nat) (query query' : Query)
    (h : invocationBinding profile request cut (hashPhase query subcall) =
      invocationBinding profile request cut' (hashPhase query' subcall')) :
    cut = cut' ∧ subcall = subcall' := by
  exact ⟨invocationBinding_invocation _ _ _ _ _ _ _ _ h,
    hashPhase_subcall (invocationBinding_phase _ _ _ _ _ _ _ _ h)⟩

#verify_constructive hashRunPrepared_eq hashPhase_subcall cshake32_has_output hashRun_is_actual_output
  hashRun_reconstructs hash_binding_injective
end Qsag.RssSigning
