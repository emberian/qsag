module
public import Qsag.Exec.RssSigningHashCalls
public import Qsag.Protocol.Threshold.ThresholdMpc
public import Qsag.Protocol.Signing.HashSigs
import Qsag.Tactic.AssuranceKit

/-!
Participant implementation of each reached production cut query. Intermediate
WOTS/FORS values remain shared. Every actual cSHAKE participant run is retained.
The returned shared answer is explicitly unverified; the active checker and
commit/open protocol must consume its evidence before resuming public control.
-/
public section
namespace Qsag.RssSigning
set_option autoImplicit false
set_option maxHeartbeats 800000

structure UnverifiedAnswer where
  evidence : List HashEvidence
  shares : RssByteShares

@[expose] def chain (prepared : Prepared) (pkSeed : Bytes) (cut : Nat) (query : Query)
    (layer : UInt32) (tree : UInt64) (kp chainIndex : Nat) :
    Nat → Nat → Nat → RssByteShares → ParticipantTape → UnverifiedAnswer
  | _, _, 0, current, _ => ⟨[], current⟩
  | subcall, step, remaining + 1, current, tape =>
      let adrs : HashAdrs := ⟨layer, tree, .wotsHash, UInt32.ofNat kp,
        UInt32.ofNat chainIndex, UInt32.ofNat step⟩
      let result := hashRunPrepared prepared cut subcall query
        (rssFrameSingleSecretCall tagThF pkSeed adrs current) tape
      let rest := chain prepared pkSeed cut query layer tree kp chainIndex
        (subcall + 1) (step + 1) remaining result.2 tape
      ⟨result.1 :: rest.evidence, rest.shares⟩

theorem chain_correct (profile : RssProduction.Profile) (request : SessionScheduleReq)
    (cut : Nat) (query : Query) (layer : UInt32) (tree : UInt64) (kp chainIndex : Nat)
    (subcall step remaining : Nat) (current : RssByteShares) (tape : ParticipantTape)
    (hw : current.WellFormed) :
    (chain (preparePublic profile request) profile.material.pkSeed cut query layer tree kp chainIndex
      subcall step remaining current tape).shares.WellFormed ∧
    reconstructRssBytes (chain (preparePublic profile request) profile.material.pkSeed cut query layer tree kp chainIndex
      subcall step remaining current tape).shares =
      wotsChainSteps cshake256Suite profile.material.pkSeed layer tree kp chainIndex step remaining
        (reconstructRssBytes current) := by
  induction remaining generalizing subcall step current with
  | zero => exact ⟨hw, by rw [wotsChainSteps_zero]; rfl⟩
  | succ remaining ih =>
    let adrs : HashAdrs := ⟨layer, tree, .wotsHash, UInt32.ofNat kp,
      UInt32.ofNat chainIndex, UInt32.ofNat step⟩
    let framed := rssFrameSingleSecretCall tagThF profile.material.pkSeed adrs current
    have hf := reconstructRssBytes_rssFrameSingleSecretCall tagThF profile.material.pkSeed adrs hw
    have hh := hashRun_is_actual_output profile request cut subcall query framed tape
    have hr := hashRun_reconstructs profile request cut subcall query framed tape hf.1
    have hnext : (hashRunPrepared (preparePublic profile request) cut subcall query framed tape).2.WellFormed := by
      rw [hashRunPrepared_eq]
      exact hh.2
    have hrec : reconstructRssBytes
        (hashRunPrepared (preparePublic profile request) cut subcall query framed tape).2 =
        thChainF cshake256Suite profile.material.pkSeed adrs (reconstructRssBytes current) := by
      rw [hashRunPrepared_eq, hr, hf.2, thChainF_eq, thCall_eq]
      rfl
    have hi := ih (subcall + 1) (step + 1) _ hnext
    refine ⟨hi.1, ?_⟩
    change reconstructRssBytes (chain (preparePublic profile request) profile.material.pkSeed cut query
      layer tree kp chainIndex (subcall + 1) (step + 1) remaining
      (hashRunPrepared (preparePublic profile request) cut subcall query framed tape).2 tape).shares = _
    rw [hi.2, hrec, wotsChainSteps_succ]

/-- Mirrors the actual PRF-msg frame, with the private PRF share between public
prefix and suffix. No secret bytes are reconstructed during framing. -/
@[expose] def prfFrame (prf : RssByteShares) (rand mu : Bytes) : RssByteShares :=
  let pubPrefix := leb128 6 ++ encodeListField tagPrfMsg ++ encodeListField [] ++
    encodeListField (encodeAdrs zeroAdrs) ++ leb128 prf.b0.length
  let pubSuffix := encodeListField rand ++ encodeListField mu
  rssAppendShares (rssPublicBytes pubPrefix) (rssAppendShares prf (rssPublicBytes pubSuffix))

@[expose] def queryRun (prepared : Prepared) (material : RssProduction.Material) (cut : Nat)
    (query : Query) (tape : ParticipantTape) : UnverifiedAnswer :=
  match query with
  | .prfMsg rand mu =>
      let result := hashRunPrepared prepared cut 0 query (prfFrame material.prf rand mu) tape
      ⟨[result.1], result.2⟩
  | .wotsChain layer tree kp r steps =>
      let adrs : HashAdrs := ⟨layer, tree, .wotsPrf, UInt32.ofNat kp, UInt32.ofNat r, 0⟩
      let base := hashRunPrepared prepared cut 0 query
        (rssFrameSingleSecretCall tagPrf material.pkSeed adrs material.seed) tape
      let rest := chain prepared material.pkSeed cut query layer tree kp r 1 0 steps base.2 tape
      ⟨base.1 :: rest.evidence, rest.shares⟩
  | .forsReveal tree kp j u =>
      let adrs : HashAdrs := ⟨0, tree, .forsPrf, UInt32.ofNat kp, UInt32.ofNat j, UInt32.ofNat u⟩
      let result := hashRunPrepared prepared cut 0 query
        (rssFrameSingleSecretCall tagPrf material.pkSeed adrs material.seed) tape
      ⟨[result.1], result.2⟩
  | .forsLeaf tree kp j u =>
      let prfAdrs : HashAdrs := ⟨0, tree, .forsPrf, UInt32.ofNat kp, UInt32.ofNat j, UInt32.ofNat u⟩
      let base := hashRunPrepared prepared cut 0 query
        (rssFrameSingleSecretCall tagPrf material.pkSeed prfAdrs material.seed) tape
      let treeAdrs : HashAdrs := ⟨0, tree, .forsTree, UInt32.ofNat kp, UInt32.ofNat j, UInt32.ofNat u⟩
      let result := hashRunPrepared prepared cut 1 query
        (rssFrameSingleSecretCall tagThF material.pkSeed treeAdrs base.2) tape
      ⟨[base.1, result.1], result.2⟩

theorem preparedHash_correct (profile : RssProduction.Profile) (request : SessionScheduleReq)
    (cut subcall : Nat) (query : Query) (input : RssByteShares) (tape : ParticipantTape)
    (hw : input.WellFormed) :
    (hashRunPrepared (preparePublic profile request) cut subcall query input tape).2.WellFormed ∧
    reconstructRssBytes (hashRunPrepared (preparePublic profile request) cut subcall query input tape).2 =
      cshake256Xof 32 pqCshakeSuiteCustom (reconstructRssBytes input) := by
  rw [hashRunPrepared_eq]
  exact ⟨(hashRun_is_actual_output profile request cut subcall query input tape).2,
    hashRun_reconstructs profile request cut subcall query input tape hw⟩

theorem prfFrame_wf (prf : RssByteShares) (rand mu : Bytes) (hw : prf.WellFormed) :
    (prfFrame prf rand mu).WellFormed :=
  rssAppendShares_wellFormed (rssPublicBytes_wellFormed _)
    (rssAppendShares_wellFormed hw (rssPublicBytes_wellFormed _))

theorem prfFrame_reconstructs (prf : RssByteShares) (rand mu : Bytes) (hw : prf.WellFormed) :
    cshake256Xof 32 pqCshakeSuiteCustom (reconstructRssBytes (prfFrame prf rand mu)) =
      thPrfMsg cshake256Suite (reconstructRssBytes prf) rand mu := by
  unfold prfFrame
  rw [reconstructRssBytes_append (rssPublicBytes_wellFormed _), reconstructRssBytes_rssPublicBytes,
    reconstructRssBytes_append hw, reconstructRssBytes_rssPublicBytes,
    thPrfMsg_eq, thCall_eq, thPreimage_eq]
  simp only [cshake256Suite, cshake256Bytes, List.cons_append, List.nil_append,
    encodeMultiFrame, List.length_cons, List.length_nil, encodeByteFields_cons, encodeByteFields_nil,
    List.append_nil, encodeListField_eq (reconstructRssBytes prf), reconstructRssBytes_length hw,
    List.append_assoc]

/-- The concrete participant handler computes every production cut operation
correctly. The equality is about unverified shares; it grants no release right. -/
theorem queryRun_correct (profile : RssProduction.Profile) (request : SessionScheduleReq)
    (cut : Nat) (query : Query) (tape : ParticipantTape) :
    (queryRun (preparePublic profile request) profile.material cut query tape).shares.WellFormed ∧
    reconstructRssBytes (queryRun (preparePublic profile request) profile.material cut query tape).shares =
      answer (RssProduction.sharedOracle profile) query := by
  have hm := RssProduction.sharedOracle_matches profile
  cases query with
  | prfMsg rand mu =>
    dsimp only [queryRun, answer]
    have hr := preparedHash_correct profile request cut 0 (.prfMsg rand mu)
      (prfFrame profile.material.prf rand mu) tape (prfFrame_wf _ _ _ profile.material.prfWf)
    refine ⟨hr.1, ?_⟩
    rw [hr.2, prfFrame_reconstructs _ _ _ profile.material.prfWf, hm.1.1]
    rfl
  | wotsChain layer tree kp r steps =>
    dsimp only [queryRun, answer]
    let adrs : HashAdrs := ⟨layer, tree, .wotsPrf, UInt32.ofNat kp, UInt32.ofNat r, 0⟩
    have hf := reconstructRssBytes_rssFrameSingleSecretCall tagPrf profile.material.pkSeed adrs
      profile.material.seedWf
    have hb := preparedHash_correct profile request cut 0 (.wotsChain layer tree kp r steps)
      (rssFrameSingleSecretCall tagPrf profile.material.pkSeed adrs profile.material.seed) tape hf.1
    have hc := chain_correct profile request cut (.wotsChain layer tree kp r steps)
      layer tree kp r 1 0 steps _ tape hb.1
    refine ⟨hc.1, ?_⟩
    rw [hc.2, hb.2, hf.2, hm.1.2.1, wotsSecretBase_eq, thSecretPrf_eq, thCall_eq]
    rfl
  | forsReveal tree kp j u =>
    dsimp only [queryRun, answer]
    let adrs : HashAdrs := ⟨0, tree, .forsPrf, UInt32.ofNat kp, UInt32.ofNat j, UInt32.ofNat u⟩
    have hf := reconstructRssBytes_rssFrameSingleSecretCall tagPrf profile.material.pkSeed adrs
      profile.material.seedWf
    have hr := preparedHash_correct profile request cut 0 (.forsReveal tree kp j u)
      (rssFrameSingleSecretCall tagPrf profile.material.pkSeed adrs profile.material.seed) tape hf.1
    refine ⟨hr.1, ?_⟩
    rw [hr.2, hf.2, hm.2.1]
    rfl
  | forsLeaf tree kp j u =>
    dsimp only [queryRun, answer]
    let prfAdrs : HashAdrs := ⟨0, tree, .forsPrf, UInt32.ofNat kp, UInt32.ofNat j, UInt32.ofNat u⟩
    let treeAdrs : HashAdrs := ⟨0, tree, .forsTree, UInt32.ofNat kp, UInt32.ofNat j, UInt32.ofNat u⟩
    have hf := reconstructRssBytes_rssFrameSingleSecretCall tagPrf profile.material.pkSeed prfAdrs
      profile.material.seedWf
    have hb := preparedHash_correct profile request cut 0 (.forsLeaf tree kp j u)
      (rssFrameSingleSecretCall tagPrf profile.material.pkSeed prfAdrs profile.material.seed) tape hf.1
    have hf2 := reconstructRssBytes_rssFrameSingleSecretCall tagThF profile.material.pkSeed treeAdrs hb.1
    have hr := preparedHash_correct profile request cut 1 (.forsLeaf tree kp j u)
      (rssFrameSingleSecretCall tagThF profile.material.pkSeed treeAdrs _) tape hf2.1
    refine ⟨hr.1, ?_⟩
    rw [hr.2, hf2.2, hb.2, hf.2, hm.2.2]
    rfl

@[expose] def HashesFrom (cut : Nat) (query : Query) : Nat → List HashEvidence → Prop
  | _, [] => True
  | subcall, e :: es => e.cut = cut ∧ e.query = query ∧ e.subcall = subcall ∧
      HashesFrom cut query (subcall + 1) es

theorem chain_numbered (prepared : Prepared) (pkSeed : Bytes) (cut : Nat) (query : Query)
    (layer : UInt32) (tree : UInt64) (kp chainIndex subcall step remaining : Nat)
    (current : RssByteShares) (tape : ParticipantTape) :
    HashesFrom cut query subcall
      (chain prepared pkSeed cut query layer tree kp chainIndex subcall step remaining current tape).evidence ∧
    (chain prepared pkSeed cut query layer tree kp chainIndex subcall step remaining current tape).evidence.length =
      remaining := by
  induction remaining generalizing subcall step current with
  | zero => exact ⟨trivial, rfl⟩
  | succ remaining ih =>
      have h := ih (subcall + 1) (step + 1)
        (hashRunPrepared prepared cut subcall query
          (rssFrameSingleSecretCall tagThF pkSeed
            ⟨layer, tree, .wotsHash, UInt32.ofNat kp, UInt32.ofNat chainIndex, UInt32.ofNat step⟩ current) tape).2
      exact ⟨⟨rfl, rfl, rfl, h.1⟩, congrArg Nat.succ h.2⟩

@[expose] def queryHashCount : Query → Nat
  | .prfMsg _ _ => 1
  | .wotsChain _ _ _ _ steps => steps + 1
  | .forsReveal _ _ _ _ => 1
  | .forsLeaf _ _ _ _ => 2

theorem queryRun_numbered (prepared : Prepared) (material : RssProduction.Material)
    (cut : Nat) (query : Query) (tape : ParticipantTape) :
    HashesFrom cut query 0 (queryRun prepared material cut query tape).evidence ∧
    (queryRun prepared material cut query tape).evidence.length = queryHashCount query := by
  cases query with
  | prfMsg rand mu => exact ⟨⟨rfl, rfl, rfl, trivial⟩, rfl⟩
  | wotsChain layer tree kp r steps =>
      have h := chain_numbered prepared material.pkSeed cut (.wotsChain layer tree kp r steps)
        layer tree kp r 1 0 steps
        (hashRunPrepared prepared cut 0 (.wotsChain layer tree kp r steps)
          (rssFrameSingleSecretCall tagPrf material.pkSeed
            ⟨layer, tree, .wotsPrf, UInt32.ofNat kp, UInt32.ofNat r, 0⟩ material.seed) tape).2 tape
      exact ⟨⟨rfl, rfl, rfl, h.1⟩, congrArg Nat.succ h.2⟩
  | forsReveal tree kp j u => exact ⟨⟨rfl, rfl, rfl, trivial⟩, rfl⟩
  | forsLeaf tree kp j u => exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩, rfl⟩

#verify_constructive chain_correct preparedHash_correct prfFrame_wf prfFrame_reconstructs queryRun_correct chain_numbered queryRun_numbered
end Qsag.RssSigning
