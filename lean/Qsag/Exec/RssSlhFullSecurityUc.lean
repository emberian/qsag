module
/-
# Qsag.Exec.RssSlhFullSecurityUc — Multi-Session Simulation of the RSS SLH-DSA Cluster Shell

Constructive Lean 4.35 simulation and forgery-transfer results for a three-round SLH-DSA
cluster shell over `Qsag.InteractiveUcEngine`. The model boundary below specifies which
transcripts, resources, and implementation refinements these theorems cover:

1. **Three-Round Protocol (`rssSlhInteractiveProtocol`) & `sk`-Free UC Simulator (`Sim_RssSlh`)**:
   - **Round 1 (coin commitments)**: every party commits with `SHAKE256` to a 128-bit coin share
     under a 64-bit blind, over an injectively length-framed preimage binding the public key, the
     request (session id, epoch, message, hedge), the monotonic `maskSessionCursor` and the party
     id (`round1NonceCommit_binding_or_collision`, `slhPkDigest_binding_or_collision`,
     `slhReqDigest_injective_on_epoch_optRand_msg`; `0` `UInt8.ofNat` truncation).
   - **Round 2**: honest parties broadcast one 64-way bitsliced Keccak `χ`-row share each
     (`rssChiLane0/1/2`), masked by fresh session pads `(chiMaskA, chiMaskB)`, and no coin share.
     The rushing adversary sees these before sending one frame holding its coin opening and its
     `deg` raw `GF(2^128)` (`Tower128`) gate wires.
   - **Coin toss and Pre-Cut Consistency Barrier (`sharedCoinTossBarrier`)**: the corrupt opening
     is checked against its Round-1 commitment, and the `BBCGGI19` / `BDOZ` Horner equation
     `bbcggiWireAccumulator sentWires gamma == bbcggiWireAccumulator expectedWires gamma` is checked
     at `gamma = coinA ⊕ coinB ⊕ corruptCoin` strictly before Round 3; any mismatch aborts with
     `.round1CommitMismatch` / `.activeConsistencyFailed`, poisons `WalLatchState` and erases the
     secret key shares.
   - **Round 3 (`honestRound3` & `finalizeCutOpen`)**: honest parties evaluate the signature
     under the zero-sharing tape expanded from the three pairwise PRG seeds
     (`expandPairwiseSeedTape`), broadcast cut-opening shares (`verifyRssActiveOpenBytes`) and
     their coin openings (`honest_coin_openings_open_round1_commitments`), assemble and verify
     the NIST `FIPS 205` signature (`decodeSlhSig` / `slhVerifyInternal`), and atomically commit
     `WalLatchState` before `SignOk(sigBytes)`.
   - **Black-Box UC Simulator (`Sim_RssSlh`)**: receives **only** `pk : SlhPublicKey` and, upon
     `t`-quorum approval in `IdealTsig`, raw `idealSigBytes : ByteArray` (`0` access to `sk` or
     secret shares). It runs the coin toss as the honest parties do and simulates the masked
     messages from uniform pads.
2. **Cluster-Shell Theorems**:
   - `rss_slh_real_ideal_view_indistinguishable`: whole-transcript multi-round, multi-session
     distance (wire `ByteArray`s and `Abort(reason)` included) at most the root-hit probability
     of the joint coin; that probability is at most `Q_cuts * deg / 2^128` in the game where the
     honest commitments carry the zero coin, and the theorem carries the difference between the
     two games as the explicit term `advCoinHide`, next to the tape-generator term `advPrf`.
   - `rss_slh_interactive_euf_cma_reduction`: constructive `0 Classical.choice` black-box reduction
     turning any rushing threshold adversary forging `(mStar, sigStar)` outside `IdealTsig.approvedMsgs`
     into an explicit witness of `ActiveConsistencySoundnessBreak` OR standalone NIST `FIPS 205` hash
     breaks (`Fips205ForsItsrBreak ∨ WotsChainSmTcrBreak ∨ XmssMerkleTcrBreak ∨ PrfMsgBreak`).
   - `threshold_slh_output_perfect_quorum_privacy`: the output of any valid 2-of-3 RSS or
     `t`-of-`n` Shamir quorum/sharing equals standalone single-signer `slhSignInternal`.
   - `#tooth` mutation refusals: `tooth_skipping_pre_cut_barrier_leaks_key_bit`,
     `tooth_reusing_session_mask_tape_breaks_simulation`,
     `tooth_wal_rollback_enables_stateful_double_sign`,
     `tooth_corrupt_coin_opening_must_match_commitment`,
     `tooth_known_challenge_admits_nonzero_deviation`.
3. **Shell-to-Hash-Game Transfer (`rss_slh_uc_forgery_to_hash_game`, `rss_slh_fresh_enrollment_euf_cma_bound`)**:
   composes the theorems above without an abstract unforgeability premise. On every uniform
   multi-session tape on which a forger wins against `RealProtocolExec`, either the tape is a
   root hit of the joint coin (`multiSessionBadHit true`) or the real transcript equals the ideal
   transcript and yields a concrete `Fips205HashGameBreak`. The forgery bound is
   `Pr[ideal forgery] + Q_s * deg / 2^128 + advCoinHide`. The ideal transcript depends on the
   signing key only through the oracle answers of sessions that reached Round 3
   (`IdealFunctionalityExec_oracle_congr`).
4. The engine-independent parts (wire codecs, tapes, hash-game extractors, the Horner tag scheme
   `hornerTagScheme` and `rss_active_tag_forgery_count_le`) are in
   `Qsag.Protocol.Threshold.RssSlhFullSecurity`.

Model boundary.
* The protocol proved here is a three-round shell around the honest pair. In a 2-of-3 replicated
  sharing the two honest parties jointly hold all three shares; `honestRound3` computes the whole
  signature from their views (`rssQuorumSlhSignBytes`) and re-shares it at the cut. The corrupt
  party contributes no share-dependent message to the output.
* The gate evaluation inside `rssQuorumSlhSignBytes` runs under an arbitrary zero-sharing tape
  expanded from the session's pairwise PRG seeds, but its gate messages are not on the modelled
  wire. The Round-2 honest message is still one 64-bit `χ` lane computed from the first eight
  bytes of each share and masked by a pad that is never used again; no later step consumes it.
  The full gate transcript of the signature computation is not modelled.
* The corrupt Round-2 frame carries a private `deg`-gate stream. The barrier recomputes it
  from the corrupt party's replicated share windows held by the honest vault, checks its
  length, and compares Horner accumulators. This replaces the public-hash wire check, but
  does not yet identify that stream with every gate of the production signing circuit.
* Coin toss. The challenge is `coinA ⊕ coinB ⊕ corruptCoin` read directly as a `GF(2^128)` point.
  The production engine commits with `cSHAKE256` to 32-byte shares bound to the wave transcript
  digest, hashes the XOR of the opened shares, and expands evaluation points from that hash;
  those hashing steps are random-oracle steps and are not modelled. The corrupt party opens its
  share in the same Round-2 frame as its wires, before the honest shares are opened in Round 3.
  The honest Round-1 commitments are deterministic `SHAKE256` values of the honest coin shares;
  nothing in this file proves that they hide those shares. The counted `deg / 2^128` bound is
  proved in the game where they carry the zero coin, and the hop to the protocol is the explicit
  term `advCoinHide` (an adversary that ignores honest Round-1 messages has `advCoinHide = 0`, as
  used in `tooth_skipping_pre_cut_barrier_leaks_key_bit`).
* Parsing requires a 24-byte opening and exactly `deg > 0` field elements, and consumes the
  complete frame.
* Both execution engines record approval before releasing Round-3 openings, including when
  `finalizeCutOpen` subsequently fails. `slhForgeryWins` retains its transcript-based freshness
  predicate over sessions that reached Round 3.
* Hash-game witnesses are stated over `Qsag.Fips205` (`SHAKE256` collisions, chain preimages, FORS
  coverage). They are not instances of the `Qsag.HypertreeEufCma` witness types, which belong to
  the tweakable-hash WOTS+C hypertree scheme; the weld for that scheme is
  `uc_emulation_forgery_to_hypertree_hash_game` in `Qsag.InteractiveUcEngine`.
-/

public import Qsag.Tactic.Prelude
public import Qsag.Math.Goldilocks
public import Qsag.Math.Gf2Pow128
public import Qsag.Oracle.Keccak
public import Qsag.Protocol.Signing.Fips205
public import Qsag.Protocol.Aggregation.UcGames
public import Qsag.Protocol.Threshold.ThresholdApproval
public import Qsag.Protocol.Threshold.IdealTsig
public import Qsag.Protocol.Threshold.ThresholdMpc
public import Qsag.Protocol.Threshold.MaliciousSecurity
public import Qsag.Exec.InteractiveUcEngine
public import Qsag.Protocol.Threshold.RssSlhFullSecurity
import all Qsag.Protocol.Aggregation.UcGames
import all Qsag.Protocol.Signing.Fips205
import all Qsag.Protocol.Threshold.ThresholdMpc
import all Qsag.Protocol.Threshold.MaliciousSecurity
import all Qsag.Exec.InteractiveUcEngine
import all Qsag.Protocol.Threshold.RssSlhFullSecurity

import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt8.instLawfulOrderOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd BitVec.instTransOrd
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## 2. Concrete 3-Round Interactive RSS/SPDZ Protocol over the UC Engine -/

/-- The root count is invariant under translating the challenge by a fixed `k`: a uniform coin
    share XORed with any value fixed beforehand is still a uniform challenge. -/
theorem tower128_shifted_roots_qsum_le (deg : Nat) (deltas : List Tower128) (k : BitVec 128)
    (hLen : deltas.length ≤ deg)
    (hNonzero : ∃ d ∈ deltas, d ≠ towerZero 7) :
    qsum (2 ^ 128)
      (fun r => if batchDeviationPoly deltas (unpackTower 7 (BitVec.ofFin r ^^^ k)) == towerZero 7
                then 1 else 0) ≤ deg := by
  refine Nat.le_trans (Nat.le_of_eq ?_) (tower128_roots_qsum_le deg deltas hLen hNonzero)
  refine Eq.trans ?_ (qsum_equiv_eq (finBitVecXorEquiv 128 k) _)
  exact qsum_congr (fun _ => rfl)

def encodeSlhReqPreimage (req : SessionScheduleReq) : List UInt8 :=
  encodeMultiFrame [slhReqDomainTag, leb128 req.reqEpoch, req.optRand, req.msg]

def slhReqDigest (req : SessionScheduleReq) : List UInt8 :=
  let framed := encodeSlhReqPreimage req
  shake256Xof 32 framed ++ framed

theorem slhReqDigest_injective_on_epoch_optRand_msg {req₁ req₂ : SessionScheduleReq}
    (h : slhReqDigest req₁ = slhReqDigest req₂) :
    req₁.reqEpoch = req₂.reqEpoch ∧ req₁.optRand = req₂.optRand ∧ req₁.msg = req₂.msg := by
  unfold slhReqDigest at h
  dsimp only at h
  have hLenEq : (shake256Xof 32 (encodeSlhReqPreimage req₁)).length =
                (shake256Xof 32 (encodeSlhReqPreimage req₂)).length := by
    rw [shake256Xof_length, shake256Xof_length]
  obtain ⟨_, hFramed⟩ := List.append_inj h hLenEq
  have hF := encodeMultiFrame_injective hFramed
  simp only [List.cons.injEq] at hF
  exact ⟨leb128_inj hF.2.1, hF.2.2.1, hF.2.2.2.1⟩

/-- Shared Round-1 commitment check used identically by `rssSlhInteractiveProtocol` and `Sim_RssSlh`. -/
def sharedVerifyRound1 (cIdx : Fin 3) (r1St : RssRound1State)
    (corrR1 : List (Nat × ByteArray)) : PSum (AbortReason × Bool) RssRound2State :=
  match corrR1.find? (fun pr => pr.1 == cIdx.val) with
  | none => .inl (.round1CommitMismatch cIdx.val, false)
  | some (_, cWire) =>
    if (unpackWireBytes cWire).length != 32 then .inl (.round1CommitMismatch cIdx.val, false)
    else .inr { cursor := r1St.cursor, corrR1Commit := cWire, gammaBits := 0#128,
                expectedWires := [] }

/-- **Commit-then-open coin toss feeding the barrier (`sharedCoinTossBarrier`).** On entry
    `r2St.gammaBits` is the honest pair's joint coin share `coinA ⊕ coinB`, neither half of which
    has been sent. The corrupt party's Round-2 frame carries its opening together with its gate
    wires; `sharedPreCutBarrier` checks that opening against the Round-1 commitment and evaluates
    both Horner accumulators at the joint coin `coinA ⊕ coinB ⊕ corruptCoin`. -/
def sharedCoinTossBarrier (cIdx : Fin 3) (deg : Nat) (pk : SlhPublicKey)
    (req : SessionScheduleReq) (r2St : RssRound2State)
    (corrR2 : List (Nat × ByteArray)) : PSum AbortReason RssRound3State :=
  sharedPreCutBarrier cIdx deg pk req
    { r2St with gammaBits := r2St.gammaBits ^^^ corruptOpenedCoin cIdx deg corrR2 } corrR2

/-- Shared Round-3 `FLNW17` cross-check + NIST FIPS 205 signature assembly & verification gate. -/
def sharedFinalizeCutOpen (p : Fips205Params) (cIdx : Fin 3)
    (pk : SlhPublicKey) (req : SessionScheduleReq)
    (cutShares : RssByteShares) (corrR3 : List (Nat × ByteArray)) :
    PSum AbortReason ByteArray :=
  match checkRound3ActiveOpen p.sigBytes cIdx cutShares corrR3 with
  | none => .inl (.cutOpenMismatch cIdx.val)
  | some openedBytes =>
    match decodeSlhSig p openedBytes with
    | none => .inl (.cutOpenMismatch cIdx.val)
    | some sig =>
      if slhVerifyInternal p req.msg sig pk then
        .inr (packWireBytes openedBytes)
      else
        .inl (.cutOpenMismatch cIdx.val)

theorem sharedFinalizeCutOpen_output (p : Fips205Params) (cIdx : Fin 3)
    (pk : SlhPublicKey) (req : SessionScheduleReq) (cutSh : RssByteShares)
    (corr : List (Nat × ByteArray)) (out : ByteArray)
    (h : sharedFinalizeCutOpen p cIdx pk req cutSh corr = .inr out) :
    out = packWireBytes (reconstructRssBytes cutSh) := by
  unfold sharedFinalizeCutOpen at h
  cases hc : checkRound3ActiveOpen p.sigBytes cIdx cutSh corr with
  | none => rw [hc] at h; cases h
  | some opened =>
    rw [hc] at h
    dsimp only at h
    have heq := checkRound3ActiveOpen_output p.sigBytes cIdx cutSh corr opened hc
    cases hd : decodeSlhSig p opened with
    | none => rw [hd] at h; cases h
    | some sig =>
      rw [hd] at h
      dsimp only at h
      split at h
      · cases h
        exact congrArg packWireBytes heq
      · cases h

theorem sharedFinalizeCutOpen_deliver_exact (p : Fips205Params) (cIdx : Fin 3)
    (pk : SlhPublicKey) (req : SessionScheduleReq) (s b0 b1 : List UInt8)
    (h0 : s.length = b0.length) (h1 : b0.length = b1.length)
    (corr : List (Nat × ByteArray)) :
    (match sharedFinalizeCutOpen p cIdx pk req
        ⟨b0, b1, xorByteStream s (xorByteStream b0 b1)⟩ corr with
     | .inl err => .inl err
     | .inr _ => .inr (packWireBytes s)) =
    sharedFinalizeCutOpen p cIdx pk req
      ⟨b0, b1, xorByteStream s (xorByteStream b0 b1)⟩ corr := by
  cases hf : sharedFinalizeCutOpen p cIdx pk req
      ⟨b0, b1, xorByteStream s (xorByteStream b0 b1)⟩ corr with
  | inl err => rfl
  | inr out =>
    have heq := sharedFinalizeCutOpen_output p cIdx pk req _ corr out hf
    rw [reconstructRssBytes_masked_eq h0 h1] at heq
    rw [heq]

/-- Public tag of a coin commitment: the public key, the request (session id, epoch, message,
    hedge, approvers), the monotonic mask cursor and the committing party. -/
structure RssCoinTag where
  pk     : SlhPublicKey
  req    : SessionScheduleReq
  cursor : Nat
  party  : Nat

/-- Three-round RSS execution with a private per-gate stream. The real game commits
its honest coin shares; the decoy game commits zero and is used for the root count.
The barrier always checks the private stream computed from the honest vault. -/
@[expose] def rssSlhCoinProtocol (commitCoins : Bool) (p : Fips205Params) (cIdx : Fin 3) (deg : Nat) :
    InteractiveThresholdProtocol SlhPublicKey RssPartyKeyShare (RssSlhSessionTape p.sigBytes)
      RssRound1State RssRound2State RssRound3State where
  pkDigestOf := slhPkDigest
  msgDigestOf := slhReqDigest
  honestRound1 := fun pk _corrupt req cursor _shares tape =>
    let (hA, hB, _) := honestPairForCorrupt cIdx
    let mA := round1NonceCommit pk req cursor hA
      (coinOpeningBytes (committedCoin commitCoins tape.gammaBits) tape.nonceA)
    let mB := round1NonceCommit pk req cursor hB
      (coinOpeningBytes (committedCoin commitCoins tape.coinB) tape.nonceB)
    ([(hA, mA), (hB, mB)], { cursor := cursor })
  verifyRound1 := fun _pk _req r1St _honR1 corrR1 =>
    sharedVerifyRound1 cIdx r1St corrR1
  honestRound2 := fun _pk _corrupt req r2Init shares tape =>
    let (hA, hB, _) := honestPairForCorrupt cIdx
    let wA := match shares hA with
              | some shA => computeHonestChiWord hA shA req.msg
              | none => 0#64
    let wB := match shares hB with
              | some shB => computeHonestChiWord hB shB req.msg
              | none => 0#64
    let wireA := packWireBytes (bvToFixedBytes 8 (wA ^^^ tape.chiMaskA))
    let wireB := packWireBytes (bvToFixedBytes 8 (wB ^^^ tape.chiMaskB))
    ([(hA, wireA), (hB, wireB)],
     { r2Init with gammaBits := tape.gammaBits ^^^ tape.coinB,
                   expectedWires := corruptExpectedChiStream cIdx deg
                     (corruptViewOfVault cIdx shares) req.msg })
  preCutBarrier := fun pk req r2St _honR2 corrR2 =>
    sharedCoinTossBarrier cIdx deg pk req r2St corrR2
  honestRound3 := fun pk _corrupt req r3Init shares tape =>
    let (_, _, q) := honestPairForCorrupt cIdx
    match extractHonestQuorumViews p.sigBytes cIdx shares with
    | none => ([], { r3Init with cutShares := ⟨[], [], []⟩ })
    | some (seedViews, prfViews, rawTag0, rawTag1) =>
      let trueSigBytes := rssQuorumSlhSignBytes p q seedViews prfViews pk.pkSeed
                            (expandPairwiseSeedTape tape.prgSeeds) req.msg req.optRand
      let crossByte :=
        evalReplicatedGateCrossByte seedViews.1.1 r3Init.sentWires r3Init.expectedWires
      let preCutBytes :=
        xorByteStream trueSigBytes (crossByte :: List.replicate (p.sigBytes - 1) 0)
      let cutB0 := bvToFixedBytes p.sigBytes (rawTag0 ^^^ tape.cutMask0)
      let cutB1 := bvToFixedBytes p.sigBytes (rawTag1 ^^^ tape.cutMask1)
      let cutB2 := xorByteStream preCutBytes (xorByteStream cutB0 cutB1)
      let cutSh : RssByteShares := ⟨cutB0, cutB1, cutB2⟩
      (buildHonestRound3Msgs cIdx cutSh ++ honestCoinOpeningMsgs cIdx tape.gammaBits tape.nonceA tape.coinB tape.nonceB,
       { r3Init with cutShares := cutSh })
  finalizeCutOpen := fun pk req r3St _honR3 corrR3 =>
    sharedFinalizeCutOpen p cIdx pk req r3St.cutShares corrR3

/-- Real execution commits to the coin shares opened in Round 3. -/
@[expose] def rssSlhInteractiveProtocol (p : Fips205Params) (cIdx : Fin 3) (deg : Nat) :
    InteractiveThresholdProtocol SlhPublicKey RssPartyKeyShare (RssSlhSessionTape p.sigBytes)
      RssRound1State RssRound2State RssRound3State :=
  rssSlhCoinProtocol true p cIdx deg

/-- **Explicit Black-Box UC Simulator (`Sim_RssSlh`)**:
    Receives public parameters `(p, cIdx, deg)`, public key `pk : SlhPublicKey`, the corrupt
    party's own replicated share view `corrView` (what the adversary holds; two of the three
    additive shares, which do not determine the key), and (upon `t`-quorum approval +
    `preCutBarrier` pass in `IdealTsig`) the ideal signature `idealSigBytes : ByteArray`.
    `Sim_RssSlh` has no access to `SlhSecretKey`, `skSeed`, `skPrf`, or any honest party's share.
    It runs the coin toss exactly as the honest parties do (commit, barrier, open). -/
@[expose] def Sim_RssSlh (corrView : RssPartyKeyShare) (p : Fips205Params) (cIdx : Fin 3) (deg : Nat) :
    BlackBoxUcSimulator SlhPublicKey (RssSlhSessionTape p.sigBytes)
      RssRound1State RssRound2State RssRound3State where
  pkDigestOf := slhPkDigest
  msgDigestOf := slhReqDigest
  simRound1 := fun pk _corrupt req cursor tape =>
    let (hA, hB, _) := honestPairForCorrupt cIdx
    let mA := round1NonceCommit pk req cursor hA
      (coinOpeningBytes tape.gammaBits tape.nonceA)
    let mB := round1NonceCommit pk req cursor hB
      (coinOpeningBytes tape.coinB tape.nonceB)
    ([(hA, mA), (hB, mB)], { cursor := cursor })
  simVerifyRound1 := fun _pk _req r1St _honR1 corrR1 =>
    sharedVerifyRound1 cIdx r1St corrR1
  simRound2 := fun _pk _corrupt req r2Init tape =>
    let (hA, hB, _) := honestPairForCorrupt cIdx
    let wireA := packWireBytes (bvToFixedBytes 8 tape.chiMaskA)
    let wireB := packWireBytes (bvToFixedBytes 8 tape.chiMaskB)
    ([(hA, wireA), (hB, wireB)],
     { r2Init with gammaBits := tape.gammaBits ^^^ tape.coinB,
                   expectedWires := corruptExpectedChiStream cIdx deg (some corrView) req.msg })
  simPreCutBarrier := fun pk req r2St _honR2 corrR2 =>
    sharedCoinTossBarrier cIdx deg pk req r2St corrR2
  simRound3 := fun _pk _corrupt _req r3Init idealSigBytes tape =>
    let cutB0 := bvToFixedBytes p.sigBytes tape.cutMask0
    let cutB1 := bvToFixedBytes p.sigBytes tape.cutMask1
    let cutB2 := xorByteStream (unpackWireBytes idealSigBytes) (xorByteStream cutB0 cutB1)
    let cutSh : RssByteShares := ⟨cutB0, cutB1, cutB2⟩
    (buildHonestRound3Msgs cIdx cutSh ++ honestCoinOpeningMsgs cIdx tape.gammaBits tape.nonceA tape.coinB tape.nonceB,
     { r3Init with cutShares := cutSh })
  simFinalizeCut := fun pk req r3St _idealSigBytes _honR3 corrR3 =>
    sharedFinalizeCutOpen p cIdx pk req r3St.cutShares corrR3

/-! ## 3. Crown-Jewel Theorem 1: Whole-Transcript Multi-Session UC Indistinguishability
    (`rss_slh_real_ideal_view_indistinguishable` & `spdz_shamir_tower128_masked_view_stat_dist_zero`) -/

/-- Ideal signing oracle for `IdealTsig` instantiated with NIST `FIPS 205` `slhSignInternal`. -/
def slhIdealSignOracle (p : Fips205Params) (sk : SlhSecretKey) : SessionScheduleReq → ByteArray :=
  fun req => packWireBytes (encodeSlhSig (slhSignInternal p req.msg sk req.optRand))

/-- Secret-dependent session mask shifts `(wA, wB, rawTag0, rawTag1)` for one scheduled session. -/
def honestSessionShifts (L : Nat) (cIdx : Fin 3)
    (shares : Nat → Option RssPartyKeyShare) (req : SessionScheduleReq) :
    BitVec 64 × BitVec 64 × BitVec (8 * L) × BitVec (8 * L) :=
  let (hA, hB, _) := honestPairForCorrupt cIdx
  let wA := match shares hA with
            | some shA => computeHonestChiWord hA shA req.msg
            | none => 0#64
  let wB := match shares hB with
            | some shB => computeHonestChiWord hB shB req.msg
            | none => 0#64
  match extractHonestQuorumViews L cIdx shares with
  | some (_, _, rawTag0, rawTag1) => (wA, wB, rawTag0, rawTag1)
  | none => (wA, wB, 0#(8 * L), 0#(8 * L))

/-- Cross-session lockstep state relation coupling `RealClusterState` and `IdealClusterState`. -/
structure RealIdealClusterMatch (cIdx : Fin 3) (seedSh prfSh : RssByteShares)
    (cl : RealClusterState SlhPublicKey RssPartyKeyShare)
    (icl : IdealClusterState SlhPublicKey) : Prop where
  pk_eq         : cl.tsig.pk = icl.tsig.pk
  th_eq         : cl.tsig.threshold = icl.tsig.threshold
  np_eq         : cl.tsig.numParties = icl.tsig.numParties
  corr_eq       : cl.tsig.corruptParties = icl.tsig.corruptParties
  cheat_eq      : cl.tsig.identifiedCheaters = icl.tsig.identifiedCheaters
  wal_eq        : cl.honestWal = icl.honestWal
  cursor_eq     : cl.maskSessionCursor = icl.maskSessionCursor
  shares_intact : cl.honestWal.poisoned = false →
                    cl.honestShares = dealHonestRssVault cIdx seedSh prfSh

private theorem extractHonestQuorumViews_deal (L : Nat) (cIdx : Fin 3)
    (seedSh prfSh : RssByteShares) (req : SessionScheduleReq) :
    let (_, _, q) := honestPairForCorrupt cIdx
    let (_, _, rawTag0, rawTag1) :=
      honestSessionShifts L cIdx (dealHonestRssVault cIdx seedSh prfSh) req
    extractHonestQuorumViews L cIdx (dealHonestRssVault cIdx seedSh prfSh) =
      some (q.views seedSh, q.views prfSh, rawTag0, rawTag1) := by
  rcases cIdx with ⟨_ | _ | _ | n, hv⟩
  · rfl
  · rfl
  · rfl
  · exact False.elim (Nat.not_lt_zero n (Nat.lt_of_add_lt_add_right hv))

/-- Extract the adversary's non-zero Round-2 wire deviation batch `deltas = sentWires ⊕ expectedWires`
    (`deltas.length ≤ deg` and `∃ d ∈ deltas, d ≠ 0`) together with the coin share it opened, when
    the Round-1/quorum/WAL gates pass. This is the adversary's side of the barrier: everything it
    fixes before the honest coin shares are opened. -/
def extractSessionNonzeroDeltas {AdvState : Type} (commitCoins : Bool)
    (p : Fips205Params) (cIdx : Fin 3) (deg : Nat)
    (A : UcRushingAdversary AdvState)
    (cl : RealClusterState SlhPublicKey RssPartyKeyShare)
    (advSt : AdvState)
    (tape : RssSlhSessionTape p.sigBytes) : Option (List Tower128 × BitVec 128) :=
  let proto := rssSlhCoinProtocol commitCoins p cIdx deg
  let (req, advSt1) := A.scheduleSession advSt
  if !(validThresholdApproval cl.tsig req.honestApprovers) then none
  else
    let pkDig := proto.pkDigestOf cl.tsig.pk
    let msgDig := proto.msgDigestOf req
    match walPreSignStep cl.honestWal pkDig req.reqEpoch msgDig with
    | .err _ _ => none
    | .ok _ (.replayCached _) => none
    | .ok _ (.authorizedFresh _) =>
      let (honR1, r1St) :=
        proto.honestRound1 cl.tsig.pk cl.tsig.corruptParties req cl.maskSessionCursor cl.honestShares tape
      let (corrR1Fn, advSt2) := A.rushRound1 advSt1 honR1
      let corrR1 := cl.tsig.corruptParties.map (fun c => (c, corrR1Fn c))
      match proto.verifyRound1 cl.tsig.pk req r1St honR1 corrR1 with
      | .inl _ => none
      | .inr r2Init =>
        let (honR2, r2St0) :=
          proto.honestRound2 cl.tsig.pk cl.tsig.corruptParties req r2Init cl.honestShares tape
        let (corrR2Fn, _) := A.rushRound2 advSt2 honR2
        let corrR2 := cl.tsig.corruptParties.map (fun c => (c, corrR2Fn c))
        let deviation := preCutNonzeroDeltas cIdx deg cl.tsig.pk req r2St0.cursor r2St0.corrR1Commit r2St0.expectedWires corrR2
        deviation.map (fun deltas => (deltas, corruptOpenedCoin cIdx deg corrR2))

private theorem extractSessionNonzeroDeltas_props {AdvState : Type} (commitCoins : Bool)
    (p : Fips205Params) (cIdx : Fin 3) (deg : Nat)
    (A : UcRushingAdversary AdvState)
    (cl : RealClusterState SlhPublicKey RssPartyKeyShare)
    (advSt : AdvState)
    (tape : RssSlhSessionTape p.sigBytes)
    {deltas : List Tower128} {cCoin : BitVec 128}
    (hSome : extractSessionNonzeroDeltas commitCoins p cIdx deg A cl advSt tape = some (deltas, cCoin)) :
    deltas.length ≤ deg ∧ ∃ d ∈ deltas, d ≠ towerZero 7 := by
  unfold extractSessionNonzeroDeltas preCutNonzeroDeltas at hSome
  dsimp only at hSome
  cases hVal : validThresholdApproval cl.tsig (A.scheduleSession advSt).1.honestApprovers
  · rw [hVal] at hSome; simp at hSome
  · rw [hVal] at hSome
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hSome
    cases hWal : walPreSignStep cl.honestWal
        ((rssSlhCoinProtocol commitCoins p cIdx deg).pkDigestOf cl.tsig.pk)
        (A.scheduleSession advSt).1.reqEpoch
        ((rssSlhCoinProtocol commitCoins p cIdx deg).msgDigestOf (A.scheduleSession advSt).1) with
    | err _ _ => rw [hWal] at hSome; cases hSome
    | ok _ res =>
      rw [hWal] at hSome
      cases res with
      | replayCached _ => cases hSome
      | authorizedFresh _ =>
        dsimp only at hSome
        let r1Out := (rssSlhCoinProtocol commitCoins p cIdx deg).honestRound1
          cl.tsig.pk cl.tsig.corruptParties (A.scheduleSession advSt).1
          cl.maskSessionCursor cl.honestShares tape
        let corrR1 := cl.tsig.corruptParties.map
          (fun c => (c, (A.rushRound1 (A.scheduleSession advSt).2 r1Out.1).1 c))
        cases hVR1 : (rssSlhCoinProtocol commitCoins p cIdx deg).verifyRound1
            cl.tsig.pk (A.scheduleSession advSt).1 r1Out.2 r1Out.1 corrR1 with
        | inl _ => rw [hVR1] at hSome; cases hSome
        | inr r2Init =>
          rw [hVR1] at hSome
          dsimp only at hSome
          let r2Out := (rssSlhCoinProtocol commitCoins p cIdx deg).honestRound2
            cl.tsig.pk cl.tsig.corruptParties (A.scheduleSession advSt).1
            r2Init cl.honestShares tape
          let advSt2 := (A.rushRound1 (A.scheduleSession advSt).2 r1Out.1).2
          let corrR2 := cl.tsig.corruptParties.map
            (fun c => (c, (A.rushRound2 advSt2 r2Out.1).1 c))
          cases hFind : corrR2.find? (fun pr => pr.1 == cIdx.val) with
          | none => rw [hFind] at hSome; cases hSome
          | some pr =>
            rcases pr with ⟨_, cWire2⟩
            rw [hFind] at hSome
            dsimp only at hSome
            cases hParse : parseCorruptRound2Wire deg cWire2 with
            | none => rw [hParse] at hSome; cases hSome
            | some nd =>
              rcases nd with ⟨nonceC, sws⟩
              rw [hParse] at hSome
              dsimp only at hSome
              cases hCmt : (round1NonceCommit cl.tsig.pk (A.scheduleSession advSt).1
                  r2Out.2.cursor cIdx.val nonceC != r2Out.2.corrR1Commit)
              · rw [hCmt] at hSome
                simp only [Bool.false_eq_true, ↓reduceIte] at hSome
                let ews := r2Out.2.expectedWires
                by_cases hLen : sws.length = ews.length
                · rw [ite_eq_right (show ¬ (sws.length ≠ ews.length) from fun h => h hLen)] at hSome
                  let ds := zipXorTower 7 sws ews
                  cases hAny : ds.any (fun d => decide (d ≠ towerZero 7))
                  · change (if ds.any (fun d => decide (d ≠ towerZero 7)) then some ds else none).map _ = some (deltas, cCoin) at hSome
                    rw [hAny] at hSome; simp at hSome
                  · change (if ds.any (fun d => decide (d ≠ towerZero 7)) then some ds else none).map _ = some (deltas, cCoin) at hSome
                    rw [hAny] at hSome
                    simp only [↓reduceIte, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hSome
                    obtain ⟨hDs, _⟩ := hSome
                    subst hDs
                    obtain ⟨d, hdMem, hdDec⟩ := List.any_eq_true.mp hAny
                    exact ⟨Nat.le_trans (zipXorTower_length_le_left 7 sws ews)
                             (parseCorruptRound2Wire_length_le deg cWire2 hParse),
                           d, hdMem, of_decide_eq_true hdDec⟩
                · rw [ite_eq_left hLen] at hSome; simp at hSome
              · rw [hCmt] at hSome; simp at hSome

/-- In the commitment-decoy game nothing the adversary sees before the barrier depends on the
    first honest coin share. -/
private theorem extractSessionNonzeroDeltas_decoy_gamma_irrel {AdvState : Type}
    (p : Fips205Params) (cIdx : Fin 3) (deg : Nat)
    (A : UcRushingAdversary AdvState)
    (cl : RealClusterState SlhPublicKey RssPartyKeyShare)
    (advSt : AdvState)
    (tape : RssSlhSessionTape p.sigBytes) (g : BitVec 128) :
    extractSessionNonzeroDeltas false p cIdx deg A cl advSt { tape with gammaBits := g } =
    extractSessionNonzeroDeltas false p cIdx deg A cl advSt tape := rfl

/-- Single-session `GF(2^128)` (`Tower128`) root-hit indicator: `true` iff the rushing adversary
    submits a non-zero wire deviation `deltas` in Round 2 AND the joint coin
    `gammaBits ⊕ coinB ⊕ corruptCoin` is a root of `batchDeviationPoly deltas`. -/
def sessionBadHit {AdvState : Type} (commitCoins : Bool)
    (p : Fips205Params) (cIdx : Fin 3) (deg : Nat)
    (A : UcRushingAdversary AdvState)
    (cl : RealClusterState SlhPublicKey RssPartyKeyShare)
    (advSt : AdvState)
    (cur : Fin (rssFullSessionCard p.sigBytes)) : Bool :=
  let tape := decodeSingleFullTape p.sigBytes cur
  match extractSessionNonzeroDeltas commitCoins p cIdx deg A cl advSt tape with
  | none => false
  | some (deltas, cCoin) =>
    batchDeviationPoly deltas (unpackTower 7 ((tape.gammaBits ^^^ tape.coinB) ^^^ cCoin)) == towerZero 7

/-- Single-session root-hit count in the commitment-decoy game:
    `badCount_1 ≤ rssPadSessionCard p.sigBytes * deg`, hence `badCount_1 * 2^128 ≤ deg * rssFullSessionCard`.
    For every value of the rest of the tape the deviation and the corrupt coin share are fixed, and
    the first honest coin share ranges over all of `GF(2^128)`. -/
private theorem sessionBadHit_qsum_le {AdvState : Type}
    (p : Fips205Params) (cIdx : Fin 3) (deg : Nat)
    (A : UcRushingAdversary AdvState)
    (cl : RealClusterState SlhPublicKey RssPartyKeyShare)
    (advSt : AdvState) :
    qsum (rssFullSessionCard p.sigBytes)
      (fun cur => if sessionBadHit false p cIdx deg A cl advSt cur then 1 else 0) ≤
    rssPadSessionCard p.sigBytes * deg := by
  unfold rssFullSessionCard
  rw [qsum_prod_eq (rssPadSessionCard p.sigBytes) (2 ^ 128)]
  rw [← qsum_const (rssPadSessionCard p.sigBytes) deg]
  apply qsum_le_qsum
  intro padIdx
  obtain ⟨tape0, hT0⟩ : ∃ t, decodeRssSessionTape p.sigBytes padIdx ⟨0, Nat.two_pow_pos 128⟩ = t :=
    ⟨_, rfl⟩
  have hInner :
      qsum (2 ^ 128) (fun gIdx =>
        if sessionBadHit false p cIdx deg A cl advSt (pairFin padIdx gIdx) then 1 else 0) =
      qsum (2 ^ 128) (fun gIdx =>
        if (match extractSessionNonzeroDeltas false p cIdx deg A cl advSt tape0 with
            | none => false
            | some (deltas, cCoin) =>
              batchDeviationPoly deltas
                (unpackTower 7 (BitVec.ofFin gIdx ^^^ (tape0.coinB ^^^ cCoin))) == towerZero 7)
        then 1 else 0) := by
    apply qsum_congr
    intro gIdx
    have hB : sessionBadHit false p cIdx deg A cl advSt (pairFin padIdx gIdx) =
        (match extractSessionNonzeroDeltas false p cIdx deg A cl advSt tape0 with
         | none => false
         | some (deltas, cCoin) =>
           batchDeviationPoly deltas
             (unpackTower 7 (BitVec.ofFin gIdx ^^^ (tape0.coinB ^^^ cCoin))) == towerZero 7) := by
      unfold sessionBadHit decodeSingleFullTape
      dsimp only
      rw [splitFinLeft_pairFin, splitFinRight_pairFin,
          decodeRssSessionTape_gamma p.sigBytes padIdx gIdx, hT0]
      dsimp only
      rw [extractSessionNonzeroDeltas_decoy_gamma_irrel p cIdx deg A cl advSt tape0 (BitVec.ofFin gIdx)]
      cases extractSessionNonzeroDeltas false p cIdx deg A cl advSt tape0 with
      | none => rfl
      | some pr =>
        rcases pr with ⟨ds, cCoin⟩
        dsimp only
        rw [BitVec.xor_assoc]
    rw [hB]
  rw [hInner]
  cases hExt : extractSessionNonzeroDeltas false p cIdx deg A cl advSt tape0 with
  | none =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have h0 : qsum (2 ^ 128) (fun _ => 0) = 0 := by rw [qsum_const, Nat.mul_zero]
    rw [h0]
    exact Nat.zero_le deg
  | some pr =>
    rcases pr with ⟨deltas, cCoin⟩
    obtain ⟨hLen, hNz⟩ := extractSessionNonzeroDeltas_props false p cIdx deg A cl advSt tape0 hExt
    refine Nat.le_trans (Nat.le_of_eq ?_) (tower128_roots_qsum_le deg deltas hLen hNz)
    refine Eq.trans ?_ (qsum_equiv_eq (finBitVecXorEquiv 128 (tape0.coinB ^^^ cCoin)) _)
    exact qsum_congr (fun _ => rfl)

/-- Per-session adaptive tape bijection conditioned on `(cl, advSt)`:
    uses `honestSessionShifts` on the scheduled `req` when `cl` and `advSt` run Round 2. -/
def adaptiveSingleSessionEquiv {AdvState : Type}
    (p : Fips205Params) (cIdx : Fin 3)
    (A : UcRushingAdversary AdvState)
    (cl : RealClusterState SlhPublicKey RssPartyKeyShare)
    (advSt : AdvState) :
    SimpleEquiv (Fin (rssFullSessionCard p.sigBytes)) (Fin (rssFullSessionCard p.sigBytes)) :=
  let (req, _) := A.scheduleSession advSt
  let (wA, wB, rawTag0, rawTag1) := honestSessionShifts p.sigBytes cIdx cl.honestShares req
  sessionFullTapeXorEquiv p.sigBytes wA wB rawTag0 rawTag1

private theorem walPreSignStep_authorizedFresh_unpoisoned
    {st wal' : WalLatchState} {pkDig : List UInt8} {ep epOut : Nat} {msgDig : List UInt8}
    (hOk : walPreSignStep st pkDig ep msgDig = .ok wal' (.authorizedFresh epOut)) :
    st.poisoned = false ∧ wal' = st := by
  unfold walPreSignStep at hOk
  cases hp : st.poisoned
  · simp only [hp, Bool.false_eq_true, ↓reduceIte] at hOk
    cases hPk : decide (pkDig = st.enrolledPkDigest)
    · rw [hPk] at hOk; simp at hOk
    · rw [hPk] at hOk
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
      cases hLat : st.latchedRecord with
      | none =>
        rw [hLat] at hOk
        cases hEp : (ep == st.nextEpoch)
        · rw [hEp] at hOk; simp at hOk
        · rw [hEp] at hOk
          simp only [↓reduceIte, UcStepOutcome.ok.injEq] at hOk
          exact ⟨rfl, hOk.1.symm⟩
      | some rec0 =>
        rcases rec0 with ⟨ep0, prevMd, prevSig⟩
        rw [hLat] at hOk
        dsimp only at hOk
        cases hHit : (ep == ep0 && decide (msgDig = prevMd))
        · rw [hHit] at hOk
          simp only [Bool.false_eq_true, ↓reduceIte] at hOk
          cases hEp : (ep == st.nextEpoch)
          · rw [hEp] at hOk; simp at hOk
          · rw [hEp] at hOk
            simp only [↓reduceIte, UcStepOutcome.ok.injEq] at hOk
            exact ⟨rfl, hOk.1.symm⟩
        · rw [hHit] at hOk; simp at hOk
  · simp [hp] at hOk

private theorem honestSessionShifts_fst_snd (L : Nat) (cIdx : Fin 3)
    (shares : Nat → Option RssPartyKeyShare) (req : SessionScheduleReq) :
    (honestSessionShifts L cIdx shares req).1 =
      (match shares (honestPairForCorrupt cIdx).1 with
       | some shA => computeHonestChiWord (honestPairForCorrupt cIdx).1 shA req.msg
       | none => 0#64) ∧
    (honestSessionShifts L cIdx shares req).2.1 =
      (match shares (honestPairForCorrupt cIdx).2.1 with
       | some shB => computeHonestChiWord (honestPairForCorrupt cIdx).2.1 shB req.msg
       | none => 0#64) := by
  unfold honestSessionShifts
  dsimp only
  cases extractHonestQuorumViews L cIdx shares <;> exact ⟨rfl, rfl⟩

/-- **Core Single-Session Lockstep Equivalence (`execRealSession_eq_execIdealSession_unless_bad`)**:
    Under `RealIdealClusterMatch cIdx seedSh prfSh cl icl`, whenever `sessionBadHit ... cur = false`,
    `execRealSession` on `decodeSingleFullTape L cur` and `execIdealSession` on
    `decodeSingleFullTape L ((adaptiveSingleSessionEquiv ...).toFun cur)` produce:
    1. **Bit-for-bit identical** `(advSt', SessionWireRecord)` (including every wire `ByteArray` and
       exact `AbortReason`), AND
    2. Successor states `(cl', icl')` preserving `RealIdealClusterMatch`! -/
theorem execRealSession_eq_execIdealSession_unless_bad {AdvState : Type}
    (p : Fips205Params) (hWf : p.wellFormed = true)
    (cIdx : Fin 3) (deg : Nat)
    {seedSh prfSh : RssByteShares}
    (hSeedWf : seedSh.WellFormed) (hPrfWf : prfSh.WellFormed)
    (pkSeed : List UInt8)
    (A : UcRushingAdversary AdvState)
    (cl : RealClusterState SlhPublicKey RssPartyKeyShare)
    (icl : IdealClusterState SlhPublicKey)
    (advSt : AdvState)
    (hMatch : RealIdealClusterMatch cIdx seedSh prfSh cl icl)
    (hPkKey : cl.tsig.pk = (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).2)
    (cur : Fin (rssFullSessionCard p.sigBytes))
    (hNoBad : sessionBadHit true p cIdx deg A cl advSt cur = false) :
    let sk := (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).1
    let tapeReal := decodeSingleFullTape p.sigBytes cur
    let tapeSim := decodeSingleFullTape p.sigBytes
                     ((adaptiveSingleSessionEquiv p cIdx A cl advSt).toFun cur)
    let resR :=
      execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt tapeReal
    let resI :=
      execIdealSession (slhIdealSignOracle p sk) (Sim_RssSlh (corruptRssView cIdx seedSh prfSh) p cIdx deg) A icl advSt tapeSim
    resR.2.1 = resI.2.1 ∧
    resR.2.2 = resI.2.2 ∧
    resR.1.tsig.pk = cl.tsig.pk ∧
    RealIdealClusterMatch cIdx seedSh prfSh resR.1 resI.1 := by
  rcases hMatch with ⟨hPkEq, hThEq, hNpEq, hCorrEq, hCheatEq, hWalEq, hCurEq, hSharesIntact⟩
  have hQuorumEq : ∀ apps, validThresholdApproval cl.tsig apps = validThresholdApproval icl.tsig apps := by
    intro apps
    unfold validThresholdApproval
    rw [hThEq, hNpEq, hCorrEq, hCheatEq]
  intro sk tapeReal tapeSim resR resI
  dsimp only [resR, resI]
  unfold execRealSession execIdealSession
  dsimp only
  rw [← hQuorumEq]
  cases hQuorum : validThresholdApproval cl.tsig (A.scheduleSession advSt).1.honestApprovers
  · exact ⟨rfl, rfl, rfl, ⟨hPkEq, hThEq, hNpEq, hCorrEq, hCheatEq, hWalEq, hCurEq, hSharesIntact⟩⟩
  · rw [ite_eq_right (by decide : ¬ ((!true) = true)),
        ite_eq_right (by decide : ¬ ((!true) = true))]
    have hPkDigR : (rssSlhInteractiveProtocol p cIdx deg).pkDigestOf = slhPkDigest := rfl
    have hPkDigS : (Sim_RssSlh (corruptRssView cIdx seedSh prfSh) p cIdx deg).pkDigestOf = slhPkDigest := rfl
    have hMsgDigR : (rssSlhInteractiveProtocol p cIdx deg).msgDigestOf = slhReqDigest := rfl
    have hMsgDigS : (Sim_RssSlh (corruptRssView cIdx seedSh prfSh) p cIdx deg).msgDigestOf = slhReqDigest := rfl
    rw [hPkDigR, hPkDigS, hMsgDigR, hMsgDigS, ← hWalEq, ← hPkEq]
    cases hWalStep : walPreSignStep cl.honestWal (slhPkDigest cl.tsig.pk)
                       (A.scheduleSession advSt).1.reqEpoch (slhReqDigest (A.scheduleSession advSt).1) with
    | err wal' rej =>
      dsimp only
      refine ⟨rfl, rfl, rfl, ⟨hPkEq, hThEq, hNpEq, hCorrEq, hCheatEq, rfl, hCurEq, ?_⟩⟩
      intro hp'
      have hUnfold := hWalStep
      unfold walPreSignStep at hUnfold
      cases hp0 : cl.honestWal.poisoned
      · exact hSharesIntact hp0
      · rw [hp0] at hUnfold
        simp only [↓reduceIte, UcStepOutcome.err.injEq] at hUnfold
        rcases hUnfold with ⟨rfl, _⟩
        rw [hp0] at hp'; cases hp'
    | ok wal' walAuth =>
      cases walAuth with
      | replayCached cachedSig =>
        dsimp only
        refine ⟨rfl, rfl, rfl, ⟨hPkEq, hThEq, hNpEq, hCorrEq, hCheatEq, rfl, hCurEq, ?_⟩⟩
        intro hp'
        unfold walPreSignStep at hWalStep
        cases hp0 : cl.honestWal.poisoned
        · exact hSharesIntact hp0
        · simp [hp0] at hWalStep
      | authorizedFresh authEp =>
        obtain ⟨hUnpoisoned, rfl⟩ := walPreSignStep_authorizedFresh_unpoisoned hWalStep
        have hShares : cl.honestShares = dealHonestRssVault cIdx seedSh prfSh :=
          hSharesIntact hUnpoisoned
        let req := (A.scheduleSession advSt).1
        let shifts := honestSessionShifts p.sigBytes cIdx cl.honestShares req
        have hTapeSimEq : tapeSim =
            { coinB := tapeReal.coinB
              prgSeeds := tapeReal.prgSeeds
              nonceA := tapeReal.nonceA
              nonceB := tapeReal.nonceB
              chiMaskA := shifts.1 ^^^ tapeReal.chiMaskA
              chiMaskB := shifts.2.1 ^^^ tapeReal.chiMaskB
              cutMask0 := shifts.2.2.1 ^^^ tapeReal.cutMask0
              cutMask1 := shifts.2.2.2 ^^^ tapeReal.cutMask1
              gammaBits := tapeReal.gammaBits } :=
          decodeSingleFullTape_sessionFullTapeXorEquiv p.sigBytes
            shifts.1 shifts.2.1 shifts.2.2.1 shifts.2.2.2 cur
        have ⟨hSW1, hSW2⟩ := honestSessionShifts_fst_snd p.sigBytes cIdx cl.honestShares req
        have hView : corruptViewOfVault cIdx cl.honestShares =
            some (corruptRssView cIdx seedSh prfSh) := by
          rw [hShares]; exact corruptViewOfVault_deal cIdx seedSh prfSh
        unfold rssSlhInteractiveProtocol rssSlhCoinProtocol Sim_RssSlh slhIdealSignOracle
          sharedCoinTossBarrier committedCoin BlackBoxUcSimulator.finalizeIdealCut
        dsimp only
        rw [← hCurEq, ← hCorrEq, hTapeSimEq]
        dsimp only [shifts]
        rw [hSW1, hSW2, hView]
        cases hVR1 : sharedVerifyRound1 cIdx _ _ with
        | inl p1 =>
          rcases p1 with ⟨r1Err, doPoison⟩
          cases doPoison
          · dsimp only
            exact ⟨rfl, rfl, rfl, ⟨hPkEq, hThEq, hNpEq, hCorrEq, hCheatEq, rfl, rfl, fun _ => hShares⟩⟩
          · dsimp only [poisonRealCluster, poisonIdealCluster, walQuarantine]
            exact ⟨rfl, rfl, rfl, ⟨hPkEq, hThEq, hNpEq, hCorrEq, hCheatEq, rfl, rfl, fun hp => by cases hp⟩⟩
        | inr r2Init =>
          dsimp only
          cases hBar : sharedPreCutBarrier cIdx deg cl.tsig.pk _ _ _ with
          | inl barrierErr =>
            dsimp only [poisonRealCluster, poisonIdealCluster, walQuarantine]
            exact ⟨rfl, rfl, rfl, ⟨hPkEq, hThEq, hNpEq, hCorrEq, hCheatEq, rfl, rfl, fun hp => by cases hp⟩⟩
          | inr r3Init =>
            obtain ⟨hExtEq, hBatchTrue, hSwLenEq⟩ :=
              sharedPreCutBarrier_extract_eq cIdx deg cl.tsig.pk _ _ _ r3Init hBar
            have hDeltasZero : r3Init.deltas.any (fun d => decide (d ≠ towerZero 7)) = false := by
              by_cases hAny : r3Init.deltas.any (fun d => decide (d ≠ towerZero 7)) = true
              · exfalso
                have hBadUnf := hNoBad
                unfold sessionBadHit extractSessionNonzeroDeltas rssSlhCoinProtocol committedCoin at hBadUnf
                dsimp only at hBadUnf
                rw [hQuorum] at hBadUnf
                simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hBadUnf
                rw [hWalStep] at hBadUnf
                dsimp only at hBadUnf
                rw [hVR1] at hBadUnf
                dsimp only at hBadUnf hExtEq hBatchTrue
                simp only [hView] at hBadUnf
                rw [hExtEq, hAny] at hBadUnf
                simp only [↓reduceIte, Option.map_some] at hBadUnf
                rw [hBatchTrue] at hBadUnf
                cases hBadUnf
              · exact Bool.eq_false_iff.mpr hAny
            have hSentEqExp : r3Init.sentWires = r3Init.expectedWires :=
              eq_of_zipXorTower_any_false 7 hSwLenEq hDeltasZero
            dsimp only
            rw [hShares]
            have hQuorumV := extractHonestQuorumViews_deal p.sigBytes cIdx seedSh prfSh req
            dsimp only at hQuorumV
            rw [hQuorumV]
            dsimp only
            let q := (honestPairForCorrupt cIdx).2.2
            have hPkSeedEq : cl.tsig.pk.pkSeed = pkSeed := by
              rw [hPkKey]; rfl
            have hTrueSigEq :
                rssQuorumSlhSignBytes p q (q.views seedSh) (q.views prfSh) cl.tsig.pk.pkSeed
                  (expandPairwiseSeedTape tapeReal.prgSeeds)
                  (A.scheduleSession advSt).1.msg (A.scheduleSession advSt).1.optRand =
                encodeSlhSig (slhSignInternal p (A.scheduleSession advSt).1.msg sk (A.scheduleSession advSt).1.optRand) := by
              rw [hPkSeedEq]
              exact (rss_threshold_sig_independent_of_quorum_and_sharing p hWf q q
                hSeedWf hPrfWf hSeedWf hPrfWf rfl rfl pkSeed
                (expandPairwiseSeedTape tapeReal.prgSeeds) (expandPairwiseSeedTape tapeReal.prgSeeds)
                (A.scheduleSession advSt).1.msg (A.scheduleSession advSt).1.optRand).1
            have hCrossZero :
                evalReplicatedGateCrossByte (q.views seedSh).1.1 r3Init.sentWires r3Init.expectedWires = 0 := by
              rw [hSentEqExp]
              exact evalReplicatedGateCrossByte_self _ _
            have hPreCutEq :
                xorByteStream
                  (rssQuorumSlhSignBytes p q (q.views seedSh) (q.views prfSh) cl.tsig.pk.pkSeed
                    (expandPairwiseSeedTape tapeReal.prgSeeds)
                    (A.scheduleSession advSt).1.msg (A.scheduleSession advSt).1.optRand)
                  (evalReplicatedGateCrossByte (q.views seedSh).1.1 r3Init.sentWires r3Init.expectedWires ::
                    List.replicate (p.sigBytes - 1) 0) =
                encodeSlhSig (slhSignInternal p (A.scheduleSession advSt).1.msg sk (A.scheduleSession advSt).1.optRand) := by
              rw [hCrossZero, hTrueSigEq]
              exact xorByteStream_zero_head_replicate
                (encodeSlhSig_slhSignInternal_length p
                  (A.scheduleSession advSt).1.msg sk (A.scheduleSession advSt).1.optRand)
            rw [hPreCutEq, unpackWireBytes_packWireBytes]
            cases hFin : sharedFinalizeCutOpen p cIdx cl.tsig.pk _ _ _ with
            | inl cutErr =>
              dsimp only [poisonRealCluster, poisonIdealCluster, walQuarantine]
              exact ⟨rfl, rfl, rfl, ⟨rfl, hThEq, hNpEq, rfl, hCheatEq, rfl, rfl, fun hp => by cases hp⟩⟩
            | inr outSigBytes =>
              have hOut := sharedFinalizeCutOpen_output p cIdx cl.tsig.pk _ _ _ outSigBytes hFin
              rw [reconstructRssBytes_masked_eq
                ((encodeSlhSig_slhSignInternal_length p _ sk _).trans
                  (bvToFixedBytes_length p.sigBytes _).symm)
                ((bvToFixedBytes_length p.sigBytes _).trans
                  (bvToFixedBytes_length p.sigBytes _).symm)] at hOut
              subst outSigBytes
              dsimp only
              exact ⟨rfl, rfl, rfl, ⟨rfl, hThEq, hNpEq, rfl, hCheatEq, rfl, rfl, fun _ => rfl⟩⟩

/-- Multi-session adaptive XOR bijection over `Fin (rssMultiSessionCard p.sigBytes s)` built via
    `depProdFinEquiv`: session `0` shifts by `(cl, advSt)`, and sessions `1..s-1` shift by the
    adaptive successor state `(cl1, advSt1)` induced by `cur`! -/
def multiSessionTapeEquiv {AdvState : Type}
    (p : Fips205Params) (cIdx : Fin 3) (deg : Nat)
    (A : UcRushingAdversary AdvState) :
    (s : Nat) →
    RealClusterState SlhPublicKey RssPartyKeyShare →
    AdvState →
    SimpleEquiv (Fin (rssMultiSessionCard p.sigBytes s)) (Fin (rssMultiSessionCard p.sigBytes s))
  | 0, _, _ => idFinEquiv 1
  | s + 1, cl, advSt =>
    depProdFinEquiv (rssMultiSessionCard_pos p.sigBytes s)
      (adaptiveSingleSessionEquiv p cIdx A cl advSt)
      (fun cur =>
        let (cl1, advSt1, _) :=
          execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt
            (decodeSingleFullTape p.sigBytes cur)
        multiSessionTapeEquiv p cIdx deg A s cl1 advSt1)

/-- Multi-session root-hit indicator across all `s` scheduled sessions of
    `rssSlhCoinProtocol commitCoins`: some session's joint coin is a root of that session's
    non-zero wire deviation. -/
def multiSessionBadHit {AdvState : Type} (commitCoins : Bool)
    (p : Fips205Params) (cIdx : Fin 3) (deg : Nat)
    (A : UcRushingAdversary AdvState) :
    (s : Nat) →
    RealClusterState SlhPublicKey RssPartyKeyShare →
    AdvState →
    Fin (rssMultiSessionCard p.sigBytes s) → Bool
  | 0, _, _, _ => false
  | s + 1, cl, advSt, ω =>
    let cur := splitFinLeft (rssMultiSessionCard_pos p.sigBytes s) ω
    let rest := splitFinRight (rssMultiSessionCard_pos p.sigBytes s) ω
    let (cl1, advSt1, _) :=
      execRealSession (rssSlhCoinProtocol commitCoins p cIdx deg) A cl advSt
        (decodeSingleFullTape p.sigBytes cur)
    sessionBadHit commitCoins p cIdx deg A cl advSt cur ||
      multiSessionBadHit commitCoins p cIdx deg A s cl1 advSt1 rest

private theorem multiSessionBadHit_pairFin {AdvState : Type} (commitCoins : Bool)
    (p : Fips205Params) (cIdx : Fin 3) (deg : Nat)
    (A : UcRushingAdversary AdvState) (s : Nat)
    (cl : RealClusterState SlhPublicKey RssPartyKeyShare) (advSt : AdvState)
    (cur : Fin (rssFullSessionCard p.sigBytes))
    (rest : Fin (rssMultiSessionCard p.sigBytes s)) :
    multiSessionBadHit commitCoins p cIdx deg A (s + 1) cl advSt (pairFin cur rest) =
    (sessionBadHit commitCoins p cIdx deg A cl advSt cur ||
      let next := execRealSession (rssSlhCoinProtocol commitCoins p cIdx deg) A cl advSt
                    (decodeSingleFullTape p.sigBytes cur)
      multiSessionBadHit commitCoins p cIdx deg A s next.1 next.2.1 rest) := by
  simp only [multiSessionBadHit, splitFinLeft_pairFin, splitFinRight_pairFin]

/-- **Multi-Session Schwartz-Zippel Root-Hit Bound, commitment-decoy game
    (`multiSessionBadHit_qsum_bound`)**:
    Across any `Q_s` adaptively scheduled rushing sessions of `rssSlhCoinProtocol false` (honest
    Round-1 commitments carry the zero coin), the total number of random tapes `ω`
    hitting `multiSessionBadHit false = true` satisfies:
    `badCount * (2 ^ 128) ≤ (Q_s * deg) * rssMultiSessionCard p.sigBytes Q_s`! -/
theorem multiSessionBadHit_qsum_bound {AdvState : Type}
    (p : Fips205Params) (cIdx : Fin 3) (deg : Nat)
    (A : UcRushingAdversary AdvState) :
    ∀ (s : Nat) (cl : RealClusterState SlhPublicKey RssPartyKeyShare) (advSt : AdvState),
      qsum (rssMultiSessionCard p.sigBytes s)
        (fun ω => if multiSessionBadHit false p cIdx deg A s cl advSt ω then 1 else 0) * (2 ^ 128) ≤
      (s * deg) * rssMultiSessionCard p.sigBytes s
  | 0, _, _ => by simp [multiSessionBadHit, rssMultiSessionCard, qsum]
  | s + 1, cl, advSt => by
    let F := rssFullSessionCard p.sigBytes
    let M := rssMultiSessionCard p.sigBytes s
    change qsum (F * M) (fun ω => if multiSessionBadHit false p cIdx deg A (s + 1) cl advSt ω then 1 else 0) * (2 ^ 128) ≤
      ((s + 1) * deg) * (F * M)
    rw [qsum_prod_eq F M]
    have hSplitOr :
        qsum F (fun cur => qsum M (fun rest =>
          if multiSessionBadHit false p cIdx deg A (s + 1) cl advSt (pairFin cur rest) then 1 else 0)) ≤
        qsum F (fun cur => qsum M (fun _ =>
          if sessionBadHit false p cIdx deg A cl advSt cur then 1 else 0)) +
        qsum F (fun cur => qsum M (fun rest =>
          let (cl1, advSt1, _) :=
            execRealSession (rssSlhCoinProtocol false p cIdx deg) A cl advSt
              (decodeSingleFullTape p.sigBytes cur)
          if multiSessionBadHit false p cIdx deg A s cl1 advSt1 rest then 1 else 0)) := by
      apply qsum_le_add_qsum
      intro cur
      apply qsum_le_add_qsum
      intro rest
      rw [multiSessionBadHit_pairFin false p cIdx deg A s cl advSt cur rest]
      let b1 := sessionBadHit false p cIdx deg A cl advSt cur
      let next := execRealSession (rssSlhCoinProtocol false p cIdx deg) A cl advSt
                    (decodeSingleFullTape p.sigBytes cur)
      let b2 := multiSessionBadHit false p cIdx deg A s next.1 next.2.1 rest
      change (if (b1 || b2) = true then 1 else 0) ≤
             (if b1 = true then 1 else 0) + (if b2 = true then 1 else 0)
      cases b1 <;> cases b2 <;> decide
    have hMulSplit := Nat.mul_le_mul_right (2 ^ 128) hSplitOr
    rw [Nat.add_mul] at hMulSplit
    have hTerm1 :
        qsum F (fun cur => qsum M (fun _ =>
          if sessionBadHit false p cIdx deg A cl advSt cur then 1 else 0)) * (2 ^ 128) ≤
        deg * (F * M) := by
      have hConstM :
          qsum F (fun cur => qsum M (fun _ =>
            if sessionBadHit false p cIdx deg A cl advSt cur then 1 else 0)) =
          qsum F (fun cur => (if sessionBadHit false p cIdx deg A cl advSt cur then 1 else 0) * M) := by
        apply qsum_congr
        intro cur
        rw [qsum_const, Nat.mul_comm]
      rw [hConstM, qsum_mul_right_local]
      have hB1 := sessionBadHit_qsum_le p cIdx deg A cl advSt
      have hScaled := Nat.mul_le_mul_right (M * (2 ^ 128)) hB1
      have hL : qsum F (fun cur => if sessionBadHit false p cIdx deg A cl advSt cur then 1 else 0) * M * (2 ^ 128) =
          qsum F (fun cur => if sessionBadHit false p cIdx deg A cl advSt cur then 1 else 0) * (M * (2 ^ 128)) :=
        Nat.mul_assoc _ _ _
      have hR : rssPadSessionCard p.sigBytes * deg * (M * (2 ^ 128)) = deg * (F * M) := by
        dsimp only [F, rssFullSessionCard]
        ac_rfl
      rw [hL, ← hR]
      exact hScaled
    have hTerm2 :
        qsum F (fun cur => qsum M (fun rest =>
          let (cl1, advSt1, _) :=
            execRealSession (rssSlhCoinProtocol false p cIdx deg) A cl advSt
              (decodeSingleFullTape p.sigBytes cur)
          if multiSessionBadHit false p cIdx deg A s cl1 advSt1 rest then 1 else 0)) * (2 ^ 128) ≤
        (s * deg) * (F * M) := by
      rw [← qsum_mul_right_local]
      have hCap : qsum F (fun _ => (s * deg) * M) = F * ((s * deg) * M) := qsum_const F _
      have hLeCap :
          qsum F (fun cur => qsum M (fun rest =>
            let (cl1, advSt1, _) :=
              execRealSession (rssSlhCoinProtocol false p cIdx deg) A cl advSt
                (decodeSingleFullTape p.sigBytes cur)
            if multiSessionBadHit false p cIdx deg A s cl1 advSt1 rest then 1 else 0) * (2 ^ 128)) ≤
          qsum F (fun _ => (s * deg) * M) := by
        apply qsum_le_qsum
        intro cur
        exact multiSessionBadHit_qsum_bound p cIdx deg A s _ _
      have hR : F * ((s * deg) * M) = (s * deg) * (F * M) := by ac_rfl
      exact Nat.le_trans hLeCap (hCap ▸ hR ▸ Nat.le_refl _)
    have hSum := Nat.add_le_add hTerm1 hTerm2
    have hRhs : deg * (F * M) + (s * deg) * (F * M) = ((s + 1) * deg) * (F * M) := by
      rw [Nat.succ_mul, Nat.add_comm (s * deg) deg, Nat.add_mul]
    exact Nat.le_trans hMulSplit (hRhs ▸ hSum)

/-- **Whole-Transcript Multi-Session Lockstep Equivalence (`multiSession_real_eq_ideal_unless_bad`)**:
    Across ANY `Q_s` adaptively scheduled sessions, whenever `multiSessionBadHit ... ω = false`,
    `RealProtocolExec` on `ω` and `IdealFunctionalityExec` (`IdealTsig` + `Sim_RssSlh`) on
    `(multiSessionTapeEquiv ...).toFun ω` emit the **EXACT SAME `ExecTranscript AdvState`**! -/
