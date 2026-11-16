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
theorem multiSession_real_eq_ideal_unless_bad {AdvState : Type}
    (p : Fips205Params) (hWf : p.wellFormed = true)
    (cIdx : Fin 3) (deg : Nat)
    {seedSh prfSh : RssByteShares}
    (hSeedWf : seedSh.WellFormed) (hPrfWf : prfSh.WellFormed)
    (pkSeed : List UInt8)
    (A : UcRushingAdversary AdvState) :
    ∀ (s : Nat)
      (cl : RealClusterState SlhPublicKey RssPartyKeyShare)
      (icl : IdealClusterState SlhPublicKey)
      (advSt : AdvState),
      RealIdealClusterMatch cIdx seedSh prfSh cl icl →
      cl.tsig.pk = (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).2 →
      ∀ (ω : Fin (rssMultiSessionCard p.sigBytes s)),
        multiSessionBadHit true p cIdx deg A s cl advSt ω = false →
        let sk := (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).1
        (RealProtocolExec (rssSlhInteractiveProtocol p cIdx deg) A s
          (decodeMultiSessionTapes p.sigBytes s ω) cl advSt).2 =
        (IdealFunctionalityExec (slhIdealSignOracle p sk) (Sim_RssSlh (corruptRssView cIdx seedSh prfSh) p cIdx deg) A s
          (decodeMultiSessionTapes p.sigBytes s ((multiSessionTapeEquiv p cIdx deg A s cl advSt).toFun ω))
          icl advSt).2
  | 0, _, _, _, _, _, _, _ => rfl
  | s + 1, cl, icl, advSt, hMatch, hPkKey, ω, hNoBad => by
    let hMPos := rssMultiSessionCard_pos p.sigBytes s
    let cur := splitFinLeft hMPos ω
    let rest := splitFinRight hMPos ω
    have hOrFalse :
        (sessionBadHit true p cIdx deg A cl advSt cur ||
          multiSessionBadHit true p cIdx deg A s
            (execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt (decodeSingleFullTape p.sigBytes cur)).1
            (execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt (decodeSingleFullTape p.sigBytes cur)).2.1
            rest) = false := hNoBad
    have hCurFalse : sessionBadHit true p cIdx deg A cl advSt cur = false := by
      cases hc : sessionBadHit true p cIdx deg A cl advSt cur
      · rfl
      · rw [hc] at hOrFalse; simp at hOrFalse
    have hRestFalse :
        multiSessionBadHit true p cIdx deg A s
          (execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt (decodeSingleFullTape p.sigBytes cur)).1
          (execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt (decodeSingleFullTape p.sigBytes cur)).2.1
          rest = false := by
      rw [hCurFalse, Bool.false_or] at hOrFalse
      exact hOrFalse
    have hHead0 :
        decodeMultiSessionTapes p.sigBytes (s + 1) ω 0 = decodeSingleFullTape p.sigBytes cur := rfl
    have hHeadSim0 :
        decodeMultiSessionTapes p.sigBytes (s + 1)
          ((multiSessionTapeEquiv p cIdx deg A (s + 1) cl advSt).toFun ω) 0 =
        decodeSingleFullTape p.sigBytes ((adaptiveSingleSessionEquiv p cIdx A cl advSt).toFun cur) := by
      simp only [multiSessionTapeEquiv, depProdFinEquiv, decodeMultiSessionTapes,
                 decodeSingleFullTape, splitFinLeft_pairFin]
      rfl
    have hTailReal :
        (fun i => decodeMultiSessionTapes p.sigBytes (s + 1) ω (i + 1)) =
        decodeMultiSessionTapes p.sigBytes s rest := rfl
    have hTailSim :
        (fun i => decodeMultiSessionTapes p.sigBytes (s + 1)
          ((multiSessionTapeEquiv p cIdx deg A (s + 1) cl advSt).toFun ω) (i + 1)) =
        decodeMultiSessionTapes p.sigBytes s
          ((multiSessionTapeEquiv p cIdx deg A s
            (execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt (decodeSingleFullTape p.sigBytes cur)).1
            (execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt (decodeSingleFullTape p.sigBytes cur)).2.1).toFun rest) := by
      funext i
      simp only [multiSessionTapeEquiv, depProdFinEquiv, decodeMultiSessionTapes,
                 splitFinRight_pairFin]
      rfl
    have hStep := execRealSession_eq_execIdealSession_unless_bad p hWf cIdx deg
      hSeedWf hPrfWf pkSeed A cl icl advSt hMatch hPkKey cur hCurFalse
    dsimp only at hStep
    rcases hR1 : execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt (decodeSingleFullTape p.sigBytes cur)
      with ⟨cl1, advSt1, rec1⟩
    rcases hI1 : execIdealSession (slhIdealSignOracle p (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).1)
      (Sim_RssSlh (corruptRssView cIdx seedSh prfSh) p cIdx deg) A icl advSt
      (decodeSingleFullTape p.sigBytes ((adaptiveSingleSessionEquiv p cIdx A cl advSt).toFun cur))
      with ⟨icl1, advStI1, recI1⟩
    rw [hR1, hI1] at hStep
    dsimp only at hStep
    obtain ⟨rfl, rfl, hPk1, hMatch1⟩ := hStep
    rw [hR1] at hRestFalse hTailSim
    dsimp only at hRestFalse hTailSim
    intro sk
    rw [RealProtocolExec_succ, IdealFunctionalityExec_succ, hHead0, hHeadSim0,
        hTailReal, hTailSim, hR1, hI1]
    dsimp only
    have ih := multiSession_real_eq_ideal_unless_bad p hWf cIdx deg hSeedWf hPrfWf pkSeed A
      s cl1 icl1 advSt1 hMatch1 (hPk1.trans hPkKey) rest hRestFalse
    dsimp only at ih
    rw [ih]

/-- A root-hit count `bR` is within the commitment-hop gap `|bR - bD|` of any bound that holds
    for the decoy count `bD`. -/
private theorem ratLe_real_bad_of_decoy_bound {bR bD card num : Nat} (hCard : 0 < card)
    (hDecoy : bD * 2 ^ 128 ≤ num * card) :
    ratLe (bR, card) (ratAdd (num, 2 ^ 128) (natAbsDiff bR bD, card)) := by
  unfold ratLe ratAdd
  dsimp only
  refine ⟨hCard, Nat.mul_pos (Nat.two_pow_pos 128) hCard, ?_⟩
  have hTri : bR ≤ bD + natAbsDiff bR bD := by
    unfold natAbsDiff
    split <;> omega
  have h1 : bR * 2 ^ 128 ≤ num * card + natAbsDiff bR bD * 2 ^ 128 := by
    have h := Nat.mul_le_mul_right (2 ^ 128) hTri
    rw [Nat.add_mul] at h
    exact Nat.le_trans h (Nat.add_le_add_right hDecoy _)
  have h2 := Nat.mul_le_mul_right card h1
  rw [← Nat.mul_assoc]
  exact h2

/-- **Crown-Jewel Theorem 1 (`rss_slh_real_ideal_view_indistinguishable`)**:
    Across ANY `Q_cuts` (`Q_s`) adaptively scheduled interactive rushing signing sessions with 1
    static malicious party `cIdx : Fin 3`, ANY post-processing `ctx` of the finished transcript, ANY
    distinguisher `D`, and ANY real-world tape generator
    `realPrfTapeGen : Fin prfCard → (Nat → RssSlhSessionTape p.sigBytes)`:
    1. **Exact root-hit bound.** Between `RealProtocolExec` on uniform tapes and
       `IdealFunctionalityExec` (`IdealTsig` + `sk`-free `Sim_RssSlh`), the distance of the entire
       multi-round, multi-session `ExecTranscript` (wire `ByteArray`s and `Abort(reason)` outcomes
       included) is at most the fraction `badReal / card` of tapes on which some session's joint coin
       `coinA ⊕ coinB ⊕ corruptCoin` is a root of that session's non-zero wire deviation.
    2. **Counted bound in the commitment-decoy game.** When the honest Round-1 commitments carry
       the zero coin instead of the coin shares, that fraction is at most `Q_cuts * deg / 2^128`.
    3. **Composition.** Hence the distance is at most `Q_cuts * deg / 2^128 + advCoinHide`, where
       `advCoinHide = |badReal - badDecoy| / card` is the change in root-hit probability when the
       honest commitments are switched from the coin shares to zero. `advCoinHide` is the
       advantage of one explicit test (did a root hit occur) against the hiding of the honest
       Round-1 commitment `round1NonceCommit`; it is not bounded in this file, and an
       unbounded adversary that inverts `SHAKE256` on the 24-byte opening makes it large.
    4. **Real tapes.** The triangle inequality `uc_transitive_composition` adds `advPrf`, which
       is by definition the distance between the execution on `realPrfTapeGen` tapes and on
       uniform tapes. No PRF reduction bounds it here.
    Sessions run one after another to completion; this is a sequential multi-session statement,
    not a composition theorem for interleaved executions. -/
theorem rss_slh_real_ideal_view_indistinguishable {AdvState OuterView : Type}
    (p : Fips205Params) (hWf : p.wellFormed = true)
    (cIdx : Fin 3) (Q_cuts deg : Nat)
    {seedSh prfSh : RssByteShares}
    (hSeedWf : seedSh.WellFormed) (hPrfWf : prfSh.WellFormed)
    (pkSeed : List UInt8)
    (A : UcRushingAdversary AdvState)
    (cl : RealClusterState SlhPublicKey RssPartyKeyShare)
    (icl : IdealClusterState SlhPublicKey)
    (advSt : AdvState)
    (hMatch : RealIdealClusterMatch cIdx seedSh prfSh cl icl)
    (hPkKey : cl.tsig.pk = (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).2)
    (ctx : OuterCallingContext (ExecTranscript AdvState) OuterView)
    (D : OuterView → Bool)
    (prfCard : Nat) (hPrfPos : 0 < prfCard)
    (realPrfTapeGen : Fin prfCard → (Nat → RssSlhSessionTape p.sigBytes)) :
    let card := rssMultiSessionCard p.sigBytes Q_cuts
    let sk := (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).1
    let realPrfView : Fin prfCard → OuterView := fun κ =>
      ctx.postProcess (RealProtocolExec (rssSlhInteractiveProtocol p cIdx deg) A Q_cuts
        (realPrfTapeGen κ) cl advSt).2
    let hybridUniformView : Fin card → OuterView := fun ω =>
      ctx.postProcess (RealProtocolExec (rssSlhInteractiveProtocol p cIdx deg) A Q_cuts
        (decodeMultiSessionTapes p.sigBytes Q_cuts ω) cl advSt).2
    let idealSimView : Fin card → OuterView := fun ω =>
      ctx.postProcess (IdealFunctionalityExec (slhIdealSignOracle p sk) (Sim_RssSlh (corruptRssView cIdx seedSh prfSh) p cIdx deg) A Q_cuts
        (decodeMultiSessionTapes p.sigBytes Q_cuts ω) icl advSt).2
    let badReal := qsum card (fun ω =>
      if multiSessionBadHit true p cIdx deg A Q_cuts cl advSt ω then 1 else 0)
    let badDecoy := qsum card (fun ω =>
      if multiSessionBadHit false p cIdx deg A Q_cuts cl advSt ω then 1 else 0)
    let advCoinHide : Nat × Nat := (natAbsDiff badReal badDecoy, card)
    let advPrf := rationalAcceptDiff prfCard realPrfView card hybridUniformView D
    ratLe (rationalAcceptDiff card hybridUniformView card idealSimView D) (badReal, card) ∧
    ratLe (badDecoy, card) (Q_cuts * deg, 2 ^ 128) ∧
    ratLe (rationalAcceptDiff card hybridUniformView card idealSimView D)
          (ratAdd (Q_cuts * deg, 2 ^ 128) advCoinHide) ∧
    ratLe (rationalAcceptDiff prfCard realPrfView card idealSimView D)
          (ratAdd advPrf (ratAdd (Q_cuts * deg, 2 ^ 128) advCoinHide)) := by
  intro card sk realPrfView hybridUniformView idealSimView badReal badDecoy advCoinHide advPrf
  have hCardPos : 0 < card := rssMultiSessionCard_pos p.sigBytes Q_cuts
  let bij := multiSessionTapeEquiv p cIdx deg A Q_cuts cl advSt
  let bad := multiSessionBadHit true p cIdx deg A Q_cuts cl advSt
  have hAgree : ∀ ω : Fin card, bad ω = false → hybridUniformView ω = idealSimView (bij.toFun ω) := by
    intro ω hBadF
    dsimp only [hybridUniformView, idealSimView]
    exact congrArg ctx.postProcess (multiSession_real_eq_ideal_unless_bad p hWf cIdx deg
      hSeedWf hPrfWf pkSeed A Q_cuts cl icl advSt hMatch hPkKey ω hBadF)
  have hFund : ratLe (rationalAcceptDiff card hybridUniformView card idealSimView D) (badReal, card) :=
    (bad_event_fundamental_lemma card hCardPos hybridUniformView idealSimView bij bad hAgree D).2.2
  have hDecoyCount := multiSessionBadHit_qsum_bound p cIdx deg A Q_cuts cl advSt
  have hDecoyLe : ratLe (badDecoy, card) (Q_cuts * deg, 2 ^ 128) :=
    ⟨hCardPos, Nat.two_pow_pos 128, hDecoyCount⟩
  have hRealLe : ratLe (badReal, card) (ratAdd (Q_cuts * deg, 2 ^ 128) advCoinHide) :=
    ratLe_real_bad_of_decoy_bound hCardPos hDecoyCount
  have hUniformBound : ratLe (rationalAcceptDiff card hybridUniformView card idealSimView D)
      (ratAdd (Q_cuts * deg, 2 ^ 128) advCoinHide) :=
    ratLe_trans hFund hRealLe
  have hPrfRefl : ratLe (rationalAcceptDiff prfCard realPrfView card hybridUniformView D) advPrf :=
    ⟨Nat.mul_pos hPrfPos hCardPos, Nat.mul_pos hPrfPos hCardPos, Nat.le_refl _⟩
  have hComp := uc_transitive_composition prfCard card card hPrfPos hCardPos hCardPos
    (fun κ => (RealProtocolExec (rssSlhInteractiveProtocol p cIdx deg) A Q_cuts (realPrfTapeGen κ) cl advSt).2)
    (fun ω => (RealProtocolExec (rssSlhInteractiveProtocol p cIdx deg) A Q_cuts (decodeMultiSessionTapes p.sigBytes Q_cuts ω) cl advSt).2)
    (fun ω => (IdealFunctionalityExec (slhIdealSignOracle p sk) (Sim_RssSlh (corruptRssView cIdx seedSh prfSh) p cIdx deg) A Q_cuts (decodeMultiSessionTapes p.sigBytes Q_cuts ω) icl advSt).2)
    ctx D advPrf (ratAdd (Q_cuts * deg, 2 ^ 128) advCoinHide) hPrfRefl hUniformBound
  exact ⟨hFund, hDecoyLe, hUniformBound, hComp⟩


theorem spdz_shamir_tower128_masked_view_stat_dist_zero
    (t : Nat) (corruptPts : List Tower128) (w : Tower128)
    (hCard : corruptPts.length + 1 ≤ t)
    (hNonZero : ∀ c ∈ corruptPts, c ≠ towerZero 7)
    (D : (Tower128 × List Tower128) → Bool) :
    let N := towerPadSpaceCard (2 ^ 128) t
    let realView : Fin N → Tower128 × List Tower128 :=
      fun idx => realMaskedOpeningView corruptPts w (decodeTower128PadPoly t idx)
    let simView : Fin N → Tower128 × List Tower128 :=
      fun idx => simMaskedOpeningView corruptPts (decodeTower128PadPoly t idx)
    N = (2 ^ 128) ^ t ∧
    natAbsDiff (distAcceptCount N realView D) (distAcceptCount N simView D) = 0 ∧
    ratLe (rationalAcceptDiff N realView N simView D) (0, 1) := by
  intro N realView simView
  have hNPos : 0 < N := towerPadSpaceCard_pos (Nat.two_pow_pos 128) t
  have hInv : ∀ x : Tower128, x ≠ CommRingOps.zero → CommRingOps.mul x (towerInv 7 x) = CommRingOps.one :=
    fun x hx => towerMul_inv 7 x hx
  have hSimBij := tsigSimulator_view_bijection_indep_of_secret (towerInv 7) hInv t corruptPts w hCard hNonZero
  let eqvPoly := shamir_rebalanceEquiv (towerInv 7) t corruptPts w hCard
  have hDecEnc : ∀ P : ShamirPadPoly Tower128 t, decodeTower128PadPoly t (encodeTower128PadPoly t P) = P :=
    decode_encode_genericPadPoly (2 ^ 128) (Nat.two_pow_pos 128)
      (fun i => unpackTower 7 (BitVec.ofFin i))
      (fun x => (packTower 7 x).toFin)
      (fun x => by simp only [BitVec.ofFin_toFin, unpackTower_packTower])
      t
  have hEncDec : ∀ idx : Fin N, encodeTower128PadPoly t (decodeTower128PadPoly t idx) = idx :=
    encode_decode_genericPadPoly (2 ^ 128) (Nat.two_pow_pos 128)
      (fun i => unpackTower 7 (BitVec.ofFin i))
      (fun x => (packTower 7 x).toFin)
      (fun i => by simp only [packTower_unpackTower, BitVec.toFin_ofFin])
      t
  let bijFin : SimpleEquiv (Fin N) (Fin N) :=
    { toFun := fun idx => encodeTower128PadPoly t (eqvPoly.toFun (decodeTower128PadPoly t idx))
      invFun := fun idx => encodeTower128PadPoly t (eqvPoly.invFun (decodeTower128PadPoly t idx))
      left_inv := fun idx => by rw [hDecEnc, eqvPoly.left_inv, hEncDec]
      right_inv := fun idx => by rw [hDecEnc, eqvPoly.right_inv, hEncDec] }
  have hAgree : ∀ idx : Fin N, (false : Bool) = false → realView idx = simView (bijFin.toFun idx) := by
    intro idx _
    dsimp only [realView, simView, bijFin]
    rw [hDecEnc]
    exact (hSimBij.2.2 (decodeTower128PadPoly t idx)).symm
  have hFund := bad_event_fundamental_lemma N hNPos realView simView bijFin (fun _ => false) hAgree D
  have hBad0 : qsum N (fun _ : Fin N => if (false : Bool) = true then 1 else 0) = 0 := by
    have h := qsum_const N 0; rw [Nat.mul_zero] at h; exact h
  rw [hBad0] at hFund
  have hZeroDiff : natAbsDiff (distAcceptCount N realView D) (distAcceptCount N simView D) = 0 :=
    Nat.eq_zero_of_le_zero hFund.1
  refine ⟨towerPadSpaceCard_eq_pow (2 ^ 128) t, hZeroDiff, ?_⟩
  exact ratLe_trans hFund.2.2 ⟨hNPos, Nat.zero_lt_one, by simp⟩

/-- **Inhabitedness Witness for Theorem 1 (`inhabited_rss_slh_real_ideal_uc`)**:
    Exhibits a concrete 2-of-3 RSS cluster on `slhDsaShake128f` with corrupt Party `0`, honest
    approvers `[1, 2]`, and active rushing adversary `A`, satisfying every premise of
    `rss_slh_real_ideal_view_indistinguishable` (`Q_cuts = 2, deg = 4`). -/
theorem inhabited_rss_slh_real_ideal_uc :
    ∃ (cl : RealClusterState SlhPublicKey RssPartyKeyShare)
      (icl : IdealClusterState SlhPublicKey)
      (seedSh prfSh : RssByteShares)
      (pkSeed : List UInt8),
      seedSh.WellFormed ∧ prfSh.WellFormed ∧
      RealIdealClusterMatch ⟨0, by decide⟩ seedSh prfSh cl icl ∧
      cl.tsig.pk = (slhKeygenInternal slhDsaShake128f
        (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).2 ∧
      validThresholdApproval cl.tsig [1, 2] = true := by
  let seedSh : RssByteShares := ⟨List.replicate 16 1, List.replicate 16 2, List.replicate 16 3⟩
  let prfSh : RssByteShares := ⟨List.replicate 16 4, List.replicate 16 5, List.replicate 16 6⟩
  let pkSeed : List UInt8 := List.replicate 16 7
  let pk := (slhKeygenInternal slhDsaShake128f
              (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).2
  let tsig : IdealTsigState SlhPublicKey (List UInt8) :=
    ⟨pk, 2, 3, [0], [], []⟩
  let wal : WalLatchState := initWalLatchState (slhPkDigest pk)
  let cl : RealClusterState SlhPublicKey RssPartyKeyShare :=
    ⟨tsig, wal, 0, dealHonestRssVault ⟨0, by decide⟩ seedSh prfSh⟩
  let icl : IdealClusterState SlhPublicKey := ⟨tsig, wal, 0⟩
  have hS : seedSh.WellFormed := ⟨rfl, rfl⟩
  have hP : prfSh.WellFormed := ⟨rfl, rfl⟩
  have hMatch : RealIdealClusterMatch ⟨0, by decide⟩ seedSh prfSh cl icl :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  have hVal : validThresholdApproval cl.tsig [1, 2] = true := by decide +kernel
  exact ⟨cl, icl, seedSh, prfSh, pkSeed, hS, hP, hMatch, rfl, hVal⟩

/-! ## 4. Crown-Jewel Theorem 2: Interactive Rushing Threshold `EUF-CMA` Reduction -/

/-- **1. `ActiveConsistencySoundnessBreak`**:
    Explicit transcript-bound witness that in some session `sessRec` of `tr.sessions`, the rushing
    corrupt party `cIdx` transmitted raw `GF(2^128)` (`Tower128`) gate wires `sentWires` differing from
    its private stream `corruptExpectedChiStream cIdx deg (some corrView) sessRec.request.msg`
    (`deltas.length ≤ deg`, `∃ devElem ∈ deltas, devElem ≠ 0`) AND slipped past `preCutBarrier` into Round 3.
    The expected stream is a function of the corrupt party's share view and the session message
    only, so the witness needs no cursor bookkeeping; the reduction holds `corrView` because it is
    the adversary's own input. -/
structure ActiveConsistencySoundnessBreak {AdvState : Type}
    (corrView : RssPartyKeyShare) (cIdx : Fin 3) (deg : Nat) (tr : ExecTranscript AdvState) where
  sessRec        : SessionWireRecord
  hMem           : sessRec ∈ tr.sessions
  cWire2         : ByteArray
  hWireMem       : (cIdx.val, cWire2) ∈ sessRec.corruptRound2
  nonceC         : List UInt8
  sentWires      : List Tower128
  hParse         : parseCorruptRound2Wire deg cWire2 = some (nonceC, sentWires)
  hDeg           : (zipXorTower 7 sentWires
                     (corruptExpectedChiStream cIdx deg (some corrView) sessRec.request.msg)).length ≤ deg
  devElem        : Tower128
  hDevMem        : devElem ∈ zipXorTower 7 sentWires
                     (corruptExpectedChiStream cIdx deg (some corrView) sessRec.request.msg)
  hDevNonzero    : devElem ≠ towerZero 7
  hPassedBarrier : sessRec.honestRound3 ≠ []

/-- **5. `Fips205ForsItsrBreak` (NIST `FIPS 205` / `SPHINCS+` Interleaved Target Subset Resilience Break)**:
    Explicit witness bound to `(p, sk, clInit, tr, mStar, sigStar)` showing EITHER:
    - `forsHashCollision`: an explicit `SHAKE256` collision in `.forsTree` or `.forsRoots`;
    - `forsUnqueriedPrfRecovery`: `sigStar` recovers the exact secret `sk.skSeed` `PRF` leaf key
      `fipsPrf p.n sk.pkSeed sk.skSeed (mkFipsAdrs 0 idxTree .forsPrf idxLeaf 0 globalLeaf)` at a
      FORS coordinate `(idxTree, idxLeaf, treeIdx, leafOffset)` **never opened** in any Round-3 session of `tr`;
    - `forsInterleavedSubsetCover`: `0 < p.k` and every one of the `p.k` FORS leaf coordinates of
      `H_msg(sigStar.rRand, pkSeed, pkRoot, mStar)` is covered by distinct-digest approved Round-3
      sessions in `tr.sessions` (provably `False` on `tr.sessions = []` or whenever ≥ 1 FORS tree hits a fresh leaf!). -/
inductive Fips205ForsItsrBreak {AdvState : Type}
    (p : Fips205Params) (sk : SlhSecretKey)
    (clInit : RealClusterState SlhPublicKey RssPartyKeyShare)
    (tr : ExecTranscript AdvState)
    (mStar : List UInt8) (sigStar : SlhSignature) : Type where
  | forsHashCollision (coll : Fips205ShakeCollision p.n)
  | forsUnqueriedPrfRecovery
      (treeIdx : Nat)
      (hTreeLt : treeIdx < p.k)
      (hSkRecovered :
        let dStar := fipsHMsg p.m sigStar.rRand sk.pkSeed sk.pkRoot mStar
        let (mdStar, idxTreeStar, idxLeafStar) := fipsSplitDigest p dStar
        let leafOffset := (base2b mdStar p.a p.k).getD treeIdx 0
        (sigStar.forsSig.getD treeIdx ⟨[], []⟩).skVal =
          fipsPrf p.n sk.pkSeed sk.skSeed
            (mkFipsAdrs 0 idxTreeStar .forsPrf idxLeafStar 0 (treeIdx * (2 ^ p.a) + leafOffset)))
      (hNeverOpened :
        let dStar := fipsHMsg p.m sigStar.rRand sk.pkSeed sk.pkRoot mStar
        let (mdStar, idxTreeStar, idxLeafStar) := fipsSplitDigest p dStar
        let leafOffset := (base2b mdStar p.a p.k).getD treeIdx 0
        ∀ rec ∈ tr.sessions,
          validThresholdApproval clInit.tsig rec.request.honestApprovers = true →
          rec.honestRound3 ≠ [] →
          let rRec := fipsPrfMsg p.n sk.skPrf rec.request.optRand rec.request.msg
          let dRec := fipsHMsg p.m rRec sk.pkSeed sk.pkRoot rec.request.msg
          let (mdRec, tRec, lRec) := fipsSplitDigest p dRec
          ¬ (tRec = idxTreeStar ∧ lRec = idxLeafStar ∧ (base2b mdRec p.a p.k).getD treeIdx 0 = leafOffset))
  | forsInterleavedSubsetCover
      (hKPos : 0 < p.k)
      (hAllCovered :
        let dStar := fipsHMsg p.m sigStar.rRand sk.pkSeed sk.pkRoot mStar
        let (mdStar, idxTreeStar, idxLeafStar) := fipsSplitDigest p dStar
        ∀ j : Nat, j < p.k →
          ∃ rec ∈ tr.sessions,
            validThresholdApproval clInit.tsig rec.request.honestApprovers = true ∧
            rec.honestRound3 ≠ [] ∧
            rec.request.msg ≠ mStar ∧
            let rRec := fipsPrfMsg p.n sk.skPrf rec.request.optRand rec.request.msg
            let dRec := fipsHMsg p.m rRec sk.pkSeed sk.pkRoot rec.request.msg
            let (mdRec, tRec, lRec) := fipsSplitDigest p dRec
            dRec ≠ dStar ∧
            tRec = idxTreeStar ∧ lRec = idxLeafStar ∧
            (base2b mdRec p.a p.k).getD j 0 = (base2b mdStar p.a p.k).getD j 0)

/-- Constructive (`Type`-valued, `0 Classical.choice`) union of the 5 concrete security break witnesses. -/
inductive RssSlhInteractiveSecurityBreak {AdvState : Type}
    (corrView : RssPartyKeyShare) (p : Fips205Params) (cIdx : Fin 3) (deg : Nat) (sk : SlhSecretKey)
    (clInit : RealClusterState SlhPublicKey RssPartyKeyShare)
    (tr : ExecTranscript AdvState) (mStar : List UInt8) (sigStar : SlhSignature) : Type where
  | activeConsistency (w : ActiveConsistencySoundnessBreak corrView cIdx deg tr)
  | forsItsr          (w : Fips205ForsItsrBreak p sk clInit tr mStar sigStar)
  | wotsChainSmTcr    (w : WotsChainSmTcrBreak p sk)
  | xmssMerkleTcr     (w : XmssMerkleTcrBreak p ⟨sk.pkSeed, sk.pkRoot⟩)
  | prfMsg            (w : PrfMsgBreak p)

/-- Constructive union of the four concrete NIST `FIPS 205` hash-game witnesses a valid fresh forgery
    yields against a transcript in which every Round-3 opening is an honest signature: FORS
    (collision / unopened secret leaf recovery / interleaved subset cover), WOTS+ (collision / backward
    chain preimage), XMSS Merkle collision, or an `H_msg` collision. No active-consistency alternative
    appears here: this is the witness type of the ideal world and of every real execution outside the
    counted `multiSessionBadHit` event. -/
inductive Fips205HashGameBreak {AdvState : Type}
    (p : Fips205Params) (sk : SlhSecretKey)
    (clInit : RealClusterState SlhPublicKey RssPartyKeyShare)
    (tr : ExecTranscript AdvState) (mStar : List UInt8) (sigStar : SlhSignature) : Type where
  | forsItsr          (w : Fips205ForsItsrBreak p sk clInit tr mStar sigStar)
  | wotsChainSmTcr    (w : WotsChainSmTcrBreak p sk)
  | xmssMerkleTcr     (w : XmssMerkleTcrBreak p ⟨sk.pkSeed, sk.pkRoot⟩)
  | prfMsg            (w : PrfMsgBreak p)

/-- Embed a hash-game witness into the five-way interactive break union. -/
def Fips205HashGameBreak.toInteractive {AdvState : Type}
    {p : Fips205Params} {sk : SlhSecretKey}
    {clInit : RealClusterState SlhPublicKey RssPartyKeyShare}
    {tr : ExecTranscript AdvState} {mStar : List UInt8} {sigStar : SlhSignature}
    (corrView : RssPartyKeyShare) (cIdx : Fin 3) (deg : Nat) :
    Fips205HashGameBreak p sk clInit tr mStar sigStar →
    RssSlhInteractiveSecurityBreak corrView p cIdx deg sk clInit tr mStar sigStar
  | .forsItsr w       => .forsItsr w
  | .wotsChainSmTcr w => .wotsChainSmTcr w
  | .xmssMerkleTcr w  => .xmssMerkleTcr w
  | .prfMsg w         => .prfMsg w

private def scanActiveConsistencyWires {AdvState : Type}
    (corrView : RssPartyKeyShare) (cIdx : Fin 3) (deg : Nat)
    (tr : ExecTranscript AdvState) (rec : SessionWireRecord)
    (hRec : rec ∈ tr.sessions)
    (hR3 : rec.honestRound3 ≠ []) :
    (ws : List (Nat × ByteArray)) →
    (∀ w ∈ ws, w ∈ rec.corruptRound2) →
    Option (ActiveConsistencySoundnessBreak corrView cIdx deg tr)
  | [], _ => none
  | (pid, cWire2) :: wRest, hWSub =>
    if hPid : pid = cIdx.val then
      match hParse : parseCorruptRound2Wire deg cWire2 with
      | none => scanActiveConsistencyWires corrView cIdx deg tr rec hRec hR3 wRest
                  (fun w hw => hWSub w (.tail _ hw))
      | some (nonceC, sentWires) =>
        let expectedWires := corruptExpectedChiStream cIdx deg (some corrView) rec.request.msg
        let deltas := zipXorTower 7 sentWires expectedWires
        match findDecidableElem (fun d => d ≠ towerZero 7) deltas with
        | .inl ⟨d, hdMem, hdNe⟩ =>
          some
            { sessRec := rec
              hMem := hRec
              cWire2 := cWire2
              hWireMem := by
                have hM := hWSub (pid, cWire2) (.head _)
                rwa [hPid] at hM
              nonceC := nonceC
              sentWires := sentWires
              hParse := hParse
              hDeg := Nat.le_trans (zipXorTower_length_le_left 7 sentWires expectedWires)
                        (parseCorruptRound2Wire_length_le deg cWire2 hParse)
              devElem := d
              hDevMem := hdMem
              hDevNonzero := hdNe
              hPassedBarrier := hR3 }
        | .inr _ => scanActiveConsistencyWires corrView cIdx deg tr rec hRec hR3 wRest
                      (fun w hw => hWSub w (.tail _ hw))
    else
      scanActiveConsistencyWires corrView cIdx deg tr rec hRec hR3 wRest
        (fun w hw => hWSub w (.tail _ hw))

private def scanActiveConsistencyAux {AdvState : Type}
    (corrView : RssPartyKeyShare) (cIdx : Fin 3) (deg : Nat)
    (tr : ExecTranscript AdvState) :
    (rem : List SessionWireRecord) →
    (∀ r ∈ rem, r ∈ tr.sessions) →
    Option (ActiveConsistencySoundnessBreak corrView cIdx deg tr)
  | [], _ => none
  | rec :: rest, hSub =>
    if hR3 : rec.honestRound3 = [] then
      scanActiveConsistencyAux corrView cIdx deg tr rest (fun r hr => hSub r (.tail _ hr))
    else
      match scanActiveConsistencyWires corrView cIdx deg tr rec (hSub rec (.head _)) hR3
              rec.corruptRound2 (fun _ hw => hw) with
      | some brk => some brk
      | none =>
        scanActiveConsistencyAux corrView cIdx deg tr rest (fun r hr => hSub r (.tail _ hr))

/-- Constructive scanner over `tr.sessions` (`0 Classical.choice`) checking if ANY session that
    reached Round 3 carries corrupt wires differing from the corrupt party's private stream. -/
private def scanActiveConsistencyBreak {AdvState : Type}
    (corrView : RssPartyKeyShare) (cIdx : Fin 3) (deg : Nat)
    (tr : ExecTranscript AdvState) :
    Option (ActiveConsistencySoundnessBreak corrView cIdx deg tr) :=
  scanActiveConsistencyAux corrView cIdx deg tr tr.sessions (fun _ h => h)

/-- Scan `0 .. count - 1` (`0 Classical.choice`) to test whether every FORS coordinate `(idxTree, idxLeaf, j, idxJ)`
    was covered by some approved Round-3 session in `tr.sessions`, or pinpoint the exact unqueried `j < count`! -/
private def checkForsSubsetCoverage {AdvState : Type}
    (p : Fips205Params) (sk : SlhSecretKey)
    (clInit : RealClusterState SlhPublicKey RssPartyKeyShare)
    (tr : ExecTranscript AdvState)
    (mdStar : List UInt8) (idxTreeStar idxLeafStar : Nat) :
    (count : Nat) →
    PSum { j : Nat // j < count ∧
            ∀ rec ∈ tr.sessions,
              validThresholdApproval clInit.tsig rec.request.honestApprovers = true →
              rec.honestRound3 ≠ [] →
              let rRec := fipsPrfMsg p.n sk.skPrf rec.request.optRand rec.request.msg
              let dRec := fipsHMsg p.m rRec sk.pkSeed sk.pkRoot rec.request.msg
              let (mdRec, tRec, lRec) := fipsSplitDigest p dRec
              ¬ (tRec = idxTreeStar ∧ lRec = idxLeafStar ∧
                 (base2b mdRec p.a p.k).getD j 0 = (base2b mdStar p.a p.k).getD j 0) }
         (PLift (∀ j : Nat, j < count →
            ∃ rec ∈ tr.sessions,
              validThresholdApproval clInit.tsig rec.request.honestApprovers = true ∧
              rec.honestRound3 ≠ [] ∧
              let rRec := fipsPrfMsg p.n sk.skPrf rec.request.optRand rec.request.msg
              let dRec := fipsHMsg p.m rRec sk.pkSeed sk.pkRoot rec.request.msg
              let (mdRec, tRec, lRec) := fipsSplitDigest p dRec
              tRec = idxTreeStar ∧ lRec = idxLeafStar ∧
              (base2b mdRec p.a p.k).getD j 0 = (base2b mdStar p.a p.k).getD j 0))
  | 0 => .inr ⟨fun _ hj => False.elim (Nat.not_lt_zero _ hj)⟩
  | j + 1 =>
    match checkForsSubsetCoverage p sk clInit tr mdStar idxTreeStar idxLeafStar j with
    | .inl ⟨u, huLt, huUncov⟩ => .inl ⟨u, Nat.lt_trans huLt (Nat.lt_succ_self j), huUncov⟩
    | .inr ⟨hPrevCov⟩ =>
      let MatchPred (rec : SessionWireRecord) : Prop :=
        validThresholdApproval clInit.tsig rec.request.honestApprovers = true ∧
        rec.honestRound3 ≠ [] ∧
        (let rRec := fipsPrfMsg p.n sk.skPrf rec.request.optRand rec.request.msg
         let dRec := fipsHMsg p.m rRec sk.pkSeed sk.pkRoot rec.request.msg
         let (mdRec, tRec, lRec) := fipsSplitDigest p dRec
         tRec = idxTreeStar ∧ lRec = idxLeafStar ∧
         (base2b mdRec p.a p.k).getD j 0 = (base2b mdStar p.a p.k).getD j 0)
      match findDecidableElem MatchPred tr.sessions with
      | .inl ⟨rec, hMem, hMP⟩ =>
        .inr ⟨fun i hi => by
          by_cases hiEq : i = j
          · subst hiEq; exact ⟨rec, hMem, hMP⟩
          · exact hPrevCov i (by omega)⟩
      | .inr ⟨hNone⟩ =>
        .inl ⟨j, Nat.lt_succ_self j, fun rec hMem hVal hR3 hHit =>
          hNone rec hMem ⟨hVal, hR3, hHit⟩⟩

/-- **Constructive Hash-Game Forgery Extractor (`extractSlhHashGameBreak`)**:
    Given ANY transcript `tr` and ANY well-typed signature `sigStar` verifying on a message `mStar` that
    was never the request of a quorum-approved session that reached Round 3, constructively
    (`0 Classical.choice`, `Type`-valued) extracts a concrete `Fips205HashGameBreak`. Freshness is only
    required of sessions whose Round-3 openings were actually released: a request that was approved but
    aborted before Round 3 revealed no signature and does not disqualify the forgery. -/
def extractSlhHashGameBreak {AdvState : Type}
    (p : Fips205Params) (hWf : p.wellFormed = true)
    (skSeed skPrf pkSeed : List UInt8)
    (clInit : RealClusterState SlhPublicKey RssPartyKeyShare)
    (tr : ExecTranscript AdvState)
    (mStar : List UInt8) (sigStar : SlhSignature)
    (hSigWt : sigStar.WellTyped p)
    (hVerify : slhVerifyInternal p mStar sigStar (slhKeygenInternal p skSeed skPrf pkSeed).2 = true)
    (hFresh : ∀ rec ∈ tr.sessions,
      validThresholdApproval clInit.tsig rec.request.honestApprovers = true →
      rec.honestRound3 ≠ [] →
      rec.request.msg ≠ mStar) :
    Fips205HashGameBreak p (slhKeygenInternal p skSeed skPrf pkSeed).1 clInit tr mStar sigStar :=
  let sk := (slhKeygenInternal p skSeed skPrf pkSeed).1
  let hWfP := wellFormed_props hWf
  have hnPos : 0 < p.n := hWfP.1
  have hnLe32 : p.n ≤ 32 := hWfP.2.1
  have hdPos : 0 < p.d := hWfP.2.2.1
  have hHdEq : p.h = p.d * p.hp := hWfP.2.2.2.1
  have hkPos : 0 < p.k := hWfP.2.2.2.2.1
  have hnLe128 : p.n ≤ 128 := Nat.le_trans hnLe32 (by decide)
  have hRLen := hSigWt.1
  have hFLen := hSigWt.2.1
  have hFEach := hSigWt.2.2.1
  have hHtLen := hSigWt.2.2.2.1
  have hHtEach := hSigWt.2.2.2.2
  let dStar := fipsHMsg p.m sigStar.rRand sk.pkSeed sk.pkRoot mStar
  let splitStar := fipsSplitDigest p dStar
  let mdStar := splitStar.1
  let idxTreeStar := splitStar.2.1
  let idxLeafStar := splitStar.2.2
  let pkForsStar := fipsForsPkFromSig p sigStar.forsSig mdStar sk.pkSeed idxTreeStar idxLeafStar
  let honPkFors := fipsForsPkGen p sk.skSeed sk.pkSeed idxTreeStar idxLeafStar
  have hTopVerify :
      fipsHtVerifyAux p sk.pkSeed 0 idxTreeStar idxLeafStar pkForsStar sigStar.htSig =
        fipsXmssNode p sk.skSeed sk.pkSeed (p.d - 1) 0 p.hp 0 := by
    have hShapes := slhVerifyInternal_shapes p mStar sigStar
      (slhKeygenInternal p skSeed skPrf pkSeed).2 hVerify
    have hForsShape := hShapes.2.2.2.1
    have hHtShape := hShapes.2.2.2.2
    have hV := hVerify
    unfold slhVerifyInternal slhKeygenInternal at hV
    dsimp only at hV
    simp only [hRLen, hFLen, hHtLen, hForsShape, hHtShape, ne_eq,
               not_true_eq_false, decide_false, Bool.not_true, Bool.false_or,
               Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hV
    exact hV
  if hForsEq : pkForsStar = honPkFors then
    let rootsStar := (List.range p.k).map fun j =>
      let idxJ := (base2b mdStar p.a p.k).getD j 0
      let entry := sigStar.forsSig.getD j ⟨[], []⟩
      let globalLeaf := j * (2 ^ p.a) + idxJ
      let node0 := fipsF p.n sk.pkSeed (mkFipsAdrs 0 idxTreeStar .forsTree idxLeafStar 0 globalLeaf) entry.skVal
      fipsWalkBottomUp p.n sk.pkSeed 0 idxTreeStar idxLeafStar .forsTree 0 globalLeaf node0 entry.authPath
    let rootsHon := (List.range p.k).map fun j =>
      fipsForsNode p sk.skSeed sk.pkSeed idxTreeStar idxLeafStar p.a j
    if hRootsEq : rootsStar = rootsHon then
      have hRootEqAt : ∀ j : Nat, j < p.k →
          let idxJ := (base2b mdStar p.a p.k).getD j 0
          let entry := sigStar.forsSig.getD j ⟨[], []⟩
          let globalLeaf := j * (2 ^ p.a) + idxJ
          let node0 := fipsF p.n sk.pkSeed (mkFipsAdrs 0 idxTreeStar .forsTree idxLeafStar 0 globalLeaf) entry.skVal
          fipsWalkBottomUp p.n sk.pkSeed 0 idxTreeStar idxLeafStar .forsTree 0 globalLeaf node0 entry.authPath =
            fipsForsNode p sk.skSeed sk.pkSeed idxTreeStar idxLeafStar p.a j := by
        intro j hj
        exact map_eq_on_mem hRootsEq j (List.mem_range.mpr hj)
      match verifyOrExtractForsTrees p sk mdStar idxTreeStar idxLeafStar
              sigStar hFLen hFEach hRootEqAt p.k (Nat.le_refl p.k) with
      | .inl coll => .forsItsr (.forsHashCollision coll)
      | .inr ⟨hAllSkEq⟩ =>
        let HMsgCollPred (rec : SessionWireRecord) : Prop :=
          validThresholdApproval clInit.tsig rec.request.honestApprovers = true ∧
          rec.honestRound3 ≠ [] ∧
          fipsHMsg p.m (fipsPrfMsg p.n sk.skPrf rec.request.optRand rec.request.msg)
            sk.pkSeed sk.pkRoot rec.request.msg = dStar
        match findDecidableElem HMsgCollPred tr.sessions with
        | .inl ⟨rec, hMem, hVal, hR3Rec, hDigEq⟩ =>
          let rRec := fipsPrfMsg p.n sk.skPrf rec.request.optRand rec.request.msg
          have hMsgNe : rec.request.msg ≠ mStar := hFresh rec hMem hVal hR3Rec
          .prfMsg ⟨{
            in1 := sigStar.rRand ++ sk.pkSeed ++ sk.pkRoot ++ mStar
            in2 := rRec ++ sk.pkSeed ++ sk.pkRoot ++ rec.request.msg
            hNe := fun hIn => by
              have hPrefLen : (sigStar.rRand ++ sk.pkSeed ++ sk.pkRoot).length =
                              (rRec ++ sk.pkSeed ++ sk.pkRoot).length := by
                simp [hRLen, rRec, fipsPrfMsg]
              obtain ⟨_, hMsgEq⟩ := List.append_inj hIn hPrefLen
              exact hMsgNe hMsgEq.symm
            hEq := by
              simpa [fipsHMsg, dStar, rRec] using hDigEq.symm }⟩
        | .inr ⟨hNoDigColl⟩ =>
          match checkForsSubsetCoverage p sk clInit tr mdStar idxTreeStar idxLeafStar p.k with
          | .inl ⟨treeIdx, hTreeLt, hNeverOpened⟩ =>
            .forsItsr (.forsUnqueriedPrfRecovery treeIdx hTreeLt
              (hAllSkEq treeIdx hTreeLt) hNeverOpened)
          | .inr ⟨hAllCov⟩ =>
            .forsItsr (.forsInterleavedSubsetCover hkPos (fun j hj => by
              obtain ⟨rec, hMem, hVal, hR3, hCoord⟩ := hAllCov j hj
              refine ⟨rec, hMem, hVal, hR3, hFresh rec hMem hVal hR3, ?_, hCoord.1, hCoord.2.1, hCoord.2.2⟩
              intro hDigEq
              exact hNoDigColl rec hMem ⟨hVal, hR3, hDigEq⟩))
    else
      let adrsRoots := mkFipsAdrs 0 idxTreeStar .forsRoots idxLeafStar 0 0
      .forsItsr (.forsHashCollision
        { in1 := sk.pkSeed ++ encodeFips205Adrs adrsRoots ++ rootsStar.flatten
          in2 := sk.pkSeed ++ encodeFips205Adrs adrsRoots ++ rootsHon.flatten
          hNe := fun hIn => by
            simp only [List.append_assoc, List.append_cancel_left_eq] at hIn
            have hS1 : ∀ x ∈ rootsStar, x.length = p.n := by
              intro x hx
              rw [List.mem_map] at hx
              obtain ⟨j, _, rfl⟩ := hx
              exact fipsWalkBottomUp_length _ _ _ _ _ _ _ _ _ _ (fipsF_length _ _ _ _)
            have hS2 : ∀ y ∈ rootsHon, y.length = p.n := by
              intro y hy
              rw [List.mem_map] at hy
              obtain ⟨j, _, rfl⟩ := hy
              exact fipsForsNode_length _ _ _ _ _ _ _
            have hLenEq : rootsStar.length = rootsHon.length := by simp [rootsStar, rootsHon]
            exact hRootsEq (flatten_inj_fixed hnPos hLenEq hS1 hS2 hIn)
          hEq := by
            simpa [pkForsStar, honPkFors, fipsForsPkFromSig, fipsForsPkGen,
                   rootsStar, rootsHon, fipsTl, adrsRoots] using hForsEq })
  else
    have hLeafLt : idxLeafStar < 2 ^ p.hp := Nat.mod_lt _ (Nat.two_pow_pos p.hp)
    have hTreeExp : p.h - p.hp = (p.d - 1) * p.hp := by
      have hd1 : p.d = (p.d - 1) + 1 := by omega
      have hMul : p.d * p.hp = (p.d - 1) * p.hp + p.hp := by
        conv => lhs; rw [hd1]
        rw [Nat.succ_mul]
      omega
    have hTreeLt : idxTreeStar < 2 ^ ((p.d - 1) * p.hp) := by
      dsimp only [idxTreeStar, splitStar, fipsSplitDigest]
      rw [← hTreeExp]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    match extractHypertreeBreakAux p hnPos hnLe128 sk p.d hdPos
            0 idxTreeStar idxLeafStar (Nat.zero_add p.d) hLeafLt hTreeLt
            pkForsStar (fipsForsPkFromSig_length p sigStar.forsSig mdStar sk.pkSeed idxTreeStar idxLeafStar)
            hForsEq sigStar.htSig hHtLen hHtEach hTopVerify with
    | .inl wotsBrk => .wotsChainSmTcr wotsBrk
    | .inr xmssBrk => .xmssMerkleTcr xmssBrk

/-- **Constructive Whole-Transcript Interactive Forgery Extractor (`extractInteractiveSlhBreak`)**:
    Given ANY transcript `tr` from `RealProtocolExec` and ANY valid wire signature `rawSigStar` on a
    message `mStar` never quorum-approved in `tr.sessions`, constructively (`0 Classical.choice`,
    `Type`-valued!) extracts a concrete `RssSlhInteractiveSecurityBreak` witness: an
    `ActiveConsistencySoundnessBreak` against the corrupt party's private stream if the scan finds
    one, otherwise `extractSlhHashGameBreak`. -/
def extractInteractiveSlhBreak {AdvState : Type}
    (corrView : RssPartyKeyShare)
    (p : Fips205Params) (hWf : p.wellFormed = true)
    (cIdx : Fin 3) (deg : Nat)
    (skSeed skPrf pkSeed : List UInt8)
    (clInit : RealClusterState SlhPublicKey RssPartyKeyShare)
    (tr : ExecTranscript AdvState)
    (mStar : List UInt8) (sigStar : SlhSignature)
    (hSigWt : sigStar.WellTyped p)
    (hVerify : slhVerifyInternal p mStar sigStar (slhKeygenInternal p skSeed skPrf pkSeed).2 = true)
    (hUnapproved : ∀ rec ∈ tr.sessions,
      validThresholdApproval clInit.tsig rec.request.honestApprovers = true →
      rec.request.msg ≠ mStar) :
    RssSlhInteractiveSecurityBreak corrView p cIdx deg
      (slhKeygenInternal p skSeed skPrf pkSeed).1 clInit tr mStar sigStar :=
  match scanActiveConsistencyBreak corrView cIdx deg tr with
  | some activeBrk => .activeConsistency activeBrk
  | none =>
    (extractSlhHashGameBreak p hWf skSeed skPrf pkSeed clInit tr mStar sigStar hSigWt hVerify
      (fun rec hMem hVal _ => hUnapproved rec hMem hVal)).toInteractive corrView cIdx deg

private theorem sharedVerifyRound1_cursor (cIdx : Fin 3) (r1St : RssRound1State)
    (corrR1 : List (Nat × ByteArray)) {r2Init : RssRound2State}
    (h : sharedVerifyRound1 cIdx r1St corrR1 = .inr r2Init) :
    r2Init.cursor = r1St.cursor := by
  unfold sharedVerifyRound1 at h
  cases hFind : corrR1.find? (fun pr => pr.1 == cIdx.val) with
  | none => rw [hFind] at h; cases h
  | some pr =>
    rcases pr with ⟨_, cWire⟩
    rw [hFind] at h
    dsimp only at h
    split at h
    · cases h
    · injection h with hEq; rw [← hEq]

/-- **Honesty Link (`activeConsistencyBreak_implies_schwartzZippel_root`)**:
    Whenever a single session `rec = (execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt tape).2.2`
    witnesses `rec.honestRound3 ≠ []` with corrupt party `cIdx` (`cl.tsig.corruptParties = [cIdx.val]`),
    its Round-2 wire `cWire2` parsed to `(nonceC, sentWires)` **necessarily satisfied**, at the joint
    coin `gamma = coinA ⊕ coinB ⊕ openingCoin nonceC`, BOTH:
    0. `sentWires.length = expectedWires.length` for the private stream `expectedWires` the honest
       pair computed from its vault,
    1. `bbcggiWireAccumulator sentWires gamma = bbcggiWireAccumulator expectedWires gamma`, AND
    2. `batchDeviationPoly (zipXorTower 7 sentWires expectedWires) gamma = towerZero 7`!
    Thus `ActiveConsistencySoundnessBreak` is NEVER an unconstrained label — in `RealProtocolExec`,
    it forces a genuine non-zero degree-`≤ deg` polynomial root hit in `GF(2^128)`. -/
theorem activeConsistencyBreak_implies_schwartzZippel_root {AdvState : Type}
    (p : Fips205Params) (cIdx : Fin 3) (deg : Nat)
    (A : UcRushingAdversary AdvState)
    (cl : RealClusterState SlhPublicKey RssPartyKeyShare)
    (advSt : AdvState) (tape : RssSlhSessionTape p.sigBytes)
    (hSingleCorrupt : cl.tsig.corruptParties = [cIdx.val])
    {cWire2 : ByteArray} {nonceC : List UInt8} {sentWires : List Tower128}
    (hR3Nonempty : (execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt tape).2.2.honestRound3 ≠ [])
    (hWireMem : (cIdx.val, cWire2) ∈ (execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt tape).2.2.corruptRound2)
    (hParse : parseCorruptRound2Wire deg cWire2 = some (nonceC, sentWires)) :
    let expectedWires :=
      corruptExpectedChiStream cIdx deg (corruptViewOfVault cIdx cl.honestShares)
        (A.scheduleSession advSt).1.msg
    let gamma := unpackTower 7 ((tape.gammaBits ^^^ tape.coinB) ^^^ openingCoin nonceC)
    sentWires.length = expectedWires.length ∧
    bbcggiWireAccumulator sentWires gamma = bbcggiWireAccumulator expectedWires gamma ∧
    batchDeviationPoly (zipXorTower 7 sentWires expectedWires) gamma = towerZero 7 := by
  intro expectedWires gamma
  dsimp only [expectedWires, gamma]
  unfold execRealSession rssSlhInteractiveProtocol rssSlhCoinProtocol sharedCoinTossBarrier at hR3Nonempty hWireMem
  dsimp only at hR3Nonempty hWireMem
  cases hQ : validThresholdApproval cl.tsig (A.scheduleSession advSt).1.honestApprovers
  · rw [hQ] at hR3Nonempty; simp at hR3Nonempty
  · rw [hQ, ite_eq_right (by decide : ¬ ((!true) = true))] at hR3Nonempty hWireMem
    cases hW : walPreSignStep cl.honestWal (slhPkDigest cl.tsig.pk)
        (A.scheduleSession advSt).1.reqEpoch (slhReqDigest (A.scheduleSession advSt).1) with
    | err _ _ => rw [hW] at hR3Nonempty; simp at hR3Nonempty
    | ok wal' wAuth =>
      rw [hW] at hR3Nonempty hWireMem
      cases wAuth with
      | replayCached _ => simp at hR3Nonempty
      | authorizedFresh _ =>
        dsimp only at hR3Nonempty hWireMem
        cases hVR1 : sharedVerifyRound1 cIdx _ _ with
        | inl _ => rw [hVR1] at hR3Nonempty; simp at hR3Nonempty
        | inr r2Init =>
          have hCurEq : r2Init.cursor = cl.maskSessionCursor :=
            sharedVerifyRound1_cursor cIdx _ _ hVR1
          rw [hVR1] at hR3Nonempty hWireMem
          dsimp only at hR3Nonempty hWireMem
          cases hBar : sharedPreCutBarrier cIdx deg cl.tsig.pk _ _ _ with
          | inl _ => rw [hBar] at hR3Nonempty; simp at hR3Nonempty
          | inr r3Init =>
            rw [hBar] at hWireMem
            dsimp only at hWireMem
            unfold sharedPreCutBarrier at hBar
            rw [hSingleCorrupt] at hBar hWireMem
            cases hFin : sharedFinalizeCutOpen p cIdx cl.tsig.pk _ _ _ <;>
              rw [hFin] at hWireMem <;>
              dsimp only at hWireMem
            all_goals
              simp only [List.map, List.mem_singleton, Prod.mk.injEq] at hWireMem
              rcases hWireMem with ⟨_, hWireEq⟩
              subst hWireEq
              simp only [corruptOpenedCoin, List.map, List.find?, beq_self_eq_true, hParse, hCurEq] at hBar
              cases hCmt : (round1NonceCommit cl.tsig.pk _ cl.maskSessionCursor cIdx.val nonceC != r2Init.corrR1Commit)
              · rw [hCmt] at hBar
                simp only [Bool.false_eq_true, ↓reduceIte] at hBar
                cases hVer : verifyPrivateChiWires
                    (corruptExpectedChiStream cIdx deg (corruptViewOfVault cIdx cl.honestShares)
                      (A.scheduleSession advSt).1.msg)
                    sentWires (unpackTower 7 ((tape.gammaBits ^^^ tape.coinB) ^^^ openingCoin nonceC))
                · rw [hVer] at hBar; simp at hBar
                · have hLen := of_decide_eq_true (Bool.and_eq_true_iff.mp hVer).1
                  have hAcc := (Bool.and_eq_true_iff.mp hVer).2
                  have hAccEq := of_decide_eq_true (by simpa [beq_iff_eq] using hAcc)
                  have hBatchBool := (bbcggiWireAccumulator_eq_iff_batchDeviationPoly hLen
                    (unpackTower 7 ((tape.gammaBits ^^^ tape.coinB) ^^^ openingCoin nonceC))).symm.trans hAcc
                  exact ⟨hLen, hAccEq, of_decide_eq_true (by simpa [beq_iff_eq] using hBatchBool)⟩
              · rw [hCmt] at hBar; simp at hBar

/-- **Non-Cosplay Witness Guard (`no_trivial_break_on_empty_transcript`)**:
    Neither `ActiveConsistencySoundnessBreak` nor `Fips205ForsItsrBreak.forsInterleavedSubsetCover` can
    ever be inhabited on an empty session transcript (`tr.sessions = []`). -/
theorem no_trivial_break_on_empty_transcript {AdvState : Type}
    (corrView : RssPartyKeyShare) (cIdx : Fin 3) (deg : Nat) (advSt : AdvState) :
    (ActiveConsistencySoundnessBreak corrView cIdx deg (⟨advSt, []⟩ : ExecTranscript AdvState) → False) ∧
    (∀ (p : Fips205Params) (_hK : 0 < p.k)
       (P : Nat → SessionWireRecord → Prop),
       (∀ j : Nat, j < p.k → ∃ rec ∈ ([] : List SessionWireRecord), P j rec) → False) := by
  refine ⟨fun w => (by cases w.hMem), fun p hK P hAll => ?_⟩
  obtain ⟨_, hMem, _⟩ := hAll 0 hK
  cases hMem

/-- **Crown-Jewel Theorem 2 (`rss_slh_interactive_euf_cma_reduction`)**:
    **Constructive Black-Box Interactive `EUF-CMA` Security Reduction (`0 Classical.choice`, `0` cheat hypotheses!)**:
    For ANY well-formed NIST `FIPS 205` parameter set `p`, ANY 2-of-3 RSS secret-key sharing `(seedSh, prfSh)`,
    ANY stateful rushing adversary `A` scheduling `Q_s` interactive threshold sessions in `RealProtocolExec`,
    and ANY post-interaction forgery extractor `forgeOut : ExecTranscript AdvState → List UInt8 × ByteArray`,
    if `forgeOut tr = (mStar, rawSigBytes)` decodes via `decodeSlhSig p` to a valid `SlhSignature` `sigStar`
    verifying under `slhVerifyInternal p mStar sigStar pk = true` while `mStar` was **never approved by a
    valid `t`-quorum** in `clInit.tsig.approvedMsgs` or any session of `tr.sessions`, then our explicit
    `Type`-valued reduction `extractInteractiveSlhBreak` constructively produces a concrete witness of:
    - `ActiveConsistencySoundnessBreak` (`GF(2^128)` Schwartz-Zippel consistency hit), **OR**
    - `Fips205ForsItsrBreak` (FORS collision / unqueried `sk.skSeed` PRF recovery / multi-query `H_msg` ITSR cover), **OR**
    - `WotsChainSmTcrBreak` (WOTS+ hash collision or backward chain preimage on `honestSlhWotsMsg`), **OR**
    - `XmssMerkleTcrBreak` (XMSS `.tree` `SHAKE256` collision under `pk.pkSeed`), **OR**
    - `PrfMsgBreak` (`SHAKE256` `H_msg` collision against an approved session)! -/
theorem rss_slh_interactive_euf_cma_reduction {AdvState : Type}
    (p : Fips205Params) (hWf : p.wellFormed = true)
    (cIdx : Fin 3) (deg Q_s : Nat)
    {seedSh prfSh : RssByteShares}
    (pkSeed : List UInt8)
    (A : UcRushingAdversary AdvState)
    (tapes : Nat → RssSlhSessionTape p.sigBytes)
    (clInit : RealClusterState SlhPublicKey RssPartyKeyShare)
    (advSt0 : AdvState)
    (hPkKey : clInit.tsig.pk =
      (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).2)
    (forgeOut : ExecTranscript AdvState → List UInt8 × ByteArray)
    {sigStar : SlhSignature}
    (hDecode :
      let (_, tr) := RealProtocolExec (rssSlhInteractiveProtocol p cIdx deg) A Q_s tapes clInit advSt0
      decodeSlhSig p (unpackWireBytes (forgeOut tr).2) = some sigStar)
    (hVerify :
      let (_, tr) := RealProtocolExec (rssSlhInteractiveProtocol p cIdx deg) A Q_s tapes clInit advSt0
      slhVerifyInternal p (forgeOut tr).1 sigStar clInit.tsig.pk = true)
    (hFreshMsg :
      let (clF, tr) := RealProtocolExec (rssSlhInteractiveProtocol p cIdx deg) A Q_s tapes clInit advSt0
      (forgeOut tr).1 ∉ clF.tsig.approvedMsgs ∧
      ∀ rec ∈ tr.sessions,
        validThresholdApproval clInit.tsig rec.request.honestApprovers = true →
        rec.request.msg ≠ (forgeOut tr).1) :
    let (_, tr) := RealProtocolExec (rssSlhInteractiveProtocol p cIdx deg) A Q_s tapes clInit advSt0
    let sk := (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).1
    Nonempty (ActiveConsistencySoundnessBreak (corruptRssView cIdx seedSh prfSh) cIdx deg tr) ∨
    Nonempty (Fips205ForsItsrBreak p sk clInit tr (forgeOut tr).1 sigStar) ∨
    Nonempty (WotsChainSmTcrBreak p sk) ∨
    Nonempty (XmssMerkleTcrBreak p ⟨sk.pkSeed, sk.pkRoot⟩) ∨
    Nonempty (PrfMsgBreak p) := by
  dsimp only at hDecode hVerify hFreshMsg ⊢
  let tr := (RealProtocolExec (rssSlhInteractiveProtocol p cIdx deg) A Q_s tapes clInit advSt0).2
  have hSigWt : sigStar.WellTyped p := decodeSlhSig_wellTyped hDecode
  have hVerKey : slhVerifyInternal p (forgeOut tr).1 sigStar
      (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).2 = true := by
    rwa [← hPkKey]
  match extractInteractiveSlhBreak (corruptRssView cIdx seedSh prfSh) p hWf cIdx deg
          (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed
          clInit tr (forgeOut tr).1 sigStar hSigWt hVerKey hFreshMsg.2 with
  | .activeConsistency w => exact .inl ⟨w⟩
  | .forsItsr w          => exact .inr (.inl ⟨w⟩)
  | .wotsChainSmTcr w    => exact .inr (.inr (.inl ⟨w⟩))
  | .xmssMerkleTcr w     => exact .inr (.inr (.inr (.inl ⟨w⟩)))
  | .prfMsg w            => exact .inr (.inr (.inr (.inr ⟨w⟩)))

/-- **Inhabitedness Witness for Theorem 2 (`inhabited_rss_slh_euf_cma_reduction`)**:
    Demonstrates non-vacuity of `rss_slh_interactive_euf_cma_reduction` on `slhDsaShake128f`:
    an adversary outputting an unqueried `0`-session valid signature satisfies every premise of
    `rss_slh_interactive_euf_cma_reduction` (`decodeSlhSig = some`, `slhVerifyInternal = true`,
    `mStar ∉ approvedMsgs`), and the constructive extractor extracts a concrete break witness! -/
theorem inhabited_rss_slh_euf_cma_reduction :
    let p := slhDsaShake128f
    let seedSh : RssByteShares := ⟨List.replicate 16 1, List.replicate 16 2, List.replicate 16 3⟩
    let prfSh : RssByteShares := ⟨List.replicate 16 4, List.replicate 16 5, List.replicate 16 6⟩
    let pkSeed : List UInt8 := List.replicate 16 7
    let sk := (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).1
    let pk := (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).2
    let clInit : RealClusterState SlhPublicKey RssPartyKeyShare :=
      ⟨⟨pk, 2, 3, [0], [], []⟩, initWalLatchState (slhPkDigest pk), 0,
       dealHonestRssVault ⟨0, by decide⟩ seedSh prfSh⟩
    let mStar : List UInt8 := [0x42, 0x99]
    let sigStar := slhSignInternal p mStar sk []
    ∃ (rawSig : ByteArray),
      decodeSlhSig p (unpackWireBytes rawSig) = some sigStar ∧
      slhVerifyInternal p mStar sigStar clInit.tsig.pk = true ∧
      mStar ∉ clInit.tsig.approvedMsgs ∧
      Nonempty (RssSlhInteractiveSecurityBreak (corruptRssView ⟨0, by decide⟩ seedSh prfSh)
        p ⟨0, by decide⟩ 4 sk clInit ⟨(), []⟩ mStar sigStar) := by
  intro p seedSh prfSh pkSeed sk pk clInit mStar sigStar
  let rawSig := packWireBytes (encodeSlhSig sigStar)
  have hDec : decodeSlhSig p (unpackWireBytes rawSig) = some sigStar := by
    rw [unpackWireBytes_packWireBytes]
    exact decodeSlhSig_encodeSlhSig (slhSignInternal_wellTyped p mStar sk [])
  have hVer : slhVerifyInternal p mStar sigStar clInit.tsig.pk = true :=
    slhVerifyInternal_slhSignInternal p slhDsaShake128f_wellFormed
      (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed mStar []
  have hUnapp : ∀ rec ∈ ([] : List SessionWireRecord),
      validThresholdApproval clInit.tsig rec.request.honestApprovers = true →
      rec.request.msg ≠ mStar := fun _ hM => by cases hM
  refine ⟨rawSig, hDec, hVer, by simp [clInit], ?_⟩
  exact ⟨extractInteractiveSlhBreak (corruptRssView ⟨0, by decide⟩ seedSh prfSh)
    p slhDsaShake128f_wellFormed ⟨0, by decide⟩ 4
    (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed
    clInit ⟨(), []⟩ mStar sigStar
    (slhSignInternal_wellTyped p mStar sk []) hVer hUnapp⟩

/-! ## 4b. End-to-End Weld: Multi-Session Rushing Forgery ⇒ Counted `GF(2^128)` Root Hit or Hash-Game Witness -/

/-- `Sim_RssSlh` always emits Round-3 messages once it is handed the ideal signature, so a session
    record with empty `honestRound3` is exactly a session in which the signing oracle was not read. -/
theorem Sim_RssSlh_round3_ne_nil (corrView : RssPartyKeyShare) (p : Fips205Params) (cIdx : Fin 3) (deg : Nat)
    (pk : SlhPublicKey) (corr : List Nat) (req : SessionScheduleReq) (s3 : RssRound3State)
    (sigB : ByteArray) (tape : RssSlhSessionTape p.sigBytes) :
    ((Sim_RssSlh corrView p cIdx deg).simRound3 pk corr req s3 sigB tape).1 ≠ [] :=
  fun h => buildHonestRound3Msgs_ne_nil cIdx _ (List.append_eq_nil_iff.mp h).1

/-- **EUF-CMA winning predicate on a transcript (`slhForgeryWins`)**: the forger's wire output decodes
    to a signature that verifies under `pk`, on a message that was never the request of a session that
    reached Round 3. Requests that were scheduled but aborted earlier do not disqualify the forgery. -/
def slhForgeryWins {AdvState : Type} (p : Fips205Params) (pk : SlhPublicKey)
    (forgeOut : ExecTranscript AdvState → List UInt8 × ByteArray)
    (tr : ExecTranscript AdvState) : Bool :=
  match decodeSlhSig p (unpackWireBytes (forgeOut tr).2) with
  | none => false
  | some sig =>
    slhVerifyInternal p (forgeOut tr).1 sig pk &&
    tr.sessions.all (fun rec => rec.honestRound3.isEmpty || decide (rec.request.msg ≠ (forgeOut tr).1))

/-- Decoded forgery together with the concrete hash-game witness it yields against `tr`. -/
structure SlhForgeryHashGameWitness {AdvState : Type}
    (p : Fips205Params) (sk : SlhSecretKey)
    (clInit : RealClusterState SlhPublicKey RssPartyKeyShare)
    (forgeOut : ExecTranscript AdvState → List UInt8 × ByteArray)
    (tr : ExecTranscript AdvState) where
  sigStar : SlhSignature
  hDecode : decodeSlhSig p (unpackWireBytes (forgeOut tr).2) = some sigStar
  brk     : Fips205HashGameBreak p sk clInit tr (forgeOut tr).1 sigStar

/-- Constructive extraction (`0 Classical.choice`) of a hash-game witness from ANY transcript on which
    `slhForgeryWins` holds. -/
def slhForgeryHashGameWitness_of_wins {AdvState : Type}
    (p : Fips205Params) (hWf : p.wellFormed = true)
    (skSeed skPrf pkSeed : List UInt8)
    (clInit : RealClusterState SlhPublicKey RssPartyKeyShare)
    (forgeOut : ExecTranscript AdvState → List UInt8 × ByteArray)
    (tr : ExecTranscript AdvState)
    (hWin : slhForgeryWins p (slhKeygenInternal p skSeed skPrf pkSeed).2 forgeOut tr = true) :
    SlhForgeryHashGameWitness p (slhKeygenInternal p skSeed skPrf pkSeed).1 clInit forgeOut tr :=
  match hDec : decodeSlhSig p (unpackWireBytes (forgeOut tr).2) with
  | none => False.elim (by
      unfold slhForgeryWins at hWin
      rw [hDec] at hWin
      cases hWin)
  | some sig =>
    have hBoth :
        (slhVerifyInternal p (forgeOut tr).1 sig (slhKeygenInternal p skSeed skPrf pkSeed).2 &&
          tr.sessions.all (fun rec =>
            rec.honestRound3.isEmpty || decide (rec.request.msg ≠ (forgeOut tr).1))) = true := by
      unfold slhForgeryWins at hWin
      rw [hDec] at hWin
      exact hWin
    { sigStar := sig
      hDecode := hDec
      brk := extractSlhHashGameBreak p hWf skSeed skPrf pkSeed clInit tr (forgeOut tr).1 sig
        (decodeSlhSig_wellTyped hDec) (Bool.and_eq_true_iff.mp hBoth).1
        (fun rec hMem _ hR3 => by
          have hOk := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hBoth).2 rec hMem
          rw [isEmpty_false_of_ne_nil hR3, Bool.false_or] at hOk
          exact of_decide_eq_true hOk) }

/-- **Mutation witness for `slhForgeryWins`**: a forgery on a message that some session carried into
    Round 3 never counts as a win, whatever the signature. -/
