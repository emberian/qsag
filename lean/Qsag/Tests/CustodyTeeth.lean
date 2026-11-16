module
public import Qsag.Spec.Algebra
public import Qsag.Tactic.Prelude
public import Qsag.Math.CommitteeMasks
/-
# Qsag.Tests.CustodyTeeth — witnesses and teeth for the threshold-custody refinements

1. The Shamir + `BeltLatch` custody network (`Qsag.Custody.ShamirThresholdCustodyRefinement`):
   an executed 2-of-4 run ending in a verifying validator signature
   (`witness_shamir_custody_nonvacuous`), the under-quorum latch equivocation tooth, and the
   unverified-combiner tooth.
2. `ShamirValidatorDeployment.WellFormed`: what fails when the evaluation points repeat or one of
   them is zero.
-/

public import Qsag.Custody.ShamirThresholdCustodyRefinement
import all Qsag.Custody.ShamirThresholdCustodyRefinement
import all Qsag.Custody.JortsBeltLatchAndQuorumSwitching
import all Qsag.Custody.SeparatedCustody
import all Qsag.Custody.CustodySuiteFull
import all Qsag.Oracle.Keccak
import all Qsag.Math.Gf2Pow128
import all Qsag.Math.CoeffPoly
import all Qsag.Protocol.Threshold.ThresholdMpc
import all Qsag.Protocol.Threshold.MaliciousSecurity
import all Qsag.Protocol.Threshold.ParametricThresholdAndUnlinkableQsa
import Qsag.Tactic.AssuranceKit

namespace Qsag

set_option autoImplicit false

/-! ## 1. Shamir custody network: concrete `(n = 4, t = 2, f = 1, q = 3)` witnesses and teeth -/

/-- Deployment identifier of the toy deployment. -/
def toyDeploymentId : Nat := 7

/-- Distinct nonzero `GF(2^128)` (`TowerElem 7`) Shamir evaluation points for `n = 4` custodians. -/
def shamirPts4 : Fin 4 → TowerElem 7
  | ⟨0, _⟩ => towerOne 7
  | ⟨1, _⟩ => towerX 7
  | ⟨2, _⟩ => towerAdd 7 (towerOne 7) (towerX 7)
  | ⟨3, _⟩ => (towerX 6, towerOne 6)

theorem shamirPts4_01_ne : shamirPts4 ⟨0, by decide⟩ ≠ shamirPts4 ⟨1, by decide⟩ :=
  towerOne_ne_towerX 6

/-- Symbolic 2-of-4 Lagrange reconstruction at `0 ∈ GF(2^128)` for custodians `{p₀, p₁}`. -/
theorem shamirPts4_lagrange01 (c₀ : TowerElem 7) (tail : ShamirPadPoly (TowerElem 7) 1) :
    ringDot (lagrange2WeightsTower 7 (shamirPts4 ⟨0, by decide⟩) (shamirPts4 ⟨1, by decide⟩))
      ([shamirPts4 ⟨0, by decide⟩, shamirPts4 ⟨1, by decide⟩].map
        (fun x => RoundPoly.evalCoeffs (c₀ :: tail.1) x)) = c₀ :=
  lagrange2WeightsTower_eval 7 shamirPts4_01_ne c₀ tail

/-- Toy 1-chain concrete `(n = 4, t = 2, f = 1, q = 3)` deployment over `GF(2^128)` (`TowerElem 7`)
    exercising `BeltLatch` bind + pairwise MAC echo + `3`-of-`4` quorum certification +
    `Custody.Vault` mint + `2`-of-`4` pre-stepped Shamir share release + combiner verification. -/
def toyShamirPolicy (r : Custody.Intent) : Custody.RoundPolicy where
  keys _ _ :=
    { alpha0 := towerZero 7
      alpha1 := towerZero 7
      localK := fun _ => (towerZero 7, towerZero 7) }
  roster := [0]
  digest _ := Custody.roundCommitment toyDeploymentId r

def toyShamirOpening (r : Custody.Intent) : Custody.RoundOpening :=
  { session := r.session
    round := r.round
    opening :=
      { partyId := 0
        shareX := towerZero 7
        mac0 := towerZero 7
        mac1 := towerZero 7 } }

theorem toyShamirPolicy_checkRound (r : Custody.Intent) :
    Custody.checkRound (toyShamirPolicy r) toyDeploymentId r (Custody.roundCommitment toyDeploymentId r)
      [toyShamirOpening r] = true := by
  unfold Custody.checkRound toyShamirPolicy toyShamirOpening Custody.roundCommitment
  have hLen : (cshake256Bytes Custody.roundDomain (Custody.payload toyDeploymentId 0 r)).length = 32 :=
    cshake256Bytes_length _ _
  have hMac : verifyBdozPairMac
      { alpha0 := towerZero 7, alpha1 := towerZero 7, localK := fun _ => (towerZero 7, towerZero 7) }
      { partyId := 0, shareX := towerZero 7, mac0 := towerZero 7, mac1 := towerZero 7 } = true := by
    decide +kernel
  simp [hLen, hMac]

/-- The toy policy admits its own burn into an empty vault of the toy deployment. -/
private theorem toy_mintGuard_initial (r : Custody.Intent) (id : Custody.VaultIdentity)
    (hId : id.deploymentId = toyDeploymentId) (hMsg : r.message ≠ []) (hRound : r.round = 0)
    (hSpend : r.spend ≤ 100) :
    Custody.mintGuard (toyShamirPolicy r) 100 (Custody.initial id)
      { intent := r, digest := Custody.roundCommitment toyDeploymentId r,
        openings := [toyShamirOpening r] } = true := by
  unfold Custody.mintGuard
  rw [show (Custody.initial id).identity.deploymentId = toyDeploymentId from hId,
    toyShamirPolicy_checkRound, Bool.and_true]
  refine decide_eq_true ⟨Nat.zero_le _, hRound, ?_, fun h => absurd h List.not_mem_nil, hMsg⟩
  show 0 + r.spend ≤ 100
  rw [Nat.zero_add]
  exact hSpend

private theorem two_pow_64_pos_local : 0 < 2 ^ 64 :=
  calc 0 < 2 ^ 0 := by decide
    _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by decide)

private theorem beltLatchBindStep_init22_epoch0 (rec : BeltLatchRecord) (hEp : rec.epoch = 0) :
    beltLatchBindStep (BeltLatchNodeState.init 2 2) rec =
      .accepted { BeltLatchNodeState.init 2 2 with
        nextEpoch := 1, inFlight := some rec,
        disk := .persisted { nextEpoch := 1, inFlight := some rec } } .fresh := by
  have hEpNat : rec.epoch.toNat = 0 := by rw [hEp]; rfl
  dsimp only [beltLatchBindStep, BeltLatchNodeState.init]
  simp [hEpNat]

private theorem checkLatchCertifiedBurn_finRange {n : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (mk : Fin n → Fin n → Digest256)
    (q depId : Nat) (v : Fin n) (Q : CustodiansMask n)
    (rec : BeltLatchRecord) (b : Custody.Burn)
    (hQ : q ≤ maskCard Q)
    (hLeaf0 : b.intent.leaf = 0)
    (hRecEp : rec.epoch = 0)
    (hRecMd : rec.msgDigest = H (intentCanonicalPayload depId b.intent)) :
    checkLatchCertifiedBurn H MAC mk q depId v
      { BeltLatchNodeState.init 2 2 with
        nextEpoch := 1, inFlight := some rec,
        disk := .persisted { nextEpoch := 1, inFlight := some rec } }
      Q rec
      ((List.finRange n).map (fun s =>
        { sender := s, receiver := v, record := rec,
          binding := beltRecordBinding H rec,
          macTag := computeBeltEchoMac MAC (mk s v) s v rec })) b = true := by
  have hVerQ : verifyQuorumEchoCertificate H MAC mk q v Q rec
      ((List.finRange n).map (fun s =>
        { sender := s, receiver := v, record := rec,
          binding := beltRecordBinding H rec,
          macTag := computeBeltEchoMac MAC (mk s v) s v rec })) = true := by
    unfold verifyQuorumEchoCertificate
    rw [Bool.and_eq_true_iff]
    refine ⟨decide_eq_true hQ, List.all_eq_true.mpr ?_⟩
    intro s _
    cases hQs : Q.mem s
    · simp
    · simp only [Bool.not_true, Bool.false_or]
      apply List.any_eq_true.mpr
      refine ⟨{ sender := s, receiver := v, record := rec,
                binding := beltRecordBinding H rec,
                macTag := computeBeltEchoMac MAC (mk s v) s v rec },
              List.mem_map.mpr ⟨s, List.mem_finRange s, rfl⟩, ?_⟩
      unfold verifyAuthenticatedBeltEcho
      simp
  unfold checkLatchCertifiedBurn
  have h2_64 : b.intent.leaf < 2 ^ 64 := by rw [hLeaf0]; exact two_pow_64_pos_local
  have hEpEq : rec.epoch = UInt64.ofNat b.intent.leaf := by rw [hRecEp, hLeaf0]; rfl
  simp [BeltLatchNodeState.init, h2_64, hEpEq, hRecMd, hVerQ]

/-! ### Single-turn transition lemmas (used to execute concrete multi-turn witnesses) -/

private theorem beltLatchEmitEcho_keeps_state {n : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (k : Digest256) (s r : Fin n) (nodeSt : BeltLatchNodeState) :
    (∃ e, beltLatchEmitEcho H MAC k s r nodeSt = .accepted nodeSt e) ∨
      (∃ err, beltLatchEmitEcho H MAC k s r nodeSt = .rejected nodeSt err) := by
  unfold beltLatchEmitEcho
  split
  · exact .inr ⟨_, rfl⟩
  · split
    · exact .inr ⟨_, rfl⟩
    · exact .inl ⟨_, rfl⟩

private theorem stepBeltNetwork_honestEmitEcho_nodes {n : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (Corrupt : CustodiansMask n) (q : Nat)
    (net : BeltLatchNetworkState n) (s r j : Fin n) :
    (stepBeltNetwork H MAC macKeys Corrupt q net (.honestEmitEcho s r)).nodes j = net.nodes j := by
  unfold stepBeltNetwork
  dsimp only
  split
  · rfl
  · have hIte : (if j = s then net.nodes s else net.nodes j) = net.nodes j := by
      by_cases hj : j = s
      · rw [hj]; exact ite_self _
      · simp only [hj, ↓reduceIte]
    rcases beltLatchEmitEcho_keeps_state H MAC (macKeys s r) s r (net.nodes s) with ⟨e, he⟩ | ⟨err, he⟩
    · rw [he]; exact hIte
    · rw [he]; exact hIte

private theorem stepBeltNetwork_honestBind_nodes_ne {n : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (Corrupt : CustodiansMask n) (q : Nat)
    (net : BeltLatchNetworkState n) (p : Fin n) (rec : BeltLatchRecord)
    (j : Fin n) (hj : j ≠ p) :
    (stepBeltNetwork H MAC macKeys Corrupt q net (.honestBind p rec)).nodes j = net.nodes j := by
  unfold stepBeltNetwork
  dsimp only
  split
  · rfl
  · split <;> exact ite_eq_right_of_eq_false _ _ (eq_false hj)

private theorem stepBeltNetwork_honestBind_fresh_node {n : Nat}
    (H : List UInt8 → Digest256)
    (MAC : Digest256 → List UInt8 → Digest256)
    (macKeys : Fin n → Fin n → Digest256)
    (Corrupt : CustodiansMask n) (q : Nat)
    (net : BeltLatchNetworkState n) (p : Fin n) (rec : BeltLatchRecord)
    (nodeSt' : BeltLatchNodeState)
    (hC : Corrupt.mem p = false)
    (hB : beltLatchBindStep (net.nodes p) rec = .accepted nodeSt' .fresh) :
    (stepBeltNetwork H MAC macKeys Corrupt q net (.honestBind p rec)).nodes p = nodeSt' := by
  unfold stepBeltNetwork
  dsimp only
  rw [hB, hC]
  exact ite_eq_left_of_eq_true _ _ (eq_self p)

/-- A belt turn acts on the custody state through `stepBeltNetwork` alone. -/
private theorem stepShamirCustody_belt_beltNet {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d) (st : ShamirCustodyNetworkState n L)
    (b : BeltNetworkTurn n) :
    (stepShamirCustody dep st (.belt b)).beltNet =
      stepBeltNetwork dep.H dep.MAC dep.macKeys dep.Corrupt dep.q st.beltNet b := rfl

/-- A belt turn leaves vaults, share releases, and combined signatures untouched. -/
private theorem stepShamirCustody_belt_frame {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d) (st : ShamirCustodyNetworkState n L)
    (b : BeltNetworkTurn n) :
    (stepShamirCustody dep st (.belt b)).vaults = st.vaults ∧
    (stepShamirCustody dep st (.belt b)).honestShareReleases = st.honestShareReleases ∧
    (stepShamirCustody dep st (.belt b)).combinedSignatures = st.combinedSignatures :=
  ⟨rfl, rfl, rfl⟩

private theorem stepShamirCustody_echo_nodes {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d) (st : ShamirCustodyNetworkState n L)
    (s r j : Fin n) :
    (stepShamirCustody dep st (.belt (.honestEmitEcho s r))).beltNet.nodes j =
      st.beltNet.nodes j := by
  rw [stepShamirCustody_belt_beltNet]
  exact stepBeltNetwork_honestEmitEcho_nodes _ _ _ _ _ _ s r j

private theorem stepShamirCustody_bind_nodes_ne {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d) (st : ShamirCustodyNetworkState n L)
    (p : Fin n) (rec : BeltLatchRecord) (j : Fin n) (hj : j ≠ p) :
    (stepShamirCustody dep st (.belt (.honestBind p rec))).beltNet.nodes j =
      st.beltNet.nodes j := by
  rw [stepShamirCustody_belt_beltNet]
  exact stepBeltNetwork_honestBind_nodes_ne _ _ _ _ _ _ p rec j hj

private theorem stepShamirCustody_bind_fresh_node {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d) (st : ShamirCustodyNetworkState n L)
    (p : Fin n) (rec : BeltLatchRecord) (nodeSt' : BeltLatchNodeState)
    (hC : dep.Corrupt.mem p = false)
    (hB : beltLatchBindStep (st.beltNet.nodes p) rec = .accepted nodeSt' .fresh) :
    (stepShamirCustody dep st (.belt (.honestBind p rec))).beltNet.nodes p = nodeSt' := by
  rw [stepShamirCustody_belt_beltNet]
  exact stepBeltNetwork_honestBind_fresh_node _ _ _ _ _ _ p rec nodeSt' hC hB

/-- A certified mint by an honest custodian whose latch check passes only changes that
    custodian's vault, to `Custody.mint` of its previous vault. -/
private theorem stepShamirCustody_certifiedMint_ok {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d) (st : ShamirCustodyNetworkState n L)
    (p : Fin n) (anchor : Nat) (Q : CustodiansMask n) (rec : BeltLatchRecord)
    (echoes : List (AuthenticatedBeltEcho n)) (b : Custody.Burn)
    (hC : dep.Corrupt.mem p = false)
    (hChk : checkLatchCertifiedBurn dep.H dep.MAC dep.macKeys dep.q dep.deploymentId p
      (st.beltNet.nodes p) Q rec echoes b = true) :
    (stepShamirCustody dep st (.certifiedMint p anchor Q rec echoes b)).beltNet = st.beltNet ∧
    (stepShamirCustody dep st (.certifiedMint p anchor Q rec echoes b)).honestShareReleases =
      st.honestShareReleases ∧
    (stepShamirCustody dep st (.certifiedMint p anchor Q rec echoes b)).combinedSignatures =
      st.combinedSignatures ∧
    (stepShamirCustody dep st (.certifiedMint p anchor Q rec echoes b)).vaults p =
      Custody.mint (dep.policies p) (dep.caps p) anchor (st.vaults p) b ∧
    ∀ j, j ≠ p →
      (stepShamirCustody dep st (.certifiedMint p anchor Q rec echoes b)).vaults j = st.vaults j := by
  unfold stepShamirCustody
  dsimp only
  rw [hC, hChk]
  simp only [Bool.false_eq_true, ↓reduceIte]
  split
  · exact ⟨rfl, rfl, rfl, ite_eq_left_of_eq_true _ _ (eq_self p),
      fun j hj => ite_eq_right_of_eq_false _ _ (eq_false hj)⟩
  · exact ⟨rfl, rfl, rfl, ite_eq_left_of_eq_true _ _ (eq_self p),
      fun j hj => ite_eq_right_of_eq_false _ _ (eq_false hj)⟩

/-- A share release by an honest custodian whose vault is unpoisoned, at the presented anchor,
    and holds `r` as its active permit records exactly one opening for `(p, r)`. -/
private theorem stepShamirCustody_releaseShare_ok {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d) (st : ShamirCustodyNetworkState n L)
    (p : Fin n) (anchor : Nat) (r : Custody.Intent) (counter : UInt32)
    (hC : dep.Corrupt.mem p = false)
    (hP : (st.vaults p).poisoned = false)
    (hA : (st.vaults p).durable.anchor = anchor)
    (hAct : (st.vaults p).active = some r) :
    (stepShamirCustody dep st (.releaseShare p anchor r counter)).beltNet = st.beltNet ∧
    (stepShamirCustody dep st (.releaseShare p anchor r counter)).combinedSignatures =
      st.combinedSignatures ∧
    (stepShamirCustody dep st (.releaseShare p anchor r counter)).honestShareReleases.map
        (fun op => (op.party, op.intent)) =
      (p, r) :: st.honestShareReleases.map (fun op => (op.party, op.intent)) ∧
    ∀ j, j ≠ p →
      (stepShamirCustody dep st (.releaseShare p anchor r counter)).vaults j = st.vaults j := by
  have hCond : ((st.vaults p).poisoned || decide ((st.vaults p).durable.anchor ≠ anchor)) = false := by
    rw [hP, hA, Bool.false_or]
    exact decide_eq_false (fun h => h rfl)
  unfold stepShamirCustody
  dsimp only
  rw [hC]
  unfold releaseShamirShareFromVault
  rw [hCond]
  simp only [Bool.false_eq_true, ↓reduceIte, hAct]
  exact ⟨trivial, trivial, rfl, fun j hj => ite_eq_right_of_eq_false _ _ (eq_false hj)⟩

private theorem stepShamirCustody_combineSig_some {n L d : Nat}
    (dep : ShamirValidatorDeployment n L d) (st : ShamirCustodyNetworkState n L)
    (leafChainPk : Fin L → Digest256) (lambdas : List (TowerElem 7))
    (r : Custody.Intent) (counter : UInt32)
    (submitted : SubmittedDigest256ShamirShares L) (authPath : List Digest256)
    (sig : QuorumJortsSig)
    (hSig : combinePreSteppedShamirValidatorSig L dep.targetSum dep.deploymentId dep.H dep.validatorPk
      dep.digitsOf leafChainPk lambdas r counter submitted authPath = some sig) :
    (stepShamirCustody dep st
        (.combineSig leafChainPk lambdas r counter submitted authPath)).combinedSignatures =
      (r, sig) :: st.combinedSignatures ∧
    (stepShamirCustody dep st
        (.combineSig leafChainPk lambdas r counter submitted authPath)).honestShareReleases =
      st.honestShareReleases := by
  unfold stepShamirCustody
  dsimp only
  rw [hSig]
  exact ⟨rfl, rfl⟩

/-- Minting into the initial vault at anchor `0` under a passing `mintGuard` leaves an
    unpoisoned vault at anchor `1` whose active permit is the burned intent. -/
private theorem custody_mint_initial_ok (pol : Custody.RoundPolicy) (cap : Nat) (b : Custody.Burn)
    (id : Custody.VaultIdentity)
    (hMG : Custody.mintGuard pol cap (Custody.initial id) b = true) :
    (Custody.mint pol cap 0 (Custody.initial id) b).poisoned = false ∧
    (Custody.mint pol cap 0 (Custody.initial id) b).durable.anchor = 1 ∧
    (Custody.mint pol cap 0 (Custody.initial id) b).active = some b.intent := by
  unfold Custody.mint
  rw [hMG]
  exact ⟨rfl, rfl, rfl⟩

def toyShamirIntent : Custody.Intent :=
  { session := 1, round := 0, leaf := 0, spend := 10, message := [0x42] }

def toyShamirDeployment : ShamirValidatorDeployment 4 1 1 where
  deploymentId := toyDeploymentId
  H bs := if 0x20 ∈ bs then 1#256 else 0#256
  MAC k _ := k
  macKeys i j := if i.val = j.val then 1#256 else 0#256
  Corrupt := ⟨fun i => decide (i.val = 3)⟩
  t := 2
  f := 1
  q := 3
  height := 2
  maxWindow := 2
  targetSum := 2
  masterSeed := 0#256
  digitsOf _ := [⟨2, by decide⟩]
  evalPts := shamirPts4
  polyTape _ _ _ := (⟨[towerOne 7], rfl⟩, ⟨[towerX 7], rfl⟩)
  policies _ := toyShamirPolicy toyShamirIntent
  caps _ := 100

/-- End-to-end inhabitedness witness executing a full multi-turn `(n = 4, t = 2, f = 1, q = 3)`
    trace producing honest latch bindings, `3`-of-`4` certified `Custody.Vault` mints, `2`-of-`4`
    `GF(2^128)²` Shamir share openings, and a combined single-validator `QuorumJortsSig` that
    verifies under `toyShamirDeployment.validatorPk`! -/
theorem witness_shamir_custody_nonvacuous :
    ∃ (dep : ShamirValidatorDeployment 4 1 1) (trace : List (ShamirCustodyTurn 4 1))
      (S : CustodiansMask 4),
      maskCard dep.Corrupt ≤ dep.f ∧
      dep.f < dep.t ∧
      2 * dep.q > 4 + dep.f ∧
      dep.t ≤ maskCard S ∧
      let st := runShamirCustodyTrace dep (ShamirCustodyNetworkState.init dep) trace
      HonestQuorumReleasedIntent dep.Corrupt st S toyShamirIntent ∧
      st.combinedSignatures.length = 1 ∧
      ∀ entry ∈ st.combinedSignatures,
        verifyQuorumJortsSigAt 1 dep.targetSum dep.H dep.validatorPk dep.digitsOf
          (intentCanonicalPayload dep.deploymentId entry.1) entry.2 = true := by
  let dep := toyShamirDeployment
  let p0 : Fin 4 := ⟨0, by decide⟩
  let p1 : Fin 4 := ⟨1, by decide⟩
  let p2 : Fin 4 := ⟨2, by decide⟩
  let Q3 : CustodiansMask 4 := ⟨fun i => decide (i.val < 3)⟩
  let S2 : CustodiansMask 4 := ⟨fun i => decide (i.val < 2)⟩
  let rec₀ : BeltLatchRecord :=
    { epoch := 0
      msgDigest := dep.H (intentCanonicalPayload dep.deploymentId toyShamirIntent)
      retrySalt := 0#256
      targetSumDigits := [2] }
  let burn₀ : Custody.Burn :=
    { intent := toyShamirIntent
      digest := Custody.roundCommitment toyDeploymentId toyShamirIntent
      openings := [toyShamirOpening toyShamirIntent] }
  let echoesFor (v : Fin 4) : List (AuthenticatedBeltEcho 4) :=
    (List.finRange 4).map (fun s =>
      { sender := s
        receiver := v
        record := rec₀
        binding := beltRecordBinding dep.H rec₀
        macTag := computeBeltEchoMac dep.MAC (dep.macKeys s v) s v rec₀ })
  let pk := dep.validatorPk
  let gLeaf := UInt64.ofNat toyShamirIntent.leaf
  let digits := dep.digitsOf (quorumCounterDigest dep.H
    (quorumMessageHash dep.H pk gLeaf (intentCanonicalPayload dep.deploymentId toyShamirIntent)) 0)
  let digitsFn : Fin 1 → Fin 4 := fun i => digits.getD i.1 ⟨0, by decide⟩
  let leafChainPk : Fin 1 → Digest256 := fun i =>
    wotsChainIter (quorumChainStep dep.H pk.pkSeed gLeaf) i.1 0 3
      (quorumStageChainSk dep.H dep.masterSeed gLeaf (UInt32.ofNat i.1))
  let authPath := quorumAuthPath dep.H pk.pkSeed
    (quorumHonestLeafDigest 1 dep.H dep.masterSeed) dep.height 0 gLeaf.toNat
  let lambdas := lagrange2WeightsTower 7 (shamirPts4 p0) (shamirPts4 p1)
  let ops := [p0, p1].map (fun p =>
    computeShamirCustodianOpening dep.H dep.masterSeed dep.polyTape (dep.evalPts p)
      p toyShamirIntent 0 digitsFn)
  let sig := quorumJortsReferenceSign dep.H dep.masterSeed gLeaf 0 digits authPath
  let bound : BeltLatchNodeState :=
    { BeltLatchNodeState.init 2 2 with
      nextEpoch := 1, inFlight := some rec₀,
      disk := .persisted { nextEpoch := 1, inFlight := some rec₀ } }
  let trace : List (ShamirCustodyTurn 4 1) :=
    [ .belt (.honestBind p0 rec₀),
      .belt (.honestBind p1 rec₀),
      .belt (.honestBind p2 rec₀),
      .belt (.honestEmitEcho p0 p0),
      .belt (.honestEmitEcho p1 p0),
      .belt (.honestEmitEcho p2 p0),
      .belt (.honestEmitEcho p0 p1),
      .belt (.honestEmitEcho p1 p1),
      .belt (.honestEmitEcho p2 p1),
      .certifiedMint p0 0 Q3 rec₀ (echoesFor p0) burn₀,
      .certifiedMint p1 0 Q3 rec₀ (echoesFor p1) burn₀,
      .releaseShare p0 1 toyShamirIntent 0,
      .releaseShare p1 1 toyShamirIntent 0,
      .combineSig leafChainPk lambdas toyShamirIntent 0
        (assembleSubmittedSharesFromOpenings ops) authPath ]
  refine ⟨dep, trace, S2, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  dsimp only
  have hCert0 : checkLatchCertifiedBurn dep.H dep.MAC dep.macKeys dep.q dep.deploymentId p0 bound
      Q3 rec₀ (echoesFor p0) burn₀ = true :=
    checkLatchCertifiedBurn_finRange dep.H dep.MAC dep.macKeys dep.q dep.deploymentId p0 Q3 rec₀ burn₀
      (by decide +kernel) rfl rfl rfl
  have hCert1 : checkLatchCertifiedBurn dep.H dep.MAC dep.macKeys dep.q dep.deploymentId p1 bound
      Q3 rec₀ (echoesFor p1) burn₀ = true :=
    checkLatchCertifiedBurn_finRange dep.H dep.MAC dep.macKeys dep.q dep.deploymentId p1 Q3 rec₀ burn₀
      (by decide +kernel) rfl rfl rfl
  have hMG (j : Fin 4) : Custody.mintGuard (toyShamirPolicy toyShamirIntent) 100
      (Custody.initial (dep.vaultIdentity j)) burn₀ = true :=
    toy_mintGuard_initial toyShamirIntent _ rfl (List.cons_ne_nil _ _) rfl
      (show (10 : Nat) ≤ 100 by decide)
  have h2_16 : 0 < 2 ^ 16 := by decide
  have hComb := (shamir_custody_combined_sig_verifies_or_collision dep
    (by decide : dep.height < 256)
    (Nat.lt_trans (by decide : 32 * 1 < 64) pow256_8_gt_64_local)).1
    [p0, p1] lambdas toyShamirIntent 0 shamirPts4_lagrange01
    (by decide) two_pow_64_pos_local h2_16 rfl rfl
  have hBind0 : beltLatchBindStep (BeltLatchNodeState.init 2 2) rec₀ = .accepted bound .fresh :=
    beltLatchBindStep_init22_epoch0 rec₀ rfl
  have hC0 : dep.Corrupt.mem p0 = false := rfl
  have hC1 : dep.Corrupt.mem p1 = false := rfl
  obtain ⟨s0, hs0⟩ : ∃ s, s = ShamirCustodyNetworkState.init dep := ⟨_, rfl⟩
  have i0 (j : Fin 4) : s0.beltNet.nodes j = BeltLatchNodeState.init 2 2 := by rw [hs0]; rfl
  have hv0 (j : Fin 4) : s0.vaults j = Custody.initial (dep.vaultIdentity j) := by rw [hs0]; rfl
  have hr0 : s0.honestShareReleases = [] := by rw [hs0]; rfl
  have hc0 : s0.combinedSignatures = [] := by rw [hs0]; rfl
  -- Three honest latch binds.
  obtain ⟨s1, hs1⟩ : ∃ s, s = stepShamirCustody dep s0 (.belt (.honestBind p0 rec₀)) := ⟨_, rfl⟩
  have b1 := stepShamirCustody_belt_frame dep s0 (.honestBind p0 rec₀)
  rw [← hs1] at b1
  have n1_0 := stepShamirCustody_bind_fresh_node dep s0 p0 rec₀ bound hC0 (by rw [i0]; exact hBind0)
  have n1_1 := stepShamirCustody_bind_nodes_ne dep s0 p0 rec₀ p1 (by decide)
  rw [← hs1] at n1_0 n1_1
  obtain ⟨s2, hs2⟩ : ∃ s, s = stepShamirCustody dep s1 (.belt (.honestBind p1 rec₀)) := ⟨_, rfl⟩
  have b2 := stepShamirCustody_belt_frame dep s1 (.honestBind p1 rec₀)
  rw [← hs2] at b2
  have n2_1 := stepShamirCustody_bind_fresh_node dep s1 p1 rec₀ bound hC1
    (by rw [n1_1, i0]; exact hBind0)
  have n2_0 := stepShamirCustody_bind_nodes_ne dep s1 p1 rec₀ p0 (by decide)
  rw [← hs2] at n2_1 n2_0
  obtain ⟨s3, hs3⟩ : ∃ s, s = stepShamirCustody dep s2 (.belt (.honestBind p2 rec₀)) := ⟨_, rfl⟩
  have b3 := stepShamirCustody_belt_frame dep s2 (.honestBind p2 rec₀)
  rw [← hs3] at b3
  have n3_0 := stepShamirCustody_bind_nodes_ne dep s2 p2 rec₀ p0 (by decide)
  have n3_1 := stepShamirCustody_bind_nodes_ne dep s2 p2 rec₀ p1 (by decide)
  rw [← hs3] at n3_0 n3_1
  -- Six echo emissions (latch nodes unchanged).
  obtain ⟨s4, hs4⟩ : ∃ s, s = stepShamirCustody dep s3 (.belt (.honestEmitEcho p0 p0)) := ⟨_, rfl⟩
  have b4 := stepShamirCustody_belt_frame dep s3 (.honestEmitEcho p0 p0)
  rw [← hs4] at b4
  have e4 (j : Fin 4) : s4.beltNet.nodes j = s3.beltNet.nodes j := by
    rw [hs4]; exact stepShamirCustody_echo_nodes dep s3 p0 p0 j
  obtain ⟨s5, hs5⟩ : ∃ s, s = stepShamirCustody dep s4 (.belt (.honestEmitEcho p1 p0)) := ⟨_, rfl⟩
  have b5 := stepShamirCustody_belt_frame dep s4 (.honestEmitEcho p1 p0)
  rw [← hs5] at b5
  have e5 (j : Fin 4) : s5.beltNet.nodes j = s4.beltNet.nodes j := by
    rw [hs5]; exact stepShamirCustody_echo_nodes dep s4 p1 p0 j
  obtain ⟨s6, hs6⟩ : ∃ s, s = stepShamirCustody dep s5 (.belt (.honestEmitEcho p2 p0)) := ⟨_, rfl⟩
  have b6 := stepShamirCustody_belt_frame dep s5 (.honestEmitEcho p2 p0)
  rw [← hs6] at b6
  have e6 (j : Fin 4) : s6.beltNet.nodes j = s5.beltNet.nodes j := by
    rw [hs6]; exact stepShamirCustody_echo_nodes dep s5 p2 p0 j
  obtain ⟨s7, hs7⟩ : ∃ s, s = stepShamirCustody dep s6 (.belt (.honestEmitEcho p0 p1)) := ⟨_, rfl⟩
  have b7 := stepShamirCustody_belt_frame dep s6 (.honestEmitEcho p0 p1)
  rw [← hs7] at b7
  have e7 (j : Fin 4) : s7.beltNet.nodes j = s6.beltNet.nodes j := by
    rw [hs7]; exact stepShamirCustody_echo_nodes dep s6 p0 p1 j
  obtain ⟨s8, hs8⟩ : ∃ s, s = stepShamirCustody dep s7 (.belt (.honestEmitEcho p1 p1)) := ⟨_, rfl⟩
  have b8 := stepShamirCustody_belt_frame dep s7 (.honestEmitEcho p1 p1)
  rw [← hs8] at b8
  have e8 (j : Fin 4) : s8.beltNet.nodes j = s7.beltNet.nodes j := by
    rw [hs8]; exact stepShamirCustody_echo_nodes dep s7 p1 p1 j
  obtain ⟨s9, hs9⟩ : ∃ s, s = stepShamirCustody dep s8 (.belt (.honestEmitEcho p2 p1)) := ⟨_, rfl⟩
  have b9 := stepShamirCustody_belt_frame dep s8 (.honestEmitEcho p2 p1)
  rw [← hs9] at b9
  have e9 (j : Fin 4) : s9.beltNet.nodes j = s8.beltNet.nodes j := by
    rw [hs9]; exact stepShamirCustody_echo_nodes dep s8 p2 p1 j
  have n9_0 : s9.beltNet.nodes p0 = bound := by
    rw [e9, e8, e7, e6, e5, e4, n3_0, n2_0, n1_0]
  have n9_1 : s9.beltNet.nodes p1 = bound := by
    rw [e9, e8, e7, e6, e5, e4, n3_1, n2_1]
  have v9 (j : Fin 4) : s9.vaults j = Custody.initial (dep.vaultIdentity j) := by
    rw [b9.1, b8.1, b7.1, b6.1, b5.1, b4.1, b3.1, b2.1, b1.1, hv0]
  have r9 : s9.honestShareReleases = [] := by
    rw [b9.2.1, b8.2.1, b7.2.1, b6.2.1, b5.2.1, b4.2.1, b3.2.1, b2.2.1, b1.2.1, hr0]
  have c9 : s9.combinedSignatures = [] := by
    rw [b9.2.2, b8.2.2, b7.2.2, b6.2.2, b5.2.2, b4.2.2, b3.2.2, b2.2.2, b1.2.2, hc0]
  have hPol (j : Fin 4) : dep.policies j = toyShamirPolicy toyShamirIntent := rfl
  have hCap (j : Fin 4) : dep.caps j = 100 := rfl
  have hOk (j : Fin 4) :=
    custody_mint_initial_ok (toyShamirPolicy toyShamirIntent) 100 burn₀ (dep.vaultIdentity j) (hMG j)
  -- Two certified mints into the initial vaults.
  obtain ⟨s10, hs10⟩ : ∃ s, s = stepShamirCustody dep s9 (.certifiedMint p0 0 Q3 rec₀ (echoesFor p0) burn₀) := ⟨_, rfl⟩
  have m10 := stepShamirCustody_certifiedMint_ok dep s9 p0 0 Q3 rec₀ (echoesFor p0) burn₀ hC0
    (by rw [n9_0]; exact hCert0)
  rw [← hs10] at m10
  obtain ⟨m10_net, m10_rel, m10_comb, m10_v, m10_frame⟩ := m10
  rw [v9, hPol, hCap] at m10_v
  obtain ⟨s11, hs11⟩ : ∃ s, s = stepShamirCustody dep s10 (.certifiedMint p1 0 Q3 rec₀ (echoesFor p1) burn₀) := ⟨_, rfl⟩
  have m11 := stepShamirCustody_certifiedMint_ok dep s10 p1 0 Q3 rec₀ (echoesFor p1) burn₀ hC1
    (by rw [m10_net, n9_1]; exact hCert1)
  rw [← hs11] at m11
  obtain ⟨_, m11_rel, m11_comb, m11_v, m11_frame⟩ := m11
  rw [m10_frame p1 (by decide), v9, hPol, hCap] at m11_v
  have v11_0 : s11.vaults p0 =
      Custody.mint (toyShamirPolicy toyShamirIntent) 100 0 (Custody.initial (dep.vaultIdentity p0))
        burn₀ := by
    rw [m11_frame p0 (by decide), m10_v]
  -- Two share releases and the combination.
  obtain ⟨s12, hs12⟩ : ∃ s, s = stepShamirCustody dep s11 (.releaseShare p0 1 toyShamirIntent 0) := ⟨_, rfl⟩
  have r12 := stepShamirCustody_releaseShare_ok dep s11 p0 1 toyShamirIntent 0 hC0
    (by rw [v11_0]; exact (hOk p0).1) (by rw [v11_0]; exact (hOk p0).2.1)
    (by rw [v11_0]; exact (hOk p0).2.2)
  rw [← hs12] at r12
  obtain ⟨_, r12_comb, r12_rel, r12_frame⟩ := r12
  have v12_1 : s12.vaults p1 =
      Custody.mint (toyShamirPolicy toyShamirIntent) 100 0 (Custody.initial (dep.vaultIdentity p1))
        burn₀ := by
    rw [r12_frame p1 (by decide), m11_v]
  obtain ⟨s13, hs13⟩ : ∃ s, s = stepShamirCustody dep s12 (.releaseShare p1 1 toyShamirIntent 0) := ⟨_, rfl⟩
  have r13 := stepShamirCustody_releaseShare_ok dep s12 p1 1 toyShamirIntent 0 hC1
    (by rw [v12_1]; exact (hOk p1).1) (by rw [v12_1]; exact (hOk p1).2.1)
    (by rw [v12_1]; exact (hOk p1).2.2)
  rw [← hs13] at r13
  obtain ⟨_, r13_comb, r13_rel, _⟩ := r13
  obtain ⟨s14, hs14⟩ : ∃ s, s = stepShamirCustody dep s13 (.combineSig leafChainPk lambdas toyShamirIntent 0
    (assembleSubmittedSharesFromOpenings ops) authPath) := ⟨_, rfl⟩
  have c14 := stepShamirCustody_combineSig_some dep s13 leafChainPk lambdas toyShamirIntent 0
    (assembleSubmittedSharesFromOpenings ops) authPath sig hComb.1
  rw [← hs14] at c14
  obtain ⟨c14_comb, c14_rel⟩ := c14
  have hRelLen : s14.honestShareReleases.map (fun op => (op.party, op.intent)) =
      [(p1, toyShamirIntent), (p0, toyShamirIntent)] := by
    rw [c14_rel, r13_rel, r12_rel, m11_rel, m10_rel, r9]
    rfl
  have hCombEq : s14.combinedSignatures = [(toyShamirIntent, sig)] := by
    rw [c14_comb, r13_comb, r12_comb, m11_comb, m10_comb, c9]
  -- The executed trace ends in `s14`.
  have hRun : runShamirCustodyTrace dep
      (ShamirCustodyNetworkState.init dep) trace = s14 := by
    rw [hs14, hs13, hs12, hs11, hs10, hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, hs0]
    rfl
  rw [hRun]
  refine ⟨?_, ?_, ?_⟩
  · intro p hpS hpHon
    have hp01 : p = p0 ∨ p = p1 := by
      rcases p with ⟨val, isLt⟩
      have hLt2 : val < 2 := of_decide_eq_true hpS
      have hCases : val = 0 ∨ val = 1 := by omega
      rcases hCases with rfl | rfl
      · exact .inl rfl
      · exact .inr rfl
    have hMemMap : (p, toyShamirIntent) ∈ s14.honestShareReleases.map (fun op => (op.party, op.intent)) := by
      rw [hRelLen]
      rcases hp01 with rfl | rfl
      · exact .tail _ (.head _)
      · exact .head _
    obtain ⟨op, hOpMem, hPair⟩ := List.mem_map.mp hMemMap
    exact ⟨op, hOpMem, (Prod.mk.inj hPair).1, (Prod.mk.inj hPair).2⟩
  · rw [hCombEq]; rfl
  · intro entry hMem
    rw [hCombEq] at hMem
    rcases List.mem_singleton.mp hMem with rfl
    exact hComb.2

/-- **`#tooth` Mutation 1 (`tooth_under_quorum_latch_allows_shamir_equivocation`):**
    Weakening the `BeltLatch` quorum bound from `2 * q > n + f` (`q = 3`) to `2 * q ≤ n + f`
    (`q = 2` on `n = 4, t = 2, f = 1`) while keeping `f < t` (`1 < 2`), ZERO MAC forgeries, and
    ZERO hash collisions allows two disjoint honest custodians `p₀` (`Q₁ = {p₀, p₃}`) and `p₁`
    (`Q₂ = {p₁, p₃}`) to certify, mint, and release Shamir shares for **two distinct intents
    `r₁ ≠ r₂` at the same leaf epoch `0`**! -/
theorem tooth_under_quorum_latch_allows_shamir_equivocation :
    ∃ (dep : ShamirValidatorDeployment 4 1 1)
      (r₁ r₂ : Custody.Intent)
      (S₁ S₂ : CustodiansMask 4)
      (trace : List (ShamirCustodyTurn 4 1)),
      -- f < t still holds (1 < 2), ONLY 2 * q > n + f is weakened to 2 * 2 ≤ 4 + 1:
      maskCard dep.Corrupt = 1 ∧
      dep.f = 1 ∧ dep.t = 2 ∧ dep.q = 2 ∧
      2 * dep.q ≤ 4 + dep.f ∧
      dep.f < dep.t ∧
      dep.t ≤ maskCard S₁ ∧
      dep.t ≤ maskCard S₂ ∧
      r₁.leaf = 0 ∧ r₂.leaf = 0 ∧ r₁ ≠ r₂ ∧
      let st := runShamirCustodyTrace dep (ShamirCustodyNetworkState.init dep) trace
      -- Zero MAC forgeries on honest pairs and distinct message digests (zero hash collision):
      dep.H (intentCanonicalPayload dep.deploymentId r₁) ≠ dep.H (intentCanonicalPayload dep.deploymentId r₂) ∧
      HonestQuorumReleasedIntent dep.Corrupt st S₁ r₁ ∧
      HonestQuorumReleasedIntent dep.Corrupt st S₂ r₂ := by
  let r₁ : Custody.Intent := { session := 1, round := 0, leaf := 0, spend := 10, message := [0x01] }
  let r₂ : Custody.Intent := { session := 2, round := 0, leaf := 0, spend := 10, message := [0x20] }
  let polByParty : Fin 4 → Custody.RoundPolicy
    | ⟨0, _⟩ => toyShamirPolicy r₁
    | ⟨1, _⟩ => toyShamirPolicy r₂
    | _ => toyShamirPolicy r₁
  let dep : ShamirValidatorDeployment 4 1 1 :=
    { toyShamirDeployment with
      q := 2
      policies := polByParty }
  let p0 : Fin 4 := ⟨0, by decide⟩
  let p1 : Fin 4 := ⟨1, by decide⟩
  let S₁ : CustodiansMask 4 := ⟨fun i => decide (i.val = 0 ∨ i.val = 3)⟩
  let S₂ : CustodiansMask 4 := ⟨fun i => decide (i.val = 1 ∨ i.val = 3)⟩
  let rec₁ : BeltLatchRecord :=
    { epoch := 0, msgDigest := dep.H (intentCanonicalPayload dep.deploymentId r₁), retrySalt := 0#256, targetSumDigits := [2] }
  let rec₂ : BeltLatchRecord :=
    { epoch := 0, msgDigest := dep.H (intentCanonicalPayload dep.deploymentId r₂), retrySalt := 0#256, targetSumDigits := [2] }
  let burn₁ : Custody.Burn :=
    { intent := r₁, digest := Custody.roundCommitment toyDeploymentId r₁, openings := [toyShamirOpening r₁] }
  let burn₂ : Custody.Burn :=
    { intent := r₂, digest := Custody.roundCommitment toyDeploymentId r₂, openings := [toyShamirOpening r₂] }
  let echoes₁ : List (AuthenticatedBeltEcho 4) :=
    (List.finRange 4).map (fun s =>
      { sender := s, receiver := p0, record := rec₁,
        binding := beltRecordBinding dep.H rec₁,
        macTag := computeBeltEchoMac dep.MAC (dep.macKeys s p0) s p0 rec₁ })
  let echoes₂ : List (AuthenticatedBeltEcho 4) :=
    (List.finRange 4).map (fun s =>
      { sender := s, receiver := p1, record := rec₂,
        binding := beltRecordBinding dep.H rec₂,
        macTag := computeBeltEchoMac dep.MAC (dep.macKeys s p1) s p1 rec₂ })
  let trace : List (ShamirCustodyTurn 4 1) :=
    [ .belt (.honestBind p0 rec₁),
      .belt (.honestEmitEcho p0 p0),
      .certifiedMint p0 0 S₁ rec₁ echoes₁ burn₁,
      .releaseShare p0 1 r₁ 0,
      .belt (.honestBind p1 rec₂),
      .belt (.honestEmitEcho p1 p1),
      .certifiedMint p1 0 S₂ rec₂ echoes₂ burn₂,
      .releaseShare p1 1 r₂ 0 ]
  refine ⟨dep, r₁, r₂, S₁, S₂, trace,
    by decide +kernel, rfl, rfl, rfl, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, rfl, rfl, by decide +kernel, ?_⟩
  dsimp only
  have hDigNe : dep.H (intentCanonicalPayload dep.deploymentId r₁) ≠ dep.H (intentCanonicalPayload dep.deploymentId r₂) := by
    have hMem1 : decide ((0x20 : UInt8) ∈ intentCanonicalPayload toyDeploymentId r₁) = false := by
      decide +kernel
    have hMem2 : decide ((0x20 : UInt8) ∈ intentCanonicalPayload toyDeploymentId r₂) = true := by
      decide +kernel
    have h1 : dep.H (intentCanonicalPayload dep.deploymentId r₁) = 0#256 := by
      dsimp only [dep, toyShamirDeployment]
      rw [ite_eq_right_iff]
      intro hIn; exact absurd (decide_eq_true hIn) (by rw [hMem1]; decide)
    have h2 : dep.H (intentCanonicalPayload dep.deploymentId r₂) = 1#256 := by
      dsimp only [dep, toyShamirDeployment]
      rw [ite_eq_left_iff]
      intro hNotIn; exact absurd (of_decide_eq_true hMem2) hNotIn
    rw [h1, h2]
    intro hEq
    have hNat := congrArg BitVec.toNat hEq
    simp at hNat
  let bound₁ : BeltLatchNodeState :=
    { BeltLatchNodeState.init 2 2 with
      nextEpoch := 1, inFlight := some rec₁,
      disk := .persisted { nextEpoch := 1, inFlight := some rec₁ } }
  let bound₂ : BeltLatchNodeState :=
    { BeltLatchNodeState.init 2 2 with
      nextEpoch := 1, inFlight := some rec₂,
      disk := .persisted { nextEpoch := 1, inFlight := some rec₂ } }
  have hCert0 : checkLatchCertifiedBurn dep.H dep.MAC dep.macKeys dep.q dep.deploymentId p0 bound₁
      S₁ rec₁ echoes₁ burn₁ = true :=
    checkLatchCertifiedBurn_finRange dep.H dep.MAC dep.macKeys dep.q dep.deploymentId p0 S₁ rec₁ burn₁
      (by decide +kernel) rfl rfl rfl
  have hCert1 : checkLatchCertifiedBurn dep.H dep.MAC dep.macKeys dep.q dep.deploymentId p1 bound₂
      S₂ rec₂ echoes₂ burn₂ = true :=
    checkLatchCertifiedBurn_finRange dep.H dep.MAC dep.macKeys dep.q dep.deploymentId p1 S₂ rec₂ burn₂
      (by decide +kernel) rfl rfl rfl
  have hMG1 : Custody.mintGuard (toyShamirPolicy r₁) 100
      (Custody.initial (dep.vaultIdentity p0)) burn₁ = true :=
    toy_mintGuard_initial r₁ _ rfl (List.cons_ne_nil _ _) rfl (show (10 : Nat) ≤ 100 by decide)
  have hMG2 : Custody.mintGuard (toyShamirPolicy r₂) 100
      (Custody.initial (dep.vaultIdentity p1)) burn₂ = true :=
    toy_mintGuard_initial r₂ _ rfl (List.cons_ne_nil _ _) rfl (show (10 : Nat) ≤ 100 by decide)
  have hB1 : beltLatchBindStep (BeltLatchNodeState.init 2 2) rec₁ = .accepted bound₁ .fresh :=
    beltLatchBindStep_init22_epoch0 rec₁ rfl
  have hB2 : beltLatchBindStep (BeltLatchNodeState.init 2 2) rec₂ = .accepted bound₂ .fresh :=
    beltLatchBindStep_init22_epoch0 rec₂ rfl
  have hC0 : dep.Corrupt.mem p0 = false := rfl
  have hC1 : dep.Corrupt.mem p1 = false := rfl
  obtain ⟨s0, hs0⟩ : ∃ s, s = ShamirCustodyNetworkState.init dep := ⟨_, rfl⟩
  have i0 (j : Fin 4) : s0.beltNet.nodes j = BeltLatchNodeState.init 2 2 := by rw [hs0]; rfl
  have hv0 (j : Fin 4) : s0.vaults j = Custody.initial (dep.vaultIdentity j) := by rw [hs0]; rfl
  have hr0 : s0.honestShareReleases = [] := by rw [hs0]; rfl
  -- Custodian `p0`: bind, echo, certified mint under `S₁`, release for `r₁`.
  obtain ⟨s1, hs1⟩ : ∃ s, s = stepShamirCustody dep s0 (.belt (.honestBind p0 rec₁)) := ⟨_, rfl⟩
  have b1 := stepShamirCustody_belt_frame dep s0 (.honestBind p0 rec₁)
  rw [← hs1] at b1
  have n1_0 := stepShamirCustody_bind_fresh_node dep s0 p0 rec₁ bound₁ hC0 (by rw [i0]; exact hB1)
  have n1_1 := stepShamirCustody_bind_nodes_ne dep s0 p0 rec₁ p1 (by decide)
  rw [← hs1] at n1_0 n1_1
  obtain ⟨s2, hs2⟩ : ∃ s, s = stepShamirCustody dep s1 (.belt (.honestEmitEcho p0 p0)) := ⟨_, rfl⟩
  have b2 := stepShamirCustody_belt_frame dep s1 (.honestEmitEcho p0 p0)
  rw [← hs2] at b2
  have e2 (j : Fin 4) : s2.beltNet.nodes j = s1.beltNet.nodes j := by
    rw [hs2]; exact stepShamirCustody_echo_nodes dep s1 p0 p0 j
  obtain ⟨s3, hs3⟩ : ∃ s, s = stepShamirCustody dep s2 (.certifiedMint p0 0 S₁ rec₁ echoes₁ burn₁) := ⟨_, rfl⟩
  have m3 := stepShamirCustody_certifiedMint_ok dep s2 p0 0 S₁ rec₁ echoes₁ burn₁ hC0
    (by rw [e2, n1_0]; exact hCert0)
  rw [← hs3] at m3
  obtain ⟨m3_net, m3_rel, _, m3_v, m3_frame⟩ := m3
  have hPol0 : dep.policies p0 = toyShamirPolicy r₁ := rfl
  have hPol1 : dep.policies p1 = toyShamirPolicy r₂ := rfl
  have hCap (j : Fin 4) : dep.caps j = 100 := rfl
  rw [b2.1, b1.1, hv0, hPol0, hCap] at m3_v
  obtain ⟨hPois1, hAnch1, hActive1⟩ := custody_mint_initial_ok (toyShamirPolicy r₁) 100 burn₁ (dep.vaultIdentity p0) hMG1
  obtain ⟨s4, hs4⟩ : ∃ s, s = stepShamirCustody dep s3 (.releaseShare p0 1 r₁ 0) := ⟨_, rfl⟩
  have r4 := stepShamirCustody_releaseShare_ok dep s3 p0 1 r₁ 0 hC0
    (by rw [m3_v]; exact hPois1) (by rw [m3_v]; exact hAnch1) (by rw [m3_v]; exact hActive1)
  rw [← hs4] at r4
  obtain ⟨r4_net, _, r4_rel, r4_frame⟩ := r4
  -- Custodian `p1`: bind, echo, certified mint under `S₂`, release for `r₂`.
  obtain ⟨s5, hs5⟩ : ∃ s, s = stepShamirCustody dep s4 (.belt (.honestBind p1 rec₂)) := ⟨_, rfl⟩
  have b5 := stepShamirCustody_belt_frame dep s4 (.honestBind p1 rec₂)
  rw [← hs5] at b5
  have n5_1 := stepShamirCustody_bind_fresh_node dep s4 p1 rec₂ bound₂ hC1
    (by rw [r4_net, m3_net, e2, n1_1, i0]; exact hB2)
  rw [← hs5] at n5_1
  obtain ⟨s6, hs6⟩ : ∃ s, s = stepShamirCustody dep s5 (.belt (.honestEmitEcho p1 p1)) := ⟨_, rfl⟩
  have b6 := stepShamirCustody_belt_frame dep s5 (.honestEmitEcho p1 p1)
  rw [← hs6] at b6
  have e6 (j : Fin 4) : s6.beltNet.nodes j = s5.beltNet.nodes j := by
    rw [hs6]; exact stepShamirCustody_echo_nodes dep s5 p1 p1 j
  obtain ⟨s7, hs7⟩ : ∃ s, s = stepShamirCustody dep s6 (.certifiedMint p1 0 S₂ rec₂ echoes₂ burn₂) := ⟨_, rfl⟩
  have m7 := stepShamirCustody_certifiedMint_ok dep s6 p1 0 S₂ rec₂ echoes₂ burn₂ hC1
    (by rw [e6, n5_1]; exact hCert1)
  rw [← hs7] at m7
  obtain ⟨_, m7_rel, _, m7_v, _⟩ := m7
  rw [b6.1, b5.1, r4_frame p1 (by decide), m3_frame p1 (by decide), b2.1, b1.1, hv0, hPol1, hCap]
    at m7_v
  obtain ⟨hPois2, hAnch2, hActive2⟩ := custody_mint_initial_ok (toyShamirPolicy r₂) 100 burn₂ (dep.vaultIdentity p1) hMG2
  obtain ⟨s8, hs8⟩ : ∃ s, s = stepShamirCustody dep s7 (.releaseShare p1 1 r₂ 0) := ⟨_, rfl⟩
  have r8 := stepShamirCustody_releaseShare_ok dep s7 p1 1 r₂ 0 hC1
    (by rw [m7_v]; exact hPois2) (by rw [m7_v]; exact hAnch2) (by rw [m7_v]; exact hActive2)
  rw [← hs8] at r8
  obtain ⟨_, _, r8_rel, _⟩ := r8
  have hRelPairs : s8.honestShareReleases.map (fun op => (op.party, op.intent)) =
      [(p1, r₂), (p0, r₁)] := by
    rw [r8_rel, m7_rel, b6.2.1, b5.2.1, r4_rel, m3_rel, b2.2.1, b1.2.1, hr0]
    rfl
  -- The executed trace ends in `s8`.
  have hRun : runShamirCustodyTrace dep
      (ShamirCustodyNetworkState.init dep) trace = s8 := by
    rw [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, hs0]
    rfl
  rw [hRun]
  refine ⟨hDigNe, ?_, ?_⟩
  · intro p hpS₁ hpHon
    have hpEq0 : p = p0 := by
      rcases p with ⟨val, isLt⟩
      rcases of_decide_eq_true hpS₁ with rfl | rfl
      · rfl
      · cases hpHon
    subst hpEq0
    have hMemMap : (p0, r₁) ∈ s8.honestShareReleases.map (fun op => (op.party, op.intent)) := by
      rw [hRelPairs]; exact .tail _ (.head _)
    obtain ⟨op, hOpMem, hPair⟩ := List.mem_map.mp hMemMap
    exact ⟨op, hOpMem, (Prod.mk.inj hPair).1, (Prod.mk.inj hPair).2⟩
  · intro p hpS₂ hpHon
    have hpEq1 : p = p1 := by
      rcases p with ⟨val, isLt⟩
      rcases of_decide_eq_true hpS₂ with rfl | rfl
      · rfl
      · cases hpHon
    subst hpEq1
    have hMemMap : (p1, r₂) ∈ s8.honestShareReleases.map (fun op => (op.party, op.intent)) := by
      rw [hRelPairs]; exact .head _
    obtain ⟨op, hOpMem, hPair⟩ := List.mem_map.mp hMemMap
    exact ⟨op, hOpMem, (Prod.mk.inj hPair).1, (Prod.mk.inj hPair).2⟩

/-- **`#tooth` Mutation 2 (`tooth_unverified_lagrange_corrupt_share_forges_node`):**
    Omitting the MAC-free WOTS+C endpoint self-verification check in Lagrange combination allows
    a single corrupted share at `x₁ = towerX 7` to shift `ringDot lambdas` away from the honest
    secret `c₀` while `preSteppedDigest256ReconstructAndSelfVerify` rejects it (`= none`). -/
theorem tooth_unverified_lagrange_corrupt_share_forges_node :
    ¬ (ringDot (lagrange2WeightsTower 7 (towerOne 7) (towerX 7))
        [RoundPoly.evalCoeffs [towerOne 7, towerZero 7] (towerOne 7),
         towerAdd 7 (RoundPoly.evalCoeffs [towerOne 7, towerZero 7] (towerX 7)) (towerX 7)] =
      towerOne 7) := by
  intro hEq'
  let x₀ := towerOne 7
  let x₁ := towerX 7
  let lambdas := lagrange2WeightsTower 7 x₀ x₁
  let s₀ := RoundPoly.evalCoeffs [towerOne 7, towerZero 7] x₀
  let s₁_corrupt := towerAdd 7 (RoundPoly.evalCoeffs [towerOne 7, towerZero 7] x₁) (towerX 7)
  have hEq : ringDot lambdas [s₀, s₁_corrupt] = towerOne 7 := hEq'
  have hHon : ringDot lambdas
      [RoundPoly.evalCoeffs [towerOne 7, towerZero 7] x₀,
       RoundPoly.evalCoeffs [towerOne 7, towerZero 7] x₁] = towerOne 7 :=
    lagrange2WeightsTower_eval 7 (towerOne_ne_towerX 6) (towerOne 7) ⟨[towerZero 7], rfl⟩
  let denom := towerInv 7 (towerAdd 7 x₀ x₁)
  have hDiff : towerMul 7 (towerMul 7 x₀ denom) (towerX 7) = towerZero 7 := by
    have hSub : towerAdd 7 (ringDot lambdas [s₀, s₁_corrupt])
        (ringDot lambdas [s₀, RoundPoly.evalCoeffs [towerOne 7, towerZero 7] x₁]) = towerZero 7 := by
      rw [hEq, hHon]
      exact towerAdd_self_zero 7 (towerOne 7)
    dsimp only [lambdas, lagrange2WeightsTower, s₁_corrupt] at hSub
    simp only [ringDot_eq, dotVec_cons, dotVec_nil_left] at hSub
    dsimp only [CommRingOps.add, CommRingOps.mul, CommRingOps.zero] at hSub
    simp only [towerAdd_zero] at hSub
    rw [towerMul_add_distrib] at hSub
    have hCancel : ∀ (a b c : TowerElem 7),
        towerAdd 7 (towerAdd 7 a (towerAdd 7 b c)) (towerAdd 7 a b) = c := fun a b c => by
      calc towerAdd 7 (towerAdd 7 a (towerAdd 7 b c)) (towerAdd 7 a b)
          = towerAdd 7 (towerAdd 7 (towerAdd 7 a b) c) (towerAdd 7 a b) := by
              rw [towerAdd_assoc 7 a b c]
        _ = towerAdd 7 (towerAdd 7 c (towerAdd 7 a b)) (towerAdd 7 a b) := by
              rw [towerAdd_comm 7 (towerAdd 7 a b) c]
        _ = towerAdd 7 c (towerAdd 7 (towerAdd 7 a b) (towerAdd 7 a b)) :=
              towerAdd_assoc 7 c _ _
        _ = towerAdd 7 c (towerZero 7) := by rw [towerAdd_self_zero]
        _ = c := towerAdd_zero 7 c
    rw [hCancel] at hSub
    exact hSub
  have hx₀Nz : x₀ ≠ towerZero 7 := towerOne_ne_zero 7
  have hLam₁Nz : towerMul 7 x₀ denom ≠ towerZero 7 := by
    have hNeSymm : x₁ ≠ x₀ := fun h => (towerOne_ne_towerX 6) h.symm
    have hHead := lagrange2HeadWeight_ne_zero 7 hNeSymm hx₀Nz
    rw [towerAdd_comm 7 x₁ x₀] at hHead
    exact hHead
  have hx₁Nz : towerX 7 ≠ towerZero 7 := by
    intro hZ
    exact towerOne_ne_zero 6 (congrArg Prod.snd hZ)
  rcases (towerMul_eq_zero_iff 7 _ (towerX 7)).mp hDiff with h1 | h2
  · exact hLam₁Nz h1
  · exact hx₁Nz h2

/-! ## 2. `ShamirValidatorDeployment.WellFormed`: witness and teeth -/

theorem shamirPts4_nonzero : ∀ p : Fin 4, ¬ (shamirPts4 p = CommRingOps.zero) := by
  decide +kernel

theorem shamirPts4_injective : ∀ p q : Fin 4, shamirPts4 p = shamirPts4 q → p = q := by
  decide +kernel

/-- The toy `(n = 4, t = 2, f = 1, q = 3)` deployment is well-formed. -/
theorem toyShamirDeployment_wellFormed : toyShamirDeployment.WellFormed where
  evalPts_nonzero := shamirPts4_nonzero
  evalPts_injective := shamirPts4_injective
  threshold_degree := rfl
  threshold_le := by decide
  corrupt_le := by decide +kernel
  f_lt_threshold := by decide
  latch_quorum := by decide

/-- The toy deployment with every custodian at the evaluation point `1`. -/
def toyShamirDeploymentDuplicatePoints : ShamirValidatorDeployment 4 1 1 :=
  { toyShamirDeployment with evalPts := fun _ => towerOne 7 }

/-- Tooth for `evalPts_injective`: with repeated evaluation points the Lagrange weights of two
    custodians do not reconstruct the constant term of `1 + X`. -/
theorem tooth_duplicate_points_do_not_reconstruct :
    ¬ (ringDot (toyShamirDeploymentDuplicatePoints.lagrangeWeights [⟨0, by decide⟩, ⟨1, by decide⟩])
        (([(⟨0, by decide⟩ : Fin 4), ⟨1, by decide⟩].map
            toyShamirDeploymentDuplicatePoints.evalPts).map
          (fun x => RoundPoly.evalCoeffs [towerOne 7, towerOne 7] x)) = towerOne 7) := by
  decide +kernel

/-- Tooth for `evalPts_nonzero`: a custodian at the evaluation point `0` holds the shared value
    itself, so its share separates the values `1` and `0` whatever the other coefficients. -/
theorem tooth_zero_point_share_is_the_secret (tail tail' : List (TowerElem 7)) :
    ¬ (RoundPoly.evalCoeffs ((CommRingOps.one : TowerElem 7) :: tail') CommRingOps.zero =
        RoundPoly.evalCoeffs ((CommRingOps.zero : TowerElem 7) :: tail) CommRingOps.zero) := by
  rw [RoundPoly.evalCoeffs_cons, RoundPoly.evalCoeffs_cons, LawfulCommRing.zero_mul,
    LawfulCommRing.zero_mul, LawfulCommRing.add_zero, LawfulCommRing.add_zero]
  exact LawfulField.one_ne_zero

/-- The share-secrecy theorem applies to the toy deployment and its corrupted custodian `3`. -/
theorem toyShamirDeployment_corrupt_share_secrecy (w : TowerElem 7) :
    ∃ e : SimpleEquiv (ShamirPadPoly (TowerElem 7) 2) (ShamirPadPoly (TowerElem 7) 2),
      ∀ P : ShamirPadPoly (TowerElem 7) 2,
        RoundPoly.evalCoeffs (e.toFun P).1 CommRingOps.zero =
          CommRingOps.add w (RoundPoly.evalCoeffs P.1 CommRingOps.zero) ∧
        ∀ p : Fin 4, p ∈ [(⟨3, by decide⟩ : Fin 4)] →
          RoundPoly.evalCoeffs (e.toFun P).1 (toyShamirDeployment.evalPts p) =
            RoundPoly.evalCoeffs P.1 (toyShamirDeployment.evalPts p) :=
  toyShamirDeployment_wellFormed.corrupt_shares_independent_of_secret [⟨3, by decide⟩]
    (by decide) w

/-! ## 3. Lagrange completeness of well-formed deployments

Proved here against the unfolded definition of `lagrangeToAdditiveShare`; the same proofs move to
`Qsag.Custody.ShamirThresholdCustodyRefinement` with the exported defining equation
`lagrangeToAdditiveShare_eq` of `Qsag.Protocol.Threshold.ParametricThresholdAndUnlinkableQsa`. -/

/-- Lagrange completeness on the toy deployment: every pair of distinct custodians reconstructs
    the constant term of every degree-1 sharing polynomial with `lagrangeWeights`. -/
theorem toyShamirDeployment_pairs_reconstruct (c₀ : TowerElem 7)
    (tail : ShamirPadPoly (TowerElem 7) 1) (p q : Fin 4) (h : p ≠ q) :
    ringDot (toyShamirDeployment.lagrangeWeights [p, q])
      (([p, q].map toyShamirDeployment.evalPts).map
        (fun x => RoundPoly.evalCoeffs (c₀ :: tail.1) x)) = c₀ :=
  wellFormed_lagrange_reconstructs toyShamirDeployment_wellFormed [p, q]
    (List.nodup_cons.mpr ⟨fun hm => h (List.mem_singleton.mp hm),
      List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩⟩)
    (show (2 : Nat) ≤ 2 from Nat.le_refl 2) c₀ tail

#verify_constructive Qsag.wellFormed_lagrange_reconstructs
#verify_constructive Qsag.shamir_custody_wellFormed_quorum_signs
#verify_constructive Qsag.shamir_custody_wellFormed_quorum_invariance
#verify_constructive Qsag.toyShamirDeployment_pairs_reconstruct
#tooth_pair Qsag.wellFormed_lagrange_reconstructs vs Qsag.tooth_duplicate_points_do_not_reconstruct

#verify_constructive Qsag.toyShamirDeployment_wellFormed
#verify_constructive Qsag.tooth_duplicate_points_do_not_reconstruct
#verify_constructive Qsag.tooth_zero_point_share_is_the_secret
#verify_constructive Qsag.toyShamirDeployment_corrupt_share_secrecy
#tooth_pair Qsag.ShamirValidatorDeployment.WellFormed.corrupt_shares_independent_of_secret vs
  Qsag.tooth_zero_point_share_is_the_secret
#verify_constructive Qsag.witness_shamir_custody_nonvacuous
#verify_inhabited Qsag.shamir_custody_epoch_non_equivocation Qsag.witness_shamir_custody_nonvacuous
#tooth_pair Qsag.shamir_custody_epoch_non_equivocation vs Qsag.tooth_under_quorum_latch_allows_shamir_equivocation
#tooth_pair Qsag.shamir_custody_combined_sig_verifies_or_collision vs Qsag.tooth_unverified_lagrange_corrupt_share_forges_node

end Qsag
