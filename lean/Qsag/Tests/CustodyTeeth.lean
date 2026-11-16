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
