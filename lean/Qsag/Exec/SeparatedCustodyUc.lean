module
public import Qsag.Protocol.Threshold.ThresholdApproval
public import Qsag.Protocol.Threshold.IdealTsig
public import Qsag.Custody.SeparatedCustody
public import Qsag.Exec.IdealOutputBoundary
public import Qsag.Exec.PosixCrashWal
import all Qsag.Protocol.Threshold.IdealTsig
import all Qsag.Protocol.Signing.HashSigs
import all Qsag.Exec.PosixCrashWal
import all Qsag.Custody.SeparatedCustody
import all Qsag.Exec.InteractiveUcEngine
import Qsag.Tactic.AssuranceKit

/-
# Qsag.Exec.SeparatedCustodyUc — Coherent Custody, Threshold UC, and Crash-WAL Bridges

Execution-level module: it relates the custody coordinator to runs of the interactive UC engine
(`SessionScheduleReq`, `WalLatchState`) and of the POSIX crash WAL, so it lives under `Exec/`.

Constructive refinement and composition bridges unifying five specifications that previously
operated over separate state carriers:

1. **Authenticated Custody Quorum → `ThresholdApproval` / `IdealTsig` / `InteractiveUcEngine`**:
   Maps an accepted `Custody.submitRecorded` certificate quorum (`SeparatedCustodyHistory`) to an
   explicit honest-approver list satisfying `validThresholdApproval` (`ThresholdApproval`,
   `IdealTsig.execIdealTsig`, and `InteractiveUcEngine`), while constructively carrying forward
   either prior policy-admitted `CompleteMediationBoundary` provenance (`ProducedPolicyApproval`)
   or a concrete `prodEufCmaWin` / hash-break witness on an honest custodian's one-time log.
2. **Party-Local Custody Roster → `RealClusterState` Share Projection & Quarantine Erasure**:
   Replaces coordinator-owned global share maps with an isolated party-local custody roster
   pairing `HonestCustodyVault` and `Custody.PolicyVault`, proving corrupt indices never appear in
   the projected honest share map and local quarantine wipes secret material without cross-party
   interference.
3. **Grounded `MatchesKey` + Non-Hiding Stateful/Stateless Production Signing Release**:
   Derives `MatchesKey` and `enrolledPk` directly from well-formed RSS shares (`ThresholdMpc`),
   supports both `statefulJorts = true` (binding `req.reqEpoch`) and `statefulJorts = false` over
   the full framed `encodeUcSigningRequest`, and maps signing/encoding failures to explicit
   `PSum.inl .activeConsistencyFailed` abort + WAL quarantine rather than `Option`-hiding `ByteArray`
   serializers.
4. **Crash-Consistent `PosixCrashWal` + `ExternalMonotoneAnchor` ↔ `WalLatchState` & `Custody.Ledger`**:
   Connects `InteractiveUcEngine.WalLatchState` (`walPreSignStep`, `walCommitBeforeRelease`,
   `walQuarantine`) and `CompleteMediationBoundary` watermarks (`nextLeaf`, `nextRound`, `spent`)
   to `PosixCrashWal` (`LockedVaultHandle`, `WalRecord`, `VaultDurableAt`, `replaceAtomic`, and
   `ExternalMonotoneAnchor`), proving atomic commit coherence, whole-disk rollback rejection, and
   sticky dual-layer quarantine on I/O errors.
-/


public section
namespace Qsag

set_option autoImplicit false
set_option maxRecDepth 4096

/-! ## 1. Constructive List Partition & Subset Helpers -/

private theorem bridgeLeb128_injective {a b : Nat} (h : leb128 a = leb128 b) : a = b :=
  (leb128_prefix_inj (show leb128 a ++ [] = leb128 b ++ [] by simpa using h)).1

private theorem mem_filter_bool {α : Type} {p : α → Bool} {x : α} :
    ∀ {xs : List α}, x ∈ xs.filter p → x ∈ xs ∧ p x = true
  | [], h => by cases h
  | y :: ys, h => by
    unfold List.filter at h
    cases hp : p y
    · rw [hp] at h
      obtain ⟨hm, hpx⟩ := mem_filter_bool h
      exact ⟨.tail _ hm, hpx⟩
    · rw [hp] at h
      cases h with
      | head => exact ⟨.head _, hp⟩
      | tail _ ht =>
        obtain ⟨hm, hpx⟩ := mem_filter_bool ht
        exact ⟨.tail _ hm, hpx⟩

private theorem mem_of_filter_bool {α : Type} {p : α → Bool} {x : α} :
    ∀ {xs : List α}, x ∈ xs → p x = true → x ∈ xs.filter p
  | [], h, _ => by cases h
  | y :: ys, h, hp => by
    unfold List.filter
    cases h with
    | head =>
      rw [hp]
      exact .head _
    | tail _ ht =>
      cases hpy : p y <;> simp only
      · exact mem_of_filter_bool ht hp
      · exact .tail _ (mem_of_filter_bool ht hp)

private theorem filter_partition_length {α : Type} (p : α → Bool) :
    ∀ (xs : List α), (xs.filter p).length + (xs.filter (fun x => !p x)).length = xs.length
  | [] => rfl
  | x :: xs => by
    have ih := filter_partition_length p xs
    unfold List.filter
    cases hp : p x <;> simp only [Bool.not_true, Bool.not_false, List.length_cons] <;> omega

private def eraseFirstNat (x : Nat) : List Nat → List Nat
  | [] => []
  | y :: ys => if x = y then ys else y :: eraseFirstNat x ys

private theorem eraseFirstNat_length {x : Nat} :
    ∀ {xs : List Nat}, x ∈ xs → (eraseFirstNat x xs).length + 1 = xs.length
  | [], h => by cases h
  | y :: ys, h => by
    unfold eraseFirstNat
    by_cases he : x = y
    · simp only [he, ↓reduceIte, List.length_cons]
    · simp only [he, ↓reduceIte, List.length_cons]
      cases h with
      | head => exact False.elim (he rfl)
      | tail _ ht => exact congrArg Nat.succ (eraseFirstNat_length ht)

private theorem eraseFirstNat_mem {x z : Nat} (hn : z ≠ x) :
    ∀ {xs : List Nat}, z ∈ xs → z ∈ eraseFirstNat x xs
  | [], h => by cases h
  | y :: ys, h => by
    unfold eraseFirstNat
    by_cases he : x = y
    · simp only [he, ↓reduceIte]
      subst y
      cases h with
      | head => exact False.elim (hn rfl)
      | tail _ ht => exact ht
    · simp only [he, ↓reduceIte]
      cases h with
      | head => exact .head _
      | tail _ ht => exact .tail _ (eraseFirstNat_mem hn ht)

private theorem nat_nodup_subset_length :
    ∀ {xs ys : List Nat}, xs.Nodup → (∀ x ∈ xs, x ∈ ys) → xs.length ≤ ys.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, ys, .cons hn hd, hs => by
    have he := eraseFirstNat_length (hs x (.head _))
    have hsub : ∀ z ∈ xs, z ∈ eraseFirstNat x ys := by
      intro z hz
      exact eraseFirstNat_mem (fun hzx => hn z hz hzx.symm) (hs z (.tail _ hz))
    have hi := nat_nodup_subset_length hd hsub
    rw [List.length_cons, ← he]
    exact Nat.add_le_add_right hi 1

private theorem filter_length_le {α : Type} (p : α → Bool) :
    ∀ (xs : List α), (xs.filter p).length ≤ xs.length
  | [] => Nat.zero_le _
  | x :: xs => by
    have ih := filter_length_le p xs
    unfold List.filter
    cases p x <;> simp only [List.length_cons] <;> omega

/-! ## 2. Custody Quorum Provenance → `ThresholdApproval` / `IdealTsig` / `InteractiveUcEngine` -/

/-- Extract the honest, unquarantined custodian roster from verified `Custody.Certificate`s. -/
@[expose] def custodyQuorumHonestApprovers
    (corruptParties : List Nat) (certs : List Custody.Certificate) : List Nat :=
  (certs.map Custody.Certificate.party).filter (fun p => decide (p ∉ corruptParties))

/-- Alignment invariant linking public `IdealTsigState` quorum parameters with `Custody.Deployment`. -/
structure CustodyTsigAligned {PK Msg : Type}
    (d : Custody.Deployment) (st : IdealTsigState PK Msg) : Prop where
  thresholdEq   : st.threshold = d.threshold
  numPartiesEq  : st.numParties = d.numParties
  thresholdLe   : d.threshold ≤ d.numParties
  corruptMinor  : st.corruptParties.length < d.threshold
  corruptNodup  : st.corruptParties.Nodup
  corruptInRng  : ∀ c ∈ st.corruptParties, c < d.numParties

/-- Construct a `SessionScheduleReq` whose `honestApprovers` come directly from an accepted
    `SeparatedCustody` certificate quorum rather than an unauthenticated scheduler claim. -/
def scheduleReqOfCustodyQuorum (corruptParties : List Nat) (r : Custody.Intent)
    (optRand : List UInt8) (certs : List Custody.Certificate) : SessionScheduleReq :=
  { sessionId       := r.session
    reqEpoch        := r.leaf
    msg             := r.message
    optRand         := optRand
    honestApprovers := custodyQuorumHonestApprovers corruptParties certs }

/-- **Accepted Custody Quorum Synthesizes `validThresholdApproval` (`acceptQuorum_implies_validThresholdApproval`)**:
    Whenever `Custody.acceptQuorum` accepts a quorum `certs` of unquarantined parties under
    `CustodyTsigAligned d st`, the extracted `custodyQuorumHonestApprovers` is non-empty and
    passes `ThresholdApproval.validThresholdApproval st` constructively. -/
theorem acceptQuorum_implies_validThresholdApproval {PK Msg : Type}
    (d : Custody.Deployment) (st : IdealTsigState PK Msg)
    (hAlign : CustodyTsigAligned d st)
    (usedSessions : List Nat) (r : Custody.Intent) (certs : List Custody.Certificate)
    (hUnquarantined : ∀ c ∈ certs, c.party ∉ st.identifiedCheaters)
    (hAcc : Custody.acceptQuorum d.signer (Custody.publicKeys d) d.deploymentId
              d.numParties d.threshold usedSessions r certs = true) :
    let hon := custodyQuorumHonestApprovers st.corruptParties certs
    hon ≠ [] ∧ validThresholdApproval st hon = true := by
  intro hon
  unfold Custody.acceptQuorum at hAcc
  rcases Bool.and_eq_true_iff.mp hAcc with ⟨hLeft, _hVerAll⟩
  rcases Bool.and_eq_true_iff.mp hLeft with ⟨_hFresh, hBoundsDec⟩
  rcases of_decide_eq_true hBoundsDec with ⟨hThPos, hThLeCerts, hIdsNd, hCertsRng⟩
  let ids := certs.map Custody.Certificate.party
  let activeCorrupt := st.corruptParties.filter (fun c => decide (c ∉ st.identifiedCheaters))
  let corrSub := ids.filter (fun p => decide (p ∈ st.corruptParties))
  have hPartEq : corrSub.length + hon.length = ids.length := by
    have hRaw := filter_partition_length (fun p => decide (p ∈ st.corruptParties)) ids
    have hExt : (fun p => !decide (p ∈ st.corruptParties)) = (fun p => decide (p ∉ st.corruptParties)) := by
      funext p
      by_cases hp : p ∈ st.corruptParties <;> simp [hp]
    dsimp only [corrSub, hon, custodyQuorumHonestApprovers, ids]
    rw [← hExt]
    exact hRaw
  have hCorrSubNd : corrSub.Nodup := nodup_filter_bool _ hIdsNd
  have hCorrSubInAct : ∀ x ∈ corrSub, x ∈ activeCorrupt := by
    intro x hx
    obtain ⟨hxIds, hxCorrDec⟩ := mem_filter_bool hx
    have hxCorr : x ∈ st.corruptParties := of_decide_eq_true hxCorrDec
    obtain ⟨c, hcMem, rfl⟩ := List.mem_map.mp hxIds
    have hcUnq : c.party ∉ st.identifiedCheaters := hUnquarantined c hcMem
    exact mem_of_filter_bool hxCorr (decide_eq_true hcUnq)
  have hCorrSubLeAct : corrSub.length ≤ activeCorrupt.length :=
    nat_nodup_subset_length hCorrSubNd hCorrSubInAct
  have hActLeCorr : activeCorrupt.length ≤ st.corruptParties.length :=
    filter_length_le _ st.corruptParties
  have hIdsLen : ids.length = certs.length := List.length_map _
  have hQuorumSum : st.threshold ≤ activeCorrupt.length + hon.length := by
    have hThEq := hAlign.thresholdEq
    omega
  have hHonPos : 0 < hon.length := by
    have hMin := hAlign.corruptMinor
    have hThEq := hAlign.thresholdEq
    omega
  have hHonNeNil : hon ≠ [] := by
    intro hNil
    rw [hNil] at hHonPos
    cases hHonPos
  have hHonNd : hon.Nodup := nodup_filter_bool _ hIdsNd
  have hHonAll : hon.all (fun h =>
      decide (h < st.numParties) &&
      decide (h ∉ st.corruptParties) &&
      decide (h ∉ st.identifiedCheaters)) = true := by
    apply List.all_eq_true.mpr
    intro h hhMem
    obtain ⟨hhIds, hhNotCorr⟩ := mem_filter_bool hhMem
    obtain ⟨c, hcMem, rfl⟩ := List.mem_map.mp hhIds
    have hcRng : c.party < st.numParties := hAlign.numPartiesEq ▸ hCertsRng c hcMem
    have hcUnq : c.party ∉ st.identifiedCheaters := hUnquarantined c hcMem
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hcRng, of_decide_eq_true hhNotCorr⟩, hcUnq⟩
  have hCorrRngAll : st.corruptParties.all (fun c => decide (c < st.numParties)) = true := by
    apply List.all_eq_true.mpr
    intro c hc
    exact decide_eq_true (hAlign.numPartiesEq ▸ hAlign.corruptInRng c hc)
  refine ⟨hHonNeNil, ?_⟩
  unfold validThresholdApproval
  dsimp only
  have hThBounds : 0 < st.threshold ∧ st.threshold ≤ st.numParties :=
    ⟨hAlign.thresholdEq ▸ hThPos, hAlign.thresholdEq ▸ hAlign.numPartiesEq ▸ hAlign.thresholdLe⟩
  have hCorrMinSt : st.corruptParties.length < st.threshold :=
    hAlign.thresholdEq ▸ hAlign.corruptMinor
  have hCNd : st.corruptParties.Nodup := hAlign.corruptNodup
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨hThBounds, hCorrMinSt⟩, hHonPos⟩, hCNd⟩, hCorrRngAll⟩, hHonNd⟩, hHonAll⟩, hQuorumSum⟩

/-- **End-to-End Custody History → `ThresholdApproval` & `IdealTsig` Provenance Bridge
    (`custodyHistory_submit_validThresholdApproval_and_provenance`)**:
    When `Custody.submitRecorded` accepts `(r, certs)` over an executed multi-party history
    `Custody.generatedHistory d commands`:
    1. `validThresholdApproval st hon = true` and `hon ≠ []` hold for both `IdealTsig.execIdealTsig`
       (`execIdealTsig` takes the `.signed` branch!) and `InteractiveUcEngine` (`scheduleReqOfCustodyQuorum`),
    2. Aggregate coordinator spend stays within `d.capacity` and `r.session` is fresh, and
    3. At least one unquarantined honest party `h ∈ hon` (`h ∉ st.corruptParties`) either has an
       actual prior admitted policy & `CompleteMediationBoundary` output (`ProducedPolicyApproval`)
       or witnesses an explicit `prodEufCmaWin` + `(ProdSmTcrBreak ∨ ProdPreimageBreak)` break! -/
theorem custodyHistory_submit_validThresholdApproval_and_provenance {PK SK Sig : Type}
    (S : AbstractSigScheme PK SK (List UInt8) Sig) (simSign : List UInt8 → Sig)
    (d : Custody.Deployment) (commands : List Custody.HistoryCommand)
    (st : IdealTsigState PK (List UInt8))
    (hAlign : CustodyTsigAligned d st)
    (r : Custody.Intent) (certs : List Custody.Certificate)
    (hRadix : d.signer.params.w = 4 ∨ d.signer.params.w = 16)
    (hStateful : d.signer.params.statefulJorts = true)
    (hUnquarantined : ∀ c ∈ certs, c.party ∉ st.identifiedCheaters)
    (hSub : (Custody.submitRecorded d (Custody.generatedHistory d commands).shared r certs).2 = true) :
    let hon := custodyQuorumHonestApprovers st.corruptParties certs
    let hist := Custody.generatedHistory d commands
    hon ≠ [] ∧
    validThresholdApproval st hon = true ∧
    execIdealTsig S simSign st (.stepSign r.message hon (fun res => match res with
      | .signed _ => .halt true
      | _ => .halt false)) = (true, { st with approvedMsgs := r.message :: st.approvedMsgs }) ∧
    hist.shared.coordinator.spent + r.spend ≤ d.capacity ∧
    (∃ c ∈ certs, c.party ∈ hon ∧ c.party ∉ st.corruptParties ∧
      (Custody.ProducedPolicyApproval d hist c.party r ∨
       (prodEufCmaWin d.signer.suite d.signer.params
          ⟨d.keys c.party, Custody.queries d.signer d.deploymentId c.party (hist.parties c.party).vault,
            Custody.payload d.deploymentId c.party r, c.signature⟩ = true ∧
        (ProdSmTcrBreak d.signer.suite d.signer.params (d.keys c.party)
           (Custody.signingLog d.signer (d.keys c.party) d.deploymentId c.party (hist.parties c.party).vault) ∨
         ProdPreimageBreak d.signer.suite d.signer.params (d.keys c.party)
           (Custody.signingLog d.signer (d.keys c.party) d.deploymentId c.party (hist.parties c.party).vault)
           (Custody.payload d.deploymentId c.party r) c.signature)))) := by
  intro hon hist
  have hVerdict :
      (Custody.submit d.signer (Custody.publicKeys d) d.deploymentId d.numParties d.threshold
        hist.shared.coordinator r certs).2 = true := by
    rw [← Custody.submitRecorded_verdict]
    exact hSub
  obtain ⟨hAccQ, hSpendCap, _⟩ := Custody.submit_accepted d.signer (Custody.publicKeys d)
    d.deploymentId d.numParties d.threshold hist.shared.coordinator r certs hVerdict
  have hCapEq : hist.shared.coordinator.capacity = d.capacity :=
    (Custody.generatedHistory_valid d commands).shared.capacity
  obtain ⟨hHonNe, hValApp⟩ :=
    acceptQuorum_implies_validThresholdApproval d st hAlign
      hist.shared.coordinator.consumedSessions r certs hUnquarantined hAccQ
  have hIdealStep :
      execIdealTsig S simSign st (.stepSign r.message hon (fun res => match res with
        | .signed _ => .halt true
        | _ => .halt false)) = (true, { st with approvedMsgs := r.message :: st.approvedMsgs }) := by
    dsimp only [hon]
    simp only [execIdealTsig, hValApp, ↓reduceIte]
  obtain ⟨c, hcMem, hcNotCorr, hProv⟩ :=
    Custody.generated_submit_provenance d commands st.corruptParties r certs
      hRadix hStateful hAlign.corruptMinor hSub
  have hcInHon : c.party ∈ hon :=
    mem_of_filter_bool (List.mem_map.mpr ⟨c, hcMem, rfl⟩) (decide_eq_true hcNotCorr)
  exact ⟨hHonNe, hValApp, hIdealStep, hCapEq ▸ hSpendCap, c, hcMem, hcInHon, hcNotCorr, hProv⟩

/-- **`#tooth` Unauthenticated `honestApprovers` Bypass (`tooth_unauthenticated_approvers_bypass_without_custody_certs`)**:
    Without the `SeparatedCustody` quorum gate, an adversary scheduling `honestApprovers = [0, 1]`
    with **empty** `certs = []` passes structural `validThresholdApproval = true`, whereas
    `Custody.acceptQuorum` and `custodyQuorumHonestApprovers` reject `certs = []` (`= false`)! -/
theorem tooth_unauthenticated_approvers_bypass_without_custody_certs
    (cfg : Custody.SigningConfig) (pks : Nat → PqPublicKey) (dep : Nat) (r : Custody.Intent) :
    ∃ (st : IdealTsigState Unit (List UInt8)),
      validThresholdApproval st [0, 1] = true ∧
      Custody.acceptQuorum cfg pks dep 3 2 [] r [] = false ∧
      validThresholdApproval st (custodyQuorumHonestApprovers st.corruptParties []) = false := by
  refine ⟨⟨(), 2, 3, [2], [], []⟩, by decide, ?_, ?_⟩
  · simp [Custody.acceptQuorum]
  · exact empty_honest_approvers_rejected _

/-! ## 3. Party-Local Custody Roster & Non-Hiding Stateful/Stateless Production Signing Release -/

/-- Isolated local state of a single honest participant pairing MPC share custody (`HonestCustodyVault`)
    with policy/mediation custody (`Custody.PolicyVault`). -/
structure PartyCustodyNode (ShareT : Type) where
  partyId     : Nat
  mpcVault    : HonestCustodyVault ShareT
  policyVault : Custody.PolicyVault

/-- Constructive party-local lookup projecting only unpoisoned honest share slots into the
    `InteractiveThresholdProtocol` callback signature (`0` coordinator-owned secret map). -/
def projectPartyLocalShares {ShareT : Type} : List (PartyCustodyNode ShareT) → Nat → Option ShareT
  | [], _ => none
  | node :: rest, pid =>
    if pid == node.partyId then
      if node.mpcVault.wal.poisoned || node.policyVault.vault.poisoned then none
      else node.mpcVault.shareSlot
    else
      projectPartyLocalShares rest pid

/-- Quarantine a single party node locally: wipes `shareSlot := none`, sets `mpcVault.wal.poisoned := true`,
    poisons `policyVault.vault`, and clears any volatile `active` grant. -/
def quarantinePartyNodes {ShareT : Type} (targetPid : Nat) :
    List (PartyCustodyNode ShareT) → List (PartyCustodyNode ShareT)
  | [] => []
  | node :: rest =>
    let updated :=
      if targetPid == node.partyId then
        { node with
          mpcVault := walPoisonVault node.mpcVault
          policyVault :=
            { node.policyVault with
              vault := { node.policyVault.vault with poisoned := true, active := none } } }
      else node
    updated :: quarantinePartyNodes targetPid rest

/-- Corrupt parties absent from the honest roster have `projectPartyLocalShares = none` structurally. -/
theorem projectPartyLocalShares_absent_none {ShareT : Type} :
    ∀ (nodes : List (PartyCustodyNode ShareT)) (pid : Nat),
      (∀ n ∈ nodes, n.partyId ≠ pid) →
      projectPartyLocalShares nodes pid = none
  | [], _, _ => rfl
  | node :: rest, pid, hAbs => by
    have hNe : (pid == node.partyId) = false :=
      beq_false_of_ne (fun hEq => hAbs node (.head _) hEq.symm)
    simp only [projectPartyLocalShares, hNe, Bool.false_eq_true, ↓reduceIte]
    exact projectPartyLocalShares_absent_none rest pid (fun n hn => hAbs n (.tail _ hn))

/-- Local quarantine wipes `targetPid`'s projected share while leaving every other party `q ≠ targetPid` intact. -/
theorem quarantinePartyNodes_isolates_and_wipes {ShareT : Type} :
    ∀ (nodes : List (PartyCustodyNode ShareT)) (targetPid q : Nat),
      projectPartyLocalShares (quarantinePartyNodes targetPid nodes) targetPid = none ∧
      (q ≠ targetPid →
        projectPartyLocalShares (quarantinePartyNodes targetPid nodes) q =
          projectPartyLocalShares nodes q)
  | [], _, _ => ⟨rfl, fun _ => rfl⟩
  | node :: rest, targetPid, q => by
    obtain ⟨ihSelf, ihOther⟩ := quarantinePartyNodes_isolates_and_wipes rest targetPid q
    refine ⟨?_, ?_⟩
    · unfold quarantinePartyNodes projectPartyLocalShares
      by_cases hHit : (targetPid == node.partyId) = true
      · simp [hHit, walPoisonVault, walQuarantine]
      · simp only [hHit, Bool.false_eq_true, ↓reduceIte]
        exact ihSelf
    · intro hqNe
      unfold quarantinePartyNodes projectPartyLocalShares
      by_cases hHit : (targetPid == node.partyId) = true
      · have hTgtEq : targetPid = node.partyId := Nat.eq_of_beq_eq_true hHit
        have hqMiss : (q == node.partyId) = false := beq_false_of_ne (hTgtEq ▸ hqNe)
        simp only [hHit, ↓reduceIte, hqMiss, Bool.false_eq_true]
        exact ihOther hqNe
      · simp only [hHit, Bool.false_eq_true, ↓reduceIte]
        by_cases hqHit : (q == node.partyId) = true
        · simp [hqHit]
        · simp only [hqHit, Bool.false_eq_true, ↓reduceIte]
          exact ihOther hqNe

/-- Grounded 3-party RSS signing bundle deriving `MatchesKey` and `enrolledPk` directly from
    well-formed RSS byte shares without uninstantiated oracle hypotheses. -/
structure GroundedRssSigningBundle where
  seedShares : RssByteShares
  prfShares  : RssByteShares
  pkSeed     : List UInt8
  params     : PqHashParams
  grindLimit : Nat
  prfTape    : Nat → Nat → Nat → Nat → RssPrfZeroSeeds
  seedWf     : seedShares.WellFormed
  prfWf      : prfShares.WellFormed

def GroundedRssSigningBundle.secretKey (b : GroundedRssSigningBundle) : PqSecretKey :=
  ⟨reconstructRssBytes b.seedShares, reconstructRssBytes b.prfShares, b.pkSeed⟩

def GroundedRssSigningBundle.mpcOracles (b : GroundedRssSigningBundle) : ProductionPqHashMpcOracles :=
  mkRssProductionPqHashMpcOracles b.seedShares b.prfShares b.pkSeed b.prfTape

def GroundedRssSigningBundle.enrolledPk (b : GroundedRssSigningBundle) : PqPublicKey :=
  derivePublicKey cshake256Suite b.params b.secretKey

theorem GroundedRssSigningBundle.matchesKey (b : GroundedRssSigningBundle) :
    b.mpcOracles.MatchesKey cshake256Suite b.secretKey :=
  mkRssProductionPqHashMpcOracles_matchesKey b.seedWf b.prfWf b.pkSeed b.prfTape

theorem GroundedRssSigningBundle.mpcDerivedPk_eq_enrolledPk (b : GroundedRssSigningBundle) :
    derivePublicKeyMpc cshake256Suite b.params b.mpcOracles.toPqHashMpcOracles b.pkSeed =
      b.enrolledPk := by
  unfold derivePublicKeyMpc GroundedRssSigningBundle.enrolledPk
  dsimp only
  have hRoot := mpcComputeXmssSubtreeRoot_eq cshake256Suite b.params
    b.mpcOracles.toPqHashMpcOracles b.secretKey b.matchesKey.1
  dsimp only [GroundedRssSigningBundle.secretKey] at hRoot
  rw [hRoot]
  rfl

/-- **Non-Hiding Stateful/Stateless Production Cut Release (`evalNonHidingRssCutRelease`)**:
    1. Evaluates over the complete framed `encodeUcSigningRequest req` (never `req.msg.take 32` or bare `req.msg`),
    2. Supports **both** `statefulJorts = true` (at leaf `req.reqEpoch`) and `statefulJorts = false`,
    3. Emits `PSum.inr (packWire raw)` ONLY when `mpcEvalProduction*Sign = some sig` AND
       `encodeProductionSigWire b.params sig = .ok raw`, mapping `none` or wire errors to
       `PSum.inl .activeConsistencyFailed` (so `execRealSession` aborts and quarantines rather than
       emitting bogus `Option`-hidden bytes as `.signOk`). -/
def evalNonHidingRssCutRelease (b : GroundedRssSigningBundle) (req : SessionScheduleReq) :
    PSum AbortReason ByteArray :=
  let framedMsg := encodeUcSigningRequest req
  let optSig :=
    if b.params.statefulJorts then
      mpcEvalProductionStatefulSign cshake256Suite b.params b.mpcOracles
        b.pkSeed framedMsg req.optRand req.reqEpoch b.grindLimit
    else
      mpcEvalProductionStatelessSign cshake256Suite b.params b.mpcOracles
        b.pkSeed framedMsg req.optRand b.grindLimit
  match optSig with
  | none => .inl .activeConsistencyFailed
  | some sig =>
    match encodeProductionSigWire b.params sig with
    | .error _ => .inl .activeConsistencyFailed
    | .ok raw => .inr (packWire raw)

/-- **Soundness of Non-Hiding Cut Release (`evalNonHidingRssCutRelease_sound`)**:
    Every `PSum.inr sigBytes` returned by `evalNonHidingRssCutRelease` decodes via
    `decodeProductionSigWire` to an actual `sig : PqHashSig` that passes
    `verifyProductionPqHashSig` under `b.enrolledPk` on `encodeUcSigningRequest req`, for both
    stateful and stateless Jorts configurations (`0` external `MatchesKey` assumptions). -/
theorem evalNonHidingRssCutRelease_sound (b : GroundedRssSigningBundle)
    (req : SessionScheduleReq) (sigBytes : ByteArray)
    (hOk : evalNonHidingRssCutRelease b req = .inr sigBytes) :
    ∃ sig : PqHashSig,
      decodeProductionSigWire b.params (unpackWire sigBytes) = .ok sig ∧
      (unpackWire sigBytes).length = b.params.wireSigBytes ∧
      verifyProductionPqHashSig cshake256Suite b.params b.enrolledPk
        (encodeUcSigningRequest req) sig = true := by
  unfold evalNonHidingRssCutRelease at hOk
  dsimp only at hOk
  by_cases hMode : b.params.statefulJorts = true
  · simp only [hMode, ↓reduceIte] at hOk
    cases hMpc : mpcEvalProductionStatefulSign cshake256Suite b.params b.mpcOracles
        b.pkSeed (encodeUcSigningRequest req) req.optRand req.reqEpoch b.grindLimit with
    | none => rw [hMpc] at hOk; cases hOk
    | some sig =>
      rw [hMpc] at hOk
      dsimp only at hOk
      cases hEnc : encodeProductionSigWire b.params sig with
      | error _ => rw [hEnc] at hOk; cases hOk
      | ok raw =>
        rw [hEnc] at hOk
        cases hOk
        simp only [unpackWire_packWire]
        have hDec := decodeProductionSigWire_encodeProductionSigWire b.params sig raw hEnc
        have hEqRef := thresholdProductionStatefulSign_eq_evalProductionStatefulSign
          cshake256Suite b.params b.mpcOracles b.secretKey b.matchesKey
          (encodeUcSigningRequest req) req.optRand req.reqEpoch b.grindLimit
        dsimp only [GroundedRssSigningBundle.secretKey] at hEqRef
        rw [hMpc] at hEqRef
        have hVer := verifyProductionPqHashSig_evalProductionStatefulSign
          cshake256Suite b.params b.secretKey (encodeUcSigningRequest req)
          req.optRand req.reqEpoch b.grindLimit sig hEqRef.symm
        exact ⟨sig, hDec.2, hDec.1, hVer⟩
  · simp only [hMode, Bool.false_eq_true, ↓reduceIte] at hOk
    cases hMpc : mpcEvalProductionStatelessSign cshake256Suite b.params b.mpcOracles
        b.pkSeed (encodeUcSigningRequest req) req.optRand b.grindLimit with
    | none => rw [hMpc] at hOk; cases hOk
    | some sig =>
      rw [hMpc] at hOk
      dsimp only at hOk
      cases hEnc : encodeProductionSigWire b.params sig with
      | error _ => rw [hEnc] at hOk; cases hOk
      | ok raw =>
        rw [hEnc] at hOk
        cases hOk
        simp only [unpackWire_packWire]
        have hDec := decodeProductionSigWire_encodeProductionSigWire b.params sig raw hEnc
        have hEqRef := thresholdProductionStatelessSign_eq_evalProductionStatelessSign
          cshake256Suite b.params b.mpcOracles b.secretKey b.matchesKey
          (encodeUcSigningRequest req) req.optRand b.grindLimit
        dsimp only [GroundedRssSigningBundle.secretKey] at hEqRef
        rw [hMpc] at hEqRef
        have hVer := verifyProductionPqHashSig_evalProductionStatelessSign
          cshake256Suite b.params b.secretKey (encodeUcSigningRequest req)
          req.optRand b.grindLimit sig hEqRef.symm
        exact ⟨sig, hDec.2, hDec.1, hVer⟩

private theorem signProductionHypertreeCore_zero_grind
    (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pk : PqPublicKey) (msg mu rRand : List UInt8)
    (leafGlobalIdx : Nat) (forsIdxs : Option (List Nat))
    (hPos : 0 < params.numLayers) :
    signProductionHypertreeCore suite params sk pk msg mu rRand leafGlobalIdx forsIdxs 0 = none := by
  unfold signProductionHypertreeCore
  dsimp only
  cases hs : params.statefulJorts
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases forsIdxs with
    | none => rfl
    | some idxs =>
      dsimp only
      obtain ⟨rem, hLayers⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hPos)
      rw [hLayers, signProductionHypertreeLayers_succ]
      simp [hs, grindTswInternalCounterAux]
  · simp only [↓reduceIte]
    obtain ⟨rem, hLayers⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hPos)
    rw [hLayers, signProductionHypertreeLayers_succ]
    simp [hs, grindTswLeafCounterAux]

/-- **`#tooth` `Option`-Hiding Serializer vs Non-Hiding Cut Release (`tooth_option_hiding_vs_non_hiding_zero_grind`)**:
    When `grindLimit = 0`, WOTS+C counter grinding exhausts immediately (`= none`).
    - The legacy `productionThresholdSignOracle` with any `ser : Option PqHashSig → ByteArray`
      silently emits `ser none` as apparent signature bytes;
    - `evalNonHidingRssCutRelease` explicitly aborts with `.inl .activeConsistencyFailed`! -/
theorem tooth_option_hiding_vs_non_hiding_zero_grind
    (b : GroundedRssSigningBundle)
    (ser : Option PqHashSig → ByteArray)
    (hZeroGrind : b.grindLimit = 0) :
    ∃ (req : SessionScheduleReq),
      productionThresholdSignOracle cshake256Suite b.params b.mpcOracles b.pkSeed 0 ser req =
        ser none ∧
      evalNonHidingRssCutRelease b req = .inl .activeConsistencyFailed := by
  let req : SessionScheduleReq := ⟨0, 0, [0x01], [], [0, 1]⟩
  have hStatelessNone :
      ∀ msg, mpcEvalProductionStatelessSign cshake256Suite b.params b.mpcOracles
        b.pkSeed msg req.optRand 0 = none := by
    intro msg
    have hEq := thresholdProductionStatelessSign_eq_evalProductionStatelessSign
      cshake256Suite b.params b.mpcOracles b.secretKey b.matchesKey msg req.optRand 0
    change mpcEvalProductionStatelessSign cshake256Suite b.params b.mpcOracles
      b.pkSeed msg req.optRand 0 =
      evalProductionStatelessSign cshake256Suite b.params b.secretKey msg req.optRand 0 at hEq
    rw [hEq, evalProductionStatelessSign_eq]
    cases hMode : b.params.statefulJorts
    · cases hWf : b.params.productionWellFormed
      · simp
      · cases hNum : b.params.numLayers with
        | zero => simp [PqHashParams.productionWellFormed, hNum] at hWf
        | succ rem =>
          simp only [Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
          cases hDer : deriveProductionStatelessInputs cshake256Suite b.params
              (thPrfMsg cshake256Suite b.secretKey.skPrf req.optRand
                (thPreHash cshake256Suite (derivePublicKey cshake256Suite b.params b.secretKey).pkSeed
                  (derivePublicKey cshake256Suite b.params b.secretKey).pkRoot msg))
              (derivePublicKey cshake256Suite b.params b.secretKey).pkSeed
              (derivePublicKey cshake256Suite b.params b.secretKey).pkRoot
              (thPreHash cshake256Suite (derivePublicKey cshake256Suite b.params b.secretKey).pkSeed
                (derivePublicKey cshake256Suite b.params b.secretKey).pkRoot msg) with
          | none => rfl
          | some pair =>
            rcases pair with ⟨leafIdx, forsIdxs⟩
            exact signProductionHypertreeCore_zero_grind cshake256Suite b.params b.secretKey
              (derivePublicKey cshake256Suite b.params b.secretKey) msg _ _ leafIdx (some forsIdxs)
              (hNum ▸ Nat.succ_pos rem)
    · simp
  refine ⟨req, ?_, ?_⟩
  · unfold productionThresholdSignOracle
    rw [hStatelessNone req.msg]
  · unfold evalNonHidingRssCutRelease
    dsimp only
    rw [hZeroGrind]
    by_cases hMode : b.params.statefulJorts = true
    · simp only [hMode, ↓reduceIte]
      have hStEq := thresholdProductionStatefulSign_eq_evalProductionStatefulSign
        cshake256Suite b.params b.mpcOracles b.secretKey b.matchesKey
        (encodeUcSigningRequest req) req.optRand req.reqEpoch 0
      change mpcEvalProductionStatefulSign cshake256Suite b.params b.mpcOracles
        b.pkSeed (encodeUcSigningRequest req) req.optRand req.reqEpoch 0 =
        evalProductionStatefulSign cshake256Suite b.params b.secretKey
          (encodeUcSigningRequest req) req.optRand req.reqEpoch 0 at hStEq
      rw [hStEq, evalProductionStatefulSign_eq]
      cases hWf : b.params.productionWellFormed
      · simp [hMode]
      · cases hRng : b.params.productionLeafIdxInRange req.reqEpoch
        · simp [hMode]
        · cases hNum : b.params.numLayers with
          | zero => simp [PqHashParams.productionWellFormed, hNum] at hWf
          | succ rem =>
            simp only [hMode, Bool.not_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
            rw [signProductionHypertreeCore_zero_grind cshake256Suite b.params b.secretKey
              (derivePublicKey cshake256Suite b.params b.secretKey) (encodeUcSigningRequest req) _ _
              req.reqEpoch none (hNum ▸ Nat.succ_pos rem)]
    · simp only [hMode, Bool.false_eq_true, ↓reduceIte, hStatelessNone (encodeUcSigningRequest req)]

/-! ## 4. Crash-Consistent `PosixCrashWal` + `ExternalMonotoneAnchor` ↔ `WalLatchState` & `Custody.Ledger` -/

/-- Canonical injective framing of `WalLatchState.latchedRecord` together with `CompleteMediationBoundary`
    durable watermarks `(nextLeaf, nextRound, spent)` inside `PosixCrashWal.WalRecordBody.payload`. -/
@[expose] def encodeDurableLatchPayload
    (latched : Option (Nat × List UInt8 × ByteArray))
    (nextLeaf nextRound spent : Nat) : List UInt8 :=
  match latched with
  | none =>
    encodeMultiFrame [[0x00], leb128 nextLeaf, leb128 nextRound, leb128 spent]
  | some (ep, msgDig, sigBytes) =>
    encodeMultiFrame [[0x01], leb128 ep, msgDig, unpackWire sigBytes,
                      leb128 nextLeaf, leb128 nextRound, leb128 spent]

theorem encodeDurableLatchPayload_injective
    {lat₁ lat₂ : Option (Nat × List UInt8 × ByteArray)}
    {nl₁ nr₁ sp₁ nl₂ nr₂ sp₂ : Nat}
    (hEq : encodeDurableLatchPayload lat₁ nl₁ nr₁ sp₁ =
           encodeDurableLatchPayload lat₂ nl₂ nr₂ sp₂) :
    lat₁ = lat₂ ∧ nl₁ = nl₂ ∧ nr₁ = nr₂ ∧ sp₁ = sp₂ := by
  cases lat₁ with
  | none =>
    cases lat₂ with
    | none =>
      have hf := encodeMultiFrame_injective hEq
      simp only [List.cons.injEq] at hf
      exact ⟨rfl, bridgeLeb128_injective hf.2.1,
        bridgeLeb128_injective hf.2.2.1, bridgeLeb128_injective hf.2.2.2.1⟩
    | some rec₂ =>
      rcases rec₂ with ⟨ep₂, md₂, sig₂⟩
      have hf := encodeMultiFrame_injective hEq
      simp only [List.cons.injEq] at hf
      exact False.elim ((by decide : (0x00 : UInt8) ≠ 0x01) hf.1.1)
  | some rec₁ =>
    rcases rec₁ with ⟨ep₁, md₁, sig₁⟩
    cases lat₂ with
    | none =>
      have hf := encodeMultiFrame_injective hEq
      simp only [List.cons.injEq] at hf
      exact False.elim ((by decide : (0x01 : UInt8) ≠ 0x00) hf.1.1)
    | some rec₂ =>
      rcases rec₂ with ⟨ep₂, md₂, sig₂⟩
      have hf := encodeMultiFrame_injective hEq
      simp only [List.cons.injEq] at hf
      have hEp := bridgeLeb128_injective hf.2.1
      have hMd := hf.2.2.1
      have hSig := unpackWire_injective hf.2.2.2.1
      have hNl := bridgeLeb128_injective hf.2.2.2.2.1
      have hNr := bridgeLeb128_injective hf.2.2.2.2.2.1
      have hSp := bridgeLeb128_injective hf.2.2.2.2.2.2.1
      subst hEp hMd hSig
      exact ⟨rfl, hNl, hNr, hSp⟩

/-- End-to-end crash-consistent state coupling invariant unifying:
    - `InteractiveUcEngine.WalLatchState` (`absWal`),
    - `CompleteMediationBoundary.Ledger` (`custodyLedger`),
    - `PosixCrashWal.PosixFsState` + `LockedVaultHandle` + `WalRecord` (`VaultDurableAt`), and
    - `PosixCrashWal.ExternalMonotoneAnchor` (`anchor`). -/
structure WalPosixCoherent
    (fs : PosixFsState) (lockIno : InodeId) (genesisNonce : List UInt8)
    (macFn : KeyedMacFn) (macKey : List UInt8)
    (absWal : WalLatchState) (custodyLedger : Custody.Ledger)
    (anchor : ExternalMonotoneAnchor)
    (h : LockedVaultHandle) (onDiskRec : WalRecord) : Prop where
  walWf        : absWal.WellFormed
  keyIdEq      : h.vaultKeyId = absWal.enrolledPkDigest
  recKeyIdEq   : onDiskRec.body.vaultKeyId = absWal.enrolledPkDigest
  genesisEq    : h.lockGenesisId = computeLockGenesisId lockIno genesisNonce
  epochSync    : onDiskRec.body.epoch = absWal.nextEpoch
  payloadSync  : onDiskRec.body.payload =
                 encodeDurableLatchPayload absWal.latchedRecord
                   custodyLedger.nextLeaf custodyLedger.nextRound custodyLedger.spent
  anchorSync   : anchor.attestedEpoch = onDiskRec.body.epoch ∧
                 anchor.attestedTag = onDiskRec.keyedMac
  poisonSync   : h.ioPoisoned = absWal.poisoned
  durableNand  : VaultDurableAt fs h.basePath lockIno genesisNonce macFn macKey onDiskRec

/-- **Atomic POSIX WAL Commit Preserves `WalPosixCoherent` & Blocks Snapshot Rollback
    (`posixWalCommit_refines_walCommitBeforeRelease`)**:
    When `walPreSignStep` authorizes fresh epoch `ep` and `PosixCrashWal.replaceAtomic` commits
    `newRec` at `ep + 1`:
    1. `walCommitBeforeRelease` steps to `walCommitAuthorized wal' ep msgDigest freshSig`,
    2. `newRec` is durably persisted to `NandBlocks` (`VaultDurableAt`) and satisfies `WalPosixCoherent`
       with the updated `ExternalMonotoneAnchor`,
    3. `newRec` is accepted by the pre-checkpoint `anchor` (`verifyAgainstExternalAnchor anchor = true`), and
    4. Restoring the pre-commit `oldRec` snapshot is strictly rejected by `anchor'` (`= false`)! -/
theorem posixWalCommit_refines_walCommitBeforeRelease
    {fs fs' : PosixFsState} {lockIno : InodeId} {genesisNonce : List UInt8}
    {macFn : KeyedMacFn} (hMacWf : WellFormedMacFn macFn) {macKey : List UInt8}
    {absWal wal' : WalLatchState} {oldLedger newLedger : Custody.Ledger}
    {anchor : ExternalMonotoneAnchor}
    {h h' : LockedVaultHandle} {oldRec newRec : WalRecord}
    {pkDigest msgDigest : List UInt8} {reqEpoch ep : Nat} {freshSig : ByteArray}
    {faults : IoFaultSchedule}
    (hCoh : WalPosixCoherent fs lockIno genesisNonce macFn macKey absWal oldLedger anchor h oldRec)
    (hAuth : walPreSignStep absWal pkDigest reqEpoch msgDigest = .ok wal' (.authorizedFresh ep))
    (hRep : replaceAtomic fs h (ep + 1)
              (encodeDurableLatchPayload (some (ep, msgDigest, freshSig))
                newLedger.nextLeaf newLedger.nextRound newLedger.spent)
              macFn macKey faults = (fs', h', .ok newRec)) :
    let walCommitted := walCommitAuthorized wal' ep msgDigest freshSig
    let anchor' : ExternalMonotoneAnchor := ⟨ep + 1, newRec.keyedMac⟩
    walCommitBeforeRelease absWal pkDigest reqEpoch msgDigest freshSig =
      .ok walCommitted freshSig ∧
    WalPosixCoherent fs' lockIno genesisNonce macFn macKey walCommitted newLedger anchor' h' newRec ∧
    verifyAgainstExternalAnchor anchor newRec.body.epoch newRec.keyedMac = true ∧
    verifyAgainstExternalAnchor anchor' oldRec.body.epoch oldRec.keyedMac = false := by
  intro walCommitted anchor'
  have hCommitEq := walCommitAuthorized_eq_walCommitBeforeRelease freshSig hAuth
  obtain ⟨hWfPost, _, hPoisonFalse, _⟩ :=
    walCommitBeforeRelease_preserves_wellFormed hCoh.walWf hCommitEq
  have hWalEq : wal' = absWal ∧ ep = absWal.nextEpoch ∧ absWal.poisoned = false := by
    unfold walPreSignStep at hAuth
    cases hp : absWal.poisoned
    · simp only [hp, Bool.false_eq_true, ↓reduceIte] at hAuth
      cases hPk : decide (pkDigest = absWal.enrolledPkDigest)
      · simp [hPk] at hAuth
      · simp only [hPk, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hAuth
        cases hLat : absWal.latchedRecord with
        | none =>
          rw [hLat] at hAuth
          cases hEp : (reqEpoch == absWal.nextEpoch)
          · simp [hEp] at hAuth
          · simp only [hEp, ↓reduceIte] at hAuth
            injection hAuth with hW hDec
            injection hDec with hEpEq
            exact ⟨hW.symm, hEpEq.symm.trans (Nat.eq_of_beq_eq_true hEp), rfl⟩
        | some rec0 =>
          rcases rec0 with ⟨ep0, prevMd, prevSig⟩
          rw [hLat] at hAuth
          cases hHit : (reqEpoch == ep0 && decide (msgDigest = prevMd))
          · simp only [hHit, Bool.false_eq_true, ↓reduceIte] at hAuth
            cases hEp : (reqEpoch == absWal.nextEpoch)
            · simp [hEp] at hAuth
            · simp only [hEp, ↓reduceIte] at hAuth
              injection hAuth with hW hDec
              injection hDec with hEpEq
              exact ⟨hW.symm, hEpEq.symm.trans (Nat.eq_of_beq_eq_true hEp), rfl⟩
          · simp [hHit] at hAuth
    · simp [hp] at hAuth
  have hVkOld : h.vaultKeyId = oldRec.body.vaultKeyId := hCoh.keyIdEq.trans hCoh.recKeyIdEq.symm
  obtain ⟨hHandleEq, hNewRecEq, hDurPost⟩ :=
    replaceAtomic_ok_durable hMacWf hVkOld hCoh.genesisEq hCoh.durableNand hRep
  cases hHandleEq
  have hEnrolledEq : walCommitted.enrolledPkDigest = absWal.enrolledPkDigest := by
    dsimp only [walCommitted, walCommitAuthorized]
    rw [hWalEq.1]
  have hNewBodyEpoch : newRec.body.epoch = ep + 1 := by
    rw [hNewRecEq]; rfl
  have hNewBodyVk : newRec.body.vaultKeyId = walCommitted.enrolledPkDigest := by
    rw [hNewRecEq, hEnrolledEq]; exact hCoh.keyIdEq
  have hNewBodyPay : newRec.body.payload =
      encodeDurableLatchPayload walCommitted.latchedRecord
        newLedger.nextLeaf newLedger.nextRound newLedger.spent := by
    rw [hNewRecEq]; rfl
  have hPoisonCoh : h.ioPoisoned = walCommitted.poisoned := by
    rw [hCoh.poisonSync, hWalEq.2.2, hPoisonFalse]
  have hSuccAnchor : verifyAgainstExternalAnchor anchor newRec.body.epoch newRec.keyedMac = true := by
    apply externalAnchor_accepts_durable_successor
    rw [hCoh.anchorSync.1, hCoh.epochSync, ← hWalEq.2.1, hNewBodyEpoch]
    exact Nat.lt_succ_self ep
  have hRollbackRej : verifyAgainstExternalAnchor anchor' oldRec.body.epoch oldRec.keyedMac = false := by
    apply externalAnchor_rejects_whole_disk_rollback
    rw [hCoh.epochSync, ← hWalEq.2.1]
    exact Nat.lt_succ_self ep
  refine ⟨hCommitEq, ?_, hSuccAnchor, hRollbackRej⟩
  exact
    { walWf       := hWfPost
      keyIdEq     := hCoh.keyIdEq.trans hEnrolledEq.symm
      recKeyIdEq  := hNewBodyVk
      genesisEq   := hCoh.genesisEq
      epochSync   := hNewBodyEpoch
      payloadSync := hNewBodyPay
      anchorSync  := ⟨hNewBodyEpoch.symm, rfl⟩
      poisonSync  := hPoisonCoh
      durableNand := hDurPost }

/-- **I/O Error Sticky Dual Quarantine (`posixWalIoError_quarantines_both`)**:
    Whenever `PosixCrashWal.replaceAtomic` fails with `.error err`, `h'.ioPoisoned = true` and
    transitioning `absWal` via `walQuarantine` locks **both** the POSIX handle and `WalLatchState`
    into sticky poisoned quarantine so neither layer can ever sign or overwrite again! -/
theorem posixWalIoError_quarantines_both
    {fs fs' : PosixFsState} {h h' : LockedVaultHandle}
    {epNext : Nat} {pay : List UInt8}
    {macFn : KeyedMacFn} {macKey : List UInt8} {faults : IoFaultSchedule} {err : PosixErr}
    (absWal : WalLatchState)
    (hFail : replaceAtomic fs h epNext pay macFn macKey faults = (fs', h', .error err)) :
    let walQ := walQuarantine absWal
    h'.ioPoisoned = true ∧
    walQ.poisoned = true ∧
    h'.ioPoisoned = walQ.poisoned ∧
    (∀ ep2 pay2 faults2,
      replaceAtomic fs' h' ep2 pay2 macFn macKey faults2 = (fs', h', .error .epoisoned)) ∧
    (∀ pkDig reqEp msgDig freshSig,
      walPreSignStep walQ pkDig reqEp msgDig = .err walQ .poisonedQuarantine ∧
      walCommitBeforeRelease walQ pkDig reqEp msgDig freshSig = .err walQ .poisonedQuarantine) := by
  intro walQ
  have hHP := (replaceAtomic_sticky_poison fs h epNext pay macFn macKey faults).2 fs' h' err hFail
  have hWP : walQ.poisoned = true := rfl
  refine ⟨hHP, hWP, hHP.trans hWP.symm, ?_, ?_⟩
  · intro ep2 pay2 faults2
    exact (replaceAtomic_sticky_poison fs' h' ep2 pay2 macFn macKey faults2).1 hHP
  · intro pkDig reqEp msgDig freshSig
    have hSticky := walLatch_poison_sticky walQ hWP pkDig reqEp msgDig freshSig
    exact ⟨hSticky.1, hSticky.2.1⟩

/-- **`#tooth` Unanchored Whole-Disk Snapshot Restore Enables Epoch-0 Double Signing
    (`tooth_unanchored_snapshot_rollback_replays_epoch`)**:
    After committing `(ep = 0, msgDig₁, sig₁)` (`nextEpoch = 1`), the committed `WalLatchState`
    rejects a distinct `msgDig₂ ≠ msgDig₁` at epoch `0`, and `ExternalMonotoneAnchor` (`attestedEpoch = 1`)
    rejects restoring the epoch-`0` `WalRecord`. Without the external anchor, restoring the valid
    MAC-authenticated epoch-`0` state re-authorizes `msgDig₂` as `.authorizedFresh 0`! -/
theorem tooth_unanchored_snapshot_rollback_replays_epoch :
    ∃ (pkDig : List UInt8) (wal0 wal1 : WalLatchState)
      (anchor1 : ExternalMonotoneAnchor) (oldTag : List UInt8),
      walPreSignStep wal1 pkDig 0 [0x02] = .err wal1 .staleOrOutOfOrderEpoch ∧
      verifyAgainstExternalAnchor anchor1 0 oldTag = false ∧
      walPreSignStep wal0 pkDig 0 [0x02] = .ok wal0 (.authorizedFresh 0) := by
  let pkDig := List.replicate 32 (0xAA : UInt8)
  let wal0 := initWalLatchState pkDig
  let wal1 := walCommitAuthorized wal0 0 [0x01] (packWire [0x99])
  let anchor1 : ExternalMonotoneAnchor := ⟨1, List.replicate 32 0xBB⟩
  let oldTag := List.replicate 32 (0xCC : UInt8)
  refine ⟨pkDig, wal0, wal1, anchor1, oldTag, by decide, ?_, by decide⟩
  exact externalAnchor_rejects_whole_disk_rollback oldTag (by decide : 0 < 1)

/-- Concrete inhabitedness witness demonstrating `acceptQuorum_implies_validThresholdApproval`
    and `CustodyTsigAligned` are jointly satisfiable on non-trivial 2-of-3 quorum parameters. -/
theorem witness_custody_tsig_aligned_inhabited :
    ∃ (d : Custody.Deployment) (st : IdealTsigState Unit (List UInt8)),
      0 < d.threshold ∧ st.corruptParties ≠ [] ∧ CustodyTsigAligned d st := by
  let sk0 : PqSecretKey := ⟨List.replicate 32 1, List.replicate 32 2, List.replicate 32 3⟩
  let cfg : Custody.SigningConfig := ⟨cshake256Suite, compactJortsProdParams, [], 1⟩
  let mk0 : BdozVerifierKeys := ⟨towerOne 7, towerOne 7, fun _ => (towerOne 7, towerOne 7)⟩
  let rp : Custody.RoundPolicy := ⟨fun _ _ => mk0, [0], fun _ => []⟩
  let pol0 := demoQuorumCustodian 0 (List.replicate 32 0x55) (List.replicate 32 0x66)
  let d : Custody.Deployment :=
    { deploymentId := 7
      signer := cfg
      keys := fun _ => sk0
      rounds := fun _ => rp
      caps := fun _ => 100
      policies := fun _ => pol0
      numParties := 3
      threshold := 2
      capacity := 100 }
  let st : IdealTsigState Unit (List UInt8) := ⟨(), 2, 3, [2], [], []⟩
  refine ⟨d, st, by decide, by decide, ?_⟩
  exact ⟨rfl, rfl, by decide, by decide, by decide, fun c hc => by
    rcases List.mem_singleton.mp hc with rfl
    decide⟩

#verify_constructive acceptQuorum_implies_validThresholdApproval
#verify_constructive custodyHistory_submit_validThresholdApproval_and_provenance
#verify_constructive tooth_unauthenticated_approvers_bypass_without_custody_certs
#verify_constructive projectPartyLocalShares_absent_none
#verify_constructive quarantinePartyNodes_isolates_and_wipes
#verify_constructive GroundedRssSigningBundle.matchesKey
#verify_constructive GroundedRssSigningBundle.mpcDerivedPk_eq_enrolledPk
#verify_constructive evalNonHidingRssCutRelease_sound
#verify_constructive tooth_option_hiding_vs_non_hiding_zero_grind
#verify_constructive encodeDurableLatchPayload_injective
#verify_constructive posixWalCommit_refines_walCommitBeforeRelease
#verify_constructive posixWalIoError_quarantines_both
#verify_constructive tooth_unanchored_snapshot_rollback_replays_epoch
#verify_constructive witness_custody_tsig_aligned_inhabited

#tooth_pair acceptQuorum_implies_validThresholdApproval vs tooth_unauthenticated_approvers_bypass_without_custody_certs
#tooth_pair evalNonHidingRssCutRelease_sound vs tooth_option_hiding_vs_non_hiding_zero_grind
#tooth_pair posixWalCommit_refines_walCommitBeforeRelease vs tooth_unanchored_snapshot_rollback_replays_epoch

end Qsag
end
