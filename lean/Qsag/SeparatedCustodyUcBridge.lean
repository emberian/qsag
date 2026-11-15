module
/-
# Qsag.SeparatedCustodyUcBridge — Coherent Custody, Threshold UC, and Crash-WAL Bridges

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

public import Qsag.ThresholdApproval
public import Qsag.IdealTsig
public import Qsag.SeparatedCustodyHistory
public import Qsag.IdealOutputBoundary
public import Qsag.PosixCrashWal
import all Qsag.IdealTsig
import all Qsag.HashSigs
import all Qsag.PosixCrashWal
import all Qsag.SeparatedCustodyHistory
import all Qsag.SeparatedCustodyPolicy
import all Qsag.SeparatedCustodySpine
import all Qsag.CompleteMediationBoundary
import all Qsag.SeparatedCustodyCore
import all Qsag.InteractiveUcEngine
import Qsag.Tactic.AssuranceKit

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

private theorem nodup_filter_bool {α : Type} (p : α → Bool) :
    ∀ {xs : List α}, xs.Nodup → (xs.filter p).Nodup
  | [], .nil => .nil
  | x :: xs, .cons hNotMem hNd => by
    unfold List.filter
    cases hp : p x
    · exact nodup_filter_bool p hNd
    · exact .cons (fun y hy hEq => hNotMem y (mem_filter_bool hy).1 hEq)
        (nodup_filter_bool p hNd)

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
    (hAcc : Custody.acceptQuorum d.signer (Custody.publicKeys d)
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
          ⟨d.keys c.party, Custody.queries d.signer c.party (hist.parties c.party).vault,
            Custody.payload c.party r, c.signature⟩ = true ∧
        (ProdSmTcrBreak d.signer.suite d.signer.params (d.keys c.party)
           (Custody.signingLog d.signer (d.keys c.party) c.party (hist.parties c.party).vault) ∨
         ProdPreimageBreak d.signer.suite d.signer.params (d.keys c.party)
           (Custody.signingLog d.signer (d.keys c.party) c.party (hist.parties c.party).vault)
           (Custody.payload c.party r) c.signature)))) := by
  intro hon hist
  have hVerdict :
      (Custody.submit d.signer (Custody.publicKeys d) d.numParties d.threshold
        hist.shared.coordinator r certs).2 = true := by
    rw [← Custody.submitRecorded_verdict]
    exact hSub
  obtain ⟨hAccQ, hSpendCap, _⟩ := Custody.submit_accepted d.signer (Custody.publicKeys d)
    d.numParties d.threshold hist.shared.coordinator r certs hVerdict
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
    (cfg : Custody.SigningConfig) (pks : Nat → PqPublicKey) (r : Custody.Intent) :
    ∃ (st : IdealTsigState Unit (List UInt8)),
      validThresholdApproval st [0, 1] = true ∧
      Custody.acceptQuorum cfg pks 3 2 [] r [] = false ∧
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
