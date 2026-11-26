module

public import Qsag.Exec.PosixCrashWal.GenesisSealedWal
import Qsag.Tactic.AssuranceKit

public section

namespace Qsag

set_option autoImplicit false

/-! ### Unified Ceremony Journal, Deterministic Replay Views, & Crash-Prefix Atomicity -/

/-- Exact fixed-width byte prefix splitter (`splitExactBytes n bs = some (bs.take n, bs.drop n)`). -/
@[expose] def splitExactBytes (n : Nat) (bs : List UInt8) : Option (List UInt8 × List UInt8) :=
  if bs.length < n then none else some (bs.take n, bs.drop n)

@[simp]
theorem splitExactBytes_append {n : Nat} {xs ys : List UInt8} (hLen : xs.length = n) :
    splitExactBytes n (xs ++ ys) = some (xs, ys) := by
  unfold splitExactBytes
  have hNotLt : ¬ ((xs ++ ys).length < n) := by
    rw [List.length_append, hLen]
    exact Nat.not_lt_of_ge (Nat.le_add_right n ys.length)
  simp only [hNotLt, ↓reduceIte,
    take_append_of_len_eq hLen,
    drop_append_of_len_eq hLen]

/-- Lifecycle phase recorded in the unified per-key `CeremonyJournalRecord`. -/
inductive CeremonyRecordPhase where
  | genesisIdle     -- Epoch-0 provisioned journal before any ceremony executes
  | round1Reserved  -- Durable intent & all resource burns committed BEFORE Round-1 network output
  | released        -- Final ceremony signature release committed
  deriving Repr, DecidableEq

/-- Canonical single-byte tag for `CeremonyRecordPhase`. -/
def CeremonyRecordPhase.encodeByte : CeremonyRecordPhase → UInt8
  | .genesisIdle    => 0x00
  | .round1Reserved => 0x01
  | .released       => 0x02

/-- Canonical single-byte decoder for `CeremonyRecordPhase`. -/
def CeremonyRecordPhase.decodeByte : UInt8 → Option CeremonyRecordPhase
  | 0x00 => some .genesisIdle
  | 0x01 => some .round1Reserved
  | 0x02 => some .released
  | _    => none

@[simp]
theorem CeremonyRecordPhase.decodeByte_encodeByte (p : CeremonyRecordPhase) :
    CeremonyRecordPhase.decodeByte p.encodeByte = some p := by
  cases p <;> rfl

/-- **Unified Per-Key Ceremony Journal Record (`CeremonyJournalRecord`)**:
    Atomically binds transaction identity, message/context, cumulative `PolicyGuard` spend,
    `BeltLatch`/`Frontier` leaf or epoch reservation, `Baggy` `FirstSigned` codeword digest,
    `pcg_dense` RNG seed generation, preprocessing correlation cursor, and threshold MPC
    Round-1 nonce slot inside a single `GenesisSealedWal` record. -/
structure CeremonyJournalRecord where
  phase                 : CeremonyRecordPhase
  txId                  : List UInt8
  msgContext            : List UInt8
  policyCumulativeSpend : Nat
  txSpendDelta          : Nat
  reservedLeafOrEpoch   : Nat
  nextLeafOrEpoch       : Nat
  baggyCodewordDigest   : List UInt8
  reservedRngSeedGen    : Nat
  nextRngSeedGen        : Nat
  reservedMpcPrepCursor : Nat
  nextMpcPrepCursor     : Nat
  reservedMpcNonceSlot  : Nat
  nextMpcNonceSlot      : Nat
  deriving Repr, DecidableEq

/-- Width invariants on `CeremonyJournalRecord` ensuring collision-free fixed/framed encoding `< 2^32`. -/
def CeremonyJournalRecord.WellFormed (j : CeremonyJournalRecord) : Prop :=
  j.txId.length = 32 ∧
  j.baggyCodewordDigest.length = 32 ∧
  j.msgContext.length ≤ 4096 ∧
  j.policyCumulativeSpend < 2 ^ 64 ∧
  j.txSpendDelta < 2 ^ 64 ∧
  j.reservedLeafOrEpoch < 2 ^ 64 ∧
  j.nextLeafOrEpoch < 2 ^ 64 ∧
  j.reservedRngSeedGen < 2 ^ 64 ∧
  j.nextRngSeedGen < 2 ^ 64 ∧
  j.reservedMpcPrepCursor < 2 ^ 64 ∧
  j.nextMpcPrepCursor < 2 ^ 64 ∧
  j.reservedMpcNonceSlot < 2 ^ 64 ∧
  j.nextMpcNonceSlot < 2 ^ 64

/-- Right-associative canonical serialization of `CeremonyJournalRecord`. -/
def encodeCeremonyJournalRecord (j : CeremonyJournalRecord) : List UInt8 :=
  [j.phase.encodeByte] ++
    (j.txId ++
      (j.baggyCodewordDigest ++
        (encodeU64BeNat j.policyCumulativeSpend ++
          (encodeU64BeNat j.txSpendDelta ++
            (encodeU64BeNat j.reservedLeafOrEpoch ++
              (encodeU64BeNat j.nextLeafOrEpoch ++
                (encodeU64BeNat j.reservedRngSeedGen ++
                  (encodeU64BeNat j.nextRngSeedGen ++
                    (encodeU64BeNat j.reservedMpcPrepCursor ++
                      (encodeU64BeNat j.nextMpcPrepCursor ++
                        (encodeU64BeNat j.reservedMpcNonceSlot ++
                          (encodeU64BeNat j.nextMpcNonceSlot ++
                            pcwFrameBytes j.msgContext))))))))))))

/-- Canonical decoder for `CeremonyJournalRecord`, rejecting truncated or trailing bytes. -/
def decodeCeremonyJournalRecord (bs : List UInt8) : Option CeremonyJournalRecord :=
  match splitExactBytes 1 bs with
  | none => none
  | some (bPhase, r0) =>
    match bPhase with
    | [phaseByte] =>
      match CeremonyRecordPhase.decodeByte phaseByte with
      | none => none
      | some phase =>
        match splitExactBytes 32 r0 with
        | none => none
        | some (txId, r1) =>
          match splitExactBytes 32 r1 with
          | none => none
          | some (baggyDigest, r2) =>
            match splitExactBytes 8 r2 with
            | none => none
            | some (bPolCum, r3) =>
              match decodeU64BeNat bPolCum with
              | none => none
              | some polCum =>
                match splitExactBytes 8 r3 with
                | none => none
                | some (bTxDelta, r4) =>
                  match decodeU64BeNat bTxDelta with
                  | none => none
                  | some txDelta =>
                    match splitExactBytes 8 r4 with
                    | none => none
                    | some (bResLeaf, r5) =>
                      match decodeU64BeNat bResLeaf with
                      | none => none
                      | some resLeaf =>
                        match splitExactBytes 8 r5 with
                        | none => none
                        | some (bNextLeaf, r6) =>
                          match decodeU64BeNat bNextLeaf with
                          | none => none
                          | some nextLeaf =>
                            match splitExactBytes 8 r6 with
                            | none => none
                            | some (bResRng, r7) =>
                              match decodeU64BeNat bResRng with
                              | none => none
                              | some resRng =>
                                match splitExactBytes 8 r7 with
                                | none => none
                                | some (bNextRng, r8) =>
                                  match decodeU64BeNat bNextRng with
                                  | none => none
                                  | some nextRng =>
                                    match splitExactBytes 8 r8 with
                                    | none => none
                                    | some (bResPrep, r9) =>
                                      match decodeU64BeNat bResPrep with
                                      | none => none
                                      | some resPrep =>
                                        match splitExactBytes 8 r9 with
                                        | none => none
                                        | some (bNextPrep, r10) =>
                                          match decodeU64BeNat bNextPrep with
                                          | none => none
                                          | some nextPrep =>
                                            match splitExactBytes 8 r10 with
                                            | none => none
                                            | some (bResNonce, r11) =>
                                              match decodeU64BeNat bResNonce with
                                              | none => none
                                              | some resNonce =>
                                                match splitExactBytes 8 r11 with
                                                | none => none
                                                | some (bNextNonce, r12) =>
                                                  match decodeU64BeNat bNextNonce with
                                                  | none => none
                                                  | some nextNonce =>
                                                    match pcwUnframeBytes r12 with
                                                    | none => none
                                                    | some (msgCtx, msgTail) =>
                                                      match msgTail with
                                                      | [] =>
                                                        if msgCtx.length ≤ 4096 then
                                                          some { phase := phase
                                                                 txId := txId
                                                                 msgContext := msgCtx
                                                                 policyCumulativeSpend := polCum
                                                                 txSpendDelta := txDelta
                                                                 reservedLeafOrEpoch := resLeaf
                                                                 nextLeafOrEpoch := nextLeaf
                                                                 baggyCodewordDigest := baggyDigest
                                                                 reservedRngSeedGen := resRng
                                                                 nextRngSeedGen := nextRng
                                                                 reservedMpcPrepCursor := resPrep
                                                                 nextMpcPrepCursor := nextPrep
                                                                 reservedMpcNonceSlot := resNonce
                                                                 nextMpcNonceSlot := nextNonce }
                                                        else none
                                                      | _ :: _ => none
    | _ => none

theorem encodeCeremonyJournalRecord_lt_two_pow_32 {j : CeremonyJournalRecord}
    (hWf : j.WellFormed) :
    (encodeCeremonyJournalRecord j).length < 2 ^ 32 := by
  rcases hWf with ⟨hTx, hBag, hMsgLe, _⟩
  apply lt_two_pow_32_of_le_8192
  rw [encodeCeremonyJournalRecord.eq_1]
  simp only [List.length_append, List.length_cons, List.length_nil,
    encodeU64BeNat_length, pcwFrameBytes_length, hTx, hBag]
  omega

theorem decodeCeremonyJournalRecord_encodeCeremonyJournalRecord {j : CeremonyJournalRecord}
    (hWf : j.WellFormed) :
    decodeCeremonyJournalRecord (encodeCeremonyJournalRecord j) = some j := by
  rcases hWf with ⟨hTx, hBag, hMsgLe, hPol, hDel, hRL, hNL, hRR, hNR, hRP, hNP, hRN, hNN⟩
  have hMsg32 : j.msgContext.length < 2 ^ 32 :=
    lt_two_pow_32_of_le_8192 (Nat.le_trans hMsgLe (by decide : 4096 ≤ 8192))
  rw [decodeCeremonyJournalRecord.eq_1, encodeCeremonyJournalRecord.eq_1]
  generalize hTail : pcwFrameBytes j.msgContext = tailBytes
  have hPhaseLen : ([j.phase.encodeByte] : List UInt8).length = 1 := rfl
  rw [splitExactBytes_append hPhaseLen]; dsimp only
  rw [CeremonyRecordPhase.decodeByte_encodeByte]; dsimp only
  rw [splitExactBytes_append hTx]; dsimp only
  rw [splitExactBytes_append hBag]; dsimp only
  rw [splitExactBytes_append (encodeU64BeNat_length _)]; dsimp only
  rw [decodeU64BeNat_encodeU64BeNat hPol]; dsimp only
  rw [splitExactBytes_append (encodeU64BeNat_length _)]; dsimp only
  rw [decodeU64BeNat_encodeU64BeNat hDel]; dsimp only
  rw [splitExactBytes_append (encodeU64BeNat_length _)]; dsimp only
  rw [decodeU64BeNat_encodeU64BeNat hRL]; dsimp only
  rw [splitExactBytes_append (encodeU64BeNat_length _)]; dsimp only
  rw [decodeU64BeNat_encodeU64BeNat hNL]; dsimp only
  rw [splitExactBytes_append (encodeU64BeNat_length _)]; dsimp only
  rw [decodeU64BeNat_encodeU64BeNat hRR]; dsimp only
  rw [splitExactBytes_append (encodeU64BeNat_length _)]; dsimp only
  rw [decodeU64BeNat_encodeU64BeNat hNR]; dsimp only
  rw [splitExactBytes_append (encodeU64BeNat_length _)]; dsimp only
  rw [decodeU64BeNat_encodeU64BeNat hRP]; dsimp only
  rw [splitExactBytes_append (encodeU64BeNat_length _)]; dsimp only
  rw [decodeU64BeNat_encodeU64BeNat hNP]; dsimp only
  rw [splitExactBytes_append (encodeU64BeNat_length _)]; dsimp only
  rw [decodeU64BeNat_encodeU64BeNat hRN]; dsimp only
  rw [splitExactBytes_append (encodeU64BeNat_length _)]; dsimp only
  rw [decodeU64BeNat_encodeU64BeNat hNN]; dsimp only
  rw [← hTail]
  have hUnf : pcwUnframeBytes (pcwFrameBytes j.msgContext) = some (j.msgContext, []) := by
    simpa only [List.append_nil] using
      (pcwUnframe_frame_append (rest := []) hMsg32)
  rw [hUnf]
  dsimp only
  simp only [hMsgLe, ↓reduceIte]

attribute [irreducible] encodeCeremonyJournalRecord decodeCeremonyJournalRecord

/-- Subordinate authority ledger views deterministically derived by replaying `CeremonyJournalRecord`. -/
structure SubordinateLedgerViews where
  beltNextEpoch         : Nat
  baggyLastCommitted    : Option (List UInt8 × List UInt8)
  rngNextSeedGen        : Nat
  mpcNextPrepCursor     : Nat
  mpcNextNonceSlot      : Nat
  policyCumulativeSpend : Nat
  deriving Repr, DecidableEq

/-- Deterministic replay projection deriving all 6 subordinate authority views from one journal record. -/
def deriveSubordinateViews (j : CeremonyJournalRecord) : SubordinateLedgerViews :=
  { beltNextEpoch := j.nextLeafOrEpoch
    baggyLastCommitted :=
      match j.phase with
      | .genesisIdle => none
      | .round1Reserved | .released => some (j.txId, j.baggyCodewordDigest)
    rngNextSeedGen := j.nextRngSeedGen
    mpcNextPrepCursor := j.nextMpcPrepCursor
    mpcNextNonceSlot := j.nextMpcNonceSlot
    policyCumulativeSpend := j.policyCumulativeSpend }

/-- **`CrashRecoverCeremony`**:
    Recovers the full ceremony state and subordinate ledger views from `PosixFsState` by opening
    the dual-bound `GenesisSealedWal`, verifying `lockGenesisId` + 256-bit `keyedMac`, decoding
    `CeremonyJournalRecord`, and replaying `deriveSubordinateViews`. -/
def CrashRecoverCeremony (st : PosixFsState) (pid : Pid) (basePath : DirName)
    (vaultKeyId : List UInt8) (macFn : KeyedMacFn) (macKey : List UInt8) :
    PosixFsState × Except PosixErr (WalRecord × CeremonyJournalRecord × SubordinateLedgerViews) :=
  match openExisting st pid basePath vaultKeyId macFn macKey with
  | (stErr, .error e) => (stErr, .error e)
  | (stOpen, .ok (h, rec)) =>
    let stClosed := (closeVaultHandle stOpen h).toOption.getD stOpen
    match decodeCeremonyJournalRecord rec.body.payload with
    | none => (stClosed, .error .einval)
    | some j => (stClosed, .ok (rec, j, deriveSubordinateViews j))

/-- Abstract-model Round-1 receipt data. This public Lean value is not an unforgeable capability;
    only issuance and consumption in a reachable machine execution authorize output. -/
structure DurableRound1Lease where
  txId                  : List UInt8
  msgContext            : List UInt8
  txSpendDelta          : Nat
  policySpendCharged    : Nat
  leafOrEpoch           : Nat
  baggyCodewordDigest   : List UInt8
  rngSeedGen            : Nat
  mpcPrepCursor         : Nat
  mpcNonceSlot          : Nat
  walEpoch              : Nat
  deriving Repr, DecidableEq

/-- Pure Round-1 output formatter. The reachable machine transition supplies authority. -/
def emitRound1NetworkPacket (lease : DurableRound1Lease) : Round1NetworkPacket :=
  { txId := lease.txId
    msgContext := lease.msgContext
    policySpendCharged := lease.policySpendCharged
    leafOrEpoch := lease.leafOrEpoch
    baggyCodewordDigest := lease.baggyCodewordDigest
    rngSeedGen := lease.rngSeedGen
    mpcPrepCursor := lease.mpcPrepCursor
    mpcNonceSlot := lease.mpcNonceSlot }

/-- Abstract-model release receipt data; the trace transition, not this public constructor,
    supplies authority. See `RustDurability.IssuedReceipt` for reachability-backed evidence. -/
structure DurableReleaseReceipt where
  txId                  : List UInt8
  msgContext            : List UInt8
  policySpendCharged    : Nat
  leafOrEpoch           : Nat
  baggyCodewordDigest   : List UInt8
  rngSeedGen            : Nat
  mpcPrepCursor         : Nat
  mpcNonceSlot          : Nat
  releaseWalEpoch       : Nat
  deriving Repr, DecidableEq

/-- Externally released final ceremony signature artifact gated by `DurableReleaseReceipt`. -/
structure ReleasedCeremonySig where
  txId                  : List UInt8
  msgContext            : List UInt8
  policySpendCharged    : Nat
  leafOrEpoch           : Nat
  baggyCodewordDigest   : List UInt8
  rngSeedGen            : Nat
  mpcPrepCursor         : Nat
  mpcNonceSlot          : Nat
  sigBytes              : List UInt8
  deriving Repr, DecidableEq

/-- Pure output formatter. Calling it is not an authorized release transition. -/
def releaseCeremonySignature (rcpt : DurableReleaseReceipt) (sigBytes : List UInt8) :
    ReleasedCeremonySig :=
  { txId := rcpt.txId
    msgContext := rcpt.msgContext
    policySpendCharged := rcpt.policySpendCharged
    leafOrEpoch := rcpt.leafOrEpoch
    baggyCodewordDigest := rcpt.baggyCodewordDigest
    rngSeedGen := rcpt.rngSeedGen
    mpcPrepCursor := rcpt.mpcPrepCursor
    mpcNonceSlot := rcpt.mpcNonceSlot
    sigBytes := sigBytes }

/-- Predicate certifying that every reservation required by a released ceremony `sig` is durably
    reflected in recovered `SubordinateLedgerViews` (`Released(tx) -> all_required_reservations_durable(tx)`). -/
def AllRequiredReservationsDurable (sig : ReleasedCeremonySig)
    (views : SubordinateLedgerViews) : Prop :=
  sig.policySpendCharged ≤ views.policyCumulativeSpend ∧
  sig.leafOrEpoch < views.beltNextEpoch ∧
  sig.rngSeedGen < views.rngNextSeedGen ∧
  sig.mpcPrepCursor < views.mpcNextPrepCursor ∧
  sig.mpcNonceSlot < views.mpcNextNonceSlot

/-- Predicate certifying that every reservation consumed by an emitted Round-1 packet `pkt`
    (even if the ceremony later crashed/aborted before signature release!) is durably burned. -/
def AllRound1ReservationsDurable (pkt : Round1NetworkPacket)
    (views : SubordinateLedgerViews) : Prop :=
  pkt.policySpendCharged ≤ views.policyCumulativeSpend ∧
  pkt.leafOrEpoch < views.beltNextEpoch ∧
  pkt.rngSeedGen < views.rngNextSeedGen ∧
  pkt.mpcPrepCursor < views.mpcNextPrepCursor ∧
  pkt.mpcNonceSlot < views.mpcNextNonceSlot

/-- Deterministic ceremony recovery theorem (`crashRecoverCeremony_of_crashed_durable`):
    On any rebooted/crashed state (`openFds = {}`, `flockTable = {}`) satisfying `VaultDurableAt`
    with `rec.body.payload = encodeCeremonyJournalRecord j` and `j.WellFormed`,
    `CrashRecoverCeremony` deterministically succeeds and returns `(rec, j, deriveSubordinateViews j)`. -/
theorem crashRecoverCeremony_of_crashed_durable
    {st : PosixFsState} {basePath : DirName} {lockIno : InodeId} {genesisNonce : List UInt8}
    {macFn : KeyedMacFn} {macKey : List UInt8} {rec : WalRecord} {j : CeremonyJournalRecord}
    (pid : Pid)
    (hFdsEmpty : st.kernel.openFds = {})
    (hFlkEmpty : st.kernel.flockTable = {})
    (hDur : VaultDurableAt st basePath lockIno genesisNonce macFn macKey rec)
    (hPay : rec.body.payload = encodeCeremonyJournalRecord j)
    (hJWf : j.WellFormed) :
    ∃ stOut,
      CrashRecoverCeremony st pid basePath rec.body.vaultKeyId macFn macKey =
        (stOut, .ok (rec, j, deriveSubordinateViews j)) := by
  obtain ⟨stOpen, hOut, hOpen⟩ :=
    openExisting_of_crashed_durable pid hFdsEmpty hFlkEmpty hDur
  unfold CrashRecoverCeremony
  rw [hOpen]
  dsimp +zetaDelta only
  rw [hPay, decodeCeremonyJournalRecord_encodeCeremonyJournalRecord hJWf]
  exact ⟨_, rfl⟩

/-- Exact readback lemma for `openExisting` on any state satisfying `VaultDurableAt`:
    even when arbitrary unrelated descriptors are open, if `openExisting` returns `.ok (h, readRec)`,
    then `readRec = curRec` and `VaultDurableAt` continues to hold in `st1`! -/
theorem openExisting_ok_of_vaultDurableAt
    {st st1 : PosixFsState} {pid : Pid} {basePath : DirName} {vkId : List UInt8}
    {lockIno : InodeId} {genesisNonce : List UInt8}
    {macFn : KeyedMacFn} {macKey : List UInt8}
    {curRec readRec : WalRecord} {h : LockedVaultHandle}
    (hDur : VaultDurableAt st basePath lockIno genesisNonce macFn macKey curRec)
    (hOpen : openExisting st pid basePath vkId macFn macKey = (st1, .ok (h, readRec))) :
    readRec = curRec ∧
    h.basePath = basePath ∧
    h.vaultKeyId = curRec.body.vaultKeyId ∧
    h.lockGenesisId = computeLockGenesisId lockIno genesisNonce ∧
    VaultDurableAt st1 basePath lockIno genesisNonce macFn macKey curRec := by
  have hOpenKeep : ∀ (sA sB : PosixFsState) (p : Pid) (nm : DirName) (w : Bool) (fd : FdId),
      posixOpenExistingNoFollow sA p nm w = .ok (sB, fd) →
      sB.kernel.dirInode = sA.kernel.dirInode ∧
      sB.kernel.pageCache = sA.kernel.pageCache ∧
      sB.driveCache = sA.driveCache ∧ sB.nand = sA.nand := by
    intro sA sB p nm w fd hO
    rw [posixOpenExistingNoFollow.public_eq_1] at hO
    cases hR : resolveDentryNoFollow sA.kernel.dirInode.unsyncedEntries nm with
    | error _ => rw [hR] at hO; cases hO
    | ok _ =>
      rw [hR] at hO; injection hO with hP; rw [← (Prod.mk.inj hP).1]; exact ⟨rfl, rfl, rfl, rfl⟩
  rcases hDur with ⟨hLockLt, hLock64, hNonceLen, hCurWf, hCurGid, hCurVer, hDrvDir,
    hLockUnsync, hLockNandDir, hLockPg, hLockDrv, hLockNand,
    recIno, hRecLt, hRecUnsync, hRecNandDir, hRecPg, hRecDrv, hRecNand⟩
  rw [openExisting.public_eq_1] at hOpen
  cases hOp1 : posixOpenExistingNoFollow st pid (walLockPath basePath) true with
  | error _ => rw [hOp1] at hOpen; cases (Prod.mk.inj hOpen).2
  | ok p1 =>
    rcases p1 with ⟨sA, lockFd⟩
    have hsA := hOpenKeep _ _ _ _ _ _ hOp1
    rw [hOp1] at hOpen; dsimp only at hOpen
    cases hFlk : posixFlockExNb sA pid lockFd with
    | error _ => rw [hFlk] at hOpen; cases (Prod.mk.inj hOpen).2
    | ok sB =>
      have hsB_A := posixFlockExNb_preserves_storage hFlk
      have hsB : sB.kernel.dirInode = st.kernel.dirInode ∧
                 sB.kernel.pageCache = st.kernel.pageCache ∧
                 sB.driveCache = st.driveCache ∧ sB.nand = st.nand :=
        ⟨hsB_A.1.trans hsA.1, hsB_A.2.1.trans hsA.2.1,
         hsB_A.2.2.1.trans hsA.2.2.1, hsB_A.2.2.2.trans hsA.2.2.2⟩
      rw [hFlk] at hOpen; dsimp only at hOpen
      cases hFst : posixFstatDescAndInode sB pid lockFd with
      | error _ => rw [hFst] at hOpen; cases (Prod.mk.inj hOpen).2
      | ok dIno =>
        rcases dIno with ⟨lockDescId, actualLockIno⟩
        cases hPr1 : posixPreadAll sB pid lockFd with
        | error _ => rw [hFst, hPr1] at hOpen; cases (Prod.mk.inj hOpen).2
        | ok rawL =>
          rw [hFst, hPr1] at hOpen; dsimp only at hOpen
          cases hDL : decodeLockSidecar rawL with
          | none => rw [hDL] at hOpen; cases (Prod.mk.inj hOpen).2
          | some ls =>
            rw [hDL] at hOpen; dsimp only at hOpen
            by_cases hM1 : (actualLockIno != ls.sealedLockInode) = true
            · simp only [hM1, ↓reduceIte] at hOpen; cases (Prod.mk.inj hOpen).2
            · simp only [hM1, Bool.false_eq_true, ↓reduceIte] at hOpen
              have hResRec : resolveDentryNoFollow sB.kernel.dirInode.unsyncedEntries basePath = .ok recIno := by
                rw [resolveDentryNoFollow.public_eq_1]; rw [hsB.1, hRecUnsync]
              let recDescId := sB.kernel.openFds.nextDescId
              let sC0 : PosixFsState :=
                { sB with
                   kernel := { sB.kernel with
                                openFds := { fdRefs := assocInsert (pid, sB.nextFd) recDescId sB.kernel.openFds.fdRefs
                                             descriptions := assocInsert recDescId
                                               { inode := recIno, writable := false, stickyFsyncErr := false }
                                               sB.kernel.openFds.descriptions
                                             nextDescId := recDescId + 1 } }
                   nextFd := sB.nextFd + 1 }
              have hOp2Eq : ∃ sC recFd,
                  posixOpenExistingNoFollow sB pid basePath false = .ok (sC, recFd) ∧
                  sC.kernel.dirInode = st.kernel.dirInode ∧
                  sC.kernel.pageCache = st.kernel.pageCache ∧
                  sC.driveCache = st.driveCache ∧ sC.nand = st.nand ∧
                  posixPreadAll sC pid recFd = .ok (encodeWalRecord curRec) := by
                refine ⟨sC0, sB.nextFd, ?_, hsB.1, hsB.2.1, hsB.2.2.1, hsB.2.2.2, ?_⟩
                · rw [posixOpenExistingNoFollow.public_eq_1]; rw [hResRec]
                · rw [posixPreadAll.public_eq_1]
                  unfold readInodeHierarchy
                  unfold pendingVolatileWrite
                  simp only [sC0, resolveOpenFd_insert_self, Bool.false_eq_true, ↓reduceIte]
                  rw [hsB.2.1, hsB.2.2.1, hsB.2.2.2, hRecPg, hRecDrv, hRecNand]
              rcases hOp2Eq with ⟨sC, recFd, hOp2, hsCDir, hsCPg, hsCDr, hsCNd, hPr2⟩
              rw [hOp2] at hOpen; dsimp +zetaDelta only at hOpen
              rw [hPr2] at hOpen; dsimp +zetaDelta only at hOpen
              rw [decodeWalRecord_encodeWalRecord hCurWf] at hOpen; dsimp +zetaDelta only at hOpen
              by_cases hGidM : (curRec.body.lockGenesisId !=
                  computeLockGenesisId actualLockIno ls.genesisNonce) = true
              · simp only [hGidM, ↓reduceIte] at hOpen; cases (Prod.mk.inj hOpen).2
              · simp only [hGidM, Bool.false_eq_true, ↓reduceIte] at hOpen
                by_cases hMacM : (curRec.body.vaultKeyId != vkId ||
                    !(verifyWalMac macFn macKey curRec)) = true
                · simp only [hMacM, ↓reduceIte] at hOpen; cases (Prod.mk.inj hOpen).2
                · simp only [hMacM, Bool.false_eq_true, ↓reduceIte] at hOpen
                  rcases Prod.mk.inj hOpen with ⟨hSt1Eq, hOkPair⟩
                  injection hOkPair with hPairEq
                  rcases Prod.mk.inj hPairEq with ⟨hHEq, hReadEq⟩
                  subst hReadEq
                  have hGidEq : computeLockGenesisId actualLockIno ls.genesisNonce =
                      computeLockGenesisId lockIno genesisNonce :=
                    (eq_of_not_bne_true hGidM).symm.trans hCurGid
                  have hVkEq : vkId = curRec.body.vaultKeyId :=
                    (eq_of_not_bne_true (fun hc => hMacM (by simp [hc]))).symm
                  have hc4 := posixCloseFd_preserves_storage sC pid recFd
                  have hSt1Dir : st1.kernel.dirInode = st.kernel.dirInode := by
                    rw [← hSt1Eq]; exact hc4.1.trans hsCDir
                  have hSt1Pg : st1.kernel.pageCache = st.kernel.pageCache := by
                    rw [← hSt1Eq]; exact hc4.2.1.trans hsCPg
                  have hSt1Dr : st1.driveCache = st.driveCache := by
                    rw [← hSt1Eq]; exact hc4.2.2.1.trans hsCDr
                  have hSt1Nd : st1.nand = st.nand := by
                    rw [← hSt1Eq]; exact hc4.2.2.2.trans hsCNd
                  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
                  · rw [← hHEq]
                  · rw [← hHEq]; exact hVkEq
                  · rw [← hHEq]; exact hGidEq
                  · unfold VaultDurableAt
                    rw [hSt1Dir, hSt1Pg, hSt1Dr, hSt1Nd]
                    exact ⟨hLockLt, hLock64, hNonceLen, hCurWf, hCurGid, hCurVer, hDrvDir,
                      hLockUnsync, hLockNandDir, hLockPg, hLockDrv, hLockNand,
                      recIno, hRecLt, hRecUnsync, hRecNandDir, hRecPg, hRecDrv, hRecNand⟩

private theorem replaceAtomic_fst_mem_steps (st : PosixFsState) (h : LockedVaultHandle)
    (ep : Nat) (pay : List UInt8) (macFn : KeyedMacFn) (macKey : List UInt8)
    (faults : IoFaultSchedule) :
    (replaceAtomic st h ep pay macFn macKey faults).1 ∈
      replaceAtomicSteps st h ep pay macFn macKey faults := by
  rw [replaceAtomic.public_eq_1]
  rw [replaceAtomicSteps.public_eq_1]
  by_cases h1 : h.ioPoisoned = true
  · simp [h1]
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : (!(decide (ep < 2 ^ 64)) || !(decide (pay.length < 2 ^ 32))) = true
    · simp [h2]
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      cases resolveOpenFd st.kernel.openFds h.pid h.lockFd with
      | none => simp
      | some dp =>
        rcases dp with ⟨dId, lDesc⟩
        dsimp only
        by_cases h3 : (dId != h.lockDescId || lDesc.inode != h.lockInode || lDesc.stickyFsyncErr ||
            st.kernel.flockTable.owner h.lockInode != some h.lockDescId) = true
        · simp [h3]
        · simp only [h3, Bool.false_eq_true, ↓reduceIte]
          cases posixCreateExclNoFollow (posixUnlinkIfPresent st (walTmpPath h.basePath)) h.pid (walTmpPath h.basePath) with
          | error _ => simp
          | ok c3 =>
            rcases c3 with ⟨stCr, tmpFd, _⟩
            dsimp only
            cases posixPwriteAll stCr h.pid tmpFd _ with
            | error _ => simp
            | ok stWr =>
              dsimp +zetaDelta only
              cases (posixSyncAllMedia stWr h.pid tmpFd faults.failRecordSync).2 with
              | error _ => simp
              | ok u =>
                cases u
                cases posixRename _ (walTmpPath h.basePath) h.basePath with
                | error _ => simp
                | ok stRn =>
                  dsimp +zetaDelta only
                  cases (posixSyncParentDir stRn faults.failParentSync).2 <;> simp

/-- Genesis idle `CeremonyJournalRecord` (`phase = .genesisIdle`, all watermarks `= 0`). -/
def ceremonyGenesisJournal : CeremonyJournalRecord :=
  { phase := .genesisIdle
    txId := List.replicate 32 0x00
    msgContext := []
    policyCumulativeSpend := 0
    txSpendDelta := 0
    reservedLeafOrEpoch := 0
    nextLeafOrEpoch := 0
    baggyCodewordDigest := List.replicate 32 0x00
    reservedRngSeedGen := 0
    nextRngSeedGen := 0
    reservedMpcPrepCursor := 0
    nextMpcPrepCursor := 0
    reservedMpcNonceSlot := 0
    nextMpcNonceSlot := 0 }

theorem ceremonyGenesisJournal_wellFormed : ceremonyGenesisJournal.WellFormed := by
  have hZ64 : 0 < 2 ^ 64 := Nat.pow_pos (by decide : 0 < 2)
  exact ⟨by decide, by decide, by decide,
    hZ64, hZ64, hZ64, hZ64, hZ64, hZ64, hZ64, hZ64, hZ64, hZ64⟩

/-- Multi-turn ceremony crash state machine combining `PosixFsState` (`GenesisSealedWal`),
    in-memory volatile `pendingRound1Lease` (wiped on any crash!), and externally observed
    `emittedRound1Msgs` and `releasedSigs`. -/
structure CeremonyCrashState where
  fs                 : PosixFsState
  basePath           : DirName
  vaultKeyId         : List UInt8
  policySpendCap     : Nat
  emittedRound1Msgs  : List Round1NetworkPacket
  releasedSigs       : List ReleasedCeremonySig
  pendingRound1Lease : Option DurableRound1Lease
  /-- A journal replacement returned an I/O error. The process is still running, the kernel
      still holds whatever dirty pages and unsynced dentries the failed replacement left, and
      the journal handle is poisoned: no reservation or release is served until a system crash
      and recovery. -/
  ioPoisoned         : Bool := false
  deriving Repr

/-- Provision an initial ceremony vault on `PosixFsState.empty`. -/
@[expose] def initProvisionedCeremonyState (pid : Pid) (basePath : DirName)
    (vaultKeyId genesisNonce : List UInt8) (policySpendCap : Nat)
    (macFn : KeyedMacFn) (macKey : List UInt8) : Option CeremonyCrashState :=
  let initPayload := encodeCeremonyJournalRecord ceremonyGenesisJournal
  match provisionGenesis PosixFsState.empty pid basePath vaultKeyId genesisNonce
          initPayload macFn macKey {} with
  | (_, .error _) => none
  | (fs0, .ok _) =>
    some { fs := fs0
           basePath := basePath
           vaultKeyId := vaultKeyId
           policySpendCap := policySpendCap
           emittedRound1Msgs := []
           releasedSigs := []
           pendingRound1Lease := none }

/-- Adversarial & fault-injected multi-turn ceremony trace events:
    Includes Round-1 reservation + network emission, final signature release gated on
    `DurableReleaseReceipt`, mid-`replaceAtomic` crash cuts during BOTH Round-1 reservation and
    signature release (either crash kind), `KernelPanicCrash` after partial Round-1 network
    output, and `PowerLossCrash` with `512B`/`4KiB` `SectorTearMask`s. An I/O error during a
    replacement is NOT a crash: it poisons the host (`ioPoisoned`) and leaves the kernel state
    as the failed syscall sequence left it. -/
inductive CeremonyCrashEvent where
  | reserveAndEmitRound1
      (pid : Pid) (txId msgCtx : List UInt8) (spendDelta : Nat)
      (baggyDigest : List UInt8) (faults : IoFaultSchedule)
  | midReplaceCrashDuringRound1
      (pid : Pid) (txId msgCtx : List UInt8) (spendDelta : Nat)
      (baggyDigest : List UInt8) (faults : IoFaultSchedule)
      (stepIdx : Nat) (crash : MidOpCrash)
  | releaseSignatureFromRound1
      (pid : Pid) (sigBytes : List UInt8) (faults : IoFaultSchedule)
  | midReplaceCrashDuringRelease
      (pid : Pid) (faults : IoFaultSchedule)
      (stepIdx : Nat) (crash : MidOpCrash)
  | kernelPanic
  | powerLoss
      (dirPick : DirCrashOutcome) (defaultTear : SectorTearMask)
      (overrides : List (InodeId × SectorTearMask))

/-- Check width and policy-cap preconditions for allocating a fresh Round-1 ceremony reservation. -/
def canReserveCeremonyRound1 (curJ : CeremonyJournalRecord) (curWalEpoch policySpendCap : Nat)
    (txId msgCtx : List UInt8) (spendDelta : Nat) (baggyDigest : List UInt8) : Bool :=
  (txId.length == 32) &&
  (baggyDigest.length == 32) &&
  decide (msgCtx.length ≤ 4096) &&
  decide (spendDelta < 2 ^ 64) &&
  decide (curJ.policyCumulativeSpend + spendDelta ≤ policySpendCap) &&
  decide (curJ.policyCumulativeSpend + spendDelta < 2 ^ 64) &&
  decide (curJ.nextLeafOrEpoch + 1 < 2 ^ 64) &&
  decide (curJ.nextRngSeedGen + 1 < 2 ^ 64) &&
  decide (curJ.nextMpcPrepCursor + 1 < 2 ^ 64) &&
  decide (curJ.nextMpcNonceSlot + 1 < 2 ^ 64) &&
  decide (curWalEpoch + 1 < 2 ^ 64)

/-- Build the next `.round1Reserved` journal record advancing all 4 monotone resource watermarks. -/
def buildRound1JournalRecord (curJ : CeremonyJournalRecord)
    (txId msgCtx : List UInt8) (spendDelta : Nat) (baggyDigest : List UInt8) :
    CeremonyJournalRecord :=
  { phase := .round1Reserved
    txId := txId
    msgContext := msgCtx
    policyCumulativeSpend := curJ.policyCumulativeSpend + spendDelta
    txSpendDelta := spendDelta
    reservedLeafOrEpoch := curJ.nextLeafOrEpoch
    nextLeafOrEpoch := curJ.nextLeafOrEpoch + 1
    baggyCodewordDigest := baggyDigest
    reservedRngSeedGen := curJ.nextRngSeedGen
    nextRngSeedGen := curJ.nextRngSeedGen + 1
    reservedMpcPrepCursor := curJ.nextMpcPrepCursor
    nextMpcPrepCursor := curJ.nextMpcPrepCursor + 1
    reservedMpcNonceSlot := curJ.nextMpcNonceSlot
    nextMpcNonceSlot := curJ.nextMpcNonceSlot + 1 }

/-- Single-step execution of `CeremonyCrashEvent` on a host whose journal handle is healthy. -/
def stepCeremonyHealthy (macFn : KeyedMacFn) (macKey : List UInt8)
    (s : CeremonyCrashState) (ev : CeremonyCrashEvent) : CeremonyCrashState :=
  match ev with
  | .reserveAndEmitRound1 pid txId msgCtx spendDelta baggyDigest faults =>
    match openExisting s.fs pid s.basePath s.vaultKeyId macFn macKey with
    | (fsErr, .error _) => { s with fs := fsErr }
    | (fs1, .ok (h, readRec)) =>
      match decodeCeremonyJournalRecord readRec.body.payload with
      | none =>
        { s with fs := (closeVaultHandle fs1 h).toOption.getD fs1 }
      | some curJ =>
        if !(canReserveCeremonyRound1 curJ readRec.body.epoch s.policySpendCap
               txId msgCtx spendDelta baggyDigest) then
          { s with fs := (closeVaultHandle fs1 h).toOption.getD fs1 }
        else
          let nextJ := buildRound1JournalRecord curJ txId msgCtx spendDelta baggyDigest
          let nextPay := encodeCeremonyJournalRecord nextJ
          match replaceAtomic fs1 h (readRec.body.epoch + 1) nextPay macFn macKey faults with
          | (fsFail, _, .error _) =>
            -- I/O error: no Round-1 lease or packet is emitted; the host is poisoned and the
            -- kernel keeps the state the failed replacement left behind (no crash happens).
            { s with fs := fsFail, ioPoisoned := true, pendingRound1Lease := none }
          | (fsOk, hAfter, .ok _) =>
            let fsClosed := (closeVaultHandle fsOk hAfter).toOption.getD fsOk
            let lease : DurableRound1Lease :=
              { txId := txId
                msgContext := msgCtx
                txSpendDelta := spendDelta
                policySpendCharged := curJ.policyCumulativeSpend + spendDelta
                leafOrEpoch := curJ.nextLeafOrEpoch
                baggyCodewordDigest := baggyDigest
                rngSeedGen := curJ.nextRngSeedGen
                mpcPrepCursor := curJ.nextMpcPrepCursor
                mpcNonceSlot := curJ.nextMpcNonceSlot
                walEpoch := readRec.body.epoch + 1 }
            let pkt := emitRound1NetworkPacket lease
            { s with
                fs := fsClosed
                emittedRound1Msgs := s.emittedRound1Msgs ++ [pkt]
                pendingRound1Lease := some lease }
  | .midReplaceCrashDuringRound1 pid txId msgCtx spendDelta baggyDigest faults
      stepIdx crash =>
    match openExisting s.fs pid s.basePath s.vaultKeyId macFn macKey with
    | (fsErr, .error _) =>
      { s with fs := crash.apply fsErr, pendingRound1Lease := none }
    | (fs1, .ok (h, readRec)) =>
      match decodeCeremonyJournalRecord readRec.body.payload with
      | none =>
        { s with fs := crash.apply fs1, pendingRound1Lease := none }
      | some curJ =>
        if !(canReserveCeremonyRound1 curJ readRec.body.epoch s.policySpendCap
               txId msgCtx spendDelta baggyDigest) then
          { s with fs := crash.apply fs1, pendingRound1Lease := none }
        else
          let nextJ := buildRound1JournalRecord curJ txId msgCtx spendDelta baggyDigest
          let steps := replaceAtomicSteps fs1 h (readRec.body.epoch + 1)
                         (encodeCeremonyJournalRecord nextJ) macFn macKey faults
          let mid := pickStepState fs1 steps stepIdx
          { s with fs := crash.apply mid, pendingRound1Lease := none }
  | .releaseSignatureFromRound1 pid sigBytes faults =>
    match s.pendingRound1Lease with
    | none => s
    | some lease =>
      match openExisting s.fs pid s.basePath s.vaultKeyId macFn macKey with
      | (fsErr, .error _) => { s with fs := fsErr }
      | (fs1, .ok (h, readRec)) =>
        match decodeCeremonyJournalRecord readRec.body.payload with
        | none =>
          { s with fs := (closeVaultHandle fs1 h).toOption.getD fs1 }
        | some curJ =>
          if !(decide (readRec.body.epoch + 1 < 2 ^ 64)) then
            { s with fs := (closeVaultHandle fs1 h).toOption.getD fs1 }
          else
            let relJ : CeremonyJournalRecord := { curJ with phase := .released }
            let relPay := encodeCeremonyJournalRecord relJ
            match replaceAtomic fs1 h (readRec.body.epoch + 1) relPay macFn macKey faults with
            | (fsFail, _, .error _) =>
              { s with fs := fsFail, ioPoisoned := true, pendingRound1Lease := none }
            | (fsOk, hAfter, .ok _) =>
              let fsClosed := (closeVaultHandle fsOk hAfter).toOption.getD fsOk
              let rcpt : DurableReleaseReceipt :=
                { txId := lease.txId
                  msgContext := lease.msgContext
                  policySpendCharged := lease.policySpendCharged
                  leafOrEpoch := lease.leafOrEpoch
                  baggyCodewordDigest := lease.baggyCodewordDigest
                  rngSeedGen := lease.rngSeedGen
                  mpcPrepCursor := lease.mpcPrepCursor
                  mpcNonceSlot := lease.mpcNonceSlot
                  releaseWalEpoch := readRec.body.epoch + 1 }
              let sig := releaseCeremonySignature rcpt sigBytes
              { s with
                  fs := fsClosed
                  releasedSigs := s.releasedSigs ++ [sig]
                  pendingRound1Lease := none }
  | .midReplaceCrashDuringRelease pid faults stepIdx crash =>
    match openExisting s.fs pid s.basePath s.vaultKeyId macFn macKey with
    | (fsErr, .error _) =>
      { s with fs := crash.apply fsErr, pendingRound1Lease := none }
    | (fs1, .ok (h, readRec)) =>
      match decodeCeremonyJournalRecord readRec.body.payload with
      | none =>
        { s with fs := crash.apply fs1, pendingRound1Lease := none }
      | some curJ =>
        if !(decide (readRec.body.epoch + 1 < 2 ^ 64)) then
          { s with fs := crash.apply fs1, pendingRound1Lease := none }
        else
          let relJ : CeremonyJournalRecord := { curJ with phase := .released }
          let steps := replaceAtomicSteps fs1 h (readRec.body.epoch + 1)
                         (encodeCeremonyJournalRecord relJ) macFn macKey faults
          let mid := pickStepState fs1 steps stepIdx
          { s with fs := crash.apply mid, pendingRound1Lease := none }
  | .kernelPanic =>
    { s with fs := KernelPanicCrash s.fs, pendingRound1Lease := none }
  | .powerLoss dirPick defaultTear overrides =>
    let tearFn := evalFiniteTearSchedule defaultTear overrides
    { s with fs := PowerLossCrash dirPick tearFn s.fs, pendingRound1Lease := none }

/-- A poisoned host serves nothing. Only a system crash (which may strike at any time,
    including as the "crash" of an attempted operation) clears the poison, by discarding the
    process together with the kernel state the failed replacement left behind. -/
def stepCeremonyPoisoned (s : CeremonyCrashState) : CeremonyCrashEvent → CeremonyCrashState
  | .reserveAndEmitRound1 .. => s
  | .releaseSignatureFromRound1 .. => s
  | .midReplaceCrashDuringRound1 _ _ _ _ _ _ _ crash =>
    { s with fs := crash.apply s.fs, ioPoisoned := false, pendingRound1Lease := none }
  | .midReplaceCrashDuringRelease _ _ _ crash =>
    { s with fs := crash.apply s.fs, ioPoisoned := false, pendingRound1Lease := none }
  | .kernelPanic =>
    { s with fs := KernelPanicCrash s.fs, ioPoisoned := false, pendingRound1Lease := none }
  | .powerLoss dirPick defaultTear overrides =>
    { s with
        fs := PowerLossCrash dirPick (evalFiniteTearSchedule defaultTear overrides) s.fs
        ioPoisoned := false
        pendingRound1Lease := none }

/-- Single-step execution of `CeremonyCrashEvent` on `CeremonyCrashState`. -/
def stepCeremonyCrashState (macFn : KeyedMacFn) (macKey : List UInt8)
    (s : CeremonyCrashState) (ev : CeremonyCrashEvent) : CeremonyCrashState :=
  if s.ioPoisoned then stepCeremonyPoisoned s ev else stepCeremonyHealthy macFn macKey s ev

/-- Execute an arbitrary multi-turn list of `CeremonyCrashEvent`s. -/
def runCeremonyCrashTrace (macFn : KeyedMacFn) (macKey : List UInt8)
    (s : CeremonyCrashState) : List CeremonyCrashEvent → CeremonyCrashState
  | [] => s
  | ev :: rest => runCeremonyCrashTrace macFn macKey (stepCeremonyCrashState macFn macKey s ev) rest

/-- Monotonicity relation between two `CeremonyJournalRecord` watermarks. -/
def CeremonyJournalRecord.MonotoneLe (prev next : CeremonyJournalRecord) : Prop :=
  prev.policyCumulativeSpend ≤ next.policyCumulativeSpend ∧
  prev.nextLeafOrEpoch ≤ next.nextLeafOrEpoch ∧
  prev.nextRngSeedGen ≤ next.nextRngSeedGen ∧
  prev.nextMpcPrepCursor ≤ next.nextMpcPrepCursor ∧
  prev.nextMpcNonceSlot ≤ next.nextMpcNonceSlot

private theorem ceremonyMonotoneLe_refl (j : CeremonyJournalRecord) : j.MonotoneLe j :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

private theorem allRound1ReservationsDurable_mono {pkt : Round1NetworkPacket}
    {j₁ j₂ : CeremonyJournalRecord} (hLe : j₁.MonotoneLe j₂)
    (hDur : AllRound1ReservationsDurable pkt (deriveSubordinateViews j₁)) :
    AllRound1ReservationsDurable pkt (deriveSubordinateViews j₂) :=
  ⟨Nat.le_trans hDur.1 hLe.1,
   Nat.lt_of_lt_of_le hDur.2.1 hLe.2.1,
   Nat.lt_of_lt_of_le hDur.2.2.1 hLe.2.2.1,
   Nat.lt_of_lt_of_le hDur.2.2.2.1 hLe.2.2.2.1,
   Nat.lt_of_lt_of_le hDur.2.2.2.2 hLe.2.2.2.2⟩

private theorem allRequiredReservationsDurable_mono {sig : ReleasedCeremonySig}
    {j₁ j₂ : CeremonyJournalRecord} (hLe : j₁.MonotoneLe j₂)
    (hDur : AllRequiredReservationsDurable sig (deriveSubordinateViews j₁)) :
    AllRequiredReservationsDurable sig (deriveSubordinateViews j₂) :=
  ⟨Nat.le_trans hDur.1 hLe.1,
   Nat.lt_of_lt_of_le hDur.2.1 hLe.2.1,
   Nat.lt_of_lt_of_le hDur.2.2.1 hLe.2.2.1,
   Nat.lt_of_lt_of_le hDur.2.2.2.1 hLe.2.2.2.1,
   Nat.lt_of_lt_of_le hDur.2.2.2.2 hLe.2.2.2.2⟩

private theorem canReserveCeremonyRound1_sound
    {curJ : CeremonyJournalRecord} {curEp cap spendDelta : Nat}
    {txId msgCtx baggyDigest : List UInt8}
    (hCan : canReserveCeremonyRound1 curJ curEp cap txId msgCtx spendDelta baggyDigest = true) :
    let nextJ := buildRound1JournalRecord curJ txId msgCtx spendDelta baggyDigest
    nextJ.WellFormed ∧
    nextJ.policyCumulativeSpend ≤ cap ∧
    curJ.MonotoneLe nextJ ∧
    curEp + 1 < 2 ^ 64 := by
  unfold canReserveCeremonyRound1 at hCan
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hCan
  rcases hCan with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hTxB, hBagB⟩, hMsgLe⟩, hDel64⟩, hCapLe⟩, hCum64⟩,
    hNL64⟩, hNR64⟩, hNP64⟩, hNN64⟩, hEp64⟩
  have hTx : txId.length = 32 := Nat.eq_of_beq_eq_true hTxB
  have hBag : baggyDigest.length = 32 := Nat.eq_of_beq_eq_true hBagB
  dsimp +zetaDelta only [buildRound1JournalRecord]
  exact ⟨⟨hTx, hBag, hMsgLe, hCum64, hDel64,
          Nat.lt_of_le_of_lt (Nat.le_succ _) hNL64, hNL64,
          Nat.lt_of_le_of_lt (Nat.le_succ _) hNR64, hNR64,
          Nat.lt_of_le_of_lt (Nat.le_succ _) hNP64, hNP64,
          Nat.lt_of_le_of_lt (Nat.le_succ _) hNN64, hNN64⟩,
         hCapLe,
         ⟨Nat.le_add_right _ _, Nat.le_succ _, Nat.le_succ _, Nat.le_succ _, Nat.le_succ _⟩,
         hEp64⟩

/-- Ceremony durability & global no-reuse invariant of a host whose storage is settled
    (`VaultDurableAt`: nothing dirty, both dentries on the current journal record). -/
