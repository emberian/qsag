module

public import Qsag.Exec.PosixCrashWal.GenesisSealedWal
import Qsag.Tactic.AssuranceKit

public section

namespace Qsag

set_option autoImplicit false

/-! ### Multi-Crash Reserve-Before-Sign Stateful Custody Machine (`BeltLatch` / `Frontier` / `PolicyGuard`) -/

/-- Stateful signing key families guarded by the `GenesisSealedWal` engine. -/
inductive StatefulKeyKind where
  | beltLatch    -- Distributed/local monotonic epoch latch (`BeltLatch`)
  | frontier     -- Bounded-use few-time rank/chain key (`Frontier`)
  | policyGuard  -- Velocity/budget-enforcing policy guard (`PolicyGuard`)
  deriving Repr, DecidableEq

/-- Encode `StatefulKeyKind` as a single domain byte. -/
def StatefulKeyKind.tagByte : StatefulKeyKind → UInt8
  | .beltLatch   => 0x01
  | .frontier    => 0x02
  | .policyGuard => 0x03

/-- Emitted signature / authorization receipt bound to `(keyKind, vaultKeyId, epoch, msg)`. -/
structure SignedEpochReceipt where
  keyKind    : StatefulKeyKind
  vaultKeyId : List UInt8
  epoch      : Nat
  msg        : List UInt8
  deriving Repr, DecidableEq

/-- Canonical length-framed custody WAL payload (`< 2^32` bytes whenever `msgBounded.length ≤ 4096`). -/
def encodeCustodyWalPayload (kind : StatefulKeyKind) (maxEpochCap : Nat)
    (msg : List UInt8) : List UInt8 :=
  pcwConcatFramed [[kind.tagByte], encodeU64BeNat maxEpochCap, msg.take 4096]

theorem encodeCustodyWalPayload_lt_two_pow_32 (kind : StatefulKeyKind) (maxEpochCap : Nat)
    (msg : List UInt8) :
    (encodeCustodyWalPayload kind maxEpochCap msg).length < 2 ^ 32 := by
  apply lt_two_pow_32_of_le_8192
  rw [encodeCustodyWalPayload.eq_1, pcwConcatFramed_cons, pcwConcatFramed_cons,
      pcwConcatFramed_cons, pcwConcatFramed_nil]
  have hTake : (msg.take 4096).length ≤ 4096 := List.length_take_le 4096 msg
  simp only [List.length_append, List.length_cons, List.length_nil,
    pcwFrameBytes_length, encodeU64BeNat_length]
  omega

/-- Open-world multi-crash + adversarial event alphabet interleaving honest signing, split-phase
    lock holding, concurrent contenders, `KernelPanicCrash`, `PowerLossCrash` with `512B`/`4KiB`
    `SectorTearMask`s, `.lock` `unlink` + spoofed recreation, rogue genesis re-provisioning,
    WAL deletion, and symlink attacks! -/
inductive MultiCrashWalEvent where
  | signAtomic (pid : Pid) (msg : List UInt8) (faults : IoFaultSchedule)
  | beginReserveHoldLock (pid : Pid) (msg : List UInt8) (faults : IoFaultSchedule)
  | finishSignFromHold
  | contenderSignAttempt (contenderPid : Pid) (msg : List UInt8)
  | midReserveCrash (pid : Pid) (msg : List UInt8) (faults : IoFaultSchedule) (stepIdx : Nat)
      (crash : MidOpCrash)
  | kernelPanic
  | powerLoss (dirPick : DirCrashOutcome) (defaultTear : SectorTearMask)
      (perInodeTears : List (InodeId × SectorTearMask))
  | unlinkLockSidecar
  | recreateSpoofLock (actorPid : Pid) (spoofBytes : List UInt8)
  | attemptReprovisionGenesis (actorPid : Pid) (newNonce : List UInt8)
  | deleteWalRecord
  | plantSymlink (entryName : DirName) (targetName : DirName)
  deriving Repr, DecidableEq

/-- Full persistent + volatile system state across multi-crash stateful signing traces. -/
structure MultiCrashCustodyState where
  fs                : PosixFsState
  basePath          : DirName
  keyKind           : StatefulKeyKind
  vaultKeyId        : List UInt8
  enrolledGenesisId : List UInt8
  maxEpochCap       : Nat
  activeHold        : Option (LockedVaultHandle × Nat × List UInt8) := none
  emittedReceipts   : List SignedEpochReceipt := []
  ghostWatermark    : Nat := 0
  deriving Repr, DecidableEq

/-- Execute a single atomic **reserve-before-sign** turn (`openExisting` → `replaceAtomic`
    advancing `epoch := e + 1` → emit `SignedEpochReceipt` at `e` ONLY after durable commit!). -/
@[expose] def execReserveBeforeSignAtomic (st : PosixFsState) (pid : Pid) (basePath : DirName)
    (keyKind : StatefulKeyKind) (vaultKeyId : List UInt8) (maxEpochCap : Nat)
    (msg : List UInt8) (macFn : KeyedMacFn) (macKey : List UInt8)
    (faults : IoFaultSchedule := {}) :
    PosixFsState × Option SignedEpochReceipt :=
  match openExisting st pid basePath vaultKeyId macFn macKey with
  | (stErr, .error _) => (stErr, none)
  | (stOpened, .ok (h, rec)) =>
    if !(decide (rec.body.epoch < maxEpochCap)) || !(decide (rec.body.epoch + 1 < 2 ^ 64)) then
      let stCl := (closeVaultHandle stOpened h).toOption.getD stOpened
      (stCl, none)
    else
      let reservedEpoch := rec.body.epoch
      let nextPayload := encodeCustodyWalPayload keyKind maxEpochCap msg
      let (stReplaced, hAfter, repRes) :=
        replaceAtomic stOpened h (reservedEpoch + 1) nextPayload macFn macKey faults
      let stClosed := (closeVaultHandle stReplaced hAfter).toOption.getD stReplaced
      match repRes with
      | .error _ => (stClosed, none) -- Sticky poisoned & aborted BEFORE emitting signature!
      | .ok _ =>
        let receipt : SignedEpochReceipt :=
          { keyKind := keyKind
            vaultKeyId := vaultKeyId
            epoch := reservedEpoch
            msg := msg }
        (stClosed, some receipt)

/-- Execute one open-world `MultiCrashWalEvent` transition on `MultiCrashCustodyState`. -/
def stepMultiCrashCustody (macFn : KeyedMacFn) (macKey : List UInt8)
    (s : MultiCrashCustodyState) (ev : MultiCrashWalEvent) :
    MultiCrashCustodyState × Option SignedEpochReceipt :=
  match ev with
  | .signAtomic pid msg faults =>
    match openExisting s.fs pid s.basePath s.vaultKeyId macFn macKey with
    | (fsErr, .error _) => ({ s with fs := fsErr }, none)
    | (fsOpened, .ok (h, rec)) =>
      if !(decide (rec.body.epoch < s.maxEpochCap)) || !(decide (rec.body.epoch + 1 < 2 ^ 64)) then
        let fsCl := (closeVaultHandle fsOpened h).toOption.getD fsOpened
        ({ s with fs := fsCl }, none)
      else
        let reservedEp := rec.body.epoch
        let nextPayload := encodeCustodyWalPayload s.keyKind s.maxEpochCap msg
        let (fsRep, hAfter, repRes) :=
          replaceAtomic fsOpened h (reservedEp + 1) nextPayload macFn macKey faults
        let fsClosed := (closeVaultHandle fsRep hAfter).toOption.getD fsRep
        match repRes with
        | .error _ => ({ s with fs := fsClosed }, none)
        | .ok _ =>
          let rcpt : SignedEpochReceipt :=
            { keyKind := s.keyKind, vaultKeyId := s.vaultKeyId, epoch := reservedEp, msg := msg }
          ({ s with
              fs := fsClosed
              emittedReceipts := s.emittedReceipts ++ [rcpt]
              ghostWatermark := reservedEp + 1 },
           some rcpt)
  | .beginReserveHoldLock pid msg faults =>
    match s.activeHold with
    | some _ => (s, none)
    | none =>
      match openExisting s.fs pid s.basePath s.vaultKeyId macFn macKey with
      | (fsErr, .error _) => ({ s with fs := fsErr }, none)
      | (fsOpened, .ok (h, rec)) =>
        if !(decide (rec.body.epoch < s.maxEpochCap)) || !(decide (rec.body.epoch + 1 < 2 ^ 64)) then
          let fsCl := (closeVaultHandle fsOpened h).toOption.getD fsOpened
          ({ s with fs := fsCl }, none)
        else
          let reservedEp := rec.body.epoch
          let nextPayload := encodeCustodyWalPayload s.keyKind s.maxEpochCap msg
          let (fsRep, hAfter, repRes) :=
            replaceAtomic fsOpened h (reservedEp + 1) nextPayload macFn macKey faults
          match repRes with
          | .error _ =>
            let fsCl := (closeVaultHandle fsRep hAfter).toOption.getD fsRep
            ({ s with fs := fsCl }, none)
          | .ok _ =>
            ({ s with
                fs := fsRep
                activeHold := some (hAfter, reservedEp, msg)
                ghostWatermark := reservedEp + 1 },
             none)
  | .finishSignFromHold =>
    match s.activeHold with
    | none => (s, none)
    | some (h, reservedEp, msg) =>
      let fsClosed := (closeVaultHandle s.fs h).toOption.getD s.fs
      let rcpt : SignedEpochReceipt :=
        { keyKind := s.keyKind, vaultKeyId := s.vaultKeyId, epoch := reservedEp, msg := msg }
      ({ s with
          fs := fsClosed
          activeHold := none
          emittedReceipts := s.emittedReceipts ++ [rcpt] },
       some rcpt)
  | .contenderSignAttempt contenderPid msg =>
    match openExisting s.fs contenderPid s.basePath s.vaultKeyId macFn macKey with
    | (fsErr, .error _) => ({ s with fs := fsErr }, none)
    | (fsOpened, .ok (h, rec)) =>
      if !(decide (rec.body.epoch < s.maxEpochCap)) || !(decide (rec.body.epoch + 1 < 2 ^ 64)) then
        let fsCl := (closeVaultHandle fsOpened h).toOption.getD fsOpened
        ({ s with fs := fsCl }, none)
      else
        let reservedEp := rec.body.epoch
        let nextPayload := encodeCustodyWalPayload s.keyKind s.maxEpochCap msg
        let (fsRep, hAfter, repRes) :=
          replaceAtomic fsOpened h (reservedEp + 1) nextPayload macFn macKey {}
        let fsClosed := (closeVaultHandle fsRep hAfter).toOption.getD fsRep
        match repRes with
        | .error _ => ({ s with fs := fsClosed }, none)
        | .ok _ =>
          let rcpt : SignedEpochReceipt :=
            { keyKind := s.keyKind, vaultKeyId := s.vaultKeyId, epoch := reservedEp, msg := msg }
          ({ s with
              fs := fsClosed
              emittedReceipts := s.emittedReceipts ++ [rcpt]
              ghostWatermark := reservedEp + 1 },
           some rcpt)
  | .midReserveCrash pid msg faults stepIdx crash =>
    -- The system dies at syscall boundary `stepIdx` of a reservation (after `openExisting`,
    -- anywhere inside `replaceAtomic`: unlink, create, write, temp sync, close, rename,
    -- directory sync). Nothing is emitted; every handle, lock and hold is gone.
    match openExisting s.fs pid s.basePath s.vaultKeyId macFn macKey with
    | (fsErr, .error _) => ({ s with fs := crash.apply fsErr, activeHold := none }, none)
    | (fsOpened, .ok (h, rec)) =>
      if !(decide (rec.body.epoch < s.maxEpochCap)) || !(decide (rec.body.epoch + 1 < 2 ^ 64)) then
        ({ s with fs := crash.apply fsOpened, activeHold := none }, none)
      else
        ({ s with
            fs := crash.apply
              (pickStepState fsOpened
                (replaceAtomicSteps fsOpened h (rec.body.epoch + 1)
                  (encodeCustodyWalPayload s.keyKind s.maxEpochCap msg) macFn macKey faults)
                stepIdx)
            activeHold := none },
         none)
  | .kernelPanic =>
    ({ s with fs := KernelPanicCrash s.fs, activeHold := none }, none)
  | .powerLoss dirPick defaultTear overrides =>
    ({ s with
        fs := PowerLossCrash dirPick (evalFiniteTearSchedule defaultTear overrides) s.fs
        activeHold := none },
     none)
  | .unlinkLockSidecar =>
    let fs' := (posixUnlink s.fs (walLockPath s.basePath)).toOption.getD s.fs
    ({ s with fs := fs' }, none)
  | .recreateSpoofLock actorPid spoofBytes =>
    let fs' := externalUnlinkAndRecreateLock s.fs actorPid s.basePath spoofBytes
    ({ s with fs := fs' }, none)
  | .attemptReprovisionGenesis actorPid newNonce =>
    -- Rogue external caller lacks the enrolled secret `macKey` (uses empty/untrusted key `[]`)!
    let (fs', _) :=
      provisionGenesis s.fs actorPid s.basePath s.vaultKeyId newNonce [] macFn [] {}
    ({ s with fs := fs' }, none)
  | .deleteWalRecord =>
    let fs' := (posixUnlink s.fs s.basePath).toOption.getD s.fs
    ({ s with fs := fs' }, none)
  | .plantSymlink entryName targetName =>
    let fs' := (posixCreateSymlink s.fs entryName targetName).toOption.getD s.fs
    ({ s with fs := fs' }, none)

/-- A reservation interrupted by a crash releases nothing and leaves no hold. -/
theorem midReserveCrash_emits_nothing (macFn : KeyedMacFn) (macKey : List UInt8)
    (s : MultiCrashCustodyState) (pid : Pid) (msg : List UInt8) (faults : IoFaultSchedule)
    (stepIdx : Nat) (crash : MidOpCrash) :
    (stepMultiCrashCustody macFn macKey s (.midReserveCrash pid msg faults stepIdx crash)).2 = none ∧
    (stepMultiCrashCustody macFn macKey s
      (.midReserveCrash pid msg faults stepIdx crash)).1.emittedReceipts = s.emittedReceipts ∧
    (stepMultiCrashCustody macFn macKey s
      (.midReserveCrash pid msg faults stepIdx crash)).1.activeHold = none := by
  unfold stepMultiCrashCustody
  dsimp only
  cases openExisting s.fs pid s.basePath s.vaultKeyId macFn macKey with
  | mk fs1 r =>
    cases r with
    | error _ => exact ⟨rfl, rfl, rfl⟩
    | ok p =>
      obtain ⟨h, rec⟩ := p
      dsimp only
      split <;> exact ⟨rfl, rfl, rfl⟩

/-- Fold an arbitrary multi-turn `List MultiCrashWalEvent` trace from initial state `s₀`. -/
def runMultiCrashCustodyTrace (macFn : KeyedMacFn) (macKey : List UInt8) :
    MultiCrashCustodyState → List MultiCrashWalEvent → MultiCrashCustodyState
  | s, [] => s
  | s, ev :: rest =>
    let (s', _) := stepMultiCrashCustody macFn macKey s ev
    runMultiCrashCustodyTrace macFn macKey s' rest

/-- Lift `stepMultiCrashCustody` into a compositional `SimulationSpine.PartyMachine`! -/
def posixCustodyPartyMachine (macFn : KeyedMacFn) (macKey : List UInt8) :
    PartyMachine MultiCrashCustodyState MultiCrashWalEvent SignedEpochReceipt where
  step s ev :=
    match stepMultiCrashCustody macFn macKey s ev with
    | (s', some rcpt) => some (s', rcpt)
    | (_, none) => none
  errStep s ev := (stepMultiCrashCustody macFn macKey s ev).1

/-- Provision a fresh `MultiCrashCustodyState` from an empty `PosixFsState` via `provisionGenesis`. -/
@[expose] def initProvisionedCustodyState (pid : Pid) (basePath : DirName)
    (keyKind : StatefulKeyKind) (vaultKeyId genesisNonce : List UInt8)
    (maxEpochCap : Nat) (macFn : KeyedMacFn) (macKey : List UInt8) :
    Option MultiCrashCustodyState :=
  let initPay := encodeCustodyWalPayload keyKind maxEpochCap []
  match provisionGenesis PosixFsState.empty pid basePath vaultKeyId genesisNonce initPay macFn macKey {} with
  | (_, .error _) => none
  | (fs0, .ok (lockIno, _)) =>
    some { fs := fs0
           basePath := basePath
           keyKind := keyKind
           vaultKeyId := vaultKeyId
           enrolledGenesisId := computeLockGenesisId lockIno genesisNonce
           maxEpochCap := maxEpochCap
           activeHold := none
           emittedReceipts := []
           ghostWatermark := 0 }

/-- Per-dentry watermark safety predicate:
    - If `basePath` is `none` (deleted WAL) or `.symlink _` (symlink attack), `openExisting`
      (`O_NOFOLLOW`, no `O_CREAT`) deterministically refuses!
    - If `basePath` is `.regular ino`, either `ino` holds a synced authentic `WalRecord` with
      `watermark ≤ rec.body.epoch`, OR `ino` holds unauthenticated rogue bytes (which `openExisting`
      rejects unless `MacForgery` against `honestBodies` occurs!). -/
def EntryWatermarkSafe (st : PosixFsState) (vkId : List UInt8)
    (macFn : KeyedMacFn) (macKey : List UInt8) (watermark : Nat)
    (entryOpt : Option EntryTarget) : Prop :=
  match entryOpt with
  | none => True
  | some (.symlink _) => True
  | some (.regular ino) =>
    ino < st.nand.nextInode ∧
    assocLookup st.kernel.pageCache.dirtyFiles ino = none ∧
    assocLookup st.driveCache.cachedFiles ino = none ∧
    ∃ bs : List UInt8,
      assocLookup st.nand.fileBlocks ino = some bs ∧
      ∀ rec : WalRecord,
        decodeWalRecord bs = some rec →
        rec.body.vaultKeyId = vkId →
        verifyWalMac macFn macKey rec = true →
        watermark ≤ rec.body.epoch

/-- Inductive multi-crash custody invariant over `MultiCrashCustodyState`. -/
def CustodyMultiCrashInv (macFn : KeyedMacFn) (macKey : List UInt8)
    (s : MultiCrashCustodyState) : Prop :=
  s.vaultKeyId.length = 32 ∧
  (s.emittedReceipts.map (·.epoch)).Nodup ∧
  (∀ r ∈ s.emittedReceipts,
    r.epoch < s.ghostWatermark ∧ r.keyKind = s.keyKind ∧ r.vaultKeyId = s.vaultKeyId) ∧
  (match s.activeHold with
   | none => True
   | some (_, resEp, _) =>
     resEp < s.ghostWatermark ∧ ∀ r ∈ s.emittedReceipts, r.epoch ≠ resEp) ∧
  s.fs.driveCache.cachedDirEntries = none ∧
  EntryWatermarkSafe s.fs s.vaultKeyId macFn macKey s.ghostWatermark
    (assocLookup s.fs.kernel.dirInode.unsyncedEntries s.basePath) ∧
  EntryWatermarkSafe s.fs s.vaultKeyId macFn macKey s.ghostWatermark
    (assocLookup s.fs.nand.dirNandEntries s.basePath)

private theorem entryWatermarkSafe_mono {st : PosixFsState} {vkId : List UInt8}
    {macFn : KeyedMacFn} {macKey : List UInt8} {w₁ w₂ : Nat} {e : Option EntryTarget}
    (hle : w₁ ≤ w₂) (hSafe : EntryWatermarkSafe st vkId macFn macKey w₂ e) :
    EntryWatermarkSafe st vkId macFn macKey w₁ e := by
  cases e with
  | none => trivial
  | some tgt =>
    cases tgt with
    | symlink _ => trivial
    | regular ino =>
      rcases hSafe with ⟨hLt, hPg, hDr, bs, hBs, hImp⟩
      exact ⟨hLt, hPg, hDr, bs, hBs, fun rec hD hVk hVer => Nat.le_trans hle (hImp rec hD hVk hVer)⟩

theorem openExisting_preserves_storage_and_bounds_epoch
    {st st' : PosixFsState} {pid : Pid} {basePath : DirName}
    {vkId : List UInt8} {macFn : KeyedMacFn} {macKey : List UInt8}
    {watermark : Nat} {h : LockedVaultHandle} {rec : WalRecord}
    (hEntry : EntryWatermarkSafe st vkId macFn macKey watermark
      (assocLookup st.kernel.dirInode.unsyncedEntries basePath))
    (hOpen : openExisting st pid basePath vkId macFn macKey = (st', .ok (h, rec))) :
    st'.kernel.dirInode = st.kernel.dirInode ∧
    st'.kernel.pageCache = st.kernel.pageCache ∧
    st'.driveCache = st.driveCache ∧
    st'.nand = st.nand ∧
    h.basePath = basePath ∧
    h.vaultKeyId = vkId ∧
    h.lockGenesisId.length = 40 ∧
    watermark ≤ rec.body.epoch := by
  rw [openExisting.public_eq_1] at hOpen
  cases hOp1 : posixOpenExistingNoFollow st pid (walLockPath basePath) true with
  | error e => rw [hOp1] at hOpen; cases (Prod.mk.inj hOpen).2
  | ok p1 =>
    rcases p1 with ⟨st1, lockFd⟩
    rw [hOp1] at hOpen
    dsimp only at hOpen
    have hSt1 : st1.kernel.dirInode = st.kernel.dirInode ∧
                st1.kernel.pageCache = st.kernel.pageCache ∧
                st1.driveCache = st.driveCache ∧ st1.nand = st.nand := by
      rw [posixOpenExistingNoFollow.public_eq_1] at hOp1
      cases hR : resolveDentryNoFollow st.kernel.dirInode.unsyncedEntries (walLockPath basePath) with
      | error e => rw [hR] at hOp1; cases hOp1
      | ok ino =>
        rw [hR] at hOp1; injection hOp1 with hP
        rw [← (Prod.mk.inj hP).1]; exact ⟨rfl, rfl, rfl, rfl⟩
    cases hFlk : posixFlockExNb st1 pid lockFd with
    | error e => rw [hFlk] at hOpen; cases (Prod.mk.inj hOpen).2
    | ok st2 =>
      rw [hFlk] at hOpen
      dsimp only at hOpen
      have hFlkS := posixFlockExNb_preserves_storage hFlk
      have hSt2 : st2.kernel.dirInode = st.kernel.dirInode ∧
                  st2.kernel.pageCache = st.kernel.pageCache ∧
                  st2.driveCache = st.driveCache ∧ st2.nand = st.nand :=
        ⟨hFlkS.1.trans hSt1.1, hFlkS.2.1.trans hSt1.2.1,
         hFlkS.2.2.1.trans hSt1.2.2.1, hFlkS.2.2.2.trans hSt1.2.2.2⟩
      cases hFst : posixFstatDescAndInode st2 pid lockFd with
      | error e => rw [hFst] at hOpen; cases (Prod.mk.inj hOpen).2
      | ok dInoPair =>
        rcases dInoPair with ⟨lockDescId, actualLockIno⟩
        cases hPr1 : posixPreadAll st2 pid lockFd with
        | error e => rw [hFst, hPr1] at hOpen; cases (Prod.mk.inj hOpen).2
        | ok rawLockBytes =>
          rw [hFst, hPr1] at hOpen; dsimp only at hOpen
          cases hDecL : decodeLockSidecar rawLockBytes with
          | none => rw [hDecL] at hOpen; cases (Prod.mk.inj hOpen).2
          | some lockSeal =>
            rw [hDecL] at hOpen; dsimp only at hOpen
            by_cases hMisI : (actualLockIno != lockSeal.sealedLockInode) = true
            · simp [hMisI] at hOpen
            · simp only [hMisI, Bool.false_eq_true, ↓reduceIte] at hOpen
              cases hOp2 : posixOpenExistingNoFollow st2 pid basePath false with
              | error e => rw [hOp2] at hOpen; cases (Prod.mk.inj hOpen).2
              | ok p2 =>
                rcases p2 with ⟨st3, recFd⟩
                rw [hOp2] at hOpen; dsimp only at hOpen
                rw [posixOpenExistingNoFollow.public_eq_1] at hOp2
                rw [resolveDentryNoFollow.public_eq_1] at hOp2
                rw [hSt2.1] at hOp2
                cases hBaseLook : assocLookup st.kernel.dirInode.unsyncedEntries basePath with
                | none => rw [hBaseLook] at hOp2; cases hOp2
                | some baseTgt =>
                  rw [hBaseLook] at hOp2
                  cases baseTgt with
                  | symlink _ => cases hOp2
                  | regular recIno =>
                    dsimp only at hOp2
                    injection hOp2 with hP2
                    rcases Prod.mk.inj hP2 with ⟨hSt3Eq, hRecFdEq⟩
                    rw [hBaseLook] at hEntry
                    rcases hEntry with ⟨_, hPgNone, hDrNone, bsDisk, hNandBs, hDiskImp⟩
                    have hPr2Val : posixPreadAll st3 pid recFd = .ok bsDisk := by
                      rw [← hSt3Eq, ← hRecFdEq]
                      rw [posixPreadAll.public_eq_1]
                      unfold readInodeHierarchy
                      unfold pendingVolatileWrite
                      simp only [resolveOpenFd_insert_self, Bool.false_eq_true, ↓reduceIte,
                        hSt2.2.1, hSt2.2.2.1, hSt2.2.2.2, hPgNone, hDrNone, hNandBs]
                    rw [hPr2Val] at hOpen
                    dsimp only at hOpen
                    cases hDecR : decodeWalRecord bsDisk with
                    | none => rw [hDecR] at hOpen; cases (Prod.mk.inj hOpen).2
                    | some recVal =>
                      rw [hDecR] at hOpen; dsimp only at hOpen
                      by_cases hGidM :
                          (recVal.body.lockGenesisId !=
                            computeLockGenesisId actualLockIno lockSeal.genesisNonce) = true
                      · simp [hGidM] at hOpen
                      · simp only [hGidM, Bool.false_eq_true, ↓reduceIte] at hOpen
                        by_cases hMacM :
                            (recVal.body.vaultKeyId != vkId ||
                             !(verifyWalMac macFn macKey recVal)) = true
                        · simp [hMacM] at hOpen
                        · simp only [hMacM, Bool.false_eq_true, ↓reduceIte] at hOpen
                          rcases Prod.mk.inj hOpen with ⟨hSt4Eq, hOkR⟩
                          injection hOkR with hPairR
                          rcases Prod.mk.inj hPairR with ⟨hHEq, hRecEq⟩
                          subst hHEq hRecEq
                          have hGidEq : recVal.body.lockGenesisId =
                              computeLockGenesisId actualLockIno lockSeal.genesisNonce :=
                            eq_of_not_bne_true hGidM
                          have hGidLen40 :
                              (computeLockGenesisId actualLockIno lockSeal.genesisNonce).length = 40 := by
                            rw [← hGidEq]
                            exact (decodeWalRecord_canonical hDecR).1.1.2.1
                          have hVkEq : recVal.body.vaultKeyId = vkId :=
                            eq_of_not_bne_true (fun hc => hMacM (by simp [hc]))
                          have hVerOk : verifyWalMac macFn macKey recVal = true := by
                            cases hv : verifyWalMac macFn macKey recVal
                            · exfalso; apply hMacM; simp [hv]
                            · rfl
                          have hCk := posixCloseFd_preserves_storage st3 pid recFd
                          have hSt3Storage :
                              st3.kernel.dirInode = st.kernel.dirInode ∧
                              st3.kernel.pageCache = st.kernel.pageCache ∧
                              st3.driveCache = st.driveCache ∧ st3.nand = st.nand := by
                            rw [← hSt3Eq]; exact hSt2
                          rw [← hSt4Eq]
                          exact ⟨hCk.1.trans hSt3Storage.1,
                                 hCk.2.1.trans hSt3Storage.2.1,
                                 hCk.2.2.1.trans hSt3Storage.2.2.1,
                                 hCk.2.2.2.trans hSt3Storage.2.2.2,
                                 rfl, rfl, hGidLen40, hDiskImp recVal hDecR hVkEq hVerOk⟩

private theorem replaceAtomic_preserves_entryWatermarkSafe
    {st st' : PosixFsState} {h h' : LockedVaultHandle}
    {newEp : Nat} {newPay : List UInt8}
    {macFn : KeyedMacFn} (hMacWf : WellFormedMacFn macFn) {macKey : List UInt8}
    {faults : IoFaultSchedule} {watermark : Nat}
    {res : Except PosixErr WalRecord}
    (hVkLen : h.vaultKeyId.length = 32)
    (hGidLen : h.lockGenesisId.length = 40)
    (hDrvDir : st.driveCache.cachedDirEntries = none)
    (hMemSafe : EntryWatermarkSafe st h.vaultKeyId macFn macKey watermark
      (assocLookup st.kernel.dirInode.unsyncedEntries h.basePath))
    (hNandSafe : EntryWatermarkSafe st h.vaultKeyId macFn macKey watermark
      (assocLookup st.nand.dirNandEntries h.basePath))
    (hLeNew : watermark ≤ newEp)
    (hRun : replaceAtomic st h newEp newPay macFn macKey faults = (st', h', res)) :
    st'.driveCache.cachedDirEntries = none ∧
    match res with
    | .error _ =>
      EntryWatermarkSafe st' h.vaultKeyId macFn macKey watermark
        (assocLookup st'.kernel.dirInode.unsyncedEntries h.basePath) ∧
      EntryWatermarkSafe st' h.vaultKeyId macFn macKey watermark
        (assocLookup st'.nand.dirNandEntries h.basePath)
    | .ok _ =>
      EntryWatermarkSafe st' h.vaultKeyId macFn macKey newEp
        (assocLookup st'.kernel.dirInode.unsyncedEntries h.basePath) ∧
      EntryWatermarkSafe st' h.vaultKeyId macFn macKey newEp
        (assocLookup st'.nand.dirNandEntries h.basePath) := by
  have hUnchangedEntry : ∀ {s0 s1 : PosixFsState} {e : Option EntryTarget},
      s0.nand.nextInode ≤ s1.nand.nextInode →
      (∀ ino < s0.nand.nextInode,
        assocLookup s1.kernel.pageCache.dirtyFiles ino = assocLookup s0.kernel.pageCache.dirtyFiles ino ∧
        assocLookup s1.driveCache.cachedFiles ino = assocLookup s0.driveCache.cachedFiles ino ∧
        assocLookup s1.nand.fileBlocks ino = assocLookup s0.nand.fileBlocks ino) →
      EntryWatermarkSafe s0 h.vaultKeyId macFn macKey watermark e →
      EntryWatermarkSafe s1 h.vaultKeyId macFn macKey watermark e := by
    intro s0 s1 e hNextLe hFrame hS0
    cases e with
    | none => trivial
    | some tgt =>
      cases tgt with
      | symlink _ => trivial
      | regular ino =>
        rcases hS0 with ⟨hLt, hPg, hDr, bs, hBs, hImp⟩
        obtain ⟨f1, f2, f3⟩ := hFrame ino hLt
        exact ⟨Nat.lt_of_lt_of_le hLt hNextLe, f1.trans hPg, f2.trans hDr, bs, f3.trans hBs, hImp⟩
  rw [replaceAtomic.public_eq_1] at hRun
  by_cases hP : h.ioPoisoned = true
  · simp only [hP, ↓reduceIte] at hRun
    rcases Prod.mk.inj hRun with ⟨rfl, h2⟩
    rcases Prod.mk.inj h2 with ⟨_, rfl⟩
    exact ⟨hDrvDir, hMemSafe, hNandSafe⟩
  · simp only [hP, Bool.false_eq_true, ↓reduceIte] at hRun
    by_cases hBnd : (!(decide (newEp < 2 ^ 64)) || !(decide (newPay.length < 2 ^ 32))) = true
    · simp only [hBnd, ↓reduceIte] at hRun
      rcases Prod.mk.inj hRun with ⟨rfl, h2⟩
      rcases Prod.mk.inj h2 with ⟨_, rfl⟩
      exact ⟨hDrvDir, hMemSafe, hNandSafe⟩
    · simp only [hBnd, Bool.false_eq_true, ↓reduceIte] at hRun
      have hEp64 : newEp < 2 ^ 64 := by
        cases hd : decide (newEp < 2 ^ 64)
        · exfalso; apply hBnd; simp [hd]
        · exact of_decide_eq_true hd
      have hPay32 : newPay.length < 2 ^ 32 := by
        cases hd : decide (newPay.length < 2 ^ 32)
        · exfalso; apply hBnd; simp [hd]
        · exact of_decide_eq_true hd
      cases hLk : resolveOpenFd st.kernel.openFds h.pid h.lockFd with
      | none =>
        rw [hLk] at hRun
        rcases Prod.mk.inj hRun with ⟨rfl, h2⟩
        rcases Prod.mk.inj h2 with ⟨_, rfl⟩
        exact ⟨hDrvDir, hMemSafe, hNandSafe⟩
      | some dPair =>
        rcases dPair with ⟨descId, lockDesc⟩
        rw [hLk] at hRun; dsimp only at hRun
        by_cases hInv :
            (descId != h.lockDescId || lockDesc.inode != h.lockInode || lockDesc.stickyFsyncErr ||
             st.kernel.flockTable.owner h.lockInode != some h.lockDescId) = true
        · simp only [hInv, ↓reduceIte] at hRun
          rcases Prod.mk.inj hRun with ⟨rfl, h2⟩
          rcases Prod.mk.inj h2 with ⟨_, rfl⟩
          exact ⟨hDrvDir, hMemSafe, hNandSafe⟩
        · simp only [hInv, Bool.false_eq_true, ↓reduceIte] at hRun
          let tmpPath := walTmpPath h.basePath
          have hTmpNeBase : h.basePath ≠ tmpPath := fun he => walTmpPath_ne_base h.basePath he.symm
          let stClean := posixUnlinkIfPresent st tmpPath
          let tmpIno := st.nand.nextInode
          let tmpFd := st.nextFd
          let tmpDescId := st.kernel.openFds.nextDescId
          let newRec := signWalRecord macFn macKey
            { vaultKeyId := h.vaultKeyId, lockGenesisId := h.lockGenesisId,
              epoch := newEp, payload := newPay }
          let stCreated : PosixFsState :=
            { kernel := { stClean.kernel with
                           openFds := { fdRefs := assocInsert (h.pid, tmpFd) tmpDescId st.kernel.openFds.fdRefs
                                        descriptions := assocInsert tmpDescId
                                                          { inode := tmpIno, writable := true, stickyFsyncErr := false }
                                                          st.kernel.openFds.descriptions
                                        nextDescId := tmpDescId + 1 }
                           dirInode := { unsyncedEntries :=
                                           assocInsert tmpPath (.regular tmpIno)
                                             stClean.kernel.dirInode.unsyncedEntries } }
              driveCache := st.driveCache
              nand := { st.nand with
                         fileBlocks := assocInsert tmpIno [] st.nand.fileBlocks
                         nextInode := tmpIno + 1 }
              nextFd := tmpFd + 1 }
          have hCrEq : posixCreateExclNoFollow stClean h.pid tmpPath = .ok (stCreated, tmpFd, tmpIno) := by
            rw [posixCreateExclNoFollow.public_eq_1]
            have hAbs : assocLookup stClean.kernel.dirInode.unsyncedEntries tmpPath = none := by
              simp [stClean, posixUnlinkIfPresent]
            rw [hAbs]; rfl
          rw [hCrEq] at hRun; dsimp only at hRun
          let stWritten : PosixFsState :=
            { stCreated with
               kernel := { stCreated.kernel with
                            pageCache := { dirtyFiles :=
                                             assocInsert tmpIno (encodeWalRecord newRec)
                                               st.kernel.pageCache.dirtyFiles } } }
          have hWrEq : posixPwriteAll stCreated h.pid tmpFd (encodeWalRecord newRec) = .ok stWritten := by
            rw [posixPwriteAll.public_eq_1]
            simp [stWritten, stCreated, stClean, posixUnlinkIfPresent, resolveOpenFd_insert_self]
          rw [hWrEq] at hRun; dsimp only at hRun
          cases hFR : faults.failRecordSync with
          | true =>
            rw [hFR] at hRun
            let sSy : PosixFsState :=
              { stWritten with
                  kernel := { stWritten.kernel with
                                openFds := { stWritten.kernel.openFds with
                                               descriptions := assocInsert tmpDescId
                                                 { inode := tmpIno, writable := true, stickyFsyncErr := true }
                                                 stWritten.kernel.openFds.descriptions }
                                pageCache := { dirtyFiles := assocErase tmpIno stWritten.kernel.pageCache.dirtyFiles } }
                  driveCache := { stWritten.driveCache with
                                   cachedFiles := assocErase tmpIno st.driveCache.cachedFiles } }
            have hSyErr : posixSyncAllMedia stWritten h.pid tmpFd true = (sSy, .error .eio) := by
              rw [posixSyncAllMedia.public_eq_1]; simp [sSy, stWritten, stCreated, resolveOpenFd_insert_self]
            rw [hSyErr] at hRun; dsimp only at hRun
            rcases Prod.mk.inj hRun with ⟨rfl, h2⟩
            rcases Prod.mk.inj h2 with ⟨_, rfl⟩
            have hc := posixCloseFd_preserves_storage sSy h.pid tmpFd
            dsimp only
            refine ⟨by rw [hc.2.2.1]; exact hDrvDir, ?_, ?_⟩
            · rw [hc.1]
              have hBaseSame :
                  assocLookup (assocInsert tmpPath (.regular tmpIno)
                    stClean.kernel.dirInode.unsyncedEntries) h.basePath =
                    assocLookup st.kernel.dirInode.unsyncedEntries h.basePath := by
                simp [stClean, posixUnlinkIfPresent, hTmpNeBase]
              dsimp only [sSy, stWritten, stCreated]
              rw [hBaseSame]
              apply hUnchangedEntry (s0 := st) (by rw [hc.2.2.2]; exact Nat.le_succ _)
              · intro ino hLt
                have hNe : ino ≠ tmpIno := Nat.ne_of_lt hLt
                rw [hc.2.1, hc.2.2.1, hc.2.2.2]
                simp [sSy, stWritten, stCreated, hNe]
              · exact hMemSafe
            · rw [hc.2.2.2]
              dsimp only [sSy, stWritten, stCreated]
              apply hUnchangedEntry (s0 := st) (by rw [hc.2.2.2]; exact Nat.le_succ _)
              · intro ino hLt
                have hNe : ino ≠ tmpIno := Nat.ne_of_lt hLt
                rw [hc.2.1, hc.2.2.1, hc.2.2.2]
                simp [sSy, stWritten, stCreated, hNe]
              · exact hNandSafe
          | false =>
            rw [hFR] at hRun
            let sSy : PosixFsState :=
              { stWritten with
                  kernel := { stWritten.kernel with
                                pageCache := { dirtyFiles := assocErase tmpIno stWritten.kernel.pageCache.dirtyFiles } }
                  driveCache := { stWritten.driveCache with
                                   cachedFiles := assocErase tmpIno st.driveCache.cachedFiles }
                  nand := { stWritten.nand with
                             fileBlocks := assocInsert tmpIno (encodeWalRecord newRec)
                                             stWritten.nand.fileBlocks } }
            have hSyOk : posixSyncAllMedia stWritten h.pid tmpFd false = (sSy, .ok ()) := by
              rw [posixSyncAllMedia.public_eq_1]
              unfold readInodeHierarchy
              unfold pendingVolatileWrite
              simp [sSy, stWritten, stCreated, resolveOpenFd_insert_self]
            rw [hSyOk] at hRun; dsimp only at hRun
            let sCl := (posixCloseFd sSy h.pid tmpFd).toOption.getD sSy
            have hc := posixCloseFd_preserves_storage sSy h.pid tmpFd
            have hTmpPres : assocLookup sCl.kernel.dirInode.unsyncedEntries tmpPath =
                some (.regular tmpIno) := by
              dsimp only [sCl]; rw [hc.1]; simp [sSy, stWritten, stCreated]
            have hRnEq :
                posixRename sCl (walTmpPath h.basePath) h.basePath =
                  .ok { sCl with
                         kernel := { sCl.kernel with
                                      dirInode := { unsyncedEntries :=
                                                      (if tmpPath == h.basePath then
                                                         assocInsert h.basePath (.regular tmpIno)
                                                           sCl.kernel.dirInode.unsyncedEntries
                                                       else
                                                         assocErase tmpPath
                                                           (assocInsert h.basePath (.regular tmpIno)
                                                             sCl.kernel.dirInode.unsyncedEntries)) } } } := by
              change posixRename sCl tmpPath h.basePath = _
              rw [posixRename.public_eq_1]; rw [hTmpPres]
            rw [hRnEq] at hRun; dsimp only at hRun
            have hTmpBeqBase : (tmpPath == h.basePath) = false := by
              cases hb : (tmpPath == h.basePath)
              · rfl
              · exfalso; exact walTmpPath_ne_base h.basePath (eq_of_beq hb)
            have hDecNew : ∀ r : WalRecord,
                decodeWalRecord (encodeWalRecord newRec) = some r → r.body.epoch = newEp := by
              intro r hDec
              have hNewWf : newRec.WellFormed :=
                signWalRecord_wellFormed hMacWf macKey ⟨hVkLen, hGidLen, hEp64, hPay32⟩
              rw [decodeWalRecord_encodeWalRecord hNewWf] at hDec
              injection hDec with hEqR
              rw [← hEqR]; rfl
            cases hFP : faults.failParentSync with
            | true =>
              rw [hFP] at hRun
              rw [posixSyncParentDir.public_eq_1] at hRun
              simp only [↓reduceIte] at hRun
              rcases Prod.mk.inj hRun with ⟨rfl, h2⟩
              rcases Prod.mk.inj h2 with ⟨_, rfl⟩
              dsimp only
              refine ⟨by dsimp only [sCl]; rw [hc.2.2.1]; exact hDrvDir, ?_, ?_⟩
              · rw [hTmpBeqBase]
                simp only [Bool.false_eq_true, ↓reduceIte, assocLookup_erase, hTmpNeBase,
                  assocLookup_insert_self]
                refine ⟨?_, ?_, ?_, encodeWalRecord newRec, ?_, ?_⟩
                · dsimp only [sCl]; rw [hc.2.2.2]; simp [sSy, stWritten, stCreated]
                · dsimp only [sCl]; rw [hc.2.1]; simp [sSy]
                · dsimp only [sCl]; rw [hc.2.2.1]; simp [sSy]
                · dsimp only [sCl]; rw [hc.2.2.2]; simp [sSy]
                · intro r hD _ _
                  rw [hDecNew r hD]
                  exact hLeNew
              · have hNandDirEq : assocLookup sCl.nand.dirNandEntries h.basePath =
                    assocLookup st.nand.dirNandEntries h.basePath := by
                  dsimp only [sCl]; rw [hc.2.2.2]
                rw [hNandDirEq]
                apply hUnchangedEntry (s0 := st)
                  (by dsimp only [sCl]; rw [hc.2.2.2]; exact Nat.le_succ _)
                · intro ino hLt
                  have hNe : ino ≠ tmpIno := Nat.ne_of_lt hLt
                  dsimp only [sCl]; rw [hc.2.1, hc.2.2.1, hc.2.2.2]
                  simp [sSy, stWritten, stCreated, hNe]
                · exact hNandSafe
            | false =>
              rw [hFP] at hRun
              rw [posixSyncParentDir.public_eq_1] at hRun
              simp only [Bool.false_eq_true, ↓reduceIte] at hRun
              rcases Prod.mk.inj hRun with ⟨rfl, h2⟩
              rcases Prod.mk.inj h2 with ⟨_, rfl⟩
              dsimp only
              have hNewSafe :
                  EntryWatermarkSafe
                    { sCl with
                      kernel := { sCl.kernel with
                                    dirInode := { unsyncedEntries :=
                                                    (if tmpPath == h.basePath then
                                                       assocInsert h.basePath (.regular tmpIno) sCl.kernel.dirInode.unsyncedEntries
                                                     else
                                                       assocErase tmpPath (assocInsert h.basePath (.regular tmpIno) sCl.kernel.dirInode.unsyncedEntries)) } }
                      driveCache := { sCl.driveCache with cachedDirEntries := none }
                      nand := { sCl.nand with
                                  dirNandEntries :=
                                    if tmpPath == h.basePath then
                                      assocInsert h.basePath (.regular tmpIno) sCl.kernel.dirInode.unsyncedEntries
                                    else
                                      assocErase tmpPath (assocInsert h.basePath (.regular tmpIno) sCl.kernel.dirInode.unsyncedEntries) } }
                    h.vaultKeyId macFn macKey newEp (some (.regular tmpIno)) := by
                refine ⟨?_, ?_, ?_, encodeWalRecord newRec, ?_, ?_⟩
                · dsimp only [sCl]; rw [hc.2.2.2]; simp [sSy, stWritten, stCreated]
                · dsimp only [sCl]; rw [hc.2.1]; simp [sSy]
                · dsimp only [sCl]; rw [hc.2.2.1]; simp [sSy]
                · dsimp only [sCl]; rw [hc.2.2.2]; simp [sSy]
                · intro r hD _ _
                  rw [hDecNew r hD]
                  exact Nat.le_refl _
              refine ⟨rfl, ?_, ?_⟩
              · rw [hTmpBeqBase]
                simp only [Bool.false_eq_true, ↓reduceIte, assocLookup_erase, hTmpNeBase, assocLookup_insert_self]
                exact hNewSafe
              · rw [hTmpBeqBase]
                simp only [Bool.false_eq_true, ↓reduceIte, assocLookup_erase, hTmpNeBase, assocLookup_insert_self]
                exact hNewSafe


private theorem entryWatermarkSafe_frame {s0 s1 : PosixFsState} {vkId : List UInt8}
    {macFn : KeyedMacFn} {macKey : List UInt8} {w : Nat} {e : Option EntryTarget}
    (hNext : s0.nand.nextInode ≤ s1.nand.nextInode)
    (hFrame : ∀ ino < s0.nand.nextInode,
      assocLookup s1.kernel.pageCache.dirtyFiles ino = assocLookup s0.kernel.pageCache.dirtyFiles ino ∧
      assocLookup s1.driveCache.cachedFiles ino = assocLookup s0.driveCache.cachedFiles ino ∧
      assocLookup s1.nand.fileBlocks ino = assocLookup s0.nand.fileBlocks ino)
    (hSafe : EntryWatermarkSafe s0 vkId macFn macKey w e) :
    EntryWatermarkSafe s1 vkId macFn macKey w e := by
  cases e with
  | none => trivial
  | some tgt =>
    cases tgt with
    | symlink _ => trivial
    | regular ino =>
      rcases hSafe with ⟨hLt, hPg, hDr, bs, hBs, hImp⟩
      obtain ⟨f1, f2, f3⟩ := hFrame ino hLt
      exact ⟨Nat.lt_of_lt_of_le hLt hNext, f1.trans hPg, f2.trans hDr, bs, f3.trans hBs, hImp⟩

private theorem entryWatermarkSafe_after_crashStep {st crashed : PosixFsState}
    {vkId : List UInt8} {macFn : KeyedMacFn} {macKey : List UInt8} {w : Nat}
    {e : Option EntryTarget}
    (hCrash : CrashStep st crashed)
    (hSafe : EntryWatermarkSafe st vkId macFn macKey w e) :
    EntryWatermarkSafe crashed vkId macFn macKey w e := by
  cases e with
  | none => trivial
  | some tgt =>
    cases tgt with
    | symlink _ => trivial
    | regular ino =>
      rcases hSafe with ⟨hLt, hPg, hDr, bs, hBs, hImp⟩
      have hImm := (syncedInode_immune_to_crashStep hPg hDr hCrash).1
      cases hCrash with
      | kernelPanic _ =>
        refine ⟨hLt, rfl, rfl, bs, ?_, hImp⟩
        rw [hImm, hBs]
      | powerLoss dirPick tearFn _ =>
        refine ⟨hLt, rfl, rfl, bs, ?_, hImp⟩
        rw [hImm, hBs]

/-- The storage part of `CustodyMultiCrashInv`: no pending directory image in the drive cache,
    and both the in-memory and the on-media `basePath` dentries are watermark-safe. -/
private def BaseEntriesSafe (macFn : KeyedMacFn) (macKey vkId : List UInt8) (basePath : DirName)
    (w : Nat) (st : PosixFsState) : Prop :=
  st.driveCache.cachedDirEntries = none ∧
  EntryWatermarkSafe st vkId macFn macKey w
    (assocLookup st.kernel.dirInode.unsyncedEntries basePath) ∧
  EntryWatermarkSafe st vkId macFn macKey w
    (assocLookup st.nand.dirNandEntries basePath)

private theorem baseEntriesSafe_after_crashStep {macFn : KeyedMacFn} {macKey vkId : List UInt8}
    {basePath : DirName} {w : Nat} {st crashed : PosixFsState}
    (hSafe : BaseEntriesSafe macFn macKey vkId basePath w st) (hCrash : CrashStep st crashed) :
    BaseEntriesSafe macFn macKey vkId basePath w crashed := by
  rcases hSafe with ⟨hDrvDir, hMemSafe, hNandSafe⟩
  cases hCrash with
  | kernelPanic _ =>
    have hCr := entryWatermarkSafe_after_crashStep (CrashStep.kernelPanic st) hNandSafe
    refine ⟨rfl, ?_, ?_⟩
    · dsimp only [KernelPanicCrash]; rw [hDrvDir]; exact hCr
    · dsimp only [KernelPanicCrash]; rw [hDrvDir]; exact hCr
  | powerLoss dirPick tearFn _ =>
    cases dirPick with
    | revertToNand =>
      have hCr := entryWatermarkSafe_after_crashStep
        (CrashStep.powerLoss .revertToNand tearFn st) hNandSafe
      refine ⟨rfl, ?_, ?_⟩
      · dsimp only [PowerLossCrash]; exact hCr
      · dsimp only [PowerLossCrash]; exact hCr
    | flushPendingDir =>
      have hCr := entryWatermarkSafe_after_crashStep
        (CrashStep.powerLoss .flushPendingDir tearFn st) hMemSafe
      refine ⟨rfl, ?_, ?_⟩
      · dsimp only [PowerLossCrash]; rw [hDrvDir]; exact hCr
      · dsimp only [PowerLossCrash]; rw [hDrvDir]; exact hCr

/-- Every syscall boundary inside `replaceAtomic` (not only its final state) keeps both
    `basePath` dentries watermark-safe: until the rename they still name the old synced inode,
    and from the rename on the in-memory dentry names the already media-synced new record. -/
private theorem replaceAtomicSteps_all_baseEntriesSafe
    {st mid : PosixFsState} {h : LockedVaultHandle}
    {newEp : Nat} {newPay : List UInt8}
    {macFn : KeyedMacFn} (hMacWf : WellFormedMacFn macFn) {macKey : List UInt8}
    {faults : IoFaultSchedule} {watermark : Nat}
    (hVkLen : h.vaultKeyId.length = 32)
    (hGidLen : h.lockGenesisId.length = 40)
    (hSafe : BaseEntriesSafe macFn macKey h.vaultKeyId h.basePath watermark st)
    (hLeNew : watermark ≤ newEp)
    (hMid : mid ∈ replaceAtomicSteps st h newEp newPay macFn macKey faults) :
    BaseEntriesSafe macFn macKey h.vaultKeyId h.basePath watermark mid := by
  have hBase := hSafe
  rcases hSafe with ⟨hDrvDir, hMemSafe, hNandSafe⟩
  have hStage : ∀ s1 : PosixFsState,
      s1.driveCache.cachedDirEntries = none →
      assocLookup s1.kernel.dirInode.unsyncedEntries h.basePath =
        assocLookup st.kernel.dirInode.unsyncedEntries h.basePath →
      s1.nand.dirNandEntries = st.nand.dirNandEntries →
      st.nand.nextInode ≤ s1.nand.nextInode →
      (∀ ino < st.nand.nextInode,
        assocLookup s1.kernel.pageCache.dirtyFiles ino = assocLookup st.kernel.pageCache.dirtyFiles ino ∧
        assocLookup s1.driveCache.cachedFiles ino = assocLookup st.driveCache.cachedFiles ino ∧
        assocLookup s1.nand.fileBlocks ino = assocLookup st.nand.fileBlocks ino) →
      BaseEntriesSafe macFn macKey h.vaultKeyId h.basePath watermark s1 := by
    intro s1 hD hM hN hNext hFr
    refine ⟨hD, ?_, ?_⟩
    · rw [hM]; exact entryWatermarkSafe_frame hNext hFr hMemSafe
    · rw [hN]; exact entryWatermarkSafe_frame hNext hFr hNandSafe
  rw [replaceAtomicSteps.public_eq_1] at hMid
  by_cases hP : h.ioPoisoned = true
  · simp only [hP, ↓reduceIte, List.mem_singleton] at hMid
    rw [hMid]; exact hBase
  · simp only [hP, Bool.false_eq_true, ↓reduceIte] at hMid
    by_cases hBnd : (!(decide (newEp < 2 ^ 64)) || !(decide (newPay.length < 2 ^ 32))) = true
    · simp only [hBnd, ↓reduceIte, List.mem_singleton] at hMid
      rw [hMid]; exact hBase
    · simp only [hBnd, Bool.false_eq_true, ↓reduceIte] at hMid
      have hEp64 : newEp < 2 ^ 64 := by
        cases hd : decide (newEp < 2 ^ 64)
        · exfalso; apply hBnd; simp [hd]
        · exact of_decide_eq_true hd
      have hPay32 : newPay.length < 2 ^ 32 := by
        cases hd : decide (newPay.length < 2 ^ 32)
        · exfalso; apply hBnd; simp [hd]
        · exact of_decide_eq_true hd
      cases hLk : resolveOpenFd st.kernel.openFds h.pid h.lockFd with
      | none =>
        rw [hLk] at hMid
        simp only [List.mem_singleton] at hMid
        rw [hMid]; exact hBase
      | some dPair =>
        rcases dPair with ⟨descId, lockDesc⟩
        rw [hLk] at hMid; dsimp only at hMid
        by_cases hInv :
            (descId != h.lockDescId || lockDesc.inode != h.lockInode || lockDesc.stickyFsyncErr ||
             st.kernel.flockTable.owner h.lockInode != some h.lockDescId) = true
        · simp only [hInv, ↓reduceIte, List.mem_singleton] at hMid
          rw [hMid]; exact hBase
        · simp only [hInv, Bool.false_eq_true, ↓reduceIte] at hMid
          let tmpPath := walTmpPath h.basePath
          have hTmpNeBase : h.basePath ≠ tmpPath := fun he => walTmpPath_ne_base h.basePath he.symm
          let stClean := posixUnlinkIfPresent st tmpPath
          let tmpIno := st.nand.nextInode
          let tmpFd := st.nextFd
          let tmpDescId := st.kernel.openFds.nextDescId
          let newRec := signWalRecord macFn macKey
            { vaultKeyId := h.vaultKeyId, lockGenesisId := h.lockGenesisId,
              epoch := newEp, payload := newPay }
          let stCreated : PosixFsState :=
            { kernel := { stClean.kernel with
                           openFds := { fdRefs := assocInsert (h.pid, tmpFd) tmpDescId st.kernel.openFds.fdRefs
                                        descriptions := assocInsert tmpDescId
                                                          { inode := tmpIno, writable := true, stickyFsyncErr := false }
                                                          st.kernel.openFds.descriptions
                                        nextDescId := tmpDescId + 1 }
                           dirInode := { unsyncedEntries :=
                                           assocInsert tmpPath (.regular tmpIno)
                                             stClean.kernel.dirInode.unsyncedEntries } }
              driveCache := st.driveCache
              nand := { st.nand with
                         fileBlocks := assocInsert tmpIno [] st.nand.fileBlocks
                         nextInode := tmpIno + 1 }
              nextFd := tmpFd + 1 }
          have hCrEq : posixCreateExclNoFollow stClean h.pid tmpPath = .ok (stCreated, tmpFd, tmpIno) := by
            rw [posixCreateExclNoFollow.public_eq_1]
            have hAbs : assocLookup stClean.kernel.dirInode.unsyncedEntries tmpPath = none := by
              simp [stClean, posixUnlinkIfPresent]
            rw [hAbs]; rfl
          rw [hCrEq] at hMid; dsimp only at hMid
          let stWritten : PosixFsState :=
            { stCreated with
               kernel := { stCreated.kernel with
                            pageCache := { dirtyFiles :=
                                             assocInsert tmpIno (encodeWalRecord newRec)
                                               st.kernel.pageCache.dirtyFiles } } }
          have hWrEq : posixPwriteAll stCreated h.pid tmpFd (encodeWalRecord newRec) = .ok stWritten := by
            rw [posixPwriteAll.public_eq_1]
            simp [stWritten, stCreated, stClean, posixUnlinkIfPresent, resolveOpenFd_insert_self]
          rw [hWrEq] at hMid; dsimp only at hMid
          have hBaseSame :
              assocLookup (assocInsert tmpPath (.regular tmpIno)
                stClean.kernel.dirInode.unsyncedEntries) h.basePath =
                assocLookup st.kernel.dirInode.unsyncedEntries h.basePath := by
            simp [stClean, posixUnlinkIfPresent, hTmpNeBase]
          have hClean : BaseEntriesSafe macFn macKey h.vaultKeyId h.basePath watermark stClean :=
            hStage stClean hDrvDir (by simp [stClean, posixUnlinkIfPresent, hTmpNeBase]) rfl
              (Nat.le_refl _) (fun _ _ => ⟨rfl, rfl, rfl⟩)
          have hCreated : BaseEntriesSafe macFn macKey h.vaultKeyId h.basePath watermark stCreated :=
            hStage stCreated hDrvDir hBaseSame rfl (Nat.le_succ _) (by
              intro ino hLt
              have hNe : ino ≠ tmpIno := Nat.ne_of_lt hLt
              simp [stCreated, stClean, posixUnlinkIfPresent, hNe])
          have hWritten : BaseEntriesSafe macFn macKey h.vaultKeyId h.basePath watermark stWritten :=
            hStage stWritten hDrvDir hBaseSame rfl (Nat.le_succ _) (by
              intro ino hLt
              have hNe : ino ≠ tmpIno := Nat.ne_of_lt hLt
              simp [stWritten, stCreated, hNe])
          cases hFR : faults.failRecordSync with
          | true =>
            rw [hFR] at hMid
            let sSy : PosixFsState :=
              { stWritten with
                  kernel := { stWritten.kernel with
                                openFds := { stWritten.kernel.openFds with
                                               descriptions := assocInsert tmpDescId
                                                 { inode := tmpIno, writable := true, stickyFsyncErr := true }
                                                 stWritten.kernel.openFds.descriptions }
                                pageCache := { dirtyFiles := assocErase tmpIno stWritten.kernel.pageCache.dirtyFiles } }
                  driveCache := { stWritten.driveCache with
                                   cachedFiles := assocErase tmpIno st.driveCache.cachedFiles } }
            have hSyErr : posixSyncAllMedia stWritten h.pid tmpFd true = (sSy, .error .eio) := by
              rw [posixSyncAllMedia.public_eq_1]; simp [sSy, stWritten, stCreated, resolveOpenFd_insert_self]
            rw [hSyErr] at hMid; dsimp only at hMid
            have hc := posixCloseFd_preserves_storage sSy h.pid tmpFd
            have hSy : BaseEntriesSafe macFn macKey h.vaultKeyId h.basePath watermark sSy :=
              hStage sSy hDrvDir hBaseSame rfl (Nat.le_succ _) (by
                intro ino hLt
                have hNe : ino ≠ tmpIno := Nat.ne_of_lt hLt
                simp [sSy, stWritten, stCreated, hNe])
            have hCl : BaseEntriesSafe macFn macKey h.vaultKeyId h.basePath watermark
                ((posixCloseFd sSy h.pid tmpFd).toOption.getD sSy) :=
              hStage _ (by rw [hc.2.2.1]; exact hDrvDir) (by rw [hc.1]; exact hBaseSame)
                (by rw [hc.2.2.2]) (by rw [hc.2.2.2]; exact Nat.le_succ _) (by
                  intro ino hLt
                  have hNe : ino ≠ tmpIno := Nat.ne_of_lt hLt
                  rw [hc.2.1, hc.2.2.1, hc.2.2.2]
                  simp [sSy, stWritten, stCreated, hNe])
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hMid
            rcases hMid with hm | hm | hm | hm | hm | hm
            · rw [hm]; exact hBase
            · rw [hm]; exact hClean
            · rw [hm]; exact hCreated
            · rw [hm]; exact hWritten
            · rw [hm]; exact hSy
            · rw [hm]; exact hCl
          | false =>
            rw [hFR] at hMid
            let sSy : PosixFsState :=
              { stWritten with
                  kernel := { stWritten.kernel with
                                pageCache := { dirtyFiles := assocErase tmpIno stWritten.kernel.pageCache.dirtyFiles } }
                  driveCache := { stWritten.driveCache with
                                   cachedFiles := assocErase tmpIno st.driveCache.cachedFiles }
                  nand := { stWritten.nand with
                             fileBlocks := assocInsert tmpIno (encodeWalRecord newRec)
                                             stWritten.nand.fileBlocks } }
            have hSyOk : posixSyncAllMedia stWritten h.pid tmpFd false = (sSy, .ok ()) := by
              rw [posixSyncAllMedia.public_eq_1]
              unfold readInodeHierarchy
              unfold pendingVolatileWrite
              simp [sSy, stWritten, stCreated, resolveOpenFd_insert_self]
            rw [hSyOk] at hMid; dsimp only at hMid
            let sCl := (posixCloseFd sSy h.pid tmpFd).toOption.getD sSy
            have hc := posixCloseFd_preserves_storage sSy h.pid tmpFd
            have hSy : BaseEntriesSafe macFn macKey h.vaultKeyId h.basePath watermark sSy :=
              hStage sSy hDrvDir hBaseSame rfl (Nat.le_succ _) (by
                intro ino hLt
                have hNe : ino ≠ tmpIno := Nat.ne_of_lt hLt
                simp [sSy, stWritten, stCreated, hNe])
            have hCl : BaseEntriesSafe macFn macKey h.vaultKeyId h.basePath watermark sCl :=
              hStage sCl (by dsimp only [sCl]; rw [hc.2.2.1]; exact hDrvDir)
                (by dsimp only [sCl]; rw [hc.1]; exact hBaseSame)
                (by dsimp only [sCl]; rw [hc.2.2.2])
                (by dsimp only [sCl]; rw [hc.2.2.2]; exact Nat.le_succ _) (by
                  intro ino hLt
                  have hNe : ino ≠ tmpIno := Nat.ne_of_lt hLt
                  dsimp only [sCl]; rw [hc.2.1, hc.2.2.1, hc.2.2.2]
                  simp [sSy, stWritten, stCreated, hNe])
            have hTmpPres : assocLookup sCl.kernel.dirInode.unsyncedEntries tmpPath =
                some (.regular tmpIno) := by
              dsimp only [sCl]; rw [hc.1]; simp [sSy, stWritten, stCreated]
            let stRn : PosixFsState :=
              { sCl with
                 kernel := { sCl.kernel with
                              dirInode := { unsyncedEntries :=
                                              (if tmpPath == h.basePath then
                                                 assocInsert h.basePath (.regular tmpIno)
                                                   sCl.kernel.dirInode.unsyncedEntries
                                               else
                                                 assocErase tmpPath
                                                   (assocInsert h.basePath (.regular tmpIno)
                                                     sCl.kernel.dirInode.unsyncedEntries)) } } }
            have hRnEq : posixRename sCl (walTmpPath h.basePath) h.basePath = .ok stRn := by
              change posixRename sCl tmpPath h.basePath = _
              rw [posixRename.public_eq_1]; rw [hTmpPres]
            rw [hRnEq] at hMid; dsimp only at hMid
            have hTmpBeqBase : (tmpPath == h.basePath) = false := by
              cases hb : (tmpPath == h.basePath)
              · rfl
              · exfalso; exact walTmpPath_ne_base h.basePath (eq_of_beq hb)
            have hDecNew : ∀ r : WalRecord,
                decodeWalRecord (encodeWalRecord newRec) = some r → r.body.epoch = newEp := by
              intro r hDec
              have hNewWf : newRec.WellFormed :=
                signWalRecord_wellFormed hMacWf macKey ⟨hVkLen, hGidLen, hEp64, hPay32⟩
              rw [decodeWalRecord_encodeWalRecord hNewWf] at hDec
              injection hDec with hEqR
              rw [← hEqR]; rfl
            -- the freshly synced temp inode, as seen from any state sharing `sCl`'s storage
            have hTmpSafe : ∀ s1 : PosixFsState,
                s1.nand.nextInode = sCl.nand.nextInode →
                s1.kernel.pageCache = sCl.kernel.pageCache →
                s1.driveCache.cachedFiles = sCl.driveCache.cachedFiles →
                s1.nand.fileBlocks = sCl.nand.fileBlocks →
                EntryWatermarkSafe s1 h.vaultKeyId macFn macKey watermark (some (.regular tmpIno)) := by
              intro s1 e1 e2 e3 e4
              refine ⟨?_, ?_, ?_, encodeWalRecord newRec, ?_, ?_⟩
              · rw [e1]; dsimp only [sCl]; rw [hc.2.2.2]; simp [sSy, stWritten, stCreated]
              · rw [e2]; dsimp only [sCl]; rw [hc.2.1]; simp [sSy]
              · rw [e3]; dsimp only [sCl]; rw [hc.2.2.1]; simp [sSy]
              · rw [e4]; dsimp only [sCl]; rw [hc.2.2.2]; simp [sSy]
              · intro r hD _ _
                rw [hDecNew r hD]
                exact hLeNew
            have hRnMem : assocLookup stRn.kernel.dirInode.unsyncedEntries h.basePath =
                some (.regular tmpIno) := by
              dsimp only [stRn]
              rw [hTmpBeqBase]
              simp only [Bool.false_eq_true, ↓reduceIte, assocLookup_erase, hTmpNeBase,
                assocLookup_insert_self]
            have hRn : BaseEntriesSafe macFn macKey h.vaultKeyId h.basePath watermark stRn := by
              refine ⟨hCl.1, ?_, hCl.2.2⟩
              rw [hRnMem]
              exact hTmpSafe stRn rfl rfl rfl rfl
            have hLast : BaseEntriesSafe macFn macKey h.vaultKeyId h.basePath watermark
                (posixSyncParentDir stRn faults.failParentSync).1 := by
              cases faults.failParentSync with
              | true => exact hRn
              | false =>
                refine ⟨rfl, ?_, ?_⟩
                · change EntryWatermarkSafe _ h.vaultKeyId macFn macKey watermark
                    (assocLookup stRn.kernel.dirInode.unsyncedEntries h.basePath)
                  rw [hRnMem]
                  exact hTmpSafe _ rfl rfl rfl rfl
                · change EntryWatermarkSafe _ h.vaultKeyId macFn macKey watermark
                    (assocLookup stRn.kernel.dirInode.unsyncedEntries h.basePath)
                  rw [hRnMem]
                  exact hTmpSafe _ rfl rfl rfl rfl
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hMid
            rcases hMid with hm | hm | hm | hm | hm | hm | hm | hm
            · rw [hm]; exact hBase
            · rw [hm]; exact hClean
            · rw [hm]; exact hCreated
            · rw [hm]; exact hWritten
            · rw [hm]; exact hSy
            · rw [hm]; exact hCl
            · rw [hm]; exact hRn
            · rw [hm]; exact hLast

/-- Exact outcome characterization of fault-free `provisionGenesis` on an arbitrary `PosixFsState`:
    either `provisionGenesis` aborts before creating `basePath` (leaving `basePath` and all
    existing `< st.nand.nextInode` inodes untouched), OR it commits a fresh synced `rec0` at `epoch = 0`. -/
private theorem provisionGenesis_noFault_outcome
    (st : PosixFsState) (pid : Pid) (basePath : DirName)
    (vkId nonce initPay : List UInt8) (macFn : KeyedMacFn) (keyUsed : List UInt8) :
    let outPair := provisionGenesis st pid basePath vkId nonce initPay macFn keyUsed {}
    (outPair.1.driveCache.cachedDirEntries = st.driveCache.cachedDirEntries ∧
     assocLookup outPair.1.kernel.dirInode.unsyncedEntries basePath =
       assocLookup st.kernel.dirInode.unsyncedEntries basePath ∧
     assocLookup outPair.1.nand.dirNandEntries basePath =
       assocLookup st.nand.dirNandEntries basePath ∧
     st.nand.nextInode ≤ outPair.1.nand.nextInode ∧
     ∀ ino < st.nand.nextInode,
       assocLookup outPair.1.kernel.pageCache.dirtyFiles ino = assocLookup st.kernel.pageCache.dirtyFiles ino ∧
       assocLookup outPair.1.driveCache.cachedFiles ino = assocLookup st.driveCache.cachedFiles ino ∧
       assocLookup outPair.1.nand.fileBlocks ino = assocLookup st.nand.fileBlocks ino) ∨
    (vkId.length = 32 ∧ nonce.length = 32 ∧ initPay.length < 2 ^ 32 ∧
     let lockIno := st.nand.nextInode
     let recIno := st.nand.nextInode + 1
     let rec0 := signWalRecord macFn keyUsed
       { vaultKeyId := vkId
         lockGenesisId := computeLockGenesisId lockIno nonce
         epoch := 0
         payload := initPay }
     outPair.2 = .ok (lockIno, rec0) ∧
     outPair.1.driveCache.cachedDirEntries = none ∧
     assocLookup outPair.1.kernel.dirInode.unsyncedEntries basePath = some (.regular recIno) ∧
     assocLookup outPair.1.nand.dirNandEntries basePath = some (.regular recIno) ∧
     recIno < outPair.1.nand.nextInode ∧
     assocLookup outPair.1.kernel.pageCache.dirtyFiles recIno = none ∧
     assocLookup outPair.1.driveCache.cachedFiles recIno = none ∧
     assocLookup outPair.1.nand.fileBlocks recIno = some (encodeWalRecord rec0)) := by
  dsimp +zetaDelta only
  rw [provisionGenesis.public_eq_1]
  by_cases hInvalid :
      (vkId.length != 32 || nonce.length != 32 || !(decide (initPay.length < 2 ^ 32))) = true
  · rw [hInvalid]
    dsimp only [↓reduceIte]
    exact Or.inl ⟨rfl, rfl, rfl, Nat.le_refl _, fun _ _ => ⟨rfl, rfl, rfl⟩⟩
  · have hInvF : (vkId.length != 32 || nonce.length != 32 || !(decide (initPay.length < 2 ^ 32))) = false := by
      cases hb : (vkId.length != 32 || nonce.length != 32 || !(decide (initPay.length < 2 ^ 32)))
      · rfl
      · exfalso; exact hInvalid hb
    rw [hInvF]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hVk32 : vkId.length = 32 :=
      eq_of_not_bne_true (fun hc => hInvalid (by simp [hc]))
    have hNonce32 : nonce.length = 32 :=
      eq_of_not_bne_true (fun hc => hInvalid (by simp [hc]))
    have hPay32 : initPay.length < 2 ^ 32 := by
      cases hd : decide (initPay.length < 2 ^ 32)
      · exfalso; apply hInvalid; simp [hd]
      · exact of_decide_eq_true hd
    let lockPath := walLockPath basePath
    have hBaseNeLock : basePath ≠ lockPath := fun he => walLockPath_ne_base basePath he.symm
    cases hLookBase : assocLookup st.kernel.dirInode.unsyncedEntries basePath with
    | some _ =>
      dsimp only
      exact Or.inl ⟨rfl, hLookBase, rfl, Nat.le_refl _, fun _ _ => ⟨rfl, rfl, rfl⟩⟩
    | none =>
      cases hLookLock : assocLookup st.kernel.dirInode.unsyncedEntries (walLockPath basePath) with
      | some _ =>
        dsimp only
        exact Or.inl ⟨rfl, hLookBase, rfl, Nat.le_refl _, fun _ _ => ⟨rfl, rfl, rfl⟩⟩
      | none =>
        dsimp only
        let lockIno := st.nand.nextInode
        let lockFd := st.nextFd
        let lockDescId := st.kernel.openFds.nextDescId
        let st1 : PosixFsState :=
          { kernel := { st.kernel with
                         openFds := { fdRefs := assocInsert (pid, lockFd) lockDescId st.kernel.openFds.fdRefs
                                      descriptions := assocInsert lockDescId
                                                        { inode := lockIno, writable := true, stickyFsyncErr := false }
                                                        st.kernel.openFds.descriptions
                                      nextDescId := lockDescId + 1 }
                         dirInode := { unsyncedEntries :=
                                         assocInsert lockPath (.regular lockIno)
                                           st.kernel.dirInode.unsyncedEntries } }
            driveCache := st.driveCache
            nand := { st.nand with
                       fileBlocks := assocInsert lockIno [] st.nand.fileBlocks
                       nextInode := lockIno + 1 }
            nextFd := lockFd + 1 }
        have hCr1 : posixCreateExclNoFollow st pid lockPath = .ok (st1, lockFd, lockIno) := by
          rw [posixCreateExclNoFollow.public_eq_1]; rw [hLookLock]
        rw [hCr1]
        dsimp only
        cases hFlk : posixFlockExNb st1 pid lockFd with
        | error _ =>
          dsimp only
          left
          refine ⟨rfl, ?_, rfl, Nat.le_succ _, ?_⟩
          · dsimp +zetaDelta only [st1, lockPath] at hBaseNeLock ⊢; simp [hBaseNeLock, hLookBase]
          · intro ino hLt
            have hNe : ino ≠ lockIno := Nat.ne_of_lt hLt
            dsimp +zetaDelta only [st1, lockIno] at hNe ⊢
            simp [hNe]
        | ok st2 =>
          dsimp only
          have hSt2Eq :
              st2.kernel.openFds = st1.kernel.openFds ∧
              st2.kernel.pageCache = st1.kernel.pageCache ∧
              st2.kernel.dirInode = st1.kernel.dirInode ∧
              st2.driveCache = st1.driveCache ∧
              st2.nand = st1.nand ∧
              st2.nextFd = st1.nextFd := by
            rw [posixFlockExNb.public_eq_1] at hFlk
            dsimp only [st1] at hFlk
            simp only [resolveOpenFd_insert_self] at hFlk
            cases hOw : st.kernel.flockTable.owner lockIno with
            | none =>
              rw [hOw] at hFlk; injection hFlk with hEq; rw [← hEq]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
            | some hld =>
              rw [hOw] at hFlk; dsimp only at hFlk
              by_cases hh : (hld == lockDescId) = true
              · simp only [hh, ↓reduceIte] at hFlk
                injection hFlk with hEq; rw [← hEq]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
              · simp only [hh, Bool.false_eq_true, ↓reduceIte] at hFlk; cases hFlk
          right
          let lockSeal : LockSidecarSeal := { sealedLockInode := lockIno, genesisNonce := nonce }
          let st3 : PosixFsState :=
            { st2 with
               kernel := { st2.kernel with
                            pageCache := { dirtyFiles :=
                                             assocInsert lockIno (encodeLockSidecar lockSeal)
                                               st2.kernel.pageCache.dirtyFiles } } }
          have hWr1 : posixPwriteAll st2 pid lockFd (encodeLockSidecar lockSeal) = .ok st3 := by
            rw [posixPwriteAll.public_eq_1]
            rw [hSt2Eq.1]
            simp [st3, st1, resolveOpenFd_insert_self]
          rw [hWr1]
          dsimp only
          let st4 : PosixFsState :=
            { st3 with
                kernel := { st3.kernel with
                              pageCache := { dirtyFiles :=
                                               assocErase lockIno st3.kernel.pageCache.dirtyFiles } }
                driveCache := { st3.driveCache with
                                 cachedFiles := assocErase lockIno st3.driveCache.cachedFiles }
                nand := { st3.nand with
                           fileBlocks := assocInsert lockIno (encodeLockSidecar lockSeal)
                                           st3.nand.fileBlocks } }
          have hResLock3 : resolveOpenFd st3.kernel.openFds pid lockFd =
              some (lockDescId, { inode := lockIno, writable := true, stickyFsyncErr := false }) := by
            change resolveOpenFd st2.kernel.openFds pid lockFd = _
            rw [hSt2Eq.1]
            exact resolveOpenFd_insert_self st.kernel.openFds pid lockFd lockDescId _
          have hReadLock3 : readInodeHierarchy st3 lockIno = some (encodeLockSidecar lockSeal) := by
            have hDirty3 : assocLookup st3.kernel.pageCache.dirtyFiles lockIno =
                some (encodeLockSidecar lockSeal) :=
              assocLookup_insert_self _ _ _
            unfold readInodeHierarchy pendingVolatileWrite
            rw [hDirty3]
          have hSy1 : posixSyncAllMedia st3 pid lockFd false = (st4, .ok ()) := by
            rw [posixSyncAllMedia.public_eq_1]
            rw [hResLock3]
            dsimp only [Bool.false_eq_true, ↓reduceIte]
            rw [hReadLock3]
            rfl
          rw [hSy1]
          dsimp only
          have hSt4BaseNone : assocLookup st4.kernel.dirInode.unsyncedEntries basePath = none := by
            change assocLookup st2.kernel.dirInode.unsyncedEntries basePath = none
            rw [hSt2Eq.2.2.1]
            dsimp +zetaDelta only [st1, lockPath] at hBaseNeLock ⊢
            simp [hBaseNeLock, hLookBase]
          have hSt4Next : st4.nand.nextInode = lockIno + 1 := by
            change st2.nand.nextInode = lockIno + 1
            rw [hSt2Eq.2.2.2.2.1]
          have hSt4NextFd : st4.nextFd = lockFd + 1 := by
            change st2.nextFd = lockFd + 1
            rw [hSt2Eq.2.2.2.2.2]
          let recIno := lockIno + 1
          let recFd := lockFd + 1
          let recDescId := st4.kernel.openFds.nextDescId
          let st5 : PosixFsState :=
            { kernel := { st4.kernel with
                           openFds := { fdRefs := assocInsert (pid, recFd) recDescId st4.kernel.openFds.fdRefs
                                        descriptions := assocInsert recDescId
                                                          { inode := recIno, writable := true, stickyFsyncErr := false }
                                                          st4.kernel.openFds.descriptions
                                        nextDescId := recDescId + 1 }
                           dirInode := { unsyncedEntries :=
                                           assocInsert basePath (.regular recIno)
                                             st4.kernel.dirInode.unsyncedEntries } }
              driveCache := st4.driveCache
              nand := { st4.nand with
                         fileBlocks := assocInsert recIno [] st4.nand.fileBlocks
                         nextInode := recIno + 1 }
              nextFd := recFd + 1 }
          have hCr2 : posixCreateExclNoFollow st4 pid basePath = .ok (st5, recFd, recIno) := by
            rw [posixCreateExclNoFollow.public_eq_1]
            rw [hSt4BaseNone, hSt4Next, hSt4NextFd]
          rw [hCr2]
          dsimp only
          let rec0 := signWalRecord macFn keyUsed
            { vaultKeyId := vkId
              lockGenesisId := computeLockGenesisId lockIno nonce
              epoch := 0
              payload := initPay }
          let st6 : PosixFsState :=
            { st5 with
               kernel := { st5.kernel with
                            pageCache := { dirtyFiles :=
                                             assocInsert recIno (encodeWalRecord rec0)
                                               st5.kernel.pageCache.dirtyFiles } } }
          have hWr2 : posixPwriteAll st5 pid recFd (encodeWalRecord rec0) = .ok st6 := by
            rw [posixPwriteAll.public_eq_1]
            dsimp +zetaDelta only [st5]
            rw [resolveOpenFd_insert_self]
            rfl
          rw [hWr2]
          dsimp only
          let st7 : PosixFsState :=
            { st6 with
                kernel := { st6.kernel with
                              pageCache := { dirtyFiles :=
                                               assocErase recIno st6.kernel.pageCache.dirtyFiles } }
                driveCache := { st6.driveCache with
                                 cachedFiles := assocErase recIno st6.driveCache.cachedFiles }
                nand := { st6.nand with
                           fileBlocks := assocInsert recIno (encodeWalRecord rec0)
                                           st6.nand.fileBlocks } }
          have hResRec6 : resolveOpenFd st6.kernel.openFds pid recFd =
              some (recDescId, { inode := recIno, writable := true, stickyFsyncErr := false }) := by
            change resolveOpenFd st5.kernel.openFds pid recFd = _
            dsimp +zetaDelta only [st5]
            exact resolveOpenFd_insert_self st4.kernel.openFds pid recFd recDescId _
          have hReadRec6 : readInodeHierarchy st6 recIno = some (encodeWalRecord rec0) := by
            have hDirty6 : assocLookup st6.kernel.pageCache.dirtyFiles recIno =
                some (encodeWalRecord rec0) :=
              assocLookup_insert_self _ _ _
            unfold readInodeHierarchy pendingVolatileWrite
            rw [hDirty6]
          have hSy2 : posixSyncAllMedia st6 pid recFd false = (st7, .ok ()) := by
            rw [posixSyncAllMedia.public_eq_1]
            rw [hResRec6]
            dsimp only [Bool.false_eq_true, ↓reduceIte]
            rw [hReadRec6]
            rfl
          rw [hSy2]
          dsimp only
          let st8 : PosixFsState :=
            { st7 with
                driveCache := { st7.driveCache with cachedDirEntries := none }
                nand := { st7.nand with dirNandEntries := st7.kernel.dirInode.unsyncedEntries } }
          have hSyDir : posixSyncParentDir st7 false = (st8, .ok ()) := rfl
          rw [hSyDir]
          dsimp only
          let st9 := (posixCloseFd st8 pid recFd).toOption.getD st8
          let st10 := (posixCloseFd st9 pid lockFd).toOption.getD st9
          have hc8 := posixCloseFd_preserves_storage st8 pid recFd
          have hc9 := posixCloseFd_preserves_storage st9 pid lockFd
          have hDir10 : st10.kernel.dirInode = st8.kernel.dirInode := hc9.1.trans hc8.1
          have hPg10 : st10.kernel.pageCache = st8.kernel.pageCache := hc9.2.1.trans hc8.2.1
          have hDr10 : st10.driveCache = st8.driveCache := hc9.2.2.1.trans hc8.2.2.1
          have hNd10 : st10.nand = st8.nand := hc9.2.2.2.trans hc8.2.2.2
          refine ⟨hVk32, hNonce32, hPay32, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [hDr10]
          · rw [hDir10]; dsimp +zetaDelta only [st8, st7, st6, st5]; simp
          · rw [hNd10]; dsimp +zetaDelta only [st8, st7, st6, st5]; simp
          · rw [hNd10]; dsimp +zetaDelta only [st8, st7, st6, st5]; exact Nat.lt_succ_self _
          · rw [hPg10]; dsimp +zetaDelta only [st8, st7, st6]; simp
          · rw [hDr10]; dsimp +zetaDelta only [st8, st7, st6]; simp
          · rw [hNd10]; dsimp +zetaDelta only [st8, st7, st6]; simp

/-- Initial provisioned custody state establishes `CustodyMultiCrashInv` at `ghostWatermark = 0`. -/
