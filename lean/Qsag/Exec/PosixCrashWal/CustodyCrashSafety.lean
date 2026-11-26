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
theorem initProvisionedCustodyState_inv
    {pid : Pid} {basePath : DirName} {keyKind : StatefulKeyKind}
    {vaultKeyId genesisNonce : List UInt8} {maxEpochCap : Nat}
    {macFn : KeyedMacFn} {macKey : List UInt8}
    {s₀ : MultiCrashCustodyState}
    (hInit : initProvisionedCustodyState pid basePath keyKind vaultKeyId genesisNonce
               maxEpochCap macFn macKey = some s₀) :
    CustodyMultiCrashInv macFn macKey s₀ ∧
    s₀.ghostWatermark = 0 ∧
    s₀.activeHold = none ∧
    s₀.emittedReceipts = [] := by
  unfold initProvisionedCustodyState at hInit
  dsimp +zetaDelta only at hInit
  let initPay := encodeCustodyWalPayload keyKind maxEpochCap []
  have hOut := provisionGenesis_noFault_outcome PosixFsState.empty pid basePath
    vaultKeyId genesisNonce initPay macFn macKey
  dsimp +zetaDelta only at hOut
  cases hGen : provisionGenesis PosixFsState.empty pid basePath vaultKeyId genesisNonce initPay macFn macKey {} with
  | mk fs0 res0 =>
    rw [hGen] at hInit hOut
    dsimp +zetaDelta only at hOut
    cases res0 with
    | error _ => cases hInit
    | ok pair0 =>
      rcases pair0 with ⟨lockIno, recOut⟩
      injection hInit with hS0Eq
      rw [← hS0Eq]
      rcases hOut with hAbort | hOk
      · have hVk32 : vaultKeyId.length = 32 := by
          rw [provisionGenesis.public_eq_1] at hGen
          by_cases hInv : (vaultKeyId.length != 32 || genesisNonce.length != 32 ||
                           !(decide (initPay.length < 2 ^ 32))) = true
          · simp only [hInv, ↓reduceIte] at hGen
            cases (Prod.mk.inj hGen).2
          · exact eq_of_not_bne_true (fun hc => hInv (by simp [hc]))
        rcases hAbort with ⟨hDrv, hMemNone, hNandNone, _, _⟩
        refine ⟨⟨hVk32, List.nodup_nil, by simp, trivial, hDrv, ?_, ?_⟩, rfl, rfl, rfl⟩
        · dsimp only; rw [hMemNone]; trivial
        · dsimp only; rw [hNandNone]; trivial
      · rcases hOk with ⟨hVk32, _, _, _, hDrv, hMemReg, hNandReg, hInoLt, hPg, hDr, hBs⟩
        have hZeroSafe : EntryWatermarkSafe fs0 vaultKeyId macFn macKey 0
            (some (.regular (PosixFsState.empty.nand.nextInode + 1))) :=
          ⟨hInoLt, hPg, hDr, _, hBs, fun _ _ _ _ => Nat.zero_le _⟩
        refine ⟨⟨hVk32, List.nodup_nil, by simp, trivial, hDrv, ?_, ?_⟩, rfl, rfl, rfl⟩
        · dsimp only; rw [hMemReg]; exact hZeroSafe
        · dsimp only; rw [hNandReg]; exact hZeroSafe

/-- Constructive uniqueness under an injective-on-support `List.Nodup` projection (`0 choice-free`). -/
theorem eq_of_mem_of_map_nodup {α β : Type} {f : α → β} {xs : List α}
    (hNodup : (xs.map f).Nodup) {x y : α}
    (hx : x ∈ xs) (hy : y ∈ xs) (hEq : f x = f y) : x = y := by
  induction xs with
  | nil => cases hx
  | cons a rest ih =>
    simp only [List.map_cons, List.Nodup, List.pairwise_cons, List.mem_map] at hNodup
    rcases hNodup with ⟨hHeadFresh, hRestNodup⟩
    simp only [List.mem_cons] at hx hy
    rcases hx with rfl | hxRest
    · rcases hy with rfl | hyRest
      · rfl
      · exfalso; exact hHeadFresh (f y) ⟨y, hyRest, rfl⟩ hEq
    · rcases hy with rfl | hyRest
      · exfalso; exact hHeadFresh (f x) ⟨x, hxRest, rfl⟩ hEq.symm
      · exact ih hRestNodup hxRest hyRest

private theorem atomicSignStep_preserves_inv
    {macFn : KeyedMacFn} (hMacWf : WellFormedMacFn macFn) {macKey : List UInt8}
    {s : MultiCrashCustodyState} (pid : Pid) (msg : List UInt8) (faults : IoFaultSchedule)
    (hInv : CustodyMultiCrashInv macFn macKey s) :
    let (s', _) :=
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
    CustodyMultiCrashInv macFn macKey s' ∧
    s.ghostWatermark ≤ s'.ghostWatermark ∧
    (∃ newRs, s'.emittedReceipts = s.emittedReceipts ++ newRs ∧
      (∀ w₀ : Nat,
        w₀ ≤ s.ghostWatermark →
        (match s.activeHold with | none => True | some (_, resEp, _) => w₀ ≤ resEp) →
        (match s'.activeHold with | none => True | some (_, resEp, _) => w₀ ≤ resEp) ∧
        ∀ r ∈ newRs, w₀ ≤ r.epoch)) := by
  rcases hInv with ⟨hVk32, hNodup, hRcpts, hHold, hDrvDir, hMemSafe, hNandSafe⟩
  dsimp only
  cases hOp : openExisting s.fs pid s.basePath s.vaultKeyId macFn macKey with
  | mk fs1 opRes =>
    cases opRes with
    | error _ =>
      obtain ⟨hd, hp, hdr, hn⟩ := openExisting_err_preserves_storage hOp
      have hFrame1 : ∀ ino < s.fs.nand.nextInode,
          assocLookup fs1.kernel.pageCache.dirtyFiles ino = assocLookup s.fs.kernel.pageCache.dirtyFiles ino ∧
          assocLookup fs1.driveCache.cachedFiles ino = assocLookup s.fs.driveCache.cachedFiles ino ∧
          assocLookup fs1.nand.fileBlocks ino = assocLookup s.fs.nand.fileBlocks ino := by
        intro ino _; rw [hp, hdr, hn]; exact ⟨rfl, rfl, rfl⟩
      refine ⟨⟨hVk32, hNodup, hRcpts, hHold, ?_, ?_, ?_⟩, Nat.le_refl _,
        ⟨[], by simp, fun _ _ hH => ⟨hH, by simp⟩⟩⟩
      · dsimp only; rw [hdr]; exact hDrvDir
      · dsimp only; rw [hd]
        exact entryWatermarkSafe_frame (by rw [hn]; exact Nat.le_refl _) hFrame1 hMemSafe
      · dsimp only; rw [hn]
        exact entryWatermarkSafe_frame (by rw [hn]; exact Nat.le_refl _) hFrame1 hNandSafe
    | ok hAndRec =>
      rcases hAndRec with ⟨h, rec⟩
      obtain ⟨hd, hp, hdr, hn, hBaseEq, hVkEqH, hGid40, hWmLe⟩ :=
        openExisting_preserves_storage_and_bounds_epoch hMemSafe hOp
      have hFrameOpen : ∀ ino < s.fs.nand.nextInode,
          assocLookup fs1.kernel.pageCache.dirtyFiles ino = assocLookup s.fs.kernel.pageCache.dirtyFiles ino ∧
          assocLookup fs1.driveCache.cachedFiles ino = assocLookup s.fs.driveCache.cachedFiles ino ∧
          assocLookup fs1.nand.fileBlocks ino = assocLookup s.fs.nand.fileBlocks ino := by
        intro ino _; rw [hp, hdr, hn]; exact ⟨rfl, rfl, rfl⟩
      have hFs1Mem : EntryWatermarkSafe fs1 h.vaultKeyId macFn macKey s.ghostWatermark
          (assocLookup fs1.kernel.dirInode.unsyncedEntries h.basePath) := by
        rw [hBaseEq, hVkEqH, hd]
        exact entryWatermarkSafe_frame (by rw [hn]; exact Nat.le_refl _) hFrameOpen hMemSafe
      have hFs1Nand : EntryWatermarkSafe fs1 h.vaultKeyId macFn macKey s.ghostWatermark
          (assocLookup fs1.nand.dirNandEntries h.basePath) := by
        rw [hBaseEq, hVkEqH, hn]
        exact entryWatermarkSafe_frame (by rw [hn]; exact Nat.le_refl _) hFrameOpen hNandSafe
      have hFs1Drv : fs1.driveCache.cachedDirEntries = none := by
        rw [hdr]; exact hDrvDir
      dsimp only
      by_cases hCap :
          (!(decide (rec.body.epoch < s.maxEpochCap)) ||
           !(decide (rec.body.epoch + 1 < 2 ^ 64))) = true
      · simp only [hCap, ↓reduceIte]
        let fsCl := (closeVaultHandle fs1 h).toOption.getD fs1
        have hc := posixCloseFd_preserves_storage fs1 h.pid h.lockFd
        have hFrameCl : ∀ ino < fs1.nand.nextInode,
            assocLookup fsCl.kernel.pageCache.dirtyFiles ino = assocLookup fs1.kernel.pageCache.dirtyFiles ino ∧
            assocLookup fsCl.driveCache.cachedFiles ino = assocLookup fs1.driveCache.cachedFiles ino ∧
            assocLookup fsCl.nand.fileBlocks ino = assocLookup fs1.nand.fileBlocks ino := by
          intro ino _
          dsimp only [fsCl, closeVaultHandle]
          rw [hc.2.1, hc.2.2.1, hc.2.2.2]
          exact ⟨rfl, rfl, rfl⟩
        refine ⟨⟨hVk32, hNodup, hRcpts, hHold, ?_, ?_, ?_⟩, Nat.le_refl _,
          ⟨[], by simp, fun _ _ hH => ⟨hH, by simp⟩⟩⟩
        · dsimp only [fsCl, closeVaultHandle]; rw [hc.2.2.1]; exact hFs1Drv
        · dsimp only [fsCl, closeVaultHandle]; rw [hc.1, ← hBaseEq, ← hVkEqH]
          exact entryWatermarkSafe_frame (by rw [hc.2.2.2]; exact Nat.le_refl _)
            hFrameCl hFs1Mem
        · dsimp only [fsCl, closeVaultHandle]; rw [hc.2.2.2, ← hBaseEq, ← hVkEqH]
          exact entryWatermarkSafe_frame (by rw [hc.2.2.2]; exact Nat.le_refl _)
            hFrameCl hFs1Nand
      · simp only [hCap, Bool.false_eq_true, ↓reduceIte]
        let reservedEp := rec.body.epoch
        let nextPayload := encodeCustodyWalPayload s.keyKind s.maxEpochCap msg
        cases hRep : replaceAtomic fs1 h (reservedEp + 1) nextPayload macFn macKey faults with
        | mk fsRep restRep =>
          rcases restRep with ⟨hAfter, repRes⟩
          have hSafeRep := replaceAtomic_preserves_entryWatermarkSafe hMacWf
            (by rw [hVkEqH]; exact hVk32) hGid40 hFs1Drv hFs1Mem hFs1Nand
            (Nat.le_trans hWmLe (Nat.le_succ _)) hRep
          rcases hSafeRep with ⟨hRepDrv, hRepCases⟩
          let fsClosed := (closeVaultHandle fsRep hAfter).toOption.getD fsRep
          have hc := posixCloseFd_preserves_storage fsRep hAfter.pid hAfter.lockFd
          have hFrameCl : ∀ ino < fsRep.nand.nextInode,
              assocLookup fsClosed.kernel.pageCache.dirtyFiles ino = assocLookup fsRep.kernel.pageCache.dirtyFiles ino ∧
              assocLookup fsClosed.driveCache.cachedFiles ino = assocLookup fsRep.driveCache.cachedFiles ino ∧
              assocLookup fsClosed.nand.fileBlocks ino = assocLookup fsRep.nand.fileBlocks ino := by
            intro ino _
            dsimp only [fsClosed, closeVaultHandle]
            rw [hc.2.1, hc.2.2.1, hc.2.2.2]
            exact ⟨rfl, rfl, rfl⟩
          dsimp +zetaDelta only
          cases repRes with
          | error _ =>
            rcases hRepCases with ⟨hErrMem, hErrNand⟩
            refine ⟨⟨hVk32, hNodup, hRcpts, hHold, ?_, ?_, ?_⟩, Nat.le_refl _,
              ⟨[], by simp, fun _ _ hH => ⟨hH, by simp⟩⟩⟩
            · dsimp only [fsClosed, closeVaultHandle]; rw [hc.2.2.1]; exact hRepDrv
            · dsimp only [fsClosed, closeVaultHandle]; rw [hc.1, ← hBaseEq, ← hVkEqH]
              exact entryWatermarkSafe_frame
                (by rw [hc.2.2.2]; exact Nat.le_refl _)
                hFrameCl hErrMem
            · dsimp only [fsClosed, closeVaultHandle]; rw [hc.2.2.2, ← hBaseEq, ← hVkEqH]
              exact entryWatermarkSafe_frame
                (by rw [hc.2.2.2]; exact Nat.le_refl _)
                hFrameCl hErrNand
          | ok _ =>
            rcases hRepCases with ⟨hOkMem, hOkNand⟩
            let rcpt : SignedEpochReceipt :=
              { keyKind := s.keyKind, vaultKeyId := s.vaultKeyId, epoch := reservedEp, msg := msg }
            have hFreshEp : ∀ e ∈ s.emittedReceipts.map (·.epoch), e ≠ reservedEp := by
              intro e hMemE
              rcases List.mem_map.mp hMemE with ⟨rOld, hROld, rfl⟩
              exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (hRcpts rOld hROld).1 hWmLe)
            have hNodupNew : ((s.emittedReceipts ++ [rcpt]).map (·.epoch)).Nodup := by
              rw [List.map_append]
              exact nodup_snoc hNodup hFreshEp
            have hRcptsNew : ∀ r ∈ s.emittedReceipts ++ [rcpt],
                r.epoch < reservedEp + 1 ∧ r.keyKind = s.keyKind ∧ r.vaultKeyId = s.vaultKeyId := by
              intro r hr
              rcases List.mem_append.mp hr with hOld | hSing
              · obtain ⟨h1, h2, h3⟩ := hRcpts r hOld
                exact ⟨Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le h1 hWmLe), h2, h3⟩
              · simp only [List.mem_singleton] at hSing
                subst hSing
                exact ⟨Nat.lt_succ_self _, rfl, rfl⟩
            have hHoldNew :
                match s.activeHold with
                | none => True
                | some (_, resEp, _) =>
                  resEp < reservedEp + 1 ∧ ∀ r ∈ s.emittedReceipts ++ [rcpt], r.epoch ≠ resEp := by
              cases hAh : s.activeHold with
              | none => trivial
              | some triple =>
                rcases triple with ⟨_, resEp, _⟩
                rw [hAh] at hHold
                rcases hHold with ⟨hResLt, hResNe⟩
                have hResLtEp : resEp < reservedEp := Nat.lt_of_lt_of_le hResLt hWmLe
                refine ⟨Nat.lt_succ_of_lt hResLtEp, ?_⟩
                intro r hr
                rcases List.mem_append.mp hr with hOld | hSing
                · exact hResNe r hOld
                · simp only [List.mem_singleton] at hSing
                  subst hSing
                  exact Nat.ne_of_gt hResLtEp
            refine ⟨⟨hVk32, hNodupNew, hRcptsNew, hHoldNew, ?_, ?_, ?_⟩,
              Nat.le_trans hWmLe (Nat.le_succ _),
              ⟨[rcpt], rfl, fun w₀ hw₀ hH => ⟨hH, ?_⟩⟩⟩
            · dsimp only [fsClosed, closeVaultHandle]; rw [hc.2.2.1]; exact hRepDrv
            · dsimp only [fsClosed, closeVaultHandle]; rw [hc.1, ← hBaseEq, ← hVkEqH]
              exact entryWatermarkSafe_frame
                (by rw [hc.2.2.2]; exact Nat.le_refl _)
                hFrameCl hOkMem
            · dsimp only [fsClosed, closeVaultHandle]; rw [hc.2.2.2, ← hBaseEq, ← hVkEqH]
              exact entryWatermarkSafe_frame
                (by rw [hc.2.2.2]; exact Nat.le_refl _)
                hFrameCl hOkNand
            · intro r hr
              simp only [List.mem_singleton] at hr
              subst hr
              exact Nat.le_trans hw₀ hWmLe

/-- Single-turn inductive preservation theorem across every `MultiCrashWalEvent` constructor, including crashes in the middle of a reservation. -/
theorem stepMultiCrashCustody_preserves_inv
    {macFn : KeyedMacFn} (hMacWf : WellFormedMacFn macFn) {macKey : List UInt8}
    (hRogueReject : ∀ b : WalRecordBody, b.epoch = 0 → b.payload = [] →
      verifyWalMac macFn macKey (signWalRecord macFn [] b) = false)
    {s : MultiCrashCustodyState} (ev : MultiCrashWalEvent)
    (hInv : CustodyMultiCrashInv macFn macKey s) :
    let (s', _) := stepMultiCrashCustody macFn macKey s ev
    CustodyMultiCrashInv macFn macKey s' ∧
    s.ghostWatermark ≤ s'.ghostWatermark ∧
    (∃ newRs, s'.emittedReceipts = s.emittedReceipts ++ newRs ∧
      (∀ w₀ : Nat,
        w₀ ≤ s.ghostWatermark →
        (match s.activeHold with | none => True | some (_, resEp, _) => w₀ ≤ resEp) →
        (match s'.activeHold with | none => True | some (_, resEp, _) => w₀ ≤ resEp) ∧
        ∀ r ∈ newRs, w₀ ≤ r.epoch)) := by
  cases ev with
  | signAtomic pid msg faults =>
    unfold stepMultiCrashCustody
    exact atomicSignStep_preserves_inv hMacWf pid msg faults hInv
  | contenderSignAttempt contenderPid msg =>
    unfold stepMultiCrashCustody
    exact atomicSignStep_preserves_inv hMacWf contenderPid msg {} hInv
  | beginReserveHoldLock pid msg faults =>
    unfold stepMultiCrashCustody
    cases hAh : s.activeHold with
    | some _ =>
      dsimp only
      exact ⟨hInv, Nat.le_refl _, ⟨[], by simp, fun _ _ hH => ⟨by rw [hAh]; exact hH, by simp⟩⟩⟩
    | none =>
      dsimp only
      rcases hInv with ⟨hVk32, hNodup, hRcpts, _, hDrvDir, hMemSafe, hNandSafe⟩
      cases hOp : openExisting s.fs pid s.basePath s.vaultKeyId macFn macKey with
      | mk fs1 opRes =>
        cases opRes with
        | error _ =>
          dsimp +zetaDelta only
          obtain ⟨hd, hp, hdr, hn⟩ := openExisting_err_preserves_storage hOp
          have hFrame1 : ∀ ino < s.fs.nand.nextInode,
              assocLookup fs1.kernel.pageCache.dirtyFiles ino = assocLookup s.fs.kernel.pageCache.dirtyFiles ino ∧
              assocLookup fs1.driveCache.cachedFiles ino = assocLookup s.fs.driveCache.cachedFiles ino ∧
              assocLookup fs1.nand.fileBlocks ino = assocLookup s.fs.nand.fileBlocks ino := by
            intro ino _; rw [hp, hdr, hn]; exact ⟨rfl, rfl, rfl⟩
          refine ⟨⟨hVk32, hNodup, hRcpts, trivial, ?_, ?_, ?_⟩, Nat.le_refl _,
            ⟨[], by simp, fun _ _ _ => ⟨trivial, by simp⟩⟩⟩
          · dsimp only; rw [hdr]; exact hDrvDir
          · dsimp only; rw [hd]
            exact entryWatermarkSafe_frame (by rw [hn]; exact Nat.le_refl _) hFrame1 hMemSafe
          · dsimp only; rw [hn]
            exact entryWatermarkSafe_frame (by rw [hn]; exact Nat.le_refl _) hFrame1 hNandSafe
        | ok hAndRec =>
          rcases hAndRec with ⟨h, rec⟩
          obtain ⟨hd, hp, hdr, hn, hBaseEq, hVkEqH, hGid40, hWmLe⟩ :=
            openExisting_preserves_storage_and_bounds_epoch hMemSafe hOp
          have hFrameOpen : ∀ ino < s.fs.nand.nextInode,
              assocLookup fs1.kernel.pageCache.dirtyFiles ino = assocLookup s.fs.kernel.pageCache.dirtyFiles ino ∧
              assocLookup fs1.driveCache.cachedFiles ino = assocLookup s.fs.driveCache.cachedFiles ino ∧
              assocLookup fs1.nand.fileBlocks ino = assocLookup s.fs.nand.fileBlocks ino := by
            intro ino _; rw [hp, hdr, hn]; exact ⟨rfl, rfl, rfl⟩
          have hFs1Mem : EntryWatermarkSafe fs1 h.vaultKeyId macFn macKey s.ghostWatermark
              (assocLookup fs1.kernel.dirInode.unsyncedEntries h.basePath) := by
            rw [hBaseEq, hVkEqH, hd]
            exact entryWatermarkSafe_frame (by rw [hn]; exact Nat.le_refl _) hFrameOpen hMemSafe
          have hFs1Nand : EntryWatermarkSafe fs1 h.vaultKeyId macFn macKey s.ghostWatermark
              (assocLookup fs1.nand.dirNandEntries h.basePath) := by
            rw [hBaseEq, hVkEqH, hn]
            exact entryWatermarkSafe_frame (by rw [hn]; exact Nat.le_refl _) hFrameOpen hNandSafe
          have hFs1Drv : fs1.driveCache.cachedDirEntries = none := by rw [hdr]; exact hDrvDir
          dsimp +zetaDelta only
          by_cases hCap :
              (!(decide (rec.body.epoch < s.maxEpochCap)) ||
               !(decide (rec.body.epoch + 1 < 2 ^ 64))) = true
          · simp only [hCap, ↓reduceIte]
            let fsCl := (closeVaultHandle fs1 h).toOption.getD fs1
            have hc := posixCloseFd_preserves_storage fs1 h.pid h.lockFd
            have hFrameCl : ∀ ino < fs1.nand.nextInode,
                assocLookup fsCl.kernel.pageCache.dirtyFiles ino = assocLookup fs1.kernel.pageCache.dirtyFiles ino ∧
                assocLookup fsCl.driveCache.cachedFiles ino = assocLookup fs1.driveCache.cachedFiles ino ∧
                assocLookup fsCl.nand.fileBlocks ino = assocLookup fs1.nand.fileBlocks ino := by
              intro ino _; dsimp only [fsCl, closeVaultHandle]
              rw [hc.2.1, hc.2.2.1, hc.2.2.2]; exact ⟨rfl, rfl, rfl⟩
            refine ⟨⟨hVk32, hNodup, hRcpts, trivial, ?_, ?_, ?_⟩, Nat.le_refl _,
              ⟨[], by simp, fun _ _ _ => ⟨trivial, by simp⟩⟩⟩
            · dsimp only [fsCl, closeVaultHandle]; rw [hc.2.2.1]; exact hFs1Drv
            · dsimp only [fsCl, closeVaultHandle]; rw [hc.1, ← hBaseEq, ← hVkEqH]
              exact entryWatermarkSafe_frame
                (by rw [hc.2.2.2]; exact Nat.le_refl _)
                hFrameCl hFs1Mem
            · dsimp only [fsCl, closeVaultHandle]; rw [hc.2.2.2, ← hBaseEq, ← hVkEqH]
              exact entryWatermarkSafe_frame
                (by rw [hc.2.2.2]; exact Nat.le_refl _)
                hFrameCl hFs1Nand
          · simp only [hCap, Bool.false_eq_true, ↓reduceIte]
            let reservedEp := rec.body.epoch
            let nextPayload := encodeCustodyWalPayload s.keyKind s.maxEpochCap msg
            cases hRep : replaceAtomic fs1 h (reservedEp + 1) nextPayload macFn macKey faults with
            | mk fsRep restRep =>
              rcases restRep with ⟨hAfter, repRes⟩
              have hSafeRep := replaceAtomic_preserves_entryWatermarkSafe hMacWf
                (by rw [hVkEqH]; exact hVk32) hGid40 hFs1Drv hFs1Mem hFs1Nand
                (Nat.le_trans hWmLe (Nat.le_succ _)) hRep
              rcases hSafeRep with ⟨hRepDrv, hRepCases⟩
              dsimp +zetaDelta only
              cases repRes with
              | error _ =>
                dsimp +zetaDelta only
                rcases hRepCases with ⟨hErrMem, hErrNand⟩
                let fsCl := (closeVaultHandle fsRep hAfter).toOption.getD fsRep
                have hc := posixCloseFd_preserves_storage fsRep hAfter.pid hAfter.lockFd
                have hFrameCl : ∀ ino < fsRep.nand.nextInode,
                    assocLookup fsCl.kernel.pageCache.dirtyFiles ino = assocLookup fsRep.kernel.pageCache.dirtyFiles ino ∧
                    assocLookup fsCl.driveCache.cachedFiles ino = assocLookup fsRep.driveCache.cachedFiles ino ∧
                    assocLookup fsCl.nand.fileBlocks ino = assocLookup fsRep.nand.fileBlocks ino := by
                  intro ino _; dsimp only [fsCl, closeVaultHandle]
                  rw [hc.2.1, hc.2.2.1, hc.2.2.2]; exact ⟨rfl, rfl, rfl⟩
                refine ⟨⟨hVk32, hNodup, hRcpts, trivial, ?_, ?_, ?_⟩, Nat.le_refl _,
                  ⟨[], by simp, fun _ _ _ => ⟨trivial, by simp⟩⟩⟩
                · dsimp only [fsCl, closeVaultHandle]; rw [hc.2.2.1]; exact hRepDrv
                · dsimp only [fsCl, closeVaultHandle]; rw [hc.1, ← hBaseEq, ← hVkEqH]
                  exact entryWatermarkSafe_frame
                    (by rw [hc.2.2.2]; exact Nat.le_refl _)
                    hFrameCl hErrMem
                · dsimp only [fsCl, closeVaultHandle]; rw [hc.2.2.2, ← hBaseEq, ← hVkEqH]
                  exact entryWatermarkSafe_frame
                    (by rw [hc.2.2.2]; exact Nat.le_refl _)
                    hFrameCl hErrNand
              | ok _ =>
                dsimp +zetaDelta only
                rcases hRepCases with ⟨hOkMem, hOkNand⟩
                have hRcptsUp : ∀ r ∈ s.emittedReceipts,
                    r.epoch < reservedEp + 1 ∧ r.keyKind = s.keyKind ∧ r.vaultKeyId = s.vaultKeyId := by
                  intro r hr
                  obtain ⟨h1, h2, h3⟩ := hRcpts r hr
                  exact ⟨Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le h1 hWmLe), h2, h3⟩
                have hHoldFresh :
                    reservedEp < reservedEp + 1 ∧ ∀ r ∈ s.emittedReceipts, r.epoch ≠ reservedEp := by
                  refine ⟨Nat.lt_succ_self _, ?_⟩
                  intro r hr
                  exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (hRcpts r hr).1 hWmLe)
                refine ⟨⟨hVk32, hNodup, hRcptsUp, hHoldFresh, hRepDrv, ?_, ?_⟩,
                  Nat.le_trans hWmLe (Nat.le_succ _),
                  ⟨[], by simp, fun _ hw₀ _ => ⟨Nat.le_trans hw₀ hWmLe, by simp⟩⟩⟩
                · dsimp only; rw [← hBaseEq, ← hVkEqH]; exact hOkMem
                · dsimp only; rw [← hBaseEq, ← hVkEqH]; exact hOkNand
  | finishSignFromHold =>
    unfold stepMultiCrashCustody
    cases hAh : s.activeHold with
    | none =>
      dsimp only
      exact ⟨hInv, Nat.le_refl _, ⟨[], by simp, fun _ _ _ => ⟨by rw [hAh]; trivial, by simp⟩⟩⟩
    | some holdTriple =>
      rcases holdTriple with ⟨h, reservedEp, msg⟩
      dsimp only
      rcases hInv with ⟨hVk32, hNodup, hRcpts, hHold, hDrvDir, hMemSafe, hNandSafe⟩
      rw [hAh] at hHold
      rcases hHold with ⟨hResLt, hResNe⟩
      let fsClosed := (closeVaultHandle s.fs h).toOption.getD s.fs
      have hc := posixCloseFd_preserves_storage s.fs h.pid h.lockFd
      have hFrameCl : ∀ ino < s.fs.nand.nextInode,
          assocLookup fsClosed.kernel.pageCache.dirtyFiles ino = assocLookup s.fs.kernel.pageCache.dirtyFiles ino ∧
          assocLookup fsClosed.driveCache.cachedFiles ino = assocLookup s.fs.driveCache.cachedFiles ino ∧
          assocLookup fsClosed.nand.fileBlocks ino = assocLookup s.fs.nand.fileBlocks ino := by
        intro ino _; dsimp only [fsClosed, closeVaultHandle]
        rw [hc.2.1, hc.2.2.1, hc.2.2.2]; exact ⟨rfl, rfl, rfl⟩
      let rcpt : SignedEpochReceipt :=
        { keyKind := s.keyKind, vaultKeyId := s.vaultKeyId, epoch := reservedEp, msg := msg }
      have hFreshEp : ∀ e ∈ s.emittedReceipts.map (·.epoch), e ≠ reservedEp := by
        intro e hMemE
        rcases List.mem_map.mp hMemE with ⟨rOld, hROld, rfl⟩
        exact hResNe rOld hROld
      have hNodupNew : ((s.emittedReceipts ++ [rcpt]).map (·.epoch)).Nodup := by
        rw [List.map_append]
        exact nodup_snoc hNodup hFreshEp
      have hRcptsNew : ∀ r ∈ s.emittedReceipts ++ [rcpt],
          r.epoch < s.ghostWatermark ∧ r.keyKind = s.keyKind ∧ r.vaultKeyId = s.vaultKeyId := by
        intro r hr
        rcases List.mem_append.mp hr with hOld | hSing
        · exact hRcpts r hOld
        · simp only [List.mem_singleton] at hSing
          subst hSing
          exact ⟨hResLt, rfl, rfl⟩
      refine ⟨⟨hVk32, hNodupNew, hRcptsNew, trivial, ?_, ?_, ?_⟩,
        Nat.le_refl _,
        ⟨[rcpt], rfl, fun _ _ hH => ⟨trivial, ?_⟩⟩⟩
      · dsimp only [fsClosed, closeVaultHandle]; rw [hc.2.2.1]; exact hDrvDir
      · dsimp only [fsClosed, closeVaultHandle]; rw [hc.1]
        exact entryWatermarkSafe_frame
          (by rw [hc.2.2.2]; exact Nat.le_refl _)
          hFrameCl hMemSafe
      · dsimp only [fsClosed, closeVaultHandle]; rw [hc.2.2.2]
        exact entryWatermarkSafe_frame
          (by rw [hc.2.2.2]; exact Nat.le_refl _)
          hFrameCl hNandSafe
      · intro r hr
        simp only [List.mem_singleton] at hr
        subst hr
        exact hH
  | midReserveCrash pid msg faults stepIdx crash =>
    unfold stepMultiCrashCustody
    rcases hInv with ⟨hVk32, hNodup, hRcpts, _, hDrvDir, hMemSafe, hNandSafe⟩
    have hFin : ∀ fsMid : PosixFsState,
        BaseEntriesSafe macFn macKey s.vaultKeyId s.basePath s.ghostWatermark fsMid →
        CustodyMultiCrashInv macFn macKey
          { s with fs := crash.apply fsMid, activeHold := none } := by
      intro fsMid hSafe
      obtain ⟨c1, c2, c3⟩ := baseEntriesSafe_after_crashStep hSafe (crash.apply_crashStep fsMid)
      exact ⟨hVk32, hNodup, hRcpts, trivial, c1, c2, c3⟩
    dsimp only
    cases hOp : openExisting s.fs pid s.basePath s.vaultKeyId macFn macKey with
    | mk fs1 opRes =>
      cases opRes with
      | error _ =>
        dsimp only
        obtain ⟨hd, hp, hdr, hn⟩ := openExisting_err_preserves_storage hOp
        have hFrame1 : ∀ ino < s.fs.nand.nextInode,
            assocLookup fs1.kernel.pageCache.dirtyFiles ino = assocLookup s.fs.kernel.pageCache.dirtyFiles ino ∧
            assocLookup fs1.driveCache.cachedFiles ino = assocLookup s.fs.driveCache.cachedFiles ino ∧
            assocLookup fs1.nand.fileBlocks ino = assocLookup s.fs.nand.fileBlocks ino := by
          intro ino _; rw [hp, hdr, hn]; exact ⟨rfl, rfl, rfl⟩
        have hSafe1 : BaseEntriesSafe macFn macKey s.vaultKeyId s.basePath s.ghostWatermark fs1 := by
          refine ⟨by rw [hdr]; exact hDrvDir, ?_, ?_⟩
          · rw [hd]
            exact entryWatermarkSafe_frame (by rw [hn]; exact Nat.le_refl _) hFrame1 hMemSafe
          · rw [hn]
            exact entryWatermarkSafe_frame (by rw [hn]; exact Nat.le_refl _) hFrame1 hNandSafe
        exact ⟨hFin fs1 hSafe1, Nat.le_refl _, ⟨[], by simp, fun _ _ _ => ⟨trivial, by simp⟩⟩⟩
      | ok hAndRec =>
        rcases hAndRec with ⟨h, rec⟩
        obtain ⟨hd, hp, hdr, hn, hBaseEq, hVkEqH, hGid40, hWmLe⟩ :=
          openExisting_preserves_storage_and_bounds_epoch hMemSafe hOp
        have hFrameOpen : ∀ ino < s.fs.nand.nextInode,
            assocLookup fs1.kernel.pageCache.dirtyFiles ino = assocLookup s.fs.kernel.pageCache.dirtyFiles ino ∧
            assocLookup fs1.driveCache.cachedFiles ino = assocLookup s.fs.driveCache.cachedFiles ino ∧
            assocLookup fs1.nand.fileBlocks ino = assocLookup s.fs.nand.fileBlocks ino := by
          intro ino _; rw [hp, hdr, hn]; exact ⟨rfl, rfl, rfl⟩
        have hSafe1 : BaseEntriesSafe macFn macKey s.vaultKeyId s.basePath s.ghostWatermark fs1 := by
          refine ⟨by rw [hdr]; exact hDrvDir, ?_, ?_⟩
          · rw [hd]
            exact entryWatermarkSafe_frame (by rw [hn]; exact Nat.le_refl _) hFrameOpen hMemSafe
          · rw [hn]
            exact entryWatermarkSafe_frame (by rw [hn]; exact Nat.le_refl _) hFrameOpen hNandSafe
        dsimp only
        by_cases hCap :
            (!(decide (rec.body.epoch < s.maxEpochCap)) ||
             !(decide (rec.body.epoch + 1 < 2 ^ 64))) = true
        · simp only [hCap, ↓reduceIte]
          exact ⟨hFin fs1 hSafe1, Nat.le_refl _, ⟨[], by simp, fun _ _ _ => ⟨trivial, by simp⟩⟩⟩
        · simp only [hCap, Bool.false_eq_true, ↓reduceIte]
          have hSafe1H : BaseEntriesSafe macFn macKey h.vaultKeyId h.basePath s.ghostWatermark fs1 := by
            rw [hBaseEq, hVkEqH]; exact hSafe1
          have hMidSafe := replaceAtomicSteps_all_baseEntriesSafe hMacWf
            (by rw [hVkEqH]; exact hVk32) hGid40 hSafe1H (Nat.le_trans hWmLe (Nat.le_succ _))
            (pickStepState_mem
              (self_mem_replaceAtomicSteps fs1 h (rec.body.epoch + 1)
                (encodeCustodyWalPayload s.keyKind s.maxEpochCap msg) macFn macKey faults) stepIdx)
          rw [hBaseEq, hVkEqH] at hMidSafe
          exact ⟨hFin _ hMidSafe, Nat.le_refl _, ⟨[], by simp, fun _ _ _ => ⟨trivial, by simp⟩⟩⟩
  | kernelPanic =>
    unfold stepMultiCrashCustody
    rcases hInv with ⟨hVk32, hNodup, hRcpts, _, hDrvDir, _, hNandSafe⟩
    have hCrSafe := entryWatermarkSafe_after_crashStep (CrashStep.kernelPanic s.fs) hNandSafe
    refine ⟨⟨hVk32, hNodup, hRcpts, trivial, rfl, ?_, ?_⟩,
      Nat.le_refl _,
      ⟨[], by simp, fun _ _ _ => ⟨trivial, by simp⟩⟩⟩
    · dsimp only [KernelPanicCrash]; rw [hDrvDir]; exact hCrSafe
    · dsimp only [KernelPanicCrash]; rw [hDrvDir]; exact hCrSafe
  | powerLoss dirPick defaultTear overrides =>
    unfold stepMultiCrashCustody
    rcases hInv with ⟨hVk32, hNodup, hRcpts, _, hDrvDir, hMemSafe, hNandSafe⟩
    let tearFn := evalFiniteTearSchedule defaultTear overrides
    cases dirPick with
    | revertToNand =>
      have hCrSafe := entryWatermarkSafe_after_crashStep
        (CrashStep.powerLoss .revertToNand tearFn s.fs) hNandSafe
      refine ⟨⟨hVk32, hNodup, hRcpts, trivial, rfl, ?_, ?_⟩,
        Nat.le_refl _,
        ⟨[], by simp, fun _ _ _ => ⟨trivial, by simp⟩⟩⟩
      · dsimp only [PowerLossCrash]; exact hCrSafe
      · dsimp only [PowerLossCrash]; exact hCrSafe
    | flushPendingDir =>
      have hCrSafe := entryWatermarkSafe_after_crashStep
        (CrashStep.powerLoss .flushPendingDir tearFn s.fs) hMemSafe
      refine ⟨⟨hVk32, hNodup, hRcpts, trivial, rfl, ?_, ?_⟩,
        Nat.le_refl _,
        ⟨[], by simp, fun _ _ _ => ⟨trivial, by simp⟩⟩⟩
      · dsimp only [PowerLossCrash]; rw [hDrvDir]; exact hCrSafe
      · dsimp only [PowerLossCrash]; rw [hDrvDir]; exact hCrSafe
  | unlinkLockSidecar =>
    unfold stepMultiCrashCustody
    rcases hInv with ⟨hVk32, hNodup, hRcpts, hHold, hDrvDir, hMemSafe, hNandSafe⟩
    dsimp only
    rw [posixUnlink.public_eq_1]
    have hBaseNeLock : s.basePath ≠ walLockPath s.basePath :=
      fun he => walLockPath_ne_base s.basePath he.symm
    cases assocLookup s.fs.kernel.dirInode.unsyncedEntries (walLockPath s.basePath) with
    | none =>
      simp only [Except.toOption, Option.getD_none]
      exact ⟨⟨hVk32, hNodup, hRcpts, hHold, hDrvDir, hMemSafe, hNandSafe⟩,
        Nat.le_refl _, ⟨[], by simp, fun _ _ hH => ⟨hH, by simp⟩⟩⟩
    | some _ =>
      simp only [Except.toOption, Option.getD_some]
      refine ⟨⟨hVk32, hNodup, hRcpts, hHold, hDrvDir, ?_, hNandSafe⟩,
        Nat.le_refl _, ⟨[], by simp, fun _ _ hH => ⟨hH, by simp⟩⟩⟩
      dsimp only
      simp only [assocLookup_erase, hBaseNeLock, ↓reduceIte]
      exact hMemSafe
  | recreateSpoofLock actorPid spoofBytes =>
    unfold stepMultiCrashCustody
    rcases hInv with ⟨hVk32, hNodup, hRcpts, hHold, hDrvDir, hMemSafe, _⟩
    dsimp only
    let lockPath := walLockPath s.basePath
    have hBaseNeLock : s.basePath ≠ lockPath :=
      fun he => walLockPath_ne_base s.basePath he.symm
    have hUnlNone :
        assocLookup (posixUnlinkIfPresent s.fs lockPath).kernel.dirInode.unsyncedEntries lockPath = none := by
      simp [posixUnlinkIfPresent]
    rw [externalUnlinkAndRecreateLock.public_eq_1]
    let newDescId := s.fs.kernel.openFds.nextDescId
    let newIno := s.fs.nand.nextInode
    let newFd := s.fs.nextFd
    let stCr : PosixFsState :=
      { kernel := { (posixUnlinkIfPresent s.fs lockPath).kernel with
                     openFds := { fdRefs := assocInsert (actorPid, newFd) newDescId s.fs.kernel.openFds.fdRefs
                                  descriptions := assocInsert newDescId
                                                    { inode := newIno, writable := true, stickyFsyncErr := false }
                                                    s.fs.kernel.openFds.descriptions
                                  nextDescId := newDescId + 1 }
                     dirInode := { unsyncedEntries :=
                                     assocInsert lockPath (.regular newIno)
                                       (posixUnlinkIfPresent s.fs lockPath).kernel.dirInode.unsyncedEntries } }
        driveCache := s.fs.driveCache
        nand := { s.fs.nand with
                   fileBlocks := assocInsert newIno [] s.fs.nand.fileBlocks
                   nextInode := newIno + 1 }
        nextFd := newFd + 1 }
    have hCr : posixCreateExclNoFollow (posixUnlinkIfPresent s.fs lockPath) actorPid lockPath =
        .ok (stCr, newFd, newIno) := by
      rw [posixCreateExclNoFollow.public_eq_1]; rw [hUnlNone]; rfl
    rw [hCr]
    dsimp only
    have hWr :
        (posixPwriteAll stCr actorPid newFd spoofBytes).toOption.getD stCr =
          { stCr with
             kernel := { stCr.kernel with
                          pageCache := { dirtyFiles := assocInsert newIno spoofBytes s.fs.kernel.pageCache.dirtyFiles } } } := by
      rw [posixPwriteAll.public_eq_1]
      simp only [stCr, resolveOpenFd_insert_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rfl
    let stWr := (posixPwriteAll stCr actorPid newFd spoofBytes).toOption.getD stCr
    have hSy :
        (posixSyncAllMedia stWr actorPid newFd false).1 =
          { stWr with
              kernel := { stWr.kernel with
                            pageCache := { dirtyFiles := assocErase newIno stWr.kernel.pageCache.dirtyFiles } }
              driveCache := { stWr.driveCache with
                               cachedFiles := assocErase newIno stWr.driveCache.cachedFiles }
              nand := { stWr.nand with
                         fileBlocks := assocInsert newIno spoofBytes
                                         stWr.nand.fileBlocks } } := by
      change (posixSyncAllMedia stWr actorPid newFd false).1 = _
      dsimp only [stWr]
      rw [hWr]
      rw [posixSyncAllMedia.public_eq_1]
      unfold readInodeHierarchy
      unfold pendingVolatileWrite
      simp [stCr, resolveOpenFd_insert_self]
    let stSy := (posixSyncAllMedia stWr actorPid newFd false).1
    let stDir := (posixSyncParentDir stSy false).1
    have hc := posixCloseFd_preserves_storage stDir actorPid newFd
    have hFrameSpoof : ∀ ino < s.fs.nand.nextInode,
        assocLookup stDir.kernel.pageCache.dirtyFiles ino = assocLookup s.fs.kernel.pageCache.dirtyFiles ino ∧
        assocLookup stDir.driveCache.cachedFiles ino = assocLookup s.fs.driveCache.cachedFiles ino ∧
        assocLookup stDir.nand.fileBlocks ino = assocLookup s.fs.nand.fileBlocks ino := by
      intro ino hLt
      have hNe : ino ≠ newIno := Nat.ne_of_lt hLt
      simp only [stDir, stSy, posixSyncParentDir.public_eqs, Bool.false_eq_true, ↓reduceIte]
      rw [hSy]
      dsimp only [stWr]
      rw [hWr]
      simp [stCr, hNe]
    have hNextLe : s.fs.nand.nextInode ≤ stDir.nand.nextInode := by
      simp only [stDir, stSy, posixSyncParentDir.public_eqs, Bool.false_eq_true, ↓reduceIte]
      rw [hSy]; dsimp only [stWr]; rw [hWr]; exact Nat.le_succ _
    have hBaseEntryEq :
        assocLookup stDir.kernel.dirInode.unsyncedEntries s.basePath =
          assocLookup s.fs.kernel.dirInode.unsyncedEntries s.basePath := by
      simp only [stDir, stSy, posixSyncParentDir.public_eqs, Bool.false_eq_true, ↓reduceIte]
      rw [hSy]; dsimp only [stWr]; rw [hWr]
      simp [stCr, posixUnlinkIfPresent, hBaseNeLock]
    have hDirBaseEq :
        assocLookup stDir.nand.dirNandEntries s.basePath =
          assocLookup s.fs.kernel.dirInode.unsyncedEntries s.basePath := by
      simp only [stDir, posixSyncParentDir.public_eqs, Bool.false_eq_true, ↓reduceIte]
      exact hBaseEntryEq
    have hTargetSafe : EntryWatermarkSafe stDir s.vaultKeyId macFn macKey s.ghostWatermark
        (assocLookup s.fs.kernel.dirInode.unsyncedEntries s.basePath) :=
      entryWatermarkSafe_frame hNextLe hFrameSpoof hMemSafe
    let stFin := (posixCloseFd stDir actorPid newFd).toOption.getD stDir
    have hFrameFin : ∀ ino < stDir.nand.nextInode,
        assocLookup stFin.kernel.pageCache.dirtyFiles ino = assocLookup stDir.kernel.pageCache.dirtyFiles ino ∧
        assocLookup stFin.driveCache.cachedFiles ino = assocLookup stDir.driveCache.cachedFiles ino ∧
        assocLookup stFin.nand.fileBlocks ino = assocLookup stDir.nand.fileBlocks ino := by
      intro ino _; dsimp only [stFin]; rw [hc.2.1, hc.2.2.1, hc.2.2.2]; exact ⟨rfl, rfl, rfl⟩
    have hFinSafe : EntryWatermarkSafe stFin s.vaultKeyId macFn macKey s.ghostWatermark
        (assocLookup s.fs.kernel.dirInode.unsyncedEntries s.basePath) :=
      entryWatermarkSafe_frame (by dsimp only [stFin]; rw [hc.2.2.2]; exact Nat.le_refl _)
        hFrameFin hTargetSafe
    refine ⟨⟨hVk32, hNodup, hRcpts, hHold, ?_, ?_, ?_⟩,
      Nat.le_refl _, ⟨[], by simp, fun _ _ hH => ⟨hH, by simp⟩⟩⟩
    · change stFin.driveCache.cachedDirEntries = none
      dsimp only [stFin]; rw [hc.2.2.1]; rfl
    · change EntryWatermarkSafe stFin s.vaultKeyId macFn macKey s.ghostWatermark
        (assocLookup stFin.kernel.dirInode.unsyncedEntries s.basePath)
      dsimp only [stFin]; rw [hc.1, hBaseEntryEq]; exact hFinSafe
    · change EntryWatermarkSafe stFin s.vaultKeyId macFn macKey s.ghostWatermark
        (assocLookup stFin.nand.dirNandEntries s.basePath)
      dsimp only [stFin]; rw [hc.2.2.2, hDirBaseEq]; exact hFinSafe
  | attemptReprovisionGenesis actorPid newNonce =>
    unfold stepMultiCrashCustody
    rcases hInv with ⟨hVk32, hNodup, hRcpts, hHold, hDrvDir, hMemSafe, hNandSafe⟩
    dsimp only
    have hOut := provisionGenesis_noFault_outcome s.fs actorPid s.basePath
      s.vaultKeyId newNonce [] macFn []
    cases hGen : provisionGenesis s.fs actorPid s.basePath s.vaultKeyId newNonce [] macFn [] {} with
    | mk fs' res' =>
      rw [hGen] at hOut
      dsimp only at hOut ⊢
      rcases hOut with hAbort | hRogueOk
      · rcases hAbort with ⟨hDrvEq, hMemEq, hNandEq, hNextLe, hFrame⟩
        refine ⟨⟨hVk32, hNodup, hRcpts, hHold, ?_, ?_, ?_⟩,
          Nat.le_refl _, ⟨[], by simp, fun _ _ hH => ⟨hH, by simp⟩⟩⟩
        · dsimp only; rw [hDrvEq]; exact hDrvDir
        · dsimp only; rw [hMemEq]; exact entryWatermarkSafe_frame hNextLe hFrame hMemSafe
        · dsimp only; rw [hNandEq]; exact entryWatermarkSafe_frame hNextLe hFrame hNandSafe
      · rcases hRogueOk with ⟨_, hNonce32, _, _, hDrvNone, hMemReg, hNandReg, hInoLt, hPg, hDr, hBs⟩
        let rogueBody : WalRecordBody :=
          { vaultKeyId := s.vaultKeyId
            lockGenesisId := computeLockGenesisId s.fs.nand.nextInode newNonce
            epoch := 0
            payload := [] }
        let rogueRec := signWalRecord macFn [] rogueBody
        have hRogueWf : rogueRec.WellFormed :=
          signWalRecord_wellFormed hMacWf []
            ⟨hVk32, computeLockGenesisId_length hNonce32,
             Nat.pow_pos (by decide : 0 < 2), Nat.pow_pos (by decide : 0 < 2)⟩
        have hRogueSafe : EntryWatermarkSafe fs' s.vaultKeyId macFn macKey s.ghostWatermark
            (some (.regular (s.fs.nand.nextInode + 1))) := by
          refine ⟨hInoLt, hPg, hDr, encodeWalRecord rogueRec, hBs, ?_⟩
          intro rec hDec _ hVerTrue
          rw [decodeWalRecord_encodeWalRecord hRogueWf] at hDec
          injection hDec with hRecEq
          rw [← hRecEq] at hVerTrue
          have hRej := hRogueReject rogueBody rfl rfl
          rw [hRej] at hVerTrue
          cases hVerTrue
        refine ⟨⟨hVk32, hNodup, hRcpts, hHold, hDrvNone, ?_, ?_⟩,
          Nat.le_refl _, ⟨[], by simp, fun _ _ hH => ⟨hH, by simp⟩⟩⟩
        · dsimp only; rw [hMemReg]; exact hRogueSafe
        · dsimp only; rw [hNandReg]; exact hRogueSafe
  | deleteWalRecord =>
    unfold stepMultiCrashCustody
    rcases hInv with ⟨hVk32, hNodup, hRcpts, hHold, hDrvDir, hMemSafe, hNandSafe⟩
    dsimp only
    rw [posixUnlink.public_eq_1]
    cases assocLookup s.fs.kernel.dirInode.unsyncedEntries s.basePath with
    | none =>
      simp only [Except.toOption, Option.getD_none]
      exact ⟨⟨hVk32, hNodup, hRcpts, hHold, hDrvDir, hMemSafe, hNandSafe⟩,
        Nat.le_refl _, ⟨[], by simp, fun _ _ hH => ⟨hH, by simp⟩⟩⟩
    | some _ =>
      simp only [Except.toOption, Option.getD_some]
      refine ⟨⟨hVk32, hNodup, hRcpts, hHold, hDrvDir, ?_, hNandSafe⟩,
        Nat.le_refl _, ⟨[], by simp, fun _ _ hH => ⟨hH, by simp⟩⟩⟩
      dsimp only
      simp only [assocLookup_erase, ↓reduceIte]
      trivial
  | plantSymlink entryName targetName =>
    unfold stepMultiCrashCustody
    rcases hInv with ⟨hVk32, hNodup, hRcpts, hHold, hDrvDir, hMemSafe, hNandSafe⟩
    dsimp only
    rw [posixCreateSymlink.public_eq_1]
    cases assocLookup s.fs.kernel.dirInode.unsyncedEntries entryName with
    | some _ =>
      simp only [Except.toOption, Option.getD_none]
      exact ⟨⟨hVk32, hNodup, hRcpts, hHold, hDrvDir, hMemSafe, hNandSafe⟩,
        Nat.le_refl _, ⟨[], by simp, fun _ _ hH => ⟨hH, by simp⟩⟩⟩
    | none =>
      simp only [Except.toOption, Option.getD_some]
      refine ⟨⟨hVk32, hNodup, hRcpts, hHold, hDrvDir, ?_, hNandSafe⟩,
        Nat.le_refl _, ⟨[], by simp, fun _ _ hH => ⟨hH, by simp⟩⟩⟩
      dsimp only
      by_cases hEq : s.basePath = entryName
      · simp only [assocLookup_insert, hEq, ↓reduceIte]
        trivial
      · simp only [assocLookup_insert, hEq, ↓reduceIte]
        exact hMemSafe

/-- Multi-step inductive trace invariance across arbitrary `List MultiCrashWalEvent` sequences. -/
theorem runMultiCrashCustodyTrace_preserves_inv
    {macFn : KeyedMacFn} (hMacWf : WellFormedMacFn macFn) {macKey : List UInt8}
    (hRogueReject : ∀ b : WalRecordBody, b.epoch = 0 → b.payload = [] →
      verifyWalMac macFn macKey (signWalRecord macFn [] b) = false)
    {s : MultiCrashCustodyState} (trace : List MultiCrashWalEvent)
    (hInv : CustodyMultiCrashInv macFn macKey s) :
    let sFinal := runMultiCrashCustodyTrace macFn macKey s trace
    CustodyMultiCrashInv macFn macKey sFinal ∧
    s.ghostWatermark ≤ sFinal.ghostWatermark ∧
    (∃ newRs, sFinal.emittedReceipts = s.emittedReceipts ++ newRs ∧
      (∀ w₀ : Nat,
        w₀ ≤ s.ghostWatermark →
        (match s.activeHold with | none => True | some (_, resEp, _) => w₀ ≤ resEp) →
        (match sFinal.activeHold with | none => True | some (_, resEp, _) => w₀ ≤ resEp) ∧
        ∀ r ∈ newRs, w₀ ≤ r.epoch)) := by
  induction trace generalizing s with
  | nil =>
    dsimp +zetaDelta only [runMultiCrashCustodyTrace]
    exact ⟨hInv, Nat.le_refl _, ⟨[], by simp, fun _ _ hH => ⟨hH, by simp⟩⟩⟩
  | cons ev rest ih =>
    dsimp +zetaDelta only [runMultiCrashCustodyTrace]
    have hStep := stepMultiCrashCustody_preserves_inv hMacWf hRogueReject ev hInv
    cases hSt : stepMultiCrashCustody macFn macKey s ev with
    | mk s1 out1 =>
      rw [hSt] at hStep
      dsimp +zetaDelta only at hStep ⊢
      rcases hStep with ⟨hInv1, hWm1, ⟨rs1, hEq1, hBound1⟩⟩
      have hRest := ih hInv1
      dsimp +zetaDelta only at hRest
      rcases hRest with ⟨hInvF, hWmF, ⟨rs2, hEq2, hBound2⟩⟩
      refine ⟨hInvF, Nat.le_trans hWm1 hWmF, ⟨rs1 ++ rs2, ?_, ?_⟩⟩
      · rw [hEq2, hEq1, List.append_assoc]
      · intro w₀ hw₀ hH0
        obtain ⟨hH1, hB1⟩ := hBound1 w₀ hw₀ hH0
        obtain ⟨hHF, hB2⟩ := hBound2 w₀ (Nat.le_trans hw₀ hWm1) hH1
        refine ⟨hHF, ?_⟩
        intro r hr
        rcases List.mem_append.mp hr with hr1 | hr2
        · exact hB1 r hr1
        · exact hB2 r hr2

theorem runMultiCrashCustodyTrace_append (macFn : KeyedMacFn) (macKey : List UInt8)
    (s : MultiCrashCustodyState) (t₁ t₂ : List MultiCrashWalEvent) :
    runMultiCrashCustodyTrace macFn macKey s (t₁ ++ t₂) =
      runMultiCrashCustodyTrace macFn macKey (runMultiCrashCustodyTrace macFn macKey s t₁) t₂ := by
  induction t₁ generalizing s with
  | nil => rfl
  | cons ev rest ih =>
    simp only [List.cons_append, runMultiCrashCustodyTrace]
    exact ih (stepMultiCrashCustody macFn macKey s ev).1

/-- **FLAGSHIP THEOREM 3 (`reserve_before_sign_multi_crash_epoch_uniqueness`)**:
    For **every** stateful signing key family (`StatefulKeyKind`: `.beltLatch`, `.frontier`,
    `.policyGuard`) provisioned via `initProvisionedCustodyState`, across **arbitrary** multi-turn
    event traces `prefixTrace ++ suffixTrace` interleaving atomic signing, split-phase lock holds,
    concurrent contenders, crashes at every syscall boundary INSIDE a reservation
    (`midReserveCrash`, either crash kind), `KernelPanicCrash`, `PowerLossCrash` with `512B`/`4KiB` `SectorTearMask`s,
    `.lock` `unlink` + spoofed recreation, rogue genesis re-provisioning, symlink attacks, and
    WAL deletion attempts:
    1. **Strict Global Epoch Uniqueness**: `(sFinal.emittedReceipts.map (·.epoch)).Nodup` — no epoch
       is ever emitted twice,
    2. **Zero Same-Epoch Message Collisions**: any `r₁, r₂ ∈ sFinal.emittedReceipts` sharing
       `r₁.epoch = r₂.epoch` satisfy `r₁ = r₂` and `r₁.msg = r₂.msg`,
    3. **Strict Post-Prefix Monotonicity**: `sFinal.emittedReceipts = sMid.emittedReceipts ++ newRs`,
       and whenever `sMid.activeHold = none`, every receipt `r ∈ newRs` emitted during `suffixTrace`
       satisfies `sMid.ghostWatermark ≤ r.epoch`,
    4. **Zero Epoch-`0` Amnesia / Reset**: once epoch `0` has been emitted (`∃ r₀ ∈ sMid.emittedReceipts, r₀.epoch = 0`),
       no subsequent suffix event ever emits epoch `0` (`∀ r ∈ newRs, r.epoch ≠ 0`); likewise once
       `1 ≤ sMid.ghostWatermark` and `sMid.activeHold = none`, every `r ∈ newRs` satisfies `0 < r.epoch`! -/
theorem reserve_before_sign_multi_crash_epoch_uniqueness
    {pid : Pid} {basePath : DirName} {keyKind : StatefulKeyKind}
    {vaultKeyId genesisNonce : List UInt8} {maxEpochCap : Nat}
    {macFn : KeyedMacFn} (hMacWf : WellFormedMacFn macFn) {macKey : List UInt8}
    (hRogueReject : ∀ b : WalRecordBody, b.epoch = 0 → b.payload = [] →
      verifyWalMac macFn macKey (signWalRecord macFn [] b) = false)
    {s₀ : MultiCrashCustodyState}
    (hInit : initProvisionedCustodyState pid basePath keyKind vaultKeyId genesisNonce
               maxEpochCap macFn macKey = some s₀)
    (prefixTrace suffixTrace : List MultiCrashWalEvent) :
    let sMid := runMultiCrashCustodyTrace macFn macKey s₀ prefixTrace
    let sFinal := runMultiCrashCustodyTrace macFn macKey s₀ (prefixTrace ++ suffixTrace)
    (sFinal.emittedReceipts.map (·.epoch)).Nodup ∧
    (∀ r₁ ∈ sFinal.emittedReceipts, ∀ r₂ ∈ sFinal.emittedReceipts,
      r₁.epoch = r₂.epoch → r₁ = r₂ ∧ r₁.msg = r₂.msg) ∧
    sMid.ghostWatermark ≤ sFinal.ghostWatermark ∧
    ∃ newRs : List SignedEpochReceipt,
      sFinal.emittedReceipts = sMid.emittedReceipts ++ newRs ∧
      (sMid.activeHold = none → ∀ r ∈ newRs, sMid.ghostWatermark ≤ r.epoch) ∧
      ((∃ r₀ ∈ sMid.emittedReceipts, r₀.epoch = 0) → ∀ r ∈ newRs, r.epoch ≠ 0) ∧
      (1 ≤ sMid.ghostWatermark → sMid.activeHold = none → ∀ r ∈ newRs, 0 < r.epoch) := by
  dsimp +zetaDelta only
  rw [runMultiCrashCustodyTrace_append]
  obtain ⟨hInv0, _, _, _⟩ := initProvisionedCustodyState_inv hInit
  obtain ⟨hInvMid, _, _⟩ := runMultiCrashCustodyTrace_preserves_inv hMacWf hRogueReject prefixTrace hInv0
  let sMid := runMultiCrashCustodyTrace macFn macKey s₀ prefixTrace
  obtain ⟨hInvFin, hWmLe, ⟨newRs, hAppEq, hWmBound⟩⟩ :=
    runMultiCrashCustodyTrace_preserves_inv hMacWf hRogueReject suffixTrace hInvMid
  let sFinal := runMultiCrashCustodyTrace macFn macKey sMid suffixTrace
  have hNodupFin : (sFinal.emittedReceipts.map (·.epoch)).Nodup := hInvFin.2.1
  refine ⟨hNodupFin, ?_, hWmLe, ⟨newRs, hAppEq, ?_, ?_, ?_⟩⟩
  · intro r₁ hr₁ r₂ hr₂ hEpEq
    have hEq := eq_of_mem_of_map_nodup hNodupFin hr₁ hr₂ hEpEq
    exact ⟨hEq, congrArg SignedEpochReceipt.msg hEq⟩
  · intro hHoldNone r hr
    have hB := hWmBound sMid.ghostWatermark (Nat.le_refl _)
      (by dsimp only [sMid] at *; rw [hHoldNone]; trivial)
    exact hB.2 r hr
  · intro hHasZero r hr hEqZero
    rcases hHasZero with ⟨r₀, hr₀, hEp0⟩
    have hNodupApp : ((sMid.emittedReceipts ++ newRs).map (·.epoch)).Nodup := by
      rw [← hAppEq]; exact hNodupFin
    have hDisjoint : ∀ (xs ys : List Nat),
        (xs ++ ys).Nodup → ∀ a ∈ xs, ∀ b ∈ ys, a ≠ b := by
      intro xs ys hNd
      induction xs with
      | nil => intro a ha; cases ha
      | cons x rest ih =>
        rw [List.cons_append, List.Nodup, List.pairwise_cons] at hNd
        intro a ha b hb
        simp only [List.mem_cons] at ha
        rcases ha with rfl | haRest
        · exact hNd.1 b (List.mem_append.mpr (Or.inr hb))
        · exact ih hNd.2 a haRest b hb
    rw [List.map_append] at hNodupApp
    have hNe := hDisjoint _ _ hNodupApp r₀.epoch (List.mem_map_of_mem hr₀)
      r.epoch (List.mem_map_of_mem hr)
    rw [hEp0, hEqZero] at hNe
    exact hNe rfl
  · intro hGe1 hHoldNone r hr
    have hB := hWmBound sMid.ghostWatermark (Nat.le_refl _)
      (by dsimp only [sMid] at *; rw [hHoldNone]; trivial)
    exact Nat.lt_of_lt_of_le hGe1 (hB.2 r hr)

/-- **Environment Anti-Narrowing Completeness (`honest_sign_complete_when_healthy`)**:
    Whenever the vault is durable & uncontended (`openFds = {}`, `flockTable = {}`, `VaultDurableAt`),
    `rec.body.epoch < maxEpochCap`, and `rec.body.epoch + 1 < 2^64`, `execReserveBeforeSignAtomic`
    with `faults = {}` **succeeds** and emits `some receipt` at `rec.body.epoch`! -/
theorem honest_sign_complete_when_healthy
    {st : PosixFsState} {basePath : DirName} {lockIno : InodeId} {genesisNonce : List UInt8}
    {macFn : KeyedMacFn} {macKey : List UInt8}
    {rec : WalRecord} (pid : Pid) (keyKind : StatefulKeyKind) (maxEpochCap : Nat) (msg : List UInt8)
    (hFdsEmpty : st.kernel.openFds = {})
    (hFlkEmpty : st.kernel.flockTable = {})
    (hDur : VaultDurableAt st basePath lockIno genesisNonce macFn macKey rec)
    (hLtCap : rec.body.epoch < maxEpochCap)
    (hLt64 : rec.body.epoch + 1 < 2 ^ 64) :
    ∃ st',
      execReserveBeforeSignAtomic st pid basePath keyKind rec.body.vaultKeyId maxEpochCap msg
        macFn macKey {} =
      (st', some { keyKind := keyKind
                   vaultKeyId := rec.body.vaultKeyId
                   epoch := rec.body.epoch
                   msg := msg }) := by
  rcases hDur with ⟨_, hLock64, hNonceLen, hRecWf, hRecGid, hRecVer,
    _, hLockUnsync, _, hLockPg, hLockDrv, hLockNand,
    recIno, _, hRecUnsync, _, hRecPg, hRecDrv, hRecNand⟩
  have hSealDec :
      decodeLockSidecar (encodeLockSidecar { sealedLockInode := lockIno, genesisNonce := genesisNonce }) =
        some { sealedLockInode := lockIno, genesisNonce := genesisNonce } :=
    decodeLockSidecar_encodeLockSidecar ⟨hLock64, hNonceLen⟩
  have hRecDec : decodeWalRecord (encodeWalRecord rec) = some rec :=
    decodeWalRecord_encodeWalRecord hRecWf
  let st1 : PosixFsState :=
    { st with
        kernel := { st.kernel with
                      openFds := { fdRefs := [((pid, st.nextFd), 1)]
                                   descriptions := [(1, { inode := lockIno, writable := true, stickyFsyncErr := false })]
                                   nextDescId := 2 } }
        nextFd := st.nextFd + 1 }
  have hOp1 : posixOpenExistingNoFollow st pid (walLockPath basePath) true = .ok (st1, st.nextFd) := by
    rw [posixOpenExistingNoFollow.public_eq_1]
    rw [resolveDentryNoFollow.public_eq_1]
    rw [hLockUnsync, hFdsEmpty]
    rfl
  let st2 : PosixFsState :=
    { st1 with kernel := { st1.kernel with flockTable := { locks := [(lockIno, 1)] } } }
  have hFlk : posixFlockExNb st1 pid st.nextFd = .ok st2 := by
    rw [posixFlockExNb.public_eq_1]
    unfold resolveOpenFd
    unfold FlockTable.owner
    dsimp only [st1]
    rw [hFlkEmpty]
    simp [assocInsert.public_eqs, st2, st1]
  have hFst : posixFstatDescAndInode st2 pid st.nextFd = .ok (1, lockIno) := by
    simp [posixFstatDescAndInode.public_eqs, resolveOpenFd, st2, st1]
  have hPread1 :
      posixPreadAll st2 pid st.nextFd =
        .ok (encodeLockSidecar { sealedLockInode := lockIno, genesisNonce := genesisNonce }) := by
    rw [posixPreadAll.public_eq_1]
    unfold resolveOpenFd
    unfold readInodeHierarchy
    unfold pendingVolatileWrite
    simp [st2, st1, hLockPg, hLockDrv, hLockNand]
  let st3 : PosixFsState :=
    { st2 with
        kernel := { st2.kernel with
                      openFds := { fdRefs := assocInsert (pid, st.nextFd + 1) 2 st2.kernel.openFds.fdRefs
                                   descriptions := assocInsert 2 { inode := recIno, writable := false, stickyFsyncErr := false }
                                                     st2.kernel.openFds.descriptions
                                   nextDescId := 3 } }
        nextFd := st.nextFd + 2 }
  have hOp2 : posixOpenExistingNoFollow st2 pid basePath false = .ok (st3, st.nextFd + 1) := by
    rw [posixOpenExistingNoFollow.public_eq_1]
    rw [resolveDentryNoFollow.public_eq_1]
    dsimp only [st2, st1]
    rw [hRecUnsync]
  have hPread2 : posixPreadAll st3 pid (st.nextFd + 1) = .ok (encodeWalRecord rec) := by
    have hRes3 : resolveOpenFd st3.kernel.openFds pid (st.nextFd + 1) =
        some (2, { inode := recIno, writable := false, stickyFsyncErr := false }) := by
      dsimp +zetaDelta only [st3]
      exact resolveOpenFd_insert_self st2.kernel.openFds pid (st.nextFd + 1) 2 _
    rw [posixPreadAll.public_eq_1]
    rw [hRes3]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold readInodeHierarchy pendingVolatileWrite
    dsimp +zetaDelta only [st3, st2, st1]
    rw [hRecPg, hRecDrv, hRecNand]
  let st4 : PosixFsState :=
    { st3 with
        kernel := { st3.kernel with
                      openFds := { fdRefs := [((pid, st.nextFd), 1)]
                                   descriptions := [(1, { inode := lockIno, writable := true, stickyFsyncErr := false })]
                                   nextDescId := 3 }
                      flockTable := { locks := [(lockIno, 1)] } } }
  have hCloseRec : (posixCloseFd st3 pid (st.nextFd + 1)).toOption.getD st3 = st4 := by
    rw [posixCloseFd.public_eq_1]
    dsimp only [st3, st2, st1]
    have hEraseFd :
        assocErase (pid, st.nextFd + 1)
          (assocInsert (pid, st.nextFd + 1) 2 [((pid, st.nextFd), 1)]) =
          [((pid, st.nextFd), 1)] := by
      have hFdNe : (pid, st.nextFd + 1) ≠ (pid, st.nextFd) :=
        fun hc => Nat.ne_of_gt (Nat.lt_succ_self st.nextFd) (Prod.mk.inj hc).2
      simp only [assocInsert.public_eqs, assocErase.public_eqs, ↓reduceIte, hFdNe]
    rw [assocLookup_insert_self, hEraseFd]
    dsimp only
    have hNoRef2 : descHasAnyRef [((pid, st.nextFd), 1)] 2 = false := by simp [descHasAnyRef.public_eqs]
    rw [hNoRef2]
    simp only [Bool.false_eq_true, ↓reduceIte, assocLookup_insert_self]
    have hLockNot2 : (assocLookup [(lockIno, (1 : OpenDescriptionId))] recIno == some 2) = false := by
      by_cases hSame : recIno = lockIno <;> simp [assocLookup, hSame]
    rw [hLockNot2]
    have hEraseDesc2 :
        assocErase (2 : OpenDescriptionId)
          (assocInsert (2 : OpenDescriptionId)
            ({ inode := recIno, writable := false, stickyFsyncErr := false } : OpenFileDesc)
            [(1, { inode := lockIno, writable := true, stickyFsyncErr := false })]) =
          [(1, { inode := lockIno, writable := true, stickyFsyncErr := false })] := by
      have h2Ne1 : (2 : OpenDescriptionId) ≠ 1 := by decide
      simp only [assocInsert.public_eqs, assocErase.public_eqs, ↓reduceIte, h2Ne1]
    simp only [Bool.false_eq_true, ↓reduceIte, hEraseDesc2, Except.toOption, Option.getD]
    rfl
  have hOpenOk :
      openExisting st pid basePath rec.body.vaultKeyId macFn macKey =
        (st4, .ok ({ pid := pid
                     basePath := basePath
                     lockFd := st.nextFd
                     lockDescId := 1
                     lockInode := lockIno
                     lockGenesisId := computeLockGenesisId lockIno genesisNonce
                     vaultKeyId := rec.body.vaultKeyId
                     ioPoisoned := false }, rec)) := by
    rw [openExisting.public_eq_1]
    rw [hOp1]; dsimp +zetaDelta only
    rw [hFlk]; dsimp +zetaDelta only
    rw [hFst, hPread1]; dsimp +zetaDelta only
    rw [hSealDec]; dsimp +zetaDelta only
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [hOp2]; dsimp +zetaDelta only
    rw [hPread2]; dsimp +zetaDelta only
    rw [hCloseRec]; dsimp +zetaDelta only
    rw [hRecDec]; dsimp +zetaDelta only
    have hGidFalse : (rec.body.lockGenesisId != computeLockGenesisId lockIno genesisNonce) = false := by
      rw [hRecGid]; exact bne_self_eq_false _
    rw [hGidFalse, bne_self_eq_false, hRecVer]
    simp
  unfold execReserveBeforeSignAtomic
  rw [hOpenOk]
  dsimp +zetaDelta only
  have hCapFalse :
      (!(decide (rec.body.epoch < maxEpochCap)) || !(decide (rec.body.epoch + 1 < 2 ^ 64))) = false := by
    simp [hLtCap, hLt64]
  rw [hCapFalse]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hPayLt32 : (encodeCustodyWalPayload keyKind maxEpochCap msg).length < 2 ^ 32 :=
    encodeCustodyWalPayload_lt_two_pow_32 keyKind maxEpochCap msg
  rw [replaceAtomic.public_eq_1]
  dsimp +zetaDelta only
  have hRepBndFalse :
      (!(decide (rec.body.epoch + 1 < 2 ^ 64)) ||
       !(decide ((encodeCustodyWalPayload keyKind maxEpochCap msg).length < 2 ^ 32))) = false := by
    simp [hLt64, hPayLt32]
  rw [hRepBndFalse]
  have hResSt4 :
      resolveOpenFd st4.kernel.openFds pid st.nextFd =
        some (1, { inode := lockIno, writable := true, stickyFsyncErr := false }) := by
    simp [resolveOpenFd, st4]
  have hFlkSt4 : st4.kernel.flockTable.owner lockIno = some 1 := by
    simp [FlockTable.owner, st4]
  rw [hResSt4, hFlkSt4]
  simp only [Bool.false_eq_true, ↓reduceIte, bne_self_eq_false, Bool.or_self]
  rw [posixCreateExclNoFollow.public_eq_1]
  have hTmpCleared :
      assocLookup (posixUnlinkIfPresent st4 (walTmpPath basePath)).kernel.dirInode.unsyncedEntries
        (walTmpPath basePath) = none := by
    simp [posixUnlinkIfPresent]
  rw [hTmpCleared]
  dsimp +zetaDelta only
  rw [posixPwriteAll.public_eq_1]
  simp only [resolveOpenFd_insert_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [posixSyncAllMedia.public_eq_1]
  unfold readInodeHierarchy
  unfold pendingVolatileWrite
  simp only [resolveOpenFd_insert_self, Bool.false_eq_true, ↓reduceIte, assocLookup_insert_self]
  rw [posixRename.public_eq_1]
  have hTmpAfterClose :
      ∀ (sX : PosixFsState) (pX : Pid) (fX : FdId),
        ((posixCloseFd sX pX fX).toOption.getD sX).kernel.dirInode = sX.kernel.dirInode :=
    fun sX pX fX => (posixCloseFd_preserves_storage sX pX fX).1
  rw [hTmpAfterClose]
  simp only [assocLookup_insert_self]
  rw [posixSyncParentDir.public_eq_1]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, rfl⟩

#export_eqns EntryWatermarkSafe

#export_eqns stepMultiCrashCustody runMultiCrashCustodyTrace

end Qsag
end
