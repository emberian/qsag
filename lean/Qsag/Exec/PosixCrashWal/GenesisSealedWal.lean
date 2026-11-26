module

public import Qsag.Exec.PosixCrashWal.StorageMachine
import Qsag.Tactic.AssuranceKit

public section

namespace Qsag

set_option autoImplicit false

/-- Active locked vault handle held by a process after `openExisting` succeeds, bound to the
    exact kernel `OpenDescriptionId` (`lockDescId`) owning the advisory `flock`! -/
structure LockedVaultHandle where
  pid           : Pid
  basePath      : DirName
  lockFd        : FdId
  lockDescId    : OpenDescriptionId
  lockInode     : InodeId
  lockGenesisId : List UInt8
  vaultKeyId    : List UInt8
  ioPoisoned    : Bool := false
  deriving Repr, DecidableEq

/-- Fault-injection flags for testing `EIO` handling at every physical sync barrier. -/
structure IoFaultSchedule where
  failLockSync   : Bool := false
  failRecordSync : Bool := false
  failParentSync : Bool := false
  deriving Repr, DecidableEq

/-- **Hardened `provisionGenesis` Protocol**:
    1. Checks **neither** `basePath` nor `walLockPath basePath` exists *before* creating anything,
    2. Creates `.lock` (`O_CREAT | O_EXCL | O_NOFOLLOW`), locks its `InodeId`, writes the
       `LockSidecarSeal` binding `(lockIno, genesisNonce)` + `posixSyncAllMedia`,
    3. Creates `basePath` (`O_CREAT | O_EXCL | O_NOFOLLOW`), writes the epoch-`0` MAC-authenticated
       `WalRecord` `(vaultKeyId, lockGenesisId, epoch := 0, initPayload, keyedMac)` +
       `posixSyncAllMedia` + `posixSyncParentDir`, and closes provisioning descriptors. -/
def provisionGenesis (st : PosixFsState) (pid : Pid) (basePath : DirName)
    (vaultKeyId genesisNonce initPayload : List UInt8)
    (macFn : KeyedMacFn) (macKey : List UInt8)
    (faults : IoFaultSchedule := {}) :
    PosixFsState × Except PosixErr (InodeId × WalRecord) :=
  if vaultKeyId.length != 32 || genesisNonce.length != 32 || !(decide (initPayload.length < 2 ^ 32)) then
    (st, .error .einval)
  else
    -- Pre-flight check: NEITHER `basePath` NOR `walLockPath basePath` may exist prior to genesis!
    match assocLookup st.kernel.dirInode.unsyncedEntries basePath,
          assocLookup st.kernel.dirInode.unsyncedEntries (walLockPath basePath) with
    | some _, _ => (st, .error .eexist)
    | _, some _ => (st, .error .eexist)
    | none, none =>
      match posixCreateExclNoFollow st pid (walLockPath basePath) with
      | .error e => (st, .error e)
      | .ok (st1, lockFd, lockIno) =>
        match posixFlockExNb st1 pid lockFd with
        | .error e => (st1, .error e)
        | .ok st2 =>
          match posixPwriteAll st2 pid lockFd
                  (encodeLockSidecar { sealedLockInode := lockIno, genesisNonce := genesisNonce }) with
          | .error e => (st2, .error e)
          | .ok st3 =>
            match posixSyncAllMedia st3 pid lockFd faults.failLockSync with
            | (st4, .error e) => (st4, .error e)
            | (st4, .ok ()) =>
              match posixCreateExclNoFollow st4 pid basePath with
              | .error e => (st4, .error e)
              | .ok (st5, recFd, _) =>
                match posixPwriteAll st5 pid recFd
                        (encodeWalRecord (signWalRecord macFn macKey
                          { vaultKeyId := vaultKeyId
                            lockGenesisId := computeLockGenesisId lockIno genesisNonce
                            epoch := 0
                            payload := initPayload })) with
                | .error e => (st5, .error e)
                | .ok st6 =>
                  match posixSyncAllMedia st6 pid recFd faults.failRecordSync with
                  | (st7, .error e) => (st7, .error e)
                  | (st7, .ok ()) =>
                    match posixSyncParentDir st7 faults.failParentSync with
                    | (st8, .error e) => (st8, .error e)
                    | (st8, .ok ()) =>
                      let st9 := (posixCloseFd st8 pid recFd).toOption.getD st8
                      let st10 := (posixCloseFd st9 pid lockFd).toOption.getD st9
                      (st10, .ok (lockIno, signWalRecord macFn macKey
                        { vaultKeyId := vaultKeyId
                          lockGenesisId := computeLockGenesisId lockIno genesisNonce
                          epoch := 0
                          payload := initPayload }))

/-- **Hardened `openExisting` Protocol**:
    1. Opens `.lock` with `O_NOFOLLOW` (**never** `O_CREAT`),
    2. Acquires non-blocking `flock(LOCK_EX | LOCK_NB)` on `.lock`'s kernel `InodeId`,
    3. Reads `LockSidecarSeal` from the locked fd and checks `actualLockIno == lockSeal.sealedLockInode`,
    4. Opens `basePath` with `O_NOFOLLOW` (**never** `O_CREAT`), decodes `WalRecord`, closes the
       transient record fd, and verifies **both** `rec.body.lockGenesisId == lockedGid` AND
       `verifyWalMac macFn macKey rec == true`! -/
def openExisting (st : PosixFsState) (pid : Pid) (basePath : DirName)
    (expectedVaultKeyId : List UInt8)
    (macFn : KeyedMacFn) (macKey : List UInt8) :
    PosixFsState × Except PosixErr (LockedVaultHandle × WalRecord) :=
  match posixOpenExistingNoFollow st pid (walLockPath basePath) true with
  | .error e => (st, .error e)
  | .ok (st1, lockFd) =>
    match posixFlockExNb st1 pid lockFd with
    | .error e =>
      ((posixCloseFd st1 pid lockFd).toOption.getD st1, .error e)
    | .ok st2 =>
      match posixFstatDescAndInode st2 pid lockFd, posixPreadAll st2 pid lockFd with
      | .ok (lockDescId, actualLockIno), .ok rawLockBytes =>
        match decodeLockSidecar rawLockBytes with
        | none =>
          ((posixCloseFd st2 pid lockFd).toOption.getD st2, .error .elockseal)
        | some lockSeal =>
          if actualLockIno != lockSeal.sealedLockInode then
            ((posixCloseFd st2 pid lockFd).toOption.getD st2, .error .elockseal)
          else
            match posixOpenExistingNoFollow st2 pid basePath false with
            | .error e =>
              ((posixCloseFd st2 pid lockFd).toOption.getD st2, .error e)
            | .ok (st3, recFd) =>
              match posixPreadAll st3 pid recFd with
              | .error e =>
                let st4 := (posixCloseFd st3 pid recFd).toOption.getD st3
                ((posixCloseFd st4 pid lockFd).toOption.getD st4, .error e)
              | .ok rawRecBytes =>
                let st4 := (posixCloseFd st3 pid recFd).toOption.getD st3
                match decodeWalRecord rawRecBytes with
                | none =>
                  ((posixCloseFd st4 pid lockFd).toOption.getD st4, .error .einval)
                | some rec =>
                  if rec.body.lockGenesisId !=
                      computeLockGenesisId actualLockIno lockSeal.genesisNonce then
                    ((posixCloseFd st4 pid lockFd).toOption.getD st4, .error .elockseal)
                  else if rec.body.vaultKeyId != expectedVaultKeyId ||
                          !(verifyWalMac macFn macKey rec) then
                    ((posixCloseFd st4 pid lockFd).toOption.getD st4, .error .emac)
                  else
                    (st4, .ok ({ pid := pid
                                 basePath := basePath
                                 lockFd := lockFd
                                 lockDescId := lockDescId
                                 lockInode := actualLockIno
                                 lockGenesisId := computeLockGenesisId actualLockIno lockSeal.genesisNonce
                                 vaultKeyId := expectedVaultKeyId
                                 ioPoisoned := false }, rec))
      | .error e, _ =>
        ((posixCloseFd st2 pid lockFd).toOption.getD st2, .error e)
      | _, .error e =>
        ((posixCloseFd st2 pid lockFd).toOption.getD st2, .error e)

/-- Release an active `LockedVaultHandle` by closing its locked sidecar descriptor. -/
@[expose] def closeVaultHandle (st : PosixFsState) (h : LockedVaultHandle) : Except PosixErr PosixFsState :=
  posixCloseFd st h.pid h.lockFd

/-- Validate that `h` is currently an active, unpoisoned, `flock`-holding handle in `st`
    whose `OpenDescriptionId` (`h.lockDescId`) has already been allocated (`< nextDescId`). -/
def LockedVaultHandle.IsActiveIn (h : LockedVaultHandle) (st : PosixFsState) : Prop :=
  h.ioPoisoned = false ∧
  h.lockDescId < st.kernel.openFds.nextDescId ∧
  (∃ desc : OpenFileDesc,
    resolveOpenFd st.kernel.openFds h.pid h.lockFd = some (h.lockDescId, desc) ∧
    desc.inode = h.lockInode ∧
    desc.stickyFsyncErr = false) ∧
  st.kernel.flockTable.owner h.lockInode = some h.lockDescId

/-- **Hardened `replaceAtomic` Protocol** (with sticky `ioPoisoned := true` on any I/O failure):
    1. Rejects immediately if `h.ioPoisoned = true` or `h.lockDescId` does not hold `flock` on `h.lockInode`,
    2. Clears any stale `.tmp`, creates a fresh `.tmp` inode (`O_CREAT | O_EXCL | O_NOFOLLOW`),
    3. Writes `encodeWalRecord newRec` to `.tmp`, calls `posixSyncAllMedia(.tmp)`, closes `.tmp`,
    4. Atomically executes `posixRename(.tmp, h.basePath)`, and calls `posixSyncParentDir`! -/
def replaceAtomic (st : PosixFsState) (h : LockedVaultHandle)
    (newEpoch : Nat) (newPayload : List UInt8)
    (macFn : KeyedMacFn) (macKey : List UInt8)
    (faults : IoFaultSchedule := {}) :
    PosixFsState × LockedVaultHandle × Except PosixErr WalRecord :=
  if h.ioPoisoned then
    (st, h, .error .epoisoned)
  else if !(decide (newEpoch < 2 ^ 64)) || !(decide (newPayload.length < 2 ^ 32)) then
    (st, { h with ioPoisoned := true }, .error .einval)
  else
    match resolveOpenFd st.kernel.openFds h.pid h.lockFd with
    | none => (st, { h with ioPoisoned := true }, .error .ebadf)
    | some (descId, lockDesc) =>
      if descId != h.lockDescId || lockDesc.inode != h.lockInode || lockDesc.stickyFsyncErr ||
         st.kernel.flockTable.owner h.lockInode != some h.lockDescId then
        (st, { h with ioPoisoned := true }, .error .epoisoned)
      else
        let newBody : WalRecordBody :=
          { vaultKeyId := h.vaultKeyId
            lockGenesisId := h.lockGenesisId
            epoch := newEpoch
            payload := newPayload }
        let newRec := signWalRecord macFn macKey newBody
        let tmpPath := walTmpPath h.basePath
        let stCleanTmp := posixUnlinkIfPresent st tmpPath
        match posixCreateExclNoFollow stCleanTmp h.pid tmpPath with
        | .error e => (stCleanTmp, { h with ioPoisoned := true }, .error e)
        | .ok (stCreated, tmpFd, _) =>
          match posixPwriteAll stCreated h.pid tmpFd (encodeWalRecord newRec) with
          | .error e =>
            let stCl := (posixCloseFd stCreated h.pid tmpFd).toOption.getD stCreated
            (stCl, { h with ioPoisoned := true }, .error e)
          | .ok stWritten =>
            let (stSyncedTmp, syncTmpRes) :=
              posixSyncAllMedia stWritten h.pid tmpFd faults.failRecordSync
            let stClosedTmp := (posixCloseFd stSyncedTmp h.pid tmpFd).toOption.getD stSyncedTmp
            match syncTmpRes with
            | .error e => (stClosedTmp, { h with ioPoisoned := true }, .error e)
            | .ok () =>
              match posixRename stClosedTmp tmpPath h.basePath with
              | .error e => (stClosedTmp, { h with ioPoisoned := true }, .error e)
              | .ok stRenamed =>
                let (stSyncedDir, syncDirRes) :=
                  posixSyncParentDir stRenamed faults.failParentSync
                match syncDirRes with
                | .error e => (stSyncedDir, { h with ioPoisoned := true }, .error e)
                | .ok () => (stSyncedDir, h, .ok newRec)

private theorem prod3_mid_eq {α β γ : Type} {a₁ a₂ : α} {b₁ b₂ : β} {c₁ c₂ : γ}
    (h : (a₁, b₁, c₁) = (a₂, b₂, c₂)) : b₁ = b₂ := by
  exact (Prod.mk.inj (Prod.mk.inj h).2).1

/-- Sticky Poisoning Lemma (`replaceAtomic_sticky_poison`):
    Once `h.ioPoisoned = true`, `replaceAtomic` immediately refuses with `.epoisoned` without
    mutating `PosixFsState`, and any error returned by `replaceAtomic` latches `ioPoisoned = true`. -/
theorem replaceAtomic_sticky_poison (st : PosixFsState) (h : LockedVaultHandle)
    (ep : Nat) (pay : List UInt8) (macFn : KeyedMacFn) (macKey : List UInt8)
    (faults : IoFaultSchedule) :
    (h.ioPoisoned = true →
      replaceAtomic st h ep pay macFn macKey faults = (st, h, .error .epoisoned)) ∧
    (∀ st' h' err,
      replaceAtomic st h ep pay macFn macKey faults = (st', h', .error err) →
      h'.ioPoisoned = true) := by
  refine ⟨fun hP => by simp [replaceAtomic, hP], ?_⟩
  intro st' h' err hRun
  unfold replaceAtomic at hRun
  by_cases hP : h.ioPoisoned = true
  · simp only [hP, ↓reduceIte] at hRun
    rw [← prod3_mid_eq hRun]
    exact hP
  · simp only [hP, Bool.false_eq_true, ↓reduceIte] at hRun
    by_cases hBnd : (!(decide (ep < 2 ^ 64)) || !(decide (pay.length < 2 ^ 32))) = true
    · simp only [hBnd, ↓reduceIte] at hRun
      rw [← prod3_mid_eq hRun]
    · simp only [hBnd, Bool.false_eq_true, ↓reduceIte] at hRun
      cases hLk : resolveOpenFd st.kernel.openFds h.pid h.lockFd with
      | none =>
        rw [hLk] at hRun
        rw [← prod3_mid_eq hRun]
      | some dPair =>
        rcases dPair with ⟨descId, lockDesc⟩
        rw [hLk] at hRun
        dsimp only at hRun
        by_cases hInvalid :
            (descId != h.lockDescId || lockDesc.inode != h.lockInode || lockDesc.stickyFsyncErr ||
             st.kernel.flockTable.owner h.lockInode != some h.lockDescId) = true
        · simp only [hInvalid, ↓reduceIte] at hRun
          rw [← prod3_mid_eq hRun]
        · simp only [hInvalid, Bool.false_eq_true, ↓reduceIte] at hRun
          cases hCr : posixCreateExclNoFollow (posixUnlinkIfPresent st (walTmpPath h.basePath))
              h.pid (walTmpPath h.basePath) with
          | error e =>
            rw [hCr] at hRun; rw [← prod3_mid_eq hRun]
          | ok crTriple =>
            rcases crTriple with ⟨stCreated, tmpFd, _⟩
            rw [hCr] at hRun
            dsimp only at hRun
            cases hWr : posixPwriteAll stCreated h.pid tmpFd
                (encodeWalRecord (signWalRecord macFn macKey
                  { vaultKeyId := h.vaultKeyId, lockGenesisId := h.lockGenesisId,
                    epoch := ep, payload := pay })) with
            | error e =>
              rw [hWr] at hRun; rw [← prod3_mid_eq hRun]
            | ok stWritten =>
              rw [hWr] at hRun
              dsimp only at hRun
              cases hSyPair : posixSyncAllMedia stWritten h.pid tmpFd faults.failRecordSync with
              | mk stSyncedTmp syncTmpRes =>
                rw [hSyPair] at hRun
                dsimp only at hRun
                cases syncTmpRes with
                | error e =>
                  rw [← prod3_mid_eq hRun]
                | ok u =>
                  cases u
                  dsimp only at hRun
                  cases hRn : posixRename
                      ((posixCloseFd stSyncedTmp h.pid tmpFd).toOption.getD stSyncedTmp)
                      (walTmpPath h.basePath) h.basePath with
                  | error e =>
                    rw [hRn] at hRun; rw [← prod3_mid_eq hRun]
                  | ok stRenamed =>
                    rw [hRn] at hRun
                    dsimp only at hRun
                    cases hSdPair : posixSyncParentDir stRenamed faults.failParentSync with
                    | mk stSyncedDir syncDirRes =>
                      rw [hSdPair] at hRun
                      dsimp only at hRun
                      cases syncDirRes with
                      | error e =>
                        rw [← prod3_mid_eq hRun]
                      | ok u2 =>
                        cases u2
                        cases hRun

/-! ## 5. Flagship Safety Theorems (Power-Loss Atomicity, Split-Brain Immunity, Multi-Crash Epoch Uniqueness) -/

theorem resolveOpenFd_insert_self (t : OpenFdTable) (p : Pid) (fd : FdId)
    (descId : OpenDescriptionId) (desc : OpenFileDesc) :
    resolveOpenFd
      { fdRefs := assocInsert (p, fd) descId t.fdRefs
        descriptions := assocInsert descId desc t.descriptions
        nextDescId := descId + 1 } p fd = some (descId, desc) := by
  simp [resolveOpenFd]

theorem posixCloseFd_preserves_storage (sA : PosixFsState) (p : Pid) (fd : FdId) :
    let sB := (posixCloseFd sA p fd).toOption.getD sA
    sB.kernel.dirInode = sA.kernel.dirInode ∧
    sB.kernel.pageCache = sA.kernel.pageCache ∧
    sB.driveCache = sA.driveCache ∧
    sB.nand = sA.nand := by
  dsimp only
  rw [posixCloseFd.public_eq_1]
  cases assocLookup sA.kernel.openFds.fdRefs (p, fd) with
  | none => simp [Except.toOption]
  | some descId =>
    dsimp only
    by_cases hRef : descHasAnyRef (assocErase (p, fd) sA.kernel.openFds.fdRefs) descId = true <;>
      simp [hRef, Except.toOption]

/-- Durable vault invariant at rest: both `.lock` (`lockIno`) and `basePath` (`recIno`) are
    committed to `NandBlocks` with zero pending volatile writes and synced directory entries. -/
@[expose] def VaultDurableAt (st : PosixFsState) (basePath : DirName) (lockIno : InodeId)
    (genesisNonce : List UInt8) (macFn : KeyedMacFn) (macKey : List UInt8)
    (rec : WalRecord) : Prop :=
  lockIno < st.nand.nextInode ∧
  lockIno < 2 ^ 64 ∧
  genesisNonce.length = 32 ∧
  rec.WellFormed ∧
  rec.body.lockGenesisId = computeLockGenesisId lockIno genesisNonce ∧
  verifyWalMac macFn macKey rec = true ∧
  st.driveCache.cachedDirEntries = none ∧
  assocLookup st.kernel.dirInode.unsyncedEntries (walLockPath basePath) = some (.regular lockIno) ∧
  assocLookup st.nand.dirNandEntries (walLockPath basePath) = some (.regular lockIno) ∧
  assocLookup st.kernel.pageCache.dirtyFiles lockIno = none ∧
  assocLookup st.driveCache.cachedFiles lockIno = none ∧
  assocLookup st.nand.fileBlocks lockIno =
    some (encodeLockSidecar { sealedLockInode := lockIno, genesisNonce := genesisNonce }) ∧
  ∃ recIno : InodeId,
    recIno < st.nand.nextInode ∧
    assocLookup st.kernel.dirInode.unsyncedEntries basePath = some (.regular recIno) ∧
    assocLookup st.nand.dirNandEntries basePath = some (.regular recIno) ∧
    assocLookup st.kernel.pageCache.dirtyFiles recIno = none ∧
    assocLookup st.driveCache.cachedFiles recIno = none ∧
    assocLookup st.nand.fileBlocks recIno = some (encodeWalRecord rec)

/-- Crash-consistency window invariant holding at **every** micro-step of `replaceAtomic`:
    both `nand.dirNandEntries[basePath]` and `kernel.dirInode.unsyncedEntries[basePath]` point
    to already-synced `NandBlocks` inodes holding exact `oldRec` or exact `newRec`. -/
def VaultCrashSafeWindow (st : PosixFsState) (basePath : DirName) (lockIno : InodeId)
    (genesisNonce : List UInt8) (macFn : KeyedMacFn) (macKey : List UInt8)
    (oldRec newRec : WalRecord) : Prop :=
  lockIno < st.nand.nextInode ∧
  lockIno < 2 ^ 64 ∧
  genesisNonce.length = 32 ∧
  oldRec.WellFormed ∧
  oldRec.body.lockGenesisId = computeLockGenesisId lockIno genesisNonce ∧
  verifyWalMac macFn macKey oldRec = true ∧
  newRec.WellFormed ∧
  newRec.body.vaultKeyId = oldRec.body.vaultKeyId ∧
  newRec.body.lockGenesisId = computeLockGenesisId lockIno genesisNonce ∧
  verifyWalMac macFn macKey newRec = true ∧
  st.driveCache.cachedDirEntries = none ∧
  assocLookup st.kernel.dirInode.unsyncedEntries (walLockPath basePath) = some (.regular lockIno) ∧
  assocLookup st.nand.dirNandEntries (walLockPath basePath) = some (.regular lockIno) ∧
  assocLookup st.kernel.pageCache.dirtyFiles lockIno = none ∧
  assocLookup st.driveCache.cachedFiles lockIno = none ∧
  assocLookup st.nand.fileBlocks lockIno =
    some (encodeLockSidecar { sealedLockInode := lockIno, genesisNonce := genesisNonce }) ∧
  (∃ nandIno : InodeId,
    nandIno < st.nand.nextInode ∧
    assocLookup st.nand.dirNandEntries basePath = some (.regular nandIno) ∧
    assocLookup st.kernel.pageCache.dirtyFiles nandIno = none ∧
    assocLookup st.driveCache.cachedFiles nandIno = none ∧
    (assocLookup st.nand.fileBlocks nandIno = some (encodeWalRecord oldRec) ∨
     assocLookup st.nand.fileBlocks nandIno = some (encodeWalRecord newRec))) ∧
  (∃ memIno : InodeId,
    memIno < st.nand.nextInode ∧
    assocLookup st.kernel.dirInode.unsyncedEntries basePath = some (.regular memIno) ∧
    assocLookup st.kernel.pageCache.dirtyFiles memIno = none ∧
    assocLookup st.driveCache.cachedFiles memIno = none ∧
    (assocLookup st.nand.fileBlocks memIno = some (encodeWalRecord oldRec) ∨
     assocLookup st.nand.fileBlocks memIno = some (encodeWalRecord newRec)))

/-- Collect every intermediate `PosixFsState` produced along the micro-steps of `replaceAtomic`. -/
def replaceAtomicSteps (st : PosixFsState) (h : LockedVaultHandle)
    (newEpoch : Nat) (newPayload : List UInt8)
    (macFn : KeyedMacFn) (macKey : List UInt8)
    (faults : IoFaultSchedule := {}) : List PosixFsState :=
  if h.ioPoisoned then
    [st]
  else if !(decide (newEpoch < 2 ^ 64)) || !(decide (newPayload.length < 2 ^ 32)) then
    [st]
  else
    match resolveOpenFd st.kernel.openFds h.pid h.lockFd with
    | none => [st]
    | some (descId, lockDesc) =>
      if descId != h.lockDescId || lockDesc.inode != h.lockInode || lockDesc.stickyFsyncErr ||
         st.kernel.flockTable.owner h.lockInode != some h.lockDescId then
        [st]
      else
        let newBody : WalRecordBody :=
          { vaultKeyId := h.vaultKeyId
            lockGenesisId := h.lockGenesisId
            epoch := newEpoch
            payload := newPayload }
        let newRec := signWalRecord macFn macKey newBody
        let tmpPath := walTmpPath h.basePath
        let stCleanTmp := posixUnlinkIfPresent st tmpPath
        match posixCreateExclNoFollow stCleanTmp h.pid tmpPath with
        | .error _ => [st, stCleanTmp]
        | .ok (stCreated, tmpFd, _) =>
          match posixPwriteAll stCreated h.pid tmpFd (encodeWalRecord newRec) with
          | .error _ =>
            let stCl := (posixCloseFd stCreated h.pid tmpFd).toOption.getD stCreated
            [st, stCleanTmp, stCreated, stCl]
          | .ok stWritten =>
            let (stSyncedTmp, syncTmpRes) :=
              posixSyncAllMedia stWritten h.pid tmpFd faults.failRecordSync
            let stClosedTmp := (posixCloseFd stSyncedTmp h.pid tmpFd).toOption.getD stSyncedTmp
            match syncTmpRes with
            | .error _ =>
              [st, stCleanTmp, stCreated, stWritten, stSyncedTmp, stClosedTmp]
            | .ok () =>
              match posixRename stClosedTmp tmpPath h.basePath with
              | .error _ =>
                [st, stCleanTmp, stCreated, stWritten, stSyncedTmp, stClosedTmp]
              | .ok stRenamed =>
                let (stSyncedDir, _) :=
                  posixSyncParentDir stRenamed faults.failParentSync
                [st, stCleanTmp, stCreated, stWritten, stSyncedTmp, stClosedTmp,
                 stRenamed, stSyncedDir]

theorem self_mem_replaceAtomicSteps (st : PosixFsState) (h : LockedVaultHandle)
    (ep : Nat) (pay : List UInt8) (macFn : KeyedMacFn) (macKey : List UInt8)
    (faults : IoFaultSchedule) :
    st ∈ replaceAtomicSteps st h ep pay macFn macKey faults := by
  unfold replaceAtomicSteps
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
                | ok _ => simp

/-- Select the `idx`-th state from `xs`, falling back to `fallback`. -/
def pickStepState (fallback : PosixFsState) (xs : List PosixFsState) (idx : Nat) : PosixFsState :=
  match xs[idx]? with
  | some s => s
  | none => fallback

theorem pickStepState_mem {fallback : PosixFsState} {xs : List PosixFsState}
    (hFb : fallback ∈ xs) (idx : Nat) :
    pickStepState fallback xs idx ∈ xs := by
  unfold pickStepState
  cases h : xs[idx]? with
  | none => exact hFb
  | some s => exact List.mem_of_getElem? h

/-- Deterministic post-crash recovery theorem (`openExisting_of_crashed_durable`):
    On any rebooted/crashed state (`openFds = {}`, `flockTable = {}`) satisfying `VaultDurableAt`,
    `openExisting` deterministically succeeds and returns the exact `rec` without corruption. -/
theorem openExisting_of_crashed_durable {st : PosixFsState} {basePath : DirName}
    {lockIno : InodeId} {genesisNonce : List UInt8}
    {macFn : KeyedMacFn} {macKey : List UInt8} {rec : WalRecord} (pid : Pid)
    (hFdsEmpty : st.kernel.openFds = {})
    (hFlkEmpty : st.kernel.flockTable = {})
    (hDur : VaultDurableAt st basePath lockIno genesisNonce macFn macKey rec) :
    ∃ st' hOut,
      openExisting st pid basePath rec.body.vaultKeyId macFn macKey =
        (st', .ok (hOut, rec)) := by
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
    simp only [st1, assocInsert.public_eqs]
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
    rw [posixPreadAll.public_eq_1]
    unfold resolveOpenFd
    unfold readInodeHierarchy
    unfold pendingVolatileWrite
    simp [st3, st2, st1, hRecPg, hRecDrv, hRecNand]
  unfold openExisting
  rw [hOp1]
  dsimp +zetaDelta only
  rw [hFlk]
  dsimp +zetaDelta only
  rw [hFst, hPread1]
  dsimp +zetaDelta only
  rw [hSealDec]
  dsimp +zetaDelta only
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [hOp2]
  dsimp +zetaDelta only
  rw [hPread2]
  dsimp +zetaDelta only
  rw [hRecDec]
  dsimp +zetaDelta only
  have hGidFalse : (rec.body.lockGenesisId != computeLockGenesisId lockIno genesisNonce) = false := by
    rw [hRecGid]; exact bne_self_eq_false _
  rw [hGidFalse, bne_self_eq_false, hRecVer]
  simp only [Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, _, rfl⟩

/-- Crashing from any state inside `VaultCrashSafeWindow` produces a rebooted state with empty
    handles/flocks satisfying `VaultDurableAt` for **either** `oldRec` **or** `newRec`! -/
theorem crashStep_preserves_window_to_durable {mid crashed : PosixFsState}
    {basePath : DirName} {lockIno : InodeId} {genesisNonce : List UInt8}
    {macFn : KeyedMacFn} {macKey : List UInt8} {oldRec newRec : WalRecord}
    (hWin : VaultCrashSafeWindow mid basePath lockIno genesisNonce macFn macKey oldRec newRec)
    (hCrash : CrashStep mid crashed) :
    crashed.kernel.openFds = {} ∧
    crashed.kernel.flockTable = {} ∧
    (VaultDurableAt crashed basePath lockIno genesisNonce macFn macKey oldRec ∨
     VaultDurableAt crashed basePath lockIno genesisNonce macFn macKey newRec) := by
  rcases hWin with ⟨hLockLt, hLock64, hNonceLen, hOldWf, hOldGid, hOldVer,
    hNewWf, hVkEq, hNewGid, hNewVer, hDrvDir,
    hLockMem, hLockNandDir, hLockPg, hLockDrv, hLockNandBytes,
    ⟨nandIno, hNandInoLt, hBaseNandDir, hNandPg, hNandDrv, hNandBytes⟩,
    ⟨memIno, hMemInoLt, hBaseMemDir, hMemPg, hMemDrv, hMemBytes⟩⟩
  have hLockImm := (syncedInode_immune_to_crashStep hLockPg hLockDrv hCrash).1
  have hNandImm := (syncedInode_immune_to_crashStep hNandPg hNandDrv hCrash).1
  have hMemImm := (syncedInode_immune_to_crashStep hMemPg hMemDrv hCrash).1
  cases hCrash with
  | kernelPanic _ =>
    have hFds : (KernelPanicCrash mid).kernel.openFds = {} := rfl
    have hFlk : (KernelPanicCrash mid).kernel.flockTable = {} := rfl
    refine ⟨hFds, hFlk, ?_⟩
    rcases hNandBytes with hOldB | hNewB
    · left
      refine ⟨hLockLt, hLock64, hNonceLen, hOldWf, hOldGid, hOldVer, rfl, ?_, ?_, rfl, rfl, ?_,
        nandIno, hNandInoLt, ?_, ?_, rfl, rfl, ?_⟩
      · simp [KernelPanicCrash, hDrvDir, hLockNandDir]
      · simp [KernelPanicCrash, hDrvDir, hLockNandDir]
      · rw [hLockImm, hLockNandBytes]
      · simp [KernelPanicCrash, hDrvDir, hBaseNandDir]
      · simp [KernelPanicCrash, hDrvDir, hBaseNandDir]
      · rw [hNandImm, hOldB]
    · right
      refine ⟨hLockLt, hLock64, hNonceLen, hNewWf, hNewGid, hNewVer, rfl, ?_, ?_, rfl, rfl, ?_,
        nandIno, hNandInoLt, ?_, ?_, rfl, rfl, ?_⟩
      · simp [KernelPanicCrash, hDrvDir, hLockNandDir]
      · simp [KernelPanicCrash, hDrvDir, hLockNandDir]
      · rw [hLockImm, hLockNandBytes]
      · simp [KernelPanicCrash, hDrvDir, hBaseNandDir]
      · simp [KernelPanicCrash, hDrvDir, hBaseNandDir]
      · rw [hNandImm, hNewB]
  | powerLoss dirPick tearFn _ =>
    have hFds : (PowerLossCrash dirPick tearFn mid).kernel.openFds = {} := rfl
    have hFlk : (PowerLossCrash dirPick tearFn mid).kernel.flockTable = {} := rfl
    refine ⟨hFds, hFlk, ?_⟩
    cases dirPick with
    | revertToNand =>
      rcases hNandBytes with hOldB | hNewB
      · left
        refine ⟨hLockLt, hLock64, hNonceLen, hOldWf, hOldGid, hOldVer, rfl, ?_, ?_, rfl, rfl, ?_,
          nandIno, hNandInoLt, ?_, ?_, rfl, rfl, ?_⟩
        · simp [PowerLossCrash, hLockNandDir]
        · simp [PowerLossCrash, hLockNandDir]
        · rw [hLockImm, hLockNandBytes]
        · simp [PowerLossCrash, hBaseNandDir]
        · simp [PowerLossCrash, hBaseNandDir]
        · rw [hNandImm, hOldB]
      · right
        refine ⟨hLockLt, hLock64, hNonceLen, hNewWf, hNewGid, hNewVer, rfl, ?_, ?_, rfl, rfl, ?_,
          nandIno, hNandInoLt, ?_, ?_, rfl, rfl, ?_⟩
        · simp [PowerLossCrash, hLockNandDir]
        · simp [PowerLossCrash, hLockNandDir]
        · rw [hLockImm, hLockNandBytes]
        · simp [PowerLossCrash, hBaseNandDir]
        · simp [PowerLossCrash, hBaseNandDir]
        · rw [hNandImm, hNewB]
    | flushPendingDir =>
      rcases hMemBytes with hOldB | hNewB
      · left
        refine ⟨hLockLt, hLock64, hNonceLen, hOldWf, hOldGid, hOldVer, rfl, ?_, ?_, rfl, rfl, ?_,
          memIno, hMemInoLt, ?_, ?_, rfl, rfl, ?_⟩
        · simp [PowerLossCrash, hDrvDir, hLockMem]
        · simp [PowerLossCrash, hDrvDir, hLockMem]
        · rw [hLockImm, hLockNandBytes]
        · simp [PowerLossCrash, hDrvDir, hBaseMemDir]
        · simp [PowerLossCrash, hDrvDir, hBaseMemDir]
        · rw [hMemImm, hOldB]
      · right
        refine ⟨hLockLt, hLock64, hNonceLen, hNewWf, hNewGid, hNewVer, rfl, ?_, ?_, rfl, rfl, ?_,
          memIno, hMemInoLt, ?_, ?_, rfl, rfl, ?_⟩
        · simp [PowerLossCrash, hDrvDir, hLockMem]
        · simp [PowerLossCrash, hDrvDir, hLockMem]
        · rw [hLockImm, hLockNandBytes]
        · simp [PowerLossCrash, hDrvDir, hBaseMemDir]
        · simp [PowerLossCrash, hDrvDir, hBaseMemDir]
        · rw [hMemImm, hNewB]

theorem vaultDurableAt_to_window {st : PosixFsState} {basePath : DirName}
    {lockIno : InodeId} {genesisNonce : List UInt8}
    {macFn : KeyedMacFn} {macKey : List UInt8} {oldRec newRec : WalRecord}
    (hDur : VaultDurableAt st basePath lockIno genesisNonce macFn macKey oldRec)
    (hNewWf : newRec.WellFormed)
    (hVkEq : newRec.body.vaultKeyId = oldRec.body.vaultKeyId)
    (hNewGid : newRec.body.lockGenesisId = computeLockGenesisId lockIno genesisNonce)
    (hNewVer : verifyWalMac macFn macKey newRec = true) :
    VaultCrashSafeWindow st basePath lockIno genesisNonce macFn macKey oldRec newRec := by
  rcases hDur with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    recIno, hInoLt, hMem, hNand, hPg, hDrv, hBytes⟩
  exact ⟨h1, h2, h3, h4, h5, h6, hNewWf, hVkEq, hNewGid, hNewVer, h7, h8, h9, h10, h11, h12,
    ⟨recIno, hInoLt, hNand, hPg, hDrv, Or.inl hBytes⟩,
    ⟨recIno, hInoLt, hMem, hPg, hDrv, Or.inl hBytes⟩⟩

/-- Every intermediate state in `replaceAtomicSteps` preserves `VaultCrashSafeWindow`! -/
theorem replaceAtomicSteps_all_in_window {st mid : PosixFsState}
    {h : LockedVaultHandle} {lockIno : InodeId} {genesisNonce : List UInt8}
    {macFn : KeyedMacFn} (hMacWf : WellFormedMacFn macFn) {macKey : List UInt8}
    {oldRec : WalRecord} {newEpoch : Nat} (hEpLt : newEpoch < 2 ^ 64)
    {newPayload : List UInt8} (hPayLt : newPayload.length < 2 ^ 32)
    (faults : IoFaultSchedule)
    (hVkEqH : h.vaultKeyId = oldRec.body.vaultKeyId)
    (hGidEqH : h.lockGenesisId = computeLockGenesisId lockIno genesisNonce)
    (hDur : VaultDurableAt st h.basePath lockIno genesisNonce macFn macKey oldRec)
    (hMid : mid ∈ replaceAtomicSteps st h newEpoch newPayload macFn macKey faults) :
    let newRec := signWalRecord macFn macKey
      { vaultKeyId := h.vaultKeyId
        lockGenesisId := h.lockGenesisId
        epoch := newEpoch
        payload := newPayload }
    VaultCrashSafeWindow mid h.basePath lockIno genesisNonce macFn macKey oldRec newRec := by
  intro newRec
  have hNewBodyWf : ({ vaultKeyId := h.vaultKeyId, lockGenesisId := h.lockGenesisId,
                       epoch := newEpoch, payload := newPayload } : WalRecordBody).WellFormed := by
    refine ⟨?_, ?_, hEpLt, hPayLt⟩
    · rw [hVkEqH]; exact hDur.2.2.2.1.1.1
    · rw [hGidEqH]; exact computeLockGenesisId_length hDur.2.2.1
  have hNewWf : newRec.WellFormed := signWalRecord_wellFormed hMacWf macKey hNewBodyWf
  have hNewVer : verifyWalMac macFn macKey newRec = true := verifyWalMac_signWalRecord _ _ _
  have hBaseWin : VaultCrashSafeWindow st h.basePath lockIno genesisNonce macFn macKey oldRec newRec :=
    vaultDurableAt_to_window hDur hNewWf hVkEqH hGidEqH hNewVer
  unfold replaceAtomicSteps at hMid
  by_cases hP : h.ioPoisoned = true
  · simp only [hP, ↓reduceIte, List.mem_singleton] at hMid
    subst hMid; exact hBaseWin
  · simp only [hP, Bool.false_eq_true, ↓reduceIte] at hMid
    have hBndFalse : (!(decide (newEpoch < 2 ^ 64)) || !(decide (newPayload.length < 2 ^ 32))) = false := by
      simp [hEpLt, hPayLt]
    rw [hBndFalse] at hMid
    simp only [Bool.false_eq_true, ↓reduceIte] at hMid
    cases hLk : resolveOpenFd st.kernel.openFds h.pid h.lockFd with
    | none =>
      rw [hLk] at hMid
      simp only [List.mem_singleton] at hMid
      subst hMid; exact hBaseWin
    | some dPair =>
      rcases dPair with ⟨descId, lockDesc⟩
      rw [hLk] at hMid
      dsimp only at hMid
      by_cases hInv :
          (descId != h.lockDescId || lockDesc.inode != h.lockInode || lockDesc.stickyFsyncErr ||
           st.kernel.flockTable.owner h.lockInode != some h.lockDescId) = true
      · simp only [hInv, ↓reduceIte, List.mem_singleton] at hMid
        subst hMid; exact hBaseWin
      · simp only [hInv, Bool.false_eq_true, ↓reduceIte] at hMid
        rcases hDur with ⟨hLockLt, hLock64, hNonceLen, hOldWf, hOldGid, hOldVer, hDrvDir,
          hLockMem, hLockNandDir, hLockPg, hLockDrv, hLockNandBytes,
          oldIno, hOldInoLt, hOldMem, hOldNandDir, hOldPg, hOldDrv, hOldNandBytes⟩
        let tmpPath := walTmpPath h.basePath
        let stCleanTmp := posixUnlinkIfPresent st tmpPath
        have hTmpNeBase : h.basePath ≠ tmpPath := fun he => walTmpPath_ne_base h.basePath he.symm
        have hTmpNeLock : walLockPath h.basePath ≠ tmpPath :=
          fun he => walTmpPath_ne_lockPath h.basePath he.symm
        have hBaseNeLock : walLockPath h.basePath ≠ h.basePath := walLockPath_ne_base h.basePath
        have hCleanWin :
            VaultCrashSafeWindow stCleanTmp h.basePath lockIno genesisNonce macFn macKey oldRec newRec := by
          refine ⟨hLockLt, hLock64, hNonceLen, hOldWf, hOldGid, hOldVer,
            hNewWf, hVkEqH, hGidEqH, hNewVer, hDrvDir, ?_, hLockNandDir, hLockPg, hLockDrv, hLockNandBytes,
            ⟨oldIno, hOldInoLt, hOldNandDir, hOldPg, hOldDrv, Or.inl hOldNandBytes⟩,
            ⟨oldIno, hOldInoLt, ?_, hOldPg, hOldDrv, Or.inl hOldNandBytes⟩⟩
          · simp [stCleanTmp, posixUnlinkIfPresent, hTmpNeLock, hLockMem]
          · simp [stCleanTmp, posixUnlinkIfPresent, hTmpNeBase, hOldMem]
        let tmpIno := st.nand.nextInode
        let tmpFd := st.nextFd
        let tmpDescId := st.kernel.openFds.nextDescId
        let stCreated : PosixFsState :=
          { kernel := { stCleanTmp.kernel with
                         openFds := { fdRefs := assocInsert (h.pid, tmpFd) tmpDescId st.kernel.openFds.fdRefs
                                      descriptions := assocInsert tmpDescId
                                                        { inode := tmpIno, writable := true, stickyFsyncErr := false }
                                                        st.kernel.openFds.descriptions
                                      nextDescId := tmpDescId + 1 }
                         dirInode := { unsyncedEntries :=
                                         assocInsert tmpPath (.regular tmpIno)
                                           stCleanTmp.kernel.dirInode.unsyncedEntries } }
            driveCache := st.driveCache
            nand := { st.nand with
                       fileBlocks := assocInsert tmpIno [] st.nand.fileBlocks
                       nextInode := tmpIno + 1 }
            nextFd := tmpFd + 1 }
        have hCrEq : posixCreateExclNoFollow stCleanTmp h.pid tmpPath = .ok (stCreated, tmpFd, tmpIno) := by
          rw [posixCreateExclNoFollow.public_eq_1]
          have hAbs : assocLookup stCleanTmp.kernel.dirInode.unsyncedEntries tmpPath = none := by
            simp [stCleanTmp, posixUnlinkIfPresent]
          rw [hAbs]
          rfl
        rw [hCrEq] at hMid
        dsimp only at hMid
        have hLockNeTmp : lockIno ≠ tmpIno := Nat.ne_of_lt hLockLt
        have hOldNeTmp : oldIno ≠ tmpIno := Nat.ne_of_lt hOldInoLt
        have hLockLtNext : lockIno < tmpIno + 1 := Nat.lt_succ_of_lt hLockLt
        have hOldLtNext : oldIno < tmpIno + 1 := Nat.lt_succ_of_lt hOldInoLt
        have hCreatedWin :
            VaultCrashSafeWindow stCreated h.basePath lockIno genesisNonce macFn macKey oldRec newRec := by
          refine ⟨hLockLtNext, hLock64, hNonceLen, hOldWf, hOldGid, hOldVer,
            hNewWf, hVkEqH, hGidEqH, hNewVer, hDrvDir, ?_, hLockNandDir, hLockPg, hLockDrv, ?_,
            ⟨oldIno, hOldLtNext, hOldNandDir, hOldPg, hOldDrv, Or.inl ?_⟩,
            ⟨oldIno, hOldLtNext, ?_, hOldPg, hOldDrv, Or.inl ?_⟩⟩
          · simp [stCreated, stCleanTmp, posixUnlinkIfPresent, hTmpNeLock, hLockMem]
          · simp [stCreated, hLockNeTmp, hLockNandBytes]
          · simp [stCreated, hOldNeTmp, hOldNandBytes]
          · simp [stCreated, stCleanTmp, posixUnlinkIfPresent, hTmpNeBase, hOldMem]
          · simp [stCreated, hOldNeTmp, hOldNandBytes]
        let stWritten : PosixFsState :=
          { stCreated with
             kernel := { stCreated.kernel with
                          pageCache := { dirtyFiles :=
                                           assocInsert tmpIno (encodeWalRecord newRec)
                                             st.kernel.pageCache.dirtyFiles } } }
        have hWrEq : posixPwriteAll stCreated h.pid tmpFd (encodeWalRecord newRec) = .ok stWritten := by
          rw [posixPwriteAll.public_eq_1]
          simp [stWritten, stCreated, stCleanTmp, posixUnlinkIfPresent, resolveOpenFd_insert_self]
        rw [hWrEq] at hMid
        dsimp only at hMid
        have hWrittenWin :
            VaultCrashSafeWindow stWritten h.basePath lockIno genesisNonce macFn macKey oldRec newRec := by
          refine ⟨hLockLtNext, hLock64, hNonceLen, hOldWf, hOldGid, hOldVer,
            hNewWf, hVkEqH, hGidEqH, hNewVer, hDrvDir,
            hCreatedWin.2.2.2.2.2.2.2.2.2.2.2.1,
            hLockNandDir, ?_, hLockDrv, hCreatedWin.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            ⟨oldIno, hOldLtNext, hOldNandDir, ?_, hOldDrv,
              Or.inl (by simp [stWritten, stCreated, hOldNeTmp, hOldNandBytes])⟩,
            ⟨oldIno, hOldLtNext,
              by simp [stWritten, stCreated, stCleanTmp, posixUnlinkIfPresent, hTmpNeBase, hOldMem],
              ?_, hOldDrv,
              Or.inl (by simp [stWritten, stCreated, hOldNeTmp, hOldNandBytes])⟩⟩
          · simp [stWritten, hLockNeTmp, hLockPg]
          · simp [stWritten, hOldNeTmp, hOldPg]
          · simp [stWritten, hOldNeTmp, hOldPg]
        by_cases hFailRec : faults.failRecordSync = true
        · have hSyFail :
              posixSyncAllMedia stWritten h.pid tmpFd faults.failRecordSync =
                ({ stWritten with
                    kernel := { stWritten.kernel with
                                  openFds := { stWritten.kernel.openFds with
                                                 descriptions := assocInsert tmpDescId
                                                   { inode := tmpIno, writable := true, stickyFsyncErr := true }
                                                   stWritten.kernel.openFds.descriptions }
                                  pageCache := { dirtyFiles := assocErase tmpIno stWritten.kernel.pageCache.dirtyFiles } }
                    driveCache := { stWritten.driveCache with
                                     cachedFiles := assocErase tmpIno st.driveCache.cachedFiles } },
                 .error .eio) := by
            rw [posixSyncAllMedia.public_eq_1]
            simp [stWritten, stCreated, resolveOpenFd_insert_self, hFailRec]
          rw [hSyFail] at hMid
          dsimp only at hMid
          let stSyErr := (posixSyncAllMedia stWritten h.pid tmpFd faults.failRecordSync).1
          have hSyErrEq : stSyErr =
              { stWritten with
                  kernel := { stWritten.kernel with
                                openFds := { stWritten.kernel.openFds with
                                               descriptions := assocInsert tmpDescId
                                                 { inode := tmpIno, writable := true, stickyFsyncErr := true }
                                                 stWritten.kernel.openFds.descriptions }
                                pageCache := { dirtyFiles := assocErase tmpIno stWritten.kernel.pageCache.dirtyFiles } }
                  driveCache := { stWritten.driveCache with
                                   cachedFiles := assocErase tmpIno st.driveCache.cachedFiles } } :=
            congrArg Prod.fst hSyFail
          have hSyErrWin :
              VaultCrashSafeWindow stSyErr h.basePath lockIno genesisNonce macFn macKey oldRec newRec := by
            rw [hSyErrEq]
            refine ⟨hLockLtNext, hLock64, hNonceLen, hOldWf, hOldGid, hOldVer,
              hNewWf, hVkEqH, hGidEqH, hNewVer, hDrvDir,
              by simp [stWritten, stCreated, stCleanTmp, posixUnlinkIfPresent, hTmpNeLock, hLockMem],
              hLockNandDir,
              by simp [stWritten, hLockNeTmp, hLockPg],
              by simp [hLockNeTmp, hLockDrv],
              by simp [stWritten, stCreated, hLockNeTmp, hLockNandBytes],
              ⟨oldIno, hOldLtNext, hOldNandDir,
                by simp [stWritten, hOldNeTmp, hOldPg],
                by simp [hOldNeTmp, hOldDrv],
                Or.inl (by simp [stWritten, stCreated, hOldNeTmp, hOldNandBytes])⟩,
              ⟨oldIno, hOldLtNext,
                by simp [stWritten, stCreated, stCleanTmp, posixUnlinkIfPresent, hTmpNeBase, hOldMem],
                by simp [stWritten, hOldNeTmp, hOldPg],
                by simp [hOldNeTmp, hOldDrv],
                Or.inl (by simp [stWritten, stCreated, hOldNeTmp, hOldNandBytes])⟩⟩
          have hClosePreserves : ∀ s0 : PosixFsState,
              VaultCrashSafeWindow s0 h.basePath lockIno genesisNonce macFn macKey oldRec newRec →
              VaultCrashSafeWindow ((posixCloseFd s0 h.pid tmpFd).toOption.getD s0)
                h.basePath lockIno genesisNonce macFn macKey oldRec newRec := by
            intro s0 hW0
            rcases posixCloseFd_preserves_storage s0 h.pid tmpFd with ⟨hDi, hPgC, hDrC, hNdC⟩
            unfold VaultCrashSafeWindow
            rw [hDi, hPgC, hDrC, hNdC]
            exact hW0
          rcases List.mem_cons.mp hMid with rfl | hMid
          · exact hBaseWin
          · rcases List.mem_cons.mp hMid with rfl | hMid
            · exact hCleanWin
            · rcases List.mem_cons.mp hMid with rfl | hMid
              · exact hCreatedWin
              · rcases List.mem_cons.mp hMid with rfl | hMid
                · exact hWrittenWin
                · rcases List.mem_cons.mp hMid with rfl | hMid
                  · rw [hSyErrEq] at hSyErrWin; exact hSyErrWin
                  · rcases List.mem_cons.mp hMid with rfl | hMid
                    · rw [hSyErrEq] at hSyErrWin
                      exact hClosePreserves _ hSyErrWin
                    · cases hMid
        · have hFailFalse : faults.failRecordSync = false := by
            cases hB : faults.failRecordSync
            · rfl
            · exfalso; exact hFailRec hB
          have hSyOk :
              posixSyncAllMedia stWritten h.pid tmpFd faults.failRecordSync =
                ({ stWritten with
                    kernel := { stWritten.kernel with
                                  pageCache := { dirtyFiles := assocErase tmpIno stWritten.kernel.pageCache.dirtyFiles } }
                    driveCache := { stWritten.driveCache with
                                     cachedFiles := assocErase tmpIno st.driveCache.cachedFiles }
                    nand := { stWritten.nand with
                               fileBlocks := assocInsert tmpIno (encodeWalRecord newRec)
                                               stWritten.nand.fileBlocks } },
                 .ok ()) := by
            rw [posixSyncAllMedia.public_eq_1]
            unfold readInodeHierarchy
            unfold pendingVolatileWrite
            simp [stWritten, stCreated, resolveOpenFd_insert_self, hFailFalse]
          rw [hSyOk] at hMid
          dsimp only at hMid
          let stSyncedTmp : PosixFsState :=
            { stWritten with
               kernel := { stWritten.kernel with
                            pageCache := { dirtyFiles := assocErase tmpIno stWritten.kernel.pageCache.dirtyFiles } }
               driveCache := { stWritten.driveCache with
                                cachedFiles := assocErase tmpIno st.driveCache.cachedFiles }
               nand := { stWritten.nand with
                          fileBlocks := assocInsert tmpIno (encodeWalRecord newRec)
                                          stWritten.nand.fileBlocks } }
          have hSyncedTmpWin :
              VaultCrashSafeWindow stSyncedTmp h.basePath lockIno genesisNonce macFn macKey oldRec newRec := by
            refine ⟨hLockLtNext, hLock64, hNonceLen, hOldWf, hOldGid, hOldVer,
              hNewWf, hVkEqH, hGidEqH, hNewVer, hDrvDir,
              by simp [stSyncedTmp, stWritten, stCreated, stCleanTmp, posixUnlinkIfPresent, hTmpNeLock, hLockMem],
              hLockNandDir,
              by simp [stSyncedTmp, stWritten, hLockNeTmp, hLockPg],
              by simp [stSyncedTmp, hLockNeTmp, hLockDrv],
              by simp [stSyncedTmp, stWritten, stCreated, hLockNeTmp, hLockNandBytes],
              ⟨oldIno, hOldLtNext, hOldNandDir,
                by simp [stSyncedTmp, stWritten, hOldNeTmp, hOldPg],
                by simp [stSyncedTmp, hOldNeTmp, hOldDrv],
                Or.inl (by simp [stSyncedTmp, stWritten, stCreated, hOldNeTmp, hOldNandBytes])⟩,
              ⟨oldIno, hOldLtNext,
                by simp [stSyncedTmp, stWritten, stCreated, stCleanTmp, posixUnlinkIfPresent, hTmpNeBase, hOldMem],
                by simp [stSyncedTmp, stWritten, hOldNeTmp, hOldPg],
                by simp [stSyncedTmp, hOldNeTmp, hOldDrv],
                Or.inl (by simp [stSyncedTmp, stWritten, stCreated, hOldNeTmp, hOldNandBytes])⟩⟩
          let stClosedTmp := (posixCloseFd stSyncedTmp h.pid tmpFd).toOption.getD stSyncedTmp
          have hClosedSameStorage := posixCloseFd_preserves_storage stSyncedTmp h.pid tmpFd
          have hClosedWin :
              VaultCrashSafeWindow stClosedTmp h.basePath lockIno genesisNonce macFn macKey oldRec newRec := by
            rcases hClosedSameStorage with ⟨hDi, hPgC, hDrC, hNdC⟩
            unfold VaultCrashSafeWindow
            rw [hDi, hPgC, hDrC, hNdC]
            exact hSyncedTmpWin
          have hTmpPresent :
              assocLookup stClosedTmp.kernel.dirInode.unsyncedEntries tmpPath =
                some (.regular tmpIno) := by
            dsimp only [stClosedTmp]
            rw [hClosedSameStorage.1]
            simp [stSyncedTmp, stWritten, stCreated]
          have hRnEq :
              posixRename stClosedTmp tmpPath h.basePath =
                .ok { stClosedTmp with
                       kernel := { stClosedTmp.kernel with
                                    dirInode := { unsyncedEntries :=
                                                    (if tmpPath == h.basePath then
                                                       assocInsert h.basePath (.regular tmpIno)
                                                         stClosedTmp.kernel.dirInode.unsyncedEntries
                                                     else
                                                       assocErase tmpPath
                                                         (assocInsert h.basePath (.regular tmpIno)
                                                           stClosedTmp.kernel.dirInode.unsyncedEntries)) } } } := by
            rw [posixRename.public_eq_1]
            rw [hTmpPresent]
          rw [hRnEq] at hMid
          dsimp only at hMid
          have hTmpBeqBase : (tmpPath == h.basePath) = false := by
            cases hB : (tmpPath == h.basePath)
            · rfl
            · exfalso; exact walTmpPath_ne_base h.basePath (eq_of_beq hB)
          let stRenamed : PosixFsState :=
            { stClosedTmp with
               kernel := { stClosedTmp.kernel with
                            dirInode := { unsyncedEntries :=
                                            (if tmpPath == h.basePath then
                                               assocInsert h.basePath (.regular tmpIno)
                                                 stClosedTmp.kernel.dirInode.unsyncedEntries
                                             else
                                               assocErase tmpPath
                                                 (assocInsert h.basePath (.regular tmpIno)
                                                   stClosedTmp.kernel.dirInode.unsyncedEntries)) } } }
          have hRenamedLockMem :
              assocLookup stRenamed.kernel.dirInode.unsyncedEntries (walLockPath h.basePath) =
                some (.regular lockIno) := by
            dsimp only [stRenamed, stClosedTmp]
            rw [hTmpBeqBase]
            simp only [Bool.false_eq_true, ↓reduceIte, assocLookup_erase, hTmpNeLock,
              assocLookup_insert, hBaseNeLock]
            rw [hClosedSameStorage.1]
            simp [stSyncedTmp, stWritten, stCreated, stCleanTmp, posixUnlinkIfPresent,
              hTmpNeLock, hLockMem]
          have hRenamedBaseMem :
              assocLookup stRenamed.kernel.dirInode.unsyncedEntries h.basePath =
                some (.regular tmpIno) := by
            dsimp only [stRenamed]
            rw [hTmpBeqBase]
            simp [hTmpNeBase]
          have hTmpCleaned :
              assocLookup stClosedTmp.kernel.pageCache.dirtyFiles tmpIno = none ∧
              assocLookup stClosedTmp.driveCache.cachedFiles tmpIno = none ∧
              assocLookup stClosedTmp.nand.fileBlocks tmpIno = some (encodeWalRecord newRec) ∧
              tmpIno < stClosedTmp.nand.nextInode := by
            dsimp only [stClosedTmp]
            rw [hClosedSameStorage.2.1, hClosedSameStorage.2.2.1, hClosedSameStorage.2.2.2]
            refine ⟨by simp [stSyncedTmp], by simp [stSyncedTmp], by simp [stSyncedTmp], ?_⟩
            simp [stSyncedTmp, stWritten, stCreated]
          have hRenamedWin :
              VaultCrashSafeWindow stRenamed h.basePath lockIno genesisNonce macFn macKey oldRec newRec := by
            rcases hClosedSameStorage with ⟨_, hPgC, hDrC, hNdC⟩
            refine ⟨?_, hLock64, hNonceLen, hOldWf, hOldGid, hOldVer,
              hNewWf, hVkEqH, hGidEqH, hNewVer, ?_,
              hRenamedLockMem, ?_, ?_, ?_, ?_,
              ⟨oldIno, ?_, ?_, ?_, ?_, Or.inl ?_⟩,
              ⟨tmpIno, hTmpCleaned.2.2.2, hRenamedBaseMem, hTmpCleaned.1, hTmpCleaned.2.1,
                Or.inr hTmpCleaned.2.2.1⟩⟩
            · dsimp only [stRenamed, stClosedTmp]; rw [hNdC]; exact hLockLtNext
            · dsimp only [stRenamed, stClosedTmp]; rw [hDrC]; exact hDrvDir
            · dsimp only [stRenamed, stClosedTmp]; rw [hNdC]; exact hLockNandDir
            · dsimp only [stRenamed, stClosedTmp]; rw [hPgC]; simp [stSyncedTmp, stWritten, hLockNeTmp, hLockPg]
            · dsimp only [stRenamed, stClosedTmp]; rw [hDrC]; simp [stSyncedTmp, hLockNeTmp, hLockDrv]
            · dsimp only [stRenamed, stClosedTmp]; rw [hNdC]; simp [stSyncedTmp, stWritten, stCreated, hLockNeTmp, hLockNandBytes]
            · dsimp only [stRenamed, stClosedTmp]; rw [hNdC]; exact hOldLtNext
            · dsimp only [stRenamed, stClosedTmp]; rw [hNdC]; exact hOldNandDir
            · dsimp only [stRenamed, stClosedTmp]; rw [hPgC]; simp [stSyncedTmp, stWritten, hOldNeTmp, hOldPg]
            · dsimp only [stRenamed, stClosedTmp]; rw [hDrC]; simp [stSyncedTmp, hOldNeTmp, hOldDrv]
            · dsimp only [stRenamed, stClosedTmp]; rw [hNdC]; simp [stSyncedTmp, stWritten, stCreated, hOldNeTmp, hOldNandBytes]
          let stSyncedDir := (posixSyncParentDir stRenamed faults.failParentSync).1
          have hSyncedDirWin :
              VaultCrashSafeWindow stSyncedDir h.basePath lockIno genesisNonce macFn macKey oldRec newRec := by
            simp only [stSyncedDir, posixSyncParentDir.public_eqs]
            by_cases hFp : faults.failParentSync = true
            · simp only [hFp, ↓reduceIte]; exact hRenamedWin
            · simp only [hFp, Bool.false_eq_true, ↓reduceIte]
              rcases hRenamedWin with ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, _,
                w12, _, w14, w15, w16, _, wMem⟩
              exact ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, rfl,
                w12, w12, w14, w15, w16, wMem, wMem⟩
          rcases List.mem_cons.mp hMid with rfl | hMid
          · exact hBaseWin
          · rcases List.mem_cons.mp hMid with rfl | hMid
            · exact hCleanWin
            · rcases List.mem_cons.mp hMid with rfl | hMid
              · exact hCreatedWin
              · rcases List.mem_cons.mp hMid with rfl | hMid
                · exact hWrittenWin
                · rcases List.mem_cons.mp hMid with rfl | hMid
                  · exact hSyncedTmpWin
                  · rcases List.mem_cons.mp hMid with rfl | hMid
                    · exact hClosedWin
                    · rcases List.mem_cons.mp hMid with rfl | hMid
                      · exact hRenamedWin
                      · rcases List.mem_cons.mp hMid with rfl | hMid
                        · exact hSyncedDirWin
                        · cases hMid

/-- **Post-Commit Durability Lemma (`replaceAtomic_ok_durable`)**:
    Whenever `replaceAtomic` returns `.ok committedRec`, `committedRec` is durably persisted on
    `NandBlocks` (`VaultDurableAt st' ... committedRec`) and survives every subsequent `CrashStep`! -/
theorem replaceAtomic_ok_durable {st st' : PosixFsState} {h h' : LockedVaultHandle}
    {lockIno : InodeId} {genesisNonce : List UInt8}
    {macFn : KeyedMacFn} (hMacWf : WellFormedMacFn macFn) {macKey : List UInt8}
    {oldRec committedRec : WalRecord} {newEpoch : Nat} {newPayload : List UInt8}
    {faults : IoFaultSchedule}
    (hVkEqH : h.vaultKeyId = oldRec.body.vaultKeyId)
    (hGidEqH : h.lockGenesisId = computeLockGenesisId lockIno genesisNonce)
    (hDur : VaultDurableAt st h.basePath lockIno genesisNonce macFn macKey oldRec)
    (hOk : replaceAtomic st h newEpoch newPayload macFn macKey faults =
             (st', h', .ok committedRec)) :
    h' = h ∧
    committedRec = signWalRecord macFn macKey
      { vaultKeyId := h.vaultKeyId, lockGenesisId := h.lockGenesisId,
        epoch := newEpoch, payload := newPayload } ∧
    VaultDurableAt st' h.basePath lockIno genesisNonce macFn macKey committedRec := by
  unfold replaceAtomic at hOk
  by_cases hP : h.ioPoisoned = true
  · simp only [hP, ↓reduceIte] at hOk; cases (Prod.mk.inj (Prod.mk.inj hOk).2).2
  · simp only [hP, Bool.false_eq_true, ↓reduceIte] at hOk
    by_cases hBnd : (!(decide (newEpoch < 2 ^ 64)) || !(decide (newPayload.length < 2 ^ 32))) = true
    · simp only [hBnd, ↓reduceIte] at hOk; cases (Prod.mk.inj (Prod.mk.inj hOk).2).2
    · simp only [hBnd, Bool.false_eq_true, ↓reduceIte] at hOk
      have hEpLt : newEpoch < 2 ^ 64 := by
        cases hD : decide (newEpoch < 2 ^ 64)
        · exfalso; apply hBnd; simp [hD]
        · exact of_decide_eq_true hD
      have hPayLt : newPayload.length < 2 ^ 32 := by
        cases hD : decide (newPayload.length < 2 ^ 32)
        · exfalso; apply hBnd; simp [hD]
        · exact of_decide_eq_true hD
      cases hLk : resolveOpenFd st.kernel.openFds h.pid h.lockFd with
      | none => rw [hLk] at hOk; cases (Prod.mk.inj (Prod.mk.inj hOk).2).2
      | some dPair =>
        rcases dPair with ⟨descId, lockDesc⟩
        rw [hLk] at hOk
        dsimp only at hOk
        by_cases hInv :
            (descId != h.lockDescId || lockDesc.inode != h.lockInode || lockDesc.stickyFsyncErr ||
             st.kernel.flockTable.owner h.lockInode != some h.lockDescId) = true
        · simp only [hInv, ↓reduceIte] at hOk; cases (Prod.mk.inj (Prod.mk.inj hOk).2).2
        · simp only [hInv, Bool.false_eq_true, ↓reduceIte] at hOk
          let newRec := signWalRecord macFn macKey
            { vaultKeyId := h.vaultKeyId, lockGenesisId := h.lockGenesisId,
              epoch := newEpoch, payload := newPayload }
          have hNewBodyWf : ({ vaultKeyId := h.vaultKeyId, lockGenesisId := h.lockGenesisId,
                               epoch := newEpoch, payload := newPayload } : WalRecordBody).WellFormed := by
            refine ⟨?_, ?_, hEpLt, hPayLt⟩
            · rw [hVkEqH]; exact hDur.2.2.2.1.1.1
            · rw [hGidEqH]; exact computeLockGenesisId_length hDur.2.2.1
          have hNewWf : newRec.WellFormed := signWalRecord_wellFormed hMacWf macKey hNewBodyWf
          have hNewVer : verifyWalMac macFn macKey newRec = true := verifyWalMac_signWalRecord _ _ _
          rcases hDur with ⟨hLockLt, hLock64, hNonceLen, _, _, _, _,
            hLockMem, _, hLockPg, hLockDrv, hLockNandBytes,
            _, _, _, _, _, _, _⟩
          let tmpPath := walTmpPath h.basePath
          let stCleanTmp := posixUnlinkIfPresent st tmpPath
          have hTmpNeBase : h.basePath ≠ tmpPath := fun he => walTmpPath_ne_base h.basePath he.symm
          have hTmpNeLock : walLockPath h.basePath ≠ tmpPath :=
            fun he => walTmpPath_ne_lockPath h.basePath he.symm
          have hBaseNeLock : walLockPath h.basePath ≠ h.basePath := walLockPath_ne_base h.basePath
          let tmpIno := st.nand.nextInode
          let tmpFd := st.nextFd
          let tmpDescId := st.kernel.openFds.nextDescId
          let stCreated : PosixFsState :=
            { kernel := { stCleanTmp.kernel with
                           openFds := { fdRefs := assocInsert (h.pid, tmpFd) tmpDescId st.kernel.openFds.fdRefs
                                        descriptions := assocInsert tmpDescId
                                                          { inode := tmpIno, writable := true, stickyFsyncErr := false }
                                                          st.kernel.openFds.descriptions
                                        nextDescId := tmpDescId + 1 }
                           dirInode := { unsyncedEntries :=
                                           assocInsert tmpPath (.regular tmpIno)
                                             stCleanTmp.kernel.dirInode.unsyncedEntries } }
              driveCache := st.driveCache
              nand := { st.nand with
                         fileBlocks := assocInsert tmpIno [] st.nand.fileBlocks
                         nextInode := tmpIno + 1 }
              nextFd := tmpFd + 1 }
          have hCrEq : posixCreateExclNoFollow stCleanTmp h.pid tmpPath = .ok (stCreated, tmpFd, tmpIno) := by
            rw [posixCreateExclNoFollow.public_eq_1]
            have hAbs : assocLookup stCleanTmp.kernel.dirInode.unsyncedEntries tmpPath = none := by
              simp [stCleanTmp, posixUnlinkIfPresent]
            rw [hAbs]; rfl
          rw [hCrEq] at hOk
          dsimp only at hOk
          have hLockNeTmp : lockIno ≠ tmpIno := Nat.ne_of_lt hLockLt
          let stWritten : PosixFsState :=
            { stCreated with
               kernel := { stCreated.kernel with
                            pageCache := { dirtyFiles :=
                                             assocInsert tmpIno (encodeWalRecord newRec)
                                               st.kernel.pageCache.dirtyFiles } } }
          have hWrEq : posixPwriteAll stCreated h.pid tmpFd (encodeWalRecord newRec) = .ok stWritten := by
            rw [posixPwriteAll.public_eq_1]
            simp [stWritten, stCreated, stCleanTmp, posixUnlinkIfPresent, resolveOpenFd_insert_self]
          rw [hWrEq] at hOk
          dsimp only at hOk
          cases hFailRec : faults.failRecordSync with
          | true =>
            have hSyF : (posixSyncAllMedia stWritten h.pid tmpFd true).2 = .error .eio := by
              rw [posixSyncAllMedia.public_eq_1]; simp [stWritten, stCreated, resolveOpenFd_insert_self]
            rw [hFailRec] at hOk
            cases hPair : posixSyncAllMedia stWritten h.pid tmpFd true with
            | mk sA rA =>
              rw [hPair] at hOk hSyF
              dsimp only at hOk hSyF
              rw [hSyF] at hOk
              cases (Prod.mk.inj (Prod.mk.inj hOk).2).2
          | false =>
            rw [hFailRec] at hOk
            let stSyncedTmp : PosixFsState :=
              { stWritten with
                  kernel := { stWritten.kernel with
                                pageCache := { dirtyFiles := assocErase tmpIno stWritten.kernel.pageCache.dirtyFiles } }
                  driveCache := { stWritten.driveCache with
                                   cachedFiles := assocErase tmpIno st.driveCache.cachedFiles }
                  nand := { stWritten.nand with
                             fileBlocks := assocInsert tmpIno (encodeWalRecord newRec)
                                             stWritten.nand.fileBlocks } }
            have hSyOk :
                posixSyncAllMedia stWritten h.pid tmpFd false = (stSyncedTmp, .ok ()) := by
              rw [posixSyncAllMedia.public_eq_1]
              unfold readInodeHierarchy
              unfold pendingVolatileWrite
              simp [stSyncedTmp, stWritten, stCreated, resolveOpenFd_insert_self]
            rw [hSyOk] at hOk
            dsimp only at hOk
            let stClosedTmp := (posixCloseFd stSyncedTmp h.pid tmpFd).toOption.getD stSyncedTmp
            have hClosedSameStorage := posixCloseFd_preserves_storage stSyncedTmp h.pid tmpFd
            have hTmpPresent :
                assocLookup stClosedTmp.kernel.dirInode.unsyncedEntries tmpPath =
                  some (.regular tmpIno) := by
              dsimp only [stClosedTmp]
              rw [hClosedSameStorage.1]
              simp [stSyncedTmp, stWritten, stCreated]
            have hRnEq :
                posixRename stClosedTmp (walTmpPath h.basePath) h.basePath =
                  .ok { stClosedTmp with
                         kernel := { stClosedTmp.kernel with
                                      dirInode := { unsyncedEntries :=
                                                      (if tmpPath == h.basePath then
                                                         assocInsert h.basePath (.regular tmpIno)
                                                           stClosedTmp.kernel.dirInode.unsyncedEntries
                                                       else
                                                         assocErase tmpPath
                                                           (assocInsert h.basePath (.regular tmpIno)
                                                             stClosedTmp.kernel.dirInode.unsyncedEntries)) } } } := by
              change posixRename stClosedTmp tmpPath h.basePath = _
              rw [posixRename.public_eq_1]; rw [hTmpPresent]
            rw [hRnEq] at hOk
            dsimp only at hOk
            cases hFailDir : faults.failParentSync with
            | true =>
              rw [hFailDir] at hOk
              rw [posixSyncParentDir.public_eq_1] at hOk
              simp only [↓reduceIte] at hOk
              cases (Prod.mk.inj (Prod.mk.inj hOk).2).2
            | false =>
              rw [hFailDir] at hOk
              rw [posixSyncParentDir.public_eq_1] at hOk
              simp only [Bool.false_eq_true, ↓reduceIte] at hOk
              have hStEq := (Prod.mk.inj hOk).1
              have hHEq := (Prod.mk.inj (Prod.mk.inj hOk).2).1
              have hRecEq : Except.ok newRec = Except.ok committedRec :=
                (Prod.mk.inj (Prod.mk.inj hOk).2).2
              injection hRecEq with hRecEq'
              subst hStEq hHEq hRecEq'
              have hTmpBeqBase : (tmpPath == h.basePath) = false := by
                cases hB : (tmpPath == h.basePath)
                · rfl
                · exfalso; exact walTmpPath_ne_base h.basePath (eq_of_beq hB)
              refine ⟨rfl, rfl, ?_⟩
              rcases hClosedSameStorage with ⟨hDi, hPgC, hDrC, hNdC⟩
              refine ⟨?_, hLock64, hNonceLen, hNewWf, hGidEqH, hNewVer, rfl, ?_, ?_, ?_, ?_, ?_,
                tmpIno, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · dsimp only [stClosedTmp]; rw [hNdC]; exact Nat.lt_succ_of_lt hLockLt
              · dsimp only; rw [hTmpBeqBase]
                simp only [Bool.false_eq_true, ↓reduceIte, assocLookup_erase, hTmpNeLock,
                  assocLookup_insert, hBaseNeLock]
                dsimp only [stClosedTmp]; rw [hDi]
                simp [stSyncedTmp, stWritten, stCreated, stCleanTmp, posixUnlinkIfPresent, hTmpNeLock, hLockMem]
              · dsimp only; rw [hTmpBeqBase]
                simp only [Bool.false_eq_true, ↓reduceIte, assocLookup_erase, hTmpNeLock,
                  assocLookup_insert, hBaseNeLock]
                dsimp only [stClosedTmp]; rw [hDi]
                simp [stSyncedTmp, stWritten, stCreated, stCleanTmp, posixUnlinkIfPresent, hTmpNeLock, hLockMem]
              · dsimp only [stClosedTmp]; rw [hPgC]; simp [stSyncedTmp, stWritten, hLockNeTmp, hLockPg]
              · dsimp only [stClosedTmp]; rw [hDrC]; simp [stSyncedTmp, hLockNeTmp, hLockDrv]
              · dsimp only [stClosedTmp]; rw [hNdC]; simp [stSyncedTmp, stWritten, stCreated, hLockNeTmp, hLockNandBytes]
              · dsimp only [stClosedTmp]; rw [hNdC]; simp [stSyncedTmp, stWritten, stCreated]
              · dsimp only; rw [hTmpBeqBase]
                simp only [Bool.false_eq_true, ↓reduceIte, assocLookup_erase, hTmpNeBase, assocLookup_insert_self]
              · dsimp only; rw [hTmpBeqBase]
                simp only [Bool.false_eq_true, ↓reduceIte, assocLookup_erase, hTmpNeBase, assocLookup_insert_self]
              · dsimp only [stClosedTmp]; rw [hPgC]; simp [stSyncedTmp]
              · dsimp only [stClosedTmp]; rw [hDrC]; simp [stSyncedTmp]
              · dsimp only [stClosedTmp]; rw [hNdC]; simp [stSyncedTmp]

/-- Structural soundness of `openExisting` on ANY arbitrary filesystem state (`openExisting_sound`):
    Whenever `openExisting` returns `.ok (h, rec)`, `rec` is well-formed, matches `expectedVaultKeyId`
    and `h.lockGenesisId`, `h` acquires a fresh `OpenDescriptionId` (`st.kernel.openFds.nextDescId`)
    holding `flock` on `h.lockInode`, and either `rec.body ∈ honestBodies` or `MacForgery` occurred! -/
theorem openExisting_sound {st st' : PosixFsState} {pid : Pid} {basePath : DirName}
    {expectedVaultKeyId : List UInt8} {macFn : KeyedMacFn} {macKey : List UInt8}
    {h : LockedVaultHandle} {rec : WalRecord}
    (honestBodies : List WalRecordBody)
    (hOpen : openExisting st pid basePath expectedVaultKeyId macFn macKey = (st', .ok (h, rec))) :
    h.pid = pid ∧
    h.basePath = basePath ∧
    h.vaultKeyId = expectedVaultKeyId ∧
    h.ioPoisoned = false ∧
    h.lockDescId = st.kernel.openFds.nextDescId ∧
    (st.kernel.flockTable.owner h.lockInode = none ∨
     st.kernel.flockTable.owner h.lockInode = some st.kernel.openFds.nextDescId) ∧
    (∃ nonce : List UInt8,
      nonce.length = 32 ∧
      h.lockInode < 2 ^ 64 ∧
      h.lockGenesisId = computeLockGenesisId h.lockInode nonce) ∧
    rec.WellFormed ∧
    rec.body.vaultKeyId = expectedVaultKeyId ∧
    rec.body.lockGenesisId = h.lockGenesisId ∧
    verifyWalMac macFn macKey rec = true ∧
    (rec.body ∈ honestBodies ∨ MacForgery macFn macKey honestBodies rec) := by
  unfold openExisting at hOpen
  cases hOp1 : posixOpenExistingNoFollow st pid (walLockPath basePath) true with
  | error e => rw [hOp1] at hOpen; cases (Prod.mk.inj hOpen).2
  | ok p1 =>
    rcases p1 with ⟨st1, lockFd⟩
    rw [hOp1] at hOpen
    dsimp only at hOpen
    rw [posixOpenExistingNoFollow.public_eq_1] at hOp1
    cases hRes1 : resolveDentryNoFollow st.kernel.dirInode.unsyncedEntries (walLockPath basePath) with
    | error e => rw [hRes1] at hOp1; cases hOp1
    | ok ino1 =>
      rw [hRes1] at hOp1
      injection hOp1 with hP1
      rcases Prod.mk.inj hP1 with ⟨hSt1Eq, hLockFdEq⟩
      cases hFlk : posixFlockExNb st1 pid lockFd with
      | error e => rw [hFlk] at hOpen; cases (Prod.mk.inj hOpen).2
      | ok st2 =>
        rw [hFlk] at hOpen
        dsimp only at hOpen
        have hFlkFacts :
            posixFstatDescAndInode st2 pid lockFd = .ok (st.kernel.openFds.nextDescId, ino1) ∧
            (st.kernel.flockTable.owner ino1 = none ∨
             st.kernel.flockTable.owner ino1 = some st.kernel.openFds.nextDescId) := by
          subst hSt1Eq hLockFdEq
          rw [posixFlockExNb.public_eq_1] at hFlk
          simp only [resolveOpenFd_insert_self] at hFlk
          cases hOwn : st.kernel.flockTable.owner ino1 with
          | none =>
            rw [hOwn] at hFlk
            injection hFlk with hSt2Eq
            rw [← hSt2Eq]
            exact ⟨by simp [posixFstatDescAndInode.public_eqs, resolveOpenFd_insert_self], Or.inl rfl⟩
          | some holderDesc =>
            rw [hOwn] at hFlk
            dsimp only at hFlk
            by_cases hHold : (holderDesc == st.kernel.openFds.nextDescId) = true
            · simp only [hHold, ↓reduceIte] at hFlk
              injection hFlk with hSt2Eq
              rw [← hSt2Eq]
              exact ⟨by simp [posixFstatDescAndInode.public_eqs, resolveOpenFd_insert_self],
                     Or.inr (congrArg some (eq_of_beq hHold))⟩
            · simp only [hHold, Bool.false_eq_true, ↓reduceIte] at hFlk
              cases hFlk
        rw [hFlkFacts.1] at hOpen
        cases hPr1 : posixPreadAll st2 pid lockFd with
        | error e => rw [hPr1] at hOpen; cases (Prod.mk.inj hOpen).2
        | ok rawLockBytes =>
          rw [hPr1] at hOpen
          dsimp only at hOpen
          cases hDecLock : decodeLockSidecar rawLockBytes with
          | none => rw [hDecLock] at hOpen; cases (Prod.mk.inj hOpen).2
          | some lockSeal =>
            rw [hDecLock] at hOpen
            dsimp only at hOpen
            by_cases hInoMismatch : (ino1 != lockSeal.sealedLockInode) = true
            · simp only [hInoMismatch, ↓reduceIte] at hOpen; cases (Prod.mk.inj hOpen).2
            · simp only [hInoMismatch, Bool.false_eq_true, ↓reduceIte] at hOpen
              have hInoEqSeal : ino1 = lockSeal.sealedLockInode :=
                eq_of_not_bne_true hInoMismatch
              obtain ⟨⟨hSeal64, hSealNonceLen⟩, _⟩ := decodeLockSidecar_canonical hDecLock
              cases hOp2 : posixOpenExistingNoFollow st2 pid basePath false with
              | error e => rw [hOp2] at hOpen; cases (Prod.mk.inj hOpen).2
              | ok p2 =>
                rcases p2 with ⟨st3, recFd⟩
                rw [hOp2] at hOpen
                dsimp only at hOpen
                cases hPr2 : posixPreadAll st3 pid recFd with
                | error e => rw [hPr2] at hOpen; cases (Prod.mk.inj hOpen).2
                | ok rawRecBytes =>
                  rw [hPr2] at hOpen
                  dsimp only at hOpen
                  cases hDecRec : decodeWalRecord rawRecBytes with
                  | none => rw [hDecRec] at hOpen; cases (Prod.mk.inj hOpen).2
                  | some recVal =>
                    rw [hDecRec] at hOpen
                    dsimp only at hOpen
                    by_cases hGidMis :
                        (recVal.body.lockGenesisId !=
                          computeLockGenesisId ino1 lockSeal.genesisNonce) = true
                    · simp only [hGidMis, ↓reduceIte] at hOpen; cases (Prod.mk.inj hOpen).2
                    · simp only [hGidMis, Bool.false_eq_true, ↓reduceIte] at hOpen
                      by_cases hMacMis :
                          (recVal.body.vaultKeyId != expectedVaultKeyId ||
                           !(verifyWalMac macFn macKey recVal)) = true
                      · simp only [hMacMis, ↓reduceIte] at hOpen; cases (Prod.mk.inj hOpen).2
                      · simp only [hMacMis, Bool.false_eq_true, ↓reduceIte] at hOpen
                        have hOkPair := (Prod.mk.inj hOpen).2
                        injection hOkPair with hTuple
                        rcases Prod.mk.inj hTuple with ⟨hHEq, hRecEq⟩
                        subst hHEq hRecEq
                        obtain ⟨hRecWf, _⟩ := decodeWalRecord_canonical hDecRec
                        have hGidEq : recVal.body.lockGenesisId =
                            computeLockGenesisId ino1 lockSeal.genesisNonce :=
                          eq_of_not_bne_true hGidMis
                        have hVkNotBne : ¬(recVal.body.vaultKeyId != expectedVaultKeyId) = true := by
                          intro hc; apply hMacMis; simp [hc]
                        have hVkEq : recVal.body.vaultKeyId = expectedVaultKeyId :=
                          eq_of_not_bne_true hVkNotBne
                        have hVerTrue : verifyWalMac macFn macKey recVal = true := by
                          cases hV : verifyWalMac macFn macKey recVal
                          · exfalso; apply hMacMis; simp [hV]
                          · rfl
                        refine ⟨rfl, rfl, rfl, rfl, rfl, hFlkFacts.2,
                          ⟨lockSeal.genesisNonce, hSealNonceLen, hInoEqSeal ▸ hSeal64, rfl⟩,
                          hRecWf, hVkEq, hGidEq, hVerTrue,
                          verifyWalMac_authentic_or_macForgery hRecWf hVerTrue⟩

/-- **FLAGSHIP THEOREM 1 (`power_loss_preserves_committed_or_prior_record`)**:
    1. **Zero Torn/Garbage/Zero-Length Exposure Across All Micro-Steps**:
       For **every** intermediate state `mid ∈ replaceAtomicSteps` and **every** `CrashStep mid crashed`
       (`KernelPanicCrash` or `PowerLossCrash` under arbitrary `512B`/`4KiB` `SectorTearMask` and
       `DirCrashOutcome`), post-crash `openExisting` deterministically succeeds and recovers
       **either** exact `oldRec` (`oldState`) **or** exact `newRec` (`newState`), and `CrashInv` is
       idempotent under arbitrary repeated crashes during recovery (`CrashHoareSpec`)!
    2. **Post-Commit Strict Durability**:
       Once `replaceAtomic` returns `.ok committedRec`, after **any** `CrashStep`, recovery yields
       **exact `committedRec`**!
    3. **Tamper / Forgery Boundary**:
       Even on an adversarially modified disk, any accepted `openExisting` record belongs to the
       vault's authenticated history `[oldRec.body, newRec.body]` or constructively witnesses
       `MacForgery`! -/
theorem power_loss_preserves_committed_or_prior_record
    {st : PosixFsState} {h : LockedVaultHandle}
    {lockIno : InodeId} {genesisNonce : List UInt8}
    {macFn : KeyedMacFn} (hMacWf : WellFormedMacFn macFn) {macKey : List UInt8}
    {oldRec : WalRecord} {newEpoch : Nat} (hEpLt : newEpoch < 2 ^ 64)
    {newPayload : List UInt8} (hPayLt : newPayload.length < 2 ^ 32)
    (faults : IoFaultSchedule) (recoverPid : Pid)
    (hVkEqH : h.vaultKeyId = oldRec.body.vaultKeyId)
    (hGidEqH : h.lockGenesisId = computeLockGenesisId lockIno genesisNonce)
    (hDur : VaultDurableAt st h.basePath lockIno genesisNonce macFn macKey oldRec) :
    let newRec := signWalRecord macFn macKey
      { vaultKeyId := h.vaultKeyId
        lockGenesisId := h.lockGenesisId
        epoch := newEpoch
        payload := newPayload }
    -- (1) Every intermediate state crashes ONLY to exact `oldRec` or exact `newRec` (idempotently!):
    (∀ mid crashed,
      mid ∈ replaceAtomicSteps st h newEpoch newPayload macFn macKey faults →
      CrashStep mid crashed →
      (∃ stRec hOut,
        openExisting crashed recoverPid h.basePath oldRec.body.vaultKeyId macFn macKey =
          (stRec, .ok (hOut, oldRec))) ∨
      (∃ stRec hOut,
        openExisting crashed recoverPid h.basePath oldRec.body.vaultKeyId macFn macKey =
          (stRec, .ok (hOut, newRec)))) ∧
    -- (2) Once `replaceAtomic` returns `.ok committedRec`, every crash recovers exact `committedRec`:
    (∀ stPost hPost committedRec crashed,
      replaceAtomic st h newEpoch newPayload macFn macKey faults =
        (stPost, hPost, .ok committedRec) →
      CrashStep stPost crashed →
      committedRec = newRec ∧
      ∃ stRec hOut,
        openExisting crashed recoverPid h.basePath oldRec.body.vaultKeyId macFn macKey =
          (stRec, .ok (hOut, committedRec))) ∧
    -- (3) Against arbitrary untrusted disk bytes, `openExisting` yields `{oldRec, newRec}` or `MacForgery`:
    (∀ anyDisk stAfter hOut recOut,
      openExisting anyDisk recoverPid h.basePath oldRec.body.vaultKeyId macFn macKey =
        (stAfter, .ok (hOut, recOut)) →
      recOut.body = oldRec.body ∨ recOut.body = newRec.body ∨
      MacForgery macFn macKey [oldRec.body, newRec.body] recOut) := by
  intro newRec
  refine ⟨?_, ?_, ?_⟩
  · intro mid crashed hMid hCrash
    have hWin := replaceAtomicSteps_all_in_window hMacWf hEpLt hPayLt faults hVkEqH hGidEqH hDur hMid
    obtain ⟨hFdsEmpty, hFlkEmpty, hCases⟩ := crashStep_preserves_window_to_durable hWin hCrash
    rcases hCases with hDurOld | hDurNew
    · exact Or.inl (openExisting_of_crashed_durable recoverPid hFdsEmpty hFlkEmpty hDurOld)
    · have hRecOpen := openExisting_of_crashed_durable recoverPid hFdsEmpty hFlkEmpty hDurNew
      have hVkNew : newRec.body.vaultKeyId = oldRec.body.vaultKeyId := hVkEqH
      rw [hVkNew] at hRecOpen
      exact Or.inr hRecOpen
  · intro stPost hPost committedRec crashed hOk hCrash
    obtain ⟨_, hComEq, hDurPost⟩ := replaceAtomic_ok_durable hMacWf hVkEqH hGidEqH hDur hOk
    have hWinPost := vaultDurableAt_to_window hDurPost hDurPost.2.2.2.1 rfl hDurPost.2.2.2.2.1 hDurPost.2.2.2.2.2.1
    obtain ⟨hFdsE, hFlkE, hPostCases⟩ := crashStep_preserves_window_to_durable hWinPost hCrash
    have hDurCrash : VaultDurableAt crashed h.basePath lockIno genesisNonce macFn macKey committedRec := by
      rcases hPostCases with hA | hA <;> exact hA
    have hRecOpen := openExisting_of_crashed_durable recoverPid hFdsE hFlkE hDurCrash
    have hVkCom : committedRec.body.vaultKeyId = oldRec.body.vaultKeyId := by
      rw [hComEq]; exact hVkEqH
    rw [hVkCom] at hRecOpen
    exact ⟨hComEq, hRecOpen⟩
  · intro anyDisk stAfter hOut recOut hOpen
    rcases openExisting_sound [oldRec.body, newRec.body] hOpen with
      ⟨_, _, _, _, _, _, _, _, _, _, _, hAuthOrForge⟩
    rcases hAuthOrForge with hMem | hForge
    · rcases List.mem_cons.mp hMem with hOld | hRest
      · exact Or.inl hOld
      · rcases List.mem_cons.mp hRest with hNew | hNil
        · exact Or.inr (Or.inl hNew)
        · cases hNil
    · exact Or.inr (Or.inr hForge)

/-- Packaging `replaceAtomic` into a full idempotent `CrashHoareSpec`! -/
theorem replaceAtomic_crashHoareSpec
    {h : LockedVaultHandle} {lockIno : InodeId} {genesisNonce : List UInt8}
    {macFn : KeyedMacFn} (hMacWf : WellFormedMacFn macFn) {macKey : List UInt8}
    {oldRec : WalRecord} {newEpoch : Nat} (hEpLt : newEpoch < 2 ^ 64)
    {newPayload : List UInt8} (hPayLt : newPayload.length < 2 ^ 32)
    (faults : IoFaultSchedule)
    (hVkEqH : h.vaultKeyId = oldRec.body.vaultKeyId)
    (hGidEqH : h.lockGenesisId = computeLockGenesisId lockIno genesisNonce) :
    let newRec := signWalRecord macFn macKey
      { vaultKeyId := h.vaultKeyId, lockGenesisId := h.lockGenesisId,
        epoch := newEpoch, payload := newPayload }
    CrashHoareSpec
      (fun st => VaultDurableAt st h.basePath lockIno genesisNonce macFn macKey oldRec)
      (fun st => replaceAtomicSteps st h newEpoch newPayload macFn macKey faults)
      (fun st =>
        let (st', _, res) := replaceAtomic st h newEpoch newPayload macFn macKey faults
        (st', res))
      (fun st' out => out = newRec ∧ VaultDurableAt st' h.basePath lockIno genesisNonce macFn macKey newRec)
      (fun crashed =>
        crashed.kernel.openFds = {} ∧ crashed.kernel.flockTable = {} ∧
        (VaultDurableAt crashed h.basePath lockIno genesisNonce macFn macKey oldRec ∨
         VaultDurableAt crashed h.basePath lockIno genesisNonce macFn macKey newRec)) := by
  intro newRec
  refine { normal_post := ?_, crash_safe := ?_, crash_idempotent := ?_ }
  · intro st st' out hPre hRun
    dsimp only at hRun
    cases hRep : replaceAtomic st h newEpoch newPayload macFn macKey faults with
    | mk sA rest =>
      cases rest with
      | mk hA resA =>
        rw [hRep] at hRun
        dsimp only at hRun
        rcases Prod.mk.inj hRun with ⟨rfl, hResEq⟩
        cases resA with
        | error e => cases hResEq
        | ok recA =>
          injection hResEq with hRecEq
          subst hRecEq
          obtain ⟨_, hComEq, hDurPost⟩ := replaceAtomic_ok_durable hMacWf hVkEqH hGidEqH hPre hRep
          rw [hComEq] at hDurPost
          exact ⟨hComEq, hDurPost⟩
  · intro st mid crashed hPre hMid hCrash
    have hWin := replaceAtomicSteps_all_in_window hMacWf hEpLt hPayLt faults hVkEqH hGidEqH hPre hMid
    exact crashStep_preserves_window_to_durable hWin hCrash
  · intro s₁ s₂ hInv₁ hCrash₂
    rcases hInv₁ with ⟨_, _, hCases⟩
    rcases hCases with hDurOld | hDurNew
    · have hNewWf : newRec.WellFormed := signWalRecord_wellFormed hMacWf macKey
        ⟨hVkEqH ▸ hDurOld.2.2.2.1.1.1, hGidEqH ▸ computeLockGenesisId_length hDurOld.2.2.1, hEpLt, hPayLt⟩
      have hW := vaultDurableAt_to_window hDurOld hNewWf hVkEqH hGidEqH (verifyWalMac_signWalRecord _ _ _)
      exact crashStep_preserves_window_to_durable hW hCrash₂
    · have hW : VaultCrashSafeWindow s₁ h.basePath lockIno genesisNonce macFn macKey newRec newRec :=
        vaultDurableAt_to_window hDurNew hDurNew.2.2.2.1 rfl hDurNew.2.2.2.2.1 hDurNew.2.2.2.2.2.1
      obtain ⟨hF, hFl, hC⟩ := crashStep_preserves_window_to_durable hW hCrash₂
      rcases hC with hN | hN <;> exact ⟨hF, hFl, Or.inr hN⟩

/-- External `.lock` unlink + new `.lock` inode creation sequence (with **arbitrary** attacker-chosen
    sidecar bytes, including even a byte-for-byte copy of Process 1's `.lock` seal!). -/
def externalUnlinkAndRecreateLock (st : PosixFsState) (actorPid : Pid)
    (basePath : DirName) (arbitraryNewLockBytes : List UInt8) : PosixFsState :=
  match posixCreateExclNoFollow (posixUnlinkIfPresent st (walLockPath basePath))
          actorPid (walLockPath basePath) with
  | .error _ => posixUnlinkIfPresent st (walLockPath basePath)
  | .ok (stCr, fdNew, _) =>
    match posixSyncAllMedia
            ((posixPwriteAll stCr actorPid fdNew arbitraryNewLockBytes).toOption.getD stCr)
            actorPid fdNew false with
    | (stSy, _) =>
      match posixSyncParentDir stSy false with
      | (stDir, _) => (posixCloseFd stDir actorPid fdNew).toOption.getD stDir

/-- **FLAGSHIP THEOREM 2 (`dual_bound_lock_prevents_unlink_recreate_split_brain`)**:
    Suppose Process 1 (`h₁.pid`) holds an active `LockedVaultHandle` `h₁` (`h₁.IsActiveIn st`)
    whose `lockGenesisId = computeLockGenesisId h₁.lockInode genesisNonce₁` (`h₁.lockInode < 2^64`).
    1. **Universal Mutual Exclusion Across Arbitrary Filesystem Tampering (Cross- & Same-Process!)**:
       Because `flock(2)` is owned by kernel `OpenDescriptionId` (`h₁.lockDescId < nextDescId`),
       in `st` (and after `externalUnlinkAndRecreateLock` with **any** attacker-chosen `.lock` bytes!),
       **NO** second `openExisting` call by **any** `pid₂` (**even `pid₂ = h₁.pid` in the same process!**)
       can EVER succeed unless `MacForgery` occurs against `honestBodies`!
    2. **Unconditional Refusal Without `MacForgery`**:
       For each candidate `rec₂`, absence of its fresh-valid-tag event excludes returning
       that candidate. This is not a universal nonexistence assumption about valid tags. -/
theorem dual_bound_lock_prevents_unlink_recreate_split_brain
    {st : PosixFsState} {h₁ : LockedVaultHandle} {genesisNonce₁ : List UInt8}
    {macFn : KeyedMacFn} {macKey : List UInt8}
    (honestBodies : List WalRecordBody)
    (hActive₁ : h₁.IsActiveIn st)
    (hIno₁Lt64 : h₁.lockInode < 2 ^ 64)
    (hGid₁ : h₁.lockGenesisId = computeLockGenesisId h₁.lockInode genesisNonce₁)
    (hHonestPin : ∀ b ∈ honestBodies, b.vaultKeyId = h₁.vaultKeyId → b.lockGenesisId = h₁.lockGenesisId) :
    -- (A) In ANY state `stCur` retaining `h₁.lockDescId < nextDescId` and `flock` on `h₁.lockInode`,
    --     NO caller `pid₂ : Pid` (not even `pid₂ = h₁.pid`!) can open a second active handle:
    (∀ (stCur stAfter : PosixFsState) (pid₂ : Pid) (h₂ : LockedVaultHandle) (rec₂ : WalRecord),
      h₁.lockDescId < stCur.kernel.openFds.nextDescId →
      stCur.kernel.flockTable.owner h₁.lockInode = some h₁.lockDescId →
      openExisting stCur pid₂ h₁.basePath h₁.vaultKeyId macFn macKey = (stAfter, .ok (h₂, rec₂)) →
      MacForgery macFn macKey honestBodies rec₂) ∧
    -- (B) Specifically, after `externalUnlinkAndRecreateLock` with ANY bytes, `h₁` retains its `flock`
    --     on `h₁.lockInode` (when `h₁.lockInode < st.nand.nextInode`) and EVERY `pid₂ : Pid` is rejected!
    (∀ (actorPid pid₂ : Pid) (spoofBytes : List UInt8),
      h₁.lockInode < st.nand.nextInode →
      let stTampered := externalUnlinkAndRecreateLock st actorPid h₁.basePath spoofBytes
      h₁.lockDescId < stTampered.kernel.openFds.nextDescId ∧
      stTampered.kernel.flockTable.owner h₁.lockInode = some h₁.lockDescId ∧
      ∀ stAfter h₂ rec₂,
        ¬ MacForgery macFn macKey honestBodies rec₂ →
        openExisting stTampered pid₂ h₁.basePath h₁.vaultKeyId macFn macKey ≠
          (stAfter, .ok (h₂, rec₂))) := by
  have hCore :
      ∀ (stCur stAfter : PosixFsState) (pid₂ : Pid) (h₂ : LockedVaultHandle) (rec₂ : WalRecord),
        h₁.lockDescId < stCur.kernel.openFds.nextDescId →
        stCur.kernel.flockTable.owner h₁.lockInode = some h₁.lockDescId →
        openExisting stCur pid₂ h₁.basePath h₁.vaultKeyId macFn macKey = (stAfter, .ok (h₂, rec₂)) →
        MacForgery macFn macKey honestBodies rec₂ := by
    intro stCur stAfter pid₂ h₂ rec₂ hDescLt hOwner₁ hOpen₂
    rcases openExisting_sound honestBodies hOpen₂ with
      ⟨_, _, _, _, _, hFlk₂, ⟨nonce₂, _, hIno₂Lt64, hGid₂⟩,
       _, hVk₂, hRecGid₂, _, hAuthOrForge⟩
    have hInoNe : h₂.lockInode ≠ h₁.lockInode := by
      intro hEqIno
      rw [hEqIno, hOwner₁] at hFlk₂
      rcases hFlk₂ with hNone | hSome
      · cases hNone
      · injection hSome with hEqDesc
        exact (Nat.ne_of_lt hDescLt) hEqDesc
    rcases hAuthOrForge with hMem | hForge
    · exfalso
      have hPin := hHonestPin rec₂.body hMem hVk₂
      rw [hRecGid₂, hGid₂, hGid₁] at hPin
      have hSameIno := (computeLockGenesisId_injective hIno₂Lt64 hIno₁Lt64 hPin).1
      exact hInoNe hSameIno
    · exact hForge
  refine ⟨hCore, ?_⟩
  intro actorPid pid₂ spoofBytes hInoLtNext
  dsimp only
  let lockPath := walLockPath h₁.basePath
  have hDescOrig : h₁.lockDescId < st.kernel.openFds.nextDescId := hActive₁.2.1
  have hOwnerOrig : st.kernel.flockTable.owner h₁.lockInode = some h₁.lockDescId := hActive₁.2.2.2
  have hTamperedLock :
      let stTampered := externalUnlinkAndRecreateLock st actorPid h₁.basePath spoofBytes
      h₁.lockDescId < stTampered.kernel.openFds.nextDescId ∧
      stTampered.kernel.flockTable.owner h₁.lockInode = some h₁.lockDescId := by
    dsimp only
    unfold externalUnlinkAndRecreateLock
    have hAbs : assocLookup (posixUnlinkIfPresent st lockPath).kernel.dirInode.unsyncedEntries lockPath = none := by
      simp [posixUnlinkIfPresent]
    let newDescId := st.kernel.openFds.nextDescId
    let newIno := st.nand.nextInode
    let newFd := st.nextFd
    have hCr :
        posixCreateExclNoFollow (posixUnlinkIfPresent st lockPath) actorPid lockPath =
          .ok ({ kernel := { (posixUnlinkIfPresent st lockPath).kernel with
                              openFds := { fdRefs := assocInsert (actorPid, newFd) newDescId st.kernel.openFds.fdRefs
                                           descriptions := assocInsert newDescId
                                                             { inode := newIno, writable := true, stickyFsyncErr := false }
                                                             st.kernel.openFds.descriptions
                                           nextDescId := newDescId + 1 }
                              dirInode := { unsyncedEntries :=
                                              assocInsert lockPath (.regular newIno)
                                                (posixUnlinkIfPresent st lockPath).kernel.dirInode.unsyncedEntries } }
                 driveCache := st.driveCache
                 nand := { st.nand with
                            fileBlocks := assocInsert newIno [] st.nand.fileBlocks
                            nextInode := newIno + 1 }
                 nextFd := newFd + 1 }, newFd, newIno) := by
      rw [posixCreateExclNoFollow.public_eq_1]; rw [hAbs]; rfl
    rw [hCr]
    dsimp only [posixUnlinkIfPresent]
    have hInoNeNew : h₁.lockInode ≠ newIno := Nat.ne_of_lt hInoLtNext
    have hDescLtNext : h₁.lockDescId < newDescId + 1 := Nat.lt_succ_of_lt hDescOrig
    rw [posixPwriteAll.public_eq_1]
    simp only [resolveOpenFd_insert_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    dsimp only [Except.toOption, Option.getD]
    rw [posixSyncAllMedia.public_eq_1]
    unfold readInodeHierarchy
    unfold pendingVolatileWrite
    simp only [resolveOpenFd_insert_self, Bool.false_eq_true, ↓reduceIte, assocLookup_insert_self]
    rw [posixSyncParentDir.public_eq_1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [posixCloseFd.public_eq_1]
    simp only [assocLookup_insert_self]
    by_cases hStillRef :
        descHasAnyRef (assocErase (actorPid, newFd)
          (assocInsert (actorPid, newFd) newDescId st.kernel.openFds.fdRefs)) newDescId = true
    · simp only [hStillRef, ↓reduceIte]
      exact ⟨hDescLtNext, hOwnerOrig⟩
    · simp only [hStillRef, Bool.false_eq_true, ↓reduceIte]
      by_cases hFlkNew : (assocLookup st.kernel.flockTable.locks newIno == some newDescId) = true
      · simp only [hFlkNew, ↓reduceIte]
        dsimp only [Except.toOption, Option.getD, FlockTable.owner]
        simp only [assocLookup_erase, hInoNeNew, ↓reduceIte]
        exact ⟨hDescLtNext, hOwnerOrig⟩
      · simp only [hFlkNew, Bool.false_eq_true, ↓reduceIte]
        exact ⟨hDescLtNext, hOwnerOrig⟩
  refine ⟨hTamperedLock.1, hTamperedLock.2, ?_⟩
  intro stAfter h₂ rec₂ hNoForge hOpenOk
  exact hNoForge (hCore _ _ pid₂ h₂ rec₂ hTamperedLock.1 hTamperedLock.2 hOpenOk)

#export_eqns openExisting replaceAtomic provisionGenesis replaceAtomicSteps closeVaultHandle externalUnlinkAndRecreateLock

theorem openExisting_err_preserves_storage
    {st st' : PosixFsState} {pid : Pid} {basePath : DirName}
    {vkId : List UInt8} {macFn : KeyedMacFn} {macKey : List UInt8} {err : PosixErr}
    (hErr : openExisting st pid basePath vkId macFn macKey = (st', .error err)) :
    st'.kernel.dirInode = st.kernel.dirInode ∧
    st'.kernel.pageCache = st.kernel.pageCache ∧
    st'.driveCache = st.driveCache ∧
    st'.nand = st.nand := by
  have hOpenKeep : ∀ (sA sB : PosixFsState) (p : Pid) (nm : DirName) (w : Bool) (fd : FdId),
      posixOpenExistingNoFollow sA p nm w = .ok (sB, fd) →
      sB.kernel.dirInode = sA.kernel.dirInode ∧
      sB.kernel.pageCache = sA.kernel.pageCache ∧
      sB.driveCache = sA.driveCache ∧ sB.nand = sA.nand := by
    intro sA sB p nm w fd hO
    rw [posixOpenExistingNoFollow.public_eq_1] at hO
    cases hR : resolveDentryNoFollow sA.kernel.dirInode.unsyncedEntries nm with
    | error e => rw [hR] at hO; cases hO
    | ok ino =>
      rw [hR] at hO; injection hO with hP; rw [← (Prod.mk.inj hP).1]; exact ⟨rfl, rfl, rfl, rfl⟩
  rw [openExisting.public_eq_1] at hErr
  cases hOp1 : posixOpenExistingNoFollow st pid (walLockPath basePath) true with
  | error _ => rw [hOp1] at hErr; rw [← (Prod.mk.inj hErr).1]; exact ⟨rfl, rfl, rfl, rfl⟩
  | ok p1 =>
    rcases p1 with ⟨st1, lockFd⟩
    have hs1 := hOpenKeep _ _ _ _ _ _ hOp1
    rw [hOp1] at hErr; dsimp only at hErr
    cases hFlk : posixFlockExNb st1 pid lockFd with
    | error _ =>
      rw [hFlk] at hErr; rw [← (Prod.mk.inj hErr).1]
      have hc := posixCloseFd_preserves_storage st1 pid lockFd
      exact ⟨hc.1.trans hs1.1, hc.2.1.trans hs1.2.1, hc.2.2.1.trans hs1.2.2.1, hc.2.2.2.trans hs1.2.2.2⟩
    | ok st2 =>
      have hs2_1 := posixFlockExNb_preserves_storage hFlk
      have hs2 : st2.kernel.dirInode = st.kernel.dirInode ∧
                 st2.kernel.pageCache = st.kernel.pageCache ∧
                 st2.driveCache = st.driveCache ∧ st2.nand = st.nand :=
        ⟨hs2_1.1.trans hs1.1, hs2_1.2.1.trans hs1.2.1,
         hs2_1.2.2.1.trans hs1.2.2.1, hs2_1.2.2.2.trans hs1.2.2.2⟩
      rw [hFlk] at hErr; dsimp only at hErr
      have hc2 := posixCloseFd_preserves_storage st2 pid lockFd
      have hClosed2 :
          ((posixCloseFd st2 pid lockFd).toOption.getD st2).kernel.dirInode = st.kernel.dirInode ∧
          ((posixCloseFd st2 pid lockFd).toOption.getD st2).kernel.pageCache = st.kernel.pageCache ∧
          ((posixCloseFd st2 pid lockFd).toOption.getD st2).driveCache = st.driveCache ∧
          ((posixCloseFd st2 pid lockFd).toOption.getD st2).nand = st.nand :=
        ⟨hc2.1.trans hs2.1, hc2.2.1.trans hs2.2.1, hc2.2.2.1.trans hs2.2.2.1, hc2.2.2.2.trans hs2.2.2.2⟩
      cases hFst : posixFstatDescAndInode st2 pid lockFd with
      | error _ => rw [hFst] at hErr; rw [← (Prod.mk.inj hErr).1]; exact hClosed2
      | ok dIno =>
        rcases dIno with ⟨_, ino⟩
        cases hPr1 : posixPreadAll st2 pid lockFd with
        | error _ => rw [hFst, hPr1] at hErr; rw [← (Prod.mk.inj hErr).1]; exact hClosed2
        | ok rawL =>
          rw [hFst, hPr1] at hErr; dsimp only at hErr
          cases hDL : decodeLockSidecar rawL with
          | none => rw [hDL] at hErr; rw [← (Prod.mk.inj hErr).1]; exact hClosed2
          | some ls =>
            rw [hDL] at hErr; dsimp only at hErr
            by_cases hM1 : (ino != ls.sealedLockInode) = true
            · simp only [hM1, ↓reduceIte] at hErr; rw [← (Prod.mk.inj hErr).1]; exact hClosed2
            · simp only [hM1, Bool.false_eq_true, ↓reduceIte] at hErr
              cases hOp2 : posixOpenExistingNoFollow st2 pid basePath false with
              | error _ => rw [hOp2] at hErr; rw [← (Prod.mk.inj hErr).1]; exact hClosed2
              | ok p2 =>
                rcases p2 with ⟨st3, recFd⟩
                have hs3_2 := hOpenKeep _ _ _ _ _ _ hOp2
                have hs3 : st3.kernel.dirInode = st.kernel.dirInode ∧
                           st3.kernel.pageCache = st.kernel.pageCache ∧
                           st3.driveCache = st.driveCache ∧ st3.nand = st.nand :=
                  ⟨hs3_2.1.trans hs2.1, hs3_2.2.1.trans hs2.2.1,
                   hs3_2.2.2.1.trans hs2.2.2.1, hs3_2.2.2.2.trans hs2.2.2.2⟩
                let st4 := (posixCloseFd st3 pid recFd).toOption.getD st3
                have hc3 := posixCloseFd_preserves_storage st3 pid recFd
                have hc4 := posixCloseFd_preserves_storage st4 pid lockFd
                have hClosed4 :
                    ((posixCloseFd st4 pid lockFd).toOption.getD st4).kernel.dirInode = st.kernel.dirInode ∧
                    ((posixCloseFd st4 pid lockFd).toOption.getD st4).kernel.pageCache = st.kernel.pageCache ∧
                    ((posixCloseFd st4 pid lockFd).toOption.getD st4).driveCache = st.driveCache ∧
                    ((posixCloseFd st4 pid lockFd).toOption.getD st4).nand = st.nand :=
                  ⟨hc4.1.trans (hc3.1.trans hs3.1), hc4.2.1.trans (hc3.2.1.trans hs3.2.1),
                   hc4.2.2.1.trans (hc3.2.2.1.trans hs3.2.2.1), hc4.2.2.2.trans (hc3.2.2.2.trans hs3.2.2.2)⟩
                rw [hOp2] at hErr; dsimp only at hErr
                cases hPr2 : posixPreadAll st3 pid recFd with
                | error _ => rw [hPr2] at hErr; rw [← (Prod.mk.inj hErr).1]; exact hClosed4
                | ok rawR =>
                  rw [hPr2] at hErr; dsimp only at hErr
                  cases hDR : decodeWalRecord rawR with
                  | none => rw [hDR] at hErr; rw [← (Prod.mk.inj hErr).1]; exact hClosed4
                  | some recV =>
                    rw [hDR] at hErr; dsimp only at hErr
                    by_cases hG : (recV.body.lockGenesisId != computeLockGenesisId ino ls.genesisNonce) = true
                    · simp only [hG, ↓reduceIte] at hErr; rw [← (Prod.mk.inj hErr).1]; exact hClosed4
                    · simp only [hG, Bool.false_eq_true, ↓reduceIte] at hErr
                      by_cases hM : (recV.body.vaultKeyId != vkId || !(verifyWalMac macFn macKey recV)) = true
                      · simp only [hM, ↓reduceIte] at hErr; rw [← (Prod.mk.inj hErr).1]; exact hClosed4
                      · simp only [hM, Bool.false_eq_true, ↓reduceIte] at hErr
                        cases (Prod.mk.inj hErr).2

end Qsag
end
