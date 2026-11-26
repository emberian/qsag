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
