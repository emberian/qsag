module
/-
# Qsag.Exec.PlatformContractInstances — the `PosixFsState` WAL host against `Spec.PosixFsyncContract`

`Qsag.Spec.Assumptions` states the storage platform contract `PosixFsyncContract M` over an abstract
`FsyncStorageModel`. This module builds the `FsyncStorageModel` induced by the three-tier
`PosixFsState` machine of `Qsag.Exec.PosixCrashWal` and decides the contract for it.

1. `WalHost` is a process holding a `PosixFsState`, running the `replaceAtomic` syscall sequence one
   `FsyncOp` at a time: `append` = `posixUnlinkIfPresent tmp`, `posixCreateExclNoFollow tmp`,
   `posixPwriteAll` of the visible log extended by the record; `fsyncFile` = `posixSyncAllMedia`;
   `rename` = `posixRename tmp log`, refused unless the staging file is synced; `fsyncDir` =
   `posixSyncParentDir`; `crash` = the next `MidOpCrash` of an environment-chosen schedule
   (`KernelPanicCrash` or `PowerLossCrash` with any directory outcome and sector tears).
   The durable log is what the NAND directory entry and NAND blocks decode to.
2. `walModel_noRollback`, `walModel_anchorMonotone`, `walModel_anchorWitnessesDurable`: three of the
   four contract fields hold on every well-formed host state, for every trace and crash schedule.
3. `walModel_commit_appends_to_visible_log`: the commit protocol makes the durable log equal to the
   log visible before it, extended by the record. `walModel_committedRecordDurable_of_quiescent`:
   from a state in which no rename is waiting for a directory sync, exactly the record is added.
4. `walModel_commit_not_exactly_one_record`: without that hypothesis "exactly one record" is
   false: a rename that precedes a directory sync is flushed by the next directory sync, so a
   commit started in that window makes two records durable. This is why
   `Spec.PosixFsyncContract.committedRecordLast` allows pending records before the committed one.
5. `walModel_contract : PosixFsyncContract (walModel ly)`: the `PosixFsState` WAL host satisfies
   the Spec contract; `walModel_committed_survives` is the resulting crash-safety statement over
   `PosixFsState`.
-/

public import Qsag.Spec.Assumptions
public import Qsag.Exec.PosixCrashWal
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.PosixWalHost
open Qsag Qsag.Spec

set_option autoImplicit false

/-! ## 1. Log file format -/

/-- One record: every payload byte is preceded by `1`, the record ends with `0`. -/
def encodeRec : List UInt8 → List UInt8
  | [] => [0]
  | b :: r => 1 :: b :: encodeRec r

/-- The log file is the concatenation of its encoded records. -/
def encodeLog : List (List UInt8) → List UInt8
  | [] => []
  | r :: L => encodeRec r ++ encodeLog L

/-- Total parser of the log format; `cur` is the record being read. -/
def decodeLogAux : List UInt8 → List UInt8 → List (List UInt8)
  | _, [] => []
  | cur, t :: rest =>
    if t = 0 then cur :: decodeLogAux [] rest
    else
      match rest with
      | [] => []
      | b :: rest' => decodeLogAux (cur ++ [b]) rest'

def decodeLog (bs : List UInt8) : List (List UInt8) := decodeLogAux [] bs

theorem decodeLogAux_encodeRec (r : List UInt8) :
    ∀ (cur tail : List UInt8),
      decodeLogAux cur (encodeRec r ++ tail) = (cur ++ r) :: decodeLogAux [] tail := by
  induction r with
  | nil =>
    intro cur tail
    rw [encodeRec, List.cons_append, List.nil_append, decodeLogAux.eq_def]
    simp only [↓reduceIte, List.append_nil]
  | cons b r ih =>
    intro cur tail
    have h10 : ¬ ((1 : UInt8) = 0) := by decide
    simp only [encodeRec, List.cons_append, decodeLogAux, h10, ↓reduceIte, ih,
      List.append_assoc, List.cons_append, List.nil_append]

theorem decodeLog_encodeLog : ∀ (L : List (List UInt8)), decodeLog (encodeLog L) = L
  | [] => by rfl
  | r :: L => by
    have ih : decodeLogAux [] (encodeLog L) = L := decodeLog_encodeLog L
    unfold decodeLog
    rw [encodeLog, decodeLogAux_encodeRec, ih, List.nil_append]

/-! ## 2. The WAL host over `PosixFsState` -/

/-- Process and path names of the host: the log and its staging file. -/
structure WalLayout where
  pid : Pid
  log : DirName
  tmp : DirName
  distinct : tmp ≠ log

/-- Host state: the filesystem, the process-side protocol flags, the external anchor, and the
    environment's remaining crash schedule. -/
structure WalHost where
  fs : PosixFsState
  /-- Open descriptor of the staging file. -/
  staged : Option FdId
  /-- The staging file has been synced since it was written. -/
  synced : Bool
  /-- No rename has happened since the last directory sync or recovery. -/
  dirClean : Bool
  anchor : Nat
  crashes : List MidOpCrash

/-- Record list stored under `name`, for a directory view and a block view. -/
def logOf (name : DirName) (entries : List (DirName × EntryTarget))
    (blk : InodeId → Option (List UInt8)) : List (List UInt8) :=
  match assocLookup entries name with
  | some (.regular ino) =>
    match blk ino with
    | some bs => decodeLog bs
    | none => []
  | _ => []

/-- The log a recovery after a crash reads: NAND directory, NAND blocks. -/
def nandLog (ly : WalLayout) (fs : PosixFsState) : List (List UInt8) :=
  logOf ly.log fs.nand.dirNandEntries (assocLookup fs.nand.fileBlocks)

/-- The log under the kernel's directory view, NAND blocks. -/
def kernLog (ly : WalLayout) (fs : PosixFsState) : List (List UInt8) :=
  logOf ly.log fs.kernel.dirInode.unsyncedEntries (assocLookup fs.nand.fileBlocks)

/-- The log the running process reads (`open(O_NOFOLLOW)` + `pread`). -/
def visLog (ly : WalLayout) (fs : PosixFsState) : List (List UInt8) :=
  logOf ly.log fs.kernel.dirInode.unsyncedEntries (readInodeHierarchy fs)

/-- Stage `visible log ++ [rec]` in a fresh staging file. -/
def stepAppend (ly : WalLayout) (h : WalHost) (rec : List UInt8) : WalHost :=
  match posixCreateExclNoFollow (posixUnlinkIfPresent h.fs ly.tmp) ly.pid ly.tmp with
  | .error _ => { h with staged := none, synced := false }
  | .ok (fs2, fd, _) =>
    match posixPwriteAll fs2 ly.pid fd (encodeLog (visLog ly h.fs ++ [rec])) with
    | .error _ => { h with fs := fs2, staged := none, synced := false }
    | .ok fs3 => { h with fs := fs3, staged := some fd, synced := false }

def stepFsyncFile (ly : WalLayout) (h : WalHost) : WalHost :=
  match h.staged with
  | none => h
  | some fd =>
    match posixSyncAllMedia h.fs ly.pid fd with
    | (fs', .ok _) => { h with fs := fs', synced := true }
    | (fs', .error _) => { h with fs := fs' }

/-- `rename(tmp, log)`, refused unless the staging file is synced. -/
def stepRename (ly : WalLayout) (h : WalHost) : WalHost :=
  if h.synced then
    match posixRename h.fs ly.tmp ly.log with
    | .ok fs' => { h with fs := fs', staged := none, synced := false, dirClean := false }
    | .error _ => h
  else h

def stepFsyncDir (h : WalHost) : WalHost :=
  match posixSyncParentDir h.fs with
  | (fs', .ok _) => { h with fs := fs', dirClean := true }
  | (fs', .error _) => { h with fs := fs' }

/-- Advance the anchor to the visible log length, refused while a rename awaits a directory
    sync. -/
def stepBump (ly : WalLayout) (h : WalHost) : WalHost :=
  if h.dirClean then { h with anchor := Nat.max h.anchor (visLog ly h.fs).length } else h

/-- The next scheduled crash (a kernel panic once the schedule is exhausted), followed by a
    process restart. -/
def stepCrash (h : WalHost) : WalHost :=
  match h.crashes with
  | [] =>
    { h with fs := MidOpCrash.kernelPanic.apply h.fs, staged := none, synced := false,
             dirClean := true }
  | c :: cs =>
    { h with fs := c.apply h.fs, staged := none, synced := false, dirClean := true,
             crashes := cs }

def step (ly : WalLayout) (h : WalHost) : FsyncOp → WalHost
  | .append rec => stepAppend ly h rec
  | .fsyncFile => stepFsyncFile ly h
  | .rename => stepRename ly h
  | .fsyncDir => stepFsyncDir h
  | .bumpAnchor => stepBump ly h
  | .crash => stepCrash h

/-! ## 3. Explicit results of the syscall sequences -/

/-- Filesystem after `unlink tmp; create tmp; pwrite bytes`. -/
def appendFs (ly : WalLayout) (fs : PosixFsState) (bytes : List UInt8) : PosixFsState :=
  { kernel :=
      { openFds :=
          { fdRefs := assocInsert (ly.pid, fs.nextFd) fs.kernel.openFds.nextDescId
              fs.kernel.openFds.fdRefs
            descriptions := assocInsert fs.kernel.openFds.nextDescId
              { inode := fs.nand.nextInode, writable := true, stickyFsyncErr := false }
              fs.kernel.openFds.descriptions
            nextDescId := fs.kernel.openFds.nextDescId + 1 }
        flockTable := fs.kernel.flockTable
        pageCache :=
          { dirtyFiles := assocInsert fs.nand.nextInode bytes fs.kernel.pageCache.dirtyFiles }
        dirInode :=
          { unsyncedEntries := assocInsert ly.tmp (.regular fs.nand.nextInode)
              (assocErase ly.tmp fs.kernel.dirInode.unsyncedEntries) } }
    driveCache := fs.driveCache
    nand :=
      { dirNandEntries := fs.nand.dirNandEntries
        fileBlocks := assocInsert fs.nand.nextInode [] fs.nand.fileBlocks
        nextInode := fs.nand.nextInode + 1 }
    nextFd := fs.nextFd + 1 }

theorem stepAppend_eq (ly : WalLayout) (h : WalHost) (rec : List UInt8) :
    stepAppend ly h rec =
      { h with fs := appendFs ly h.fs (encodeLog (visLog ly h.fs ++ [rec])),
               staged := some h.fs.nextFd, synced := false } := by
  simp [stepAppend, posixCreateExclNoFollow, posixUnlinkIfPresent, posixPwriteAll, resolveOpenFd,
    assocLookup_erase, appendFs]

/-- Filesystem after a successful `posixSyncAllMedia` of inode `ino` holding `bs`. -/
def syncedFs (fs : PosixFsState) (ino : InodeId) (bs : List UInt8) : PosixFsState :=
  { fs with
      kernel := { fs.kernel with
                    pageCache := { dirtyFiles := assocErase ino fs.kernel.pageCache.dirtyFiles } }
      driveCache := { fs.driveCache with cachedFiles := assocErase ino fs.driveCache.cachedFiles }
      nand := { fs.nand with fileBlocks := assocInsert ino bs fs.nand.fileBlocks } }

theorem posixSyncAllMedia_eq {fs : PosixFsState} {pid : Pid} {fd : FdId}
    {descId : OpenDescriptionId} {desc : OpenFileDesc} {bs : List UInt8}
    (hRes : resolveOpenFd fs.kernel.openFds pid fd = some (descId, desc))
    (hSticky : desc.stickyFsyncErr = false)
    (hRead : readInodeHierarchy fs desc.inode = some bs) :
    posixSyncAllMedia fs pid fd = (syncedFs fs desc.inode bs, .ok ()) := by
  simp [posixSyncAllMedia, hRes, hSticky, hRead, syncedFs]

/-- Filesystem after `rename(tmp, log)` when `tmp` names inode `ino`. -/
def renamedFs (ly : WalLayout) (fs : PosixFsState) (ino : InodeId) : PosixFsState :=
  { fs with
      kernel := { fs.kernel with
                    dirInode :=
                      { unsyncedEntries := assocErase ly.tmp
                          (assocInsert ly.log (.regular ino) fs.kernel.dirInode.unsyncedEntries) } } }

theorem posixRename_eq (ly : WalLayout) {fs : PosixFsState} {ino : InodeId}
    (hTmp : assocLookup fs.kernel.dirInode.unsyncedEntries ly.tmp = some (.regular ino)) :
    posixRename fs ly.tmp ly.log = .ok (renamedFs ly fs ino) := by
  simp [posixRename, hTmp, ly.distinct, renamedFs]

/-- Filesystem after `posixSyncParentDir`. -/
def dirSyncedFs (fs : PosixFsState) : PosixFsState :=
  { fs with
      driveCache := { fs.driveCache with cachedDirEntries := none }
      nand := { fs.nand with dirNandEntries := fs.kernel.dirInode.unsyncedEntries } }

theorem stepFsyncDir_eq (h : WalHost) :
    stepFsyncDir h = { h with fs := dirSyncedFs h.fs, dirClean := true } := by
  simp [stepFsyncDir, posixSyncParentDir, dirSyncedFs]

/-! ## 4. Host invariant -/

/-- No write to `ino` is in flight in either volatile tier, and `ino` is allocated. -/
def Settled (fs : PosixFsState) (ino : InodeId) : Prop :=
  pendingVolatileWrite fs ino = none ∧ ino < fs.nand.nextInode

/-- Descriptor `fd` is the open staging file, named `tmp`, reading back `encodeLog L`. -/
def StagedWith (ly : WalLayout) (fs : PosixFsState) (fd : FdId) (L : List (List UInt8)) : Prop :=
  ∃ (descId : OpenDescriptionId) (desc : OpenFileDesc),
    resolveOpenFd fs.kernel.openFds ly.pid fd = some (descId, desc) ∧
    desc.stickyFsyncErr = false ∧
    assocLookup fs.kernel.dirInode.unsyncedEntries ly.tmp = some (.regular desc.inode) ∧
    desc.inode < fs.nand.nextInode ∧
    readInodeHierarchy fs desc.inode = some (encodeLog L)

/-- `tmp` names a settled inode whose NAND blocks are `encodeLog L`. -/
def SyncedWith (ly : WalLayout) (fs : PosixFsState) (L : List (List UInt8)) : Prop :=
  ∃ ino : InodeId,
    assocLookup fs.kernel.dirInode.unsyncedEntries ly.tmp = some (.regular ino) ∧
    Settled fs ino ∧
    assocLookup fs.nand.fileBlocks ino = some (encodeLog L)

/-- States of the host reachable under the protocol: the log inode is settled under both
    directory views, the kernel view extends the NAND view, and the process flags are accurate. -/
structure WellFormed (ly : WalLayout) (h : WalHost) : Prop where
  dirCache : h.fs.driveCache.cachedDirEntries = none
  nandSettled : ∀ ino, assocLookup h.fs.nand.dirNandEntries ly.log = some (.regular ino) →
    Settled h.fs ino
  kernSettled : ∀ ino,
    assocLookup h.fs.kernel.dirInode.unsyncedEntries ly.log = some (.regular ino) →
    Settled h.fs ino
  nandPrefix : nandLog ly h.fs <+: kernLog ly h.fs
  staged : ∀ fd, h.staged = some fd → ∃ L, StagedWith ly h.fs fd L ∧ kernLog ly h.fs <+: L
  synced : h.synced = true → ∃ L, SyncedWith ly h.fs L ∧ kernLog ly h.fs <+: L
  clean : h.dirClean = true → kernLog ly h.fs = nandLog ly h.fs

theorem pending_none {fs : PosixFsState} {ino : InodeId}
    (h : pendingVolatileWrite fs ino = none) :
    assocLookup fs.kernel.pageCache.dirtyFiles ino = none ∧
      assocLookup fs.driveCache.cachedFiles ino = none := by
  unfold pendingVolatileWrite at h
  cases hd : assocLookup fs.kernel.pageCache.dirtyFiles ino with
  | some d => rw [hd] at h; cases h
  | none => rw [hd] at h; exact ⟨rfl, h⟩

theorem read_of_pending_none {fs : PosixFsState} {ino : InodeId}
    (h : pendingVolatileWrite fs ino = none) :
    readInodeHierarchy fs ino = assocLookup fs.nand.fileBlocks ino := by
  unfold readInodeHierarchy
  rw [h]

theorem logOf_congr {name : DirName} {e e' : List (DirName × EntryTarget)}
    {blk blk' : InodeId → Option (List UInt8)}
    (hE : assocLookup e' name = assocLookup e name)
    (hB : ∀ ino, assocLookup e name = some (.regular ino) → blk' ino = blk ino) :
    logOf name e' blk' = logOf name e blk := by
  unfold logOf
  rw [hE]
  cases hL : assocLookup e name with
  | none => rfl
  | some t =>
    cases t with
    | regular ino =>
      dsimp only
      rw [hB ino hL]
    | symlink _ => rfl

theorem visLog_eq_kernLog {ly : WalLayout} {fs : PosixFsState}
    (hK : ∀ ino, assocLookup fs.kernel.dirInode.unsyncedEntries ly.log = some (.regular ino) →
      Settled fs ino) :
    visLog ly fs = kernLog ly fs :=
  logOf_congr rfl (fun ino hI => read_of_pending_none (hK ino hI).1)

/-! ### `append` -/

theorem appendFs_settled (ly : WalLayout) {fs : PosixFsState} (bytes : List UInt8) {j : InodeId}
    (hS : Settled fs j) :
    Settled (appendFs ly fs bytes) j ∧
      assocLookup (appendFs ly fs bytes).nand.fileBlocks j = assocLookup fs.nand.fileBlocks j := by
  have hne : j ≠ fs.nand.nextInode := Nat.ne_of_lt hS.2
  refine ⟨⟨?_, Nat.lt_succ_of_lt hS.2⟩, assocLookup_insert_of_ne _ _ hne⟩
  have hP : pendingVolatileWrite (appendFs ly fs bytes) j = pendingVolatileWrite fs j := by
    simp only [pendingVolatileWrite, appendFs, assocLookup_insert_of_ne _ _ hne]
  rw [hP]
  exact hS.1

theorem appendFs_log_entry (ly : WalLayout) (fs : PosixFsState) (bytes : List UInt8) :
    assocLookup (appendFs ly fs bytes).kernel.dirInode.unsyncedEntries ly.log =
      assocLookup fs.kernel.dirInode.unsyncedEntries ly.log := by
  have hne : ly.log ≠ ly.tmp := fun h => ly.distinct h.symm
  simp only [appendFs, assocLookup_insert, assocLookup_erase, hne, ↓reduceIte]

theorem stepAppend_spec (ly : WalLayout) {h : WalHost} (hW : WellFormed ly h) (rec : List UInt8) :
    WellFormed ly (stepAppend ly h rec) ∧
    (stepAppend ly h rec).staged = some h.fs.nextFd ∧
    StagedWith ly (stepAppend ly h rec).fs h.fs.nextFd (kernLog ly h.fs ++ [rec]) ∧
    kernLog ly (stepAppend ly h rec).fs = kernLog ly h.fs ∧
    nandLog ly (stepAppend ly h rec).fs = nandLog ly h.fs := by
  rw [stepAppend_eq, visLog_eq_kernLog hW.kernSettled]
  have hKern : kernLog ly (appendFs ly h.fs (encodeLog (kernLog ly h.fs ++ [rec]))) =
      kernLog ly h.fs :=
    logOf_congr (appendFs_log_entry ly h.fs _)
      (fun ino hI => (appendFs_settled ly _ (hW.kernSettled ino hI)).2)
  have hNand : nandLog ly (appendFs ly h.fs (encodeLog (kernLog ly h.fs ++ [rec]))) =
      nandLog ly h.fs :=
    logOf_congr rfl (fun ino hI => (appendFs_settled ly _ (hW.nandSettled ino hI)).2)
  have hStaged : StagedWith ly (appendFs ly h.fs (encodeLog (kernLog ly h.fs ++ [rec])))
      h.fs.nextFd (kernLog ly h.fs ++ [rec]) := by
    refine ⟨h.fs.kernel.openFds.nextDescId,
      { inode := h.fs.nand.nextInode, writable := true, stickyFsyncErr := false }, ?_, rfl, ?_,
      Nat.lt_succ_self _, ?_⟩
    · simp [appendFs, resolveOpenFd]
    · simp [appendFs]
    · simp [readInodeHierarchy, pendingVolatileWrite, appendFs]
  refine ⟨?_, rfl, hStaged, hKern, hNand⟩
  exact
    { dirCache := hW.dirCache
      nandSettled := fun ino hI => (appendFs_settled ly _ (hW.nandSettled ino hI)).1
      kernSettled := fun ino hI =>
        (appendFs_settled ly _
          (hW.kernSettled ino ((appendFs_log_entry ly h.fs _).symm.trans hI))).1
      nandPrefix := by rw [hKern, hNand]; exact hW.nandPrefix
      staged := fun fd hfd => by
        obtain rfl := Option.some.inj hfd
        exact ⟨_, hStaged, by rw [hKern]; exact List.prefix_append _ _⟩
      synced := fun hs => Bool.noConfusion hs
      clean := fun hc => by rw [hKern, hNand]; exact hW.clean hc }

/-! ### `fsyncFile` -/

theorem syncedFs_settled {fs : PosixFsState} {ino : InodeId} {bs : List UInt8}
    (hRead : readInodeHierarchy fs ino = some bs) {j : InodeId} (hS : Settled fs j) :
    Settled (syncedFs fs ino bs) j ∧
      assocLookup (syncedFs fs ino bs).nand.fileBlocks j = assocLookup fs.nand.fileBlocks j := by
  obtain ⟨hd, hc⟩ := pending_none hS.1
  by_cases hj : j = ino
  · subst hj
    refine ⟨⟨?_, hS.2⟩, ?_⟩
    · simp [pendingVolatileWrite, syncedFs]
    · rw [← read_of_pending_none hS.1, hRead]
      simp [syncedFs]
  · refine ⟨⟨?_, hS.2⟩, assocLookup_insert_of_ne _ _ hj⟩
    simp [pendingVolatileWrite, syncedFs, hj, hd, hc]

theorem syncedFs_self (fs : PosixFsState) (ino : InodeId) (bs : List UInt8) :
    pendingVolatileWrite (syncedFs fs ino bs) ino = none ∧
      assocLookup (syncedFs fs ino bs).nand.fileBlocks ino = some bs := by
  constructor
  · simp [pendingVolatileWrite, syncedFs]
  · simp [syncedFs]

theorem stepFsyncFile_staged (ly : WalLayout) {h : WalHost} (hW : WellFormed ly h) {fd : FdId}
    {L : List (List UInt8)} (hS : h.staged = some fd) (hSt : StagedWith ly h.fs fd L) :
    (stepFsyncFile ly h).synced = true ∧
    SyncedWith ly (stepFsyncFile ly h).fs L ∧
    kernLog ly (stepFsyncFile ly h).fs = kernLog ly h.fs ∧
    nandLog ly (stepFsyncFile ly h).fs = nandLog ly h.fs ∧
    (kernLog ly h.fs <+: L → WellFormed ly (stepFsyncFile ly h)) := by
  obtain ⟨descId, desc, hRes, hSticky, hTmp, hLt, hRead⟩ := hSt
  have hEq : stepFsyncFile ly h =
      { h with fs := syncedFs h.fs desc.inode (encodeLog L), synced := true } := by
    simp only [stepFsyncFile, hS, posixSyncAllMedia_eq hRes hSticky hRead]
  rw [hEq]
  have hKern : kernLog ly (syncedFs h.fs desc.inode (encodeLog L)) = kernLog ly h.fs :=
    logOf_congr rfl (fun ino hI => (syncedFs_settled hRead (hW.kernSettled ino hI)).2)
  have hNand : nandLog ly (syncedFs h.fs desc.inode (encodeLog L)) = nandLog ly h.fs :=
    logOf_congr rfl (fun ino hI => (syncedFs_settled hRead (hW.nandSettled ino hI)).2)
  have hSelf := syncedFs_self h.fs desc.inode (encodeLog L)
  have hSynced : SyncedWith ly (syncedFs h.fs desc.inode (encodeLog L)) L :=
    ⟨desc.inode, hTmp, ⟨hSelf.1, hLt⟩, hSelf.2⟩
  refine ⟨rfl, hSynced, hKern, hNand, fun hPre => ?_⟩
  exact
    { dirCache := hW.dirCache
      nandSettled := fun ino hI => (syncedFs_settled hRead (hW.nandSettled ino hI)).1
      kernSettled := fun ino hI => (syncedFs_settled hRead (hW.kernSettled ino hI)).1
      nandPrefix := by rw [hKern, hNand]; exact hW.nandPrefix
      staged := fun fd' hfd' => by
        obtain rfl : fd = fd' := Option.some.inj (hS.symm.trans hfd')
        refine ⟨L, ⟨descId, desc, hRes, hSticky, hTmp, hLt, ?_⟩, by rw [hKern]; exact hPre⟩
        rw [read_of_pending_none hSelf.1]
        exact hSelf.2
      synced := fun _ => ⟨L, hSynced, by rw [hKern]; exact hPre⟩
      clean := fun hc => by rw [hKern, hNand]; exact hW.clean hc }

theorem stepFsyncFile_spec (ly : WalLayout) {h : WalHost} (hW : WellFormed ly h) :
    WellFormed ly (stepFsyncFile ly h) ∧
      nandLog ly (stepFsyncFile ly h).fs = nandLog ly h.fs := by
  cases hS : h.staged with
  | none =>
    have hEq : stepFsyncFile ly h = h := by simp only [stepFsyncFile, hS]
    rw [hEq]
    exact ⟨hW, rfl⟩
  | some fd =>
    obtain ⟨L, hSt, hPre⟩ := hW.staged fd hS
    obtain ⟨_, _, _, hNand, hWf⟩ := stepFsyncFile_staged ly hW hS hSt
    exact ⟨hWf hPre, hNand⟩

/-! ### `rename` -/

theorem stepRename_synced (ly : WalLayout) {h : WalHost} (hW : WellFormed ly h)
    {L : List (List UInt8)} (hs : h.synced = true) (hSy : SyncedWith ly h.fs L) :
    kernLog ly (stepRename ly h).fs = L ∧
    nandLog ly (stepRename ly h).fs = nandLog ly h.fs ∧
    (kernLog ly h.fs <+: L → WellFormed ly (stepRename ly h)) := by
  obtain ⟨ino, hTmp, hSet, hBlk⟩ := hSy
  have hEq : stepRename ly h =
      { h with fs := renamedFs ly h.fs ino, staged := none, synced := false,
               dirClean := false } := by
    simp only [stepRename, hs, ↓reduceIte, posixRename_eq ly hTmp]
  rw [hEq]
  have hne : ly.log ≠ ly.tmp := fun e => ly.distinct e.symm
  have hEntry : assocLookup (renamedFs ly h.fs ino).kernel.dirInode.unsyncedEntries ly.log =
      some (.regular ino) := by
    simp only [renamedFs, assocLookup_erase, assocLookup_insert_self, hne, ↓reduceIte]
  have hKern : kernLog ly (renamedFs ly h.fs ino) = L := by
    have hB : assocLookup (renamedFs ly h.fs ino).nand.fileBlocks ino = some (encodeLog L) := hBlk
    unfold kernLog logOf
    rw [hEntry]
    dsimp only
    rw [hB]
    exact decodeLog_encodeLog L
  refine ⟨hKern, rfl, fun hPre => ?_⟩
  exact
    { dirCache := hW.dirCache
      nandSettled := hW.nandSettled
      kernSettled := fun j hj => by
        have hEq' : EntryTarget.regular ino = EntryTarget.regular j :=
          Option.some.inj (hEntry.symm.trans hj)
        injection hEq' with hij
        subst hij
        exact hSet
      nandPrefix := by rw [hKern]; exact List.IsPrefix.trans hW.nandPrefix hPre
      staged := fun _ hfd => by cases hfd
      synced := fun hs' => Bool.noConfusion hs'
      clean := fun hc => Bool.noConfusion hc }

theorem stepRename_spec (ly : WalLayout) {h : WalHost} (hW : WellFormed ly h) :
    WellFormed ly (stepRename ly h) ∧
      nandLog ly (stepRename ly h).fs = nandLog ly h.fs := by
  cases hs : h.synced with
  | false =>
    have hEq : stepRename ly h = h := by simp [stepRename, hs]
    rw [hEq]
    exact ⟨hW, rfl⟩
  | true =>
    obtain ⟨L, hSy, hPre⟩ := hW.synced hs
    obtain ⟨_, hNand, hWf⟩ := stepRename_synced ly hW hs hSy
    exact ⟨hWf hPre, hNand⟩

/-! ### `fsyncDir`, `bumpAnchor` -/

theorem stepFsyncDir_spec (ly : WalLayout) {h : WalHost} (hW : WellFormed ly h) :
    WellFormed ly (stepFsyncDir h) ∧
    nandLog ly (stepFsyncDir h).fs = kernLog ly h.fs ∧
    kernLog ly (stepFsyncDir h).fs = kernLog ly h.fs := by
  rw [stepFsyncDir_eq]
  refine ⟨?_, rfl, rfl⟩
  exact
    { dirCache := rfl
      nandSettled := hW.kernSettled
      kernSettled := hW.kernSettled
      nandPrefix := List.prefix_refl _
      staged := hW.staged
      synced := hW.synced
      clean := fun _ => rfl }

theorem stepBump_spec (ly : WalLayout) {h : WalHost} (hW : WellFormed ly h) :
    WellFormed ly (stepBump ly h) ∧ (stepBump ly h).fs = h.fs := by
  unfold stepBump
  split
  · exact ⟨⟨hW.dirCache, hW.nandSettled, hW.kernSettled, hW.nandPrefix, hW.staged, hW.synced,
      hW.clean⟩, rfl⟩
  · exact ⟨hW, rfl⟩

/-! ### `crash` -/

theorem crashStep_facts {fs fs' : PosixFsState} (hC : fs.driveCache.cachedDirEntries = none)
    (hCrash : CrashStep fs fs') :
    (fs'.nand.dirNandEntries = fs.nand.dirNandEntries ∨
      fs'.nand.dirNandEntries = fs.kernel.dirInode.unsyncedEntries) ∧
    fs'.kernel.dirInode.unsyncedEntries = fs'.nand.dirNandEntries ∧
    fs'.driveCache.cachedDirEntries = none ∧
    fs'.nand.nextInode = fs.nand.nextInode ∧
    (∀ j, pendingVolatileWrite fs' j = none) := by
  cases hCrash with
  | kernelPanic _ =>
    refine ⟨.inl ?_, rfl, rfl, rfl, fun _ => rfl⟩
    simp [KernelPanicCrash, hC]
  | powerLoss dirPick tearFn _ =>
    cases dirPick with
    | revertToNand => exact ⟨.inl rfl, rfl, rfl, rfl, fun _ => rfl⟩
    | flushPendingDir =>
      refine ⟨.inr ?_, rfl, rfl, rfl, fun _ => rfl⟩
      simp [PowerLossCrash, hC]

/-- A crash followed by a process restart: the recovered log is the old NAND log or the log
    under the kernel directory view at the crash. -/
theorem crash_spec (ly : WalLayout) {h : WalHost} (hW : WellFormed ly h) {fs' : PosixFsState}
    (hCrash : CrashStep h.fs fs') (cs : List MidOpCrash) :
    WellFormed ly
        { h with fs := fs', staged := none, synced := false, dirClean := true, crashes := cs } ∧
      nandLog ly h.fs <+: nandLog ly fs' := by
  obtain ⟨hDir, hKN, hC', hNext, hPend⟩ := crashStep_facts hW.dirCache hCrash
  have hBlk : ∀ j, Settled h.fs j →
      assocLookup fs'.nand.fileBlocks j = assocLookup h.fs.nand.fileBlocks j := fun j hS =>
    (syncedInode_immune_to_crashStep (pending_none hS.1).1 (pending_none hS.1).2 hCrash).1
  have hKernEq : kernLog ly fs' = nandLog ly fs' := by
    unfold kernLog nandLog
    rw [hKN]
  have hSettled : ∀ ino, assocLookup fs'.nand.dirNandEntries ly.log = some (.regular ino) →
      Settled fs' ino := by
    intro ino hI
    have hOld : Settled h.fs ino := by
      rcases hDir with hD | hD
      · exact hW.nandSettled ino (hD ▸ hI)
      · exact hW.kernSettled ino (hD ▸ hI)
    exact ⟨hPend ino, hNext ▸ hOld.2⟩
  have hPrefix : nandLog ly h.fs <+: nandLog ly fs' := by
    rcases hDir with hD | hD
    · have hEq : nandLog ly fs' = nandLog ly h.fs :=
        logOf_congr (congrArg (fun e => assocLookup e ly.log) hD)
          (fun ino hI => hBlk ino (hW.nandSettled ino hI))
      rw [hEq]
      exact List.prefix_refl _
    · have hEq : nandLog ly fs' = kernLog ly h.fs :=
        logOf_congr (congrArg (fun e => assocLookup e ly.log) hD)
          (fun ino hI => hBlk ino (hW.kernSettled ino hI))
      rw [hEq]
      exact hW.nandPrefix
  refine ⟨?_, hPrefix⟩
  exact
    { dirCache := hC'
      nandSettled := hSettled
      kernSettled := fun ino hI => hSettled ino (hKN ▸ hI)
      nandPrefix := by rw [hKernEq]; exact List.prefix_refl _
      staged := fun _ hfd => by cases hfd
      synced := fun hs => Bool.noConfusion hs
      clean := fun _ => hKernEq }

theorem stepCrash_spec (ly : WalLayout) {h : WalHost} (hW : WellFormed ly h) :
    WellFormed ly (stepCrash h) ∧ nandLog ly h.fs <+: nandLog ly (stepCrash h).fs := by
  unfold stepCrash
  split
  · exact crash_spec ly hW (MidOpCrash.apply_crashStep .kernelPanic h.fs) h.crashes
  · exact crash_spec ly hW (MidOpCrash.apply_crashStep _ h.fs) _

/-! ### Every step -/

theorem step_wellFormed (ly : WalLayout) {h : WalHost} (hW : WellFormed ly h) (op : FsyncOp) :
    WellFormed ly (step ly h op) := by
  cases op with
  | append rec => exact (stepAppend_spec ly hW rec).1
  | fsyncFile => exact (stepFsyncFile_spec ly hW).1
  | rename => exact (stepRename_spec ly hW).1
  | fsyncDir => exact (stepFsyncDir_spec ly hW).1
  | bumpAnchor => exact (stepBump_spec ly hW).1
  | crash => exact (stepCrash_spec ly hW).1

theorem step_nandLog_prefix (ly : WalLayout) {h : WalHost} (hW : WellFormed ly h) (op : FsyncOp) :
    nandLog ly h.fs <+: nandLog ly (step ly h op).fs := by
  cases op with
  | append rec =>
    show nandLog ly h.fs <+: nandLog ly (stepAppend ly h rec).fs
    rw [(stepAppend_spec ly hW rec).2.2.2.2]
    exact List.prefix_refl _
  | fsyncFile =>
    show nandLog ly h.fs <+: nandLog ly (stepFsyncFile ly h).fs
    rw [(stepFsyncFile_spec ly hW).2]
    exact List.prefix_refl _
  | rename =>
    show nandLog ly h.fs <+: nandLog ly (stepRename ly h).fs
    rw [(stepRename_spec ly hW).2]
    exact List.prefix_refl _
  | fsyncDir =>
    show nandLog ly h.fs <+: nandLog ly (stepFsyncDir h).fs
    rw [(stepFsyncDir_spec ly hW).2.1]
    exact hW.nandPrefix
  | bumpAnchor =>
    show nandLog ly h.fs <+: nandLog ly (stepBump ly h).fs
    rw [(stepBump_spec ly hW).2]
    exact List.prefix_refl _
  | crash => exact (stepCrash_spec ly hW).2

theorem step_anchor_mono (ly : WalLayout) (h : WalHost) (op : FsyncOp) :
    h.anchor ≤ (step ly h op).anchor := by
  cases op with
  | append rec =>
    show h.anchor ≤ (stepAppend ly h rec).anchor
    rw [stepAppend_eq]
    exact Nat.le_refl _
  | fsyncFile =>
    show h.anchor ≤ (stepFsyncFile ly h).anchor
    unfold stepFsyncFile
    split
    · exact Nat.le_refl _
    · split <;> exact Nat.le_refl _
  | rename =>
    show h.anchor ≤ (stepRename ly h).anchor
    unfold stepRename
    split
    · split <;> exact Nat.le_refl _
    · exact Nat.le_refl _
  | fsyncDir =>
    show h.anchor ≤ (stepFsyncDir h).anchor
    rw [stepFsyncDir_eq]
    exact Nat.le_refl _
  | bumpAnchor =>
    show h.anchor ≤ (stepBump ly h).anchor
    unfold stepBump
    split
    · exact Nat.le_max_left _ _
    · exact Nat.le_refl _
  | crash =>
    show h.anchor ≤ (stepCrash h).anchor
    unfold stepCrash
    split <;> exact Nat.le_refl _

theorem step_anchor_le_durable (ly : WalLayout) {h : WalHost} (hW : WellFormed ly h)
    (op : FsyncOp) (hA : h.anchor ≤ (nandLog ly h.fs).length) :
    (step ly h op).anchor ≤ (nandLog ly (step ly h op).fs).length := by
  have hLen : (nandLog ly h.fs).length ≤ (nandLog ly (step ly h op).fs).length :=
    (step_nandLog_prefix ly hW op).length_le
  cases op with
  | bumpAnchor =>
    show (stepBump ly h).anchor ≤ (nandLog ly (stepBump ly h).fs).length
    unfold stepBump
    split
    · rename_i hc
      show Nat.max h.anchor (visLog ly h.fs).length ≤ (nandLog ly h.fs).length
      rw [visLog_eq_kernLog hW.kernSettled, hW.clean hc]
      exact Nat.max_le.mpr ⟨hA, Nat.le_refl _⟩
    · exact hA
  | append rec =>
    refine Nat.le_trans (Nat.le_of_eq ?_) (Nat.le_trans hA hLen)
    show (stepAppend ly h rec).anchor = h.anchor
    rw [stepAppend_eq]
  | fsyncFile =>
    refine Nat.le_trans (Nat.le_of_eq ?_) (Nat.le_trans hA hLen)
    show (stepFsyncFile ly h).anchor = h.anchor
    unfold stepFsyncFile
    split
    · rfl
    · split <;> rfl
  | rename =>
    refine Nat.le_trans (Nat.le_of_eq ?_) (Nat.le_trans hA hLen)
    show (stepRename ly h).anchor = h.anchor
    unfold stepRename
    split
    · split <;> rfl
    · rfl
  | fsyncDir =>
    refine Nat.le_trans (Nat.le_of_eq ?_) (Nat.le_trans hA hLen)
    show (stepFsyncDir h).anchor = h.anchor
    rw [stepFsyncDir_eq]
  | crash =>
    refine Nat.le_trans (Nat.le_of_eq ?_) (Nat.le_trans hA hLen)
    show (stepCrash h).anchor = h.anchor
    unfold stepCrash
    split <;> rfl

/-! ## 5. The induced storage model and the contract -/

/-- The `FsyncStorageModel` induced by the `PosixFsState` WAL host. Its states are the
    well-formed hosts; `durable` is the log decoded from NAND. -/
@[expose] def walModel (ly : WalLayout) : FsyncStorageModel where
  State := { h : WalHost // WellFormed ly h }
  step := fun s op => ⟨step ly s.1 op, step_wellFormed ly s.2 op⟩
  durable := fun s => nandLog ly s.1.fs
  anchor := fun s => s.1.anchor

/-- The log under the kernel directory view: what the next directory sync makes durable. -/
def walVisible (ly : WalLayout) (s : (walModel ly).State) : List Bytes := kernLog ly s.1.fs

/-- No rename is waiting for a directory sync. -/
def Quiescent (ly : WalLayout) (s : (walModel ly).State) : Prop :=
  walVisible ly s = (walModel ly).durable s

/-- Contract field `noRollback` for the `PosixFsState` host: no trace, with any schedule of
    kernel panics and power losses, removes or reorders durable records. -/
theorem walModel_noRollback (ly : WalLayout) :
    ∀ (tr : List FsyncOp) (s : (walModel ly).State),
      (walModel ly).durable s <+: (walModel ly).durable ((walModel ly).run s tr)
  | [], _ => List.prefix_refl _
  | op :: rest, s =>
    List.IsPrefix.trans (step_nandLog_prefix ly s.2 op)
      (walModel_noRollback ly rest ((walModel ly).step s op))

/-- Contract field `anchorMonotone` for the `PosixFsState` host. -/
theorem walModel_anchorMonotone (ly : WalLayout) :
    ∀ (tr : List FsyncOp) (s : (walModel ly).State),
      (walModel ly).anchor s ≤ (walModel ly).anchor ((walModel ly).run s tr)
  | [], _ => Nat.le_refl _
  | op :: rest, s =>
    Nat.le_trans (step_anchor_mono ly s.1 op)
      (walModel_anchorMonotone ly rest ((walModel ly).step s op))

/-- Contract field `anchorWitnessesDurable` for the `PosixFsState` host. -/
theorem walModel_anchorWitnessesDurable (ly : WalLayout) :
    ∀ (tr : List FsyncOp) (s : (walModel ly).State),
      (walModel ly).anchor s ≤ ((walModel ly).durable s).length →
      (walModel ly).anchor ((walModel ly).run s tr) ≤
        ((walModel ly).durable ((walModel ly).run s tr)).length
  | [], _, h => h
  | op :: rest, s, h =>
    walModel_anchorWitnessesDurable ly rest ((walModel ly).step s op)
      (step_anchor_le_durable ly s.2 op h)

/-- `append; fsyncFile; rename` extends the visible log by the record and leaves the durable
    log unchanged. -/
theorem walModel_stage_rename (ly : WalLayout) (s : (walModel ly).State) (rec : Bytes) :
    walVisible ly ((walModel ly).run s [.append rec, .fsyncFile, .rename]) =
        walVisible ly s ++ [rec] ∧
      (walModel ly).durable ((walModel ly).run s [.append rec, .fsyncFile, .rename]) =
        (walModel ly).durable s := by
  obtain ⟨hW1, hS1, hSt1, hK1, hN1⟩ := stepAppend_spec ly s.2 rec
  obtain ⟨hs2, hSy2, _, hN2, hWf2⟩ := stepFsyncFile_staged ly hW1 hS1 hSt1
  have hW2 := hWf2 (by rw [hK1]; exact List.prefix_append _ _)
  obtain ⟨hK3, hN3, _⟩ := stepRename_synced ly hW2 hs2 hSy2
  exact ⟨hK3, hN3.trans (hN2.trans hN1)⟩

/-- **The commit protocol on the `PosixFsState` host.** From every well-formed state, after
    `walCommitOps rec` the durable log is the previously visible log extended by `rec`. -/
theorem walModel_commit_appends_to_visible_log (ly : WalLayout) (s : (walModel ly).State)
    (rec : Bytes) :
    (walModel ly).durable ((walModel ly).run s (walCommitOps rec)) = walVisible ly s ++ [rec] := by
  have hRun : (walModel ly).run s (walCommitOps rec) =
      (walModel ly).run ((walModel ly).run s [.append rec, .fsyncFile, .rename])
        [.fsyncDir, .bumpAnchor] :=
    (walModel ly).run_append [.append rec, .fsyncFile, .rename] [.fsyncDir, .bumpAnchor] s
  rw [hRun]
  obtain ⟨hK, _⟩ := walModel_stage_rename ly s rec
  generalize (walModel ly).run s [.append rec, .fsyncFile, .rename] = s3 at hK
  obtain ⟨hW4, hN4, _⟩ := stepFsyncDir_spec ly s3.2
  have hN5 := congrArg (nandLog ly) (stepBump_spec ly hW4).2
  exact (hN5.trans hN4).trans hK

/-- Contract field `committedRecordDurable` for the `PosixFsState` host, from a state in which
    no rename is waiting for a directory sync. -/
theorem walModel_committedRecordDurable_of_quiescent (ly : WalLayout)
    (s : (walModel ly).State) (rec : Bytes) (hQ : Quiescent ly s) :
    (walModel ly).durable ((walModel ly).run s (walCommitOps rec)) =
      (walModel ly).durable s ++ [rec] := by
  rw [walModel_commit_appends_to_visible_log, hQ]

/-- A freshly formatted volume with an idle host. -/
def emptyHost : WalHost :=
  { fs := PosixFsState.empty, staged := none, synced := false, dirClean := true, anchor := 0,
    crashes := [] }

theorem emptyHost_wellFormed (ly : WalLayout) : WellFormed ly emptyHost where
  dirCache := rfl
  nandSettled := fun _ h => by cases h
  kernSettled := fun _ h => by cases h
  nandPrefix := List.prefix_refl _
  staged := fun _ h => by cases h
  synced := fun h => Bool.noConfusion h
  clean := fun _ => rfl

/-- **`#tooth`: a commit on the `PosixFsState` host does not add exactly one record.** On a
    fresh volume, after `append r₀; fsyncFile; rename` nothing is durable, yet a full commit of
    `r₁` makes both `r₀` and `r₁` durable: the rename of `r₀` is flushed by the directory sync
    of the commit. -/
theorem walModel_commit_not_exactly_one_record (ly : WalLayout) :
    ¬ ∀ (s : (walModel ly).State) (rec : Bytes),
      (walModel ly).durable ((walModel ly).run s (walCommitOps rec)) =
        (walModel ly).durable s ++ [rec] := by
  intro c
  have hStage := walModel_stage_rename ly ⟨emptyHost, emptyHost_wellFormed ly⟩ []
  have hField := c
    ((walModel ly).run ⟨emptyHost, emptyHost_wellFormed ly⟩ [.append [], .fsyncFile, .rename]) []
  have hV : walVisible ly ⟨emptyHost, emptyHost_wellFormed ly⟩ = [] := rfl
  have hD : (walModel ly).durable ⟨emptyHost, emptyHost_wellFormed ly⟩ = [] := rfl
  rw [walModel_commit_appends_to_visible_log, hStage.1, hStage.2, hV, hD] at hField
  exact absurd (congrArg List.length hField) (by decide)

/-! ## 6. The Spec contract -/

/-- **The `PosixFsState` WAL host satisfies `Spec.PosixFsyncContract`.** -/
theorem walModel_contract (ly : WalLayout) : PosixFsyncContract (walModel ly) where
  committedRecordLast s rec := by
    obtain ⟨pending, hp⟩ := s.2.nandPrefix
    refine ⟨pending, ?_⟩
    rw [walModel_commit_appends_to_visible_log]
    exact congrArg (· ++ [rec]) hp.symm
  noRollback s tr := walModel_noRollback ly tr s
  anchorMonotone s tr := walModel_anchorMonotone ly tr s
  anchorWitnessesDurable s tr h := walModel_anchorWitnessesDurable ly tr s h

/-- **Crash safety of a committed record on `PosixFsState`.** After the commit protocol for
    `rec`, every later trace of host steps, kernel panics and power losses (any directory
    outcome, any sector tears) recovers a log containing `rec`. -/
theorem walModel_committed_survives (ly : WalLayout) (s : (walModel ly).State) (rec : Bytes)
    (post : List FsyncOp) :
    rec ∈ (walModel ly).durable ((walModel ly).run s (walCommitOps rec ++ post)) :=
  (walModel_contract ly).committed_survives s rec post

#verify_constructive
  Qsag.PosixWalHost.decodeLog_encodeLog
  Qsag.PosixWalHost.step_wellFormed
  Qsag.PosixWalHost.walModel_noRollback
  Qsag.PosixWalHost.walModel_anchorMonotone
  Qsag.PosixWalHost.walModel_anchorWitnessesDurable
  Qsag.PosixWalHost.walModel_stage_rename
  Qsag.PosixWalHost.walModel_commit_appends_to_visible_log
  Qsag.PosixWalHost.walModel_committedRecordDurable_of_quiescent
  Qsag.PosixWalHost.walModel_commit_not_exactly_one_record
  Qsag.PosixWalHost.walModel_contract
  Qsag.PosixWalHost.walModel_committed_survives
#tooth_pair Qsag.PosixWalHost.walModel_committedRecordDurable_of_quiescent vs Qsag.PosixWalHost.walModel_commit_not_exactly_one_record

end Qsag.PosixWalHost
end
