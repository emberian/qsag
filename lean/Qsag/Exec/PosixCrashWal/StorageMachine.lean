module

public import Qsag.Exec.PosixCrashWal.WalRecordCodec
public import Qsag.Tactic.Prelude
public import Qsag.Exec.SimulationSpine
public import Qsag.Oracle.Keccak
import Qsag.Tactic.AssuranceKit

public section

namespace Qsag

set_option autoImplicit false

/-- POSIX directory component name (`d_name` raw byte sequence, avoiding UTF-8 string axioms). -/
structure DirName where
  rawBytes : List UInt8
  deriving Repr, DecidableEq

instance : LawfulBEq DirName where
  eq_of_beq {a b} h := by
    have hDec : decide (a = b) = true := h
    exact of_decide_eq_true hDec
  rfl {a} := decide_eq_true rfl

/-- Canonical `.lock` sidecar filename `<base>.lock` (`[0x2e, 0x6c, 0x6f, 0x63, 0x6b]`). -/
@[expose]
def walLockPath (base : DirName) : DirName :=
  ⟨base.rawBytes ++ [0x2e, 0x6c, 0x6f, 0x63, 0x6b]⟩

/-- Canonical `.tmp` staging filename `<base>.tmp` (`[0x2e, 0x74, 0x6d, 0x70]`). -/
@[expose]
def walTmpPath (base : DirName) : DirName :=
  ⟨base.rawBytes ++ [0x2e, 0x74, 0x6d, 0x70]⟩

theorem walLockPath_ne_base (base : DirName) : walLockPath base ≠ base := by
  intro hEq
  have hLen := congrArg (fun d => d.rawBytes.length) hEq
  dsimp only [walLockPath] at hLen
  rw [List.length_append] at hLen
  exact Nat.ne_of_gt (Nat.lt_add_of_pos_right (by decide : 0 < 5)) hLen

theorem walTmpPath_ne_base (base : DirName) : walTmpPath base ≠ base := by
  intro hEq
  have hLen := congrArg (fun d => d.rawBytes.length) hEq
  dsimp only [walTmpPath] at hLen
  rw [List.length_append] at hLen
  exact Nat.ne_of_gt (Nat.lt_add_of_pos_right (by decide : 0 < 4)) hLen

theorem walTmpPath_ne_lockPath (base : DirName) : walTmpPath base ≠ walLockPath base := by
  intro hEq
  have hLen := congrArg (fun d => d.rawBytes.length) hEq
  simp [walTmpPath, walLockPath] at hLen

/-! ## 2. Hardware-True Three-Tier Storage + POSIX Inode / Dentry / Symlink / Flock Machine -/

/-- POSIX and hardened vault error codes. -/
inductive PosixErr where
  | enoent        -- Missing pathname / directory entry (`ENOENT`)
  | eexist        -- Exclusive creation target already exists (`EEXIST`)
  | eloop         -- Symlink rejected by `O_NOFOLLOW` or hop limit exceeded (`ELOOP`)
  | ewouldblock   -- Non-blocking `flock(LOCK_EX | LOCK_NB)` contended (`EWOULDBLOCK`)
  | ebadf         -- Invalid or wrong-process file descriptor (`EBADF`)
  | eacces        -- Write attempted on read-only open file description (`EACCES`)
  | eio           -- Physical media / controller flush failure (`EIO`)
  | einval        -- Malformed wire framing or invalid argument (`EINVAL`)
  | epoisoned     -- `CuttleFS`/`fsyncgate` sticky handle poison latched
  | elockseal     -- Dual-bound `lockGenesisId` or locked `st_ino` mismatch
  | emac          -- Keyed-MAC authentication failure or wrong `vaultKeyId`
  deriving Repr, DecidableEq

/-- Directory entry target: either a regular persistent `InodeId` or a symbolic link target name. -/
inductive EntryTarget where
  | regular (ino : InodeId)
  | symlink (target : DirName)
  deriving Repr, DecidableEq

/-- Explicit POSIX directory entry (`d_name ↦ EntryTarget`). -/
structure Dentry where
  name   : DirName
  target : EntryTarget
  deriving Repr, DecidableEq

/-- Kernel in-memory directory inode holding unsynced directory entries. -/
structure DirInode where
  unsyncedEntries : List (DirName × EntryTarget) := []
  deriving Repr, DecidableEq

/-- Kernel open file description (`struct file`): bound to `InodeId` (NOT pathname!), refcounted
    across per-process `(Pid × FdId)` descriptors (`dup` / `fork` / `close`), and carrying
    `CuttleFS` / Linux `errseq_t` sticky `fsync` error state (`stickyFsyncErr`). -/
structure OpenFileDesc where
  inode          : InodeId
  writable       : Bool
  stickyFsyncErr : Bool := false
  deriving Repr, DecidableEq

/-- Per-process file descriptor table (`FdTable : (Pid × FdId) → Option OpenDescriptionId`) paired
    with the kernel open file description table (`OpenDescriptionId → Option OpenFileDesc`) and
    monotonic kernel `nextDescId` allocator. -/
structure OpenFdTable where
  fdRefs       : List ((Pid × FdId) × OpenDescriptionId) := []
  descriptions : List (OpenDescriptionId × OpenFileDesc) := []
  nextDescId   : OpenDescriptionId := 1
  deriving Repr, DecidableEq

/-- Explicit alias highlighting the per-process `(Pid × FdId) → Option OpenDescriptionId` table. -/
abbrev FdTable := OpenFdTable

/-- Resolve `(pid, fd)` in `FdTable` to its underlying kernel `OpenDescriptionId`. -/
@[expose]
def FdTable.lookupDescId (ft : FdTable) (pid : Pid) (fd : FdId) : Option OpenDescriptionId :=
  assocLookup ft.fdRefs (pid, fd)

/-- Resolve `(pid, fd)` through `FdTable` to `(OpenDescriptionId, OpenFileDesc)`. -/
@[expose] def resolveOpenFd (t : OpenFdTable) (pid : Pid) (fd : FdId) :
    Option (OpenDescriptionId × OpenFileDesc) :=
  match assocLookup t.fdRefs (pid, fd) with
  | none => none
  | some descId =>
    match assocLookup t.descriptions descId with
    | none => none
    | some desc => some (descId, desc)

/-- Kernel volatile advisory `flock(2)` table (`InodeId → Option OpenDescriptionId`), keyed by
    `InodeId` and owned by kernel **open file description** (`man 2 flock`), NOT `Pid`! -/
structure FlockTable where
  locks : List (InodeId × OpenDescriptionId) := []
  deriving Repr, DecidableEq

/-- Query the exclusive `LOCK_EX` `OpenDescriptionId` owner of `ino` in `FlockTable`. -/
@[expose]
def FlockTable.owner (ft : FlockTable) (ino : InodeId) : Option OpenDescriptionId :=
  assocLookup ft.locks ino

instance : CoeFun FlockTable (fun _ => InodeId → Option OpenDescriptionId) where
  coe := FlockTable.owner

/-- Kernel volatile per-inode dirty page cache (`InodePageCache`). -/
structure InodePageCache where
  dirtyFiles : List (InodeId × List UInt8) := []
  deriving Repr, DecidableEq

/-- **Tier (a) Kernel Volatile State**: lost on both `KernelPanicCrash` and `PowerLossCrash`. -/
structure KernelVolatileState where
  openFds    : OpenFdTable := {}
  flockTable : FlockTable := {}
  pageCache  : InodePageCache := {}
  dirInode   : DirInode := {}
  deriving Repr, DecidableEq

/-- **Tier (b) Drive Volatile Write-Back Cache (`DriveWriteCache`)**:
    Survives OS `KernelPanicCrash` (controller DRAM remains powered and drains to NAND),
    but is **lost or sector-torn** on `PowerLossCrash` unless flushed via `F_FULLFSYNC`/`REQ_FUA`! -/
structure DriveWriteCache where
  cachedFiles      : List (InodeId × List UInt8) := []
  cachedDirEntries : Option (List (DirName × EntryTarget)) := none
  deriving Repr, DecidableEq

/-- Hardware sector/page atomicity width on underlying block media (`512B` legacy LBA or `4KiB` 4Kn). -/
inductive SectorSize where
  | bytes512
  | bytes4096
  deriving Repr, DecidableEq

/-- Exact byte width of a physical sector (`512` or `4096`). -/
def SectorSize.byteWidth : SectorSize → Nat
  | .bytes512  => 512
  | .bytes4096 => 4096

theorem SectorSize.byteWidth_pos (g : SectorSize) : 0 < g.byteWidth := by
  cases g <;> decide

/-- Per-sector physical outcome when power fails mid-DMA or mid-NAND page program. -/
inductive SectorTearChoice where
  | keepOldSector
  | writeNewSector
  | corruptProgramPage (corruptedBytes : List UInt8)
  deriving Repr, DecidableEq

/-- Adversarial sector torn-write mask governing uncommitted writes during `PowerLossCrash`. -/
structure SectorTearMask where
  geometry      : SectorSize := .bytes512
  sectorChoices : List SectorTearChoice := []
  deriving Repr, DecidableEq

/-- Canonical power-loss mask where all volatile caches evaporate without reaching NAND media. -/
def SectorTearMask.dropAllVolatile : SectorTearMask :=
  { geometry := .bytes512, sectorChoices := [] }

/-- Reassemble `width`-byte sectors across `oldBytes` (NAND) and `newBytes` (in-flight write). -/
def mixSectors (width : Nat) : List SectorTearChoice → List UInt8 → List UInt8 → List UInt8
  | [], oldBytes, _ => oldBytes
  | c :: cs, oldBytes, newBytes =>
    let headSlice :=
      match c with
      | .keepOldSector => oldBytes.take width
      | .writeNewSector => newBytes.take width
      | .corruptProgramPage raw => raw.take width
    headSlice ++ mixSectors width cs (oldBytes.drop width) (newBytes.drop width)

/-- Resolve physical NAND contents of an inode under `PowerLossCrash`:
    - If `pendingOpt = none` (no uncommitted write in `InodePageCache` or `DriveWriteCache`),
      NAND cells are idle and preserved verbatim (`nandBytes`).
    - If `pendingOpt = some pendingBytes`, `mixSectors` applies the hardware `SectorTearMask`. -/
def resolveInodePowerLoss (mask : SectorTearMask) (nandBytes : List UInt8)
    (pendingOpt : Option (List UInt8)) : List UInt8 :=
  match pendingOpt with
  | none => nandBytes
  | some pendingBytes => mixSectors mask.geometry.byteWidth mask.sectorChoices nandBytes pendingBytes

@[simp]
theorem resolveInodePowerLoss_none (mask : SectorTearMask) (nandBytes : List UInt8) :
    resolveInodePowerLoss mask nandBytes none = nandBytes := by rfl

/-- **Tier (c) Non-Volatile NAND Media (`NandBlocks`)**: persistent directory entries, file data
    blocks, and strictly monotonic inode allocator `nextInode`. -/
structure NandBlocks where
  dirNandEntries : List (DirName × EntryTarget) := []
  fileBlocks     : List (InodeId × List UInt8) := []
  nextInode      : InodeId := 1
  deriving Repr, DecidableEq

/-- Complete three-tier hardware + POSIX filesystem state. -/
structure PosixFsState where
  kernel     : KernelVolatileState := {}
  driveCache : DriveWriteCache := {}
  nand       : NandBlocks := {}
  nextFd     : FdId := 3
  deriving Repr, DecidableEq

/-- Fresh formatted empty POSIX directory state. -/
@[expose] def PosixFsState.empty : PosixFsState := {}

/-- Pending volatile write for `ino` (kernel `InodePageCache` shadows `DriveWriteCache`). -/
@[expose] def pendingVolatileWrite (st : PosixFsState) (ino : InodeId) : Option (List UInt8) :=
  match assocLookup st.kernel.pageCache.dirtyFiles ino with
  | some dirty => some dirty
  | none => assocLookup st.driveCache.cachedFiles ino

/-- Effective coherent file bytes visible to `read`/`pread` across the 3-tier hierarchy:
    `InodePageCache` → `DriveWriteCache` → `NandBlocks`. -/
@[expose] def readInodeHierarchy (st : PosixFsState) (ino : InodeId) : Option (List UInt8) :=
  match pendingVolatileWrite st ino with
  | some pending => some pending
  | none => assocLookup st.nand.fileBlocks ino

/-- `O_NOFOLLOW` dentry resolution: rejects `.symlink` immediately with `.eloop`. -/
def resolveDentryNoFollow (entries : List (DirName × EntryTarget)) (name : DirName) :
    Except PosixErr InodeId :=
  match assocLookup entries name with
  | none => .error .enoent
  | some (.regular ino) => .ok ino
  | some (.symlink _) => .error .eloop

/-- Symlink-following dentry resolution (bounded by `fuel` hops, returning `.eloop` on cycles). -/
def resolveDentryFollow (entries : List (DirName × EntryTarget)) :
    Nat → DirName → Except PosixErr InodeId
  | 0, _ => .error .eloop
  | fuel + 1, name =>
    match assocLookup entries name with
    | none => .error .enoent
    | some (.regular ino) => .ok ino
    | some (.symlink target) => resolveDentryFollow entries fuel target

/-- Open an existing regular file with `O_NOFOLLOW` (NO `O_CREAT`).
    Allocates a fresh kernel `OpenDescriptionId` (`nextDescId`) so two independent `open` calls
    in the **same** process receive distinct `OpenDescriptionId`s and contend under `flock(2)`! -/
def posixOpenExistingNoFollow (st : PosixFsState) (pid : Pid) (name : DirName)
    (writable : Bool) : Except PosixErr (PosixFsState × FdId) :=
  match resolveDentryNoFollow st.kernel.dirInode.unsyncedEntries name with
  | .error e => .error e
  | .ok ino =>
    let fd := st.nextFd
    let descId := st.kernel.openFds.nextDescId
    let desc : OpenFileDesc := { inode := ino, writable := writable, stickyFsyncErr := false }
    let fdRefs' := assocInsert (pid, fd) descId st.kernel.openFds.fdRefs
    let descs' := assocInsert descId desc st.kernel.openFds.descriptions
    .ok ({ st with
            kernel := { st.kernel with
                          openFds := { fdRefs := fdRefs'
                                       descriptions := descs'
                                       nextDescId := descId + 1 } }
            nextFd := fd + 1 }, fd)

/-- Create a brand-new regular file with `O_CREAT | O_EXCL | O_NOFOLLOW` (fails with `.eexist`
    if `name` exists even as a dangling symlink!), allocating a fresh `OpenDescriptionId`. -/
def posixCreateExclNoFollow (st : PosixFsState) (pid : Pid) (name : DirName) :
    Except PosixErr (PosixFsState × FdId × InodeId) :=
  match assocLookup st.kernel.dirInode.unsyncedEntries name with
  | some _ => .error .eexist
  | none =>
    let ino := st.nand.nextInode
    let fd := st.nextFd
    let descId := st.kernel.openFds.nextDescId
    let desc : OpenFileDesc := { inode := ino, writable := true, stickyFsyncErr := false }
    let entries' := assocInsert name (.regular ino) st.kernel.dirInode.unsyncedEntries
    let fdRefs' := assocInsert (pid, fd) descId st.kernel.openFds.fdRefs
    let descs' := assocInsert descId desc st.kernel.openFds.descriptions
    let blocks' := assocInsert ino [] st.nand.fileBlocks
    .ok ({ kernel := { st.kernel with
                        openFds := { fdRefs := fdRefs'
                                     descriptions := descs'
                                     nextDescId := descId + 1 }
                        dirInode := { unsyncedEntries := entries' } }
           driveCache := st.driveCache
           nand := { st.nand with
                      fileBlocks := blocks'
                      nextInode := ino + 1 }
           nextFd := fd + 1 }, fd, ino)

/-- POSIX `dup(oldFd)`: allocates a fresh descriptor `newFd` in `pid` referencing the **same**
    kernel `OpenDescriptionId` (`man 2 dup` / `man 2 flock`). -/
def posixDup (st : PosixFsState) (pid : Pid) (oldFd : FdId) :
    Except PosixErr (PosixFsState × FdId) :=
  match assocLookup st.kernel.openFds.fdRefs (pid, oldFd) with
  | none => .error .ebadf
  | some descId =>
    let newFd := st.nextFd
    let fdRefs' := assocInsert (pid, newFd) descId st.kernel.openFds.fdRefs
    .ok ({ st with
            kernel := { st.kernel with
                          openFds := { st.kernel.openFds with fdRefs := fdRefs' } }
            nextFd := newFd + 1 }, newFd)

/-- Clone all `(parentPid, fd) ↦ descId` entries to `(childPid, fd) ↦ descId` (`fork(2)`). -/
def forkCloneFdRefs (parentPid childPid : Pid) :
    List ((Pid × FdId) × OpenDescriptionId) →
    List ((Pid × FdId) × OpenDescriptionId) →
    List ((Pid × FdId) × OpenDescriptionId)
  | [], acc => acc
  | ((p, fd), descId) :: rest, acc =>
    let acc' := if p == parentPid then assocInsert (childPid, fd) descId acc else acc
    forkCloneFdRefs parentPid childPid rest acc'

/-- POSIX `fork(2)` descriptor table inheritance: `childPid` inherits every open `fd` of
    `parentPid`, sharing the underlying kernel `OpenDescriptionId`s (`man 2 flock`). -/
def posixForkFds (st : PosixFsState) (parentPid childPid : Pid) : PosixFsState :=
  let fdRefs' := forkCloneFdRefs parentPid childPid st.kernel.openFds.fdRefs st.kernel.openFds.fdRefs
  { st with
      kernel := { st.kernel with
                    openFds := { st.kernel.openFds with fdRefs := fdRefs' } } }

/-- Plant a symbolic link `name -> target` in `unsyncedEntries` (fails with `.eexist` if `name` exists). -/
def posixCreateSymlink (st : PosixFsState) (name target : DirName) :
    Except PosixErr PosixFsState :=
  match assocLookup st.kernel.dirInode.unsyncedEntries name with
  | some _ => .error .eexist
  | none =>
    let entries' := assocInsert name (.symlink target) st.kernel.dirInode.unsyncedEntries
    .ok { st with kernel := { st.kernel with dirInode := { unsyncedEntries := entries' } } }

/-- Check whether any remaining `(pid, fd)` entry in `fdRefs` still points to `descId`. -/
def descHasAnyRef (fdRefs : List ((Pid × FdId) × OpenDescriptionId))
    (descId : OpenDescriptionId) : Bool :=
  fdRefs.any (fun (_, dId) => dId == descId)

/-- Close descriptor `(pid, fd)`: removes `(pid, fd)` from `fdRefs`; if **zero** remaining
    descriptors in `fdRefs` reference `descId`, destroys `descriptions[descId]` and releases
    any `flock(2)` held by `descId` (`man 2 flock` open-file-description refcount semantics!). -/
def posixCloseFd (st : PosixFsState) (pid : Pid) (fd : FdId) : Except PosixErr PosixFsState :=
  match assocLookup st.kernel.openFds.fdRefs (pid, fd) with
  | none => .error .ebadf
  | some descId =>
    let fdRefs' := assocErase (pid, fd) st.kernel.openFds.fdRefs
    if descHasAnyRef fdRefs' descId then
      .ok { st with
              kernel := { st.kernel with
                            openFds := { st.kernel.openFds with fdRefs := fdRefs' } } }
    else
      let locks' :=
        match assocLookup st.kernel.openFds.descriptions descId with
        | none => st.kernel.flockTable.locks
        | some desc =>
          if assocLookup st.kernel.flockTable.locks desc.inode == some descId then
            assocErase desc.inode st.kernel.flockTable.locks
          else
            st.kernel.flockTable.locks
      let descs' := assocErase descId st.kernel.openFds.descriptions
      .ok { st with
              kernel := { st.kernel with
                            openFds := { st.kernel.openFds with
                                           fdRefs := fdRefs'
                                           descriptions := descs' }
                            flockTable := { locks := locks' } } }

/-- Acquire non-blocking exclusive advisory lock `flock(fd, LOCK_EX | LOCK_NB)`:
    Keyed by `desc.inode` and owned by kernel `OpenDescriptionId` (`descId`), so:
    - Two independent `open` calls in the **same** `pid` have `holderDescId != descId` and
      contend with `.error .ewouldblock`, whereas
    - `dup`ed / `fork`ed descriptors sharing `descId` satisfy `holderDescId == descId`! -/
def posixFlockExNb (st : PosixFsState) (pid : Pid) (fd : FdId) : Except PosixErr PosixFsState :=
  match resolveOpenFd st.kernel.openFds pid fd with
  | none => .error .ebadf
  | some (descId, desc) =>
    match st.kernel.flockTable.owner desc.inode with
    | none =>
      let locks' := assocInsert desc.inode descId st.kernel.flockTable.locks
      .ok { st with kernel := { st.kernel with flockTable := { locks := locks' } } }
    | some holderDescId =>
      if holderDescId == descId then .ok st else .error .ewouldblock

/-- Explicit `flock(fd, LOCK_UN)` unlock releasing the lock held by `fd`'s `OpenDescriptionId`
    across all descriptors sharing that open file description. -/
def posixFlockUnlock (st : PosixFsState) (pid : Pid) (fd : FdId) : Except PosixErr PosixFsState :=
  match resolveOpenFd st.kernel.openFds pid fd with
  | none => .error .ebadf
  | some (descId, desc) =>
    let locks' :=
      if assocLookup st.kernel.flockTable.locks desc.inode == some descId then
        assocErase desc.inode st.kernel.flockTable.locks
      else
        st.kernel.flockTable.locks
    .ok { st with kernel := { st.kernel with flockTable := { locks := locks' } } }

/-- Query `(OpenDescriptionId, st_ino)` (`fstat`) on an open file descriptor owned by `pid`. -/
def posixFstatDescAndInode (st : PosixFsState) (pid : Pid) (fd : FdId) :
    Except PosixErr (OpenDescriptionId × InodeId) :=
  match resolveOpenFd st.kernel.openFds pid fd with
  | none => .error .ebadf
  | some (descId, desc) => .ok (descId, desc.inode)

/-- Query `fstat(fd).st_ino` on an open file descriptor owned by `pid`. -/
def posixFstatInode (st : PosixFsState) (pid : Pid) (fd : FdId) : Except PosixErr InodeId :=
  match resolveOpenFd st.kernel.openFds pid fd with
  | none => .error .ebadf
  | some (_, desc) => .ok desc.inode

/-- Read full file contents from open descriptor `fd` (`pread` from offset 0). -/
def posixPreadAll (st : PosixFsState) (pid : Pid) (fd : FdId) : Except PosixErr (List UInt8) :=
  match resolveOpenFd st.kernel.openFds pid fd with
  | none => .error .ebadf
  | some (_, desc) =>
    if desc.stickyFsyncErr then
      .error .epoisoned
    else
      match readInodeHierarchy st desc.inode with
      | none => .error .eio
      | some bs => .ok bs

/-- Write full payload `bytes` into `InodePageCache` via open writable descriptor `fd`. -/
def posixPwriteAll (st : PosixFsState) (pid : Pid) (fd : FdId) (bytes : List UInt8) :
    Except PosixErr PosixFsState :=
  match resolveOpenFd st.kernel.openFds pid fd with
  | none => .error .ebadf
  | some (_, desc) =>
    if !desc.writable then
      .error .eacces
    else if desc.stickyFsyncErr then
      .error .epoisoned
    else
      let dirty' := assocInsert desc.inode bytes st.kernel.pageCache.dirtyFiles
      .ok { st with kernel := { st.kernel with pageCache := { dirtyFiles := dirty' } } }

/-- Plain POSIX `fsync(2)` WITHOUT `F_FULLFSYNC` / `REQ_FUA`:
    Flushes kernel `InodePageCache` down into the drive's volatile `DriveWriteCache`, leaving
    `NandBlocks` stale until a barrier flush occurs! -/
def posixFsyncVolatileCacheOnly (st : PosixFsState) (pid : Pid) (fd : FdId) :
    Except PosixErr PosixFsState :=
  match resolveOpenFd st.kernel.openFds pid fd with
  | none => .error .ebadf
  | some (_, desc) =>
    if desc.stickyFsyncErr then
      .error .epoisoned
    else
      match assocLookup st.kernel.pageCache.dirtyFiles desc.inode with
      | none => .ok st
      | some dirtyBytes =>
        let pageCache' := assocErase desc.inode st.kernel.pageCache.dirtyFiles
        let driveFiles' := assocInsert desc.inode dirtyBytes st.driveCache.cachedFiles
        .ok { st with
                kernel := { st.kernel with pageCache := { dirtyFiles := pageCache' } }
                driveCache := { st.driveCache with cachedFiles := driveFiles' } }

/-- Plain POSIX directory `fsync` WITHOUT `F_FULLFSYNC` / `REQ_FUA`:
    Pushes `dirInode.unsyncedEntries` only into `DriveWriteCache.cachedDirEntries`. -/
def posixFsyncDirVolatileOnly (st : PosixFsState) : PosixFsState :=
  { st with driveCache := { st.driveCache with
                              cachedDirEntries := some st.kernel.dirInode.unsyncedEntries } }

/-- Full media barrier sync (`F_FULLFSYNC` / `fsync` + `REQ_FUA` + `NVME_CMD_FLUSH`):
    - If `injectEio = true`, models Linux `errseq_t` / `CuttleFS` (`fsyncgate`): drops the failed
      dirty page-cache buffer back to stale media, marks `desc.stickyFsyncErr := true` on the
      kernel `OpenDescriptionId` (`descId`), and returns `.error .eio` with the mutated state!
    - If `injectEio = false`, flushes `fd.inode` completely through `InodePageCache` and
      `DriveWriteCache` into non-volatile `NandBlocks`, clearing both volatile caches for `fd.inode`. -/
def posixSyncAllMedia (st : PosixFsState) (pid : Pid) (fd : FdId) (injectEio : Bool := false) :
    PosixFsState × Except PosixErr Unit :=
  match resolveOpenFd st.kernel.openFds pid fd with
  | none => (st, .error .ebadf)
  | some (descId, desc) =>
    if desc.stickyFsyncErr then
      (st, .error .epoisoned)
    else if injectEio then
      let poisonedDesc := { desc with stickyFsyncErr := true }
      let descs' := assocInsert descId poisonedDesc st.kernel.openFds.descriptions
      let pageCache' := assocErase desc.inode st.kernel.pageCache.dirtyFiles
      let driveFiles' := assocErase desc.inode st.driveCache.cachedFiles
      ({ st with
          kernel := { st.kernel with
                        openFds := { st.kernel.openFds with descriptions := descs' }
                        pageCache := { dirtyFiles := pageCache' } }
          driveCache := { st.driveCache with cachedFiles := driveFiles' } },
       .error .eio)
    else
      match readInodeHierarchy st desc.inode with
      | none => (st, .error .eio)
      | some latestBytes =>
        let pageCache' := assocErase desc.inode st.kernel.pageCache.dirtyFiles
        let driveFiles' := assocErase desc.inode st.driveCache.cachedFiles
        let nandBlocks' := assocInsert desc.inode latestBytes st.nand.fileBlocks
        ({ st with
            kernel := { st.kernel with pageCache := { dirtyFiles := pageCache' } }
            driveCache := { st.driveCache with cachedFiles := driveFiles' }
            nand := { st.nand with fileBlocks := nandBlocks' } },
         .ok ())

/-- Full media barrier sync on the parent directory (`open(dir) + F_FULLFSYNC` / `REQ_FUA`):
    Flushes `dirInode.unsyncedEntries` directly into `nand.dirNandEntries` and clears
    `driveCache.cachedDirEntries` unless `injectEio = true`. -/
@[expose] def posixSyncParentDir (st : PosixFsState) (injectEio : Bool := false) :
    PosixFsState × Except PosixErr Unit :=
  if injectEio then
    (st, .error .eio)
  else
    ({ st with
        driveCache := { st.driveCache with cachedDirEntries := none }
        nand := { st.nand with dirNandEntries := st.kernel.dirInode.unsyncedEntries } },
     .ok ())

/-- POSIX `unlink(name)`: removes `name` from `dirInode.unsyncedEntries` while keeping all
    open file descriptions (`openFds`), `flock` ownership (`flockTable`), and `InodeId` data alive! -/
def posixUnlink (st : PosixFsState) (name : DirName) : Except PosixErr PosixFsState :=
  match assocLookup st.kernel.dirInode.unsyncedEntries name with
  | none => .error .enoent
  | some _ =>
    let entries' := assocErase name st.kernel.dirInode.unsyncedEntries
    .ok { st with kernel := { st.kernel with dirInode := { unsyncedEntries := entries' } } }

/-- Unlink `name` if present (ignoring `.enoent`, used to clear any orphan `.tmp` before `O_EXCL`). -/
@[expose] def posixUnlinkIfPresent (st : PosixFsState) (name : DirName) : PosixFsState :=
  let entries' := assocErase name st.kernel.dirInode.unsyncedEntries
  { st with kernel := { st.kernel with dirInode := { unsyncedEntries := entries' } } }

/-- POSIX atomic `rename(src, dst)`: atomically binds `dst` to `src`'s `EntryTarget` and erases
    `src` inside `dirInode.unsyncedEntries` (does NOT flush `DriveWriteCache` or `NandBlocks`!). -/
def posixRename (st : PosixFsState) (src dst : DirName) : Except PosixErr PosixFsState :=
  match assocLookup st.kernel.dirInode.unsyncedEntries src with
  | none => .error .enoent
  | some target =>
    let afterInsert := assocInsert dst target st.kernel.dirInode.unsyncedEntries
    let entries' := if src == dst then afterInsert else assocErase src afterInsert
    .ok { st with kernel := { st.kernel with dirInode := { unsyncedEntries := entries' } } }

/-- **POSIX Unlink Fidelity Lemma (`posixUnlink_preserves_openFds_and_flock`)**:
    `unlink` removes the directory entry `name` while preserving every open `OpenDescriptionId` and
    every `InodeId` lock in `FlockTable` verbatim. -/
theorem posixUnlink_preserves_openFds_and_flock {st st' : PosixFsState} {name : DirName}
    (hUnl : posixUnlink st name = .ok st') :
    assocLookup st'.kernel.dirInode.unsyncedEntries name = none ∧
    st'.kernel.openFds = st.kernel.openFds ∧
    st'.kernel.flockTable = st.kernel.flockTable ∧
    st'.nand = st.nand := by
  unfold posixUnlink at hUnl
  cases hLook : assocLookup st.kernel.dirInode.unsyncedEntries name with
  | none => rw [hLook] at hUnl; cases hUnl
  | some _ =>
    rw [hLook] at hUnl
    injection hUnl with hEq
    subst hEq
    simp

/-- **Linux/POSIX `flock(2)` Same-Process Independent-Open Contention**:
    For **any** state `st` where `name` resolves (`O_NOFOLLOW`) to a regular inode `ino`, two
    independent `posixOpenExistingNoFollow` calls in the **exact same `pid`** allocate distinct
    `OpenDescriptionId`s (`descId₁ ≠ descId₂`), so after `fd₁` acquires `LOCK_EX | LOCK_NB`,
    `posixFlockExNb` on `fd₂` deterministically fails with **`.error .ewouldblock`**! -/
theorem same_pid_independent_opens_contend_flock_ewouldblock
    (st : PosixFsState) (pid : Pid) (name : DirName) (ino : InodeId) (w₁ w₂ : Bool)
    (hReg : assocLookup st.kernel.dirInode.unsyncedEntries name = some (.regular ino))
    (hFree : st.kernel.flockTable.owner ino = none) :
    ∃ st1 fd₁ st2 st3 fd₂,
      posixOpenExistingNoFollow st pid name w₁ = .ok (st1, fd₁) ∧
      posixFlockExNb st1 pid fd₁ = .ok st2 ∧
      posixOpenExistingNoFollow st2 pid name w₂ = .ok (st3, fd₂) ∧
      FdTable.lookupDescId st3.kernel.openFds pid fd₁ ≠
        FdTable.lookupDescId st3.kernel.openFds pid fd₂ ∧
      posixFlockExNb st3 pid fd₂ = .error .ewouldblock := by
  let fd₁ := st.nextFd
  let d₁ := st.kernel.openFds.nextDescId
  let st1 : PosixFsState :=
    { st with
        kernel := { st.kernel with
                      openFds := { fdRefs := assocInsert (pid, fd₁) d₁ st.kernel.openFds.fdRefs
                                   descriptions := assocInsert d₁
                                     { inode := ino, writable := w₁, stickyFsyncErr := false }
                                     st.kernel.openFds.descriptions
                                   nextDescId := d₁ + 1 } }
        nextFd := fd₁ + 1 }
  let st2 : PosixFsState :=
    { st1 with
        kernel := { st1.kernel with
                      flockTable := { locks := assocInsert ino d₁ st.kernel.flockTable.locks } } }
  let st3 : PosixFsState :=
    { st2 with
        kernel := { st2.kernel with
                      openFds := { fdRefs := assocInsert (pid, fd₁ + 1) (d₁ + 1) st1.kernel.openFds.fdRefs
                                   descriptions := assocInsert (d₁ + 1)
                                     { inode := ino, writable := w₂, stickyFsyncErr := false }
                                     st1.kernel.openFds.descriptions
                                   nextDescId := d₁ + 2 } }
        nextFd := fd₁ + 2 }
  have hFdNe : (pid, fd₁) ≠ (pid, fd₁ + 1) := by
    intro hEq
    exact Nat.ne_of_lt (Nat.lt_succ_self fd₁) (Prod.mk.inj hEq).2
  have hDescNe : d₁ ≠ d₁ + 1 := Nat.ne_of_lt (Nat.lt_succ_self d₁)
  have hDescBeqFalse : (d₁ == d₁ + 1) = false := by
    cases hb : (d₁ == d₁ + 1)
    · rfl
    · exfalso; exact hDescNe (eq_of_beq hb)
  refine ⟨st1, fd₁, st2, st3, fd₁ + 1, ?_, ?_, ?_, ?_, ?_⟩
  · unfold posixOpenExistingNoFollow resolveDentryNoFollow
    rw [hReg]
  · unfold posixFlockExNb resolveOpenFd
    dsimp only [st1]
    simp only [assocLookup_insert_self, hFree]
    rfl
  · unfold posixOpenExistingNoFollow resolveDentryNoFollow
    dsimp only [st2, st1]
    rw [hReg]
  · unfold FdTable.lookupDescId
    dsimp only [st3, st1]
    simp only [assocLookup_insert, hFdNe, ↓reduceIte]
    intro hSomeEq
    injection hSomeEq with hEqD
    exact hDescNe hEqD
  · unfold posixFlockExNb resolveOpenFd FlockTable.owner
    dsimp only [st3, st2]
    simp only [assocLookup_insert_self, hDescBeqFalse, Bool.false_eq_true, ↓reduceIte]

/-- **Linux/POSIX `flock(2)` Shared-Description Refcount Semantics**:
    Duplicating a locked descriptor via `posixDup` (and inheriting via `posixForkFds`) shares a
    single `OpenDescriptionId`:
    1. `posixFlockExNb` on `dupFd` and on the forked child's `(childPid, fd₁)` **succeeds** (`.ok`)
       because `flock` belongs to the shared `OpenDescriptionId` (not a per-thread/per-fd mutex!),
    2. Closing `fd₁` and closing `(childPid, fd₁)` while `dupFd` remains open **keeps** the `flock`
       alive on `ino` (so an independent `open` still gets `.ewouldblock`), and
    3. Closing `dupFd` (the **last** open reference to that `OpenDescriptionId`) **releases**
       `flockTable.owner ino = none`! -/
theorem dup_and_fork_shared_description_shares_flock_until_last_close :
    let filePath : DirName := ⟨[0x6b, 0x65, 0x79]⟩
    let parentPid : Pid := 100
    let childPid : Pid := 200
    ∃ s1 fd₁ ino s2 s3 dupFd s5 s6 s7 s8,
      posixCreateExclNoFollow PosixFsState.empty parentPid filePath = .ok (s1, fd₁, ino) ∧
      posixFlockExNb s1 parentPid fd₁ = .ok s2 ∧
      posixDup s2 parentPid fd₁ = .ok (s3, dupFd) ∧
      let s4 := posixForkFds s3 parentPid childPid
      FdTable.lookupDescId s4.kernel.openFds parentPid fd₁ = some 1 ∧
      FdTable.lookupDescId s4.kernel.openFds parentPid dupFd = some 1 ∧
      FdTable.lookupDescId s4.kernel.openFds childPid fd₁ = some 1 ∧
      (posixFlockExNb s4 parentPid dupFd).isOk = true ∧
      (posixFlockExNb s4 childPid fd₁).isOk = true ∧
      posixCloseFd s4 parentPid fd₁ = .ok s5 ∧
      posixCloseFd s5 childPid fd₁ = .ok s6 ∧
      posixCloseFd s6 childPid dupFd = .ok s7 ∧
      s7.kernel.flockTable.owner ino = some 1 ∧
      posixCloseFd s7 parentPid dupFd = .ok s8 ∧
      s8.kernel.flockTable.owner ino = none := by
  exact ⟨_, _, _, _, _, _, _, _, _, _,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 3. Crash Hoare Logic (`KernelPanicCrash`, `PowerLossCrash`, `CrashStep`, `CrashHoareSpec`) -/

/-- Directory persistence resolution on `PowerLossCrash` when directory updates were not yet synced. -/
inductive DirCrashOutcome where
  | revertToNand     -- Unsynced volatile directory updates evaporate; NAND dentries survive
  | flushPendingDir  -- Background metadata writeback reached NAND before power died (`ext4` reorder!)
  deriving Repr, DecidableEq

/-- **OS Kernel Panic (`KernelPanicCrash`)**:
    Wipes all Tier-(a) `KernelVolatileState` (`openFds`, `flockTable`, `InodePageCache`, unsynced
    kernel `dirInode`), while Tier-(b) `DriveWriteCache` drains cleanly into Tier-(c) `NandBlocks`
    because drive controller power was never interrupted. -/
@[expose] def KernelPanicCrash (st : PosixFsState) : PosixFsState :=
  let drainedFiles :=
    mapAssocValues
      (fun ino nandBytes => (assocLookup st.driveCache.cachedFiles ino).getD nandBytes)
      st.nand.fileBlocks
  let drainedDir := st.driveCache.cachedDirEntries.getD st.nand.dirNandEntries
  { kernel := { openFds := {}
                flockTable := {}
                pageCache := {}
                dirInode := { unsyncedEntries := drainedDir } }
    driveCache := {}
    nand := { st.nand with
                dirNandEntries := drainedDir
                fileBlocks := drainedFiles }
    nextFd := 3 }

/-- **Hardware Power Loss (`PowerLossCrash`)**:
    Wipes both Tier-(a) `KernelVolatileState` and Tier-(b) `DriveWriteCache`; any inode with an
    uncommitted write in `InodePageCache` or `DriveWriteCache` undergoes `512B`/`4KiB` sector
    torn-write resolution (`tearFn ino`), while synced inodes (`pendingVolatileWrite = none`)
    remain untouched on `NandBlocks`. -/
@[expose] def PowerLossCrash (dirPick : DirCrashOutcome) (tearFn : InodeId → SectorTearMask)
    (st : PosixFsState) : PosixFsState :=
  let crashedFiles :=
    mapAssocValues
      (fun ino nandBytes =>
        resolveInodePowerLoss (tearFn ino) nandBytes (pendingVolatileWrite st ino))
      st.nand.fileBlocks
  let pendingDir :=
    match st.driveCache.cachedDirEntries with
    | some cached => cached
    | none => st.kernel.dirInode.unsyncedEntries
  let crashedDir :=
    match dirPick with
    | .revertToNand => st.nand.dirNandEntries
    | .flushPendingDir => pendingDir
  { kernel := { openFds := {}
                flockTable := {}
                pageCache := {}
                dirInode := { unsyncedEntries := crashedDir } }
    driveCache := {}
    nand := { st.nand with
                dirNandEntries := crashedDir
                fileBlocks := crashedFiles }
    nextFd := 3 }

/-- Single crash transition relation unifying `KernelPanicCrash` and `PowerLossCrash`. -/
inductive CrashStep : PosixFsState → PosixFsState → Prop where
  | kernelPanic (st : PosixFsState) :
      CrashStep st (KernelPanicCrash st)
  | powerLoss (dirPick : DirCrashOutcome) (tearFn : InodeId → SectorTearMask) (st : PosixFsState) :
      CrashStep st (PowerLossCrash dirPick tearFn st)

/-- Process restart closes descriptors and drops advisory locks, but is not a storage barrier:
    the kernel page cache and every storage tier retain their exact previous contents. -/
def ProcessRestart (st : PosixFsState) : PosixFsState :=
  { st with kernel := { st.kernel with openFds := {}, flockTable := {} } }

theorem processRestart_preserves_dirty_pages (st : PosixFsState) :
    (ProcessRestart st).kernel.pageCache = st.kernel.pageCache ∧
    (ProcessRestart st).driveCache = st.driveCache ∧
    (ProcessRestart st).nand = st.nand := ⟨rfl, rfl, rfl⟩

theorem processRestart_dirty_page_remains_readable (st : PosixFsState) (ino : InodeId)
    (bytes : List UInt8) (hDirty : assocLookup st.kernel.pageCache.dirtyFiles ino = some bytes) :
    readInodeHierarchy (ProcessRestart st) ino = some bytes ∧
      assocLookup (ProcessRestart st).nand.fileBlocks ino = assocLookup st.nand.fileBlocks ino := by
  have hPending : pendingVolatileWrite (ProcessRestart st) ino = some bytes := by
    simp [pendingVolatileWrite, ProcessRestart, hDirty]
  exact ⟨by simp [readInodeHierarchy, hPending], rfl⟩

/-- Restart alone supplies no durable-release event: a dirty page survives for subsequent reads,
    while NAND is unchanged until an explicit successful media sync. -/
theorem processRestart_is_not_fsync (st : PosixFsState) (ino : InodeId) (bytes : List UInt8)
    (hDirty : assocLookup st.kernel.pageCache.dirtyFiles ino = some bytes) :
    (ProcessRestart st).kernel.flockTable.locks = [] ∧
      assocLookup (ProcessRestart st).kernel.pageCache.dirtyFiles ino = some bytes ∧
      assocLookup (ProcessRestart st).nand.fileBlocks ino = assocLookup st.nand.fileBlocks ino := by
  exact ⟨rfl, hDirty, rfl⟩

/-- **Synced Inode Crash Immunity (`syncedInode_immune_to_crashStep`)**:
    Any inode `ino` with zero uncommitted writes in `InodePageCache` and `DriveWriteCache`
    preserves its exact `NandBlocks` payload across **every** `CrashStep` (for all `512B`/`4KiB`
    `SectorTearMask`s and all `DirCrashOutcome`s). -/
theorem syncedInode_immune_to_crashStep {st crashed : PosixFsState} {ino : InodeId}
    (hPageClean : assocLookup st.kernel.pageCache.dirtyFiles ino = none)
    (hDriveClean : assocLookup st.driveCache.cachedFiles ino = none)
    (hCrash : CrashStep st crashed) :
    assocLookup crashed.nand.fileBlocks ino = assocLookup st.nand.fileBlocks ino ∧
    readInodeHierarchy crashed ino = assocLookup st.nand.fileBlocks ino := by
  have hPend : pendingVolatileWrite st ino = none := by
    unfold pendingVolatileWrite
    rw [hPageClean, hDriveClean]
  cases hCrash with
  | kernelPanic _ =>
    dsimp only [KernelPanicCrash, readInodeHierarchy, pendingVolatileWrite]
    simp only [assocLookup_nil, assocLookup_mapAssocValues, hDriveClean, Option.getD_none]
    exact ⟨option_map_id_ext (fun _ => rfl) _, option_map_id_ext (fun _ => rfl) _⟩
  | powerLoss dirPick tearFn _ =>
    dsimp only [PowerLossCrash, readInodeHierarchy, pendingVolatileWrite]
    simp only [assocLookup_nil, assocLookup_mapAssocValues]
    have hFn : ∀ nb : List UInt8,
        resolveInodePowerLoss (tearFn ino) nb (pendingVolatileWrite st ino) = nb := by
      intro nb
      rw [hPend]
      rfl
    exact ⟨option_map_id_ext hFn _, option_map_id_ext hFn _⟩

/-- **Synced Directory Crash Immunity (`syncedDir_immune_to_crashStep`)**:
    When `dirInode.unsyncedEntries = nand.dirNandEntries` and `driveCache.cachedDirEntries = none`,
    every `CrashStep` preserves `dirNandEntries` and reloads `unsyncedEntries` identically. -/
theorem syncedDir_immune_to_crashStep {st crashed : PosixFsState}
    (hDirSynced : st.kernel.dirInode.unsyncedEntries = st.nand.dirNandEntries)
    (hDriveDirClean : st.driveCache.cachedDirEntries = none)
    (hCrash : CrashStep st crashed) :
    crashed.nand.dirNandEntries = st.nand.dirNandEntries ∧
    crashed.kernel.dirInode.unsyncedEntries = st.nand.dirNandEntries := by
  cases hCrash with
  | kernelPanic _ =>
    simp [KernelPanicCrash, hDriveDirClean]
  | powerLoss dirPick tearFn _ =>
    cases dirPick <;> simp [PowerLossCrash, hDriveDirClean, hDirSynced]

/-- **Post-Crash Idempotence (`crashStep_idempotent`)**:
    Immediately after any `CrashStep s₀ s₁`, all volatile caches are empty and synced with NAND,
    so any second crash `CrashStep s₁ s₂` during recovery leaves `s₂ = s₁`! -/
theorem crashStep_idempotent {s₀ s₁ s₂ : PosixFsState}
    (h1 : CrashStep s₀ s₁) (h2 : CrashStep s₁ s₂) : s₂ = s₁ := by
  have hClean :
      s₁.kernel.openFds = {} ∧
      s₁.kernel.flockTable = {} ∧
      s₁.kernel.pageCache = {} ∧
      s₁.driveCache = {} ∧
      s₁.kernel.dirInode.unsyncedEntries = s₁.nand.dirNandEntries ∧
      s₁.nextFd = 3 := by
    cases h1 <;> simp [KernelPanicCrash, PowerLossCrash]
  rcases hClean with ⟨hFds, hFlk, hPg, hDrv, hDir, hNextFd⟩
  cases h2 with
  | kernelPanic _ =>
    have hMap :
        mapAssocValues (fun ino nb => (assocLookup s₁.driveCache.cachedFiles ino).getD nb)
          s₁.nand.fileBlocks = s₁.nand.fileBlocks := by
      apply mapAssocValues_id
      intro ino nb
      rw [hDrv]
      rfl
    cases s₁ with
    | mk k d n nf =>
      cases k with
      | mk o fl p di =>
        cases di with
        | mk ue =>
          cases n with
          | mk dne fb ni =>
            dsimp only at hFds hFlk hPg hDrv hDir hNextFd hMap
            subst hFds hFlk hPg hDrv hDir hNextFd
            unfold KernelPanicCrash
            dsimp only
            rw [hMap]
            rfl
  | powerLoss dirPick tearFn _ =>
    have hMap :
        mapAssocValues
          (fun ino nb => resolveInodePowerLoss (tearFn ino) nb (pendingVolatileWrite s₁ ino))
          s₁.nand.fileBlocks = s₁.nand.fileBlocks := by
      apply mapAssocValues_id
      intro ino nb
      have hPend : pendingVolatileWrite s₁ ino = none := by
        unfold pendingVolatileWrite
        rw [hPg, hDrv]
        rfl
      rw [hPend]
      rfl
    cases s₁ with
    | mk k d n nf =>
      cases k with
      | mk o fl p di =>
        cases di with
        | mk ue =>
          cases n with
          | mk dne fb ni =>
            dsimp only at hFds hFlk hPg hDrv hDir hNextFd hMap
            subst hFds hFlk hPg hDrv hDir hNextFd
            unfold PowerLossCrash
            dsimp only
            rw [hMap]
            cases dirPick <;> rfl

/-- **Crash Hoare Logic Specification (`CrashHoareSpec`)**:
    Certifies that an operation with intermediate step trace `intermediates` satisfies:
    1. `normal_post`: successful execution establishes `Post`,
    2. `crash_safe`: crashing from **any** pre/intermediate/post state in `intermediates st`
       establishes `CrashInv`, and
    3. `crash_idempotent`: `CrashInv` is preserved across arbitrary repeated crashes during recovery! -/
structure CrashHoareSpec {α : Type}
    (Pre : PosixFsState → Prop)
    (intermediates : PosixFsState → List PosixFsState)
    (run : PosixFsState → PosixFsState × Except PosixErr α)
    (Post : PosixFsState → α → Prop)
    (CrashInv : PosixFsState → Prop) : Prop where
  normal_post : ∀ st st' out, Pre st → run st = (st', .ok out) → Post st' out
  crash_safe : ∀ st mid crashed,
    Pre st → mid ∈ intermediates st → CrashStep mid crashed → CrashInv crashed
  crash_idempotent : ∀ s₁ s₂, CrashInv s₁ → CrashStep s₁ s₂ → CrashInv s₂

#export_eqns KernelPanicCrash PowerLossCrash posixCreateExclNoFollow posixPwriteAll posixSyncAllMedia posixSyncParentDir posixUnlinkIfPresent posixRename

#export_eqns posixCloseFd posixOpenExistingNoFollow resolveDentryNoFollow posixFlockExNb posixFstatDescAndInode posixPreadAll


#export_eqns descHasAnyRef posixUnlink posixCreateSymlink

/-- Externally visible Round-1 network message consuming threshold MPC nonce, prep cursor, & RNG seed. -/
structure Round1NetworkPacket where
  txId                  : List UInt8
  msgContext            : List UInt8
  policySpendCharged    : Nat
  leafOrEpoch           : Nat
  baggyCodewordDigest   : List UInt8
  rngSeedGen            : Nat
  mpcPrepCursor         : Nat
  mpcNonceSlot          : Nat
  deriving Repr, DecidableEq

/-- Helper reading a durable 64-bit counter file via `O_NOFOLLOW` + `pread` + `decodeU64BeNat`. -/
def readDurableU64Counter (st : PosixFsState) (pid : Pid) (path : DirName) : Option Nat :=
  match posixOpenExistingNoFollow st pid path false with
  | .error _ => none
  | .ok (st1, fd) =>
    match posixPreadAll st1 pid fd with
    | .error _ => none
    | .ok raw => decodeU64BeNat raw

/-- **Mutation Witness (`tooth_split_subordinate_wals_crash_between_commits_causes_resource_desync`)**:
    Demonstrates why storing subordinate ceremony authorities (`beltPath` for `BeltLatch`/`Frontier`
    and `noncePath` for the threshold MPC Round-1 nonce cursor) in **separate** WAL files instead of
    a single unified `CeremonyJournalRecord` is unsound under crash faults:
    when `PowerLossCrash` strikes after `beltPath` commits watermark `1` (and Round-1 packet `pkt`
    using `(leafOrEpoch = 0, mpcNonceSlot = 0)` is emitted) but **before** `noncePath` commits `1`,
    post-crash recovery observes `belt = some 1` alongside `nonce = some 0` (`¬ (pkt.mpcNonceSlot < 0)`),
    desynchronizing the two authorities and allowing Round-1 MPC nonce `0` reuse! -/
theorem tooth_split_subordinate_wals_crash_between_commits_causes_resource_desync :
    let beltPath : DirName := ⟨[0x62]⟩
    let noncePath : DirName := ⟨[0x6e]⟩
    let beltTmp : DirName := walTmpPath beltPath
    let b0 := encodeU64BeNat 0
    let b1 := encodeU64BeNat 1
    let pkt : Round1NetworkPacket :=
      { txId := List.replicate 32 0xAA
        msgContext := [0x01]
        policySpendCharged := 10
        leafOrEpoch := 0
        baggyCodewordDigest := List.replicate 32 0xBB
        rngSeedGen := 0
        mpcPrepCursor := 0
        mpcNonceSlot := 0 }
    ∃ s1 s2 s3 s4 s5 s6 s7 s8 sInit s9 s10 s11 s12 s13 sBeltCommitted,
      posixCreateExclNoFollow PosixFsState.empty 1 beltPath = .ok (s1, 3, 1) ∧
      posixPwriteAll s1 1 3 b0 = .ok s2 ∧
      posixSyncAllMedia s2 1 3 false = (s3, .ok ()) ∧
      posixCloseFd s3 1 3 = .ok s4 ∧
      posixCreateExclNoFollow s4 1 noncePath = .ok (s5, 4, 2) ∧
      posixPwriteAll s5 1 4 b0 = .ok s6 ∧
      posixSyncAllMedia s6 1 4 false = (s7, .ok ()) ∧
      posixCloseFd s7 1 4 = .ok s8 ∧
      posixSyncParentDir s8 false = (sInit, .ok ()) ∧
      readDurableU64Counter sInit 2 beltPath = some 0 ∧
      readDurableU64Counter sInit 2 noncePath = some 0 ∧
      -- Mutated split-WAL Round-1 commit: `beltPath` commits `1`, then `PowerLossCrash` strikes
      -- before `noncePath` commits `1`!
      posixCreateExclNoFollow sInit 1 beltTmp = .ok (s9, 5, 3) ∧
      posixPwriteAll s9 1 5 b1 = .ok s10 ∧
      posixSyncAllMedia s10 1 5 false = (s11, .ok ()) ∧
      posixCloseFd s11 1 5 = .ok s12 ∧
      posixRename s12 beltTmp beltPath = .ok s13 ∧
      posixSyncParentDir s13 false = (sBeltCommitted, .ok ()) ∧
      let sCrashed := PowerLossCrash .revertToNand (fun _ => SectorTearMask.dropAllVolatile) sBeltCommitted
      readDurableU64Counter sCrashed 2 beltPath = some 1 ∧
      readDurableU64Counter sCrashed 2 noncePath = some 0 ∧
      pkt.leafOrEpoch < 1 ∧
      ¬ (pkt.mpcNonceSlot < 0) := by
  have h0Lt64 : 0 < 2 ^ 64 := Nat.pow_pos (by decide : 0 < 2)
  have h1Lt64 : 1 < 2 ^ 64 :=
    Nat.lt_trans (lt_two_pow_32_of_le_8192 (by decide : 1 ≤ 8192))
      two_pow_32_lt_two_pow_64
  have hDec0 : decodeU64BeNat (encodeU64BeNat 0) = some 0 := decodeU64BeNat_encodeU64BeNat h0Lt64
  have hDec1 : decodeU64BeNat (encodeU64BeNat 1) = some 1 := decodeU64BeNat_encodeU64BeNat h1Lt64
  refine ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ?_, ?_,
    rfl, rfl, rfl, rfl, rfl, rfl,
    ?_, ?_, by decide, by decide⟩
  · exact hDec0
  · exact hDec0
  · exact hDec1
  · exact hDec0

/-- Concrete base filename `"vault.wal"` (`[0x76, 0x61, 0x75, 0x6c, 0x74, 0x2e, 0x77, 0x61, 0x6c]`). -/
def concreteBasePath : DirName :=
  ⟨[0x76, 0x61, 0x75, 0x6c, 0x74, 0x2e, 0x77, 0x61, 0x6c]⟩

/-- Helper reading raw file bytes at `path` via `O_NOFOLLOW` + `pread`. -/
def readRawFileNoFollow (st : PosixFsState) (pid : Pid) (path : DirName) :
    Except PosixErr (List UInt8) :=
  match posixOpenExistingNoFollow st pid path false with
  | .error e => .error e
  | .ok (st1, fd) => posixPreadAll st1 pid fd

set_option maxRecDepth 4096 in
/-- **#tooth 1 (`tooth_rename_without_tmp_sync_exposes_torn_or_garbage_file`)**:
    Models the `ext4` `data=writeback` / delayed-allocation reorder hazard:
    if a mutated `replaceAtomic` writes `newBytes` (`512` bytes of `0xBB` + `[0xCC]`) to `.tmp`
    and calls `posixRename(.tmp, concreteBasePath)` **without** `posixSyncAllMedia(.tmp)` first,
    then on `PowerLossCrash .flushPendingDir`:
    1. Under `SectorTearMask.dropAllVolatile`, `concreteBasePath` recovers as **0-length `[]`**
       (neither `oldBytes` nor `newBytes`!), and
    2. Under a 512B partial sector flush `{ geometry := .bytes512, sectorChoices := [.writeNewSector, .keepOldSector] }`,
       `concreteBasePath` recovers as a **512-byte torn half-write** `List.replicate 512 0xBB`
       (strictly neither `oldBytes` nor `newBytes`)! -/
theorem tooth_rename_without_tmp_sync_exposes_torn_or_garbage_file :
    let oldBytes : List UInt8 := [0xAA, 0xAA, 0xAA, 0xAA]
    let newBytes : List UInt8 := List.replicate 512 0xBB ++ [0xCC]
    let tmpPath : DirName := walTmpPath concreteBasePath
    let halfTear : SectorTearMask :=
      { geometry := .bytes512, sectorChoices := [.writeNewSector, .keepOldSector] }
    ∃ s1 s2 s3 s4 sOld s5 s6 s7 sBuggyRenamed,
      posixCreateExclNoFollow PosixFsState.empty 1 concreteBasePath = .ok (s1, 3, 1) ∧
      posixPwriteAll s1 1 3 oldBytes = .ok s2 ∧
      posixSyncAllMedia s2 1 3 false = (s3, .ok ()) ∧
      posixCloseFd s3 1 3 = .ok s4 ∧
      posixSyncParentDir s4 false = (sOld, .ok ()) ∧
      -- Mutated update: write `.tmp` and `rename` WITHOUT `posixSyncAllMedia(.tmp)`!
      posixCreateExclNoFollow sOld 1 tmpPath = .ok (s5, 4, 2) ∧
      posixPwriteAll s5 1 4 newBytes = .ok s6 ∧
      posixCloseFd s6 1 4 = .ok s7 ∧
      posixRename s7 tmpPath concreteBasePath = .ok sBuggyRenamed ∧
      let sCrashZero :=
        PowerLossCrash .flushPendingDir (fun _ => SectorTearMask.dropAllVolatile) sBuggyRenamed
      let sCrashTorn :=
        PowerLossCrash .flushPendingDir (fun _ => halfTear) sBuggyRenamed
      readRawFileNoFollow sCrashZero 2 concreteBasePath = .ok [] ∧
      ([] : List UInt8) ≠ oldBytes ∧
      ([] : List UInt8) ≠ newBytes ∧
      readRawFileNoFollow sCrashTorn 2 concreteBasePath = .ok (List.replicate 512 0xBB) ∧
      List.replicate 512 (0xBB : UInt8) ≠ oldBytes ∧
      List.replicate 512 (0xBB : UInt8) ≠ newBytes := by
  refine ⟨_, _, _, _, _, _, _, _, _,
    rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl,
    rfl, by decide, by decide, rfl, by decide, ?_⟩
  intro hEq
  have hLen := congrArg List.length hEq
  simp at hLen

/-- **#tooth 2 (`tooth_darwin_fsync_without_fullfsync_loses_committed_epoch_on_power_loss`)**:
    Models NVMe / SSD volatile write-back caches (`DriveWriteCache`) where plain POSIX `fsync(2)`
    without `F_FULLFSYNC` / `REQ_FUA` (`posixFsyncVolatileCacheOnly` + `posixFsyncDirVolatileOnly`)
    drains across `KernelPanicCrash` (passing naive reboot tests at epoch `1`!), yet **loses the
    committed epoch `1` back to epoch `0`** when `PowerLossCrash` wipes `DriveWriteCache`! -/
theorem tooth_darwin_fsync_without_fullfsync_loses_committed_epoch_on_power_loss :
    let tmpPath : DirName := walTmpPath concreteBasePath
    let b0 := encodeU64BeNat 0
    let b1 := encodeU64BeNat 1
    ∃ s1 s2 s3 s4 sEpoch0 s5 s6 s7 s8 s9,
      posixCreateExclNoFollow PosixFsState.empty 1 concreteBasePath = .ok (s1, 3, 1) ∧
      posixPwriteAll s1 1 3 b0 = .ok s2 ∧
      posixSyncAllMedia s2 1 3 false = (s3, .ok ()) ∧
      posixCloseFd s3 1 3 = .ok s4 ∧
      posixSyncParentDir s4 false = (sEpoch0, .ok ()) ∧
      -- Mutated commit of epoch `1`: plain `fsync` into `DriveWriteCache` WITHOUT `F_FULLFSYNC`!
      posixCreateExclNoFollow sEpoch0 1 tmpPath = .ok (s5, 4, 2) ∧
      posixPwriteAll s5 1 4 b1 = .ok s6 ∧
      posixFsyncVolatileCacheOnly s6 1 4 = .ok s7 ∧
      posixCloseFd s7 1 4 = .ok s8 ∧
      posixRename s8 tmpPath concreteBasePath = .ok s9 ∧
      let sPlainFsync := posixFsyncDirVolatileOnly s9
      -- Survives OS kernel panic (masking the bug in reboot-only tests):
      readDurableU64Counter (KernelPanicCrash sPlainFsync) 2 concreteBasePath = some 1 ∧
      -- Evaporates back to epoch `0` on real hardware power loss:
      readDurableU64Counter
        (PowerLossCrash .revertToNand (fun _ => SectorTearMask.dropAllVolatile) sPlainFsync)
        2 concreteBasePath = some 0 := by
  have h0Lt64 : 0 < 2 ^ 64 := Nat.pow_pos (by decide : 0 < 2)
  have h1Lt64 : 1 < 2 ^ 64 :=
    Nat.lt_trans (lt_two_pow_32_of_le_8192 (by decide : 1 ≤ 8192))
      two_pow_32_lt_two_pow_64
  refine ⟨_, _, _, _, _, _, _, _, _, _,
    rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl,
    decodeU64BeNat_encodeU64BeNat h1Lt64,
    decodeU64BeNat_encodeU64BeNat h0Lt64⟩

/-- **#tooth 4 (`tooth_unlink_and_failed_mustCreate_splits_flock_without_lockGenesisId`)**:
    Mechanizes the exact two-step POSIX `.lock` unlink + recreate split-brain race:
    1. Process `1` creates `.lock` (`ino₁ = 1`) and acquires `posixFlockExNb` (`owner 1 = some 1`),
    2. An external actor (`pid = 99`) `unlink`s `.lock` and creates a new `.lock` (`ino₂ = 2`),
    3. Process `2` attempts `posixCreateExclNoFollow` (which fails with `.error .eexist`!) and
       falls back to `posixOpenExistingNoFollow` + `posixFlockExNb` **without** `lockGenesisId`:
       **both** Process `1` (`ino₁ = 1`) and Process `2` (`ino₂ = 2`, `1 ≠ 2`) simultaneously hold
       live `LOCK_EX` `flock`s! -/
theorem tooth_unlink_and_failed_mustCreate_splits_flock_without_lockGenesisId :
    let lockPath := walLockPath concreteBasePath
    ∃ s1 s2 s3 s4 s5 s6 s7,
      -- Process 1 opens & locks `ino₁ = 1`:
      posixCreateExclNoFollow PosixFsState.empty 1 lockPath = .ok (s1, 3, 1) ∧
      posixFlockExNb s1 1 3 = .ok s2 ∧
      -- External actor unlinks `lockPath` and recreates a fresh inode `ino₂ = 2`:
      posixUnlink s2 lockPath = .ok s3 ∧
      posixCreateExclNoFollow s3 99 lockPath = .ok (s4, 4, 2) ∧
      posixCloseFd s4 99 4 = .ok s5 ∧
      -- Process 2 tries `O_CREAT|O_EXCL` (gets `.eexist`), falls back to `open` + `flock` without `lockGenesisId`:
      posixCreateExclNoFollow s5 2 lockPath = .error .eexist ∧
      posixOpenExistingNoFollow s5 2 lockPath true = .ok (s6, 5) ∧
      posixFlockExNb s6 2 5 = .ok s7 ∧
      -- Split-brain: Process 1 and Process 2 BOTH hold active `LOCK_EX` locks on distinct inodes `1 ≠ 2`!
      posixFstatDescAndInode s7 1 3 = .ok (1, 1) ∧
      posixFstatDescAndInode s7 2 5 = .ok (3, 2) ∧
      s7.kernel.flockTable.owner 1 = some 1 ∧
      s7.kernel.flockTable.owner 2 = some 3 ∧
      (1 : InodeId) ≠ 2 := by
  exact ⟨_, _, _, _, _, _, _,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- Helper simulating a **buggy non-sticky** `fsync` kernel that clears `stickyFsyncErr := false`
    on `descId` after reporting an initial `EIO` (`fsyncgate` vulnerability!). -/
def clearStickyFsyncErrOnDesc (st : PosixFsState) (descId : OpenDescriptionId) : PosixFsState :=
  match assocLookup st.kernel.openFds.descriptions descId with
  | none => st
  | some d =>
    let descs' := assocInsert descId { d with stickyFsyncErr := false } st.kernel.openFds.descriptions
    { st with kernel := { st.kernel with
                            openFds := { st.kernel.openFds with descriptions := descs' } } }

/-- **#tooth 6 (`tooth_retry_after_fsync_eio_without_sticky_poison_violates_durability`)**:
    Mechanizes the `CuttleFS` / `fsyncgate` (`errseq_t`) hazard:
    1. Process `1` commits `oldBytes = [0x10]` to NAND, then writes `newBytes = [0x20]` (`≠ oldBytes`)
       into `InodePageCache`,
    2. `posixSyncAllMedia ... true` fails with `.error .eio`, evicting the failed dirty page buffer
       back to stale NAND (`[0x10]`) and latching `stickyFsyncErr := true`,
    3. Under **hardened sticky poisoning**, retrying `posixSyncAllMedia ... false` returns
       `.error .epoisoned` (preventing silent data loss!), whereas
    4. Under **mutated non-sticky error clearing** (`clearStickyFsyncErrOnDesc`), retrying
       `posixSyncAllMedia ... false` **falsely returns `.ok ()`** while NAND and `readInodeHierarchy`
       still hold stale `oldBytes = [0x10]` (`≠ newBytes`)! -/
theorem tooth_retry_after_fsync_eio_without_sticky_poison_violates_durability :
    let oldBytes : List UInt8 := [0x10]
    let newBytes : List UInt8 := [0x20]
    ∃ s1 s2 sClean sDirty sAfterEio sFalseOk,
      posixCreateExclNoFollow PosixFsState.empty 1 concreteBasePath = .ok (s1, 3, 1) ∧
      posixPwriteAll s1 1 3 oldBytes = .ok s2 ∧
      posixSyncAllMedia s2 1 3 false = (sClean, .ok ()) ∧
      posixPwriteAll sClean 1 3 newBytes = .ok sDirty ∧
      posixSyncAllMedia sDirty 1 3 true = (sAfterEio, .error .eio) ∧
      -- Hardened sticky handle refuses retry with `.error .epoisoned`:
      posixSyncAllMedia sAfterEio 1 3 false = (sAfterEio, .error .epoisoned) ∧
      posixPreadAll sAfterEio 1 3 = .error .epoisoned ∧
      -- Mutated non-sticky handle falsely succeeds on retry while losing `newBytes`!
      posixSyncAllMedia (clearStickyFsyncErrOnDesc sAfterEio 1) 1 3 false = (sFalseOk, .ok ()) ∧
      assocLookup sFalseOk.nand.fileBlocks 1 = some oldBytes ∧
      readInodeHierarchy sFalseOk 1 = some oldBytes ∧
      oldBytes ≠ newBytes := by
  exact ⟨_, _, _, _, _, _,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-! ## 7. Per-Inode Crash Outcomes, Media Damage, Whole-Device Rollback & the External Anchor -/

/-- **Every crash outcome of one inode (`crashStep_inode_outcome`)**: after any `CrashStep`, the
    NAND bytes of an inode whose settled contents were `old` are one of
    1. `old` (nothing pending, or the pending write was dropped);
    2. the drive-cache copy (a kernel panic drains the drive cache; dirty page-cache data is lost);
    3. a sector mix of `old` and the pending write under some tear mask (power loss: any sector
       may keep the old bytes, take the new bytes, or hold garbage).
    An inode with no pending write is in case 1 (`syncedInode_immune_to_crashStep`). -/
theorem crashStep_inode_outcome {st crashed : PosixFsState} {ino : InodeId} {old : List UInt8}
    (hNand : assocLookup st.nand.fileBlocks ino = some old) (hCrash : CrashStep st crashed) :
    assocLookup crashed.nand.fileBlocks ino = some old ∨
    (∃ dc, assocLookup st.driveCache.cachedFiles ino = some dc ∧
      assocLookup crashed.nand.fileBlocks ino = some dc) ∨
    (∃ (pending : List UInt8) (mask : SectorTearMask), pendingVolatileWrite st ino = some pending ∧
      assocLookup crashed.nand.fileBlocks ino =
        some (mixSectors mask.geometry.byteWidth mask.sectorChoices old pending)) := by
  cases hCrash with
  | kernelPanic _ =>
    dsimp only [KernelPanicCrash]
    rw [assocLookup_mapAssocValues, hNand]
    cases hDc : assocLookup st.driveCache.cachedFiles ino with
    | none => exact Or.inl rfl
    | some dc => exact Or.inr (Or.inl ⟨dc, rfl, rfl⟩)
  | powerLoss dirPick tearFn _ =>
    dsimp only [PowerLossCrash]
    rw [assocLookup_mapAssocValues, hNand]
    cases hP : pendingVolatileWrite st ino with
    | none => exact Or.inl rfl
    | some pending => exact Or.inr (Or.inr ⟨pending, tearFn ino, rfl, rfl⟩)

/-- Offline media fault on one inode: its settled NAND bytes are replaced by ARBITRARY bytes
    (bit-rot, a failed block, or tampering with the powered-off device). Not a `CrashStep`: it
    can hit an inode that has nothing pending. -/
def MediaDamageInode (st : PosixFsState) (ino : InodeId) (garbage : List UInt8) : PosixFsState :=
  { st with nand := { st.nand with fileBlocks := assocInsert ino garbage st.nand.fileBlocks } }

theorem mediaDamageInode_lookup (st : PosixFsState) (ino q : InodeId) (garbage : List UInt8) :
    assocLookup (MediaDamageInode st ino garbage).nand.fileBlocks q =
      if q = ino then some garbage else assocLookup st.nand.fileBlocks q := by
  unfold MediaDamageInode
  exact assocLookup_insert ino garbage st.nand.fileBlocks q

/-- File sync persists the bytes, but the unsynced directory disappears after power loss. -/
theorem unsyncedGenesis_file_operations (sealBytes recordBytes : List UInt8) :
    ∃ s1 s2 s3 s4 s5 s6 s7 s8 sNoDirSync,
      posixCreateExclNoFollow PosixFsState.empty 1 (walLockPath concreteBasePath) = .ok (s1, 3, 1) ∧
      posixFlockExNb s1 1 3 = .ok s2 ∧
      posixPwriteAll s2 1 3 sealBytes = .ok s3 ∧
      posixSyncAllMedia s3 1 3 false = (s4, .ok ()) ∧
      posixCreateExclNoFollow s4 1 concreteBasePath = .ok (s5, 4, 2) ∧
      posixPwriteAll s5 1 4 recordBytes = .ok s6 ∧
      posixSyncAllMedia s6 1 4 false = (s7, .ok ()) ∧
      posixCloseFd s7 1 4 = .ok s8 ∧
      posixCloseFd s8 1 3 = .ok sNoDirSync ∧
      (∃ openedLock locked openedRecord,
        posixOpenExistingNoFollow sNoDirSync 2 (walLockPath concreteBasePath) true = .ok (openedLock, 5) ∧
        posixFlockExNb openedLock 2 5 = .ok locked ∧
        posixFstatDescAndInode locked 2 5 = .ok (3, 1) ∧
        posixPreadAll locked 2 5 = .ok sealBytes ∧
        posixOpenExistingNoFollow locked 2 concreteBasePath false = .ok (openedRecord, 6) ∧
        posixPreadAll openedRecord 2 6 = .ok recordBytes) ∧
      let crashed := PowerLossCrash .revertToNand (fun _ => SectorTearMask.dropAllVolatile) sNoDirSync
      assocLookup crashed.kernel.dirInode.unsyncedEntries concreteBasePath = none ∧
      posixOpenExistingNoFollow crashed 2 (walLockPath concreteBasePath) true = .error .enoent :=
  ⟨_, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩

namespace RustDurability

/-- Independent unsynced metadata operations are not a whole-directory snapshot. Each
writeback chooses one operation, preserving its order relative to other selected operations.
A filesystem-specific contract must additionally constrain dependency ordering and barriers. -/
inductive MetadataOp where
  | put (name : DirName) (inode : InodeId)
  | remove (name : DirName)
  deriving Repr, DecidableEq

def applyMetadataOp (entries : List (DirName × EntryTarget)) : MetadataOp → List (DirName × EntryTarget)
  | .put name inode => assocInsert name (.regular inode) entries
  | .remove name => assocErase name entries

def persistMetadata (entries : List (DirName × EntryTarget)) : List (Bool × MetadataOp) →
    List (DirName × EntryTarget)
  | [] => entries
  | (persist, op) :: rest =>
    persistMetadata (if persist then applyMetadataOp entries op else entries) rest

/-- Explicit counterexample to treating `DirCrashOutcome` as unrestricted POSIX semantics. -/
theorem independent_metadata_writeback_not_whole_snapshot :
    let a : MetadataOp := .put ⟨[1]⟩ 1
    let b : MetadataOp := .put ⟨[2]⟩ 2
    persistMetadata [] [(true, a), (false, b)] ≠ [] ∧
    persistMetadata [] [(true, a), (false, b)] ≠ persistMetadata [] [(true, a), (true, b)] := by
  decide

end RustDurability

/-- Finite `SectorTearMask` lookup schedule used in concrete/decidable trace events. -/
def evalFiniteTearSchedule (defaultTear : SectorTearMask)
    (overrides : List (InodeId × SectorTearMask)) (ino : InodeId) : SectorTearMask :=
  (assocLookup overrides ino).getD defaultTear

/-- System crash striking in the middle of a reservation: either crash kind, with the
    power-loss directory outcome and per-inode sector tears chosen by the environment. -/
inductive MidOpCrash where
  | kernelPanic
  | powerLoss (dirPick : DirCrashOutcome) (defaultTear : SectorTearMask)
      (perInodeTears : List (InodeId × SectorTearMask))
  deriving Repr, DecidableEq

def MidOpCrash.apply : MidOpCrash → PosixFsState → PosixFsState
  | .kernelPanic, st => KernelPanicCrash st
  | .powerLoss dirPick defaultTear overrides, st =>
    PowerLossCrash dirPick (evalFiniteTearSchedule defaultTear overrides) st

theorem MidOpCrash.apply_crashStep (c : MidOpCrash) (st : PosixFsState) :
    CrashStep st (c.apply st) := by
  cases c with
  | kernelPanic => exact CrashStep.kernelPanic st
  | powerLoss dirPick defaultTear overrides => exact CrashStep.powerLoss dirPick _ st

theorem posixFlockExNb_preserves_storage {sA sB : PosixFsState} {p : Pid} {fd : FdId}
    (hFlk : posixFlockExNb sA p fd = .ok sB) :
    sB.kernel.dirInode = sA.kernel.dirInode ∧
    sB.kernel.pageCache = sA.kernel.pageCache ∧
    sB.driveCache = sA.driveCache ∧
    sB.nand = sA.nand := by
  rw [posixFlockExNb.public_eq_1] at hFlk
  cases hRes : resolveOpenFd sA.kernel.openFds p fd with
  | none => rw [hRes] at hFlk; cases hFlk
  | some dPair =>
    rcases dPair with ⟨descId, d⟩
    rw [hRes] at hFlk
    dsimp only at hFlk
    cases hOw : sA.kernel.flockTable.owner d.inode with
    | none =>
      rw [hOw] at hFlk
      injection hFlk with hEq
      rw [← hEq]
      exact ⟨rfl, rfl, rfl, rfl⟩
    | some hld =>
      rw [hOw] at hFlk
      dsimp only at hFlk
      by_cases hh : (hld == descId) = true
      · simp only [hh, ↓reduceIte] at hFlk
        injection hFlk with hEq
        rw [← hEq]
        exact ⟨rfl, rfl, rfl, rfl⟩
      · simp [hh] at hFlk

end Qsag
end
