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
