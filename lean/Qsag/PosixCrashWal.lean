module
/-
# Qsag.PosixCrashWal — Hardware- & POSIX-Faithful Crash-Safe Storage, Dual-Bound Locking, & WAL Proofs

Complete `0 Classical.choice` formalization (`0` proof gaps, `0` custom axioms, `≤ 12` `@[expose]`)
of hardware-realistic three-tier crash semantics, POSIX inode/dentry/symlink/`flock` behavior,
`CuttleFS`/`fsyncgate` sticky I/O-error handle poisoning, dual-bound `lockGenesisId` inode sealing,
and reserve-before-sign multi-crash epoch uniqueness:

1. **Hardware-True Three-Tier Storage + POSIX Inode / Dentry / Symlink / Open-Description `flock` Machine**:
   - **Tier (a) Kernel Volatile State**: `FdTable` (`(Pid × FdId) → Option OpenDescriptionId`),
     kernel `OpenDescriptionId` table (`OpenDescriptionId → Option OpenFileDesc` refcounted across
     `dup`, `fork`, and `close`), `FlockTable` (`InodeId → Option OpenDescriptionId` matching Linux
     `man 2 flock`), `InodePageCache` (dirty kernel page cache), and `DirInode.unsyncedEntries`.
   - **Tier (b) Drive Volatile Write-Back Cache (`DriveWriteCache`)**: models NVMe/SSD volatile DRAM
     caches where plain POSIX `fsync` without `F_FULLFSYNC` / `REQ_FUA` survives a `KernelPanicCrash`
     yet evaporates on a `PowerLossCrash`.
   - **Tier (c) Non-Volatile NAND Media (`NandBlocks`)**: persistent directory dentries and file
     blocks subject to `512B` / `4KiB` sector-granular torn writes (`SectorTearMask`) on any
     uncommitted write in flight when power fails.
   - Real POSIX `Dentry` (`DirName → EntryTarget` supporting `.regular InodeId` and `.symlink target`
     to mechanize `O_NOFOLLOW` vs symlink following), `unlink` (unlinks pathname while open file
     descriptions keep the old `InodeId` and its `flock` alive), atomic `rename(tmp, dst)` (updates
     `unsyncedEntries` until `syncParentDir` + media flush), `dup`/`fork`/`close` open-description
     `flock` sharing vs independent-`open()` contention, and `CuttleFS`/`fsyncgate` sticky handle
     poisoning (`EIO` during `syncAllMedia` discards failed dirty pages and poisons the description).

2. **Dual-Bound `lockGenesisId` Inode Seal + Keyed-MAC `GenesisSealedWal` Protocol**:
   - `provisionGenesis`: verifies neither the WAL record nor `.lock` exists before creating anything
     (`O_CREAT | O_EXCL | O_NOFOLLOW`), binds `(lockInodeId, genesisNonce)` into `lockGenesisId`
     inside `.lock` + `syncAllMedia`, writes epoch-`0` MAC-authenticated `WalRecord` + `syncAllMedia`
     + `syncParentDir`.
   - `openExisting`: opens `.lock` with `O_NOFOLLOW` (never `O_CREAT`), acquires non-blocking
     `flock(LOCK_EX | LOCK_NB)` on `.lock`'s `InodeId`, verifies the locked inode matches the `.lock`
     seal, reads the WAL record with `O_NOFOLLOW`, and checks **both**
     `record.lockGenesisId == lockedFd.lockGenesisId` and valid 256-bit `keyedMac`.
   - `replaceAtomic`: unlinks any stale `.tmp`, creates fresh `.tmp` (`O_CREAT | O_EXCL | O_NOFOLLOW`),
     writes encoded record, calls `syncAllMedia(.tmp)`, `rename(.tmp, record)`, and `syncParentDir`,
     irreversibly latching `ioPoisoned := true` upon any I/O failure.

3. **Crash Hoare Logic (`CrashStep`, `PowerLossCrash`, `KernelPanicCrash`) & Flagship Theorems**:
   - `power_loss_preserves_committed_or_prior_record`
   - `dual_bound_lock_prevents_unlink_recreate_split_brain`
   - `reserve_before_sign_multi_crash_epoch_uniqueness`

4. **Hardware/POSIX `#tooth` Mutation Witnesses & Concrete Multi-Crash Trace Witness**:
   - `tooth_rename_without_tmp_sync_exposes_torn_or_garbage_file`
   - `tooth_darwin_fsync_without_fullfsync_loses_committed_epoch_on_power_loss`
   - `tooth_missing_parent_dir_sync_loses_genesis_after_power_loss`
   - `tooth_unlink_and_failed_mustCreate_splits_flock_without_lockGenesisId`
   - `tooth_missing_wal_treated_as_fresh_causes_epoch_zero_amnesia`
   - `tooth_retry_after_fsync_eio_without_sticky_poison_violates_durability`
   - `inhabited_posix_crash_wal_trace`
-/

public import Qsag.Constructive
public import Qsag.SimulationSpine

public section

namespace Qsag

set_option autoImplicit false

/-! ## 1. Constructive Finite Association Maps, Byte-Sequence `DirName`, & `u64be` Framing -/

/-- Process identifier in the local POSIX OS model. -/
abbrev Pid := Nat

/-- Persistent filesystem inode number (`st_ino`). -/
abbrev InodeId := Nat

/-- Process-wide file descriptor number (`fd`). -/
abbrev FdId := Nat

/-- Kernel open file description identifier (`struct file` identity, shared across `dup`/`fork`). -/
abbrev OpenDescriptionId := Nat

/-- Constructive `LawfulBEq` negation helper avoiding classical boolean lemmas. -/
theorem eq_of_not_bne_true {α : Type} [BEq α] [LawfulBEq α] {a b : α}
    (h : ¬(a != b) = true) : a = b := by
  cases hBeq : (a == b)
  · exfalso
    apply h
    simp [bne, hBeq]
  · exact eq_of_beq hBeq

/-- Constructive finite association-list lookup (`0 Classical.choice`). -/
@[expose]
def assocLookup {K V : Type} [DecidableEq K] : List (K × V) → K → Option V
  | [], _ => none
  | (k, v) :: rest, q => if q = k then some v else assocLookup rest q

/-- Constructive finite association-list upsert replacing the first matching key or appending. -/
def assocInsert {K V : Type} [DecidableEq K] (k : K) (v : V) : List (K × V) → List (K × V)
  | [] => [(k, v)]
  | (k', v') :: rest => if k = k' then (k, v) :: rest else (k', v') :: assocInsert k v rest

/-- Constructive finite association-list key removal erasing every binding for `k`. -/
def assocErase {K V : Type} [DecidableEq K] (k : K) : List (K × V) → List (K × V)
  | [] => []
  | (k', v') :: rest => if k = k' then assocErase k rest else (k', v') :: assocErase k rest

/-- Map values pointwise across a finite association list while preserving key order. -/
def mapAssocValues {K V W : Type} (f : K → V → W) : List (K × V) → List (K × W)
  | [] => []
  | (k, v) :: rest => (k, f k v) :: mapAssocValues f rest

@[simp]
theorem assocLookup_nil {K V : Type} [DecidableEq K] (q : K) :
    assocLookup ([] : List (K × V)) q = none := by rfl

@[simp]
theorem assocLookup_insert {K V : Type} [DecidableEq K]
    (k : K) (v : V) (m : List (K × V)) (q : K) :
    assocLookup (assocInsert k v m) q = if q = k then some v else assocLookup m q := by
  induction m with
  | nil => rfl
  | cons kv rest ih =>
    rcases kv with ⟨k', v'⟩
    dsimp only [assocInsert]
    by_cases hkk : k = k'
    · subst hkk
      simp only [↓reduceIte, assocLookup]
      by_cases hqk : q = k <;> simp [hqk]
    · simp only [hkk, ↓reduceIte, assocLookup]
      by_cases hqk' : q = k'
      · subst hqk'
        have hqk : q ≠ k := fun hEq => hkk hEq.symm
        simp only [↓reduceIte, hqk]
      · simp only [hqk', ↓reduceIte, ih]

@[simp]
theorem assocLookup_cons_self {K V : Type} [DecidableEq K]
    (k : K) (v : V) (m : List (K × V)) :
    assocLookup ((k, v) :: m) k = some v := by
  simp [assocLookup]

@[simp]
theorem assocLookup_insert_self {K V : Type} [DecidableEq K]
    (k : K) (v : V) (m : List (K × V)) :
    assocLookup (assocInsert k v m) k = some v := by
  simp

theorem assocLookup_insert_of_ne {K V : Type} [DecidableEq K]
    {k q : K} (v : V) (m : List (K × V)) (hNe : q ≠ k) :
    assocLookup (assocInsert k v m) q = assocLookup m q := by
  simp [hNe]

@[simp]
theorem assocLookup_erase {K V : Type} [DecidableEq K]
    (k : K) (m : List (K × V)) (q : K) :
    assocLookup (assocErase k m) q = if q = k then none else assocLookup m q := by
  induction m with
  | nil =>
    by_cases h : q = k <;> simp [assocErase, h]
  | cons kv rest ih =>
    rcases kv with ⟨k', v'⟩
    dsimp only [assocErase]
    by_cases hkk : k = k'
    · subst hkk
      simp only [↓reduceIte, ih]
      by_cases hqk : q = k
      · simp [hqk]
      · simp [hqk, assocLookup]
    · simp only [hkk, ↓reduceIte, assocLookup]
      by_cases hqk' : q = k'
      · subst hqk'
        have hqk : q ≠ k := fun hEq => hkk hEq.symm
        simp [hqk]
      · simp [hqk', ih]

@[simp]
theorem assocLookup_mapAssocValues {K V W : Type} [DecidableEq K]
    (f : K → V → W) (m : List (K × V)) (q : K) :
    assocLookup (mapAssocValues f m) q = (assocLookup m q).map (f q) := by
  induction m with
  | nil => rfl
  | cons kv rest ih =>
    rcases kv with ⟨k, v⟩
    dsimp only [mapAssocValues, assocLookup]
    by_cases h : q = k
    · simp [h]
    · simp [h, ih]

theorem mapAssocValues_id {K V : Type} {f : K → V → V}
    (hId : ∀ k v, f k v = v) (m : List (K × V)) :
    mapAssocValues f m = m := by
  induction m with
  | nil => rfl
  | cons kv rest ih =>
    rcases kv with ⟨k, v⟩
    dsimp only [mapAssocValues]
    rw [hId k v, ih]

theorem option_map_id_ext {α : Type} {f : α → α} (hId : ∀ x, f x = x) (o : Option α) :
    o.map f = o := by
  cases o with
  | none => rfl
  | some x => exact congrArg some (hId x)

theorem assocLookup_mem_of_some {K V : Type} [DecidableEq K]
    {m : List (K × V)} {q : K} {v : V} (h : assocLookup m q = some v) :
    (q, v) ∈ m := by
  induction m with
  | nil => cases h
  | cons kv rest ih =>
    rcases kv with ⟨k, v'⟩
    dsimp only [assocLookup] at h
    by_cases hqk : q = k
    · subst hqk
      simp only [↓reduceIte, Option.some.injEq] at h
      subst h
      exact List.Mem.head rest
    · simp only [hqk, ↓reduceIte] at h
      exact List.Mem.tail (k, v') (ih h)

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
  simp [walLockPath] at hLen

theorem walTmpPath_ne_base (base : DirName) : walTmpPath base ≠ base := by
  intro hEq
  have hLen := congrArg (fun d => d.rawBytes.length) hEq
  simp [walTmpPath] at hLen

theorem walTmpPath_ne_lockPath (base : DirName) : walTmpPath base ≠ walLockPath base := by
  intro hEq
  have hLen := congrArg (fun d => d.rawBytes.length) hEq
  simp [walTmpPath, walLockPath] at hLen

/-- Encode a natural number `< 2^64` as 8 big-endian bytes (`u64be`). -/
@[expose]
def encodeU64BeNat (n : Nat) : List UInt8 :=
  encodeU32BeNat (n / 4294967296) ++ encodeU32BeNat (n % 4294967296)

/-- Decode 8 big-endian bytes into a natural number `< 2^64`. -/
@[expose]
def decodeU64BeNat (bs : List UInt8) : Option Nat :=
  if bs.length == 8 then
    match decodeU32BeNat (bs.take 4), decodeU32BeNat (bs.drop 4) with
    | some hi, some lo => some (hi * 4294967296 + lo)
    | _, _ => none
  else
    none

theorem encodeU64BeNat_length (n : Nat) : (encodeU64BeNat n).length = 8 := by
  simp [encodeU64BeNat, encodeU32BeNat_length]

private theorem lt_two_pow_32_of_le_8192 {n : Nat} (h : n ≤ 8192) : n < 2 ^ 32 :=
  Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (by decide : 8192 < 2 ^ 14)
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by decide : 14 ≤ 32)))

theorem decodeU64BeNat_encodeU64BeNat {n : Nat} (hLt : n < 2 ^ 64) :
    decodeU64BeNat (encodeU64BeNat n) = some n := by
  unfold decodeU64BeNat encodeU64BeNat
  have hHiLt : n / 4294967296 < 2 ^ 32 := by omega
  have hLoLt : n % 4294967296 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hBeq : ((encodeU32BeNat (n / 4294967296) ++ encodeU32BeNat (n % 4294967296)).length == 8) = true := rfl
  simp only [hBeq, ↓reduceIte,
    take_append_of_len_eq (encodeU32BeNat_length _),
    drop_append_of_len_eq (encodeU32BeNat_length _),
    decodeU32BeNat_encodeU32BeNat hHiLt,
    decodeU32BeNat_encodeU32BeNat hLoLt]
  apply congrArg some
  omega

theorem encodeU64BeNat_injective {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (hEq : encodeU64BeNat a = encodeU64BeNat b) : a = b := by
  have hDec := congrArg decodeU64BeNat hEq
  rw [decodeU64BeNat_encodeU64BeNat ha, decodeU64BeNat_encodeU64BeNat hb] at hDec
  injection hDec

theorem decodeU32BeNat_lt_two_pow_32 {bs : List UInt8} {v : Nat}
    (h : decodeU32BeNat bs = some v) : v < 2 ^ 32 := by
  match bs with
  | [b3, b2, b1, b0] =>
    dsimp only [decodeU32BeNat] at h
    injection h with hVal
    have h3 : b3.toNat < 256 := b3.toBitVec.isLt
    have h2 : b2.toNat < 256 := b2.toBitVec.isLt
    have h1 : b1.toNat < 256 := b1.toBitVec.isLt
    have h0 : b0.toNat < 256 := b0.toBitVec.isLt
    omega
  | [] => cases h
  | [_] => cases h
  | [_, _] => cases h
  | [_, _, _] => cases h
  | _ :: _ :: _ :: _ :: _ :: _ => cases h

theorem decodeU32BeNat_canonical {bs : List UInt8} {v : Nat}
    (h : decodeU32BeNat bs = some v) : encodeU32BeNat v = bs := by
  match bs with
  | [b3, b2, b1, b0] =>
    dsimp only [decodeU32BeNat] at h
    injection h with hVal
    subst hVal
    have h3 : b3.toNat < 256 := b3.toBitVec.isLt
    have h2 : b2.toNat < 256 := b2.toBitVec.isLt
    have h1 : b1.toNat < 256 := b1.toBitVec.isLt
    have h0 : b0.toNat < 256 := b0.toBitVec.isLt
    dsimp only [encodeU32BeNat]
    have e3 : ((b3.toNat * 16777216 + b2.toNat * 65536 + b1.toNat * 256 + b0.toNat) / 16777216) % 256 = b3.toNat := by omega
    have e2 : ((b3.toNat * 16777216 + b2.toNat * 65536 + b1.toNat * 256 + b0.toNat) / 65536) % 256 = b2.toNat := by omega
    have e1 : ((b3.toNat * 16777216 + b2.toNat * 65536 + b1.toNat * 256 + b0.toNat) / 256) % 256 = b1.toNat := by omega
    have e0 : (b3.toNat * 16777216 + b2.toNat * 65536 + b1.toNat * 256 + b0.toNat) % 256 = b0.toNat := by omega
    rw [e3, e2, e1, e0]
    have u8_ofNat_toNat : ∀ b : UInt8, UInt8.ofNat b.toNat = b := fun b =>
      UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt b.toBitVec.isLt))
    rw [u8_ofNat_toNat b3, u8_ofNat_toNat b2, u8_ofNat_toNat b1, u8_ofNat_toNat b0]
  | [] => cases h
  | [_] => cases h
  | [_, _] => cases h
  | [_, _, _] => cases h
  | _ :: _ :: _ :: _ :: _ :: _ => cases h

theorem decodeU64BeNat_canonical {bs : List UInt8} {v : Nat}
    (h : decodeU64BeNat bs = some v) : v < 2 ^ 64 ∧ encodeU64BeNat v = bs := by
  unfold decodeU64BeNat at h
  by_cases hLen : (bs.length == 8) = true
  · simp only [hLen, ↓reduceIte] at h
    cases hHi : decodeU32BeNat (bs.take 4) with
    | none => rw [hHi] at h; cases h
    | some hi =>
      cases hLo : decodeU32BeNat (bs.drop 4) with
      | none => rw [hHi, hLo] at h; cases h
      | some lo =>
        rw [hHi, hLo] at h
        injection h with hVal
        subst hVal
        have hiLt := decodeU32BeNat_lt_two_pow_32 hHi
        have loLt := decodeU32BeNat_lt_two_pow_32 hLo
        refine ⟨by omega, ?_⟩
        unfold encodeU64BeNat
        have hDiv : (hi * 4294967296 + lo) / 4294967296 = hi := by omega
        have hMod : (hi * 4294967296 + lo) % 4294967296 = lo := by omega
        rw [hDiv, hMod, decodeU32BeNat_canonical hHi, decodeU32BeNat_canonical hLo, List.take_append_drop]
  · simp only [hLen, Bool.false_eq_true, ↓reduceIte] at h
    cases h

theorem unframeBytes_canonical {buf payload rest : List UInt8}
    (h : unframeBytes buf = some (payload, rest)) :
    payload.length < 2 ^ 32 ∧ buf = frameBytes payload ++ rest := by
  unfold unframeBytes at h
  by_cases hLt4 : buf.length < 4
  · simp only [hLt4, ↓reduceIte] at h
    cases h
  · simp only [hLt4, ↓reduceIte] at h
    cases hDec : decodeU32BeNat (buf.take 4) with
    | none => rw [hDec] at h; cases h
    | some len =>
      rw [hDec] at h
      dsimp only at h
      by_cases hBody : (buf.drop 4).length < len
      · simp only [hBody, ↓reduceIte] at h
        cases h
      · simp only [hBody, ↓reduceIte] at h
        injection h with hPair
        injection hPair with hPay hRest
        have hLenLt := decodeU32BeNat_lt_two_pow_32 hDec
        have hPayLen : payload.length = len := by
          rw [← hPay, List.length_take]
          omega
        refine ⟨hPayLen ▸ hLenLt, ?_⟩
        unfold frameBytes
        rw [hPayLen, decodeU32BeNat_canonical hDec, ← hPay, ← hRest]
        rw [List.append_assoc, List.take_append_drop, List.take_append_drop]

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
def resolveOpenFd (t : OpenFdTable) (pid : Pid) (fd : FdId) :
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
def PosixFsState.empty : PosixFsState := {}

/-- Pending volatile write for `ino` (kernel `InodePageCache` shadows `DriveWriteCache`). -/
def pendingVolatileWrite (st : PosixFsState) (ino : InodeId) : Option (List UInt8) :=
  match assocLookup st.kernel.pageCache.dirtyFiles ino with
  | some dirty => some dirty
  | none => assocLookup st.driveCache.cachedFiles ino

/-- Effective coherent file bytes visible to `read`/`pread` across the 3-tier hierarchy:
    `InodePageCache` → `DriveWriteCache` → `NandBlocks`. -/
def readInodeHierarchy (st : PosixFsState) (ino : InodeId) : Option (List UInt8) :=
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
    Allocates a fresh kernel `OpenDescriptionId` (`nextDescId`) so two independent `open()` calls
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
    - Two independent `open()` calls in the **same** `pid` have `holderDescId != descId` and
      contend with `.error .ewouldblock`, whereas
    - `dup()`ed / `fork()`ed descriptors sharing `descId` satisfy `holderDescId == descId`! -/
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
def posixSyncParentDir (st : PosixFsState) (injectEio : Bool := false) :
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
def posixUnlinkIfPresent (st : PosixFsState) (name : DirName) : PosixFsState :=
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

/-- **Linux/POSIX `flock(2)` Same-Process Independent-Open Contention (`G1-H` Part 1a)**:
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
    rw [hReg]; rfl
  · unfold posixFlockExNb resolveOpenFd
    dsimp only [st1]
    simp only [assocLookup_insert_self, hFree]
    rfl
  · unfold posixOpenExistingNoFollow resolveDentryNoFollow
    dsimp only [st2, st1]
    rw [hReg]; rfl
  · unfold FdTable.lookupDescId
    dsimp only [st3, st1]
    simp only [assocLookup_insert, hFdNe, ↓reduceIte]
    intro hSomeEq
    injection hSomeEq with hEqD
    exact hDescNe hEqD
  · unfold posixFlockExNb resolveOpenFd FlockTable.owner
    dsimp only [st3, st2]
    simp only [assocLookup_insert_self, hDescBeqFalse, Bool.false_eq_true, ↓reduceIte]

/-- **Linux/POSIX `flock(2)` Shared-Description Refcount Semantics (`G1-H` Part 1b)**:
    Duplicating a locked descriptor via `posixDup` (and inheriting via `posixForkFds`) shares a
    single `OpenDescriptionId`:
    1. `posixFlockExNb` on `dupFd` and on the forked child's `(childPid, fd₁)` **succeeds** (`.ok`)
       because `flock` belongs to the shared `OpenDescriptionId` (not a per-thread/per-fd mutex!),
    2. Closing `fd₁` and closing `(childPid, fd₁)` while `dupFd` remains open **keeps** the `flock`
       alive on `ino` (so an independent `open()` still gets `.ewouldblock`), and
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
def KernelPanicCrash (st : PosixFsState) : PosixFsState :=
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
def PowerLossCrash (dirPick : DirCrashOutcome) (tearFn : InodeId → SectorTearMask)
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

/-! ## 4. Dual-Bound `lockGenesisId` Inode Seal & Keyed-MAC `GenesisSealedWal` Protocol -/

/-- Domain tag `"QSAGLCK1"` (`8` bytes) framing the `.lock` sidecar seal. -/
def lockSidecarMagicTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x4c, 0x43, 0x4b, 0x31]

/-- Domain tag `"QSAGWAL1"` (`8` bytes) framing on-disk WAL records. -/
def walFileMagicTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x57, 0x41, 0x4c, 0x31]

/-- Domain tag `"QSAGMAC1"` (`8` bytes) domain-separating the keyed-MAC preimage. -/
def walMacDomainTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x4d, 0x41, 0x43, 0x31]

/-- Dual-bound `.lock` sidecar seal binding the kernel `st_ino` allocated at genesis together
    with a 256-bit (32-byte) genesis nonce. -/
structure LockSidecarSeal where
  sealedLockInode : InodeId
  genesisNonce    : List UInt8
  deriving Repr, DecidableEq

/-- Well-formedness of a `LockSidecarSeal` (`st_ino < 2^64`, 32-byte 256-bit `genesisNonce`). -/
def LockSidecarSeal.WellFormed (s : LockSidecarSeal) : Prop :=
  s.sealedLockInode < 2 ^ 64 ∧ s.genesisNonce.length = 32

/-- Compute the 40-byte dual-bound `lockGenesisId := u64be(lockIno) || genesisNonce32`. -/
@[expose]
def computeLockGenesisId (lockIno : InodeId) (genesisNonce : List UInt8) : List UInt8 :=
  encodeU64BeNat lockIno ++ genesisNonce

theorem computeLockGenesisId_length {lockIno : InodeId} {nonce : List UInt8}
    (hNonce : nonce.length = 32) :
    (computeLockGenesisId lockIno nonce).length = 40 := by
  simp [computeLockGenesisId, encodeU64BeNat_length, hNonce]

theorem computeLockGenesisId_injective {ino₁ ino₂ : InodeId} {n₁ n₂ : List UInt8}
    (hIno₁ : ino₁ < 2 ^ 64) (hIno₂ : ino₂ < 2 ^ 64)
    (hEq : computeLockGenesisId ino₁ n₁ = computeLockGenesisId ino₂ n₂) :
    ino₁ = ino₂ ∧ n₁ = n₂ := by
  unfold computeLockGenesisId at hEq
  have hTake := congrArg (List.take 8) hEq
  have hDrop := congrArg (List.drop 8) hEq
  rw [take_append_of_len_eq (encodeU64BeNat_length ino₁),
      take_append_of_len_eq (encodeU64BeNat_length ino₂)] at hTake
  rw [drop_append_of_len_eq (encodeU64BeNat_length ino₁),
      drop_append_of_len_eq (encodeU64BeNat_length ino₂)] at hDrop
  exact ⟨encodeU64BeNat_injective hIno₁ hIno₂ hTake, hDrop⟩

/-- Encode `LockSidecarSeal` onto `.lock` media (`concatFramed [magic, u64be(ino), nonce32]`). -/
def encodeLockSidecar (s : LockSidecarSeal) : List UInt8 :=
  concatFramed [lockSidecarMagicTag, encodeU64BeNat s.sealedLockInode, s.genesisNonce]

/-- Decode and validate canonical `LockSidecarSeal` bytes. -/
def decodeLockSidecar (bs : List UInt8) : Option LockSidecarSeal :=
  match unframeBytes bs with
  | none => none
  | some (magic, r1) =>
    if magic != lockSidecarMagicTag then none
    else match unframeBytes r1 with
    | none => none
    | some (inoBytes, r2) =>
      match decodeU64BeNat inoBytes, unframeBytes r2 with
      | some ino, some (nonce, []) =>
        if nonce.length == 32 then
          some { sealedLockInode := ino, genesisNonce := nonce }
        else none
      | _, _ => none

theorem decodeLockSidecar_encodeLockSidecar {s : LockSidecarSeal} (hWf : s.WellFormed) :
    decodeLockSidecar (encodeLockSidecar s) = some s := by
  rcases hWf with ⟨hIno, hNonce⟩
  unfold decodeLockSidecar encodeLockSidecar
  dsimp only [concatFramed]
  have hm : lockSidecarMagicTag.length < 2 ^ 32 := lt_two_pow_32_of_le_8192 (by decide)
  have hi : (encodeU64BeNat s.sealedLockInode).length < 2 ^ 32 := by
    rw [encodeU64BeNat_length]; exact lt_two_pow_32_of_le_8192 (by decide)
  have hn : s.genesisNonce.length < 2 ^ 32 := by
    rw [hNonce]; exact lt_two_pow_32_of_le_8192 (by decide)
  rw [FramedBytesCodec.unframe_frame_append hm]
  dsimp only
  have hMagFalse : (lockSidecarMagicTag != lockSidecarMagicTag) = false := rfl
  rw [hMagFalse]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [FramedBytesCodec.unframe_frame_append hi]
  dsimp only
  rw [decodeU64BeNat_encodeU64BeNat hIno,
      FramedBytesCodec.unframe_frame_append hn]
  dsimp only
  have hNBeq : (s.genesisNonce.length == 32) = true := by rw [hNonce]; rfl
  simp only [hNBeq, ↓reduceIte]

theorem decodeLockSidecar_canonical {bs : List UInt8} {s : LockSidecarSeal}
    (hDec : decodeLockSidecar bs = some s) :
    s.WellFormed ∧ encodeLockSidecar s = bs := by
  unfold decodeLockSidecar at hDec
  cases h1 : unframeBytes bs with
  | none => rw [h1] at hDec; cases hDec
  | some p1 =>
    rcases p1 with ⟨magic, r1⟩
    rw [h1] at hDec
    dsimp only at hDec
    by_cases hMag : (magic != lockSidecarMagicTag) = true
    · simp only [hMag, ↓reduceIte] at hDec; cases hDec
    · simp only [hMag, Bool.false_eq_true, ↓reduceIte] at hDec
      have hMagEq : magic = lockSidecarMagicTag := eq_of_not_bne_true hMag
      cases h2 : unframeBytes r1 with
      | none => rw [h2] at hDec; cases hDec
      | some p2 =>
        rcases p2 with ⟨inoBytes, r2⟩
        rw [h2] at hDec
        dsimp only at hDec
        cases hIno : decodeU64BeNat inoBytes with
        | none => rw [hIno] at hDec; cases hDec
        | some ino =>
          cases h3 : unframeBytes r2 with
          | none => rw [hIno, h3] at hDec; cases hDec
          | some p3 =>
            rcases p3 with ⟨nonce, tail⟩
            rw [hIno, h3] at hDec
            cases tail with
            | cons _ _ => cases hDec
            | nil =>
              dsimp only at hDec
              by_cases hNLen : (nonce.length == 32) = true
              · simp only [hNLen, ↓reduceIte] at hDec
                injection hDec with hEqS
                subst hEqS
                obtain ⟨_, hBs1⟩ := unframeBytes_canonical h1
                obtain ⟨_, hBs2⟩ := unframeBytes_canonical h2
                obtain ⟨_, hBs3⟩ := unframeBytes_canonical h3
                obtain ⟨hInoLt, hInoCan⟩ := decodeU64BeNat_canonical hIno
                refine ⟨⟨hInoLt, Nat.eq_of_beq_eq_true hNLen⟩, ?_⟩
                unfold encodeLockSidecar
                dsimp only [concatFramed]
                rw [hMagEq] at hBs1
                rw [hInoCan, hBs1, hBs2, hBs3]
              · simp only [hNLen, Bool.false_eq_true, ↓reduceIte] at hDec; cases hDec

/-- Authenticated body of a `GenesisSealedWal` record. -/
structure WalRecordBody where
  vaultKeyId    : List UInt8 -- 32-byte (256-bit) enrolled vault public-key / share identifier
  lockGenesisId : List UInt8 -- 40-byte dual-bound `(sealedLockInode, genesisNonce)` seal
  epoch         : Nat        -- Monotonic 64-bit signing epoch watermark
  payload       : List UInt8 -- Length-framed protocol state payload
  deriving Repr, DecidableEq

/-- Width invariants on `WalRecordBody` (`256`-bit `vaultKeyId`, `40`-byte `lockGenesisId`,
    `64`-bit `epoch`, `< 2^32`-byte length-framed `payload`). -/
def WalRecordBody.WellFormed (b : WalRecordBody) : Prop :=
  b.vaultKeyId.length = 32 ∧
  b.lockGenesisId.length = 40 ∧
  b.epoch < 2 ^ 64 ∧
  b.payload.length < 2 ^ 32

/-- Full on-disk MAC-authenticated WAL record (`body` + 256-bit `keyedMac`). -/
structure WalRecord where
  body     : WalRecordBody
  keyedMac : List UInt8 -- 32-byte (256-bit) keyed MAC tag
  deriving Repr, DecidableEq

/-- Width invariants on `WalRecord`. -/
def WalRecord.WellFormed (r : WalRecord) : Prop :=
  r.body.WellFormed ∧ r.keyedMac.length = 32

/-- Canonical length-framed MAC preimage covering **every** field of `WalRecordBody`. -/
def encodeWalBody (b : WalRecordBody) : List UInt8 :=
  concatFramed [walMacDomainTag, b.vaultKeyId, b.lockGenesisId, encodeU64BeNat b.epoch, b.payload]

/-- **MAC Preimage Collision-Freedom (`encodeWalBody_injective`)**:
    Every field of `WalRecordBody` is length-framed via `concatFramed`, so distinct well-formed
    record bodies **never** share a MAC preimage (`0 Classical.choice`). -/
theorem encodeWalBody_injective {b₁ b₂ : WalRecordBody}
    (h₁ : b₁.WellFormed) (h₂ : b₂.WellFormed)
    (hEq : encodeWalBody b₁ = encodeWalBody b₂) : b₁ = b₂ := by
  rcases h₁ with ⟨hk₁, hl₁, he₁, hp₁⟩
  rcases h₂ with ⟨hk₂, hl₂, he₂, hp₂⟩
  unfold encodeWalBody at hEq
  have hBnd₁ : ∀ x ∈ [walMacDomainTag, b₁.vaultKeyId, b₁.lockGenesisId, encodeU64BeNat b₁.epoch, b₁.payload],
      x.length < 2 ^ 32 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact lt_two_pow_32_of_le_8192 (by decide)
    · rcases List.mem_cons.mp hx with rfl | hx
      · rw [hk₁]; exact lt_two_pow_32_of_le_8192 (by decide)
      · rcases List.mem_cons.mp hx with rfl | hx
        · rw [hl₁]; exact lt_two_pow_32_of_le_8192 (by decide)
        · rcases List.mem_cons.mp hx with rfl | hx
          · rw [encodeU64BeNat_length]; exact lt_two_pow_32_of_le_8192 (by decide)
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact hp₁
            · cases hx
  have hBnd₂ : ∀ y ∈ [walMacDomainTag, b₂.vaultKeyId, b₂.lockGenesisId, encodeU64BeNat b₂.epoch, b₂.payload],
      y.length < 2 ^ 32 := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact lt_two_pow_32_of_le_8192 (by decide)
    · rcases List.mem_cons.mp hy with rfl | hy
      · rw [hk₂]; exact lt_two_pow_32_of_le_8192 (by decide)
      · rcases List.mem_cons.mp hy with rfl | hy
        · rw [hl₂]; exact lt_two_pow_32_of_le_8192 (by decide)
        · rcases List.mem_cons.mp hy with rfl | hy
          · rw [encodeU64BeNat_length]; exact lt_two_pow_32_of_le_8192 (by decide)
          · rcases List.mem_cons.mp hy with rfl | hy
            · exact hp₂
            · cases hy
  have hListEq := FramedBytesCodec.concatFramed_injective hBnd₁ hBnd₂ hEq
  injection hListEq with _ hTail1
  injection hTail1 with hVk hTail2
  injection hTail2 with hLg hTail3
  injection hTail3 with hEpBytes hTail4
  injection hTail4 with hPay _
  have hEp := encodeU64BeNat_injective he₁ he₂ hEpBytes
  cases b₁; cases b₂
  dsimp only at hVk hLg hEp hPay
  subst hVk hLg hEp hPay
  rfl

/-- Encode a complete `WalRecord` onto disk bytes using strict prefix-free framing. -/
def encodeWalRecord (r : WalRecord) : List UInt8 :=
  concatFramed [walFileMagicTag, r.body.vaultKeyId, r.body.lockGenesisId,
                encodeU64BeNat r.body.epoch, r.body.payload, r.keyedMac]

/-- Decode a complete `WalRecord` from disk bytes, rejecting truncated, torn, or trailing bytes. -/
def decodeWalRecord (bs : List UInt8) : Option WalRecord :=
  match unframeBytes bs with
  | none => none
  | some (magic, r1) =>
    if magic != walFileMagicTag then none
    else match unframeBytes r1 with
    | none => none
    | some (vkId, r2) =>
      if vkId.length != 32 then none
      else match unframeBytes r2 with
      | none => none
      | some (lgId, r3) =>
        if lgId.length != 40 then none
        else match unframeBytes r3 with
        | none => none
        | some (epBytes, r4) =>
          match decodeU64BeNat epBytes, unframeBytes r4 with
          | some ep, some (payload, r5) =>
            match unframeBytes r5 with
            | some (mac, []) =>
              if mac.length == 32 then
                some { body := { vaultKeyId := vkId
                                 lockGenesisId := lgId
                                 epoch := ep
                                 payload := payload }
                       keyedMac := mac }
              else none
            | _ => none
          | _, _ => none

theorem decodeWalRecord_encodeWalRecord {r : WalRecord} (hWf : r.WellFormed) :
    decodeWalRecord (encodeWalRecord r) = some r := by
  rcases hWf with ⟨⟨hVk, hLg, hEp, hPay⟩, hMac⟩
  unfold decodeWalRecord encodeWalRecord
  dsimp only [concatFramed]
  have hm : walFileMagicTag.length < 2 ^ 32 := lt_two_pow_32_of_le_8192 (by decide)
  have hvkLt : r.body.vaultKeyId.length < 2 ^ 32 := by
    rw [hVk]; exact lt_two_pow_32_of_le_8192 (by decide)
  have hlgLt : r.body.lockGenesisId.length < 2 ^ 32 := by
    rw [hLg]; exact lt_two_pow_32_of_le_8192 (by decide)
  have hepLt : (encodeU64BeNat r.body.epoch).length < 2 ^ 32 := by
    rw [encodeU64BeNat_length]; exact lt_two_pow_32_of_le_8192 (by decide)
  have hmacLt : r.keyedMac.length < 2 ^ 32 := by
    rw [hMac]; exact lt_two_pow_32_of_le_8192 (by decide)
  rw [FramedBytesCodec.unframe_frame_append hm]
  dsimp only
  have hMagFalse : (walFileMagicTag != walFileMagicTag) = false := rfl
  rw [hMagFalse]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [FramedBytesCodec.unframe_frame_append hvkLt]
  dsimp only
  have hVkNe : (r.body.vaultKeyId.length != 32) = false := by
    rw [hVk]; rfl
  rw [hVkNe]; simp only [Bool.false_eq_true, ↓reduceIte]
  rw [FramedBytesCodec.unframe_frame_append hlgLt]
  dsimp only
  have hLgNe : (r.body.lockGenesisId.length != 40) = false := by
    rw [hLg]; rfl
  rw [hLgNe]; simp only [Bool.false_eq_true, ↓reduceIte]
  rw [FramedBytesCodec.unframe_frame_append hepLt]
  dsimp only
  rw [decodeU64BeNat_encodeU64BeNat hEp,
      FramedBytesCodec.unframe_frame_append hPay]
  dsimp only
  rw [FramedBytesCodec.unframe_frame_append hmacLt]
  dsimp only
  have hMacEq : (r.keyedMac.length == 32) = true := by rw [hMac]; rfl
  simp only [hMacEq, ↓reduceIte]

theorem decodeWalRecord_canonical {bs : List UInt8} {r : WalRecord}
    (hDec : decodeWalRecord bs = some r) :
    r.WellFormed ∧ encodeWalRecord r = bs := by
  unfold decodeWalRecord at hDec
  cases h1 : unframeBytes bs with
  | none => rw [h1] at hDec; cases hDec
  | some p1 =>
    rcases p1 with ⟨magic, r1⟩
    rw [h1] at hDec
    dsimp only at hDec
    by_cases hMag : (magic != walFileMagicTag) = true
    · simp only [hMag, ↓reduceIte] at hDec; cases hDec
    · simp only [hMag, Bool.false_eq_true, ↓reduceIte] at hDec
      have hMagEq : magic = walFileMagicTag := eq_of_not_bne_true hMag
      cases h2 : unframeBytes r1 with
      | none => rw [h2] at hDec; cases hDec
      | some p2 =>
        rcases p2 with ⟨vkId, r2⟩
        rw [h2] at hDec
        dsimp only at hDec
        by_cases hVk : (vkId.length != 32) = true
        · simp only [hVk, ↓reduceIte] at hDec; cases hDec
        · simp only [hVk, Bool.false_eq_true, ↓reduceIte] at hDec
          have hVkEq : vkId.length = 32 := eq_of_not_bne_true hVk
          cases h3 : unframeBytes r2 with
          | none => rw [h3] at hDec; cases hDec
          | some p3 =>
            rcases p3 with ⟨lgId, r3⟩
            rw [h3] at hDec
            dsimp only at hDec
            by_cases hLg : (lgId.length != 40) = true
            · simp only [hLg, ↓reduceIte] at hDec; cases hDec
            · simp only [hLg, Bool.false_eq_true, ↓reduceIte] at hDec
              have hLgEq : lgId.length = 40 := eq_of_not_bne_true hLg
              cases h4 : unframeBytes r3 with
              | none => rw [h4] at hDec; cases hDec
              | some p4 =>
                rcases p4 with ⟨epBytes, r4⟩
                rw [h4] at hDec
                dsimp only at hDec
                cases hEp : decodeU64BeNat epBytes with
                | none => rw [hEp] at hDec; cases hDec
                | some ep =>
                  cases h5 : unframeBytes r4 with
                  | none => rw [hEp, h5] at hDec; cases hDec
                  | some p5 =>
                    rcases p5 with ⟨payload, r5⟩
                    rw [hEp, h5] at hDec
                    dsimp only at hDec
                    cases h6 : unframeBytes r5 with
                    | none => rw [h6] at hDec; cases hDec
                    | some p6 =>
                      rcases p6 with ⟨mac, tail⟩
                      rw [h6] at hDec
                      cases tail with
                      | cons _ _ => cases hDec
                      | nil =>
                        dsimp only at hDec
                        by_cases hMac : (mac.length == 32) = true
                        · simp only [hMac, ↓reduceIte] at hDec
                          injection hDec with hRec
                          subst hRec
                          obtain ⟨_, hBs1⟩ := unframeBytes_canonical h1
                          obtain ⟨_, hBs2⟩ := unframeBytes_canonical h2
                          obtain ⟨_, hBs3⟩ := unframeBytes_canonical h3
                          obtain ⟨_, hBs4⟩ := unframeBytes_canonical h4
                          obtain ⟨hPayLt, hBs5⟩ := unframeBytes_canonical h5
                          obtain ⟨_, hBs6⟩ := unframeBytes_canonical h6
                          obtain ⟨hEpLt, hEpCan⟩ := decodeU64BeNat_canonical hEp
                          have hMacLen : mac.length = 32 := Nat.eq_of_beq_eq_true hMac
                          refine ⟨⟨⟨hVkEq, hLgEq, hEpLt, hPayLt⟩, hMacLen⟩, ?_⟩
                          unfold encodeWalRecord
                          dsimp only [concatFramed]
                          rw [hMagEq] at hBs1
                          rw [hEpCan, hBs1, hBs2, hBs3, hBs4, hBs5, hBs6]
                        · simp only [hMac, Bool.false_eq_true, ↓reduceIte] at hDec; cases hDec

/-- Keyed-MAC function type (`Key → Preimage → 32-byte Tag`, e.g. `KMAC256` / `HMAC-SHA3-256`). -/
abbrev KeyedMacFn := List UInt8 → List UInt8 → List UInt8

/-- Width invariant on a 256-bit `KeyedMacFn` (`∀ key msg, (macFn key msg).length = 32`). -/
def WellFormedMacFn (macFn : KeyedMacFn) : Prop :=
  ∀ key msg, (macFn key msg).length = 32

/-- Compute a 32-byte keyed MAC over the domain-separated length-framed `WalRecordBody`. -/
def computeWalMac (macFn : KeyedMacFn) (macKey : List UInt8) (b : WalRecordBody) : List UInt8 :=
  macFn macKey (encodeWalBody b)

/-- Attach a 256-bit `keyedMac` tag to `WalRecordBody`. -/
def signWalRecord (macFn : KeyedMacFn) (macKey : List UInt8) (b : WalRecordBody) : WalRecord :=
  { body := b, keyedMac := computeWalMac macFn macKey b }

/-- Verify a `WalRecord`'s 256-bit `keyedMac`. -/
def verifyWalMac (macFn : KeyedMacFn) (macKey : List UInt8) (r : WalRecord) : Bool :=
  r.keyedMac == computeWalMac macFn macKey r.body

theorem signWalRecord_wellFormed {macFn : KeyedMacFn} (hMacWf : WellFormedMacFn macFn)
    (macKey : List UInt8) {b : WalRecordBody} (hb : b.WellFormed) :
    (signWalRecord macFn macKey b).WellFormed :=
  ⟨hb, hMacWf macKey (encodeWalBody b)⟩

@[simp]
theorem verifyWalMac_signWalRecord (macFn : KeyedMacFn) (macKey : List UInt8) (b : WalRecordBody) :
    verifyWalMac macFn macKey (signWalRecord macFn macKey b) = true := by
  simp [verifyWalMac, signWalRecord]

/-- **Existential EUF-CMA `MacForgery` Predicate (`0 Classical.choice`)**:
    Holds iff an adversary produces a well-formed `WalRecord` with a valid 256-bit `keyedMac`
    whose `WalRecordBody` was **never** authenticated by the honest vault (`r.body ∉ honestBodies`). -/
def MacForgery (macFn : KeyedMacFn) (macKey : List UInt8)
    (honestBodies : List WalRecordBody) : Prop :=
  ∃ r : WalRecord,
    r.WellFormed ∧
    r.body ∉ honestBodies ∧
    verifyWalMac macFn macKey r = true

/-- **Constructive Authentication Split (`verifyWalMac_authentic_or_macForgery`, `0 Classical`)**:
    Branching via `DecidableEq WalRecordBody`, any well-formed `WalRecord` passing `verifyWalMac`
    either belongs to `honestBodies` OR constructively witnesses `MacForgery`! -/
theorem verifyWalMac_authentic_or_macForgery
    {macFn : KeyedMacFn} {macKey : List UInt8}
    {honestBodies : List WalRecordBody} {r : WalRecord}
    (hWf : r.WellFormed) (hVer : verifyWalMac macFn macKey r = true) :
    r.body ∈ honestBodies ∨ MacForgery macFn macKey honestBodies := by
  by_cases hMem : r.body ∈ honestBodies
  · exact Or.inl hMem
  · exact Or.inr ⟨r, hWf, hMem, hVer⟩

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
def closeVaultHandle (st : PosixFsState) (h : LockedVaultHandle) : Except PosixErr PosixFsState :=
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

private theorem resolveOpenFd_insert_self (t : OpenFdTable) (p : Pid) (fd : FdId)
    (descId : OpenDescriptionId) (desc : OpenFileDesc) :
    resolveOpenFd
      { fdRefs := assocInsert (p, fd) descId t.fdRefs
        descriptions := assocInsert descId desc t.descriptions
        nextDescId := descId + 1 } p fd = some (descId, desc) := by
  simp [resolveOpenFd]

private theorem posixCloseFd_preserves_storage (sA : PosixFsState) (p : Pid) (fd : FdId) :
    let sB := (posixCloseFd sA p fd).toOption.getD sA
    sB.kernel.dirInode = sA.kernel.dirInode ∧
    sB.kernel.pageCache = sA.kernel.pageCache ∧
    sB.driveCache = sA.driveCache ∧
    sB.nand = sA.nand := by
  dsimp only
  unfold posixCloseFd
  cases assocLookup sA.kernel.openFds.fdRefs (p, fd) with
  | none => simp [Except.toOption]
  | some descId =>
    dsimp only
    by_cases hRef : descHasAnyRef (assocErase (p, fd) sA.kernel.openFds.fdRefs) descId = true <;>
      simp [hRef, Except.toOption]

/-- Durable vault invariant at rest: both `.lock` (`lockIno`) and `basePath` (`recIno`) are
    committed to `NandBlocks` with zero pending volatile writes and synced directory entries. -/
def VaultDurableAt (st : PosixFsState) (basePath : DirName) (lockIno : InodeId)
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
    unfold posixOpenExistingNoFollow resolveDentryNoFollow
    rw [hLockUnsync, hFdsEmpty]
    rfl
  let st2 : PosixFsState :=
    { st1 with kernel := { st1.kernel with flockTable := { locks := [(lockIno, 1)] } } }
  have hFlk : posixFlockExNb st1 pid st.nextFd = .ok st2 := by
    unfold posixFlockExNb resolveOpenFd FlockTable.owner
    dsimp only [st1]
    rw [hFlkEmpty]
    simp [assocInsert]
  have hFst : posixFstatDescAndInode st2 pid st.nextFd = .ok (1, lockIno) := by
    simp [posixFstatDescAndInode, resolveOpenFd, st2, st1]
  have hPread1 :
      posixPreadAll st2 pid st.nextFd =
        .ok (encodeLockSidecar { sealedLockInode := lockIno, genesisNonce := genesisNonce }) := by
    unfold posixPreadAll resolveOpenFd readInodeHierarchy pendingVolatileWrite
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
    unfold posixOpenExistingNoFollow resolveDentryNoFollow
    dsimp only [st2, st1]
    rw [hRecUnsync]
  have hPread2 : posixPreadAll st3 pid (st.nextFd + 1) = .ok (encodeWalRecord rec) := by
    unfold posixPreadAll resolveOpenFd readInodeHierarchy pendingVolatileWrite
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
          unfold posixCreateExclNoFollow
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
          unfold posixPwriteAll
          simp [stCreated, resolveOpenFd_insert_self]
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
                                  pageCache := { dirtyFiles :=
                                    assocErase tmpIno stWritten.kernel.pageCache.dirtyFiles } }
                    driveCache := { stWritten.driveCache with
                                     cachedFiles := assocErase tmpIno st.driveCache.cachedFiles } },
                 .error .eio) := by
            unfold posixSyncAllMedia
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
                                pageCache := { dirtyFiles :=
                                  assocErase tmpIno stWritten.kernel.pageCache.dirtyFiles } }
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
                  · rw [← hSyErrEq] at hSyErrWin; exact hSyErrWin
                  · rcases List.mem_cons.mp hMid with rfl | hMid
                    · rw [← hSyErrEq] at hSyErrWin
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
                                  pageCache := { dirtyFiles :=
                                    assocErase tmpIno stWritten.kernel.pageCache.dirtyFiles } }
                    driveCache := { stWritten.driveCache with
                                     cachedFiles := assocErase tmpIno st.driveCache.cachedFiles }
                    nand := { stWritten.nand with
                               fileBlocks := assocInsert tmpIno (encodeWalRecord newRec)
                                               stWritten.nand.fileBlocks } },
                 .ok ()) := by
            unfold posixSyncAllMedia readInodeHierarchy pendingVolatileWrite
            simp [stWritten, stCreated, resolveOpenFd_insert_self, hFailFalse]
          rw [hSyOk] at hMid
          dsimp only at hMid
          let stSyncedTmp : PosixFsState :=
            { stWritten with
               kernel := { stWritten.kernel with
                            pageCache := { dirtyFiles :=
                              assocErase tmpIno stWritten.kernel.pageCache.dirtyFiles } }
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
                                      if tmpPath == h.basePath then
                                        assocInsert h.basePath (.regular tmpIno)
                                          stClosedTmp.kernel.dirInode.unsyncedEntries
                                      else
                                        assocErase tmpPath
                                          (assocInsert h.basePath (.regular tmpIno)
                                            stClosedTmp.kernel.dirInode.unsyncedEntries) } } } := by
            unfold posixRename
            rw [hTmpPresent]
            rfl
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
                              if tmpPath == h.basePath then
                                assocInsert h.basePath (.regular tmpIno)
                                  stClosedTmp.kernel.dirInode.unsyncedEntries
                              else
                                assocErase tmpPath
                                  (assocInsert h.basePath (.regular tmpIno)
                                    stClosedTmp.kernel.dirInode.unsyncedEntries) } } }
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
            dsimp only [stSyncedDir, posixSyncParentDir]
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
