module
/-
# Qsag.Exec.PosixCrashWal — Conditional storage contracts and crash safety models

Choice-free formalization (`0` proof gaps, `0` custom axioms, `≤ 12` `@[expose]`)
of explicitly contracted three-tier crash semantics, POSIX inode/dentry/symlink/`flock` behavior,
`CuttleFS`/`fsyncgate` sticky I/O-error handle poisoning, dual-bound `lockGenesisId` inode sealing,
unified `CeremonyJournalRecord` crash-prefix atomicity, and reserve-before-sign multi-crash safety:

1. **Contractual Three-Tier Storage + POSIX Inode / Dentry / Symlink / Open-Description `flock` Machine**:
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
     `flock` sharing vs independent-`open()` contention (`same_pid_independent_opens_contend_flock_ewouldblock`,
     `dup_and_fork_shared_description_shares_flock_until_last_close`), and `CuttleFS`/`fsyncgate` sticky handle
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
   - `ceremony_journal_released_implies_all_reservations_durable_and_no_reuse`
   - `externalAnchor_rejects_whole_disk_rollback`

4. **Per-Inode Crash Outcomes, Media Damage, Whole-Device Rollback & the External Anchor (§7)**:
   - `crashStep_inode_outcome`: every `CrashStep` leaves an inode holding its old bytes, the
     drive-cache copy, or a sector mix of old and in-flight bytes; `MediaDamageInode` models
     bit-rot of settled blocks.
   - `ExternalMonotoneAnchor` is the `LedgerCheckpoint` of `durable_ledger.rs`: a minimum
     generation plus tag (`externalAnchor_rejects_whole_disk_rollback`,
     `externalAnchor_accepts_durable_successor`, `externalAnchor_rejects_same_generation_fork`).
   - `anchored_custody_epoch_unique_under_device_rollback`: with the anchor checked before
     release, NO sequence of whole-device replacements (snapshot restore, bit-rot, forged image)
     reuses an epoch, for any MAC; `tooth_unanchored_device_restore_reuses_epoch` and
     `witness_unanchored_device_restore_reuses_epoch` show the unanchored machine does.
   - `qsag-fts/src/wal.rs`: `verifyBurnChain` / `openBurnJournal` (tag chained through
     `last_tag`, whole-record length, no duplicates), `burnJournal_append_crash_outcomes`,
     `verifyBurnChain_prefix`, `tooth_burnJournal_truncation_is_undetectable_without_anchor`,
     `burnJournal_anchor_rejects_truncation`.
   - `burnHost_multi_crash_no_double_burn`: the append journal across arbitrary opens,
     reservations and crashes during an append that leave ANY not-shorter file: no leaf is
     burned twice and every burned leaf survives every successful recovery, or the accepted
     file exhibits a `BurnChainSubstitution` (`burnAppendCrash_outcome_complete` shows the crash
     alphabet covers every such file). `openBurnBytes_journalBytes` identifies the byte-level
     `QSBURN03` decoder with the record model; `openBurnBytes_copied_inode_refused`.
   - `qsag-cli/src/vault.rs`: `vault_reserve_crash_old_new_or_fail_closed` (companion MAC
     overwritten in place, then atomic rename) and `vault_state_file_rollback_rejected`.
   - `recoverLedger_intact_slot_never_rolls_back`: two-slot `durable_ledger.rs` recovery with
     the non-current slot damaged arbitrarily.

   Crash coverage of the two trace machines. The custody machine has `midReserveCrash`: the
   system dies at any syscall boundary inside a reservation (either crash kind); the flagship
   uniqueness theorem quantifies over traces containing it. In the ceremony machine an I/O
   error is not a crash: the host is poisoned (`ioPoisoned`), keeps the kernel state the failed
   replacement left, serves nothing, and any later crash of either kind recovers the old or the
   new journal record. `ProcessRestart` separately drops descriptors and locks while preserving
   dirty pages and NAND; `processRestart_is_not_fsync` prevents treating that restart as a commit.

5. **Hardware/POSIX `#tooth` Mutation Witnesses & Concrete Multi-Crash Trace Witness**:
   - `tooth_split_subordinate_wals_crash_between_commits_causes_resource_desync`
   - `tooth_rename_without_tmp_sync_exposes_torn_or_garbage_file`
   - `tooth_darwin_fsync_without_fullfsync_loses_committed_epoch_on_power_loss`
   - `tooth_missing_parent_dir_sync_loses_genesis_after_power_loss`
   - `tooth_unlink_and_failed_mustCreate_splits_flock_without_lockGenesisId`
   - `tooth_missing_wal_treated_as_fresh_causes_epoch_zero_amnesia`
   - `tooth_retry_after_fsync_eio_without_sticky_poison_violates_durability`
   - `inhabited_posix_crash_wal_trace`
-/

public import Qsag.Math.Constructive
public import Qsag.Exec.SimulationSpine
public import Qsag.Oracle.Keccak
import Qsag.Tactic.AssuranceKit

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

/-- Constructive finite association-list lookup (choice-free). -/
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

private theorem two_pow_32_lt_two_pow_64 : 2 ^ 32 < 2 ^ 64 := by decide

private def encodeLeBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | w + 1, n => UInt8.ofNat (n % 256) :: encodeLeBytes w (n / 256)

private def decodeLeBytes : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * decodeLeBytes bs

private theorem encodeLeBytes_length : ∀ (w n : Nat), (encodeLeBytes w n).length = w
  | 0, _ => rfl
  | w + 1, n => congrArg Nat.succ (encodeLeBytes_length w (n / 256))

private theorem decodeLeBytes_encodeLeBytes :
    ∀ (w n : Nat), n < 256 ^ w → decodeLeBytes (encodeLeBytes w n) = n
  | 0, n, h => by
    simp only [Nat.pow_zero] at h
    have hn : n = 0 := by omega
    subst hn; rfl
  | w + 1, n, h => by
    dsimp only [encodeLeBytes, decodeLeBytes]
    have hMod : (UInt8.ofNat (n % 256)).toNat = n % 256 := by
      change ((BitVec.ofNat 8 (n % 256)).toNat) = n % 256
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (Nat.mod_lt n (by decide))
    rw [hMod]
    have hDiv : n / 256 < 256 ^ w := by
      rw [Nat.pow_succ] at h
      omega
    rw [decodeLeBytes_encodeLeBytes w (n / 256) hDiv]
    omega

private theorem decodeLeBytes_canonical :
    ∀ (bs : List UInt8),
      decodeLeBytes bs < 256 ^ bs.length ∧ encodeLeBytes bs.length (decodeLeBytes bs) = bs
  | [] => ⟨by decide, rfl⟩
  | b :: bs => by
    obtain ⟨hLt, hCan⟩ := decodeLeBytes_canonical bs
    dsimp only [List.length_cons, decodeLeBytes, encodeLeBytes]
    have hb : b.toNat < 256 := b.toBitVec.isLt
    refine ⟨by rw [Nat.pow_succ]; omega, ?_⟩
    have hMod : (b.toNat + 256 * decodeLeBytes bs) % 256 = b.toNat := by omega
    have hDiv : (b.toNat + 256 * decodeLeBytes bs) / 256 = decodeLeBytes bs := by omega
    have hU8 : UInt8.ofNat b.toNat = b :=
      UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt hb))
    rw [hMod, hDiv, hU8, hCan]

private theorem pow_256_8_eq_two_pow_64 : (256 : Nat) ^ 8 = 2 ^ 64 := by
  show (2 ^ 8) ^ 8 = 2 ^ 64
  rw [← Nat.pow_mul]

/-- Encode a natural number `< 2^64` as 8 big-endian bytes (`u64be`). -/
def encodeU64BeNat (n : Nat) : List UInt8 :=
  (encodeLeBytes 8 n).reverse

/-- Decode 8 big-endian bytes into a natural number `< 2^64`. -/
def decodeU64BeNat (bs : List UInt8) : Option Nat :=
  if bs.length == 8 then
    some (decodeLeBytes bs.reverse)
  else
    none

theorem encodeU64BeNat_length (n : Nat) : (encodeU64BeNat n).length = 8 := by
  simp [encodeU64BeNat, encodeLeBytes_length]

private theorem lt_two_pow_32_of_le_8192 {n : Nat} (h : n ≤ 8192) : n < 2 ^ 32 :=
  Nat.lt_of_le_of_lt h (Nat.lt_of_lt_of_le (by decide : 8192 < 2 ^ 14)
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by decide : 14 ≤ 32)))

theorem decodeU64BeNat_encodeU64BeNat {n : Nat} (hLt : n < 2 ^ 64) :
    decodeU64BeNat (encodeU64BeNat n) = some n := by
  unfold decodeU64BeNat encodeU64BeNat
  have hLen : ((encodeLeBytes 8 n).reverse.length == 8) = true := by
    rw [List.length_reverse, encodeLeBytes_length]; rfl
  rw [hLen]
  simp only [↓reduceIte, List.reverse_reverse]
  have hLt256 : n < 256 ^ 8 := by rw [pow_256_8_eq_two_pow_64]; exact hLt
  rw [decodeLeBytes_encodeLeBytes 8 n hLt256]

theorem encodeU64BeNat_injective {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (hEq : encodeU64BeNat a = encodeU64BeNat b) : a = b := by
  have hDec := congrArg decodeU64BeNat hEq
  rw [decodeU64BeNat_encodeU64BeNat ha, decodeU64BeNat_encodeU64BeNat hb] at hDec
  injection hDec

theorem decodeU64BeNat_canonical {bs : List UInt8} {v : Nat}
    (h : decodeU64BeNat bs = some v) : v < 2 ^ 64 ∧ encodeU64BeNat v = bs := by
  unfold decodeU64BeNat at h
  by_cases hLen : (bs.length == 8) = true
  · simp only [hLen, ↓reduceIte] at h
    injection h with hVal
    subst hVal
    have hBsLen : bs.length = 8 := Nat.eq_of_beq_eq_true hLen
    have hRevLen : bs.reverse.length = 8 := by rw [List.length_reverse, hBsLen]
    obtain ⟨hLt, hCan⟩ := decodeLeBytes_canonical bs.reverse
    rw [hRevLen] at hLt hCan
    refine ⟨by rw [← pow_256_8_eq_two_pow_64]; exact hLt, ?_⟩
    unfold encodeU64BeNat
    rw [hCan, List.reverse_reverse]
  · simp only [hLen, Bool.false_eq_true, ↓reduceIte] at h
    cases h

attribute [irreducible] encodeU64BeNat decodeU64BeNat

private theorem pow_256_4_eq_two_pow_32 : (256 : Nat) ^ 4 = 2 ^ 32 := by
  show (2 ^ 8) ^ 4 = 2 ^ 32
  rw [← Nat.pow_mul]

private def pcwEncodeU32Be (n : Nat) : List UInt8 :=
  (encodeLeBytes 4 n).reverse

private def pcwDecodeU32Be (bs : List UInt8) : Option Nat :=
  if bs.length == 4 then some (decodeLeBytes bs.reverse) else none

private theorem pcwEncodeU32Be_length (n : Nat) : (pcwEncodeU32Be n).length = 4 := by
  simp [pcwEncodeU32Be, encodeLeBytes_length]

private theorem pcwDecodeU32Be_encodeU32Be {n : Nat} (hLt : n < 2 ^ 32) :
    pcwDecodeU32Be (pcwEncodeU32Be n) = some n := by
  unfold pcwDecodeU32Be pcwEncodeU32Be
  have hLen : ((encodeLeBytes 4 n).reverse.length == 4) = true := by
    rw [List.length_reverse, encodeLeBytes_length]; rfl
  rw [hLen]
  simp only [↓reduceIte, List.reverse_reverse]
  have hLt256 : n < 256 ^ 4 := by rw [pow_256_4_eq_two_pow_32]; exact hLt
  rw [decodeLeBytes_encodeLeBytes 4 n hLt256]

private theorem pcwDecodeU32Be_canonical {bs : List UInt8} {v : Nat}
    (h : pcwDecodeU32Be bs = some v) : v < 2 ^ 32 ∧ pcwEncodeU32Be v = bs := by
  unfold pcwDecodeU32Be at h
  by_cases hLen : (bs.length == 4) = true
  · simp only [hLen, ↓reduceIte] at h
    injection h with hVal
    subst hVal
    have hBsLen : bs.length = 4 := Nat.eq_of_beq_eq_true hLen
    have hRevLen : bs.reverse.length = 4 := by rw [List.length_reverse, hBsLen]
    obtain ⟨hLt, hCan⟩ := decodeLeBytes_canonical bs.reverse
    rw [hRevLen] at hLt hCan
    refine ⟨by rw [← pow_256_4_eq_two_pow_32]; exact hLt, ?_⟩
    unfold pcwEncodeU32Be
    rw [hCan, List.reverse_reverse]
  · simp only [hLen, Bool.false_eq_true, ↓reduceIte] at h
    cases h

private def pcwFrameBytes (payload : List UInt8) : List UInt8 :=
  pcwEncodeU32Be payload.length ++ payload

private def pcwUnframeBytes (buf : List UInt8) : Option (List UInt8 × List UInt8) :=
  if buf.length < 4 then
    none
  else
    match pcwDecodeU32Be (buf.take 4) with
    | none => none
    | some len =>
      let body := buf.drop 4
      if body.length < len then
        none
      else
        some (body.take len, body.drop len)

private def pcwConcatFramed : List (List UInt8) → List UInt8
  | [] => []
  | x :: xs => pcwFrameBytes x ++ pcwConcatFramed xs

@[simp]
private theorem pcwFrameBytes_length (xs : List UInt8) :
    (pcwFrameBytes xs).length = 4 + xs.length := by
  simp [pcwFrameBytes, pcwEncodeU32Be_length]

private theorem pcwConcatFramed_nil : pcwConcatFramed [] = [] := rfl

private theorem pcwConcatFramed_cons (x : List UInt8) (xs : List (List UInt8)) :
    pcwConcatFramed (x :: xs) = pcwFrameBytes x ++ pcwConcatFramed xs := rfl

private theorem pcwUnframe_frame_append {payload : List UInt8} (hLen : payload.length < 2 ^ 32)
    (rest : List UInt8) :
    pcwUnframeBytes (pcwFrameBytes payload ++ rest) = some (payload, rest) := by
  unfold pcwUnframeBytes pcwFrameBytes
  rw [List.append_assoc]
  have hNotLt4 : ¬ (pcwEncodeU32Be payload.length ++ (payload ++ rest)).length < 4 := by
    rw [List.length_append, pcwEncodeU32Be_length]
    omega
  have hNotLtBody : ¬ (payload ++ rest).length < payload.length := by
    rw [List.length_append]
    omega
  simp only [hNotLt4, ↓reduceIte,
    take_append_of_len_eq (pcwEncodeU32Be_length payload.length),
    drop_append_of_len_eq (pcwEncodeU32Be_length payload.length),
    pcwDecodeU32Be_encodeU32Be hLen,
    hNotLtBody, take_append_exact, drop_append_exact]

private theorem pcwUnframeBytes_canonical {buf payload rest : List UInt8}
    (h : pcwUnframeBytes buf = some (payload, rest)) :
    payload.length < 2 ^ 32 ∧ buf = pcwFrameBytes payload ++ rest := by
  unfold pcwUnframeBytes at h
  by_cases hLt4 : buf.length < 4
  · simp only [hLt4, ↓reduceIte] at h
    cases h
  · simp only [hLt4, ↓reduceIte] at h
    cases hDec : pcwDecodeU32Be (buf.take 4) with
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
        obtain ⟨hLenLt, hDecCan⟩ := pcwDecodeU32Be_canonical hDec
        have hPayLen : payload.length = len := by
          rw [← hPay, List.length_take]
          omega
        refine ⟨hPayLen ▸ hLenLt, ?_⟩
        unfold pcwFrameBytes
        rw [hPayLen, hDecCan, ← hPay, ← hRest]
        rw [List.append_assoc, List.take_append_drop, List.take_append_drop]

private theorem pcwConcatFramed_injective :
    ∀ {xs ys : List (List UInt8)},
      (∀ x ∈ xs, x.length < 2 ^ 32) →
      (∀ y ∈ ys, y.length < 2 ^ 32) →
      pcwConcatFramed xs = pcwConcatFramed ys →
      xs = ys
  | [], [], _, _, _ => rfl
  | x :: xs, [], hx, _, hEq => by
    have hUnf := congrArg pcwUnframeBytes hEq
    rw [pcwConcatFramed_cons, pcwUnframe_frame_append (hx x (.head _))] at hUnf
    cases hUnf
  | [], y :: ys, _, hy, hEq => by
    have hUnf := congrArg pcwUnframeBytes hEq
    rw [pcwConcatFramed_cons, pcwUnframe_frame_append (hy y (.head _))] at hUnf
    cases hUnf
  | x :: xs, y :: ys, hx, hy, hEq => by
    have hUnf := congrArg pcwUnframeBytes hEq
    rw [pcwConcatFramed_cons, pcwConcatFramed_cons,
        pcwUnframe_frame_append (hx x (.head _)),
        pcwUnframe_frame_append (hy y (.head _))] at hUnf
    injection hUnf with hPair
    injection hPair with hHead hTail
    rw [hHead, pcwConcatFramed_injective
      (fun a ha => hx a (.tail _ ha))
      (fun b hb => hy b (.tail _ hb))
      hTail]

attribute [irreducible] pcwFrameBytes pcwUnframeBytes pcwConcatFramed

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

/-- Encode `LockSidecarSeal` onto `.lock` media (`pcwConcatFramed [magic, u64be(ino), nonce32]`). -/
def encodeLockSidecar (s : LockSidecarSeal) : List UInt8 :=
  pcwConcatFramed [lockSidecarMagicTag, encodeU64BeNat s.sealedLockInode, s.genesisNonce]

/-- Decode and validate canonical `LockSidecarSeal` bytes. -/
def decodeLockSidecar (bs : List UInt8) : Option LockSidecarSeal :=
  match pcwUnframeBytes bs with
  | none => none
  | some (magic, r1) =>
    if magic != lockSidecarMagicTag then none
    else match pcwUnframeBytes r1 with
    | none => none
    | some (inoBytes, r2) =>
      match decodeU64BeNat inoBytes with
      | none => none
      | some ino =>
        match pcwUnframeBytes r2 with
        | none => none
        | some (nonce, tail) =>
          match tail with
          | [] =>
            if nonce.length == 32 then
              some { sealedLockInode := ino, genesisNonce := nonce }
            else none
          | _ :: _ => none

theorem decodeLockSidecar_encodeLockSidecar {s : LockSidecarSeal} (hWf : s.WellFormed) :
    decodeLockSidecar (encodeLockSidecar s) = some s := by
  rcases hWf with ⟨hIno, hNonce⟩
  rw [decodeLockSidecar.eq_1, encodeLockSidecar.eq_1]
  have hm : lockSidecarMagicTag.length < 2 ^ 32 :=
    lt_two_pow_32_of_le_8192 (by decide)
  have hi : (encodeU64BeNat s.sealedLockInode).length < 2 ^ 32 := by
    apply lt_two_pow_32_of_le_8192; rw [encodeU64BeNat_length]; decide
  have hn : s.genesisNonce.length < 2 ^ 32 := by
    apply lt_two_pow_32_of_le_8192; rw [hNonce]; decide
  rw [pcwConcatFramed_cons, pcwUnframe_frame_append hm]
  dsimp only
  rw [bne_self_eq_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [pcwConcatFramed_cons, pcwUnframe_frame_append hi]
  dsimp only
  rw [decodeU64BeNat_encodeU64BeNat hIno]
  dsimp only
  rw [pcwConcatFramed_cons, pcwConcatFramed_nil, pcwUnframe_frame_append hn]
  dsimp only
  have hNBeq : (s.genesisNonce.length == 32) = true := by rw [hNonce]; rfl
  rw [hNBeq]
  simp only [↓reduceIte]

theorem decodeLockSidecar_canonical {bs : List UInt8} {s : LockSidecarSeal}
    (hDec : decodeLockSidecar bs = some s) :
    s.WellFormed ∧ encodeLockSidecar s = bs := by
  rw [decodeLockSidecar.eq_1] at hDec
  cases h1 : pcwUnframeBytes bs with
  | none => rw [h1] at hDec; cases hDec
  | some p1 =>
    rcases p1 with ⟨magic, r1⟩
    rw [h1] at hDec
    dsimp only at hDec
    by_cases hMag : (magic != lockSidecarMagicTag) = true
    · simp only [hMag, ↓reduceIte] at hDec; cases hDec
    · simp only [hMag, Bool.false_eq_true, ↓reduceIte] at hDec
      have hMagEq : magic = lockSidecarMagicTag := eq_of_not_bne_true hMag
      cases h2 : pcwUnframeBytes r1 with
      | none => rw [h2] at hDec; cases hDec
      | some p2 =>
        rcases p2 with ⟨inoBytes, r2⟩
        rw [h2] at hDec
        dsimp only at hDec
        cases hIno : decodeU64BeNat inoBytes with
        | none => rw [hIno] at hDec; cases hDec
        | some ino =>
          rw [hIno] at hDec
          dsimp only at hDec
          cases h3 : pcwUnframeBytes r2 with
          | none => rw [h3] at hDec; cases hDec
          | some p3 =>
            rcases p3 with ⟨nonce, tail⟩
            rw [h3] at hDec
            dsimp only at hDec
            cases tail with
            | cons _ _ => cases hDec
            | nil =>
              dsimp only at hDec
              by_cases hNLen : (nonce.length == 32) = true
              · simp only [hNLen, ↓reduceIte] at hDec
                injection hDec with hEqS
                subst hEqS
                obtain ⟨_, hBs1⟩ := pcwUnframeBytes_canonical h1
                obtain ⟨_, hBs2⟩ := pcwUnframeBytes_canonical h2
                obtain ⟨_, hBs3⟩ := pcwUnframeBytes_canonical h3
                obtain ⟨hInoLt, hInoCan⟩ := decodeU64BeNat_canonical hIno
                refine ⟨⟨hInoLt, Nat.eq_of_beq_eq_true hNLen⟩, ?_⟩
                rw [encodeLockSidecar.eq_1]
                rw [pcwConcatFramed_cons, pcwConcatFramed_cons, pcwConcatFramed_cons, pcwConcatFramed_nil]
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
  pcwConcatFramed [walMacDomainTag, b.vaultKeyId, b.lockGenesisId, encodeU64BeNat b.epoch, b.payload]

/-- **MAC Preimage Collision-Freedom (`encodeWalBody_injective`)**:
    Every field of `WalRecordBody` is length-framed via `pcwConcatFramed`, so distinct well-formed
    record bodies **never** share a MAC preimage (choice-free). -/
theorem encodeWalBody_injective {b₁ b₂ : WalRecordBody}
    (h₁ : b₁.WellFormed) (h₂ : b₂.WellFormed)
    (hEq : encodeWalBody b₁ = encodeWalBody b₂) : b₁ = b₂ := by
  rcases h₁ with ⟨hk₁, hl₁, he₁, hp₁⟩
  rcases h₂ with ⟨hk₂, hl₂, he₂, hp₂⟩
  rw [encodeWalBody.eq_1, encodeWalBody.eq_1] at hEq
  have hBnd₁ : ∀ x ∈ [walMacDomainTag, b₁.vaultKeyId, b₁.lockGenesisId, encodeU64BeNat b₁.epoch, b₁.payload],
      x.length < 2 ^ 32 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact lt_two_pow_32_of_le_8192 (by decide)
    · rcases List.mem_cons.mp hx with rfl | hx
      · apply lt_two_pow_32_of_le_8192; rw [hk₁]; decide
      · rcases List.mem_cons.mp hx with rfl | hx
        · apply lt_two_pow_32_of_le_8192; rw [hl₁]; decide
        · rcases List.mem_cons.mp hx with rfl | hx
          · apply lt_two_pow_32_of_le_8192; rw [encodeU64BeNat_length]; decide
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact hp₁
            · cases hx
  have hBnd₂ : ∀ y ∈ [walMacDomainTag, b₂.vaultKeyId, b₂.lockGenesisId, encodeU64BeNat b₂.epoch, b₂.payload],
      y.length < 2 ^ 32 := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact lt_two_pow_32_of_le_8192 (by decide)
    · rcases List.mem_cons.mp hy with rfl | hy
      · apply lt_two_pow_32_of_le_8192; rw [hk₂]; decide
      · rcases List.mem_cons.mp hy with rfl | hy
        · apply lt_two_pow_32_of_le_8192; rw [hl₂]; decide
        · rcases List.mem_cons.mp hy with rfl | hy
          · apply lt_two_pow_32_of_le_8192; rw [encodeU64BeNat_length]; decide
          · rcases List.mem_cons.mp hy with rfl | hy
            · exact hp₂
            · cases hy
  have hListEq := pcwConcatFramed_injective hBnd₁ hBnd₂ hEq
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
  pcwConcatFramed [walFileMagicTag, r.body.vaultKeyId, r.body.lockGenesisId,
                   encodeU64BeNat r.body.epoch, r.body.payload, r.keyedMac]

/-- Decode a complete `WalRecord` from disk bytes, rejecting truncated, torn, or trailing bytes. -/
def decodeWalRecord (bs : List UInt8) : Option WalRecord :=
  match pcwUnframeBytes bs with
  | none => none
  | some (magic, r1) =>
    if magic != walFileMagicTag then none
    else match pcwUnframeBytes r1 with
    | none => none
    | some (vkId, r2) =>
      if vkId.length != 32 then none
      else match pcwUnframeBytes r2 with
      | none => none
      | some (lgId, r3) =>
        if lgId.length != 40 then none
        else match pcwUnframeBytes r3 with
        | none => none
        | some (epBytes, r4) =>
          match decodeU64BeNat epBytes with
          | none => none
          | some ep =>
            match pcwUnframeBytes r4 with
            | none => none
            | some (payload, r5) =>
              match pcwUnframeBytes r5 with
              | none => none
              | some (mac, tail) =>
                match tail with
                | [] =>
                  if mac.length == 32 then
                    some { body := { vaultKeyId := vkId
                                     lockGenesisId := lgId
                                     epoch := ep
                                     payload := payload }
                           keyedMac := mac }
                  else none
                | _ :: _ => none

theorem decodeWalRecord_encodeWalRecord {r : WalRecord} (hWf : r.WellFormed) :
    decodeWalRecord (encodeWalRecord r) = some r := by
  rcases hWf with ⟨⟨hVk, hLg, hEp, hPay⟩, hMac⟩
  rw [decodeWalRecord.eq_1, encodeWalRecord.eq_1]
  have hm : walFileMagicTag.length < 2 ^ 32 :=
    lt_two_pow_32_of_le_8192 (by decide)
  have hvkLt : r.body.vaultKeyId.length < 2 ^ 32 := by
    apply lt_two_pow_32_of_le_8192; rw [hVk]; decide
  have hlgLt : r.body.lockGenesisId.length < 2 ^ 32 := by
    apply lt_two_pow_32_of_le_8192; rw [hLg]; decide
  have hepLt : (encodeU64BeNat r.body.epoch).length < 2 ^ 32 := by
    apply lt_two_pow_32_of_le_8192; rw [encodeU64BeNat_length]; decide
  have hmacLt : r.keyedMac.length < 2 ^ 32 := by
    apply lt_two_pow_32_of_le_8192; rw [hMac]; decide
  rw [pcwConcatFramed_cons, pcwUnframe_frame_append hm]
  dsimp only
  rw [bne_self_eq_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [pcwConcatFramed_cons, pcwUnframe_frame_append hvkLt]
  dsimp only
  have hVkNe : (r.body.vaultKeyId.length != 32) = false := by rw [hVk]; rfl
  rw [hVkNe]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [pcwConcatFramed_cons, pcwUnframe_frame_append hlgLt]
  dsimp only
  have hLgNe : (r.body.lockGenesisId.length != 40) = false := by rw [hLg]; rfl
  rw [hLgNe]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [pcwConcatFramed_cons, pcwUnframe_frame_append hepLt]
  dsimp only
  rw [decodeU64BeNat_encodeU64BeNat hEp]
  dsimp only
  rw [pcwConcatFramed_cons, pcwUnframe_frame_append hPay]
  dsimp only
  rw [pcwConcatFramed_cons, pcwConcatFramed_nil, pcwUnframe_frame_append hmacLt]
  dsimp only
  have hMacEq : (r.keyedMac.length == 32) = true := by rw [hMac]; rfl
  rw [hMacEq]
  simp only [↓reduceIte]

theorem decodeWalRecord_canonical {bs : List UInt8} {r : WalRecord}
    (hDec : decodeWalRecord bs = some r) :
    r.WellFormed ∧ encodeWalRecord r = bs := by
  rw [decodeWalRecord.eq_1] at hDec
  cases h1 : pcwUnframeBytes bs with
  | none => rw [h1] at hDec; cases hDec
  | some p1 =>
    rcases p1 with ⟨magic, r1⟩
    rw [h1] at hDec
    dsimp only at hDec
    by_cases hMag : (magic != walFileMagicTag) = true
    · simp only [hMag, ↓reduceIte] at hDec; cases hDec
    · simp only [hMag, Bool.false_eq_true, ↓reduceIte] at hDec
      have hMagEq : magic = walFileMagicTag := eq_of_not_bne_true hMag
      cases h2 : pcwUnframeBytes r1 with
      | none => rw [h2] at hDec; cases hDec
      | some p2 =>
        rcases p2 with ⟨vkId, r2⟩
        rw [h2] at hDec
        dsimp only at hDec
        by_cases hVk : (vkId.length != 32) = true
        · simp only [hVk, ↓reduceIte] at hDec; cases hDec
        · simp only [hVk, Bool.false_eq_true, ↓reduceIte] at hDec
          have hVkEq : vkId.length = 32 := eq_of_not_bne_true hVk
          cases h3 : pcwUnframeBytes r2 with
          | none => rw [h3] at hDec; cases hDec
          | some p3 =>
            rcases p3 with ⟨lgId, r3⟩
            rw [h3] at hDec
            dsimp only at hDec
            by_cases hLg : (lgId.length != 40) = true
            · simp only [hLg, ↓reduceIte] at hDec; cases hDec
            · simp only [hLg, Bool.false_eq_true, ↓reduceIte] at hDec
              have hLgEq : lgId.length = 40 := eq_of_not_bne_true hLg
              cases h4 : pcwUnframeBytes r3 with
              | none => rw [h4] at hDec; cases hDec
              | some p4 =>
                rcases p4 with ⟨epBytes, r4⟩
                rw [h4] at hDec
                dsimp only at hDec
                cases hEp : decodeU64BeNat epBytes with
                | none => rw [hEp] at hDec; cases hDec
                | some ep =>
                  rw [hEp] at hDec
                  dsimp only at hDec
                  cases h5 : pcwUnframeBytes r4 with
                  | none => rw [h5] at hDec; cases hDec
                  | some p5 =>
                    rcases p5 with ⟨payload, r5⟩
                    rw [h5] at hDec
                    dsimp only at hDec
                    cases h6 : pcwUnframeBytes r5 with
                    | none => rw [h6] at hDec; cases hDec
                    | some p6 =>
                      rcases p6 with ⟨mac, tail⟩
                      rw [h6] at hDec
                      dsimp only at hDec
                      cases tail with
                      | cons _ _ => cases hDec
                      | nil =>
                        dsimp only at hDec
                        by_cases hMac : (mac.length == 32) = true
                        · simp only [hMac, ↓reduceIte] at hDec
                          injection hDec with hRec
                          subst hRec
                          obtain ⟨_, hBs1⟩ := pcwUnframeBytes_canonical h1
                          obtain ⟨_, hBs2⟩ := pcwUnframeBytes_canonical h2
                          obtain ⟨_, hBs3⟩ := pcwUnframeBytes_canonical h3
                          obtain ⟨_, hBs4⟩ := pcwUnframeBytes_canonical h4
                          obtain ⟨hPayLt, hBs5⟩ := pcwUnframeBytes_canonical h5
                          obtain ⟨_, hBs6⟩ := pcwUnframeBytes_canonical h6
                          obtain ⟨hEpLt, hEpCan⟩ := decodeU64BeNat_canonical hEp
                          have hMacLen : mac.length = 32 := Nat.eq_of_beq_eq_true hMac
                          refine ⟨⟨⟨hVkEq, hLgEq, hEpLt, hPayLt⟩, hMacLen⟩, ?_⟩
                          rw [encodeWalRecord.eq_1]
                          rw [pcwConcatFramed_cons, pcwConcatFramed_cons, pcwConcatFramed_cons,
                              pcwConcatFramed_cons, pcwConcatFramed_cons, pcwConcatFramed_cons, pcwConcatFramed_nil]
                          rw [hMagEq] at hBs1
                          rw [hEpCan, hBs1, hBs2, hBs3, hBs4, hBs5, hBs6]
                        · simp only [hMac, Bool.false_eq_true, ↓reduceIte] at hDec; cases hDec

attribute [irreducible] encodeLockSidecar decodeLockSidecar encodeWalBody encodeWalRecord decodeWalRecord

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
    verifyWalMac macFn macKey (signWalRecord macFn macKey b) = true :=
  (beq_iff_eq (a := computeWalMac macFn macKey b) (b := computeWalMac macFn macKey b)).mpr rfl

/-- **Candidate-specific EUF-CMA bad event**:
    Holds iff an adversary produces a well-formed `WalRecord` with a valid 256-bit `keyedMac`
    whose `WalRecordBody` was **never** authenticated by the honest vault (`r.body ∉ honestBodies`). -/
def MacForgery (macFn : KeyedMacFn) (macKey : List UInt8)
    (queriedBodies : List WalRecordBody) (r : WalRecord) : Prop :=
    r.WellFormed ∧
    r.body ∉ queriedBodies ∧
    verifyWalMac macFn macKey r = true

/-- **Constructive Authentication Split (`verifyWalMac_authentic_or_macForgery`, `0 choice-free`)**:
    Branching via `DecidableEq WalRecordBody`, any well-formed `WalRecord` passing `verifyWalMac`
    either belongs to `honestBodies` OR constructively witnesses `MacForgery`! -/
theorem verifyWalMac_authentic_or_macForgery
    {macFn : KeyedMacFn} {macKey : List UInt8}
    {honestBodies : List WalRecordBody} {r : WalRecord}
    (hWf : r.WellFormed) (hVer : verifyWalMac macFn macKey r = true) :
    r.body ∈ honestBodies ∨ MacForgery macFn macKey honestBodies r := by
  by_cases hMem : r.body ∈ honestBodies
  · exact Or.inl hMem
  · exact Or.inr ⟨hWf, hMem, hVer⟩

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

private theorem self_mem_replaceAtomicSteps (st : PosixFsState) (h : LockedVaultHandle)
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

private theorem pickStepState_mem {fallback : PosixFsState} {xs : List PosixFsState}
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
    unfold posixOpenExistingNoFollow resolveDentryNoFollow
    rw [hLockUnsync, hFdsEmpty]
    rfl
  let st2 : PosixFsState :=
    { st1 with kernel := { st1.kernel with flockTable := { locks := [(lockIno, 1)] } } }
  have hFlk : posixFlockExNb st1 pid st.nextFd = .ok st2 := by
    unfold posixFlockExNb resolveOpenFd FlockTable.owner
    dsimp only [st1]
    rw [hFlkEmpty]
    simp [assocInsert, st2, st1]
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
            unfold posixSyncAllMedia readInodeHierarchy pendingVolatileWrite
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
            unfold posixRename
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
            unfold posixCreateExclNoFollow
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
            unfold posixPwriteAll
            simp [stWritten, stCreated, stCleanTmp, posixUnlinkIfPresent, resolveOpenFd_insert_self]
          rw [hWrEq] at hOk
          dsimp only at hOk
          cases hFailRec : faults.failRecordSync with
          | true =>
            have hSyF : (posixSyncAllMedia stWritten h.pid tmpFd true).2 = .error .eio := by
              unfold posixSyncAllMedia; simp [stWritten, stCreated, resolveOpenFd_insert_self]
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
              unfold posixSyncAllMedia readInodeHierarchy pendingVolatileWrite
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
              unfold posixRename; rw [hTmpPresent]
            rw [hRnEq] at hOk
            dsimp only at hOk
            cases hFailDir : faults.failParentSync with
            | true =>
              rw [hFailDir] at hOk
              unfold posixSyncParentDir at hOk
              simp only [↓reduceIte] at hOk
              cases (Prod.mk.inj (Prod.mk.inj hOk).2).2
            | false =>
              rw [hFailDir] at hOk
              unfold posixSyncParentDir at hOk
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
    unfold posixOpenExistingNoFollow at hOp1
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
          unfold posixFlockExNb at hFlk
          simp only [resolveOpenFd_insert_self] at hFlk
          cases hOwn : st.kernel.flockTable.owner ino1 with
          | none =>
            rw [hOwn] at hFlk
            injection hFlk with hSt2Eq
            rw [← hSt2Eq]
            exact ⟨by simp [posixFstatDescAndInode, resolveOpenFd_insert_self], Or.inl rfl⟩
          | some holderDesc =>
            rw [hOwn] at hFlk
            dsimp only at hFlk
            by_cases hHold : (holderDesc == st.kernel.openFds.nextDescId) = true
            · simp only [hHold, ↓reduceIte] at hFlk
              injection hFlk with hSt2Eq
              rw [← hSt2Eq]
              exact ⟨by simp [posixFstatDescAndInode, resolveOpenFd_insert_self],
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
      unfold posixCreateExclNoFollow; rw [hAbs]; rfl
    rw [hCr]
    dsimp only [posixUnlinkIfPresent]
    have hInoNeNew : h₁.lockInode ≠ newIno := Nat.ne_of_lt hInoLtNext
    have hDescLtNext : h₁.lockDescId < newDescId + 1 := Nat.lt_succ_of_lt hDescOrig
    unfold posixPwriteAll
    simp only [resolveOpenFd_insert_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    dsimp only [Except.toOption, Option.getD]
    unfold posixSyncAllMedia readInodeHierarchy pendingVolatileWrite
    simp only [resolveOpenFd_insert_self, Bool.false_eq_true, ↓reduceIte, assocLookup_insert_self]
    unfold posixSyncParentDir
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold posixCloseFd
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
def execReserveBeforeSignAtomic (st : PosixFsState) (pid : Pid) (basePath : DirName)
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
def initProvisionedCustodyState (pid : Pid) (basePath : DirName)
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

private theorem posixFlockExNb_preserves_storage {sA sB : PosixFsState} {p : Pid} {fd : FdId}
    (hFlk : posixFlockExNb sA p fd = .ok sB) :
    sB.kernel.dirInode = sA.kernel.dirInode ∧
    sB.kernel.pageCache = sA.kernel.pageCache ∧
    sB.driveCache = sA.driveCache ∧
    sB.nand = sA.nand := by
  unfold posixFlockExNb at hFlk
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

private theorem openExisting_preserves_storage_and_bounds_epoch
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
  unfold openExisting at hOpen
  cases hOp1 : posixOpenExistingNoFollow st pid (walLockPath basePath) true with
  | error e => rw [hOp1] at hOpen; cases (Prod.mk.inj hOpen).2
  | ok p1 =>
    rcases p1 with ⟨st1, lockFd⟩
    rw [hOp1] at hOpen
    dsimp only at hOpen
    have hSt1 : st1.kernel.dirInode = st.kernel.dirInode ∧
                st1.kernel.pageCache = st.kernel.pageCache ∧
                st1.driveCache = st.driveCache ∧ st1.nand = st.nand := by
      unfold posixOpenExistingNoFollow at hOp1
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
                unfold posixOpenExistingNoFollow resolveDentryNoFollow at hOp2
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
                      unfold posixPreadAll readInodeHierarchy pendingVolatileWrite
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

private theorem openExisting_err_preserves_storage
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
    unfold posixOpenExistingNoFollow at hO
    cases hR : resolveDentryNoFollow sA.kernel.dirInode.unsyncedEntries nm with
    | error e => rw [hR] at hO; cases hO
    | ok ino =>
      rw [hR] at hO; injection hO with hP; rw [← (Prod.mk.inj hP).1]; exact ⟨rfl, rfl, rfl, rfl⟩
  unfold openExisting at hErr
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
  unfold replaceAtomic at hRun
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
            unfold posixCreateExclNoFollow
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
            unfold posixPwriteAll
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
              unfold posixSyncAllMedia; simp [sSy, stWritten, stCreated, resolveOpenFd_insert_self]
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
              unfold posixSyncAllMedia readInodeHierarchy pendingVolatileWrite
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
              unfold posixRename; rw [hTmpPres]
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
              unfold posixSyncParentDir at hRun
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
              unfold posixSyncParentDir at hRun
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
  unfold replaceAtomicSteps at hMid
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
            unfold posixCreateExclNoFollow
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
            unfold posixPwriteAll
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
              unfold posixSyncAllMedia; simp [sSy, stWritten, stCreated, resolveOpenFd_insert_self]
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
              unfold posixSyncAllMedia readInodeHierarchy pendingVolatileWrite
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
              unfold posixRename; rw [hTmpPres]
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
  unfold provisionGenesis
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
          unfold posixCreateExclNoFollow; rw [hLookLock]
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
            unfold posixFlockExNb at hFlk
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
            unfold posixPwriteAll
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
            unfold posixSyncAllMedia
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
            unfold posixCreateExclNoFollow
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
            unfold posixPwriteAll
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
            unfold posixSyncAllMedia
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
          unfold provisionGenesis at hGen
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

private theorem nodup_snoc {α : Type} {xs : List α} {x : α}
    (hNodup : xs.Nodup) (hFresh : ∀ y ∈ xs, y ≠ x) :
    (xs ++ [x]).Nodup := by
  induction xs with
  | nil =>
    simp [List.Nodup]
  | cons a rest ih =>
    rw [List.cons_append, List.Nodup, List.pairwise_cons] at *
    refine ⟨?_, ih hNodup.2 (fun y hy => hFresh y (by simp [hy]))⟩
    intro y hy
    rcases List.mem_append.mp hy with hInRest | hInSing
    · exact hNodup.1 y hInRest
    · simp only [List.mem_singleton] at hInSing
      subst hInSing
      exact hFresh a (by simp)

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
