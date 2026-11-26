module

public import Qsag.Exec.PosixCrashWal.WalRecordCodec
public import Qsag.Exec.PosixCrashWal.StorageMachine
public import Qsag.Exec.PosixCrashWal.GenesisSealedWal
public import Qsag.Exec.PosixCrashWal.CustodyCrashSafety
public import Qsag.Exec.PosixCrashWal.CeremonyJournal
public import Qsag.Exec.PosixCrashWal.CrashWitnessesAndRecovery
public import Qsag.Exec.PosixCrashWal.RustDurability
import Qsag.Tactic.AssuranceKit

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
     `QSBURN05` decoder with the record model; `openBurnBytes_copied_inode_refused`.
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

public section

namespace Qsag.RustDurability

set_option autoImplicit false

/-- `QSBURN05` page geometry (`crates/qsag-fts/src/wal.rs:31-40`):
    page 0 (`0..4096`) holds the 104-byte `burnHeader` genesis prefix, page 1 (`4096..8192`)
    holds 80-byte HWM slot A (`QSAG.BURN.HWM.V4`), page 2 (`8192..12288`) holds 80-byte HWM
    slot B, and 42-byte burn records start at `HEADER_LEN = 12288`. -/
def burnHwmPageBytes : Nat := 4096
def burnHwmSlotOffsetA : Nat := 4096
def burnHwmSlotOffsetB : Nat := 8192
def burnPagedHeaderLen : Nat := 12288
def burnHwmSlotBytes : Nat := 80

/-- `QSAG.BURN.HWM.V4` slot MAC (`wal.rs:210-222`). -/
def burnHwmSlotMac (key identity keyId genesis : Bytes) (slot : UInt8)
    (generationBe8 tip32 reserved8 : Bytes) : Bytes :=
  burnTag [0x51, 0x53, 0x41, 0x47, 0x2e, 0x42, 0x55, 0x52, 0x4e, 0x2e, 0x48, 0x57, 0x4d, 0x2e, 0x56, 0x34]
    [key, identity, keyId, genesis, [slot], generationBe8, tip32, reserved8]

theorem qsburn05_paged_offsets_match :
    (Qsag.Exec.TwoSlotHwmCrashModel.qsburn05 512).offA = burnHwmSlotOffsetA ∧
    (Qsag.Exec.TwoSlotHwmCrashModel.qsburn05 512).offB = burnHwmSlotOffsetB ∧
    (Qsag.Exec.TwoSlotHwmCrashModel.qsburn05 512).chainOff = burnPagedHeaderLen ∧
    (Qsag.Exec.TwoSlotHwmCrashModel.qsburn05 512).Separated burnHwmSlotBytes :=
  ⟨rfl, rfl, rfl, Qsag.Exec.TwoSlotHwmCrashModel.qsburn05_separated (by decide) ⟨8, by decide⟩⟩

#verify_constructive qsburn05_paged_offsets_match

end Qsag.RustDurability
end
