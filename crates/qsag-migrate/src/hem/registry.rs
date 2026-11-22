//! Durable one-way nullifier registry (the migration "turnstile").
//!
//! A verified migration proof binds a legacy credential to one post-quantum address.
//! This registry makes that binding permanent: once a nullifier or a legacy identifier
//! is recorded, it stays bound to exactly that post-quantum commitment across crashes,
//! restarts and (with an anchor) rollbacks of the storage. The registry does not verify
//! proofs; callers submit `OwnershipStatement::binding()` only after
//! `hem::relations::verify_ownership` accepted the statement's proof.
//!
//! # State machine
//!
//! Per nullifier: `Absent -> Enrolled -> Finalized`, or `Absent -> Finalized` in one
//! step. There is no transition back and no rebinding.
//!
//! * [`NullifierRegistry::register`]: atomic enrol-and-finalize, the single-step
//!   re-registration of the Anchorage turnstile (Ray, Gautam, Ryan 2026, section 4.1).
//! * [`NullifierRegistry::enroll`] then [`NullifierRegistry::finalize`]: the enrolment
//!   and authorization-switch steps of ePrint 2026/352 (sections 7.3 and 7.4). An
//!   enrolment already reserves the nullifier and the legacy identifier; finalization
//!   reopens the same binding and only changes its status.
//! * An identical submission is idempotent. A different binding under a recorded
//!   nullifier is [`RegistryError::NullifierConflict`]; a new nullifier for a recorded
//!   legacy identifier (the same legacy key in another replay domain or epoch) is
//!   [`RegistryError::LegacyConflict`].
//!
//! Where the two papers disagree, the stricter rule is implemented:
//!
//! * Conflicting bindings. In the turnstile the post-quantum key is derived from the
//!   legacy secret, so a second, different key for one record cannot come from a valid
//!   proof. In 2026/352 the key is fresh, competing enrolments are possible and the
//!   "first valid finalized" one wins. Here the first durable enrolment wins: a pending
//!   enrolment cannot be displaced by a later one that finalizes sooner.
//! * Eligibility. The turnstile admits only never-revealed keys; 2026/352 also admits
//!   revealed keys through a dual-signature mode. The mode is recorded and bound
//!   ([`KeyExposure`]); deciding which modes to admit is the caller's policy.
//! * Later key changes. 2026/352 allows a post-quantum rotation policy after migration
//!   and the turnstile leaves re-invocation open. Neither goes through this registry:
//!   a recorded binding is never rewritten.
//! * Identifier. 2026/352 keys the record by an asset identifier, the turnstile by the
//!   on-chain hash commitment. The registry indexes both the proof's nullifier and a
//!   digest of the legacy commitment.
//!
//! # Storage
//!
//! One file, `registry.log`, in a private directory, in 4096-byte pages: page 0 holds
//! `magic || genesis id || genesis MAC`, pages 1 and 2 hold the two high-water-mark
//! slots (`TwoSlotHwm`), fixed-size records follow from page 3. Every record carries a
//! MAC over the storage key, the genesis id, the previous record's MAC and its own
//! ordinal, so the MACs form a running chain rooted in a genesis MAC that covers the
//! file's device and inode. An append syncs the record, then slot A, then slot B, then
//! advances the anchor; only then does the call return.
//!
//! Detected on open, with or without an anchor: a changed byte in any committed record
//! or in the genesis prefix, reordered or substituted records, a record area cut below
//! the high-water mark, a log copied to another inode, and a log written under another
//! key. An interrupted append leaves at most one record of unauthenticated bytes, which
//! is removed; a record that reached the disk whole is kept.
//!
//! Not detected without an anchor or a retained checkpoint: replacing the whole file
//! content, slots included, with an earlier state of the same file; and deleting the
//! log followed by a new [`NullifierRegistry::create`]. Both are whole-file rollback.
//! [`NullifierRegistry::open_anchored`] and [`NullifierRegistry::open_at_least`] refuse
//! them, and also refuse a rolled-back log that was extended past the anchored length,
//! because the chain MAC at the anchored generation must equal the anchored tag.
//!
//! Memory is one index entry per binding (two ordered maps keyed by 32-byte digests);
//! records stay on disk and are re-authenticated when read.

use qsag_accel::ct::{RedactedSecret, ct_eq_bytes, ct_zeroize_bytes};
use qsag_accel::keccak::cshake256_framed_32;
use qsag_addr::QsagAddress;
use qsag_asm::durable::{
    ChainHead, CounterOrder, HWM_PAGE_BYTES, HWM_SLOT_BYTES, TwoSlotHwm, file_dev_ino,
    no_follow_options, sync_parent_dir, write_at_exact,
};
use qsag_core::{ExternalMonotoneAnchor, LedgerCheckpoint};
use std::boxed::Box;
use std::collections::BTreeMap;
use std::fs::{self, File, TryLockError};
use std::io::{self, Read};
use std::path::{Path, PathBuf};
use std::vec;

const MAGIC: &[u8; 8] = b"QSNULRG1";
const LOG_NAME: &str = "registry.log";
const TMP_NAME: &str = "registry.log.new";
const PAGE_LEN: usize = HWM_PAGE_BYTES as usize;
const GENESIS_PREFIX_LEN: usize = 72;
const HWM_FIRST_PAGE: u32 = 1;
const SLOT_A_OFFSET: usize = PAGE_LEN;
const SLOT_B_OFFSET: usize = 2 * PAGE_LEN;
const HEADER_LEN: usize = 3 * PAGE_LEN;
const BODY_LEN: usize = 144;
const RECORD_LEN: usize = BODY_LEN + 32;
/// Records authenticated per read while opening.
const OPEN_BATCH_RECORDS: usize = 512;
const _: () = assert!(GENESIS_PREFIX_LEN <= PAGE_LEN && HWM_SLOT_BYTES <= PAGE_LEN);

const KIND_ENROLL: u8 = 1;
const KIND_FINALIZE: u8 = 2;
const KIND_REGISTER: u8 = 3;

/// Whether the legacy public key was already public when the migration was proved
/// (the `mode` of ePrint 2026/352). Part of the binding.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum KeyExposure {
    /// Only a hash of the key is public (the turnstile's eligible class).
    Hidden = 0,
    /// The key itself is public.
    Revealed = 1,
}

/// One legacy credential bound to one post-quantum address commitment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MigrationBinding {
    /// The statement's nullifier (`hem::relations::OwnershipStatement::nullifier`).
    pub nullifier: [u8; 32],
    pub migration_domain: [u8; 32],
    /// `hem::relations::Credential::identifier` of the legacy credential: one value per
    /// on-chain credential, independent of the replay domain and epoch.
    pub legacy_id: [u8; 32],
    /// [`pq_commitment`] of the target address.
    pub pq_commitment: [u8; 32],
    pub epoch: u64,
    pub exposure: KeyExposure,
}

/// Commitment to every field of the target address (prefix, version, suite, key kind
/// and key commitment).
pub fn pq_commitment(address: &QsagAddress) -> [u8; 32] {
    cshake256_framed_32(
        b"QSAG.MIGRATE.REGISTRY.PQ.V1",
        &[
            address.hrp.as_bytes(),
            &[address.version as u8],
            &(address.suite_tag as u16).to_be_bytes(),
            &[address.kind as u8],
            &address.commitment_256,
        ],
    )
}

impl MigrationBinding {
    /// Registry leaf `H(assetID || H(pk_pq) || suite || epoch)` of ePrint 2026/352
    /// section 7.4, extended by the replay domain and the mode, for callers that also
    /// keep an external Merkle accumulator.
    pub fn leaf(&self) -> [u8; 32] {
        cshake256_framed_32(
            b"QSAG.MIGRATE.REGISTRY.LEAF.V1",
            &[
                &self.legacy_id,
                &self.pq_commitment,
                &self.epoch.to_be_bytes(),
                &self.migration_domain,
                &[self.exposure as u8],
            ],
        )
    }

    fn encode(&self, kind: u8) -> [u8; BODY_LEN] {
        let mut body = [0; BODY_LEN];
        body[0] = kind;
        body[1] = self.exposure as u8;
        body[8..16].copy_from_slice(&self.epoch.to_be_bytes());
        body[16..48].copy_from_slice(&self.nullifier);
        body[48..80].copy_from_slice(&self.migration_domain);
        body[80..112].copy_from_slice(&self.legacy_id);
        body[112..144].copy_from_slice(&self.pq_commitment);
        body
    }

    fn decode(body: &[u8]) -> Option<(u8, Self)> {
        if body.len() != BODY_LEN || body[2..8] != [0; 6] {
            return None;
        }
        let exposure = match body[1] {
            0 => KeyExposure::Hidden,
            1 => KeyExposure::Revealed,
            _ => return None,
        };
        if !matches!(body[0], KIND_ENROLL | KIND_FINALIZE | KIND_REGISTER) {
            return None;
        }
        let field = |at: usize| -> Option<[u8; 32]> { body[at..at + 32].try_into().ok() };
        Some((
            body[0],
            Self {
                nullifier: field(16)?,
                migration_domain: field(48)?,
                legacy_id: field(80)?,
                pq_commitment: field(112)?,
                epoch: u64::from_be_bytes(body[8..16].try_into().ok()?),
                exposure,
            },
        ))
    }
}

/// Where a recorded binding stands.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BindingStatus {
    /// The binding is reserved; legacy authorization has not been switched off yet.
    Enrolled,
    /// The migration is complete: only the post-quantum key authorizes from here on.
    Finalized,
}

/// A binding as read back from the log.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RegisteredBinding {
    pub binding: MigrationBinding,
    pub status: BindingStatus,
    /// Position of the enrolling record in the log.
    pub ordinal: u64,
}

/// Result of an accepted submission. The state it describes is durable.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Receipt {
    pub status: BindingStatus,
    /// False when the log already held this exact binding at this status.
    pub appended: bool,
    /// Log length and chain tip after the call; retain it outside the registry's
    /// storage for [`NullifierRegistry::open_at_least`].
    pub checkpoint: LedgerCheckpoint,
}

#[derive(Debug)]
pub enum RegistryError {
    Io(io::Error),
    /// Another handle holds the registry.
    Locked,
    /// The log does not authenticate, or authenticates and is not a valid history.
    Corrupt(&'static str),
    /// The log is behind the anchor or the retained checkpoint, or diverges from it.
    RolledBack,
    /// The nullifier is already bound to a different record.
    NullifierConflict,
    /// The legacy identifier is already bound under another nullifier.
    LegacyConflict,
    /// `finalize` of a nullifier that was never enrolled.
    NotEnrolled,
    /// An earlier operation on this handle failed part-way; reopen the registry.
    Poisoned,
}

impl core::fmt::Display for RegistryError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Io(e) => write!(f, "nullifier registry I/O: {e}"),
            Self::Locked => f.write_str("nullifier registry is held by another handle"),
            Self::Corrupt(what) => write!(f, "nullifier registry is corrupt: {what}"),
            Self::RolledBack => f.write_str("nullifier registry was rolled back"),
            Self::NullifierConflict => f.write_str("nullifier is bound to a different record"),
            Self::LegacyConflict => f.write_str("legacy identifier is already migrated"),
            Self::NotEnrolled => f.write_str("nullifier is not enrolled"),
            Self::Poisoned => f.write_str("nullifier registry handle failed; reopen it"),
        }
    }
}

impl std::error::Error for RegistryError {}

impl From<io::Error> for RegistryError {
    fn from(e: io::Error) -> Self {
        Self::Io(e)
    }
}

#[derive(Clone, Copy)]
struct IndexEntry {
    ordinal: u64,
    finalized: bool,
}

pub struct NullifierRegistry {
    path: PathBuf,
    file: File,
    identity: [u8; 16],
    mac_key: RedactedSecret<32>,
    genesis: [u8; 32],
    genesis_tag: [u8; 32],
    last_tag: [u8; 32],
    entries: u64,
    by_nullifier: BTreeMap<[u8; 32], IndexEntry>,
    by_legacy: BTreeMap<[u8; 32], u64>,
    failed: bool,
    anchor: Option<Box<dyn ExternalMonotoneAnchor>>,
}

impl core::fmt::Debug for NullifierRegistry {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("NullifierRegistry")
            .field("path", &self.path)
            .field("entries", &self.entries)
            .field("bindings", &self.by_nullifier.len())
            .field("failed", &self.failed)
            .field("anchored", &self.anchor.is_some())
            .finish()
    }
}

fn guard_key(mut raw: [u8; 32]) -> RedactedSecret<32> {
    let guarded = RedactedSecret::new(raw);
    ct_zeroize_bytes(&mut raw);
    guarded
}

fn check_private_regular(meta: &fs::Metadata) -> Result<(), RegistryError> {
    if !meta.is_file() {
        return Err(RegistryError::Corrupt("log is not a regular file"));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        if meta.permissions().mode() & 0o077 != 0 {
            return Err(RegistryError::Io(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "nullifier registry log must have private (0600) permissions",
            )));
        }
    }
    Ok(())
}

fn check_directory(dir: &Path) -> Result<(), RegistryError> {
    let meta = fs::symlink_metadata(dir)?;
    if !meta.is_dir() {
        return Err(RegistryError::Corrupt("registry path is not a directory"));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        if meta.permissions().mode() & 0o022 != 0 {
            return Err(RegistryError::Io(io::Error::new(
                io::ErrorKind::PermissionDenied,
                "nullifier registry directory must not be group or world writable",
            )));
        }
    }
    Ok(())
}

fn lock_exclusive(file: &File) -> Result<(), RegistryError> {
    match file.try_lock() {
        Ok(()) => Ok(()),
        Err(TryLockError::WouldBlock) => Err(RegistryError::Locked),
        Err(TryLockError::Error(e)) => Err(RegistryError::Io(e)),
    }
}

/// `dev_be64 || ino_be64` of the held descriptor, bound into the genesis and slot MACs.
fn descriptor_identity(file: &File) -> Result<[u8; 16], RegistryError> {
    let meta = file.metadata()?;
    check_private_regular(&meta)?;
    let (dev, ino) =
        file_dev_ino(&meta).ok_or(RegistryError::Corrupt("no file identity on this target"))?;
    let mut identity = [0; 16];
    identity[..8].copy_from_slice(&dev.to_be_bytes());
    identity[8..].copy_from_slice(&ino.to_be_bytes());
    Ok(identity)
}

fn read_at(file: &File, offset: u64, buf: &mut [u8]) -> io::Result<()> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::FileExt;
        file.read_exact_at(buf, offset)
    }
    #[cfg(not(unix))]
    {
        let _ = (file, offset, buf);
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "positional reads are unavailable on this target",
        ))
    }
}

fn record_offset(ordinal: u64) -> u64 {
    HEADER_LEN as u64 + RECORD_LEN as u64 * ordinal
}

impl NullifierRegistry {
    /// Provision an empty registry in `dir` (created with mode `0700` if absent).
    /// Refuses a directory that already holds a log. `mac_key` authenticates the log
    /// and must be kept where the log's writer cannot be impersonated.
    pub fn create(dir: impl AsRef<Path>, mac_key: [u8; 32]) -> Result<Self, RegistryError> {
        Self::provision(dir.as_ref(), guard_key(mac_key))
    }

    /// Reopen an existing registry. A missing log is an error, never a fresh registry.
    pub fn open(dir: impl AsRef<Path>, mac_key: [u8; 32]) -> Result<Self, RegistryError> {
        Self::load(dir.as_ref(), guard_key(mac_key), None)
    }

    /// Reopen, refusing a log that is shorter than `minimum` or whose chain at
    /// `minimum.generation` is not `minimum.tag`.
    pub fn open_at_least(
        dir: impl AsRef<Path>,
        mac_key: [u8; 32],
        minimum: LedgerCheckpoint,
    ) -> Result<Self, RegistryError> {
        Self::load(dir.as_ref(), guard_key(mac_key), Some(minimum))
    }

    /// [`Self::create`] under an anchor that has never held a checkpoint. Every later
    /// append advances the anchor before it returns.
    pub fn create_anchored(
        dir: impl AsRef<Path>,
        mac_key: [u8; 32],
        anchor: Box<dyn ExternalMonotoneAnchor>,
    ) -> Result<Self, RegistryError> {
        let mac_key = guard_key(mac_key);
        if anchor.load()?.is_some() {
            return Err(RegistryError::RolledBack);
        }
        let mut registry = Self::provision(dir.as_ref(), mac_key)?;
        anchor.advance(registry.checkpoint())?;
        registry.anchor = Some(anchor);
        Ok(registry)
    }

    /// [`Self::open_at_least`] with the anchor's checkpoint as the minimum. An anchor
    /// that holds nothing is refused.
    pub fn open_anchored(
        dir: impl AsRef<Path>,
        mac_key: [u8; 32],
        anchor: Box<dyn ExternalMonotoneAnchor>,
    ) -> Result<Self, RegistryError> {
        let mac_key = guard_key(mac_key);
        let minimum = anchor.load()?.ok_or(RegistryError::RolledBack)?;
        let mut registry = Self::load(dir.as_ref(), mac_key, Some(minimum))?;
        anchor.advance(registry.checkpoint())?;
        registry.anchor = Some(anchor);
        Ok(registry)
    }

    /// Number of log records and the chain tip.
    pub fn checkpoint(&self) -> LedgerCheckpoint {
        LedgerCheckpoint {
            generation: self.entries,
            tag: self.last_tag,
        }
    }

    /// Number of recorded bindings, enrolled or finalized.
    pub fn bindings(&self) -> usize {
        self.by_nullifier.len()
    }

    /// Record `binding` as migrated in one step. Durable when it returns `Ok`.
    /// An identical finalized binding is accepted without writing; an identical
    /// pending enrolment is finalized.
    pub fn register(&mut self, binding: &MigrationBinding) -> Result<Receipt, RegistryError> {
        self.submit(binding, true, false)
    }

    /// Reserve `binding` without switching authorization. Idempotent for an identical
    /// binding in either status.
    pub fn enroll(&mut self, binding: &MigrationBinding) -> Result<Receipt, RegistryError> {
        self.submit(binding, false, false)
    }

    /// Complete an enrolment. `binding` must equal the enrolled one field for field.
    pub fn finalize(&mut self, binding: &MigrationBinding) -> Result<Receipt, RegistryError> {
        self.submit(binding, true, true)
    }

    /// The binding recorded under `nullifier`, re-authenticated from the log.
    pub fn lookup(&self, nullifier: &[u8; 32]) -> Result<Option<RegisteredBinding>, RegistryError> {
        self.usable()?;
        let Some(entry) = self.by_nullifier.get(nullifier) else {
            return Ok(None);
        };
        let found = self.read_binding(*entry)?;
        if found.binding.nullifier != *nullifier {
            return Err(RegistryError::Corrupt("index does not match the log"));
        }
        Ok(Some(found))
    }

    /// The binding recorded for a legacy identifier, under whichever nullifier.
    pub fn lookup_legacy(
        &self,
        legacy_id: &[u8; 32],
    ) -> Result<Option<RegisteredBinding>, RegistryError> {
        self.usable()?;
        let Some(&ordinal) = self.by_legacy.get(legacy_id) else {
            return Ok(None);
        };
        let (_, binding) = self.read_record(ordinal)?;
        let entry = self
            .by_nullifier
            .get(&binding.nullifier)
            .filter(|entry| entry.ordinal == ordinal && binding.legacy_id == *legacy_id)
            .ok_or(RegistryError::Corrupt("index does not match the log"))?;
        self.read_binding(*entry).map(Some)
    }

    fn usable(&self) -> Result<(), RegistryError> {
        if self.failed {
            Err(RegistryError::Poisoned)
        } else {
            Ok(())
        }
    }

    fn submit(
        &mut self,
        binding: &MigrationBinding,
        finalize: bool,
        must_exist: bool,
    ) -> Result<Receipt, RegistryError> {
        self.usable()?;
        if let Some(entry) = self.by_nullifier.get(&binding.nullifier).copied() {
            if self.read_binding(entry)?.binding != *binding {
                return Err(RegistryError::NullifierConflict);
            }
            let appended = finalize && !entry.finalized;
            if appended {
                self.append(KIND_FINALIZE, binding)?;
            }
            return Ok(self.receipt(entry.finalized || finalize, appended));
        }
        if must_exist {
            return Err(RegistryError::NotEnrolled);
        }
        if self.by_legacy.contains_key(&binding.legacy_id) {
            return Err(RegistryError::LegacyConflict);
        }
        self.append(if finalize { KIND_REGISTER } else { KIND_ENROLL }, binding)?;
        Ok(self.receipt(finalize, true))
    }

    fn receipt(&self, finalized: bool, appended: bool) -> Receipt {
        Receipt {
            status: if finalized {
                BindingStatus::Finalized
            } else {
                BindingStatus::Enrolled
            },
            appended,
            checkpoint: self.checkpoint(),
        }
    }

    fn read_binding(&self, entry: IndexEntry) -> Result<RegisteredBinding, RegistryError> {
        let (kind, binding) = self.read_record(entry.ordinal)?;
        if kind == KIND_FINALIZE {
            return Err(RegistryError::Corrupt("index does not match the log"));
        }
        Ok(RegisteredBinding {
            binding,
            status: if entry.finalized {
                BindingStatus::Finalized
            } else {
                BindingStatus::Enrolled
            },
            ordinal: entry.ordinal,
        })
    }

    /// Read record `ordinal` and check its MAC against the tag stored before it.
    fn read_record(&self, ordinal: u64) -> Result<(u8, MigrationBinding), RegistryError> {
        if ordinal >= self.entries {
            return Err(RegistryError::Corrupt("index does not match the log"));
        }
        let mut raw = [0u8; 32 + RECORD_LEN];
        if ordinal == 0 {
            raw[..32].copy_from_slice(&self.genesis_tag);
            read_at(&self.file, record_offset(0), &mut raw[32..])?;
        } else {
            read_at(&self.file, record_offset(ordinal) - 32, &mut raw)?;
        }
        let (previous, record) = raw.split_at(32);
        let (body, tag) = record.split_at(BODY_LEN);
        if !ct_eq_bytes(&self.record_tag(previous, ordinal, body), tag) {
            return Err(RegistryError::Corrupt("record changed after open"));
        }
        MigrationBinding::decode(body).ok_or(RegistryError::Corrupt("malformed record"))
    }

    fn record_tag(&self, previous: &[u8], ordinal: u64, body: &[u8]) -> [u8; 32] {
        cshake256_framed_32(
            b"QSAG.MIGRATE.REGISTRY.RECORD.V1",
            &[
                self.mac_key.expose(),
                &self.genesis,
                previous,
                &ordinal.to_be_bytes(),
                body,
            ],
        )
    }

    fn genesis_mac(&self, prefix: &[u8]) -> [u8; 32] {
        cshake256_framed_32(
            b"QSAG.MIGRATE.REGISTRY.GENESIS.V1",
            &[self.mac_key.expose(), &self.identity, prefix],
        )
    }

    fn with_hwm<T>(&self, f: impl FnOnce(&TwoSlotHwm<'_>, &File) -> T) -> T {
        let mac = |slot: u8, generation: &[u8; 8], tip: &[u8; 32], reserved: &[u8; 8]| {
            cshake256_framed_32(
                b"QSAG.MIGRATE.REGISTRY.HWM.V1",
                &[
                    self.mac_key.expose(),
                    &self.identity,
                    &self.genesis,
                    &[slot],
                    generation,
                    tip,
                    reserved,
                ],
            )
        };
        f(
            &TwoSlotHwm::paged(HWM_FIRST_PAGE, CounterOrder::Big, &mac),
            &self.file,
        )
    }

    /// The path still names the locked inode.
    fn check_path_identity(&self) -> Result<fs::Metadata, RegistryError> {
        let named = fs::symlink_metadata(&self.path)?;
        check_private_regular(&named)?;
        let held = self.file.metadata()?;
        if file_dev_ino(&named) != file_dev_ino(&held)
            || descriptor_identity(&self.file)? != self.identity
        {
            return Err(RegistryError::Corrupt("log file was replaced"));
        }
        Ok(named)
    }

    fn check_identity(&self) -> Result<(), RegistryError> {
        if self.check_path_identity()?.len() != record_offset(self.entries) {
            return Err(RegistryError::Corrupt("log length changed"));
        }
        Ok(())
    }

    /// Apply one authenticated record to the index, refusing histories the state
    /// machine cannot produce.
    fn admit(
        &mut self,
        kind: u8,
        binding: &MigrationBinding,
        ordinal: u64,
    ) -> Result<(), RegistryError> {
        if kind == KIND_FINALIZE {
            let entry = self
                .by_nullifier
                .get(&binding.nullifier)
                .copied()
                .filter(|entry| !entry.finalized)
                .ok_or(RegistryError::Corrupt("finalization without enrolment"))?;
            if self.read_record(entry.ordinal)?.1 != *binding {
                return Err(RegistryError::Corrupt("finalization of another binding"));
            }
            self.by_nullifier.insert(
                binding.nullifier,
                IndexEntry {
                    ordinal: entry.ordinal,
                    finalized: true,
                },
            );
            return Ok(());
        }
        if self.by_nullifier.contains_key(&binding.nullifier)
            || self.by_legacy.contains_key(&binding.legacy_id)
        {
            return Err(RegistryError::Corrupt("log binds one credential twice"));
        }
        self.by_nullifier.insert(
            binding.nullifier,
            IndexEntry {
                ordinal,
                finalized: kind == KIND_REGISTER,
            },
        );
        self.by_legacy.insert(binding.legacy_id, ordinal);
        Ok(())
    }

    fn append(&mut self, kind: u8, binding: &MigrationBinding) -> Result<(), RegistryError> {
        // Any failure from here leaves the handle unusable: what reached the disk is
        // decided by the next open.
        self.failed = true;
        self.check_identity()?;
        let ordinal = self.entries;
        let next = ordinal
            .checked_add(1)
            .ok_or(RegistryError::Corrupt("log is full"))?;
        let mut record = [0u8; RECORD_LEN];
        record[..BODY_LEN].copy_from_slice(&binding.encode(kind));
        let tag = self.record_tag(&self.last_tag, ordinal, &record[..BODY_LEN]);
        record[BODY_LEN..].copy_from_slice(&tag);
        write_at_exact(&self.file, record_offset(ordinal), &record)?;
        self.file.sync_all()?;
        self.with_hwm(|hwm, file| hwm.commit(file, next, &tag))?;
        self.entries = next;
        self.last_tag = tag;
        self.admit(kind, binding, ordinal)?;
        self.check_identity()?;
        if let Some(anchor) = &self.anchor {
            anchor.advance(self.checkpoint())?;
        }
        self.failed = false;
        Ok(())
    }

    fn empty(path: PathBuf, file: File, identity: [u8; 16], mac_key: RedactedSecret<32>) -> Self {
        Self {
            path,
            file,
            identity,
            mac_key,
            genesis: [0; 32],
            genesis_tag: [0; 32],
            last_tag: [0; 32],
            entries: 0,
            by_nullifier: BTreeMap::new(),
            by_legacy: BTreeMap::new(),
            failed: false,
            anchor: None,
        }
    }

    fn provision(dir: &Path, mac_key: RedactedSecret<32>) -> Result<Self, RegistryError> {
        match fs::symlink_metadata(dir) {
            Ok(_) => {}
            Err(e) if e.kind() == io::ErrorKind::NotFound => {
                let mut builder = fs::DirBuilder::new();
                #[cfg(unix)]
                {
                    use std::os::unix::fs::DirBuilderExt;
                    builder.mode(0o700);
                }
                builder.create(dir)?;
                sync_parent_dir(dir)?;
            }
            Err(e) => return Err(e.into()),
        }
        check_directory(dir)?;
        let path = dir.join(LOG_NAME);
        let staging = dir.join(TMP_NAME);
        match fs::symlink_metadata(&path) {
            Ok(_) => {
                return Err(RegistryError::Io(io::Error::new(
                    io::ErrorKind::AlreadyExists,
                    "nullifier registry already provisioned",
                )));
            }
            Err(e) if e.kind() == io::ErrorKind::NotFound => {}
            Err(e) => return Err(e.into()),
        }
        // A staging file left by a provisioning that died before its log was linked
        // holds nothing; one that is locked belongs to a live provisioning.
        match no_follow_options()?.read(true).write(true).open(&staging) {
            Ok(stale) => {
                lock_exclusive(&stale)?;
                fs::remove_file(&staging)?;
            }
            Err(e) if e.kind() == io::ErrorKind::NotFound => {}
            Err(e) => return Err(e.into()),
        }
        let file = no_follow_options()?
            .read(true)
            .write(true)
            .create_new(true)
            .open(&staging)?;
        lock_exclusive(&file)?;
        let identity = descriptor_identity(&file)?;
        let mut registry = Self::empty(path, file, identity, mac_key);
        File::open("/dev/urandom")?.read_exact(&mut registry.genesis)?;
        let mut header = vec![0u8; HEADER_LEN];
        header[..8].copy_from_slice(MAGIC);
        header[8..40].copy_from_slice(&registry.genesis);
        registry.genesis_tag = registry.genesis_mac(&header[..40]);
        registry.last_tag = registry.genesis_tag;
        header[40..GENESIS_PREFIX_LEN].copy_from_slice(&registry.genesis_tag);
        let (slot_a, slot_b) = registry.with_hwm(|hwm, _| {
            (
                hwm.encode(0, 0, &registry.genesis_tag),
                hwm.encode(1, 0, &registry.genesis_tag),
            )
        });
        header[SLOT_A_OFFSET..SLOT_A_OFFSET + HWM_SLOT_BYTES].copy_from_slice(&slot_a);
        header[SLOT_B_OFFSET..SLOT_B_OFFSET + HWM_SLOT_BYTES].copy_from_slice(&slot_b);
        write_at_exact(&registry.file, 0, &header)?;
        registry.file.sync_all()?;
        // Publish the complete genesis under the log name without replacing anything:
        // a link fails if the name exists, and the inode (hence the lock and the
        // identity in the MACs) is the one already held.
        fs::hard_link(&staging, &registry.path)?;
        fs::remove_file(&staging)?;
        sync_parent_dir(&registry.path)?;
        registry.check_identity()?;
        Ok(registry)
    }

    fn load(
        dir: &Path,
        mac_key: RedactedSecret<32>,
        minimum: Option<LedgerCheckpoint>,
    ) -> Result<Self, RegistryError> {
        check_directory(dir)?;
        let path = dir.join(LOG_NAME);
        check_private_regular(&fs::symlink_metadata(&path)?)?;
        let file = no_follow_options()?.read(true).write(true).open(&path)?;
        let identity = descriptor_identity(&file)?;
        lock_exclusive(&file)?;
        let mut registry = Self::empty(path, file, identity, mac_key);
        registry.check_path_identity()?;
        let file_len = registry.file.metadata()?.len();
        if file_len < HEADER_LEN as u64 {
            return Err(RegistryError::Corrupt("log is shorter than its header"));
        }
        let mut header = vec![0u8; HEADER_LEN];
        read_at(&registry.file, 0, &mut header)?;
        if &header[..8] != MAGIC {
            return Err(RegistryError::Corrupt("not a nullifier registry log"));
        }
        registry.genesis.copy_from_slice(&header[8..40]);
        registry.genesis_tag = registry.genesis_mac(&header[..40]);
        if !ct_eq_bytes(&registry.genesis_tag, &header[40..GENESIS_PREFIX_LEN]) {
            return Err(RegistryError::Corrupt("genesis does not authenticate"));
        }
        registry.last_tag = registry.genesis_tag;

        // Authenticate the chain in bounded batches, building only the index. Stop at
        // the first record whose MAC fails: everything from there is the tail.
        let body_len = file_len - HEADER_LEN as u64;
        let whole = body_len / RECORD_LEN as u64;
        let mut tail_len = body_len % RECORD_LEN as u64;
        let mut previous_tag = registry.genesis_tag;
        let mut tag_at_minimum =
            (minimum.map(|m| m.generation) == Some(0)).then_some(registry.genesis_tag);
        let mut batch = vec![0u8; OPEN_BATCH_RECORDS * RECORD_LEN];
        'chain: while registry.entries < whole {
            let count = (whole - registry.entries).min(OPEN_BATCH_RECORDS as u64) as usize;
            let chunk = &mut batch[..count * RECORD_LEN];
            read_at(&registry.file, record_offset(registry.entries), chunk)?;
            for record in chunk.chunks_exact(RECORD_LEN) {
                let (body, tag) = record.split_at(BODY_LEN);
                let ordinal = registry.entries;
                let expected = registry.record_tag(&registry.last_tag, ordinal, body);
                if !ct_eq_bytes(&expected, tag) {
                    tail_len = body_len - RECORD_LEN as u64 * ordinal;
                    break 'chain;
                }
                let (kind, binding) = MigrationBinding::decode(body)
                    .ok_or(RegistryError::Corrupt("malformed record"))?;
                previous_tag = registry.last_tag;
                registry.last_tag = expected;
                registry.entries = ordinal + 1;
                registry.admit(kind, &binding, ordinal)?;
                if minimum.map(|m| m.generation) == Some(registry.entries) {
                    tag_at_minimum = Some(expected);
                }
            }
        }
        drop(batch);
        // An interrupted append leaves at most one record of unauthenticated bytes.
        if tail_len > RECORD_LEN as u64 {
            return Err(RegistryError::Corrupt("record does not authenticate"));
        }
        if let Some(minimum) = minimum {
            match tag_at_minimum {
                Some(tag) if ct_eq_bytes(&tag, &minimum.tag) => {}
                _ => return Err(RegistryError::RolledBack),
            }
        }
        registry.check_path_identity()?;
        let committed = registry.entries;
        let slot_a = &header[SLOT_A_OFFSET..SLOT_A_OFFSET + HWM_SLOT_BYTES];
        let slot_b = &header[SLOT_B_OFFSET..SLOT_B_OFFSET + HWM_SLOT_BYTES];
        // Refuses a chain cut below the mark; heals a record synced before slot A,
        // slot A synced before slot B, and one slot torn mid-write.
        registry
            .with_hwm(|hwm, file| {
                hwm.recover(
                    file,
                    slot_a,
                    slot_b,
                    &ChainHead {
                        len: committed,
                        tip: &registry.last_tag,
                        previous_tip: &previous_tag,
                    },
                )
            })
            .map_err(|_| RegistryError::Corrupt("log does not match its high-water mark"))?;
        if tail_len != 0 {
            registry.file.set_len(record_offset(committed))?;
            registry.file.sync_all()?;
            registry.with_hwm(|hwm, file| hwm.commit(file, committed, &registry.last_tag))?;
        }
        registry.check_identity()?;
        Ok(registry)
    }
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use crate::hem::relations::{Credential, credential_identifier};
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::sync::{Arc, Mutex};
    use std::vec::Vec;

    const KEY: [u8; 32] = [0x5a; 32];

    struct TempDir(PathBuf);

    impl TempDir {
        fn new(name: &str) -> Self {
            static NEXT: AtomicU64 = AtomicU64::new(0);
            let nanos = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos();
            let dir = std::env::temp_dir().join(std::format!(
                "dregg-sig-nullifier-registry-{name}-{}-{nanos}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed),
            ));
            Self(dir)
        }
        fn log(&self) -> PathBuf {
            self.0.join(LOG_NAME)
        }
        /// Create the directory the way an operator must: not group or world writable,
        /// whatever the umask.
        fn make(&self) {
            use std::os::unix::fs::DirBuilderExt;
            fs::DirBuilder::new().mode(0o700).create(&self.0).unwrap();
        }
    }

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    #[derive(Clone, Default)]
    struct MemoryAnchor(Arc<Mutex<Option<LedgerCheckpoint>>>);

    impl ExternalMonotoneAnchor for MemoryAnchor {
        fn load(&self) -> io::Result<Option<LedgerCheckpoint>> {
            Ok(*self.0.lock().unwrap())
        }
        fn advance(&self, checkpoint: LedgerCheckpoint) -> io::Result<()> {
            let mut cell = self.0.lock().unwrap();
            if let Some(old) = *cell
                && (old.generation > checkpoint.generation
                    || (old.generation == checkpoint.generation && old.tag != checkpoint.tag))
            {
                return Err(io::Error::other("anchor rejects rollback"));
            }
            *cell = Some(checkpoint);
            Ok(())
        }
    }

    fn binding(id: u8) -> MigrationBinding {
        MigrationBinding {
            nullifier: [id; 32],
            migration_domain: [0xd0; 32],
            legacy_id: [id ^ 0x80; 32],
            pq_commitment: [id.wrapping_mul(3).wrapping_add(1); 32],
            epoch: 7,
            exposure: KeyExposure::Hidden,
        }
    }

    /// Replace the log's content in place, keeping its inode.
    fn overwrite(path: &Path, bytes: &[u8]) {
        let file = fs::OpenOptions::new().write(true).open(path).unwrap();
        write_at_exact(&file, 0, bytes).unwrap();
        file.set_len(bytes.len() as u64).unwrap();
    }

    fn populated(dir: &TempDir, count: u8) -> Vec<u8> {
        let mut registry = NullifierRegistry::create(&dir.0, KEY).unwrap();
        for id in 1..=count {
            assert!(registry.register(&binding(id)).unwrap().appended);
        }
        drop(registry);
        fs::read(dir.log()).unwrap()
    }

    #[test]
    fn register_and_lookup_survive_reopen() {
        let dir = TempDir::new("roundtrip");
        let mut registry = NullifierRegistry::create(&dir.0, KEY).unwrap();
        for id in 1..=3 {
            let receipt = registry.register(&binding(id)).unwrap();
            assert_eq!(receipt.status, BindingStatus::Finalized);
            assert_eq!(receipt.checkpoint.generation, u64::from(id));
        }
        registry.enroll(&binding(4)).unwrap();
        let checkpoint = registry.checkpoint();
        drop(registry);

        let registry = NullifierRegistry::open(&dir.0, KEY).unwrap();
        assert_eq!(registry.checkpoint(), checkpoint);
        assert_eq!(registry.bindings(), 4);
        for id in 1..=4u8 {
            let found = registry.lookup(&[id; 32]).unwrap().unwrap();
            assert_eq!(found.binding, binding(id));
            assert_eq!(found.ordinal, u64::from(id) - 1);
            assert_eq!(
                found.status,
                if id == 4 {
                    BindingStatus::Enrolled
                } else {
                    BindingStatus::Finalized
                }
            );
            assert_eq!(
                registry.lookup_legacy(&binding(id).legacy_id).unwrap(),
                Some(found)
            );
        }
        assert_eq!(registry.lookup(&[9; 32]).unwrap(), None);
        assert_eq!(registry.lookup_legacy(&[9; 32]).unwrap(), None);

        // A record changed under an open handle is refused when it is read.
        let good = fs::read(dir.log()).unwrap();
        let mut bad = good.clone();
        bad[HEADER_LEN + RECORD_LEN + 20] ^= 1;
        overwrite(&dir.log(), &bad);
        assert!(matches!(
            registry.lookup(&[2; 32]),
            Err(RegistryError::Corrupt(_))
        ));
        assert_eq!(
            registry.lookup(&[1; 32]).unwrap().unwrap().binding,
            binding(1)
        );
        overwrite(&dir.log(), &good);
        drop(registry);
        assert!(matches!(
            NullifierRegistry::open(&dir.0, [0x5b; 32]),
            Err(RegistryError::Corrupt(_))
        ));
        assert!(matches!(
            NullifierRegistry::create(&dir.0, KEY),
            Err(RegistryError::Io(e)) if e.kind() == io::ErrorKind::AlreadyExists
        ));
    }

    /// One on-chain credential has one identifier whichever statement migrates it, and
    /// the second statement kind to arrive is refused by that identifier.
    #[test]
    fn a_credential_migrates_once_across_statement_kinds() {
        use crate::hem::relations::{
            Bip32Root, Credential, KeySource, Lock, OwnershipStatement, OwnershipWitness, PathSpec,
            bip32_derive,
        };
        let seed = [0x42u8; 32];
        let path = vec![0x8000_002c, 3];
        let leaf = bip32_derive(&seed, &path).unwrap();
        let derive = |lock, source, witness: &OwnershipWitness| {
            OwnershipStatement::derive(lock, source, witness, [9; 32], [0xd0; 32], 7).unwrap()
        };
        let bip32 = || KeySource::Bip32 {
            root: Bip32Root::Seed,
            path: PathSpec::Public(path.clone()),
        };
        let key = OwnershipWitness::secp256k1_key(&leaf.private_key);
        let hidden = derive(Lock::Ethereum, KeySource::Secp256k1Key, &key);
        let seeded = derive(Lock::Ethereum, bip32(), &OwnershipWitness::seed(&seed));
        let other_lock = derive(Lock::P2pkh, bip32(), &OwnershipWitness::seed(&seed));

        // Same address, same identifier; the nullifiers differ by design.
        assert_eq!(hidden.credential, seeded.credential);
        assert_eq!(hidden.binding().legacy_id, seeded.binding().legacy_id);
        assert_ne!(hidden.nullifier, seeded.nullifier);
        assert_eq!(hidden.binding().exposure, KeyExposure::Hidden);
        assert_eq!(seeded.binding().exposure, KeyExposure::Revealed);
        // Another credential of the same key is another identifier.
        assert_ne!(other_lock.binding().legacy_id, seeded.binding().legacy_id);

        // The identifiers of the four older kinds are unchanged, the new one is its own.
        let Credential::EthereumAddress(address) = seeded.credential else {
            panic!("an Ethereum lock yields an address");
        };
        assert_eq!(
            credential_identifier(3, &address),
            seeded.credential.identifier()
        );
        assert_eq!(
            credential_identifier(1, &address),
            Credential::BitcoinKeyHash(address).identifier()
        );
        assert_eq!(
            credential_identifier(2, &[5; 32]),
            Credential::BitcoinTaproot([5; 32]).identifier()
        );
        assert_eq!(
            credential_identifier(4, &[5; 32]),
            Credential::Ed25519Key([5; 32]).identifier()
        );
        let ids = [
            Credential::BitcoinKeyHash(address).identifier(),
            Credential::EthereumAddress(address).identifier(),
            Credential::BitcoinScriptHash(address).identifier(),
        ];
        assert!(ids[0] != ids[1] && ids[1] != ids[2] && ids[0] != ids[2]);

        for (first, second) in [(&seeded, &hidden), (&hidden, &seeded)] {
            let dir = TempDir::new("kinds");
            let mut registry = NullifierRegistry::create(&dir.0, KEY).unwrap();
            registry.register(&first.binding()).unwrap();
            assert!(matches!(
                registry.register(&second.binding()),
                Err(RegistryError::LegacyConflict)
            ));
            // The key's other credential is free to migrate.
            registry.register(&other_lock.binding()).unwrap();
            assert_eq!(registry.bindings(), 2);
        }
    }

    #[test]
    fn second_binding_is_refused() {
        let dir = TempDir::new("double");
        let mut registry = NullifierRegistry::create(&dir.0, KEY).unwrap();
        registry.register(&binding(1)).unwrap();
        let before = registry.checkpoint();

        let mut other_target = binding(1);
        other_target.pq_commitment = [0xee; 32];
        let mut other_nullifier = binding(1);
        other_nullifier.nullifier = [0x77; 32];
        other_nullifier.migration_domain = [0xd1; 32];
        let mut other_epoch = binding(1);
        other_epoch.epoch += 1;
        let mut other_mode = binding(1);
        other_mode.exposure = KeyExposure::Revealed;

        for reopen in [false, true] {
            if reopen {
                drop(registry);
                registry = NullifierRegistry::open(&dir.0, KEY).unwrap();
            }
            for changed in [&other_target, &other_epoch, &other_mode] {
                assert!(matches!(
                    registry.register(changed),
                    Err(RegistryError::NullifierConflict)
                ));
                assert!(matches!(
                    registry.enroll(changed),
                    Err(RegistryError::NullifierConflict)
                ));
            }
            assert!(matches!(
                registry.register(&other_nullifier),
                Err(RegistryError::LegacyConflict)
            ));
            assert!(matches!(
                registry.enroll(&other_nullifier),
                Err(RegistryError::LegacyConflict)
            ));
            assert_eq!(registry.checkpoint(), before);
            assert_eq!(
                registry.lookup(&[1; 32]).unwrap().unwrap().binding,
                binding(1)
            );
            assert_eq!(registry.lookup(&[0x77; 32]).unwrap(), None);
        }
    }

    #[test]
    fn identical_replay_is_idempotent() {
        let dir = TempDir::new("replay");
        let mut registry = NullifierRegistry::create(&dir.0, KEY).unwrap();
        let first = registry.register(&binding(1)).unwrap();
        assert!(first.appended);
        let len = fs::metadata(dir.log()).unwrap().len();
        for reopen in [false, true] {
            if reopen {
                drop(registry);
                registry = NullifierRegistry::open(&dir.0, KEY).unwrap();
            }
            let again = registry.register(&binding(1)).unwrap();
            assert_eq!(
                again,
                Receipt {
                    appended: false,
                    ..first
                }
            );
            assert_eq!(registry.enroll(&binding(1)).unwrap(), again);
            assert_eq!(registry.finalize(&binding(1)).unwrap(), again);
            assert_eq!(fs::metadata(dir.log()).unwrap().len(), len);
        }
    }

    #[test]
    fn enrolment_then_finalization() {
        let dir = TempDir::new("phases");
        let mut registry = NullifierRegistry::create(&dir.0, KEY).unwrap();
        assert!(matches!(
            registry.finalize(&binding(1)),
            Err(RegistryError::NotEnrolled)
        ));
        let enrolled = registry.enroll(&binding(1)).unwrap();
        assert_eq!(
            (enrolled.status, enrolled.appended),
            (BindingStatus::Enrolled, true)
        );
        assert!(!registry.enroll(&binding(1)).unwrap().appended);

        // A pending enrolment already excludes every other binding.
        let mut other_target = binding(1);
        other_target.pq_commitment = [0xee; 32];
        assert!(matches!(
            registry.finalize(&other_target),
            Err(RegistryError::NullifierConflict)
        ));
        let mut other_nullifier = binding(1);
        other_nullifier.nullifier = [0x77; 32];
        assert!(matches!(
            registry.register(&other_nullifier),
            Err(RegistryError::LegacyConflict)
        ));

        registry.enroll(&binding(2)).unwrap();
        drop(registry);
        let mut registry = NullifierRegistry::open(&dir.0, KEY).unwrap();
        assert_eq!(
            registry.lookup(&[1; 32]).unwrap().unwrap().status,
            BindingStatus::Enrolled
        );
        let finalized = registry.finalize(&binding(1)).unwrap();
        assert_eq!(
            (finalized.status, finalized.appended),
            (BindingStatus::Finalized, true)
        );
        // `register` over an identical pending enrolment completes it.
        let completed = registry.register(&binding(2)).unwrap();
        assert_eq!(
            (completed.status, completed.appended),
            (BindingStatus::Finalized, true)
        );
        assert!(!registry.finalize(&binding(1)).unwrap().appended);
        assert_eq!(registry.checkpoint().generation, 4);
        drop(registry);

        let registry = NullifierRegistry::open(&dir.0, KEY).unwrap();
        assert_eq!(registry.bindings(), 2);
        for id in 1..=2u8 {
            let found = registry.lookup(&[id; 32]).unwrap().unwrap();
            assert_eq!(found.status, BindingStatus::Finalized);
            assert_eq!(found.ordinal, u64::from(id) - 1);
            assert_eq!(found.binding, binding(id));
        }
    }

    #[test]
    fn torn_tail_of_every_length_recovers_previous_state() {
        let dir = TempDir::new("torn");
        let committed = populated(&dir, 2);
        let mut registry = NullifierRegistry::open(&dir.0, KEY).unwrap();
        let before = registry.checkpoint();
        registry.register(&binding(3)).unwrap();
        let after = registry.checkpoint();
        drop(registry);
        let full = fs::read(dir.log()).unwrap();
        assert_eq!(full.len(), committed.len() + RECORD_LEN);
        let record = &full[committed.len()..];

        // The append died after `cut` bytes of the record, before either slot moved.
        for cut in 1..RECORD_LEN {
            for zeroed in [false, true] {
                let mut torn = committed.clone();
                torn.extend_from_slice(&record[..cut]);
                if zeroed {
                    let at = committed.len();
                    torn[at..].fill(0);
                }
                overwrite(&dir.log(), &torn);
                let mut registry = NullifierRegistry::open(&dir.0, KEY)
                    .unwrap_or_else(|e| panic!("cut {cut}: {e}"));
                assert_eq!(registry.checkpoint(), before, "cut {cut}");
                assert_eq!(registry.bindings(), 2);
                assert_eq!(registry.lookup(&[3; 32]).unwrap(), None);
                assert_eq!(
                    registry.lookup(&[2; 32]).unwrap().unwrap().binding,
                    binding(2)
                );
                assert_eq!(
                    fs::metadata(dir.log()).unwrap().len(),
                    committed.len() as u64
                );
                if cut % 29 == 1 && !zeroed {
                    registry.register(&binding(3)).unwrap();
                    assert_eq!(registry.checkpoint(), after);
                }
            }
        }

        // The whole record reached the disk and the slots did not: it stays.
        let mut unmarked = committed.clone();
        unmarked.extend_from_slice(record);
        overwrite(&dir.log(), &unmarked);
        let registry = NullifierRegistry::open(&dir.0, KEY).unwrap();
        assert_eq!(registry.checkpoint(), after);
        assert_eq!(
            registry.lookup(&[3; 32]).unwrap().unwrap().binding,
            binding(3)
        );
        drop(registry);
        assert_eq!(fs::read(dir.log()).unwrap(), full);

        // A whole record of garbage after the chain is an interrupted append too; two
        // are not.
        let mut garbage = committed.clone();
        garbage.extend_from_slice(&[0xa5; RECORD_LEN]);
        overwrite(&dir.log(), &garbage);
        let registry = NullifierRegistry::open(&dir.0, KEY).unwrap();
        assert_eq!(registry.checkpoint(), before);
        drop(registry);
        garbage.extend_from_slice(&[0xa5; RECORD_LEN]);
        overwrite(&dir.log(), &garbage);
        assert!(matches!(
            NullifierRegistry::open(&dir.0, KEY),
            Err(RegistryError::Corrupt(_))
        ));
    }

    #[test]
    fn flipped_byte_in_committed_data_refuses_open() {
        let dir = TempDir::new("flip");
        let good = populated(&dir, 3);
        assert_eq!(good.len(), HEADER_LEN + 3 * RECORD_LEN);
        let flips = (0..GENESIS_PREFIX_LEN).chain(HEADER_LEN..good.len());
        for at in flips {
            let mut bad = good.clone();
            bad[at] ^= 1 << (at % 8);
            overwrite(&dir.log(), &bad);
            assert!(
                matches!(
                    NullifierRegistry::open(&dir.0, KEY),
                    Err(RegistryError::Corrupt(_))
                ),
                "flip at {at} was accepted"
            );
            // The refusal wrote nothing.
            assert_eq!(fs::read(dir.log()).unwrap(), bad, "flip at {at}");
        }
        overwrite(&dir.log(), &good);
        assert_eq!(NullifierRegistry::open(&dir.0, KEY).unwrap().bindings(), 3);
    }

    #[test]
    fn damaged_slots_heal_from_one_and_refuse_without_any() {
        let dir = TempDir::new("slots");
        let good = populated(&dir, 2);
        for slot in [SLOT_A_OFFSET, SLOT_B_OFFSET] {
            let mut bad = good.clone();
            bad[slot + 9] ^= 0x40;
            overwrite(&dir.log(), &bad);
            let registry = NullifierRegistry::open(&dir.0, KEY).unwrap();
            assert_eq!(registry.checkpoint().generation, 2);
            drop(registry);
            assert_eq!(fs::read(dir.log()).unwrap(), good);
        }
        let mut bad = good.clone();
        bad[SLOT_A_OFFSET + 9] ^= 0x40;
        bad[SLOT_B_OFFSET + 9] ^= 0x40;
        overwrite(&dir.log(), &bad);
        assert!(matches!(
            NullifierRegistry::open(&dir.0, KEY),
            Err(RegistryError::Corrupt(_))
        ));
    }

    #[test]
    fn reordered_substituted_and_copied_logs_are_refused() {
        let dir = TempDir::new("reorder");
        let good = populated(&dir, 3);
        let record = |i: usize| HEADER_LEN + i * RECORD_LEN..HEADER_LEN + (i + 1) * RECORD_LEN;
        let refused = |bytes: &[u8]| {
            overwrite(&dir.log(), bytes);
            matches!(
                NullifierRegistry::open(&dir.0, KEY),
                Err(RegistryError::Corrupt(_))
            )
        };

        let mut swapped = good.clone();
        swapped[record(0)].copy_from_slice(&good[record(1)]);
        swapped[record(1)].copy_from_slice(&good[record(0)]);
        assert!(refused(&swapped));
        let mut swapped_tail = good.clone();
        swapped_tail[record(1)].copy_from_slice(&good[record(2)]);
        swapped_tail[record(2)].copy_from_slice(&good[record(1)]);
        assert!(refused(&swapped_tail));
        let mut duplicated = good.clone();
        duplicated[record(2)].copy_from_slice(&good[record(1)]);
        assert!(refused(&duplicated));

        // A record that authenticates in another registry under the same key.
        let other = TempDir::new("reorder-other");
        let foreign = populated(&other, 3);
        let mut substituted = good.clone();
        substituted[record(2)].copy_from_slice(&foreign[record(2)]);
        assert!(refused(&substituted));
        // The other registry's whole log, on this inode.
        assert!(refused(&foreign));

        // The same bytes on another inode.
        overwrite(&dir.log(), &good);
        let copy = TempDir::new("reorder-copy");
        copy.make();
        fs::copy(dir.log(), copy.log()).unwrap();
        assert!(matches!(
            NullifierRegistry::open(&copy.0, KEY),
            Err(RegistryError::Corrupt(_))
        ));
        assert_eq!(NullifierRegistry::open(&dir.0, KEY).unwrap().bindings(), 3);
    }

    #[test]
    fn truncation_and_rollback() {
        let dir = TempDir::new("rollback");
        let anchor = MemoryAnchor::default();
        let mut registry =
            NullifierRegistry::create_anchored(&dir.0, KEY, Box::new(anchor.clone())).unwrap();
        assert_eq!(anchor.load().unwrap().unwrap().generation, 0);
        registry.register(&binding(1)).unwrap();
        let old_checkpoint = registry.checkpoint();
        drop(registry);
        let old = fs::read(dir.log()).unwrap();
        let mut registry =
            NullifierRegistry::open_anchored(&dir.0, KEY, Box::new(anchor.clone())).unwrap();
        registry.register(&binding(2)).unwrap();
        registry.register(&binding(3)).unwrap();
        let checkpoint = registry.checkpoint();
        assert_eq!(anchor.load().unwrap(), Some(checkpoint));
        drop(registry);
        let current = fs::read(dir.log()).unwrap();

        // Records cut off, slots untouched: refused with no anchor at all.
        for keep in 0..3 {
            overwrite(&dir.log(), &current[..HEADER_LEN + keep * RECORD_LEN]);
            assert!(matches!(
                NullifierRegistry::open(&dir.0, KEY),
                Err(RegistryError::Corrupt(_))
            ));
        }

        // The whole file put back to an earlier state of itself: every MAC verifies.
        overwrite(&dir.log(), &old);
        assert!(matches!(
            NullifierRegistry::open_anchored(&dir.0, KEY, Box::new(anchor.clone())),
            Err(RegistryError::RolledBack)
        ));
        assert!(matches!(
            NullifierRegistry::open_at_least(&dir.0, KEY, checkpoint),
            Err(RegistryError::RolledBack)
        ));
        assert_eq!(anchor.load().unwrap(), Some(checkpoint));
        // Without an anchor or a retained checkpoint this rollback is not detectable:
        // the registry opens at the earlier state and nullifier 2 is free again.
        let mut registry = NullifierRegistry::open(&dir.0, KEY).unwrap();
        assert_eq!(registry.checkpoint(), old_checkpoint);
        assert_eq!(registry.lookup(&[2; 32]).unwrap(), None);
        // Growing the rolled-back log past the anchored length does not help either.
        let mut rebound = binding(2);
        rebound.pq_commitment = [0xee; 32];
        registry.register(&rebound).unwrap();
        registry.register(&binding(4)).unwrap();
        registry.register(&binding(5)).unwrap();
        assert!(registry.checkpoint().generation > checkpoint.generation);
        drop(registry);
        assert!(matches!(
            NullifierRegistry::open_anchored(&dir.0, KEY, Box::new(anchor.clone())),
            Err(RegistryError::RolledBack)
        ));
        assert!(matches!(
            NullifierRegistry::open_at_least(&dir.0, KEY, checkpoint),
            Err(RegistryError::RolledBack)
        ));

        // The current state still opens, also against the older checkpoint.
        overwrite(&dir.log(), &current);
        drop(NullifierRegistry::open_at_least(&dir.0, KEY, old_checkpoint).unwrap());
        let registry =
            NullifierRegistry::open_anchored(&dir.0, KEY, Box::new(anchor.clone())).unwrap();
        assert_eq!(registry.checkpoint(), checkpoint);
        drop(registry);

        // A deleted log cannot be provisioned again under the same anchor, and an
        // empty anchor cannot adopt an existing log's history as its floor.
        fs::remove_file(dir.log()).unwrap();
        assert!(matches!(
            NullifierRegistry::create_anchored(&dir.0, KEY, Box::new(anchor.clone())),
            Err(RegistryError::RolledBack)
        ));
        assert!(matches!(
            NullifierRegistry::open_anchored(&dir.0, KEY, Box::new(anchor)),
            Err(RegistryError::Io(e)) if e.kind() == io::ErrorKind::NotFound
        ));
        drop(NullifierRegistry::create(&dir.0, KEY).unwrap());
        assert!(matches!(
            NullifierRegistry::open_anchored(&dir.0, KEY, Box::new(MemoryAnchor::default())),
            Err(RegistryError::RolledBack)
        ));
    }

    #[test]
    fn two_handles_cannot_both_write() {
        let dir = TempDir::new("lock");
        let mut first = NullifierRegistry::create(&dir.0, KEY).unwrap();
        for _ in 0..2 {
            assert!(matches!(
                NullifierRegistry::open(&dir.0, KEY),
                Err(RegistryError::Locked)
            ));
            assert!(matches!(
                NullifierRegistry::create(&dir.0, KEY),
                Err(RegistryError::Io(e)) if e.kind() == io::ErrorKind::AlreadyExists
            ));
            first.register(&binding(1)).unwrap();
        }
        let held = std::thread::scope(|scope| {
            scope
                .spawn(|| NullifierRegistry::open(&dir.0, KEY).map(|_| ()))
                .join()
                .unwrap()
        });
        assert!(matches!(held, Err(RegistryError::Locked)));
        drop(first);
        let mut second = NullifierRegistry::open(&dir.0, KEY).unwrap();
        assert!(second.register(&binding(2)).unwrap().appended);
        assert_eq!(second.bindings(), 2);
    }

    #[test]
    fn interrupted_provisioning_is_retried() {
        let dir = TempDir::new("genesis");
        dir.make();
        let staging = dir.0.join(TMP_NAME);
        let stale = no_follow_options()
            .unwrap()
            .write(true)
            .create_new(true)
            .open(&staging)
            .unwrap();
        stale.try_lock().unwrap();
        // A live provisioning holds its staging file.
        assert!(matches!(
            NullifierRegistry::create(&dir.0, KEY),
            Err(RegistryError::Locked)
        ));
        assert!(matches!(
            NullifierRegistry::open(&dir.0, KEY),
            Err(RegistryError::Io(e)) if e.kind() == io::ErrorKind::NotFound
        ));
        drop(stale);
        {
            use std::os::unix::fs::PermissionsExt;
            let mode =
                |bits| fs::set_permissions(&dir.0, fs::Permissions::from_mode(bits)).unwrap();
            mode(0o770);
            assert!(matches!(
                NullifierRegistry::create(&dir.0, KEY),
                Err(RegistryError::Io(e)) if e.kind() == io::ErrorKind::PermissionDenied
            ));
            mode(0o700);
        }
        let mut registry = NullifierRegistry::create(&dir.0, KEY).unwrap();
        assert!(!staging.exists());
        registry.register(&binding(1)).unwrap();
        drop(registry);
        assert_eq!(NullifierRegistry::open(&dir.0, KEY).unwrap().bindings(), 1);
    }

    #[test]
    fn statement_binding_separates_credentials_and_targets() {
        use qsag_addr::{KeyIdentityKind, WitnessSuiteTag};
        let address = |seed: u8| {
            QsagAddress::from_pubkey_poseidon2(
                "qsp",
                WitnessSuiteTag::MlDsa65,
                KeyIdentityKind::SingleOrThreshold,
                &[seed; 32],
            )
            .unwrap()
        };
        let binding = |credential: Credential, seed: u8| MigrationBinding {
            nullifier: [7; 32],
            migration_domain: [3; 32],
            legacy_id: credential.identifier(),
            pq_commitment: pq_commitment(&address(seed)),
            epoch: 11,
            exposure: KeyExposure::Hidden,
        };
        let base = binding(Credential::BitcoinKeyHash([9; 20]), 1);
        let other_chain = binding(Credential::EthereumAddress([9; 20]), 1);
        let other_target = binding(Credential::BitcoinKeyHash([9; 20]), 2);
        assert_ne!(base.legacy_id, other_chain.legacy_id);
        assert_eq!(base.pq_commitment, other_chain.pq_commitment);
        assert_eq!(base.legacy_id, other_target.legacy_id);
        assert_ne!(base.pq_commitment, other_target.pq_commitment);
        assert_ne!(base.leaf(), other_target.leaf());
        assert_ne!(base.leaf(), other_chain.leaf());

        let dir = TempDir::new("statement");
        let mut registry = NullifierRegistry::create(&dir.0, KEY).unwrap();
        registry.register(&base).unwrap();
        assert!(matches!(
            registry.register(&other_target),
            Err(RegistryError::NullifierConflict)
        ));
    }
}
