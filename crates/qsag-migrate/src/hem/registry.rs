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

