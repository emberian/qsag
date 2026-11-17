//! One-use acceptance records for authenticated capability seals.
//!
//! A seal is accepted once per **consumption domain**: the single set of records
//! that every verifier of an audience consults before it accepts. The verifier API
//! takes that domain as [`SealConsumptionDomain`], so a caller cannot verify without
//! naming it. What a domain must be is a deployment requirement this crate cannot
//! check:
//!
//! * one domain per audience. A fresh store per request, or one store per replica,
//!   lets every seal be accepted once per store. Replicas share one linearizable
//!   implementation of [`SealConsumptionDomain`], or route to one host;
//! * as durable as the acceptance lifetime: [`MemorySealConsumptionStore`] ends with
//!   its process;
//! * protected against being put back: [`FsSealConsumptionStore`] with an external
//!   anchor refuses a restored file; without one it does not.
//!
//! Consumption happens after authentication and before authorization is returned;
//! later application failure does not refund a consumed seal.

use alloc::vec::Vec;

use crate::MAX_POLICY_CAPACITY;
use crate::macaroon::CapabilityError;

/// The one consumption domain of an audience (see the module documentation).
///
/// `consume` atomically reserves a previously unseen seal identifier before returning
/// success. Implementations must reject repeats, retain all accepted identifiers, and
/// fail closed on storage errors or exhaustion. Replicated verifiers need a shared,
/// linearizable implementation. Returning success without recording the identifier
/// violates this contract.
pub trait SealConsumptionDomain {
    fn consume(&mut self, seal_id: [u8; 32]) -> Result<(), CapabilityError>;
}

/// Bounded process-local consumption. Dropping this store loses replay protection.
/// Use only when the verifier's entire acceptance lifetime is this process; durable
/// services should use persistent storage. There is deliberately no reset or eviction.
pub struct MemorySealConsumptionStore {
    consumed: Vec<[u8; 32]>,
    capacity: usize,
}

impl MemorySealConsumptionStore {
    /// A capacity outside `1..=MAX_POLICY_CAPACITY` fails closed on every consumption.
    pub const fn new(capacity: usize) -> Self {
        Self {
            consumed: Vec::new(),
            capacity,
        }
    }

    fn insertion_index(&self, seal_id: &[u8; 32]) -> Result<usize, CapabilityError> {
        let index = match self.consumed.binary_search(seal_id) {
            Ok(_) => return Err(CapabilityError::Replay),
            Err(index) => index,
        };
        if self.capacity > MAX_POLICY_CAPACITY || self.consumed.len() >= self.capacity {
            return Err(CapabilityError::ConsumptionFailed);
        }
        Ok(index)
    }
}

impl SealConsumptionDomain for MemorySealConsumptionStore {
    fn consume(&mut self, seal_id: [u8; 32]) -> Result<(), CapabilityError> {
        let index = self.insertion_index(&seal_id)?;
        self.consumed
            .try_reserve(1)
            .map_err(|_| CapabilityError::ConsumptionFailed)?;
        self.consumed.insert(index, seal_id);
        Ok(())
    }
}

/// One exclusively locked file holding the current snapshot of a small state machine,
/// optionally pinned by an [`ExternalMonotoneAnchor`] kept outside the file's own
/// rollback domain (another device, a TPM counter, a remote monotonic service).
///
/// Frame: `magic[8] || anchored[1] || 0[7] || sequence u64 BE || previous_tag[32] ||
/// payload`. Every commit increases `sequence` by one and records the tag of the frame
/// it replaces. The frame's checkpoint is `(sequence + 1, cSHAKE256(frame))`.
///
/// With an anchor, a commit writes the frame durably and then advances the anchor to
/// the frame's checkpoint; opening compares the two:
///
/// * equal generation: the tags must be equal, so any other content at that
///   generation is refused, whoever wrote it;
/// * the frame is one generation ahead and names the anchored tag as its predecessor:
///   the process stopped between the two writes, and the anchor is advanced here;
/// * the frame is behind the anchor: an earlier state was put back (file restored in
///   place, directory restored from a backup, volume snapshot). Refused;
/// * the anchor is empty: it is not the anchor this file was created under. Refused.
///
/// The frame carries no MAC: a writer with arbitrary access to the file who acts in
/// the one-commit window before the anchor advances can substitute a successor frame.
/// The anchor's guarantee is against restoring earlier bytes, in every state.
///
/// Without an anchor this is crash recovery and process exclusion only: nothing
/// distinguishes the current frame from an earlier one. An anchored file refuses to
/// open without its anchor, and the reverse.
#[cfg(feature = "std")]
pub struct AnchoredSnapshot {
    record: qsag_asm::durable::LockedRecord,
    anchor: Option<alloc::boxed::Box<dyn ExternalMonotoneAnchor>>,
    magic: [u8; 8],
    sequence: u64,
    tag: [u8; 32],
    failed: bool,
}

#[cfg(feature = "std")]
use qsag_core::{ExternalMonotoneAnchor, LedgerCheckpoint};

#[cfg(feature = "std")]
impl AnchoredSnapshot {
    const HEADER_BYTES: usize = 56;

    fn invalid(message: impl Into<alloc::string::String>) -> std::io::Error {
        std::io::Error::new(std::io::ErrorKind::InvalidData, message.into())
    }

    fn frame(&self, sequence: u64, previous: &[u8; 32], payload: &[u8]) -> Vec<u8> {
        let mut frame = Vec::with_capacity(Self::HEADER_BYTES + payload.len());
        frame.extend_from_slice(&self.magic);
        frame.push(u8::from(self.anchor.is_some()));
        frame.extend_from_slice(&[0; 7]);
        frame.extend_from_slice(&sequence.to_be_bytes());
        frame.extend_from_slice(previous);
        frame.extend_from_slice(payload);
        frame
    }

    fn frame_tag(frame: &[u8]) -> [u8; 32] {
        qsag_accel::keccak::cshake256_framed_32(b"QSAG.SNAPSHOT.CHECKPOINT.V1", &[frame])
    }

    fn checkpoint_of(sequence: u64, tag: [u8; 32]) -> std::io::Result<LedgerCheckpoint> {
        Ok(LedgerCheckpoint {
            generation: sequence
                .checked_add(1)
                .ok_or_else(|| std::io::Error::other("snapshot sequence exhausted"))?,
            tag,
        })
    }

    /// The checkpoint of the current frame: what an anchor holds when settled.
    pub fn checkpoint(&self) -> LedgerCheckpoint {
        LedgerCheckpoint {
            generation: self.sequence + 1,
            tag: self.tag,
        }
    }

    pub fn is_anchored(&self) -> bool {
        self.anchor.is_some()
    }

    /// Create the file with its first frame. An `anchor` must be empty: one that
    /// already holds a checkpoint belongs to other state.
    pub fn create_new(
        path: impl Into<std::path::PathBuf>,
        magic: [u8; 8],
        payload: &[u8],
        anchor: Option<alloc::boxed::Box<dyn ExternalMonotoneAnchor>>,
    ) -> std::io::Result<Self> {
        if let Some(anchor) = &anchor
            && anchor.load()?.is_some()
        {
            return Err(std::io::Error::new(
                std::io::ErrorKind::AlreadyExists,
                "the external anchor already holds a checkpoint; a new store needs a fresh anchor",
            ));
        }
        let mut this = Self {
            record: qsag_asm::durable::LockedRecord::create_new(path)?,
            anchor,
            magic,
            sequence: 0,
            tag: [0; 32],
            failed: false,
        };
        let frame = this.frame(0, &[0; 32], payload);
        this.record.replace(&frame)?;
        this.tag = Self::frame_tag(&frame);
        if let Some(anchor) = &this.anchor {
            anchor.advance(this.checkpoint())?;
        }
        Ok(this)
    }

    /// Open the file and return its payload (at most `max_payload` bytes), after
    /// reconciling it with `anchor` as described on the type.
    pub fn open_existing(
        path: impl Into<std::path::PathBuf>,
        magic: [u8; 8],
        max_payload: usize,
        anchor: Option<alloc::boxed::Box<dyn ExternalMonotoneAnchor>>,
    ) -> std::io::Result<(Self, Vec<u8>)> {
        let record = qsag_asm::durable::LockedRecord::open_existing(path)?;
        let frame = record.read_bounded(Self::HEADER_BYTES.saturating_add(max_payload))?;
        if frame.len() < Self::HEADER_BYTES || frame[..8] != magic || frame[9..16] != [0; 7] {
            return Err(Self::invalid(
                "not a snapshot record of this kind and format version",
            ));
        }
        match (frame[8], anchor.is_some()) {
            (0, false) | (1, true) => {}
            (1, false) => {
                return Err(Self::invalid(
                    "this store was created with an external anchor and must be opened with it",
                ));
            }
            (0, true) => {
                return Err(Self::invalid(
                    "this store was created without an external anchor; it has no anchored history to check",
                ));
            }
            _ => return Err(Self::invalid("invalid anchor flag in snapshot record")),
        }
        let mut sequence = [0; 8];
        sequence.copy_from_slice(&frame[16..24]);
        let sequence = u64::from_be_bytes(sequence);
        let mut previous = [0; 32];
        previous.copy_from_slice(&frame[24..56]);
        let this = Self {
            record,
            anchor,
            magic,
            sequence,
            tag: Self::frame_tag(&frame),
            failed: false,
        };
        let checkpoint = Self::checkpoint_of(sequence, this.tag)?;
        if let Some(anchor) = &this.anchor {
            let anchored = anchor.load()?.ok_or_else(|| {
                Self::invalid(
                    "the external anchor holds no checkpoint: it is not the anchor this store was created under, or it was reset",
                )
            })?;
            if anchored.generation == checkpoint.generation {
                if !qsag_accel::ct::ct_eq_bytes(&anchored.tag, &checkpoint.tag) {
                    return Err(Self::invalid(
                        "store content differs from the externally anchored state at the same generation",
                    ));
                }
            } else if anchored.generation.checked_add(1) == Some(checkpoint.generation)
                && qsag_accel::ct::ct_eq_bytes(&anchored.tag, &previous)
            {
                anchor.advance(checkpoint)?;
            } else if anchored.generation > checkpoint.generation {
                return Err(Self::invalid(alloc::format!(
                    "store is at generation {} but its external anchor is at {}: an earlier state was restored (rollback)",
                    checkpoint.generation,
                    anchored.generation
                )));
            } else {
                return Err(Self::invalid(
                    "store is ahead of its external anchor by more than one interrupted commit",
                ));
            }
        }
        let payload = frame[Self::HEADER_BYTES..].to_vec();
        Ok((this, payload))
    }

    /// Replace the payload: durable write, then the anchor. After any failure this
    /// handle refuses further commits; reopen to learn which state is durable.
    pub fn commit(&mut self, payload: &[u8]) -> std::io::Result<()> {
        if self.failed {
            return Err(std::io::Error::other("snapshot handle failed earlier"));
        }
        self.failed = true;
        let sequence = self
            .sequence
            .checked_add(1)
            .filter(|next| *next < u64::MAX)
            .ok_or_else(|| std::io::Error::other("snapshot sequence exhausted"))?;
        let frame = self.frame(sequence, &self.tag, payload);
        self.record.replace(&frame)?;
        self.sequence = sequence;
        self.tag = Self::frame_tag(&frame);
        if let Some(anchor) = &self.anchor {
            anchor.advance(self.checkpoint())?;
        }
        self.failed = false;
        Ok(())
    }
}

/// Crash-durable, exclusively locked consumption records for one acceptance domain.
///
/// All processes in an acceptance domain must open the same provisioned path. A
/// competing open fails while this handle holds the lock; callers may retry after
/// the holder exits. `open_existing` never creates a missing ledger.
///
/// # Rollback
/// [`Self::create_new_anchored`] pins every consumption in an
/// [`ExternalMonotoneAnchor`] (see [`AnchoredSnapshot`]): a store whose file or whole
/// directory was put back to an earlier state is refused on open, so a seal consumed
/// after that state cannot be accepted again. [`Self::create_new`] has no anchor and
/// gives crash recovery and process exclusion only: an administrator, backup tool or
/// volume snapshot that restores the file re-admits every seal consumed since.
///
/// # One consumption domain
/// An anchor does nothing for a second, independent copy of the service: two replicas
/// with their own stores each accept every seal once. That cannot be detected locally.
/// A deployment has exactly one consumption domain per audience: one store on one
/// host, or one linearizable service behind [`SealConsumptionDomain`].
///
/// No accepted entry is evicted on exhaustion.
#[cfg(feature = "std")]
pub struct FsSealConsumptionStore {
    snapshot: AnchoredSnapshot,
    memory: MemorySealConsumptionStore,
    domain_id: [u8; 32],
}

#[cfg(feature = "std")]
impl FsSealConsumptionStore {
    // QSBURN01 was the unframed, unanchorable record; it is not read.
    const MAGIC: [u8; 8] = *b"QSBURN02";
    const PAYLOAD_HEADER_BYTES: usize = 40;

    fn check_capacity(capacity: usize) -> std::io::Result<()> {
        if capacity == 0 || capacity > MAX_POLICY_CAPACITY {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "seal consumption capacity outside supported range",
            ));
        }
        Ok(())
    }

    fn create(
        path: impl Into<std::path::PathBuf>,
        capacity: usize,
        domain_id: [u8; 32],
        anchor: Option<alloc::boxed::Box<dyn ExternalMonotoneAnchor>>,
    ) -> std::io::Result<Self> {
        Self::check_capacity(capacity)?;
        let memory = MemorySealConsumptionStore::new(capacity);
        let payload = Self::encode(&domain_id, &memory);
        Ok(Self {
            snapshot: AnchoredSnapshot::create_new(path, Self::MAGIC, &payload, anchor)?,
            memory,
            domain_id,
        })
    }

    /// Provision an empty acceptance domain with no rollback protection. Never use
    /// this to recover a lost ledger.
    pub fn create_new(
        path: impl Into<std::path::PathBuf>,
        capacity: usize,
    ) -> std::io::Result<Self> {
        Self::create(path, capacity, [0; 32], None)
    }

    /// Provision an empty acceptance domain pinned by `anchor`, which must be empty
    /// and must not share the store's rollback domain. `domain_id` is recorded so a
    /// later open can locate the same anchor ([`Self::anchored_domain_id`]).
    pub fn create_new_anchored(
        path: impl Into<std::path::PathBuf>,
        capacity: usize,
        domain_id: [u8; 32],
        anchor: alloc::boxed::Box<dyn ExternalMonotoneAnchor>,
    ) -> std::io::Result<Self> {
        Self::create(path, capacity, domain_id, Some(anchor))
    }

    fn open(
        path: impl Into<std::path::PathBuf>,
        capacity: usize,
        anchor: Option<alloc::boxed::Box<dyn ExternalMonotoneAnchor>>,
    ) -> std::io::Result<Self> {
        Self::check_capacity(capacity)?;
        let (snapshot, payload) = AnchoredSnapshot::open_existing(
            path,
            Self::MAGIC,
            Self::PAYLOAD_HEADER_BYTES + 32 * capacity,
            anchor,
        )?;
        let (domain_id, memory) = Self::decode(&payload, capacity)?;
        Ok(Self {
            snapshot,
            memory,
            domain_id,
        })
    }

    /// Recover an unanchored domain, requiring its original capacity and format.
    pub fn open_existing(
        path: impl Into<std::path::PathBuf>,
        capacity: usize,
    ) -> std::io::Result<Self> {
        Self::open(path, capacity, None)
    }

    /// Recover an anchored domain; a store older than `anchor` is refused.
    pub fn open_existing_anchored(
        path: impl Into<std::path::PathBuf>,
        capacity: usize,
        anchor: alloc::boxed::Box<dyn ExternalMonotoneAnchor>,
    ) -> std::io::Result<Self> {
        Self::open(path, capacity, Some(anchor))
    }

    /// The `domain_id` an anchored store at `path` was created with, read without
    /// trusting it: the anchor it leads to still has to agree with the store.
    pub fn anchored_domain_id(
        path: impl Into<std::path::PathBuf>,
        capacity: usize,
    ) -> std::io::Result<[u8; 32]> {
        Self::check_capacity(capacity)?;
        let record = qsag_asm::durable::LockedRecord::open_existing(path)?;
        let frame = record.read_bounded(
            AnchoredSnapshot::HEADER_BYTES + Self::PAYLOAD_HEADER_BYTES + 32 * capacity,
        )?;
        if frame.len() < AnchoredSnapshot::HEADER_BYTES + Self::PAYLOAD_HEADER_BYTES
            || frame[..8] != Self::MAGIC
        {
            return Err(Self::invalid());
        }
        if frame[8] != 1 {
            return Err(AnchoredSnapshot::invalid(
                "this seal consumption store was created without an external anchor; it has no anchored history to check",
            ));
        }
        let mut domain_id = [0; 32];
        domain_id.copy_from_slice(
            &frame[AnchoredSnapshot::HEADER_BYTES..AnchoredSnapshot::HEADER_BYTES + 32],
        );
        Ok(domain_id)
    }

    pub fn domain_id(&self) -> &[u8; 32] {
        &self.domain_id
    }

    pub fn is_anchored(&self) -> bool {
        self.snapshot.is_anchored()
    }

    fn invalid() -> std::io::Error {
        AnchoredSnapshot::invalid(
            "invalid or unsupported seal consumption record (expected QSBURN02 and configured capacity)",
        )
    }

    fn decode(
        payload: &[u8],
        capacity: usize,
    ) -> std::io::Result<([u8; 32], MemorySealConsumptionStore)> {
        if payload.len() < Self::PAYLOAD_HEADER_BYTES {
            return Err(Self::invalid());
        }
        let mut domain_id = [0; 32];
        domain_id.copy_from_slice(&payload[..32]);
        let word = |at: usize| {
            u32::from_be_bytes([
                payload[at],
                payload[at + 1],
                payload[at + 2],
                payload[at + 3],
            ])
        };
        let (stored_capacity, count) = (word(32), word(36) as usize);
        if stored_capacity as usize != capacity
            || count > capacity
            || payload.len() != Self::PAYLOAD_HEADER_BYTES + count * 32
        {
            return Err(Self::invalid());
        }
        let mut memory = MemorySealConsumptionStore::new(capacity);
        memory
            .consumed
            .try_reserve_exact(count)
            .map_err(std::io::Error::other)?;
        let (ids, rest) = payload[Self::PAYLOAD_HEADER_BYTES..].as_chunks::<32>();
        if !rest.is_empty() {
            return Err(Self::invalid());
        }
        for &id in ids {
            if memory.consumed.last().is_some_and(|prev| prev >= &id) {
                return Err(Self::invalid());
            }
            memory.consumed.push(id);
        }
        Ok((domain_id, memory))
    }

    fn encode(domain_id: &[u8; 32], memory: &MemorySealConsumptionStore) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(Self::PAYLOAD_HEADER_BYTES + memory.consumed.len() * 32);
        bytes.extend_from_slice(domain_id);
        bytes.extend_from_slice(&(memory.capacity as u32).to_be_bytes());
        bytes.extend_from_slice(&(memory.consumed.len() as u32).to_be_bytes());
        for id in &memory.consumed {
            bytes.extend_from_slice(id);
        }
        bytes
    }
}

#[cfg(feature = "std")]
impl SealConsumptionDomain for FsSealConsumptionStore {
    fn consume(&mut self, seal_id: [u8; 32]) -> Result<(), CapabilityError> {
        // A failed commit may already be durable: the snapshot handle refuses every
        // later commit until a fresh open has recovered the committed record.
        if self.snapshot.failed {
            return Err(CapabilityError::ConsumptionFailed);
        }
        self.memory.consume(seal_id)?;
        self.snapshot
            .commit(&Self::encode(&self.domain_id, &self.memory))
            .map_err(|_| CapabilityError::ConsumptionFailed)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[cfg(all(feature = "std", unix))]
    use alloc::boxed::Box;

    /// A forked child holds copies of this process's lock descriptors until it execs,
    /// so a store dropped and reopened on one thread while another thread spawns a
    /// child can find its own lock still held. Tests that lock files or spawn take this.
    #[cfg(all(feature = "std", unix))]
    fn serial() -> std::sync::MutexGuard<'static, ()> {
        static SERIAL: std::sync::Mutex<()> = std::sync::Mutex::new(());
        SERIAL
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
    }

    #[test]
    fn memory_rejects_replay_without_eviction() {
        let mut store = MemorySealConsumptionStore::new(2);
        assert_eq!(store.consume([2; 32]), Ok(()));
        assert_eq!(store.consume([1; 32]), Ok(()));
        assert_eq!(store.consume([2; 32]), Err(CapabilityError::Replay));
        assert_eq!(
            store.consume([3; 32]),
            Err(CapabilityError::ConsumptionFailed)
        );
        assert_eq!(store.consume([1; 32]), Err(CapabilityError::Replay));
        assert_eq!(
            MemorySealConsumptionStore::new(0).consume([1; 32]),
            Err(CapabilityError::ConsumptionFailed)
        );
        assert_eq!(
            MemorySealConsumptionStore::new(usize::MAX).consume([1; 32]),
            Err(CapabilityError::ConsumptionFailed)
        );
    }

    #[cfg(all(feature = "std", unix))]
    #[test]
    fn disk_rejects_replay_after_restart_and_competing_process() {
        let _serial = serial();
        const CHILD: &str = "QSAG_SEAL_STORE_CHILD_PATH";
        if let Some(path) = std::env::var_os(CHILD) {
            assert!(FsSealConsumptionStore::open_existing(path, 2).is_err());
            return;
        }
        let dir = temporary_directory("restart");
        let path = dir.join("consumed");
        let mut store = FsSealConsumptionStore::create_new(&path, 2).unwrap();
        store.consume([2; 32]).unwrap();
        let child = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "seal_store::tests::disk_rejects_replay_after_restart_and_competing_process",
                "--nocapture",
            ])
            .env(CHILD, &path)
            .status()
            .unwrap();
        assert!(child.success());
        drop(store);
        let mut store = FsSealConsumptionStore::open_existing(&path, 2).unwrap();
        assert_eq!(store.consume([2; 32]), Err(CapabilityError::Replay));
        store.consume([1; 32]).unwrap();
        drop(store);
        let mut store = FsSealConsumptionStore::open_existing(&path, 2).unwrap();
        assert_eq!(
            store.consume([3; 32]),
            Err(CapabilityError::ConsumptionFailed)
        );
        assert_eq!(store.consume([1; 32]), Err(CapabilityError::Replay));
        drop(store);
        assert!(FsSealConsumptionStore::open_existing(&path, 3).is_err());
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[cfg(all(feature = "std", unix))]
    #[test]
    fn disk_write_failure_poison_and_invalid_format_fail_closed() {
        let _serial = serial();
        let dir = temporary_directory("failure");
        let path = dir.join("consumed");
        let mut store = FsSealConsumptionStore::create_new(&path, 2).unwrap();
        // A directory where atomic replacement needs its temporary file forces I/O failure.
        std::fs::create_dir(dir.join("consumed.tmp")).unwrap();
        assert_eq!(
            store.consume([1; 32]),
            Err(CapabilityError::ConsumptionFailed)
        );
        std::fs::remove_dir(dir.join("consumed.tmp")).unwrap();
        assert_eq!(
            store.consume([2; 32]),
            Err(CapabilityError::ConsumptionFailed)
        );
        drop(store);
        let mut store = FsSealConsumptionStore::open_existing(&path, 2).unwrap();
        store.consume([2; 32]).unwrap();
        drop(store);
        // The superseded unframed format is refused, not migrated.
        let mut old = Vec::new();
        old.extend_from_slice(b"QSBURN01");
        old.extend_from_slice(&2u32.to_be_bytes());
        old.extend_from_slice(&0u32.to_be_bytes());
        let record = qsag_asm::durable::LockedRecord::open_existing(&path).unwrap();
        record.replace(&old).unwrap();
        drop(record);
        assert!(FsSealConsumptionStore::open_existing(&path, 2).is_err());
        std::fs::remove_dir_all(dir).unwrap();
    }

    /// An anchor outside the store's directory: it keeps what it was last given.
    #[cfg(all(feature = "std", unix))]
    #[derive(Clone, Default)]
    struct TestAnchor {
        cell: std::sync::Arc<std::sync::Mutex<Option<LedgerCheckpoint>>>,
        fail_next_advance: std::sync::Arc<std::sync::atomic::AtomicBool>,
    }

    #[cfg(all(feature = "std", unix))]
    impl ExternalMonotoneAnchor for TestAnchor {
        fn load(&self) -> std::io::Result<Option<LedgerCheckpoint>> {
            Ok(*self.cell.lock().unwrap())
        }
        fn advance(&self, checkpoint: LedgerCheckpoint) -> std::io::Result<()> {
            if self
                .fail_next_advance
                .swap(false, std::sync::atomic::Ordering::SeqCst)
            {
                return Err(std::io::Error::other("anchor unreachable"));
            }
            let mut cell = self.cell.lock().unwrap();
            if let Some(old) = *cell
                && (old.generation > checkpoint.generation
                    || (old.generation == checkpoint.generation && old.tag != checkpoint.tag))
            {
                return Err(std::io::Error::other("anchor rejects rolled-back state"));
            }
            *cell = Some(checkpoint);
            Ok(())
        }
    }

    #[cfg(all(feature = "std", unix))]
    fn dir_files(dir: &std::path::Path) -> Vec<(std::path::PathBuf, Vec<u8>)> {
        let mut files: Vec<_> = std::fs::read_dir(dir)
            .unwrap()
            .map(|e| e.unwrap().path())
            .map(|p| {
                let bytes = std::fs::read(&p).unwrap();
                (p, bytes)
            })
            .collect();
        files.sort();
        files
    }

    // A seal consumed after a backup must stay consumed when the backup is put back,
    // both over the same inodes and as a replaced directory. The unanchored store in
    // the same scenario accepts the seal again: that is the gap the anchor closes.
    #[cfg(all(feature = "std", unix))]
    #[test]
    fn anchored_store_refuses_in_place_and_whole_directory_restore() {
        let _serial = serial();
        for anchored in [false, true] {
            let dir = temporary_directory(if anchored { "anchored" } else { "bare" });
            let path = dir.join("consumed");
            let anchor = TestAnchor::default();
            let create = || {
                if anchored {
                    FsSealConsumptionStore::create_new_anchored(
                        &path,
                        4,
                        [7; 32],
                        Box::new(anchor.clone()),
                    )
                } else {
                    FsSealConsumptionStore::create_new(&path, 4)
                }
            };
            let open = || {
                if anchored {
                    FsSealConsumptionStore::open_existing_anchored(
                        &path,
                        4,
                        Box::new(anchor.clone()),
                    )
                } else {
                    FsSealConsumptionStore::open_existing(&path, 4)
                }
            };
            let mut store = create().unwrap();
            store.consume([1; 32]).unwrap();
            drop(store);
            let backup = dir_files(&dir);
            let mut store = open().unwrap();
            store.consume([2; 32]).unwrap();
            drop(store);
            let current = dir_files(&dir);

            // In place: same inodes, earlier bytes. This is also what a volume or
            // filesystem snapshot restore looks like to the store.
            for (file, bytes) in &backup {
                std::fs::write(file, bytes).unwrap();
            }
            let in_place = open().map(|mut store| store.consume([2; 32]));
            if anchored {
                let err = in_place.expect_err("rolled-back store must not open");
                assert!(alloc::format!("{err}").contains("rollback"), "{err}");
                // The current state still opens and still refuses the replay.
                for (file, bytes) in &current {
                    std::fs::write(file, bytes).unwrap();
                }
                let mut store = open().unwrap();
                assert_eq!(store.consume([2; 32]), Err(CapabilityError::Replay));
                assert_eq!(store.consume([1; 32]), Err(CapabilityError::Replay));
                store.consume([3; 32]).unwrap();
                drop(store);
                assert_eq!(
                    FsSealConsumptionStore::anchored_domain_id(&path, 4).unwrap(),
                    [7; 32]
                );
            } else {
                // No anchor: the consumed seal is accepted a second time.
                assert_eq!(in_place.unwrap(), Ok(()));
            }

            // Whole directory removed and rebuilt from the backup's file copies. A
            // record is bound to its lock file's inode, so this never opens, anchored
            // or not; only an inode-preserving restore reaches the anchor.
            {
                use std::io::Write;
                use std::os::unix::fs::OpenOptionsExt;
                std::fs::remove_dir_all(&dir).unwrap();
                std::fs::create_dir(&dir).unwrap();
                for (file, bytes) in &backup {
                    std::fs::OpenOptions::new()
                        .write(true)
                        .create_new(true)
                        .mode(0o600)
                        .open(file)
                        .unwrap()
                        .write_all(bytes)
                        .unwrap();
                }
            }
            assert!(open().is_err());
            std::fs::remove_dir_all(dir).unwrap();
        }
    }

    #[cfg(all(feature = "std", unix))]
    #[test]
    fn anchored_store_recovers_an_interrupted_commit_and_binds_its_anchor() {
        let _serial = serial();
        let dir = temporary_directory("anchor-binding");
        let path = dir.join("consumed");
        let anchor = TestAnchor::default();
        let open = |anchor: &TestAnchor| {
            FsSealConsumptionStore::open_existing_anchored(&path, 4, Box::new(anchor.clone()))
        };
        let mut store = FsSealConsumptionStore::create_new_anchored(
            &path,
            4,
            [7; 32],
            Box::new(anchor.clone()),
        )
        .unwrap();
        store.consume([1; 32]).unwrap();
        let settled = anchor.load().unwrap().unwrap();
        assert_eq!(settled.generation, 2);

        // The record is durable and the anchor write is lost: the handle is dead, the
        // seal stays consumed, and the next open settles the anchor on the record.
        anchor
            .fail_next_advance
            .store(true, std::sync::atomic::Ordering::SeqCst);
        assert_eq!(
            store.consume([2; 32]),
            Err(CapabilityError::ConsumptionFailed)
        );
        assert_eq!(
            store.consume([3; 32]),
            Err(CapabilityError::ConsumptionFailed)
        );
        drop(store);
        assert_eq!(anchor.load().unwrap(), Some(settled));
        let mut store = open(&anchor).unwrap();
        assert_eq!(anchor.load().unwrap().unwrap().generation, 3);
        assert_eq!(store.consume([2; 32]), Err(CapabilityError::Replay));
        drop(store);

        // A used anchor cannot be given to a new store, an empty one cannot open an
        // existing store, and the anchor requirement cannot be dropped or added.
        assert_eq!(
            FsSealConsumptionStore::create_new_anchored(
                dir.join("second"),
                4,
                [8; 32],
                Box::new(anchor.clone())
            )
            .err()
            .unwrap()
            .kind(),
            std::io::ErrorKind::AlreadyExists
        );
        assert!(open(&TestAnchor::default()).is_err());
        let err = FsSealConsumptionStore::open_existing(&path, 4)
            .err()
            .unwrap();
        assert!(
            alloc::format!("{err}").contains("must be opened with it"),
            "{err}"
        );
        let bare = dir.join("bare");
        drop(FsSealConsumptionStore::create_new(&bare, 4).unwrap());
        assert!(
            FsSealConsumptionStore::open_existing_anchored(
                &bare,
                4,
                Box::new(TestAnchor::default())
            )
            .is_err()
        );
        assert!(FsSealConsumptionStore::anchored_domain_id(&bare, 4).is_err());

        // Other content at the anchored generation: one consumed id replaced.
        let record = qsag_asm::durable::LockedRecord::open_existing(&path).unwrap();
        let mut frame = record.read_bounded(4096).unwrap();
        let last = frame.len() - 1;
        frame[last] ^= 1;
        record.replace(&frame).unwrap();
        drop(record);
        let err = open(&anchor).err().unwrap();
        assert!(alloc::format!("{err}").contains("differs"), "{err}");
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[cfg(all(feature = "std", unix))]
    fn temporary_directory(label: &str) -> std::path::PathBuf {
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(alloc::format!(
            "qsag-seal-store-{label}-{}-{nanos}",
            std::process::id()
        ));
        std::fs::create_dir(&path).unwrap();
        path
    }
}
