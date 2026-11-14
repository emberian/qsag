//! Authenticated append-only session journal with permanent sidecar inode lock.
//!
//! One locked journal lineage owns one MPC party's session history. Recovery fails closed on
//! missing, partial, reordered, unauthenticated, or inode-swapped records:
//! - A permanent `<path>.lock` sidecar is opened with `O_NOFOLLOW`, locked exclusively via OS
//!   advisory locking, and binds `(lock_dev, lock_ino, lock_nonce24)` into a 48-byte lock seal.
//! - The journal data file is opened with `O_NOFOLLOW`, verified as a regular file, and binds
//!   `(data_dev, data_ino)` into a 16-byte data seal.
//! - Every hash-chained record MAC-authenticates both seals, the previous tag, the monotonic
//!   generation, the 32-byte session identifier, and the monotonic intra-generation state
//!   (`Allocated = 0 -> Consumed = 2 -> Poisoned = 1`, or `Allocated = 0 -> Poisoned = 1`).
//! - Before every mutation and query, both pathnames are re-verified via `symlink_metadata`
//!   against the held descriptors so live pathname replacement or sidecar swapping invalidates
//!   the active handle immediately.

use crate::hash::{mac32, mac32_verify};
use crate::party_node::{NodeError, PoisonJournal};
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};

const DOMAIN: &[u8] = b"QSAG.POISON.JOURNAL/v2";
const LOCK_MAGIC: &[u8; 8] = b"QSPJLCK2";
const LOCK_HEADER_BYTES: usize = 48;
const RECORD_BYTES: usize = 73;

const STATE_ALLOCATED: u8 = 0;
const STATE_POISONED: u8 = 1;
const STATE_CONSUMED: u8 = 2;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum JournalOpenMode {
    /// Create a new lineage, refusing to overwrite any existing file or sidecar.
    CreateNew,
    /// Require and authenticate an existing lineage and its permanent sidecar.
    RecoverExisting,
}

fn lock_path_for(path: &Path) -> PathBuf {
    let mut os = path.as_os_str().to_os_string();
    os.push(".lock");
    PathBuf::from(os)
}

fn nofollow_options() -> Result<OpenOptions, NodeError> {
    let mut options = OpenOptions::new();
    #[cfg(all(target_os = "linux", any(target_arch = "aarch64", target_arch = "arm")))]
    let flags = 0x8000 | 0x800;
    #[cfg(all(
        target_os = "linux",
        any(
            target_arch = "x86_64",
            target_arch = "x86",
            target_arch = "riscv64",
            target_arch = "riscv32"
        )
    ))]
    let flags = 0x20000 | 0x800;
    #[cfg(target_os = "macos")]
    let flags = 0x100 | 0x4;
    #[cfg(any(
        target_os = "macos",
        all(
            target_os = "linux",
            any(
                target_arch = "aarch64",
                target_arch = "arm",
                target_arch = "x86_64",
                target_arch = "x86",
                target_arch = "riscv64",
                target_arch = "riscv32"
            )
        )
    ))]
    {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600).custom_flags(flags);
        Ok(options)
    }
    #[cfg(not(any(
        target_os = "macos",
        all(
            target_os = "linux",
            any(
                target_arch = "aarch64",
                target_arch = "arm",
                target_arch = "x86_64",
                target_arch = "x86",
                target_arch = "riscv64",
                target_arch = "riscv32"
            )
        )
    )))]
    {
        let _ = &mut options;
        Err(NodeError::Journal)
    }
}

fn regular_dev_ino(meta: &fs::Metadata) -> Result<(u64, u64), NodeError> {
    if !meta.is_file() || meta.file_type().is_symlink() {
        return Err(NodeError::Journal);
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        Ok((meta.dev(), meta.ino()))
    }
    #[cfg(not(unix))]
    {
        Err(NodeError::Journal)
    }
}

fn check_regular_if_present(path: &Path) -> Result<Option<(u64, u64)>, NodeError> {
    match fs::symlink_metadata(path) {
        Ok(meta) => regular_dev_ino(&meta).map(Some),
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => Ok(None),
        Err(_) => Err(NodeError::Journal),
    }
}

fn fill_lock_nonce(key: &[u8; 32], session: &[u8; 32], dev: u64, ino: u64) -> Result<[u8; 24], NodeError> {
    let mut raw = [0u8; 24];
    File::open("/dev/urandom")
        .and_then(|mut f| f.read_exact(&mut raw))
        .map_err(|_| NodeError::Journal)?;
    let mixed = mac32(
        key,
        b"QSAG.POISON.LOCK_NONCE/v2",
        &[&raw, session, &dev.to_be_bytes(), &ino.to_be_bytes()],
    );
    let mut out = [0u8; 24];
    out.copy_from_slice(&mixed[..24]);
    Ok(out)
}

/// A synchronous durable journal. Keep the MAC key outside the journal directory.
/// An exclusive OS file lock on the permanent sidecar prevents concurrent writers,
/// including across restarts or data-pathname replacement attempts.
pub struct FsDurablePoisonAndSessionJournal {
    path: PathBuf,
    lock_path: PathBuf,
    lock_file: File,
    file: File,
    parent: File,
    lock_id: (u64, u64),
    data_id: (u64, u64),
    lock_seal: [u8; LOCK_HEADER_BYTES],
    data_seal: [u8; 16],
    key: [u8; 32],
    session: [u8; 32],
    generation: u64,
    state: u8,
    tag: [u8; 32],
    failed: bool,
}

impl core::fmt::Debug for FsDurablePoisonAndSessionJournal {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("FsDurablePoisonAndSessionJournal([REDACTED])")
    }
}

impl Drop for FsDurablePoisonAndSessionJournal {
    fn drop(&mut self) {
        self.key.fill(0);
        core::hint::black_box(&mut self.key);
    }
}

impl FsDurablePoisonAndSessionJournal {
    pub fn open(
        path: impl AsRef<Path>,
        key: [u8; 32],
        session: [u8; 32],
        mode: JournalOpenMode,
    ) -> Result<Self, NodeError> {
        let path = path.as_ref().to_path_buf();
        let lock_path = lock_path_for(&path);
        let parent_path = path
            .parent()
            .filter(|p| !p.as_os_str().is_empty())
            .unwrap_or(Path::new("."));
        let parent = File::open(parent_path).map_err(|_| NodeError::Journal)?;

        match mode {
            JournalOpenMode::CreateNew => {
                if fs::symlink_metadata(&path).is_ok() || fs::symlink_metadata(&lock_path).is_ok() {
                    return Err(NodeError::Journal);
                }
            }
            JournalOpenMode::RecoverExisting => {
                if check_regular_if_present(&path)?.is_none()
                    || check_regular_if_present(&lock_path)?.is_none()
                {
                    return Err(NodeError::Journal);
                }
            }
        }

        let mut lock_opts = nofollow_options()?;
        lock_opts.read(true).write(true);
        if mode == JournalOpenMode::CreateNew {
            lock_opts.create_new(true);
        }
        let mut lock_file = lock_opts.open(&lock_path).map_err(|_| NodeError::Journal)?;
        lock_file.try_lock().map_err(|_| NodeError::Journal)?;
        let lock_meta = lock_file.metadata().map_err(|_| NodeError::Journal)?;
        let lock_id = regular_dev_ino(&lock_meta)?;

        let mut lock_seal = [0u8; LOCK_HEADER_BYTES];
        match mode {
            JournalOpenMode::CreateNew => {
                let nonce = fill_lock_nonce(&key, &session, lock_id.0, lock_id.1)?;
                lock_seal[..8].copy_from_slice(LOCK_MAGIC);
                lock_seal[8..16].copy_from_slice(&lock_id.0.to_be_bytes());
                lock_seal[16..24].copy_from_slice(&lock_id.1.to_be_bytes());
                lock_seal[24..48].copy_from_slice(&nonce);
                lock_file
                    .write_all(&lock_seal)
                    .map_err(|_| NodeError::Journal)?;
                lock_file.sync_all().map_err(|_| NodeError::Journal)?;
                parent.sync_all().map_err(|_| NodeError::Journal)?;
            }
            JournalOpenMode::RecoverExisting => {
                if lock_meta.len() != LOCK_HEADER_BYTES as u64 {
                    return Err(NodeError::Journal);
                }
                lock_file
                    .read_exact(&mut lock_seal)
                    .map_err(|_| NodeError::Journal)?;
                let stored_dev = u64::from_be_bytes(core::array::from_fn(|i| lock_seal[8 + i]));
                let stored_ino = u64::from_be_bytes(core::array::from_fn(|i| lock_seal[16 + i]));
                if &lock_seal[..8] != LOCK_MAGIC || (stored_dev, stored_ino) != lock_id {
                    return Err(NodeError::Journal);
                }
            }
        }

        let mut data_opts = nofollow_options()?;
        data_opts.read(true).write(true);
        if mode == JournalOpenMode::CreateNew {
            data_opts.create_new(true);
        }
        let file = data_opts.open(&path).map_err(|_| NodeError::Journal)?;
        file.try_lock().map_err(|_| NodeError::Journal)?;
        let data_meta = file.metadata().map_err(|_| NodeError::Journal)?;
        let data_id = regular_dev_ino(&data_meta)?;
        let mut data_seal = [0u8; 16];
        data_seal[..8].copy_from_slice(&data_id.0.to_be_bytes());
        data_seal[8..16].copy_from_slice(&data_id.1.to_be_bytes());

        let mut journal = Self {
            path,
            lock_path,
            lock_file,
            file,
            parent,
            lock_id,
            data_id,
            lock_seal,
            data_seal,
            key,
            session,
            generation: 0,
            state: STATE_ALLOCATED,
            tag: [0; 32],
            failed: false,
        };
        journal.verify_live_files()?;

        match mode {
            JournalOpenMode::CreateNew => journal.persist(0, session, STATE_ALLOCATED)?,
            JournalOpenMode::RecoverExisting => {
                let length = data_meta.len();
                if length == 0 || !length.is_multiple_of(RECORD_BYTES as u64) {
                    return Err(NodeError::Journal);
                }
                let mut seen_sessions: std::vec::Vec<[u8; 32]> = std::vec::Vec::new();
                for index in 0..length / RECORD_BYTES as u64 {
                    let mut record = [0u8; RECORD_BYTES];
                    journal
                        .file
                        .read_exact(&mut record)
                        .map_err(|_| NodeError::Journal)?;
                    let generation = u64::from_be_bytes(core::array::from_fn(|i| record[i]));
                    let id: [u8; 32] = core::array::from_fn(|i| record[8 + i]);
                    let state = record[40];
                    let tag = core::array::from_fn(|i| record[41 + i]);
                    if state > STATE_CONSUMED
                        || !mac32_verify(
                            &journal.key,
                            DOMAIN,
                            &[
                                &journal.lock_seal,
                                &journal.data_seal,
                                &journal.tag,
                                &record[..41],
                            ],
                            &tag,
                        )
                    {
                        return Err(NodeError::Journal);
                    }
                    let valid = if index == 0 {
                        seen_sessions.push(id);
                        generation == 0 && state == STATE_ALLOCATED
                    } else if generation == journal.generation {
                        id == journal.session
                            && matches!(
                                (journal.state, state),
                                (STATE_ALLOCATED, STATE_CONSUMED)
                                    | (STATE_ALLOCATED, STATE_POISONED)
                                    | (STATE_CONSUMED, STATE_POISONED)
                            )
                    } else if journal.generation.checked_add(1) == Some(generation)
                        && state == STATE_ALLOCATED
                        && !seen_sessions.contains(&id)
                    {
                        seen_sessions.push(id);
                        true
                    } else {
                        false
                    };
                    if !valid {
                        return Err(NodeError::Journal);
                    }
                    journal.generation = generation;
                    journal.session = id;
                    journal.state = state;
                    journal.tag = tag;
                }
                if journal.session != session {
                    return Err(NodeError::Journal);
                }
            }
        }
        journal.file.sync_all().map_err(|_| NodeError::Journal)?;
        journal.parent.sync_all().map_err(|_| NodeError::Journal)?;
        Ok(journal)
    }

    pub fn session_generation(&self) -> u64 {
        self.generation
    }

    /// True if the active session has already been durably reserved by an MPC party instance.
    pub fn is_session_consumed(&self, session: &[u8; 32]) -> bool {
        self.failed
            || self.verify_live_files().is_err()
            || *session != self.session
            || self.state != STATE_ALLOCATED
    }

    fn verify_live_files(&self) -> Result<(), NodeError> {
        let live_data = fs::symlink_metadata(&self.path).map_err(|_| NodeError::Journal)?;
        let held_data = self.file.metadata().map_err(|_| NodeError::Journal)?;
        if regular_dev_ino(&live_data)? != self.data_id
            || regular_dev_ino(&held_data)? != self.data_id
            || live_data.len() != held_data.len()
        {
            return Err(NodeError::Journal);
        }
        let live_lock = fs::symlink_metadata(&self.lock_path).map_err(|_| NodeError::Journal)?;
        let held_lock = self.lock_file.metadata().map_err(|_| NodeError::Journal)?;
        if regular_dev_ino(&live_lock)? != self.lock_id
            || regular_dev_ino(&held_lock)? != self.lock_id
            || held_lock.len() != LOCK_HEADER_BYTES as u64
        {
            return Err(NodeError::Journal);
        }
        let mut header = [0u8; LOCK_HEADER_BYTES];
        let mut verify_lock = nofollow_options()?
            .read(true)
            .open(&self.lock_path)
            .map_err(|_| NodeError::Journal)?;
        verify_lock
            .read_exact(&mut header)
            .map_err(|_| NodeError::Journal)?;
        if !qsag_core::wipe::ct_eq_bytes(&header, &self.lock_seal) {
            return Err(NodeError::Journal);
        }
        Ok(())
    }

    /// Start fresh protocol counters only after durably advancing the generation.
    /// `session` must be a fresh cryptographic session identifier, never reused.
    pub fn advance_session(&mut self, session: [u8; 32]) -> Result<(), NodeError> {
        if self.failed || session == self.session {
            return Err(NodeError::Journal);
        }
        if self.verify_live_files().is_err() {
            self.failed = true;
            return Err(NodeError::Journal);
        }
        // Reject reuse of any earlier session identifier across the entire lineage.
        self.file.rewind().map_err(|_| {
            self.failed = true;
            NodeError::Journal
        })?;
        let length = self
            .file
            .metadata()
            .map_err(|_| {
                self.failed = true;
                NodeError::Journal
            })?
            .len();
        if !length.is_multiple_of(RECORD_BYTES as u64) {
            self.failed = true;
            return Err(NodeError::Journal);
        }
        for _ in 0..length / RECORD_BYTES as u64 {
            let mut record = [0u8; RECORD_BYTES];
            self.file.read_exact(&mut record).map_err(|_| {
                self.failed = true;
                NodeError::Journal
            })?;
            if record[8..40] == session {
                return Err(NodeError::Journal);
            }
        }
        let generation = self.generation.checked_add(1).ok_or(NodeError::Journal)?;
        self.persist(generation, session, STATE_ALLOCATED)
    }

    fn persist(
        &mut self,
        generation: u64,
        session: [u8; 32],
        state: u8,
    ) -> Result<(), NodeError> {
        if self.failed {
            return Err(NodeError::Journal);
        }
        // Any failed, partial, or inode-swapped append permanently disables this handle.
        self.failed = true;
        self.verify_live_files()?;
        let mut record = [0u8; RECORD_BYTES];
        record[..8].copy_from_slice(&generation.to_be_bytes());
        record[8..40].copy_from_slice(&session);
        record[40] = state;
        let tag = mac32(
            &self.key,
            DOMAIN,
            &[
                &self.lock_seal,
                &self.data_seal,
                &self.tag,
                &record[..41],
            ],
        );
        record[41..].copy_from_slice(&tag);
        self.file
            .seek(SeekFrom::End(0))
            .map_err(|_| NodeError::Journal)?;
        self.file
            .write_all(&record)
            .map_err(|_| NodeError::Journal)?;
        self.file.sync_all().map_err(|_| NodeError::Journal)?;
        self.parent.sync_all().map_err(|_| NodeError::Journal)?;
        self.verify_live_files()?;
        self.generation = generation;
        self.session = session;
        self.state = state;
        self.tag = tag;
        self.failed = false;
        Ok(())
    }
}

impl PoisonJournal for FsDurablePoisonAndSessionJournal {
    fn reserve_session(&mut self, session: &[u8; 32]) -> Result<(), NodeError> {
        if self.failed || *session != self.session || self.state != STATE_ALLOCATED {
            return Err(NodeError::Journal);
        }
        self.persist(self.generation, *session, STATE_CONSUMED)
    }

    fn mark_poisoned(&mut self, session: &[u8; 32]) -> Result<(), NodeError> {
        if self.failed || *session != self.session {
            return Err(NodeError::Journal);
        }
        if self.state == STATE_POISONED {
            self.verify_live_files().inspect_err(|_| {
                self.failed = true;
            })?;
            return Ok(());
        }
        self.persist(self.generation, *session, STATE_POISONED)
    }

    fn is_poisoned(&self, session: &[u8; 32]) -> bool {
        self.failed
            || *session != self.session
            || self.state == STATE_POISONED
            || self.verify_live_files().is_err()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::party_node::{IsolatedRss256Party, deal_rss256_keys};
    use crate::wire_channel::InMemoryWireMesh;

    fn unique_dir(tag: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(std::format!(
            "qsag-poison-{tag}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    #[test]
    fn durable_recovery_and_fail_closed() {
        let dir = unique_dir("recovery");
        let path = dir.join("party0.journal");
        let key = [17; 32];
        let session = [23; 32];
        assert!(
            FsDurablePoisonAndSessionJournal::open(
                &path,
                key,
                session,
                JournalOpenMode::RecoverExisting
            )
            .is_err()
        );
        let mut j =
            FsDurablePoisonAndSessionJournal::open(&path, key, session, JournalOpenMode::CreateNew)
                .unwrap();
        assert!(
            FsDurablePoisonAndSessionJournal::open(&path, key, session, JournalOpenMode::CreateNew)
                .is_err()
        );
        assert!(
            FsDurablePoisonAndSessionJournal::open(
                &path,
                key,
                session,
                JournalOpenMode::RecoverExisting
            )
            .is_err()
        );
        j.mark_poisoned(&session).unwrap();
        drop(j);
        assert!(
            FsDurablePoisonAndSessionJournal::open(
                &path,
                [18; 32],
                session,
                JournalOpenMode::RecoverExisting
            )
            .is_err()
        );
        let mut j = FsDurablePoisonAndSessionJournal::open(
            &path,
            key,
            session,
            JournalOpenMode::RecoverExisting,
        )
        .unwrap();
        assert!(j.is_poisoned(&session));
        j.advance_session([24; 32]).unwrap();
        assert!(j.is_poisoned(&session));
        assert_eq!(j.advance_session(session), Err(NodeError::Journal));
        drop(j);
        let j = FsDurablePoisonAndSessionJournal::open(
            &path,
            key,
            [24; 32],
            JournalOpenMode::RecoverExisting,
        )
        .unwrap();
        assert_eq!(j.session_generation(), 1);
        assert!(!j.is_poisoned(&[24; 32]));
        drop(j);
        // Simulate a crash during append: recovery must not silently discard a tail.
        OpenOptions::new()
            .append(true)
            .open(&path)
            .unwrap()
            .write_all(&[0; 7])
            .unwrap();
        assert!(
            FsDurablePoisonAndSessionJournal::open(
                &path,
                key,
                [24; 32],
                JournalOpenMode::RecoverExisting
            )
            .is_err()
        );
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn clean_session_restart_without_advance_is_refused_preventing_mask_reuse() {
        let dir = unique_dir("no-mask-reuse");
        let path = dir.join("party0.journal");
        let key = [0x42; 32];
        let session_a = [0xA1; 32];
        let session_b = [0xB2; 32];
        let keys = deal_rss256_keys(&[0x99; 32]);

        // Process 1 creates the journal and constructs IsolatedRss256Party for `session_a`.
        // Construction durably reserves `session_a` before any wave-0 pad or coin is derived,
        // then crashes cleanly before recording poison.
        {
            let (mut endpoints, _) = InMemoryWireMesh::connect(3, session_a);
            let journal = FsDurablePoisonAndSessionJournal::open(
                &path,
                key,
                session_a,
                JournalOpenMode::CreateNew,
            )
            .unwrap();
            let _party = IsolatedRss256Party::new(
                session_a,
                keys[0].clone(),
                endpoints.remove(0),
                journal,
            )
            .unwrap();
        }

        // Process 2 recovers the clean journal after crash and attempts to construct a party
        // with the same `session_a`: MUST fail closed so wave-0 pads/coins never repeat!
        let recovered = FsDurablePoisonAndSessionJournal::open(
            &path,
            key,
            session_a,
            JournalOpenMode::RecoverExisting,
        )
        .unwrap();
        assert!(!recovered.is_poisoned(&session_a));
        assert!(recovered.is_session_consumed(&session_a));
        {
            let (mut endpoints, _) = InMemoryWireMesh::connect(3, session_a);
            let retry = IsolatedRss256Party::new(
                session_a,
                keys[0].clone(),
                endpoints.remove(0),
                recovered,
            );
            assert!(matches!(retry, Err(NodeError::Journal)));
        }

        // Advancing to a fresh `session_b` durably allocates a new namespace that succeeds once.
        let mut recovered = FsDurablePoisonAndSessionJournal::open(
            &path,
            key,
            session_a,
            JournalOpenMode::RecoverExisting,
        )
        .unwrap();
        recovered.advance_session(session_b).unwrap();
        let (mut endpoints, _) = InMemoryWireMesh::connect(3, session_b);
        let party_b = IsolatedRss256Party::new(
            session_b,
            keys[0].clone(),
            endpoints.remove(0),
            recovered,
        )
        .unwrap();
        assert!(!party_b.is_poisoned());
        drop(party_b);
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn live_pathname_replacement_and_sidecar_inode_swap_fail_closed() {
        let dir = unique_dir("pathname-swap");
        let path = dir.join("party0.journal");
        let lock_path = lock_path_for(&path);
        let key = [0x55; 32];
        let session = [0x77; 32];

        let mut live =
            FsDurablePoisonAndSessionJournal::open(&path, key, session, JournalOpenMode::CreateNew)
                .unwrap();

        // Snapshot the authenticated clean journal file and rename a replacement inode over `path`
        // while `live` still holds the open descriptor and sidecar lock.
        let snapshot = fs::read(&path).unwrap();
        let staged_copy = dir.join("party0.journal.copy");
        fs::write(&staged_copy, &snapshot).unwrap();
        fs::rename(&staged_copy, &path).unwrap();

        // 1. A competing process cannot acquire ownership because `<path>.lock` stays locked,
        //    and even after `live` drops, the replacement inode fails `data_seal` MAC verification.
        assert!(
            FsDurablePoisonAndSessionJournal::open(
                &path,
                key,
                session,
                JournalOpenMode::RecoverExisting
            )
            .is_err()
        );
        // 2. The original handle detects pathname inode divergence immediately and fails closed!
        assert!(live.is_poisoned(&session));
        assert_eq!(live.mark_poisoned(&session), Err(NodeError::Journal));
        drop(live);

        // Even with the lock released, recovering the renamed inode fails `data_seal` authentication.
        assert!(
            FsDurablePoisonAndSessionJournal::open(
                &path,
                key,
                session,
                JournalOpenMode::RecoverExisting
            )
            .is_err()
        );

        // Now provision a fresh lineage and simulate offline sidecar replacement preserving the
        // 24-byte nonce while rewriting `(lock_dev, lock_ino)` to match the new sidecar inode.
        let path2 = dir.join("party1.journal");
        let lock_path2 = lock_path_for(&path2);
        let j2 = FsDurablePoisonAndSessionJournal::open(
            &path2,
            key,
            session,
            JournalOpenMode::CreateNew,
        )
        .unwrap();
        drop(j2);
        let orig_lock = fs::read(&lock_path2).unwrap();
        let fake_lock_tmp = dir.join("party1.journal.lock.fake");
        fs::write(&fake_lock_tmp, &orig_lock).unwrap();
        let (new_dev, new_ino) = regular_dev_ino(&fs::symlink_metadata(&fake_lock_tmp).unwrap()).unwrap();
        let mut forged_lock = orig_lock;
        forged_lock[8..16].copy_from_slice(&new_dev.to_be_bytes());
        forged_lock[16..24].copy_from_slice(&new_ino.to_be_bytes());
        fs::write(&fake_lock_tmp, &forged_lock).unwrap();
        fs::rename(&fake_lock_tmp, &lock_path2).unwrap();
        let _ = lock_path;

        // Opening fails closed because every record MAC binds the original `(lock_dev, lock_ino)`!
        assert!(
            FsDurablePoisonAndSessionJournal::open(
                &path2,
                key,
                session,
                JournalOpenMode::RecoverExisting
            )
            .is_err()
        );
        fs::remove_dir_all(dir).unwrap();
    }
}
