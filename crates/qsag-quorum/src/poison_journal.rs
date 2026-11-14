//! Authenticated append-only session journal. One locked file owns one session lineage.
//! Recovery fails closed on missing, partial, reordered or unauthenticated records.
//! Detecting replacement by an older *complete* journal requires an external generation
//! anchor; a local file alone cannot detect rollback of the entire filesystem.

use crate::hash::{mac32, mac32_verify};
use crate::party_node::{NodeError, PoisonJournal};
use std::fs::{File, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::Path;

const DOMAIN: &[u8] = b"QSAG.POISON.JOURNAL/v1";
const RECORD_BYTES: usize = 73;

#[derive(Clone, Copy, Debug)]
pub enum JournalOpenMode {
    /// Create a new lineage, refusing to overwrite any existing file.
    CreateNew,
    /// Require and authenticate an existing lineage.
    RecoverExisting,
}

/// A synchronous durable journal. Keep the MAC key outside the journal directory.
/// An exclusive OS file lock prevents concurrent writers, including across restarts.
pub struct FsDurablePoisonAndSessionJournal {
    file: File,
    parent: File,
    key: [u8; 32],
    session: [u8; 32],
    generation: u64,
    poisoned: bool,
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
        let path = path.as_ref();
        let parent_path = path
            .parent()
            .filter(|p| !p.as_os_str().is_empty())
            .unwrap_or(Path::new("."));
        let parent = File::open(parent_path).map_err(|_| NodeError::Journal)?;
        let mut options = OpenOptions::new();
        options.read(true).write(true);
        if matches!(mode, JournalOpenMode::CreateNew) {
            options.create_new(true);
        }
        let file = options.open(path).map_err(|_| NodeError::Journal)?;
        file.try_lock().map_err(|_| NodeError::Journal)?;
        let mut journal = Self {
            file,
            parent,
            key,
            session,
            generation: 0,
            poisoned: false,
            tag: [0; 32],
            failed: false,
        };
        match mode {
            JournalOpenMode::CreateNew => journal.persist(0, session, false)?,
            JournalOpenMode::RecoverExisting => {
                let length = journal
                    .file
                    .metadata()
                    .map_err(|_| NodeError::Journal)?
                    .len();
                if length == 0 || !length.is_multiple_of(RECORD_BYTES as u64) {
                    return Err(NodeError::Journal);
                }
                for index in 0..length / RECORD_BYTES as u64 {
                    let mut record = [0u8; RECORD_BYTES];
                    journal
                        .file
                        .read_exact(&mut record)
                        .map_err(|_| NodeError::Journal)?;
                    let generation = u64::from_be_bytes(core::array::from_fn(|i| record[i]));
                    let id: [u8; 32] = core::array::from_fn(|i| record[8 + i]);
                    let tag = core::array::from_fn(|i| record[41 + i]);
                    if record[40] > 1
                        || !mac32_verify(&journal.key, DOMAIN, &[&journal.tag, &record[..41]], &tag)
                    {
                        return Err(NodeError::Journal);
                    }
                    let poisoned = record[40] == 1;
                    let valid = if index == 0 {
                        generation == 0 && !poisoned
                    } else if generation == journal.generation {
                        id == journal.session && !journal.poisoned && poisoned
                    } else {
                        journal.generation.checked_add(1) == Some(generation)
                            && id != journal.session
                            && !poisoned
                    };
                    if !valid {
                        return Err(NodeError::Journal);
                    }
                    journal.generation = generation;
                    journal.session = id;
                    journal.poisoned = poisoned;
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

    /// Start fresh protocol counters only after durably advancing the generation.
    /// `session` must be a fresh cryptographic session identifier, never reused.
    pub fn advance_session(&mut self, session: [u8; 32]) -> Result<(), NodeError> {
        if self.failed || session == self.session {
            return Err(NodeError::Journal);
        }
        // Reject reuse of any earlier session identifier, not only the latest one.
        self.file.rewind().map_err(|_| NodeError::Journal)?;
        let length = self.file.metadata().map_err(|_| NodeError::Journal)?.len();
        for _ in 0..length / RECORD_BYTES as u64 {
            let mut record = [0u8; RECORD_BYTES];
            self.file
                .read_exact(&mut record)
                .map_err(|_| NodeError::Journal)?;
            if record[8..40] == session {
                return Err(NodeError::Journal);
            }
        }
        let generation = self.generation.checked_add(1).ok_or(NodeError::Journal)?;
        self.persist(generation, session, false)
    }

    fn persist(
        &mut self,
        generation: u64,
        session: [u8; 32],
        poisoned: bool,
    ) -> Result<(), NodeError> {
        if self.failed {
            return Err(NodeError::Journal);
        }
        // Any failed or partial append permanently disables this handle.
        self.failed = true;
        let mut record = [0u8; RECORD_BYTES];
        record[..8].copy_from_slice(&generation.to_be_bytes());
        record[8..40].copy_from_slice(&session);
        record[40] = u8::from(poisoned);
        let tag = mac32(&self.key, DOMAIN, &[&self.tag, &record[..41]]);
        record[41..].copy_from_slice(&tag);
        self.file
            .seek(SeekFrom::End(0))
            .map_err(|_| NodeError::Journal)?;
        self.file
            .write_all(&record)
            .map_err(|_| NodeError::Journal)?;
        self.file.sync_all().map_err(|_| NodeError::Journal)?;
        self.parent.sync_all().map_err(|_| NodeError::Journal)?;
        self.generation = generation;
        self.session = session;
        self.poisoned = poisoned;
        self.tag = tag;
        self.failed = false;
        Ok(())
    }
}

impl PoisonJournal for FsDurablePoisonAndSessionJournal {
    fn mark_poisoned(&mut self, session: &[u8; 32]) -> Result<(), NodeError> {
        if self.failed || *session != self.session {
            return Err(NodeError::Journal);
        }
        if self.poisoned {
            return Ok(());
        }
        self.poisoned = true;
        self.persist(self.generation, *session, true)
    }

    fn is_poisoned(&self, session: &[u8; 32]) -> bool {
        self.failed || *session != self.session || self.poisoned
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn durable_recovery_and_fail_closed() {
        let path = std::env::temp_dir().join(std::format!(
            "qsag-poison-{}-{:?}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
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
        std::fs::remove_file(path).unwrap();
    }
}
