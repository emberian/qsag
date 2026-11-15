//! Production durable custody anchors for [`qsag_core::LedgerCheckpoint`],
//! [`FsSeedBurnTracker`], and [`FsFirstSignedLedger`].
//!
//! `qsag_core::durable_ledger::Ledger` protects two-slot snapshots against torn writes and
//! requires callers to retain [`LedgerCheckpoint`] in an independent rollback domain before
//! releasing signatures or expanded PCG correlations, supplying that retained checkpoint on
//! every reload. This module wires that checkpoint lifecycle end-to-end with:
//!
//! * [`FsLedgerCheckpointAnchor`] — an OS-locked, MAC-authenticated monotonic anchor record
//!   stored outside the ledger's `.slot_a` / `.slot_b` directory;
//! * [`AnchoredSeedBurnTracker`] — combines [`FsCeremonyJournal`], [`FsSeedBurnTracker`], and
//!   [`FsLedgerCheckpointAnchor`] so every PCG seed burn ratchets and `fsync`s the anchor before
//!   expanded material is returned;
//! * [`AnchoredFirstSignedCustody`] — combines [`FsCeremonyJournal`], [`FsFirstSignedLedger`],
//!   and [`FsLedgerCheckpointAnchor`] so every Baggy `FirstSignedLedger` update ratchets and
//!   `fsync`s the anchor before any signature is released.

use std::io;
use std::path::{Path, PathBuf};

use qsag_asm::durable::LockedRecord;
use qsag_core::LedgerCheckpoint;
use qsag_core::baggy::{
    BaggyError, BaggyKeyBinding, BaggyParams, BaggyPublicKey, BaggySig, FirstSignedError,
    FirstSignedLedger, FirstSignedRecord, FsFirstSignedLedger, WaistbandCache, baggy_msg_digest,
    baggy_sign_mpc,
};
use qsag_core::ceremony_journal::{CeremonyReservation, FsCeremonyJournal};
use qsag_core::pcg_dense::{
    DensePcgExpandedVault, DensePcgPartySeed, FsSeedBurnTracker, SeedBurnError, SeedBurnTracker,
};
use qsag_core::preprocessing::PreprocessError;
use qsag_core::rss256::Rss256Engine;
use qsag_core::wipe::{ct_eq_bytes32, wipe_bytes32};

use crate::hash::{SecretKey, mac32, mac32_verify};

const ANCHOR_MAGIC: &[u8; 8] = b"QSAGCKP1";
const ANCHOR_MAC_DOMAIN: &[u8] = b"QSAG.QUORUM.CHECKPOINT.ANCHOR.V1";
const KEY_DERIVE_DOMAIN: &[u8] = b"QSAG.QUORUM.ANCHORED_CUSTODY.KEY.V1";

fn journal_anchor_path(anchor: &Path) -> PathBuf {
    let mut path = anchor.as_os_str().to_os_string();
    path.push(".ceremony");
    path.into()
}

fn invalid_anchor(msg: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, msg)
}

fn derive_subkey(master_key: &[u8; 32], key_id: &[u8; 32], purpose: &[u8]) -> [u8; 32] {
    mac32(master_key, KEY_DERIVE_DOMAIN, &[key_id, purpose])
}

fn anchor_lock_inode(path: &Path) -> io::Result<[u8; 16]> {
    let mut os = path.as_os_str().to_os_string();
    os.push(".lock");
    let meta = std::fs::symlink_metadata(PathBuf::from(os))?;
    if !meta.is_file() || meta.file_type().is_symlink() {
        return Err(invalid_anchor("invalid checkpoint anchor lock sidecar"));
    }
    let mut id = [0u8; 16];
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        id[..8].copy_from_slice(&meta.dev().to_le_bytes());
        id[8..].copy_from_slice(&meta.ino().to_le_bytes());
    }
    Ok(id)
}

/// Independent OS-locked, MAC-authenticated monotonic [`LedgerCheckpoint`] anchor.
///
/// Place `path` in an independent directory / mount or hardware-backed filesystem from the
/// ledger's `.slot_a` / `.slot_b` files so rolling back the ledger directory fails closed on
/// [`AnchoredSeedBurnTracker::open_existing`] and [`AnchoredFirstSignedCustody::open_existing`].
pub struct FsLedgerCheckpointAnchor {
    path: PathBuf,
    lock_id: [u8; 16],
    record: LockedRecord,
    key: [u8; 32],
    domain: &'static [u8],
    current: LedgerCheckpoint,
    poisoned: bool,
}

impl Drop for FsLedgerCheckpointAnchor {
    fn drop(&mut self) {
        wipe_bytes32(&mut self.key);
    }
}

impl FsLedgerCheckpointAnchor {
    /// Create and `fsync` a fresh checkpoint anchor initialized to `initial`.
    pub fn provision_genesis(
        path: impl Into<PathBuf>,
        key: [u8; 32],
        domain: &'static [u8],
        initial: LedgerCheckpoint,
    ) -> io::Result<Self> {
        let mut key = SecretKey(key);
        let path = path.into();
        let record = LockedRecord::create_new(&path)?;
        let lock_id = anchor_lock_inode(&path)?;
        let derived = mac32(
            &key,
            ANCHOR_MAC_DOMAIN,
            &[&lock_id, &record.lock_seal(), domain],
        );
        wipe_bytes32(&mut key);
        let anchor = Self {
            path,
            lock_id,
            record,
            key: derived,
            domain,
            current: initial,
            poisoned: false,
        };
        anchor.record.replace(&anchor.encode(&initial))?;
        Ok(anchor)
    }

    /// Recover and authenticate an existing checkpoint anchor.
    pub fn open_existing(
        path: impl Into<PathBuf>,
        key: [u8; 32],
        domain: &'static [u8],
    ) -> io::Result<Self> {
        let mut key = SecretKey(key);
        let path = path.into();
        let record = LockedRecord::open_existing(&path)?;
        let lock_id = anchor_lock_inode(&path)?;
        let derived = mac32(
            &key,
            ANCHOR_MAC_DOMAIN,
            &[&lock_id, &record.lock_seal(), domain],
        );
        wipe_bytes32(&mut key);
        let mut anchor = Self {
            path,
            lock_id,
            record,
            key: derived,
            domain,
            current: LedgerCheckpoint {
                generation: 0,
                tag: [0u8; 32],
            },
            poisoned: false,
        };
        let raw = anchor.record.read()?;
        anchor.current = anchor.decode(&raw)?;
        Ok(anchor)
    }

    /// Retained minimum checkpoint enforced on ledger recovery.
    pub const fn checkpoint(&self) -> LedgerCheckpoint {
        self.current
    }

    /// Monotonically advance and `fsync` the retained checkpoint.
    ///
    /// Rejects any `next.generation < self.current.generation` and any tag mismatch at the
    /// same generation; any I/O or rollback error permanently poisons this handle.
    pub fn ratchet_to(&mut self, next: LedgerCheckpoint) -> io::Result<()> {
        if self.poisoned {
            return Err(io::Error::other("checkpoint anchor handle is poisoned"));
        }
        if anchor_lock_inode(&self.path).ok() != Some(self.lock_id) {
            self.poisoned = true;
            return Err(invalid_anchor("checkpoint anchor lock sidecar replaced"));
        }
        let meta = std::fs::symlink_metadata(&self.path)?;
        if meta.file_type().is_symlink() || !meta.is_file() {
            self.poisoned = true;
            return Err(invalid_anchor(
                "checkpoint anchor path is not a regular file",
            ));
        }
        let live_raw = match self.record.read() {
            Ok(bytes) => bytes,
            Err(e) => {
                self.poisoned = true;
                return Err(e);
            }
        };
        let on_disk = match self.decode(&live_raw) {
            Ok(ckpt) => ckpt,
            Err(e) => {
                self.poisoned = true;
                return Err(e);
            }
        };
        if on_disk.generation != self.current.generation
            || !ct_eq_bytes32(&on_disk.tag, &self.current.tag)
        {
            self.poisoned = true;
            return Err(invalid_anchor(
                "on-disk checkpoint anchor diverged from handle",
            ));
        }
        if next.generation < self.current.generation {
            self.poisoned = true;
            return Err(invalid_anchor(
                "ledger checkpoint generation rollback refused",
            ));
        }
        if next.generation == self.current.generation
            && !ct_eq_bytes32(&next.tag, &self.current.tag)
        {
            self.poisoned = true;
            return Err(invalid_anchor(
                "ledger checkpoint tag mismatch at equal generation",
            ));
        }
        if next.generation == self.current.generation {
            return Ok(());
        }
        let encoded = self.encode(&next);
        if let Err(e) = self.record.replace(&encoded) {
            self.poisoned = true;
            return Err(e);
        }
        self.current = next;
        Ok(())
    }

    fn encode(&self, ckpt: &LedgerCheckpoint) -> Vec<u8> {
        let domain_len = (self.domain.len() as u16).to_be_bytes();
        let mut body = Vec::with_capacity(8 + 2 + self.domain.len() + 8 + 32 + 32);
        body.extend_from_slice(ANCHOR_MAGIC);
        body.extend_from_slice(&domain_len);
        body.extend_from_slice(self.domain);
        body.extend_from_slice(&ckpt.generation.to_be_bytes());
        body.extend_from_slice(&ckpt.tag);
        let tag = mac32(
            &self.key,
            ANCHOR_MAC_DOMAIN,
            &[&self.record.lock_seal(), &body],
        );
        body.extend_from_slice(&tag);
        body
    }

    fn decode(&self, raw: &[u8]) -> io::Result<LedgerCheckpoint> {
        let expected_len = 8 + 2 + self.domain.len() + 8 + 32 + 32;
        if raw.len() != expected_len {
            return Err(invalid_anchor("invalid checkpoint anchor length"));
        }
        let (body, tag_slice) = raw.split_at(expected_len - 32);
        let tag: [u8; 32] = tag_slice
            .try_into()
            .map_err(|_| invalid_anchor("invalid checkpoint anchor tag"))?;
        if !mac32_verify(
            &self.key,
            ANCHOR_MAC_DOMAIN,
            &[&self.record.lock_seal(), body],
            &tag,
        ) {
            return Err(invalid_anchor("checkpoint anchor MAC verification failed"));
        }
        if &body[..8] != ANCHOR_MAGIC {
            return Err(invalid_anchor("invalid checkpoint anchor magic"));
        }
        let domain_len = u16::from_be_bytes([body[8], body[9]]) as usize;
        if domain_len != self.domain.len() || &body[10..10 + domain_len] != self.domain {
            return Err(invalid_anchor("checkpoint anchor domain mismatch"));
        }
        let cursor = 10 + domain_len;
        let generation = u64::from_be_bytes(
            body[cursor..cursor + 8]
                .try_into()
                .map_err(|_| invalid_anchor("invalid generation"))?,
        );
        let ckpt_tag: [u8; 32] = body[cursor + 8..cursor + 40]
            .try_into()
            .map_err(|_| invalid_anchor("invalid checkpoint tag"))?;
        Ok(LedgerCheckpoint {
            generation,
            tag: ckpt_tag,
        })
    }
}

/// Errors from [`AnchoredSeedBurnTracker`] operations.
#[derive(Debug)]
pub enum AnchoredSeedBurnError {
    Io(io::Error),
    Burn(SeedBurnError),
    Preprocess(PreprocessError),
}

/// Production single-use PCG seed burn custody backed by [`FsCeremonyJournal`],
/// [`FsSeedBurnTracker`], and an independent [`FsLedgerCheckpointAnchor`].
pub struct AnchoredSeedBurnTracker {
    key_id: [u8; 32],
    next_cursor: u64,
    journal: FsCeremonyJournal,
    burns: FsSeedBurnTracker,
    anchor: FsLedgerCheckpointAnchor,
}

impl AnchoredSeedBurnTracker {
    /// Provision fresh journal, two-slot seed-burn ledger, and retained checkpoint anchor.
    pub fn provision_genesis(
        ledger_path: impl AsRef<Path>,
        journal_path: impl AsRef<Path>,
        anchor_path: impl AsRef<Path>,
        key_id: [u8; 32],
        master_key: [u8; 32],
    ) -> io::Result<Self> {
        let mut master_key = SecretKey(master_key);
        let journal_key = SecretKey(derive_subkey(&master_key, &key_id, b"seedburn.journal"));
        let ledger_key = SecretKey(derive_subkey(&master_key, &key_id, b"seedburn.ledger"));
        let anchor_key = SecretKey(derive_subkey(&master_key, &key_id, b"seedburn.anchor"));
        wipe_bytes32(&mut master_key);

        let journal_anchor = crate::FsDirectoryMonotoneAnchor::create_new(
            journal_anchor_path(anchor_path.as_ref()),
            derive_subkey(&anchor_key, &key_id, b"ceremony.anchor"),
        )?;
        let journal = FsCeremonyJournal::create_new_anchored(
            journal_path.as_ref(),
            key_id,
            journal_key.0,
            Box::new(journal_anchor),
        )?;
        let burns = FsSeedBurnTracker::provision_genesis(ledger_path.as_ref(), ledger_key.0)
            .map_err(|_| io::Error::other("failed to provision FsSeedBurnTracker"))?;
        let initial = burns.checkpoint();
        let anchor = FsLedgerCheckpointAnchor::provision_genesis(
            anchor_path.as_ref(),
            anchor_key.0,
            b"QSAG.SEED_BURN.V1",
            initial,
        )?;
        Ok(Self {
            key_id,
            next_cursor: 1,
            journal,
            burns,
            anchor,
        })
    }

    /// Recover existing seed-burn custody, enforcing the retained [`LedgerCheckpoint`] from
    /// `anchor_path` before admitting the ledger snapshot.
    pub fn open_existing(
        ledger_path: impl AsRef<Path>,
        journal_path: impl AsRef<Path>,
        anchor_path: impl AsRef<Path>,
        key_id: [u8; 32],
        master_key: [u8; 32],
    ) -> io::Result<Self> {
        let mut master_key = SecretKey(master_key);
        let journal_key = SecretKey(derive_subkey(&master_key, &key_id, b"seedburn.journal"));
        let ledger_key = SecretKey(derive_subkey(&master_key, &key_id, b"seedburn.ledger"));
        let anchor_key = SecretKey(derive_subkey(&master_key, &key_id, b"seedburn.anchor"));
        wipe_bytes32(&mut master_key);

        let mut anchor = FsLedgerCheckpointAnchor::open_existing(
            anchor_path.as_ref(),
            anchor_key.0,
            b"QSAG.SEED_BURN.V1",
        )?;
        let retained = anchor.checkpoint();
        let journal_anchor = crate::FsDirectoryMonotoneAnchor::open_existing(
            journal_anchor_path(anchor_path.as_ref()),
            derive_subkey(&anchor_key, &key_id, b"ceremony.anchor"),
        )?;
        let journal = FsCeremonyJournal::open_existing_anchored(
            journal_path.as_ref(),
            key_id,
            journal_key.0,
            Box::new(journal_anchor),
        )?;
        let burns = FsSeedBurnTracker::open_existing(ledger_path.as_ref(), ledger_key.0, retained)
            .map_err(|_| {
                invalid_anchor("seed burn ledger failed retained checkpoint verification")
            })?;
        let recovered = burns.checkpoint();
        // If a prior crash happened after `burns.burn` committed a successor slot and before
        // `anchor.ratchet_to` completed, ratchet the anchor forward before resuming work.
        anchor.ratchet_to(recovered)?;
        let next_cursor = recovered
            .generation
            .max(journal.last_committed().map_or(0, |r| r.seed_burn_cursor))
            .checked_add(1)
            .ok_or_else(|| invalid_anchor("seed burn cursor overflow"))?;
        Ok(Self {
            key_id,
            next_cursor,
            journal,
            burns,
            anchor,
        })
    }

    pub const fn checkpoint(&self) -> LedgerCheckpoint {
        self.anchor.checkpoint()
    }

    pub fn is_burned(&self, seed_id: &[u8; 32]) -> Result<bool, SeedBurnError> {
        self.burns.is_burned(seed_id)
    }

    /// Commit a ceremony reservation, burn `seed_id` in [`FsSeedBurnTracker`], and `fsync`
    /// the updated [`LedgerCheckpoint`] to [`FsLedgerCheckpointAnchor`] before returning.
    pub fn burn_seed_anchored(
        &mut self,
        session_id: [u8; 32],
        seed_id: [u8; 32],
        hedge_generation: u64,
    ) -> Result<LedgerCheckpoint, AnchoredSeedBurnError> {
        if self
            .burns
            .is_burned(&seed_id)
            .map_err(AnchoredSeedBurnError::Burn)?
        {
            return Err(AnchoredSeedBurnError::Burn(SeedBurnError::AlreadyBurned));
        }
        let cursor = self.next_cursor;
        let next_cursor = cursor
            .checked_add(1)
            .ok_or_else(|| AnchoredSeedBurnError::Io(invalid_anchor("cursor exhausted")))?;
        let permit = self
            .journal
            .persist_before_release(CeremonyReservation {
                ceremony_id: session_id,
                key_id: self.key_id,
                epoch_or_codeword: seed_id,
                seed_burn_cursor: cursor,
                hedge_generation,
            })
            .map_err(AnchoredSeedBurnError::Io)?;
        self.next_cursor = next_cursor;
        self.burns
            .authorize_release(&self.journal, permit)
            .map_err(AnchoredSeedBurnError::Burn)?;
        self.burns
            .begin_expansion(&session_id, &seed_id)
            .map_err(AnchoredSeedBurnError::Burn)?;
        self.burns
            .burn(&seed_id)
            .map_err(AnchoredSeedBurnError::Burn)?;
        let ckpt = self.burns.checkpoint();
        self.anchor
            .ratchet_to(ckpt)
            .map_err(AnchoredSeedBurnError::Io)?;
        Ok(ckpt)
    }

    /// Authorize, burn, expand a [`DensePcgPartySeed`], and `fsync` the updated
    /// [`LedgerCheckpoint`] anchor BEFORE releasing [`DensePcgExpandedVault`].
    pub fn expand_party_seed_anchored(
        &mut self,
        seed: DensePcgPartySeed,
        hedge_generation: u64,
    ) -> Result<(DensePcgExpandedVault, LedgerCheckpoint), AnchoredSeedBurnError> {
        let seed_id = seed.seed_id();
        if self
            .burns
            .is_burned(&seed_id)
            .map_err(AnchoredSeedBurnError::Burn)?
        {
            return Err(AnchoredSeedBurnError::Preprocess(
                PreprocessError::PcgSeedAlreadyBurned,
            ));
        }
        let cursor = self.next_cursor;
        let next_cursor = cursor
            .checked_add(1)
            .ok_or_else(|| AnchoredSeedBurnError::Io(invalid_anchor("cursor exhausted")))?;
        let permit = self
            .journal
            .persist_before_release(CeremonyReservation {
                ceremony_id: seed.session_id,
                key_id: self.key_id,
                epoch_or_codeword: seed_id,
                seed_burn_cursor: cursor,
                hedge_generation,
            })
            .map_err(AnchoredSeedBurnError::Io)?;
        self.next_cursor = next_cursor;
        self.burns
            .authorize_release(&self.journal, permit)
            .map_err(AnchoredSeedBurnError::Burn)?;

        let prev_gen = self.anchor.checkpoint().generation;
        match seed.expand_local(&mut self.burns) {
            Ok(vault) => {
                let ckpt = self.burns.checkpoint();
                self.anchor
                    .ratchet_to(ckpt)
                    .map_err(AnchoredSeedBurnError::Io)?;
                Ok((vault, ckpt))
            }
            Err(err) => {
                let ckpt = self.burns.checkpoint();
                if ckpt.generation > prev_gen {
                    self.anchor
                        .ratchet_to(ckpt)
                        .map_err(AnchoredSeedBurnError::Io)?;
                }
                Err(AnchoredSeedBurnError::Preprocess(err))
            }
        }
    }
}

/// Errors from [`AnchoredFirstSignedCustody`] operations.
#[derive(Debug)]
pub enum AnchoredFirstSignedError {
    Io(io::Error),
    Ledger(FirstSignedError),
    Baggy(BaggyError),
}

/// Production Baggy first-signed custody backed by [`FsCeremonyJournal`],
/// [`FsFirstSignedLedger`], and an independent [`FsLedgerCheckpointAnchor`].
pub struct AnchoredFirstSignedCustody {
    key_id: [u8; 32],
    next_cursor: u64,
    journal: FsCeremonyJournal,
    first_signed: FsFirstSignedLedger,
    anchor: FsLedgerCheckpointAnchor,
}

impl AnchoredFirstSignedCustody {
    /// Provision fresh ceremony journal, `FsFirstSignedLedger`, and retained checkpoint anchor.
    pub fn provision_genesis(
        ledger_path: impl AsRef<Path>,
        journal_path: impl AsRef<Path>,
        anchor_path: impl AsRef<Path>,
        key_id: [u8; 32],
        master_key: [u8; 32],
    ) -> io::Result<Self> {
        let mut master_key = SecretKey(master_key);
        let journal_key = SecretKey(derive_subkey(&master_key, &key_id, b"firstsigned.journal"));
        let ledger_key = SecretKey(derive_subkey(&master_key, &key_id, b"firstsigned.ledger"));
        let anchor_key = SecretKey(derive_subkey(&master_key, &key_id, b"firstsigned.anchor"));
        wipe_bytes32(&mut master_key);

        let journal_anchor = crate::FsDirectoryMonotoneAnchor::create_new(
            journal_anchor_path(anchor_path.as_ref()),
            derive_subkey(&anchor_key, &key_id, b"ceremony.anchor"),
        )?;
        let journal = FsCeremonyJournal::create_new_anchored(
            journal_path.as_ref(),
            key_id,
            journal_key.0,
            Box::new(journal_anchor),
        )?;
        let first_signed =
            FsFirstSignedLedger::provision_genesis(ledger_path.as_ref(), ledger_key.0)
                .map_err(|_| io::Error::other("failed to provision FsFirstSignedLedger"))?;
        let initial = first_signed.checkpoint();
        let anchor = FsLedgerCheckpointAnchor::provision_genesis(
            anchor_path.as_ref(),
            anchor_key.0,
            b"QSAG.FIRST_SIGNED.V1",
            initial,
        )?;
        Ok(Self {
            key_id,
            next_cursor: 1,
            journal,
            first_signed,
            anchor,
        })
    }

    /// Recover existing `FsFirstSignedLedger` custody, enforcing the retained
    /// [`LedgerCheckpoint`] from `anchor_path` before admitting the ledger snapshot.
    pub fn open_existing(
        ledger_path: impl AsRef<Path>,
        journal_path: impl AsRef<Path>,
        anchor_path: impl AsRef<Path>,
        key_id: [u8; 32],
        master_key: [u8; 32],
    ) -> io::Result<Self> {
        let mut master_key = SecretKey(master_key);
        let journal_key = SecretKey(derive_subkey(&master_key, &key_id, b"firstsigned.journal"));
        let ledger_key = SecretKey(derive_subkey(&master_key, &key_id, b"firstsigned.ledger"));
        let anchor_key = SecretKey(derive_subkey(&master_key, &key_id, b"firstsigned.anchor"));
        wipe_bytes32(&mut master_key);

        let mut anchor = FsLedgerCheckpointAnchor::open_existing(
            anchor_path.as_ref(),
            anchor_key.0,
            b"QSAG.FIRST_SIGNED.V1",
        )?;
        let retained = anchor.checkpoint();
        let journal_anchor = crate::FsDirectoryMonotoneAnchor::open_existing(
            journal_anchor_path(anchor_path.as_ref()),
            derive_subkey(&anchor_key, &key_id, b"ceremony.anchor"),
        )?;
        let journal = FsCeremonyJournal::open_existing_anchored(
            journal_path.as_ref(),
            key_id,
            journal_key.0,
            Box::new(journal_anchor),
        )?;
        let first_signed =
            FsFirstSignedLedger::open_existing(ledger_path.as_ref(), ledger_key.0, retained)
                .map_err(|_| {
                    invalid_anchor("first-signed ledger failed retained checkpoint verification")
                })?;
        let recovered = first_signed.checkpoint();
        anchor.ratchet_to(recovered)?;
        let next_cursor = recovered
            .generation
            .max(journal.last_committed().map_or(0, |r| r.seed_burn_cursor))
            .checked_add(1)
            .ok_or_else(|| invalid_anchor("first-signed cursor overflow"))?;
        Ok(Self {
            key_id,
            next_cursor,
            journal,
            first_signed,
            anchor,
        })
    }

    pub const fn checkpoint(&self) -> LedgerCheckpoint {
        self.anchor.checkpoint()
    }

    /// Record static-key first-signed digits with ceremony authorization and anchor `fsync`
    /// BEFORE returning the committed [`LedgerCheckpoint`].
    pub fn sync_records_anchored(
        &mut self,
        ceremony_id: [u8; 32],
        codeword: [u8; 32],
        records: &[FirstSignedRecord],
        hedge_generation: u64,
    ) -> Result<LedgerCheckpoint, AnchoredFirstSignedError> {
        let cursor = self.next_cursor;
        let next_cursor = cursor
            .checked_add(1)
            .ok_or_else(|| AnchoredFirstSignedError::Io(invalid_anchor("cursor exhausted")))?;
        let permit = self
            .journal
            .persist_before_release(CeremonyReservation {
                ceremony_id,
                key_id: self.key_id,
                epoch_or_codeword: codeword,
                seed_burn_cursor: cursor,
                hedge_generation,
            })
            .map_err(AnchoredFirstSignedError::Io)?;
        self.next_cursor = next_cursor;
        self.first_signed
            .authorize_release(&self.journal, permit)
            .map_err(AnchoredFirstSignedError::Ledger)?;
        self.first_signed
            .begin_release(&self.key_id, &ceremony_id, &codeword)
            .map_err(AnchoredFirstSignedError::Ledger)?;
        self.first_signed
            .sync_record(records)
            .map_err(AnchoredFirstSignedError::Ledger)?;
        let ckpt = self.first_signed.checkpoint();
        self.anchor
            .ratchet_to(ckpt)
            .map_err(AnchoredFirstSignedError::Io)?;
        Ok(ckpt)
    }

    /// Authorize, sign via [`baggy_sign_mpc`], and `fsync` the updated [`LedgerCheckpoint`]
    /// to [`FsLedgerCheckpointAnchor`] BEFORE releasing the [`BaggySig`].
    #[allow(clippy::too_many_arguments)]
    pub fn baggy_sign_mpc_anchored(
        &mut self,
        engine: &mut Rss256Engine,
        params: &BaggyParams,
        pk: &BaggyPublicKey,
        binding: &BaggyKeyBinding,
        cache: &mut WaistbandCache,
        msg: &[u8],
        hedge_generation: u64,
    ) -> Result<(BaggySig, LedgerCheckpoint), AnchoredFirstSignedError> {
        if binding.identity() != self.key_id {
            return Err(AnchoredFirstSignedError::Baggy(
                BaggyError::KeyBindingMismatch,
            ));
        }
        let mu = baggy_msg_digest(pk, msg);
        let cursor = self.next_cursor;
        let next_cursor = cursor
            .checked_add(1)
            .ok_or_else(|| AnchoredFirstSignedError::Io(invalid_anchor("cursor exhausted")))?;
        let permit = self
            .journal
            .persist_before_release(CeremonyReservation {
                ceremony_id: *engine.session_id(),
                key_id: self.key_id,
                epoch_or_codeword: mu,
                seed_burn_cursor: cursor,
                hedge_generation,
            })
            .map_err(AnchoredFirstSignedError::Io)?;
        self.next_cursor = next_cursor;
        self.first_signed
            .authorize_release(&self.journal, permit)
            .map_err(AnchoredFirstSignedError::Ledger)?;

        let prev_gen = self.anchor.checkpoint().generation;
        match baggy_sign_mpc(
            engine,
            params,
            pk,
            binding,
            cache,
            &mut self.first_signed,
            msg,
        ) {
            Ok(sig) => {
                let ckpt = self.first_signed.checkpoint();
                self.anchor
                    .ratchet_to(ckpt)
                    .map_err(AnchoredFirstSignedError::Io)?;
                Ok((sig, ckpt))
            }
            Err(err) => {
                let ckpt = self.first_signed.checkpoint();
                if ckpt.generation > prev_gen {
                    self.anchor
                        .ratchet_to(ckpt)
                        .map_err(AnchoredFirstSignedError::Io)?;
                }
                Err(AnchoredFirstSignedError::Baggy(err))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use qsag_core::baggy::StaticKeyId;
    use std::sync::atomic::{AtomicU64, Ordering};

    fn test_dir(label: &str) -> PathBuf {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let dir = std::env::temp_dir().join(std::format!(
            "qsag-anchored-custody-{label}-{}-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(dir.join("ledger")).unwrap();
        std::fs::create_dir_all(dir.join("anchor")).unwrap();
        dir
    }

    #[test]
    fn recovers_after_reservation_persisted_before_seed_burn() {
        let dir = test_dir("reservation-crash");
        let ledger = dir.join("ledger/burns");
        let journal = dir.join("ledger/ceremony");
        let anchor = dir.join("anchor/burns");
        let mut tracker = AnchoredSeedBurnTracker::provision_genesis(
            &ledger, &journal, &anchor, [1; 32], [2; 32],
        )
        .unwrap();
        tracker
            .journal
            .persist_before_release(CeremonyReservation {
                ceremony_id: [3; 32],
                key_id: [1; 32],
                epoch_or_codeword: [4; 32],
                seed_burn_cursor: 1,
                hedge_generation: 1,
            })
            .unwrap();
        drop(tracker); // Crash before the burn ledger commits.
        let mut tracker =
            AnchoredSeedBurnTracker::open_existing(&ledger, &journal, &anchor, [1; 32], [2; 32])
                .unwrap();
        assert_eq!(tracker.next_cursor, 2);
        tracker.burn_seed_anchored([5; 32], [6; 32], 2).unwrap();
        drop(tracker);
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn anchored_seed_burn_and_first_signed_reject_slot_rollback_on_reopen() {
        let dir = test_dir("rollback");
        let ledger_dir = dir.join("ledger");
        let anchor_dir = dir.join("anchor");
        let key_id = [0x44; 32];
        let master = [0x77; 32];

        // 1. AnchoredSeedBurnTracker: burn two seeds, snapshot old slots after burn 1, verify
        // rolling `.slot_a` + `.slot_b` back to burn 1 fails closed against retained anchor 2!
        let burn_path = ledger_dir.join("seedburn");
        let burn_journal = ledger_dir.join("seedburn.journal");
        let burn_anchor = anchor_dir.join("seedburn.anchor");

        let mut tracker = AnchoredSeedBurnTracker::provision_genesis(
            &burn_path,
            &burn_journal,
            &burn_anchor,
            key_id,
            master,
        )
        .unwrap();
        assert_eq!(tracker.checkpoint().generation, 0);
        let ckpt1 = tracker
            .burn_seed_anchored([0x01; 32], [0xA1; 32], 1)
            .unwrap();
        assert_eq!(ckpt1.generation, 1);
        let saved_slot_a = std::fs::read(ledger_dir.join("seedburn.slot_a")).unwrap();
        let saved_slot_b = std::fs::read(ledger_dir.join("seedburn.slot_b")).unwrap();

        let ckpt2 = tracker
            .burn_seed_anchored([0x02; 32], [0xA2; 32], 2)
            .unwrap();
        assert_eq!(ckpt2.generation, 2);
        drop(tracker);

        // Honest reopen succeeds at generation 2 and remembers both burns.
        let mut recovered = AnchoredSeedBurnTracker::open_existing(
            &burn_path,
            &burn_journal,
            &burn_anchor,
            key_id,
            master,
        )
        .unwrap();
        assert_eq!(recovered.checkpoint(), ckpt2);
        assert!(recovered.is_burned(&[0xA1; 32]).unwrap());
        assert!(recovered.is_burned(&[0xA2; 32]).unwrap());
        assert!(matches!(
            recovered.burn_seed_anchored([0x03; 32], [0xA2; 32], 3),
            Err(AnchoredSeedBurnError::Burn(SeedBurnError::AlreadyBurned))
        ));
        drop(recovered);

        // Roll `.slot_a` and `.slot_b` back to generation 1 while `anchor_dir` retains ckpt2:
        // `open_existing` MUST deterministically fail closed!
        std::fs::write(ledger_dir.join("seedburn.slot_a"), &saved_slot_a).unwrap();
        std::fs::write(ledger_dir.join("seedburn.slot_b"), &saved_slot_b).unwrap();
        assert!(
            AnchoredSeedBurnTracker::open_existing(
                &burn_path,
                &burn_journal,
                &burn_anchor,
                key_id,
                master,
            )
            .is_err()
        );

        // 2. AnchoredFirstSignedCustody: sync two generations, roll slots back, verify rejection!
        let fs_path = ledger_dir.join("firstsigned");
        let fs_journal = ledger_dir.join("firstsigned.journal");
        let fs_anchor = anchor_dir.join("firstsigned.anchor");

        let mut custody = AnchoredFirstSignedCustody::provision_genesis(
            &fs_path,
            &fs_journal,
            &fs_anchor,
            key_id,
            master,
        )
        .unwrap();
        let rec1 = FirstSignedRecord {
            key: StaticKeyId {
                identity: key_id,
                layer: 1,
                tree: 0,
                key_pair: 3,
            },
            digits: vec![1, 2, 3, 0],
        };
        let fs_ckpt1 = custody
            .sync_records_anchored([0x11; 32], [0xB1; 32], &[rec1], 1)
            .unwrap();
        assert_eq!(fs_ckpt1.generation, 1);
        let fs_slot_a = std::fs::read(ledger_dir.join("firstsigned.slot_a")).unwrap();
        let fs_slot_b = std::fs::read(ledger_dir.join("firstsigned.slot_b")).unwrap();

        let rec2 = FirstSignedRecord {
            key: StaticKeyId {
                identity: key_id,
                layer: 2,
                tree: 0,
                key_pair: 7,
            },
            digits: vec![3, 2, 1, 0],
        };
        let fs_ckpt2 = custody
            .sync_records_anchored([0x12; 32], [0xB2; 32], &[rec2], 2)
            .unwrap();
        assert_eq!(fs_ckpt2.generation, 2);
        drop(custody);

        let mut fs_recovered = AnchoredFirstSignedCustody::open_existing(
            &fs_path,
            &fs_journal,
            &fs_anchor,
            key_id,
            master,
        )
        .unwrap();
        assert_eq!(fs_recovered.checkpoint(), fs_ckpt2);
        // Conflicting digits for `(layer=1, tree=0, key_pair=3)` are rejected!
        let conflicting = FirstSignedRecord {
            key: StaticKeyId {
                identity: key_id,
                layer: 1,
                tree: 0,
                key_pair: 3,
            },
            digits: vec![0, 2, 3, 0],
        };
        assert!(matches!(
            fs_recovered.sync_records_anchored([0x13; 32], [0xB3; 32], &[conflicting], 3),
            Err(AnchoredFirstSignedError::Ledger(FirstSignedError::Conflict))
        ));
        drop(fs_recovered);

        // Roll `firstsigned` slots back to generation 1 -> `open_existing` fails closed!
        std::fs::write(ledger_dir.join("firstsigned.slot_a"), &fs_slot_a).unwrap();
        std::fs::write(ledger_dir.join("firstsigned.slot_b"), &fs_slot_b).unwrap();
        assert!(
            AnchoredFirstSignedCustody::open_existing(
                &fs_path,
                &fs_journal,
                &fs_anchor,
                key_id,
                master,
            )
            .is_err()
        );

        std::fs::remove_dir_all(dir).unwrap();
    }
}
