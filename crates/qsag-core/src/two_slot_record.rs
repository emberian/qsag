//! One authenticated two-slot generation record under a permanent genesis lock.
//!
//! On disk (every file is a [`LockedRecord`] payload, mode `0600`, never followed
//! through a symlink, replaced by write-temp, `fsync`, rename, directory `fsync`):
//!
//! * genesis: `"QSAG2SR1" || record_id[32] || slot_a_identity[24] || slot_b_identity[24]
//!   || mac[32]`, written once. The slot identities are the `dev || ino || nonce`
//!   of each slot's lock sidecar, so a recreated or copied sidecar is not a slot.
//! * slot `i`: `generation_le64 || payload || mac[32]` with `generation % 2 == i`.
//!
//! Every MAC is `cSHAKE256("QSAG.TWO_SLOT_RECORD.MAC/v1")` over
//! `len(domain) || domain || key || genesis_identity[24] || record_id || purpose`,
//! followed for a slot by `slot index || slot identity || generation || payload`.
//! The user's `domain` separates one user's records from another's under one key.
//!
//! A commit writes the successor generation to the slot that does not hold the
//! current one, so the current generation stays readable until its successor is
//! durable. Opening takes the highest generation that authenticates and passes the
//! caller's minimum. One unreadable slot is survivable, and whether the surviving
//! generation is recent enough is decided by that minimum (or, for a record that is
//! itself the rollback authority, by [`TwoSlotRecord::commit_mirrored`]).
use crate::durable_ledger::LedgerCheckpoint;
use crate::sponge::Cshake256Xof;
use crate::wipe::{ct_eq_bytes32, wipe_bytes32};
use alloc::vec::Vec;
use core::sync::atomic::{AtomicBool, Ordering};
use qsag_asm::durable::LockedRecord;
use std::{io, path::PathBuf};

const GENESIS_MAGIC: &[u8; 8] = b"QSAG2SR1";
const GENESIS_LEN: usize = 8 + 32 + 24 + 24 + 32;
const SLOT_OVERHEAD: usize = 8 + 32;
const PURPOSE_GENESIS: u8 = 0;
const PURPOSE_SLOT: u8 = 1;

/// Where the three files of one record live. Each also owns a `.lock` sidecar and a
/// transient `.tmp` next to it.
pub struct TwoSlotPaths {
    pub genesis: PathBuf,
    pub slots: [PathBuf; 2],
}

struct Key([u8; 32]);
impl Drop for Key {
    fn drop(&mut self) {
        wipe_bytes32(&mut self.0);
    }
}

pub struct TwoSlotRecord {
    genesis: LockedRecord,
    slots: [Option<LockedRecord>; 2],
    slot_identities: [[u8; 24]; 2],
    key: Key,
    domain: &'static [u8],
    record_id: [u8; 32],
    limit: usize,
    current: LedgerCheckpoint,
    failed: AtomicBool,
}

fn invalid() -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidData,
        "two-slot record failed authentication or rolled back",
    )
}

impl TwoSlotRecord {
    /// Provision a new record holding `payload` at generation 0. Fails if any of the
    /// three files or sidecars exists. An interrupted provisioning leaves sidecars
    /// behind, so it is never mistaken for a fresh path and never becomes readable.
    pub fn create(
        paths: TwoSlotPaths,
        key: [u8; 32],
        domain: &'static [u8],
        limit: usize,
        payload: &[u8],
    ) -> io::Result<Self> {
        use std::io::Read;
        let key = Key(key);
        let [slot_a, slot_b] = paths.slots;
        let genesis = LockedRecord::create_new(paths.genesis)?;
        let slots = [
            LockedRecord::create_new(slot_a)?,
            LockedRecord::create_new(slot_b)?,
        ];
        let slot_identities = slots.each_ref().map(LockedRecord::lock_identity_seal);
        let mut record_id = [0; 32];
        std::fs::File::open("/dev/urandom")?.read_exact(&mut record_id)?;
        let mut this = Self {
            genesis,
            slots: slots.map(Some),
            slot_identities,
            key,
            domain,
            record_id,
            limit,
            current: LedgerCheckpoint {
                generation: 0,
                tag: [0; 32],
            },
            failed: AtomicBool::new(false),
        };
        // Slot B exists (empty, so unauthenticated) before genesis is sealed, and
        // genesis is sealed before generation 0 is written.
        this.check_len(payload)?;
        this.slot(1)?.replace(&[])?;
        this.genesis.replace(&this.genesis_bytes())?;
        this.write(0, payload)?;
        Ok(this)
    }

    /// Open an existing record at its highest authenticated generation. With a
    /// `minimum`, generations below it, and a different tag at its generation, are
    /// not candidates, so a restored older snapshot is refused.
    pub fn open(
        paths: TwoSlotPaths,
        key: [u8; 32],
        domain: &'static [u8],
        limit: usize,
        minimum: Option<LedgerCheckpoint>,
    ) -> io::Result<Self> {
        let key = Key(key);
        let genesis = LockedRecord::open_existing(paths.genesis)?;
        let bytes = genesis.read_bounded(GENESIS_LEN)?;
        if bytes.len() != GENESIS_LEN || &bytes[..8] != GENESIS_MAGIC {
            return Err(invalid());
        }
        let record_id = bytes[8..40].try_into().map_err(|_| invalid())?;
        let slot_identities: [[u8; 24]; 2] = [
            bytes[40..64].try_into().map_err(|_| invalid())?,
            bytes[64..88].try_into().map_err(|_| invalid())?,
        ];
        // A slot whose sidecar is missing, damaged or not the one genesis names is
        // unavailable: it is neither read nor written, and the other slot still opens.
        let slots = core::array::from_fn(|index| {
            LockedRecord::acquire(&paths.slots[index])
                .ok()
                .filter(|slot| slot.lock_identity_seal() == slot_identities[index])
        });
        let mut this = Self {
            genesis,
            slots,
            slot_identities,
            key,
            domain,
            record_id,
            limit,
            current: LedgerCheckpoint {
                generation: 0,
                tag: [0; 32],
            },
            failed: AtomicBool::new(false),
        };
        this.check_genesis()?;
        let mut best: Option<LedgerCheckpoint> = None;
        for index in 0..2 {
            let Ok((candidate, _)) = this.read_slot(index) else {
                continue;
            };
            if let Some(minimum) = minimum
                && (candidate.generation < minimum.generation
                    || (candidate.generation == minimum.generation
                        && !ct_eq_bytes32(&candidate.tag, &minimum.tag)))
            {
                continue;
            }
            if best.is_none_or(|old| candidate.generation > old.generation) {
                best = Some(candidate);
            }
        }
        this.current = best.ok_or_else(invalid)?;
        Ok(this)
    }

    /// Generation and MAC of the current slot. Retained outside this record's
    /// rollback domain, it is the `minimum` of a later [`Self::open`].
    pub fn checkpoint(&self) -> LedgerCheckpoint {
        self.current
    }

    /// Whether an earlier check or write failed on this handle. A failed handle
    /// refuses everything; reopen to continue.
    pub fn is_failed(&self) -> bool {
        self.failed.load(Ordering::SeqCst)
    }

    /// Fail this handle permanently, for a caller whose own invariant broke.
    pub fn latch_failure(&self) {
        self.failed.store(true, Ordering::SeqCst);
    }

    /// The current payload, after checking that genesis and the current slot on disk
    /// are still the ones this handle last saw.
    pub fn read(&self) -> io::Result<Vec<u8>> {
        self.latching(|| {
            self.check_genesis()?;
            let (checkpoint, payload) = self.read_slot((self.current.generation % 2) as usize)?;
            if checkpoint != self.current {
                return Err(invalid());
            }
            Ok(payload)
        })
    }

    /// Durably replace the payload: one write, to the slot not holding the current
    /// generation.
    pub fn commit(&mut self, payload: &[u8]) -> io::Result<LedgerCheckpoint> {
        self.check_len(payload)?;
        self.read()?;
        let generation = self.current.generation.checked_add(1).ok_or_else(invalid)?;
        self.write(generation, payload)?;
        Ok(self.current)
    }

    /// Durably replace the payload in both slots, as two successive generations.
    /// Once this returns, either slot alone recovers `payload`, so losing one slot
    /// cannot surface the payload that was replaced. A crash between the two writes
    /// recovers the new payload while its slot survives.
    pub fn commit_mirrored(&mut self, payload: &[u8]) -> io::Result<LedgerCheckpoint> {
        self.commit(payload)?;
        self.commit(payload)
    }

    fn latching<T>(&self, operation: impl FnOnce() -> io::Result<T>) -> io::Result<T> {
        if self.is_failed() {
            return Err(io::Error::other("two-slot record handle failed; reopen"));
        }
        operation().inspect_err(|_| self.latch_failure())
    }

    fn slot(&self, index: usize) -> io::Result<&LockedRecord> {
        self.slots[index].as_ref().ok_or_else(invalid)
    }

    fn mac(&self, purpose: u8, parts: &[&[u8]]) -> [u8; 32] {
        let mut xof = Cshake256Xof::new(b"QSAG.TWO_SLOT_RECORD.MAC/v1");
        xof.absorb(&(self.domain.len() as u64).to_le_bytes());
        xof.absorb(self.domain);
        xof.absorb(&self.key.0);
        xof.absorb(&self.genesis.lock_identity_seal());
        xof.absorb(&self.record_id);
        xof.absorb(&[purpose]);
        for part in parts {
            xof.absorb(part);
        }
        let mut tag = [0; 32];
        xof.squeeze(&mut tag);
        tag
    }

    fn genesis_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(GENESIS_LEN);
        bytes.extend_from_slice(GENESIS_MAGIC);
        bytes.extend_from_slice(&self.record_id);
        for identity in &self.slot_identities {
            bytes.extend_from_slice(identity);
        }
        let tag = self.mac(PURPOSE_GENESIS, &[&bytes]);
        bytes.extend_from_slice(&tag);
        bytes
    }

    fn check_genesis(&self) -> io::Result<()> {
        let actual = self.genesis.read_bounded(GENESIS_LEN)?;
        let expected = self.genesis_bytes();
        let split = GENESIS_LEN - 32;
        if actual.len() != GENESIS_LEN || actual[..split] != expected[..split] {
            return Err(invalid());
        }
        let actual_tag: [u8; 32] = actual[split..].try_into().map_err(|_| invalid())?;
        let expected_tag: [u8; 32] = expected[split..].try_into().map_err(|_| invalid())?;
        if !ct_eq_bytes32(&actual_tag, &expected_tag) {
            return Err(invalid());
        }
        Ok(())
    }

    fn slot_mac(&self, index: usize, body: &[u8]) -> [u8; 32] {
        self.mac(
            PURPOSE_SLOT,
            &[&[index as u8], &self.slot_identities[index], body],
        )
    }

    fn read_slot(&self, index: usize) -> io::Result<(LedgerCheckpoint, Vec<u8>)> {
        let mut bytes = self
            .slot(index)?
            .read_bounded(self.limit.saturating_add(SLOT_OVERHEAD))?;
        if bytes.len() < SLOT_OVERHEAD {
            return Err(invalid());
        }
        let end = bytes.len() - 32;
        let tag: [u8; 32] = bytes[end..].try_into().map_err(|_| invalid())?;
        if !ct_eq_bytes32(&tag, &self.slot_mac(index, &bytes[..end])) {
            return Err(invalid());
        }
        let generation = u64::from_le_bytes(bytes[..8].try_into().map_err(|_| invalid())?);
        if generation % 2 != index as u64 {
            return Err(invalid());
        }
        bytes.truncate(end);
        bytes.drain(..8);
        Ok((LedgerCheckpoint { generation, tag }, bytes))
    }

    fn check_len(&self, payload: &[u8]) -> io::Result<()> {
        if payload.len() > self.limit {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "two-slot record payload exceeds its limit",
            ));
        }
        Ok(())
    }

    fn seal_slot(&self, generation: u64, payload: &[u8]) -> io::Result<LedgerCheckpoint> {
        let index = (generation % 2) as usize;
        let mut bytes = Vec::with_capacity(payload.len() + SLOT_OVERHEAD);
        bytes.extend_from_slice(&generation.to_le_bytes());
        bytes.extend_from_slice(payload);
        let tag = self.slot_mac(index, &bytes);
        bytes.extend_from_slice(&tag);
        self.slot(index)?.replace(&bytes)?;
        Ok(LedgerCheckpoint { generation, tag })
    }

    fn write(&mut self, generation: u64, payload: &[u8]) -> io::Result<()> {
        self.current = self.latching(|| self.seal_slot(generation, payload))?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const KEY: [u8; 32] = [0x4b; 32];
    const DOMAIN: &[u8] = b"QSAG.TEST.TWO_SLOT";

    struct Scratch(PathBuf);
    impl Scratch {
        fn new(tag: &str) -> Self {
            static NEXT: core::sync::atomic::AtomicU64 = core::sync::atomic::AtomicU64::new(0);
            let dir = std::env::temp_dir().join(std::format!(
                "qsag-two-slot-{tag}-{}-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed),
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos()
            ));
            std::fs::create_dir(&dir).unwrap();
            Self(dir)
        }
        fn paths(&self) -> TwoSlotPaths {
            TwoSlotPaths {
                genesis: self.0.join("genesis"),
                slots: [self.slot(0), self.slot(1)],
            }
        }
        fn slot(&self, index: usize) -> PathBuf {
            self.0.join(["slot_a", "slot_b"][index])
        }
        fn open(&self, minimum: Option<LedgerCheckpoint>) -> io::Result<TwoSlotRecord> {
            TwoSlotRecord::open(self.paths(), KEY, DOMAIN, 1024, minimum)
        }
        /// Generation 0 in slot A, 1 in slot B, then 2 in slot A.
        fn three_generations(&self) -> [LedgerCheckpoint; 3] {
            let mut record =
                TwoSlotRecord::create(self.paths(), KEY, DOMAIN, 1024, b"zero").unwrap();
            let zero = record.checkpoint();
            let one = record.commit(b"one").unwrap();
            let two = record.commit(b"two").unwrap();
            assert_eq!((zero.generation, one.generation, two.generation), (0, 1, 2));
            assert_eq!(record.read().unwrap(), b"two");
            [zero, one, two]
        }
        fn tear(&self, index: usize) {
            let path = self.slot(index);
            let mut bytes = std::fs::read(&path).unwrap();
            bytes.truncate(bytes.len() / 2);
            std::fs::write(path, bytes).unwrap();
        }
    }
    impl Drop for Scratch {
        fn drop(&mut self) {
            std::fs::remove_dir_all(&self.0).unwrap();
        }
    }

    #[test]
    fn a_torn_slot_a_recovers_the_generation_in_slot_b() {
        let dir = Scratch::new("torn-a");
        let [_, one, two] = dir.three_generations();
        dir.tear(0);
        let mut record = dir.open(None).unwrap();
        assert_eq!(record.checkpoint(), one);
        assert_eq!(record.read().unwrap(), b"one");
        // The newest generation was lost with slot A; a caller that retained its
        // checkpoint is told so instead of being handed the older payload.
        assert!(dir.open(Some(two)).is_err());
        // The torn slot is the next write target and is repaired by it.
        let three = record.commit(b"three").unwrap();
        assert_eq!(three.generation, 2);
        assert_ne!(three, two);
        drop(record);
        assert_eq!(dir.open(Some(three)).unwrap().read().unwrap(), b"three");
    }

    #[test]
    fn a_torn_slot_b_leaves_the_newer_generation_in_slot_a() {
        let dir = Scratch::new("torn-b");
        let [_, _, two] = dir.three_generations();
        dir.tear(1);
        let mut record = dir.open(Some(two)).unwrap();
        assert_eq!(record.checkpoint(), two);
        assert_eq!(record.read().unwrap(), b"two");
        assert_eq!(record.commit(b"three").unwrap().generation, 3);
        assert_eq!(record.read().unwrap(), b"three");
    }

    #[test]
    fn both_slots_torn_fails_closed() {
        let dir = Scratch::new("torn-both");
        dir.three_generations();
        dir.tear(0);
        dir.tear(1);
        assert!(dir.open(None).is_err());
        // Nothing reprovisions over the remains.
        assert!(TwoSlotRecord::create(dir.paths(), KEY, DOMAIN, 1024, b"again").is_err());
        assert!(dir.open(None).is_err());
    }

    #[test]
    fn a_stale_generation_never_wins() {
        let dir = Scratch::new("stale");
        let mut record = TwoSlotRecord::create(dir.paths(), KEY, DOMAIN, 1024, b"zero").unwrap();
        let stale_slot_a = std::fs::read(dir.slot(0)).unwrap();
        let one = record.commit(b"one").unwrap();
        let stale_slot_b = std::fs::read(dir.slot(1)).unwrap();
        let two = record.commit(b"two").unwrap();
        let three = record.commit(b"three").unwrap();
        drop(record);
        // Slot A is put back to its authentic generation 0: slot B (3) still wins.
        let current_slot_a = std::fs::read(dir.slot(0)).unwrap();
        std::fs::write(dir.slot(0), &stale_slot_a).unwrap();
        let record = dir.open(None).unwrap();
        assert_eq!(record.checkpoint(), three);
        assert_eq!(record.read().unwrap(), b"three");
        drop(record);
        // Slot B is put back to generation 1 as well: without a minimum the best
        // authentic generation is 2 or 1, and every retained later checkpoint refuses.
        std::fs::write(dir.slot(0), &current_slot_a).unwrap();
        std::fs::write(dir.slot(1), &stale_slot_b).unwrap();
        assert_eq!(dir.open(None).unwrap().checkpoint(), two);
        assert_eq!(dir.open(Some(one)).unwrap().checkpoint(), two);
        assert!(dir.open(Some(three)).is_err());
        // An equal generation with another tag is not the retained checkpoint.
        let forged = LedgerCheckpoint {
            generation: two.generation,
            tag: [0xee; 32],
        };
        assert!(dir.open(Some(forged)).is_err());
        // A slot image is bound to its own slot: slot A's bytes under slot B's
        // record header do not authenticate there.
        let mut transplanted = stale_slot_b[..16].to_vec();
        transplanted.extend_from_slice(&current_slot_a[16..]);
        std::fs::write(dir.slot(1), &transplanted).unwrap();
        std::fs::write(dir.slot(0), b"").unwrap();
        assert!(dir.open(None).is_err());
    }

    #[test]
    fn a_tampered_payload_is_rejected_and_latches_a_live_handle() {
        let dir = Scratch::new("tamper");
        let [_, one, two] = dir.three_generations();
        let record = dir.open(Some(two)).unwrap();
        let mut bytes = std::fs::read(dir.slot(0)).unwrap();
        // Record header (16) and generation (8) precede the payload.
        bytes[24] ^= 1;
        std::fs::write(dir.slot(0), &bytes).unwrap();
        assert!(record.read().is_err());
        assert!(record.is_failed());
        bytes[24] ^= 1;
        std::fs::write(dir.slot(0), &bytes).unwrap();
        // Repairing the file does not revive the handle.
        assert!(record.read().is_err());
        drop(record);
        assert_eq!(dir.open(Some(two)).unwrap().read().unwrap(), b"two");
        // Every other byte of the slot is covered too.
        for offset in [16, 23, 25, bytes.len() - 33, bytes.len() - 1] {
            let mut bad = bytes.clone();
            bad[offset] ^= 0x80;
            std::fs::write(dir.slot(0), &bad).unwrap();
            assert!(dir.open(Some(two)).is_err(), "offset {offset}");
            assert_eq!(dir.open(None).unwrap().checkpoint(), one, "offset {offset}");
        }
    }

    #[test]
    fn key_domain_and_genesis_bind_the_record() {
        let dir = Scratch::new("bind");
        let [_, _, two] = dir.three_generations();
        assert!(TwoSlotRecord::open(dir.paths(), [0x4c; 32], DOMAIN, 1024, None).is_err());
        assert!(TwoSlotRecord::open(dir.paths(), KEY, b"QSAG.TEST.OTHER", 1024, None).is_err());
        let genesis = std::fs::read(dir.0.join("genesis")).unwrap();
        for offset in [16, 16 + 8, 16 + 40, 16 + 64, genesis.len() - 1] {
            let mut bad = genesis.clone();
            bad[offset] ^= 1;
            std::fs::write(dir.0.join("genesis"), &bad).unwrap();
            assert!(dir.open(None).is_err(), "offset {offset}");
        }
        std::fs::write(dir.0.join("genesis"), &genesis).unwrap();
        let mut record = dir.open(Some(two)).unwrap();
        // An oversized payload is refused before anything is written.
        assert!(record.commit(&[0; 1025]).is_err());
        assert_eq!(record.commit(&[0; 1024]).unwrap().generation, 3);
    }

    #[test]
    fn a_mirrored_commit_survives_the_loss_of_either_slot() {
        for lost in 0..2 {
            let dir = Scratch::new("mirror");
            let mut record = TwoSlotRecord::create(dir.paths(), KEY, DOMAIN, 1024, b"old").unwrap();
            record.commit_mirrored(b"older").unwrap();
            let acknowledged = record.commit_mirrored(b"new").unwrap();
            assert_eq!(acknowledged.generation, 4);
            drop(record);
            dir.tear(lost);
            let mut record = dir.open(None).unwrap();
            assert_eq!(record.read().unwrap(), b"new");
            record.commit_mirrored(b"next").unwrap();
            drop(record);
            assert_eq!(dir.open(None).unwrap().read().unwrap(), b"next");
        }
    }
}
