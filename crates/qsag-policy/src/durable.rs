//! Canonical authenticated V3 ledger codec. This is a snapshot, not a storage
//! transaction: callers must atomically persist it and fence its generation in
//! trusted monotonic storage before releasing a signature. A MAC alone cannot
//! detect rollback of both the checkpoint and its external generation fence.
//!
//! All integers are big endian. The MAC covers, in order: the 29-byte domain
//! `QSAG.POLICY.DURABLE_LEDGER.V3`, key ID (32), enrolled party (u16), generation
//! (u64), window (u64), spend (u128), next local slot (u16), poisoned and
//! authenticated-initiator flags (one canonical 0/1 byte each), then nonce and
//! session windows (each: u16 count, zero u16 cursor, count * 32 bytes), then
//! two optional eviction watermarks (flag + 32 bytes each), then peer slots
//! (u16 count, strictly ascending (u16 party, u64 mask) pairs). A 32-byte keyed
//! cSHAKE256 framed tag follows. Trailing bytes and noncanonical encodings fail.
//! Key identity identifies the original secret provisioning, not just party ID.
//! Restore requires the same provisioned secrets; secrets are never serialized.

use super::*;

const DOMAIN: &[u8] = b"QSAG.POLICY.DURABLE_LEDGER.V3";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PolicyGuardError {
    InvalidCheckpoint,
    AuthenticationFailed,
    WrongGuard,
    Rollback,
    ActiveSession,
}

struct Reader<'a>(&'a [u8]);
impl Reader<'_> {
    fn take<const N: usize>(&mut self) -> Result<[u8; N], PolicyGuardError> {
        let bytes = self.0.get(..N).ok_or(PolicyGuardError::InvalidCheckpoint)?;
        let out = bytes
            .try_into()
            .map_err(|_| PolicyGuardError::InvalidCheckpoint)?;
        self.0 = &self.0[N..];
        Ok(out)
    }
    fn short(&mut self) -> Result<usize, PolicyGuardError> {
        Ok(u16::from_be_bytes(self.take()?) as usize)
    }
    fn flag(&mut self) -> Result<bool, PolicyGuardError> {
        match self.take::<1>()?[0] {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(PolicyGuardError::InvalidCheckpoint),
        }
    }
    fn ring(&mut self) -> Result<(Vec<[u8; 32]>, usize), PolicyGuardError> {
        let count = self.short()?;
        let cursor = self.short()?;
        if count > MAX_BURNED_INTENT_NONCES
            || cursor >= MAX_BURNED_INTENT_NONCES
            || (count < MAX_BURNED_INTENT_NONCES && cursor != 0)
        {
            return Err(PolicyGuardError::InvalidCheckpoint);
        }
        let mut values = Vec::with_capacity(count);
        for _ in 0..count {
            values.push(self.take()?);
        }
        Ok((values, cursor))
    }
}

impl PolicySignerGuardShare {
    /// Export authenticated ledger bytes. Generation is clamped to the largest
    /// generation already exported/restored by this handle. Persist the result
    /// atomically with an external monotonic fence before releasing output.
    /// A snapshot taken during an in-flight session is quarantined on restore:
    /// peer openings may already have escaped, so it restores a poisoned guard.
    pub fn export_durable_checkpoint(
        &self,
        storage_mac_key: &[u8; 32],
        monotonic_generation: u64,
    ) -> Vec<u8> {
        let generation = monotonic_generation.max(self.durable_generation.get());
        self.durable_generation.set(generation);
        let mut out = Vec::new();
        out.extend_from_slice(DOMAIN);
        out.extend_from_slice(&self.durable_key_id);
        out.extend_from_slice(&self.enrolled_party_id.to_be_bytes());
        out.extend_from_slice(&generation.to_be_bytes());
        out.extend_from_slice(&self.current_window_id.to_be_bytes());
        out.extend_from_slice(&self.accumulated_window_spend.to_be_bytes());
        out.extend_from_slice(&(self.next_slot.get() as u16).to_be_bytes());
        out.push(u8::from(self.poisoned || self.active_phase.is_some()));
        out.push(u8::from(self.require_authenticated_initiator));
        for (values, cursor) in [
            (&self.burned_intent_nonces, self.burned_nonce_cursor),
            (&self.burned_sessions, self.burned_session_cursor),
        ] {
            out.extend_from_slice(&(values.len() as u16).to_be_bytes());
            out.extend_from_slice(&(cursor as u16).to_be_bytes());
            for value in values {
                out.extend_from_slice(value);
            }
        }
        for floor in [self.min_nonce_watermark, self.min_session_watermark] {
            out.push(u8::from(floor.is_some()));
            out.extend_from_slice(&floor.unwrap_or([0; 32]));
        }
        let mut peers = self.consumed_peer_slots.clone();
        peers.sort_unstable_by_key(|p| p.0);
        out.extend_from_slice(&(peers.len() as u16).to_be_bytes());
        for (peer, mask) in peers {
            out.extend_from_slice(&peer.to_be_bytes());
            out.extend_from_slice(&mask.to_be_bytes());
        }
        let tag = cshake256_framed_32(DOMAIN, &[storage_mac_key, &out]);
        out.extend_from_slice(&tag);
        out
    }

    /// Authenticate and validate completely before mutating the ledger. Live
    /// spend, nonce/session burns and retired preprocessing slots cannot regress.
    /// `min_expected_generation` must come from rollback-resistant storage.
    pub fn restore_from_durable_checkpoint(
        &mut self,
        bytes: &[u8],
        storage_mac_key: &[u8; 32],
        min_expected_generation: u64,
    ) -> Result<u64, PolicyGuardError> {
        if self.active_phase.is_some() {
            return Err(PolicyGuardError::ActiveSession);
        }
        let split = bytes
            .len()
            .checked_sub(32)
            .ok_or(PolicyGuardError::InvalidCheckpoint)?;
        let (body, tag) = bytes.split_at(split);
        if !ct_eq_bytes(&cshake256_framed_32(DOMAIN, &[storage_mac_key, body]), tag) {
            return Err(PolicyGuardError::AuthenticationFailed);
        }
        let mut r = Reader(body);
        if r.take::<29>()? != DOMAIN {
            return Err(PolicyGuardError::InvalidCheckpoint);
        }
        if r.take::<32>()? != self.durable_key_id
            || u16::from_be_bytes(r.take()?) != self.enrolled_party_id
            || self.party_id != self.enrolled_party_id
        {
            return Err(PolicyGuardError::WrongGuard);
        }
        let generation = u64::from_be_bytes(r.take()?);
        let window = u64::from_be_bytes(r.take()?);
        let spend = u128::from_be_bytes(r.take()?);
        let next = r.short()?;
        let poisoned = r.flag()?;
        let authenticated = r.flag()?;
        let (nonces, nonce_cursor) = r.ring()?;
        let (sessions, session_cursor) = r.ring()?;
        let nonce_floor = if r.flag()? { Some(r.take::<32>()?) } else {
            if r.take::<32>()? != [0; 32] { return Err(PolicyGuardError::InvalidCheckpoint); }
            None
        };
        let session_floor = if r.flag()? { Some(r.take::<32>()?) } else {
            if r.take::<32>()? != [0; 32] { return Err(PolicyGuardError::InvalidCheckpoint); }
            None
        };
        if nonce_cursor != 0 || session_cursor != 0
            || nonces.windows(2).any(|w| w[0] >= w[1])
            || sessions.windows(2).any(|w| w[0] >= w[1])
            || nonces.iter().any(|n| nonce_floor.is_some_and(|f| *n <= f))
            || sessions.iter().any(|n| session_floor.is_some_and(|f| *n <= f)) {
            return Err(PolicyGuardError::InvalidCheckpoint);
        }
        let count = r.short()?;
        if next > self.preproc_r.len() || count != self.consumed_peer_slots.len() {
            return Err(PolicyGuardError::InvalidCheckpoint);
        }
        let mut peers = Vec::with_capacity(count);
        for _ in 0..count {
            let peer = u16::from_be_bytes(r.take()?);
            let mask = u64::from_be_bytes(r.take()?);
            if peers.last().is_some_and(|&(p, _)| p >= peer)
                || !self.consumed_peer_slots.iter().any(|p| p.0 == peer)
            {
                return Err(PolicyGuardError::InvalidCheckpoint);
            }
            peers.push((peer, mask));
        }
        if !r.0.is_empty() {
            return Err(PolicyGuardError::InvalidCheckpoint);
        }
        if generation < min_expected_generation.max(self.durable_generation.get())
            || window < self.current_window_id
            || (window == self.current_window_id && spend < self.accumulated_window_spend)
            || self.burned_intent_nonces.iter()
                .any(|n| !nonces.contains(n) && !nonce_floor.is_some_and(|f| *n <= f))
            || nonce_floor < self.min_nonce_watermark
            || session_floor < self.min_session_watermark
            || self.burned_sessions.iter().any(|s| !sessions.contains(s) && !session_floor.is_some_and(|f| *s <= f))
            || next < self.next_slot.get()
            || (self.poisoned && !poisoned)
            || (self.require_authenticated_initiator && !authenticated)
            || self
                .consumed_peer_slots
                .iter()
                .any(|(p, mask)| !peers.iter().any(|(q, new)| p == q && new & mask == *mask))
        {
            return Err(PolicyGuardError::Rollback);
        }
        self.current_window_id = window;
        self.accumulated_window_spend = spend;
        self.burned_intent_nonces = nonces;
        self.burned_nonce_cursor = nonce_cursor;
        self.min_nonce_watermark = nonce_floor;
        self.burned_sessions = sessions;
        self.burned_session_cursor = session_cursor;
        self.min_session_watermark = session_floor;
        self.next_slot.set(next);
        self.require_authenticated_initiator = authenticated;
        self.durable_generation.set(generation);
        for slot in 0..next {
            self.retire_own_slot(slot);
        }
        for &(peer, mask) in &peers {
            for slot in 0..64 {
                if mask & (1u64 << slot) != 0 {
                    self.retire_peer_slot(peer, slot);
                }
            }
        }
        self.consumed_peer_slots = peers;
        if poisoned {
            self.poison();
        }
        Ok(generation)
    }
}

/// Disk-backed authenticated checkpoints. The lock genesis seal is part of the
/// MAC key derivation, preventing a record from migrating to a replacement lock.
/// Whole-directory rollback still requires an external monotonic generation fence.
#[cfg(feature = "std")]
pub struct FsPolicyDurableLedger {
    record: qsag_asm::durable::LockedRecord,
    key: qsag_accel::ct::RedactedSecret<32>,
    generation: u64,
}
#[cfg(feature = "std")]
impl FsPolicyDurableLedger {
    pub fn create_new(path: impl Into<std::path::PathBuf>, key: [u8; 32], guard: &PolicySignerGuardShare) -> std::io::Result<Self> {
        let record = qsag_asm::durable::LockedRecord::create_new(path)?;
        let key = qsag_accel::ct::RedactedSecret::new(cshake256_framed_32(
            b"QSAG.POLICY.FS.SEAL.V1", &[&key, &record.lock_seal()]));
        let mut ledger = Self { record, key, generation: guard.durable_generation.get() };
        ledger.sync_persist(guard)?;
        Ok(ledger)
    }
    pub fn open_existing(path: impl Into<std::path::PathBuf>, key: [u8; 32], guard: &mut PolicySignerGuardShare, min_generation: u64) -> std::io::Result<Self> {
        let record = qsag_asm::durable::LockedRecord::open_existing(path)?;
        let key = qsag_accel::ct::RedactedSecret::new(cshake256_framed_32(
            b"QSAG.POLICY.FS.SEAL.V1", &[&key, &record.lock_seal()]));
        let generation = guard.restore_from_durable_checkpoint(&record.read()?, key.expose(), min_generation)
            .map_err(|_| std::io::Error::other("invalid policy checkpoint"))?;
        Ok(Self { record, key, generation })
    }
    pub fn generation(&self) -> u64 { self.generation }
    /// Call before releasing any authorized signature; failure is fail-closed.
    pub fn sync_persist(&mut self, guard: &PolicySignerGuardShare) -> std::io::Result<()> {
        let generation = self.generation.max(guard.durable_generation.get()).checked_add(1)
            .ok_or_else(|| std::io::Error::other("generation exhausted"))?;
        self.record.replace(&guard.export_durable_checkpoint(self.key.expose(), generation))?;
        self.generation = generation;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(feature = "std")]
    #[test]
    fn disk_checkpoint_recovers_burns_and_seal_binding() {
        let path = std::env::temp_dir().join(std::format!("policy-ledger-{}-{}", std::process::id(), std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        let mut guards = trusted_dealer_setup_for_testing([3; 32], &[1, 2]);
        let mut disk = FsPolicyDurableLedger::create_new(&path, [8; 32], &guards[0]).unwrap();
        guards[0].record_approved_intent(4, [5; 32], [6; 32]);
        disk.sync_persist(&guards[0]).unwrap();
        let generation = disk.generation();
        drop(disk);
        let mut restarted = trusted_dealer_setup_for_testing([3; 32], &[1, 2]);
        let disk = FsPolicyDurableLedger::open_existing(&path, [8; 32], &mut restarted[0], generation).unwrap();
        assert!(restarted[0].is_nonce_burned(&[5; 32]));
        assert!(restarted[0].is_session_burned(&[6; 32]));
        drop(disk);
        std::fs::remove_file(&path).unwrap();
        std::fs::remove_file(std::format!("{}.lock", path.display())).unwrap();
    }

    #[test]
    fn authenticated_malformed_snapshots_are_atomic_and_poison_is_durable() {
        let key = [0x42; 32];
        let mut guards = trusted_dealer_setup_for_testing([0x61; 32], &[1, 2]);
        let guard = &mut guards[0];
        let snapshot = guard.export_durable_checkpoint(&key, 7);
        let body = &snapshot[..snapshot.len() - 32];
        for length in 0..body.len() {
            let mut malformed = body[..length].to_vec();
            let tag = cshake256_framed_32(DOMAIN, &[&key, &malformed]);
            malformed.extend_from_slice(&tag);
            assert!(
                guard
                    .restore_from_durable_checkpoint(&malformed, &key, 7)
                    .is_err()
            );
            assert_eq!(guard.export_durable_checkpoint(&key, 7), snapshot);
        }
        let mut trailing = body.to_vec();
        trailing.push(0);
        let tag = cshake256_framed_32(DOMAIN, &[&key, &trailing]);
        trailing.extend_from_slice(&tag);
        assert_eq!(
            guard.restore_from_durable_checkpoint(&trailing, &key, 7),
            Err(PolicyGuardError::InvalidCheckpoint)
        );
        guard.next_slot.set(3);
        guard.retire_peer_slot(2, 5);
        let retired = guard.export_durable_checkpoint(&key, 8);
        let mut restarted = trusted_dealer_setup_for_testing([0x61; 32], &[1, 2]);
        let fresh = &mut restarted[0];
        fresh
            .restore_from_durable_checkpoint(&retired, &key, 8)
            .unwrap();
        assert_eq!(fresh.next_slot.get(), 3);
        assert!(fresh.preproc_r[..3].iter().all(|r| *r == [0; 2]));
        assert!(fresh.is_peer_slot_consumed(2, 5));
        assert_eq!(fresh.preproc_incoming_keys[0].1[5], [0; 2]);
        guard.active_phase = Some((3, 1));
        let in_flight = guard.export_durable_checkpoint(&key, 8);
        fresh
            .restore_from_durable_checkpoint(&in_flight, &key, 8)
            .unwrap();
        assert!(fresh.poisoned);
        guard.poison();
        let poisoned = guard.export_durable_checkpoint(&key, 9);
        fresh
            .restore_from_durable_checkpoint(&poisoned, &key, 9)
            .unwrap();
        assert!(fresh.poisoned);
        assert_eq!(fresh.bdoz_alpha_share, [0; 2]);
        assert_eq!(
            fresh.restore_from_durable_checkpoint(&retired, &key, 0),
            Err(PolicyGuardError::Rollback)
        );
    }
}
