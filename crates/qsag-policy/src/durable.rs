//! Canonical authenticated V6 ledger codec. This is a snapshot, not a storage
//! transaction: callers must atomically persist it and fence its generation in
//! trusted monotonic storage before releasing a signature. A MAC alone cannot
//! detect rollback of both the checkpoint and its external generation fence.
//!
//! Integers are big endian. The authenticated body binds the key identity,
//! enrolled party, monotonic generation, window, spend, configured replay
//! capacity, local slot cursor, flags, replay sets, reserved watermarks, peer
//! slot bitmaps, and verified velocity state. Replay counts and slot cursors
//! use u32; each peer bitmap has a u32 word count followed by u64 words. Peers
//! are strictly ascending and unused bitmap bits must be zero. A 32-byte keyed
//! cSHAKE256 framed tag follows. Trailing bytes and noncanonical encodings fail.
//! Restore rebuilds the velocity guard and rejects spend above its pinned cap.
//! Key identity identifies the original secret provisioning, not just party ID.
//! Restore requires the same provisioned secrets; secrets are never serialized.
//! Earlier codec versions are rejected rather than reinterpreted.

use super::*;
use qsag_verified::StatefulVelocityGuard;

const DOMAIN: &[u8] = b"QSAG.POLICY.DURABLE_LEDGER.V6";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PolicyGuardError {
    InvalidCheckpoint,
    AuthenticationFailed,
    WrongGuard,
    Rollback,
    ActiveSession,
}

/// Whether every identifier in `old` is still burned by `new` or lies at or below `floor`.
/// Both lists are strictly ascending, so one merge pass decides it.
fn retains_burns(old: &[[u8; 32]], new: &[[u8; 32]], floor: Option<[u8; 32]>) -> bool {
    let mut new = new.iter().peekable();
    old.iter().all(|burned| {
        if floor.is_some_and(|f| *burned <= f) {
            return true;
        }
        while new.next_if(|candidate| *candidate < burned).is_some() {}
        new.peek() == Some(&burned)
    })
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
    fn count(&mut self) -> Result<usize, PolicyGuardError> {
        Ok(u32::from_be_bytes(self.take()?) as usize)
    }
    /// A replay set: count, a reserved u32 that must be zero, then the entries.
    fn replay_set(&mut self, capacity: usize) -> Result<Vec<[u8; 32]>, PolicyGuardError> {
        let count = self.count()?;
        let reserved = self.count()?;
        if count > capacity || reserved != 0 || count > self.0.len() / 32 {
            return Err(PolicyGuardError::InvalidCheckpoint);
        }
        let mut values = Vec::with_capacity(count);
        for _ in 0..count {
            values.push(self.take()?);
        }
        Ok(values)
    }
}

impl PolicySignerGuardShare {
    fn enrolled_checkpoint_key(&self, ledger: &[u8; 32]) -> SecretBuffer<[u8; 32]> {
        SecretBuffer(cshake256_framed_32(
            b"QSAG.POLICY.GUARD.CHECKPOINT.KEY.V1",
            &[&self.local_salt_seed, ledger],
        ))
    }

    /// Authenticate this ledger's checkpoint with the enrolled guard's private key.
    pub fn export_enrolled_checkpoint(&self, ledger: &[u8; 32], generation: u64) -> Vec<u8> {
        self.export_durable_checkpoint(&self.enrolled_checkpoint_key(ledger), generation)
    }

    /// Restore a checkpoint authenticated by this guard for this ledger.
    pub fn restore_enrolled_checkpoint(
        &mut self,
        ledger: &[u8; 32],
        bytes: &[u8],
        generation: u64,
    ) -> Result<u64, PolicyGuardError> {
        self.restore_from_durable_checkpoint(
            bytes,
            &self.enrolled_checkpoint_key(ledger),
            generation,
        )
    }

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
        out.extend_from_slice(&(self.replay_capacity as u32).to_be_bytes());
        out.extend_from_slice(&(self.next_slot.get() as u32).to_be_bytes());
        out.push(u8::from(self.poisoned || self.active_phase.is_some()));
        out.push(u8::from(self.require_authenticated_initiator));
        for values in [&self.burned_intent_nonces, &self.burned_sessions] {
            out.extend_from_slice(&(values.len() as u32).to_be_bytes());
            out.extend_from_slice(&0u32.to_be_bytes());
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
        for (peer, words) in peers {
            out.extend_from_slice(&peer.to_be_bytes());
            out.extend_from_slice(&(words.len() as u32).to_be_bytes());
            for word in words {
                out.extend_from_slice(&word.to_be_bytes());
            }
        }
        out.extend_from_slice(&self.velocity_generation.to_be_bytes());
        let pinned_cap = self.verified_velocity.as_ref().map(|g| g.cap_units());
        out.push(u8::from(pinned_cap.is_some()));
        out.extend_from_slice(&pinned_cap.unwrap_or(0).to_be_bytes());
        let tag = cshake256_framed_32(DOMAIN, &[storage_mac_key, &out]);
        out.extend_from_slice(&tag);
        out
    }

    /// The largest checkpoint this guard can be asked to restore: its committed pool size
    /// and peer set fix the slot bitmaps, and each replay set holds at most
    /// [`MAX_POLICY_CAPACITY`] identifiers. `None` only if that does not fit in `usize`.
    pub fn max_durable_checkpoint_len(&self) -> Option<usize> {
        // Domain, key id, party, generation, window, spend, capacity, cursor, two flags.
        const HEAD: usize = DOMAIN.len() + 32 + 2 + 8 + 8 + 16 + 4 + 4 + 2;
        // Two replay sets (count, reserved word, entries) and two optional floors.
        const REPLAY: usize = 2 * (8 + MAX_POLICY_CAPACITY * 32) + 2 * 33;
        // Peer count; velocity generation, pinned flag and cap; tag.
        const TAIL: usize = 2 + 8 + 1 + 16 + 32;
        let per_peer = self
            .preproc_r
            .len()
            .div_ceil(64)
            .checked_mul(8)?
            .checked_add(2 + 4)?;
        self.consumed_peer_slots
            .len()
            .checked_mul(per_peer)?
            .checked_add(HEAD + REPLAY + TAIL)
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
        if !ct_eq_bytes(&r.take::<32>()?, &self.durable_key_id)
            || u16::from_be_bytes(r.take()?) != self.enrolled_party_id
            || self.party_id != self.enrolled_party_id
        {
            return Err(PolicyGuardError::WrongGuard);
        }
        let generation = u64::from_be_bytes(r.take()?);
        let window = u64::from_be_bytes(r.take()?);
        let spend = u128::from_be_bytes(r.take()?);
        let replay_capacity = r.count()?;
        if replay_capacity == 0 || replay_capacity > MAX_POLICY_CAPACITY {
            return Err(PolicyGuardError::InvalidCheckpoint);
        }
        let next = r.count()?;
        let poisoned = r.flag()?;
        let authenticated = r.flag()?;
        let nonces = r.replay_set(replay_capacity)?;
        let sessions = r.replay_set(replay_capacity)?;
        let nonce_floor = if r.flag()? {
            Some(r.take::<32>()?)
        } else {
            if r.take::<32>()? != [0; 32] {
                return Err(PolicyGuardError::InvalidCheckpoint);
            }
            None
        };
        let session_floor = if r.flag()? {
            Some(r.take::<32>()?)
        } else {
            if r.take::<32>()? != [0; 32] {
                return Err(PolicyGuardError::InvalidCheckpoint);
            }
            None
        };
        if nonces.windows(2).any(|w| w[0] >= w[1])
            || sessions.windows(2).any(|w| w[0] >= w[1])
            || nonces.iter().any(|n| nonce_floor.is_some_and(|f| *n <= f))
            || sessions
                .iter()
                .any(|n| session_floor.is_some_and(|f| *n <= f))
        {
            return Err(PolicyGuardError::InvalidCheckpoint);
        }
        let count = r.short()?;
        if next > self.preproc_r.len() || count != self.consumed_peer_slots.len() {
            return Err(PolicyGuardError::InvalidCheckpoint);
        }
        let mut peers = Vec::with_capacity(count);
        for _ in 0..count {
            let peer = u16::from_be_bytes(r.take()?);
            let word_count = r.count()?;
            if word_count != self.preproc_r.len().div_ceil(64) || word_count > r.0.len() / 8 {
                return Err(PolicyGuardError::InvalidCheckpoint);
            }
            let mut words = Vec::with_capacity(word_count);
            for _ in 0..word_count {
                words.push(u64::from_be_bytes(r.take()?));
            }
            let tail = self.preproc_r.len() % 64;
            if tail != 0 && words.last().is_some_and(|w| *w >> tail != 0) {
                return Err(PolicyGuardError::InvalidCheckpoint);
            }
            if peers.last().is_some_and(|(p, _)| *p >= peer)
                || !self.consumed_peer_slots.iter().any(|p| p.0 == peer)
            {
                return Err(PolicyGuardError::InvalidCheckpoint);
            }
            peers.push((peer, words));
        }
        let velocity_generation = u64::from_be_bytes(r.take()?);
        let pinned = r.flag()?;
        let cap = u128::from_be_bytes(r.take()?);
        if !r.0.is_empty()
            || (!pinned && (cap != 0 || spend != 0 || velocity_generation != 0))
            || (spend != 0 && velocity_generation == 0)
        {
            return Err(PolicyGuardError::InvalidCheckpoint);
        }
        // Rebuild the verified guard before touching the ledger: the snapshot's spend must
        // pass the extracted cap check under its own pinned cap.
        let verified = if pinned {
            let (guard, _) = rebuild_verified_velocity(
                window,
                cap,
                self.durable_key_id,
                velocity_generation,
                spend,
            )
            .ok_or(PolicyGuardError::InvalidCheckpoint)?;
            Some(guard)
        } else {
            None
        };
        if generation < min_expected_generation.max(self.durable_generation.get())
            || velocity_generation < self.velocity_generation
            || window < self.current_window_id
            || (window == self.current_window_id && spend < self.accumulated_window_spend)
            // Replay sets and floors belong to one window; a newer window starts them afresh.
            || (window == self.current_window_id
                && (nonce_floor < self.min_nonce_watermark
                    || session_floor < self.min_session_watermark
                    || !retains_burns(&self.burned_intent_nonces, &nonces, nonce_floor)
                    || !retains_burns(&self.burned_sessions, &sessions, session_floor)))
            || next < self.next_slot.get()
            || (self.poisoned && !poisoned)
            || (self.require_authenticated_initiator && !authenticated)
            || self.consumed_peer_slots.iter().any(|(p, mask)| {
                !peers.iter().any(|(q, new)| {
                    p == q
                        && new.len() == mask.len()
                        && new.iter().zip(mask).all(|(n, m)| n & m == *m)
                })
            })
        {
            return Err(PolicyGuardError::Rollback);
        }
        self.current_window_id = window;
        self.accumulated_window_spend = spend;
        self.verified_velocity = verified;
        self.velocity_generation = velocity_generation;
        self.replay_capacity = replay_capacity;
        self.burned_intent_nonces = nonces;
        self.min_nonce_watermark = nonce_floor;
        self.burned_sessions = sessions;
        self.min_session_watermark = session_floor;
        self.next_slot.set(next);
        self.require_authenticated_initiator = authenticated;
        self.durable_generation.set(generation);
        for slot in 0..next {
            self.retire_own_slot(slot);
        }
        for (peer, words) in &peers {
            for (index, word) in words.iter().enumerate() {
                for bit in 0..64 {
                    if word & (1u64 << bit) != 0 {
                        self.retire_peer_slot(*peer, index * 64 + bit);
                    }
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

/// A locked record together with the MAC key that seals it to its sidecar: the supplied
/// key is bound to the sidecar's `(dev, ino)` identity and its genesis seal, both taken from
/// the lock the handle holds, so a record cannot migrate to a replacement sidecar inode.
#[cfg(feature = "std")]
struct SealedRecord {
    record: qsag_asm::durable::LockedRecord,
    key: SecretBytes<32>,
}
#[cfg(feature = "std")]
impl SealedRecord {
    fn open(
        path: std::path::PathBuf,
        key: [u8; 32],
        domain: &[u8],
        create: bool,
    ) -> std::io::Result<Self> {
        let key = SecretBuffer(key);
        let record = if create {
            qsag_asm::durable::LockedRecord::create_new(path)?
        } else {
            qsag_asm::durable::LockedRecord::open_existing(path)?
        };
        let key = secret_digest(domain, &[&*key, &record.lock_inode(), &record.lock_seal()]);
        Ok(Self { record, key })
    }
}

/// Disk-backed authenticated checkpoints, sealed to their lock sidecar.
/// Whole-directory rollback still requires an external monotonic generation fence.
#[cfg(feature = "std")]
pub struct FsPolicyDurableLedger {
    sealed: SealedRecord,
    generation: u64,
}
#[cfg(feature = "std")]
impl FsPolicyDurableLedger {
    const DOMAIN: &[u8] = b"QSAG.POLICY.FS.SEAL.V2";

    pub fn create_new(
        path: impl Into<std::path::PathBuf>,
        key: [u8; 32],
        guard: &PolicySignerGuardShare,
    ) -> std::io::Result<Self> {
        let mut ledger = Self {
            sealed: SealedRecord::open(path.into(), key, Self::DOMAIN, true)?,
            generation: guard.durable_generation.get(),
        };
        ledger.sync_persist(guard)?;
        Ok(ledger)
    }
    pub fn open_existing(
        path: impl Into<std::path::PathBuf>,
        key: [u8; 32],
        guard: &mut PolicySignerGuardShare,
        min_generation: u64,
    ) -> std::io::Result<Self> {
        let sealed = SealedRecord::open(path.into(), key, Self::DOMAIN, false)?;
        let bound = guard
            .max_durable_checkpoint_len()
            .ok_or_else(|| std::io::Error::other("policy checkpoint bound overflow"))?;
        let generation = guard
            .restore_from_durable_checkpoint(
                &sealed.record.read_bounded(bound)?,
                &sealed.key,
                min_generation,
            )
            .map_err(|_| std::io::Error::other("invalid policy checkpoint"))?;
        Ok(Self { sealed, generation })
    }
    pub fn generation(&self) -> u64 {
        self.generation
    }
    /// Call before releasing any authorized signature; failure is fail-closed.
    pub fn sync_persist(&mut self, guard: &PolicySignerGuardShare) -> std::io::Result<()> {
        let generation = self
            .generation
            .max(guard.durable_generation.get())
            .checked_add(1)
            .ok_or_else(|| std::io::Error::other("generation exhausted"))?;
        self.sealed
            .record
            .replace(&guard.export_durable_checkpoint(&self.sealed.key, generation))?;
        self.generation = generation;
        Ok(())
    }
}

/// Independent monotonic generation fence for [`FsPolicyDurableLedger`], stored in a
/// separate [`qsag_asm::durable::LockedRecord`] domain so rolling back the policy checkpoint
/// file is caught on [`FsPolicyDurableLedger::open_existing`].
#[cfg(feature = "std")]
pub struct FsPolicyGenerationFence {
    sealed: SealedRecord,
    generation: u64,
    failed: bool,
}

#[cfg(feature = "std")]
impl FsPolicyGenerationFence {
    const DOMAIN: &[u8] = b"QSAG.POLICY.GEN.FENCE.V2";

    pub fn create_new(
        path: impl Into<std::path::PathBuf>,
        key: [u8; 32],
        initial_generation: u64,
    ) -> std::io::Result<Self> {
        let fence = Self {
            sealed: SealedRecord::open(path.into(), key, Self::DOMAIN, true)?,
            generation: initial_generation,
            failed: false,
        };
        fence
            .sealed
            .record
            .replace(&fence.encode(initial_generation))?;
        Ok(fence)
    }

    pub fn open_existing(
        path: impl Into<std::path::PathBuf>,
        key: [u8; 32],
    ) -> std::io::Result<Self> {
        let mut fence = Self {
            sealed: SealedRecord::open(path.into(), key, Self::DOMAIN, false)?,
            generation: 0,
            failed: false,
        };
        fence.generation = fence.read_disk_generation()?;
        Ok(fence)
    }

    pub const fn generation(&self) -> u64 {
        self.generation
    }

    pub fn ratchet_to(&mut self, next_generation: u64) -> std::io::Result<()> {
        if self.failed {
            return Err(std::io::Error::other("policy generation fence failed"));
        }
        self.failed = true;
        let result = self.ratchet_inner(next_generation);
        if result.is_ok() {
            self.failed = false;
        }
        result
    }

    fn ratchet_inner(&mut self, next_generation: u64) -> std::io::Result<()> {
        let disk_gen = self.read_disk_generation()?;
        if disk_gen != self.generation || next_generation < self.generation {
            return Err(std::io::Error::other("policy generation fence rollback"));
        }
        if next_generation > self.generation {
            self.sealed.record.replace(&self.encode(next_generation))?;
            self.generation = next_generation;
        }
        Ok(())
    }

    fn tag(&self, gen_be: &[u8]) -> [u8; 32] {
        let record = &self.sealed.record;
        cshake256_framed_32(
            Self::DOMAIN,
            &[
                &*self.sealed.key,
                &record.lock_inode(),
                &record.lock_seal(),
                gen_be,
            ],
        )
    }

    fn encode(&self, generation: u64) -> Vec<u8> {
        let gen_be = generation.to_be_bytes();
        let mut out = Vec::with_capacity(40);
        out.extend_from_slice(&gen_be);
        out.extend_from_slice(&self.tag(&gen_be));
        out
    }

    fn read_disk_generation(&self) -> std::io::Result<u64> {
        let raw = self.sealed.record.read_bounded(40)?;
        let (gen_be, tag) = raw
            .split_first_chunk::<8>()
            .filter(|(_, tag)| tag.len() == 32)
            .ok_or_else(|| std::io::Error::other("invalid policy fence length"))?;
        if !ct_eq_bytes(&self.tag(gen_be), tag) {
            return Err(std::io::Error::other("invalid policy fence MAC"));
        }
        Ok(u64::from_be_bytes(*gen_be))
    }
}

const SHARED_DOMAIN: &[u8] = b"QSAG.POLICY.SHARED_LEDGER.V2";

impl SharedWindowSpendLedger {
    /// Monotonic revision to fence outside the checkpoint's rollback domain.
    pub const fn generation(&self) -> u64 {
        self.generation
    }

    /// Authenticate the shared accounting state. Persist this together with participating
    /// guard checkpoints before release. Recovery must retain the same window authority.
    pub fn export_durable_checkpoint(&self, storage_mac_key: &[u8; 32]) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(SHARED_DOMAIN);
        out.extend_from_slice(&self.policy_digest);
        out.extend_from_slice(&self.authority_binding());
        out.extend_from_slice(&self.generation.to_be_bytes());
        out.extend_from_slice(&self.current_window_id.to_be_bytes());
        out.extend_from_slice(&self.accumulated_window_spend.to_be_bytes());
        out.extend_from_slice(&(self.replay_capacity as u32).to_be_bytes());
        for (values, floor) in [
            (&self.burned_intent_nonces, self.min_nonce_watermark),
            (&self.burned_sessions, self.min_session_watermark),
        ] {
            out.extend_from_slice(&(values.len() as u32).to_be_bytes());
            for value in values {
                out.extend_from_slice(value);
            }
            out.push(u8::from(floor.is_some()));
            out.extend_from_slice(&floor.unwrap_or([0; 32]));
        }
        let tag = cshake256_framed_32(SHARED_DOMAIN, &[storage_mac_key, &out]);
        out.extend_from_slice(&tag);
        out
    }

    fn authority_binding(&self) -> [u8; 32] {
        match &self.window_authority {
            None => cshake256_framed_32(SHARED_DOMAIN, &[b"no authority"]),
            Some(a) => cshake256_framed_32(SHARED_DOMAIN, &[b"authority", &a.policy_id, &a.key]),
        }
    }

    /// Restore only a fully authenticated, canonical, nonregressing state. The generation
    /// floor must come from independently retained storage, never from the supplied bytes.
    /// Restore into a newly provisioned handle under the same exclusive storage lock.
    pub fn restore_from_durable_checkpoint(
        &mut self,
        bytes: &[u8],
        storage_mac_key: &[u8; 32],
        min_expected_generation: u64,
    ) -> Result<u64, PolicyGuardError> {
        let split = bytes
            .len()
            .checked_sub(32)
            .ok_or(PolicyGuardError::InvalidCheckpoint)?;
        let (body, tag) = bytes.split_at(split);
        if !ct_eq_bytes(
            &cshake256_framed_32(SHARED_DOMAIN, &[storage_mac_key, body]),
            tag,
        ) {
            return Err(PolicyGuardError::AuthenticationFailed);
        }
        let mut r = Reader(body);
        if r.take::<28>()? != SHARED_DOMAIN {
            return Err(PolicyGuardError::InvalidCheckpoint);
        }
        if !ct_eq_bytes(&r.take::<32>()?, &self.policy_digest)
            || !ct_eq_bytes(&r.take::<32>()?, &self.authority_binding())
        {
            return Err(PolicyGuardError::WrongGuard);
        }
        let generation = u64::from_be_bytes(r.take()?);
        let window = u64::from_be_bytes(r.take()?);
        let spend = u128::from_be_bytes(r.take()?);
        let replay_capacity = r.count()?;
        if replay_capacity == 0 || replay_capacity > MAX_POLICY_CAPACITY {
            return Err(PolicyGuardError::InvalidCheckpoint);
        }
        let mut sets = Vec::with_capacity(2);
        for _ in 0..2 {
            let count = r.count()?;
            if count > replay_capacity || count > r.0.len() / 32 {
                return Err(PolicyGuardError::InvalidCheckpoint);
            }
            let mut values = Vec::with_capacity(count);
            for _ in 0..count {
                values.push(r.take::<32>()?);
            }
            let present = r.flag()?;
            let raw = r.take::<32>()?;
            if !present && raw != [0; 32] {
                return Err(PolicyGuardError::InvalidCheckpoint);
            }
            let floor = present.then_some(raw);
            if values.windows(2).any(|w| w[0] >= w[1])
                || values.iter().any(|v| floor.is_some_and(|f| *v <= f))
            {
                return Err(PolicyGuardError::InvalidCheckpoint);
            }
            sets.push((values, floor));
        }
        if !r.0.is_empty() {
            return Err(PolicyGuardError::InvalidCheckpoint);
        }
        if self.failed
            || generation < min_expected_generation.max(self.generation)
            || window < self.current_window_id
            || (window == self.current_window_id && spend < self.accumulated_window_spend)
        {
            return Err(PolicyGuardError::Rollback);
        }
        for ((old, old_floor), (new, floor)) in [
            (&self.burned_intent_nonces, self.min_nonce_watermark),
            (&self.burned_sessions, self.min_session_watermark),
        ]
        .into_iter()
        .zip(&sets)
        {
            if window == self.current_window_id
                && (*floor < old_floor || !retains_burns(old, new, *floor))
            {
                return Err(PolicyGuardError::Rollback);
            }
        }
        let (sessions, session_floor) = sets.pop().ok_or(PolicyGuardError::InvalidCheckpoint)?;
        let (nonces, nonce_floor) = sets.pop().ok_or(PolicyGuardError::InvalidCheckpoint)?;
        // Rehydrate only after authentication, policy binding, and rollback checks.
        // The checkpoint generation is the verified guard's monotone request nonce.
        let cap = self
            .verified_velocity
            .as_ref()
            .ok_or(PolicyGuardError::InvalidCheckpoint)?
            .cap_units();
        let mut verified =
            StatefulVelocityGuard::new_window(window, cap, self.policy_digest, self.policy_digest);
        if generation != 0 {
            let (next, result) = verified.authorize_spend(qsag_verified::VelocitySpendRequest {
                window_id: window,
                nonce: generation,
                amount_units: spend,
                policy_pin: self.policy_digest,
                authority_pin: self.policy_digest,
            });
            result.map_err(|_| PolicyGuardError::InvalidCheckpoint)?;
            verified = next;
        } else if spend != 0 {
            return Err(PolicyGuardError::InvalidCheckpoint);
        }
        self.verified_velocity = Some(verified);
        self.generation = generation;
        self.current_window_id = window;
        self.accumulated_window_spend = spend;
        self.replay_capacity = replay_capacity;
        self.burned_intent_nonces = nonces;
        self.min_nonce_watermark = nonce_floor;
        self.burned_sessions = sessions;
        self.min_session_watermark = session_floor;
        Ok(generation)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(feature = "std")]
    #[test]
    fn disk_checkpoint_recovers_burns_and_seal_binding() {
        let path = std::env::temp_dir().join(std::format!(
            "policy-ledger-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let mut guards = trusted_dealer_setup_for_testing([3; 32], &[1, 2]);
        let mut disk = FsPolicyDurableLedger::create_new(&path, [8; 32], &guards[0]).unwrap();
        guards[0]
            .record_approved_intent(100, 4, [5; 32], [6; 32])
            .unwrap();
        disk.sync_persist(&guards[0]).unwrap();
        let generation = disk.generation();
        drop(disk);
        let mut restarted = trusted_dealer_setup_for_testing([3; 32], &[1, 2]);
        let disk =
            FsPolicyDurableLedger::open_existing(&path, [8; 32], &mut restarted[0], generation)
                .unwrap();
        assert!(restarted[0].is_nonce_burned(&[5; 32]));
        assert!(restarted[0].is_session_burned(&[6; 32]));
        // The verified guard came back with the snapshot's cap, spend and request nonce.
        let verified = restarted[0].verified_velocity.as_ref().unwrap();
        assert_eq!(
            (
                verified.cap_units(),
                verified.spent_units(),
                verified.last_nonce()
            ),
            (100, 4, 1)
        );
        // It still enforces that cap: 97 more would exceed 100 and changes nothing.
        assert_eq!(
            restarted[0].record_approved_intent(100, 101, [7; 32], [8; 32]),
            Err(PolicyViolation::VelocityCapOverflowOrExceeded)
        );
        assert_eq!(restarted[0].accumulated_window_spend(), 4);
        assert!(!restarted[0].is_nonce_burned(&[7; 32]));
        restarted[0]
            .record_approved_intent(100, 100, [7; 32], [8; 32])
            .unwrap();
        assert_eq!(
            restarted[0]
                .verified_velocity
                .as_ref()
                .unwrap()
                .last_nonce(),
            2
        );
        drop(disk);
        std::fs::remove_file(&path).unwrap();
        std::fs::remove_file(std::format!("{}.lock", path.display())).unwrap();
    }

    #[test]
    fn merge_containment_agrees_with_the_quadratic_definition() {
        let id = |b: u8| [b; 32];
        let cases: [(&[u8], &[u8], Option<u8>); 9] = [
            (&[], &[], None),
            (&[], &[1, 2], None),
            (&[1, 3], &[1, 2, 3], None),
            (&[1, 3], &[1, 2], None),
            (&[4], &[], None),
            (&[1, 2, 9], &[9], Some(2)),
            (&[1, 2, 9], &[9], Some(1)),
            (&[5, 6], &[4, 5, 6, 7], Some(0)),
            (&[5, 8], &[4, 5, 6, 7], Some(5)),
        ];
        for (old, new, floor) in cases {
            let old: Vec<_> = old.iter().map(|b| id(*b)).collect();
            let new: Vec<_> = new.iter().map(|b| id(*b)).collect();
            let floor = floor.map(id);
            let quadratic = old
                .iter()
                .all(|v| new.contains(v) || floor.is_some_and(|f| *v <= f));
            assert_eq!(retains_burns(&old, &new, floor), quadratic);
        }
    }

    #[test]
    fn newer_window_checkpoint_restores_over_live_floors_and_burns() {
        let key = [0x42; 32];
        let provision = || {
            let mut guards = trusted_dealer_setup_for_testing([0x63; 32], &[1, 2]);
            guards
                .remove(0)
                .with_window_authority([7; 32], [8; 32])
                .unwrap()
        };
        let burn = |guard: &mut PolicySignerGuardShare, spend: u128, tag: u8| {
            guard
                .record_approved_intent(1000, spend, [tag; 32], [tag ^ 0x80; 32])
                .unwrap();
        };
        // The live handle: window 0 with floors and burned identifiers above them.
        let mut live = provision();
        burn(&mut live, 10, 0x20);
        burn(&mut live, 20, 0x30);
        live.compact_monotone_replay_floor([0x10; 32], [0x90; 32])
            .unwrap();
        let same_window = live.export_durable_checkpoint(&key, 1);
        // A replica that moved on to window 1, where nothing is floored or burned yet.
        let mut ahead = provision();
        ahead
            .restore_from_durable_checkpoint(&same_window, &key, 1)
            .unwrap();
        ahead
            .advance_velocity_window(&WindowAdvanceAuthorization::new(&[8; 32], &[7; 32], 0, 1))
            .unwrap();
        burn(&mut ahead, 5, 0x01);
        let newer_window = ahead.export_durable_checkpoint(&key, 2);
        assert_eq!(
            live.restore_from_durable_checkpoint(&newer_window, &key, 2),
            Ok(2)
        );
        assert_eq!(live.current_window_id(), 1);
        assert_eq!(live.accumulated_window_spend(), 5);
        assert!(live.is_nonce_burned(&[0x01; 32]));
        assert!(!live.is_nonce_burned(&[0x20; 32]));
        assert_eq!(live.min_nonce_watermark, None);

        // Within one window, losing a burn or lowering a floor is still a rollback.
        let mut live = provision();
        burn(&mut live, 10, 0x20);
        let before_burn = {
            let mut earlier = provision();
            earlier
                .record_approved_intent(1000, 10, [0x21; 32], [0xa1; 32])
                .unwrap();
            earlier.export_durable_checkpoint(&key, 5)
        };
        assert_eq!(
            live.restore_from_durable_checkpoint(&before_burn, &key, 0),
            Err(PolicyGuardError::Rollback)
        );
        let unfloored = live.export_durable_checkpoint(&key, 6);
        live.compact_monotone_replay_floor([0x10; 32], [0x10; 32])
            .unwrap();
        assert_eq!(
            live.restore_from_durable_checkpoint(&unfloored, &key, 0),
            Err(PolicyGuardError::Rollback)
        );
        assert!(live.is_nonce_burned(&[0x20; 32]));
        assert_eq!(live.min_nonce_watermark, Some([0x10; 32]));
    }

    /// Bookkeeping only: a guard with `slots` pool entries and `peers` peer bitmaps.
    #[cfg(feature = "std")]
    fn wide_guard(slots: usize, peers: u16) -> PolicySignerGuardShare {
        let mut guard = trusted_dealer_setup_for_testing([0x64; 32], &[1, 2]).remove(0);
        guard.preproc_r.resize(slots, [0; 2]);
        guard.consumed_peer_slots = (2..2 + peers)
            .map(|peer| (peer, alloc::vec![0u64; slots.div_ceil(64)]))
            .collect();
        guard
    }

    #[cfg(feature = "std")]
    #[test]
    fn max_capacity_many_peer_checkpoint_restores_within_its_derived_bound() {
        // 700 peers at the maximum pool size: larger than any fixed per-capacity allowance.
        let guard = wide_guard(MAX_POLICY_CAPACITY, 700);
        let bound = guard.max_durable_checkpoint_len().unwrap();
        let encoded = guard.export_durable_checkpoint(&[1; 32], 1).len();
        assert!(encoded > MAX_POLICY_CAPACITY * 80 + 1024 * 1024);
        assert_eq!(bound - encoded, 2 * MAX_POLICY_CAPACITY * 32);
        let path = std::env::temp_dir().join(std::format!(
            "policy-wide-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let disk = FsPolicyDurableLedger::create_new(&path, [8; 32], &guard).unwrap();
        let generation = disk.generation();
        drop(disk);
        let mut restarted = wide_guard(MAX_POLICY_CAPACITY, 700);
        let reopened =
            FsPolicyDurableLedger::open_existing(&path, [8; 32], &mut restarted, generation);
        // A guard committed to a smaller peer set refuses the same file by size alone.
        let mut narrow = wide_guard(MAX_POLICY_CAPACITY, 1);
        assert!(narrow.max_durable_checkpoint_len().unwrap() < encoded);
        let refused = reopened.and_then(|disk| {
            drop(disk);
            FsPolicyDurableLedger::open_existing(&path, [8; 32], &mut narrow, generation)
                .map(|_| ())
        });
        std::fs::remove_file(&path).unwrap();
        std::fs::remove_file(std::format!("{}.lock", path.display())).unwrap();
        assert_eq!(refused.unwrap_err().kind(), std::io::ErrorKind::InvalidData);
        assert_eq!(restarted.consumed_peer_slots.len(), 700);
    }

    #[test]
    fn dynamic_slot_bitmap_restores_above_64_without_reopening_consumed_slots() {
        fn expanded() -> Vec<PolicySignerGuardShare> {
            let mut guards = trusted_dealer_setup_for_testing([0x61; 32], &[1, 2]);
            for guard in &mut guards {
                // This test exercises checkpoint bookkeeping, never cryptographic preprocessing.
                guard.preproc_r.resize(130, [0; 2]);
                for (_, words) in &mut guard.consumed_peer_slots {
                    words.resize(3, 0);
                }
                for (_, macs) in &mut guard.preproc_outgoing_macs {
                    macs.resize(130, [0; 2]);
                }
                for (_, keys) in &mut guard.preproc_incoming_keys {
                    keys.resize(130, [0; 2]);
                }
            }
            guards
        }
        let key = [0x42; 32];
        let mut guards = expanded();
        let before = guards[0].export_durable_checkpoint(&key, 1);
        guards[0].retire_peer_slot(2, 65);
        guards[0].retire_peer_slot(2, 129);
        let snapshot = guards[0].export_durable_checkpoint(&key, 2);
        let mut fresh = expanded();
        fresh[0]
            .restore_from_durable_checkpoint(&snapshot, &key, 2)
            .unwrap();
        assert!(fresh[0].is_peer_slot_consumed(2, 65));
        assert!(fresh[0].is_peer_slot_consumed(2, 129));
        assert!(!fresh[0].is_peer_slot_consumed(2, 64));
        assert_eq!(fresh[0].export_durable_checkpoint(&key, 2), snapshot);
        assert_eq!(
            fresh[0].restore_from_durable_checkpoint(&before, &key, 0),
            Err(PolicyGuardError::Rollback)
        );
    }

    #[cfg(feature = "std")]
    fn temp_record(tag: &str) -> std::path::PathBuf {
        std::env::temp_dir().join(std::format!(
            "{tag}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ))
    }

    #[cfg(feature = "std")]
    fn remove_record(path: &std::path::Path) {
        std::fs::remove_file(path).unwrap();
        std::fs::remove_file(std::format!("{}.lock", path.display())).unwrap();
    }

    /// The checkpoint and the fence are replaced by write-to-temporary, sync, rename: a
    /// crash while the next generation is being written tears only `<record>.tmp`, never
    /// the committed record. Recovery reads the committed generation and the next persist
    /// discards the torn temporary.
    #[cfg(feature = "std")]
    #[test]
    fn torn_checkpoint_write_recovers_the_committed_generation() {
        let path = temp_record("policy-torn-tmp");
        let tmp = std::path::PathBuf::from(std::format!("{}.tmp", path.display()));
        let mut guards = trusted_dealer_setup_for_testing([3; 32], &[1, 2]);
        let mut disk = FsPolicyDurableLedger::create_new(&path, [8; 32], &guards[0]).unwrap();
        guards[0]
            .record_approved_intent(100, 4, [5; 32], [6; 32])
            .unwrap();
        disk.sync_persist(&guards[0]).unwrap();
        let generation = disk.generation();
        drop(disk);
        let committed = std::fs::read(&path).unwrap();

        // Crash mid-write of the following checkpoint, at several torn lengths.
        for torn_len in [0usize, 1, 16, 17, committed.len() / 2, committed.len() - 1] {
            let mut torn = committed[..torn_len].to_vec();
            for (i, byte) in torn.iter_mut().enumerate().skip(torn_len / 2) {
                *byte ^= 0xa5 ^ i as u8;
            }
            // Model the durable writer: its temporary is private, just like the record.
            std::fs::copy(&path, &tmp).unwrap();
            std::fs::write(&tmp, &torn).unwrap();
            let mut restarted = trusted_dealer_setup_for_testing([3; 32], &[1, 2]);
            let mut disk =
                FsPolicyDurableLedger::open_existing(&path, [8; 32], &mut restarted[0], generation)
                    .unwrap();
            assert_eq!(disk.generation(), generation);
            assert!(restarted[0].is_nonce_burned(&[5; 32]));
            assert_eq!(restarted[0].accumulated_window_spend(), 4);
            assert_eq!(std::fs::read(&path).unwrap(), committed);
            // The next persist replaces the torn temporary and advances the generation.
            disk.sync_persist(&restarted[0]).unwrap();
            assert_eq!(disk.generation(), generation + 1);
            assert!(!tmp.exists());
            drop(disk);
            let mut again = trusted_dealer_setup_for_testing([3; 32], &[1, 2]);
            FsPolicyDurableLedger::open_existing(&path, [8; 32], &mut again[0], generation + 1)
                .unwrap();
            assert!(again[0].is_nonce_burned(&[5; 32]));
            std::fs::write(&path, &committed).unwrap();
        }

        // The committed record has no second copy: damage to it fails closed and is never
        // read as an older or empty state.
        for index in [0usize, 8, 16, committed.len() / 2, committed.len() - 1] {
            let mut corrupt = committed.clone();
            corrupt[index] ^= 1;
            std::fs::write(&path, &corrupt).unwrap();
            let mut restarted = trusted_dealer_setup_for_testing([3; 32], &[1, 2]);
            assert!(
                FsPolicyDurableLedger::open_existing(&path, [8; 32], &mut restarted[0], 0).is_err(),
                "byte {index}"
            );
            assert!(!restarted[0].is_nonce_burned(&[5; 32]));
        }
        for torn_len in [0usize, 15, 16, committed.len() - 1] {
            std::fs::write(&path, &committed[..torn_len]).unwrap();
            let mut restarted = trusted_dealer_setup_for_testing([3; 32], &[1, 2]);
            assert!(
                FsPolicyDurableLedger::open_existing(&path, [8; 32], &mut restarted[0], 0).is_err(),
                "length {torn_len}"
            );
        }
        remove_record(&path);
    }

    #[cfg(feature = "std")]
    #[test]
    fn torn_fence_write_recovers_the_committed_generation() {
        let path = temp_record("policy-torn-fence");
        let tmp = std::path::PathBuf::from(std::format!("{}.tmp", path.display()));
        let mut fence = FsPolicyGenerationFence::create_new(&path, [9; 32], 3).unwrap();
        fence.ratchet_to(7).unwrap();
        drop(fence);
        let committed = std::fs::read(&path).unwrap();
        // 16-byte record header, then `generation_be(8) || mac(32)`.
        assert_eq!(committed.len(), 16 + 40);

        for torn_len in [0usize, 1, 16, 24, committed.len() - 1] {
            std::fs::copy(&path, &tmp).unwrap();
            std::fs::write(&tmp, &committed[..torn_len]).unwrap();
            let mut fence = FsPolicyGenerationFence::open_existing(&path, [9; 32]).unwrap();
            assert_eq!(fence.generation(), 7);
            assert!(fence.ratchet_to(6).is_err());
            drop(fence);
            let mut fence = FsPolicyGenerationFence::open_existing(&path, [9; 32]).unwrap();
            fence.ratchet_to(8).unwrap();
            assert!(!tmp.exists());
            drop(fence);
            assert_eq!(
                FsPolicyGenerationFence::open_existing(&path, [9; 32])
                    .unwrap()
                    .generation(),
                8
            );
            std::fs::write(&path, &committed).unwrap();
        }
        // A damaged fence is refused; it is never read as a lower generation.
        for index in [0usize, 8, 16, 23, 24, committed.len() - 1] {
            let mut corrupt = committed.clone();
            corrupt[index] ^= 1;
            std::fs::write(&path, &corrupt).unwrap();
            assert!(
                FsPolicyGenerationFence::open_existing(&path, [9; 32]).is_err(),
                "byte {index}"
            );
        }
        remove_record(&path);
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
