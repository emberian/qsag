//! Canonical authenticated V4 ledger codec. This is a snapshot, not a storage
//! transaction: callers must atomically persist it and fence its generation in
//! trusted monotonic storage before releasing a signature. A MAC alone cannot
//! detect rollback of both the checkpoint and its external generation fence.
//!
//! All integers are big endian. The MAC covers, in order: the 29-byte domain
//! `QSAG.POLICY.DURABLE_LEDGER.V4`, key ID (32), enrolled party (u16), generation
//! (u64), window (u64), spend (u128), next local slot (u16), poisoned and
//! authenticated-initiator flags (one canonical 0/1 byte each), then nonce and
//! session windows (each: u16 count, zero u16 cursor, count * 32 bytes), then
//! two optional eviction watermarks (flag + 32 bytes each), then peer slots
//! (u16 count, strictly ascending (u16 party, u64 mask) pairs), then the verified
//! velocity state: request nonce (u64), pinned-cap flag and cap (u128, zero when
//! unpinned). A 32-byte keyed cSHAKE256 framed tag follows. On restore the extracted
//! velocity guard is rebuilt from window, cap, nonce and spend through its own
//! transition, so a snapshot whose spend exceeds its cap is refused. Trailing bytes and noncanonical encodings fail.
//! Key identity identifies the original secret provisioning, not just party ID.
//! Restore requires the same provisioned secrets; secrets are never serialized.

use super::*;

const DOMAIN: &[u8] = b"QSAG.POLICY.DURABLE_LEDGER.V4";

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
        out.extend_from_slice(&self.velocity_generation.to_be_bytes());
        let pinned_cap = self.verified_velocity.as_ref().map(|g| g.cap_units());
        out.push(u8::from(pinned_cap.is_some()));
        out.extend_from_slice(&pinned_cap.unwrap_or(0).to_be_bytes());
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
        if !ct_eq_bytes(&r.take::<32>()?, &self.durable_key_id)
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
        if nonce_cursor != 0
            || session_cursor != 0
            || nonces.windows(2).any(|w| w[0] >= w[1])
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
            let mask = u64::from_be_bytes(r.take()?);
            if peers.last().is_some_and(|&(p, _)| p >= peer)
                || !self.consumed_peer_slots.iter().any(|p| p.0 == peer)
            {
                return Err(PolicyGuardError::InvalidCheckpoint);
            }
            peers.push((peer, mask));
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
            || self
                .burned_intent_nonces
                .iter()
                .any(|n| !nonces.contains(n) && !nonce_floor.is_some_and(|f| *n <= f))
            || nonce_floor < self.min_nonce_watermark
            || session_floor < self.min_session_watermark
            || self
                .burned_sessions
                .iter()
                .any(|s| !sessions.contains(s) && !session_floor.is_some_and(|f| *s <= f))
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
        self.verified_velocity = verified;
        self.velocity_generation = velocity_generation;
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

#[cfg(feature = "std")]
fn policy_lock_inode(path: &std::path::Path) -> std::io::Result<[u8; 16]> {
    let mut os = path.as_os_str().to_os_string();
    os.push(".lock");
    let meta = std::fs::symlink_metadata(std::path::PathBuf::from(os))?;
    if !meta.is_file() || meta.file_type().is_symlink() {
        return Err(std::io::Error::other(
            "policy lock sidecar is not a regular file",
        ));
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

/// Disk-backed authenticated checkpoints. Both the sidecar `(dev, ino)` identity and
/// its genesis seal are bound into the MAC key derivation, preventing a record from
/// migrating to a replacement sidecar inode.
/// Whole-directory rollback still requires an external monotonic generation fence.
#[cfg(feature = "std")]
pub struct FsPolicyDurableLedger {
    path: std::path::PathBuf,
    lock_id: [u8; 16],
    record: qsag_asm::durable::LockedRecord,
    key: qsag_accel::ct::RedactedSecret<32>,
    generation: u64,
    initialized: bool,
}
#[cfg(feature = "std")]
impl FsPolicyDurableLedger {
    pub fn create_new(
        path: impl Into<std::path::PathBuf>,
        mut key: [u8; 32],
        guard: &PolicySignerGuardShare,
    ) -> std::io::Result<Self> {
        let path = path.into();
        let record = qsag_asm::durable::LockedRecord::create_new(&path)?;
        let lock_id = policy_lock_inode(&path)?;
        let derived = cshake256_framed_32(
            b"QSAG.POLICY.FS.SEAL.V2",
            &[&key, &lock_id, &record.lock_seal()],
        );
        ct_zeroize_bytes(&mut key);
        let key = qsag_accel::ct::RedactedSecret::new(derived);
        let mut ledger = Self {
            path,
            lock_id,
            record,
            key,
            generation: guard.durable_generation.get(),
            initialized: false,
        };
        ledger.sync_persist(guard)?;
        Ok(ledger)
    }
    pub fn open_existing(
        path: impl Into<std::path::PathBuf>,
        mut key: [u8; 32],
        guard: &mut PolicySignerGuardShare,
        min_generation: u64,
    ) -> std::io::Result<Self> {
        let path = path.into();
        let record = qsag_asm::durable::LockedRecord::open_existing(&path)?;
        let lock_id = policy_lock_inode(&path)?;
        let derived = cshake256_framed_32(
            b"QSAG.POLICY.FS.SEAL.V2",
            &[&key, &lock_id, &record.lock_seal()],
        );
        ct_zeroize_bytes(&mut key);
        let key = qsag_accel::ct::RedactedSecret::new(derived);
        let generation = guard
            .restore_from_durable_checkpoint(&record.read()?, key.expose(), min_generation)
            .map_err(|_| std::io::Error::other("invalid policy checkpoint"))?;
        Ok(Self {
            path,
            lock_id,
            record,
            key,
            generation,
            initialized: true,
        })
    }
    pub fn generation(&self) -> u64 {
        self.generation
    }
    /// Call before releasing any authorized signature; failure is fail-closed.
    pub fn sync_persist(&mut self, guard: &PolicySignerGuardShare) -> std::io::Result<()> {
        if policy_lock_inode(&self.path)? != self.lock_id {
            return Err(std::io::Error::other("policy lock sidecar inode replaced"));
        }
        if self.initialized {
            let meta = std::fs::symlink_metadata(&self.path)?;
            if !meta.is_file() {
                return Err(std::io::Error::other(
                    "policy checkpoint path is not a regular file",
                ));
            }
        }
        let generation = self
            .generation
            .max(guard.durable_generation.get())
            .checked_add(1)
            .ok_or_else(|| std::io::Error::other("generation exhausted"))?;
        self.record
            .replace(&guard.export_durable_checkpoint(self.key.expose(), generation))?;
        self.generation = generation;
        self.initialized = true;
        Ok(())
    }
}

/// Independent monotonic generation fence for [`FsPolicyDurableLedger`], stored in a
/// separate [`qsag_asm::durable::LockedRecord`] domain so rolling back the policy checkpoint
/// file is caught on [`FsPolicyDurableLedger::open_existing`].
#[cfg(feature = "std")]
pub struct FsPolicyGenerationFence {
    path: std::path::PathBuf,
    lock_id: [u8; 16],
    record: qsag_asm::durable::LockedRecord,
    key: qsag_accel::ct::RedactedSecret<32>,
    generation: u64,
}

#[cfg(feature = "std")]
impl FsPolicyGenerationFence {
    const DOMAIN: &[u8] = b"QSAG.POLICY.GEN.FENCE.V2";

    pub fn create_new(
        path: impl Into<std::path::PathBuf>,
        mut key: [u8; 32],
        initial_generation: u64,
    ) -> std::io::Result<Self> {
        let path = path.into();
        let record = qsag_asm::durable::LockedRecord::create_new(&path)?;
        let lock_id = policy_lock_inode(&path)?;
        let derived = cshake256_framed_32(Self::DOMAIN, &[&key, &lock_id, &record.lock_seal()]);
        ct_zeroize_bytes(&mut key);
        let fence = Self {
            path,
            lock_id,
            record,
            key: qsag_accel::ct::RedactedSecret::new(derived),
            generation: initial_generation,
        };
        fence.record.replace(&fence.encode(initial_generation))?;
        Ok(fence)
    }

    pub fn open_existing(
        path: impl Into<std::path::PathBuf>,
        mut key: [u8; 32],
    ) -> std::io::Result<Self> {
        let path = path.into();
        let record = qsag_asm::durable::LockedRecord::open_existing(&path)?;
        let lock_id = policy_lock_inode(&path)?;
        let derived = cshake256_framed_32(Self::DOMAIN, &[&key, &lock_id, &record.lock_seal()]);
        ct_zeroize_bytes(&mut key);
        let key = qsag_accel::ct::RedactedSecret::new(derived);
        let raw = record.read()?;
        let generation = Self::decode(key.expose(), &lock_id, &record.lock_seal(), &raw)?;
        Ok(Self {
            path,
            lock_id,
            record,
            key,
            generation,
        })
    }

    pub const fn generation(&self) -> u64 {
        self.generation
    }

    pub fn ratchet_to(&mut self, next_generation: u64) -> std::io::Result<()> {
        if policy_lock_inode(&self.path)? != self.lock_id {
            return Err(std::io::Error::other("policy fence lock sidecar replaced"));
        }
        let meta = std::fs::symlink_metadata(&self.path)?;
        if !meta.is_file() {
            return Err(std::io::Error::other(
                "policy fence path is not a regular file",
            ));
        }
        let disk_gen = Self::decode(
            self.key.expose(),
            &self.lock_id,
            &self.record.lock_seal(),
            &self.record.read()?,
        )?;
        if disk_gen != self.generation || next_generation < self.generation {
            return Err(std::io::Error::other("policy generation fence rollback"));
        }
        if next_generation > self.generation {
            self.record.replace(&self.encode(next_generation))?;
            self.generation = next_generation;
        }
        Ok(())
    }

    fn encode(&self, generation: u64) -> Vec<u8> {
        let gen_be = generation.to_be_bytes();
        let tag = cshake256_framed_32(
            Self::DOMAIN,
            &[
                self.key.expose(),
                &self.lock_id,
                &self.record.lock_seal(),
                &gen_be,
            ],
        );
        let mut out = Vec::with_capacity(40);
        out.extend_from_slice(&gen_be);
        out.extend_from_slice(&tag);
        out
    }

    fn decode(
        key: &[u8; 32],
        lock_id: &[u8; 16],
        lock_seal: &[u8; 8],
        raw: &[u8],
    ) -> std::io::Result<u64> {
        if raw.len() != 40 {
            return Err(std::io::Error::other("invalid policy fence length"));
        }
        let expected = cshake256_framed_32(Self::DOMAIN, &[key, lock_id, lock_seal, &raw[..8]]);
        if !ct_eq_bytes(&expected, &raw[8..40]) {
            return Err(std::io::Error::other("invalid policy fence MAC"));
        }
        let mut gen_be = [0u8; 8];
        gen_be.copy_from_slice(&raw[..8]);
        Ok(u64::from_be_bytes(gen_be))
    }
}

const SHARED_DOMAIN: &[u8] = b"QSAG.POLICY.SHARED_LEDGER.V1";

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
        for (values, floor) in [
            (&self.burned_intent_nonces, self.min_nonce_watermark),
            (&self.burned_sessions, self.min_session_watermark),
        ] {
            out.extend_from_slice(&(values.len() as u16).to_be_bytes());
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
        let mut sets = Vec::with_capacity(2);
        for _ in 0..2 {
            let count = r.short()?;
            if count > MAX_BURNED_INTENT_NONCES {
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
            if *floor < old_floor
                || old
                    .iter()
                    .any(|v| !new.contains(v) && !floor.is_some_and(|f| *v <= f))
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
        let mut verified = qsag_verified::StatefulVelocityGuard::new_window(
            window,
            cap,
            self.policy_digest,
            self.policy_digest,
        );
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
            (verified.cap_units(), verified.spent_units(), verified.last_nonce()),
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
            restarted[0].verified_velocity.as_ref().unwrap().last_nonce(),
            2
        );
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
