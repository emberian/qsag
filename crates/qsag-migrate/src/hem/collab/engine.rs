//! Authenticated arithmetic over Goldilocks and its quintic extension `Fp5` for a quorum
//! of custodians.
//!
//! SPDZ over additive shares (Damgard, Pastro, Smart, Zakarias, CRYPTO 2012; the MAC check
//! is the commit-then-open check of SPDZ-2, Damgard et al., ESORICS 2013). A shared value
//! `x` is held as additive shares of `x` and of `alpha_0 x`, `alpha_1 x` for two
//! Goldilocks keys that are themselves additively shared. An extension-field value (`Fp5`)
//! carries the same two base-field keys limb by limb, so multiplying a share by a public
//! extension element is local.
//!
//! * **9-triple Toom-3 `Fp5` Beaver multiplication ([`Engine::mul_ext`]):** Two degree-4
//!   polynomials over `F_p` are evaluated locally at `{0, 1, -1, 2, -2, 3, -3, 4, inf}`,
//!   multiplied in one batched base-field Beaver round (`9` triples per `Fp5` product —
//!   43.75% fewer triples than `Fp4` schoolbook's 16 and 64% fewer than `Fp5` schoolbook's
//!   25), interpolated in `F_p`, and reduced modulo `u^5 - 3`.
//! * **Anti-rollback preprocessing burn before round 1 ([`Engine::new_anchored`]):** Every [`Preprocessing`] tape has a cryptographic
//!   identifier (`tape_id`) bound to its MAC key shares, lengths, and opening material.
//!   Session setup atomically burns `tape_id` (and, with [`Engine::new_anchored`], advances
//!   the hardware/external monotone counter via [`qsag_core::ExternalMonotoneAnchor`])
//!   before round 1 (`0` network messages sent). Persist the expected generation with
//!   the tape snapshot so a rollback remains detectable after a process restart.
//! * Opening a value sends the value shares and queues the MAC shares; [`Engine::check`]
//!   settles the queue (`2 / p^2 < 2^-126`) and checks echo-chain agreement across peers.

#[cfg(test)]
use alloc::vec;
use alloc::vec::Vec;

use qsag_agg::field::{Goldilocks, GoldilocksOps as _};
use qsag_agg::sponge::cshake256_32;
use qsag_agg::zk_hem::SeedStream;
use qsag_agg::zk_hem::v2::field5::Fp5;
use qsag_agg::zk_hem::v2::params::{EXT_BYTES, LIMBS};

use qsag_core::wipe::{SecretBuffer, SecretScratch, SecretWipe};

use super::net::{NetError, Transport};

type F = Goldilocks;
type E = Fp5;

/// Base-field Beaver triples consumed per `Fp5` product via Toom-3 interpolation.
pub const EXT_MUL_TRIPLES: usize = 9;

/// One party's share of an authenticated base-field value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Sb {
    pub v: F,
    pub m: [F; 2],
}

/// One party's share of an authenticated quintic extension-field value (`Fp5`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Sh {
    pub v: E,
    pub m: [E; 2],
}

impl SecretWipe for Sb {
    fn secret_wipe(&mut self) {
        Self::wipe_slice(core::slice::from_mut(self));
    }

    fn wipe_slice(items: &mut [Self]) {
        qsag_asm::volatile_fill(items, Self::ZERO);
    }
}

impl Sb {
    pub const ZERO: Self = Self {
        v: F::ZERO,
        m: [F::ZERO; 2],
    };

    #[inline]
    pub fn scale(self, k: F) -> Self {
        Self {
            v: self.v * k,
            m: [self.m[0] * k, self.m[1] * k],
        }
    }

    /// The share times a public extension element.
    #[inline]
    pub fn scale_ext(self, k: E) -> Sh {
        Sh {
            v: k.mul_base(self.v),
            m: [k.mul_base(self.m[0]), k.mul_base(self.m[1])],
        }
    }

    #[inline]
    pub fn lift(self) -> Sh {
        Sh {
            v: E::from_base(self.v),
            m: [E::from_base(self.m[0]), E::from_base(self.m[1])],
        }
    }
}

impl core::ops::Add for Sb {
    type Output = Self;
    #[inline]
    fn add(self, r: Self) -> Self {
        Self {
            v: self.v + r.v,
            m: [self.m[0] + r.m[0], self.m[1] + r.m[1]],
        }
    }
}

impl core::ops::Sub for Sb {
    type Output = Self;
    #[inline]
    fn sub(self, r: Self) -> Self {
        Self {
            v: self.v - r.v,
            m: [self.m[0] - r.m[0], self.m[1] - r.m[1]],
        }
    }
}

impl core::ops::AddAssign for Sb {
    #[inline]
    fn add_assign(&mut self, r: Self) {
        *self = *self + r;
    }
}

impl SecretWipe for Sh {
    fn secret_wipe(&mut self) {
        Self::wipe_slice(core::slice::from_mut(self));
    }

    fn wipe_slice(items: &mut [Self]) {
        qsag_asm::volatile_fill(items, Self::ZERO);
    }
}

impl Sh {
    pub const ZERO: Self = Self {
        v: E::ZERO,
        m: [E::ZERO; 2],
    };

    #[inline]
    pub fn scale(self, k: E) -> Self {
        Self {
            v: self.v * k,
            m: [self.m[0] * k, self.m[1] * k],
        }
    }

    /// Limb `j` (`0..5`) of the value, as a base-field share.
    #[inline]
    pub fn limb(self, j: usize) -> Sb {
        Sb {
            v: self.v.to_limbs()[j],
            m: [self.m[0].to_limbs()[j], self.m[1].to_limbs()[j]],
        }
    }

    /// Assemble an `Fp5` share from five base-field limb shares.
    #[inline]
    pub fn from_limbs(limbs: [Sb; LIMBS]) -> Self {
        Self {
            v: E::from_limbs(limbs.map(|s| s.v)),
            m: [
                E::from_limbs(limbs.map(|s| s.m[0])),
                E::from_limbs(limbs.map(|s| s.m[1])),
            ],
        }
    }
}

impl core::ops::Add for Sh {
    type Output = Self;
    #[inline]
    fn add(self, r: Self) -> Self {
        Self {
            v: self.v + r.v,
            m: [self.m[0] + r.m[0], self.m[1] + r.m[1]],
        }
    }
}

impl core::ops::Sub for Sh {
    type Output = Self;
    #[inline]
    fn sub(self, r: Self) -> Self {
        Self {
            v: self.v - r.v,
            m: [self.m[0] - r.m[0], self.m[1] - r.m[1]],
        }
    }
}

impl core::ops::AddAssign for Sh {
    #[inline]
    fn add_assign(&mut self, r: Self) {
        *self = *self + r;
    }
}

/// One party's one-use material: its shares of the two MAC keys, of Beaver triples
/// `(a, b, a b)` and of uniform values, all over the base field. Every party consumes
/// its store in the same order. Intentionally non-`Clone`; wiped on `Drop`.
pub struct Preprocessing {
    pub key: [F; 2],
    pub triples: Vec<[Sb; 3]>,
    pub randoms: Vec<Sb>,
}

impl Preprocessing {
    /// Bind both keys, both lengths and every value and MAC, in tape order.
    pub fn tape_id(&self) -> [u8; 32] {
        self.hash_tape(usize::MAX)
    }

    fn hash_tape(&self, limit: usize) -> [u8; 32] {
        use qsag_accel::keccak::{finalize_cshake256, init_cshake256};
        let mut hash = init_cshake256(b"", TAPE_ID_DOMAIN);
        for key in &self.key {
            hash.absorb(&key.to_le_bytes());
        }
        hash.absorb(&(self.triples.len() as u64).to_le_bytes());
        hash.absorb(&(self.randoms.len() as u64).to_le_bytes());
        for share in self.triples.iter().take(limit).flatten().chain(self.randoms.iter().take(limit)) {
            for word in [&share.v, &share.m[0], &share.m[1]] {
                hash.absorb(&word.to_le_bytes());
            }
        }
        finalize_cshake256(&mut hash, true);
        let mut id = [0; 32];
        hash.squeeze(&mut id);
        id
    }
}

impl Drop for Preprocessing {
    fn drop(&mut self) {
        qsag_asm::volatile_fill(&mut self.key, F::ZERO);
        self.triples.secret_wipe();
        self.randoms.secret_wipe();
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MpcError {
    Net(NetError),
    /// A message has the wrong length or a non-canonical field element.
    Malformed {
        from: usize,
    },
    OutOfTriples,
    OutOfRandoms,
    /// The batch MAC check failed: some opened value was wrong.
    MacCheck,
    /// Two parties hold different transcripts of the broadcast messages.
    Equivocation,
    /// A party's opened check value does not match its commitment.
    BadCommitment {
        from: usize,
    },
    /// A preprocessing tape / MAC key share was already burned by an earlier session.
    PreprocessingReused,
    /// The external monotone anti-rollback anchor refused the pre-round-1 burn.
    AntiRollback,
}

impl From<NetError> for MpcError {
    fn from(e: NetError) -> Self {
        Self::Net(e)
    }
}

/// What one party sent and consumed.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Stats {
    /// Payload bytes sent, summed over all peers.
    pub bytes_sent: u64,
    /// Broadcast rounds.
    pub rounds: u64,
    pub triples_used: u64,
    pub randoms_used: u64,
    pub mac_checks: u64,
}

const COIN_DOMAIN: &[u8] = b"QSAG.COLLAB.MAC.COINS/v2";
const COMMIT_DOMAIN: &[u8] = b"QSAG.COLLAB.MAC.COMMIT/v2";
const ECHO_DOMAIN: &[u8] = b"QSAG.COLLAB.ECHO/v2";
#[cfg(any(feature = "std", test))]
const LOCAL_DOMAIN: &[u8] = b"QSAG.COLLAB.LOCAL/v2";
const TAPE_ID_DOMAIN: &[u8] = b"QSAG.COLLAB.TAPE.ID/v1";
#[cfg(feature = "std")]
const TAPE_BURN_DOMAIN: &[u8] = b"QSAG.COLLAB.TAPE.BURN/v1";

#[cfg(feature = "std")]
fn burn_tape_in_process(tape_id: [u8; 32]) -> Result<(), MpcError> {
    use std::collections::BTreeSet;
    use std::sync::{Mutex, OnceLock};
    static BURNED: OnceLock<Mutex<BTreeSet<[u8; 32]>>> = OnceLock::new();
    let mut set = BURNED
        .get_or_init(|| Mutex::new(BTreeSet::new()))
        .lock()
        .map_err(|_| MpcError::AntiRollback)?;
    if !set.insert(tape_id) {
        return Err(MpcError::PreprocessingReused);
    }
    Ok(())
}

/// Check packet size in [`Engine::check`]: `2 * EXT_BYTES` (`sigma`) + `32` (`echo`) + `32` (`nonce`).
const CHECK_OPENING_BYTES: usize = 2 * EXT_BYTES + 32 + 32;

/// One custodian's side of the authenticated computation.
pub struct Engine<T: Transport> {
    net: T,
    prep: Preprocessing,
    t_used: usize,
    r_used: usize,
    /// Opened values awaiting the MAC check, with this party's MAC shares.
    pending: SecretScratch<Sh>,
    failed: bool,
    /// Hash chain over every broadcast round.
    echo: [u8; 32],
    local: SeedStream,
    pub stats: Stats,
}

fn put_base(out: &mut Vec<u8>, v: F) {
    out.extend_from_slice(&v.to_le_bytes());
}

fn put_ext(out: &mut Vec<u8>, v: E) {
    out.extend_from_slice(&v.to_le_bytes());
}

fn get_base(bytes: &[u8]) -> Option<SecretScratch<F>> {
    if bytes.len() % 8 != 0 {
        return None;
    }
    bytes
        .chunks_exact(8)
        .map(|c| F::from_canonical_u64(u64::from_le_bytes(c.try_into().ok()?)))
        .collect()
}

fn get_ext(bytes: &[u8]) -> Option<Vec<E>> {
    if bytes.len() % EXT_BYTES != 0 {
        return None;
    }
    bytes
        .chunks_exact(EXT_BYTES)
        .map(|c| E::from_le_bytes_canonical(c.try_into().ok()?))
        .collect()
}

impl<T: Transport> Engine<T> {
    /// Construct an unanchored unit-test engine. With `std`, burn `prep.tape_id()`
    /// in-process before round 1. Sealed to `#[cfg(test)]`: every public collaborative
    /// MPC session MUST be constructed via [`Engine::new_anchored`].
    #[cfg(test)]
    pub(crate) fn try_new(
        net: T,
        prep: Preprocessing,
        session: &[u8; 32],
        local_seed: &[u8; 32],
    ) -> Result<Self, MpcError> {
        #[cfg(feature = "std")]
        burn_tape_in_process(prep.tape_id())?;
        Ok(Self::build_unchecked(net, prep, session, local_seed))
    }

    /// Construct an engine while durably burning `(session, prep.tape_id())` into a
    /// hardware/TPM/filesystem [`qsag_core::ExternalMonotoneAnchor`] **before round 1**
    /// (`0` network bytes sent). If the monotone counter rejects or fails to persist,
    /// `prep` (including the MAC key share) is wiped immediately and [`MpcError::AntiRollback`]
    /// is returned before any share is transmitted.
    #[cfg(feature = "std")]
    pub fn new_anchored(
        net: T,
        prep: Preprocessing,
        session: &[u8; 32],
        local_seed: &[u8; 32],
        anchor: &dyn qsag_core::ExternalMonotoneAnchor,
        expected_prev_gen: Option<u64>,
    ) -> Result<Self, MpcError> {
        let tape_id = prep.tape_id();
        let tag_for = |id: &[u8; 32]| qsag_accel::keccak::cshake256_framed_32(
            TAPE_BURN_DOMAIN,
            &[session, id, &(net.me() as u64).to_le_bytes()],
        );
        let burn_tag = tag_for(&tape_id);
        let prev = anchor.load().map_err(|_| MpcError::AntiRollback)?;
        if prev.map(|cp| cp.generation) != expected_prev_gen {
            return Err(MpcError::AntiRollback);
        }
        if let Some(cp) = prev
            && (cp.tag == burn_tag || cp.tag == tag_for(&prep.hash_tape(4)))
        {
            return Err(MpcError::AntiRollback);
        }
        let next_gen = prev
            .map_or(Some(1u64), |cp| cp.generation.checked_add(1))
            .ok_or(MpcError::AntiRollback)?;
        burn_tape_in_process(tape_id)?;
        anchor
            .advance(qsag_core::LedgerCheckpoint {
                generation: next_gen,
                tag: burn_tag,
            })
            .map_err(|_| MpcError::AntiRollback)?;
        Ok(Self::build_unchecked(net, prep, session, local_seed))
    }

    /// `local_seed` is this party's private randomness; it must be uniform and never
    /// reused across runs. With `std`, panics if this process already burned `prep`.
    /// Sealed to `#[cfg(test)]`: production callers MUST use [`Engine::new_anchored`].
    #[cfg(test)]
    pub(crate) fn new(net: T, prep: Preprocessing, session: &[u8; 32], local_seed: &[u8; 32]) -> Self {
        Self::try_new(net, prep, session, local_seed)
            .expect("preprocessing tape / MAC key share must never be reused across sessions")
    }

    #[cfg(test)]
    pub(super) fn new_for_obliviousness_test(
        net: T,
        prep: Preprocessing,
        session: &[u8; 32],
        local_seed: &[u8; 32],
    ) -> Self {
        Self::build_unchecked(net, prep, session, local_seed)
    }

    #[cfg(any(feature = "std", test))]
    fn build_unchecked(
        net: T,
        prep: Preprocessing,
        session: &[u8; 32],
        local_seed: &[u8; 32],
    ) -> Self {
        Self {
            net,
            prep,
            t_used: 0,
            r_used: 0,
            pending: SecretScratch::new(),
            failed: false,
            echo: cshake256_32(ECHO_DOMAIN, session),
            local: SeedStream::new(LOCAL_DOMAIN, local_seed),
            stats: Stats::default(),
        }
    }

    #[inline]
    pub fn me(&self) -> usize {
        self.net.me()
    }

    #[inline]
    pub fn parties(&self) -> usize {
        self.net.parties()
    }

    /// A uniform base-field element known to this party only.
    pub fn local_base(&mut self) -> F {
        self.local.next_base()
    }

    /// A uniform `Fp5` element known to this party only.
    pub fn local_ext(&mut self) -> E {
        self.local.next_fp5()
    }

    /// Triples and randoms not yet consumed.
    pub fn remaining(&self) -> (usize, usize) {
        (
            self.prep.triples.len() - self.t_used,
            self.prep.randoms.len() - self.r_used,
        )
    }

    /// Permanently mark this engine failed so no further preprocessing, openings, or broadcasts run.
    pub(super) fn poison(&mut self) {
        self.failed = true;
    }

    /// Broadcast `payload` and collect one message from every party, in party order (the
    /// own message included).
    pub fn exchange(&mut self, payload: Vec<u8>) -> Result<Vec<Vec<u8>>, MpcError> {
        self.exchange_guarded(payload).map(SecretBuffer::into_inner)
    }

    pub(super) fn exchange_guarded(&mut self, payload: Vec<u8>) -> Result<SecretBuffer<Vec<Vec<u8>>>, MpcError> {
        let payload = SecretBuffer(payload);
        if self.failed {
            return Err(MpcError::MacCheck);
        }
        self.failed = true;
        let (me, n) = (self.me(), self.parties());
        for p in (0..n).filter(|&p| p != me) {
            self.net.send(p, &payload)?;
        }
        self.stats.bytes_sent += (payload.len() * (n - 1)) as u64;
        self.stats.rounds += 1;
        let mut all = SecretBuffer(Vec::with_capacity(n));
        for p in 0..n {
            if p == me {
                all.push(Vec::new());
            } else {
                all.push(self.net.recv(p)?);
            }
        }
        all[me] = payload.into_inner();
        let mut chain = self.echo.to_vec();
        for msg in all.iter() {
            chain.extend_from_slice(&(msg.len() as u64).to_le_bytes());
            chain.extend_from_slice(&cshake256_32(ECHO_DOMAIN, msg));
        }
        self.echo = cshake256_32(ECHO_DOMAIN, &chain);
        self.failed = false;
        Ok(all)
    }

    /// The share of a public constant.
    #[inline]
    pub fn public(&self, c: F) -> Sb {
        Sb {
            v: if self.me() == 0 { c } else { F::ZERO },
            m: [self.prep.key[0] * c, self.prep.key[1] * c],
        }
    }

    /// The share of a public extension-field constant.
    #[inline]
    pub fn public_ext(&self, c: E) -> Sh {
        Sh {
            v: if self.me() == 0 { c } else { E::ZERO },
            m: [c.mul_base(self.prep.key[0]), c.mul_base(self.prep.key[1])],
        }
    }

    /// The next preprocessed uniform value.
    pub fn random(&mut self) -> Result<Sb, MpcError> {
        if self.failed { return Err(MpcError::MacCheck); }
        let r = *self
            .prep
            .randoms
            .get(self.r_used)
            .ok_or(MpcError::OutOfRandoms)?;
        self.prep.randoms[self.r_used].secret_wipe();
        self.r_used += 1;
        self.stats.randoms_used += 1;
        Ok(r)
    }

    /// A uniform `Fp5` value from five preprocessed base values.
    pub fn random_ext(&mut self) -> Result<Sh, MpcError> {
        let mut limbs = SecretBuffer([Sb::ZERO; LIMBS]);
        for limb in limbs.iter_mut() {
            *limb = self.random()?;
        }
        Ok(Sh::from_limbs(*limbs))
    }

    fn sum_opened<V: Copy + core::ops::AddAssign, const N: usize>(
        &mut self,
        payload: Vec<u8>,
        len: usize,
        zero: V,
        decode: impl Fn([u8; N]) -> Option<V>,
    ) -> Result<Vec<V>, MpcError> {
        let all = self.exchange_guarded(payload)?;
        let mut total = alloc::vec![zero; len];
        self.failed = true;
        for (from, msg) in all.iter().enumerate() {
            let (chunks, tail) = msg.as_chunks::<N>();
            if chunks.len() != len || !tail.is_empty() {
                qsag_asm::volatile_fill(&mut total, zero);
                return Err(MpcError::Malformed { from });
            }
            for (slot, chunk) in total.iter_mut().zip(chunks) {
                let Some(value) = decode(*chunk) else {
                    qsag_asm::volatile_fill(&mut total, zero);
                    return Err(MpcError::Malformed { from });
                };
                *slot += value;
            }
        }
        self.failed = false;
        Ok(total)
    }

    /// Open base-field values. Their MACs are queued for [`Self::check`].
    pub fn open(&mut self, shares: &[Sb]) -> Result<Vec<F>, MpcError> {
        let mut payload = Vec::with_capacity(8 * shares.len());
        for s in shares {
            put_base(&mut payload, s.v);
        }
        let opened = self.sum_opened(payload, shares.len(), F::ZERO, |word| {
            F::from_canonical_u64(u64::from_le_bytes(word))
        })?;
        self.pending
            .extend(opened.iter().zip(shares).map(|(&x, s)| {
                Sh {
                    v: E::from_base(x),
                    m: [E::from_base(s.m[0]), E::from_base(s.m[1])],
                }
            }));
        Ok(opened)
    }

    /// Open `Fp5` extension-field values. Their MACs are queued for [`Self::check`].
    pub fn open_ext(&mut self, shares: &[Sh]) -> Result<Vec<E>, MpcError> {
        let mut payload = Vec::with_capacity(EXT_BYTES * shares.len());
        for s in shares {
            put_ext(&mut payload, s.v);
        }
        let opened = self.sum_opened(payload, shares.len(), E::ZERO, E::from_le_bytes_canonical)?;
        self.pending
            .extend(opened.iter().zip(shares).map(|(&x, s)| Sh { v: x, m: s.m }));
        Ok(opened)
    }

    /// Settle every opening made since the last check, and compare transcripts.
    pub fn check(&mut self) -> Result<(), MpcError> {
        if self.failed {
            return Err(MpcError::MacCheck);
        }
        let result = self.check_pending();
        self.failed = result.is_err();
        result
    }

    fn check_pending(&mut self) -> Result<(), MpcError> {
        self.stats.mac_checks += 1;
        let echo = self.echo;
        let mut coins = SeedStream::new(COIN_DOMAIN, &echo);
        let mut sigma = Sh::ZERO;
        for &Sh { v: x, m } in &self.pending {
            let r = coins.next_fp5();
            for k in 0..2 {
                sigma.m[k] += r * (m[k] - x.mul_base(self.prep.key[k]));
            }
        }
        self.pending.clear();
        let mut opening = SecretBuffer(Vec::with_capacity(CHECK_OPENING_BYTES));
        put_ext(&mut opening, sigma.m[0]);
        put_ext(&mut opening, sigma.m[1]);
        sigma.secret_wipe();
        opening.extend_from_slice(&echo);
        for _ in 0..4 {
            opening.extend_from_slice(&self.local.next_base().to_le_bytes());
        }
        let commitments = self.exchange(cshake256_32(COMMIT_DOMAIN, &opening).to_vec())?;
        let openings = self.exchange_guarded(opening.into_inner())?;
        let mut total = [E::ZERO; 2];
        let ext_pair = 2 * EXT_BYTES;
        for (from, (commitment, opened)) in commitments.iter().zip(openings.iter()).enumerate() {
            if opened.len() != CHECK_OPENING_BYTES
                || !qsag_asm::ct_eq_bytes(commitment, &cshake256_32(COMMIT_DOMAIN, opened))
            {
                return Err(MpcError::BadCommitment { from });
            }
            if opened[ext_pair..ext_pair + 32] != echo[..] {
                return Err(MpcError::Equivocation);
            }
            let parts = get_ext(&opened[..ext_pair]).ok_or(MpcError::Malformed { from })?;
            total[0] += parts[0];
            total[1] += parts[1];
        }
        let difference = total.iter().flat_map(|v| v.to_limbs()).fold(0, |acc, x| acc | x.to_canonical_u64());
        if !qsag_accel::ct::ct_eq_u64(difference, 0) {
            return Err(MpcError::MacCheck);
        }
        Ok(())
    }

    /// Whether any opening awaits a check.
    pub fn has_pending(&self) -> bool {
        !self.pending.is_empty()
    }

    /// Products of base-field values: one triple and two masked openings each.
    pub fn mul(&mut self, xs: &[Sb], ys: &[Sb]) -> Result<Vec<Sb>, MpcError> {
        Ok(self.mul_open(xs, ys, &[])?.0)
    }

    /// The products `xs[i] ys[i]` and the values of `opens`, in one round: the masked
    /// openings of the products and the plain openings travel in the same exchange.
    #[allow(clippy::type_complexity)]
    pub fn mul_open(
        &mut self,
        xs: &[Sb],
        ys: &[Sb],
        opens: &[Sb],
    ) -> Result<(Vec<Sb>, Vec<F>), MpcError> {
        if self.failed { return Err(MpcError::MacCheck); }
        assert_eq!(xs.len(), ys.len());
        let n = xs.len();
        if self.prep.triples.len() - self.t_used < n {
            return Err(MpcError::OutOfTriples);
        }
        // Consume the whole range before any masked opening can reach a peer.
        let start = self.t_used;
        self.t_used += n;
        self.stats.triples_used += n as u64;
        let triples = &self.prep.triples[start..self.t_used];
        let mut masked = SecretScratch::with_capacity(2 * n + opens.len());
        for ((x, y), t) in xs.iter().zip(ys).zip(triples) {
            masked.push(*x - t[0]);
            masked.push(*y - t[1]);
        }
        masked.extend_from_slice(opens);
        let mut opened = match self.open(&masked) {
            Ok(opened) => opened,
            Err(err) => {
                self.prep.triples[start..self.t_used].secret_wipe();
                return Err(err);
            }
        };
        let plain = opened.split_off(2 * n);
        let mut out = Vec::with_capacity(n);
        for (k, pair) in opened.chunks_exact(2).enumerate() {
            let (d, e) = (pair[0], pair[1]);
            let t = self.prep.triples[start + k];
            out.push(t[2] + t[1].scale(d) + t[0].scale(e) + self.public(d * e));
        }
        qsag_asm::volatile_fill(
            &mut self.prep.triples[start..self.t_used],
            [Sb::ZERO; 3],
        );
        Ok((out, plain))
    }

    /// Products of `Fp5` extension-field values via **9-triple Toom-3 interpolation** over
    /// `{0, 1, -1, 2, -2, 3, -3, 4, inf}` modulo `u^5 - 3` (`9` base-field Beaver triples
    /// per product, batched into a single broadcast round).
    pub fn mul_ext(&mut self, xs: &[Sh], ys: &[Sh]) -> Result<Vec<Sh>, MpcError> {
        if self.failed { return Err(MpcError::MacCheck); }
        assert_eq!(xs.len(), ys.len());
        if xs.is_empty() {
            return Ok(Vec::new());
        }
        let c = |v: u64| F::from_u64_reduced(v);
        let eval9 = |s: &Sh| -> [Sb; EXT_MUL_TRIPLES] {
            let [a0, a1, a2, a3, a4] = [s.limb(0), s.limb(1), s.limb(2), s.limb(3), s.limb(4)];
            let e1 = a0 + a2 + a4;
            let o1 = a1 + a3;
            let e2 = a0 + a2.scale(c(4)) + a4.scale(c(16));
            let o2 = a1.scale(c(2)) + a3.scale(c(8));
            let e3 = a0 + a2.scale(c(9)) + a4.scale(c(81));
            let o3 = a1.scale(c(3)) + a3.scale(c(27));
            let v4 = a0 + a1.scale(c(4)) + a2.scale(c(16)) + a3.scale(c(64)) + a4.scale(c(256));
            [
                a0,
                e1 + o1,
                e1 - o1,
                e2 + o2,
                e2 - o2,
                e3 + o3,
                e3 - o3,
                v4,
                a4,
            ]
        };

        let mut lhs = SecretScratch::with_capacity(EXT_MUL_TRIPLES * xs.len());
        let mut rhs = SecretScratch::with_capacity(EXT_MUL_TRIPLES * ys.len());
        for (x, y) in xs.iter().zip(ys) {
            lhs.extend_from_slice(&eval9(x));
            rhs.extend_from_slice(&eval9(y));
        }
        let prods = SecretScratch::from(self.mul(&lhs, &rhs)?);

        let inv2 = c(2).inv();
        let inv3 = c(3).inv();
        let inv4 = c(4).inv();
        let inv5 = c(5).inv();
        let inv6 = c(6).inv();
        let inv7 = c(7).inv();
        let inv8 = c(8).inv();
        let inv9 = c(9).inv();
        let inv12 = c(12).inv();
        let inv15 = c(15).inv();

        Ok(prods
            .chunks_exact(EXT_MUL_TRIPLES)
            .map(|v| {
                let [v0, v1, vm1, v2, vm2, v3, vm3, v4, vinf] =
                    [v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8]];
                let p0 = v0;
                let p8 = vinf;

                // Even part E(u) = p2 + p4 u + p6 u^2 at u in {1, 4, 9}:
                let s1 = (v1 + vm1).scale(inv2) - p0 - p8;
                let s2 = ((v2 + vm2).scale(inv2) - p0 - p8.scale(c(256))).scale(inv4);
                let s3 = ((v3 + vm3).scale(inv2) - p0 - p8.scale(c(6561))).scale(inv9);
                let d01 = (s2 - s1).scale(inv3);
                let d12 = (s3 - s2).scale(inv5);
                let p6 = (d12 - d01).scale(inv8);
                let p4 = d01 - p6.scale(c(5));
                let p2 = s1 - p4 - p6;

                // Odd part O(u) = p1 + p3 u + p5 u^2 + p7 u^3 at u in {1, 4, 9, 16}:
                let q1 = (v1 - vm1).scale(inv2);
                let q2 = (v2 - vm2).scale(inv4);
                let q3 = (v3 - vm3).scale(inv6);
                let even_at_4 = p0
                    + p2.scale(c(16))
                    + p4.scale(c(256))
                    + p6.scale(c(4096))
                    + p8.scale(c(65536));
                let q4 = (v4 - even_at_4).scale(inv4);

                let del0 = (q2 - q1).scale(inv3);
                let del1 = (q3 - q2).scale(inv5);
                let del2 = (q4 - q3).scale(inv7);
                let del01 = (del1 - del0).scale(inv8);
                let del12 = (del2 - del1).scale(inv12);
                let p7 = (del12 - del01).scale(inv15);
                let p5 = del01 - p7.scale(c(14));
                let p3 = del0 - del01.scale(c(5)) + p7.scale(c(49));
                let p1 = q1 - del0 + del01.scale(c(4)) - p7.scale(c(36));

                // Reduce modulo u^5 - 3:
                Sh::from_limbs([
                    p0 + p5.scale(c(3)),
                    p1 + p6.scale(c(3)),
                    p2 + p7.scale(c(3)),
                    p3 + p8.scale(c(3)),
                    p4,
                ])
            })
            .collect())
    }

    /// Party `owner` contributes private base-field values; every party gets shares of
    /// them. `values` is `Some` for the owner and `None` for everyone else. One
    /// preprocessed random per value.
    pub fn input(
        &mut self,
        owner: usize,
        values: Option<&[F]>,
        count: usize,
    ) -> Result<Vec<Sb>, MpcError> {
        let (me, n) = (self.me(), self.parties());
        if self.failed {
            return Err(MpcError::MacCheck);
        }
        let masks: SecretScratch<Sb> = (0..count)
            .map(|_| self.random())
            .collect::<Result<_, _>>()?;
        self.failed = true;
        if me != owner {
            let mut payload = SecretScratch::with_capacity(8 * count);
            for mask in &masks {
                payload.extend_from_slice(&mask.v.to_le_bytes());
            }
            self.net.send(owner, &payload)?;
            self.stats.bytes_sent += payload.len() as u64;
            let received = SecretBuffer(self.net.recv(owner)?);
            let eps = get_base(&received)
                .filter(|e| e.len() == count)
                .ok_or(MpcError::Malformed { from: owner })?;
            self.failed = false;
            return Ok(masks
                .iter()
                .zip(eps)
                .map(|(&mask, e)| mask + self.public(e))
                .collect());
        }
        let values = values
            .filter(|v| v.len() == count)
            .expect("the owner's values");
        let mut clear: SecretScratch<F> = masks.iter().map(|mask| mask.v).collect();
        for p in (0..n).filter(|&p| p != me) {
            let received = SecretBuffer(self.net.recv(p)?);
            let part = get_base(&received)
                .filter(|e| e.len() == count)
                .ok_or(MpcError::Malformed { from: p })?;
            for (c, s) in clear.iter_mut().zip(part) {
                *c += s;
            }
        }
        let eps: Vec<F> = values.iter().zip(&clear).map(|(&x, &r)| x - r).collect();
        qsag_asm::volatile_fill(&mut clear, F::ZERO);
        let mut payload = SecretScratch::with_capacity(8 * count);
        for &e in &eps {
            payload.extend_from_slice(&e.to_le_bytes());
        }
        for p in (0..n).filter(|&p| p != me) {
            self.net.send(p, &payload)?;
        }
        self.stats.bytes_sent += (payload.len() * (n - 1)) as u64;
        self.failed = false;
        Ok(masks
            .iter()
            .zip(eps)
            .map(|(&mask, e)| mask + self.public(e))
            .collect())
    }
}

/// A single generator that knows both MAC keys and every share. Sealed strictly to
/// `#[cfg(test)]` unit tests inside `qsag-migrate`: never compiled into library builds.
#[cfg(test)]
pub(crate) struct Dealer {
    parties: usize,
    key: [F; 2],
    key_shares: Vec<[F; 2]>,
    stream: SeedStream,
    epoch: u64,
}

#[cfg(test)]
impl Drop for Dealer {
    fn drop(&mut self) {
        self.key.secret_wipe();
        self.key_shares.secret_wipe();
    }
}

#[cfg(test)]
impl Dealer {
    pub fn new(parties: usize, seed: &[u8; 32]) -> Self {
        assert!(parties >= 2);
        let mut stream = SeedStream::new(b"QSAG.COLLAB.TEST.DEALER/v1", seed);
        let key_shares: Vec<[F; 2]> = (0..parties)
            .map(|_| [stream.next_base(), stream.next_base()])
            .collect();
        let key = key_shares
            .iter()
            .fold([F::ZERO; 2], |acc, s| [acc[0] + s[0], acc[1] + s[1]]);
        Self {
            parties,
            key,
            key_shares,
            stream,
            epoch: 0,
        }
    }

    /// Authenticated shares of `value`, one per party.
    pub fn share(&mut self, value: F) -> Vec<Sb> {
        let mut rest = Sb {
            v: value,
            m: [self.key[0] * value, self.key[1] * value],
        };
        let mut out = vec![Sb::ZERO; self.parties];
        for slot in &mut out[1..] {
            *slot = Sb {
                v: self.stream.next_base(),
                m: [self.stream.next_base(), self.stream.next_base()],
            };
            rest = rest - *slot;
        }
        out[0] = rest;
        out
    }

    /// Every party's store with `triples` triples and `randoms` uniform values.
    /// Re-randomizes the additive split of `self.key` on each call while preserving the sum
    /// `self.key`, so distinct batches from the same test `Dealer` have distinct `tape_id`s.
    pub fn preprocessing(&mut self, triples: usize, randoms: usize) -> Vec<Preprocessing> {
        if self.epoch > 0 {
            let mut rest = self.key;
            for share in &mut self.key_shares[1..] {
                *share = [self.stream.next_base(), self.stream.next_base()];
                rest = [rest[0] - share[0], rest[1] - share[1]];
            }
            self.key_shares[0] = rest;
        }
        self.epoch += 1;
        let mut out: Vec<Preprocessing> = self
            .key_shares
            .iter()
            .map(|&key| Preprocessing {
                key,
                triples: Vec::with_capacity(triples),
                randoms: Vec::with_capacity(randoms),
            })
            .collect();
        for _ in 0..triples {
            let (a, b) = (self.stream.next_base(), self.stream.next_base());
            let (sa, sb, sc) = (self.share(a), self.share(b), self.share(a * b));
            for (p, prep) in out.iter_mut().enumerate() {
                prep.triples.push([sa[p], sb[p], sc[p]]);
            }
        }
        for _ in 0..randoms {
            let r = self.stream.next_base();
            let sr = self.share(r);
            for (p, prep) in out.iter_mut().enumerate() {
                prep.randoms.push(sr[p]);
            }
        }
        out
    }
}

#[cfg(test)]
pub(super) mod tests {
    use core::sync::atomic::{AtomicU64, Ordering};

    use super::super::net::{ChannelLink, Framed, channel_mesh};
    use super::*;

    pub(in super::super) type TestEngine = Engine<Framed<ChannelLink>>;

    /// Run `party` for every custodian on its own thread over a channel mesh.
    pub(in super::super) fn run_parties<R: Send>(
        preps: Vec<Preprocessing>,
        party: impl Fn(TestEngine) -> R + Sync,
    ) -> Vec<R> {
        static NEXT_SESSION: AtomicU64 = AtomicU64::new(1);
        let id = NEXT_SESSION.fetch_add(1, Ordering::Relaxed);
        let mut session = [9u8; 32];
        session[..8].copy_from_slice(&id.to_le_bytes());
        let mesh = channel_mesh(session, preps.len());
        std::thread::scope(|scope| {
            let handles: Vec<_> = mesh
                .into_iter()
                .zip(preps)
                .enumerate()
                .map(|(p, (net, prep))| {
                    let party = &party;
                    scope.spawn(move || {
                        let mut lseed = [p as u8 + 100; 32];
                        lseed[..8].copy_from_slice(&id.to_le_bytes());
                        party(Engine::new(net, prep, &session, &lseed))
                    })
                })
                .collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        })
    }

    fn f(x: u64) -> F {
        F::from_u64_reduced(x)
    }

    #[test]
    fn toom3_fp5_products_openings_and_inputs_match_direct_field5_for_every_quorum() {
        let u = E::from_limbs([F::ZERO, F::ONE, F::ZERO, F::ZERO, F::ZERO]);
        let full_a = E::from_limbs([
            f(0xffff_ffff_0000_0000),
            f(0x1234_5678_9abc_def0),
            f(7),
            f(0xdead_beef_cafe_babe),
            f(0xffff_fffe_ffff_ffff),
        ]);
        let full_b = E::from_limbs([
            f(42),
            f(0xfedc_ba98_7654_3210),
            f(0xffff_ffff_0000_0000),
            f(19),
            f(0x7777_8888_9999_aaaa),
        ]);
        for parties in [2usize, 3, 5] {
            let mut dealer = Dealer::new(parties, &[10 + parties as u8; 32]);
            let (x, y) = (f(123_456_789), f(987_654_321_012));
            let (sx, sy) = (dealer.share(x), dealer.share(y));
            let s_full_a: [Vec<Sb>; 5] = core::array::from_fn(|j| dealer.share(full_a.0[j]));
            let s_full_b: [Vec<Sb>; 5] = core::array::from_fn(|j| dealer.share(full_b.0[j]));
            // 1 base mul + 3 Fp5 muls = 1 + 27 = 28 triples; 1 random_ext + 1 input = 6 randoms.
            let preps = dealer.preprocessing(28, 6);
            let secret = f(77);
            let out = run_parties(preps, |mut e| {
                let me = e.me();
                let prod = e.mul(&[sx[me]], &[sy[me]]).unwrap()[0];
                let sum = prod + e.public(f(5)) - sx[me].scale(f(2));
                let rx = e.random_ext().unwrap();
                let sa = Sh::from_limbs(core::array::from_fn(|j| s_full_a[j][me]));
                let sb = Sh::from_limbs(core::array::from_fn(|j| s_full_b[j][me]));
                let ext = e
                    .mul_ext(&[sx[me].scale_ext(u), rx, sa], &[sy[me].lift(), rx, sb])
                    .unwrap();
                let input = e.input(1, (me == 1).then_some(&[secret][..]), 1).unwrap()[0];
                let opened = e.open(&[prod, sum, input]).unwrap();
                let opened_ext = e.open_ext(&[ext[0], ext[1], ext[2], rx]).unwrap();
                e.check().unwrap();
                assert!(!e.has_pending());
                assert_eq!(e.remaining(), (0, 0));
                (opened, opened_ext, e.stats)
            });
            for (opened, opened_ext, stats) in &out {
                assert_eq!(opened, &[x * y, x * y + f(5) - x * f(2), secret]);
                assert_eq!(opened_ext[0], u.mul_base(x) * E::from_base(y));
                assert_eq!(opened_ext[1], opened_ext[3].square());
                assert_eq!(opened_ext[2], full_a * full_b);
                assert_eq!(stats.triples_used, 1 + 3 * EXT_MUL_TRIPLES as u64);
                assert_eq!(stats.randoms_used, 6);
            }
        }
    }

    #[test]
    fn tape_id_binds_late_triples_and_random_macs() {
        let mut dealer = Dealer::new(2, &[71; 32]);
        let mut tape = dealer.preprocessing(5, 5).remove(0);
        let original = tape.tape_id();
        tape.triples[4][2].m[1] += F::ONE;
        assert_ne!(tape.tape_id(), original);
        tape.triples[4][2].m[1] -= F::ONE;
        tape.randoms[4].m[0] += F::ONE;
        assert_ne!(tape.tape_id(), original);
    }

    #[test]
    fn failed_send_burns_the_reserved_triples_before_retry() {
        struct Closed;
        impl Transport for Closed {
            fn me(&self) -> usize { 0 }
            fn parties(&self) -> usize { 2 }
            fn send(&mut self, peer: usize, _: &[u8]) -> Result<(), NetError> {
                Err(NetError::Closed { peer })
            }
            fn recv(&mut self, _: usize) -> Result<Vec<u8>, NetError> { unreachable!() }
        }
        let mut dealer = Dealer::new(2, &[79; 32]);
        let prep = dealer.preprocessing(2, 0).remove(0);
        let mut e = Engine::new(Closed, prep, &[3; 32], &[4; 32]);
        let share = e.public(F::ONE);
        assert_eq!(e.mul(&[share], &[share]), Err(MpcError::Net(NetError::Closed { peer: 1 })));
        assert_eq!(e.prep.triples[0], [Sb::ZERO; 3]);
        assert_eq!(e.mul(&[share], &[share]), Err(MpcError::MacCheck));
        assert_eq!(e.remaining(), (1, 0));
    }

    #[cfg(feature = "std")]
    #[test]
    fn aborted_session_burns_preprocessing_and_mac_share_via_anti_rollback_before_round_1() {
        use std::io;
        use std::sync::Mutex;

        use qsag_core::{ExternalMonotoneAnchor, LedgerCheckpoint};

        struct MemAnchor {
            state: Mutex<Option<LedgerCheckpoint>>,
            fail_next: bool,
        }
        impl ExternalMonotoneAnchor for MemAnchor {
            fn load(&self) -> io::Result<Option<LedgerCheckpoint>> {
                Ok(*self.state.lock().unwrap())
            }
            fn advance(&self, checkpoint: LedgerCheckpoint) -> io::Result<()> {
                if self.fail_next {
                    return Err(io::Error::other("hardware fault"));
                }
                let mut cell = self.state.lock().unwrap();
                if let Some(old) = *cell
                    && old.generation >= checkpoint.generation
                {
                    return Err(io::Error::other("anchor rejects rollback"));
                }
                *cell = Some(checkpoint);
                Ok(())
            }
        }

        let mut dealer = Dealer::new(2, &[0x91; 32]);
        let mut preps = dealer.preprocessing(2, 2);
        let prep0 = preps.remove(0);
        // Simulate a disk snapshot copy of the same MAC key share & triples before an abort.
        let snapshot_copy = Preprocessing {
            key: prep0.key,
            triples: prep0.triples.clone(),
            randoms: prep0.randoms.clone(),
        };
        assert_eq!(prep0.tape_id(), snapshot_copy.tape_id());

        let anchor = MemAnchor {
            state: Mutex::new(None),
            fail_next: false,
        };
        let session_a = [0xa1; 32];
        let mut mesh_a = channel_mesh(session_a, 2);
        // Session A burns prep0 into the monotone anchor before round 1, then aborts before any message!
        let engine_a = Engine::new_anchored(
            mesh_a.remove(0),
            prep0,
            &session_a,
            &[0xb1; 32],
            &anchor,
            None,
        )
        .expect("fresh anchored burn succeeds");
        assert_eq!(engine_a.stats.rounds, 0);
        assert_eq!(engine_a.stats.bytes_sent, 0);
        assert_eq!(anchor.load().unwrap().unwrap().generation, 1);
        drop(engine_a); // Ceremony aborts before round 1!

        // Re-running with the snapshot copy under a new session is refused BEFORE round 1:
        // 1) If the attacker also rolled back `expected_prev_gen` to `None`, the anchor catches it:
        let session_b = [0xa2; 32];
        let mut mesh_b = channel_mesh(session_b, 2);
        let copy_rollback = Preprocessing {
            key: snapshot_copy.key,
            triples: snapshot_copy.triples.clone(),
            randoms: snapshot_copy.randoms.clone(),
        };
        let err = Engine::new_anchored(
            mesh_b.remove(0),
            copy_rollback,
            &session_b,
            &[0xb2; 32],
            &anchor,
            None,
        )
        .err();
        assert_eq!(err, Some(MpcError::AntiRollback));

        // 2) Even if the attacker passes `expected_prev_gen = Some(1)`, the burned-tape registry
        //    refuses reuse of the burned MAC share / preprocessing tape before round 1:
        let mut mesh_c = channel_mesh(session_b, 2);
        let err_reuse = Engine::new_anchored(
            mesh_c.remove(0),
            snapshot_copy,
            &session_b,
            &[0xb3; 32],
            &anchor,
            Some(1),
        )
        .err();
        assert_eq!(err_reuse, Some(MpcError::PreprocessingReused));
    }

    /// A party that opens a wrong value, sends a wrong MAC-check share, or tells two
    /// parties different things is caught at the check by every honest party.
    #[test]
    fn the_check_catches_wrong_openings_and_equivocation() {
        #[derive(Clone, Copy, PartialEq, Debug)]
        enum Cheat {
            None,
            Value,
            Mac,
            Key,
        }
        for (idx, cheat) in [Cheat::None, Cheat::Value, Cheat::Mac, Cheat::Key]
            .into_iter()
            .enumerate()
        {
            let mut dealer = Dealer::new(3, &[20 + idx as u8; 32]);
            let sx = dealer.share(f(41));
            let preps = dealer.preprocessing(0, 0);
            let out = run_parties(preps, |mut e| {
                let me = e.me();
                let mut share = sx[me];
                if me == 2 {
                    match cheat {
                        Cheat::None => {}
                        Cheat::Value => share.v += F::ONE,
                        Cheat::Mac => share.m[1] += F::ONE,
                        Cheat::Key => e.prep.key[0] += F::ONE,
                    }
                }
                let opened = e.open(&[share]).unwrap();
                let verdict = e.check();
                if verdict.is_err() {
                    assert_eq!(e.check(), Err(MpcError::MacCheck));
                    assert_eq!(e.open(&[share]), Err(MpcError::MacCheck));
                }
                (opened[0], verdict)
            });
            for (p, (value, verdict)) in out.iter().enumerate() {
                match cheat {
                    Cheat::None => assert_eq!((*value, *verdict), (f(41), Ok(()))),
                    _ => {
                        assert_eq!(*verdict, Err(MpcError::MacCheck), "party {p} {cheat:?}");
                        assert_eq!(*value, if cheat == Cheat::Value { f(42) } else { f(41) });
                    }
                }
            }
        }

        // Equivocation: party 2 sends party 0 another value than party 1.
        let mut dealer = Dealer::new(3, &[33; 32]);
        let sx = dealer.share(f(9));
        let preps = dealer.preprocessing(0, 0);
        let out = run_parties(preps, |mut e| {
            let me = e.me();
            if me == 2 {
                let mut to0 = Vec::new();
                put_base(&mut to0, sx[me].v + F::ONE);
                let mut to1 = Vec::new();
                put_base(&mut to1, sx[me].v);
                e.net.send(0, &to0).unwrap();
                e.net.send(1, &to1).unwrap();
                let _ = (e.net.recv(0).unwrap(), e.net.recv(1).unwrap());
                e.echo = [0; 32];
                return e.check();
            }
            e.open(&[sx[me]]).unwrap();
            e.check()
        });
        assert!(out[..2].iter().all(|v| v.is_err()));
        assert!(
            out[..2].contains(&Err(MpcError::Equivocation))
                || out[..2].contains(&Err(MpcError::MacCheck))
        );
    }

    #[test]
    fn exhausted_preprocessing_fails_closed() {
        let mut dealer = Dealer::new(2, &[44; 32]);
        let sx = dealer.share(f(3));
        let preps = dealer.preprocessing(1, 0);
        let out = run_parties(preps, |mut e| {
            let me = e.me();
            let twice = e.mul(&[sx[me], sx[me]], &[sx[me], sx[me]]).map(|_| ());
            (twice, e.random().map(|_| ()), e.remaining())
        });
        for o in out {
            assert_eq!(
                o,
                (
                    Err(MpcError::OutOfTriples),
                    Err(MpcError::OutOfRandoms),
                    (1, 0)
                )
            );
        }
    }
}
