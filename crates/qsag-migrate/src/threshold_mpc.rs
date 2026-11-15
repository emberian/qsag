//! Actively secure outer MPC for general custodian quorums.
//!
//! The selected quorum runs SPDZ over additive shares. Every shared wire
//! carries an information-theoretic MAC under a global key that no proper
//! subset of the quorum knows:
//!
//! * a Boolean wire is one 64-lane word `x` with the MAC `Δ · x(X)` in
//!   `GF(2)[X]/(X^128 + X^7 + X^2 + X + 1)`, where `x(X)` reads the 64 lanes as
//!   the coefficients of a polynomial of degree below 64;
//! * a prime-field wire is one field element per lane with the MAC `α · v`
//!   (two independent keys over Goldilocks).
//!
//! Multiplications use Beaver triples, conversions use doubly authenticated
//! bits, and inputs use authenticated random words; all of it comes from
//! preprocessing that is independent of the witness (`threshold_prep`).
//! Values opened inside the protocol are only *partially* opened: their MAC
//! shares are queued, and the queue is settled by a commit-then-open batch
//! MAC check ([`SpdzEngine::check`]) before any output opening is sent and
//! again before an opened output is returned to the caller. A failed check,
//! a malformed message, an inconsistent broadcast or exhausted preprocessing
//! poisons the engine and erases its MAC key shares.
//!
//! Soundness per check: a party that sends a wrong share of any opened value
//! passes with probability at most `2^-127` for Boolean wires, `2^-126` for
//! Goldilocks and `2^-254` for the 255/256-bit fields. Privacy holds against
//! any strict subset of the quorum (and, for Shamir custody, fewer than `t`
//! custodians overall). Abort is not identifiable and not fair.
use crate::{
    circuit::{Domain, Value},
    outer_mpc::{Core, Envelope, Error, FieldWord, Gadgets, ShareBit, Transport, Word},
    secret::{Secret, SecretVec, Wipe},
};
use alloc::{vec, vec::Vec};
use qsag_accel::{
    ct::{ct_eq_bytes_mask, ct_zeroize_bytes, ct_zeroize_u64s},
    gf2_128::gf2_128_mul,
    goldilocks::{gl_add, gl_mul, gl_sub},
    keccak::{Shake256, cshake256_framed_32},
};

/// Immutable roster and ordered active quorum. Party identities are zero based;
/// Shamir evaluation points are `party + 1` in the AES GF(256) polynomial basis.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ThresholdConfig {
    threshold: usize,
    parties: usize,
    quorum: Vec<usize>,
}
impl ThresholdConfig {
    pub fn new(threshold: usize, parties: usize, quorum: Vec<usize>) -> Result<Self, Error> {
        if !(2..=64).contains(&parties)
            || !(2..=parties).contains(&threshold)
            || quorum.len() < threshold
            || quorum.len() > parties
            || quorum.iter().any(|&p| p >= parties)
            || quorum.windows(2).any(|w| w[0] >= w[1])
        {
            return Err(Error::InvalidConfiguration);
        }
        Ok(Self {
            threshold,
            parties,
            quorum,
        })
    }
    pub fn threshold(&self) -> usize {
        self.threshold
    }
    pub fn parties(&self) -> usize {
        self.parties
    }
    pub fn quorum(&self) -> &[usize] {
        &self.quorum
    }
    pub(crate) fn binding(&self) -> Vec<u8> {
        let mut b = vec![self.threshold as u8, self.parties as u8];
        b.extend(self.quorum.iter().map(|&p| p as u8));
        b
    }
    /// Convert a bytewise degree-(t-1) Shamir share to its XOR contribution,
    /// without reconstructing any byte of the witness locally.
    pub fn shamir_contribution(&self, party: usize, share: &[u8; 32]) -> Result<[u8; 32], Error> {
        if !self.quorum.contains(&party) {
            return Err(Error::InvalidConfiguration);
        }
        let x = (party + 1) as u8;
        let mut weight = 1;
        for &peer in &self.quorum {
            if peer != party {
                let y = (peer + 1) as u8;
                weight = gf_mul(weight, gf_mul(y, gf_pow(x ^ y, 254)));
            }
        }
        Ok(share.map(|b| gf_mul(b, weight)))
    }
}
pub(crate) fn gf_mul(mut a: u8, mut b: u8) -> u8 {
    let mut out = 0;
    for _ in 0..8 {
        out ^= a & 0u8.wrapping_sub(b & 1);
        a = (a << 1) ^ (0x1b & 0u8.wrapping_sub(a >> 7));
        b >>= 1;
    }
    out
}
fn gf_pow(mut a: u8, mut n: u8) -> u8 {
    let mut out = 1;
    while n != 0 {
        if n & 1 != 0 {
            out = gf_mul(out, a);
        }
        a = gf_mul(a, a);
        n >>= 1;
    }
    out
}

/// Prime field of a preprocessing request.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ThresholdField {
    Goldilocks,
    Secp256k1,
    Ed25519,
}
impl ThresholdField {
    pub const ALL: [Self; 3] = [Self::Goldilocks, Self::Secp256k1, Self::Ed25519];
    pub(crate) fn domain(self) -> Domain {
        match self {
            Self::Goldilocks => Domain::Gold,
            Self::Secp256k1 => Domain::Secp,
            Self::Ed25519 => Domain::Ed,
        }
    }
    pub(crate) fn from_domain(d: Domain) -> Self {
        match d {
            Domain::Gold => Self::Goldilocks,
            Domain::Secp => Self::Secp256k1,
            Domain::Ed => Self::Ed25519,
            Domain::Bit => unreachable!("Boolean wires are not field wires"),
        }
    }
    pub(crate) fn index(self) -> usize {
        self as usize
    }
    /// Number of bits in the binary encoding of a field element.
    pub fn width(self) -> usize {
        self.domain().width()
    }
}

// ============================================================================
// MAC arithmetic
// ============================================================================

/// Multiply by `X` in `GF(2)[X]/(X^128 + X^7 + X^2 + X + 1)`.
#[inline(always)]
const fn mul_x(a: u128) -> u128 {
    (a << 1) ^ (0x87 & 0u128.wrapping_sub(a >> 127))
}

/// `sum_k lanes_k · X^k · macs[k]`: the word MAC of the lanes selected by
/// `lanes`, from per-lane MAC shares.
#[inline]
pub(crate) fn pack_macs(macs: &[u128; 64], lanes: u64) -> u128 {
    let mut acc = 0u128;
    for k in (0..64).rev() {
        acc = mul_x(acc) ^ (macs[k] & 0u128.wrapping_sub(((lanes >> k) & 1) as u128));
    }
    acc
}

/// MAC arithmetic of a field. Goldilocks MACs are pairs under two keys held
/// in limbs 0 and 1; the larger fields use one key and the plain field law.
#[inline(always)]
pub(crate) fn mac_add(d: Domain, a: Value, b: Value) -> Value {
    if d == Domain::Gold {
        [gl_add(a[0], b[0]), gl_add(a[1], b[1]), 0, 0]
    } else {
        d.add(a, b)
    }
}
#[inline(always)]
pub(crate) fn mac_sub(d: Domain, a: Value, b: Value) -> Value {
    if d == Domain::Gold {
        [gl_sub(a[0], b[0]), gl_sub(a[1], b[1]), 0, 0]
    } else {
        d.sub(a, b)
    }
}
/// MAC (or MAC key) times a field element.
#[inline(always)]
pub(crate) fn mac_scale(d: Domain, mac: Value, by: Value) -> Value {
    if d == Domain::Gold {
        [gl_mul(mac[0], by[0]), gl_mul(mac[1], by[0]), 0, 0]
    } else {
        d.mul(mac, by)
    }
}
pub(crate) fn mac_canonical(d: Domain, mac: Value) -> bool {
    if d == Domain::Gold {
        d.canonical([mac[0], 0, 0, 0]) && d.canonical([mac[1], 0, 0, 0]) && mac[2] | mac[3] == 0
    } else {
        d.canonical(mac)
    }
}

// ============================================================================
// Wires and preprocessing material
// ============================================================================

/// One party's share of an authenticated 64-lane Boolean word:
/// `[value share, MAC share low, MAC share high]`.
#[derive(Clone, Copy, Default)]
pub(crate) struct ABit(pub [u64; 3]);
impl ABit {
    #[inline(always)]
    pub(crate) const fn new(share: u64, mac: u128) -> Self {
        Self([share, mac as u64, (mac >> 64) as u64])
    }
    #[inline(always)]
    pub(crate) const fn share(self) -> u64 {
        self.0[0]
    }
    #[inline(always)]
    pub(crate) const fn mac(self) -> u128 {
        (self.0[1] as u128) | ((self.0[2] as u128) << 64)
    }
}
impl core::ops::BitXor for ABit {
    type Output = Self;
    #[inline(always)]
    fn bitxor(self, rhs: Self) -> Self {
        Self([
            self.0[0] ^ rhs.0[0],
            self.0[1] ^ rhs.0[1],
            self.0[2] ^ rhs.0[2],
        ])
    }
}
impl Wipe for ABit {
    fn secret_wipe(&mut self) {
        ct_zeroize_u64s(&mut self.0);
    }
    fn wipe_slice(values: &mut [Self]) {
        qsag_asm::volatile_fill(values, Self::default());
    }
}
impl ShareBit for ABit {}

/// One party's additive shares of the global MAC keys. Summed over the
/// quorum they give `Δ` (Boolean, never zero in practice), the two
/// Goldilocks keys and the secp256k1 and Ed25519 base-field keys. Erased on
/// drop; a party never learns another party's share.
pub struct MacKeyShare {
    pub boolean: u128,
    /// Indexed by [`ThresholdField`]; Goldilocks uses limbs 0 and 1.
    pub field: [Value; 3],
}
impl Drop for MacKeyShare {
    fn drop(&mut self) {
        qsag_asm::volatile_fill(core::slice::from_mut(&mut self.boolean), 0);
        ct_zeroize_u64s(self.field.as_flattened_mut());
    }
}
impl MacKeyShare {
    pub(crate) fn duplicate(&self) -> Self {
        Self {
            boolean: self.boolean,
            field: self.field,
        }
    }
    fn valid(&self) -> bool {
        ThresholdField::ALL
            .iter()
            .all(|f| mac_canonical(f.domain(), self.field[f.index()]))
    }
}

/// One party's share of 64 authenticated bits: lane `k` of `share` is its XOR
/// share of bit `k`, and `macs[k]` its XOR share of `bit_k · Δ`.
pub struct AuthWord {
    pub share: u64,
    pub macs: [u128; 64],
}
impl Drop for AuthWord {
    fn drop(&mut self) {
        ct_zeroize_u64s(core::slice::from_mut(&mut self.share));
        qsag_asm::volatile_fill(&mut self.macs, 0);
    }
}
impl AuthWord {
    fn bit(&self) -> ABit {
        ABit::new(self.share, pack_macs(&self.macs, u64::MAX))
    }
}

/// One party's share of 64 Boolean Beaver triples `c_k = a_k & b_k`.
pub struct BooleanTriple {
    pub a: AuthWord,
    pub b: AuthWord,
    pub c: AuthWord,
}

/// One party's share of an authenticated field element: `[value, MAC]`.
pub struct FieldShare(pub [Value; 2]);
impl Drop for FieldShare {
    fn drop(&mut self) {
        ct_zeroize_u64s(self.0.as_flattened_mut());
    }
}

/// One party's share of a field Beaver triple `(a, b, a·b)`.
pub struct FieldTriple(pub [FieldShare; 3]);

/// One party's share of 64 doubly authenticated bits: the same uniformly
/// random bits shared as a Boolean word and, lane by lane, as field elements.
pub struct DaBitWord {
    pub bits: AuthWord,
    pub field: [FieldShare; 64],
}

// ============================================================================
// Engine
// ============================================================================

const CHECK_WORDS: usize = 12;

struct PendingField {
    values: SecretVec<Value>,
    macs: SecretVec<Value>,
}

/// One party's online state. Wires made by one engine may be used by another
/// engine of the same party that holds the same MAC key shares.
pub(crate) struct SpdzEngine<T> {
    pub(crate) config: ThresholdConfig,
    pub(crate) party: usize,
    first: bool,
    peers: Vec<usize>,
    /// Session as given by the caller; batch engines derive theirs from it.
    #[cfg(any(feature = "std", test))]
    root_session: [u8; 32],
    session: [u8; 32],
    link_keys: Vec<[u8; 32]>,
    keys: MacKeyShare,
    ones_mac: u128,
    sequence: u64,
    failed: bool,
    rng: Shake256,
    /// Hash chain over every broadcast payload, in quorum order. Compared
    /// across the quorum at each check, so equivocation is caught there.
    transcript: [u8; 32],
    transcript_dirty: bool,
    pending_bits: SecretVec<u64>,
    pending_bit_macs: SecretVec<u128>,
    pending_fields: [PendingField; 3],
    #[cfg(any(feature = "std", test))]
    pub(crate) batch_cancelled: Option<alloc::sync::Arc<core::sync::atomic::AtomicBool>>,
    #[cfg(test)]
    pub(crate) fault: Option<Fault>,
    pub(crate) transport: T,
}

/// Deviations a corrupt custodian can make, for regression tests. Each one
/// fires once, on the first matching operation.
#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Fault {
    /// Flip one lane of the local value share of a wire about to be opened.
    FlipOpenedShare { lane: usize },
    /// Send a wrong masked difference in a Boolean Beaver opening.
    BeaverOpening { lane: usize },
    /// Use a wrong local product share after a Boolean Beaver opening.
    BeaverOutput { lane: usize },
    /// Send a wrong masked difference in a field Beaver opening.
    FieldBeaverOpening { lane: usize },
    /// Send a wrong masked bit during a Boolean-to-field conversion.
    ConversionBit { lane: usize },
    /// Send a wrong masked difference during a field-to-Boolean conversion.
    ConversionField { lane: usize },
    /// Contribute a non-uniform word where lane-uniform input is required.
    SplitInput,
    /// Send different opening shares to different peers.
    Equivocate,
    /// Open the correct value share but hold a wrong MAC share for it.
    WrongMac,
}

impl<T> Drop for SpdzEngine<T> {
    fn drop(&mut self) {
        for key in &mut self.link_keys {
            ct_zeroize_bytes(key);
        }
        qsag_asm::volatile_fill(core::slice::from_mut(&mut self.ones_mac), 0);
        ct_zeroize_bytes(&mut self.transcript);
    }
}

fn words32(bytes: &[u8; 32]) -> [u64; 4] {
    core::array::from_fn(|i| u64::from_le_bytes(bytes[8 * i..8 * i + 8].try_into().unwrap()))
}
fn bytes_of(words: &[u64]) -> Vec<u8> {
    words.iter().flat_map(|w| w.to_le_bytes()).collect()
}

impl<T: Transport> SpdzEngine<T> {
    pub(crate) fn new(
        party: usize,
        session: [u8; 32],
        config: ThresholdConfig,
        mut link_keys: Vec<[u8; 32]>,
        keys: MacKeyShare,
        transport: T,
    ) -> Result<Self, Error> {
        if !config.quorum.contains(&party)
            || link_keys.len() != config.quorum.len() - 1
            || !keys.valid()
        {
            for key in &mut link_keys {
                ct_zeroize_bytes(key);
            }
            return Err(Error::InvalidConfiguration);
        }
        #[cfg(any(feature = "std", test))]
        let root_session = session;
        let session = cshake256_framed_32(b"QSAG.OUTER.SPDZ.V1", &[&session, &config.binding()]);
        let mut rng = Shake256::new();
        rng.absorb(b"QSAG.OUTER.SPDZ.RNG.V1");
        rng.absorb(&session);
        rng.absorb(&[party as u8]);
        for key in &link_keys {
            rng.absorb(key);
        }
        rng.finalize(0x1f);
        let peers = config
            .quorum
            .iter()
            .copied()
            .filter(|&p| p != party)
            .collect();
        let empty = || PendingField {
            values: SecretVec::new(),
            macs: SecretVec::new(),
        };
        Ok(Self {
            first: party == config.quorum[0],
            ones_mac: gf2_128_mul(keys.boolean, u64::MAX as u128),
            transcript: cshake256_framed_32(b"QSAG.OUTER.SPDZ.TRANSCRIPT.V1", &[&session]),
            config,
            party,
            peers,
            #[cfg(any(feature = "std", test))]
            root_session,
            session,
            link_keys,
            keys,
            sequence: 0,
            failed: false,
            rng,
            transcript_dirty: false,
            pending_bits: SecretVec::new(),
            pending_bit_macs: SecretVec::new(),
            pending_fields: [empty(), empty(), empty()],
            #[cfg(any(feature = "std", test))]
            batch_cancelled: None,
            #[cfg(test)]
            fault: None,
            transport,
        })
    }

    /// Custody secrets for starting this custodian's batch engines.
    #[cfg(any(feature = "std", test))]
    pub(crate) fn custody(&self) -> ([u8; 32], ThresholdConfig, Vec<[u8; 32]>, MacKeyShare) {
        (
            self.root_session,
            self.config.clone(),
            self.link_keys.clone(),
            self.keys.duplicate(),
        )
    }

    /// Hedge local commitment and coin randomness with private ceremony entropy.
    pub(crate) fn mix_entropy(&mut self, entropy: &[u8; 32]) {
        let mut current = [0u8; 32];
        self.rng.squeeze(&mut current);
        let mut next = Shake256::new();
        next.absorb(b"QSAG.OUTER.SPDZ.HEDGE.V1");
        next.absorb(&current);
        next.absorb(entropy);
        next.absorb(&self.session);
        next.finalize(0x1f);
        ct_zeroize_bytes(&mut current);
        self.rng = next;
    }

    fn fail<V>(&mut self, error: Error) -> Result<V, Error> {
        Core::poison(self);
        Err(error)
    }

    fn tag(&self, key: &[u8; 32], sender: usize, recipient: usize, payload: &[u64]) -> [u8; 32] {
        let mut encoded = bytes_of(payload);
        let tag = cshake256_framed_32(
            b"QSAG.OUTER.SPDZ.MAC.V1",
            &[
                key,
                &self.session,
                &(sender as u64).to_le_bytes(),
                &(recipient as u64).to_le_bytes(),
                &self.sequence.to_le_bytes(),
                &encoded,
            ],
        );
        ct_zeroize_bytes(&mut encoded);
        tag
    }

    /// Send `own` to every peer and return all payloads in quorum order (own
    /// included). Any transport or authentication failure poisons the engine.
    fn broadcast(&mut self, own: &[u64]) -> Result<Vec<SecretVec<u64>>, Error> {
        self.send(&vec![own; self.peers.len()], own)
    }

    fn send(&mut self, to_peers: &[&[u64]], own: &[u64]) -> Result<Vec<SecretVec<u64>>, Error> {
        if self.failed {
            return Err(Error::MultiplicationCheck);
        }
        #[cfg(any(feature = "std", test))]
        if self
            .batch_cancelled
            .as_ref()
            .is_some_and(|flag| flag.load(core::sync::atomic::Ordering::Relaxed))
        {
            return Err(Error::Transport);
        }
        let outgoing = self
            .peers
            .iter()
            .zip(&self.link_keys)
            .zip(to_peers)
            .map(|((&peer, key), payload)| Envelope {
                sender: self.party,
                recipient: peer,
                sequence: self.sequence,
                payload: payload.to_vec(),
                tag: self.tag(key, self.party, peer, payload),
            })
            .collect();
        let incoming = match self.transport.exchange_many(outgoing) {
            Ok(incoming) => incoming,
            Err(error) => return self.fail(error),
        };
        if incoming.len() != self.peers.len() {
            return self.fail(Error::InvalidConfiguration);
        }
        let mut received = Vec::with_capacity(self.peers.len());
        for (i, mut message) in incoming.into_iter().enumerate() {
            let peer = self.peers[i];
            if message.sender != peer
                || message.recipient != self.party
                || message.sequence != self.sequence
                || message.payload.len() != own.len()
                || ct_eq_bytes_mask(
                    &message.tag,
                    &self.tag(&self.link_keys[i], peer, self.party, &message.payload),
                ) != u64::MAX
            {
                return self.fail(Error::Authentication(peer));
            }
            received.push(SecretVec::from(core::mem::take(&mut message.payload)));
        }
        let mine = self
            .config
            .quorum
            .iter()
            .position(|&p| p == self.party)
            .unwrap();
        received.insert(mine, own.iter().copied().collect());
        let mut chain = Shake256::new();
        chain.absorb(b"QSAG.OUTER.SPDZ.CHAIN.V1");
        chain.absorb(&self.transcript);
        chain.absorb(&self.sequence.to_le_bytes());
        for payload in &received {
            let mut bytes = bytes_of(payload);
            chain.absorb(&bytes);
            ct_zeroize_bytes(&mut bytes);
        }
        chain.finalize(0x1f);
        chain.squeeze(&mut self.transcript);
        self.transcript_dirty = true;
        self.sequence = match self.sequence.checked_add(1) {
            Some(next) => next,
            None => return self.fail(Error::InvalidConfiguration),
        };
        Ok(received)
    }

    /// Hiding and binding commitment of the quorum member at `position` to
    /// `payload` in the current round. Binding the position stops one member
    /// from replaying another's commitment and opening.
    fn commitment(
        &self,
        label: &[u8],
        position: usize,
        payload: &[u64],
        nonce: &[u8; 32],
    ) -> [u64; 4] {
        let mut bytes = bytes_of(payload);
        let digest = cshake256_framed_32(
            b"QSAG.OUTER.SPDZ.COMMIT.V1",
            &[
                label,
                &self.session,
                &self.sequence.to_le_bytes(),
                &[position as u8],
                &bytes,
                nonce,
            ],
        );
        ct_zeroize_bytes(&mut bytes);
        words32(&digest)
    }

    /// Commit to `payload`, then open it; every party's opening is checked
    /// against its commitment. Returns all payloads in quorum order.
    fn commit_then_open(
        &mut self,
        label: &[u8],
        payload: &[u64],
        prefix: &[u64],
    ) -> Result<Vec<SecretVec<u64>>, Error> {
        let mut nonce = [0u8; 32];
        self.rng.squeeze(&mut nonce);
        let mine = self
            .config
            .quorum
            .iter()
            .position(|&p| p == self.party)
            .unwrap();
        let own_commit = self.commitment(label, mine, payload, &nonce);
        let committed_at = self.sequence;
        let mut first: Vec<u64> = prefix.to_vec();
        first.extend_from_slice(&own_commit);
        let commits = self.broadcast(&first)?;
        if commits
            .iter()
            .any(|c| c[..prefix.len()] != first[..prefix.len()])
        {
            return self.fail(Error::MultiplicationCheck);
        }
        let mut opening: SecretVec<u64> = payload.iter().copied().collect();
        opening.extend_from_slice(&words32(&nonce));
        ct_zeroize_bytes(&mut nonce);
        let opened = self.broadcast(&opening)?;
        let now = self.sequence;
        self.sequence = committed_at;
        let mut ok = true;
        for (position, (commit, open)) in commits.iter().zip(&opened).enumerate() {
            let (body, nonce) = open.split_at(payload.len());
            let mut nonce_bytes = [0u8; 32];
            for (chunk, word) in nonce_bytes.chunks_exact_mut(8).zip(nonce) {
                chunk.copy_from_slice(&word.to_le_bytes());
            }
            ok &= commit[prefix.len()..] == self.commitment(label, position, body, &nonce_bytes);
        }
        self.sequence = now;
        if !ok {
            return self.fail(Error::MultiplicationCheck);
        }
        Ok(opened
            .into_iter()
            .map(|open| open[..payload.len()].iter().copied().collect())
            .collect())
    }

    fn field_challenge(xof: &mut Shake256, d: Domain) -> Value {
        loop {
            let mut bytes = [0u8; 32];
            xof.squeeze(&mut bytes[..d.width().div_ceil(64) * 8]);
            let mut value = words32(&bytes);
            if d == Domain::Ed {
                value[3] &= 0x7fff_ffff_ffff_ffff;
            }
            if d.canonical(value) {
                return value;
            }
        }
    }

    /// Batch MAC check of every partially opened value since the last check.
    ///
    /// 1. All parties compare their transcript chains and commit to coin shares.
    /// 2. The coin shares open and fix the challenges `χ`.
    /// 3. Each party commits to `σ_i = Σ χ_j (m_ij − key_i · v_j)`, per field.
    /// 4. The `σ_i` open; they must sum to zero.
    ///
    /// The challenges are fixed only after every checked value is public, and
    /// each `σ_i` is bound before any other is seen, so a wrong opened value
    /// survives only if its sender predicted a key or a challenge collapse.
    pub(crate) fn check(&mut self) -> Result<(), Error> {
        if self.failed {
            return Err(Error::MultiplicationCheck);
        }
        if !self.transcript_dirty {
            return Ok(());
        }
        let transcript = words32(&self.transcript);
        let mut coin = [0u8; 32];
        self.rng.squeeze(&mut coin);
        let coins = self.commit_then_open(b"coin", &words32(&coin), &transcript)?;
        ct_zeroize_bytes(&mut coin);
        let mut xof = Shake256::new();
        xof.absorb(b"QSAG.OUTER.SPDZ.CHALLENGE.V1");
        xof.absorb(&self.session);
        xof.absorb(&self.transcript);
        for share in &coins {
            xof.absorb(&bytes_of(share));
        }
        xof.finalize(0x1f);

        let mut sigma = Secret([0u64; CHECK_WORDS]);
        {
            let count = self.pending_bits.len();
            let mut chi = vec![0u128; count];
            for c in &mut chi {
                let mut bytes = [0u8; 16];
                xof.squeeze(&mut bytes);
                *c = u128::from_le_bytes(bytes);
            }
            let values: SecretVec<u128> = self.pending_bits.iter().map(|&v| v as u128).collect();
            let mac_sum = qsag_asm::gf2_128_dot(&chi, &self.pending_bit_macs);
            let value_sum = qsag_asm::gf2_128_dot(&chi, &values);
            let s = mac_sum ^ gf2_128_mul(self.keys.boolean, value_sum);
            sigma[0] = s as u64;
            sigma[1] = (s >> 64) as u64;
            self.pending_bits.clear();
            self.pending_bit_macs.clear();
        }
        for field in ThresholdField::ALL {
            let d = field.domain();
            let key = self.keys.field[field.index()];
            let pending = &mut self.pending_fields[field.index()];
            // Goldilocks: an independent challenge vector per key, so that a
            // collapse of one linear combination does not defeat both MACs.
            let mut acc = Secret([0u64; 4]);
            let lanes = if d == Domain::Gold { 2 } else { 1 };
            for lane in 0..lanes {
                let mut total = Secret([0u64; 4]);
                for (value, mac) in pending.values.iter().zip(pending.macs.iter()) {
                    let chi = Self::field_challenge(&mut xof, d);
                    let (m, k) = if d == Domain::Gold {
                        ([mac[lane], 0, 0, 0], [key[lane], 0, 0, 0])
                    } else {
                        (*mac, key)
                    };
                    let term = d.sub(m, d.mul(k, *value));
                    *total = d.add(*total, d.mul(chi, term));
                }
                if d == Domain::Gold {
                    acc[lane] = total[0];
                } else {
                    *acc = *total;
                }
            }
            let at = match field {
                ThresholdField::Goldilocks => 2,
                ThresholdField::Secp256k1 => 4,
                ThresholdField::Ed25519 => 8,
            };
            let len = if d == Domain::Gold { 2 } else { 4 };
            sigma[at..at + len].copy_from_slice(&acc[..len]);
            pending.values.clear();
            pending.macs.clear();
        }
        let sigmas = self.commit_then_open(b"sigma", &sigma[..], &[])?;
        let mut boolean = 0u128;
        let mut fields = [[0u64; 4]; 3];
        for s in &sigmas {
            boolean ^= (s[0] as u128) | ((s[1] as u128) << 64);
            for field in ThresholdField::ALL {
                let d = field.domain();
                let share = match field {
                    ThresholdField::Goldilocks => [s[2], s[3], 0, 0],
                    ThresholdField::Secp256k1 => [s[4], s[5], s[6], s[7]],
                    ThresholdField::Ed25519 => [s[8], s[9], s[10], s[11]],
                };
                if !mac_canonical(d, share) {
                    return self.fail(Error::MultiplicationCheck);
                }
                fields[field.index()] = mac_add(d, fields[field.index()], share);
            }
        }
        if boolean != 0 || fields != [[0u64; 4]; 3] {
            return self.fail(Error::MultiplicationCheck);
        }
        self.transcript_dirty = false;
        Ok(())
    }

    /// Reveal Boolean wires to the quorum without checking them yet; their
    /// MAC shares join the queue settled by the next [`Self::check`].
    fn partial_open(&mut self, wires: &[ABit]) -> Result<Vec<u64>, Error> {
        let own: SecretVec<u64> = wires.iter().map(|w| w.share()).collect();
        #[cfg(test)]
        if self.fault == Some(Fault::Equivocate) && !own.is_empty() {
            self.fault = None;
            let mut other = own.clone();
            other[0] ^= 1;
            let mut payloads: Vec<&[u64]> = vec![&own; self.peers.len()];
            payloads[0] = &other;
            return self.finish_partial_open(wires, &payloads, &own);
        }
        let payloads: Vec<&[u64]> = vec![&own; self.peers.len()];
        self.finish_partial_open(wires, &payloads, &own)
    }

    fn finish_partial_open(
        &mut self,
        wires: &[ABit],
        payloads: &[&[u64]],
        own: &[u64],
    ) -> Result<Vec<u64>, Error> {
        let shares = self.send(payloads, own)?;
        let mut out = vec![0u64; wires.len()];
        for share in &shares {
            for (acc, s) in out.iter_mut().zip(share.iter()) {
                *acc ^= s;
            }
        }
        self.pending_bits.extend_from_slice(&out);
        self.pending_bit_macs.extend(wires.iter().map(|w| w.mac()));
        Ok(out)
    }

    fn partial_open_fields(
        &mut self,
        shares: &[[Value; 2]],
        d: Domain,
    ) -> Result<Vec<Value>, Error> {
        let own: SecretVec<u64> = shares.iter().flat_map(|s| s[0]).collect();
        let received = self.broadcast(&own)?;
        let mut out = vec![[0u64; 4]; shares.len()];
        for row in &received {
            for (acc, limbs) in out.iter_mut().zip(row.chunks_exact(4)) {
                let value: Value = limbs.try_into().unwrap();
                if !d.canonical(value) {
                    return self.fail(Error::InvalidConfiguration);
                }
                *acc = d.add(*acc, value);
            }
        }
        let pending = &mut self.pending_fields[ThresholdField::from_domain(d).index()];
        pending.values.extend_from_slice(&out);
        pending.macs.extend(shares.iter().map(|s| s[1]));
        Ok(out)
    }

    fn public_bit(&self, x: u64) -> ABit {
        let mac = match x {
            0 => 0,
            u64::MAX => self.ones_mac,
            _ => gf2_128_mul(self.keys.boolean, x as u128),
        };
        ABit::new(if self.first { x } else { 0 }, mac)
    }

    fn public_field(&self, value: Value, d: Domain) -> [Value; 2] {
        let key = self.keys.field[ThresholdField::from_domain(d).index()];
        [
            if self.first { value } else { [0; 4] },
            mac_scale(d, key, value),
        ]
    }

    fn take<V>(&mut self, taken: Result<Vec<V>, Error>, count: usize) -> Result<Vec<V>, Error> {
        match taken {
            Ok(items) if items.len() == count => Ok(items),
            Ok(_) => self.fail(Error::InvalidConfiguration),
            Err(error) => self.fail(error),
        }
    }

    fn field_share_valid(d: Domain, share: &FieldShare) -> bool {
        d.canonical(share.0[0]) && mac_canonical(d, share.0[1])
    }

    fn input(&mut self, own: &[u64], uniform: bool) -> Result<Word<ABit>, Error> {
        if self.failed {
            return Err(Error::MultiplicationCheck);
        }
        let taken = self.transport.take_auth_words(own.len());
        let masks = self.take(taken, own.len())?;
        // The mask is itself lane-uniform in the uniform case: its single
        // authenticated bit (lane 0) is spread over all lanes, so the masked
        // word reveals nothing and the shared input is uniform by construction.
        let masks: SecretVec<ABit> = masks
            .iter()
            .map(|r| {
                if uniform {
                    ABit::new(
                        0u64.wrapping_sub(r.share & 1),
                        gf2_128_mul(r.macs[0], u64::MAX as u128),
                    )
                } else {
                    r.bit()
                }
            })
            .collect();
        #[allow(unused_mut)]
        let mut masked: SecretVec<u64> = own
            .iter()
            .zip(masks.iter())
            .map(|(&x, r)| x ^ r.share())
            .collect();
        #[cfg(test)]
        if uniform && self.fault == Some(Fault::SplitInput) && !masked.is_empty() {
            self.fault = None;
            masked[0] ^= 1;
        }
        let received = self.broadcast(&masked)?;
        let mut public = vec![0u64; own.len()];
        for (position, row) in received.iter().enumerate() {
            if uniform && row.iter().any(|&w| w != 0 && w != u64::MAX) {
                let culprit = self.config.quorum[position];
                return self.fail(Error::Disagreement(culprit));
            }
            for (acc, w) in public.iter_mut().zip(row.iter()) {
                *acc ^= w;
            }
        }
        Ok(masks
            .iter()
            .zip(public)
            .map(|(&r, e)| r ^ self.public_bit(e))
            .collect())
    }
}

impl<T: Transport> Core for SpdzEngine<T> {
    type Bit = ABit;

    #[inline]
    fn constant(&self, x: u64) -> ABit {
        self.public_bit(x)
    }

    fn share(&mut self, own: &[u64]) -> Result<Word<ABit>, Error> {
        self.input(own, false)
    }

    fn share_uniform_lanes(&mut self, own: &[u64]) -> Result<Word<ABit>, Error> {
        if own.iter().any(|&w| w != 0 && w != u64::MAX) {
            return Err(Error::InvalidConfiguration);
        }
        self.input(own, true)
    }

    fn and_into(&mut self, pairs: &[(ABit, ABit)], out: &mut Word<ABit>) -> Result<(), Error> {
        out.clear();
        if self.failed {
            return Err(Error::MultiplicationCheck);
        }
        if pairs.is_empty() {
            return Ok(());
        }
        let taken = self.transport.take_boolean_triples(pairs.len());
        let triples = self.take(taken, pairs.len())?;
        let k = pairs.len();
        let mut masked: SecretVec<ABit> = SecretVec::with_capacity(2 * k);
        for (&(x, _), t) in pairs.iter().zip(&triples) {
            masked.push(x ^ t.a.bit());
        }
        for (&(_, y), t) in pairs.iter().zip(&triples) {
            masked.push(y ^ t.b.bit());
        }
        #[cfg(test)]
        if let Some(Fault::BeaverOpening { lane }) = self.fault {
            self.fault = None;
            masked[0].0[0] ^= 1 << (lane & 63);
        }
        let opened = self.partial_open(&masked)?;
        let (d, e) = opened.split_at(k);
        out.reserve(k);
        for ((t, &d), &e) in triples.iter().zip(d).zip(e) {
            let share = t.c.share ^ (d & t.b.share) ^ (e & t.a.share);
            let mac =
                pack_macs(&t.c.macs, u64::MAX) ^ pack_macs(&t.b.macs, d) ^ pack_macs(&t.a.macs, e);
            out.push(ABit::new(share, mac) ^ self.public_bit(d & e));
        }
        #[cfg(test)]
        if let Some(Fault::BeaverOutput { lane }) = self.fault {
            self.fault = None;
            out[0].0[0] ^= 1 << (lane & 63);
        }
        Ok(())
    }

    fn verify_all_pending(&mut self) -> Result<(), Error> {
        self.check()
    }

    fn open(&mut self, bits: &[ABit]) -> Result<Vec<u64>, Error> {
        self.check()?;
        #[cfg(test)]
        if let Some(Fault::FlipOpenedShare { lane }) = self.fault
            && !bits.is_empty()
        {
            self.fault = None;
            let mut forged: SecretVec<ABit> = bits.iter().copied().collect();
            forged[0].0[0] ^= 1 << (lane & 63);
            let opened = self.partial_open(&forged)?;
            self.check()?;
            return Ok(opened);
        }
        #[cfg(test)]
        if self.fault == Some(Fault::WrongMac) && !bits.is_empty() {
            self.fault = None;
            let mut forged: SecretVec<ABit> = bits.iter().copied().collect();
            forged[0].0[1] ^= 1;
            let opened = self.partial_open(&forged)?;
            self.check()?;
            return Ok(opened);
        }
        let opened = self.partial_open(bits)?;
        self.check()?;
        Ok(opened)
    }

    fn open_lanes(&mut self, bits: &[ABit], mask: u64) -> Result<Vec<u64>, Error> {
        if mask == u64::MAX {
            return self.open(bits);
        }
        if self.failed {
            return Err(Error::MultiplicationCheck);
        }
        // Hidden lanes are one-time padded with authenticated random bits.
        let taken = self.transport.take_auth_words(bits.len());
        let pads = self.take(taken, bits.len())?;
        let padded: SecretVec<ABit> = bits
            .iter()
            .zip(&pads)
            .map(|(&b, r)| b ^ ABit::new(r.share & !mask, pack_macs(&r.macs, !mask)))
            .collect();
        let mut opened = self.open(&padded)?;
        for word in &mut opened {
            *word &= mask;
        }
        Ok(opened)
    }

    fn agree(&mut self, root: [u8; 32]) -> Result<(), Error> {
        self.check()?;
        let own = words32(&root);
        let received = self.broadcast(&own)?;
        for (position, row) in received.iter().enumerate() {
            if row[..] != own[..] {
                let culprit = self.config.quorum[position];
                return self.fail(Error::Disagreement(culprit));
            }
        }
        Ok(())
    }

    fn poison(&mut self) {
        self.failed = true;
        self.keys = MacKeyShare {
            boolean: 0,
            field: [[0; 4]; 3],
        };
        qsag_asm::volatile_fill(core::slice::from_mut(&mut self.ones_mac), 0);
        self.pending_bits.clear();
        self.pending_bit_macs.clear();
        for pending in &mut self.pending_fields {
            pending.values.clear();
            pending.macs.clear();
        }
    }

    fn fconstant(&self, value: Value, d: Domain) -> FieldWord {
        vec![self.public_field(value, d); 64].into()
    }

    fn fscale_lanes(&self, a: &FieldWord, by: &[Value], d: Domain) -> FieldWord {
        a.iter()
            .zip(by)
            .map(|(a, by)| [d.mul(a[0], *by), mac_scale(d, a[1], *by)])
            .collect()
    }

    fn fadd(&self, a: &FieldWord, b: &FieldWord, d: Domain) -> FieldWord {
        a.iter()
            .zip(b.iter())
            .map(|(a, b)| {
                let (a, b) = (*a, *b);
                [d.add(a[0], b[0]), mac_add(d, a[1], b[1])]
            })
            .collect()
    }

    fn fsub(&self, a: &FieldWord, b: &FieldWord, d: Domain) -> FieldWord {
        a.iter()
            .zip(b.iter())
            .map(|(a, b)| {
                let (a, b) = (*a, *b);
                [d.sub(a[0], b[0]), mac_sub(d, a[1], b[1])]
            })
            .collect()
    }

    fn fscale(&self, a: &FieldWord, by: Value, d: Domain) -> FieldWord {
        a.iter()
            .map(|a| {
                let a = *a;
                [d.mul(a[0], by), mac_scale(d, a[1], by)]
            })
            .collect()
    }

    fn frandom(&mut self, d: Domain) -> Result<FieldWord, Error> {
        if self.failed {
            return Err(Error::MultiplicationCheck);
        }
        let taken = self
            .transport
            .take_field_randoms(ThresholdField::from_domain(d), 64);
        let randoms = self.take(taken, 64)?;
        if randoms.iter().any(|r| !Self::field_share_valid(d, r)) {
            return self.fail(Error::InvalidConfiguration);
        }
        Ok(randoms.iter().map(|r| r.0).collect())
    }

    fn fmul_many(
        &mut self,
        pairs: &[(&FieldWord, &FieldWord)],
        d: Domain,
    ) -> Result<Vec<FieldWord>, Error> {
        if self.failed {
            return Err(Error::MultiplicationCheck);
        }
        if pairs.is_empty() {
            return Ok(Vec::new());
        }
        let count = pairs.len() * 64;
        let taken = self
            .transport
            .take_field_triples(ThresholdField::from_domain(d), count);
        let triples = self.take(taken, count)?;
        if triples
            .iter()
            .any(|t| t.0.iter().any(|s| !Self::field_share_valid(d, s)))
        {
            return self.fail(Error::InvalidConfiguration);
        }
        let mut masked: SecretVec<[Value; 2]> = SecretVec::with_capacity(2 * count);
        let lanes = || pairs.iter().flat_map(|(a, b)| a.iter().zip(b.iter()));
        for ((x, _), t) in lanes().zip(&triples) {
            let x = *x;
            let a = t.0[0].0;
            masked.push([d.sub(x[0], a[0]), mac_sub(d, x[1], a[1])]);
        }
        for ((_, y), t) in lanes().zip(&triples) {
            let y = *y;
            let b = t.0[1].0;
            masked.push([d.sub(y[0], b[0]), mac_sub(d, y[1], b[1])]);
        }
        #[cfg(test)]
        if let Some(Fault::FieldBeaverOpening { lane }) = self.fault {
            self.fault = None;
            masked[lane & 63][0] = d.add(masked[lane & 63][0], [1, 0, 0, 0]);
        }
        let opened = self.partial_open_fields(&masked, d)?;
        let (delta, epsilon) = opened.split_at(count);
        let products: FieldWord = triples
            .iter()
            .zip(delta)
            .zip(epsilon)
            .map(|((t, &de), &ep)| {
                let [a, b, c] = [t.0[0].0, t.0[1].0, t.0[2].0];
                let constant = self.public_field(d.mul(de, ep), d);
                let share = d.add(
                    d.add(c[0], constant[0]),
                    d.add(d.mul(de, b[0]), d.mul(ep, a[0])),
                );
                let mac = mac_add(
                    d,
                    mac_add(d, c[1], constant[1]),
                    mac_add(d, mac_scale(d, b[1], de), mac_scale(d, a[1], ep)),
                );
                [share, mac]
            })
            .collect();
        Ok(products
            .chunks_exact(64)
            .map(|w| w.iter().copied().collect())
            .collect())
    }

    fn fopen_many(&mut self, words: &[FieldWord], d: Domain) -> Result<Vec<Vec<Value>>, Error> {
        if words.is_empty() {
            return Ok(Vec::new());
        }
        self.check()?;
        let flat: SecretVec<[Value; 2]> = words.iter().flat_map(|w| w.iter().copied()).collect();
        let opened = self.partial_open_fields(&flat, d)?;
        self.check()?;
        Ok(opened.chunks_exact(64).map(|v| v.to_vec()).collect())
    }

    /// `[x]_p = c + (1 − 2c)·[r]_p` for the public masked bit `c = x ⊕ r` of a
    /// doubly authenticated random bit `r`: no multiplication and no input
    /// from any party, so a party cannot substitute a different bit.
    fn lift_bits_many(&mut self, bits: &[ABit], d: Domain) -> Result<Vec<FieldWord>, Error> {
        if self.failed {
            return Err(Error::MultiplicationCheck);
        }
        if bits.is_empty() {
            return Ok(Vec::new());
        }
        let taken = self
            .transport
            .take_dabits(ThresholdField::from_domain(d), bits.len());
        let dabits = self.take(taken, bits.len())?;
        if dabits
            .iter()
            .any(|r| r.field.iter().any(|s| !Self::field_share_valid(d, s)))
        {
            return self.fail(Error::InvalidConfiguration);
        }
        #[allow(unused_mut)]
        let mut masked: SecretVec<ABit> = bits
            .iter()
            .zip(&dabits)
            .map(|(&x, r)| x ^ r.bits.bit())
            .collect();
        #[cfg(test)]
        if let Some(Fault::ConversionBit { lane }) = self.fault {
            self.fault = None;
            masked[0].0[0] ^= 1 << (lane & 63);
        }
        let opened = self.partial_open(&masked)?;
        let one = self.public_field([1, 0, 0, 0], d);
        Ok(dabits
            .iter()
            .zip(opened)
            .map(|(r, c)| {
                (0..64)
                    .map(|lane| {
                        let r = r.field[lane].0;
                        if (c >> lane) & 1 == 0 {
                            r
                        } else {
                            [d.sub(one[0], r[0]), mac_sub(d, one[1], r[1])]
                        }
                    })
                    .collect()
            })
            .collect())
    }

    fn bits_to_field_many(
        &mut self,
        words: &[Word<ABit>],
        d: Domain,
    ) -> Result<Vec<FieldWord>, Error> {
        let mut out = Vec::with_capacity(words.len());
        // Each lifted bit holds 64 field lanes; bound the scratch per round.
        let words_per_batch = (1024 / d.width()).max(1);
        for chunk in words.chunks(words_per_batch) {
            let bits: Word<ABit> = chunk.iter().flat_map(|word| word.iter().copied()).collect();
            let lifted = self.lift_bits_many(&bits, d)?;
            let mut offset = 0;
            for word in chunk {
                out.push(self.weighted_sum(&lifted[offset..offset + word.len()], d));
                offset += word.len();
            }
        }
        Ok(out)
    }

    /// Open `v − ρ` for a random `ρ` known bit by bit, then add the public
    /// difference back inside the Boolean circuit. `ρ` is assembled from
    /// doubly authenticated bits, so its field and Boolean forms agree.
    fn field_to_bits_many(
        &mut self,
        words: &[&FieldWord],
        d: Domain,
    ) -> Result<Vec<Word<ABit>>, Error> {
        if words.is_empty() {
            return Ok(Vec::new());
        }
        let width = d.width();
        let mut rho_bits: Vec<Word<ABit>> = Vec::with_capacity(words.len());
        let mut rho_field: Vec<FieldWord> = Vec::with_capacity(words.len());
        for _ in words {
            let (bits, field) = self.random_bits_of_field(d)?;
            rho_bits.push(bits);
            rho_field.push(field);
        }
        #[allow(unused_mut)]
        let mut masked: SecretVec<[Value; 2]> = words
            .iter()
            .zip(&rho_field)
            .flat_map(|(v, r)| {
                v.iter().zip(r.iter()).map(|(v, r)| {
                    let v = *v;
                    [d.sub(v[0], r[0]), mac_sub(d, v[1], r[1])]
                })
            })
            .collect();
        #[cfg(test)]
        if let Some(Fault::ConversionField { lane }) = self.fault {
            self.fault = None;
            masked[lane & 63][0] = d.add(masked[lane & 63][0], [1, 0, 0, 0]);
        }
        let opened = self.partial_open_fields(&masked, d)?;
        let public: Vec<Word<ABit>> = opened
            .chunks_exact(64)
            .map(|lanes| {
                (0..width)
                    .map(|bit| {
                        self.public_bit(lanes.iter().enumerate().fold(0, |word, (lane, v)| {
                            word | (((v[bit / 64] >> (bit % 64)) & 1) << lane)
                        }))
                    })
                    .collect()
            })
            .collect();
        self.field_add_many(&public, &rho_bits, d)
    }
}

impl<T: Transport> SpdzEngine<T> {
    fn weighted_sum(&self, bits: &[FieldWord], d: Domain) -> FieldWord {
        let mut sum: FieldWord = vec![self.public_field([0; 4], d); 64].into();
        let mut weight = [1, 0, 0, 0];
        for bit in bits {
            sum = self.fadd(&sum, &self.fscale(bit, weight, d), d);
            weight = d.add(weight, weight);
        }
        sum
    }

    /// A uniformly random field word together with its binary encoding.
    ///
    /// The value is `Σ 2^b r_b` over `width` doubly authenticated bits. For
    /// Goldilocks the candidate is rejected (and its acceptance bit opened)
    /// unless it is below the modulus in every lane, so the accepted value is
    /// exactly uniform. For the 255/256-bit fields the excess above the
    /// modulus has probability below `2^-222` per lane and is not sampled out.
    fn random_bits_of_field(&mut self, d: Domain) -> Result<(Word<ABit>, FieldWord), Error> {
        let width = d.width();
        for _ in 0..4 {
            let taken = self
                .transport
                .take_dabits(ThresholdField::from_domain(d), width);
            let dabits = self.take(taken, width)?;
            if dabits
                .iter()
                .any(|r| r.field.iter().any(|s| !Self::field_share_valid(d, s)))
            {
                return self.fail(Error::InvalidConfiguration);
            }
            let bits: Word<ABit> = dabits.iter().map(|r| r.bits.bit()).collect();
            let lifted: Vec<FieldWord> = dabits
                .iter()
                .map(|r| r.field.iter().map(|s| s.0).collect())
                .collect();
            let field = self.weighted_sum(&lifted, d);
            if d != Domain::Gold {
                return Ok((bits, field));
            }
            let below = self.less_than_modulus_many(core::slice::from_ref(&bits), d)?;
            if self.open(&below)?[0] == u64::MAX {
                return Ok((bits, field));
            }
        }
        self.fail(Error::InvalidProof)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::threshold_prep::FixtureDealer;
    use std::{
        boxed::Box,
        collections::BTreeMap,
        sync::{Arc, Mutex, mpsc},
        time::Duration,
    };

    enum Batch {
        Triples(Vec<Option<Vec<BooleanTriple>>>),
        Words(Vec<Option<Vec<AuthWord>>>),
        FieldTriples(Vec<Option<Vec<FieldTriple>>>),
        FieldRandoms(Vec<Option<Vec<FieldShare>>>),
        DaBits(Vec<Option<Vec<DaBitWord>>>),
    }
    /// Shared fixture: the first quorum member to reach a request generates
    /// the material for everyone; all members must make the same requests.
    struct Supply {
        dealer: FixtureDealer,
        batches: BTreeMap<usize, (std::string::String, Batch)>,
    }
    enum Source {
        Fixture(Arc<Mutex<Supply>>),
        /// Material produced ahead of time by a preprocessing ceremony.
        Stored(Box<crate::threshold_prep::PartyPreprocessing>),
    }
    pub(crate) struct Network {
        position: usize,
        config: ThresholdConfig,
        senders: Vec<mpsc::Sender<Envelope>>,
        incoming: mpsc::Receiver<Envelope>,
        pending: BTreeMap<(u64, usize), Envelope>,
        source: Source,
        round: usize,
    }
    impl Network {
        fn supplied<V>(
            &mut self,
            request: std::string::String,
            make: impl FnOnce(&mut FixtureDealer) -> Batch,
            rows: impl FnOnce(&mut Batch) -> &mut Vec<Option<Vec<V>>>,
            stored: impl FnOnce(&mut crate::threshold_prep::PartyPreprocessing) -> Result<Vec<V>, Error>,
        ) -> Result<Vec<V>, Error> {
            let supply = match &mut self.source {
                Source::Stored(store) => return stored(store),
                Source::Fixture(supply) => supply,
            };
            let mut supply = supply.lock().unwrap();
            if !supply.batches.contains_key(&self.round) {
                let batch = make(&mut supply.dealer);
                supply.batches.insert(self.round, (request.clone(), batch));
            }
            let (expected, batch) = supply.batches.get_mut(&self.round).unwrap();
            assert_eq!(
                *expected, request,
                "quorum members disagree on preprocessing"
            );
            let rows = rows(batch);
            let mine = rows[self.position].take().unwrap();
            if rows.iter().all(Option::is_none) {
                supply.batches.remove(&self.round);
            }
            self.round += 1;
            Ok(mine)
        }
    }
    fn options<V>(rows: Vec<Vec<V>>) -> Vec<Option<Vec<V>>> {
        rows.into_iter().map(Some).collect()
    }
    impl Transport for Network {
        fn exchange_many(&mut self, outgoing: Vec<Envelope>) -> Result<Vec<Envelope>, Error> {
            let sequence = outgoing[0].sequence;
            for envelope in outgoing {
                self.senders[envelope.recipient]
                    .send(envelope)
                    .map_err(|_| Error::Transport)?;
            }
            let mut received = Vec::new();
            for &peer in &self.config.quorum {
                if peer == self.config.quorum[self.position] {
                    continue;
                }
                let key = (sequence, peer);
                while !self.pending.contains_key(&key) {
                    let envelope = self
                        .incoming
                        .recv_timeout(Duration::from_secs(30))
                        .map_err(|_| Error::Transport)?;
                    assert!(
                        self.pending
                            .insert((envelope.sequence, envelope.sender), envelope)
                            .is_none()
                    );
                }
                received.push(self.pending.remove(&key).unwrap());
            }
            Ok(received)
        }
        fn take_boolean_triples(&mut self, count: usize) -> Result<Vec<BooleanTriple>, Error> {
            self.supplied(
                std::format!("triples {count}"),
                |d| Batch::Triples(options(d.boolean_triples(count))),
                |b| match b {
                    Batch::Triples(rows) => rows,
                    _ => unreachable!(),
                },
                |store| store.take_boolean_triples(count),
            )
        }
        fn take_auth_words(&mut self, count: usize) -> Result<Vec<AuthWord>, Error> {
            self.supplied(
                std::format!("words {count}"),
                |d| Batch::Words(options(d.auth_words(count))),
                |b| match b {
                    Batch::Words(rows) => rows,
                    _ => unreachable!(),
                },
                |store| store.take_auth_words(count),
            )
        }
        fn take_field_triples(
            &mut self,
            field: ThresholdField,
            count: usize,
        ) -> Result<Vec<FieldTriple>, Error> {
            self.supplied(
                std::format!("field triples {field:?} {count}"),
                |d| Batch::FieldTriples(options(d.field_triples(field, count))),
                |b| match b {
                    Batch::FieldTriples(rows) => rows,
                    _ => unreachable!(),
                },
                |store| store.take_field_triples(field, count),
            )
        }
        fn take_field_randoms(
            &mut self,
            field: ThresholdField,
            count: usize,
        ) -> Result<Vec<FieldShare>, Error> {
            self.supplied(
                std::format!("field randoms {field:?} {count}"),
                |d| Batch::FieldRandoms(options(d.field_randoms(field, count))),
                |b| match b {
                    Batch::FieldRandoms(rows) => rows,
                    _ => unreachable!(),
                },
                |store| store.take_field_randoms(field, count),
            )
        }
        fn take_dabits(
            &mut self,
            field: ThresholdField,
            count: usize,
        ) -> Result<Vec<DaBitWord>, Error> {
            self.supplied(
                std::format!("dabits {field:?} {count}"),
                |d| Batch::DaBits(options(d.dabits(field, count))),
                |b| match b {
                    Batch::DaBits(rows) => rows,
                    _ => unreachable!(),
                },
                |store| store.take_dabits(field, count),
            )
        }
    }
    pub(crate) fn keys(config: &ThresholdConfig, party: usize) -> Vec<[u8; 32]> {
        config
            .quorum
            .iter()
            .filter(|&&p| p != party)
            .map(|&p| {
                cshake256_framed_32(
                    b"TEST.THRESHOLD.KEY",
                    &[&[party.min(p) as u8, party.max(p) as u8]],
                )
            })
            .collect()
    }
    /// Run `f(party, MAC key share, transport)` on one thread per quorum
    /// member and return the results in quorum order. Preprocessing comes
    /// from the shared deterministic fixture, generated on demand.
    pub(crate) fn run<R: Send, F: Fn(usize, MacKeyShare, Network) -> R + Sync>(
        config: ThresholdConfig,
        f: F,
    ) -> Vec<R> {
        let dealer = FixtureDealer::new(&config, [13; 32]);
        let mac_keys = dealer.mac_key_shares();
        let supply = Arc::new(Mutex::new(Supply {
            dealer,
            batches: BTreeMap::new(),
        }));
        let parties = mac_keys
            .into_iter()
            .map(|keys| (keys, Source::Fixture(supply.clone())))
            .collect();
        run_parties(config, parties, f)
    }

    /// As [`run`], with each member's keys and stored material from a
    /// preprocessing ceremony, in quorum order.
    pub(crate) fn run_stored<R: Send, F: Fn(usize, MacKeyShare, Network) -> R + Sync>(
        config: ThresholdConfig,
        parties: Vec<(MacKeyShare, crate::threshold_prep::PartyPreprocessing)>,
        f: F,
    ) -> Vec<R> {
        let parties = parties
            .into_iter()
            .map(|(keys, store)| (keys, Source::Stored(Box::new(store))))
            .collect();
        run_parties(config, parties, f)
    }

    fn run_parties<R: Send, F: Fn(usize, MacKeyShare, Network) -> R + Sync>(
        config: ThresholdConfig,
        parties: Vec<(MacKeyShare, Source)>,
        f: F,
    ) -> Vec<R> {
        let (senders, receivers): (Vec<_>, Vec<_>) =
            (0..config.parties).map(|_| mpsc::channel()).unzip();
        let mut receivers: Vec<_> = receivers.into_iter().map(Some).collect();
        std::thread::scope(|scope| {
            let handles: Vec<_> = config
                .quorum
                .iter()
                .zip(parties)
                .enumerate()
                .map(|(position, (&party, (keys, source)))| {
                    let network = Network {
                        position,
                        config: config.clone(),
                        senders: senders.clone(),
                        incoming: receivers[party].take().unwrap(),
                        pending: BTreeMap::new(),
                        source,
                        round: 0,
                    };
                    let f = &f;
                    scope.spawn(move || f(party, keys, network))
                })
                .collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        })
    }
    pub(crate) fn engine(
        config: &ThresholdConfig,
        party: usize,
        mac_keys: MacKeyShare,
        network: Network,
    ) -> SpdzEngine<Network> {
        let mut engine = SpdzEngine::new(
            party,
            [9; 32],
            config.clone(),
            keys(config, party),
            mac_keys,
            network,
        )
        .unwrap();
        engine.mix_entropy(&[party as u8; 32]);
        engine
    }
    pub(crate) fn shamir_share(party: usize, threshold: usize, witness: &[u8; 32]) -> [u8; 32] {
        let x = (party + 1) as u8;
        core::array::from_fn(|byte| {
            let mut out = witness[byte];
            let mut power = x;
            for degree in 1..threshold {
                let coefficient = (byte as u8)
                    .wrapping_mul(31)
                    .wrapping_add(degree as u8)
                    .wrapping_mul(13);
                out ^= gf_mul(power, coefficient);
                power = gf_mul(power, x);
            }
            out
        })
    }

    #[test]
    fn shamir_quorums_cover_every_supported_threshold_and_size() {
        let witness = core::array::from_fn(|i| i as u8 * 7);
        for n in 2..=64 {
            for t in 2..=n {
                // Include nonconsecutive, high party identifiers.
                let quorum: Vec<_> = (n - t..n).collect();
                let cfg = ThresholdConfig::new(t, n, quorum).unwrap();
                let mut reconstructed = [0; 32];
                for &p in cfg.quorum() {
                    let share = shamir_share(p, t, &witness);
                    for (a, b) in reconstructed
                        .iter_mut()
                        .zip(cfg.shamir_contribution(p, &share).unwrap())
                    {
                        *a ^= b;
                    }
                }
                assert_eq!(reconstructed, witness, "{t}-of-{n}");
            }
        }
        let cfg = ThresholdConfig::new(2, 64, vec![0, 31, 63]).unwrap();
        let mut reconstructed = [0; 32];
        for &p in cfg.quorum() {
            for (a, b) in reconstructed.iter_mut().zip(
                cfg.shamir_contribution(p, &shamir_share(p, 2, &witness))
                    .unwrap(),
            ) {
                *a ^= b;
            }
        }
        assert_eq!(reconstructed, witness);
        for (t, n, q) in [
            (1, 3, vec![0, 1]),
            (4, 3, vec![0, 1, 2]),
            (2, 65, vec![0, 1]),
            (2, 3, vec![0]),
            (2, 3, vec![0, 0]),
            (2, 3, vec![1, 0]),
            (2, 3, vec![0, 3]),
        ] {
            assert!(ThresholdConfig::new(t, n, q).is_err());
        }
    }

    #[test]
    fn word_macs_are_linear_and_match_the_global_key() {
        let cfg = ThresholdConfig::new(3, 5, vec![0, 2, 4]).unwrap();
        let mut dealer = FixtureDealer::new(&cfg, [1; 32]);
        let words = dealer.auth_words(8);
        for item in 0..8 {
            let word = words.iter().fold(0, |w, row| w ^ row[item].share);
            for lanes in [u64::MAX, 0, 1, 0x8000_0000_0000_0000, 0xdead_beef_0123_4567] {
                let mac = words
                    .iter()
                    .fold(0, |m, row| m ^ pack_macs(&row[item].macs, lanes));
                assert_eq!(mac, dealer.boolean_mac_of(word & lanes));
            }
        }
        // X^k weights agree with field multiplication by the lane monomial.
        let macs: [u128; 64] = core::array::from_fn(|k| 0x1234_5678_9abc_def0_u128 << k | 1);
        let expected = (0..64).fold(0, |acc, k| acc ^ gf2_128_mul(macs[k], 1u128 << k));
        assert_eq!(pack_macs(&macs, u64::MAX), expected);
    }

    #[test]
    fn authenticated_engines_support_sparse_and_full_rosters() {
        for cfg in [
            ThresholdConfig::new(2, 64, vec![0, 63]).unwrap(),
            ThresholdConfig::new(3, 9, vec![1, 4, 8]).unwrap(),
            ThresholdConfig::new(16, 16, (0..16).collect()).unwrap(),
        ] {
            run(cfg.clone(), |party, mac_keys, network| {
                let mut engine = engine(&cfg, party, mac_keys, network);
                engine.agree([17; 32]).unwrap();
                let contribution = |p: usize, k: u64| k.wrapping_mul(p as u64 + 1);
                let a = engine.share(&[contribution(party, 0xa55a)]).unwrap();
                let b = engine.share(&[contribution(party, 0x81f0)]).unwrap();
                let c = engine.and(&[(a[0], b[0])]).unwrap();
                let total = |k| cfg.quorum.iter().fold(0, |v, &p| v ^ contribution(p, k));
                let mixed = c[0] ^ a[0] ^ engine.constant(0xffff);
                assert_eq!(
                    engine.open(&[c[0], mixed]).unwrap(),
                    vec![
                        total(0xa55a) & total(0x81f0),
                        (total(0xa55a) & total(0x81f0)) ^ total(0xa55a) ^ 0xffff
                    ]
                );
                // Only the selected lanes of a masked opening are revealed.
                let mask = 0x00ff_00ff_0f0f_3333;
                assert_eq!(
                    engine.open_lanes(&[a[0], c[0]], mask).unwrap(),
                    vec![total(0xa55a) & mask, total(0xa55a) & total(0x81f0) & mask]
                );
                let uniform = engine
                    .share_uniform_lanes(&[if party == cfg.quorum[0] { u64::MAX } else { 0 }, 0])
                    .unwrap();
                assert_eq!(engine.open(&uniform).unwrap(), vec![u64::MAX, 0]);
                for d in [Domain::Gold, Domain::Secp, Domain::Ed] {
                    let a = engine.fconstant([7, 0, 0, 0], d);
                    let r = engine.frandom(d).unwrap();
                    let ar = engine.fadd(&a, &r, d);
                    let product = engine.fmul(&ar, &ar, d).unwrap();
                    let opened = engine.fopen_many(&[product, r], d).unwrap();
                    for (square, r) in opened[0].iter().zip(&opened[1]) {
                        let sum = d.add([7, 0, 0, 0], *r);
                        assert_eq!(*square, d.mul(sum, sum));
                    }
                }
                engine.agree([18; 32]).unwrap();
            });
        }
    }

    #[test]
    fn conversions_and_inverse_match_native() {
        let cfg = ThresholdConfig::new(3, 7, vec![1, 3, 6]).unwrap();
        run(cfg.clone(), |party, mac_keys, network| {
            let mut engine = engine(&cfg, party, mac_keys, network);
            for d in [Domain::Gold, Domain::Secp, Domain::Ed] {
                let value = d.sub(d.modulus(), [1, 0, 0, 0]);
                let expected: Vec<Value> = (0..64)
                    .map(|lane| match lane % 3 {
                        0 => value,
                        1 => [17, 0, 0, 0],
                        _ => [lane as u64, 1, 0, 0]
                            .map(|x| if d == Domain::Gold { x & !1 } else { x }),
                    })
                    .map(|v| {
                        if d == Domain::Gold {
                            [v[0], 0, 0, 0]
                        } else {
                            v
                        }
                    })
                    .collect();
                let own: Vec<_> = (0..d.width())
                    .map(|bit| {
                        expected.iter().enumerate().fold(0, |v, (lane, x)| {
                            v | (((x[bit / 64] >> (bit % 64)) & 1) << lane)
                        })
                    })
                    .collect();
                // Three XOR contributions, none of them the value itself.
                let contribution: Vec<_> = own
                    .iter()
                    .enumerate()
                    .map(|(bit, &v)| match party {
                        1 => v ^ (bit as u64).wrapping_mul(0x12345678),
                        3 => (bit as u64).wrapping_mul(0x12345678) ^ 0xabcdef,
                        _ => 0xabcdef,
                    })
                    .collect();
                let bits = engine.share(&contribution).unwrap();
                let field = engine.bits_to_field(&bits, d).unwrap();
                let opened = engine
                    .fopen_many(&[field.iter().copied().collect()], d)
                    .unwrap();
                assert_eq!(opened[0], expected);
                let roundtrip = engine.field_to_bits(&field, d).unwrap();
                assert_eq!(engine.open(&roundtrip).unwrap(), own);
                let inverse = engine.finverse(&field, d).unwrap();
                let product = engine.fmul(&inverse, &field, d).unwrap();
                let encoded = engine.field_to_bits(&product, d).unwrap();
                let opened = engine.open(&encoded).unwrap();
                assert_eq!(opened[0], u64::MAX);
                assert!(opened[1..].iter().all(|&x| x == 0));
            }
        });
    }

    /// One custodian of a 3-of-5 quorum deviates once. Every honest custodian
    /// must abort inside `f` and must not obtain any opened value from it.
    fn cheat<F>(fault: Fault, cheater: usize, f: F)
    where
        F: Fn(&mut SpdzEngine<Network>, usize) -> Result<Vec<u64>, Error> + Sync,
    {
        let cfg = ThresholdConfig::new(3, 5, vec![0, 2, 4]).unwrap();
        // Control: with nobody deviating the same steps succeed and agree.
        let honest = run(cfg.clone(), |party, mac_keys, network| {
            let mut engine = engine(&cfg, party, mac_keys, network);
            let outcome = f(&mut engine, party);
            assert!(!engine.failed);
            outcome
        });
        let reference = honest[0].clone().expect("honest run must succeed");
        assert!(!reference.is_empty());
        assert!(
            honest
                .iter()
                .all(|outcome| outcome.as_ref() == Ok(&reference))
        );
        let outcomes = run(cfg.clone(), |party, mac_keys, network| {
            let mut engine = engine(&cfg, party, mac_keys, network);
            if party == cheater {
                engine.fault = Some(fault);
            }
            let outcome = f(&mut engine, party);
            assert!(
                party != cheater || engine.fault.is_none(),
                "{fault:?} was never injected"
            );
            // A poisoned engine refuses all further work and holds no keys.
            assert!(engine.failed);
            assert_eq!(engine.keys.boolean, 0);
            assert_eq!(engine.keys.field, [[0; 4]; 3]);
            assert_eq!(engine.open(&[]), Err(Error::MultiplicationCheck));
            assert_eq!(engine.agree([0; 32]), Err(Error::MultiplicationCheck));
            assert!(engine.share(&[1]).is_err());
            outcome
        });
        for (position, outcome) in outcomes.iter().enumerate() {
            assert!(
                matches!(
                    outcome,
                    Err(Error::MultiplicationCheck) | Err(Error::Disagreement(_))
                ),
                "{fault:?}: custodian at position {position} got {outcome:?}"
            );
        }
    }

    fn inputs(engine: &mut SpdzEngine<Network>, party: usize) -> Result<(ABit, ABit), Error> {
        let a = engine.share(&[0x0123_4567_89ab_cdef_u64.rotate_left(party as u32)])?;
        let b = engine.share(&[0xfedc_ba98_7654_3210_u64.rotate_left(3 * party as u32)])?;
        Ok((a[0], b[0]))
    }

    #[test]
    fn flipped_wire_share_is_caught_before_the_opening_is_returned() {
        for cheater in [0, 2, 4] {
            for lane in [0, 31, 63] {
                cheat(Fault::FlipOpenedShare { lane }, cheater, |e, party| {
                    let (a, b) = inputs(e, party)?;
                    e.open(&[a ^ b])
                });
            }
        }
    }

    #[test]
    fn lying_in_a_beaver_opening_is_caught_before_the_product_opens() {
        for cheater in [0, 2, 4] {
            for lane in [0, 17, 63] {
                cheat(Fault::BeaverOpening { lane }, cheater, |e, party| {
                    let (a, b) = inputs(e, party)?;
                    let c = e.and(&[(a, b)])?;
                    // The lie is still undetected here; no honest custodian
                    // sends a share of the product before the check runs.
                    e.open(&c)
                });
                cheat(Fault::BeaverOutput { lane }, cheater, |e, party| {
                    let (a, b) = inputs(e, party)?;
                    let c = e.and(&[(a, b)])?;
                    e.open(&c)
                });
            }
        }
    }

    #[test]
    fn lying_in_a_field_beaver_opening_is_caught_in_every_field() {
        for d in [Domain::Gold, Domain::Secp, Domain::Ed] {
            for cheater in [0, 4] {
                cheat(Fault::FieldBeaverOpening { lane: 9 }, cheater, |e, _| {
                    let a = e.frandom(d)?;
                    let b = e.frandom(d)?;
                    let c = e.fmul(&a, &b, d)?;
                    let bits = e.field_to_bits(&c, d)?;
                    e.open(&bits)
                });
            }
        }
    }

    #[test]
    fn forged_conversion_bits_are_caught_in_both_directions() {
        for d in [Domain::Gold, Domain::Secp, Domain::Ed] {
            for cheater in [0, 2] {
                cheat(Fault::ConversionBit { lane: 5 }, cheater, |e, party| {
                    let (a, _) = inputs(e, party)?;
                    let lifted = e.lift_bits_many(&[a], d)?;
                    Ok(e.fopen_many(&lifted, d)?[0].iter().map(|v| v[0]).collect())
                });
                cheat(Fault::ConversionField { lane: 40 }, cheater, |e, _| {
                    let a = e.frandom(d)?;
                    let bits = e.field_to_bits(&a, d)?;
                    e.open(&bits)
                });
            }
        }
    }

    #[test]
    fn split_inputs_wrong_macs_and_equivocation_are_caught() {
        for cheater in [0, 2, 4] {
            cheat(Fault::SplitInput, cheater, |e, _| {
                let w = e.share_uniform_lanes(&[u64::MAX])?;
                e.open(&w)
            });
            cheat(Fault::WrongMac, cheater, |e, party| {
                let (a, b) = inputs(e, party)?;
                e.open(&[a ^ b])
            });
            cheat(Fault::Equivocate, cheater, |e, party| {
                let (a, b) = inputs(e, party)?;
                let c = e.and(&[(a, b)])?;
                e.open(&c)
            });
        }
    }

    #[test]
    fn stored_preprocessing_is_served_in_order_and_exhaustion_fails_closed() {
        use crate::threshold_prep::{Demand, PartyPreprocessing};
        let cfg = ThresholdConfig::new(3, 5, vec![0, 2, 4]).unwrap();
        let mut dealer = FixtureDealer::new(&cfg, [21; 32]);
        let field = ThresholdField::Goldilocks;
        let mut stores: Vec<PartyPreprocessing> =
            (0..3).map(|_| PartyPreprocessing::new()).collect();
        for (store, words) in stores.iter_mut().zip(dealer.auth_words(2)) {
            store.add_auth_words(words);
        }
        for (store, triples) in stores.iter_mut().zip(dealer.boolean_triples(1)) {
            store.add_boolean_triples(triples);
        }
        for (store, dabits) in stores.iter_mut().zip(dealer.dabits(field, 1)) {
            store.add_dabits(field, dabits);
        }
        let mut demand = Demand {
            boolean_triples: 1,
            auth_words: 2,
            ..Demand::default()
        };
        demand.dabits[field.index()] = 1;
        assert!(stores.iter().all(|store| store.remaining() == demand));
        let parties = dealer.mac_key_shares().into_iter().zip(stores).collect();
        run_stored(cfg.clone(), parties, |party, mac_keys, network| {
            let mut engine = engine(&cfg, party, mac_keys, network);
            let (a, b) = inputs(&mut engine, party).unwrap();
            let c = engine.and(&[(a, b)]).unwrap();
            let lifted = engine.lift_bits_many(&c, Domain::Gold).unwrap();
            let total = |k: u64, r: u32| {
                cfg.quorum
                    .iter()
                    .fold(0, |v, &p| v ^ k.rotate_left(r * p as u32))
            };
            let expected = total(0x0123_4567_89ab_cdef, 1) & total(0xfedc_ba98_7654_3210, 3);
            assert_eq!(engine.open(&c).unwrap(), vec![expected]);
            let opened = engine.fopen_many(&lifted, Domain::Gold).unwrap();
            for (lane, value) in opened[0].iter().enumerate() {
                assert_eq!(*value, [(expected >> lane) & 1, 0, 0, 0]);
            }
            // Everything stored has been used exactly once; one more request
            // fails closed, consumes nothing and poisons the engine.
            assert_eq!(
                engine.and(&[(a, b)]).err(),
                Some(Error::MissingPreprocessing)
            );
            assert!(engine.failed);
            assert_eq!(engine.open(&c), Err(Error::MultiplicationCheck));
        });
    }

    #[test]
    fn malformed_rounds_and_invalid_custody_are_rejected() {
        struct Altered;
        impl Transport for Altered {
            fn exchange_many(&mut self, out: Vec<Envelope>) -> Result<Vec<Envelope>, Error> {
                Ok(out
                    .iter()
                    .map(|m| Envelope {
                        sender: m.recipient,
                        recipient: m.sender,
                        sequence: m.sequence,
                        payload: m.payload.clone(),
                        tag: [0; 32],
                    })
                    .collect())
            }
        }
        struct Empty;
        impl Transport for Empty {}
        let cfg = ThresholdConfig::new(2, 64, vec![0, 63]).unwrap();
        let mac_keys = || FixtureDealer::new(&cfg, [3; 32]).mac_key_shares().remove(0);
        let state = |transport| {
            SpdzEngine::new(
                0,
                [9; 32],
                cfg.clone(),
                keys(&cfg, 0),
                mac_keys(),
                transport,
            )
        };
        let mut altered = state(Altered).unwrap();
        assert_eq!(altered.agree([1; 32]), Err(Error::Authentication(63)));
        assert_eq!(altered.agree([1; 32]), Err(Error::MultiplicationCheck));
        let mut empty =
            SpdzEngine::new(0, [9; 32], cfg.clone(), keys(&cfg, 0), mac_keys(), Empty).unwrap();
        assert_eq!(empty.share(&[1]).err(), Some(Error::MissingPreprocessing));
        assert_eq!(empty.open(&[]), Err(Error::MultiplicationCheck));
        let mut empty =
            SpdzEngine::new(0, [9; 32], cfg.clone(), keys(&cfg, 0), mac_keys(), Empty).unwrap();
        assert_eq!(empty.agree([1; 32]), Err(Error::InvalidConfiguration));
        assert_eq!(empty.agree([1; 32]), Err(Error::MultiplicationCheck));
        // Not a quorum member, wrong number of channel keys, non-canonical key share.
        assert!(
            SpdzEngine::new(1, [9; 32], cfg.clone(), keys(&cfg, 0), mac_keys(), Empty).is_err()
        );
        assert!(SpdzEngine::new(0, [9; 32], cfg.clone(), vec![], mac_keys(), Empty).is_err());
        let mut bad = mac_keys();
        bad.field[ThresholdField::Secp256k1.index()] = [u64::MAX; 4];
        assert!(SpdzEngine::new(0, [9; 32], cfg.clone(), keys(&cfg, 0), bad, Empty).is_err());
        assert!(
            crate::CoZkCustodianShare::new_shamir(
                1,
                cfg.clone(),
                [0; 32],
                [0; 32],
                [0; 32],
                keys(&cfg, 0),
                mac_keys(),
            )
            .is_err()
        );
        assert!(
            crate::CoZkCustodianShare::new_shamir(
                0,
                cfg.clone(),
                [0; 32],
                [0; 32],
                [0; 32],
                vec![],
                mac_keys()
            )
            .is_err()
        );
        for parties in [0, 1, 65, usize::MAX] {
            assert!(
                crate::CoZkCustodianShare::new_additive(
                    0,
                    parties,
                    [0; 32],
                    [0; 32],
                    [0; 32],
                    vec![],
                    mac_keys(),
                )
                .is_err()
            );
        }
        assert!(
            crate::CoZkCustodianShare::new_additive(
                63,
                64,
                [0; 32],
                [0; 32],
                [0; 32],
                vec![[1; 32]; 63],
                mac_keys(),
            )
            .is_ok()
        );
    }
}
